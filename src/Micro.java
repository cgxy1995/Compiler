import java.io.*;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
public class Micro{
	public static ArrayList<ASTnode> node_list = new ArrayList<ASTnode>();
	public static LinkedHashMap<String,Symbol_block> symbol_map = new LinkedHashMap<String,Symbol_block>();
	public static LinkedHashMap<String,LinkedHashMap> function_list = new LinkedHashMap<String,LinkedHashMap>();
	public static ArrayList<String> function_name_list = new ArrayList<String>();
	public static String code_list="";
	public static String code_list_op1="";
	public static Stack<ASTnode> node_stack = new Stack<ASTnode>();
	public static Stack<Integer> addnum_stack = new Stack<Integer>();
	public static Stack<Integer> mulnum_stack = new Stack<Integer>();
	public static Stack<Integer> if_stack = new Stack<Integer>(); //save current if label num on stack
	public static Stack<Integer> else_stack = new Stack<Integer>();
	public static Stack<Integer> while_stack = new Stack<Integer>();
	//public static ArrayList<LinkedHashMap<String,String>> registers = new ArrayList<LinkedHashMap<String,String>>();
	public static Stack<ArrayList<LinkedHashMap<String,String>>> register_stack = new Stack<ArrayList<LinkedHashMap<String,String>>>();
	public static LinkedHashMap<String,ArrayList<IRnode>> CFGbyFunctions = new LinkedHashMap<String,ArrayList<IRnode>>();
	private static int scp_ct=1;
	private static int if_ct=0; //num of ifs
	private static int expr_depth=0; //current depth in tree
	private static int while_ct=0; //num of whiles
	private static int intfloat=0; //current expression 0=int 1=float
	private static int curr_func_inx=0;
	private static String curr_block = null;
	public static boolean func_call_mode=false;
	private static String parsing_function=null;
	private static String calling_function=null;
	private static String parsing_block = null;
	private static int parsing_block_ct = 1;
	private static Stack<String> calling_function_stack = new Stack<String>();
	public static final int LEFT_VAL = 0;
    public static final int RGHT_VAL = 1;
    public static final int CONS_VAL = 2;
    public static final int OP_VAL = 3;
    public static int regcnt = 0;    
	//public static int addnum=0;
	//public static int mulnum=0;
	public static void main(String args[]){
		try{
		    MicroLexer lexer = new MicroLexer(new ANTLRFileStream(args[0]));
		    CommonTokenStream tokens = new CommonTokenStream(lexer);
		    MicroParser parser = new MicroParser(tokens);
		    ANTLRErrorStrategy es = new MyErrorHandler();
		    ByteArrayOutputStream dummy = new ByteArrayOutputStream();	
		    addnum_stack.push(0);
		    mulnum_stack.push(0);	    
		    parser.program();
		    peepHole(code_list);
		    create_CFG(code_list_op1);
		    compute_liveness();
		    init_reg();
		    asm_gen(code_list_op1);
		    //System.out.println("size= "+node_stack.size());		
		    String teststring = "STOREI 1 $T1;STOREI $T1 a;"+
		    "STOREI 2 $T2;STOREI $T2 b;READI c;READI d;MULTI a c $T3;MULTI b d $T4;"+
			"ADDI $T3 $T4 $T5;STOREI $T5 e;WRITEI c;WRITES newline;WRITEI d;"+
			"WRITES newline;WRITEI e;WRITES newline";
		    //asm_gen(teststring);
		    //print_stack();
		}catch(IOException e){
			//System.out.println("Accepted");
		}
	}
	private static void print_stack(){
		while (node_stack.size()>0){
			ASTnode node=node_stack.pop();
			node.printname();
		}
	}
	private static void create_CFG(String code){
		String current_func = "";
		String [] lines = code.split(";");
		ArrayList<String> func_names = new ArrayList<String>();
		ArrayList<IRnode> IR_list = new ArrayList<IRnode>();
		int func_name_idx = -1;
		boolean startoffunction = true;
		struct_by_functions(code);
		for(String key: CFGbyFunctions.keySet()){
			func_names.add(key);//contains names of function
		}
		for(int i=0;i<lines.length;i++){
			IRnode node = new IRnode(lines[i]);
			IR_list.add(node);
			String [] line2 = lines[i].split(" ");
			if(i+1<lines.length){
				String [] line3 = lines[i+1].split(" ");
				if(line3[0].equals("LINK")){
					func_name_idx++;
				}
			}
			CFGbyFunctions.get(func_names.get(func_name_idx)).add(node);
		}
		func_name_idx=0;
		for(String key: CFGbyFunctions.keySet()){
			for(int i=0;i<CFGbyFunctions.get(key).size();i++){
				if(startoffunction){
					startoffunction=false;
					CFGbyFunctions.get(key).get(i).addsuccessor(CFGbyFunctions.get(key).get(i+1));
				}else if(i==CFGbyFunctions.get(key).size()-1){
					startoffunction=true;
					CFGbyFunctions.get(key).get(i).addpredecessor(CFGbyFunctions.get(key).get(i-1));
				}else{
					String [] line = CFGbyFunctions.get(key).get(i).code.split(" ");
					if(line[0].equals("LEI")||line[0].equals("LTI")||line[0].equals("GEI")||line[0].equals("GTI")||line[0].equals("NEI")||line[0].equals("EQI")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")){
						CFGbyFunctions.get(key).get(i).addsuccessor(CFGbyFunctions.get(key).get(i+1));
						CFGbyFunctions.get(key).get(i).addpredecessor(CFGbyFunctions.get(key).get(i-1));
						for(int j=i;j<CFGbyFunctions.get(key).size();j++){
							String [] line2 = CFGbyFunctions.get(key).get(j).code.split(" ");
							try{
								if(line2[1].equals(line[3])){
									CFGbyFunctions.get(key).get(i).addsuccessor(CFGbyFunctions.get(key).get(j));
									break;
								}
							}catch(Exception e){}
						}
					}else if(line[0].equals("LABEL")){
						CFGbyFunctions.get(key).get(i).addsuccessor(CFGbyFunctions.get(key).get(i+1));
						CFGbyFunctions.get(key).get(i).addpredecessor(CFGbyFunctions.get(key).get(i-1));
						for(int j=0;j<i;j++){
							String [] line2 = CFGbyFunctions.get(key).get(j).code.split(" ");
							try{
								if(line[1].equals(line2[3])){
									CFGbyFunctions.get(key).get(i).addpredecessor(CFGbyFunctions.get(key).get(j));
								}
							}catch(Exception e){}
						}
					}else if(line[0].equals("JUMP")){
						CFGbyFunctions.get(key).get(i).addpredecessor(CFGbyFunctions.get(key).get(i-1));
						for(int j =0;j<CFGbyFunctions.get(key).size();j++){
							String [] line2 = CFGbyFunctions.get(key).get(j).code.split(" ");
							try{
								if(line2[1].equals(line[1])&&j!=i){
									CFGbyFunctions.get(key).get(i).addsuccessor(CFGbyFunctions.get(key).get(j));
									CFGbyFunctions.get(key).get(j).addpredecessor(CFGbyFunctions.get(key).get(i));
									break;
								}
							}catch(Exception e){}
						}
					}else{
						CFGbyFunctions.get(key).get(i).addsuccessor(CFGbyFunctions.get(key).get(i+1));
						CFGbyFunctions.get(key).get(i).addpredecessor(CFGbyFunctions.get(key).get(i-1));
					}
				}
			}
		}
		func_name_idx=0;
		/*for(String key: CFGbyFunctions.keySet()){
			for(int i=0;i<CFGbyFunctions.get(key).size();i++){
				System.out.println(";"+CFGbyFunctions.get(key).get(i).code);
				if(CFGbyFunctions.get(key).get(i).predecessors.size()>0){
					System.out.print("predecessors: ");
					for(int j=0;j<CFGbyFunctions.get(key).get(i).predecessors.size();j++){
						System.out.print(CFGbyFunctions.get(key).get(i).predecessors.get(j).code+" ");
					}
				}
				if(CFGbyFunctions.get(key).get(i).successors.size()>0){
					System.out.print(",successors: ");
					for(int j=0;j<CFGbyFunctions.get(key).get(i).successors.size();j++){
						System.out.print(CFGbyFunctions.get(key).get(i).successors.get(j).code+" ");
					}
				}
				System.out.println();
			}
		}*/
	}
	private static void struct_by_functions(String code){
		String [] lines = code.split(";");
		for(int i=0;i<lines.length;i++){
			if(lines[i].equals("LINK")){
				String [] seg = lines[i-1].split(" ");
				ArrayList<IRnode> a = new ArrayList<IRnode>();
				CFGbyFunctions.put(seg[1],a);
			}
		}
	}
	private static void peepHole(String IRcode){
		String [] lines = IRcode.split(";");
		Pattern num=Pattern.compile("([0-9]+)||([0-9]*\\.[0-9]+)");
		Pattern reg=Pattern.compile("\\$T([0-9]+)");
		Pattern id=Pattern.compile("[a-zA-Z]([a-zA-Z]|[0-9])*");
		boolean storeFlag1 = false;
		/*for(int i=0;i<lines.length;i++){
			System.out.println(";"+lines[i]);
		}*/
		for(int i=0;i<lines.length;i++){
			String [] code = lines[i].split(" ");
			try{
				Matcher num_matcher_1 = num.matcher(code[1]);
				Matcher reg_matcher_2 = reg.matcher(code[2]);
				Matcher id_matcher_2 = id.matcher(code[2]);
				Matcher reg_matcher_1 = reg.matcher(code[1]);
				if((code[0].equals("STOREI")||code[0].equals("STOREF"))&&storeFlag1==false){
					if(num_matcher_1.matches()&&reg_matcher_2.matches()){
						storeFlag1=true;
					}else{
						code_list_op1 = code_list_op1 + lines[i] +";";
					}
				}else if((code[0].equals("STOREI")||code[0].equals("STOREF"))&&storeFlag1==true){
					if(id_matcher_2.matches()&&reg_matcher_1.matches()){
						storeFlag1=false;
						String [] lastLine = lines[i-1].split(" ");
						code_list_op1 = code_list_op1 + code[0]+ " " + lastLine[1] + " " + code[2] + ";";
					}else{
						storeFlag1 = false;
						code_list_op1 = code_list_op1 + lines[i-1] + ";" + lines[i] + ";";
					}
				}else{
					if(storeFlag1==true){
						code_list_op1 = code_list_op1 + lines[i-1] + ";" + lines[i] + ";";
						storeFlag1=false;
					}else{
						code_list_op1 = code_list_op1 + lines[i] + ";";
					}
				}
			}catch(Exception e){code_list_op1 = code_list_op1 + lines[i] + ";";}
		}
		/*lines = code_list_op1.split(";");
		for(int i=0;i<lines.length;i++){
			System.out.println(";"+lines[i]);
		}
		System.out.println(";------------------------------");*/
		/*for(int i=0;i<lines.length;i++){
			System.out.println(";"+lines[i]);
		}*/
	}
	private static void compute_liveness(){
		ArrayList<String> current_liveness = new ArrayList<String>();
		Pattern num=Pattern.compile("([0-9]+)||([0-9]*\\.[0-9]+)");
		for(String key: CFGbyFunctions.keySet()){
			for(int i=CFGbyFunctions.get(key).size()-1;i>1;i--){
				for(int j=0;j<CFGbyFunctions.get(key).get(i).successors.size();j++){
					current_liveness.clear();
					current_liveness.addAll(CFGbyFunctions.get(key).get(i).successors.get(j).liveness);
					String [] line = CFGbyFunctions.get(key).get(i).successors.get(j).code.split(" ");
					if(line[0].equals("MOVE")){
						Matcher num_matcher = num.matcher(line[1]);
						current_liveness.remove(line[2]);
						if(!num_matcher.matches()){
							current_liveness.add(line[1]);
						}
					}else if(line[0].equals("STOREI")||line[0].equals("STOREF")){
						Matcher num_matcher = num.matcher(line[1]);
						current_liveness.remove(line[2]);
						if(!num_matcher.matches()){
							current_liveness.add(line[1]);
						}
					}else if(line[0].equals("LEI")||line[0].equals("LTI")||line[0].equals("GEI")||line[0].equals("GTI")||line[0].equals("NEI")||line[0].equals("EQI")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")||line[0].equals("LEF")){
						current_liveness.add(line[1]);
						current_liveness.add(line[2]);
					}else if(line[0].equals("WRITEI")||line[0].equals("WRITEF")){
						current_liveness.add(line[1]);
					}else if(line[0].equals("READI")||line[0].equals("READF")){
						current_liveness.remove(line[1]);
					}else if(line[0].equals("ADDI")||line[0].equals("ADDF")||line[0].equals("SUBI")||line[0].equals("SUBF")||line[0].equals("MULTI")||line[0].equals("MULTF")||line[0].equals("DIVI")||line[0].equals("DIVF")){
						Matcher num_matcher = num.matcher(line[1]);
						if(!num_matcher.matches()){
							current_liveness.add(line[1]);
						}
						current_liveness.add(line[2]);
						current_liveness.remove(line[3]);
					}else if(line[0].equals("PUSH")&&line.length>1){
						Matcher num_matcher = num.matcher(line[1]);
						if(!num_matcher.matches()){
							current_liveness.add(line[1]);
						}
					}else if(line[0].equals("POP")&&line.length>1){
						current_liveness.remove(line[1]);
					}
					CFGbyFunctions.get(key).get(i).update_liveness(current_liveness);
				}
			}
		}
		/*System.out.println(";--------------------------------------");
		for(String key: CFGbyFunctions.keySet()){
			for(int i=0;i<CFGbyFunctions.get(key).size();i++){
				System.out.println(";"+CFGbyFunctions.get(key).get(i).code);
				System.out.print("liveness: ");				
				for(int j=0;j<CFGbyFunctions.get(key).get(i).liveness.size();j++){
					System.out.print(CFGbyFunctions.get(key).get(i).liveness.get(j)+", ");
				}
				System.out.println();
			}
		}*/

	}
	public static void evaluate(){
		ASTnode right=node_stack.pop();
		ASTnode equal=node_stack.pop();
		ASTnode left=node_stack.pop();
		equal.left=left;
		equal.right=right;
		//view_tree(equal);
		postorder_IR(equal);
		node_list.add(equal);
		int addnum=addnum_stack.pop();
		addnum=0;
		addnum_stack.push(addnum);
	}
	public static void eval_expr(){ //generate code for expr in IF and WHILE
		ASTnode node=node_stack.pop();
		postorder_IR(node);
		intfloat=node.i_fchk;
		int addnum=addnum_stack.pop();
		addnum=0;
		addnum_stack.push(addnum);
	}
	public static void setList(LinkedHashMap<String,Symbol_block> b){ // sync symbol_map in Micro.java and Symbol_table.java
		symbol_map=b;
	}
	public static void view_blocks(){
		/*for (int i=0; i<symbol_list.size();i++){
			System.out.println(symbol_map.get(i).getName());
		}*/
		for (String key: symbol_map.keySet()){
			System.out.println(key);
		}
	}
	public static void add_ASTnode(String name,int LR,int intvalue,float floatvalue,int i_fchk){
		String realname=name;
		String thekey=null;
		/*if(parsing_function.equals("main")){
			System.out.println(name);
		}*/
		for(String key: symbol_map.keySet()){
			if(LR==0||LR==1){
				try{
					if(symbol_map.get(key).symbol_hash_table.get(name).getType().equals("INT")&&key.equals(parsing_function)&&!key.equals("GLOBAL")){
						i_fchk=0;
						thekey=key;
						break;
					}else if(symbol_map.get(key).symbol_hash_table.get(name).getType().equals("FLOAT")&&key.equals(parsing_function)&&!key.equals("GLOBAL")){
						i_fchk=1;
						thekey=key;
						break;
					}
				}catch(Exception e){
				}
			}
		}
		if(thekey==null&&(LR==0||LR==1)){
			for(String key: symbol_map.keySet()){
				try{
					if(symbol_map.get(key).symbol_hash_table.get(name).getType().equals("INT")&&symbol_map.get(key).symbol_hash_table.get(name).includedBy.equals(parsing_function)&&!key.equals("GLOBAL")){
						i_fchk=0;
						thekey=key;
						break;
					}else if(symbol_map.get(key).symbol_hash_table.get(name).getType().equals("FLOAT")&&symbol_map.get(key).symbol_hash_table.get(name).includedBy.equals(parsing_function)&&!key.equals("GLOBAL")){
						i_fchk=1;
						thekey=key;
						break;
					}
				}catch(Exception e){
				}
			}
		}
		if(thekey==null&&(LR==0||LR==1)){
			try{
				if(symbol_map.get("GLOBAL").symbol_hash_table.get(name).getType().equals("INT")){
					i_fchk=0;
					thekey="GLOBAL";
				}else if(symbol_map.get("GLOBAL").symbol_hash_table.get(name).getType().equals("FLOAT")){
					i_fchk=1;
					thekey="GLOBAL";
				}
			}catch(Exception e){}
		}
		try{
			realname = symbol_map.get(thekey).symbol_hash_table.get(name).getName();
		}catch(Exception e){}
		if(i_fchk==0){
			ASTnode node = new ASTnode(realname,LR,intvalue,floatvalue,i_fchk);//realname
			node_stack.push(node);
		}else{
			ASTnode node = new ASTnode(realname,LR,intvalue,floatvalue,i_fchk);
			node_stack.push(node);
		}
		if (name.equals("+")||name.equals("-")){
			int addnum=addnum_stack.pop();
			addnum++;
			addnum_stack.push(addnum);
		}else if(name.equals("*")||name.equals("/")){
			int mulnum=mulnum_stack.pop();
			mulnum++;
			mulnum_stack.push(mulnum);
		}
	}
	public static void comb_add(int mode){
		int addnum=addnum_stack.pop();
		if(addnum>0){
			ASTnode right=node_stack.pop();
			ASTnode op=node_stack.pop();
			ASTnode left=node_stack.pop();
			op.left=left;
			op.right=right;
			node_stack.push(op);
		}
		if(mode==1){
			addnum=0;
		}
		addnum_stack.push(addnum);
	}
	public static void comb_mul(int mode){
		int mulnum=mulnum_stack.pop();
		if(mulnum>0){
			ASTnode right=node_stack.pop();
			ASTnode op=node_stack.pop();
			ASTnode left=node_stack.pop();
			op.left=left;
			op.right=right;
			node_stack.push(op);
		}
		if(mode==1){
			mulnum=0;
		}
		mulnum_stack.push(mulnum);
	}
	public static void new_opstack(){
		addnum_stack.push(0);
		mulnum_stack.push(0);
	}
	public static void pop_opstack(){
		addnum_stack.pop();
		mulnum_stack.pop();
	}
	public static void postorder_IR(ASTnode head){
		if(head==null){
			expr_depth--;
			return;}
		if(!head.name.equals(":=")){
			expr_depth++;
	    	postorder_IR(head.left);
		}
		expr_depth++;
		postorder_IR(head.right);
		IR_generator(head);
		if(expr_depth>0){
			expr_depth--;
		}
    }
    public static void IR_generator(ASTnode head){	
		if(head.LR==CONS_VAL){
		    //	    System.out.println("IN1");		  
		    if(head.i_fchk==0){
			//		System.out.println("IN9");
			regcnt++;
			head.code="STOREI " + head.name + " " +  "$T" + Integer.toString(regcnt);	     
		    }
		    else if(head.i_fchk==1){
			//		System.out.println("IN10");
			regcnt++;
			head.code="STOREF " + head.name + " " + "$T" + Integer.toString(regcnt);
		    }
		    head.name="$T" + Integer.toString(regcnt);
		}
		else if(head.LR==1 && (expr_depth==1 ||expr_depth==0)){
			regcnt++;
			head.code="MOVE " + head.name + " " + "$T" + Integer.toString(regcnt);
			head.name="$T" + Integer.toString(regcnt);
		}		
		else if(head.LR==OP_VAL){
		    ///System.out.println("IN2");
		    if(head.name.equals("+")){
			if(head.left.i_fchk==0 && head.right.i_fchk==0){
			    //	    System.out.println("IN3");
			    regcnt++;
			    head.code="ADDI " + head.left.name + " " + head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=0;
			}
			else{
			    regcnt++;
			    head.code="ADDF " + head.left.name + " " + head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=1;
		        }
		    }	    
		    else if(head.name.equals("-")){
			if(head.left.i_fchk==0 && head.right.i_fchk==0){
			    ///System.out.println("IN4");
			    regcnt++;		    
			    head.code="SUBI " + head.left.name + " " +head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=0;
			}
			else{
			    regcnt++;
			    head.code="SUBF " + head.left.name + " " + head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=1;
		        }
		    }
		    else if(head.name.equals("*")){
			//System.out.println("IN5");
			if(head.left.i_fchk==0 && head.right.i_fchk==0){
			    regcnt++;		   
			    head.code="MULTI " + head.left.name + " " + head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=0;
			}
			else{
			    regcnt++;
			    head.code="MULTF " + head.left.name + " " + head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=1;
		        }
		    }
	 	    else if(head.name.equals("/")){
			if(head.left.i_fchk==0 && head.right.i_fchk==0){
			    //System.out.println("IN6");
			    regcnt++;
			    head.code="DIVI " + head.left.name + " " + head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=0;
			}
			else{
			    regcnt++;
			    head.code="DIVF " + head.left.name + " " + head.right.name + " " + "$T" + Integer.toString(regcnt);
			    head.name="$T" + Integer.toString(regcnt);
			    head.i_fchk=1;
		        }
		    }
		    else if(head.name.equals(":=")){
			if(head.right.LR == OP_VAL){
			    if(head.left.i_fchk==0){
				head.code="STOREI " + "$T" + Integer.toString(regcnt) + " " + head.left.name;
				head.i_fchk=0;
			    }
			    else if(head.left.i_fchk==1){
				head.code="STOREF " + "$T" + Integer.toString(regcnt) + " " + head.left.name;
				head.i_fchk=1;
			    }
			}else if(head.right.LR == 1){
				if(head.left.i_fchk==0){
				head.code=/*"STOREI "+ head.right.name +" $T"+Integer.toString(regcnt)+*/"STOREI " + "$T" + Integer.toString(regcnt) + " " + head.left.name;
				head.i_fchk=0;
			    }
			    else if(head.left.i_fchk==1){
				head.code=/*"STOREF "+ head.right.name +" $T"+Integer.toString(regcnt)+*/"STOREF " + "$T" + Integer.toString(regcnt) + " " + head.left.name;
				head.i_fchk=1;
			    }
			}	       
			else{
			    //		    System.out.println("IN8");
			    if(head.left.i_fchk==0){
				head.code="STOREI " + head.right.name + " " + head.left.name;
				head.i_fchk=0;
			    }
			    else if(head.left.i_fchk==1){
				head.code="STOREF " + head.right.name + " " + head.left.name;
				head.i_fchk=1;
			    }
			}
		    }
		}
		    if(head.code!=null){
		    	//System.out.println(";"+head.code);
		    	code_list=code_list+head.code+";";
		    }
	}
	public static void READ_IR(String codeline){
		String [] codeseg = codeline.split(",");
		String current_func=null; 
		for(int i=0;i<codeseg.length;i++){ //check vars in functions
			for(String key: symbol_map.keySet()){
				if(symbol_map.get(key).symbol_hash_table.containsKey(codeseg[i])){
					if(key.equals(parsing_function)){
						current_func=key;
						break;
					}
				}
			}
			if(current_func==null){
				for(String key: symbol_map.keySet()){//check vars in blocks
					if(symbol_map.get(key).symbol_hash_table.containsKey(codeseg[i])){
						if(key.equals(parsing_block)){
							current_func=key;
							break;
						}
					}
				}
			}
			if(current_func==null){
				current_func="GLOBAL";
			}
			if(current_func.equals("GLOBAL")){
				if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("INT")){
					//System.out.println(";READI "+codeseg[i]);
					code_list=code_list+"READI "+codeseg[i]+";";
				}else if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("FLOAT")){
					//System.out.println(";READF "+codeseg[i]);
					code_list=code_list+"READF "+codeseg[i]+";";
				}
			}else{
				if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("INT")){
					//System.out.println(";READI "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName());
					code_list=code_list+"READI "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName()+";";
				}else if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("FLOAT")){
					//System.out.println(";READF "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName());
					code_list=code_list+"READF "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName()+";";
				}
			}
		}
	}
	public static void WRITE_IR(String codeline){
		String [] codeseg = codeline.split(",");
		/*for(int i=0;i<symbol_list.size();i++){ // need improvement
			if(symbol_map.get(i).getName().equals("GLOBAL")){
				"GLOBAL"=i;
			}
		}*/
		for(int i=0;i<codeseg.length;i++){
			/*if(function_list.get(function_name_list.get(curr_func_inx-1)).containsKey(codeseg[i])){
				if(symbol_map.get(function_name_list.get(curr_func_inx-1)).symbol_hash_table.get(codeseg[i]).getType().equals("INT")){
					System.out.println(";WRITEI "+function_list.get(function_name_list.get(curr_func_inx-1)).get(codeseg[i]));
					code_list=code_list+"WRITEI "+function_list.get(function_name_list.get(curr_func_inx-1)).get(codeseg[i])+";";
				}else if(symbol_map.get(function_name_list.get(curr_func_inx-1)).symbol_hash_table.get(codeseg[i]).getType().equals("FLOAT")){
					System.out.println(";WRITEF "+function_list.get(function_name_list.get(curr_func_inx-1)).get(codeseg[i]));
					code_list=code_list+"WRITEF "+function_list.get(function_name_list.get(curr_func_inx-1)).get(codeseg[i])+";";
				}
				else if(symbol_map.get(function_name_list.get(curr_func_inx-1)).symbol_hash_table.get(codeseg[i]).getType().equals("STRING")){
					System.out.println(";WRITES "+function_list.get(function_name_list.get(curr_func_inx-1)).get(codeseg[i]));
					code_list=code_list+"WRITES "+function_list.get(function_name_list.get(curr_func_inx-1)).get(codeseg[i])+";";
				}
			}else{*/
			String current_func=null; 
			for(String key: symbol_map.keySet()){
				if(symbol_map.get(key).symbol_hash_table.containsKey(codeseg[i])){
					if(key.equals(parsing_function)){
						current_func=key;
						break;
					}
				}
			}
			if(current_func==null){
				for(String key: symbol_map.keySet()){
					if(symbol_map.get(key).symbol_hash_table.containsKey(codeseg[i])){
						if(key.equals(parsing_block)){
							current_func=key;
							break;
						}
					}
				}
			}
			if(current_func==null){
				current_func="GLOBAL";
			}
			if(current_func.equals("GLOBAL")){
				if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("INT")){
					//System.out.println(";WRITEI "+codeseg[i]);
					code_list=code_list+"WRITEI "+codeseg[i]+";";
				}else if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("FLOAT")){
					//System.out.println(";WRITEF "+codeseg[i]);
					code_list=code_list+"WRITEF "+codeseg[i]+";";
				}
				else if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("STRING")){
					//System.out.println(";WRITES "+codeseg[i]);
					code_list=code_list+"WRITES "+codeseg[i]+";";
				}
			}else{
				if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("INT")){
					//System.out.println(";WRITEI "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName());
					code_list=code_list+"WRITEI "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName()+";";
				}else if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("FLOAT")){
					//System.out.println(";WRITEF "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName());
					code_list=code_list+"WRITEF "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName()+";";
				}
				else if(symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getType().equals("STRING")){
					//System.out.println(";WRITES "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName());
					code_list=code_list+"WRITES "+symbol_map.get(current_func).symbol_hash_table.get(codeseg[i]).getName()+";";
				}
			}
		}
	}
	public static void IF_IR(String cond){ //generate IR for IF
		Pattern condp = Pattern.compile("[^!=<>]+([!=<>]+)[^!=<>]+");
		Matcher condp_matcher = condp.matcher(cond);
		parsing_block="BLOCK"+(parsing_block_ct++);
		if(condp_matcher.matches()){
			if_ct++;
			if_stack.push(if_ct);
			if(intfloat==0){
				if(condp_matcher.group(1).equals(">")){
					//System.out.println(";LEI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"LEI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals(">=")){
					//System.out.println(";LTI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"LTI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("<")){
					//System.out.println(";GEI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"GEI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("<=")){
					//System.out.println(";GTI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"GTI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("!=")){
					//System.out.println(";EQI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"EQI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("=")){
					//System.out.println(";NEI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"NEI "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}
			}else{
				if(condp_matcher.group(1).equals(">")){
					//System.out.println(";LEF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"LEF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals(">=")){
					//System.out.println(";LTF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"LTF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("<")){
					//System.out.println(";GEF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"GEF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("<=")){
					//System.out.println(";GTF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"GTF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("!=")){
					//System.out.println(";EQF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"EQF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}else if(condp_matcher.group(1).equals("=")){
					//System.out.println(";NEF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct));
					code_list=code_list+"NEF "+"$T"+(regcnt-1)+" $T"+regcnt+" IFLABEL"+(if_ct)+";";
				}
			}
		}else{
			System.out.println("error while matching op in IF");
		}
	}
	public static void IF_LABEL(String elsestatement){ //IR label END_IF
		if(!elsestatement.equals("")){
			int a = else_stack.pop();
			//System.out.println(";LABEL IFLABEL"+ (a));
			code_list=code_list+"LABEL IFLABEL"+ (a)+";";
			if_ct++;
		}else{
			//System.out.println(elsestatement+" AAAAA");
			int a=if_stack.pop();
			//System.out.println(";LABEL IFLABEL"+ a);
			code_list=code_list+"LABEL IFLABEL"+a+";";
		}
	}
	public static void ELSE_LABEL(){ //IR label ELSE
		parsing_block="BLOCK"+(parsing_block_ct++);
		//System.out.println(";JUMP IFLABEL"+ (if_ct+1)); //jump out of IF
		code_list=code_list+"JUMP IFLABEL"+ (if_ct+1)+";";
		int a=if_stack.pop();
		//System.out.println(";LABEL IFLABEL"+ (a));
		code_list=code_list+"LABEL IFLABEL"+ (a)+";";
		if_ct++;
		else_stack.push(if_ct);
	}
	public static void WHILE_LABEL(){
		parsing_block="BLOCK"+(parsing_block_ct++);
		while_ct++;
		while_stack.push(while_ct);
		//System.out.println(";LABEL WHILELABEL" + while_ct);
		code_list=code_list+"LABEL WHILELABEL" + while_ct +";";
	}
	public static void WHILE_IR(String cond){
		Pattern condp = Pattern.compile("[^!=<>]+([!=<>]+)[^!=<>]+");
		Matcher condp_matcher = condp.matcher(cond);
		if(condp_matcher.matches()){
			while_ct++;
			while_stack.push(while_ct);
			if(intfloat==0){
				if(condp_matcher.group(1).equals(">")){
					//System.out.println(";LEI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"LEI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals(">=")){
					//System.out.println(";LTI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"LTI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("<")){
					//System.out.println(";GEI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"GEI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("<=")){
					//System.out.println(";GTI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"GTI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("!=")){
					//System.out.println(";EQI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"EQI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("=")){
					//System.out.println(";NEI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"NEI "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}
			}else{
				if(condp_matcher.group(1).equals(">")){
					//System.out.println(";LEF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"LEF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals(">=")){
					//System.out.println(";LTF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"LTF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("<")){
					//System.out.println(";GEF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"GEF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("<=")){
					//System.out.println(";GTF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"GTF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("!=")){
					//System.out.println(";EQF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"EQF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}else if(condp_matcher.group(1).equals("=")){
					//System.out.println(";NEF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct));
					code_list=code_list+"NEF "+"$T"+(regcnt-1)+" $T"+regcnt+" WHILELABEL"+(while_ct)+";";
				}
			}
		}else{
			System.out.println("error while matching op in WHILE");
		}
	}
	public static void ENDWHILE_LABEL(){
		int a=while_stack.pop();
		int b=while_stack.pop();
		//System.out.println(";JUMP WHILELABEL" + (b));
		code_list=code_list+"JUMP WHILELABEL" + (b)+";";
		//System.out.println(";LABEL WHILELABEL" + a);
		code_list=code_list+"LABEL WHILELABEL" + (a)+";";
	}
	public static void FUNCTION_HEAD_IR(String name){
		parsing_function=name;
		//System.out.println(";LABEL"+" "+name);
		if(name.equals("main")){
			code_list=code_list+"LABEL"+" "+name+";";
		}else{
			code_list=code_list+"LABEL"+" "+name+";";
		}
		//System.out.println(";LINK");
		code_list=code_list+"LINK"+";";
	}
	public static void FUNCTION_RETURN_IR(String func_name){
		func_name=parsing_function;
		//System.out.println(";MOVE $T"+regcnt+" $R");
		code_list=code_list+"MOVE $T"+regcnt+" $R"+";";
		//System.out.println(";RET");
		code_list=code_list+"RET"+";";
	}
	public static void pre_func_call(){
		//System.out.println(";PUSH");
		code_list=code_list+"PUSH"+";";
	}
	public static void eval_func_para(){
		Pattern reg=Pattern.compile("\\$T([0-9]+)");
		ASTnode node=node_stack.pop();
		if(node.name.equals("+")||node.name.equals("/")||node.name.equals("*")||node.name.equals("-")){
			postorder_IR(node);
		}
		intfloat=node.i_fchk;
		String scope=null;
		for(String key:symbol_map.keySet()){
			//System.out.println(key+" "+parsing_function+" "+node.name);
			if(symbol_map.get(key).symbol_hash_table.containsKey(node.name)&&key.equals(parsing_function)){
				scope=key;
				break;
			}
		}
			if(scope==null){
				scope="GLOBAL";
			}
			try{
				Matcher reg_matcher=reg.matcher(node.name);
				if(reg_matcher.matches()){
					//System.out.println(";PUSH $T"+regcnt);
					code_list=code_list+"PUSH $T"+regcnt+";";
				}else{
					//System.out.println(";PUSH "+node.name);
					code_list=code_list+"PUSH "+node.name+";";//.symbol_map.get(scope).symbol_hash_table.get(node.name).getName()
				}
			}catch(Exception e){
				System.out.println("ERROR: "+node.name+" does not appear in any scope");
				System.exit(1);
			}
		int addnum=addnum_stack.pop();
		addnum=0;
		addnum_stack.push(addnum);
	}
	public static void FUNCTION_CALL_IR(String func_name,String para_list){
		String [] para_arr = para_list.split(",");
		int para_list_len=0;
		//calling_function=func_name;

		if(!para_arr[0].equals("")){
			para_list_len=para_arr.length;
		}
		//System.out.println(";PUSH");
		//code_list=code_list+"PUSH"+";";
		/*String scope=null;
		for(int i=0;i<para_list_len;i++){
			for(String key:symbol_map.keySet()){
				if(symbol_map.get(key).symbol_hash_table.containsKey(para_arr[i])){
					scope=key;
				}
			}
			if(scope==null){
				scope="GLOBAL";
			}
			try{
				System.out.println(";PUSH "+symbol_map.get(scope).symbol_hash_table.get(para_arr[i]).getName());
				code_list=code_list+"PUSH "+symbol_map.get(scope).symbol_hash_table.get(para_arr[i]).getName()+";";
			}catch(Exception e){
				System.out.println("ERROR: "+para_arr[i]+" does not appear in any scope");
				System.exit(1);
			}
		}*/
		//System.out.println(";JSR "+func_name);
		code_list=code_list+"JSR "+func_name+";";
		for(int i=0;i<para_list_len;i++){
			//System.out.println(";POP");
			code_list=code_list+"POP"+";";
		}
		regcnt++;
		//System.out.println(";POP "+"$T"+regcnt);
		code_list=code_list+"POP "+"$T"+regcnt+";";
		add_ASTnode("$T"+regcnt,1,0,0,0);//need to specify type
	}
	public static void asm_gen(String code){
		boolean storeiflag=false;boolean multiflag=false;
		boolean storefflag=false;boolean multfflag=false;
		boolean addiflag=false;boolean diviflag=false;
		boolean addfflag=false;boolean divfflag=false;
		boolean subiflag=false;
		boolean subfflag=false;
		parsing_block_ct=1;
		//for(int i=0; i<symbol_list.size();i++){
			//if(symbol_map.get(i).getName().equals("GLOBAL")){
				for(int j=0; j<symbol_map.get("GLOBAL").symbol_list_table.size();j++){
					if(symbol_map.get("GLOBAL").symbol_list_table.get(j).getType()=="STRING"){
						System.out.println("str "+symbol_map.get("GLOBAL").symbol_list_table.get(j).getName()+" "+symbol_map.get("GLOBAL").symbol_list_table.get(j).getValue());
					}else{
						System.out.println("var "+symbol_map.get("GLOBAL").symbol_list_table.get(j).getName());
					}
				}
			//}
		//}
			System.out.println("push");
			System.out.println("jsr main");
		    System.out.println("sys halt");
		if(code!=null){
			String [] codeline = code.split(";");
			for(int i=0;i<codeline.length;i++){
				System.out.println(";"+codeline[i]);
				String [] codeseg=codeline[i].split(" ");
				//System.out.println(codeline[i]);
				if(codeseg.length==4){
					inst_gen(codeseg[0],codeseg[1],codeseg[2],codeseg[3]);
				}else if(codeseg.length==3){
					inst_gen(codeseg[0],codeseg[1],null,codeseg[2]);
				}
				else if (codeseg.length==2){
					//System.out.println(codeseg[0]+codeseg[1]);
					inst_gen(codeseg[0],null,null,codeseg[1]);
				}else if(codeseg.length==1){
					inst_gen(codeseg[0],null,null,null);
				}
			}
		}
	}
	/*public static void inst_gen(String inst,String src1, String src2, String dest){
		//Matcher num_matcher=num.matcher(dest);
		Pattern num=Pattern.compile("([0-9]+)||([0-9]*\\.[0-9]+)");
		Pattern reg=Pattern.compile("\\$T([0-9]+)");
		Pattern id=Pattern.compile("[a-zA-Z]([a-zA-Z]|[0-9])*");	
		//Pattern lreg=Pattern.compile("\\$L([0-9]+)");
		Pattern lpreg=Pattern.compile("\\$[PL]([0-9]+)"); 
		String output1=null; String output2=null;
		String output3=null; String output4=null;
		if(src2==null&&src1!=null){//move only
			Matcher src1_num_matcher=num.matcher(src1);
			Matcher src1_reg_matcher=reg.matcher(src1);
			Matcher src1_id_matcher=id.matcher(src1);
			Matcher src1_lpreg_matcher=lpreg.matcher(src1);
			Matcher dest_reg_matcher=reg.matcher(dest);
			Matcher dest_id_matcher=id.matcher(dest);
			Matcher dest_lpreg_matcher=lpreg.matcher(dest);
			if(src1_lpreg_matcher.matches()){
				output1=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src1);
			}else if(src1_reg_matcher.matches()){ //matches reg
				output1="r"+src1_reg_matcher.group(1);
			}else if(src1_id_matcher.matches()||src1_num_matcher.matches()){ //matches id num
				output1=src1;
			}else{
				System.out.println("error while matching scr1");
			}
			if(dest_lpreg_matcher.matches()){
				output2=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(dest);
			}else if(dest_reg_matcher.matches()){
				output2="r"+dest_reg_matcher.group(1);
			}else if(dest_id_matcher.matches()){
				output2=dest;
			}else if(dest.equals("$R")){
				String calling = calling_function_stack.pop();
				output2=(String)function_list.get(calling).get("return_address");
				calling_function_stack.push(calling);
			}else{
				System.out.println("error while matching dest");
			}
			System.out.println("move "+output1+" "+output2);
		}else if(src1!=null&&src2!=null){
			Matcher src1_num_matcher=num.matcher(src1);
			Matcher src1_reg_matcher=reg.matcher(src1);
			Matcher src1_id_matcher=id.matcher(src1);
			//Matcher src1_lreg_matcher=lreg.matches(src1);
			Matcher src1_lpreg_matcher=lpreg.matcher(src1);
			Matcher src2_num_matcher=num.matcher(src2);
			Matcher src2_reg_matcher=reg.matcher(src2);
			Matcher src2_id_matcher=id.matcher(src2);
			//Matcher src2_lreg_matcher=lreg.matches(src2);
			Matcher src2_lpreg_matcher=lpreg.matcher(src2);
			Matcher dest_reg_matcher=reg.matcher(dest);
			//Matcher dest_lreg_matcher=lreg.matches(dest);
			Matcher dest_lpreg_matcher=lpreg.matcher(dest);
			Matcher dest_id_matcher=id.matcher(dest);
			if(inst.equals("ADDI")||inst.equals("ADDF")||inst.equals("SUBI")||inst.equals("SUBF")||inst.equals("MULTI")||inst.equals("MULTF")||inst.equals("DIVI")||inst.equals("DIVF")){
				if(src1_reg_matcher.matches()){
					output1="r"+src1_reg_matcher.group(1);
				}else if(src1_id_matcher.matches()){
					output1=src1;
				}else if(src1_num_matcher.matches()){
					output1=src1;
				}else if(src1_lpreg_matcher.matches()){
					output1=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src1);
				}else{
					System.out.println("error during matching src1");
				}
				if(src2_reg_matcher.matches()){
					output3="r"+src2_reg_matcher.group(1);
				}else if(src2_id_matcher.matches()){
					output3=src2;
				}else if(src2_num_matcher.matches()){
					output3=src2;
				}else if(src2_lpreg_matcher.matches()){
					output3=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src2);
				}else{
					System.out.println("error during matching src2");
				}
				if(dest_reg_matcher.matches()){
					output2="r"+dest_reg_matcher.group(1);
					output4="r"+dest_reg_matcher.group(1);
				}else if(dest_lpreg_matcher.matches()){
					output2=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(dest);
					output4=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(dest);
				}else{
					System.out.println("error during matching dest");
				}
				System.out.println("move "+output1+" "+output2);
				if(inst.equals("ADDI")){
					System.out.println("addi "+output3+" "+output4);
				}else if(inst.equals("ADDF")){
					System.out.println("addr "+output3+" "+output4);
				}else if(inst.equals("SUBI")){
					System.out.println("subi "+output3+" "+output4);
				}else if(inst.equals("SUBF")){
					System.out.println("subr "+output3+" "+output4);
				}else if(inst.equals("MULTI")){
					System.out.println("muli "+output3+" "+output4);
				}else if(inst.equals("MULTF")){
					System.out.println("mulr "+output3+" "+output4);
				}else if(inst.equals("DIVI")){
					System.out.println("divi "+output3+" "+output4);
				}else if(inst.equals("DIVF")){
					System.out.println("divr "+output3+" "+output4);
				}
			}else if(inst.equals("GTI")||inst.equals("GEI")||inst.equals("LTI")||inst.equals("LEI")||inst.equals("NEI")||inst.equals("EQI")||inst.equals("GTF")||inst.equals("GEF")||inst.equals("LTF")||inst.equals("LEF")||inst.equals("NEF")||inst.equals("EQF")){
				curr_block = "BLOCK"+(parsing_block_ct++);
				if(src1_reg_matcher.matches()){
					output1="r"+src1_reg_matcher.group(1);
				}else if(src1_lpreg_matcher.matches()){
					output1=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src1);
				}
				if(src2_reg_matcher.matches()){
					output2="r"+src2_reg_matcher.group(1);
				}else if(src2_lpreg_matcher.matches()){
					output2=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src2);
				}
				if(inst.equals("GTI")){//integer compare
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jgt "+dest);
				}else if(inst.equals("LTI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jlt "+dest);
				}else if(inst.equals("GEI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jge "+dest);
				}else if(inst.equals("LEI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jle "+dest);
				}else if(inst.equals("EQI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jeq "+dest);
				}else if(inst.equals("NEI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jne "+dest);
				}else if(inst.equals("GTF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jgt "+dest);
				}else if(inst.equals("LTF")){//float compare
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jlt "+dest);
				}else if(inst.equals("GEF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jge "+dest);
				}else if(inst.equals("LEF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jle "+dest);
				}else if(inst.equals("EQF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jeq "+dest);
				}else if(inst.equals("NEF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jne "+dest);
				}
			}
		}else if(src1==null&&src2==null&&dest!=null){
			Matcher dest_reg_matcher=reg.matcher(dest);
			Matcher dest_id_matcher=id.matcher(dest);
			Matcher dest_lpreg_matcher=lpreg.matcher(dest);
			Matcher dest_num_matcher=num.matcher(dest);
			if(inst.equals("JUMP")){
				if(dest_id_matcher.matches()){
					System.out.println("jmp "+dest);
				}else{
					System.out.println("error while jump");
				}
			}else if(inst.equals("JSR")){
				if(dest_id_matcher.matches()){
					System.out.println("jsr "+dest);
				}else{
					System.out.println("error while jsr");
				}
			}else if(inst.equals("LABEL")){
				if(dest_id_matcher.matches()){
					if(function_list.containsKey(dest)){
						if(!calling_function_stack.empty()){
							calling_function_stack.pop();
						}
						calling_function_stack.push(dest);//push function name to stack
					}
					System.out.println("label "+dest);
				}else{
					System.out.println("error while label");
				}
			}else if(inst.equals("PUSH")){
				if(dest_id_matcher.matches()){
					System.out.println("push "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("push r"+dest_reg_matcher.group(1));
				}else if(dest_num_matcher.matches()){
					System.out.println("push "+dest);
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("push "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while push");
				}
			}else if(inst.equals("POP")){
				if(dest_id_matcher.matches()){
					System.out.println("pop "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("pop r"+dest_reg_matcher.group(1));
				}else if(dest_num_matcher.matches()){
					System.out.println("pop "+dest);
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("pop "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while pop");
				}
			}else if(inst.equals("READI")){
				if(dest_id_matcher.matches()){
					System.out.println("sys readi "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys readi r"+dest_reg_matcher.group(1));
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys readi "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while readi");
				}
			}else if(inst.equals("READF")){
				if(dest_id_matcher.matches()){
					System.out.println("sys readr "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys readr r"+dest_reg_matcher.group(1));
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys readr "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while readr");
				}
			}
			else if(inst.equals("WRITEI")){
				if(dest_id_matcher.matches()){
					System.out.println("sys writei "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys writei r"+dest_reg_matcher.group(1));
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys writei "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while writei");
				}
			}else if(inst.equals("WRITEF")){
				if(dest_id_matcher.matches()){
					System.out.println("sys writer "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys writer r"+dest_reg_matcher.group(1));
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys writer "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while writer");
				}
			}else if(inst.equals("WRITES")){
				if(dest_id_matcher.matches()){
					System.out.println("sys writes "+dest);
				}else{
					System.out.println("error while writes");
				}
			}
		}else if(dest==null){
			if(inst.equals("LINK")){
				System.out.println("link "+function_list.get(function_name_list.get(curr_func_inx++)).get("link_num"));
			}else if(inst.equals("RET")){
				//calling_function_stack.pop();//pop from stack, only pop once
				System.out.println("unlnk\nret");
			}else if(inst.equals("PUSH")){
				System.out.println("push");
			}else if(inst.equals("POP")){
				System.out.println("pop");
			}
		}
	}*/
	public static void init_reg(){
		ArrayList<LinkedHashMap<String,String>> registers = new ArrayList<LinkedHashMap<String,String>>();
		LinkedHashMap<String,String> reg = new LinkedHashMap<String,String>();
		reg.put("name","");
		reg.put("dirty","no");
		reg.put("free","yes");
		registers.add(reg);
		LinkedHashMap<String,String> reg2 = new LinkedHashMap<String,String>();
		reg2.put("name","");
		reg2.put("dirty","no");
		reg2.put("free","yes");
		registers.add(reg2);
		LinkedHashMap<String,String> reg3 = new LinkedHashMap<String,String>();
		reg3.put("name","");
		reg3.put("dirty","no");
		reg3.put("free","yes");
		registers.add(reg3);
		LinkedHashMap<String,String> reg4 = new LinkedHashMap<String,String>();
		reg4.put("name","");
		reg4.put("dirty","no");
		reg4.put("free","yes");
		registers.add(reg4);
		register_stack.push(registers);
	}
	public static String ensure(String temp){
		ArrayList<LinkedHashMap<String,String>> registers = register_stack.pop();
		for(int i=0;i<registers.size();i++){
			if(registers.get(i).get("name").equals(temp)){
				register_stack.push(registers);
				return ("r"+i);
			}
		}
		register_stack.push(registers);
		return "ensure fail";
	}
	public static String regalloc(String temp){//1=ensure+alloc 2=alloc
		ArrayList<LinkedHashMap<String,String>> registers = register_stack.pop();
		for(int i=0;i<registers.size();i++){
			if(registers.get(i).get("free").equals("yes")){
				registers.get(i).put("free","no");
				registers.get(i).put("name",temp);
				register_stack.push(registers);
				return ("r"+i);
			}
		}
		register_stack.push(registers);
		return "alloc fail "+temp;
	}
	public static void free(String temp){
		ArrayList<LinkedHashMap<String,String>> registers = register_stack.pop();
		for(int i=0;i<registers.size();i++){
			if(registers.get(i).get("name").equals(temp)){
				registers.get(i).put("free","yes");
				register_stack.push(registers);
				return;
			}				
		}
		register_stack.push(registers);
	}
	public static void inst_gen(String inst,String src1, String src2, String dest){
		//Matcher num_matcher=num.matcher(dest);
		Pattern num=Pattern.compile("([0-9]+)||([0-9]*\\.[0-9]+)");
		Pattern reg=Pattern.compile("\\$T([0-9]+)");
		Pattern id=Pattern.compile("[a-zA-Z]([a-zA-Z]|[0-9])*");	
		//Pattern lreg=Pattern.compile("\\$L([0-9]+)");
		Pattern lpreg=Pattern.compile("\\$[PL]([0-9]+)"); 
		String output1=null; String output2=null;
		String output3=null; String output4=null;
		if(src2==null&&src1!=null){//move only
			Matcher src1_num_matcher=num.matcher(src1);
			Matcher src1_reg_matcher=reg.matcher(src1);
			Matcher src1_id_matcher=id.matcher(src1);
			Matcher src1_lpreg_matcher=lpreg.matcher(src1);
			Matcher dest_reg_matcher=reg.matcher(dest);
			Matcher dest_id_matcher=id.matcher(dest);
			Matcher dest_lpreg_matcher=lpreg.matcher(dest);
			if(src1_lpreg_matcher.matches()){
				output1=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src1);
			}else if(src1_reg_matcher.matches()){ //matches reg
				output1=ensure(src1);
				free(src1);
			}else if(src1_id_matcher.matches()||src1_num_matcher.matches()){ //matches id num
				output1=src1;
			}else{
				System.out.println("error while matching scr1");
			}
			if(dest_lpreg_matcher.matches()){
				output2=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(dest);
			}else if(dest_reg_matcher.matches()){
				output2=regalloc(dest);
			}else if(dest_id_matcher.matches()){
				output2=dest;
			}else if(dest.equals("$R")){
				String calling = calling_function_stack.pop();
				output2=(String)function_list.get(calling).get("return_address");
				calling_function_stack.push(calling);
			}else{
				System.out.println("error while matching dest");
			}
			System.out.println("move "+output1+" "+output2);
		}else if(src1!=null&&src2!=null){
			Matcher src1_num_matcher=num.matcher(src1);
			Matcher src1_reg_matcher=reg.matcher(src1);
			Matcher src1_id_matcher=id.matcher(src1);
			//Matcher src1_lreg_matcher=lreg.matches(src1);
			Matcher src1_lpreg_matcher=lpreg.matcher(src1);
			Matcher src2_num_matcher=num.matcher(src2);
			Matcher src2_reg_matcher=reg.matcher(src2);
			Matcher src2_id_matcher=id.matcher(src2);
			//Matcher src2_lreg_matcher=lreg.matches(src2);
			Matcher src2_lpreg_matcher=lpreg.matcher(src2);
			Matcher dest_reg_matcher=reg.matcher(dest);
			//Matcher dest_lreg_matcher=lreg.matches(dest);
			Matcher dest_lpreg_matcher=lpreg.matcher(dest);
			Matcher dest_id_matcher=id.matcher(dest);
			if(inst.equals("ADDI")||inst.equals("ADDF")||inst.equals("SUBI")||inst.equals("SUBF")||inst.equals("MULTI")||inst.equals("MULTF")||inst.equals("DIVI")||inst.equals("DIVF")){
				if(src1_reg_matcher.matches()){
					output1=ensure(src1);
				}else if(src1_id_matcher.matches()){
					output1=src1;
				}else if(src1_num_matcher.matches()){
					output1=src1;
				}else if(src1_lpreg_matcher.matches()){
					output1=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src1);
				}else{
					System.out.println("error during matching src1");
				}
				if(src2_reg_matcher.matches()){
					output3=ensure(src2);
				}else if(src2_id_matcher.matches()){
					output3=src2;
				}else if(src2_num_matcher.matches()){
					output3=src2;
				}else if(src2_lpreg_matcher.matches()){
					output3=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src2);
				}else{
					System.out.println("error during matching src2");
				}
				if(dest_reg_matcher.matches()){
					output2=regalloc(dest);
					output4=output2;
				}else if(dest_lpreg_matcher.matches()){
					output2=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(dest);
					output4=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(dest);
				}else{
					System.out.println("error during matching dest");
				}
				free(src1);free(src2);
				System.out.println("move "+output1+" "+output2);
				if(inst.equals("ADDI")){
					System.out.println("addi "+output3+" "+output4);
				}else if(inst.equals("ADDF")){
					System.out.println("addr "+output3+" "+output4);
				}else if(inst.equals("SUBI")){
					System.out.println("subi "+output3+" "+output4);
				}else if(inst.equals("SUBF")){
					System.out.println("subr "+output3+" "+output4);
				}else if(inst.equals("MULTI")){
					System.out.println("muli "+output3+" "+output4);
				}else if(inst.equals("MULTF")){
					System.out.println("mulr "+output3+" "+output4);
				}else if(inst.equals("DIVI")){
					System.out.println("divi "+output3+" "+output4);
				}else if(inst.equals("DIVF")){
					System.out.println("divr "+output3+" "+output4);
				}
			}else if(inst.equals("GTI")||inst.equals("GEI")||inst.equals("LTI")||inst.equals("LEI")||inst.equals("NEI")||inst.equals("EQI")||inst.equals("GTF")||inst.equals("GEF")||inst.equals("LTF")||inst.equals("LEF")||inst.equals("NEF")||inst.equals("EQF")){
				curr_block = "BLOCK"+(parsing_block_ct++);
				if(src1_reg_matcher.matches()){
					output1=ensure(src1);
				}else if(src1_lpreg_matcher.matches()){
					output1=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src1);
				}
				if(src2_reg_matcher.matches()){
					output2=ensure(src2);

				}else if(src2_lpreg_matcher.matches()){
					output2=(String)function_list.get(function_name_list.get(curr_func_inx-1)).get(src2);
				}
				free(src1);free(src2);
				if(inst.equals("GTI")){//integer compare
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jgt "+dest);
				}else if(inst.equals("LTI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jlt "+dest);
				}else if(inst.equals("GEI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jge "+dest);
				}else if(inst.equals("LEI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jle "+dest);
				}else if(inst.equals("EQI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jeq "+dest);
				}else if(inst.equals("NEI")){
					System.out.println("cmpi "+output1+" "+output2);
					System.out.println("jne "+dest);
				}else if(inst.equals("GTF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jgt "+dest);
				}else if(inst.equals("LTF")){//float compare
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jlt "+dest);
				}else if(inst.equals("GEF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jge "+dest);
				}else if(inst.equals("LEF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jle "+dest);
				}else if(inst.equals("EQF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jeq "+dest);
				}else if(inst.equals("NEF")){
					System.out.println("cmpr "+output1+" "+output2);
					System.out.println("jne "+dest);
				}
			}
		}else if(src1==null&&src2==null&&dest!=null){
			Matcher dest_reg_matcher=reg.matcher(dest);
			Matcher dest_id_matcher=id.matcher(dest);
			Matcher dest_lpreg_matcher=lpreg.matcher(dest);
			Matcher dest_num_matcher=num.matcher(dest);
			if(inst.equals("JUMP")){
				if(dest_id_matcher.matches()){
					System.out.println("jmp "+dest);
				}else{
					System.out.println("error while jump");
				}
			}else if(inst.equals("JSR")){
				if(dest_id_matcher.matches()){
					System.out.println("jsr "+dest);
				}else{
					System.out.println("error while jsr");
				}
			}else if(inst.equals("LABEL")){
				if(dest_id_matcher.matches()){
					if(function_list.containsKey(dest)){
						if(!calling_function_stack.empty()){
							calling_function_stack.pop();
						}
						calling_function_stack.push(dest);//push function name to stack
					}
					System.out.println("label "+dest);
				}else{
					System.out.println("error while label");
				}
			}else if(inst.equals("PUSH")){
				if(dest_id_matcher.matches()){
					System.out.println("push "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("push "+ensure(dest));
					free(dest);
				}else if(dest_num_matcher.matches()){
					System.out.println("push "+dest);
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("push "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while push");
				}
			}else if(inst.equals("POP")){
				if(dest_id_matcher.matches()){
					System.out.println("pop "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("pop "+regalloc(dest));
				}else if(dest_num_matcher.matches()){
					System.out.println("pop "+dest);
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("pop "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while pop");
				}
			}else if(inst.equals("READI")){
				if(dest_id_matcher.matches()){
					System.out.println("sys readi "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys readi "+regalloc(dest));
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys readi "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while readi");
				}
			}else if(inst.equals("READF")){
				if(dest_id_matcher.matches()){
					System.out.println("sys readr "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys readr "+regalloc(dest));
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys readr "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while readr");
				}
			}
			else if(inst.equals("WRITEI")){
				if(dest_id_matcher.matches()){
					System.out.println("sys writei "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys writei "+ensure(dest));
					free(dest);
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys writei "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while writei");
				}
			}else if(inst.equals("WRITEF")){
				if(dest_id_matcher.matches()){
					System.out.println("sys writer "+dest);
				}else if(dest_reg_matcher.matches()){
					System.out.println("sys writer "+ensure(dest));
					free(dest);
				}else if(dest_lpreg_matcher.matches()){
					System.out.println("sys writer "+function_list.get(function_name_list.get(curr_func_inx-1)).get(dest));
				}else{
					System.out.println("error while writer");
				}
			}else if(inst.equals("WRITES")){
				if(dest_id_matcher.matches()){
					System.out.println("sys writes "+dest);
				}else{
					System.out.println("error while writes");
				}
			}
		}else if(dest==null){
			if(inst.equals("LINK")){
				if(!register_stack.empty()){
					register_stack.pop();
				}
				System.out.println("link "+function_list.get(function_name_list.get(curr_func_inx++)).get("link_num"));
				init_reg();//new register stack
			}else if(inst.equals("RET")){
				//calling_function_stack.pop();//pop from stack, only pop once
				System.out.println("unlnk\nret");
			}else if(inst.equals("PUSH")){
				System.out.println("push");
			}else if(inst.equals("POP")){
				System.out.println("pop");
			}
		}
	}
    public static void create_function_list(String name, String para_list, String return_type){
    	LinkedHashMap<String,String> this_function_list = new LinkedHashMap<String,String>();
    	String para[] = para_list.split(",");
    	int paras=para.length;
    	int linknum=0;
    	int included_ct=0;
    	Pattern parap=Pattern.compile("\\$P([0-9]+)");
    	Pattern localp=Pattern.compile("\\$L([0-9]+)");
    	int pntct=1;
    	int pntct2=-1;
    	if(para[0].equals("")){
    		paras=0;
    	}
    	pntct=(paras+1);
    	int locals = symbol_map.get(name).symbol_list_table.size()-paras;
    	/*if(!name.equals("main")){
    		linknum=locals+1;
    	}else{
    		linknum=locals;
    	}*/
    	linknum=locals;
    	//System.out.println(name+" has "+paras+" input parameters and "+locals+" local variables");
    	this_function_list.put("input_para_num",Integer.toString(paras));
    	this_function_list.put("local_var_num",Integer.toString(locals));
    	this_function_list.put("link_num",Integer.toString(linknum));
    	this_function_list.put("return_type",return_type);
    	function_name_list.add(name);
    	this_function_list.put("return_address","$"+Integer.toString(pntct+1));
    	for(String key: symbol_map.get(name).symbol_hash_table.keySet()){
    		//function_name_list.add(name);
    		Matcher param = parap.matcher(symbol_map.get(name).symbol_hash_table.get(key).getName());
    		Matcher localm = localp.matcher(symbol_map.get(name).symbol_hash_table.get(key).getName());
    		if(param.matches()){
    			this_function_list.put(symbol_map.get(name).symbol_hash_table.get(key).getName(),"$"+Integer.toString(pntct--));//between fp and sp
    		}else if(localm.matches()){
    			this_function_list.put(symbol_map.get(name).symbol_hash_table.get(key).getName(),"$"+Integer.toString(pntct2--));//before fp
    		}
    	}
    	this_function_list.put("last_local",Integer.toString(pntct2));
    	/*for(String key: this_function_list.keySet()){
    		System.out.println(key+":"+this_function_list.get(key));
    	}*/
    	function_list.put(name,this_function_list);
    }
    public static void put_local_var(String code){
    	int ct=0;
    	if(code!=null&&!code.equals("")){
    		String [] codeline = code.split(";");
    		for(int i=0; i<codeline.length;i++){
    			String [] pre = codeline[i].split("INT");
    			String [] var = pre[1].split(",");
    			int pntct2 = 0;
    			int linknum=0;
    			pntct2 = Integer.parseInt((String)function_list.get(parsing_function).get("last_local"));
    			for(int j=0;j<var.length;j++){
    				//System.out.println(parsing_function+" "+symbol_map.get(parsing_block).symbol_hash_table.get(var[j]).getName()+" "+"$"+pntct2);
    				function_list.get(parsing_function).put(symbol_map.get(parsing_block).symbol_hash_table.get(var[j]).getName(),"$"+Integer.toString(pntct2--));
    				linknum = Integer.parseInt((String)function_list.get(parsing_function).get("link_num"))+1;
    				function_list.get(parsing_function).put("link_num",Integer.toString(linknum));
    			}
    		}
    	}
    }
	private static void view_tree(ASTnode head){//in order
		if (head.left==null){
			System.out.print(head.name);
			return;
		}else if(head.right==null){
			System.out.print(head.name);
			return;
		}
		System.out.print(head.name);
		view_tree(head.left);
		//System.out.print(head.name);
		view_tree(head.right);
		//System.out.print(head.name);
	}
	public static String Type(int type){
		String typestr = "";
		if (type==3){
			typestr = "IDENTIFIER";
		}else if(type==4){
			typestr = "INTLITERAL";
		}
		else if(type==5){
			typestr = "FLOATLITERAL";
		}else if(type==6){
			typestr = "STRINGLITERAL";
		}else if(type==2){
			typestr = "KEYWORD";
		}else if(type==7){
			typestr = "OPERATOR";
		}else if(type==8){
			typestr = "COMMENT";
		}
		return typestr;
	}
}
