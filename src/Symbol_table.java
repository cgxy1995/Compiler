import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
public class Symbol_table
{
	public static Stack<Symbol_block> symbol_stack = new Stack<Symbol_block>();
	public static ArrayList<Symbol_block> symbol_list = new ArrayList<Symbol_block>();
	public static LinkedHashMap<String,Symbol_block> symbol_map = new LinkedHashMap<String,Symbol_block>();
	private static int scp_ct=1;
	private static String _scope="";
	private static int local_num=1;
	private static int para_num=1;
	private static String curr_func = null;
	public static void add_global(){
		Symbol_block a = new Symbol_block("GLOBAL");
		local_num=1;
		para_num=1;
		set_scope("GLOBAL");
		symbol_stack.push(a);
		//symbol_list.add(a);
		symbol_map.put("GLOBAL",a);
	}
	public static void add_block(String name){
		Symbol_block a = new Symbol_block("BLOCK "+Integer.toString(scp_ct));
		//Symbol_block a = new Symbol_block(curr_func);
		//local_num=1;
		//para_num=1;
		set_scope(name+Integer.toString(scp_ct));
		symbol_stack.push(a);
		//symbol_list.add(a);
		symbol_map.put("BLOCK"+Integer.toString(scp_ct++),a);
	}
	public static void add_function(String name){
		Symbol_block a = new Symbol_block(name);
		local_num=1;
		curr_func=name;
		set_scope(name);
		symbol_stack.push(a);
		//symbol_list.add(a);
		symbol_map.put(name,a);
	}
	public static void set_scope(String s){
		if(s.equals("GLOBAL")){
			_scope=s;
		}else{
			_scope=s+Integer.toString(scp_ct);
		}
	}
	public static void add_variable(String name, String type, String value, String scope){
		Symbol_block a = symbol_stack.pop();
		Pattern blockp = Pattern.compile("((WHILE)|(IF))[0-9]+");
		Matcher blockm = blockp.matcher(_scope);
		if(_scope.equals("GLOBAL")){
			local_num = a.add_symbol(name,type,value,_scope,0,curr_func,local_num);
		}else if(scope.equals("function_decl")){
			local_num =a.add_symbol(name,type,value,_scope,1,curr_func,local_num);
		}else{
			if(blockm.matches()){
				local_num =a.add_symbol(name,type,value,_scope,3,curr_func,local_num);//var in IF and WHILE
			}else{
				local_num =a.add_symbol(name,type,value,_scope,2,curr_func,local_num);
			}
		}
		symbol_stack.push(a);
	}
	public static void print_scope(){
		Symbol_block a = symbol_stack.pop();
		a.print_content();
		symbol_stack.push(a);
	}
	public static void pop_scope(){
		Symbol_block a = symbol_stack.pop();
		//a.print_content();
	}
	public static void view_blocks(){
		for (int i=0; i<symbol_list.size();i++){
			System.out.println(symbol_list.get(i).getName());
		}
	}

}
class Symbol_block{
	private String name;
	public LinkedHashMap<String,Symbol> symbol_hash_table = new LinkedHashMap<String, Symbol>();
	public ArrayList<String> var_names = new ArrayList<String>();
	public ArrayList<Symbol> symbol_list_table = new ArrayList<Symbol>();
	//private int local_num;
	private int para_num;
	public Symbol_block(String name){
		this.name=name;
		this.para_num=1;
	}
	public String getName(){
		return this.name;
	}
	public void print_content(){
		System.out.println("Symbol table "+this.name);
		for(int i=0;i<var_names.size();i++){
			symbol_list_table.get(i).print_content();
		}
		System.out.println();
	}
	public int add_symbol(String name, String type, String value, String scope,int ctrl, String curr_func,int local_num){
		String[] names = name.split(",");
		for(int i=0; i<names.length;i++){
			if(var_names.contains(names[i])){
				System.out.println("DECLARATION ERROR "+name);
				System.exit(1);
			}else{
				Symbol a=null;
				if(ctrl==0){
					a = new Symbol(names[i],type,value,scope,null);
					symbol_hash_table.put(names[i],a);
				}else if(ctrl==1){
					a = new Symbol("$P"+Integer.toString(para_num++),type,value,scope,null);
					symbol_hash_table.put(names[i],a);
				}else if(ctrl==2){
					a = new Symbol("$L"+Integer.toString(local_num++),type,value,scope,null);
					symbol_hash_table.put(names[i],a);
				}
				else if(ctrl==3){
					a = new Symbol("$L"+Integer.toString(local_num++),type,value,scope,curr_func);
					//System.out.println("test "+curr_func);
					symbol_hash_table.put(names[i],a);
				}
				var_names.add(names[i]);
				symbol_list_table.add(a);
			}
		}
		return local_num;
	}
}
class Symbol{
	private String name;
	private String type;
	private String value;
	private String scope;
	private String IR;
	public String includedBy = null;
	public Symbol(String name, String type, String value, String scope, String includedBy){
		this.name=name;
		this.type=type;
		this.value=value;
		this.scope=scope;
		this.includedBy = includedBy;
	}
	public void print_content(){
		if(this.type.equals("STRING")){
			System.out.println("name "+this.name+" type "+"STRING value "+this.value); //+this.value+" scope "+this.scope
		}else{
			System.out.println("name "+this.name+" type "+this.type);
		}
	}
	public String getName(){
		return this.name;
	}
	public String getType(){
		return this.type;
	}
	public String getValue(){
		return this.value;
	}
	public String getScope(){
		return this.scope;
	}
}