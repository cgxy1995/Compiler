import java.util.*;
public class IRnode{
	public String code;
	public ArrayList<IRnode> predecessors;
	public ArrayList<IRnode> successors;
	public ArrayList<String> liveness;
	public IRnode(String code){
		this.code = code;
		this.predecessors = new ArrayList<IRnode>();
		this.successors = new ArrayList<IRnode>();
		this.liveness = new ArrayList<String>();
	}
	public void addpredecessor(IRnode node){
		predecessors.add(node);
	}
	public void addsuccessor(IRnode node){
		successors.add(node);
	}
	public void addliveness(String var){
		liveness.add(var);
	}
	public void removeliveness(String var){
		liveness.remove(var);
	}
	public void update_liveness(ArrayList<String> curr_liveness){
		for(int i=0;i<curr_liveness.size();i++){
			if(!this.liveness.contains(curr_liveness.get(i))){
				this.liveness.add(curr_liveness.get(i));
			}
		}
	}
}