import java.util.*;
public class ASTnode
{
    public String name;
    public String code;
    public int LR;//0=L 1=R 2=constant 3=op
    public float floatvalue=0;
    public int intvalue=0;
    public ASTnode left =null;
    public ASTnode right =null;
    public int i_fchk=0;
    public ASTnode(String name,int LR,int intvalue,float floatvalue,int i_fchk){
    	this.name=name;
    	this.LR=LR;
        this.intvalue=intvalue;
        this.floatvalue=floatvalue;
        this.i_fchk=i_fchk;
    }
    public void printname(){
    	System.out.println(name);
    }
}	