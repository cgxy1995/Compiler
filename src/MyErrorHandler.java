import org.antlr.v4.runtime.*;
import java.io.*;
import java.util.*;
@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class MyErrorHandler extends DefaultErrorStrategy{
	public int ct;
	public MyErrorHandler(){
		super();
		this.ct=0;
	}
	@Override
	public Token recoverInline(Parser parser){
		//System.out.println("Not Accepted1");
		if (this.ct==0){
			System.out.println("Not accepted");
			this.ct++;
		}
		CommonToken t = new CommonToken(1);
		return t;
	}
	@Override
	public void reportError(Parser parser,RecognitionException re){
		//System.out.println("Not Accepted2");
		if (this.ct==0){
			System.out.println("Not accepted");
			this.ct++;
		}
	}
	@Override
	public void reportMissingToken(Parser parser){
		//System.out.println("Not Accepted3");
		if (this.ct==0){
			System.out.println("Not accepted");
			this.ct++;
		}
	}
	@Override
	public void recover(Parser parser,RecognitionException re){
		//System.out.println("Not Accepted4");
		if (this.ct==0){
			System.out.println("Not accepted");
			this.ct++;
		}
	}
	@Override
	public void reportUnwantedToken(Parser parser){
		//System.out.println("Not Accepted5");
		if (this.ct==0){
			System.out.println("Not Accepted");
			this.ct++;
		}
	}
}