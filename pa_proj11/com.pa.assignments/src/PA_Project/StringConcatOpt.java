package PA_Project;


import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import soot.Body;
import soot.Local;
import soot.Value;
import soot.ValueBox;
import soot.jimple.Stmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ArraySparseSet;
import soot.toolkits.scalar.FlowSet;
import soot.toolkits.scalar.ForwardFlowAnalysis;

public class StringConcatOpt extends ForwardFlowAnalysis{

	Body b; int stmtNum = 0;
	public HashMap<String, Integer> mapOfRedefs = new HashMap<String, Integer>();
	public HashSet<String> globalList= new HashSet<String>();
	public HashSet<HashMap<String, Integer>> set = new HashSet<HashMap<String, Integer>>();
	public HashSet<String> SCB = new HashSet<String>();
	
	public StringConcatOpt(UnitGraph graph) {
		super(graph);
		ExceptionalUnitGraph ug=(ExceptionalUnitGraph)graph;
		b=ug.getBody();
		
		doAnalysis();
	}

	@Override
	protected void flowThrough(Object in, Object unit, Object out) {
		
		FlowSet inval=(FlowSet)in;
		FlowSet outval=(FlowSet)out;
		
		
		
		
		Stmt s=(Stmt)unit;
		//System.out.println("this is the statement "+ s.toString());
		inval.copy(outval);
		Iterator box=s.getDefBoxes().iterator();
		while(box.hasNext())
		{
			final ValueBox vb=(ValueBox) box.next();
			//System.out.println("this is the value box "+ vb.toString());
			Value v=vb.getValue();
			//System.out.println("this is the value "+ v);
			//Local used for storing the local var as was done earlier
			if(v instanceof Local)
			{//System.out.println("this is it "+ outval);
				
				outval.add(v);
				if(globalList.contains(v.toString())){
					//System.out.println("redefinition "+ v);
					HashMap<String, Integer> map = new HashMap<String, Integer>();
					
					
				} else {
					if(!(v.toString().contains("$") || !v.toString().equals("this"))) {
						globalList.add(v.toString());
					}
				}
			}
		}
		
	
	
		
	
	}

	@Override
	protected void copy(Object src, Object dst) {
		FlowSet srcSet=(FlowSet)src;
		FlowSet destSet=(FlowSet)dst;
		srcSet.copy(destSet);
		
	}

	@Override
	protected Object entryInitialFlow() {
		// TODO Auto-generated method stub
		return new ArraySparseSet();
	}

	@Override
	protected void merge(Object in1, Object in2, Object out) {
		
		FlowSet inval1=(FlowSet)in1;
		FlowSet inval2=(FlowSet)in2;
		FlowSet outSet=(FlowSet)out;
		inval1.union(inval2, outSet);
		
	}

	@Override
	protected Object newInitialFlow() {
		ArraySparseSet arr = new ArraySparseSet();
		
		return arr;
	}
	
	

}
