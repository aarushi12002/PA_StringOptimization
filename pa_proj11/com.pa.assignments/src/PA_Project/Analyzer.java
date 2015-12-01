package PA_Project;



import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.Body;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.AssignExpr;
import soot.toolkits.graph.DominatorNode;
import soot.toolkits.graph.DominatorTree;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.util.Chain;
import soot.BodyTransformer;
import soot.Local;
import soot.PatchingChain;
import soot.SootMethod;
import soot.Unit;
import soot.UnitBox;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeStmt;


import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.thread.mhp.DominatorsFinder;
import soot.toolkits.scalar.FlowSet;

public class Analyzer extends BodyTransformer {
	
	Analyzer(){
		
	}
	public static int count = 0;
	public static Map<String, ArrayList<Unit>> SCB = new HashMap<String, ArrayList<Unit>>();
	public static  Map<String, Integer> loopCond = new HashMap<String, Integer>();
	
	public static ArrayList<String> orderedScbs = new ArrayList<String>();
	public static Map<String, ArrayList<String>> preds = new HashMap<String, ArrayList<String>>();
	public static Map<String, String> doms = new HashMap<String, String>();
	public static ArrayList<Unit> stmts = null ;
	
	protected void internalTransform(Body body, String arg1, Map arg2) {
		if(count<1){
		ExceptionalUnitGraph g=new ExceptionalUnitGraph(body);
		//System.out.println(g);
		//MHGDominatorsFinder dominator = new MHGDominatorsFinder(g);
		//System.out.println(dominator);
		
		PatchingChain<Unit> u = body.getUnits();
		ArrayList<String> listOfLabels = new ArrayList<String>();
	
		String stringAssignedToVar = null;
		String lastStringBufferStmt = null;
		int conditionalLoop = 0;
		boolean forLoopFlag = false;
		boolean ifFlag = false;
	
		int goto2=0;
		int nop2=0;
		int gotoCount = 0;
		int noOpCount = 0;
		Unit gotoLabel = null;
		
		String returnedImmediateDom = null;
		for(Unit un : u){
			//System.out.println("dom "+ un+ "  :"+dominator.getDominators(un));
			Stmt s = (Stmt) un;
			//System.out.println("For STatement "+s+" goto count "+gotoCount+" nop count "+noOpCount);
			
				
		if(s instanceof IfStmt) {
			
			
			Unit nop = g.getPredsOf(un).get(0);
			
			if(g.getPredsOf(nop).size()>1) {
				gotoLabel = nop;
				forLoopFlag = true;
				System.out.println("this is the statement "+s+" where if flag is false");
			} else {
				{
					ifFlag = true;
				}
			}
			//System.out.println(g.getSuccsOf(gotoLabel));
			
					
		}
		if (gotoLabel!=null) {
			//
			if(un instanceof GotoStmt) {
				//System.out.println("yayyy goto "+ un);
				
				System.out.println("target "+ ((GotoStmt) un).getTarget());
			Unit unit = ((GotoStmt) un).getTarget();
			if(unit.equals(gotoLabel)) {
				System.out.println("here "+gotoLabel);
				forLoopFlag = false;
				conditionalLoop = 0;
			//conditionalLoop = 2;
			//checkAndModifyBits(loopCond, forLoop, gotoLabel);
			}
			}
		}
		if((forLoopFlag == true)&&(ifFlag==false) ) {
			conditionalLoop =2;
		} else if(ifFlag==true && forLoopFlag==true) {
			//System.out.println("Inside for and if : unit "+ un+" ; nop count "+noOpCount+" gotocOUNT"+gotoCount);
			//ifFlag=false;
			conditionalLoop = 4;
			if(nop2==2)
			{
				ifFlag=false;
				conditionalLoop=2;//can reset nop2 and goto2 here
			}
			if(un.toString().equals("nop"))
			{
				System.out.println("found nop has predsize="+g.getPredsOf(un).size()+" and nop2"+nop2);
				
				if(g.getPredsOf(un).size()>1) 
				{
					if(nop2==1)
					{
						System.out.println("preds are "+g.getPredsOf(un).get(0).toString()+" and "+g.getPredsOf(un).get(1).toString());
						if(g.getPredsOf(un).get(0).toString().equals("nop")||g.getPredsOf(un).get(1).toString().equals("nop"))
								nop2++;
					}
					if((nop2==0))
					{
						System.out.println("preds are "+g.getPredsOf(un).get(0).toString()+" and "+g.getPredsOf(un).get(1).toString());
						
						if(!(g.getPredsOf(un).get(0).toString().equals("nop")&&!(g.getPredsOf(un).get(1).toString().equals("nop"))))
							nop2++;
					}
				}
					
				
				
				
			}
			
		} else if(ifFlag ==true && forLoopFlag==false) {
			if(un.toString().equals("nop")){
				noOpCount++;
				if(noOpCount>gotoCount){
					conditionalLoop = 0;
					ifFlag=false;
					gotoCount=0;
					noOpCount=0;
				}
			}

			if(un.toString().equals("goto [?= nop]")) {
					conditionalLoop = 1;
					gotoCount++;
				} 
		} 
		
			//System.out.println("unit "+ un);
			if(s instanceof AssignStmt && lastStringBufferStmt!=null && (un.toString().contains(lastStringBufferStmt))) {
				//System.out.println("yayaya "+ un);
				Iterator box=un.getDefBoxes().iterator();
				ValueBox vb = null;
				while(box.hasNext()) {
					Object m = box.next();
					 vb=(ValueBox) m;
					 stringAssignedToVar = vb.getValue().toString();	
					 String scbIdentifier = stringAssignedToVar+lastStringBufferStmt;
					 SCB.put(scbIdentifier, stmts);
					 orderedScbs.add(scbIdentifier);
					 loopCond.put(scbIdentifier, conditionalLoop);
					// forLoop.put(scbIdentifier, gotoLabel);
					 if(returnedImmediateDom == null) {
						 //System.out.println(returnedImmediateDom);
						 doms.put(stringAssignedToVar+lastStringBufferStmt, stringAssignedToVar+lastStringBufferStmt);
					 } else {
						 //System.out.println(returnedImmediateDom);
						 doms.put(stringAssignedToVar+lastStringBufferStmt, returnedImmediateDom);
					 }
					// System.out.println("dominator for scb"+scbIdentifier+" are "+recursDominator(un, g));
				}
			}
			//System.out.println(un);
			if(un.toString().contains("new java.lang.StringBuffer")) {
				
				stmts = new ArrayList<Unit>();
				returnedImmediateDom = recursDominator(un, g);
				//System.out.println(un);
				stmts.add(un);
			}
			if(un.toString().contains("java.lang.StringBuffer:") && 
					!(un.toString().contains("java.lang.StringBuffer: java.lang.String toString()"))) {
				stmts.add(un);
			}
		
			
			if(un.toString().contains("java.lang.StringBuffer: java.lang.String toString()")) {
				stmts.add(un);
				ValueBox vb = null;
				
				Iterator box=un.getDefBoxes().iterator();
				while(box.hasNext()) {
					Object m = box.next();
					 vb=(ValueBox) m;
					 		
				}
				lastStringBufferStmt = vb.getValue().toString();
			}
			
			
			
			//if(g.getPredsOf(un).size()>=2)
			
			//System.out.println(g);
		}
		getIncomingEdges();
		System.out.println("ordered scbs are "+orderedScbs);
		System.out.println(" ");
		System.out.println(" ");
		System.out.println("Final SCB bits are ");
		System.out.println(loopCond);
		System.out.println(" ");
		System.out.println(" ");
		System.out.println("SCB predecessors are ");
		for(String key: preds.keySet()) {
			System.out.println(key+" ----- "+preds.get(key));
		}
		System.out.println(" ");
		System.out.println(" ");
		System.out.println("dominators are "+doms);
		System.out.println(" ");
		System.out.println(" ");
		//Implementing the Reaching definition relation analysis algorithm
		rdra();
		
		
		
		count++;
		
		}
}
	
	public static void rdra()
	{
		for(String key: preds.keySet()) 
		{
			if(preds.get(key).size()==1)
			{
				if(preds.get(key).get(0).equals(key)||!(preds.get(key).get(0).equals(doms.get(key))))
					System.out.println("Looping case");
				else if(preds.get(key).get(0).equals(doms.get(key)))
						System.out.println("scb "+key+" is redundant.Can use scb "+doms.get(key));
			}
			else if(preds.get(key).size()>1)
			{
				//System.out.println(" checking for key "+key);
				HashMap<String,Integer> unique=new HashMap<String,Integer>();
				for(String pred: preds.get(key))
				{
					String dom_of_pred=doms.get(pred);
					if(unique.containsKey(dom_of_pred))
						unique.put(dom_of_pred, unique.get(dom_of_pred)+1);
					else
						unique.put(dom_of_pred,0);
				}
				if(unique.keySet().size()==1)
					System.out.println("scb "+key+" is redundant.Can use scb"+unique.keySet());
				else
					System.out.println("scb "+key+" should be created");
			}
			else
				System.out.println("scb "+key+" should be created");
		}
	}
	public static String recursDominator(Unit unit, ExceptionalUnitGraph graph ) {
		MHGDominatorsFinder dominator = new MHGDominatorsFinder(graph);
		//System.out.println("dom "+ unit+ "  :"+dominator.getDominators(unit));
		//System.out.println("dom size "+ dominator.getDominators(unit).size());
		//List dom = dominator.getDominators(unit);
		String lastStringBufferStmt = null; 
		String stringAssignedToVar = null;
		//System.out.println("this is the unit "+ unit);
		for(int i=0; i<dominator.getDominators(unit).size(); i++) {
			//System.out.println("Et tu brute? "+ o);
			
			Unit un = (Unit)dominator.getDominators(unit).get(i);
			//System.out.println("who is John Galt "+un);
			Stmt s = (Stmt)un;
			if(un.toString().contains("java.lang.StringBuffer: java.lang.String toString()")) {
				//System.out.println(un+" yat" );
				//stmts.add(un);
				ValueBox vb = null;
				
				Iterator box=un.getDefBoxes().iterator();
				while(box.hasNext()) {
					Object m = box.next();
					 vb=(ValueBox) m;
					 		
				}
				lastStringBufferStmt = vb.getValue().toString();
				//return true;
			}
			
			if(s instanceof AssignStmt && lastStringBufferStmt!=null && (un.toString().contains(lastStringBufferStmt)) ) {
				//System.out.println("yayaya "+ un);
				Iterator box=un.getDefBoxes().iterator();
				ValueBox vb = null;
				while(box.hasNext()) {
					Object m = box.next();
					 vb=(ValueBox) m;
					 stringAssignedToVar = vb.getValue().toString();	
					 //doms.put(unit, stringAssignedToVar+lastStringBufferStmt);
					 
					// SCB.put(stringAssignedToVar+lastStringBufferStmt+conditionalLoop, stmts);
				}
				//return true;
			}
			
			
		}
		if(stringAssignedToVar==null) {
			return null;
		}
		
		String immediateDomSCB =  stringAssignedToVar+lastStringBufferStmt;
		return immediateDomSCB;
	}
	

	
	public static void getIncomingEdges() {
		String firstScb = orderedScbs.get(0);
		//the first scb has no predecessors and so, an empty list
		preds.put(firstScb, new ArrayList<String>());
		
		for(int i=1; i<orderedScbs.size(); i++) 
		{
			String scb = orderedScbs.get(i);
			String scbPred1 = orderedScbs.get(i-1);
			//System.out.println("for node "+scb+" its pred is "+scbPred1);
			ArrayList<String> predec = new ArrayList<String>();
			
			if (loopCond.get(scb)==0) 
			{
				if(loopCond.get(scbPred1)==1) 
				{
					if(i>2 && loopCond.get(orderedScbs.get(i-2))==1) 
					{
						predec.add(orderedScbs.get(i-2));
					} 
					predec.add(scbPred1);
				} 
				else if(loopCond.get(scbPred1)==2)
				{
					predec.add(scbPred1);
					int j=i-2;
					while(loopCond.get(orderedScbs.get(j))>1)
						j--;
					//System.out.println("I IS "+i+" and j is "+j);
					if(loopCond.get(orderedScbs.get(j))==1)
					{
						predec.add(orderedScbs.get(j));
						if(loopCond.get(orderedScbs.get(j-1))<=1)//before loop an if-else or just an if- //not if & elseif
						{
							predec.add(orderedScbs.get(j-1));
						}
					}
					else if(loopCond.get(orderedScbs.get(j))==0)
						predec.add(orderedScbs.get(j));
						
				}
				else if(loopCond.get(scbPred1)==4)
				{
					//add case for 244[here 0 can have 4 preds] and 44[here 0 can have 3preds] here
				}
				else //if pred is 0
				{
					predec.add(scbPred1);
				}
			} 
			else if(loopCond.get(scb)==1) 
			{
				if(loopCond.get(scbPred1)==0) 
				{
					predec.add(scbPred1);
				} 
				else if(i>=2 && loopCond.get(orderedScbs.get(i-1))==1) //or if(loopCond.get(scbPred1)==1) 
				{
					predec.add(orderedScbs.get(i-2));
					
				} 
				else if(loopCond.get(scbPred1)==2)
				{
					predec.add(scbPred1);
					int j=i-2;
					while(loopCond.get(orderedScbs.get(j))>1)
						j--;
					if(loopCond.get(orderedScbs.get(j))==1)
					{
						predec.add(orderedScbs.get(j));
						if(loopCond.get(orderedScbs.get(j-1))<=1)//before loop an if-else or just an if- //not if & elseif
						{
							predec.add(orderedScbs.get(j-1));
						}
					}
					else if(loopCond.get(orderedScbs.get(j))==0)
						predec.add(orderedScbs.get(j));
				}
				else if(loopCond.get(scbPred1)==4)
				{
					//add case for 244[here 1 can have 4 preds] and 44[here 1 can have 3preds] here
				}
			}
			else if(loopCond.get(scb)==2) 
			{
				if(loopCond.get(scbPred1)<2) 
				{
					predec.add(scbPred1);
					if(loopCond.get(scbPred1)==1)
					{
						if(i>2 && loopCond.get(orderedScbs.get(i-2))==1) 
						{
							predec.add(orderedScbs.get(i-2));
						} 
					}
					int j=i;
					while((j+1<orderedScbs.size())&&(loopCond.get(orderedScbs.get(j))>=2)&&(loopCond.get(orderedScbs.get(j+1))>=2))
					{
						j++;
					}
					if(loopCond.get(orderedScbs.get(j))==4&&loopCond.get(orderedScbs.get(j-1))==4)
					{
						predec.add(orderedScbs.get(j-1));
						predec.add(orderedScbs.get(i));
					}
					predec.add(orderedScbs.get(j));
				} 
				else if(loopCond.get(scbPred1)==4)
				{ System.out.println("we are here");
					int j=i-1;
					while(j>=0 ) 
					{System.out.println("came here "+ orderedScbs.get(j));
						predec.add(orderedScbs.get(j));
						if(loopCond.get(orderedScbs.get(j))<=2) {
							
							predec.add(orderedScbs.get(--j));
						}
						if(loopCond.get(orderedScbs.get(j))<=2)
							break;
						j--;	
					} 
				}
				else
					predec.add(scbPred1);
			}
			else if(loopCond.get(scb)==4) 
			{
				System.out.println("for node "+scb+" its pred has "+loopCond.get(scbPred1));
				if(loopCond.get(scbPred1)<2)
				{
					predec.add(scbPred1);
					if(loopCond.get(scbPred1)==1)
					{
						if(i>2 && loopCond.get(orderedScbs.get(i-2))==1) 
						{
							predec.add(orderedScbs.get(i-2));
						} 
					}
					int j=i;
					while((j+1<orderedScbs.size())&&(loopCond.get(orderedScbs.get(j))>=2)&&(loopCond.get(orderedScbs.get(j+1))>=2))
					{
						j++;
					}
					predec.add(orderedScbs.get(j));
				}
				else if(loopCond.get(scbPred1)==4)
				{
					if(i>=2 && loopCond.get(orderedScbs.get(i-2))<2) 
					{
						predec.add(orderedScbs.get(i-2));
						System.out.println("Added for "+orderedScbs.get(i)+" scb "+orderedScbs.get(i-2));
						if(loopCond.get(orderedScbs.get(i-2))==1)
							predec.add(orderedScbs.get(i-3));
						
						int j=i;
						while((j+1<orderedScbs.size())&&(loopCond.get(orderedScbs.get(j))>=2)&&(loopCond.get(orderedScbs.get(j+1))>=2))
						{
							j++;
						}
						if(j!=i)
						predec.add(orderedScbs.get(j));
						else
							predec.add(orderedScbs.get(j-1));
					} 
					else if(i>=2 && loopCond.get(orderedScbs.get(i-2))==2)
						predec.add(orderedScbs.get(i-2));
				}
				else
					predec.add(scbPred1);
			}
			preds.put(scb, predec);
		}
		
	}
	
}