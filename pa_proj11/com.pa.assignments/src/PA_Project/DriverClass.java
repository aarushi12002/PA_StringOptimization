package PA_Project;


import java.util.Iterator;
import java.util.Map;

import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.G;
import soot.Local;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SootResolver;
import soot.Transform;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.Chain;

import soot.Pack;



public class DriverClass {
	private static final String SRC_DIR = "C:\\Users\\sunil\\workspace\\com.pa.assignments\\src;";
	 public static void main(String[] args) { 
		 Options.v().setPhaseOption("jb", "use-original-names:true");
		 Options.v().set_src_prec(Options.src_prec_java);
		 Scene.v().setSootClassPath(DriverClass.SRC_DIR+Scene.v().getSootClassPath());
		 System.out.println("Calling jtp");
		 Pack jtp = PackManager.v().getPack("jtp");
		 System.out.println("after pack");
		  jtp.add(new Transform("jtp.myTransform", new LiveVarWrapper()));
		  SootResolver.v().resolveClass("java.lang.CloneNotSupportedException", SootClass.SIGNATURES);
			Options.v().set_output_format(Options.output_format_jimple);
		  soot.Main.main(args);
		 }
	 public static class MyAnalysis /*extends ForwardFlowAnalysis */ {

			public MyAnalysis(ExceptionalUnitGraph exceptionalUnitGraph) {
				//doAnalysis();
			}

		}

}