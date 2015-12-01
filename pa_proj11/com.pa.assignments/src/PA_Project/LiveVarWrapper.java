package PA_Project;



import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class LiveVarWrapper extends BodyTransformer{

	@Override
	protected void internalTransform(Body b, String phase, Map options) {
		// TODO Auto-generated method stub
		ExceptionalUnitGraph g=new ExceptionalUnitGraph(b);
		LiveVarAnalysis1 live=new LiveVarAnalysis1(g);
	}

}
