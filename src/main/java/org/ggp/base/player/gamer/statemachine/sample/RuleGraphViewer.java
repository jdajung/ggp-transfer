package org.ggp.base.player.gamer.statemachine.sample;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Paint;
import java.awt.Shape;
import java.awt.geom.AffineTransform;
import java.awt.geom.Ellipse2D;
import java.awt.geom.Point2D;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import javax.imageio.ImageIO;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.algorithms.layout.CircleLayout;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.SparseGraph;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.BasicVisualizationServer;
import edu.uci.ics.jung.visualization.VisualizationImageServer;

public class RuleGraphViewer {

	private ArrayList<RuleNode> ruleNodes;
	private ArrayList<Integer> drawIds;

	public static final int DRAW_WIDTH = 2000;
	public static final String[] INDEX_COLOURS = new String[]{
	        "#000000", "#FFFF00", "#1CE6FF", "#FF34FF", "#FF4A46", "#008941", "#006FA6", "#A30059",
	        "#FFDBE5", "#7A4900", "#0000A6", "#63FFAC", "#B79762", "#004D43", "#8FB0FF", "#997D87",
	        "#5A0007", "#809693", "#FEFFE6", "#1B4400", "#4FC601", "#3B5DFF", "#4A3B53", "#FF2F80",
	        "#61615A", "#BA0900", "#6B7900", "#00C2A0", "#FFAA92", "#FF90C9", "#B903AA", "#D16100",
	        "#DDEFFF", "#000035", "#7B4F4B", "#A1C299", "#300018", "#0AA6D8", "#013349", "#00846F",
	        "#372101", "#FFB500", "#C2FFED", "#A079BF", "#CC0744", "#C0B9B2", "#C2FF99", "#001E09",
	        "#00489C", "#6F0062", "#0CBD66", "#EEC3FF", "#456D75", "#B77B68", "#7A87A1", "#788D66",
	        "#885578", "#FAD09F", "#FF8A9A", "#D157A0", "#BEC459", "#456648", "#0086ED", "#886F4C",

	        "#34362D", "#B4A8BD", "#00A6AA", "#452C2C", "#636375", "#A3C8C9", "#FF913F", "#938A81",
	        "#575329", "#00FECF", "#B05B6F", "#8CD0FF", "#3B9700", "#04F757", "#C8A1A1", "#1E6E00",
	        "#7900D7", "#A77500", "#6367A9", "#A05837", "#6B002C", "#772600", "#D790FF", "#9B9700",
	        "#549E79", "#FFF69F", "#201625", "#72418F", "#BC23FF", "#99ADC0", "#3A2465", "#922329",
	        "#5B4534", "#FDE8DC", "#404E55", "#0089A3", "#CB7E98", "#A4E804", "#324E72", "#6A3A4C",
	        "#83AB58", "#001C1E", "#D1F7CE", "#004B28", "#C8D0F6", "#A3A489", "#806C66", "#222800",
	        "#BF5650", "#E83000", "#66796D", "#DA007C", "#FF1A59", "#8ADBB4", "#1E0200", "#5B4E51",
	        "#C895C5", "#320033", "#FF6832", "#66E1D3", "#CFCDAC", "#D0AC94", "#7ED379", "#012C58"
	};

	public RuleGraphViewer(final RuleGraph ruleGraph) {
		this.ruleNodes = ruleGraph.getGraph();
		this.drawIds = ruleGraph.getTopLevelNonVarIds();
	}

	public RuleGraphViewer(final RuleGraphRecord record) {
		this.ruleNodes = record.getGraph();
		this.drawIds = record.getTopLevelNonVarIds();
	}

	public static String cleanName(String origName) {
		String outStr = "";
		for(char c : origName.toCharArray()) {
			if(c == '?') {
				outStr += "var_";
			} else if(c == '[') {
				outStr += "_";
			} else if(c == ']') {
				//pass
			} else {
				outStr += c;
			}
		}
		return outStr;
	}

	//generate drawings around all top level nodes in the rule graph up to a distance, dist
	public void drawTopLevel(int dist, String dirString) {
		drawAroundNodes(drawIds, dist, dirString);
	}

	//generate a drawing for each node in nodeIDs, up to a distance, dist
	public void drawAroundNodes(List<Integer> nodeIDs, int dist, String dirString) {
		for(int currID : nodeIDs) {
			int edgeNum = 0;

	        // Create a graph with Integer vertices and String edges
	        Graph<Integer, Integer> g = new SparseGraph<Integer, Integer>();
	        Queue<Pair<Integer,Integer>> q = new LinkedList<Pair<Integer,Integer>>(); //key in pair is depth, value is id in ruleGraph
	        q.add(new Pair<Integer,Integer>(0, currID));
	        RuleNode currRoot = ruleNodes.get(currID);

	        while(!q.isEmpty()) {
	        	Pair<Integer,Integer> currPair = q.remove();
	        	int depth = currPair.getKey();
	        	int pairID = currPair.getValue();
	        	RuleNode currNode = ruleNodes.get(pairID);
	        	for(RuleNode currChild : currNode.getChildren()) {
	        		if(!g.containsVertex(currChild.getId())) {
	        			g.addVertex(currChild.getId());
	        		}
	        		if(g.findEdge(currNode.getId(), currChild.getId()) == null) {
	        			g.addEdge(edgeNum, currNode.getId(), currChild.getId(), EdgeType.DIRECTED);
	        			edgeNum++;
	        		}
	        		if(depth < dist) {
		        		Pair<Integer,Integer> newPair = new Pair<Integer,Integer>(depth+1, currChild.getId());
		        		q.add(newPair);
	        		}
	        	}
	        	for(RuleNode currParent : currNode.getParents()) {
	        		if(!g.containsVertex(currParent.getId())) {
	        			g.addVertex(currParent.getId());
	        		}
	        		if(g.findEdge(currParent.getId(), currNode.getId()) == null) {
	        			g.addEdge(edgeNum, currParent.getId(), currNode.getId(), EdgeType.DIRECTED);
	        			edgeNum++;
	        		}
	        		if(depth < dist) {
		        		Pair<Integer,Integer> newPair = new Pair<Integer,Integer>(depth+1, currParent.getId());
		        		q.add(newPair);
	        		}
	        	}
	        }

	        drawSaveJungGraph(g, dirString + RuleGraphViewer.cleanName(currRoot.getName()));
		}
	}


	//do all the drawing and save to saveLoc, given a completed JUNG graph, g
	public void drawSaveJungGraph(Graph<Integer,Integer> g, String saveLoc) {
        // Layout implements the graph drawing logic
        Layout<Integer, Integer> layout = new CircleLayout<Integer, Integer>(g);
        layout.setSize(new Dimension(DRAW_WIDTH,DRAW_WIDTH));

        // VisualizationServer actually displays the graph
        BasicVisualizationServer<Integer,Integer> vv = new BasicVisualizationServer<Integer,Integer>(layout);
        vv.setPreferredSize(new Dimension(DRAW_WIDTH + 700,DRAW_WIDTH + 100)); //Sets the viewing area size

        // Transformer maps the vertex number to a vertex property
        Transformer<Integer,Paint> vertexColor = new Transformer<Integer,Paint>() {
            @Override
			public Paint transform(Integer i) {
            	RuleNode node = ruleNodes.get(i);
            	int colourInd = node.getColour().getVal();
                return Color.decode(INDEX_COLOURS[colourInd]);
            }
        };
        Transformer<Integer,Shape> vertexSize = new Transformer<Integer,Shape>(){
            @Override
			public Shape transform(Integer i){
                Ellipse2D circle = new Ellipse2D.Double(-15, -15, 30, 30);
                // in this case, the vertex is twice as large
                if(i == 0) return AffineTransform.getScaleInstance(2, 2).createTransformedShape(circle);
                else return circle;
            }
        };
        Transformer<Integer,String> vertexLabel = new Transformer<Integer,String>(){
            @Override
			public String transform(Integer i){
            	RuleNode node = ruleNodes.get(i);
                return node.shortToString();
            }
        };
        vv.getRenderContext().setVertexFillPaintTransformer(vertexColor);
        vv.getRenderContext().setVertexShapeTransformer(vertexSize);
        vv.getRenderContext().setVertexLabelTransformer(vertexLabel);

        //Shows graph on screen
//	        JFrame frame = new JFrame("Rule Graph");
//	        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
//	        frame.getContentPane().add(vv);
//	        frame.pack();
//	        frame.setVisible(true);

        // save whole image to file
		// Create the VisualizationImageServer
        // vv is the VisualizationViewer containing my graph
		VisualizationImageServer<Integer, Integer> vis = new VisualizationImageServer<Integer, Integer>(vv.getGraphLayout(), vv.getGraphLayout().getSize());

		// Configure the VisualizationImageServer the same way
		// you did your VisualizationViewer. In my case e.g.

		vis.setBackground(Color.WHITE);
		vis.getRenderContext().setVertexFillPaintTransformer(vertexColor);
        vis.getRenderContext().setVertexShapeTransformer(vertexSize);
        vis.getRenderContext().setVertexLabelTransformer(vertexLabel);

		// Create the buffered image
		BufferedImage image = (BufferedImage) vis.getImage(new Point2D.Double(vv.getGraphLayout().getSize().getWidth() / 2, vv.getGraphLayout().getSize().getHeight() / 2),
		    new Dimension(vv.getGraphLayout().getSize()));

		// Write image to a png file
		File outputfile = new File(saveLoc + ".png");

		try {
		    ImageIO.write(image, "png", outputfile);
		} catch (IOException e) {
			System.out.println(e);
		}
	}

	//draw and save the whole rule graph
	public void drawRuleGraph() {
		int edgeNum = 0;

        // Create a graph with Integer vertices and String edges
        Graph<Integer, Integer> g = new SparseGraph<Integer, Integer>();
        for(RuleNode node : this.ruleNodes) {
        	g.addVertex(node.getId());
        }
        for(RuleNode node : this.ruleNodes) {
        	for (RuleNode child : node.getChildren()) {
        		if(g.findEdge(node.getId(), child.getId()) == null) {
	        		g.addEdge(edgeNum, node.getId(), child.getId(), EdgeType.DIRECTED);
	        		edgeNum++;
        		}
        	}
        }

        drawSaveJungGraph(g, "rule_graph");

        //save image to file - but it only saves the part that is visible on screen
        /*
        try
        {
            BufferedImage image = new BufferedImage(frame.getWidth(), frame.getHeight(), BufferedImage.TYPE_INT_RGB);
            Graphics2D graphics2D = image.createGraphics();
            frame.paint(graphics2D);
            ImageIO.write(image,"jpeg", new File("rule_graph.jpeg"));
        }
        catch(Exception exception)
        {
            System.out.println(exception);
        }
        */

        //A different example that didn't work
        /*
        //GraphBuilding gb = new GraphBuilding(); // This builds the graph

        // Layout<V, E>, BasicVisualizationServer<V,E>
        Layout<String, String> layout = new CircleLayout(g);

        layout.setSize(new Dimension(300, 300));
        BasicVisualizationServer<String, String> vv =
            new BasicVisualizationServer<String, String>(layout);
        vv.setPreferredSize(new Dimension(350, 350));

        // Setup up a new vertex to paint transformer...
        Function<String, Paint> vertexPaint = new Function<String, Paint>() {
                @Override
				public Paint apply(String i) {
                return Color.GREEN;
            }
        };

        // Set up a new stroke Transformer for the edges
        float dash[] = {10.0f};
        final Stroke edgeStroke = new BasicStroke(1.0f, BasicStroke.CAP_BUTT,
            BasicStroke.JOIN_MITER, 10.0f, dash, 0.0f);
        Function<String, Stroke> edgeStrokeTransformer =
            new Function<String, Stroke>() {
                @Override
				public Stroke apply(String s) {
                    return edgeStroke;
                }
            };

        vv.getRenderContext().setVertexFillPaintTransformer(vertexPaint);
        vv.getRenderContext().setEdgeStrokeTransformer(edgeStrokeTransformer);
        vv.getRenderContext().setVertexLabelTransformer(new ToStringLabeller());
        vv.getRenderContext().setEdgeLabelTransformer(new ToStringLabeller());
        vv.getRenderer().getVertexLabelRenderer()
             .setPosition(Renderer.VertexLabel.Position.CNTR);

        JFrame frame = new JFrame("Custom Graph View");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        frame.getContentPane().add(vv);
        frame.pack();
        frame.setVisible(true);
		*/
    }
}
