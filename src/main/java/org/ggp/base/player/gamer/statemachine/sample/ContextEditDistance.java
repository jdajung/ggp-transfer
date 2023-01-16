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
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Random;

import javax.imageio.ImageIO;

import org.apache.commons.collections15.Transformer;
import org.ggp.base.player.gamer.statemachine.sample.RuleGraph.RuleNodeColour;

import edu.uci.ics.jung.algorithms.layout.CircleLayout;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.SparseGraph;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.BasicVisualizationServer;
import edu.uci.ics.jung.visualization.VisualizationImageServer;

public class ContextEditDistance {
	private ArrayList<RuleNode> g1;
	private ArrayList<RuleNode> g2;
	private ArrayList<Integer> g1NonVarSymbols;
	private ArrayList<Integer> g2NonVarSymbols;
	private HashMap<Integer, ContextRuleNode> g1TopNodeTable;
	private HashMap<Integer, ContextRuleNode> g2TopNodeTable;
	private HashMap<String, ContextRuleNode> g1NameTopNodeTable;
	private HashMap<String, ContextRuleNode> g2NameTopNodeTable;
	private HashSet<Integer> g1NumberIDs;
	private List<Pair<Integer,List<Integer>>> g1NumberChains;
	private HashSet<Integer> g2NumberIDs;
	private List<Pair<Integer,List<Integer>>> g2NumberChains;
	private HashMap<Integer, Integer> mapping; //g1 -> g2
	private HashMap<Integer, Integer> revMapping; //g2 -> g1
	private HashMap<Integer, Integer> roleIndexMapping;
	private HashMap<Integer, Integer> revRoleIndexMapping;
	private HashSet<Integer> directedEdges;
	private HashSet<Integer> undirectedEdges;
	private float distVal;

	public static final String DEFAULT_MAPPING_ALG = "two_lines"; //one of: "full_matrix", "two_lines"

	public static final float BIG_NUM = 1000000;
	public static final float FLOAT_TOLERANCE = 0.0000001f;
	public static final float INSERT_EDGE_COST = 1;
	public static final float DELETE_EDGE_COST = 1;
	public static final float INSERT_NODE_COST = 1;
	public static final float DELETE_NODE_COST = 1;
	public static final float MISSING_KNOWN_CHILD_COST = 4;
	public static final float MISSING_KNOWN_PARENT_COST = 4;
	public static final float CHANGE_NODE_COLOUR_COST = BIG_NUM;

	public static final float BASE_CONTEXT_NODE_UNMATCHED_COST = 0.5f; //applies at depth 1
	public static final float BASE_RELATIONSHIP_MISMATCH_COST = 1;
	public static final float DEPTH_REDUCED_RELATIONSHIP_MISMATCH_COST = 0;//2;
	public static final float BASE_CONTEXT_DIF_COST = 1;
	public static final float DEPTH_REDUCED_CONTEXT_DIF_COST = 0;//2;
	public static final float BASE_RELATIONSHIP_UNMATCHED_COST = 1;
	public static final float DEPTH_REDUCED_RELATIONSHIP_UNMATCHED_COST = 0;//2;
	public static final float BASE_ARG_NUM_MISMATCH_COST = 0.1f;
	public static final float DEPTH_REDUCED_ARG_NUM_MISMATCH_COST = 0;//0.2f;
	public static final float ARG_DIST_PROPORTION = 0.5f;
	public static final float USERP_THRESH = 0.02f;

	public static final float AVG_COST_WEIGHT = 0.8f;
	public static final float RAW_NUM_SUCCESSFUL_WEIGHT = 0.18f;
	public static final float UNIQUE_MATCH_WEIGHT = 0.02f;
	public static final float NON_UNIQUE_ASSIGNMENT_PENALTY = 0.1f;
//	public static final float REJECT_MAPPING_THRESHOLD = 1.0f;

	public static final int MAX_EXPAND_DEPTH = 5;
	private static final List<RuleNodeColour> NON_VAR_SYM_COLOURS = Arrays.asList(RuleNodeColour.NON_VAR_SYM_CONST, RuleNodeColour.NON_VAR_SYM_FUNC, RuleNodeColour.NON_VAR_SYM_PROP, RuleNodeColour.NON_VAR_SYM_RELATION);

	public class RelationshipNode {
		private RuleNode node;
		private int depth;
		private int numExpanded;
		private int reachableNodes;
		private RuleNodeColour colour;
		private HashSet<Object> relevantParents;
		private HashSet<Object> relevantChildren;
		private HashSet<Object> relevantSiblings;

		public RelationshipNode(RuleNode node) {
			this.node = node;
			this.depth = ContextEditDistance.MAX_EXPAND_DEPTH+1;
			this.numExpanded = 0;
			this.reachableNodes = 0;
			this.colour = node.getColour();
			this.relevantParents = new HashSet<Object>();
			this.relevantChildren = new HashSet<Object>();
			this.relevantSiblings = new HashSet<Object>();
		}

		public RuleNode getNode() {
			return this.node;
		}

		public int getDepth() {
			return this.depth;
		}

		public void setDepth(int newDepth) {
			this.depth = newDepth;
		}

		public int getNumExpanded() {
			return numExpanded;
		}

		public int getReachableNodes() {
			return reachableNodes;
		}

		public RuleNodeColour getColour() {
			return this.colour;
		}

		public HashSet<Object> getRelevantParents() {
			return relevantParents;
		}

		public HashSet<Object> getRelevantChildren() {
			return relevantChildren;
		}

		public HashSet<Object> getRelevantSiblings() {
			return relevantSiblings;
		}

		public void addRelevantParent(Object o) {
			this.relevantParents.add(o);
		}

		public void addRelevantChild(Object o) {
			this.relevantChildren.add(o);
		}

		public void addRelevantSibling(Object o) {
			this.relevantSiblings.add(o);
		}

		private void addRelevantNode(RuleNode node, HashSet<Object> whichRelevant, HashMap<Integer, RelationshipNode> knownNodes, HashMap<String, ContextRuleNode> nameTable, int depth) {
			if(node.getColour() == RuleNodeColour.PRED_OC || node.getColour() == RuleNodeColour.FN_OC) {
				if(nameTable.containsKey(node.getName())) {
					ContextRuleNode crn = nameTable.get(node.getName());
					whichRelevant.add(crn);
					this.numExpanded++;
				} else {
					//With ContextRuleNodes no longer being made for numbers, this would trigger every time we hit one
//					System.out.println("ERROR: encountered PRED_OC or FN_OC without finding same-named ContextRuleNode while expanding");
				}
			} else {
				RelationshipNode newNode;
				if(knownNodes.containsKey(node.getId())) {
					newNode = knownNodes.get(node.getId());
					if(depth+1 < newNode.getDepth()) {
//						newNode.setDepth(depth+1);
						newNode.expand(knownNodes, nameTable, depth+1);
					}
				} else {
					newNode = new RelationshipNode(node);
					knownNodes.put(node.getId(), newNode);
					newNode.expand(knownNodes, nameTable, depth+1);
					this.numExpanded += newNode.getNumExpanded();
				}
				whichRelevant.add(newNode);
				// HashSet prevents adding duplicates
			}
		}

		public void expand(HashMap<Integer, RelationshipNode> knownNodes, HashMap<String, ContextRuleNode> nameTable, int depth) {
			if(depth < ContextEditDistance.MAX_EXPAND_DEPTH && depth < this.depth) {
				this.depth = depth;
				if(this.colour == RuleNodeColour.PRED_OC || this.colour == RuleNodeColour.FN_OC) {
					if(depth == 1) {
						for(RuleNode child : node.getChildren()) {
							addRelevantNode(child, relevantChildren, knownNodes, nameTable, depth);
						}
						for(RuleNode parent : node.getParents()) {
							if(!ContextEditDistance.NON_VAR_SYM_COLOURS.contains(parent.getColour())) {
								addRelevantNode(parent, relevantParents, knownNodes, nameTable, depth);
							}
							if(parent.getColour() == RuleNodeColour.PRED_OC || parent.getColour() == RuleNodeColour.FN_OC) {
								for(RuleNode sibling : parent.getChildren()) {
									if(sibling.getId() != this.node.getId()) {
										addRelevantNode(sibling, relevantSiblings, knownNodes, nameTable, depth);
									}
								}
							}
						}
					} else {
						System.out.println("ERROR: expanded occurrence node " + this.node.getName() + "at depth > 1");
					}

				} else if(this.colour == RuleNodeColour.VAR_OC) {
					//pass; we won't look beyond the fact that we have some variable here

				} else if(this.colour == RuleNodeColour.ARG) {
					if(depth == 1) { //If this is an initial ARG node, add children. Don't clutter the graph with them if we find an ARG node later.
						for(RuleNode child : node.getChildren()) {
							addRelevantNode(child, relevantChildren, knownNodes, nameTable, depth);
						}
					}
					if(nameTable.containsKey(this.node.getName())) {
						ContextRuleNode crn = nameTable.get(this.node.getName());
						relevantParents.add(crn);
						this.numExpanded++;
					} else {
						System.out.println("ERROR: encountered ARG " + this.node.getName() + " without finding same-named ContextRuleNode while expanding");
					}

				} else if(this.colour == RuleNodeColour.VAR_SYM || ContextEditDistance.NON_VAR_SYM_COLOURS.contains(this.colour)) {
					System.out.println("ERROR: Somehow arrived at a symbol node while expanding RelationshipNode: " + this.node.shortToString());

				} else {
					for(RuleNode child : node.getChildren()) {
						addRelevantNode(child, relevantChildren, knownNodes, nameTable, depth);
					}
					for(RuleNode parent : node.getParents()) {
						addRelevantNode(parent, relevantParents, knownNodes, nameTable, depth);
						if(parent.getColour() == RuleNodeColour.PRED_OC || parent.getColour() == RuleNodeColour.FN_OC) {
							for(RuleNode sibling : parent.getChildren()) {
								if(sibling.getId() != this.node.getId()) {
									addRelevantNode(sibling, relevantSiblings, knownNodes, nameTable, depth);
								}
							}
						}
					}
				}
			}
		}


		//difVector[0] = # of differences
		//difVector[1] = # nodes examined
		//difVector[2] = # nodes successfully matched
		//difVector[3] = # unique colours successfully matched
		private int[] countColourDifs(ArrayList<ContextRuleNode> l1, ArrayList<ContextRuleNode> l2) {
			int[] difVector = new int[4];

			HashMap<Integer,Integer> l1ColourCounts = new HashMap<Integer,Integer>();
			HashMap<Integer,Integer> l2ColourCounts = new HashMap<Integer,Integer>();

			for(ContextRuleNode currNode : l1) {
				int currColour = currNode.getColour();
				if(l1ColourCounts.containsKey(currColour)) {
					l1ColourCounts.replace(currColour, l1ColourCounts.get(currColour)+1);
				} else {
					l1ColourCounts.put(currColour, 1);
				}
			}
			for(ContextRuleNode currNode : l2) {
				int currColour = currNode.getColour();
				if(l2ColourCounts.containsKey(currColour)) {
					l2ColourCounts.replace(currColour, l2ColourCounts.get(currColour)+1);
				} else {
					l2ColourCounts.put(currColour, 1);
				}
			}

			for(int l1Colour : l1ColourCounts.keySet()) {
				if(l2ColourCounts.containsKey(l1Colour)) {
					difVector[0] += Math.abs(l1ColourCounts.get(l1Colour) - l2ColourCounts.get(l1Colour));
					difVector[1] += Math.max(l1ColourCounts.get(l1Colour), l2ColourCounts.get(l1Colour));
					difVector[2] += Math.min(l1ColourCounts.get(l1Colour), l2ColourCounts.get(l1Colour));
					difVector[3] += ContextEditDistance.isUniqueColour(l1Colour)*difVector[2];
				} else {
					difVector[0] += l1ColourCounts.get(l1Colour);
					difVector[1] += l1ColourCounts.get(l1Colour);
				}
			}
			for(int l2Colour : l2ColourCounts.keySet()) {
				if(!l1ColourCounts.containsKey(l2Colour)) { //Don't double count common colours
					difVector[0] += l2ColourCounts.get(l2Colour);
					difVector[1] += l2ColourCounts.get(l2Colour);
				}
			}

			return difVector;
		}


		//costVector[0] = TOTAL cost
		//costVector[1] = # nodes examined
		//costVector[2] = # nodes successfully matched
		//costVector[3] = # unique colours successfully matched
		private float[] mixedNodeListDistance(HashSet<Object> l1, HashSet<Object> l2, HashSet<Integer> l1Visited, HashSet<Integer> l2Visited, HashMap<String, ContextRuleNode> l1NameTable, HashMap<String, ContextRuleNode> l2NameTable, int depth) {
			float[] costVector = new float[4];
			ArrayList<RelationshipNode> l1Relationships = new ArrayList<RelationshipNode>();
			ArrayList<RelationshipNode> l2Relationships = new ArrayList<RelationshipNode>();
			ArrayList<ContextRuleNode> l1Contexts = new ArrayList<ContextRuleNode>();
			ArrayList<ContextRuleNode> l2Contexts = new ArrayList<ContextRuleNode>();

			for(Object child : l1) {
				if(child instanceof RelationshipNode) {
					RelationshipNode typedChild = (RelationshipNode)child;
					if(!l1Visited.contains(typedChild.getNode().getId())) {
						l1Relationships.add(typedChild);
					}
				} else if(child instanceof ContextRuleNode) {
					ContextRuleNode typedChild = (ContextRuleNode)child;
					l1Contexts.add(typedChild);
				} else {
					System.out.println("ERROR: Found node of invalid type while finding distance");
				}
 			}
			for(Object child : l2) {
				if(child instanceof RelationshipNode) {
					RelationshipNode typedChild = (RelationshipNode)child;
					if(!l2Visited.contains(typedChild.getNode().getId())) {
						l2Relationships.add(typedChild);
					}
				} else if(child instanceof ContextRuleNode) {
					ContextRuleNode typedChild = (ContextRuleNode)child;
					l2Contexts.add(typedChild);
				} else {
					System.out.println("ERROR: Found node of invalid type while finding distance");
				}
 			}

			int[] difVector = countColourDifs(l1Contexts, l2Contexts);
			costVector[0] += difVector[0]*(ContextEditDistance.BASE_CONTEXT_DIF_COST + ContextEditDistance.DEPTH_REDUCED_CONTEXT_DIF_COST/(float)(depth+1));
			costVector[1] += difVector[1];
			costVector[2] += difVector[2];
			costVector[3] += difVector[3];

			float[] relationshipVector = relationshipListDistance(l1Relationships, l2Relationships, l1Visited, l2Visited, l1NameTable, l2NameTable, depth);
			costVector[0] += relationshipVector[0];
			costVector[1] += relationshipVector[1];
			costVector[2] += relationshipVector[2];
			costVector[3] += relationshipVector[3];

			return costVector;
		}


		private int mixedNodeListReachable(HashSet<Object> l1, HashSet<Integer> l1Visited, HashMap<String, ContextRuleNode> l1NameTable, HashMap<Integer,Integer> contextReached, int depth) {
			int totalReachable = 0;

			for(Object child : l1) {
				if(child instanceof RelationshipNode) {
					RelationshipNode typedChild = (RelationshipNode)child;
					if(!l1Visited.contains(typedChild.getNode().getId())) {
						typedChild.calcReachableNodes(l1Visited, l1NameTable, contextReached, depth);
						totalReachable += typedChild.getReachableNodes();
					}
				} else if(child instanceof ContextRuleNode) {
					ContextRuleNode typedChild = (ContextRuleNode)child;
					totalReachable++;
					int crnId = typedChild.getBaseNode().getId();
					if(!contextReached.containsKey(crnId)) {
						contextReached.put(crnId, 0);
					}
					contextReached.replace(crnId, contextReached.get(crnId)+1);
				} else {
					System.out.println("ERROR: Found node of invalid type while finding distance");
				}
 			}

			return totalReachable;
		}


		//costVector[0] = average cost/node
		//costVector[1] = # nodes examined
		//costVector[2] = # nodes successfully matched
		//costVector[3] = # unique colours successfully matched
		public float[] distance(RelationshipNode other, HashSet<Integer> thisVisited, HashSet<Integer> otherVisited, HashMap<String, ContextRuleNode> thisNameTable, HashMap<String, ContextRuleNode> otherNameTable, int depth) {
			float[] costVector = new float[4];
			costVector[1] = 1;

			if(this.colour != other.getColour()) {
				costVector[0] += ContextEditDistance.BASE_RELATIONSHIP_MISMATCH_COST + ContextEditDistance.DEPTH_REDUCED_RELATIONSHIP_MISMATCH_COST/(float)(depth+1);
			} else {
				costVector[2] = 1;
				//not possible for a RelationshipNode to be of a unique colour

				if(depth < ContextEditDistance.MAX_EXPAND_DEPTH && (depth == 1 || (this.colour != RuleNodeColour.ARG && other.getColour() != RuleNodeColour.ARG))) {
					thisVisited.add(this.node.getId());
					otherVisited.add(other.getNode().getId());
					float[] childVector = mixedNodeListDistance(this.relevantChildren, other.getRelevantChildren(), thisVisited, otherVisited, thisNameTable, otherNameTable, depth+1);
					float[] parentVector = mixedNodeListDistance(this.relevantParents, other.getRelevantParents(), thisVisited, otherVisited, thisNameTable, otherNameTable, depth+1);
					float[] siblingVector = mixedNodeListDistance(this.relevantSiblings, other.getRelevantSiblings(), thisVisited, otherVisited, thisNameTable, otherNameTable, depth+1);
					thisVisited.remove(this.node.getId());
					otherVisited.remove(other.getNode().getId());

					float totalNodes = childVector[1] + parentVector[1] + siblingVector[1];
					if(totalNodes > ContextEditDistance.FLOAT_TOLERANCE) {
						costVector[0] = childVector[0]/totalNodes + parentVector[0]/totalNodes + siblingVector[0]/totalNodes;
					}
					costVector[1] += totalNodes;
					costVector[2] += childVector[2] + parentVector[2] + siblingVector[2];
					costVector[3] += childVector[3] + parentVector[3] + siblingVector[3];

				} else if(depth < ContextEditDistance.MAX_EXPAND_DEPTH && this.colour == RuleNodeColour.ARG && other.getColour() == RuleNodeColour.ARG) {
					//we have argument nodes, but don't want to expand everything. Just look at their parent ContextRuleNode colour
					if(thisNameTable.containsKey(this.node.getName()) && otherNameTable.containsKey(other.getNode().getName())) {
						ContextRuleNode thisCrn = thisNameTable.get(this.node.getName());
						ContextRuleNode otherCrn = otherNameTable.get(other.getNode().getName());
						costVector[1]++;
						if (this.node.getArgNum() != other.getNode().getArgNum()) {
							costVector[0] += ContextEditDistance.BASE_ARG_NUM_MISMATCH_COST + ContextEditDistance.DEPTH_REDUCED_ARG_NUM_MISMATCH_COST/(float)(depth+1);
						}
						if(thisCrn.getColour() != otherCrn.getColour()) {
							costVector[0] += ContextEditDistance.BASE_CONTEXT_DIF_COST + ContextEditDistance.DEPTH_REDUCED_CONTEXT_DIF_COST/(float)(depth+1);
						} else {
							costVector[2]++;
							costVector[3] += ContextEditDistance.isUniqueColour(thisCrn.getColour());
						}
					} else {
						System.out.println("ERROR: Found argument node without matching ContextRuleNode of same name in distance");
					}
				}
			}

//			System.out.println(costVector[0] + " " + costVector[1] + " " + costVector[2] + " " + costVector[3]);
			return costVector;
		}


		public void calcReachableNodes(HashSet<Integer> thisVisited, HashMap<String, ContextRuleNode> thisNameTable, HashMap<Integer,Integer> contextReached, int depth) {
			this.reachableNodes = 1;

			if(depth < ContextEditDistance.MAX_EXPAND_DEPTH && (depth == 1 || this.colour != RuleNodeColour.ARG)) {
				thisVisited.add(this.node.getId());
				int reachableChildren = mixedNodeListReachable(this.relevantChildren, thisVisited, thisNameTable, contextReached, depth+1);
				int reachableParents = mixedNodeListReachable(this.relevantParents, thisVisited, thisNameTable, contextReached, depth+1);
				int reachableSiblings = mixedNodeListReachable(this.relevantSiblings, thisVisited, thisNameTable, contextReached, depth+1);
				thisVisited.remove(this.node.getId());

				this.reachableNodes += reachableChildren + reachableParents + reachableSiblings;

			} else if(depth < ContextEditDistance.MAX_EXPAND_DEPTH && this.colour == RuleNodeColour.ARG) {
				//we have argument nodes, but don't want to expand everything. Just look at their parent ContextRuleNode colour
				if(thisNameTable.containsKey(this.node.getName())) {
					ContextRuleNode thisCrn = thisNameTable.get(this.node.getName());
					this.reachableNodes += 1;
					int crnId = thisCrn.getBaseNode().getId();
					if(!contextReached.containsKey(crnId)) {
						contextReached.put(crnId, 0);
					}
					contextReached.replace(crnId, contextReached.get(crnId)+1);
				} else {
					System.out.println("ERROR: Found argument node without matching ContextRuleNode of same name in distance");
				}
			}
		}


		public float unmatchedCost(HashSet<Integer> visited, int depth) {
			float cost = ContextEditDistance.BASE_RELATIONSHIP_UNMATCHED_COST + ContextEditDistance.DEPTH_REDUCED_RELATIONSHIP_UNMATCHED_COST/(float)(depth+1);

			return cost;
		}
	}

	public class CostPair<U,V> implements Comparable<Object>{
		private float[] costVector;
		private U first;
		private V second;

		public CostPair(float[] costVector, U first, V second) {
			this.costVector = costVector;
			this.first = first;
			this.second = second;
		}

		public float[] getCostVector() {
			return costVector;
		}

		public U getFirst() {
			return first;
		}

		public V getSecond() {
			return second;
		}

		@Override
		public String toString() {
			return "CostPair [costVector=" + costVector + ", first=" + first + ", second=" + second + "]";
		}

		@Override
		public int compareTo(Object o) {
			int ans = 0;
			if(o instanceof CostPair) {
				CostPair other = (CostPair) o;
//				System.out.println(this.costVector[0] + " - " + other.getCostVector()[0]);
				if(this.costVector[0] - other.getCostVector()[0] < -1*ContextEditDistance.FLOAT_TOLERANCE) {
					ans = -1;
				} else if (this.costVector[0] - other.getCostVector()[0] > ContextEditDistance.FLOAT_TOLERANCE) {
					ans = 1;
				}
			} else {
				System.out.println("ERROR: tried to compare a CostPair to an unknown object: " + o);
			}
			return ans;
		}
	}


	private class ContextRuleNode {
		private RuleNode baseNode;
		private int colour;
		private int numExpanded; //not used for anything important
		private int reachableNodes;
		private int reachableUniques;
		private ArrayList<RelationshipNode> occurrences;
		private ArrayList<RelationshipNode> args;
		private HashMap<Integer,Integer> contextReached;

		public ContextRuleNode(RuleNode baseNode) {
			this.baseNode = baseNode;
			this.colour = baseNode.getColour().getVal();
			this.numExpanded = 0;
			this.reachableNodes = 0;
			this.reachableUniques = 0;
			this.occurrences = new ArrayList<RelationshipNode>();
			this.args = new ArrayList<RelationshipNode>();
			this.contextReached = new HashMap<Integer,Integer>();
		}

		public RuleNode getBaseNode() {
			return baseNode;
		}

		public int getNumExpanded() {
			return numExpanded;
		}

		public int getReachableNodes() {
			return reachableNodes;
		}

		public int getReachableUniques() {
			return reachableUniques;
		}

		public void addReachableUniques(int numUniques) {
			this.reachableUniques += numUniques;
		}

		public int getColour() {
			return colour;
		}

		public void setColour(int newColour) {
			this.colour = newColour;
		}

		public ArrayList<RelationshipNode> getOccurrences() {
			return occurrences;
		}

		public ArrayList<RelationshipNode> getArgs() {
			return args;
		}


		public void uniqueAlert(HashMap<Integer,ContextRuleNode> idTable) {
			if(ContextEditDistance.isUniqueColour(this.colour) == 1) {
				for(int id : contextReached.keySet()) {
					ContextRuleNode alertedNode = idTable.get(id);
					alertedNode.addReachableUniques(1);
//					alertedNode.addReachableUniques(this.contextReached.get(id));
				}
			}
		}


		public void expand(HashMap<Integer, RelationshipNode> knownNodes, HashMap<String, ContextRuleNode> nameTable) {
			if(colour == RuleNodeColour.NON_VAR_SYM_CONST.getVal() || colour == RuleNodeColour.NUMBER_SYM.getVal()) {
				for(RuleNode child : baseNode.getChildren()) {
					if(child.getColour() == RuleNodeColour.FN_OC) {
						RelationshipNode newOcc;
						if(knownNodes.containsKey(child.getId())) {
							newOcc = knownNodes.get(child.getId());
						} else {
							newOcc = new RelationshipNode(child);
						}
						knownNodes.put(child.getId(), newOcc);
						newOcc.expand(knownNodes, nameTable, 1);
						this.numExpanded += newOcc.getNumExpanded();
						this.occurrences.add(newOcc);
					} else {
						System.out.println("ERROR1: Unexpected type for child of " + baseNode.getName() + " while generating occurrence nodes, " + child.getColour());
					}
				}
			} else if(colour == RuleNodeColour.NON_VAR_SYM_PROP.getVal()) {
				for(RuleNode child : baseNode.getChildren()) {
					if(child.getColour() == RuleNodeColour.PRED_OC) {
						RelationshipNode newOcc;
						if(knownNodes.containsKey(child.getId())) {
							newOcc = knownNodes.get(child.getId());
						} else {
							newOcc = new RelationshipNode(child);
						}
						knownNodes.put(child.getId(), newOcc);
						newOcc.expand(knownNodes, nameTable, 1);
						this.numExpanded += newOcc.getNumExpanded();
						this.occurrences.add(newOcc);
					} else {
						System.out.println("ERROR2: Unexpected type for child of " + baseNode.getName() + " while generating occurrence nodes, " + child.getColour());
					}
				}
			} else if(colour == RuleNodeColour.NON_VAR_SYM_FUNC.getVal()) {
				for(RuleNode child : baseNode.getChildren()) {
					if(child.getColour() == RuleNodeColour.FN_OC) {
						RelationshipNode newOcc;
						if(knownNodes.containsKey(child.getId())) {
							newOcc = knownNodes.get(child.getId());
						} else {
							newOcc = new RelationshipNode(child);
						}
						knownNodes.put(child.getId(), newOcc);
						newOcc.expand(knownNodes, nameTable, 1);
						this.numExpanded += newOcc.getNumExpanded();
						this.occurrences.add(newOcc);
					} else if (child.getColour() == RuleNodeColour.ARG) {
						RelationshipNode newArg;
						if(knownNodes.containsKey(child.getId())) {
							newArg = knownNodes.get(child.getId());
						} else {
							newArg = new RelationshipNode(child);
						}
						knownNodes.put(child.getId(), newArg);
						newArg.expand(knownNodes, nameTable, 1);
						this.numExpanded += newArg.getNumExpanded();
						this.args.add(newArg);
					} else if(child.getColour() == RuleNodeColour.PRED_OC) {
						RelationshipNode newOcc;
						if(knownNodes.containsKey(child.getId())) {
							newOcc = knownNodes.get(child.getId());
						} else {
							newOcc = new RelationshipNode(child);
						}
						knownNodes.put(child.getId(), newOcc);
						newOcc.expand(knownNodes, nameTable, 1);
						this.numExpanded += newOcc.getNumExpanded();
						this.occurrences.add(newOcc);
					} else {
						System.out.println("ERROR3: Unexpected type for child of " + baseNode.getName() + " while generating occurrence nodes, " + child.getColour());
					}
				}
			} else if(colour == RuleNodeColour.NON_VAR_SYM_RELATION.getVal()) {
				for(RuleNode child : baseNode.getChildren()) {
					if(child.getColour() == RuleNodeColour.PRED_OC) {
						RelationshipNode newOcc;
						if(knownNodes.containsKey(child.getId())) {
							newOcc = knownNodes.get(child.getId());
						} else {
							newOcc = new RelationshipNode(child);
						}
						knownNodes.put(child.getId(), newOcc);
						newOcc.expand(knownNodes, nameTable, 1);
						this.numExpanded += newOcc.getNumExpanded();
						this.occurrences.add(newOcc);
					} else if (child.getColour() == RuleNodeColour.ARG) {
						RelationshipNode newArg;
						if(knownNodes.containsKey(child.getId())) {
							newArg = knownNodes.get(child.getId());
						} else {
							newArg = new RelationshipNode(child);
						}
						knownNodes.put(child.getId(), newArg);
						newArg.expand(knownNodes, nameTable, 1);
						this.numExpanded += newArg.getNumExpanded();
						this.args.add(newArg);
					} else {
						System.out.println("ERROR4: Unexpected type for child of " + baseNode.getName() + " while generating occurrence nodes, " + child.getColour());
					}
				}
			} else {
				System.out.println("ERROR: ContextRuleNode made with base node of invalid type");
			}
		}


		//costVector[0] = average cost/node
		//costVector[1] = # nodes examined
		//costVector[2] = # nodes successfully matched
		//costVector[3] = # unique colours successfully matched
		public float[] distance(ContextRuleNode other, HashMap<String, ContextRuleNode> thisNameTable, HashMap<String, ContextRuleNode> otherNameTable, int depth) {
			float[] costVector = new float[4];
			costVector[1] = 1;

			if(this.colour != other.getColour()) {
				costVector[0] = ContextEditDistance.BASE_CONTEXT_DIF_COST + ContextEditDistance.DEPTH_REDUCED_CONTEXT_DIF_COST/(float)(depth+1);
			} else {
				costVector[2] = 1;
				costVector[3] = ContextEditDistance.isUniqueColour(this.colour);
				if(depth == 0) {
					HashSet<Integer> thisVisited = new HashSet<Integer>();
					thisVisited.add(this.baseNode.getId());
					HashSet<Integer> otherVisited = new HashSet<Integer>();
					otherVisited.add(other.getBaseNode().getId());
					float[] occCosts = relationshipListDistance(this.occurrences, other.getOccurrences(), thisVisited, otherVisited, thisNameTable, otherNameTable, 1);
					float[] argCosts = relationshipListDistance(this.args, other.getArgs(), thisVisited, otherVisited, thisNameTable, otherNameTable, 1);

					//Old calulation method weights all nodes equally, not considering how many might be args or occurrences
//					float totalNumChildren = occCosts[1] + argCosts[1];
//					if(totalNumChildren != 0) {
//						costVector[0] += occCosts[0]/totalNumChildren + argCosts[0]/totalNumChildren;
//					}

					float argProp = ARG_DIST_PROPORTION;
					float occProp = 1 - argProp;
					float argTerm = 0;
					float occTerm = 0;
					if(argCosts[1] > FLOAT_TOLERANCE) {
						argTerm = argCosts[0] / argCosts[1];
					}
					if(occCosts[1] > FLOAT_TOLERANCE) {
						occTerm = occCosts[0] / occCosts[1];
					}
					costVector[0] += argProp*argTerm + occProp*occTerm;

					costVector[1] += occCosts[1] + argCosts[1];
					costVector[2] += occCosts[2] + argCosts[2];
					costVector[3] += occCosts[3] + argCosts[3];
				}
			}
//			System.out.println(costVector[0] + " " + costVector[1] + " " + costVector[2] + " " + costVector[3]);
			return costVector;
		}


		public void calcReachable(HashMap<String, ContextRuleNode> thisNameTable) {
			this.reachableNodes = 1;
			this.contextReached = new HashMap<Integer,Integer>();

			HashSet<Integer> thisVisited = new HashSet<Integer>();
			thisVisited.add(this.baseNode.getId());

			for (RelationshipNode occNode : this.occurrences) {
				occNode.calcReachableNodes(thisVisited, thisNameTable, this.contextReached, 1);
				this.reachableNodes += occNode.getReachableNodes();
			}

			for (RelationshipNode argNode : this.args) {
				argNode.calcReachableNodes(thisVisited, thisNameTable, this.contextReached, 1);
				this.reachableNodes += argNode.getReachableNodes();
			}
		}


		public float unmatchedCost() {
			float totalCost = 1; //BASE_CONTEXT_NODE_UNMATCHED_COST;
//			HashSet<Integer> visited = new HashSet<Integer>();
//			visited.add(this.baseNode.getId());
//
//			for(RelationshipNode occ : this.occurrences) {
//				totalCost += occ.unmatchedCost(visited, 1);
//			}
//			for(RelationshipNode arg : this.args) {
//				totalCost += arg.unmatchedCost(visited, 1);
//			}
			return totalCost;
		}
	}


	//costVector[0] = TOTAL cost
	//costVector[1] = # nodes examined
	//costVector[2] = # nodes successfully matched
	//costVector[3] = # unique colours successfully matched
	public float[] relationshipListDistance(ArrayList<RelationshipNode> l1, ArrayList<RelationshipNode> l2, HashSet<Integer> l1Visited, HashSet<Integer> l2Visited, HashMap<String, ContextRuleNode> l1NameTable, HashMap<String, ContextRuleNode> l2NameTable, int depth) {
		float[] costVector = new float[4];
		ArrayList<CostPair<Integer, Integer>> costs = new ArrayList<CostPair<Integer, Integer>>();
		boolean[] l1Used = new boolean[l1.size()];
		boolean[] l2Used = new boolean[l2.size()]; //initialized to all false
		int numUsed = 0;

		for(int i=0;i<l1.size();i++) {
			if(!l1Used[i]) {
				RelationshipNode l1Node = l1.get(i);
				for(int j=0;j<l2.size();j++) {
					if(!l2Used[j]) {
						RelationshipNode l2Node = l2.get(j);
						CostPair<Integer,Integer> currCost = new CostPair<Integer,Integer>(l1Node.distance(l2Node, l1Visited, l2Visited, l1NameTable, l2NameTable, depth), i, j);
						if(currCost.getCostVector()[0] < ContextEditDistance.FLOAT_TOLERANCE) {
							l1Used[currCost.getFirst()] = true;
							l2Used[currCost.getSecond()] = true;
							numUsed++;
							costVector[1] += currCost.getCostVector()[1];
							costVector[2] += currCost.getCostVector()[2];
							costVector[3] += currCost.getCostVector()[3];
							break;
						} else {
							costs.add(currCost);
						}
					}
				}
			}
		}

		Collections.sort(costs);
		while(numUsed < l1.size() && numUsed < l2.size() && !costs.isEmpty()) {
			CostPair<Integer,Integer> currCost = costs.remove(0);
			if(!l1Used[currCost.getFirst()] && !l2Used[currCost.getSecond()]) {
				l1Used[currCost.getFirst()] = true;
				l2Used[currCost.getSecond()] = true;
				numUsed++;
				costVector[0] += currCost.getCostVector()[0];
				costVector[1] += currCost.getCostVector()[1];
				costVector[2] += currCost.getCostVector()[2];
				costVector[3] += currCost.getCostVector()[3];

			}
		}

		for(int i=0;i<l1Used.length;i++) {
			if(!l1Used[i]) {
				costVector[0] += l1.get(i).unmatchedCost(l1Visited, depth);
				costVector[1] += 1;
			}
		}
		for(int i=0;i<l2Used.length;i++) {
			if(!l2Used[i]) {
				costVector[0] += l2.get(i).unmatchedCost(l2Visited, depth);
				costVector[1] += 1;
			}
		}

		return costVector;
	}

	public ContextEditDistance(ArrayList<RuleNode> g1, ArrayList<RuleNode> g2, ArrayList<Integer> g1NonVarSymbols, ArrayList<Integer> g2NonVarSymbols,
			HashSet<Integer> g1NumberIDs, HashSet<Integer> g2NumberIDs, List<Pair<Integer,List<Integer>>> g1NumberChains, List<Pair<Integer,List<Integer>>> g2NumberChains) {
		this(g1, g2, g1NonVarSymbols, g2NonVarSymbols, g1NumberIDs, g2NumberIDs, g1NumberChains, g2NumberChains, 8288034731336811092L);
	}

	public ContextEditDistance(ArrayList<RuleNode> g1, ArrayList<RuleNode> g2, ArrayList<Integer> g1NonVarSymbols, ArrayList<Integer> g2NonVarSymbols,
			HashSet<Integer> g1NumberIDs, HashSet<Integer> g2NumberIDs, List<Pair<Integer,List<Integer>>> g1NumberChains, List<Pair<Integer,List<Integer>>> g2NumberChains, long randomSeed) {
		this.g1 = g1;
		this.g2 = g2;
		this.g1NonVarSymbols = g1NonVarSymbols;
		this.g2NonVarSymbols = g2NonVarSymbols;
		this.g1NumberIDs = g1NumberIDs;
		this.g2NumberIDs = g2NumberIDs;
		this.g1NumberChains = g1NumberChains;
		this.g2NumberChains = g2NumberChains;
		this.g1TopNodeTable = new HashMap<Integer,ContextRuleNode>();
		this.g2TopNodeTable = new HashMap<Integer,ContextRuleNode>();
		this.g1NameTopNodeTable = new HashMap<String,ContextRuleNode>();
		this.g2NameTopNodeTable = new HashMap<String,ContextRuleNode>();
		this.directedEdges = new HashSet<Integer>();
		this.undirectedEdges = new HashSet<Integer>();

		for(int currID : g1NonVarSymbols) {
			RuleNode rn = g1.get(currID);
			ContextRuleNode newNode = new ContextRuleNode(rn);
			g1TopNodeTable.put(currID, newNode);
			if(!g1NameTopNodeTable.containsKey(rn.getName())) {
				g1NameTopNodeTable.put(rn.getName(), newNode);
			} else {
				System.out.println("ERROR: encountered duplicate non-variable symbol name in G1 while initializing ContextEditDistance");
			}
		}
		for(int currID : g2NonVarSymbols) {
			RuleNode rn = g2.get(currID);
			ContextRuleNode newNode = new ContextRuleNode(rn);
			g2TopNodeTable.put(currID, newNode);
			if(!g2NameTopNodeTable.containsKey(rn.getName())) {
				g2NameTopNodeTable.put(rn.getName(), newNode);
			} else {
				System.out.println("ERROR: encountered duplicate non-variable symbol name in G2 while initializing ContextEditDistance");
			}
		}

		Collections.shuffle(this.g2NonVarSymbols, new Random(randomSeed));
//		Collections.sort(this.g1);
//		Collections.sort(this.g2);
//		Collections.shuffle(this.g2, new Random(8288034731336811092L));
//		Collections.sort(this.g2, Collections.reverseOrder());
		this.mapping = new HashMap<Integer, Integer>();
		this.revMapping = new HashMap<Integer, Integer>();
		this.roleIndexMapping = new HashMap<Integer, Integer>();
		this.revRoleIndexMapping = new HashMap<Integer, Integer>();
		this.mapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
		this.revMapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);

		this.distVal = -1;
	}

	public ArrayList<RuleNode> getG1() {
		return g1;
	}

	public ArrayList<RuleNode> getG2() {
		return g2;
	}

	public HashMap<Integer, Integer> getMapping() {
		return mapping;
	}

	public HashMap<Integer, Integer> getRevMapping() {
		return revMapping;
	}

	public int targetIDToSource(int targetID) {
		int result = -1;
		if(this.mapping.containsKey(targetID)) {
			result = this.mapping.get(targetID);
		}
		return result;
	}

	public int sourceIDToTarget(int sourceID) {
		int result = -1;
		if(this.revMapping.containsKey(sourceID)) {
			result = this.revMapping.get(sourceID);
		}
		return result;
	}

	public int getG1IdFromName(String name) {
		int returnVal = -1;
		if(this.g1NameTopNodeTable.containsKey(name)) {
			returnVal = this.g1NameTopNodeTable.get(name).getBaseNode().getId();
		}
		return returnVal;
	}


	public float getDistance() {
		return distVal;
	}

	public String mappedNamesToString() {
		String outStr = "";
		outStr += "G1->G2\n";
		for(int g1ID : this.mapping.keySet()) {
//			System.out.println(outStr);
//			System.out.println(g1ID);
			if(g1ID != StateNode.ROOT_ID && g1ID != -1) {
				RuleNode g1Node = this.g1.get(g1ID);
				outStr += g1Node.getName() + "{" + g1Node.getColour() + ";" + g1Node.getArgNum() + "}=";
				if(this.mapping.get(g1ID) != -1) {
					RuleNode g2Match = this.g2.get(this.mapping.get(g1ID));
					outStr += g2Match.getName() + "{" + g2Match.getColour() + ";" + g2Match.getArgNum() + "} ";
				} else {
					outStr += "-1 ";
				}
			}
		}
		outStr += "\nG2->G1\n";
		for(int g2ID : this.revMapping.keySet()) {
//			System.out.println(outStr);
//			System.out.println(g1ID);
			if(g2ID != StateNode.ROOT_ID && g2ID != -1) {
				RuleNode g2Node = this.g2.get(g2ID);
				outStr += g2Node.getName() + "{" + g2Node.getColour() + ";" + g2Node.getArgNum() + "}=";
				if(this.revMapping.get(g2ID) != -1) {
					RuleNode g1Match = this.g1.get(this.revMapping.get(g2ID));
					outStr += g1Match.getName() + "{" + g1Match.getColour() + ";" + g1Match.getArgNum() + "} ";
				} else {
					outStr += "-1 ";
				}
			}
		}
		//-1 (ie. no match) are reported from g1 to g2 only (not the reverse)
		return outStr;
	}

	public static float isUniqueColour(int colour) {
		if(colour >= RuleNodeColour.values().length) {
			return 1;
		} else {
			return 0;
		}
	}


	public static float scoreFunction(float[] costVector, float[] maxVector) {
		float avgCostComp = 0;
		float rawNumSuccessfulComp = 0;
		float uniqueMatchComp = 0;
		if(maxVector[0] > ContextEditDistance.FLOAT_TOLERANCE) {
			avgCostComp = costVector[0]/maxVector[0]*ContextEditDistance.AVG_COST_WEIGHT;
		}
		if(maxVector[2] > ContextEditDistance.FLOAT_TOLERANCE) {
			rawNumSuccessfulComp = (1-costVector[2]/maxVector[2])*ContextEditDistance.RAW_NUM_SUCCESSFUL_WEIGHT;
		}
		if(maxVector[3] > ContextEditDistance.FLOAT_TOLERANCE) {
			uniqueMatchComp = (1-costVector[3]/maxVector[3])*ContextEditDistance.UNIQUE_MATCH_WEIGHT;
		}

		return avgCostComp + rawNumSuccessfulComp + uniqueMatchComp;
	}


	//first in pair is score matrix
	//second is whole cost vector matrix, including the actual costs
	private Pair<float[][], float[][][]> bruteForceCostMatrix(ArrayList<ContextRuleNode> g1Nodes, ArrayList<ContextRuleNode> g2Nodes, HashMap<String, ContextRuleNode> g1NameTable, HashMap<String, ContextRuleNode> g2NameTable) {
		float[][] scores = new float[g1Nodes.size()][g2Nodes.size()];
		float[][][] vectorStorage = new float[g1Nodes.size()][g2Nodes.size()][4];
		float[] maxVector = new float[4];

		for(int i=0;i<g1Nodes.size();i++) {
			for(int j=0;j<g2Nodes.size();j++) {
				ContextRuleNode g1n = g1Nodes.get(i);
				ContextRuleNode g2n = g2Nodes.get(j);
				float[] costVector = g1n.distance(g2n, g1NameTable, g2NameTable, 0);
//				if((g1n.getBaseNode().getName().equals("1") || g1n.getBaseNode().getName().equals("8")) && (g2n.getBaseNode().getName().equals("1") || g2n.getBaseNode().getName().equals("8"))) {
//					System.out.println("* " + g1n.getBaseNode().getName() + " " + g2n.getBaseNode().getName() + " " + costVector[0] + " " + costVector[1] + " " + costVector[2] + " " + costVector[3] );
//				}
				vectorStorage[i][j] = costVector;
				for(int k=0;k<4;k++) {
					if(costVector[k] > maxVector[k]) {
						maxVector[k] = costVector[k];
					}
				}
			}
		}
		for(int i=0;i<g1Nodes.size();i++) {
			for(int j=0;j<g2Nodes.size();j++) {
				scores[i][j] = scoreFunction(vectorStorage[i][j], maxVector);
				ContextRuleNode g1n = g1Nodes.get(i);
				ContextRuleNode g2n = g2Nodes.get(j);
//				if((g1n.getBaseNode().getName().equals("1") || g1n.getBaseNode().getName().equals("8")) && (g2n.getBaseNode().getName().equals("1") || g2n.getBaseNode().getName().equals("8"))) {
//					System.out.println("** " + g1n.getBaseNode().getName() + " " + g2n.getBaseNode().getName() + " " + scores[i][j] );
//				}
			}
		}

//		System.out.println("* " + vectorStorage[12])

		return new Pair<float[][], float[][][]>(scores,vectorStorage);
	}

	//if 2 or more matchings share the same target or source node and have the same distance, penalize them
	private void applyNonUniquePenalty(float[][] scores) {
		HashSet<Pair<Integer,Integer>> penalized = new HashSet<Pair<Integer,Integer>>();
		for(int i=0;i<scores.length;i++) {
			ArrayList<Pair<Float,Integer>> rowScores = new ArrayList<Pair<Float,Integer>>();
			for(int j=0;j<scores[i].length;j++) {
				rowScores.add(new Pair<Float,Integer>(scores[i][j], j));
			}

			Collections.sort(rowScores, new PairComparator());
			for(int j=0;j<rowScores.size()-1;j++) {
				Pair<Float,Integer> first = rowScores.get(j);
				Pair<Float,Integer> second = rowScores.get(j+1);
				if(Math.abs(first.getKey() - second.getKey()) < ContextEditDistance.FLOAT_TOLERANCE) {
					penalized.add(new Pair<Integer,Integer>(i, first.getValue()));
					penalized.add(new Pair<Integer,Integer>(i, second.getValue()));
				}
			}
		}
		for(int j=0;j<scores[0].length;j++) {
			ArrayList<Pair<Float,Integer>> colScores = new ArrayList<Pair<Float,Integer>>();
			for(int i=0;i<scores.length;i++) {
				colScores.add(new Pair<Float,Integer>(scores[i][j], i));
			}

			Collections.sort(colScores, new PairComparator());
			for(int i=0;i<colScores.size()-1;i++) {
				Pair<Float,Integer> first = colScores.get(i);
				Pair<Float,Integer> second = colScores.get(i+1);
				if(Math.abs(first.getKey() - second.getKey()) < ContextEditDistance.FLOAT_TOLERANCE) {
					penalized.add(new Pair<Integer,Integer>(first.getValue(), j));
					penalized.add(new Pair<Integer,Integer>(second.getValue(), j));
				}
			}
		}

		for(Pair<Integer,Integer> p : penalized) {
			scores[p.getKey()][p.getValue()] += ContextEditDistance.NON_UNIQUE_ASSIGNMENT_PENALTY;
		}
	}


	private ArrayList<int[]> findMinAssignments(float[][] costs) {
		float currMin = -1;
		ArrayList<int[]> minAssignments = null;

		for(int i=0;i<costs.length;i++) {
			for(int j=0;j<costs[i].length;j++) {
				if(minAssignments == null || costs[i][j] < currMin) {
					currMin = costs[i][j];
					minAssignments = new ArrayList<int[]>();
					minAssignments.add(new int[] {i,j});
				} else if(Math.abs(costs[i][j] - currMin) < ContextEditDistance.FLOAT_TOLERANCE) {
					minAssignments.add(new int[] {i,j});
				}
			}
		}

		return minAssignments;
	}


	//returnValue[0] is mappings of to->from; returnValue[1] is reverse
	public ArrayList<HashMap<Integer,ArrayList<Integer>>> groupPossibleAssignments(ArrayList<int[]> possibleAssignments) {
		ArrayList<HashMap<Integer,ArrayList<Integer>>> result = new ArrayList<HashMap<Integer,ArrayList<Integer>>>();
		result.add(new HashMap<Integer,ArrayList<Integer>>());
		result.add(new HashMap<Integer,ArrayList<Integer>>());

		for(int[] pair : possibleAssignments) {
			HashMap<Integer,ArrayList<Integer>> forwardMapping = result.get(0);
			HashMap<Integer,ArrayList<Integer>> reverseMapping = result.get(1);
			if(!forwardMapping.containsKey(pair[0])) {
				forwardMapping.put(pair[0], new ArrayList<Integer>());
			}
			forwardMapping.get(pair[0]).add(pair[1]);
			if(!reverseMapping.containsKey(pair[1])) {
				reverseMapping.put(pair[1], new ArrayList<Integer>());
			}
			reverseMapping.get(pair[1]).add(pair[0]);
		}

		return result;
	}

	public ArrayList<int[]> findMostUniquePairs(HashMap<Integer,ArrayList<Integer>> forwardAssignments, HashMap<Integer,ArrayList<Integer>> reverseAssignments) {
		ArrayList<int[]> pairs = new ArrayList<int[]>();
		HashSet<Pair<Integer,Integer>> added = new HashSet<Pair<Integer,Integer>>();

		int minCount = -1;
		for(int key : forwardAssignments.keySet()) {
			ArrayList<Integer> currAssn = forwardAssignments.get(key);
			if(minCount == -1 || currAssn.size() < minCount) {
				minCount = currAssn.size();
			}
		}
		for(int key : reverseAssignments.keySet()) {
			ArrayList<Integer> currAssn = reverseAssignments.get(key);
			if(minCount == -1 || currAssn.size() < minCount) {
				minCount = currAssn.size();
			}
		}

		for(int key : forwardAssignments.keySet()) {
			ArrayList<Integer> currAssn = forwardAssignments.get(key);
			if(currAssn.size() == minCount) {
				for(int other : currAssn) {
					pairs.add(new int[]{key, other});
					added.add(new Pair<Integer,Integer>(key,other));
				}
			}
		}
		for(int key : reverseAssignments.keySet()) {
			ArrayList<Integer> currAssn = reverseAssignments.get(key);
			if(currAssn.size() == minCount) {
				for(int other : currAssn) {
					if(!added.contains(new Pair<Integer,Integer>(other,key))) {
						pairs.add(new int[]{other, key});
					}
				}
			}
		}

		return pairs;
	}


	public ArrayList<ContextRuleNode> genContextNodes(ArrayList<Integer> symbolIds, HashMap<Integer, ContextRuleNode> topNodeTable, HashMap<String, ContextRuleNode> nameTopNodeTable) {
		HashMap<Integer, RelationshipNode> knownNodes = new HashMap<Integer, RelationshipNode>();
		ArrayList<ContextRuleNode> contextNodes = new ArrayList<ContextRuleNode>();
		for(int currID : symbolIds) {
			ContextRuleNode currNode = topNodeTable.get(currID);
			currNode.expand(knownNodes, nameTopNodeTable);
			contextNodes.add(currNode);
		}
		return contextNodes;
	}


	public ArrayList<CostPair<RuleNode,RuleNode>> calcDistance() {
		return calcDistance(ContextEditDistance.DEFAULT_MAPPING_ALG);
	}


	//Calculate the distance and do a full mapping between G1 and G2
	// "full_matrix" calls MMap
	// "two_lines" calls LMap
	public ArrayList<CostPair<RuleNode,RuleNode>> calcDistance(String mappingAlg) {
		ArrayList<CostPair<RuleNode,RuleNode>> distList = null;
		if(mappingAlg == "full_matrix") {
			distList = fullMatrixCalcDistance();
		} else if(mappingAlg == "two_lines") {
			distList = twoLineCalcDistance();
		} else {
			System.out.println("ERROR: unrecognized String mappingAlg passed to calcDistance");
		}
		mapNumbers();

		return distList;
	}


	//maps chains of numbers together based on the way that successor functions are mapped
	//if there is more than one chain per successor function, then just put together the chains that are the most similar in length
	//(a more sophisticated method would look at the Rule Graph connections into and out of the chain)
	private void mapNumbers() {
		HashMap<Integer, List<List<Integer>>> g1ChainsPerFn = new HashMap<Integer, List<List<Integer>>>();
		HashMap<Integer, List<List<Integer>>> g2ChainsPerFn = new HashMap<Integer, List<List<Integer>>>();
		for(Pair<Integer,List<Integer>> chain : this.g1NumberChains) {
			int fnID = chain.getKey();
			if(!g1ChainsPerFn.containsKey(fnID)) {
				g1ChainsPerFn.put(fnID, new ArrayList<List<Integer>>());
			}
			g1ChainsPerFn.get(fnID).add(chain.getValue());
		}
		for(Pair<Integer,List<Integer>> chain : this.g2NumberChains) {
			int fnID = chain.getKey();
			if(!g2ChainsPerFn.containsKey(fnID)) {
				g2ChainsPerFn.put(fnID, new ArrayList<List<Integer>>());
			}
			g2ChainsPerFn.get(fnID).add(chain.getValue());
		}

		for(int fnID : g1ChainsPerFn.keySet()) {
			int mappedFnID = this.mapping.get(fnID);
			List<List<Integer>> allG1Chains = g1ChainsPerFn.get(fnID);
			Collections.sort(allG1Chains, new MyUtil.ListSizeComparator<Integer>());  //sorting from smallest to largest means that if a number ID gets mapped in 2 different ways, the one belonging to the longer chain will be kept
			List<List<Integer>> allG2Chains = null;
			if(mappedFnID != -1 && g2ChainsPerFn.get(mappedFnID) != null) {
				allG2Chains = g2ChainsPerFn.get(mappedFnID);
				Collections.sort(allG2Chains, new MyUtil.ListSizeComparator<Integer>());
			}
			mapChainsOneWay(allG1Chains, allG2Chains, this.mapping);
		}
		for(int fnID : g2ChainsPerFn.keySet()) {
			int mappedFnID = this.revMapping.get(fnID);
			List<List<Integer>> allG2Chains = g2ChainsPerFn.get(fnID);
			Collections.sort(allG2Chains, new MyUtil.ListSizeComparator<Integer>());
			List<List<Integer>> allG1Chains = null;
			if(mappedFnID != -1 && g1ChainsPerFn.get(mappedFnID) != null) {
				allG1Chains = g1ChainsPerFn.get(mappedFnID);
				Collections.sort(allG1Chains, new MyUtil.ListSizeComparator<Integer>());
			}
			mapChainsOneWay(allG2Chains, allG1Chains, this.revMapping);
		}
	}


	private void mapChainsOneWay(List<List<Integer>> from, List<List<Integer>> onto, HashMap<Integer,Integer> mapping) {
		if(onto != null) {
			for(List<Integer> currFromChain : from) {
				int closestSize = Integer.MAX_VALUE;
				List<Integer> closestOntoChain = null;
				for(List<Integer> currOntoChain : onto) {
					int sizeDifference = Math.abs(currFromChain.size() - currOntoChain.size());
					if(sizeDifference < closestSize) {
						closestSize = sizeDifference;
						closestOntoChain = currOntoChain;
					}
				}
				int i;
				for(i=0;i<currFromChain.size()&&i<closestOntoChain.size();i++) {
					mapping.put(currFromChain.get(i), closestOntoChain.get(i));
				}
				while(i<currFromChain.size()) {
					if(!mapping.containsKey(currFromChain.get(i))) {
						mapping.put(currFromChain.get(i), -1);
					}
					i++;
				}
			}
		} else {
			for(List<Integer> currChain : from) {
				for(int currID : currChain) {
					if(!mapping.containsKey(currID)) {
						mapping.put(currID, -1); //maybe it would be better to map orphan numbers to something
					}
				}
			}
		}
	}


	public ArrayList<CostPair<RuleNode,RuleNode>> twoLineCalcDistance() {
		float totalCost = 0;
		float totalDivisor = 0;
		ArrayList<CostPair<RuleNode,RuleNode>> returnList = new ArrayList<CostPair<RuleNode,RuleNode>>();
		int nextColour = RuleNodeColour.values().length;

		ArrayList<Integer> g1NonVarNonNumSymbols = new ArrayList<Integer>();
		ArrayList<Integer> g2NonVarNonNumSymbols = new ArrayList<Integer>();
		for(int id : g1NonVarSymbols) {
			if(!g1NumberIDs.contains(id)) {
				g1NonVarNonNumSymbols.add(id);
			}
		}
		for(int id : g2NonVarSymbols) {
			if(!g2NumberIDs.contains(id)) {
				g2NonVarNonNumSymbols.add(id);
			}
		}

		ArrayList<ContextRuleNode> g1NodesRemaining = genContextNodes(g1NonVarNonNumSymbols, g1TopNodeTable, g1NameTopNodeTable);
		ArrayList<ContextRuleNode> g2NodesRemaining = genContextNodes(g2NonVarNonNumSymbols, g2TopNodeTable, g2NameTopNodeTable);

		for(ContextRuleNode g1Node : g1NodesRemaining) {
			g1Node.calcReachable(g1NameTopNodeTable);
		}

		while(!g1NodesRemaining.isEmpty()  && !g2NodesRemaining.isEmpty()) {
			float[] maxVector = new float[4];

			for(ContextRuleNode g1Node : g1NodesRemaining) {
				if(g1Node.getReachableNodes() > maxVector[2]) {
					maxVector[2] = g1Node.getReachableNodes();
				}
				if(g1Node.getReachableUniques() > maxVector[3]) {
					maxVector[3] = g1Node.getReachableUniques();
				}
			}

			//find g1 node to begin mapping
			float bestScore = -1;
			ContextRuleNode g1BestNode = null;
			for(ContextRuleNode g1Node : g1NodesRemaining) {
				float[] currVector = new float[] {0,0,g1Node.getReachableNodes(),g1Node.getReachableUniques()};
				float currScore = ContextEditDistance.scoreFunction(currVector, maxVector); //this is an abuse of the score function because of the [2] position
				if(g1BestNode == null || currScore < bestScore) {
					bestScore = currScore;
					g1BestNode = g1Node;
				}
//				System.out.println("* " + bestScore + " " + currScore + " " + g1BestNode.getBaseNode().getName() + " " + g1Node.getBaseNode().getName() + " " + g1Node.getReachableNodes() + " " + g1Node.getReachableUniques());
			}

			//find best g2 node for g1 node
			ArrayList<float[]> firstDistanceList = new ArrayList<float[]>();
			float bestRawDistance = -1;
			float[] maxFirstDistVector = new float[4];
			for(ContextRuleNode g2Node : g2NodesRemaining) {
				float[] currVector = g1BestNode.distance(g2Node, g1NameTopNodeTable, g2NameTopNodeTable, 0);
				firstDistanceList.add(currVector);
				if(bestRawDistance < -0.9 || currVector[0] < bestRawDistance) {
					bestRawDistance = currVector[0];
				}
				for(int k=0;k<4;k++) {
					if(currVector[k] > maxFirstDistVector[k]) {
						maxFirstDistVector[k] = currVector[k];
					}
				}
			}
			System.out.println(g1BestNode.getBaseNode().getName() + " " + bestRawDistance);
			if(bestRawDistance > ContextEditDistance.BASE_CONTEXT_NODE_UNMATCHED_COST) { //all g2 matches are too poor; map g1Node to nothing
				float unmatchedCost = g1BestNode.unmatchedCost();
				totalCost += unmatchedCost;
				totalDivisor++;
				returnList.add(new CostPair<RuleNode,RuleNode>(new float[] {unmatchedCost,-1,-1,-1}, g1BestNode.getBaseNode(), null));
				mapping.put(g1BestNode.getBaseNode().getId(), -1);
//				revMapping.put(-1, g1BestNode.getBaseNode().getId());
				g1NodesRemaining.remove(g1BestNode);
			} else {
//				ArrayList<Float> firstScoreList = new ArrayList<Float>();
				float bestFirstScore = -1;
				float bestFirstCost = -1;
				float[] bestFirstCostVector = null;
				ContextRuleNode g2BestNode = null;
				boolean firstNonUnique = false;
				for(int i=0;i<firstDistanceList.size();i++) { //calculate scores for g2Nodes, and choose node with the lowest score
					float[] currVector = firstDistanceList.get(i);
					float currScore = ContextEditDistance.scoreFunction(currVector, maxFirstDistVector);
					if(Math.abs(bestFirstScore - currScore) < ContextEditDistance.FLOAT_TOLERANCE) {
						firstNonUnique = true;
					}
					if(bestFirstScore < -0.9 || currScore < bestFirstScore) {
						if(Math.abs(bestFirstScore - currScore) >= ContextEditDistance.FLOAT_TOLERANCE) {
							firstNonUnique = false;
						}
						bestFirstScore = currScore;
						bestFirstCost = currVector[0];
						bestFirstCostVector = currVector;
						g2BestNode = g2NodesRemaining.get(i);
					}
				}
				if(firstNonUnique) {
					bestFirstScore += ContextEditDistance.NON_UNIQUE_ASSIGNMENT_PENALTY;
				}

				//go back to g1 nodes and find best match for selected g2 node
				ArrayList<float[]> secondDistanceList = new ArrayList<float[]>();
				bestRawDistance = -1;
				float[] maxSecondDistVector = new float[4];
				for(ContextRuleNode g1Node : g1NodesRemaining) {
					float[] currVector = g1Node.distance(g2BestNode, g1NameTopNodeTable, g2NameTopNodeTable, 0);
					secondDistanceList.add(currVector);
					if(bestRawDistance < -0.9 || currVector[0] < bestRawDistance) {
						if(g1Node.getBaseNode().getId() != g1BestNode.getBaseNode().getId()) {
							bestRawDistance = currVector[0];
						}
					}
					for(int k=0;k<4;k++) {
						if(currVector[k] > maxSecondDistVector[k]) {
							maxSecondDistVector[k] = currVector[k];
						}
					}
				}
				if(bestRawDistance > ContextEditDistance.BASE_CONTEXT_NODE_UNMATCHED_COST) { //all other g2 matches are too poor to consider; map g1 best and g2 best immediately
					g1NodesRemaining.remove(g1BestNode);
					g2NodesRemaining.remove(g2BestNode);
					mapping.put(g1BestNode.getBaseNode().getId(), g2BestNode.getBaseNode().getId());
					revMapping.put(g2BestNode.getBaseNode().getId(), g1BestNode.getBaseNode().getId());
					totalCost += bestFirstCost;
					totalDivisor++;
					returnList.add(new CostPair<RuleNode,RuleNode>(bestFirstCostVector, g1BestNode.getBaseNode(), g2BestNode.getBaseNode()));
					g1BestNode.setColour(nextColour);
					g2BestNode.setColour(nextColour);
					nextColour++;
					g1BestNode.uniqueAlert(g1TopNodeTable);
				} else {
					float bestSecondScore = -1;
					float bestSecondCost = -1;
					float[] bestSecondCostVector = null;
					ContextRuleNode g1BestSecondNode = null;
					boolean secondNonUnique = false;
					for(int i=0;i<secondDistanceList.size();i++) { //calculate scores for g1Nodes, and choose node with the lowest score
						if(g1NodesRemaining.get(i).getBaseNode().getId() != g1BestNode.getBaseNode().getId()) {
							float[] currVector = secondDistanceList.get(i);
							float currScore = ContextEditDistance.scoreFunction(currVector, maxSecondDistVector);
							if(Math.abs(bestSecondScore - currScore) < ContextEditDistance.FLOAT_TOLERANCE) {
								secondNonUnique = true;
							}
							if(bestSecondScore < -0.9 || currScore < bestSecondScore) {
								if(Math.abs(bestSecondScore - currScore) >= ContextEditDistance.FLOAT_TOLERANCE) {
									secondNonUnique = false;
								}
								bestSecondScore = currScore;
								bestSecondCost = currVector[0];
								bestSecondCostVector = currVector;
								g1BestSecondNode = g1NodesRemaining.get(i);
							}
						}
					}
					if(secondNonUnique) {
						bestSecondScore += ContextEditDistance.NON_UNIQUE_ASSIGNMENT_PENALTY;
					}

					//verbose printing stuff
//					System.out.println("********");
//					System.out.println("First G1 Node: " + g1BestNode.getBaseNode().shortToString());
//					System.out.println("      G2 Node: " + g2BestNode.getBaseNode().shortToString());
//					System.out.println("Score: " + bestFirstScore + "; Unique: " + (!firstNonUnique));
//					if(g1BestSecondNode != null) {
//						System.out.println("Second G1 Node: " + g1BestSecondNode.getBaseNode().shortToString());
//						System.out.println("Score: " + bestSecondScore + "; Unique: " + (!secondNonUnique));
//					}

					if(g1BestSecondNode == null || bestFirstScore < bestSecondScore + USERP_THRESH) { //make first assignment
						g1NodesRemaining.remove(g1BestNode);
						g2NodesRemaining.remove(g2BestNode);
						mapping.put(g1BestNode.getBaseNode().getId(), g2BestNode.getBaseNode().getId());
						revMapping.put(g2BestNode.getBaseNode().getId(), g1BestNode.getBaseNode().getId());
						totalCost += bestFirstCost;
						returnList.add(new CostPair<RuleNode,RuleNode>(bestFirstCostVector, g1BestNode.getBaseNode(), g2BestNode.getBaseNode()));
						totalDivisor++;
						g1BestNode.setColour(nextColour);
						g2BestNode.setColour(nextColour);
						nextColour++;
						g1BestNode.uniqueAlert(g1TopNodeTable);
//						System.out.println(bestFirstScore + " " + bestFirstCostVector[0]);
					} else { //make second assignment
						g1NodesRemaining.remove(g1BestSecondNode);
						g2NodesRemaining.remove(g2BestNode);
						mapping.put(g1BestSecondNode.getBaseNode().getId(), g2BestNode.getBaseNode().getId());
						revMapping.put(g2BestNode.getBaseNode().getId(), g1BestSecondNode.getBaseNode().getId());
						totalCost += bestSecondCost;
						returnList.add(new CostPair<RuleNode,RuleNode>(bestSecondCostVector, g1BestSecondNode.getBaseNode(), g2BestNode.getBaseNode()));
						totalDivisor++;
						g1BestSecondNode.setColour(nextColour);
						g2BestNode.setColour(nextColour);
						nextColour++;
						g1BestSecondNode.uniqueAlert(g1TopNodeTable);
//						System.out.println(bestSecondScore + " " + bestSecondCostVector[0]);
					}
				}
			}
		}

		//assign remaining g1 nodes to nothing
		for(ContextRuleNode remainingNode : g1NodesRemaining) {
			float remainingCost = remainingNode.unmatchedCost();
			totalCost += remainingCost;
			totalDivisor++;
			returnList.add(new CostPair<RuleNode,RuleNode>(new float[] {remainingCost,-1,-1,-1}, remainingNode.getBaseNode(), null));
			mapping.put(remainingNode.getBaseNode().getId(), -1);
		}

		//assign remaining g2 nodes to nothing
		for(ContextRuleNode remainingNode : g2NodesRemaining) {
			float remainingCost = remainingNode.unmatchedCost();
			totalCost += remainingCost;
			totalDivisor++;
			returnList.add(new CostPair<RuleNode,RuleNode>(new float[] {remainingCost,-1,-1,-1}, null, remainingNode.getBaseNode()));
//			mapping.put(-1, remainingNode.getBaseNode().getId());
			revMapping.put(remainingNode.getBaseNode().getId(), -1);
		}

		if(totalDivisor > 0) {
			distVal = totalCost/totalDivisor;
		} else {
			System.out.println("ERROR: totalDivisor = 0 in calcDistance");
		}
		return returnList;
	}


	public ArrayList<CostPair<RuleNode,RuleNode>> fullMatrixCalcDistance() {
		float totalCost = 0;
		float totalDivisor = 0;
		int nextColour = RuleNodeColour.values().length;
		ArrayList<CostPair<RuleNode,RuleNode>> returnList = new ArrayList<CostPair<RuleNode,RuleNode>>();

		ArrayList<Integer> g1NonVarNonNumSymbols = new ArrayList<Integer>();
		ArrayList<Integer> g2NonVarNonNumSymbols = new ArrayList<Integer>();
		for(int id : g1NonVarSymbols) {
			if(!g1NumberIDs.contains(id)) {
				g1NonVarNonNumSymbols.add(id);
			}
		}
		for(int id : g2NonVarSymbols) {
			if(!g2NumberIDs.contains(id)) {
				g2NonVarNonNumSymbols.add(id);
			}
		}

		ArrayList<ContextRuleNode> g1NodesRemaining = genContextNodes(g1NonVarNonNumSymbols, g1TopNodeTable, g1NameTopNodeTable);
		ArrayList<ContextRuleNode> g2NodesRemaining = genContextNodes(g2NonVarNonNumSymbols, g2TopNodeTable, g2NameTopNodeTable);

		//draw select context graphs
//		ArrayList<ContextRuleNode> g1DrawNodes = new ArrayList<ContextRuleNode>();
//		g1DrawNodes.add(g1NameTopNodeTable.get("1"));
//		g1DrawNodes.add(g1NameTopNodeTable.get("8"));
//		ArrayList<ContextRuleNode> g2DrawNodes = new ArrayList<ContextRuleNode>();
//		g2DrawNodes.add(g2NameTopNodeTable.get("1"));
//		g2DrawNodes.add(g2NameTopNodeTable.get("8"));
//		drawAroundNodes(g1DrawNodes, g1, 10, "context_images/g1/");
//		drawAroundNodes(g2DrawNodes, g2, 10, "context_images/g2/");

		//draw all generated context graphs
//		drawAroundNodes(g1NodesRemaining, g1, 10, "context_images/g1/");
//		drawAroundNodes(g2NodesRemaining, g2, 10, "context_images/g2/");

		//
		while(!g1NodesRemaining.isEmpty() && !g2NodesRemaining.isEmpty()) {
			Pair<float[][],float[][][]> costPair = bruteForceCostMatrix(g1NodesRemaining, g2NodesRemaining, g1NameTopNodeTable, g2NameTopNodeTable);
			float[][] scores = costPair.getKey();
			float[][][] costVectors = costPair.getValue();
			applyNonUniquePenalty(scores);
			ArrayList<int[]> possibleAssignments = findMinAssignments(scores);
			ArrayList<HashMap<Integer,ArrayList<Integer>>> groupedAssignments = groupPossibleAssignments(possibleAssignments);
			HashMap<Integer,ArrayList<Integer>> forwardAssignments = groupedAssignments.get(0);
			HashMap<Integer,ArrayList<Integer>> reverseAssignments = groupedAssignments.get(1);

			//break ties in distance by uniqueness of assignments (i.e. most unique if one side of a matching can only be matched to one node in the other game)
			ArrayList<int[]> mostUniquePairs = findMostUniquePairs(forwardAssignments, reverseAssignments);

			//break ties in uniqueness by most nodes expanded
			int[] assignment = null;
			if(mostUniquePairs.isEmpty()) {
				System.out.println("ERROR: mostUniquePairs is empty in calcDistance");
			}
			assignment = mostUniquePairs.get(0);


			//Verbose print stuff
//			System.out.println("********");
//			System.out.println("scores:");
//			for(int[] pair : mostUniquePairs) {
//				System.out.print(costs[pair[0]][pair[1]] + " ");
//			}
//			System.out.println();
//			System.out.println("pairs: " + mostUniquePairs.size());
//			for(int[] pair : mostUniquePairs) {
//				System.out.println(g1NodesRemaining.get(pair[0]).getBaseNode().shortToString());
//				System.out.println(g2NodesRemaining.get(pair[1]).getBaseNode().shortToString());
//				System.out.println();
//			}
//			System.out.println("selected:");
//			System.out.println(g1NodesRemaining.get(assignment[0]).getBaseNode().shortToString());
//			System.out.println(g2NodesRemaining.get(assignment[1]).getBaseNode().shortToString());
//			System.out.println();


			if(costVectors[assignment[0]][assignment[1]][0] < ContextEditDistance.BASE_CONTEXT_NODE_UNMATCHED_COST) { //if costs have become worse than insertion/deletion, don't make more assignments
				ContextRuleNode g1Assigned = g1NodesRemaining.remove(assignment[0]);
				ContextRuleNode g2Assigned = g2NodesRemaining.remove(assignment[1]);
				mapping.put(g1Assigned.getBaseNode().getId(), g2Assigned.getBaseNode().getId());
				revMapping.put(g2Assigned.getBaseNode().getId(), g1Assigned.getBaseNode().getId());
				totalCost += costVectors[assignment[0]][assignment[1]][0];
				totalDivisor++;
				returnList.add(new CostPair<RuleNode,RuleNode>(costVectors[assignment[0]][assignment[1]],g1Assigned.getBaseNode(), g2Assigned.getBaseNode()));

				g1Assigned.setColour(nextColour);
				g2Assigned.setColour(nextColour);
				nextColour++;
			} else {
				break;
			}
		}


		for(ContextRuleNode remainingNode : g1NodesRemaining) {
			float remainingCost = remainingNode.unmatchedCost();
			totalCost += remainingCost;
			totalDivisor++;
			returnList.add(new CostPair<RuleNode,RuleNode>(new float[] {remainingCost,-1,-1,-1}, remainingNode.getBaseNode(), null));
			mapping.put(remainingNode.getBaseNode().getId(), -1);
//			revMapping.put(-1, remainingNode.getBaseNode().getId());
		}
		for(ContextRuleNode remainingNode : g2NodesRemaining) {
			float remainingCost = remainingNode.unmatchedCost();
			totalCost += remainingCost;
			totalDivisor++;
			returnList.add(new CostPair<RuleNode,RuleNode>(new float[] {remainingCost,-1,-1,-1}, null, remainingNode.getBaseNode()));
//			mapping.put(-1, remainingNode.getBaseNode().getId());
			revMapping.put(remainingNode.getBaseNode().getId(), -1);
		}

		//might need to include this root mapping. maybe others too?
//		mapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
//		revMapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
		if(totalDivisor > 0) {
			distVal = totalCost/totalDivisor;
		} else {
			System.out.println("ERROR: totalDivisor = 0 in calcDistance");
		}
		return returnList;
	}




	//generate a drawing for each node in nodeIDs, up to a distance, dist
	public void drawAroundNodes(ArrayList<ContextRuleNode> nodes, ArrayList<RuleNode> ruleNodes, int dist, String dirString) {
		for(ContextRuleNode currRoot : nodes) {
			int edgeNum = 0;

	        // Create a graph with Integer vertices and String edges
	        Graph<Integer, Integer> g = new SparseGraph<Integer, Integer>();
	        Queue<Pair<Integer,Object>> q = new LinkedList<Pair<Integer,Object>>(); //key in pair is depth, value is a node
	        q.add(new Pair<Integer,Object>(0, currRoot));
	        g.addVertex(currRoot.getBaseNode().getId());

	        while(!q.isEmpty()) {
	        	Pair<Integer,Object> currPair = q.remove();
	        	int depth = currPair.getKey();
	        	if(currPair.getValue() instanceof ContextRuleNode) {
	        		ContextRuleNode currNode = (ContextRuleNode)currPair.getValue();
	        		if(depth == 0) {
	        			for(RelationshipNode currChild : currNode.getOccurrences()) {
	        				if(!g.containsVertex(currChild.getNode().getId())) {
	    	        			g.addVertex(currChild.getNode().getId());
	    	        		}
	    	        		if(g.findEdge(currNode.getBaseNode().getId(), currChild.getNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, currNode.getBaseNode().getId(), currChild.getNode().getId(), EdgeType.DIRECTED);
	    	        			this.directedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
    		        		Pair<Integer,Object> newPair = new Pair<Integer,Object>(depth+1, currChild);
    		        		q.add(newPair);
	        			}
	        			for(RelationshipNode currChild : currNode.getArgs()) {
	        				if(!g.containsVertex(currChild.getNode().getId())) {
	    	        			g.addVertex(currChild.getNode().getId());
	    	        		}
	    	        		if(g.findEdge(currNode.getBaseNode().getId(), currChild.getNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, currNode.getBaseNode().getId(), currChild.getNode().getId(), EdgeType.DIRECTED);
	    	        			this.directedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
    		        		Pair<Integer,Object> newPair = new Pair<Integer,Object>(depth+1, currChild);
    		        		q.add(newPair);
	        			}
	        		} //else pass
	        	} else if (currPair.getValue() instanceof RelationshipNode){
	        		RelationshipNode currNode = (RelationshipNode)currPair.getValue();
	        		for(Object currChild : currNode.getRelevantChildren()) {
	        			if(currChild instanceof ContextRuleNode) {
	        				ContextRuleNode typedChild = (ContextRuleNode)currChild;
	        				if(!g.containsVertex(typedChild.getBaseNode().getId())) {
	    	        			g.addVertex(typedChild.getBaseNode().getId());
	    	        		}
	    	        		if(g.findEdge(currNode.getNode().getId(), typedChild.getBaseNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, currNode.getNode().getId(), typedChild.getBaseNode().getId(), EdgeType.DIRECTED);
	    	        			this.directedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
	        			} else if(currChild instanceof RelationshipNode) {
	        				RelationshipNode typedChild = (RelationshipNode)currChild;
	        				if(!g.containsVertex(typedChild.getNode().getId())) {
	    	        			g.addVertex(typedChild.getNode().getId());
	    	        		}
	    	        		if(g.findEdge(currNode.getNode().getId(), typedChild.getNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, currNode.getNode().getId(), typedChild.getNode().getId(), EdgeType.DIRECTED);
	    	        			this.directedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
	    	        		if(depth < dist) {
	    		        		Pair<Integer,Object> newPair = new Pair<Integer,Object>(depth+1, currChild);
	    		        		q.add(newPair);
	    	        		}
	        			} else {
	        				System.out.println("ERROR:  Unrecognized type found as child node while drawing Context graphs");
	        			}
        			}
	        		for(Object currParent : currNode.getRelevantParents()) {
	        			if(currParent instanceof ContextRuleNode) {
	        				ContextRuleNode typedParent = (ContextRuleNode)currParent;
	        				if(!g.containsVertex(typedParent.getBaseNode().getId())) {
	    	        			g.addVertex(typedParent.getBaseNode().getId());
	    	        		}
	    	        		if(g.findEdge(typedParent.getBaseNode().getId(), currNode.getNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, typedParent.getBaseNode().getId(), currNode.getNode().getId(), EdgeType.DIRECTED);
	    	        			this.directedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
	        			} else if(currParent instanceof RelationshipNode) {
	        				RelationshipNode typedParent = (RelationshipNode)currParent;
	        				if(!g.containsVertex(typedParent.getNode().getId())) {
	    	        			g.addVertex(typedParent.getNode().getId());
	    	        		}
	    	        		if(g.findEdge(typedParent.getNode().getId(), currNode.getNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, typedParent.getNode().getId(), currNode.getNode().getId(), EdgeType.DIRECTED);
	    	        			this.directedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
	    	        		if(depth < dist) {
	    		        		Pair<Integer,Object> newPair = new Pair<Integer,Object>(depth+1, currParent);
	    		        		q.add(newPair);
	    	        		}
	        			} else {
	        				System.out.println("ERROR:  Unrecognized type found as parent node while drawing Context graphs");
	        			}
        			}
	        		for(Object currSibling : currNode.getRelevantSiblings()) {
	        			if(currSibling instanceof ContextRuleNode) {
	        				ContextRuleNode typedSibling = (ContextRuleNode)currSibling;
	        				if(!g.containsVertex(typedSibling.getBaseNode().getId())) {
	    	        			g.addVertex(typedSibling.getBaseNode().getId());
	    	        		}
	    	        		if(g.findEdge(typedSibling.getBaseNode().getId(), currNode.getNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, typedSibling.getBaseNode().getId(), currNode.getNode().getId(), EdgeType.UNDIRECTED);
	    	        			this.undirectedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
	        			} else if(currSibling instanceof RelationshipNode) {
	        				RelationshipNode typedSibling = (RelationshipNode)currSibling;
	        				if(!g.containsVertex(typedSibling.getNode().getId())) {
	    	        			g.addVertex(typedSibling.getNode().getId());
	    	        		}
	    	        		if(g.findEdge(typedSibling.getNode().getId(), currNode.getNode().getId()) == null) {
	    	        			g.addEdge(edgeNum, typedSibling.getNode().getId(), currNode.getNode().getId(), EdgeType.UNDIRECTED);
	    	        			this.undirectedEdges.add(edgeNum);
	    	        			edgeNum++;
	    	        		}
//	    	        		if(depth < dist) {
//	    		        		Pair<Integer,Object> newPair = new Pair<Integer,Object>(depth+1, currSibling);
//	    		        		q.add(newPair);
//	    	        		}
	        			} else {
	        				System.out.println("ERROR:  Unrecognized type found as sibling node while drawing Context graphs");
	        			}
	        		}
	        	} else {
	        		System.out.println("ERROR: Unrecognized type found while drawing Context graphs");
	        	}
	        }

	        drawSaveJungGraph(g, ruleNodes, dirString + RuleGraphViewer.cleanName(currRoot.getBaseNode().getName()));
		}
	}


	//do all the drawing and save to saveLoc, given a completed JUNG graph, g
	public void drawSaveJungGraph(Graph<Integer,Integer> g, final ArrayList<RuleNode> ruleNodes, String saveLoc) {
        // Layout implements the graph drawing logic
        Layout<Integer, Integer> layout = new CircleLayout<Integer, Integer>(g);
        layout.setSize(new Dimension(RuleGraphViewer.DRAW_WIDTH,RuleGraphViewer.DRAW_WIDTH));

        // VisualizationServer actually displays the graph
        BasicVisualizationServer<Integer,Integer> vv = new BasicVisualizationServer<Integer,Integer>(layout);
        vv.setPreferredSize(new Dimension(RuleGraphViewer.DRAW_WIDTH + 700,RuleGraphViewer.DRAW_WIDTH + 100)); //Sets the viewing area size

        // Transformer maps the vertex number to a vertex property
        Transformer<Integer,Paint> vertexColor = new Transformer<Integer,Paint>() {
            @Override
			public Paint transform(Integer i) {
            	RuleNode node = ruleNodes.get(i);
            	int colourInd = node.getColour().getVal();
                return Color.decode(RuleGraphViewer.INDEX_COLOURS[colourInd]);
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
        Transformer<Integer, Paint> edgePaint = new Transformer<Integer, Paint>() {
            @Override
            public Paint transform(Integer edgeNum) {    // s represents the edge
	            if (directedEdges.contains(edgeNum)){    // your condition
	                return Color.BLACK;
	            }
	            else if (undirectedEdges.contains(edgeNum)){
	                return Color.RED;
	            } else {
	            	System.out.println("ERROR: Found unknown edge type while drawing graph");
	            	return Color.YELLOW;
	            }
            }
        };


        vv.getRenderContext().setVertexFillPaintTransformer(vertexColor);
        vv.getRenderContext().setVertexShapeTransformer(vertexSize);
        vv.getRenderContext().setVertexLabelTransformer(vertexLabel);
        vv.getRenderContext().setEdgeDrawPaintTransformer(edgePaint);

        //Shows graph on screen
//		        JFrame frame = new JFrame("Rule Graph");
//		        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
//		        frame.getContentPane().add(vv);
//		        frame.pack();
//		        frame.setVisible(true);

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
        vis.getRenderContext().setEdgeDrawPaintTransformer(edgePaint);

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


	private class PairComparator implements Comparator<Pair<Float, Integer>> {
		@Override
		public int compare(Pair<Float,Integer> pr1, Pair<Float,Integer> pr2) {
		    return pr1.getKey().compareTo(pr2.getKey());
		}
	}
}