package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Random;

import org.ggp.base.player.gamer.statemachine.sample.RuleGraph.RuleNodeColour;

public class EditDistance {
	private ArrayList<EDRuleNode> g1;
	private ArrayList<EDRuleNode> g2;
	private HashMap<Integer, EDRuleNode> g1IDtoEdnode;
	private HashMap<Integer, EDRuleNode> g2IDtoEdnode;
	private HashMap<Integer, Integer> mapping; //g1 -> g2
	private HashMap<Integer, Integer> revMapping; //g2 -> g1
	private float distVal;
	private HashMap<ArrayList<Integer>,HashSet<EDRuleNode>> g1ChildColourMap;

	public static final float BIG_NUM = 1000000;
	public static final float INSERT_EDGE_COST = 1;
	public static final float DELETE_EDGE_COST = 1;
	public static final float INSERT_NODE_COST = 1;
	public static final float DELETE_NODE_COST = 1;
	public static final float MISSING_KNOWN_CHILD_COST = 4;
	public static final float MISSING_KNOWN_PARENT_COST = 4;
	public static final float CHANGE_NODE_COLOUR_COST = BIG_NUM;

	public static final int MAX_EXPAND_DEPTH = 5;

	public static enum CostType {
		COLOUR_ONLY,
		COLOUR_AND_KNOWN_EDGES
	}

	private class EDRuleNode extends RuleNode {
		private HashSet<EDRuleNode> expectedChildren;
		private HashSet<EDRuleNode> expectedParents;
		private ArrayList<Integer> childColourClass;
		private long whenInvalidated;

		public EDRuleNode(RuleNode rn) {
			super(rn.getId(), rn.getName(), rn.getArgNum(), rn.getType(), rn.getChildren(), rn.getParents(), rn.getColour(), rn.getChildColourNums());
			this.expectedChildren = new HashSet<EDRuleNode>();
			this.expectedParents = new HashSet<EDRuleNode>();
			this.whenInvalidated = -1;

			this.childColourClass = new ArrayList<Integer>();
			for(RuleNodeColour colour : RuleNodeColour.values()) {
				childColourClass.add(0);
			}
			for(RuleNodeColour colourNum : this.getChildColourNums().keySet()) {
				childColourClass.set(colourNum.getVal(), this.getChildColourNums().get(colourNum));
			}
		}

		public HashSet<EDRuleNode> getExpectedChildren() {
			return expectedChildren;
		}

		public HashSet<EDRuleNode> getExpectedParents() {
			return expectedParents;
		}

		public long getWhenInvalidated() {
			return whenInvalidated;
		}

		public void invalidate(long when) {
			this.whenInvalidated = when;
		}

		public ArrayList<Integer> getChildColourClass() {
			return this.childColourClass;
		}

		@Override
		public int compareTo(Object o) {
			int ans = 0;
			try {
				EDRuleNode other = (EDRuleNode) o;
				int g1ColourClassSize = g1ChildColourMap.get(this.childColourClass).size();
				int otherG1ColourClassSize = g1ChildColourMap.get(other.getChildColourClass()).size();
				int expectedNum = this.expectedChildren.size() + this.expectedParents.size();
				int otherExpectedNum = other.getExpectedChildren().size() + other.getExpectedParents().size();
				if(g1ColourClassSize == 1 && !(otherG1ColourClassSize == 1)) {
					ans = -1;
				} else if(!(g1ColourClassSize == 1) && otherG1ColourClassSize == 1) {
					ans = 1;
				} else {
					if(expectedNum > otherExpectedNum) {
						ans = -1;
					} else if (expectedNum < otherExpectedNum) {
						ans = 1;
					} else {
						if(g1ColourClassSize < otherG1ColourClassSize) {
							ans = -1;
						} else if(g1ColourClassSize > otherG1ColourClassSize) {
							ans = 1;
						} else {
							ans = super.compareTo(o);
						}
					}
				}

			} catch(Exception e) {
				System.out.println(e);
			}
			return ans;
		}
	}

	private class EDCost {
		private long whenUpdated;
		private float cost;

		public EDCost() {
			this.whenUpdated = -1;
			this.cost = -1;
		}

		public long getWhenUpdated() {
			return whenUpdated;
		}

		public float getCost() {
			return cost;
		}

		public void update(long when, float cost) {
			this.whenUpdated = when;
			this.cost = cost;
		}
	}


	public EditDistance(ArrayList<RuleNode> g1, ArrayList<RuleNode> g2) {
		this.g1 = new ArrayList<EDRuleNode>();
		this.g2 = new ArrayList<EDRuleNode>();
		this.g1IDtoEdnode = new HashMap<Integer,EDRuleNode>();
		this.g2IDtoEdnode = new HashMap<Integer,EDRuleNode>();

		g1ChildColourMap = new HashMap<ArrayList<Integer>,HashSet<EDRuleNode>>();
//		this.g1 = (ArrayList<RuleNode>) g1.clone();
//		this.g2 = (ArrayList<RuleNode>) g2.clone();
		for(RuleNode node : g1) {
			EDRuleNode newNode = new EDRuleNode(node);
			this.g1.add(newNode);
			this.g1IDtoEdnode.put(newNode.getId(), newNode);
			ArrayList<Integer> childColours = newNode.getChildColourClass();
			if(!g1ChildColourMap.containsKey(childColours)) {
				g1ChildColourMap.put(childColours, new HashSet<EDRuleNode>());
			}
			g1ChildColourMap.get(childColours).add(newNode);
		}
		for(RuleNode node : g2) {
			EDRuleNode newNode = new EDRuleNode(node);
			this.g2.add(newNode);
			this.g2IDtoEdnode.put(newNode.getId(), newNode);
		}

//		for(ArrayList<Integer> key : g1ChildColourMap.keySet()) {
//			System.out.println("**" + key);
//			System.out.println(g1ChildColourMap.get(key).size());
//			for(EDRuleNode node : g1ChildColourMap.get(key)) {
//				System.out.println(node.getName());
//			}
//		}

		Collections.shuffle(this.g2, new Random(8288034731336811092L));
		Collections.sort(this.g1);
		Collections.sort(this.g2);
//		Collections.shuffle(this.g2, new Random(8288034731336811092L));
//		Collections.sort(this.g2, Collections.reverseOrder());
		this.mapping = new HashMap<Integer, Integer>();
		this.revMapping = new HashMap<Integer, Integer>();

		this.distVal = -1;
	}

	public ArrayList<EDRuleNode> getG1() {
		return g1;
	}

	public ArrayList<EDRuleNode> getG2() {
		return g2;
	}

	public HashMap<Integer, Integer> getMapping() {
		return mapping;
	}

	public HashMap<Integer, Integer> getRevMapping() {
		return revMapping;
	}

	public float getDistance() {
		return distVal;
	}

	public String mappedNamesToString() {
		String outStr = "";
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
		//-1 (ie. no match) are reported from g1 to g2 only (not the reverse)
		return outStr;
	}

	private float assignmentCost(CostType type, int from, int to) {
		float ans = 0;
		EDRuleNode ednode1, ednode2;

		if(from == -1 && to == -1) {
			//pass
		} else if(from == -1) {
			ednode2 = g2.get(to);
			ans = INSERT_NODE_COST + INSERT_EDGE_COST * ednode2.getChildren().size();
			//No check for known edges, since 'from' node doesn't exist to get edges from
		} else if(to == -1) {
			ednode1 = g1.get(from);
			ans = DELETE_NODE_COST + DELETE_EDGE_COST * ednode1.getChildren().size();
			if (type == CostType.COLOUR_AND_KNOWN_EDGES) {
				ans += MISSING_KNOWN_CHILD_COST * ednode1.getExpectedChildren().size();
				ans += MISSING_KNOWN_PARENT_COST * ednode1.getExpectedParents().size();
			}
		} else {
			ednode1 = g1.get(from);
			ednode2 = g2.get(to);
			if(type == CostType.COLOUR_ONLY || type == CostType.COLOUR_AND_KNOWN_EDGES) {
				if(ednode1.getColour() != ednode2.getColour()) {
					ans += CHANGE_NODE_COLOUR_COST;
				}
				for(RuleNodeColour currColour: RuleNodeColour.values()) {
					int initNum = ednode1.getChildColourNums().get(currColour);
					int finalNum = ednode2.getChildColourNums().get(currColour);
					if(initNum > finalNum) {
						ans += DELETE_EDGE_COST * (initNum - finalNum);
					} else if(finalNum > initNum) {
						ans += INSERT_EDGE_COST * (finalNum - initNum);
					}
				}
			}
			if (type == CostType.COLOUR_AND_KNOWN_EDGES) {
				for(EDRuleNode expected : ednode1.getExpectedChildren()) {
					if (!ednode2.getChildren().contains(expected)) {
						ans += MISSING_KNOWN_CHILD_COST;
					}
				}
				for(EDRuleNode expected : ednode1.getExpectedParents()) {
					if (!ednode2.getParents().contains(expected)) {
						ans += MISSING_KNOWN_PARENT_COST;
					}
				}
			}
		}

		return ans;
	}

	//original matrix from paper, with large numbers of empty cells
//	private ArrayList<ArrayList<Float>> genCostMatrix(CostType type) {
//		int matHeight = 2 * g2.size();
//		int matWidth = 2 * g1.size();
//		ArrayList<ArrayList<Float>> c = new ArrayList<ArrayList<Float>>(matHeight);
//		for(int i=0;i<matHeight;i++) {
//			c.set(i, new ArrayList<Float>(matWidth));
//		}
//
//		//top left (substitutions)
//		for(int i=0;i<matHeight/2;i++) {
//			for(int j=0;j<matWidth/2;j++) {
//				c.get(i).set(j, assignmentCost(type, i, j));
//			}
//		}
//		//top right (deletions)
//		for(int i=0;i<matHeight/2;i++) {
//			for(int j=matWidth/2;j<matWidth;j++) {
//				if(j-matWidth/2 == i) {
//					c.get(i).set(j, assignmentCost(type, i, -1));
//				} else {
//					c.get(i).set(j, BIG_NUM);
//				}
//			}
//		}
//		//bottom left (insertions)
//		for(int i=matHeight/2;i<matHeight;i++) {
//			for(int j=0;j<matWidth/2;j++) {
//				if(i-matHeight/2 == j) {
//					c.get(i).set(j, assignmentCost(type, -1, j));
//				} else {
//					c.get(i).set(j, BIG_NUM);
//				}
//			}
//		}
//		//bottom right (pass)
//		for(int i=matHeight/2;i<matHeight;i++) {
//			for(int j=matWidth/2;j<matWidth;j++) {
//				c.get(i).set(j, new Float(0));
//			}
//		}
//
//		return c;
//	}


//	private ArrayList<ArrayList<Float>> genCostMatrix(CostType type) {
//		int matHeight = g1.size() + 1;
//		int matWidth = g2.size() + 1;
//		ArrayList<ArrayList<Float>> c = new ArrayList<ArrayList<Float>>(matHeight);
//		for(int i=0;i<matHeight;i++) {
//			c.add(new ArrayList<Float>(matWidth));
//			for(int j=0;j<matWidth;j++) {
//				c.get(i).add(new Float(0));
//			}
//		}
//
//		//top left (substitutions)
//		for(int i=0;i<matHeight-1;i++) {
//			for(int j=0;j<matWidth-1;j++) {
//				c.get(i).set(j, assignmentCost(type, i, j));
//			}
//		}
//		//top right (deletions)
//		for(int i=0;i<matHeight - 1;i++) {
//			int j = matWidth - 1;
//			c.get(i).set(j, assignmentCost(type, i, -1));
//		}
//		//bottom left (insertions)
//		for(int j=0;j<matWidth - 1;j++) {
//			int i = matHeight - 1;
//			c.get(i).set(j, assignmentCost(type, -1, j));
//		}
//		//bottom right (pass)
//		int i = matHeight - 1;
//		int j = matWidth - 1;
//		c.get(i).set(j, new Float(0));
//
//		return c;
//	}


	//use memoization to reduce the number of cost calculations
	public float calcSingleCost(int from, int to, long when, CostType type, EDCost[][] costMatrix) {
		EDCost entry = costMatrix[from][to];
		if (from < g1.size()) {
			long whenInvalid = g1.get(from).getWhenInvalidated();
			if (entry.getWhenUpdated() == -1 || whenInvalid >= entry.getWhenUpdated()) {
				if (to < g2.size()) {
					entry.update(when, assignmentCost(type, from, to));
				} else {
					entry.update(when, assignmentCost(type, from, -1));
				}
			}
		} else {
			if (entry.getWhenUpdated() == -1) {
				if (to < g2.size()) {
					entry.update(when, assignmentCost(type, -1, to));
				} else {
					entry.update(when, assignmentCost(type, -1, -1));
				}
			}
		}
		return entry.getCost();
	}



	public void updateExpectedEdges(int from, int to, long when) {
		EDRuleNode ednode1 = g1.get(from);
		EDRuleNode ednode2 = g2.get(to);

		for(RuleNode node1Parent : ednode1.getParents()) {
			EDRuleNode ednode1Parent = this.g1IDtoEdnode.get(node1Parent.getId());
			ednode1Parent.getExpectedChildren().add(ednode2);
//			This was wrong. ednode1Parent should have expected edge to ednode2, not ednode2's children
//			for(RuleNode node2Child : ednode2.getChildren()) {
//				EDRuleNode ednode2Child = this.g2IDtoEdnode.get(node2Child.getId());
//				ednode1Parent.getExpectedChildren().add(ednode2Child);
//			}
			ednode1Parent.invalidate(when);
		}
		for(RuleNode node1Child : ednode1.getChildren()) {
			EDRuleNode ednode1Child = this.g1IDtoEdnode.get(node1Child.getId());
			ednode1Child.getExpectedParents().add(ednode2);
//			for(RuleNode node2Parent : ednode2.getParents()) {
//				EDRuleNode ednode2Parent = this.g2IDtoEdnode.get(node2Parent.getId());
//				ednode1Child.getExpectedChildren().add(ednode2Parent);
//			}
			ednode1Child.invalidate(when);
		}
	}


	public float calcDistance(CostType type) {
		int matHeight = g1.size() + 1;
		int matWidth = g2.size() + 1;
		EDCost[][] costMatrix = new EDCost[matHeight][matWidth];
		for(int i=0;i<matHeight;i++) {
			for(int j=0;j<matWidth;j++) {
				costMatrix[i][j] = new EDCost();
			}
		}

		float distance = 0;
		boolean[] rowUsed = new boolean[matHeight];
		boolean[] colUsed = new boolean[matWidth];
		long when = 0;
		long rowsAssigned = 0;

		while(rowsAssigned < matHeight - 1) {
			int i = -1; //row index
			EDRuleNode currMin = null;
			for(int currRow=0;currRow<matHeight-1;currRow++) {
				if(!rowUsed[currRow]) {
					if(i == -1 || this.g1.get(currRow).compareTo(currMin) < 0) {
						i = currRow;
						currMin = this.g1.get(currRow);
					}
				}
			}

			System.out.println("* " + when + " *");
			System.out.println(currMin.getName() + "{" + currMin.getColour() + ";" + currMin.getArgNum() + "}");
			System.out.println("Class size: " + g1ChildColourMap.get(currMin.getChildColourClass()).size());
			System.out.println("Expected children: " + currMin.getExpectedChildren().size());
			System.out.println("Expected parents: " + currMin.getExpectedParents().size());

			int minCol = -1;
			int minRow = -1;
			for(int j=0;j<colUsed.length;j++) { //column index
				if (!colUsed[j]) {
					if (minCol == -1 || calcSingleCost(i,j,when,type,costMatrix) < calcSingleCost(i,minCol,when,type,costMatrix)) {
						minCol = j;
					}
				}
			}
			if (minCol == colUsed.length - 1) {//deletion
				mapping.put(i, -1);
				distance += calcSingleCost(i,minCol,when,type,costMatrix);
				rowUsed[i] = true;
				rowsAssigned++;
				//No cost invalidations, because there is no 'to' node to pull expected edges from
			} else {//not deletion
				for(int k=0;k<rowUsed.length;k++) { //secondary row index
					if(!rowUsed[k] && i!=k) {
						if (minRow == -1 || calcSingleCost(k,minCol,when,type,costMatrix) < calcSingleCost(minRow,minCol,when,type,costMatrix)) {
							minRow = k;
						}
					}
				}
				if (calcSingleCost(i,minCol,when,type,costMatrix) <= calcSingleCost(minRow,minCol,when,type,costMatrix)) { //original row was better substitution
					mapping.put(i, minCol);
					revMapping.put(minCol, i);
					distance += calcSingleCost(i,minCol,when,type,costMatrix);
					rowUsed[i] = true;
					colUsed[minCol] = true;
					rowsAssigned++;
					updateExpectedEdges(i,minCol,when);
					String g1NodeStr = this.g1.get(i).getName() + "{" + this.g1.get(i).getColour() + ";" + this.g1.get(i).getArgNum() + "}";
					String g2NodeStr = this.g2.get(minCol).getName() + "{" + this.g2.get(minCol).getColour() + ";" + this.g2.get(minCol).getArgNum() + "}";
					System.out.println("Distance: " + calcSingleCost(i,minCol,when,type,costMatrix) + " " + g1NodeStr + " " + g2NodeStr);
				} else { //searched row was better
					if(minRow == rowUsed.length - 1) { //insertion
						revMapping.put(minCol, -1);
						distance += calcSingleCost(minRow,minCol,when,type,costMatrix);
						colUsed[minCol] = true;
						//No cost invalidations, because there are no child or parent nodes in 'from' graph to invalidate
					} else { //actual substitution
						mapping.put(minRow, minCol);
						revMapping.put(minCol, minRow);
						distance += calcSingleCost(minRow,minCol,when,type,costMatrix);
						rowUsed[minRow] = true;
						colUsed[minCol] = true;
						rowsAssigned++;
						updateExpectedEdges(minRow,minCol,when);
						String g1NodeStr = this.g1.get(minRow).getName() + "{" + this.g1.get(minRow).getColour() + ";" + this.g1.get(minRow).getArgNum() + "}";
						String g2NodeStr = this.g2.get(minCol).getName() + "{" + this.g2.get(minCol).getColour() + ";" + this.g2.get(minCol).getArgNum() + "}";
						System.out.println("Distance: " + calcSingleCost(minRow,minCol,when,type,costMatrix) + " " + g1NodeStr + " " + g2NodeStr);
					}
				}
			}

			when++;
		}

		int i = rowUsed.length - 1;
		for(int j=0;j<colUsed.length-1;j++) { //perform any insertions for any remaining columns
			if(!colUsed[j]) {
				revMapping.put(j, -1);
				distance += calcSingleCost(i,j,when,type,costMatrix);
				//No invalidations for insertions, as before
			}
		}

		mapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
		revMapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
		distVal = distance;
		return distance;
	}



//	Version of calcDistance from before dynamic cost calculations
//	(generates matrix once, and then uses costs to for whole distance calculation)
//	public float calcDistance(CostType type) {
//		float distance = 0;
//		ArrayList<ArrayList<Float>> costMatrix = genCostMatrix(type);
//		boolean[] rowUsed = new boolean[costMatrix.size()];
//		boolean[] colUsed = new boolean[costMatrix.get(0).size()];
//		int i = 0; //row index
//		while(i < costMatrix.size() - 1) {
//			if (!rowUsed[i]) {
//				int minCol = -1;
//				int minRow = -1;
//				for(int j=0;j<colUsed.length;j++) { //column index
//					if (!colUsed[j]) {
//						if (minCol == -1 || costMatrix.get(i).get(j) < costMatrix.get(i).get(minCol)) {
//							minCol = j;
//						}
//					}
//				}
//				if (minCol == colUsed.length - 1) {//deletion
//					mapping.put(i, -1);
//					distance += costMatrix.get(i).get(minCol);
//					rowUsed[i] = true;
//					i++;
//				} else {//not deletion
//					for(int k=0;k<rowUsed.length;k++) { //secondary row index
//						if(!rowUsed[k] && i!=k) {
//							if (minRow == -1 || costMatrix.get(k).get(minCol) < costMatrix.get(minRow).get(minCol)) {
//								minRow = k;
//							}
//						}
//					}
//					if (costMatrix.get(i).get(minCol) <= costMatrix.get(minRow).get(minCol)) { //original row was better substitution
//						mapping.put(i, minCol);
//						revMapping.put(minCol, i);
//						distance += costMatrix.get(i).get(minCol);
//						rowUsed[i] = true;
//						colUsed[minCol] = true;
//						i++;
//					} else { //searched row was better
//						if(minRow == rowUsed.length - 1) { //insertion
//							revMapping.put(minCol, -1);
//							distance += costMatrix.get(minRow).get(minCol);
//							colUsed[minCol] = true;
//						} else { //actual substitution
//							mapping.put(minRow, minCol);
//							revMapping.put(minCol, minRow);
//							distance += costMatrix.get(minRow).get(minCol);
//							rowUsed[minRow] = true;
//							colUsed[minCol] = true;
//						}
//					}
//				}
//			} else { //row has already been removed
//				i++;
//			}
//		}
//
//		i = rowUsed.length - 1;
//		for(int j=0;j<colUsed.length-1;j++) { //perform any insertions for any remaining columns
//			if(!colUsed[j]) {
//				revMapping.put(j, -1);
//				distance += costMatrix.get(i).get(j);
//			}
//		}
//
//		mapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
//		revMapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
//		distVal = distance;
//		return distance;
//	}


//	calcDistance from before min finding on g1, but after dynamic matrix calculations
//	public float calcDistance(CostType type) {
//		int matHeight = g1.size() + 1;
//		int matWidth = g2.size() + 1;
//		EDCost[][] costMatrix = new EDCost[matHeight][matWidth];
//		for(int i=0;i<matHeight;i++) {
//			for(int j=0;j<matWidth;j++) {
//				costMatrix[i][j] = new EDCost();
//			}
//		}
//
//		float distance = 0;
//		boolean[] rowUsed = new boolean[matHeight];
//		boolean[] colUsed = new boolean[matWidth];
//		long when = 0;
//
//		int i = 0; //row index
//		while(i < matHeight - 1) {
//			if (!rowUsed[i]) {
//				int minCol = -1;
//				int minRow = -1;
//				for(int j=0;j<colUsed.length;j++) { //column index
//					if (!colUsed[j]) {
//						if (minCol == -1 || calcSingleCost(i,j,when,type,costMatrix) < calcSingleCost(i,minCol,when,type,costMatrix)) {
//							minCol = j;
//						}
//					}
//				}
//				if (minCol == colUsed.length - 1) {//deletion
//					mapping.put(i, -1);
//					distance += calcSingleCost(i,minCol,when,type,costMatrix);
//					rowUsed[i] = true;
//					//No cost invalidations, because there is no 'to' node to pull expected edges from
//					i++;
//				} else {//not deletion
//					for(int k=0;k<rowUsed.length;k++) { //secondary row index
//						if(!rowUsed[k] && i!=k) {
//							if (minRow == -1 || calcSingleCost(k,minCol,when,type,costMatrix) < calcSingleCost(minRow,minCol,when,type,costMatrix)) {
//								minRow = k;
//							}
//						}
//					}
//					if (calcSingleCost(i,minCol,when,type,costMatrix) <= calcSingleCost(minRow,minCol,when,type,costMatrix)) { //original row was better substitution
//						mapping.put(i, minCol);
//						revMapping.put(minCol, i);
//						distance += calcSingleCost(i,minCol,when,type,costMatrix);
//						rowUsed[i] = true;
//						colUsed[minCol] = true;
//						updateExpectedEdges(i,minCol,when);
//						System.out.println(calcSingleCost(i,minCol,when,type,costMatrix) + " " + this.g1.get(i).getName() + " " + this.g2.get(minCol).getName());
//						i++;
//					} else { //searched row was better
//						if(minRow == rowUsed.length - 1) { //insertion
//							revMapping.put(minCol, -1);
//							distance += calcSingleCost(minRow,minCol,when,type,costMatrix);
//							colUsed[minCol] = true;
//							//No cost invalidations, because there are no child or parent nodes in 'from' graph to invalidate
//						} else { //actual substitution
//							mapping.put(minRow, minCol);
//							revMapping.put(minCol, minRow);
//							distance += calcSingleCost(minRow,minCol,when,type,costMatrix);
//							rowUsed[minRow] = true;
//							colUsed[minCol] = true;
//							updateExpectedEdges(minRow,minCol,when);
//							System.out.println(calcSingleCost(minRow,minCol,when,type,costMatrix) + " " + this.g1.get(minRow).getName() + " " + this.g2.get(minCol).getName());
//						}
//					}
//				}
//			} else { //row has already been removed
//				i++;
//			}
//
//			when++;
//		}
//
//		i = rowUsed.length - 1;
//		for(int j=0;j<colUsed.length-1;j++) { //perform any insertions for any remaining columns
//			if(!colUsed[j]) {
//				revMapping.put(j, -1);
//				distance += calcSingleCost(i,j,when,type,costMatrix);
//				//No invalidations for insertions, as before
//			}
//		}
//
//		mapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
//		revMapping.put(StateNode.ROOT_ID, StateNode.ROOT_ID);
//		distVal = distance;
//		return distance;
//	}

}