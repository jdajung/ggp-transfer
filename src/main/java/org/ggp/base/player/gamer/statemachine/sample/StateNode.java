package org.ggp.base.player.gamer.statemachine.sample;

import java.util.Arrays;
import java.util.HashMap;

public class StateNode {
	private int idNum;
	private HashMap<Integer, StateNode> children;
	private StateNode parent;

	public static final int ROOT_ID = -99;

	public StateNode(int idNum) {
		this.idNum = idNum;
		children = null;
		parent = null;
	}

	public int getIdNum() {
		return idNum;
	}

	public void setIdNum(int idNum) {
		this.idNum = idNum;
	}

	public HashMap<Integer, StateNode> getChildren() {
		return children;
	}

	public void setChildren(HashMap<Integer, StateNode> children) {
		this.children = children;
	}

	public StateNode getParent() {
		return parent;
	}

	public void setParent(StateNode parent) {
		this.parent = parent;
	}

	public void addChild(int childID) {
		if(children == null) {
			children = new HashMap<Integer, StateNode>();
		}
		if(!children.containsKey(childID)) {
			children.put(childID, new StateNode(childID));
		}
	}

	public boolean checkChild(int childID) {
		boolean ans = true;
		if(children == null || !children.containsKey(childID)) {
			ans = false;
		}
		return ans;
	}

	@Override
	public String toString() {
		String result = "";

//		result += idNum + " ";
//		if(children != null) {
//			for(int childID : children.keySet()) {
//				result += childID + " ";
//			}
//			result += "\n";
//			for(int childID : children.keySet()) {
//				result += children.get(childID).toString();
//			}
//		}
//		result += "\n";

		result += "( " + idNum + " ";
		if(children != null) {
			int[] sortedKeys = new int[children.size()];
			int i = 0;
			for(int childID : children.keySet()) {
				sortedKeys[i] = childID;
				i++;
			}
			Arrays.sort(sortedKeys);
			for(i=0;i<sortedKeys.length;i++) {
				result += children.get(sortedKeys[i]).toString();
			}
		}
		result += " ) ";

		return result;
	}


	public int numLeaves() {
		int count = 0;

		if(children == null) {
			count = 1;
		} else {
			for(int childID : children.keySet()) {
				count += children.get(childID).numLeaves();
			}
		}

		return count;
	}

	public StateNode deepCopy() {
		StateNode newNode = new StateNode(this.idNum);
		if(this.children != null) {
			newNode.setChildren(new HashMap<Integer, StateNode>());
			for (int childID : children.keySet()) {
				Integer newId = new Integer(childID);
				newNode.getChildren().put(newId, children.get(childID).deepCopy());
				newNode.getChildren().get(childID).setParent(newNode);
			}
		}
		return newNode;
	}
}

