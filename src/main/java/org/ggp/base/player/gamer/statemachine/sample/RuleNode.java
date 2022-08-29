package org.ggp.base.player.gamer.statemachine.sample;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.ggp.base.player.gamer.statemachine.sample.RuleGraph.RuleNodeColour;
import org.ggp.base.player.gamer.statemachine.sample.RuleGraph.RuleNodeType;

public class RuleNode implements Comparable<Object>{
	private int id;
	private String name;
	private int argNum;
	private RuleNodeType type;
	private Set<RuleNode> children;
	private Set<RuleNode> parents;
	private RuleNodeColour colour;
	private HashMap<RuleNodeColour, Integer> childColourNums;

	public RuleNode(int id, String name, int argNum, RuleNodeType type) {
		this.id = id;
		this.name = name;
		this.argNum = argNum;
		this.type = type;
		this.children = new HashSet<RuleNode>();
		this.parents = new HashSet<RuleNode>();
		this.childColourNums = new HashMap<RuleNodeColour, Integer>();
		for(RuleNodeColour currColour: RuleNodeColour.values()) {
			this.childColourNums.put(currColour, 0);
		}
	}

	public RuleNode(int id, String name, int argNum, RuleNodeType type, RuleNodeColour colour) {
		this.id = id;
		this.name = name;
		this.argNum = argNum;
		this.type = type;
		this.children = new HashSet<RuleNode>();
		this.parents = new HashSet<RuleNode>();
		this.colour = colour;
		this.childColourNums = new HashMap<RuleNodeColour, Integer>();
		for(RuleNodeColour currColour: RuleNodeColour.values()) {
			this.childColourNums.put(currColour, 0);
		}
	}

	public RuleNode(int id, String name, int argNum, RuleNodeType type, Set<RuleNode> children, Set<RuleNode> parents,
			RuleNodeColour colour, HashMap<RuleNodeColour, Integer> childColourNums) {
		this.id = id;
		this.name = name;
		this.argNum = argNum;
		this.type = type;
		this.children = children;
		this.parents = parents;
		this.colour = colour;
		this.childColourNums = childColourNums;
	}

	public RuleNode(int id, String name, int argNum, RuleNodeColour colour) {
		this.id = id;
		this.name = name;
		this.argNum = argNum;
		this.type = null;
		this.children = new HashSet<RuleNode>();
		this.parents = new HashSet<RuleNode>();
		this.colour = colour;
		this.childColourNums = new HashMap<RuleNodeColour, Integer>();
		for(RuleNodeColour currColour: RuleNodeColour.values()) {
			this.childColourNums.put(currColour, 0);
		}
	}

	public RuleNode(int id, RuleNodeColour colour) {
		this.id = id;
		this.name = "";
		this.argNum = -2;
		this.type = null;
		this.children = new HashSet<RuleNode>();
		this.parents = new HashSet<RuleNode>();
		this.colour = colour;
		this.childColourNums = new HashMap<RuleNodeColour, Integer>();
		for(RuleNodeColour currColour: RuleNodeColour.values()) {
			this.childColourNums.put(currColour, 0);
		}
	}

	public void addChild(RuleNode newChild) {
		children.add(newChild);
		int oldNum = childColourNums.get(newChild.getColour());
		childColourNums.put(newChild.getColour(), oldNum + 1);
		newChild.addParent(this);
	}

	public void addParent(RuleNode newParent) { //called by addChild
		parents.add(newParent);
	}

	public int getId() {
		return id;
	}

	public String getName() {
		return name;
	}

	public int getArgNum() {
		return argNum;
	}

	public RuleNodeType getType() {
		return type;
	}

	public Set<RuleNode> getChildren() {
		return children;
	}

	public Set<RuleNode> getParents() {
		return parents;
	}

	public RuleNodeColour getColour() {
		return colour;
	}

	public void setColour(RuleNodeColour colour) {
		this.colour = colour;
	}

	public HashMap<RuleNodeColour, Integer> getChildColourNums() {
		return childColourNums;
	}

	@Override
	public String toString() {
		String returnVal = "RuleNode [id=" + id + ", name=" + name + ", argNum=" + argNum + ", type=" + type + ", colour=" + colour + "\nChildren:";
		for(RuleNode child : children) {
			returnVal += "\n" + child.shortToString();
		}
		returnVal += "]";
		return returnVal;
	}

	public String shortToString() {
		return "[id=" + id + ", name=" + name + ", argNum=" + argNum + ", colour=" + colour + "]";
	}

	@Override
	public int compareTo(Object o) {
		int ans = 0;
		try {
			RuleNode other = (RuleNode) o;
			if(this.children.size() > other.getChildren().size()) {
				ans = -1;
			} else if (this.children.size() < other.getChildren().size()) {
				ans = 1;
			}

		} catch(Exception e) {
			System.out.println(e);
		}
		return ans;
	}

	@Override
	public boolean equals(Object o) {
		try {
			RuleNode other = (RuleNode) o;
			return this.id == other.getId();
		} catch(Exception e) {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return ((Integer)this.id).hashCode();
	}

}