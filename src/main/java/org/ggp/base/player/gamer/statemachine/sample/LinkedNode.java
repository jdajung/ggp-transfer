package org.ggp.base.player.gamer.statemachine.sample;

public class LinkedNode {
	private MCTNode value;
	private LinkedNode next;

	public LinkedNode(MCTNode value) {
		this.value = value;
		this.next = null;
	}

	public MCTNode getValue() {
		return value;
	}

	public void setValue(MCTNode value) {
		this.value = value;
	}

	public LinkedNode getNext() {
		return next;
	}

	public void setNext(LinkedNode next) {
		this.next = next;
	}
}
