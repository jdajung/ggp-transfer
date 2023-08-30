package org.ggp.base.player.gamer.statemachine.sample;

import org.apache.commons.math4.legacy.stat.regression.SimpleRegression;

public class RegressionRecord {
	private double slope;
	private double intercept;
	private double numEntries;
	private double r;

	public RegressionRecord(double slope, double intercept, double numEntries, double r) {
		this.slope = slope;
		this.intercept = intercept;
		this.numEntries = numEntries;
		this.r = r;
	}

	public RegressionRecord(SimpleRegression simple) {
		this.slope = simple.getSlope();
		this.intercept = simple.getIntercept();
		this.numEntries = simple.getN();
		this.r = simple.getR();
	}

	public double predict(double x) {
		return slope*x + intercept;
	}

	public double getSlope() {
		return slope;
	}

	public double getIntercept() {
		return intercept;
	}

	public double getN() {
		return numEntries;
	}

	public double getR() {
		return r;
	}

	public void setR(double r) {
		this.r = r;
	}

	@Override
	public String toString() {
		return "y=" + slope + "*x+" + intercept + ", r=" + r;
	}
}
