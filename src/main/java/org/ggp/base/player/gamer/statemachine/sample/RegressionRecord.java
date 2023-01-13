package org.ggp.base.player.gamer.statemachine.sample;

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

	@Override
	public String toString() {
		return "y=" + slope + "*x+" + intercept + ", r=" + r;
	}
}
