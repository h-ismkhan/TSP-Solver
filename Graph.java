import java.io.File;
import java.util.Scanner;
public class Graph {

	private double max_Y = 0, max_X = 0, min_X = 1000000, min_Y = 1000000;
	private double M_PI = 3.14159265358979323846264;
	private double M_RRR = 6378388.0;

	private static interface CostFunction_1 {
		int invoke(int a, int b);
	}

	private static interface CostFunction_2 {
		int invoke(double x1, double y1, double x2, double y2);
	}

	private CostFunction_1 distance_1;
	private CostFunction_2 distance_2;
	private point[] nodeptr;

	public static class point {
		public double x;
		public double y;
	}

	public final point getItem(int i) {
		return nodeptr[i];
	}

	private static double dtrunc(double x) {
		int k;
		k = (int) x;
		x = (double) k;
		return x;
	}

	private int roundDistance(int i, int j) {
		double xd = nodeptr[i].x - nodeptr[j].x;
		double yd = nodeptr[i].y - nodeptr[j].y;
		double r = Math.sqrt(xd * xd + yd * yd) + 0.5;
		return (int) r;
	}

	private int ceilDistance(int i, int j) {
		double xd = nodeptr[i].x - nodeptr[j].x;
		double yd = nodeptr[i].y - nodeptr[j].y;
		double r = Math.sqrt(xd * xd + yd * yd) + 0.000000001;
		return (int) r;
	}

	private int geoDistance(int i, int j) {
		double deg, min, lati, latj, longi, longj, q1, q2, q3;
		double x1 = nodeptr[i].x;
		double x2 = nodeptr[j].x;
		double y1 = nodeptr[i].y;
		double y2 = nodeptr[j].y;
		deg = dtrunc(x1);
		min = x1 - deg;
		lati = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;
		deg = dtrunc(x2);
		min = x2 - deg;
		latj = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;

		deg = dtrunc(y1);
		min = y1 - deg;
		longi = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;
		deg = dtrunc(y2);
		min = y2 - deg;
		longj = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;

		q1 = Math.cos(longi - longj);
		q2 = Math.cos(lati - latj);
		q3 = Math.cos(lati + latj);
		return (int) (6378.388 * Math.acos(0.5 * ((1.0 + q1) * q2 - (1.0 - q1)
				* q3)) + 1.0);
	}

	private int attDistance(int i, int j) {
		double xd = nodeptr[i].x - nodeptr[j].x;
		double yd = nodeptr[i].y - nodeptr[j].y;
		double rij = Math.sqrt((xd * xd + yd * yd) / 10.0);
		double tij = dtrunc(rij);
		int dij;
		if (tij < rij) {
			dij = (int) tij + 1;
		} else {
			dij = (int) tij;
		}
		return dij;
	}

	private int geomDistance(int i, int j) {
		point Na = nodeptr[i];
		point Nb = nodeptr[j];
		double lati = this.M_PI * (Na.x / 180.0);
		double latj = this.M_PI * (Nb.x / 180.0);
		double longi = this.M_PI * (Na.y / 180.0);
		double longj = this.M_PI * (Nb.y / 180.0);
		double q1 = Math.cos(latj) * Math.sin(longi - longj);
		double q3 = Math.sin((longi - longj) / 2.0);
		double q4 = Math.cos((longi - longj) / 2.0);
		double q2 = Math.sin(lati + latj) * q3 * q3 - Math.sin(lati - latj)
				* q4 * q4;
		double q5 = Math.cos(lati - latj) * q4 * q4 - Math.cos(lati + latj)
				* q3 * q3;
		return (int) (M_RRR * Math.atan2(Math.sqrt(q1 * q1 + q2 * q2), q5) + 1.0);
	}

	private int roundDistance(double x1, double y1, double x2, double y2) {
		double xd = x1 - x2;
		double yd = y1 - y2;
		double r = Math.sqrt(xd * xd + yd * yd) + 0.5;
		return (int) r;
	}

	private int ceilDistance(double x1, double y1, double x2, double y2) {
		double xd = x1 - x2;
		double yd = y1 - y2;
		double r = Math.sqrt(xd * xd + yd * yd) + 0.000000001;
		return (int) r;
	}

	private int geoDistance(double x1, double y1, double x2, double y2) {
		double deg, min, lati, latj, longi, longj, q1, q2, q3;
		deg = dtrunc(x1);
		min = x1 - deg;
		lati = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;
		deg = dtrunc(x2);
		min = x2 - deg;
		latj = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;
		deg = dtrunc(y1);
		min = y1 - deg;
		longi = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;
		deg = dtrunc(y2);
		min = y2 - deg;
		longj = this.M_PI * (deg + 5.0 * min / 3.0) / 180.0;
		q1 = Math.cos(longi - longj);
		q2 = Math.cos(lati - latj);
		q3 = Math.cos(lati + latj);
		return (int) (6378.388 * Math.acos(0.5 * ((1.0 + q1) * q2 - (1.0 - q1)
				* q3)) + 1.0);
	}

	private int attDistance(double x1, double y1, double x2, double y2) {
		double xd = x1 - x2;
		double yd = y1 - y2;
		double rij = Math.sqrt((xd * xd + yd * yd) / 10.0);
		double tij = dtrunc(rij);
		int dij;

		if (tij < rij) {
			dij = (int) tij + 1;
		} else {
			dij = (int) tij;
		}
		return dij;
	}

	private int geomDistance(double x1, double y1, double x2, double y2) {
		double lati = this.M_PI * (x1 / 180.0);
		double latj = this.M_PI * (x2 / 180.0);
		double longi = this.M_PI * (y1 / 180.0);
		double longj = this.M_PI * (y2 / 180.0);
		double q1 = Math.cos(latj) * Math.sin(longi - longj);
		double q3 = Math.sin((longi - longj) / 2.0);
		double q4 = Math.cos((longi - longj) / 2.0);
		double q2 = Math.sin(lati + latj) * q3 * q3 - Math.sin(lati - latj)
				* q4 * q4;
		double q5 = Math.cos(lati - latj) * q4 * q4 - Math.cos(lati + latj)
				* q3 * q3;
		return (int) (M_RRR * Math.atan2(Math.sqrt(q1 * q1 + q2 * q2), q5) + 1.0);
	}

	private String GraphName = "";

	public final double getItem(int i, int j) {
		return 0;
	}

	public final double getMax_X() {
		return this.max_X;
	}

	public final double getMax_Y() {
		return this.max_Y;
	}

	public final double getMin_X() {
		return this.min_X;
	}

	public final double getMin_Y() {
		return this.min_Y;
	}

	public final int getNumber_Of_Node() {
		return this.nodeptr.length;
	}

	public final String getGraph_Name() {
		return this.GraphName;
	}

	public Graph(String Directory, String ProblemName) {
		this.InitializeGraph(Directory + "\\" + ProblemName + ".tsp" + "\\"
				+ ProblemName + ".tsp");
	}

	public Graph(String path) {
		this.InitializeGraph(path);
	}

	int GetDimension(String input) {
		String ret = "";
		int i = 0;
		while (!(input.charAt(i) <= '9' && input.charAt(i) >= '0')) {
			i++;
			if (i == input.length())
				return 0;
		}
		while (input.charAt(i) <= '9' && input.charAt(i) >= '0') {
			ret = ret + input.charAt(i);
			i++;
			if (i == input.length())
				break;
		}
		return Integer.parseInt(ret);
	}

	String GetType(String input) {
		return null;
	}

	private void InitializeGraph(String path) {
		Scanner reader = null;
		try {
			reader = new Scanner(new File(path));
		} catch (Exception e) {
		}
		String temp = "";
		while (reader.hasNextLine()) {
			temp = reader.nextLine();
			if (temp.indexOf("EUC_2D") >= 0) {
				this.distance_1 = new Graph.CostFunction_1() {
					public int invoke(int a, int b) {
						return roundDistance(a, b);
					}
				};
				this.distance_2 = new Graph.CostFunction_2() {
					public int invoke(double x1, double y1, double x2, double y2) {
						return roundDistance(x1, y1, x2, y2);
					}
				};
			} else if (temp.indexOf("CEIL_2D") >= 0) {
				this.distance_1 = new Graph.CostFunction_1() {
					public int invoke(int a, int b) {
						return ceilDistance(a, b);
					}
				};
				this.distance_2 = new Graph.CostFunction_2() {
					public int invoke(double x1, double y1, double x2, double y2) {
						return ceilDistance(x1, y1, x2, y2);
					}
				};

			} else if (temp.indexOf("GEO") >= 0) {

				this.distance_1 = new Graph.CostFunction_1() {
					public int invoke(int a, int b) {
						return geoDistance(a, b);
					}
				};
				this.distance_2 = new Graph.CostFunction_2() {
					public int invoke(double x1, double y1, double x2, double y2) {
						return geoDistance(x1, y1, x2, y2);
					}
				};
			} else if (temp.indexOf("ATT") >= 0) {
				this.distance_1 = new Graph.CostFunction_1() {
					public int invoke(int a, int b) {
						return attDistance(a, b);
					}
				};
				this.distance_2 = new Graph.CostFunction_2() {
					public int invoke(double x1, double y1, double x2, double y2) {
						return attDistance(x1, y1, x2, y2);
					}
				};
			} else if (temp.indexOf("GEOM") >= 0) {
				this.distance_1 = new Graph.CostFunction_1() {
					public int invoke(int a, int b) {
						return geomDistance(a, b);
					}
				};
				this.distance_2 = new Graph.CostFunction_2() {
					public int invoke(double x1, double y1, double x2, double y2) {
						return geomDistance(x1, y1, x2, y2);
					}
				};
			} else if (temp.indexOf("DIMENSION") >= 0) {
				this.nodeptr = new point[this.GetDimension(temp)];
			} else if (temp.indexOf("1") == 0) {
				break;
			}
		}// while (reader.hasNextLine())

		int index = 0;
		do {
			String arg1 = "";
			String arg2 = "";
			int nodeptr_i = 0;
			while (temp.charAt(nodeptr_i) >= '0'
					&& temp.charAt(nodeptr_i) <= '9')
				nodeptr_i++;
			while (!(temp.charAt(nodeptr_i) >= '0' && temp.charAt(nodeptr_i) <= '9'))
				nodeptr_i++;

			while ((temp.charAt(nodeptr_i) >= '0' && temp.charAt(nodeptr_i) <= '9')
					|| temp.charAt(nodeptr_i) == '+'
					|| temp.charAt(nodeptr_i) == '.'
					|| temp.charAt(nodeptr_i) == 'e') {
				arg1 = arg1 + temp.charAt(nodeptr_i);
				nodeptr_i++;
			}
			while (!(temp.charAt(nodeptr_i) >= '0' && temp.charAt(nodeptr_i) <= '9'))
				nodeptr_i++;
			while ((temp.charAt(nodeptr_i) >= '0' && temp.charAt(nodeptr_i) <= '9')
					|| temp.charAt(nodeptr_i) == '+'
					|| temp.charAt(nodeptr_i) == '.'
					|| temp.charAt(nodeptr_i) == 'e') {
				arg2 = arg2 + temp.charAt(nodeptr_i);
				nodeptr_i++;
				if (nodeptr_i >= temp.length())
					break;
			}
			this.nodeptr[index] = new point();
			this.nodeptr[index].x = Double.parseDouble(arg1);
			this.nodeptr[index].y = Double.parseDouble(arg2);
			index++;
			if (!reader.hasNextLine())
				break;
			temp = reader.nextLine();
			if (temp.indexOf("EOF") >= 0)
				break;
		} while (true);
	}

	public double Height(int node) {
		if (node < this.getNumber_Of_Node()) {
			return this.nodeptr[node].y;
		}

		return -1;
	} // public int Height(int node)

	public double Width(int node) {
		if (node < this.getNumber_Of_Node()) {
			return this.nodeptr[node].x;
		}
		return -1;
	} // public int Width(int node)

	public int D(int node1, int node2) {
		return this.distance_1.invoke(node1, node2);
	}

	public int D(double x1, double y1, double x2, double y2) {
		return distance_2.invoke(x1, y1, x2, y2);
	}

}

