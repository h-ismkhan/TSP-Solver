
public class Tour {
	private static class Node {
		public short IsExist;
		public Node left;
		public Node right;
		public int Id;
	}

	private MyRandomGenerator random = new MyRandomGenerator();
	private Node[] nodes;
	private Node first; // first-> . . . ->last->first
	private Node last;
	private Graph graph;
	private int Dimension;
	private long cost;
	private int count;

	private void CalculateCost() {
		int node = 0;
		for (int i = 0; i < Dimension; i++) {
			int right = this.Right(node);
			cost = cost + graph.D(node, right);
			node = right;
		}
	}

	public Tour(Graph graph) {
		Dimension = graph.getNumber_Of_Node();
		this.graph = graph;
		nodes = new Node[Dimension];
		for (int i = 0; i < Dimension; i++) {
			this.nodes[i] = new Node();
			this.nodes[i].IsExist = 0;
		}
		for (int i = 0; i < Dimension; i++) {
			this.nodes[i].Id = i;
		}
		first = last = null;
		cost = 0;
		count = 0;
	}

	public final void Reset() {
		for (int i = 0; i < Dimension; i++) {
			this.nodes[i].IsExist = 0;
		}
		first = last = null;
		cost = 0;
		count = 0;
	}

	public final void dispose() {
		nodes = null;
	}

	public final short Add(int node) {
		if (node >= Dimension || node < 0 || nodes[node].IsExist != 0) {
			return 0;
		}
		count++;
		nodes[node].IsExist = 1;
		if (last == null) {
			first = last = nodes[node];
			nodes[node].left = nodes[node].right = nodes[node];
			return 1;
		}
		last.right = nodes[node];
		nodes[node].left = last;
		nodes[node].right = first;
		first.left = nodes[node];
		last = nodes[node];
		if (count == Dimension) {
			this.CalculateCost();
		}
		return 1;
	}

	public final boolean AddToLeft(int node) {
		if (node >= Dimension || node < 0 || nodes[node].IsExist != 0) {
			return false;
		}
		count++;
		nodes[node].IsExist = 1;
		if (first == null) {
			first = last = nodes[node];
			nodes[node].left = nodes[node].right = nodes[node];
			return true;
		}
		last.right = nodes[node];
		nodes[node].left = last;
		nodes[node].right = first;
		first.left = nodes[node];
		first = nodes[node];
		if (count == Dimension) {
			this.CalculateCost();
		}
		return true;
	}

	public final long Cost() {
		return cost;
	}

	public final int Right(int node) {
		return nodes[node].right.Id;
	}

	public final int Left(int node) {
		return nodes[node].left.Id;
	}

	public final boolean IsComplete() {
		return (count == Dimension);
	}

	public final void InitiateRandomly() {
		int[] order = random.RandomArray(Dimension);
		for (int i = 0; i < Dimension; i++) {
			Add(order[i]);
		}
		order = null;
	}

	public final Tour Copy() {
		Tour output = new Tour(this.graph);
		int iter = 0;
		for (int i = 0; i < Dimension; i++) {
			output.Add(iter);
			iter = Right(iter);
		}
		return output;
	}

	public final void InitiateOrderly() {
		for (int i = 0; i < Dimension; i++) {
			Add(i);
		}
	}
}