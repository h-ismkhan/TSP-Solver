import java.util.*;

public class Heuristics {

	private class Node {
		public int _Id;
		public Node _Pred;
		public Node _Suc;
		public Node BestPred;
		public Node BestSuc;
		public Candidate[] CandidateSet;
		public double X;
		public double Y;
		public double Z;
		public int Axis;
		public Node Nearest;
		public Node Next;
		public int Degree;
		public Node Tail;
		public int Cost;
		public Node OldPred;
		public Node OldSuc;
		public int Level;
		public int mark;
		public int Loc;
		public int Rank;
		public boolean OldPredExcluded, OldSucExcluded;
		public Segment _Parent;
		public boolean IsActivated;
		public int PredCost;
		public int SucCost;
	}

	private class Candidate {
		public Node To;
		public int Cost;
		public int Alpha;
	}

	private class Segment {
		public boolean Reversed;
		public Node _First;
		public Node _Last;
		public Segment _Pred;
		public Segment _Suc;
		public int Rank;
		public int Size;
		public SSegment _Parent;
	}

	private class SSegment {
		public boolean Reversed;
		public Segment First;
		public Segment Last;
		public SSegment Pred;
		public SSegment Suc;
		public int Rank;
		public int Size;
	}

	private class SwapRecord {
		public Node t1;
		public Node t2;
		public Node t3;
		public Node t4;
	}

	private class Heap {
		private int Size;
		private Node[] Nodes;
		private int HeapCount; // Its current number of elements
		private int HeapCapacity; // Its capacity

		public Heap(int Size) {
			this.Size = Size;
			Nodes = new Node[Size + 1];
			HeapCapacity = Size;
			HeapCount = 0;
		}

		public final void HeapSiftUp(Node N) {
			int Loc = N.Loc;
			int Parent = Loc / 2;

			while (Parent != 0 && N.Rank < Nodes[Parent].Rank) {
				Nodes[Loc] = Nodes[Parent];
				Nodes[Loc].Loc = Loc;
				Loc = Parent;
				Parent /= 2;
			}
			Nodes[Loc] = N;
			N.Loc = Loc;
		}

		public final void HeapSiftDown(Node N) {
			int Loc = N.Loc;
			int Child;

			while (Loc <= HeapCount / 2) {
				Child = 2 * Loc;
				if (Child < HeapCount
						&& Nodes[Child + 1].Rank < Nodes[Child].Rank) {
					Child++;
				}
				if (N.Rank <= Nodes[Child].Rank) {
					break;
				}
				Nodes[Loc] = Nodes[Child];
				Nodes[Loc].Loc = Loc;
				Loc = Child;
			}
			Nodes[Loc] = N;
			N.Loc = Loc;
		}

		public Node HeapDeleteMin() {
			Node Remove;

			if (HeapCount == 0) {
				return null;
			}
			Remove = Nodes[1];
			Nodes[1] = Nodes[HeapCount--];
			Nodes[1].Loc = 1;
			HeapSiftDown(Nodes[1]);
			Remove.Loc = 0;
			return Remove;
		}

		public void HeapInsert(Node N) {
			HeapLazyInsert(N);
			HeapSiftUp(N);
		}

		public void HeapDelete(Node N) {
			int Loc = N.Loc;
			if (Loc == 0) {
				return;
			}
			Nodes[Loc] = Nodes[HeapCount--];
			Nodes[Loc].Loc = Loc;
			if (Nodes[Loc].Rank > N.Rank) {
				HeapSiftDown(Nodes[Loc]);
			} else {
				HeapSiftUp(Nodes[Loc]);
			}
			N.Loc = 0;
		}

		public void HeapLazyInsert(Node N) {
			assert HeapCount < HeapCapacity;
			HeapCount++;
			Nodes[HeapCount] = N;
			N.Loc = HeapCount;
		}

		public void Heapify() {
			int Loc;
			for (Loc = HeapCount / 2; Loc >= 1; Loc--) {
				HeapSiftDown(Nodes[Loc]);
			}
		}
	}

	private Segment FirstSegment;
	private Segment[] SegmentSet;
	private SSegment FirstSSegment;
	private Node[] NodeSet;
	private Node FirstNode;
	private int Dimension;
	private int MaxSwaps;
	private Graph graph;
	private SwapRecord[] SwapStack;
	private Node[] KDTree;
	private Candidate[] CandidateSet;
	private double[] XMin;
	private double[] XMax;
	private double[] YMin;
	private double[] YMax;

	private int cutoff;
	private int Swaps;
	private int cand_num;
	private int GroupSize;
	private int Groups;
	private int SGroupSize;
	private int SGroups;
	private boolean Reversed;
	private boolean OldReversed;
	private int Candidates;
	private int Radius;
	private Node FirstActive;

	private int Number_Of_Candidates;
	private Node LastActive;
	private double SPLIT_CUTOFF = 0.75;

	private enum CoordTypes {
		TWOD_COORDS, THREED_COORDS, NO_COORDS;
		public int getValue() {
			return this.ordinal();
		}

		public static CoordTypes forValue(int value) {
			return values()[value];
		}
	}

	private static interface ContainsFunction {
		boolean invoke(Node T, int Q, Node N);
	}

	private static interface BoxOverlapsFunction {
		boolean invoke(Node T, int Q, Node N);
	}

	private ContainsFunction Contains;
	private BoxOverlapsFunction BoxOverlaps;

	private double Coord(Node N, int axis) {
		if (axis == 0) {
			return N.X;
		} else if (axis == 1) {
			return N.Y;
		}
		return N.Z;
	}

	private int C(Node n1, Node n2) {
		return (int) graph.D(n1._Id - 1, n2._Id - 1);
	}

	private Node Pred(Node a) {
		if (Reversed == (a)._Parent.Reversed) {
			return (a)._Pred;
		}
		return (a)._Suc;
	}

	private Node Suc(Node a) {
		if (Reversed == (a)._Parent.Reversed) {
			return (a)._Suc;
		}
		return (a)._Pred;
	}

	private boolean InBestTour(Node a, Node b) {
		return ((a).BestSuc == (b) || (b).BestSuc == (a));
	}

	private boolean Near(Node a, Node b) {
		if ((a).BestSuc != null) {
			return InBestTour(a, b);
		}
		return false;
	}

	private void Link(Node a, Node b) {
		(a)._Suc = (b);
		(b)._Pred = (a);
	}

	private void Follow(Node a, Node b) {
		Link((b)._Pred, (b)._Suc);
		Link(b, b);
		Link(b, (a)._Suc);
		Link(a, b);
	}

	private void Precede(Node a, Node b) {
		Link((a)._Pred, (a)._Suc);
		Link(a, a);
		Link((b)._Pred, a);
		Link(a, b);
	}

	private void SLink(Node a, Node b) {
		(a)._Suc = (b);
		(b)._Pred = (a);
	}

	private void Link(SSegment a, SSegment b) {
		(a).Suc = (b);
		(b).Pred = (a);
	}

	private void Follow(SSegment a, SSegment b) {
		Link((b).Pred, (b).Suc);
		Link(b, b);
		Link(b, (a).Suc);
		Link(a, b);
	}

	private void Precede(SSegment a, SSegment b) {
		Link((a).Pred, (a).Suc);
		Link(a, a);
		Link((b).Pred, a);
		Link(a, b);
	}

	private void SLink(SSegment a, SSegment b) {
		(a).Suc = (b);
		(b).Pred = (a);
	}

	private void Link(Segment a, Segment b) {
		(a)._Suc = (b);
		(b)._Pred = (a);
	}

	private void Follow(Segment a, Segment b) {
		Link((b)._Pred, (b)._Suc);
		Link(b, b);
		Link(b, (a)._Suc);
		Link(a, b);
	}

	private void Precede(Segment a, Segment b) {
		Link((a)._Pred, (a)._Suc);
		Link(a, a);
		Link((b)._Pred, a);
		Link(a, b);
	}

	private void SLink(Segment a, Segment b) {
		(a)._Suc = (b);
		(b)._Pred = (a);
	}

	private void Exclude(Node ta, Node tb) {
		if (ta == tb._Pred || ta == tb._Suc) {
			return;
		}
		if (ta == tb.OldPred) {
			tb.OldPredExcluded = true;
		} else if (ta == tb.OldSuc) {
			tb.OldSucExcluded = true;
		}
		if (tb == ta.OldPred) {
			ta.OldPredExcluded = true;
		} else if (tb == ta.OldSuc) {
			ta.OldSucExcluded = true;
		}
	}

	private int SegmentSize(Node ta, Node tb) {
		Segment Pa;
		Segment Pb;
		int n;
		int nLeft;
		int nMid;
		int nRight;

		Pa = ta._Parent;
		Pb = tb._Parent;
		if (Pa == Pb) {
			n = Reversed == Pa.Reversed ? tb.Rank - ta.Rank : ta.Rank - tb.Rank;
			return (n < 0 ? n + Dimension : n) + 1;
		}
		nLeft = Reversed == Pa.Reversed ? Pa._Last.Rank - ta.Rank : ta.Rank
				- Pa._First.Rank;
		if (nLeft < 0) {
			nLeft += Pa.Size;
		}
		nMid = !Reversed ? Pb.Rank - Pa.Rank : Pa.Rank - Pb.Rank;
		if (nMid < 0) {
			nMid += Groups;
		}
		nMid = nMid == 2 ? (!Reversed ? Pa._Suc : Pa._Pred).Size : (nMid - 1)
				* GroupSize;
		nRight = Reversed == Pb.Reversed ? tb.Rank - Pb._First.Rank
				: Pb._Last.Rank - tb.Rank;
		if (nRight < 0) {
			nRight += Pb.Size;
		}
		return nLeft + nMid + nRight + 2;
	}

	private boolean Excludable(Node ta, Node tb) {
		if (ta == tb.OldPred) {
			return !tb.OldPredExcluded;
		}
		if (ta == tb.OldSuc) {
			return !tb.OldSucExcluded;
		}
		return false;
	}

	private boolean Between_SL(Node ta, Node tb, Node tc) {
		Segment Pa, Pb, Pc;

		if (tb == ta || tb == tc) {
			return true;
		}
		if (ta == tc) {
			return false;
		}
		Pa = ta._Parent;
		Pb = tb._Parent;
		Pc = tc._Parent;
		if (Pa == Pc) {
			if (Pb == Pa) {
				return (Reversed == Pa.Reversed) == (ta.Rank < tc.Rank ? tb.Rank > ta.Rank
						&& tb.Rank < tc.Rank
						: tb.Rank > ta.Rank || tb.Rank < tc.Rank);
			}
			return (Reversed == Pa.Reversed) == (ta.Rank > tc.Rank);
		}
		if (Pb == Pc) {
			return (Reversed == Pb.Reversed) == (tb.Rank < tc.Rank);
		}
		if (Pa == Pb) {
			return (Reversed == Pa.Reversed) == (ta.Rank < tb.Rank);
		}
		return Reversed != (Pa.Rank < Pc.Rank ? Pb.Rank > Pa.Rank
				&& Pb.Rank < Pc.Rank : Pb.Rank > Pa.Rank || Pb.Rank < Pc.Rank);
	}

	private boolean BETWEEN(Node a, Node b, Node c) {
		return Between_SL(a, b, c);
	}

	private void SplitSegment(Node t1, Node t2) {
		Segment P = t1._Parent;
		Segment Q;
		Node t;
		Node u;
		int i;
		int Count;
		int Temp;

		if (t2.Rank < t1.Rank) {
			t = t1;
			t1 = t2;
			t2 = t;
		}
		Count = t1.Rank - P._First.Rank + 1;
		if (2 * Count < P.Size) {
			/* The left part of P is merged with its neighbouring segment, Q */
			Q = P.Reversed ? P._Suc : P._Pred;
			t = P._First._Pred;
			i = t.Rank;
			if (t == Q._Last) {
				if (t == Q._First && t._Suc != P._First) {
					u = t._Suc;
					t._Suc = t._Pred;
					t._Pred = u;
					Q.Reversed ^= true;
					Temp = t.SucCost;
					t.SucCost = t.PredCost;
					t.PredCost = Temp;
				}
				for (t = P._First; t != t2; t = t._Suc) {
					t._Parent = Q;
					t.Rank = ++i;
				}
				Q._Last = t1;
			} else {
				for (t = P._First; t != t2; t = u) {
					t._Parent = Q;
					t.Rank = --i;
					u = t._Suc;
					t._Suc = t._Pred;
					t._Pred = u;
					Temp = t.SucCost;
					t.SucCost = t.PredCost;
					t.PredCost = Temp;
				}
				Q._First = t1;
			}
			P._First = t2;
		} else {
			/* The right part of P is merged with its neighbouring segment, Q */
			Q = P.Reversed ? P._Pred : P._Suc;
			t = P._Last._Suc;
			i = t.Rank;
			if (t == Q._First) {
				if (t == Q._Last && t._Pred != P._Last) {
					u = t._Suc;
					t._Suc = t._Pred;
					t._Pred = u;
					Q.Reversed ^= true;
					Temp = t.SucCost;
					t.SucCost = t.PredCost;
					t.PredCost = Temp;
				}
				for (t = P._Last; t != t1; t = t._Pred) {
					t._Parent = Q;
					t.Rank = --i;
				}
				Q._First = t2;
			} else {
				for (t = P._Last; t != t1; t = u) {
					t._Parent = Q;
					t.Rank = ++i;
					u = t._Pred;
					t._Pred = t._Suc;
					t._Suc = u;
					Temp = t.SucCost;
					t.SucCost = t.PredCost;
					t.PredCost = Temp;
				}
				Q._Last = t2;
			}
			Count = P.Size - Count;
			P._Last = t1;
		}
		P.Size -= Count;
		Q.Size += Count;
	}

	private void Flip(Node t1, Node t2, Node t3) {
		Node s1;
		Node s2;
		Node t4;
		int R;
		int Temp;
		int Ct2t3;
		int Ct4t1;

		assert t1._Pred == t2 || t1._Suc == t2;
		if (t3 == t2._Pred || t3 == t2._Suc) {
			return;
		}
		t4 = t1._Suc == t2 ? t3._Pred : t3._Suc;
		if (t1._Suc != t2) {
			s1 = t1;
			t1 = t2;
			t2 = s1;
			s1 = t3;
			t3 = t4;
			t4 = s1;
		}
		/* Find the segment with the smallest number of nodes */
		if ((R = t2.Rank - t3.Rank) < 0) {
			R += Dimension;
		}
		if (2 * R > Dimension) {
			s1 = t3;
			t3 = t2;
			t2 = s1;
			s1 = t4;
			t4 = t1;
			t1 = s1;
		}
		Ct2t3 = graph.D(t2._Id, t3._Id);
		Ct4t1 = graph.D(t4._Id, t1._Id);
		/* Swap segment (t3 --> t1) */
		R = t1.Rank;
		t1._Suc = null;
		s2 = t3;
		while ((s1 = s2) != null) {
			s2 = s1._Suc;
			s1._Suc = s1._Pred;
			s1._Pred = s2;
			s1.Rank = R--;
			Temp = s1.SucCost;
			s1.SucCost = s1.PredCost;
			s1.PredCost = Temp;
		}
		(t3._Suc = t2)._Pred = t3;
		(t4._Suc = t1)._Pred = t4;
		t3.SucCost = t2.PredCost = Ct2t3;
		t1.PredCost = t4.SucCost = Ct4t1;
		SwapStack[Swaps].t1 = t1;
		SwapStack[Swaps].t2 = t2;
		SwapStack[Swaps].t3 = t3;
		SwapStack[Swaps].t4 = t4;
		Swaps++;
	}

	private void Flip_SL(Node t1, Node t2, Node t3) {
		Node t4, a = null, b, cc = null, d = null, s1, s2;
		Segment P1, P2, P3, P4, Q1, Q2;
		int i, Temp;
		assert t1._Pred == t2 || t1._Suc == t2;
		if (t3 == t2._Pred || t3 == t2._Suc) {
			return;
		}
		if (Groups == 1) {
			Flip(t1, t2, t3);
			return;
		}
		t4 = t2 == Suc(t1) ? Pred(t3) : Suc(t3);
		P1 = t1._Parent;
		P2 = t2._Parent;
		P3 = t3._Parent;
		P4 = t4._Parent;

		if (P1 != P3 && P2 != P4) {
			if (P1 == P2) {
				SplitSegment(t1, t2);
				P1 = t1._Parent;
				P2 = t2._Parent;
			}
			if (P3 == P4 && P1 != P3 && P2 != P4) {
				SplitSegment(t3, t4);
				P3 = t3._Parent;
				P4 = t4._Parent;
			}
		} else {
			if ((P1 == P3 && Math.abs(t3.Rank - t1.Rank) > SPLIT_CUTOFF
					* GroupSize)
					|| (P2 == P4 && Math.abs(t4.Rank - t2.Rank) > SPLIT_CUTOFF
							* GroupSize)) {
				if (P1 == P2) {
					SplitSegment(t1, t2);
					P1 = t1._Parent;
					P2 = t2._Parent;
					P3 = t3._Parent;
					P4 = t4._Parent;
				}
				if (P3 == P4) {
					SplitSegment(t3, t4);
					P1 = t1._Parent;
					P2 = t2._Parent;
					P3 = t3._Parent;
					P4 = t4._Parent;
				}
			}
		}
		/* Check if it is possible to flip locally within a segment */
		b = null;
		if (P1 == P3) {
			/*
			 * Either the t1 --> t3 path or the t2 --> t4 path lies within one
			 * segment
			 */
			if (t1.Rank < t3.Rank) {
				if (P1 == P2 && P1 == P4 && t2.Rank > t1.Rank) {
					a = t1;
					b = t2;
					cc = t3;
					d = t4;
				} else {
					a = t2;
					b = t1;
					cc = t4;
					d = t3;
				}
			} else {
				if (P1 == P2 && P1 == P4 && t2.Rank < t1.Rank) {
					a = t3;
					b = t4;
					cc = t1;
					d = t2;
				} else {
					a = t4;
					b = t3;
					cc = t2;
					d = t1;
				}
			}
		} else if (P2 == P4) {
			/* The t2 --> t4 path lies within one segment */
			if (t4.Rank < t2.Rank) {
				a = t3;
				b = t4;
				cc = t1;
				d = t2;
			} else {
				a = t1;
				b = t2;
				cc = t3;
				d = t4;
			}
		}
		if (b != null) {
			int Cbc = graph.D(b._Id, cc._Id);
			int Cda = graph.D(d._Id, a._Id);
			/* Flip locally (b --> d) within a segment */
			i = d.Rank;
			d._Suc = null;
			s2 = b;
			while ((s1 = s2) != null) {
				s2 = s1._Suc;
				s1._Suc = s1._Pred;
				s1._Pred = s2;
				s1.Rank = i--;
				Temp = s1.SucCost;
				s1.SucCost = s1.PredCost;
				s1.PredCost = Temp;
			}
			d._Pred = a;
			b._Suc = cc;
			d.PredCost = Cda;
			b.SucCost = Cbc;
			if (a._Suc == b) {
				a._Suc = d;
				a.SucCost = d.PredCost;
			} else {
				a._Pred = d;
				a.PredCost = d.PredCost;
			}
			if (cc._Pred == d) {
				cc._Pred = b;
				cc.PredCost = b.SucCost;
			} else {
				cc._Suc = b;
				cc.SucCost = b.SucCost;
			}
			if (b._Parent._First == b) {
				b._Parent._First = d;
			} else if (d._Parent._First == d) {
				d._Parent._First = b;
			}
			if (b._Parent._Last == b) {
				b._Parent._Last = d;
			} else if (d._Parent._Last == d) {
				d._Parent._Last = b;
			}
		} else {
			int Ct2t3;
			int Ct4t1;
			/* Reverse a sequence of segments */
			if (P1._Suc != P2) {
				a = t1;
				t1 = t2;
				t2 = a;
				a = t3;
				t3 = t4;
				t4 = a;
				Q1 = P1;
				P1 = P2;
				P2 = Q1;
				Q1 = P3;
				P3 = P4;
				P4 = Q1;
			}
			/* Find the sequence with the smallest number of segments */
			if ((i = P2.Rank - P3.Rank) < 0) {
				i += Groups;
			}
			if (2 * i > Groups) {
				a = t3;
				t3 = t2;
				t2 = a;
				a = t1;
				t1 = t4;
				t4 = a;
				Q1 = P3;
				P3 = P2;
				P2 = Q1;
				Q1 = P1;
				P1 = P4;
				P4 = Q1;
			}
			Ct2t3 = graph.D(t2._Id, t3._Id);
			Ct4t1 = graph.D(t4._Id, t1._Id);
			/*
			 * Reverse the sequence of segments (P3 --> P1). Mirrors the
			 * corresponding code in the Flip function
			 */
			i = P1.Rank;
			P1._Suc = null;
			Q2 = P3;
			while ((Q1 = Q2) != null) {
				Q2 = Q1._Suc;
				Q1._Suc = Q1._Pred;
				Q1._Pred = Q2;
				Q1.Rank = i--;
				Q1.Reversed ^= true;
			}
			P3._Suc = P2;
			P2._Pred = P3;
			P1._Pred = P4;
			P4._Suc = P1;
			if (t3._Suc == t4) {
				t3._Suc = t2;
				t3.SucCost = Ct2t3;
			} else {
				t3._Pred = t2;
				t3.PredCost = Ct2t3;
			}
			if (t2._Suc == t1) {
				t2._Suc = t3;
				t2.SucCost = Ct2t3;
			} else {
				t2._Pred = t3;
				t2.PredCost = Ct2t3;
			}
			if (t1._Pred == t2) {
				t1._Pred = t4;
				t1.PredCost = Ct4t1;
			} else {
				t1._Suc = t4;
				t1.SucCost = Ct4t1;
			}
			if (t4._Pred == t3) {
				t4._Pred = t1;
				t4.PredCost = Ct4t1;
			} else {
				t4._Suc = t1;
				t4.SucCost = Ct4t1;
			}
		}
		SwapStack[Swaps].t1 = t1;
		SwapStack[Swaps].t2 = t2;
		SwapStack[Swaps].t3 = t3;
		SwapStack[Swaps].t4 = t4;
		Swaps++;

	}

	private void Swap1(Node a1, Node a2, Node a3) {
		Flip_SL(a1, a2, a3);
	}

	private void Swap2(Node a1, Node a2, Node a3, Node b1, Node b2, Node b3) {
		Swap1(a1, a2, a3);
		Swap1(b1, b2, b3);
	}

	private void Swap3(Node a1, Node a2, Node a3, Node b1, Node b2, Node b3,
			Node c1, Node c2, Node c3) {
		Swap2(a1, a2, a3, b1, b2, b3);
		Swap1(c1, c2, c3);
	}

	private void Swap4(Node a1, Node a2, Node a3, Node b1, Node b2, Node b3,
			Node c1, Node c2, Node c3, Node d1, Node d2, Node d3) {
		Swap3(a1, a2, a3, b1, b2, b3, c1, c2, c3);
		Swap1(d1, d2, d3);
	}

	private void Swap5(Node a1, Node a2, Node a3, Node b1, Node b2, Node b3,
			Node c1, Node c2, Node c3, Node d1, Node d2, Node d3, Node e1,
			Node e2, Node e3) {
		Swap4(a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3);
		Swap1(e1, e2, e3);
	}

	private void AllocateStructures() {
		SwapStack = new SwapRecord[MaxSwaps + 6 * 5];
		for (int k = 0; k < SwapStack.length; k++) {
			SwapStack[k] = new SwapRecord();
		}
	}

	private void Activate(Node N) {
		if (N.Next != null) {
			return;
		}
		if (FirstActive == null) {
			FirstActive = LastActive = N;
		} else {
			LastActive = LastActive.Next = N;
		}
		LastActive.Next = FirstActive;
	}

	private Node RemoveFirstActive() {
		Node N = FirstActive;
		if (FirstActive == LastActive) {
			FirstActive = LastActive = null;
		} else {
			LastActive.Next = FirstActive = FirstActive.Next;
		}
		if (N != null) {
			N.Next = null;
		}
		return N;
	}

	private boolean Contains2D(Node T, int Q, Node N) {
		switch (Q) {
		case 1:
			return T.X >= N.X && T.Y >= N.Y;
		case 2:
			return T.X <= N.X && T.Y >= N.Y;
		case 3:
			return T.X <= N.X && T.Y <= N.Y;
		case 4:
			return T.X >= N.X && T.Y <= N.Y;
		default:
			return true;
		}
	}

	private boolean Contains3D(Node T, int Q, Node N) {
		switch (Q) {
		case 1:
			return T.X >= N.X && T.Y >= N.Y && T.Z >= N.Z;
		case 2:
			return T.X <= N.X && T.Y >= N.Y && T.Z >= N.Z;
		case 3:
			return T.X <= N.X && T.Y <= N.Y && T.Z >= N.Z;
		case 4:
			return T.X >= N.X && T.Y <= N.Y && T.Z >= N.Z;
		case 5:
			return T.X >= N.X && T.Y >= N.Y && T.Z <= N.Z;
		case 6:
			return T.X <= N.X && T.Y >= N.Y && T.Z <= N.Z;
		case 7:
			return T.X <= N.X && T.Y <= N.Y && T.Z <= N.Z;
		case 8:
			return T.X >= N.X && T.Y < N.Y && T.Z <= N.Z;
		default:
			return true;
		}
	}

	private boolean BoxOverlaps2D(Node T, int Q, Node N) {
		switch (Q) {
		case 1:
			return XMax[T._Id] >= N.X && YMax[T._Id] >= N.Y;
		case 2:
			return XMin[T._Id] <= N.X && YMax[T._Id] >= N.Y;
		case 3:
			return XMin[T._Id] <= N.X && YMin[T._Id] <= N.Y;
		case 4:
			return XMax[T._Id] >= N.X && YMin[T._Id] <= N.Y;
		default:
			return true;
		}
	}

	private boolean BoxOverlaps3D(Node T, int Q, Node N) {
		switch (Q) {
		case 1:
			return XMax[T._Id] >= N.X && YMax[T._Id] >= N.Y;
		case 2:
			return XMin[T._Id] <= N.X && YMax[T._Id] >= N.Y;
		case 3:
			return XMin[T._Id] <= N.X && YMin[T._Id] <= N.Y;
		case 4:
			return XMax[T._Id] >= N.X && YMin[T._Id] <= N.Y;
		case 5:
			return XMax[T._Id] >= N.X && YMax[T._Id] >= N.Y;
		case 6:
			return XMin[T._Id] <= N.X && YMax[T._Id] >= N.Y;
		case 7:
			return XMin[T._Id] <= N.X && YMin[T._Id] <= N.Y;
		case 8:
			return XMax[T._Id] >= N.X && YMin[T._Id] <= N.Y;
		default:
			return true;
		}
	}

	private Node[] BuildKDTree(int Cutoff) {
		int i;
		Node N;

		cutoff = Cutoff >= 1 ? Cutoff : 1;
		KDTree = new Node[Dimension];
		for (i = 0, N = FirstNode; i < Dimension; i++, N = N._Suc) {
			KDTree[i] = N;
		}
		BuildSubKDTree(0, Dimension - 1);
		return KDTree;
	}

	private void BuildSubKDTree(int start, int end) {
		if (end - start + 1 > cutoff) {
			int mid = (start + end) / 2;
			int axis = FindMaxSpread(start, end);
			Partition(start, end, mid, axis);
			KDTree[mid].Axis = axis;
			BuildSubKDTree(start, mid - 1);
			BuildSubKDTree(mid + 1, end);
		}
	}

	private void Partition(int start, int end, int k, int axis) {
		while (start < end) {
			int i = start;
			int j = end - 1;
			int mid = (start + end) / 2;
			double pivot;
			if (Coord(KDTree[mid], axis) < Coord(KDTree[start], axis)) {
				Swap(start, mid);
			}
			if (Coord(KDTree[end], axis) < Coord(KDTree[start], axis)) {
				Swap(start, end);
			}
			if (Coord(KDTree[end], axis) < Coord(KDTree[mid], axis)) {
				Swap(mid, end);
			}
			if (end - start <= 2) {
				return;
			}
			Swap(mid, j);
			pivot = Coord(KDTree[j], axis);
			while (true) {
				while (Coord(KDTree[++i], axis) < pivot)
					;
				while (pivot < Coord(KDTree[--j], axis))
					;
				if (i >= j) {
					break;
				}
				Swap(i, j);
			}
			Swap(i, end - 1);
			if (i >= k) {
				end = i - 1;
			}
			if (i <= k) {
				start = i + 1;
			}
		}
	}

	private void Swap(int i, int j) {
		Node T = KDTree[i];
		KDTree[i] = KDTree[j];
		KDTree[j] = T;
	}

	private int FindMaxSpread(int start, int end) {
		int i;
		int axis;
		Node N;
		double[] Min = new double[3];
		double[] Max = new double[3];

		N = KDTree[start];
		Min[0] = Max[0] = N.X;
		Min[1] = Max[1] = N.Y;
		Min[2] = Max[2] = N.Z;
		for (i = start + 1; i <= end; i++) {
			for (axis = 1; axis >= 0; axis--) {
				N = KDTree[i];
				if (Coord(N, axis) < Min[axis]) {
					Min[axis] = Coord(N, axis);
				} else if (Coord(N, axis) > Max[axis]) {
					Max[axis] = Coord(N, axis);
				}
			}
		}
		if (Max[0] - Min[0] > Max[1] - Min[1]) {
			return 0;
		}
		return 1;

	}

	private boolean AddCandidate(Node From, Node To, int Cost, int Alpha) {
		int Count;
		Candidate NFrom = null;

		if (From.CandidateSet == null) {
			From.CandidateSet = new Candidate[this.Number_Of_Candidates + 1];
			for (int k = 0; k < From.CandidateSet.length; k++) {
				From.CandidateSet[k] = new Candidate();
			}
		}
		if (From == To) {
			return false;
		}
		Count = 0;
		int i = 0;
		for (NFrom = From.CandidateSet[i]; NFrom.To != null && NFrom.To != To; NFrom = From.CandidateSet[i]) {
			Count++;
			i++;
		}
		if (NFrom.To != null) {
			return false;
		}
		NFrom.Cost = Cost;
		NFrom.Alpha = Alpha;
		NFrom.To = To;
		// From.CandidateSet = new Candidate[Count + 2];
		// for (int k = 0; k < From.CandidateSet.Length; k++)
		// From.CandidateSet[k] = new Candidate();
		From.CandidateSet[Count + 1] = new Candidate();
		From.CandidateSet[Count + 1].To = null;
		return true;
	}

	private void NQN(Node N, int Q, int start, int end, int K) {
		double diff;
		int mid = (start + end) / 2;
		int d;
		int i;
		Node T = KDTree[mid];
		Node P = new Node();
		int axis = T.Axis;

		if (start <= end && T != N && Contains.invoke(T, Q, N)
				&& !InCandidateSet(N, T)
				&& (d = this.graph.D(N.X, N.Y, T.X, T.Y)) <= Radius) {
			i = Candidates;
			while (--i >= 0 && d < CandidateSet[i].Cost) {
				CandidateSet[i + 1].Alpha = CandidateSet[i].Alpha;
				CandidateSet[i + 1].Cost = CandidateSet[i].Cost;
				CandidateSet[i + 1].To = CandidateSet[i].To;
			}
			CandidateSet[i + 1].To = T;
			CandidateSet[i + 1].Cost = d;
			if (Candidates < K) {
				Candidates++;
			}
			if (Candidates == K) {
				Radius = CandidateSet[Candidates - 1].Cost;
			}
		}
		if (start < end && BoxOverlaps.invoke(T, Q, N)) {
			P.X = axis == 0 ? T.X : N.X;
			P.Y = axis == 1 ? T.Y : N.Y;
			P.Z = axis == 2 ? T.Z : N.Z;

			diff = Coord(T, axis) - Coord(N, axis);
			if (diff >= 0) {
				if (Overlaps(Q, diff, 0, axis)) {
					NQN(N, Q, start, mid - 1, K);
				}
				if (Overlaps(Q, diff, 1, axis)
						&& this.graph.D(N.X, N.Y, (P).X, (P).Y) <= Radius) {
					NQN(N, Q, mid + 1, end, K);
				}
			} else {
				if (Overlaps(Q, diff, 1, axis)) {
					NQN(N, Q, mid + 1, end, K);
				}
				if (Overlaps(Q, diff, 0, axis)
						&& this.graph.D(N.X, N.Y, (P).X, (P).Y) <= Radius) {
					NQN(N, Q, start, mid - 1, K);
				}
			}
		}
	}

	private void NearestQuadrantNeighbors(Node N, int Q, int K) {
		Candidates = 0;
		Radius = Integer.MAX_VALUE;
		NQN(N, Q, 0, Dimension - 1, K);
	}

	private boolean Overlaps(int Q, double diff, int High, int axis) {
		switch (Q) {
		case 1:
			return High != 0 || diff >= 0;
		case 2:
			return axis == 0 ? High == 0 || diff <= 0 : High != 0 || diff >= 0;
		case 3:
			return axis <= 1 ? High == 0 || diff <= 0 : High != 0 || diff >= 0;
		case 4:
			return axis == 1 ? High == 0 || diff <= 0 : High != 0 || diff >= 0;
		case 5:
			return axis <= 1 ? High != 0 || diff >= 0 : High == 0 || diff <= 0;
		case 6:
			return axis == 1 ? High != 0 || diff >= 0 : High == 0 || diff <= 0;
		case 7:
			return High == 0 || diff <= 0;
		case 8:
			return axis == 0 ? High != 0 || diff >= 0 : High == 0 || diff <= 0;
		default:
			return true;
		}
	}

	private boolean IsCandidate(Node ta, Node tb) {
		int i = 0;
		if (ta.CandidateSet == null) {
			return false;
		}
		for (Candidate Nta = ta.CandidateSet[i]; Nta != null && Nta.To != null; Nta = ta.CandidateSet[i]) {
			if (Nta.To == tb) {
				return true;
			}
			i++;
		}
		return false;
	}

	private boolean InCandidateSet(Node N, Node T) {
		for (int i = 0; i < Candidates; i++) {
			if (CandidateSet[i].To == T) {
				return true;
			}
		}
		return IsCandidate(N, T);
	}

	private void ComputeBounds(int start, int end) {
		if (start <= end) {
			int mid = (start + end) / 2;
			int i;
			Node T = KDTree[mid];
			XMin[T._Id] = YMin[T._Id] = Double.MAX_VALUE;
			XMax[T._Id] = YMax[T._Id] = -Double.MAX_VALUE;
			for (i = start; i <= end; i++) {
				Node N = KDTree[i];
				if (N == T) {
					continue;
				}
				if (N.X < XMin[T._Id]) {
					XMin[T._Id] = N.X;
				}
				if (N.X > XMax[T._Id]) {
					XMax[T._Id] = N.X;
				}
				if (N.Y < YMin[T._Id]) {
					YMin[T._Id] = N.Y;
				}
				if (N.Y > YMax[T._Id]) {
					YMax[T._Id] = N.Y;
				}
			}
			ComputeBounds(start, mid - 1);
			ComputeBounds(mid + 1, end);
		}
	}

	private void CreateNearestNeighborCandidateSet(int K) {
		Node From, To;
		int i;

		KDTree = BuildKDTree(1);
		XMin = new double[1 + Dimension];
		XMax = new double[1 + Dimension];
		YMin = new double[1 + Dimension];
		YMax = new double[1 + Dimension];
		ComputeBounds(0, Dimension - 1);
		Contains = new Heuristics.ContainsFunction() {
			public boolean invoke(Node T, int Q, Node N) {
				return Contains2D(T, Q, N);
			}
		};
		BoxOverlaps = new Heuristics.BoxOverlapsFunction() {
			public boolean invoke(Node T, int Q, Node N) {
				return BoxOverlaps2D(T, Q, N);
			}
		};

		CandidateSet = new Candidate[K + 1];
		for (int k = 0; k < CandidateSet.length; k++) {
			CandidateSet[k] = new Candidate();
		}

		From = FirstNode;
		do {
			NearestQuadrantNeighbors(From, 0, K);
			for (i = 0; i < Candidates; i++) {
				To = CandidateSet[i].To;
				AddCandidate(From, To,
						this.graph.D(From.X, From.Y, To.X, To.Y), 1);
			}
		} while ((From = From._Suc) != FirstNode);
	}

	private void CreateNodes() {
		NodeSet = new Node[Dimension];
		for (int i = 0; i < Dimension; i++) {
			NodeSet[i] = new Node();
			NodeSet[i]._Id = i;
			NodeSet[i].X = this.graph.Width(i);
			NodeSet[i].Y = this.graph.Height(i);
		}
		Node Prev = null;
		Node N = null;

		if (Dimension <= 0) {
			System.out.print("DIMENSION is not positive (or not specified)");
		}

		for (int i = 0; i < Dimension; i++, Prev = N) {
			N = NodeSet[i];
			if (i == 0) {
				FirstNode = N;
			} else {
				Link(Prev, N);
			}
			N._Id = i;
		}
		Link(N, FirstNode);
	}

	private void Make2OptMove(Node t1, Node t2, Node t3, Node t4) {
		Swap1(t1, t2, t3);
	}

	private void Make3OptMove(Node t1, Node t2, Node t3, Node t4, Node t5,
			Node t6, int Case) {
		switch (Case) {
		case 1:
		case 2:
			Swap2(t1, t2, t3, t6, t5, t4);
			return;
		case 5:
			Swap3(t1, t2, t4, t6, t5, t4, t6, t2, t3);
			return;
		case 6:
			Swap2(t3, t4, t5, t1, t2, t3);
			return;
		default:
			System.out.print("Make3OptMove: Internal error");
			break;
		}
	}

	private void Make4OptMove(Node t1, Node t2, Node t3, Node t4, Node t5,
			Node t6, Node t7, Node t8, int Case) {
		if (Suc(t1) != t2) {
			Reversed ^= true;
		}
		switch (Case) {
		case 1:
		case 2:
			Swap3(t1, t2, t3, t6, t5, t4, t7, t8, t1);
			return;
		case 3:
		case 4:
			Swap3(t1, t2, t3, t8, t7, t6, t5, t8, t1);
			return;
		case 5:
			if (!BETWEEN(t2, t7, t3)) {
				Swap3(t5, t6, t7, t2, t1, t4, t1, t4, t5);
			} else if (BETWEEN(t2, t7, t6)) {
				Swap3(t5, t6, t7, t5, t8, t3, t3, t8, t1);
			} else {
				Swap3(t1, t2, t7, t7, t2, t3, t4, t7, t6);
			}
			return;
		case 6:
			Swap3(t3, t4, t5, t6, t3, t2, t1, t6, t7);
			return;
		case 7:
			Swap3(t6, t5, t8, t2, t1, t4, t8, t5, t4);
			return;
		case 11:
			Swap3(t1, t2, t7, t3, t4, t5, t3, t6, t7);
			return;
		case 12:
			Swap3(t3, t4, t5, t7, t8, t1, t3, t6, t7);
			return;
		case 15:
			Swap3(t3, t4, t5, t3, t6, t7, t8, t3, t2);
			return;
		default:
			System.out.print("Make4OptMove: Internal error");
			break;
		}
	}

	private void Make5OptMove(Node t1, Node t2, Node t3, Node t4, Node t5,
			Node t6, Node t7, Node t8, Node t9, Node t10, int Case) {
		if (Suc(t1) != t2) {
			Reversed ^= true;
		}
		switch (Case) {
		case 1:
			Swap4(t1, t2, t3, t8, t7, t6, t10, t9, t8, t10, t5, t4);
			return;
		case 2:
			if (BETWEEN(t2, t9, t4)) {
				Swap4(t1, t2, t3, t5, t6, t7, t10, t9, t8, t5, t10, t1);
			} else {
				Swap4(t1, t2, t3, t7, t8, t9, t6, t5, t4, t7, t10, t1);
			}
			return;
		case 3:
			Swap4(t3, t4, t5, t7, t8, t9, t1, t2, t3, t7, t10, t1);
			return;
		case 4:
			Swap5(t5, t6, t8, t1, t2, t3, t10, t9, t8, t1, t4, t5, t6, t10, t1);
			return;
		case 5:
			Swap5(t5, t6, t10, t1, t2, t3, t6, t10, t1, t8, t7, t6, t8, t4, t5);
			return;
		case 6:
			Swap4(t1, t2, t3, t9, t10, t1, t7, t8, t9, t6, t5, t4);
			return;
		case 7:
			if (BETWEEN(t3, t9, t7)) {
				Swap4(t3, t4, t5, t8, t7, t6, t10, t9, t8, t1, t2, t3);
			} else if (BETWEEN(t6, t9, t4)) {
				Swap4(t3, t4, t5, t8, t7, t6, t9, t10, t1, t9, t2, t3);
			} else {
				Swap4(t1, t2, t3, t6, t5, t4, t7, t8, t9, t7, t10, t1);
			}
			return;
		case 8:
			Swap4(t3, t4, t5, t9, t10, t1, t8, t7, t6, t8, t3, t2);
			return;
		case 9:
			Swap4(t10, t9, t8, t5, t6, t7, t1, t2, t3, t1, t4, t5);
			return;
		case 10:
			if (BETWEEN(t5, t9, t7)) {
				Swap4(t5, t6, t7, t9, t10, t1, t4, t3, t2, t4, t9, t8);
			} else if (BETWEEN(t3, t9, t6)) {
				Swap4(t1, t2, t3, t6, t5, t4, t7, t8, t9, t7, t10, t1);
			} else {
				Swap4(t1, t2, t3, t9, t10, t1, t5, t6, t7, t5, t8, t9);
			}
			return;
		case 11:
			if (BETWEEN(t3, t9, t6)) {
				Swap4(t1, t2, t3, t6, t5, t4, t9, t10, t1, t7, t8, t9);
			} else {
				Swap4(t5, t6, t7, t10, t9, t8, t2, t1, t10, t4, t3, t2);
			}
			return;
		case 12:
			Swap4(t1, t2, t3, t8, t7, t6, t10, t9, t8, t5, t10, t1);
			return;
		case 13:
			if (BETWEEN(t4, t9, t7)) {
				Swap5(t7, t8, t10, t5, t6, t7, t1, t2, t3, t5, t9, t1, t9, t1,
						t10);
			} else if (BETWEEN(t6, t9, t3)) {
				Swap5(t10, t9, t1, t7, t8, t9, t3, t4, t5, t3, t6, t7, t3, t1,
						t10);
			} else {
				Swap5(t10, t9, t1, t4, t3, t2, t5, t6, t7, t5, t8, t10, t9, t1,
						t10);
			}
			return;
		case 14:
			Swap5(t10, t9, t1, t5, t6, t7, t5, t8, t9, t3, t4, t5, t3, t1, t10);
			return;
		case 15:
			if (BETWEEN(t6, t9, t3)) {
				Swap5(t10, t9, t1, t3, t4, t5, t6, t3, t2, t8, t7, t6, t9, t1,
						t10);
			} else {
				Swap5(t1, t2, t6, t3, t4, t5, t8, t7, t6, t10, t9, t8, t2, t10,
						t1);
			}
			return;
		case 16:
			if (BETWEEN(t4, t9, t7)) {
				Swap4(t3, t4, t5, t8, t7, t6, t9, t10, t1, t8, t3, t2);
			} else if (BETWEEN(t5, t9, t3)) {
				Swap4(t3, t4, t5, t9, t10, t1, t6, t3, t2, t7, t8, t9);
			} else {
				Swap4(t3, t4, t5, t1, t2, t3, t7, t8, t9, t7, t10, t1);
			}
			return;
		case 17:
			if (BETWEEN(t7, t9, t3)) {
				Swap4(t3, t4, t5, t7, t8, t9, t2, t1, t10, t3, t6, t7);
			} else {
				Swap4(t7, t8, t9, t2, t1, t10, t3, t4, t5, t3, t6, t7);
			}
			return;
		case 18:
			Swap4(t3, t4, t5, t7, t8, t9, t3, t6, t7, t1, t2, t3);
			return;
		case 19:
			Swap4(t7, t8, t9, t1, t2, t3, t6, t5, t4, t7, t10, t1);
			return;
		case 20:
			Swap4(t7, t8, t9, t3, t4, t5, t10, t7, t6, t3, t10, t1);
			return;
		case 21:
			Swap4(t5, t6, t7, t5, t8, t9, t1, t2, t3, t4, t1, t10);
			return;
		case 22:
			Swap4(t1, t2, t3, t6, t5, t4, t7, t8, t1, t9, t10, t1);
			return;
		case 23:
			Swap4(t1, t2, t3, t6, t5, t4, t7, t8, t1, t9, t10, t1);
			return;
		case 24:
			Swap4(t1, t2, t3, t8, t7, t6, t5, t8, t1, t9, t10, t1);
			return;
		case 25:
			Swap4(t1, t2, t3, t8, t7, t6, t5, t8, t1, t9, t10, t1);
			return;
		case 26:
			if (!BETWEEN(t2, t7, t3)) {
				Swap4(t5, t6, t7, t2, t1, t4, t1, t4, t5, t9, t10, t1);
			} else if (BETWEEN(t2, t7, t6)) {
				Swap4(t5, t6, t7, t5, t8, t3, t3, t8, t1, t9, t10, t1);
			} else {
				Swap4(t1, t2, t7, t7, t2, t3, t4, t7, t6, t9, t10, t1);
			}
			return;
		case 27:
			Swap4(t3, t4, t5, t6, t3, t2, t1, t6, t7, t9, t10, t1);
			return;
		case 28:
			Swap4(t6, t5, t8, t2, t1, t4, t8, t5, t4, t9, t10, t1);
			return;
		case 29:
			Swap4(t1, t2, t7, t3, t4, t5, t3, t6, t7, t9, t10, t1);
			return;
		case 30:
			if (BETWEEN(t3, t7, t5)) {
				Swap4(t3, t4, t5, t7, t8, t1, t7, t2, t3, t9, t10, t1);
			} else {
				Swap4(t3, t4, t5, t3, t6, t7, t1, t2, t3, t9, t10, t1);
			}
			return;
		case 31:
			Swap4(t3, t4, t5, t3, t6, t7, t8, t3, t2, t9, t10, t1);
			return;
		case 32:
			Swap4(t1, t2, t3, t7, t8, t9, t6, t5, t4, t7, t10, t1);
			return;
		case 33:
			if (BETWEEN(t3, t9, t5)) {
				Swap4(t1, t2, t3, t5, t6, t7, t10, t9, t8, t5, t10, t1);
			} else {
				Swap4(t1, t2, t3, t7, t8, t9, t7, t10, t1, t5, t6, t7);
			}
			return;
		case 34:
			Swap4(t7, t8, t9, t1, t2, t3, t1, t4, t5, t7, t10, t1);
			return;
		case 35:
			Swap4(t9, t10, t1, t5, t6, t7, t4, t3, t2, t9, t4, t5);
			return;
		case 36:
			Swap4(t9, t10, t1, t7, t8, t9, t3, t4, t5, t6, t3, t2);
			return;
		case 37:
			if (BETWEEN(t6, t9, t4)) {
				Swap4(t1, t2, t3, t6, t5, t4, t9, t10, t1, t8, t7, t6);
			} else {
				Swap4(t9, t10, t1, t3, t4, t5, t3, t6, t7, t3, t8, t9);
			}
			return;
		case 38:
			if (BETWEEN(t3, t9, t7)) {
				Swap4(t1, t2, t3, t7, t8, t9, t6, t5, t4, t6, t1, t10);
			} else if (BETWEEN(t6, t9, t4)) {
				Swap4(t1, t2, t3, t6, t5, t4, t7, t8, t9, t7, t10, t1);
			} else {
				Swap4(t3, t4, t5, t9, t10, t1, t8, t7, t6, t3, t8, t9);
			}
			return;
		case 39:
			Swap4(t1, t2, t3, t7, t8, t9, t5, t6, t7, t1, t4, t5);
			return;
		case 40:
			Swap4(t9, t10, t1, t4, t3, t2, t5, t6, t7, t5, t8, t9);
			return;
		case 41:
			if (BETWEEN(t5, t9, t7)) {
				Swap4(t7, t8, t9, t1, t2, t3, t6, t5, t4, t7, t10, t1);
			} else if (BETWEEN(t3, t9, t6)) {
				Swap4(t1, t2, t3, t5, t6, t7, t9, t10, t1, t5, t8, t9);
			} else {
				Swap4(t5, t6, t7, t9, t10, t1, t2, t9, t8, t3, t4, t5);
			}
			return;
		case 42:
			if (BETWEEN(t3, t9, t6)) {
				Swap4(t7, t8, t9, t5, t6, t7, t1, t2, t3, t1, t4, t5);
			} else {
				Swap4(t9, t10, t1, t5, t6, t7, t3, t4, t5, t3, t8, t9);
			}
			return;
		case 43:
			Swap4(t1, t2, t3, t7, t8, t9, t6, t5, t4, t7, t10, t1);
			return;
		case 44:
			if (BETWEEN(t4, t9, t7)) {
				Swap4(t7, t8, t9, t5, t6, t7, t1, t2, t3, t5, t10, t1);
			} else if (BETWEEN(t6, t9, t3)) {
				Swap4(t9, t10, t1, t5, t6, t7, t3, t4, t5, t3, t8, t9);
			} else {
				Swap4(t7, t8, t9, t1, t2, t3, t6, t5, t4, t7, t10, t1);
			}
			return;
		case 45:
			Swap4(t9, t10, t1, t3, t4, t5, t7, t8, t9, t3, t6, t7);
			return;
		case 46:
			if (BETWEEN(t6, t9, t3)) {
				Swap4(t7, t8, t9, t5, t6, t7, t3, t4, t5, t1, t2, t3);
			} else {
				Swap4(t7, t8, t9, t5, t6, t7, t3, t4, t5, t1, t2, t3);
			}
			return;
		case 47:
			if (BETWEEN(t4, t9, t7)) {
				Swap4(t5, t6, t7, t1, t2, t3, t9, t10, t1, t5, t8, t9);
			} else if (BETWEEN(t5, t9, t3)) {
				Swap4(t9, t10, t1, t7, t8, t9, t5, t6, t7, t3, t4, t5);
			} else {
				Swap4(t7, t8, t9, t3, t4, t5, t3, t6, t7, t2, t1, t10);
			}
			return;
		case 48:
			if (BETWEEN(t7, t9, t3)) {
				Swap4(t3, t4, t5, t8, t7, t6, t2, t1, t10, t8, t3, t2);
			} else {
				Swap4(t3, t4, t5, t7, t8, t9, t3, t6, t7, t1, t2, t3);
			}
			return;
		case 49:
			Swap4(t9, t10, t1, t5, t6, t7, t3, t4, t5, t3, t8, t9);
			return;
		case 50:
			Swap4(t3, t4, t5, t3, t6, t7, t9, t10, t1, t8, t3, t2);
			return;
		case 51:
			Swap4(t5, t6, t7, t1, t2, t3, t9, t10, t1, t4, t9, t8);
			return;
		case 52:
			Swap4(t5, t6, t7, t3, t4, t5, t9, t10, t1, t3, t8, t9);
			return;
		default:
			System.out.println("Make5OptMove: Internal error");
			break;
		}
	}

	private Node Best5OptMove(Node t1, Node t2, PassByRef.RefObject<Long> G0,
			PassByRef.RefObject<Long> Gain) {
		Node t3, t4, t5, t6 = null, t7, t8 = null, t9, t10 = null, T3 = null, T4 = null, T5 = null, T6 = null, T7 = null, T8 = null, T9 = null, T10 = null;
		Candidate Nt2, Nt4, Nt6, Nt8;
		long G1, G2, G3, G4, G5, G6, G7, G8, BestG8 = Integer.MIN_VALUE;
		int Case6 = 0, Case8 = 0, Case10 = 0, BestCase10 = 0;
		int X4, X6, X8, X10;
		boolean BTW275 = false, BTW674 = false, BTW571 = false, BTW376 = false, BTW574 = false, BTW671 = false, BTW471 = false, BTW673 = false, BTW573 = false, BTW273 = false;

		if (t2 != Suc(t1)) {
			Reversed ^= true;
		}

		/* Choose (t2,t3) as a candidate edge emanating from t2 */
		int i2 = 0;
		for (Nt2 = t2.CandidateSet[i2]; (t3 = Nt2.To) != null; Nt2 = t2.CandidateSet[++i2]) {
			if (t3 == t2._Pred || t3 == t2._Suc
					|| ((G1 = G0.argvalue - Nt2.Cost) <= 0)) {
				continue;
			}
			/* Choose t4 as one of t3's two neighbors on the tour */
			for (X4 = 1; X4 <= 2; X4++) {
				t4 = X4 == 1 ? Pred(t3) : Suc(t3);
				G2 = G1 + graph.D(t3._Id, t4._Id);
				if (X4 == 1
						&& (Gain.argvalue = G2 - graph.D(t4._Id, t1._Id)) > 0) {
					Make2OptMove(t1, t2, t3, t4);
					return null;
				}
				/* Choose (t4,t5) as a candidate edge emanating from t4 */
				int i4 = 0;
				for (Nt4 = t4.CandidateSet[i4]; (t5 = Nt4.To) != null; Nt4 = t4.CandidateSet[++i4]) {
					if (t5 == t4._Pred || t5 == t4._Suc
							|| ((G3 = G2 - Nt4.Cost) <= 0)) {
						continue;
					}

					/* Choose t6 as one of t5's two neighbors on the tour */
					for (X6 = 1; X6 <= 2; X6++) {
						if (X4 == 1) {
							if (X6 == 1) {
								if (BETWEEN(t2, t5, t4)) {
									Case6 = 1;
								} else {
									Case6 = 2;
								}
								t6 = Case6 == 1 ? Suc(t5) : Pred(t5);
							} else {
								t6 = t6 == t5._Pred ? t5._Suc : t5._Pred;
								if ((t5 == t1 && t6 == t2)
										|| (t5 == t2 && t6 == t1)) {
									continue;
								}
								Case6 += 2;
							}
						} else if (BETWEEN(t2, t5, t3)) {
							Case6 = 4 + X6;
							t6 = X6 == 1 ? Suc(t5) : Pred(t5);
							if (t6 == t1) {
								continue;
							}
						} else {
							Case6 = 6 + X6;
							t6 = X6 == 1 ? Pred(t5) : Suc(t5);
							if (t6 == t2) {
								continue;
							}
						}
						G4 = G3 + graph.D(t5._Id, t6._Id);
						if ((Case6 <= 2 || Case6 == 5 || Case6 == 6)
								&& (Gain.argvalue = G4
										- graph.D(t6._Id, t1._Id)) > 0) {
							Make3OptMove(t1, t2, t3, t4, t5, t6, Case6);
							return null;
						}
						/* Choose (t6,t7) as a candidate edge emanating from t6 */
						int i6 = 0;
						for (Nt6 = t6.CandidateSet[i6]; (t7 = Nt6.To) != null; Nt6 = t6.CandidateSet[++i6]) {
							if (t7 == t6._Pred || t7 == t6._Suc
									|| (t6 == t2 && t7 == t3)
									|| (t6 == t3 && t7 == t2)
									|| ((G5 = G4 - Nt6.Cost) <= 0)) {
								continue;
							}
							for (X8 = 1; X8 <= 2; X8++) {
								if (X8 == 1) {
									Case8 = Case6;
									switch (Case6) {
									case 1:
										if ((BTW275 = BETWEEN(t2, t7, t5))) {
											t8 = Suc(t7);
										} else {
											t8 = Pred(t7);
											BTW674 = BETWEEN(t6, t7, t4);
										}
										break;
									case 2:
										if ((BTW376 = BETWEEN(t3, t7, t6)))
											t8 = Suc(t7);
										else {
											t8 = Pred(t7);
											BTW571 = BETWEEN(t5, t7, t1);
										}
										break;
									case 3:
										t8 = Suc(t7);
										BTW574 = BETWEEN(t5, t7, t4);
										break;
									case 4:
										if ((BTW671 = BETWEEN(t6, t7, t1)))
											t8 = Pred(t7);
										else
											t8 = BETWEEN(t2, t7, t4) ? Suc(t7)
													: Pred(t7);
										break;
									case 5:
										t8 = Pred(t7);
										BTW471 = BETWEEN(t4, t7, t1);
										if (!BTW471)
											BTW673 = BETWEEN(t6, t7, t3);
										break;
									case 6:
										if ((BTW471 = BETWEEN(t4, t7, t1)))
											t8 = Pred(t7);
										else {
											t8 = Suc(t7);
											BTW573 = BETWEEN(t5, t7, t3);
										}
										break;
									case 7:
									case 8:
										t8 = Suc(t7);
										BTW273 = BETWEEN(t2, t7, t3);
										break;
									}
								} else {
									t8 = t8 == t7._Pred ? t7._Suc : t7._Pred;
									Case8 += 8;
								}
								if ((t7 == t1 && t8 == t2)
										|| (t7 == t2 && t8 == t1)
										|| (t7 == t3 && t8 == t4)
										|| (t7 == t4 && t8 == t3)) {
									continue;
								}
								if (Case6 == 3 && !BTW574
										&& (X8 == 1) == BETWEEN(t3, t7, t1)) {
									continue;
								}
								if (Case6 == 4 && BTW671 && X8 == 2) {
									break;
								}
								if (Case6 == 7 && !BTW273
										&& (X8 == 1) == BETWEEN(t5, t7, t1)) {
									continue;
								}
								if (Case6 == 8 && !BTW273
										&& !BETWEEN(t4, t7, t5)) {
									break;
								}
								G6 = G5 + graph.D(t7._Id, t8._Id);
								if (t8 != t1
										&& (Case6 == 3 ? BTW574
												: Case6 == 4 ? !BTW671
														: Case6 == 7 ? BTW273
																: Case6 != 8
																		&& X8 == 1)
										&& (Gain.argvalue = G6
												- graph.D(t8._Id, t1._Id)) > 0) {
									Make4OptMove(t1, t2, t3, t4, t5, t6, t7,
											t8, Case8);
									return null;
								}
								/*
								 * Choose (t8,t9) as a candidate edge emanating
								 * from t8
								 */
								int i8 = 0;
								for (Nt8 = t8.CandidateSet[i8]; (t9 = Nt8.To) != null; Nt8 = t8.CandidateSet[++i8]) {
									if (t9 == t8._Pred || t9 == t8._Suc
											|| t9 == t1
											|| (t8 == t2 && t9 == t3)
											|| (t8 == t3 && t9 == t2)
											|| (t8 == t4 && t9 == t5)
											|| (t8 == t5 && t9 == t4)
											|| ((G7 = G6 - Nt8.Cost) <= 0)) {
										continue;
									}
									/*
									 * Choose t10 as one of t9's two neighbors
									 * on the tour
									 */
									for (X10 = 1; X10 <= 2; X10++) {
										if (X10 == 1) {
											t10 = null;
											switch (Case8) {
											case 1:
												t10 = (BTW275 ? BETWEEN(t8, t9,
														t5)
														|| BETWEEN(t3, t9, t1)
														: BTW674 ? BETWEEN(t7,
																t9, t1)
																: BETWEEN(t7,
																		t9, t5)) ? Pred(t9)
														: Suc(t9);
												Case10 = 22;
												break;

											case 2:
												t10 = (BTW376 ? BETWEEN(t8, t9,
														t4) : BTW571 ? BETWEEN(
														t7, t9, t1)
														|| BETWEEN(t3, t9, t6)
														: BETWEEN(t7, t9, t1)) ? Pred(t9)
														: Suc(t9);
												Case10 = 23;
												break;
											case 3:
												if (BTW574) {
													t10 = BETWEEN(t5, t9, t1) ? Pred(t9)
															: Suc(t9);
													Case10 = 24;
													break;
												}
												if (!BETWEEN(t5, t9, t4))
													break;
												t10 = Suc(t9);
												Case10 = 1;
												break;
											case 4:
												if (BTW671) {
													if (!BETWEEN(t2, t9, t5))
														break;
													t10 = Suc(t9);
													Case10 = 2;
													break;
												}
												t10 = BETWEEN(t6, t9, t4) ? Pred(t9)
														: Suc(t9);
												Case10 = 25;
												break;
											case 5:
												t10 = (BTW471 ? BETWEEN(t7, t9,
														t1) : BTW673 ? BETWEEN(
														t7, t9, t5) : BETWEEN(
														t4, t9, t1)
														|| BETWEEN(t7, t9, t5)) ? Pred(t9)
														: Suc(t9);
												Case10 = 26;
												break;
											case 6:
												t10 = (BTW471 ? BETWEEN(t7, t9,
														t3) : BTW573 ? BETWEEN(
														t8, t9, t6) : BETWEEN(
														t4, t9, t1)
														|| BETWEEN(t8, t9, t6)) ? Pred(t9)
														: Suc(t9);
												Case10 = 27;
												break;
											case 7:
												if (BTW273) {
													t10 = BETWEEN(t5, t9, t3) ? Pred(t9)
															: Suc(t9);
													Case10 = 28;
													break;
												}
												if (!BETWEEN(t2, t9, t3))
													break;
												t10 = Suc(t9);
												Case10 = 3;
												break;
											case 8:
												if (BTW273) {
													if (!BETWEEN(t4, t9, t5))
														break;
													Case10 = 4;
												} else {
													if (!BETWEEN(t2, t9, t3))
														break;
													Case10 = 5;
												}
												t10 = Suc(t9);
												break;
											case 9:
												if (BTW275) {
													if (!BETWEEN(t7, t9, t4))
														break;
													t10 = Suc(t9);
													Case10 = 6;
													break;
												}
												if (!BTW674) {
													if (!BETWEEN(t2, t9, t7))
														break;
													t10 = Suc(t9);
													Case10 = 7;
													break;
												}
												if (!BETWEEN(t6, t9, t7))
													break;
												t10 = Suc(t9);
												Case10 = 8;
												break;
											case 10:
												if (BTW376) {
													if (!BETWEEN(t7, t9, t6))
														break;
													t10 = Suc(t9);
													Case10 = 9;
													break;
												}
												if (BTW571) {
													if (!BETWEEN(t2, t9, t7))
														break;
													t10 = Suc(t9);
													Case10 = 10;
													break;
												}
												if (!BETWEEN(t3, t9, t6)
														&& !BETWEEN(t2, t9, t7))
													break;
												t10 = Suc(t9);
												Case10 = 11;
												break;
											case 11:
												if (BTW574) {
													t10 = BETWEEN(t3, t9, t1) ? Pred(t9)
															: Suc(t9);
													Case10 = 29;
													break;
												}
												if (!BETWEEN(t5, t9, t4))
													break;
												t10 = Suc(t9);
												Case10 = 12;
												break;
											case 12:
												t10 = BETWEEN(t3, t9, t1) ? Pred(t9)
														: Suc(t9);
												Case10 = 30;
												break;
											case 13:
												if (BTW471) {
													if (!BETWEEN(t2, t9, t7))
														break;
													t10 = Suc(t9);
													Case10 = 13;
													break;
												}
												if (BTW673) {
													if (!BETWEEN(t6, t9, t7))
														break;
													t10 = Suc(t9);
													Case10 = 14;
													break;
												}
												if (!BETWEEN(t6, t9, t3)
														&& !BETWEEN(t2, t9, t7))
													break;
												t10 = Suc(t9);
												Case10 = 15;
												break;
											case 14:
												if (BTW471) {
													if (!BETWEEN(t2, t9, t7))
														break;
													t10 = Suc(t9);
													Case10 = 16;
													break;
												}
												if (BTW573) {
													if (!BETWEEN(t7, t9, t3)
															&& !BETWEEN(t2, t9,
																	t6))
														break;
													t10 = Suc(t9);
													Case10 = 17;
													break;
												}
												if (!BETWEEN(t7, t9, t6))
													break;
												t10 = Suc(t9);
												Case10 = 18;
												break;
											case 15:
												if (BTW273) {
													t10 = BETWEEN(t5, t9, t1) ? Pred(t9)
															: Suc(t9);
													Case10 = 31;
													break;
												}
												if (!BETWEEN(t2, t9, t3))
													break;
												t10 = Suc(t9);
												Case10 = 19;
												break;
											case 16:
												if (BTW273) {
													if (!BETWEEN(t4, t9, t5)) {
														break;
													}
													Case10 = 20;
												} else {
													if (!BETWEEN(t2, t9, t3)) {
														break;
													}
													Case10 = 21;
												}
												t10 = Suc(t9);
												break;
											}
											if (t10 == null) {
												break;
											}
										} else {
											if (Case10 >= 22) {
												continue;
											}
											Case10 += 31;
											t10 = t10 == t9._Pred ? t9._Suc
													: t9._Pred;
										}
										if (t10 == t1
												|| (t9 == t3 && t10 == t4)
												|| (t9 == t4 && t10 == t3)
												|| (t9 == t5 && t10 == t6)
												|| (t9 == t6 && t10 == t5)) {
											continue;
										}
										G8 = G7 + graph.D(t9._Id, t10._Id);
										if ((Gain.argvalue = G8
												- graph.D(t10._Id, t1._Id)) > 0) {
											Make5OptMove(t1, t2, t3, t4, t5,
													t6, t7, t8, t9, t10, Case10);
											return null;
										}
										if (G8 < t10.Cost) {
											continue;
										}
										if ((G8 > BestG8 || (G8 == BestG8
												&& Near(T9, T10) && !Near(t9,
													t10)))
												&& Swaps < MaxSwaps
												&& Excludable(t9, t10)) {
											/*
											 * Ignore the move if the gain does
											 * not vary
											 */
											if (G7 == G5 && G5 == G3
													&& G3 == G1) {
												continue;
											}
											T3 = t3;
											T4 = t4;
											T5 = t5;
											T6 = t6;
											T7 = t7;
											T8 = t8;
											T9 = t9;
											T10 = t10;
											BestCase10 = Case10;
											BestG8 = G8;
										}
									}
								}
							}
						}
					}
				}
			}
		}
		Gain.argvalue = (long) 0;
		if (T10 != null) {
			/* Make the best 5-opt move */
			Make5OptMove(t1, t2, T3, T4, T5, T6, T7, T8, T9, T10, BestCase10);
			Exclude(t1, t2);
			Exclude(T3, T4);
			Exclude(T5, T6);
			Exclude(T7, T8);
			Exclude(T9, T10);
			G0.argvalue = BestG8;
		}
		return T10;
	}

	private void RestoreTour() {
		Node t1;
		Node t2;
		Node t3;
		Node t4;

		/* Loop as long as the stack is not empty */
		while (Swaps > 0) {
			/* Undo topmost 2-opt move */
			Swaps--;
			t1 = SwapStack[Swaps].t1;
			t2 = SwapStack[Swaps].t2;
			t3 = SwapStack[Swaps].t3;
			t4 = SwapStack[Swaps].t4;
			Swap1(t3, t2, t1);
			Swaps--;
			/* Make edges (t1,t2) and (t2,t3) excludable again */
			t1.OldPredExcluded = t1.OldSucExcluded = false;
			t2.OldPredExcluded = t2.OldSucExcluded = false;
			t3.OldPredExcluded = t3.OldSucExcluded = false;
			t4.OldPredExcluded = t4.OldSucExcluded = false;
		}
	}

	private void StoreTour() {
		Node t;
		Node u;
		Candidate Nt;
		int i;
		while (Swaps > 0) {
			Swaps--;
			for (i = 1; i <= 4; i++) {
				t = i == 1 ? SwapStack[Swaps].t1 : i == 2 ? SwapStack[Swaps].t2
						: i == 3 ? SwapStack[Swaps].t3 : SwapStack[Swaps].t4;
				Activate(t);
				t.OldPred = t._Pred;
				t.OldSuc = t._Suc;
				t.OldPredExcluded = t.OldSucExcluded = false;
				t.Cost = Integer.MAX_VALUE;
				int z = 0;
				for (Nt = t.CandidateSet[z]; (u = Nt.To) != null; Nt = t.CandidateSet[++z]) {
					if (u != t._Pred && u != t._Suc && Nt.Cost < t.Cost) {
						t.Cost = Nt.Cost;
					}
				}
			}
		}
	}

	private long BridgeGain(Node s1, Node s2, Node s3, Node s4, Node s5,
			Node s6, Node s7, Node s8, int Case6, long G) {
		Node t1, t2, t3, t4, t5, t6, t7, t8, u2 = null, u3 = null;
		Candidate Nt2, Nt4, Nt6;
		long G0, G1, G2, G3, G4, G5, G6, Gain;
		int X4;

		switch (Case6) {
		case 3:
			if (2 * SegmentSize(s5, s4) <= Dimension) {
				u2 = s5;
				u3 = s4;
			} else {
				u2 = s3;
				u3 = s6;
			}
			break;
		case 4:
			if (2 * SegmentSize(s2, s5) <= Dimension) {
				u2 = s2;
				u3 = s5;
			} else {
				u2 = s6;
				u3 = s1;
			}
			break;
		case 0:
		case 7:
			if (2 * SegmentSize(s2, s3) <= Dimension) {
				u2 = s2;
				u3 = s3;
			} else {
				u2 = s4;
				u3 = s1;
			}
			break;
		}

		/* Choose t1 between u2 and u3 */
		for (t1 = u2; t1 != u3; t1 = t2) {
			/* Choose t2 as the successor of t1 */
			t2 = Suc(t1);
			if ((t1 == s1 && t2 == s2) || (t1 == s2 && t2 == s1)
					|| (t1 == s3 && t2 == s4) || (t1 == s4 && t2 == s3)
					|| (t1 == s5 && t2 == s6) || (t1 == s6 && t2 == s5)
					|| (t1 == s7 && t2 == s8) || (t1 == s8 && t2 == s7)) {
				continue;
			}
			G0 = G + graph.D(t1._Id, t2._Id);
			/*
			 * Choose (t2,t3) as a candidate edge emanating from t2. t3 must not
			 * be between u2 and u3
			 */
			int i2 = 0;
			for (Nt2 = t2.CandidateSet[i2]; (t3 = Nt2.To) != null; Nt2 = t2.CandidateSet[++i2]) {
				if (t3 == t2._Pred || t3 == t2._Suc || BETWEEN(u2, t3, u3)) {
					continue;
				}
				G1 = G0 - Nt2.Cost;
				/* Choose t4 as one of t3's two neighbors on the tour */
				for (X4 = 1; X4 <= 2; X4++) {
					t4 = X4 == 1 ? Suc(t3) : Pred(t3);
					if (t4 == t2 || (t3 == s1 && t4 == s2)
							|| (t3 == s2 && t4 == s1) || (t3 == s3 && t4 == s4)
							|| (t3 == s4 && t4 == s3) || (t3 == s5 && t4 == s6)
							|| (t3 == s6 && t4 == s5) || (t3 == s7 && t4 == s8)
							|| (t3 == s8 && t4 == s7)) {
						continue;
					}
					G2 = G1 + graph.D(t3._Id, t4._Id);
					/* Test if an improvement can be obtained */
					if ((Gain = G2 - graph.D(t4._Id, t1._Id)) > 0) {
						switch (Case6) {
						case 0:
							if (X4 == 1) {
								Swap3(s1, s2, s4, t3, t4, t1, s1, s3, s2);
							} else {
								Swap2(t1, t2, t3, s1, s2, s3);
							}
							return Gain;
						case 3:
							if ((X4 == 1) == (!BETWEEN(s2, t1, s6) && !BETWEEN(
									s2, t3, s6))) {
								Swap3(s1, s2, s3, t1, t2, t3, s5, s6, s1);
							} else {
								Swap4(s1, s2, s3, t1, t2, t4, s5, s6, s1, t2,
										t4, t1);
							}
							if (s8 != null) {
								Swap1(s7, s8, s1);
							}
							return Gain;
						case 4:
							if ((X4 == 1) == (!BETWEEN(s3, t1, s5) && !BETWEEN(
									s3, t3, s5))) {
								Swap3(s1, s2, s3, t1, t2, t3, s5, s6, s1);
							} else {
								Swap4(s1, s2, s3, t1, t2, t4, s5, s6, s1, t2,
										t4, t1);
							}
							if (s8 != null) {
								Swap1(s7, s8, s1);
							}
							return Gain;
						case 7:
							if ((X4 == 1) == (!BETWEEN(s4, t1, s6) && !BETWEEN(
									s4, t3, s6))) {
								Swap3(s5, s6, s1, t1, t2, t3, s3, s4, s5);
							} else {
								Swap4(s5, s6, s1, t1, t2, t4, s3, s4, s5, t2,
										t4, t1);
							}
							if (s8 != null) {
								Swap1(s7, s8, s1);
							}
							return Gain;
						}
					}
					/*
					 * If BridgeGain has been called with a nonfeasible 2-opt
					 * move, then try to find a 3-opt or 4-opt move which, when
					 * composed with the 2-opt move, results in an improvement
					 * of the tour
					 */
					if (Case6 != 0) {
						continue;
					}
					/* Choose (t4,t5) as a candidate edge emanating from t4 */
					int i4 = 0;
					for (Nt4 = t4.CandidateSet[i4]; (t5 = Nt4.To) != null; Nt4 = t4.CandidateSet[++i4]) {
						if (t5 == t4._Pred || t5 == t4._Suc || t5 == t1
								|| t5 == t2) {
							continue;
						}
						/*
						 * Choose t6 as one of t5's two neighbors on the tour.
						 * Only one choice!
						 */
						t6 = X4 == 1 || BETWEEN(u2, t5, u3) ? Pred(t5)
								: Suc(t5);
						if ((t5 == s1 && t6 == s2) || (t5 == s2 && t6 == s1)
								|| (t5 == s3 && t6 == s4)
								|| (t5 == s4 && t6 == s3)) {
							continue;
						}
						G3 = G2 - Nt4.Cost;
						G4 = G3 + graph.D(t5._Id, t6._Id);
						if ((Gain = G4 - graph.D(t6._Id, t1._Id)) > 0) {
							if (X4 == 1) {
								Swap4(s1, s2, s4, t3, t4, t1, s1, s3, s2, t5,
										t6, t1);
							} else {
								Swap3(t1, t2, t3, s1, s2, s3, t5, t6, t1);
							}
							return Gain;
						}
						/*
						 * Choose (t7,t8) as a candidate edge emanating from t7.
						 * Only one choice!
						 */
						int i6 = 0;
						for (Nt6 = t6.CandidateSet[i6]; (t7 = Nt6.To) != null; Nt6 = t6.CandidateSet[++i6]) {
							if (t7 == t6._Pred || t7 == t6._Suc) {
								continue;
							}
							/*
							 * Choose t8 as one of t7's two neighbors on the
							 * tour. Only one choice!
							 */
							if (X4 == 1) {
								t8 = (BETWEEN(u2, t5, t1) ? BETWEEN(t5, t7, t1)
										: BETWEEN(t2, t5, u3) ? BETWEEN(u2, t7,
												t1) || BETWEEN(t5, t7, u3)
												: BETWEEN(Suc(u3), t5, t3) ? BETWEEN(
														u2, t7, u3)
														|| BETWEEN(t5, t7, t3)
														: !BETWEEN(t4, t7, t6)) ? Pred(t7)
										: Suc(t7);
							} else {
								t8 = (BETWEEN(u2, t5, t1) ? !BETWEEN(u2, t7, t6)
										&& !BETWEEN(t2, t7, u3)
										: BETWEEN(t2, t5, u3) ? !BETWEEN(t2,
												t7, t6) : BETWEEN(Suc(u3), t5,
												t4) ? !BETWEEN(Suc(u3), t7, t5)
												&& !BETWEEN(t3, t7, Pred(u2))
												: !BETWEEN(t3, t7, t5)) ? Pred(t7)
										: Suc(t7);
							}
							if (t8 == t1 || (t7 == t1 && t8 == t2)
									|| (t7 == t3 && t8 == t4)
									|| (t7 == t4 && t8 == t3)
									|| (t7 == s1 && t8 == s2)
									|| (t7 == s2 && t8 == s1)
									|| (t7 == s3 && t8 == s4)
									|| (t7 == s4 && t8 == s3)) {
								continue;
							}

							G5 = G4 - Nt6.Cost;
							G6 = G5 + graph.D(t7._Id, t8._Id);
							/* Test if an improvement can be achieved */
							if ((Gain = G6 - graph.D(t8._Id, t1._Id)) > 0) {
								if (X4 == 1) {
									Swap4(s1, s2, s4, t3, t4, t1, s1, s3, s2,
											t5, t6, t1);
								} else {
									Swap3(t1, t2, t3, s1, s2, s3, t5, t6, t1);
								}
								Swap1(t7, t8, t1);
								return Gain;
							}
						}
					}
				}
			}
		}
		/* No improvement has been found */
		return 0;
	}

	private Node s1;

	private long Gain23() {
		Node s2, s3, s4, s5, s6 = null, s7, s8 = null, s1Stop;
		Candidate Ns2, Ns4, Ns6;
		long G0, G1, G2, G3, G4, G5, G6, Gain, Gain6;
		int X2, X4, X6, X8;
		int Case6 = 0, Case8 = 0;

		if (s1 == null) {
			s1 = FirstNode;
		}
		s1Stop = s1;
		for (X2 = 1; X2 <= 2; X2++) {
			Reversed = X2 == 1 ? OldReversed : (OldReversed ^= true);
			do {
				s2 = Suc(s1);

				G0 = graph.D(s1._Id, s2._Id);
				/* Choose (s2,s3) as a candidate edge emanating from s2 */
				int i2 = 0;
				for (Ns2 = s2.CandidateSet[i2]; (s3 = Ns2.To) != null; Ns2 = s2.CandidateSet[++i2]) {

					if (s3 == s2._Pred || s3 == s2._Suc) {
						continue;
					}
					G1 = G0 - Ns2.Cost;
					for (X4 = 1; X4 <= 2; X4++) {
						s4 = X4 == 1 ? Suc(s3) : Pred(s3);
						G2 = G1 + graph.D(s3._Id, s4._Id);

						/*
						 * Try any gainful nonfeasible 2-opt move followed by a
						 * 2-, 3- or 4-opt move
						 */
						if (X4 == 1
								&& s4 != s1
								&& 2 * SegmentSize(s2, s3) <= Dimension
								&& (G3 = G2 - graph.D(s4._Id, s1._Id)) > 0
								&& (Gain = BridgeGain(s1, s2, s3, s4, null,
										null, null, null, 0, G3)) > 0) {
							return Gain;
						}
						if (X4 == 2
								&& (Gain = G2 - graph.D(s4._Id, s1._Id)) > 0) {
							Swap1(s1, s2, s3);
							return Gain;
						}
						if (G2 - s4.Cost <= 0) {
							continue;
						}
						/*
						 * Try any gainful nonfeasible 3- or 4-opt move
						 * folllowed by a 2-opt move
						 */
						/* Choose (s4,s5) as a candidate edge emanating from s4 */
						int i4 = 0;
						for (Ns4 = s4.CandidateSet[i4]; (s5 = Ns4.To) != null; Ns4 = s4.CandidateSet[++i4]) {
							if (s5 == s4._Pred || s5 == s4._Suc
									|| (G3 = G2 - Ns4.Cost) <= 0) {
								continue;
							}
							/*
							 * Choose s6 as one of s5's two neighbors on the
							 * tour
							 */
							for (X6 = 1; X6 <= 2; X6++) {
								if (X4 == 2) {
									if (X6 == 1) {
										if (BETWEEN(s2, s5, s4)) {
											Case6 = 1;
										} else {
											Case6 = 2;
										}
										s6 = Case6 == 1 ? Suc(s5) : Pred(s5);
									} else {
										s6 = s6 == s5._Pred ? s5._Suc
												: s5._Pred;
										if (s5 == s1 || s6 == s1) {
											continue;
										}
										Case6 += 2;
									}
								} else if (BETWEEN(s2, s5, s3)) {
									Case6 = 4 + X6;
									s6 = X6 == 1 ? Suc(s5) : Pred(s5);
									if (s6 == s1) {
										continue;
									}
								} else {
									if (X6 == 2) {
										break;
									}
									Case6 = 7;
									s6 = Pred(s5);
								}
								G4 = G3 + graph.D(s5._Id, s6._Id);
								Gain6 = 0;
								if ((Gain6 = G4 - graph.D(s6._Id, s1._Id)) > 0) {
									if (Case6 <= 2 || Case6 == 5 || Case6 == 6) {
										Make3OptMove(s1, s2, s3, s4, s5, s6,
												Case6);
										return Gain6;
									}
									if ((Gain = BridgeGain(s1, s2, s3, s4, s5,
											s6, null, null, Case6, Gain6)) > 0) {
										return Gain;
									}
								}
								/*
								 * Choose (s6,s7) as a candidate edge emanating
								 * from s6
								 */
								int i6 = 0;
								for (Ns6 = s6.CandidateSet[i6]; (s7 = Ns6.To) != null; Ns6 = s6.CandidateSet[++i6]) {
									if (s7 == s6._Pred || s7 == s6._Suc
											|| (s6 == s2 && s7 == s3)
											|| (s6 == s3 && s7 == s2)
											|| (G5 = G4 - Ns6.Cost) <= 0) {
										continue;
									}
									/*
									 * Choose s6 as one of s5's two neighbors on
									 * the tour
									 */
									for (X8 = 1; X8 <= 2; X8++) {
										if (X8 == 1) {
											Case8 = Case6;
											switch (Case6) {
											case 1:
												s8 = BETWEEN(s2, s7, s5) ? Suc(s7)
														: Pred(s7);
												break;
											case 2:
												s8 = BETWEEN(s3, s7, s6) ? Suc(s7)
														: Pred(s7);
												break;
											case 3:
												if (BETWEEN(s5, s7, s4)) {
													s8 = Suc(s7);
												} else {
													s8 = BETWEEN(s3, s7, s1) ? Pred(s7)
															: Suc(s7);
													Case8 = 17;
												}
												break;
											case 4:
												if (BETWEEN(s2, s7, s5)) {
													s8 = BETWEEN(s2, s7, s4) ? Suc(s7)
															: Pred(s7);
												} else {
													s8 = Pred(s7);
													Case8 = 18;
												}
												break;
											case 5:
												s8 = Pred(s7);
												break;
											case 6:
												s8 = BETWEEN(s2, s7, s3) ? Suc(s7)
														: Pred(s7);
												break;
											case 7:
												if (BETWEEN(s2, s7, s3)) {
													s8 = Suc(s7);
												} else {
													s8 = BETWEEN(s5, s7, s1) ? Pred(s7)
															: Suc(s7);
													Case8 = 19;
												}
												break;
											}
										} else {
											if (Case8 >= 17
													|| (Case6 != 3
															&& Case6 != 4 && Case6 != 7)) {
												break;
											}
											s8 = s8 == s7._Pred ? s7._Suc
													: s7._Pred;
											Case8 += 8;
										}
										if (s8 == s1 || (s7 == s1 && s8 == s2)
												|| (s7 == s3 && s8 == s4)
												|| (s7 == s4 && s8 == s3)) {
											continue;
										}
										G6 = G5 + graph.D(s7._Id, s8._Id);
										if ((Gain = G6
												- graph.D(s8._Id, s1._Id)) > 0) {
											if (Case8 <= 15) {
												Make4OptMove(s1, s2, s3, s4,
														s5, s6, s7, s8, Case8);
												return Gain;
											}
											if (Gain > Gain6
													&& (Gain = BridgeGain(s1,
															s2, s3, s4, s5, s6,
															s7, s8, Case6, Gain)) > 0) {
												return Gain;
											}
										}
									}
								}
							}
						}
					}
				}
			} while ((s1 = s2) != s1Stop);
		}
		return 0;
	}

	private MyRandomGenerator rand = new MyRandomGenerator();
	private int EdgesInFragments;
	private long Cost;
	private int mark;

	private Node NearestNeighbor(Node From) {
		Candidate NN;
		Node To, N, First = null, Last = null, Nearest = null;
		int MaxLevel = Dimension, Min = Integer.MAX_VALUE, d;

		if (From.Degree == 2) {
			return null;
		}
		int ii = 0;
		for (NN = From.CandidateSet[ii]; (To = NN.To) != null; NN = From.CandidateSet[++ii]) {
			if (MayBeAddedToFragments(From, To)) {
				From.Cost = NN.Cost;
				return To;
			}
		}
		From.Level = 0;
		if (++mark == 0) {
			mark = 1;
		}
		From.mark = mark;
		/* Insert From into an empty queue */
		First = Last = From;
		From.OldSuc = null;

		while ((N = First) != null && N.Level < MaxLevel) {
			/* Remove the first node from the queue */
			if (N == Last) {
				First = Last = null;
			} else {
				First = N.OldSuc;
			}
			ii = 0;
			for (NN = N.CandidateSet[ii]; (To = NN.To) != null; NN = N.CandidateSet[++ii]) {
				if (To.mark != mark) {
					To.mark = mark;
					To.Level = N.Level + 1;
					if (MayBeAddedToFragments(From, To)
							&& (N == From ? (d = NN.Cost) < Min
									: (d = this.graph.D(From._Id, To._Id)) < Min)) {
						Min = From.Cost = d;
						/* Randomization */
						if (Nearest == null && rand.nextInt() % 3 != 0) {
							return To;
						}
						Nearest = To;
						MaxLevel = To.Level;
					} else if (To.Level < MaxLevel) {
						/* Insert To as the last element of the queue */
						if (Last != null) {
							Last.OldSuc = To;
						} else {
							First = To;
						}
						Last = To;
						Last.OldSuc = null;
					}
				}
			}
		}
		return Nearest;
	}

	private Node NearestInList(Node From, Node First) {
		Node To, Nearest = null;
		int Min = Integer.MAX_VALUE, d;

		To = First;
		do {
			if (MayBeAddedToFragments(From, To)
					&& (d = graph.D(From._Id, To._Id)) < Min) {
				Min = From.Cost = d;
				Nearest = To;
			}
		} while ((To = To.OldSuc) != First);
		return Nearest;
	}

	private boolean MayBeAddedToFragments(Node From, Node To) {
		return From != To && From.Degree != 2 && To.Degree != 2
				&& (From.Tail != To || EdgesInFragments == Dimension - 1);
	}

	private void AddEdgeToFragments(Node From, Node To) {
		Node Temp;

		if (From._Pred == null) {
			From._Pred = To;
		} else {
			From._Suc = To;
		}
		if (To._Pred == null) {
			To._Pred = From;
		} else {
			To._Suc = From;
		}
		From.Degree++;
		To.Degree++;
		Temp = From.Tail;
		Temp.Tail = To.Tail;
		To.Tail.Tail = Temp;
		EdgesInFragments++;
		Cost += From.Cost;
	}

	private void RemoveFromList(Node N, PassByRef.RefObject<Node> First) {
		if (First.argvalue == N) {
			First.argvalue = N.OldSuc;
		}

		N.OldPred.OldSuc = N.OldSuc;
		N.OldSuc.OldPred = N.OldPred;
	}

	private void InitateNodes() {
		for (int t = 0; t < Dimension; t++) {
			NodeSet[t].OldPredExcluded = NodeSet[t].OldSucExcluded = false;
			NodeSet[t].OldPred = NodeSet[t]._Pred;
			NodeSet[t].OldSuc = NodeSet[t]._Suc;
		}
	}

	private void InitiateNodesSegments() {
		Node FirstNode = NodeSet[0];
		Node t1;
		Node t2;
		int i;
		Segment S;
		SSegment SS;
		Reversed = false;
		S = FirstSegment;
		i = 0;
		do {
			S.Size = 0;
			S.Rank = ++i;
			S.Reversed = false;
			S._First = S._Last = null;
		} while ((S = S._Suc) != FirstSegment);
		SS = FirstSSegment;
		i = 0;
		do {
			SS.Size = 0;
			SS.Rank = ++i;
			SS.Reversed = false;
			SS.First = SS.Last = null;
		} while ((SS = SS.Suc) != FirstSSegment);
		i = 0;
		t1 = FirstNode;
		do {
			t2 = t1.OldSuc = t1._Suc;
			t1.OldPred = t1._Pred;
			t1.Rank = ++i;

			t1._Parent = S;
			S.Size++;
			if (S.Size == 1) {
				S._First = t1;
			}
			S._Last = t1;
			if (SS.Size == 0) {
				SS.First = S;
			}
			S._Parent = SS;
			SS.Last = S;
			if (S.Size == GroupSize) {
				S = S._Suc;
				SS.Size++;
				if (SS.Size == SGroupSize) {
					SS = SS.Suc;
				}
			}
			t1.OldPredExcluded = t1.OldSucExcluded = false;

		} while ((t1 = t1._Suc) != FirstNode);
		if (S.Size < GroupSize) {
			SS.Size++;
		}
	}

	private void AllocateSegments() {
		Segment S = null;
		Segment SPrev;
		SSegment SS = null;
		SSegment SSPrev;
		int i;

		GroupSize = (int) Math.sqrt((double) Dimension);
		SegmentSet = new Segment[(Dimension / GroupSize) + 1];
		for (int k = 0; k < SegmentSet.length; k++) {
			SegmentSet[k] = new Segment();
		}

		Groups = 0;
		int j = 0;
		for (i = Dimension, SPrev = null; i > 0; i -= GroupSize, SPrev = S) {
			S = SegmentSet[j];
			j++;
			S.Rank = ++Groups;
			if (SPrev == null) {
				FirstSegment = S;
			} else {
				SLink(SPrev, S);
			}
		}
		SLink(S, FirstSegment);
		SGroupSize = Dimension;
		SGroups = 0;
		for (i = Groups, SSPrev = null; i > 0; i -= SGroupSize, SSPrev = SS) {
			SS = new SSegment();
			SS.Rank = ++SGroups;
			if (SSPrev == null) {
				FirstSSegment = SS;
			} else {
				SLink(SSPrev, SS);
			}
		}
		SLink(SS, FirstSSegment);
		InitateNodes();
		InitiateNodesSegments();
	}

	private void SetTour(Tour tour) {
		this.s1 = null;
		int r_node = -1;
		int node = 0;
		int l_node = 0;
		r_node = l_node = -1;
		for (int i = 0; i < Dimension; i++) {
			NodeSet[i]._Id = i;
			NodeSet[i].Cost = Integer.MAX_VALUE;
			NodeSet[i].IsActivated = false;
			NodeSet[i].Next = NodeSet[i].OldPred = NodeSet[i].OldSuc = NodeSet[i]._Pred = NodeSet[i]._Suc = null;
			NodeSet[i]._Parent = null;
		}
		FirstActive = LastActive = null;
		this.Reversed = false;
		for (int i = 0; i <= Dimension; i++) {
			if (r_node == -1) {
				NodeSet[node]._Suc = NodeSet[node];
				NodeSet[node]._Pred = NodeSet[node];
				l_node = r_node = node;
				continue;
			}
			NodeSet[node]._Pred = NodeSet[r_node];
			NodeSet[node]._Suc = NodeSet[l_node];
			NodeSet[l_node]._Pred = NodeSet[node];
			NodeSet[r_node]._Suc = NodeSet[node];
			r_node = node;
			node = tour.Right(node);
		}
		AllocateSegments();
	}

	public Heuristics(Graph graph, int NumberOfCandidates) {
		this.cand_num = NumberOfCandidates;
		this.Number_Of_Candidates = NumberOfCandidates;
		this.graph = graph;
		MaxSwaps = Dimension = graph.getNumber_Of_Node();
		Swaps = 0;
		this.Reversed = this.OldReversed = false;
		AllocateStructures();
		CreateNodes();
		CreateNearestNeighborCandidateSet(NumberOfCandidates);
	}

	private class NodeComparator implements Comparator<Node> {
		public int compare(Node Na, Node Nb) {
			double x1 = ((Node) Na).X;
			double y1 = ((Node) Na).Y;
			double x2 = ((Node) Nb).X;
			double y2 = ((Node) Nb).Y;
			return x1 < x2 ? -1 : x1 > x2 ? 1 : y1 < y2 ? -1 : y1 > y2 ? 1 : 0;
		}
	}

	public final Tour Q_Boruvka() {
		Node From;
		Node To;
		Node First;
		Node Last = null;
		Node[] Perm;
		int Count;
		int i;
		Heap heap = new Heap(Dimension);
		Tour tour = new Tour(graph);
		mark = 0;
		Cost = 0;
		EdgesInFragments = 0;Node Prev = null;
        Node N = null;
        for (i = 0; i < Dimension; i++, Prev = N)
        {
            N = NodeSet[i];
            if (i == 0)
                FirstNode = N;
            else
                Link(Prev, N);
            N._Id = i;
        }
        Link(N, FirstNode);

        From = FirstNode = NodeSet[0];
		do {
			From.Degree = 0;
			From.Tail = From;
			From.mark = 0;
			From.Next = From._Suc;
			From._Pred = From._Suc = null;
		} while ((From = From.Next) != FirstNode);
		Count = 0;
		for (;;) {
			To = NearestNeighbor(From);

			if ((From.Nearest = To) != null) {
				Count++;
			}
			if ((From = From.Next) == FirstNode) {
				break;
			}

		}
		Perm = new Node[Count];
		for (From = FirstNode, i = 0; i < Count; From = From.Next) {
			if (From.Nearest != null) {
				Perm[i++] = From;
			}
		}

		NodeComparator compare = new NodeComparator();
		Arrays.sort(Perm, compare);

		for (i = 0; i < Count; i++) {
			From = Perm[i];
			if ((To = NearestNeighbor(From)) != null) {
				AddEdgeToFragments(From, To);
				i--;
			}
		}
		if (EdgesInFragments < Dimension) {
			/* Create a list of the degree-0 and degree-1 nodes */

			First = null;
			From = FirstNode;
			do {
				if (From.Degree != 2) {
					From.OldSuc = First;
					if (First != null) {
						First.OldPred = From;
					} else {
						Last = From;
					}
					First = From;
				}
			} while ((From = From.Next) != FirstNode);
			First.OldPred = Last;
			Last.OldSuc = First;
			/* Initialize the heap */
			From = First;
			do {
				if ((From.Nearest = NearestInList(From, First)) != null) {
					From.Rank = From.Cost;
					heap.HeapLazyInsert(From);
				}
			} while ((From = From.OldSuc) != First);
			heap.Heapify();
			/* Find the remaining fragments */
			while ((From = heap.HeapDeleteMin()) != null) {
				To = From.Nearest;
				if (MayBeAddedToFragments(From, To)) {
					AddEdgeToFragments(From, To);
					if (From.Degree == 2) {
						PassByRef.RefObject<Node> tempRef_First = new PassByRef.RefObject<Node>(
								First);
						RemoveFromList(From, tempRef_First);
						First = tempRef_First.argvalue;
					}
					if (To.Degree == 2) {
						PassByRef.RefObject<Node> tempRef_First2 = new PassByRef.RefObject<Node>(
								First);
						RemoveFromList(From, tempRef_First2);
						First = tempRef_First2.argvalue;
					}
				}
				if (From.Degree != 2
						&& (From.Nearest = NearestInList(From, First)) != null) {
					From.Rank = From.Cost;
					heap.HeapInsert(From);
				}
			}
		}
		To = FirstNode;
		From = To._Pred;
		do {
			tour.Add(To._Id);
			if (To._Suc == From) {
				To._Suc = To._Pred;
				To._Pred = From;
			}
			From = To;
		} while ((To = From._Suc) != FirstNode);
		To._Pred = From;
		heap = null;
		return tour;
	}

	public final void LinKernighan(Tour tour)
	{

			this.SetTour(tour);
			for (int t = 0; t < this.Dimension; t++)
			{
				Activate(NodeSet[t]);
			}

			long Gain = 0, G0;
			int X2;

			Node t1 = null, SUCt1 = null, t2 = null;
			Candidate Nt;

			for (int i = 0; i < Dimension; i++)
			{
				Node t = NodeSet[i];
				int ii = 0;
				for (Nt = t.CandidateSet[ii]; Nt.To != null; Nt = t.CandidateSet[++ii])
				{
					t2 = Nt.To;
					int cost_candidate = graph.D(t._Id, t2._Id);
					if (t2 != Pred(t) && t2 != Suc(t) && cost_candidate < t.Cost)
					{
						t.Cost = cost_candidate;
					}
				}
			}
			while (true)
			{
				while ((t1 = RemoveFirstActive()) != null)
				{
					SUCt1 = Suc(t1);
					for (X2 = 1; X2 <= 2; X2++)
					{
						t2 = X2 == 1 ? Pred(t1) : SUCt1;
						if (t2 == t1.BestPred || t2 == t1.BestSuc)
						{
							continue;
						}
						G0 = graph.D(t1._Id, t2._Id);
						do
						{
							PassByRef.RefObject<Long> tempRef_G0 = new PassByRef.RefObject<Long>(G0);
							PassByRef.RefObject<Long> tempRef_Gain = new PassByRef.RefObject<Long>(Gain);
							t2 = Best5OptMove(t1, t2, tempRef_G0, tempRef_Gain);
							G0 = tempRef_G0.argvalue;
							Gain = tempRef_Gain.argvalue;
						}
						while (t2 != null);
						if (Gain > 0)
						{
							StoreTour();
							Activate(t1);
							break;
						}
						RestoreTour();
					}
				}
				if ((Gain = Gain23()) > 0)
				{
					StoreTour();
				}
				else
				{
					break;
				}
			}

			tour.Reset();
			int node = 0;
			for (int i = 0; i < Dimension; i++)
			{
				tour.Add(node);
				Node p = Suc(this.NodeSet[node]);
				node = p._Id;
			}
	}
		public final void LinKernighan(Tour tour, int[] ActiveNodes, int NumberOfActiveNodes)
		{
			this.SetTour(tour);
			for (int t = 0; t < NumberOfActiveNodes; t++)
			{
				Activate(NodeSet[ActiveNodes[t]]);
			}

			long Gain = 0;
			long G0;
			int X2;

			Node t1 = null, SUCt1 = null, t2 = null;
			Candidate Nt;

			for (int i = 0; i < Dimension; i++)
			{
				Node t = NodeSet[i];
				int nti = 0;
				for (Nt = t.CandidateSet[nti]; Nt.To != null; Nt = t.CandidateSet[++nti])
				{
					t2 = Nt.To;
					int cost_candidate = graph.D(t._Id, t2._Id);
					if (t2 != Pred(t) && t2 != Suc(t) && cost_candidate < t.Cost)
					{
						t.Cost = cost_candidate;
					}
				}
			}
			while (true)
			{
				while ((t1 = RemoveFirstActive()) != null)
				{
					SUCt1 = Suc(t1);
					for (X2 = 1; X2 <= 2; X2++)
					{
						t2 = X2 == 1 ? Pred(t1) : SUCt1;
						if (t2 == t1.BestPred || t2 == t1.BestSuc)
						{
							continue;
						}
						G0 = graph.D(t1._Id, t2._Id);
						do
						{
							PassByRef.RefObject<Long> tempRef_G0 = new PassByRef.RefObject<Long>(G0);
							PassByRef.RefObject<Long> tempRef_Gain = new PassByRef.RefObject<Long>(Gain);
							t2 = Best5OptMove(t1, t2, tempRef_G0, tempRef_Gain);
							G0 = tempRef_G0.argvalue;
							Gain = tempRef_Gain.argvalue;
						}
						while (t2 != null);
						if (Gain > 0)
						{
							StoreTour();
							Activate(t1);
							break;
						}
						RestoreTour();
					}
				}
				if ((Gain = Gain23()) > 0)
				{
					StoreTour();
				}
				else
				{
					break;
				}
			}
			tour.Reset();
			int node = 0;
			for (int i = 0; i < Dimension; i++)
			{
				tour.Add(node);
				Node p = Suc(this.NodeSet[node]);
				node = p._Id;
			}
		}
	
	public final int[] DoubleBridge(Tour tour) {
		// return 8 nodes and these nodes will be activated in LK.
		int Dimension = this.graph.getNumber_Of_Node();
		int[] input = new int[Dimension];
		int node = 0;
		for (int i = 0; i < Dimension; i++) {
			input[i] = node;
			node = tour.Right(node);
		}
		int[] ret_nodes = new int[8];
		int A_F = 0;
		int A_E = rand.Random(1, Dimension - 6 - 1);
		int B_F = A_E + 1;
		int B_E = rand.Random(B_F + 1, Dimension - 4 - 1);
		int C_F = B_E + 1;
		int C_E = rand.Random(C_F + 1, Dimension - 2 - 1);
		int D_F = C_E + 1;
		int D_E = Dimension - 1;
		ret_nodes[0] = A_F;
		ret_nodes[1] = A_E;
		ret_nodes[2] = B_F;
		ret_nodes[3] = B_E;
		ret_nodes[4] = C_F;
		ret_nodes[5] = C_E;
		ret_nodes[6] = D_F;
		ret_nodes[7] = D_E;
		int A_LEN = A_E - A_F + 1;
		int B_LEN = B_E - B_F + 1;
		int C_LEN = C_E - C_F + 1;
		int D_LEN = D_E - D_F + 1;
		int[] output = new int[(Dimension)];

		for (int i = A_F; i <= A_E; i++) {
			output[i] = input[i];
		}
		for (int i = 0; i < D_LEN; i++) {
			output[A_LEN + i] = input[i + D_F];
		}
		for (int i = 0; i < C_LEN; i++) {
			output[i + A_LEN + D_LEN] = input[i + C_F];
		}
		for (int i = 0; i < B_LEN; i++) {
			output[i + A_LEN + D_LEN + C_LEN] = input[i + B_F];
		}
		tour.Reset();
		for (int i = 0; i < Dimension; i++) {
			tour.Add(output[i]);
		}
		output = null;
		input = null;
		return ret_nodes;
	} // DoubleBridge

	public final void SetBestTour(Tour best_tour) {
		for (int t = 0; t < Dimension; t++) {
			NodeSet[t].BestPred = NodeSet[best_tour.Left(t)];
			NodeSet[t].BestSuc = NodeSet[best_tour.Right(t)];
		}
	}

	public final void ResetBestTour() {
		for (int t = 0; t < Dimension; t++) {
			NodeSet[t].BestPred = null;
			NodeSet[t].BestSuc = null;
		}
	}

	public final int GetCandidate(int node, int index) {
		return NodeSet[node].CandidateSet[index].To._Id;
	}
}
