import java.util.ArrayList;
import java.util.Random;

public class EntryPoint 
{	
	static Tour IGX(Graph graph, Tour father,Tour mother)
	{
		int Number_Of_Node = graph.getNumber_Of_Node();
        Tour child = new Tour(graph);
        MyRandomGenerator rand = new MyRandomGenerator();
        
		int CurrentNode , WinnerNode;		
		//int RightOf_C_In_Father , LeftOf_C_In_Father; 
		//int RightOf_C_In_Mother , LeftOf_C_In_Mother; 
		int Dimension = graph.getNumber_Of_Node();
		int CandidateNextNodeFromParents[]=new int[4];
		int RightOf_C_In_Father[] = new int[Dimension];
		int LeftOf_C_In_Father[] = new int[Dimension];
		int RightOf_C_In_Mother[] = new int[Dimension];
		int LeftOf_C_In_Mother[] = new int[Dimension];
		for (int i = 0; i < Dimension; i++)
		{
			RightOf_C_In_Father[i] = father.Right(i);
			LeftOf_C_In_Father[i] = father.Left(i);
			RightOf_C_In_Mother[i] = mother.Right(i);
			LeftOf_C_In_Mother[i] = mother.Left(i);
		}
		CurrentNode = rand.Random(0,Dimension - 1);
		WinnerNode = CurrentNode;
		for (int k = 0; k < Dimension - 1; k++)
		{
			child.Add(WinnerNode);
			CurrentNode = WinnerNode;

			RightOf_C_In_Father[LeftOf_C_In_Father[CurrentNode]] = RightOf_C_In_Father[CurrentNode];
			LeftOf_C_In_Father[RightOf_C_In_Father[CurrentNode]] = LeftOf_C_In_Father[CurrentNode];
			RightOf_C_In_Mother[LeftOf_C_In_Mother[CurrentNode]] = RightOf_C_In_Mother[CurrentNode];
			LeftOf_C_In_Mother[RightOf_C_In_Mother[CurrentNode]] = LeftOf_C_In_Mother[CurrentNode];

			CandidateNextNodeFromParents[0] = RightOf_C_In_Father[CurrentNode];
			CandidateNextNodeFromParents[1] = LeftOf_C_In_Father[CurrentNode];
			CandidateNextNodeFromParents[2] = RightOf_C_In_Mother[CurrentNode];
			CandidateNextNodeFromParents[3] = LeftOf_C_In_Mother[CurrentNode];

			WinnerNode = CandidateNextNodeFromParents[0];
			for (int j = 1; j < 4; j++)
			{
				if (graph.D(CandidateNextNodeFromParents[j], CurrentNode) <
					graph.D(WinnerNode, CurrentNode))
					WinnerNode = CandidateNextNodeFromParents[j];
			}
		}
		child.Add(WinnerNode);

		return child;
	}
	
	public static Tour Operate_GSX2_AndGet(Graph graph, Tour father, Tour mother)
    {
		int Number_Of_Node = graph.getNumber_Of_Node();
        Tour child = new Tour(graph);
        MyRandomGenerator rand = new MyRandomGenerator();
        int B_Node = rand.Random(0, Number_Of_Node - 1);
        child.Add(B_Node);

        int xNode = father.Left(B_Node);
        int yNode = father.Right(B_Node);
        int pNode = mother.Left(B_Node);
        int qNode = mother.Right(B_Node);
        if (xNode == qNode || yNode == pNode)
        {
            int direct1 = father.Right(B_Node), direct2 = mother.Right(B_Node);
            while (!child.IsComplete())
            {
                child.AddToLeft(direct2);
                child.Add(direct1);
                direct2 = mother.Right(direct2);
                direct1 = father.Right(direct1);

            }//while (child1.IsCompleted)
        }
        else
        {
            int direct2 = mother.Left(B_Node), direct1 = father.Right(B_Node);
            while (!child.IsComplete())
            {
                child.AddToLeft(direct2);
                child.Add(direct1);
                direct2 = mother.Left(direct2);
                direct1 = father.Right(direct1);
            }//while (child1.IsCompleted)
        }
        return child;
    }//public void Operate_GSX_2(ref Tour child)
	
	static int LinearSelection(int pop_size)
	{
		MyRandomGenerator rnd = new MyRandomGenerator();
		
		final double Bias = 1.25;
		return (int)(pop_size *
			(Bias -
			Math.sqrt((Bias * Bias - 4 * (Bias - 1) * rnd.nextDouble()))) /
			2 / (Bias - 1));
	}
	static void SimpleHGA(Graph g, int popsize, int gensize)
	{
		Heuristics heur = new Heuristics(g, 5);
		
		Tour population[] = new Tour[popsize];
		for(int i = 0; i < population.length; i++)
		{
			population[i] = heur.Q_Boruvka();
			//heur.LinKernighan(population[i]);
			
			//population[i] = new Tour(g);
			//population[i].InitiateRandomly();
			//heur.LinKernighan(population[i]);
		}
		
		double bestCost = population[0].Cost();
		int bestindex = 0;
		for(int i = 0; i < population.length; i++)
		{		
			if(population[i].Cost() < bestCost)
			{
				bestCost = population[i].Cost();
				bestindex = i;
			}
		}
		
		MyRandomGenerator rnd = new MyRandomGenerator();
		double XR = 0.9;
		for(int gen = 0; gen < gensize; gen++)
		{
			if(rnd.nextDouble() < XR)
			{
				int findex = LinearSelection(popsize);
				int mindex = LinearSelection(popsize);
				Tour child = IGX(g, population[findex], population[mindex]);
				heur.LinKernighan(child);
				int rindex = findex;
				if(population[mindex].Cost() > population[rindex].Cost())
					rindex = mindex;
				if(child.Cost() < population[rindex].Cost())
					population[rindex] = child;
				
				if(population[rindex].Cost() < bestCost)
				{
					bestCost = population[rindex].Cost();
					bestindex = rindex;
					System.out.println(bestCost);
				}
			}
			else
			{
				int mindex = LinearSelection(popsize);
				if(mindex == bestindex)
					mindex = (mindex + 1) % popsize;
				heur.DoubleBridge(population[mindex]);
				heur.LinKernighan(population[mindex]);
								
				if(population[mindex].Cost() < bestCost)
				{
					bestCost = population[mindex].Cost();
					bestindex = mindex;
					System.out.println(bestCost);
				}
			}
		}
	}
	
	public static void main(String[] args) 
	{	
		Graph g = null;
		try
		{
			g = new Graph("E:\\Research\\TSP\\_#_ExHD_\\FinalPaper\\ProgramAboutTSP\\Temp\\Tour_Design\\My_LK\\LKHWin-2.0.5\\LKHWin-2.0.5\\pr2392.tsp");
		}
		catch(Exception e)
		{
			System.out.println("error");
		}
		
		SimpleHGA(g, 5, 10000);
		
		/*Heuristics heur = new Heuristics(g, 5);
		Tour tour = new Tour(g);		
		tour.InitiateOrderly();
		long t1 = System.currentTimeMillis();
		tour = heur.Q_Boruvka();
		System.out.println(tour.Cost());
		heur.DoubleBridge(tour);
		System.out.println(tour.Cost());
		heur.LinKernighan(tour);
		long t2 = System.currentTimeMillis();
		
		System.out.println(tour.Cost());
		System.out.println(t2 - t1);*/
		
		
	}
}
