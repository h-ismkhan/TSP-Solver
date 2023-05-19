import java.util.ArrayList;
import java.util.Random;

public class EntryPoint 
{	
	public static void main(String[] args) 
	{	
		Graph g = null;
		try
		{
			g = new Graph("E:\\a280.tsp");
		}
		catch(Exception e)
		{
			System.out.println("error");
		}
		
		Tour tour = new Tour(g);		
		tour.InitiateOrderly();//0-1-2-3...-279(280-1)
		
		
		System.out.println(tour.Cost());
		System.out.println(t2 - t1);*/
		
		
	}
}
