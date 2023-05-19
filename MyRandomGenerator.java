public class MyRandomGenerator extends java.util.Random {

	public int Random(int a, int b) {
		int nextInt = this.nextInt();
		int range = b - a;
		int portion = (int)(this.nextDouble() * (double)range);
		int retval = a + portion;
		return retval;
		//return a + (this.nextInt() / (b - a));
	}

	public int[] RandomArray(int Dimension) {
		int[] output = new int[Dimension];
		for (int i = 0; i < Dimension; i++) {
			output[i] = i;
		}
		for (int i = 0; i < Dimension; i++) {
			int index = Random(0, Dimension - 1);
			int temp = output[i];
			output[i] = output[index];
			output[index] = temp;
		}
		return output;
	}
}