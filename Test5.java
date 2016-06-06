public class Test5{
	public void testMe(int x, int y) {
		int z = x + 3 - 32 * y;
		int k;
		k = -3 + x;
		if (!(x>=y) && k == 3){
			k = k/x;
		}else{
			z = z-2;
		}
		assert(z - y > 0 && k < 0 || z < 0);
	}
}
