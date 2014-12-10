package za.co.twyst.GA144.assembler;

/** Container class for a program segment.
 * 
 */
public class Segment {
	// INSTANCE VARIABLES
	
	public final int   origin;
	public final int[] code;
	
	// CONSTRUCTOR
	
	public Segment(int origin,int[] code) {
		this.origin = origin;
		this.code   = code;
	}
}
