package Model.Player.Strategy;

import java.util.List;
import java.util.Random;

import Exceptions.NoMovePossibleException;
import Model.Board;
import Model.Piece;
// TODO: Auto-generated Javadoc
/**
 * A class implementing the Strategy interface should have a method to determine a move on the board with the given pieces. The NaiveStrategy randomly goes through the pieces and locations, until it has found a valid move. 
 * SmartStrategy has some algorithm to determine which moves are better than others. 
 * For example, if a base can be places, this is always done. 
 * If not, then placing pieces which occupy a field is given priority, then playing even in a field, 
 * and then the rest of the moves.
 * @author Oskar
 */
public abstract class Strategy {
	
	/**
	 * This method returns a String encoding a move suggested by the Strategy .
	 *
	 * @param board to be played on
	 * @param pieces the strategy can choose from
	 * @param colors the colors
	 * @return a String encoding the move, null if no move could be found
	 */
	public abstract String detMove(Board board, List<Piece> pieces, List<String> colors);
	
	/**
	 * Det move.
	 *
	 * @param board the board
	 * @param pieces the pieces
	 * @param colors the colors
	 * @param totalTime the total time
	 * @return the string
	 */
	public abstract String detMove(Board board, List<Piece> pieces, List<String> colors, int totalTime);
	
// 	A Fisher–Yates shuffle
	/**
	 * Randomizing an <code>array</code> using the Fisher-Yates shuffle method.
	 * @param array which needs to be shuffled.
	 */
	public static void shuffleArray(int[] array)
	{
	    int index, temp;
	    Random random = new Random();
	    for (int i = array.length - 1; i > 0; i--)
	    {
	        index = random.nextInt(i + 1);
	        temp = array[index];
	        array[index] = array[i];
	        array[i] = temp;
	    }
	}
}
