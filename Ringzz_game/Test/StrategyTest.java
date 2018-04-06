package Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.io.PrintWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

import org.junit.Before;
import org.junit.Test;

import Client.Controller.Client;
import Client.Controller.Player;
import Client.View.TUI;
import Model.Board;
import Model.Piece;
import Model.User;
import Model.Player.Strategy.*;
import Server.Game;
import Server.Server;
import Server.UserIO;

import static org.junit.Assert.assertTrue;

// TODO: Auto-generated Javadoc
/**
 * The Class StrategyTest.
 */
public class StrategyTest {
	
	/** The strat. */
	private Strategy strat;
	
	/** The strat 2. */
	private Strategy strat2;
	
	/**
	 * Sets the up.
	 */
	@Before
    public void setUp() {
		strat = new NaiveStrategy();
		strat2 = new SmartStrategy();
    }
    
	/**
	 * Test whether the shuffleArray() method actually gives a different array.
	 * Visual inspection is also used to test the randomization.
	 * It is also checked if elements which are expected in the shuffled array, are still there.
	 */
    @Test
    public void testShuffleArray() {
    	int[] array1 = new int[25];
    	int[] array2 = new int[25];
        for (int i=0; i<25; i++) {
        	array1[i] = i;
        	array2[i] = i;
        }
        System.out.println("array1: " + (Arrays.toString(array1)));
        assertTrue(Arrays.equals(array1, array2));
        Strategy.shuffleArray(array1);
        System.out.println("shuffled array1: " + (Arrays.toString(array1)));
        assertFalse(Arrays.equals(array1, array2));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 0));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 1));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 3));
    	assertFalse(IntStream.of(array1).anyMatch(x -> x == -5));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 13));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 15));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 17));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 18));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 20));
    	assertTrue(IntStream.of(array1).anyMatch(x -> x == 24));
    	assertFalse(IntStream.of(array1).anyMatch(x -> x == 25));
    }
    
    /**
     * Test whether the strategy returns null if there is no move possible.
     */
    @Test
    public void testNoMovePossible() {
    	List<String> colors = new ArrayList<>();
    	colors.add(Game.COLOR4);
    	Board board = new Board();
    	List<Piece> pieces = new ArrayList<>();
    	Piece piece1 = new Piece (Game.SBASE, Game.COLOR4);
    	Piece piece2 = new Piece (Game.RING1, Game.COLOR4);
    	pieces.add(piece1);
    	pieces.add(piece2);
    	assertFalse(strat.detMove(board, pieces, colors) == (null));
    	assertFalse(strat2.detMove(board, pieces, colors) == (null));
    	pieces.remove(piece1);
    	pieces.remove(piece2);
    	assertTrue(strat.detMove(board, pieces, colors) == (null));
    	assertTrue(strat2.detMove(board, pieces, colors) == (null));
    }
}
