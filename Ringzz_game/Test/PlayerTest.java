package Test;

import org.junit.Before;
import org.junit.Test;

import Client.Controller.Client;
import Client.Controller.ComputerPlayer;
import Client.Controller.HumanPlayer;
import Client.Controller.Player;
import Client.View.TUI;
import Exceptions.MoveNotPossibleException;
import Exceptions.NoMovePossibleException;
import Exceptions.ServerCommunicationException;
import Model.Board;
import Model.Piece;
import Model.Player.*;
import Model.Player.Strategy.*;
import Server.Game;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

// TODO: Auto-generated Javadoc
/**
 * The Class PlayerTest.
 */
public class PlayerTest {
	
	/** The computer. */
	private Player human, computer;
	
	/** The colors 2. */
	private List<String> colors1, colors2;
	
	/** The pieces 2. */
	private List<Piece> pieces1, pieces2;
	
	/** The piece 2. */
	private Piece piece1, piece2;
	
	/** The strat. */
	private Strategy strat;
	
	/**
	 * Sets the up.
	 */
	@Before
    public void setUp() {
		//Creating the names, colors, and pieces of the players
		String name1 = "human";
		String name2 = "computer";
		
		// Colors
		colors1 = new ArrayList<String>();
		colors1.add(Game.COLOR1);
		colors1.add(Game.COLOR2);
		colors2 = new ArrayList<String>();
		colors2.add(Game.COLOR3);
		colors2.add(Game.COLOR4);
		
		// Pieces
		pieces1 = new ArrayList<Piece>();
		piece1 = new Piece(Game.RING1, Game.COLOR1);
		piece2 = new Piece(Game.RING2, Game.COLOR2);
		pieces1.add(piece1);
		pieces1.add(piece2);
		
		pieces2 = new ArrayList<Piece>();
		pieces2.add(new Piece(Game.RING3, Game.COLOR3));
		pieces2.add(new Piece(Game.RING4, Game.COLOR4));
		
		// Board, TUI and strategy
		Board board = new Board();
		PrintWriter printer = new PrintWriter(System.out, false);
		PrintWriter printer2 = new PrintWriter(System.out, false);
		Client client1 = new Client(printer, name1);
		Client client2 = new Client(printer2, name2);
		TUI tui = new TUI(client1);
		strat = new NaiveStrategy();

		// Creating the players
		human = new HumanPlayer(name1, colors1, board, pieces1, client1, tui, 10);
		computer = new ComputerPlayer(name2, colors2, board, pieces2, client2, strat, 10);		
    }
    
    /**
     * Test whether both players return the right name.
     */
    @Test
    public void testGetName() {
    	assertEquals("human", human.getName());
    	assertEquals("computer", computer.getName());
    }
    
    /**
     * Test whether both players return the right colors.
     */
    @Test
    public void testGetColor() {
    	assertEquals(colors1, human.getColor());
    	assertEquals(colors2, computer.getColor());
    }
	
    /**
     * Test whether both players return the right available pieces.
     */
    @Test
    public void testAvailablePieces() {
    	assertEquals(pieces2, computer.getAvailablePieces());
    	assertEquals(pieces1, human.getAvailablePieces());
//    	try {
//			computer.setMove();
//		} catch (ServerCommunicationException | InterruptedException | MoveNotPossibleException
//				| NoMovePossibleException e) {
//			System.out.println(e.getMessage());
//		}
//    	assertFalse(pieces2.equals(computer.getAvailablePieces()));
    }
    
    /**
     * Test whether the method recognises the piece and picks the right one if it has it.
     * Test whether returns null if it does not have the piece.
     */
    @Test
    public void testGetPiece() {
		assertEquals(piece1, human.getPiece(Game.COLOR1, Game.RING1));
		assertEquals(piece2, human.getPiece(Game.COLOR2, Game.RING2));
		assertEquals(null, human.getPiece(Game.COLOR3, Game.RING3));
		assertEquals(null, human.getPiece(Game.COLOR1, Game.RING2));
    }
    
    // ------------ Specifically for the HumanPlayer
    
    /**
     * Test whether the method checkColor works.
     */
    @Test
    public void testCheckColor() {
    	assertTrue(((HumanPlayer)human).checkColor(Game.COLOR1));
    	assertTrue(((HumanPlayer)human).checkColor(Game.COLOR2));
    	assertFalse(((HumanPlayer)human).checkColor(Game.COLOR3));
    	assertFalse(((HumanPlayer)human).checkColor(Game.COLOR4));
    }
    
    // ------------ Specifically for the ComputerPlayer
    /**
     * Test whether getStrategy() returns the right strategy object.
     */
    @Test
    public void testGetStrategy() {
    	assertEquals(strat,((ComputerPlayer)computer).getStrategy());
    }
    
//    @Test
//    public void testComputerSetMove() {
//    	try {
//			computer.setMove();
//		} catch (ServerCommunicationException | InterruptedException | MoveNotPossibleException
//				| NoMovePossibleException e) {
//			System.out.println(e.getMessage());
//		}
//    }
}
