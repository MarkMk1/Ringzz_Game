package Test;

import static org.junit.Assert.assertEquals;

import java.io.PrintWriter;
import java.util.Scanner;

import org.junit.Before;
import org.junit.Test;

import Client.Controller.Client;
import Client.Controller.ComputerPlayer;
import Client.Controller.Player;
import Client.View.TUI;
import Exceptions.InvalidArgumentContentException;
import Exceptions.InvalidInputException;
import Exceptions.ServerCommunicationException;
import Model.Board;
import Model.Piece;
import Server.Game;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;

// TODO: Auto-generated Javadoc
/**
 * The Class ClientTest.
 */
public class ClientTest {
	
	/** The client. */
	private Client client;
	
	/** The tui. */
	private TUI tui;
	
	/** The board. */
	private Board board;
	
	/**
	 * Sets the up.
	 */
	@Before
    public void setUp() {
		client = new Client(new PrintWriter(System.out, true), "Harry");
		tui = new TUI(client);
		board =  new Board();
		client.addColor(Game.COLOR1);
		client.addColor(Game.COLOR2);
    }
    
    /**
     * Check whether creating a player works correctly, in the case
     * where for one of the colors only 1/3 of the pieces is received.
     */
    @Test
    public void testCreateAndGetPlayer() {
    	client.createPlayer(Game.COLOR1, true, true, tui, board, 100);
    	Player harry = client.getPlayer();
    	assertTrue(harry.getColor().contains(Game.COLOR1));
    	assertTrue(harry.getColor().contains(Game.COLOR2));
    	assertEquals(harry.getAvailablePieces().size(), 20);
    }
    
    /**
     * Check whether creating a player works correctly, 
     * with the right amount of pieces and the right colors.
     */
    @Test
    public void testCreateAndGetPlayer2() {
    	client.createPlayer(null, true, true, tui, board, 100);
    	Player harry = client.getPlayer();
    	assertTrue(harry.getColor().contains(Game.COLOR1));
    	assertTrue(harry.getColor().contains(Game.COLOR2));
    	assertEquals(harry.getAvailablePieces().size(), 30);
    }
    
    /**
     * Check whether creating a player works correctly, 
     * with the right amount of pieces and the right colors in the case that the player has the first turn
     * (and thus has the starting base as well).
     */
    @Test
    public void testCreateAndGetPlayer3() {
    	client.createPlayer(null, true, true, tui, board, 100, true);
    	Player harry = client.getPlayer();
    	assertTrue(harry.getColor().contains(Game.COLOR1));
    	assertTrue(harry.getColor().contains(Game.COLOR2));
    	assertEquals(harry.getAvailablePieces().size(), 31);
    	assertTrue(harry.getPiece(Game.COLOR5, Game.SBASE).getType() == Game.SBASE);
    }
    
    /**
     * Check whether creating a player works correctly, 
     * with the right amount of pieces and the right colors in the case that the player has the first turn
     * (and thus has the starting base as well), and it is a ComputerPlayer with NaiveStrategy.
     */
    @Test
    public void testCreateAndGetPlayer4() {
    	client.createPlayer(null, false, false, tui, board, 100, true);
    	Player harry = client.getPlayer();
    	assertTrue(harry.getColor().contains(Game.COLOR1));
    	assertTrue(harry.getColor().contains(Game.COLOR2));
    	assertEquals(harry.getAvailablePieces().size(), 31);
    	assertTrue(harry.getPiece(Game.COLOR5, Game.SBASE).getType() == Game.SBASE);
    	assertTrue(harry instanceof ComputerPlayer);
    }
    
    /**
     * Test whether setting and checking the state of the player works correctly.
     */
    @Test
    public void testState() {
    	assertEquals(client.getPlayerState(), Client.State.CONNECTED);
    	client.setState(Client.State.INGAME);
    	assertEquals(client.getPlayerState(), Client.State.INGAME);
    	client.setState(Client.State.JOINED);
    	assertEquals(client.getPlayerState(), Client.State.JOINED);
    	client.setState(Client.State.CONNECTED);
    	assertEquals(client.getPlayerState(), Client.State.CONNECTED);
    }
    
    /**
     * Test whether the method getColors() returns the right list of colors.
     */
    @Test
    public void testGetColors() {
    	assertTrue(client.getColors().contains(Game.COLOR1));
    	assertTrue(client.getColors().contains(Game.COLOR2));
    }
    
    /**
     * Test setting and getting acknowledgements.
     */
    @Test
    public void testAck() {
    	client.setAck(Client.Acknowledge.CONNECTED);
    	assertEquals(client.getAck(), Client.Acknowledge.CONNECTED);
    }
    
    /**
     * Test disconnecting.
     */
    @Test
    public void testDisconnect() {
    	try {
			client.disconnect();
		} catch (InterruptedException | ServerCommunicationException e) {
			e.printStackTrace();
		}
    	assertTrue(client.getDisconnected());
    }
    
    /**
     * Test joining.
     */
    @Test
    public void testJoin() {
    	try {
			client.join();
		} catch (InterruptedException | ServerCommunicationException | InvalidInputException e) {
			e.printStackTrace();
		}
    	assertEquals(client.getPlayerState(), Client.State.JOINED);
    }
    
    /**
     * Test ready.
     */
    @Test
    public void testReady() {
    	client.setState(Client.State.JOINED);
    	try {
			client.ready();
		} catch (InterruptedException | ServerCommunicationException | InvalidInputException e) {
			e.printStackTrace();
		}
    	assertEquals(client.getPlayerState(), Client.State.INGAME);
    }
    
    /**
     * Test leave.
     */
    @Test
    public void testLeave() {
    	client.setState(Client.State.INGAME);
    	try {
			client.leave();
		} catch (InterruptedException | ServerCommunicationException | InvalidInputException e) {
			e.printStackTrace();
		}
    	assertEquals(client.getPlayerState(), Client.State.CONNECTED);
    }
    
    /**
     * Test make move.
     */
    @Test
    public void testMakeMove() {
    	try {
			client.makeMove("move 1 red 2");
		} catch (InterruptedException | ServerCommunicationException e) {
			e.printStackTrace();
		}
    }
    
    /**
     * Test name.
     */
    @Test
    public void testGetName() {
    	assertEquals(client.getName(),"Harry");
    }
    
    /**
     * Test client receive gameover.
     */
    @Test
    public void testGameOver() {
    	// It is important for this one to press a number, 2 for example
    	client.handleInput("gameover", new TUI(client));
    	assertEquals(client.getPlayerState(),Client.State.CONNECTED);
    }
    
    /**
     * Test client receive multiple colors and the right shared color.
     */
    @Test
    public void testSharedColor() {
//    	client.addColor("purple");
//    	client.addColor("yellow");
    	client.handleInput("color Harry purple yellow", new TUI(client));
    	client.handleInput("color gerrit purple green", new TUI(client));
//    	System.out.println(client.getSharedColor());
    	assertEquals(client.getSharedColor(), "purple");
    }
    
    /**
     * Test whether on start the tui prints the board.
     */
    @Test
    public void testStart() {
    	client.handleInput("start", new TUI(client));
    }
    
    /**
     * Test whether receiving a move actually sets a move on the local board.
     */
    @Test
    public void testReceiveMove() {
    	try {
	    	Board board2 = client.getBoard();
	    	assertTrue(board2.getField(13).testOccupied(new Piece(Game.SBASE, Game.COLOR5)));
    		client.handleInput("move S 13", new TUI(client));
	    	assertFalse(board2.getField(13).testOccupied(new Piece(Game.SBASE, Game.COLOR5)));
	    	assertTrue(board2.getField(12).testOccupied(new Piece(Game.RING1, Game.COLOR1)));
    		client.handleInput("move 1 purple 12", new TUI(client));
	    	assertFalse(board2.getField(12).testOccupied(new Piece(Game.RING1, Game.COLOR1)));
    	} catch (InvalidArgumentContentException e) {
			e.printStackTrace();
		}
    }

}
