package Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.io.PrintWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import Client.Controller.Client;
import Client.Controller.Player;
import Client.View.TUI;
import Model.Board;
import Model.Piece;
import Model.User;
import Server.Game;
import Server.Server;
import Server.UserIO;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;

// TODO: Auto-generated Javadoc
/**
 * The Class UserTest.
 */
public class UserTest {
	
	/** The user. */
	private User user;
	
	/**
	 * Sets the up.
	 */
	@Before
    public void setUp() {
		user = new User("Harry");
    }
    
    /**
     * Check whether the pieces are initialised correctly.
     */
    @Test
    public void testPieces() {
    	List<Piece> pieces = new ArrayList<>();
    	pieces.add(new Piece(Game.BASE, Game.COLOR1));
    	pieces.add(new Piece(Game.RING1, Game.COLOR2));
    	pieces.add(new Piece(Game.RING3, Game.COLOR3));
    	pieces.add(new Piece(Game.RING4, Game.COLOR3));
    	user.setPieces(pieces);
    	assertEquals(user.getPieces(),pieces);
    }
    
    /**
     * Test whether setting and getting the colors from the user works correctly.
     */
    @Test
    public void testColor() {
    	List<String> colors = new ArrayList<>();
    	colors.add(Game.COLOR1);
    	colors.add(Game.COLOR2);
    	user.setColor(colors);
    	assertEquals(user.getColor(),colors);
    }
    
    /**
     * Test whether setting and getting the states works correctly.
     */
    @Test
    public void testStates() {
    	assertTrue(user.isNone());
    	user.setReady();
    	assertTrue(user.isReady());
    	user.setJoined();
    	assertTrue(user.isJoined());
    	user.setLeft();
    	assertTrue(user.isLeft());
    }
    
    /**
     * Test getting the name of User.
     */
    @Test
    public void testName() {
    	assertTrue(user.getName().equals("Harry"));
    }
    
    /**
     * Test whether setting and getting the state of playing works.
     */
    @Test
    public void testPlaying() {
    	user.setLeft();
    	assertFalse(user.isPlaying());
    	user.setPlaying();
    	assertTrue(user.isPlaying());
    }
    
    
    
    /**
     * Test method checkPiece().
     */
    @Test
    public void testCheckPiece() {
    	List<Piece> pieces = new ArrayList<>();
    	pieces.add(new Piece(Game.RING1, Game.COLOR1));
    	user.setPieces(pieces);
    	assertTrue(user.checkPiece(Game.COLOR1, Game.RING1) != -1);
    	assertTrue(user.checkPiece(Game.COLOR2, Game.RING1) == -1);
    }
}
