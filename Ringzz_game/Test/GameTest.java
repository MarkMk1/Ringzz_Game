package Test;

import org.junit.Before;
import org.junit.Test;

import Exceptions.InvalidInputException;
import Exceptions.InvalidPlayerCountException;
import Model.Piece;
import Model.User;
import Server.Game;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Observable;
import java.util.Observer;

// TODO: Auto-generated Javadoc
/**
 * The Class GameTest.
 */
public class GameTest {
	
	/** The users 4. */
	private List<User> users2, users3, users4;
	
	/** The user 4. */
	private User user1, user2, user3, user4;
	
	/** The game 4. */
	private Game game2, game3, game4;
	
	/**
	 * The Class ObserverTest.
	 */
	class ObserverTest implements Observer {

		/* (non-Javadoc)
		 * @see java.util.Observer#update(java.util.Observable, java.lang.Object)
		 */
		public void update(Observable arg0, Object arg1) {
			String arg = ((String) arg1);
			List<String> argArray = Arrays.asList(arg.split("[\\s']"));
			switch (argArray.get(0)) {	
			case "color":
				break;
			case "score":
				break;
			case "move":
				break;
			case "gameover":
				break;
			default:
				break;
			}

		}
	}
	
	/**
	 * Sets the up.
	 */
	@Before
    public void setUp() {
		user1 = new User("Harry");
		user2 = new User("Oskar");
		user3 = new User("Mark");
		user4 = new User("Raquel");
		users2 = new ArrayList<>();
		users3 = new ArrayList<>();
		users4 = new ArrayList<>();

		users2.add(user1);
		users2.add(user2);

		users3.add(user1);
		users3.add(user2);
		users3.add(user3);

		users4.add(user1);
		users4.add(user2);
		users4.add(user3);
		users4.add(user4);

		ObserverTest Observer = new ObserverTest();
			
		
		try {
			game2 = new Game(users2);
			game2.addObserver(Observer);
			game3 = new Game(users3);
			game3.addObserver(Observer);
			game4 = new Game(users4);
			game4.addObserver(Observer);
		} catch (InvalidPlayerCountException e) {
			System.out.println(e.getMessage() + " InvalidPlayerCountExceptionx");
		}
	}
	
	/**
	 * For the purpose of testing, variables were set to public. 
	 */
	@Test
	public void testMoveColorRecognition() {
		game2.setCurrentColor(Arrays.asList("move S all 14".split("[\\s']")));
		assertTrue(game2.currentColor.equals("all"));
		game2.setCurrentColor(Arrays.asList("move B green 21".split("[\\s']")));
		assertTrue(game2.currentColor.equals("green"));
		game2.setCurrentColor(Arrays.asList("move 4 purple 12".split("[\\s']")));
		assertTrue(game2.currentColor.equals("purple"));
		game2.setCurrentColor(Arrays.asList("move 2 yellow 6".split("[\\s']")));
		assertTrue(game2.currentColor.equals("yellow"));
		game2.setCurrentColor(Arrays.asList("move 4 grey 3".split("[\\s']")));
		//Should not be set, as grey is invalid. Thus, old setting should remain.
		assertTrue(game2.currentColor.equals("yellow"));
	}
	
	/**
	 * Test move ring recognition.
	 */
	@Test
	public void testMoveRingRecognition() {
		game2.setCurrentRing(Arrays.asList("move S all 14".split("[\\s']")));
		assertTrue(game2.currentRing == 'S');
		game2.setCurrentRing(Arrays.asList("move B red 21".split("[\\s']")));
		assertTrue(game2.currentRing == ('B'));
		game2.setCurrentRing(Arrays.asList("move 4 purple 12".split("[\\s']")));
		assertTrue(game2.currentRing == ('4'));
		game2.setCurrentRing(Arrays.asList("move 2 yellow 6".split("[\\s']")));
		assertTrue(game2.currentRing == ('2'));
		game2.setCurrentRing(Arrays.asList("move -1 grey 3".split("[\\s']")));
		//Should not be set, as -1 is invalid. Thus, old setting should remain.
		assertTrue(game2.currentRing == ('2'));
	}
	
	/**
	 * Test move position recognition.
	 */
	@Test
	public void testMovePositionRecognition() {
		game2.currentPosition = 0;
		game2.setCurrentPosition(Arrays.asList("move S all 14".split("[\\s']")));
		assertTrue(game2.currentPosition == 14);
		game2.setCurrentPosition(Arrays.asList("move B red 21".split("[\\s']")));
		assertTrue(game2.currentPosition == 21);
		game2.setCurrentPosition(Arrays.asList("move 4 purple 12".split("[\\s']")));
		assertTrue(game2.currentPosition == 12);
		game2.setCurrentPosition(Arrays.asList("move 2 yellow 6".split("[\\s']")));
		assertTrue(game2.currentPosition == 6);
		game2.setCurrentPosition(Arrays.asList("move -1 grey 99".split("[\\s']")));
		//Should not be set, as grey is invalid. Thus, old setting should remain.
//		assertTrue(game2.currentPosition == 12);	
	}
	
	/**
     * Test whether users get the right amount of pieces and colours in the case of 2 players.
     */
    @Test
    public void testPiecesTwoPlayer() {
  	
    	try {
			game2.divideColors();
		} catch (InvalidPlayerCountException e) {
			System.out.println("InvalidPlayerCountException");
			fail();
		}
    	assertTrue(user1.getColor().contains(Game.COLOR1));
    	assertTrue(user1.getColor().contains(Game.COLOR2));
    	assertTrue(user2.getColor().contains(Game.COLOR3));
    	assertTrue(user2.getColor().contains(Game.COLOR4));
    	//As user1 has starting base;
    	assertEquals(user1.getPieces().size(),31);
    	assertEquals(user2.getPieces().size(),30);
    }
    
    /**
     * Test whether users get the right list of pieces and colours in the case of 3 players.
     */
    @Test
    public void testPiecesThreePlayer() {

    	try {
			game3.divideColors();
		} catch (InvalidPlayerCountException e) {
			System.out.println("InvalidPlayerCountException");
			fail();
		}
    	
    	assertTrue(user1.getColor().contains(Game.COLOR1));
    	assertTrue(user1.getColor().contains(Game.COLOR2));
    	assertTrue(user2.getColor().contains(Game.COLOR3));
    	assertTrue(user2.getColor().contains(Game.COLOR2));
    	assertTrue(user3.getColor().contains(Game.COLOR4));
    	assertTrue(user3.getColor().contains(Game.COLOR2));
    	assertEquals(user1.getPieces().size(),21);
    	assertEquals(user2.getPieces().size(),20);
    	assertEquals(user3.getPieces().size(),20);
    }
    
    /**
     * Test whether users get the right list of pieces and colours in the case of 4 players.
     */
    @Test
    public void testPiecesFourPlayer() {

    	try {
			game4.divideColors();
		} catch (InvalidPlayerCountException e) {
			System.out.println("InvalidPlayerCountException");
			fail();
		}
    	assertTrue(user1.getColor().contains(Game.COLOR1));
    	assertTrue(user2.getColor().contains(Game.COLOR2));
    	assertTrue(user3.getColor().contains(Game.COLOR3));
    	assertTrue(user4.getColor().contains(Game.COLOR4));
    	assertEquals(user1.getPieces().size(),16);
    	assertEquals(user2.getPieces().size(),15);
    	assertEquals(user3.getPieces().size(),15);
    	assertEquals(user4.getPieces().size(),15);
    }
    
    /**
     * Test whether the method getPieces() gives the right pieces.
     */
    
    public void testGetPiecesTwo() {
		// Creating list of users with 2 players and a game with these players
    	

    	user1.setColor(Game.colors.subList(0, 2));
    	user2.setColor(Game.colors.subList(2, 4));
    	List<Piece> pieces1 = game2.getPieces(user1);
    	List<Piece> pieces2 = game2.getPieces(user2, Game.COLOR4);
    	
    	// Testing two pieces for user1
    	boolean hasPiece1 = false;
    	boolean hasPiece2 = false;
    	for (Piece p : pieces1) {
//    		System.out.println(p.getColour() + " " + p.getType());
    		if(p.getColour().equals(Game.COLOR1) && p.getType() == '1') {
    			hasPiece1 = true;
    		}
    		if(p.getColour().equals(Game.COLOR2) && p.getType() == 'B') {
    			hasPiece2 = true;
    		}
    	}
    	assertTrue(hasPiece1);
    	assertTrue(hasPiece2);
    	
    	// Testing two pieces for Oscar
    	hasPiece1 = false;
    	hasPiece2 = false;
    	for (Piece p : pieces2) {
    		if(p.getColour().equals(Game.COLOR3) && p.getType() == 'B') {
    			hasPiece1 = true;
    		}
    		if(p.getColour().equals(Game.COLOR4) && p.getType() == '2') {
    			hasPiece2 = true;
    		}
    	}
    	assertTrue(hasPiece1);
    	assertTrue(hasPiece2);
    }
}
