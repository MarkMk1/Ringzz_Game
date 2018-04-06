package Model;

import java.util.ArrayList;
import java.util.List;

import Client.Controller.Client;
import Server.UserIO;

// TODO: Auto-generated Javadoc
/**
 * This class is a way for the server and the game to represent the different players. 
 * With the User object the state of the player can be checked 
 * (i.e. whether the player has joined a game, left a game, is ready, or is in none yet). 
 * Each User object has its own Socket and UserIO, 
 * which is used to communicate with the client of the player. 
 * The User object is also used for bookkeeping the pieces and colors.
 * @author Oskar
 */

public class User {
	
	/**
	 * Describes the various states the users can be in.
	 */
	public enum State {
		
		/** The none. */
		NONE, 
 /** The ready. */
 READY, 
 /** The joined. */
 JOINED, 
 /** The left. */
 LEFT, 
 /** The ingame. */
 INGAME;
	}
	
	/** The name. */
	private String name;
	
	/** The colors. */
	private List<String> colors = new ArrayList<>();
	
	/** The pieces. */
	private List<Piece> pieces = new ArrayList<>();
	
	/** The state. */
	private State state;
	
	/** The user IO. */
	private UserIO userIO;
	
	/** The bot. */
	private boolean bot;
	
	// --------------- Constructor ------------
	
	/**
	 * Instantiates a new user.
	 *
	 * @param name the name
	 */
	public User(String name) {
		this.name = name;
		this.state = State.NONE;
		this.bot = false;
	}
	
	/**
	 * Instantiates a new user.
	 *
	 * @param name the name
	 * @param bot the bot
	 */
	public User(String name, boolean bot) {
		this.name = name;
		this.bot = bot;
	}
	
	// ------------- Commands ----------------
	

	/**
	 * Clean.
	 */
	public void clean() {
		this.colors.clear();
		this.pieces.clear();
		this.setNone();
	}
	
	/**
	 * Set the pieces of the user.
	 *
	 * @param pieces the pieces the user should own
	 */
	public void setPieces(List<Piece> pieces) {
		this.pieces = pieces;
	}
	
	// TODO: should modify the list with pieces if a piece is used by the game
	/**
	 * Set the colors owned by the user.
	 *
	 * @param colors of the user
	 */
	public void setColor(List<String> colors) {
		this.colors = colors;
	}
	
	/**
	 * Set the state of the user to NONE (i.e. not in a game and not left)
	 */
	public void setNone() {
		state = State.NONE;
	}
	
	/**
	 * Set the state of the user to LEFT (when left a game).
	 */
	public void setLeft() {
		state = State.LEFT;
	}
	
	/**
	 * Set the state of the user to JOINED (when joined a game).
	 */
	public void setJoined() {
		state = State.JOINED;
	}
	
	/**
	 * Set the state of the user to READY (when ready to play a game).
	 */
	public void setReady() {
		state = State.READY;
	}
	
	/**
	 * Set the state of the user to INGAME (when playing a game).
	 */
	public void setPlaying() {
		state = State.INGAME;
	}
	
	/**
	 * Set the userIO to be used for communicating with the client of this player.
	 *
	 * @param userIO userIO for this user
	 */
	public void setUserIO(UserIO userIO) {
		this.userIO = userIO;
	}
	
	// ------------- Queries ---------
	
	
	/**
	 * Checks if is bot.
	 *
	 * @return true, if is bot
	 */
	public boolean isBot() {
//		return this.getUserIO().checkConnection();
		return false;
	}
	
	/**
	 * Get the colors of the user.
	 *
	 * @return the color
	 * @)return list of colors
	 */
	public List<String> getColor() {
		return this.colors;
	}
	
	/**
	 * Get the pieces from the user.
	 *
	 * @return the pieces
	 */
	public List<Piece> getPieces() {
		return this.pieces;
	}
	
	/**
	 * Get the name of the user.
	 *
	 * @return the name as a String
	 */
	public String getName() {
		return this.name;
	}
	
	/**
	 * Check whether the user is in the NONE state.
	 *
	 * @return true if the user is in the NONE state
	 */
	public boolean isNone() {
		return state == State.NONE;
	}
	
	/**
	 * Check whether the user is in the LEFT state.
	 *
	 * @return true if the user has left a game
	 */
	public boolean isLeft() {
		return state == State.LEFT;
	}
	
	/**
	 * Check whether the user is in the JOINED state.
	 *
	 * @return true if the user has joined a game
	 */
	public boolean isJoined() {
		return state == State.JOINED;
	}

	/**
	 * Check whether the user is in the READY state.
	 *
	 * @return true if the user is ready to play a game
	 */
	public boolean isReady() {
		return state == State.READY;
	}
	
	/**
	 * Check at what index the piece with the given colour and ring type is in the list of pieces.
	 *
	 * @param colour the colour of the piece
	 * @param type the ringtype of the piece
	 * @return the index in the list of pieces where the piece is, -1 if the list does not contain the piece
	 */
	public int checkPiece(String colour, char type) {
		int location = -1;
		for (Piece p : this.getPieces()) {
			location ++;
			if (p.getColour().equals(colour)) {
				if (p.getType() == type) {
					return location;
				}
			}
		}
		return -1;
	}

	/**
	 * Query to check whether the user is playing a game.
	 *
	 * @return true if he is playing a game
	 */
	public boolean isPlaying() {
		return state == State.INGAME;
	}
	
	/**
	 * Query to get userIO of this user.
	 *
	 * @return the userIO of this user
	 */
	public UserIO getUserIO() {
		return this.userIO;
	}

	/**
	 * Console out.
	 *
	 * @param string the string
	 */
	public void consoleOut(String string) {
		System.out.println(string);
	}

	/**
	 * Sets the bot.
	 */
	public void setBot() {
		this.bot = true;
	}
}
