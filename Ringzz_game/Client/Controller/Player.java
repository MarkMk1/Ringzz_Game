package Client.Controller;

import java.util.List;

import Exceptions.InvalidInputException;
import Exceptions.MoveNotPossibleException;
import Exceptions.NoMovePossibleException;
import Exceptions.ServerCommunicationException;
import Model.*;
// TODO: Auto-generated Javadoc
/**
 * Player is an abstract class and HumanPlayer and ComputerPlayer are subclasses 
 * of Player. Each Player object has a name, a board, 
 * a list of colors of the player, a list of pieces and a client. 
 * The Player object is used to set moves on the board and informs the Client 
 * about the respective move. A ComputerPlayer object uses a Strategy to determine 
 * the next move, while a HumanPlayer object asks the user of the program for a move 
 * via the User Interface. 
 * A Player object checks if the move is possible and throws an exception otherwise. 
 * A HumanPlayer object can also give a hint move, given by the selected Strategy.
 * 
 * @author Oskar
 *
 */
public abstract class Player {
	
	/** The colors. */
	protected List<String> colors;
	
	/** The name. */
	private String name; 
	
	/** The board. */
	protected Board board;
	
	/** The pieces. */
	protected List<Piece> pieces;
	
	/** The client. */
	protected Client client;
	
	/** The total time. */
	protected int totalTime;
	

	/**
	 * Constructs a new Player object.
	 *
	 * @param name name of the Player
	 * @param colors colors owned by the Player
	 * @param board board the Player is playing on
	 * @param pieces a list of pieces owned by the Player
	 * @param client the client which created this Player object
	 * @param totalTime the total time
	 */
	public Player(String name, List<String> colors, Board board, List<Piece> pieces, Client client, int totalTime) {
		this.name = name;
		this.board = board;
		this.colors = colors;
		this.pieces = pieces;
		this.client = client;
		this.totalTime = totalTime;
	}
	
	/**
	 * Method to return a hint to the user.
	 * @param smart boolean to indicate whether the Strategy should be a SmartStrategy or not
	 * @param readMove boolean to indicate whether it is the turn of the Player
	 * @return a String describing a possible move.
	 * @throws InvalidInputException if is not possible to ask for a hint now
	 * @throws NoMovePossibleException if no valid move could be given by the Strategy
	 */
	public abstract String hint(boolean smart, boolean readMove) throws InvalidInputException, NoMovePossibleException;
	
	/**
	 * The Player object sets a move on the board and informs the client about it.
	 *
	 * @throws ServerCommunicationException the server communication exception
	 * @throws InterruptedException the interrupted exception
	 * @throws MoveNotPossibleException the move not possible exception
	 * @throws NoMovePossibleException the no move possible exception
	 * @throws InvalidInputException the invalid input exception
	 */
	public abstract void setMove() throws ServerCommunicationException, InterruptedException, MoveNotPossibleException, NoMovePossibleException, InvalidInputException;
	
	/**
	 * Returns the name of the player.
	 *
	 * @return string the name
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * Returns a list of colors owned by the Player.
	 *
	 * @return list of colors
	 */
	public List<String> getColor() {
		return colors;
	}
	
	/**
	 * This method returns a list with all the available pieces to the player.
	 * @return a list with all the available pieces.
	 */
	public List<Piece> getAvailablePieces() {
		return this.pieces;
	}
	
	/**
	 * This method is used to return a specific piece, based on the user input.
	 * @param color Color of the piece.
	 * @param type  Type of the piece.
	 * @return the piece the user requested, null when the piece is not available.
	 */
	public Piece getPiece(String color, char type) {
		for (Piece e : pieces) {
			if (color.equals(e.getColour()) && type == e.getType()) {
				return e;
			}
		}
		return null;
	}
	
	/**
	 * This method is used to print the pieces the player owns to the client.
	 *
	 * @return the string
	 */
	public String printPieces() {
		String result = "";
		for (Piece p : pieces) {
			result = result + " | " + p.toString();
		}
		return result;
	}
}
