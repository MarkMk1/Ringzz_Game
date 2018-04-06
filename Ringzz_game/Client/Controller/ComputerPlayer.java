package Client.Controller;

import java.util.List;

import Exceptions.InvalidInputException;
import Exceptions.MoveNotPossibleException;
import Exceptions.NoMovePossibleException;
import Exceptions.ServerCommunicationException;
import Model.Board;
import Model.Piece;
import Model.Player.Strategy.*;
import Server.Game;

// TODO: Auto-generated Javadoc
/**
 * This class extends the abstract class Player. Instead of a human player,
 * a Strategy object is used to determine a move on the given board
 * for the given pieces.
 * @author Oskar
 */

public class ComputerPlayer extends Player {
	
	/**
	 * The strategy implemented by the ComputerPlayer.
	 */
	private Strategy strat;
	
	/** The total time. */
	private int totalTime;
	
	/**
	 * Constructs a new <code>ComputerPlayer</code> with a <code>name</code>, <code>board</code>, <code>colors</code> of the rings, 
	 * and a <code>strategy</code>.
	 *
	 * @param name Name of the player.
	 * @param colors Colors of the rings of the player.
	 * @param board Board the player is playing on.
	 * @param pieces A list of all the pieces the player has.
	 * @param client the client to which this player is connected
	 * @param strat Strategy implemented, allowing for AI of varying power.
	 * @param totalTime the total time
	 */
	public ComputerPlayer(String name, List<String> colors, Board board, List<Piece> pieces, Client client, Strategy strat, int totalTime) {
		super(name, colors, board, pieces, client, totalTime);
		this.strat = strat;
	}

	/**
	 * Places a ring or base on a specific position on the board. Makes use of the strategy to determine its move.
	 *
	 * @throws ServerCommunicationException the server communication exception
	 * @throws InterruptedException the interrupted exception
	 * @throws NoMovePossibleException the no move possible exception
	 * @throws MoveNotPossibleException the move not possible exception
	 */
	@Override
	public void setMove() throws ServerCommunicationException, InterruptedException, NoMovePossibleException, MoveNotPossibleException {
		String move = strat.detMove(board, pieces, colors);
		System.out.println("we've got a move: " + move);
		if (move == null) {
			throw new NoMovePossibleException("No valid move could be found.");
		}
		String[] words = move.split("[\\s']");
		String color = words[2];
		int position = -1;
		char ringtype = ' ';
		Piece piece = null;
		try {
			position = Integer.parseInt(words[3]); 
		} catch (NumberFormatException e) {
			throw new MoveNotPossibleException("The position should be an integer");
		}
		ringtype = words[1].charAt(0);
		piece = getPiece(color, ringtype);
		if(piece == null) {
			throw new MoveNotPossibleException("You do not have that piece anymore, please place another piece.");
		}
		
		if(board.setField(position, piece)) {
			pieces.remove(piece);
			if (piece.getType() == Game.SBASE) {
				client.makeMove("move " + Game.SBASE + " " + Game.COLOR1 + " " + position);
			} else {
				System.out.println("move : " + move);
				client.makeMove(move);
			}
		} else {
			throw new MoveNotPossibleException("This move is not possible, please try again.");
		}
	}
	
	/**
	 * Returns the strategy used by the <code>ComputerPlayer</code>.
	 * @return the strategy used.
	 */
	public Strategy getStrategy() {
		return this.strat;
	}

	/**
	 * When asking for a hint when a ComputerPlayer is playing, throw an InvalidInputException.
	 *
	 * @param smart the smart
	 * @param readMove the read move
	 * @return the string
	 * @throws InvalidInputException the invalid input exception
	 */
	@Override
	public String hint(boolean smart, boolean readMove) throws InvalidInputException {
		throw new InvalidInputException("You cannot ask for a hint, the computer is playing");
	}
}
