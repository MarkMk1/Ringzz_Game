package Client.Controller;
import Model.*;
import Model.Player.Strategy.NaiveStrategy;
//import Model.Player.Strategy.Smart.SmartStrategy;
import Model.Player.Strategy.SmartStrategy;
import Model.Player.Strategy.Strategy;
import Server.Game;

import java.util.List;

import Client.View.*;
import Exceptions.*;
// TODO: Auto-generated Javadoc
/**
 * This class extends the abstract class Player.
 * HumanPlayer asks for input from the user via the TUI when a move has to be made.
 * A hint can also be asked when it is the turn of the player.
 * @author Oskar
 */
public class HumanPlayer extends Player {
	
	/**
	 * The User Interface used by the human player.
	 */
	private TUI tui;

	/**
	 * Constructs a new <code>HumanPlayer</code> with a name, board and colors of the rings.
	 *
	 * @param name Name of the player.
	 * @param colors Colors of the rings of the player.
	 * @param board Board the player is playing on.
	 * @param pieces A list of all the pieces the player has.
	 * @param client client which is informed about the successful move made
	 * @param tui The User Interface used by the <code>HumanPlayer</code>.
	 * @param totalTime the total time
	 */
	public HumanPlayer(String name, List<String> colors, Board board, List<Piece> pieces, Client client, TUI tui, int totalTime) { 
		super(name, colors, board, pieces, client, totalTime);
		this.tui = tui;
	}

	/**
	 * Returns suggested move as given by <code>strategy</code>'s determineMove().
	 *
	 * @param smart true if the player has selected the SmartStrategy, otherwise using the NaiveStrategy
	 * @param readMove true if it is the player's turn
	 * @return a String encoding the move.
	 * @throws InvalidInputException if the input if the player cannot ask for a hint (it is not his or her turn)
	 * @throws NoMovePossibleException if the strategy cannot find a possible move
	 */
	@Override
	public String hint(boolean smart, boolean readMove) throws InvalidInputException, NoMovePossibleException {
		if (client.getPlayerState() != Client.State.INGAME) {
			throw new InvalidInputException("Sorry, you are not in a game now");
		} else if (!readMove) {
			throw new InvalidInputException("It is not your turn");
		}
		Strategy strat;
		if (smart) {
			strat = new SmartStrategy();
		} else {
			strat = new NaiveStrategy();
		}
		String result = strat.detMove(board, pieces, colors);
		if (result.equals(null)) {
			throw new NoMovePossibleException("No valid move could be found");
		} else {
			return result;
		}
	}

	/**
	 * Places a ring or base on a specific position on the board. Makes use of the TUI to ask the user for input.
	 *
	 * @throws ServerCommunicationException the server communication exception
	 * @throws InterruptedException the interrupted exception
	 * @throws MoveNotPossibleException the move not possible exception
	 * @throws InvalidInputException the invalid input exception
	 */
	@Override
	public void setMove() throws ServerCommunicationException, InterruptedException, MoveNotPossibleException, InvalidInputException {
		int position = -1;
		String color = null;
		char ringtype = ' ';
		Piece piece = null;
		String move = null;
		while(!checkColor(color) || piece == null) {
			move = tui.readMove();
			if (move.equals("quit")) {
				return;
			}
//			System.out.println("hey: " + move);
			String[] words = move.split("[\\s']");
			color = words[2];
			try {
				position = Integer.parseInt(words[3]); 
			} catch (NumberFormatException e) {
				throw new InvalidInputException("The position should be an integer");
			}
			ringtype = words[1].charAt(0);
			if(!checkColor(color)) {
				throw new MoveNotPossibleException("You do not own that color, please choose one of your own.");
			}
			piece = getPiece(color, ringtype);
			if(piece == null) {
				throw new MoveNotPossibleException("You do not have that piece anymore, please place another piece.");
			}
		}
		if(board.setField(position, piece)) {
			pieces.remove(piece);
			if (piece.getType() == Game.SBASE) {
				client.makeMove("move " + Game.SBASE + " " + Game.COLOR1 + " " + position);
			} else {
				client.makeMove(move);
			}
		} else {
			throw new MoveNotPossibleException("This move is not possible, please try again.");
		}
	}
	
	/**
	 * This method checks whether the player owns this color.
	 * @param color Color to check.
	 * @return true if the player owns this color.
	 */
	public boolean checkColor(String color) {
		if (color == null) {
			return false;
		} else if (color.equals(Game.COLOR5)) {
			return true;
		} else {
			return this.colors.contains(color);
		}
	}
}