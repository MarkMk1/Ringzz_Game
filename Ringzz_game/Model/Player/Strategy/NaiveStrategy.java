package Model.Player.Strategy;

import java.util.*;

import Exceptions.MoveNotPossibleException;
import Exceptions.NoMovePossibleException;
import Exceptions.InvalidArgumentContentException;
import Model.Board;
import Model.Piece;
import Server.Game;

// TODO: Auto-generated Javadoc
/**
 * NaiveStrategy extends the abstract class Strategy, and is used to give a random valid move
 * for a certain board and pieces.
 * @author Ozzypossie
 *
 */
public class NaiveStrategy extends Strategy {
	
	/**
	 * Instantiates a new naive strategy.
	 */
	public NaiveStrategy() {
	}

	/**
	 * Randomly chooses space which has room for randomly chosen piece. 
	 * If there is none, chooses another piece to check for all spaces.
	 *
	 * @param board the board
	 * @param pieces the pieces
	 * @param colors the colors
	 * @param totalTime the total time
	 * @return a string encoding the possible move, null if no move could be found
	 */
	@Override
	public String detMove(Board board, List<Piece> pieces, List<String> colors, int totalTime) {
		long startTime = System.currentTimeMillis();
		if (pieces.isEmpty()) {
			return null;
		}
		// Creating a shuffled list with an index for each piece available
		int[] numberOfPieces = new int[pieces.size()];
		for (int i=0; i<pieces.size(); i++) {
			numberOfPieces[i] = i;
		}
		shuffleArray(numberOfPieces);
		
		// Looping through each available piece
		outerloop:
		for(int pieceIndex : numberOfPieces) {
	        Piece randomPiece = pieces.get(pieceIndex);
//	        System.out.println(randomPiece);
	        
	        // Make a shuffled list of all possible spaces
	        int[] possibleLocations = new int[25];
	        for(int i=0; i<25; i++) {
	        	possibleLocations[i] = i;
	        }
	        shuffleArray(possibleLocations);
	        
	        // Try a random space on the board, if it fails, try the next random position
//	        System.out.println("Random array: " + (Arrays.toString(possibleLocations)));
	        for(int e : possibleLocations) {
//	        	System.out.println(e);
	        	try {
					if (board.testMove(e, randomPiece)) {
//	        		System.out.println("Found a possible move!");
						return "move " + randomPiece.getType() + " " + randomPiece.getColour() + " " + e;
					}
				} catch (InvalidArgumentContentException e1) {
					System.out.println(e1);
				}
	        	if (System.currentTimeMillis() - startTime >= totalTime) {
	        		break outerloop;
	        	}
	        }
	        if (System.currentTimeMillis() - startTime >= totalTime) {
        		break outerloop;
        	}
		}
		return null;
	}
	
	/**
	 * The main method.
	 *
	 * @param args the arguments
	 */
	public static void main(String[] args) {
//		Board board = new Board();
//		List<Piece> pieces = new ArrayList<Piece>();
//		pieces.add(new Piece(Game.RING1, Game.COLOR1));
//		pieces.add(new Piece(Game.RING2, Game.COLOR2));
//		NaiveStrategy strat = new NaiveStrategy();
//		System.out.println(strat.detMove(board, pieces));
	}

	/* (non-Javadoc)
	 * @see Model.Player.Strategy.Strategy#detMove(Model.Board, java.util.List, java.util.List)
	 */
	@Override
	public String detMove(Board board, List<Piece> pieces, List<String> colors) {
		int[] numberOfPieces = new int[pieces.size()];
		for (int i=0; i<pieces.size(); i++) {
			numberOfPieces[i] = i;
		}
		shuffleArray(numberOfPieces);
		
		// Looping through each available piece
		for(int pieceIndex : numberOfPieces) {
	        Piece randomPiece = pieces.get(pieceIndex);
//	        System.out.println(randomPiece);
	        
	        // Make a shuffled list of all possible spaces
	        int[] possibleLocations = new int[25];
	        for(int i=0; i<25; i++) {
	        	possibleLocations[i] = i;
	        }
	        shuffleArray(possibleLocations);
	        
	        // Try a random space on the board, if it fails, try the next random position
//	        System.out.println("Random array: " + (Arrays.toString(possibleLocations)));
	        for(int e : possibleLocations) {
//	        	System.out.println(e);
	        	try {
					if (board.testMove(e, randomPiece)) {
//	        		System.out.println("Found a possible move!");
						return "move " + randomPiece.getType() + " " + randomPiece.getColour() + " " + e;
					}
				} catch (InvalidArgumentContentException e1) {
					// TODO Auto-generated catch block
					System.out.println(e1.getMessage());
				}
	        } 
		}
		return null;
	}
}
