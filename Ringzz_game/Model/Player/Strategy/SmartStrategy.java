package Model.Player.Strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import Exceptions.InvalidArgumentContentException;
import Exceptions.NoMovePossibleException;
import Model.Board;
import Model.Field;
import Model.Piece;
import Server.Game;
// TODO: Auto-generated Javadoc
/**
 * A class implementing the Strategy interface should have a method to determine a move on the board with the given pieces. 
 * SmartStrategy has some algorithm to determine which moves are better than others. 
 * For example, if a base can be places, this is always done. 
 * If not, then placing pieces which occupy a field is given priority, then playing even in a field, 
 * and then the rest of the moves.
 * @author Oskar
 */
public class SmartStrategy extends Strategy {
	
	/**
	 * This method determines the score for putting the piece on this field.
	 *
	 * @param field the field to check the move on
	 * @param piece the piece we want to put on this field
	 * @return 2 if we would occupy the field with this move, 1 if we would play even, 0 else
	 */
	public int testWin(Field field, Piece piece) {
		List<Character> ringtypes = Game.ringTypes;
		ringtypes.remove(piece.getType());
		int rings = 0;
		List<String> colors = Game.colors;
		for (String c : colors) {
			if (!field.testColour(c)) {
				colors.remove(c);
			}
		}
		// No one occupies the field yet
		if (colors.size() == 0) {
			return 3;
		}
		Piece p;
		for (char t : ringtypes) {
			p = new Piece(t, Game.COLOR1);
			if (field.testOccupied(p)) {
				rings++;
			}
		}
		/*
		 *  Check if the number of rings and owners is the same;
		 *  If so, and we own one of these rings, we get 2 points (because we then occupy the field)
		 *  If we do not own one of these rings, we get 1 point (because we play even)
		 */
		if (rings/colors.size() == 1) {
			if (colors.contains(field.testOwner())) { // If we own the field, give it a low score!
				return 0;
			} else if (colors.contains(piece.getColour())) {
				return 2;
			} else {
				return 1;
			}
		} else {
			return 0;
		}
	}
	
	/**
	 * Method for determining the next move given the board, list of pieces and given 'smart' strategy.
	 * Runs approximately for <code>totalTime</code> milliseconds
	 *
	 * @param board we play on
	 * @param pieces list of pieces the player can use
	 * @param colors list of colors the player owns, is used to determine which fields the player already owns
	 * @param totalTime milliseconds the method is approximately allowed to run
	 * @return the string
	 * @returns a valid move encoded in a String, null if no move could be found
	 */
	@Override
	public String detMove(Board board, List<Piece> pieces, List<String> colors, int totalTime) {
		long startTime = System.currentTimeMillis();
		
		if (pieces.isEmpty()) {
			return null;
		}
		
		
		boolean firstMove = true;
		int score = 0; // play losing = 0, play even = 1, win field = 2, set base = 3
		int location = -1;
		Piece piece = null;
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
//			        System.out.println(randomPiece);
	        
	        // Make a shuffled list of all possible spaces
	        int[] possibleLocations = new int[25];
	        for(int i=0; i<25; i++) {
	        	possibleLocations[i] = i;
	        }
	        shuffleArray(possibleLocations);
	        
	        // Try a random space on the board, if it fails, try the next random position
//			        System.out.println("Random array: " + (Arrays.toString(possibleLocations)));
	        for(int e : possibleLocations) {
//			        	System.out.println(e);
	        	try {
					if (board.testMove(e, randomPiece)) {
//			        		System.out.println("Found a possible move!");
						if (!firstMove) {
							if (randomPiece.getType() == Game.SBASE) {
								piece = randomPiece;
								location = e;
								break outerloop;
							} else if (randomPiece.getType() == Game.BASE) {
								piece = randomPiece;
								location = e;
								break outerloop;
							} else if (score == 2 ) {
								continue;
							} else if (testWin(board.getField(e), randomPiece) > score) {
								score = testWin(board.getField(e), randomPiece);
								piece = randomPiece;
					    		location = e;
							}
							continue;
						}
						piece = randomPiece;
						location = e;
						break outerloop;
					}
				} catch (InvalidArgumentContentException e1) {
					System.out.println(e1.getMessage() + " - Smart Strategy detMove");
				}
	        	if (System.currentTimeMillis() - startTime >= totalTime) {
	        		break outerloop;
	        	}
	        }
	        if (System.currentTimeMillis() - startTime >= totalTime) {
	        	break outerloop;
	        }
		}
		if (location == -1) {
			return (new NaiveStrategy().detMove(board, pieces, colors));
		}
		return "move " + piece.getType() + " " + piece.getColour() + " " + location;
	}
	
	/**
	 * Method for determining the next move given the board, list of pieces and given 'smart' strategy.
	 *
	 * @param board we play on
	 * @param pieces list of pieces the player can use
	 * @param colors list of colors the player owns, is used to determine which fields the player already owns
	 * @return the string
	 * @returns a valid move encoded in a String, null if no move could be found
	 */
	@Override
	public String detMove(Board board, List<Piece> pieces, List<String> colors) {
		if (pieces.isEmpty()) {
			return null;
		}
		
		
		boolean firstMove = true;
		int score = 0; // play losing = 0, play even = 1, win field = 2, set base = 3
		int location = -1;
		Piece piece = null;
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
//			        System.out.println(randomPiece);
	        
	        // Make a shuffled list of all possible spaces
	        int[] possibleLocations = new int[25];
	        for(int i=0; i<25; i++) {
	        	possibleLocations[i] = i;
	        }
	        shuffleArray(possibleLocations);
	        
	        // Try a random space on the board, if it fails, try the next random position
//			        System.out.println("Random array: " + (Arrays.toString(possibleLocations)));
	        for(int e : possibleLocations) {
//			        	System.out.println(e);
	        	try {
					if (board.testMove(e, randomPiece)) {
//			        		System.out.println("Found a possible move!");
						if (!firstMove) {
							if (randomPiece.getType() == Game.BASE) {
								piece = randomPiece;
								location = e;
								break outerloop;
							} else if (score == 2 ) {
								continue;
							} else if (testWin(board.getField(e), randomPiece) > score) {
								score = testWin(board.getField(e), randomPiece);
								piece = randomPiece;
					    		location = e;
							}
							continue;
						}
						piece = randomPiece;
						location = e;
						break outerloop;
					}
				} catch (InvalidArgumentContentException e1) {
					System.out.println(e1.getMessage() + " - Smartstrategy's testMove");
				}
	        } 
		}
		if (location == -1) {
			return (new NaiveStrategy().detMove(board, pieces, colors));
		}
		return "move " + piece.getType() + " " + piece.getColour() + " " + location;
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
//		SmartStrategy strat = new SmartStrategy();
//		System.out.println(strat.detMove(board, pieces));
	}
}
