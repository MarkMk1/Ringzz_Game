package Model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import Exceptions.InvalidArgumentContentException;
import Exceptions.InvalidInputException;
import Exceptions.NoMovePossibleException;
import Model.Player.Strategy.NaiveStrategy;
import Server.Game;
 
// TODO: Auto-generated Javadoc
/**
 * Class responsible for modelling the board. 
 * Can also be responsible for pieces, once number of players is passed. 
 * In this way, it can also tell if a game over condition has been met. 
 * @author Mark
 *
 */

public class Board {

//	private static final String[] NUMBERING = {" 0 | 1 | 2 | 3 | 4 ", "---+---+---",
//	        								   " 5 | 6 | 7 | 8 | 9  ", "---+---+---", 
//	        								   " 10 | 11 | 12 | 13 | 14 ", "---+---+---",
//	        								   " 15 | 16 | 17 | 18 | 19 ", "---+---+---", 
/** The Constant NEW_LINE_DELIM. */
//	        								   " 20 | 21 | 22 | 23 | 24 "};
	private static final String NEW_LINE_DELIM = new String(new char[45]).replace("\0", "=");
	
	/** The Constant VALID_START_FIELDS. */
	/*@ invariant VALID_START_FIELDS != null; */
	public static final List<Integer> VALID_START_FIELDS = new ArrayList<>(Arrays.asList(6,
			7, 8, 11, 12, 13, 14, 16, 17, 18));

	/** array representing fields for the board. */
	private Field[] fields;
	/** int storing the set position of the starting base. */
	private int sBasePos = 0;

	/**
	 * Constructor for the Board. Initialises all fields
	 * for the board as empty.
	 */
	//@ ensures fields.length() == 25;
	public Board() {
		fields = new Field[25];
		for (int i = 0; i <= 24; i++) {
			fields[i] = new Field();
		}
	}
	
	/**
	 * Gets field as specific position.
	 * @param position int from 0 to 24.
	 * @return Field from fields[position]
	 * @throws InvalidArgumentContentException if position is out of range.
	 */
	//@ requires position >= 0 && position <= 24;
	//@ ensures \result.toString().equals(fields[position].toString());
	public Field getField(int position) throws InvalidArgumentContentException {
		if ((position >= 0) && (position <= 24)) {
			return fields[position];
		}
		throw new InvalidArgumentContentException("Position not present on board");
	}
	
	/**
	 * Sets initial base position, allowing ease of access. 
	 * Prevents need for looping through fields. 
	 * @param position int between 0 and 24, though should only be
	 * within range valid for starting base, VALID_START_FIELDS
	 * @throws InvalidInputException if input violates precondition.
	 */
	//@ requires position <= 24 && position >= 0;
	//@ ensures sBasePos == position;
	public void setInitialBasePosition(int position) throws InvalidInputException {
		if (position > -1 && position < 25) {
			this.sBasePos = position;
		} else {
			throw new InvalidInputException("Starting base"
				+ "must be in middle nine spaces");
			}
	}
	
	/**
	 * Gets base position, as set by setInitialBasePosition().
	 * @return int that's member of VALID_START_FIELDS.
	 */
	//@ ensures \result == sBasePos;
	public int getInitialBasePosition() {
		return this.sBasePos;
	}
	
	/**
	 * Sets field, using int specifying position, and game piece.
	 * First tests the move to check validity.
	 *
	 * @param position the position
	 * @param piece the piece
	 * @return boolean stating whether or not the field was set.
	 */
	//@ requires position <= 24 && position >= 0;
	//@ ensures testMove(position,piece) ? \result = true : \result = false;
	public boolean setField(int position, Piece piece) {
		Field field;
		try {
			if (testMove(position, piece)) {
				field = this.getField(position);
				field.addPiece(piece);
				return true;
			} else {
				return false;
			}
		} catch (InvalidArgumentContentException e) {
			System.out.println(e.getMessage());
			return false;
		}
	}
	
	/**
	 * Tests if move is valid.
	 * This considers pieces in space, as well as surrounding pieces.
	 * If field has base on it, or is occupied by same ringType as piece,
	 * return false. If no adjacent colour is the same as piece, or if piece
	 * is not starting base, return false.
	 *
	 * @param position int between 0 and 24
	 * @param piece of class Piece. Has colour and ringtype.
	 * @return boolean stating whether move is valid or not.
	 * @throws InvalidArgumentContentException the invalid argument content exception
	 */
	//@ requires position <= 24 && position >= 0;
	//@ ensures ((piece.getType() == Game.SBASE) && VALID_START_FIELDS.contains(position)) ? true : true || false;
	//@ ensures (piece.getType() == this.getField(position)) ? \result == false : true || false;
	//@ ensures (this.getField(position) == Game.BASE) ? \result == false : true || false;
	//@ ensures (this.getField(position) == Game.SBASE) ? \result == false : true || false;
	public boolean testMove(int position, Piece piece) throws InvalidArgumentContentException {
		if ((piece.getType() == Game.SBASE) && VALID_START_FIELDS.contains(position)) {
			return true;
		}
		
		if (this.getField(position).testOccupied(piece)) { //testOccupied returns false if full;
			String colour = piece.getColour();
			boolean movePossible = false;
			if (position > 4) {
				int abovePosition = position - 5;
				if (this.getField(abovePosition).testColour(colour)) {
					if (this.getField(abovePosition).isBase() && piece.getType() == Game.BASE) {
						return false;
					} else {
						movePossible = true;
					}
				}
			}
			if (position < 20) { // you test for the field below
				int belowPosition = position + 5;
				if (this.getField(belowPosition).testColour(colour)) {
					if (this.getField(belowPosition).isBase() && piece.getType() == Game.BASE) {
						return false;
					} else {
						movePossible = true;
					}
				}
			}
			if (position % 5 != 0 && position != 0) { //test to the left
				int leftPosition = position - 1;
				if (this.getField(leftPosition).testColour(colour)) {
					if (this.getField(leftPosition).isBase() && piece.getType() == Game.BASE) {
						return false;
					} else {
						movePossible = true;
					}
				}
			}
			if (position != 4 && position != 9 && position != 14 
					&& position != 19 && position != 24) {
				int rightPosition = position + 1;
				if (this.getField(rightPosition).testColour(colour)) {
					if (this.getField(rightPosition).isBase() && piece.getType() == Game.BASE) {
						return false;
					} else {
						movePossible = true;
					}
					return true;
				}
			}
			return movePossible;
		}
		return false;
	}
	
	/**
	 * Uses the strategy designed to systematically search for possible moves.
	 * If move is possible, return true, else false. 
	 * @param pieces are the pieces used to see if a move is possible.
	 * @return boolean
	 */
	//@ requires !pieces.isEmpty();
	public boolean possibleMoves(List<Piece> pieces) {
		NaiveStrategy dumbBud = new NaiveStrategy();
		String move = dumbBud.detMove(this, pieces, null);
		if (move == null) {
			return false;
		} else {
			return true;
		}
	}
	
	/**
	 * Returns readable representation of board.
	 * Uses toString() specified in Field.
	 *
	 * @return the string
	 */
	//@ ensures \result instanceof String;
	@Override
	public String toString() {
		
		String prettyBoard = "";
		prettyBoard += "\n" + Board.NEW_LINE_DELIM + "\n";
				
		int j = 1;
		for (int i = 0; i <= 24; i++, j++) {
			prettyBoard += fields[i];
			if (j % 5 == 0) {
				prettyBoard += "\n" + Board.NEW_LINE_DELIM + "\n";
			}
		}
		return prettyBoard;
	}	
	

	/**
	 * Calculates the points of a given color. 
	 * Does this by cycling through every field, and using it's testOwner() function. 
	 *
	 * @param color the color
	 * @return int representing score.
	 */
	//@ requires Game.colors.contains(color);
	public int countPoints(String color) {
		int points = 0;
		for (Field f : fields) {
			if (f.testOwner().equals(color) && !f.isBase()) {
				points ++;
			}
		}
		return points;
	}
	
//	public static void main (String[] args) {
//		Board b = new Board();
//		System.out.print(b);
//		try {
//			b.getField(3).addPiece(new Piece(Game.SBASE, "all"));
//		} catch (InvalidArgumentContentException e) {
//			System.out.println(e.getMessage());
//		}
//		b.setField(4, new Piece(Game.RING3, Game.COLOR2));
//		b.setField(2, new Piece(Game.RING3, Game.COLOR2));
//		b.setField(4, new Piece(Game.RING2, Game.COLOR2));
//		b.setField(12, new Piece(Game.RING2, Game.COLOR2));

//		for (Field field : b.fields) {
//			field.addPiece(new Piece(Game.RING3, Game.COLOR2));
//			field.addPiece(new Piece(Game.RING2, Game.COLOR1));
//			field.addPiece(new Piece(Game.RING1, Game.COLOR3));
//			field.addPiece(new Piece(Game.RING4, Game.COLOR4));
//		}
//		System.out.print(b);
}
