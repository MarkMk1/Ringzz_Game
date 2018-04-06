package Model;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import Server.Game;

// TODO: Auto-generated Javadoc
/**
 * The Class Field.
 */
public class Field {
	
	/** The pieces. */
	public Map<Character, Piece> pieces = new HashMap<Character, Piece>();
	
	/** The pretty field. */
	private String prettyField = "       "; //7 spaces, middle for smallest ring.
	
	/** The Constant DELIMITER. */
	public static final String DELIMITER = "|";
	
	/** The Constant START_BASE. */
	public static final String START_BASE = "~~~S~~~";



	/**
	 * Instantiates a new field.
	 */
	public Field() {
		
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	/**
	 * Returns pretty string for printing board. 
	 * @return String pretty field
	 */
	public String toString () {
		for (Piece p : pieces.values()) {
			String colourCap = p.getColour().substring(0, 1).toUpperCase();
			
			if (p.getType() == Game.SBASE) {
				this.prettyField = Field.START_BASE;
			}
			if (p.getType() == Game.BASE) {
				String boxString = Field.START_BASE.substring(0,3) + colourCap +
						Field.START_BASE.substring(4);
				this.prettyField = boxString;
			}
			
			if (p.getType() == Game.RING4) {
				this.prettyField = colourCap + this.prettyField.substring(1,6) + colourCap;
			}
			if (p.getType() == Game.RING3) {
				this.prettyField = this.prettyField.substring(0,1) + colourCap + this.prettyField.substring(2,5) + colourCap + this.prettyField.substring(6);
			}
			if (p.getType() == Game.RING2) {
				this.prettyField = this.prettyField.substring(0,2) + colourCap + this.prettyField.substring(3,4) + colourCap + this.prettyField.substring(5);
			}
			if (p.getType() == Game.RING1) {
				this.prettyField = this.prettyField.substring(0,3) + colourCap + this.prettyField.substring(4);
			}
		}
        return DELIMITER + this.prettyField + DELIMITER;
        }
	
	/**
	 * Tests whether field has piece of that type, or base.
	 * If occupied, return false, you can't use space. 
	 *
	 * @param piece the piece
	 * @return boolean
	 */
	public boolean testOccupied(Piece piece) {
		char pieceType = piece.getType();
		if (pieces.containsKey(Game.BASE) || pieces.containsKey(Game.SBASE) || pieces.containsKey(pieceType)) {
//			System.out.println("Field - Contains Base or similar piece, can't place there");
			return false;
		} else if ((pieceType == (Game.BASE) || pieceType == (Game.SBASE)) && !pieces.isEmpty()) {
			return false;
		}
		return true;
	}
	
	/**
	 * Checks if is base.
	 *
	 * @return true, if is base
	 */
	public boolean isBase() {
		if (pieces.containsKey(Game.BASE)) {
			return true;
		}
		return false;
	}

	
	/**
	 * Creates an iterator to go through pieces map's characters. 
	 * Is true if field has piece of that colour, or if it has starting base.
	 *
	 * @param colour the colour
	 * @return boolean
	 */
	public boolean testColour(String colour) {
		Iterator<Character> piecesIter = pieces.keySet().iterator();
		while (piecesIter.hasNext()) {
			if (pieces.get(piecesIter.next()).getColour().equals(colour)) {
				return true;
			} else if (pieces.containsKey(Game.SBASE)) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * First tests if position is occupied with similar piece, or base.
	 * If true, then pieces.put. 
	 *
	 * @param piece the piece
	 */
	public void addPiece(Piece piece) {
		if (testOccupied(piece)) {
			pieces.put(piece.getType(), piece);
		}
	}
	
	/**
	 * Tests the owner of this field amongst Game's COLOR constants. 
	 * @return String, null for draw, otherwise winning colour. 
	 */
	public String testOwner() {
		Map<String, Integer> colourCount = new HashMap<String, Integer>();
		colourCount.put(Game.COLOR1, 0);
		colourCount.put(Game.COLOR2, 0);
		colourCount.put(Game.COLOR3, 0);
		colourCount.put(Game.COLOR4, 0);
		
		for (Piece p : this.pieces.values()) {
			if (p.getColour().equals(Game.COLOR3)) {
				colourCount.replace(Game.COLOR3, colourCount.get(Game.COLOR3) + 1);
			} else if (p.getColour().equals(Game.COLOR1)) {
				colourCount.replace(Game.COLOR1, colourCount.get(Game.COLOR1) + 1);
			} else if (p.getColour().equals(Game.COLOR2)) {
				colourCount.replace(Game.COLOR2, colourCount.get(Game.COLOR2) + 1);
			} else if (p.getColour().equals(Game.COLOR4)) {
				colourCount.replace(Game.COLOR4, colourCount.get(Game.COLOR4) + 1);
			}
			
		}
		
		Map.Entry<String, Integer> maxEntry = null;
		boolean drawFlag = true;
		
		for (Map.Entry<String, Integer> entry : colourCount.entrySet())
		{
		    if (maxEntry == null || entry.getValue().compareTo(maxEntry.getValue()) > 0)
		    {
		        maxEntry = entry;
		        drawFlag = false;
//		        System.out.println("Got to false");
		    } else if (entry.getValue().compareTo(maxEntry.getValue()) == 0) {
		    	drawFlag = true;
//		    	System.out.print("Got to drawFlag true");
		    }
		}		
//		System.out.println(maxEntry);
		if (drawFlag) {
//			System.out.println("draw");
			return " ";
		};
//		System.out.print(maxEntry.getKey());
		return maxEntry.getKey();
	}
	
	/**
	 * The main method.
	 *
	 * @param arg the arguments
	 */
	public static void main (String[] arg) {
//		Field field = new Field();
//		field.addPiece(new Piece(Game.RING3, Game.COLOR2));
//		field.addPiece(new Piece(Game.RING2, Game.COLOR1));
//		field.addPiece(new Piece(Game.RING1, Game.COLOR3));
//		field.addPiece(new Piece(Game.RING4, Game.COLOR4));
//		System.out.println(field);
	}
}
