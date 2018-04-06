package Model;

import java.util.Arrays;

import Exceptions.*;
import Server.Game;

// TODO: Auto-generated Javadoc
/**
 * The Class Piece.
 */
public class Piece {
	
	/** The colour. */
	private String colour;
	
	/** The type. */
	private char type;
	
	/**
	 * Instantiates a new piece.
	 *
	 * @param type the type
	 * @param colour the colour
	 */
	public Piece(char type, String colour) {
		this.colour = null;
		this.type = ' ';
		try {
			if (!Game.ringTypes.contains(type)) {	
				throw new InvalTypeArgException();
				} 
			else if (!Game.colors.contains(colour)) {
				throw new InvalColourArgException();
			} else {
				this.colour = colour;
				this.type = type;
			}
		} catch (InvalidArgumentContentException e) {
			System.out.println("invalid input, " + e.getMessage());
		}
	}
	
	/**
	 * Gets the type.
	 *
	 * @return the type
	 */
	public char getType() {
		return type;
	}
	
	/**
	 * Gets the colour.
	 *
	 * @return the colour
	 */
	public String getColour() {
		return colour;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return this.getColour() + ": " + this.getType();
	}
}
