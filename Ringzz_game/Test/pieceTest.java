package Test;

import static org.junit.jupiter.api.Assertions.*;

import Model.Piece;
import Server.Game;

import org.junit.jupiter.api.Test;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertNull;

class PieceTest {


	@Test
	void invalidColoursTest() {
		Piece p1 = new Piece(Game.RING2, Game.COLOR1);
		Piece p2 = new Piece(Game.RING3, "maroon");
		Piece p3 = new Piece(Game.SBASE, "turqiouse");
			assertTrue(p1.getColour().equals(Game.COLOR1));
		assertNull(p2.getColour());
		assertNull(p3.getColour());
	}
	
	@Test
	void invalidTypeTest() {
		Piece p1 = new Piece('x', Game.COLOR1);
		Piece p2 = new Piece('9', Game.COLOR1);
		Piece p3 = new Piece(Game.BASE, Game.COLOR1);
		assertTrue(p1.getType() == ' ');
		assertTrue(p2.getType() == ' ');
		assertTrue(p3.getType() == Game.BASE);
	}
	
	@Test
	void getTypeTest() {
		Piece p3 = new Piece('B', "green");
		assertTrue(p3.getType() == Game.BASE);
	}
	
	@Test
	void getColourTest() {
		Piece p1 = new Piece('2', Game.COLOR2);
		assertTrue(p1.getColour().equals(Game.COLOR2));
	}
}
