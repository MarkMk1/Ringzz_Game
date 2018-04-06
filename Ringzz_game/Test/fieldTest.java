package Test;

import static org.junit.jupiter.api.Assertions.*;

import Model.Field;
import Model.Piece;
import Server.Game;

import org.junit.Before;
import org.junit.jupiter.api.Test;
import static org.junit.Assert.assertTrue;

class FieldTest {

Field field1;
Field field2;
Field field3;

	@Before
	void setUp() {
		field1 = new Field();
		field1.addPiece(new Piece(Game.RING1, Game.COLOR1));
		field1.addPiece(new Piece(Game.RING2, Game.COLOR2));
		field1.addPiece(new Piece(Game.BASE, Game.COLOR1));
		
		field2 = new Field();
		field2.addPiece(new Piece(Game.RING1, Game.COLOR3));
		field2.addPiece(new Piece(Game.RING3, Game.COLOR3));
		field2.addPiece(new Piece(Game.BASE, Game.COLOR1));
		
		field3 = new Field();
		field3.addPiece(new Piece(Game.RING1, Game.COLOR1));
		field3.addPiece(new Piece(Game.RING2, Game.COLOR2));
		field3.addPiece(new Piece(Game.BASE, Game.COLOR4));

	}

	@Test
	void testOccupiedTest() {
		field1 = new Field();
		field1.addPiece(new Piece(Game.RING1, Game.COLOR1));
		field1.addPiece(new Piece(Game.RING2, Game.COLOR2));
		field1.addPiece(new Piece(Game.BASE, Game.COLOR1));
		
		assertTrue(field1.testOccupied(new Piece(Game.RING3, Game.COLOR3)));
		assertFalse(field1.testOccupied(new Piece(Game.RING2, Game.COLOR1)));
	}
	
	@Test
	void testColourTest() {
		field1 = new Field();
		field1.addPiece(new Piece(Game.RING1, Game.COLOR1));
		field1.addPiece(new Piece(Game.RING2, Game.COLOR2));
		field1.addPiece(new Piece(Game.BASE, Game.COLOR1));
		
		assertTrue(field1.testColour(Game.COLOR1));
		assertTrue(field1.testColour(Game.COLOR2));
		assertFalse(field1.testColour(Game.COLOR3));
		assertFalse(field1.testColour("all"));
		assertFalse(field1.testColour("marroon"));
	}
	
	@Test
	void AddPieceTest() {
		field1 = new Field();
		field1.addPiece(new Piece(Game.RING1, Game.COLOR1));
		field1.addPiece(new Piece(Game.RING2, Game.COLOR2));
		field1.addPiece(new Piece(Game.BASE, Game.COLOR1));
		field1.addPiece(new Piece(Game.RING1, Game.COLOR2));
		field1.addPiece(new Piece(Game.RING3, Game.COLOR3));
		
		
		assertTrue(field1.pieces.get(Game.RING1).getColour().equals(Game.COLOR1) && 
				field1.pieces.get(Game.RING1).getType() == Game.RING1);
		assertTrue(field1.pieces.get(Game.RING3).getColour().equals(Game.COLOR3) && 
				field1.pieces.get(Game.RING3).getType() == Game.RING3);
		
		field2 = new Field();
		field2.addPiece(new Piece(Game.SBASE, "all"));
		assertTrue(field2.pieces.get(Game.SBASE).getColour().equals("all"));
	}
	
	@Test
	void testOwnerTest() {
		
		field1 = new Field();
		field1.addPiece(new Piece(Game.BASE, Game.COLOR1));
		field1.addPiece(new Piece(Game.RING1, Game.COLOR1));
		field1.addPiece(new Piece(Game.RING2, Game.COLOR2));

		field2 = new Field();
		field2.addPiece(new Piece(Game.RING1, Game.COLOR3));
		field2.addPiece(new Piece(Game.RING3, Game.COLOR3));
		field2.addPiece(new Piece(Game.BASE, Game.COLOR1));
		
		field3 = new Field();
		field3.addPiece(new Piece(Game.RING1, Game.COLOR1));
		field3.addPiece(new Piece(Game.RING2, Game.COLOR2));
		field3.addPiece(new Piece(Game.BASE, Game.COLOR4));

//		System.out.println(field1.testOwner());
//		System.out.println(field1);
//		System.out.println(field2.testOwner());		
//		System.out.println(field2);
//		System.out.println(field3.testOwner());
//		System.out.println(field3);
		
		System.out.println("HEY" + field3.testOwner());
		assertTrue(field1.testOwner().equals(Game.COLOR1));
		assertTrue(field2.testOwner().equals(Game.COLOR3));
		assertNull(field3.testOwner());
	}

}
