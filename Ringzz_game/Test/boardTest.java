package Test;

import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.jupiter.api.BeforeEach;

import Model.Board;
import org.junit.jupiter.api.Test;

import Exceptions.InvalidArgumentContentException;
import Exceptions.InvalidInputException;
import Model.Piece;
import Server.Game;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;



class BoardTest {
	
	List<Board> boards;
	int c;
	Board b1;
	Board b2;
	Board b3;
	Board b4;

	@BeforeEach
	void setUp() {
		this.b1 = new Board();
		this.b2 = new Board(); 
		this.b3 = new Board(); 
		this.b4 = new Board();
		this.boards = Arrays.asList(b1,b2,b3,b4);
		this.c = 0;
		b1.setField(2, new Piece(Game.SBASE, Game.COLOR5));
		b2.setField(6, new Piece(Game.SBASE, Game.COLOR5));
		b3.setField(16, new Piece(Game.SBASE, Game.COLOR5));
		b4.setField(18, new Piece(Game.SBASE, Game.COLOR5));
		try {
			b2.setInitialBasePosition(6);
			b3.setInitialBasePosition(16);
			b4.setInitialBasePosition(18);
		} catch (InvalidInputException e) {
			System.out.println(e.getMessage());
		}
		
	}
	
	@Test
	void constructTest() { //test the placement of the startBase.
		
		for (Board b : boards) {
			for (int i = 0; i <= 24 ; i++)
				try {
					if (!b.getField(i).testOccupied(new Piece(Game.SBASE, "all"))) {
						if (Board.VALID_START_FIELDS.contains(i)) {
							this.c++;
						} else {
							System.out.println("S piece was found outside of valid positions");
							fail();
						}
					}
				} catch (InvalidArgumentContentException e) {
					System.out.println(e.getMessage());
					fail();
				}
		}
		// As one board is set incorrectly, only three should have a base.	
		assertTrue(c == 3);
	}
	
	@Test
	void getFieldTest() {
		try {
			for (Board b : boards) {
				for (int i = 0; i <= 24; i++) {
					b.getField(i);
				}
			}
		} catch (InvalidArgumentContentException e) {
			System.out.println("recieved exception in getFieldTest()");
			fail();
		}
	}
	
	
	@Test
	void setInitialBasePositionTest() {
		try {
			for (Board b : boards) {
				for (int i = 0; i <= 24; i++) {
					if (b.getField(i).pieces.containsKey(Game.SBASE)) {
						b.setInitialBasePosition(i);
					}
				}
				if (b.getField(b.getInitialBasePosition()).pieces.containsKey(Game.SBASE)) {
					c++;
				}
			}
		} catch (InvalidArgumentContentException e) {
			System.out.println("recieved exception in getFieldTest()");
			fail();
		} catch (InvalidInputException e) {
			System.out.println("Invalid index found for SBASE");
			fail();
		}
		
		assertTrue(c == 3);
	}
	
	
	@Test
	void correctSetFieldTest() {
		b2.setField(b2.getInitialBasePosition() + 5, new Piece(Game.RING2, Game.COLOR1));
		b2.setField(b2.getInitialBasePosition() - 5, new Piece(Game.RING3, Game.COLOR2));
		b2.setField(b2.getInitialBasePosition() + 1, new Piece(Game.RING4, Game.COLOR3));
		b2.setField(b2.getInitialBasePosition() - 1, new Piece(Game.RING2, Game.COLOR4));
		System.out.println("Board 2 \n" + b2);
		assertTrue(true);
	}
		
	
	@Test
	void incorrectSetFieldTest() {
		b1.setField(b2.getInitialBasePosition() + 5, new Piece(Game.RING2, Game.COLOR1));
		b1.setField(b2.getInitialBasePosition() - 5, new Piece(Game.RING3, Game.COLOR2));
		b1.setField(b2.getInitialBasePosition() + 1, new Piece(Game.RING4, Game.COLOR3));
		b1.setField(b2.getInitialBasePosition() - 1, new Piece(Game.RING2, Game.COLOR4));
		System.out.println("Board 1 \n" + b1);

		assertTrue(true);
	}

	@Test
	void countPointsTest() {	
		c = b2.getInitialBasePosition();
		Piece pieceR1, pieceR2, pieceR3, pieceR4, pieceG1, pieceG2, pieceGB, pieceY4, piecePB, pieceY3;
		pieceR1 = new Piece(Game.RING1,Game.COLOR1);
		pieceR2 = new Piece(Game.RING2,Game.COLOR1);
		pieceR3 = new Piece(Game.RING3,Game.COLOR1);
		pieceR4 = new Piece(Game.RING4,Game.COLOR1);
		pieceG1 = new Piece(Game.RING1,Game.COLOR2);
		pieceG2 = new Piece(Game.BASE,Game.COLOR2);
		pieceGB = new Piece(Game.RING2,Game.COLOR2);
		pieceY3 = new Piece(Game.RING3,Game.COLOR4);
		pieceY4 = new Piece(Game.RING4,Game.COLOR4);
		piecePB = new Piece(Game.BASE,Game.COLOR3);
		
		b2.setField(c+1, pieceR1);
		b2.setField(c+5, pieceR2);
		b2.setField(c+1, pieceR3);
		b2.setField(c-5, pieceGB);
		b2.setField(c-1, piecePB);
		b2.setField(c+1, pieceG2);
		b2.setField(c+5, pieceG1);
		b2.setField(c+1, pieceR4);
		b2.setField(c+5, pieceY4);
		b2.setField(c+5, pieceY3);
		
//		System.out.println(b1.countPoints(Game.COLOR1));
//		System.out.println(b1.countPoints(Game.COLOR2));
//		System.out.println(b1.countPoints(Game.COLOR3));
//		System.out.println(b1.countPoints(Game.COLOR4));

		boolean testRed = 1 == b2.countPoints(Game.COLOR1);
		boolean testPurple = 1 == b2.countPoints(Game.COLOR2);
		boolean testYellow = 1 == b2.countPoints(Game.COLOR4);
		boolean testGreen = 1 == b2.countPoints(Game.COLOR3);
		
		System.out.println(b2);
		assertTrue(testRed);
		assertTrue(testGreen);
		assertTrue(testYellow);
		assertTrue(testPurple);
		
	}
	
	void possibleMovesTest() {
		//TODO possibleMovesTest, can also do it in systems testing as required setup is rather large
	}
	
}
