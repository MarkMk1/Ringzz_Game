package Server;

import Model.Board;
import Model.Piece;
import Model.User;
//import Model.Player.*;
import Model.Player.Strategy.*;

import java.io.IOException;
import java.net.Socket;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import Client.Controller.Client;
import Client.Controller.Player;
import Exceptions.InvalidInputException;
import Exceptions.InvalidPlayerCountException;
import Exceptions.InvalidArgumentContentException;

// TODO: Auto-generated Javadoc
/**
 * Game of Ringzz. 
 * @author Mark
 *
 */
public class Game extends Observable implements Runnable{

	/** The board. */
	private Board board;
	
	/** The users. */
	private List<User> users;
	
	/** The finished players. */
	private int finishedPlayers = 0;
	
	/** The current move. */
	private String currentMove;
	
	/** The no valid move prop. */
	private boolean noValidMoveProp = false;
	
	/** The current field. */
	private int currentField;
	
	/** The current ring. */
	public char currentRing = ' ';
	
	/** The current color. */
	public String currentColor = null;
	
	/** The current position. */
	public int currentPosition = 99;
	
	/** The current turn. */
	private User currentTurn = null;
	
	/** The valid move. */
	private boolean validMove;
	/** Used to determine move when user disconnects.	 */
	private Strategy naive = new NaiveStrategy();
	
	/** The ending. */
	private boolean ending;
	
	/** The user 4. */
	private User user1, user2, user3, user4;
	
	/**  Constants for the colors of the rings. */
	public final static String COLOR1 = "red";
	
	/** The Constant COLOR2. */
	public final static String COLOR2 = "purple";
	
	/** The Constant COLOR3. */
	public final static String COLOR3 = "green";
	
	/** The Constant COLOR4. */
	public final static String COLOR4 = "yellow";
	
	/** The Constant COLOR5. */
	public final static String COLOR5 = "all";
	
	/**  List with all the available colors. */
	public final static List<String> colors = new ArrayList<>(Arrays.asList(COLOR1, COLOR2, COLOR3, COLOR4, COLOR5));
	
	/**  List with the colors of user3 in case of 3 players. */
	List<String> listColors1, listColors2, listColors4, listColors3;
	
	/**  Constants for the different types of pieces. */
	public final static char RING1 = '1'; // ring of size 1
	
	/** The Constant RING2. */
	public final static char RING2 = '2'; // ring of size 2
	
	/** The Constant RING3. */
	public final static char RING3 = '3'; // ring of size 3
	
	/** The Constant RING4. */
	public final static char RING4 = '4'; // ring of size 4
	
	/** The Constant BASE. */
	public final static char BASE = 'B'; // the base
	
	/** The Constant SBASE. */
	public final static char SBASE = 'S'; // the starting base
	
	/** The Constant ringTypes. */
	public final static List<Character> ringTypes = new ArrayList<>(Arrays.asList(RING1, RING2, RING3, RING4, BASE, SBASE));
	
	/**
	 * Initialises Game. Opens board, assigns colours. 
	 *
	 * @param users List of every user, including AI users.
	 * @throws InvalidPlayerCountException the invalid player count exception
	 */
	//@ requires !users.isEmpty();
	//@ ensures gamePlayers() == users;
	public Game(List<User> users) throws InvalidPlayerCountException {
		this.users = users;
		this.validMove = true;	
		this.board = new Board();
		this.ending = false;
		}
	
	/**
	 * Returns a list with the users in the game.
	 *
	 * @return list with users in the game
	 */
	//@ pure
	public List<User> gamePlayers() {
		return users;
	}
	
	
	/**
	 * Notifies UserIOs that game is starting, prints that it has been done.
	 */
	//@ pure
	public void gameStart() {
		setChanged();
		notifyObservers("start");
	}
	
	/**
	 * Divides the colors to the players of the game. 
	 * This function also calls a function which distributes the pieces by notifying Observers of game.
	 *
	 * @throws InvalidPlayerCountException the invalid player count exception
	 */
	//@ ensures !users.get(0).getPieces().isEmpty();
	//@ ensures !users.get(1).getPieces().isEmpty();
	public void divideColors() throws InvalidPlayerCountException {
		// Divide the colors and pieces to the users
		List<Piece> pieces;
//		System.out.println(this.users.size());
		switch(this.users.size()) {
			case 2:
				// User 1
				user1 = users.get(0);
				listColors1 = new ArrayList<String>();
				listColors1.add(colors.get(0));
				listColors1.add(colors.get(1));
				user1.setColor(listColors1);
				user1.setPieces(getPieces(user1));
				pieces = user1.getPieces();
				pieces.add(new Piece(Game.SBASE, Game.COLOR5));
				user1.setPieces(pieces);
				
				// User 2
				user2 = users.get(1);
				listColors2 = new ArrayList<String>();
				listColors2.add(colors.get(2));
				listColors2.add(colors.get(3));
				user2.setColor(listColors2);
				user2.setPieces(getPieces(user2));
				
				setChanged();
				notifyObservers("color " + user1.getName() + " " + user1.getColor().get(0) + " "+ user1.getColor().get(1));
				setChanged();
				notifyObservers("color " + user2.getName() + " "+ user2.getColor().get(0) +" "+ user2.getColor().get(1));
				break;
			case 3:
				// User 1
				user1 = users.get(0);
				listColors1 = new ArrayList<String>();
				listColors1.add(colors.get(0));
				listColors1.add(colors.get(1));
				user1.setColor(listColors1);
				user1.setPieces(getPieces(user1, colors.get(1)));
				pieces = user1.getPieces();
				pieces.add(new Piece(Game.SBASE, Game.COLOR5));
				user1.setPieces(pieces);
				// User 2
				user2 = users.get(1);
				listColors2 = new ArrayList<String>();
				listColors2.add(colors.get(1));
				listColors2.add(colors.get(2));
				user2.setColor(listColors2);
				user2.setPieces(getPieces(user2, colors.get(1)));
				// User 3
				user3 = users.get(2);
				listColors3 = new ArrayList<String>();
				listColors3.add(colors.get(1));
				listColors3.add(colors.get(3));
				user3.setColor(listColors3);
				user3.setPieces(getPieces(user3, colors.get(1)));
				
				setChanged();
				notifyObservers("color " + user1.getName() +" "+ user1.getColor().get(0) +" "+ user1.getColor().get(1));
				setChanged();
				notifyObservers("color " + user2.getName() +" "+ user2.getColor().get(0) +" "+ user2.getColor().get(1));
				setChanged();
				notifyObservers("color " + user3.getName() +" "+ Game.COLOR2 +" "+ Game.COLOR4);
				break;
			case 4:
				// User 1
				user1 = users.get(0);
				listColors1 = new ArrayList<String>();
				listColors1.add(colors.get(0));
				user1.setColor(listColors1);
				user1.setPieces(getPieces(user1));
				pieces = user1.getPieces();
				pieces.add(new Piece(Game.SBASE, Game.COLOR5));
				user1.setPieces(pieces);
				// User 2
				user2 = users.get(1);
				listColors2 = new ArrayList<String>();
				listColors2.add(colors.get(1));
				user2.setColor(listColors2);
				user2.setPieces(getPieces(user2));
				// User 3
				user3 = users.get(2);
				listColors3 = new ArrayList<String>();
				listColors3.add(colors.get(2));
				user3.setColor(listColors3);
				user3.setPieces(getPieces(user3));
				// User 4
				user4 = users.get(3);
				listColors4 = new ArrayList<String>();
				listColors4.add(colors.get(3));
				user4.setColor(listColors4);
				user4.setPieces(getPieces(user4));
				
				setChanged();
				notifyObservers("color " + user1.getName() +" "+ Game.COLOR1);
				setChanged();
				notifyObservers("color " + user2.getName() +" "+ Game.COLOR2);
				setChanged();
				notifyObservers("color " + user3.getName() +" "+ Game.COLOR3);
				setChanged();
				notifyObservers("color " + user4.getName() +" "+ Game.COLOR4);
				break;
			default:
				throw new InvalidPlayerCountException("game must have between 2 and 4 players");
		}
	}
	
	/**
	 * Returns a list with all the pieces the user should have, for one color it only gives 1/3rd of the pieces.
	 *
	 * @param user the user who needs the pieces
	 * @param colorLessPieces for this color only one-third of the pieces should be given
	 * @return a list with all the pieces the user should have
	 */
	//@ requires user != null;
	//@ requires Game.colors.contains(colorLessPieces);
	public List<Piece> getPieces(User user, String colorLessPieces) {
		List<String> colors = user.getColor();
		List<Piece> pieces = new ArrayList<Piece>();
		for (String col : colors) {
			if(!col.equals(colorLessPieces)) {
				for(int i=0; i<3; i++) {
					pieces.add(new Piece(RING1, col));
					pieces.add(new Piece(RING2, col));
					pieces.add(new Piece(RING3, col));
					pieces.add(new Piece(RING4, col));
					pieces.add(new Piece(BASE, col));
				}
			} else {
				pieces.add(new Piece(RING1, col));
				pieces.add(new Piece(RING2, col));
				pieces.add(new Piece(RING3, col));
				pieces.add(new Piece(RING4, col));
				pieces.add(new Piece(BASE, col));
			}
		}
		return pieces;
	}
	
	/**
	 * Returns a list with all the pieces the user should have.
	 *
	 * @param user the user who needs the pieces
	 * @return a list with all the pieces the user should have
	 */
	//@ requires user != null;
	//@ pure
	public List<Piece> getPieces(User user) {
		List<String> colors = user.getColor();
		List<Piece> pieces = new ArrayList<Piece>();
		for (String col : colors) {
			for(int i=0; i<3; i++) {
				pieces.add(new Piece(RING1, col));
				pieces.add(new Piece(RING2, col));
				pieces.add(new Piece(RING3, col));
				pieces.add(new Piece(RING4, col));
				pieces.add(new Piece(BASE, col));
			}
		}
		return pieces;
	}

	
	/**
	 * Returns a list of the users in the game.
	 *
	 * @return the list of users in the game
	 */
	//@ pure
	public List<User> getUsers() {
		return this.users;
	}
	
	/**
	 * Sets the type of the ring to be used for the current move. 
	 * Does this by taking in an array representing the entered move string,
	 * and checking the appropriate position for one of the ring types.
	 * Sets String currentRing;
	 *
	 * @param moveArray the new current ring
	 */
	//@ requires moveArray != null;
	//@ ensures (moveArray.get(1).charAt(0) == Game.RING1 || moveArray.get(1).charAt(0) == Game.RING2 || moveArray.get(1).charAt(0) == Game.RING3 || moveArray.get(1).charAt(0) == Game.RING4 || moveArray.get(1).charAt(0) == Game.BASE || moveArray.get(1).charAt(0) == Game.SBASE)) ==> validMove == true */
	public void setCurrentRing(List<String> moveArray) {
		switch(moveArray.get(1).charAt(0)) {
			case Game.RING1:
				currentRing = Game.RING1;
				break;
			case Game.RING2:
				currentRing = Game.RING2;
				break;
			case Game.RING3:
				currentRing = Game.RING3;
				break;
			case Game.RING4:
				currentRing = Game.RING4;
				break;
			case Game.BASE:
				currentRing = Game.BASE;
				break;
			case Game.SBASE:
				currentRing = Game.SBASE;
				break;
			default: 
				validMove = false;
				System.out.println(new InvalidInputException("moveArray.get(1) does not produce a valid ringType."));
				break;
		}
	}
	
	/**
	 * Sets color to be used for current move. 
	 * Takes array representing current move, checks appropriate position
	 * for valid color type. 
	 * Sets currentColor. 
	 *
	 * @param moveArray the new current color
	 */
	//@ requires moveArray.get(2) != null;
	//@ ensures colors.contains(moveArray.get(2)) ?  = true : false;
	public void setCurrentColor(List<String> moveArray) {
		if (currentRing == Game.SBASE) {
			currentColor = Game.COLOR5;
		} else {
			switch(moveArray.get(2)) {
			case Game.COLOR1:
				currentColor = Game.COLOR1;
				break;
			case Game.COLOR2:
				currentColor = Game.COLOR2;
				break;
			case Game.COLOR3:
				currentColor = Game.COLOR3;
				break;
			case Game.COLOR4:
				currentColor = Game.COLOR4;
				break;
			case Game.COLOR5:
				currentColor = Game.COLOR5;
				break;
			default:
				validMove = false;
				System.out.println(new InvalidInputException("moveArray.get(2) does not produce a valid colour."));
				break;
			}
		}
	}

	/**
	 * Parses integer from moveArrays appropriate space. 
	 * Sets it as int currentPosition.
	 *
	 * @param moveArray the new current position
	 */
	//@ requires moveArray.get(3) != null;
	//@ requires moveArray.get(3).matches("^[+-]?\\d+$");
	//TODO
	//@ ensures Integer.parseInt(moveArray.get(3)) < 0 || Integer.parseInt(moveArray.get(3)) > 24 ? validMove = false : true  
	public void setCurrentPosition(List<String> moveArray) {		
		currentPosition = Integer.parseInt(moveArray.get(3)); 
		if (currentPosition >= 0 && currentPosition <= 24) {
			currentField = currentPosition;
		} else {
			validMove = false;
			System.out.println(new InvalidInputException("moveArray.get(2) does not produce a valid position."));
		}
	}

	
	/**
	 * The run function is what is called when thread is started in Server. 
	 * It first notifies users that game is starting with gameStart(). 
	 * It then divides the colors depending on how many players there are with divideColors().
	 * Then, while there are players who still have possible moves, it will notify the players of whos turn it is. 
	 * If that user is connected, it will wait for them to set the current move with setCurrentMove(). 
	 * Else, it will set that move with the naive strategy. 
	 * It then retrieves a matcher for that move, the pattern in use depends on whether this is the first turn or not. 
	 * It then uses this to test the move, and set it if it passes.
	 */
	//@ requires users.size() >= 2;
	public void run() {
		gameStart();
		int finishedPlayers = 0;
		
		try {
			divideColors();
		} catch (InvalidPlayerCountException e1) {
			System.out.print(e1.getMessage() + "- run() found invalid no. of players");
		}
		
		List<User> playersWhoCantPlay = new ArrayList<User>();
		outerloop:
		while(finishedPlayers < users.size() && !ending) {
			for (User u : users) {
				currentTurn = u;
				noValidMoveProp = true; 
				
				while (noValidMoveProp && !ending) {
					validMove = true;
					if(!board.possibleMoves(u.getPieces())) {
//						System.out.println("No possible moves anymore");
						if (!playersWhoCantPlay.contains(u)) {
							playersWhoCantPlay.add(u);
							finishedPlayers ++;
						}
						break;
					}
					
					/**
					 * Checks connection with user. 
					 * If fails, it closes the UserIO,
					 * as well as removing this user from the server lobby. 
					 * It should then go to endGame().
					 */
					try {
						Socket socket = u.getUserIO().getSocket();
						if (!Client.checkConnection(socket)) {
							System.out.println("Connection is lost");
							u.getUserIO().getServer().clientDisconnect(u);
							u.getUserIO().close();
							break outerloop;
						} 
					} catch (IOException e) {
						System.out.println(e.getMessage() + " - Checked client in UserIO");
					}
		
					try {
						synchronized(this) {
							u.getUserIO().setTurn();
							setChanged();
							notifyObservers("turn " + u.getName()); 
							this.wait();
						}
					} catch (InterruptedException e) {
						Server.toConsole(e.toString());
					}
					
					if (ending) {
						break outerloop;
					}
					
//					System.out.println(currentMove);
					List<String> moveArray = Arrays.asList(currentMove.split("[\\s']"));
					
					setCurrentRing(moveArray);
					setCurrentColor(moveArray);
					setCurrentPosition(moveArray);
								
					
					if (testMove(u, currentColor, currentRing, currentField, validMove)) {
						this.noValidMoveProp = false;

						board.setField(currentField, new Piece(currentRing, currentColor));
						
						List<Piece> pieces = u.getPieces();
						System.out.println(pieces);

						pieces.remove(u.checkPiece(currentColor, currentRing));
						u.setPieces(pieces);
						
						if (currentRing == Game.SBASE) {
							try {
								board.setInitialBasePosition(currentField);
							} catch (InvalidInputException e) {
								System.out.println(e.getMessage());
							}
						}
						setChanged();
						notifyObservers("move " + currentRing + " " + currentColor + " " + currentField);
					} else {
						setChanged();
						notifyObservers("error InvalidMoveError " + currentTurn.getName());
					}
				}
//				else {
//					// TODO valid error message?
//					u.getUserIO().invalidMove("server could not recognise move");
//				}
			}
		}
		if (!ending) {
			endGame();
		}
	}
	
	/**
	 * Prints the points for each player. 
	 */
	public void countPoints() {
		for (User u : users) {
			int score = 0;
			for (String color : u.getColor()) {
				score = score + board.countPoints(color); // ? score : board.countPoints(color);
			}
			setChanged();
			notifyObservers("score " + u.getName() + " " + score );
		}
	}
	
	/**
	 * Ends game by printing points, declaring winner, and closing game. 
	 */
	//@ pure
	public void endGame() {
		countPoints();
		setChanged();
		notifyObservers("gameover");
	}
	
	/**
	 * This method can be called by the server, to end this game in a not natural way
	 * (e.g. when a user leaves or disconnects). 
	 * @param name the name of the user who disconnects or leaves
	 */
	//@ requires name != null;
	public void endGame(String name) {
		System.out.println("We are ending the game in Game.java");
		ending = true;
		synchronized(this) { // In case the run method is locked
			notifyAll();
		}
		countPoints();
		setChanged();
		notifyObservers("gameover");
//		for (User u : users) {
//			u.setNone();
//		}
	}


	/**
	 * Sets the current move. 
	 * Can be used by another class, to allow the run() method to continue
	 * if it is waiting for move to be set. 
	 * @param currentMove String of format 'move' + 'rsize' + 'color' + 'index'.
	 * @param u user, so as to make sure that only the user whos turn it is can set this.
	 */
	//@ requires currentMove != null; 
	//@ requires u != null;
	//@ requires currentTurn != null;
	//@ ensures currentTurn.getName().equals(u.getName()) ? this.currentMove == currentMove : this.currentMove == \old(currentMove);
	public synchronized void  setCurrentMove(String currentMove, User u) {
		if (currentTurn.getName().equals(u.getName())) {
			this.currentMove = currentMove;
			notifyAll();
		}
	}
	
	/**
	 * Tests that user u has the piece, and that it is a valid piece.
	 *
	 * @param u the u
	 * @param color the color
	 * @param type the type
	 * @param position the position
	 * @param validMove the valid move
	 * @return boolean true if valid.
	 */
	//@ requires u != null;
	//@ requires color != null;
	//@ requires ringTypes.contains(type);
	//@ requires position >= 0 && position <= 24;
	public boolean testMove(User u, String color, char type, int position, boolean validMove) {
		if (!validMove) {
			return false;
		}
		try {
			return (u.checkPiece(color, type) >= 0) && board.testMove(currentField, new Piece(currentRing, currentColor)) ? true : false;
		} catch (InvalidArgumentContentException e) {
			System.out.println(e.getMessage() + " - testMove of Game");
		} return false;
	}

	
//	public static void main (String[] args) {
//		Pattern validMovePattern = Pattern.compile("(move) (.+) (.+) (.+)");
//		Matcher moveMatcher = validMovePattern.matcher("move 2 red 23 \n move 2 blue 11 \n move 3 grey 100");
//		moveMatcher.find();
//		System.out.println(moveMatcher.group(1));
//		System.out.println(moveMatcher.group(2));
//		System.out.println(moveMatcher.group(3));
//		System.out.println(moveMatcher.group(4));
//		moveMatcher.find();
//		System.out.println(moveMatcher.group(1));
//		System.out.println(moveMatcher.group(2));
//		System.out.println(moveMatcher.group(3));
//		System.out.println(moveMatcher.group(4));
//		System.out.println(moveMatcher.group(5));
//	}
}
