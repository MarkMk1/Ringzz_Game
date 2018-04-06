package Client.Controller;

import java.io.IOException;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.*;
import java.util.regex.*;

import Server.Game;
import Client.View.*;
import Exceptions.*;
import Model.*;

import Model.Player.Strategy.NaiveStrategy;
import Model.Player.Strategy.SmartStrategy;

// TODO: Auto-generated Javadoc
/**
 * The main method of this class initializes the objects on the client side 
 * (e.g. create a new board, create a new TUI, create a new Player, create a new Client) 
 * Running the main method, a socket is created which is connected to a server at the given IP address and port number. 
 * The Client signals to the server that it wants to connect and communicates the extensions it has. 
 * The Client communicates the username and the states the Player is, as signalled via a created TUI and 
 * listens for inputs from the server: who joins the game, whether a game is started, error messages. 
 * When a new game is started, the Client creates a new Board, and listens to the colors the player should have. 
 * The newly created Player object is given the right list of Pieces. Each time a move has been made as notified by the server, 
 * the same move is made on the local board and the TUI is told to print the new state of the board. 
 * If it is the turn of the player, the player object is signalled to set a move. This move is communicated to the server as well.
 * The client also allows for disconnecting anytime, after which the thread is finished.
 * A Client object also has several methods which can be called by the TUI or the Player object 
 * (e.g. whether the user wants to join a game, leave, disconnect or indicate he/she is ready to play a game)
 * @author Oskar
 */

public class Client extends Observable {
	// Should use port 50000
	
	/** The Constant USAGE. */
	/*@ invariant USAGE != null; */
	private static final String USAGE
    = "usage: <name> <address> <port>";
	
	/** The printwriter. */
	/*@ invariant printwriter != null; */
	private PrintWriter printwriter;
	
	/** The name. */
	/*@ invariant name != null; */
	private String name;
	
	/**  The player object, used for playing a game. */
	private Player player;
	
	/**  The board on which we will play on. */
    private Board board = new Board();
    
    /**  Boolean to check whether it is the first time the 'turn <username>' command is sent by the server. */
    private boolean firstTurn;
    
    /**  Value to count how many players are in a game. */
    private int nrOfPlayer;
    
    /**  Boolean describing whether the user wants to play him or herself. */
    protected boolean human;
    
    /**  Boolean describing whether the user wants to use the SmartStrategy or not (the NaiveStrategy). */
    protected boolean smart;
    
    /**  Boolean to check whether the client has already waited for an acknowledgement, but had received something else instead. */
    private boolean secondTime;
    
    /**  String describing which color is shared by the players in the game, can be null. */
    private String sharedColor;
    
    /**  Value assigned by the user on how many milliseconds he/she allows the strategy to think. */
    protected int totalTime;
    
    /**  Value indicating how many players the player wants in a game. */
    private int howManyPlayers;
    
    /**  Set of all the colors called in the game to check for shared colors. */
    private Set<String> colorsInGame = new HashSet<>();
    
    
    
    
	/**
	 *  The states the player can be in.
	 */
	public static enum State {
		
		/** The connected. */
		CONNECTED, 
 /** The joined. */
 JOINED, 
 /** The ingame. */
 INGAME;
	}
	
	/** The state. */
	/*@ invariant state != null; */
	private State state;
	
	/**  The colors owned by the player. */
	/*@ invariant colors != null; */
	private List<String> colors = new ArrayList<>();
	
	/**  When the client is waiting for an acknowledgement from the server, this is set to true. */
	private boolean waitForAck;
	
	/**
	 *  The types of acknowledgements the client can receive.
	 */
	public static enum Acknowledge {
		
		/** The failed. */
		FAILED, 
 /** The connected. */
 CONNECTED, 
 /** The disconnected. */
 DISCONNECTED, 
 /** The left. */
 LEFT, 
 /** The joined. */
 JOINED, 
 /** The mademove. */
 MADEMOVE, 
 /** The ready. */
 READY;
	}
	
	/**  The type of acknowledgement received. */
	private Acknowledge acknowledge;
	
	/**  Indicate whether the player wants to disconnect. */
	private boolean disconnected;

	/** Lock used for synchronizing two threads running the TUI, when specific user input is requested. */
	/*@ invariant lockTUI != null; */
	public static Object lockTUI = new Object();
	
	/**  Patterns. */
	// Make patterns for recognizing certain commands
	public static String movePattern = "(move) (.+) (.+) (.+)";
	
	/** The move S base pattern. */
	public static String moveSBasePattern = "(move) (S) (.+)";
	
	/** The one color pattern. */
	public String oneColorPattern;
	
	/** The two color pattern. */
	public String twoColorPattern;
	
	/** The other color pattern. */
	public static String otherColorPattern = "(color) (.+) (.+) (.*)";
	
	/** The turn pattern. */
	public static String turnPattern = "(turn) (.+)";
	
	/** The r 1. */
	public static Pattern r1 = Pattern.compile(movePattern);
	
	/** The r 2. */
	public Pattern r2;
	
	/** The r 3. */
	public Pattern r3;
	
	/** The r 4. */
	public static Pattern r4 = Pattern.compile(otherColorPattern); // This is to keep track of all the distributed colors to the others
	
	/** The r 5. */
	public static Pattern r5 = Pattern.compile(turnPattern);
	
	/** The r 6. */
	public static Pattern r6 = Pattern.compile(moveSBasePattern);
	
	
	
	
	
	// ----------------------- Constructor -------------------------
	/**
	 * The constructor initializes the name, sets the state to CONNECTED, and indicates that
	 * player does not want to disconnect (disconnected = false) and that the client is not waiting
	 * for an acknowledgement from the server (waitForAck = false).
	 *
	 * @param writer output stream to the server
	 * @param name username of the player
	 */
	//@ requires writer != null;
	//@ requires name != null;
	//@ ensures getPlayerState() == State.CONNECTED;
	//@ ensures getWaitForAck() == false;
	//@ ensures getDisconnected() == false;
	//@ ensures getName().equals(name);
	//@ ensures getBoard() != null;
	public Client(PrintWriter writer, String name) {
		this.name = name;
		this.state = State.CONNECTED;
		this.printwriter = writer;
		waitForAck = false;
		disconnected = false;
		this.board = new Board();
		this.firstTurn = true;
		this.nrOfPlayer = 0;
		player = null;
		secondTime = false;
		sharedColor = null;
		totalTime = 0;
		howManyPlayers = 0;
		
		// Setting up patterns
		oneColorPattern = "(color " + name + ") (.+)";
		twoColorPattern = "(color " + name + ") (.+) (.+)";
		r2 = Pattern.compile(oneColorPattern);
		r3 = Pattern.compile(twoColorPattern);
	}
	
	// ---------------------- Commands ---------------------------
	
	/**
	 * Set whether the client is waiting for acknowledgement for sent command.
	 *
	 * @param ack true if waiting
	 */
	//@ requires ack != null;
	//@ ensures getAck() == ack;
	public void setAck (Acknowledge ack) {
		acknowledge = ack;
	}
	
	/**
	 * Add a color to the colors owned by the player.
	 *
	 * @param color which the player owns
	 */
	//@ requires Game.colors.contains(color);
	//@ ensures colors.contains(color);
	public void addColor(String color) {
		colors.add(color);
//		System.out.println("size of colors: " + colors.size());
	}
	
	/**
	 * Handle errors which the client cannot handle himself, is sent to all the observers (i.e. the TUI)
	 * @param line the string which needs to be handled by the observers
	 */
	/*@ requires line != null;
	 */
	public void handleError(String line) {
		setChanged();
		notifyObservers(line);
	}
	
	/**
	 * Handles disconnecting the server.
	 *
	 * @throws InterruptedException the interrupted exception
	 * @throws ServerCommunicationException if no acknowledgement is received from the server
	 */
	/*@ ensures getDisconnected() == true;
	 * ensures getWaitForAck() == false;
	 */
	public void disconnect() throws InterruptedException, ServerCommunicationException {
		printwriter.println("disconnect");
//		waitForAck = true;
//		synchronized (System.out) {
//			System.out.wait();
//		}
//		if (acknowledge != Acknowledge.DISCONNECTED) {
//			setAck(Acknowledge.FAILED);
//			throw new ServerCommunicationException("Failed to disconnect: received no acknowledge from the server");
//		}
		disconnected = true;
	}
	
	/**
	 * Handles joining a game on the server.
	 *
	 * @throws InvalidInputException if the player is not allowed to join
	 * @throws ServerCommunicationException if no acknowledgement is received from the server
	 * @throws InterruptedException the interrupted exception
	 */
	/*@ ensures getPlayerState() == State.JOINED;
	 * ensures getWaitForAck() == false;
	 */
	public void join () throws InvalidInputException, ServerCommunicationException, InterruptedException {
		if (this.getPlayerState() != Client.State.CONNECTED) {
			throw new InvalidInputException("Sorry, you are already in a game");
		}
//		System.out.println("sending to server: " + "join " + this.howManyPlayers);
		printwriter.println("join " + this.howManyPlayers);
//		waitForAck = true;
//		synchronized (System.out) {
//			System.out.wait();
//		}
//		if (acknowledge != Acknowledge.DISCONNECTED) {
//			setAck(Acknowledge.FAILED);
//			throw new ServerCommunicationException("Something went wrong, received no acknowledge from the server");
//		}
		this.state = State.JOINED;
	}
	
	/**
	 * Handles signalling to be ready to start a game.
	 *
	 * @throws InvalidInputException if the player is not allowed to send ready to the server
	 * @throws ServerCommunicationException if no acknowledgement is received from the server
	 * @throws InterruptedException the interrupted exception
	 */
	/*@ ensures getPlayerState() == State.INGAME;
	 * ensures getWaitForAck() == false;
	 */
	public void ready () throws InvalidInputException, ServerCommunicationException, InterruptedException {
		if (this.getPlayerState() != Client.State.JOINED) {
			throw new InvalidInputException("Sorry, you first have to join a game");
		}
		printwriter.println("ready");
//		waitForAck = true;
//		synchronized (System.out) {
//			System.out.wait();
//		}
//		if (acknowledge != Acknowledge.DISCONNECTED) {
//			setAck(Acknowledge.FAILED);
//			throw new ServerCommunicationException("Something went wrong, received no acknowledge from the server");
//		}
		this.state = State.INGAME;
	}
	
	/**
	 * Handles leaving from a game.
	 *
	 * @throws InvalidInputException if this command is not allowed
	 * @throws ServerCommunicationException if no acknowledgement is received
	 * @throws InterruptedException the interrupted exception
	 */
	/*@ ensures getPlayerState() == State.CONNECTED;
	 * ensures getWaitForAck() == false;
	 */
	public void leave () throws InvalidInputException, ServerCommunicationException, InterruptedException {
		if (getPlayerState() != Client.State.JOINED && getPlayerState() != Client.State.INGAME) {
			throw new InvalidInputException("You cannot leave when you are not in a game");
		}
		printwriter.println("leave");
//		waitForAck = true;
//		synchronized (System.out) {
//			System.out.wait();
//		}
//		if (acknowledge != Acknowledge.DISCONNECTED) {
//			setAck(Acknowledge.FAILED);
//			throw new ServerCommunicationException("Something went wrong, received no acknowledge from the server");
//		}
		this.state = State.CONNECTED;
		restartGame();
	}
	
	/**
	 * Handles making a move for the game.
	 *
	 * @param move the string with the move command
	 * @throws ServerCommunicationException if no acknowledgement is received
	 * @throws InterruptedException the interrupted exception
	 */
	/*@ requires getPlayerState() == State.INGAME;
	 * ensures getWaitForAck() == false;
	 */
	public void makeMove (String move) throws ServerCommunicationException, InterruptedException {
		printwriter.println(move);
//		System.out.println("Sending to server: " + move);
//		waitForAck = true;
//		synchronized (System.out) {
//			System.out.wait();
//		}
//		if (acknowledge != Acknowledge.MADEMOVE) {
//			setAck(Acknowledge.FAILED);
//			throw new ServerCommunicationException("Something went wrong, received no acknowledge from the server");
//		}
	}
	
	/**
	 * Returns a player with all the pieces the user should have, for one color it might only give 1/3rd of the pieces.
	 *
	 * @param colorLessPieces for this color only one-third of the pieces should be given, could be set to null if there is no such color
	 * @param human boolean to indicate whether the player should be a HumanPlayer
	 * @param smart boolean to indicate whether the strategy used should be the smart strategy (only applicable for ComputerPlayer)
	 * @param tui which the player should use
	 * @param board which the player plays on
	 * @param totalTime total time in milliseconds the strategy is approximately allowed to think
	 * @return a player object
	 */
	/*@ requires Game.colors.contains(colorLessPieces) || colorLessPieces == null;
	 * requires tui != null;
	 * requires board != null;
	 * requires totalTime >= 0;
	 * ensures \result ;
	 * ensures !\result.getColor().contains(colorLessPieces);
	 * ensures human ==> \result instanceof HumanPlayer;
	 * ensures (!human && smart) ==> ((ComputerPlayer)player).getStrategy() instanceof SmartStrategy();
	 */
	public Player createPlayer(String colorLessPieces, boolean human, boolean smart, TUI tui, Board board, int totalTime) {
		List<Piece> pieces = new ArrayList<Piece>();
		List<String> kleuren = getColors();
		for (String col : kleuren) {
//			System.out.println("Colors: " + col);
			if(!col.equals(colorLessPieces)) {
				for(int i=0; i<3; i++) {
					pieces.add(new Piece(Game.RING1, col));
					pieces.add(new Piece(Game.RING2, col));
					pieces.add(new Piece(Game.RING3, col));
					pieces.add(new Piece(Game.RING4, col));
					pieces.add(new Piece(Game.BASE, col));
				}
			} else {
				pieces.add(new Piece(Game.RING1, col));
				pieces.add(new Piece(Game.RING2, col));
				pieces.add(new Piece(Game.RING3, col));
				pieces.add(new Piece(Game.RING4, col));
				pieces.add(new Piece(Game.BASE, col));
			}
		}		
		if (human) {
			player = (Player) new HumanPlayer(name, colors, board, pieces, this, tui, totalTime);
		} else {
			if (smart) {
				player = (Player) new ComputerPlayer(name, colors, board, pieces, this, new SmartStrategy(), totalTime);
			} else {
				player = (Player) new ComputerPlayer(name, colors, board, pieces, this, new NaiveStrategy(), totalTime);
			}
		}
		return player;
	}
	
	/**
	 * Returns a player with all the pieces the user should have, for one color it might only give 1/3rd of the pieces.
	 * This method is used if the player has the first turn and thus also has a starting base.
	 * @param colorLessPieces for this color only one-third of the pieces should be given, could be set to null if there is no such color
	 * @param human boolean to indicate whether the player should be a HumanPlayer
	 * @param smart boolean to indicate whether the strategy used should be the smart strategy (only applicable for ComputerPlayer)
	 * @param tui which the player should use
	 * @param board which the player plays on
	 * @param totalTime total time in milliseconds the strategy is approximately allowed to think
	 * @param firstTurn true (or false) if the player has the first turn and thus also has a starting base
	 * @return a player object
	 */
	/*@ requires Game.colors.contains(colorLessPieces) || colorLessPieces == null;
	 * requires tui != null;
	 * requires board != null;
	 * requires totalTime >= 0;
	 * ensures \result ;
	 * ensures !\result.getColor().contains(colorLessPieces);
	 * ensures human ==> \result instanceof HumanPlayer;
	 * ensures (!human && smart) ==> ((ComputerPlayer)player).getStrategy() instanceof SmartStrategy();
	 */
	public Player createPlayer(String colorLessPieces, boolean human, boolean smart, TUI tui, Board board, int totalTime, boolean firstTurn) {
		List<Piece> pieces = new ArrayList<Piece>();
		List<String> kleuren = getColors();
		for (String col : kleuren) {
			if(!col.equals(colorLessPieces)) {
				for(int i=0; i<3; i++) {
					pieces.add(new Piece(Game.RING1, col));
					pieces.add(new Piece(Game.RING2, col));
					pieces.add(new Piece(Game.RING3, col));
					pieces.add(new Piece(Game.RING4, col));
					pieces.add(new Piece(Game.BASE, col));
				}
			} else {
				pieces.add(new Piece(Game.RING1, col));
				pieces.add(new Piece(Game.RING2, col));
				pieces.add(new Piece(Game.RING3, col));
				pieces.add(new Piece(Game.RING4, col));
				pieces.add(new Piece(Game.BASE, col));
			}
		}
		pieces.add(new Piece(Game.SBASE, Game.COLOR5));
		if (human) {
			player = (Player) new HumanPlayer(name, colors, board, pieces, this, tui, totalTime);
		} else {
			if (smart) {
				player = (Player) new ComputerPlayer(name, colors, board, pieces, this, new SmartStrategy(), totalTime);
			} else {
				player = (Player) new ComputerPlayer(name, colors, board, pieces, this, new NaiveStrategy(), totalTime);
			}
		}
		return player;
	}
	
	/**
	 * Set the state of the player.
	 *
	 * @param state the state of the player
	 */
	/*@ requires getPlayerState() == state;
	 */
	public void setState(State state) {
		this.state = state;
	}
	

	/**
	 * This method re-initialises important variables and objects for a new game.
	 */
	/*@ requires tui != null;
	 * ensures getBoard() != null;
	 */
	public void restartGame() {
		board = new Board();
        firstTurn = true;
        sharedColor = null;
        nrOfPlayer = 0;
        colorsInGame.clear();
        colors.clear();
//        boolean rightInput = false;
        this.howManyPlayers = 2;
//        while (!rightInput) {
//        	try {
//    			this.howManyPlayers = tui.howManyPlayers();
//    			rightInput = true;
//    		} catch (InvalidInputException e) {
//    			this.handleError(e.getMessage());
//    		}
    }
	
	/**
	 * This method handles acknowledgements 
	 * if the client has indicated it is waiting for one from the server.
	 * If the first time an acknowledgement is not received, this method will be called again.
	 * If a second time an acknowledgement is not received, it sets the Ack to FAILURE.
	 *
	 * @param line the line which is expected to be the acknowledgement.
	 * @param tui the tui
	 */
	//@ requires line != null;
	public void handleAcknowledgement(String line, TUI tui) {
		Matcher m1 = r1.matcher(line);
		boolean foundAck = false;
		if (line.equals("connected " + name)) {
			this.setAck(Acknowledge.CONNECTED);
			foundAck = true;
		} else if (line.equals("disconnected " + name)) {
			this.setAck(Acknowledge.DISCONNECTED);
			foundAck = true;
		} else if (line.equals("player " + name + " joined")) {
			this.setAck(Acknowledge.JOINED);
			foundAck = true;
		} else if (line.equals("player " + name + " left")) {
			if (this.getPlayerState() == State.INGAME) {
				// Reinitialize some variables and the board to facilitate a new game
				restartGame();
			}
			this.setAck(Acknowledge.LEFT);
			foundAck = true;
		} else if (line.equals("player " + name + " ready")) {
			this.setAck(Acknowledge.READY);
			foundAck = true;
		} else if (m1.find()) {
			this.setAck(Acknowledge.MADEMOVE);
			foundAck = true;
		} else if (secondTime) {
			this.setAck(Acknowledge.FAILED);
			foundAck = true;
		}
		if (foundAck) {
			synchronized(System.out) {
				System.out.notifyAll();    						
			}
		}
		secondTime = true;
	}
	
	/**
	 * This method handles the input from the server after initialization, but without
	 * taking acknowledgements into account.
	 *
	 * @param line the piece of text received from the server
	 * @param tui to which to print messages to
	 */
	/*@ requires line != null;
	 * requires tui != null;
	 * requires in != null;
	 */
	public void handleInput(String line, TUI tui) {
		// Create matchers with the patterns
		Matcher m1 = r1.matcher(line);
		Matcher m2 = r2.matcher(line);
		Matcher m3 = r3.matcher(line);
		Matcher m4 = r4.matcher(line);
		Matcher m5 = r5.matcher(line);
		Matcher m6 = r6.matcher(line);
		
		switch(line) {
		case "start":
			tui.message("Starting a game..");
			break;
		case "gameover":
			tui.message("The game has ended!");
//			for (int i=0; i<nrOfPlayer; i++) {
//				if (in.hasNextLine()) {
//					System.out.println("Printing a score:");
//					tui.handleScores(in.nextLine());
//				}
//			}
//			tui.handleScores(scores);
			this.setState(State.CONNECTED);
			
			// Reinitialize some variables and the board
			restartGame();
	        
	        tui.message("To join another game, enter 'join'.");
			break;
		default:
			if (m1.find()) { // Found a move command
//				System.out.println("Found a move command!");
				String color;
				char type = m1.group(2).charAt(0);
				if (type == Game.SBASE) {
					color = Game.COLOR5;
				} else {
					color = m1.group(3);
				}
				int position = Integer.parseInt(m1.group(4));
				Piece piece = new Piece(type, color);
				board.setField(position, piece);
				tui.printBoard(board);
			} else if (m6.find()) { // Probably found a move S <position> command
//				System.out.println("Found a special move command!");
				char type = Game.SBASE;
				String color = Game.COLOR5;
				int position = Integer.parseInt(m6.group(3));
//				System.out.println(position);
				Piece piece = new Piece(type, color);
				board.setField(position, piece);
				tui.printBoard(board);
			} else if (m3.find()) { // Found we get two colors
//				System.out.println("Found two colors!!");
				this.addColor(m3.group(2));
				this.addColor(m3.group(3));
				nrOfPlayer++;
				colorsInGame.add(m3.group(2));
				colorsInGame.add(m3.group(3));
				tui.message(m3.group(0));
			} else if (m2.find()) { // Found we get one color
//				System.out.println("Found only one color!!");
				this.addColor(m2.group(2));	
				colorsInGame.add(m2.group(2));
				nrOfPlayer++;
				tui.message(m2.group(0));
			} else if (m4.find()) { // Keep track of shared colors, stays null if no shared color
				nrOfPlayer++;
				if (colorsInGame.contains(m4.group(3))) {
					sharedColor = m4.group(3);
					break;
				} else if (m4.group(4).length()!=0 && colorsInGame.contains(m4.group(4))) {
					sharedColor = m4.group(4);
					break;
				}
				colorsInGame.add(m4.group(3));
				if (m4.group(4).length()!=0) {
					colorsInGame.add(m4.group(4));
				}				
				
//				System.out.println("Found someone received a color");
//				for (String c : this.getColors()) {
//					Pattern p = Pattern.compile(c);
//					Matcher m = p.matcher(m4.group(0));
//					if (m.find()) {
//						sharedColor = c;
//					}
//				}
				tui.message(m4.group(0));
			} else if (m5.find()) { // Found turn command
				if (firstTurn) { // To create a player
//					System.out.println(m5.group(0));
					tui.message("The shared color is: " + getSharedColor());
					if (m5.group(2).equals(name)) {
						player = this.createPlayer(getSharedColor(), human, smart, tui, board, totalTime, true);
//						System.out.println("we have a SBASE " + player.getPiece(Game.COLOR5, Game.SBASE));
					} else {
						player = this.createPlayer(getSharedColor(), human, smart, tui, board, totalTime);
//						System.out.println("we have a SBASE " + player.getPiece(Game.COLOR5, Game.SBASE));
					}
					firstTurn = false;
					tui.printBoard(board);
				}
				if (m5.group(2).equals(name)) {
					boolean moveHasBeenMade = false;
					while (!moveHasBeenMade) {
						try {
							tui.message("It is your turn!");
							tui.message(player.printPieces());
							player.setMove();
							moveHasBeenMade = true;
//							System.out.println("Player has this many pieces: " + player.getAvailablePieces().size());
						} catch (ServerCommunicationException | InterruptedException | MoveNotPossibleException | NoMovePossibleException | InvalidInputException e) {
							this.handleError(e.getMessage());
						}
					}
//					tui.printBoard(board);
				}
			} else { // Here all other messages are just printed to the TUI
				this.handleError("server: " + line);
			}
			break;
		}
	}
	
	/**
	 * This method sets up a communication with the server, prepares for a new game, and listens for input from the server 
	 * (e.g. whose turn it is, what inputs are requested from the client and what moves have been made).
	 * It starts a TUI and initializes a client, board, player with the right pieces, and handles acknowledgements of
	 * sent commands. The method keeps running until the player has made clear it wants to disconnect via the TUI,
	 * or no communication with the server is possible anymore, or when another exception is thrown.
	 * @param sock socket connected to the server
	 * @param name username of the player
	 */
	/*@ requires sock != null;
	 * requires name != null;
	 * ensures client.getDisconnected() || Client.checkConnection(sock, client);
	 */
	public static void handleClientServerCommunication(Socket sock, String name) {
		// Initialize variables and objects
        
        /** String with the command received from the server */
        String line;
        
		try (Scanner in = new Scanner(sock.getInputStream())) {
			try (PrintWriter writer = new PrintWriter(sock.getOutputStream(), true)) {
				writer.println("extension");
				// Check whether there is still a connection with the server and waits for the scanner to receive a line
				if (Client.checkConnection(sock) && in.hasNextLine()) {
					// Initialisation
					
					line = in.nextLine(); // now you have the extensions
					System.out.println(line);
					writer.println("connect " + name);
					if (Client.checkConnection(sock) && in.hasNextLine()) {
						line = in.nextLine(); // receive connected
						System.out.println(line);
					
						Client client = new Client(writer, name);
						TUI tui = new TUI(client);
						client.addObserver(tui);
						client.human = tui.humanPlayer();
						client.smart = tui.smartStrategy();
						boolean validResponse = false;
						while (!validResponse) {
							try {
								client.totalTime = tui.totalTimeStrategy();
								client.howManyPlayers = tui.howManyPlayers();
								validResponse = true;
							} catch (InvalidInputException e) {
								client.handleError(e.getMessage());
							}
						}
						
						// Create a new thread to handle user input separate from the server inputs
						Runnable r = tui;
						Thread tt = new Thread(r);
						tt.start();
						
						
						
						while (!client.getDisconnected() && Client.checkConnection(sock, client)) {
							while (in.hasNextLine()) {
								line = in.nextLine();
								
//								if (client.waitForAck) {
//									client.handleAcknowledgement(line, tui);
//								}
								client.handleInput(line, tui);
//								System.out.println("Client disconnected: " + client.getDisconnected() + " checkConnection: " + Client.checkConnection(sock, client));
							}
						}
					} else {
						System.out.println("Something must have gone wrong. It is most likely that the connection has failed.");
					}
				} else {
					System.out.println("Something must have gone wrong. It is most likely that the connection has failed.");
				}
			}
		} catch (NumberFormatException | IOException e) {
			System.out.println(e.getMessage());
		}
	}
	
	// ----------------------- Queries ---------------------------
	
	/**
	 * Checks whether the connection with the server is still okay.
	 *
	 * @param socket socket of which the connection needs to be tested
	 * @return true if connection is still okay, false if the connection probably out
	 * @throws IOException Signals that an I/O exception has occurred.
	 */
	//@ requires socket != null;
	//@ pure
	public static boolean checkConnection(Socket socket) throws IOException {
		return socket.getInetAddress().isReachable(10000);
	}
	
	/**
	 * Checks whether the connection with the server is still okay. Lets the client object handle the message if no connection could be established
	 *
	 * @param socket socket of which the connection needs to be tested
	 * @param client which needs to handle the message if no connection could be made
	 * @return true if connection is still okay, false if the connection probably out
	 * @throws IOException Signals that an I/O exception has occurred.
	 */
	/*@ requires socket != null;
	 * requires client != null;
	 * pure
	 */
	public static boolean checkConnection(Socket socket, Client client) throws IOException {
		boolean result = socket.getInetAddress().isReachable(500);
		if (result == false) {
			client.handleError("No connection with the server");
		}
		return result;
	}
	
	/**
	 * Returns the player object currently playing the game via the client.
	 *
	 * @return player object
	 */
	/*@ pure
	 */
	public Player getPlayer() {
		return this.player;
	}
	
	/**
	 * Gets the board.
	 *
	 * @return the board
	 */
	public Board getBoard() {
		return this.board;
	}
	
	/**
	 * Query for the colors owned by the player.
	 *
	 * @return list of colors
	 */
	//@ pure
	public List<String> getColors() {
		return colors;
	}
	
	/**
	 * Get the state of the player.
	 *
	 * @return State type; either State.CONNECTED, State.JOINED, or State.INGAME
	 */
	//@ pure
	public State getPlayerState() {
		return this.state;
	}
	
	/**
	 * Query to check whether the client is waiting for an acknowledgement from the server.
	 *
	 * @return true if waiting for acknowledgement
	 */
	//@ pure
	public boolean getWaitForAck () {
		return waitForAck;
	}
	
	/**
	 * Check if the player has indicated it wants to disconnect from the server.
	 *
	 * @return true if the player wants to disconnect
	 */
	//@ pure
	public boolean getDisconnected() {
		return disconnected;
	}
	
	/**
	 * Returns the name of the player using the client.
	 *
	 * @return name of the player using the client
	 */
	/*@ \result != null;
	 * pure
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * Returns what kind of acknowledgement the client has received.
	 *
	 * @return the kind of acknowledgement the client has last received
	 */
	/*@ pure
	 */
	public Acknowledge getAck() {
		return acknowledge;
	}
	
	/**
	 * Method to get the shared color in the game.
	 *
	 * @return the shared color
	 */
	/*@ pure
	 */
	public String getSharedColor() {
		return sharedColor;
	}
	
	// --------------------- Main --------------------------------
	
	/**
	 * The main method.
	 *
	 * @param args the arguments
	 * @throws InterruptedException the interrupted exception
	 */
	/**
	 * @param args
	 * @throws InterruptedException
	 */
	public static void main(String[] args) throws InterruptedException {
		// 3 arguments should be given as input, otherwise this would be told the user and the client shuts down
		if (args.length != 3) {
            System.out.println(USAGE);
            System.exit(0);
        }

		/** The username */
        String name = args[0];
        /** The IP address of the server */
        InetAddress addr = null;
        /** The port number this client will connect to */
        int port = 0;
        /** The socket which will connect to the server */
        Socket sock = null;

        // check args[1] - the IP-address
        try {
            addr = InetAddress.getByName(args[1]);
        } catch (UnknownHostException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: host " + args[1] + " unknown");
            System.exit(0);
        }

        // parse args[2] - the port number
        try {
            port = Integer.parseInt(args[2]);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: port " + args[2]
            		           + " is not an integer");
            System.exit(0);
        }

        // try to open a Socket to the server
        try {
            sock = new Socket(addr, port);
            // Actually communicating with the server and playing the game
            handleClientServerCommunication(sock, name);
            System.out.print("Closing the socket. Enter 'disconnect' to close the client.");
            sock.close();
        } catch (IOException e) {
            System.out.println("ERROR: could not create a socket on " + addr
                    + " and port " + port);
        }       
	}
}
