package Server;
import java.io.*;
import java.net.Socket;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import Client.Controller.Client;
import Exceptions.InvalidInputException;
import Exceptions.JoinException;
import Model.*;

// TODO: Auto-generated Javadoc
/**
 * The Class UserIO.
 */
public class UserIO implements Runnable {
	
	/** The user name. */
	private String userName;
	
	/** The socket. */
	private Socket socket;
	
	/** The server. */
	private Server server;
	
	/** The in stream. */
	private InputStream inStream;
	
	/** The user. */
	private User user;
	
	/** The game. */
	private Game game;
	
	/** The move pattern. */
	private Pattern movePattern;
	
	/** The starting move pattern. */
	private Pattern startingMovePattern;
	
	/** The disconnect. */
	private boolean disconnect = false;
	
	/** The server output. */
	private ServerOutputThread serverOutput;
	
	/** The game will start. */
	boolean gameWillStart = false;
	
	/** The Constant EXTENSIONS. */
	private static final String EXTENSIONS = "extension";
	
	/** The my turn. */
	boolean myTurn;
	
	/**
	 * Instantiates a new user IO.
	 *
	 * @param server the server
	 * @param sockArg the sock arg
	 */
	public UserIO(Server server, Socket sockArg) {
		this.socket = sockArg;
		this.server = server;
		newOutputThread();		
		try {
			inStream = socket.getInputStream();
		} catch (IOException e) {
			e.printStackTrace();
		}
		myTurn = false;
	}
	
	/**
	 * New output thread.
	 */
	public void newOutputThread() {
		serverOutput = new ServerOutputThread(server, socket, this);
		this.serverOutput = serverOutput;
		Thread outputThread = new Thread(serverOutput);
		outputThread.start();
	}
	
	/**
	 * Sets the turn.
	 */
	public void setTurn() {
		myTurn = true;
	}
	
	/**
	 * Sets the game.
	 *
	 * @param game the new game
	 */
	public void setGame(Game game) {
		this.game = game;
	}
	
	/**
	 * Gets the output thread.
	 *
	 * @return the output thread
	 */
	public ServerOutputThread getOutputThread() {
		return this.serverOutput;
	}
	
	/**
	 * Checks for game.
	 *
	 * @return true, if successful
	 */
	public boolean hasGame() {
		if (this.game.equals(null)) {
			return false;
		} else {
			return true;
		}
	}
	
	/**
	 * Check connection.
	 *
	 * @return true, if successful
	 */
	public boolean checkConnection() {
		try {
			return Client.checkConnection(socket);
		} catch (IOException e) {
			System.out.println(e.getMessage() + " - checkConnection IOException");
			return false;
		}
	}
	
	/**
	 * Handles user input and output.
	 */
	@Override
	public void run() {
		try (Scanner in = new Scanner(inStream)) {
			boolean disconnect = false;
			while (!disconnect && in.hasNextLine()) {
				String line = in.nextLine();
				Server.toConsole(line);

				List<String> lineArray = Arrays.asList(line.split("[\\s']"));
				switch (lineArray.get(0)) {
					case "extension":
						// As we have no extensions
						serverOutput.printOutput(UserIO.EXTENSIONS);
						break;
					case "connect":
						initialConnect(lineArray);
						serverOutput.setUser(user);
						break;
					case "disconnect":
						//Only prints to this client as joining hasn't been announced to other players yet.
						serverOutput.printOutput("disconnected " + this.userName);
						Server.toConsole(this.userName + " disconnected");
						server.leaveLobby(this.user);
						server.removeUser(this.user);
						this.close();
					case "join":
						if (user.isNone()) {
							server.joinGame(this.user);
							server.playerJoined(user);
							Server.toConsole(user.getName() + " joined");
						} else {
							serverOutput.printOutput("error joinError");
						}
						break;
					case "ready":
						if (user.isJoined()) {
							server.userReady(user);
							Server.toConsole(user.getName() + " readied");
						}
						break;
					case "leave":
						if (user.isPlaying() || user.isJoined() || user.isReady() ) {
								server.leaveLobby(user);
//								serverOutput.printOutput("player " + user.getName() + " left");
	//							server.clientLeftLobby(user);
						} else {
							//TODO send error message
						}
						break;
		    		default:
		    			if (myTurn) {
		    				Matcher moveMatcher = movePattern.matcher(line);
			    			
			    			if (moveMatcher.find()) { // Found a move command
								game.setCurrentMove(moveMatcher.group(0), this.user);
			    			}
			    			myTurn = false;
		    			} else { 
		    				// TODO!!!
							serverOutput.printOutput("error formattingError");
							throw new InvalidInputException("- invalid input given when extension, connect, and disconnect were only "
			    					+ "valid inputs"); // TODO where have this?
						}
						break;	    			
					}
		    			
				if (line.trim().equals("disconnect")) {
					disconnect = true;
				}
			}
		} catch (InvalidInputException e) {
			serverOutput.printOutput(e.getMessage());
		}
	}
	
	
	
	
	
	
	
	
	/**
	 * Initial connect.
	 *
	 * @param lineArray the line array
	 */
	private void initialConnect(List<String> lineArray) {
		if (lineArray.size() < 2) {
			this.errorOut(new InvalidInputException("connect command should not have more than username and password"));
		}
		this.userName = lineArray.get(1);
		this.user = new User(this.userName);
		this.serverOutput.setUser(user);
		this.serverOutput.setName(this.userName);
		user.setUserIO(this);
		server.addUser(user);
		for(User u : server.getUsers()) {
			if (!(u == this.user)) {
				serverOutput.printOutput("connect " + u.getName());
			}
		}
		System.out.println(user.getName() + " connected");
	}
	
	/**
	 * Gets the socket.
	 *
	 * @return the socket
	 */
	public Socket getSocket() {
		return socket;
	}
	
	/**
	 * Gets the server.
	 *
	 * @return the server
	 */
	public Server getServer() {
		return server;
	}
	
	/**
	 * Close.
	 */
	public void close() {
		disconnect = true;
		serverOutput.setExit();
		try {
			Thread.sleep(5000);
			inStream.close();
			socket.close();
		} catch (IOException | InterruptedException e) {
			System.out.println(e.getMessage());;
		}
	}	
	
	/**
	 * Error out.
	 *
	 * @param exception the exception
	 */
	public void errorOut(Exception exception) {
		if (exception instanceof InvalidInputException) {
			serverOutput.printOutput("error "+ "invalidMoveError" );
		}
	}

}
