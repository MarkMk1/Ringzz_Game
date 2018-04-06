package Client.View;

import java.util.Observable;
import java.util.Observer;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import Client.Controller.*;
import Exceptions.*;
import Model.Board;
import Server.Game;
// TODO: Auto-generated Javadoc
/**
 * The TUI object is a textual user interface. 
 * It listens to inputs from the user via the console, and interprets the command. 
 * Depending on the command, the TUI handles it itself or a method from the client is called. 
 * The TUI has various methods which can be called by other classes to ask for specific inputs from the user or 
 * to print certain strings to the console. 
 * TUI is also an observer, and prints messages as notified by the client.
 * @author Oskar
 */
public class TUI implements Observer, Runnable {
	
	/** The read move. */
	private boolean readMove;
	
	/** The disconnect. */
	private boolean disconnect;
	
	/** The smart. */
	private boolean smart;
	
	/** The move. */
	private String move;
	
	/** The client. */
	private Client client;
	
	/** The input. */
	private Scanner input;

	/**
	 * Constructor to create a new TUI object with a respective client.
	 *
	 * @param client client connected to this TUI
	 */
	public TUI(Client client) {
		this.client = client;
		readMove = false;
		input = new Scanner(System.in);
	}
	
//	/**
//	 * Handle scores to be printed in the console
//	 * @param scores to be shown to the user
//	 */
//	public void handleScores(String scores) {
//		System.out.println(scores);
//	}
	
	/**
 * Handle arbitrary messages to be printed to the console.
 *
 * @param text to be printed
 */
	public void message(String text) {
		System.out.println(text);
	}
	
	/**
	 * Method called by the client to ask the user whether he/she wants to play himself, or that a ComputerPlayer must be created.
	 *
	 * @return true if the user wants to play himself, and thus a HumanPlayer must be created by the Client
	 */
	public boolean humanPlayer() {
		System.out.println("Do you want to play yourself? y/n");
		while (input.hasNextLine()) {
			String answer = input.nextLine();
			if (answer.equals("y")) {
				return true;
			} else if (answer.equals("n")) {
				return false;
			} else {
				System.out.println("Please answer 'y' or 'n'");
			}
		}
		return false;
	}
	
	/**
	 * Method called by the client to ask from the user whether he/she wants a smart strategy (for the hints or the ComputerPlayer).
	 *
	 * @return true if the user wants a smart strategy
	 */
	public boolean smartStrategy() {
		System.out.println("Do you want a smart strategy? y/n");
		while (input.hasNextLine()) {
//			System.out.println("In the smart while loop!");
			String answer = input.nextLine();
			if (answer.equals("y")) {
				this.smart = true;
				return true;
			} else if (answer.equals("n")) {
				this.smart = false;
				return false;
			} else {
				System.out.println("Please answer 'y' or 'n'");
			}
		}
		this.smart = true;
		return true;
	}
	
	/**
	 * Method called by the client to ask from the user how much milliseconds the strategies are allowed to think.
	 *
	 * @return the milliseconds the user wants the strategy to think
	 * @throws InvalidInputException if not an integer was given
	 */
	public int totalTimeStrategy() throws InvalidInputException {
		int result;
		System.out.println("How many seconds is the strategy allowed to think about a move?");
		while (input.hasNextLine()) {
			String answer = input.nextLine();
			try {
				result = Integer.parseInt(answer);
				if (result <= 0) {
					throw new InvalidInputException("Please insert a positive value");
				}
			} catch (NumberFormatException e) {
			  throw new InvalidInputException("The total time should be an integer!");
			}
			return result*1000;
		}
		return 10; // Default is 10 seconds
	}
	
	/**
	 * Method called by the client to ask from the user how many players he wants to have in a game.
	 *
	 * @return the number of players to have in a game
	 * @throws InvalidInputException if not an integer was given between 1 and 5
	 */
	public int howManyPlayers() throws InvalidInputException {
		int result;
		System.out.println("How many players do you want in the game?");
		while (input.hasNextLine()) {
			String answer = input.nextLine();
			try {
				result = Integer.parseInt(answer);
				if (result <= 1 || result > 4) {
					throw new InvalidInputException("Please insert a positive value, with 1<x<5");
				}
			} catch (NumberFormatException e) {
			  throw new InvalidInputException("The number of players should be an integer!");
			}
			return result;
		}
		return 2; // Default is 2 players
	}
	
	/**
	 * A method when a Player object wants to read a move from the user.
	 * The handleCommand() method now allows for the move command to be given.
	 * If a valid move command has been given, this method is notified and returns the string to to the Player object
	 * @return string with a valid move command
	 */
	public String readMove() {
		System.out.println("Please make a move like this: move <ringtype> <color> <position>");
		synchronized (Client.lockTUI) {
			this.readMove = true;
		    try {
		    	Client.lockTUI.wait();
		    } catch(InterruptedException e) {
		    	System.out.print("An InterruptedException in the readMove()");
		    }
		}
		return move;
	}
	
	/**
	 * On changes in board, update will print to console.
	 *
	 * @param arg0 the arg 0
	 * @param arg1 the arg 1
	 */
	@Override
	public void update(Observable arg0, Object arg1) {
		System.out.println(arg1);
	}
	
	/**
	 * This method checks if the given String contains a valid move command.
	 *
	 * @param move the string containing the move command as given by the user
	 * @throws InvalidInputException if the user has given an invalid move command or if it is not his/her turn
	 */
	private void setMove(String move) throws InvalidInputException {
		if (!readMove) {
			throw new InvalidInputException("Sorry, but it is not your turn!");
		}
		
		String[] words = move.split("[\\s']");
		
		// Checking the ring type
		char type = words[1].charAt(0);
		switch(type) {
			case Game.SBASE:
				break;
			case Game.BASE:
				break;
			case Game.RING1:
				break;
			case Game.RING2:
				break;
			case Game.RING3:
				break;
			case Game.RING4:
				break;
			default:
				throw new InvalidInputException("Please fill in a valid ringtype character!");
		}
		
		// Checking the position
		try {
			int x = Integer.parseInt(words[3]);
			if (x<0 || x>24) {
				throw new InvalidInputException("Please pick an integer from 0 to 24 for the position");
			}
		  } catch (NumberFormatException e) {
			  throw new InvalidInputException("The position should be an integer!");
		  }

		// Checking the color
		switch(words[2]) {
			case Game.COLOR1:
				break;
			case Game.COLOR2:
				break;
			case Game.COLOR3:
				break;
			case Game.COLOR4:
				break;
			case Game.COLOR5:
				break;
			default:
				throw new InvalidInputException("Please fill in a valid color!");
		}
		
		readMove = false;
		this.move = move;
		synchronized(Client.lockTUI) {
			Client.lockTUI.notifyAll();	    						
		}
	}
	
	/**
	 * Method to handle inputs from the user.
	 *
	 * @param line string inserted by the user via the TUI
	 * @param m1 matcher for recognizing the move command
	 * @param m2 the m 2
	 * @throws InvalidInputException the invalid input exception
	 * @throws ServerCommunicationException the server communication exception
	 * @throws InterruptedException the interrupted exception
	 * @throws NoMovePossibleException the no move possible exception
	 */
	public void handleCommand(String line, Matcher m1, Matcher m2) throws InvalidInputException, ServerCommunicationException, InterruptedException, NoMovePossibleException {
		switch (line) {
		case "ready":
			client.ready();
			break;
		case "join":
			client.join();
			break;
		case "hint":
			if (client.getPlayer() != null) {
				System.out.println(client.getPlayer().hint(smart, readMove));
			} else {
				throw new InvalidInputException("You are not playing a game, so you cannot ask for a hint!");
			}
			break;
		case "move":
			System.out.println("Please 'move <ringtype> <color> <position>'");
		    break;
		case "leave":
			client.leave();
			if (readMove) {
				readMove = false;
				this.move = "quit";
				synchronized(Client.lockTUI) {
					Client.lockTUI.notifyAll();	    						
				}
			}
			break;
		case "disconnect":
			disconnect = true;
			client.disconnect();
			if (readMove) {
				readMove = false;
				this.move = "quit";
				synchronized(Client.lockTUI) {
					Client.lockTUI.notifyAll();	    						
				}
			}
			System.out.println("Press enter to leave");
			break;
//		case "help":
//			System.out.println("Sorry, can't help you");
//			break;
		default:
			if (m1.find()) { // If found a move command
				setMove(m1.group(0));
			} else if(m2.find()) {
				setMove(m2.group(0));
			} else {
				throw new InvalidInputException("Invalid command");
			}
		}
	}
	
	/**
	 * This method prints the current state of the board.
	 *
	 * @param board the board which is printed
	 */
	public void printBoard(Board board) {
		System.out.println(board);
	}

	/**
	 * This method listens to the user inputs from System.in, and handles exceptions by printing it to the console
	 */
	@Override
	public void run() {
		// Create a pattern object for certain commands
		String movePattern = "(move) (.+) (.+) (.+)";
		String moveSbasePattern = "(move) (S) (.+) (.+)";
        Pattern r1 = Pattern.compile(movePattern);
        Pattern r2 = Pattern.compile(moveSbasePattern);
		
        System.out.println("You can do the following things: 'join' (after which you can send 'ready' or 'leave') \n"
        		+ "'disconnect' \n"
        		+ "The piece types are: 1, 2, 3, 4, 5, B(ase), S(tarting base) \n"
        		+ "The positions are integers, where 0<= x <=24");
        
		String line = null;
		disconnect = false;

		// Listen for user inputs
		while (input.hasNextLine() && !disconnect) {
			line = input.nextLine();
			
			// Create a matcher object for the patterns of certain commands
	        Matcher m1 = r1.matcher(line);
	        Matcher m2 = r2.matcher(line);
	        
	        // Handle the user input
	        try {
				handleCommand(line, m1, m2);
			} catch (InvalidInputException | ServerCommunicationException | InterruptedException | NoMovePossibleException e) {
				System.out.println(e.getMessage());
			}
		}
//		input.close();
		System.out.println("Closing the TUI");
	}
}
