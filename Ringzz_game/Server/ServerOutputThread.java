package Server;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.net.Socket;
import java.util.Arrays;
import java.util.List;
import java.util.Observable;
import java.util.Observer;
import java.util.regex.Pattern;

import Client.Controller.Client;
import Model.User;

// TODO: Auto-generated Javadoc
/**
 * The Class ServerOutputThread.
 */
public class ServerOutputThread implements Runnable, Observer {

	/** The user name. */
	private String userName;
	
	/** The socket. */
	private Socket socket;
	
	/** The server. */
	private Server server;
	
	/** The in stream. */
	private InputStream inStream;
	
	/** The out stream. */
	private OutputStream outStream;
	
	/** The out. */
	private PrintWriter out;
	
	/** The user. */
	private User user;
	
	/** The game. */
	private Game game;
	
	/** The move pattern. */
	private Pattern movePattern;
	
	/** The starting move pattern. */
	private Pattern startingMovePattern;
	
	/** The disconnect. */
	private boolean disconnect;
	
	/** The user IO. */
	private UserIO userIO;
	
	/** The exit. */
	private Boolean exit;
	
	/**
	 * Instantiates a new server output thread.
	 *
	 * @param server the server
	 * @param sockArg the sock arg
	 * @param userIO the user IO
	 */
	ServerOutputThread(Server server, Socket sockArg, UserIO userIO) {
		this.userIO = userIO;
		this.socket = sockArg;
		this.server = server;
		disconnect = false;
		exit = false;
		game =  null;
		try {
			outStream = socket.getOutputStream();
		} catch (IOException e) {
			e.printStackTrace();
		}
		out = new PrintWriter(outStream, true /* autoFlush */);
		
		movePattern = Pattern.compile("(move) (.+) (.+) (.+)");
		startingMovePattern = Pattern.compile("(move) (.+) (.+)");
		//Pattern turnPattern = Pattern.compile("(turn) (.+)");
		// Send all the users in the game to 
	}
	
	/**
	 * Prints the output.
	 *
	 * @param message the message
	 */
	public void printOutput(String message) {
		out.println(message);
	}
	
	/**
	 * Sets the user.
	 *
	 * @param user the new user
	 */
	public void setUser(User user) {
		this.user = user;
		System.out.println("Name of user in serveroutput: " + user.getName());
	}
	
	/**
	 * Sets the exit.
	 */
	public void setExit() {
		this.exit = true;
	}
	
	/**
	 * Sets the name.
	 *
	 * @param name the new name
	 */
	public void setName(String name) {
		this.userName = name;
	}
	
	/* (non-Javadoc)
	 * @see java.util.Observer#update(java.util.Observable, java.lang.Object)
	 */
	@Override
	public void update(Observable arg0, Object arg1) {
		String arg = ((String) arg1);
		List<String> argArray = Arrays.asList(arg.split("[\\s']"));
		switch (argArray.get(0)) {
			case "color":
				out.println(arg);
				out.flush();
				// Is this correct? Do you also print the username??
//				System.out.println("Gets to color");
//				String colorOutput = "";
//				boolean firstPass = true;
//				for (String s : argArray) {
//					if (s.equals("color") && !firstPass) {
//						//TODO
//						System.out.println(colorOutput);
//						out.println(colorOutput);
//						colorOutput = "color ";
//					} else {
//						colorOutput += s + " ";
//					}
//					firstPass = false;
//				}
				break;
		
			case "connected":
				out.println("connect "+argArray.get(1));
				break;
				
			case "error":
				if (argArray.get(2).equals(this.userName)) {
					out.println(argArray.get(0) + " " + argArray.get(1));
				}
				break;
				
			case "start":
				System.out.println("Start sent to " + userName);
				System.out.println("start");
				out.println("start");
				out.flush();
				System.out.print("It got past the print out");
				out.flush();
//				try {
//					Thread.sleep(1000);
//				} catch (InterruptedException e1) {
//					System.out.println(e1.getMessage());
//				}
				break;

			case "skipping":
				break;
				
			case "ready":
				//TODO
				System.out.println(argArray.get(1) +" ready");
				out.println("player " + argArray.get(1) +" ready");
				break;
				
			case "turn":
				out.println(argArray.get(0)+" "+argArray.get(1));
				break;
				
			case "move":
				out.println(argArray.get(0)+" "+argArray.get(1)+" "+argArray.get(2)+" "+argArray.get(3));
				break;
				
			case "player":
				out.println(argArray.get(0)+" "+argArray.get(1)+" "+argArray.get(2));
				break;
				
			case "gameover":
				out.println("gameover");
				System.out.println("sent gameover to " + user.getName());
				this.user.setNone();
				this.server.leaveLobby(this.user);
				System.out.println(user.getName() + " left the lobby");
				break;
				
			case "score":
				out.println(argArray.get(0) + " " + argArray.get(1) + " " + argArray.get(2));
				break;


//			case "score": 
//				while (argArray.size() >= 3) {
//					String scoreMessage = argArray.get(0) + " " + argArray.get(1) + " " + argArray.get(2);
//					out.println(scoreMessage);
//					argArray.remove(0); argArray.remove(0); argArray.remove(0); 
//				}
//				break;
			default:
				out.println(arg);
		}
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	@Override
	public void run() {
		while (!exit) {
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				System.out.println(e.getMessage());
			}
		}
		out.close();
		try {
			outStream.close();
		} catch (IOException e) {
			System.out.println(e.getMessage());
		}
		//TODO Set while loop
		//Sleep
	}

}
