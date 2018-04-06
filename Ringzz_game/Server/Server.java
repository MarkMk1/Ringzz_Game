package Server;

import java.io.IOException;
import java.net.BindException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.*;

import Client.Controller.Client;
import Exceptions.InvalidPlayerCountException;
import Model.*;

// TODO: Auto-generated Javadoc
/**
 * The Class Server.
 */
public class Server extends Observable implements Runnable {
	
	/**  Port at which the server is connected. */
	private final int port; // Do we need this?
	
	/**  List of users connected to this server. */
	private List<User> users = new ArrayList<>();
	
	/**  A list which keeps track of which users have joined a game. */
	private List<List<User>> lobby = new ArrayList<>();
	
	/** The games. */
	private Map<Game, List<User>> games = new HashMap<>();
	
	/**
	 * Instantiates a new server.
	 *
	 * @param port the port
	 */
	public Server(int port) {
		this.port = port;
		users = new ArrayList<>();
		lobby = new ArrayList<>();
		List<User> newLobbyList = new ArrayList<>();
		lobby.add(newLobbyList);
	}
	
	/**
	 * Port needed.
	 *
	 * @return the int
	 */
	public static int portNeeded() {
		Scanner input = new Scanner(System.in);
		String answer = input.nextLine();
		try {
		return Integer.parseInt(answer);
		} catch (NumberFormatException e) {
			System.out.println("Invalid port number, please try again:");
			portNeeded();
		}
		return 0;
	}

	/**
	 * The main method.
	 *
	 * @param args the arguments
	 */
	public static void main(String[] args) {	
		
		if (args.length != 1) {
            System.out.println("Fill out the port number!");
            System.exit(0);
        }

		int portnr = 0;
        InetAddress address;
        ServerSocket sock = null;
        Socket incoming = null;
        
        System.out.println("Setting up a server");
        
        try {
        	address = InetAddress.getLocalHost();
        	System.out.println("IP address of this server is " + address);
        } catch(UnknownHostException e) {
        	System.out.println(e.getMessage());
        }
        
        try {
            portnr = Integer.parseInt(args[0]);
        } catch (NumberFormatException e) {
            System.out.println("ERROR: port " + args[0]
            		           + " is not an integer");
            System.exit(0);
        }
        
        // Start the run method of this server
        Server server = new Server(portnr);
        Runnable r1 = server;
		Thread t1 = new Thread(r1);
		t1.start();
        
		// Connect to clients
    	try {
        	try {
    		sock = new ServerSocket(portnr);
        	} catch(BindException e) {
        		System.out.println("Need another port, experienced BindException");
        		System.out.println("\nPlease enter port:");
         		portnr = Server.portNeeded();
        		sock = new ServerSocket(portnr);
         	} 
        	
        	while(true) {
        		try {
    				incoming = sock.accept();
    				//TODO
    				System.out.println("Someone accessed the server");
    			} catch (IOException e) {
    				System.out.println(e.getMessage() + " - occured while accepting connections to 'sock'");
    			}
        		UserIO userIO = new UserIO(server, incoming);
        		server.addObserver(userIO.getOutputThread());
        		
        		Runnable r2 = userIO;
        		Thread t2 = new Thread(r2);
        		t2.start();
    		}
        	//sock.close();
    	} catch(IOException e1) {
    		System.out.println(e1.getMessage());
    	}    		
//        		sock.close();
	}
	
	/**
	 * This method adds a user to the list of users connected to the server,
	 * and notifies all connected users a new user has been added.
	 * @param user which should be added to the list.
	 */
	public void addUser(User user) {
		users.add(user);
		
		setChanged();
        notifyObservers("connected " + user.getName());
        this.addObserver(user.getUserIO().getOutputThread());
//        System.out.println(users.get(0).getName() + " name from server's addUser");
	}
	
	
	
	/**
	 * Removes the user.
	 *
	 * @param user the user
	 */
	public void removeUser(User user) {
		users.remove(user);
	}
	
	/**
	 * Gets the users.
	 *
	 * @return the users
	 */
	public List<User> getUsers() {
		return this.users;
	}
	
	/**
	 * This method adds a user to a waiting list with players who have joined a game.
	 * If the game is already full (4 users), a new list will be created.
	 * @param user to add to a waiting list to play a game
	 */
	//May have to consider adding/removing players from the general users list. Doubt it. 
	public void joinGame(User user) {
		user.setJoined();
		boolean createNewGame = false;
		if (lobby.isEmpty()) {
			createNewGame = true;
		} else {
			for (List<User> e : lobby) {
				if (e.size() < 4) {
					if (e.size() > 0) {
						if (!e.get(0).isPlaying()) {
							e.add(user);
						} else {
							createNewGame = true;
						}
					} else {
						e.add(user);
					}
				} else {
				createNewGame = true;
				}
			}
		}
		
		
		if (createNewGame) {
			List<User> newLobbyList = new ArrayList<User>();
			newLobbyList.add(user);
			this.lobby.add(newLobbyList);
			createNewGame = false;
			System.out.println("A new lobby is created");
		}

	}
	
	/**
	 * Player joined.
	 *
	 * @param user the user
	 */
	public void playerJoined(User user) {
		setChanged();
		notifyObservers("player " + user.getName() + " joined");
	}
	
	/**
	 * To console.
	 *
	 * @param message the message
	 */
	public static void toConsole(String message) {
		System.out.println(message);
	}
	
	/**
	 * A user's state is set to ready and it is checked whether a new game should be started;
	 * which is the case if all the users who have joined that game are ready.
	 * @param user is set to ready
	 */
	public void userReady(User user) {
		user.setReady();
		
		for (List<User> e : lobby) {
			if (e.contains(user)) {
				boolean userReady = true;
				for (User u : e) {
//					try {
//						if (Client.checkConnection(u.getUserIO().getSocket())) {
//							this.clientDisconnect(u);
//							continue;
//						}
//					} catch (IOException e1) {
//						System.out.println(e1.getMessage());
//					}
					if (u.isReady() == false) {
						userReady = false;
					}
				}
				if (userReady == true && e.size() >= 2) {
					try {
						Runnable theGame = new Game(e);
						games.put((Game) theGame, e);
						for (User u : e) {
							u.setPlaying();
							((Game) theGame).addObserver(u.getUserIO().getOutputThread());
							u.getUserIO().setGame((Game) theGame);
						}
						startNewThread((Game)theGame);						
					} catch (InvalidPlayerCountException e1) {
						System.out.println(e1.getMessage());
					}
				}
				break;
			}
		}
		setChanged();
		notifyObservers("ready "+user.getName());
	}
	
	/**
	 * Start new thread.
	 *
	 * @param game the game
	 */
	public void startNewThread(Game game) {
		Thread gameThread = new Thread(game);
		gameThread.start();
		System.out.println("got to thread start");
	}
	
	/**
	 * Leave lobby.
	 *
	 * @param user the user
	 */
	public void leaveLobby(User user) {
		Game removeGame = null;
		if (user.isPlaying()) {
			for (Game g : getGames()) {
				for (User u : g.gamePlayers()) {
					if (u == user) {
						removeGame = g;
					}
				}
			}
			if (removeGame != null) {
//				removeGame.deleteObserver(user.getUserIO().getOutputThread());
				removeGame.endGame(user.getName());
				games.remove(removeGame);
			}
		} else {
			System.out.println("toLobby" + user.getName());
			user.setNone();
			System.out.println("user cleaned" + user.getName());
			List<User> removeLobby = null;
			List<User> listToRemoveUser = null;
			User userToRemove = null;
			
			outerloop:
			for (List<User> l : lobby) {
				for (User u : l) {
					System.out.println("cycles through lobby lists" + user.getName());
					if (u == user) {
						System.out.println("finds user in lobby list" + user.getName());
						userToRemove = u;
						listToRemoveUser = l;
						if (l.isEmpty()) {
							removeLobby = l;
						}
						break outerloop;
					}
				}
			}
			if (listToRemoveUser != null) {
				listToRemoveUser.remove(userToRemove);
			}
			
			if (removeLobby != null) {
				lobby.remove(removeLobby);
			}
			user.clean();
			setChanged();
			notifyObservers("player " + user.getName() + " left");
			System.out.println("player " + user.getName() + " left");
		}
	}
	
	/**
	 * Gets the games.
	 *
	 * @return the games
	 */
	public Set<Game> getGames() {
		return games.keySet();
	}
	
//	public void clientLeftLobby(User user) {
//		for (List<User> e : lobby) {
//			System.out.println("gets to lobby loop");
//			if (e.contains(user)) {
//				System.out.println("finds user in a lobby list");
//				e.remove(user);
//				if (!e.isEmpty()) {
//					System.out.println("list is still not empty");
//					for (Game g : games.keySet()) {
//						System.out.println("finds a game in games keyset");
//						for (User u : g.gamePlayers()) {
//							System.out.println("finds a user in gamePlayers()");
//							if (u == user) {
//								System.out.println("finds the appropriate user");
//								g.endGame(user.getName());
//							}
//						}
//					}
//				}
//			}
//		}
//	}
	
	/**
 * Client disconnect.
 *
 * @param user the user
 */
public void clientDisconnect(User user) {
		for (List<User> e : lobby) {
			if (e.contains(user)) {
				e.remove(user);
				if (!e.isEmpty()) {
					for (Game g : games.keySet()) {
						for (User u : g.gamePlayers()) {
							if (u == user) {
								g.endGame();
							}
						}
					}
				}
			}
		}
		user.getUserIO().close();
		user.clean();
		users.remove(user);
		setChanged();
		notifyObservers("player "+user.getName()+" disconnected");	
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	// Maybe not necessary
	@Override
	public void run() {
		
	}
}
