package Test;

import static org.junit.Assert.fail;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import Exceptions.InvalidPlayerCountException;
import Model.User;
import Server.Game;
import Server.Server;

// TODO: Auto-generated Javadoc
/**
 * The Class ServerTest.
 */
class ServerTest {

	/** The server. */
	Server server;
	
	/** The user 6. */
	User user1, user2, user3, user4, user5, user6;
	
	/** The users. */
	List<User> users;
	
	/**
	 * Sets the up.
	 *
	 * @throws Exception the exception
	 */
	@BeforeEach
	void setUp() throws Exception {
        server = new Server(50000);
        user1 = new User("Brenda");
        user2 = new User("Marley");
        user3 = new User("Brenda");
        user4 = new User("Marley");
        user5 = new User("Brenda");
        user6 = new User("Marley");
        
        users = new ArrayList<>();
        users.add(user1);
        users.add(user2);
        users.add(user3);
        users.add(user4);

		server.getUsers().add(user1);
		server.getUsers().add(user2);
		server.getUsers().add(user3);
		server.getUsers().add(user4);
		server.getUsers().add(user5);
		server.getUsers().add(user6);
	}

	/**
	 * Test remove user.
	 */
	@Test
	void testRemoveUser() {
		assertTrue(server.getUsers().size() == 6);
		server.removeUser(user1);
		assertTrue(server.getUsers().size() == 5);
	}
	
	/**
	 * Test port needed.
	 */
	@Test
	void testPortNeeded() {
		Server.portNeeded();
	}
	
	/**
	 * Test player joined.
	 */
	@Test
	void testPlayerJoined() {
		server.playerJoined(user1);
	}
	
	/**
	 * Test to console.
	 */
	@Test
	void testToConsole() {
		server.toConsole("This is a pass");
	}
	
	/**
	 * Test join game.
	 */
	@Test
	void testJoinGame() {
		server.joinGame(user1);
		server.joinGame(user2);
		server.joinGame(user3);
		server.joinGame(user4);
		server.joinGame(user5);
		server.joinGame(user6);
	}
	
	/**
	 * Test ready.
	 */
	@Test
	void testReady() {
		
		server.joinGame(user1);
		server.joinGame(user2);
		server.joinGame(user3);
		server.joinGame(user4);
		server.joinGame(user5);
		server.joinGame(user6);
		try {
			server.userReady(user1);
			server.userReady(user2);
			server.userReady(user3);
			server.userReady(user4);
		} catch (NullPointerException e) {
			System.out.println(e.getMessage() + ": From acting on objects not instantiated");
		}
	}
	
	/**
	 * Test new thread.
	 */
	@Test 
	void testNewThread() {
		Game game = null;
		try {
			game = new Game(users);
		} catch (InvalidPlayerCountException e) {
			fail();
		}
		server.startNewThread(game);
	}
}
