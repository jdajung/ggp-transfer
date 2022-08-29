package org.ggp.base.player.gamer.statemachine.sample;

import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import javax.swing.border.TitledBorder;

import org.ggp.base.apps.player.config.ConfigPanel;
import org.ggp.base.apps.player.detail.DetailPanel;
import org.ggp.base.apps.player.match.MatchPanel;
import org.ggp.base.apps.player.network.NetworkPanel;
import org.ggp.base.player.GamePlayer;
import org.ggp.base.player.gamer.Gamer;
import org.ggp.base.util.reflection.ProjectSearcher;
import org.ggp.base.util.ui.NativeUI;

import com.google.common.collect.Lists;

@SuppressWarnings("serial")
public final class AutoPlayer extends JPanel
{
    private static void createAndShowGUI(AutoPlayer playerPanel)
    {
        JFrame frame = new JFrame("Game Player");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

        frame.setPreferredSize(new Dimension(1024, 768));
        frame.getContentPane().add(playerPanel);

        frame.pack();
        frame.setVisible(true);
    }

    public static void main(String[] args) throws IOException
    {
        NativeUI.setNativeUI();

        final AutoPlayer playerPanel = new AutoPlayer();
        javax.swing.SwingUtilities.invokeLater(new Runnable()
        {

            @Override
            public void run()
            {
                createAndShowGUI(playerPanel);
            }
        });




        //*************** Designate Players here ******************

        // for a TestGamer, these are the parameters in order.
        // USE_TRANSFER: boolean. If set to false, all forms of transfer are disabled, and agent becomes UCT.
        // USE_PLAY_TRANSFER: boolean. When true, transfer influences the action taken (A).
        // USE_SELECTION_TRANSFER: boolean. When true, transfer guides selection (S).
        // USE_ROLLOUT_TRANSFER: boolean. When true, transfer guides rollouts (R).
        // PLAY_TRANSFER_RATIO: double, range [0,1]. Determines the weighting of action influence (alpha).
        // SELECTION_TRANSFER_RATIO: double, range[0,1]. Determines the weighting of selection influence (beta).
        // SAVE_RULE_GRAPH_TO_FILE: boolean. When true, a copy of the game's rule graph will be saved to file as last_rule_graph.txt
        // SAVE_MCT_TO_FILE: boolean. When true, all nodes in the MCT with at least 2 visits will be saved to the directory given by MCT_SAVE_DIR in TestGamer.java
        // MCT_READ_DIR: String. Gives the location of the MCT archive to be read
        // EXPERIMENT_SAVE_DIR: String. When not empty, specifies a directory in which to save experiment data. For each game played, saves one file that specifies every state that was played, and adds a line to summary.txt
        //                      summary.txt contains one line for each game. The first number of each line is the amount of reward received by the agent that did the saving. The second number is the number of turns played. The remaining numbers indicate the final game state.

        //The current set of two players are UCT and SRA
        playerPanel.genPlayer("TestGamer", Arrays.asList(new Boolean(false), new Boolean(false), new Boolean(false), new Boolean(false), new Double(0.5), new Double(0.5), new Boolean(false), new Boolean(false), new String("MCTs"), new String("")));
        playerPanel.genPlayer("TestGamer", Arrays.asList(new Boolean(true), new Boolean(true), new Boolean(true), new Boolean(true), new Double(0.5), new Double(0.5), new Boolean(false), new Boolean(false), new String("MCTs/checkers"), new String("Experiments/000")));
//        playerPanel.genPlayer("RandomGamer", null);
    }

    private final JButton createButton;
    private final JTabbedPane playersTabbedPane;

    private final JTextField portTextField;

    private final JComboBox<String> typeComboBox;

    private Integer defaultPort = 9147;

    private List<Class<? extends Gamer>> gamers = Lists.newArrayList(ProjectSearcher.GAMERS.getConcreteClasses());

    public AutoPlayer()
    {
        super(new GridBagLayout());

        portTextField = new JTextField(defaultPort.toString());
        typeComboBox = new JComboBox<String>();
        createButton = new JButton(createButtonMethod());
        playersTabbedPane = new JTabbedPane();

        portTextField.setColumns(15);

        // Sort the list of gamers before displaying it to the user
        java.util.Collections.sort(gamers, new Comparator<Class<? extends Gamer>>() {
            @Override
            public int compare(Class<? extends Gamer> left, Class<? extends Gamer> right) {
                return left.getSimpleName().compareTo(right.getSimpleName());
            }
        });

        List<Class<? extends Gamer>> gamersCopy = new ArrayList<Class<? extends Gamer>>(gamers);
        for(Class<? extends Gamer> gamer : gamersCopy)
        {
            Gamer g;
            try {
                g = gamer.newInstance();
                typeComboBox.addItem(g.getName());
            } catch(Exception ex) {
//            	System.out.println(ex);
                gamers.remove(gamer);
            }
        }
        typeComboBox.setSelectedItem("Random");

        JPanel managerPanel = new JPanel(new GridBagLayout());
        managerPanel.setBorder(new TitledBorder("Manager"));

        managerPanel.add(new JLabel("Port:"), new GridBagConstraints(0, 0, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(20, 5, 5, 5), 5, 5));
        managerPanel.add(portTextField, new GridBagConstraints(1, 0, 1, 1, 1.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.HORIZONTAL, new Insets(20, 5, 5, 5), 5, 5));
        managerPanel.add(new JLabel("Type:"), new GridBagConstraints(0, 1, 1, 1, 0.0, 0.0, GridBagConstraints.EAST, GridBagConstraints.NONE, new Insets(5, 5, 5, 5), 5, 5));
        managerPanel.add(typeComboBox, new GridBagConstraints(1, 1, 1, 1, 1.0, 0.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
        managerPanel.add(createButton, new GridBagConstraints(1, 2, 1, 1, 1.0, 1.0, GridBagConstraints.SOUTH, GridBagConstraints.HORIZONTAL, new Insets(5, 5, 5, 5), 0, 0));

        JPanel playersPanel = new JPanel(new GridBagLayout());
        playersPanel.setBorder(new TitledBorder("Players"));

        playersPanel.add(playersTabbedPane, new GridBagConstraints(0, 0, 1, 1, 1.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));

        this.add(managerPanel, new GridBagConstraints(0, 0, 1, 1, 0.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
        this.add(playersPanel, new GridBagConstraints(1, 0, 1, 1, 1.0, 1.0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(5, 5, 5, 5), 5, 5));
    }

    public void genPlayer(String type, List<?> params) {
    	int port = Integer.valueOf(portTextField.getText());
    	int typeIndex = -1;
    	for(int i=0;i<gamers.size();i++) {
    		String fullName = gamers.get(i).getCanonicalName();
    		String shortName = fullName.substring(fullName.lastIndexOf(".") + 1);
//    		shortName = shortName.trim();
    		if(shortName.equals(type)) {
    			typeIndex = i;
    			break;
    		}
    	}

    	if(typeIndex != -1) {
	        MatchPanel matchPanel = new MatchPanel();
	        NetworkPanel networkPanel = new NetworkPanel();
	        DetailPanel detailPanel = null;
	        ConfigPanel configPanel = null;
	        Gamer gamer = null;

	        Class<?> gamerClass = gamers.get(typeIndex);
	        try {
	            gamer = (Gamer) gamerClass.newInstance();
	            if(type.equals("TestGamer") && params != null) {
	            	((TestGamer)gamer).initParams(params);
	            }
	        } catch(Exception ex) { throw new RuntimeException(ex); }
	        detailPanel = gamer.getDetailPanel();
	        configPanel = gamer.getConfigPanel();

	        gamer.addObserver(matchPanel);
	        gamer.addObserver(detailPanel);

	        GamePlayer player = null;
			try {
				player = new GamePlayer(port, gamer);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
	        player.addObserver(networkPanel);
	        player.start();

	        JTabbedPane tab = new JTabbedPane();
	        tab.addTab("Match", matchPanel);
	        tab.addTab("Network", networkPanel);
	        tab.addTab("Configuration", configPanel);
	        tab.addTab("Detail", detailPanel);
	        playersTabbedPane.addTab(type + " (" + player.getGamerPort() + ")", tab);
	        playersTabbedPane.setSelectedIndex(playersTabbedPane.getTabCount()-1);

	        defaultPort++;
	        portTextField.setText(defaultPort.toString());
    	} else {
    		System.out.println("ERROR: cannot generate player. Player type " + type + " not found.");
    	}
    }


    private AbstractAction createButtonMethod()
    {
        return new AbstractAction("Create")
        {

            @Override
            public void actionPerformed(ActionEvent evt)
            {
                try
                {
                    int port = Integer.valueOf(portTextField.getText());
                    String type = (String) typeComboBox.getSelectedItem();

                    MatchPanel matchPanel = new MatchPanel();
                    NetworkPanel networkPanel = new NetworkPanel();
                    DetailPanel detailPanel = null;
                    ConfigPanel configPanel = null;
                    Gamer gamer = null;

                    Class<?> gamerClass = gamers.get(typeComboBox.getSelectedIndex());
                    try {
                        gamer = (Gamer) gamerClass.newInstance();
                    } catch(Exception ex) { throw new RuntimeException(ex); }
                    detailPanel = gamer.getDetailPanel();
                    configPanel = gamer.getConfigPanel();

                    gamer.addObserver(matchPanel);
                    gamer.addObserver(detailPanel);

                    GamePlayer player = new GamePlayer(port, gamer);
                    player.addObserver(networkPanel);
                    player.start();

                    JTabbedPane tab = new JTabbedPane();
                    tab.addTab("Match", matchPanel);
                    tab.addTab("Network", networkPanel);
                    tab.addTab("Configuration", configPanel);
                    tab.addTab("Detail", detailPanel);
                    playersTabbedPane.addTab(type + " (" + player.getGamerPort() + ")", tab);
                    playersTabbedPane.setSelectedIndex(playersTabbedPane.getTabCount()-1);

                    defaultPort++;
                    portTextField.setText(defaultPort.toString());
                }
                catch (Exception e)
                {
                    e.printStackTrace();
                }
            }
        };
    }
}