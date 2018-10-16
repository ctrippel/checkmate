/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/* MainClass.java
 * 
 * This is a wrapper that was repurposed from some example Alloy API code by Lustig
 * et al.: (https://github.com/NVlabs/litmustestgen). We again slighly modified
 * this wrapper for use in CheckMate.
 *
 * This program takes in an Alloy uspec model (-f uspecmodelname.als), and the name
 * of a run statement (or multiple run statements) to generate instances (i.e.,
 * satisfying uhb graphs). It will continue generating instances until there are
 * none remaining or until it has reached the user-provided limit. This program
 * prints each instance to stdout. Redirect the output from this program to a file
 * for parsing and filtering by CheckMate's analysis scripts.
 */

//package AlloyAnalyzer.dist.edu.mit.csail.sdg.alloy4whole;
package edu.mit.csail.sdg.alloy4whole;

import java.util.*;
import java.io.PrintWriter;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

/** This class demonstrates how to access Alloy4 via the compiler methods. */

public final class MainClass {
    public static void print_usage() {
        System.err.println("Usage:");
        System.err.println("    <program_name> <options> [{<commands_to_run>}]");
        System.err.println("");
        System.err.println("Options:");
        System.err.println("    -h");
        System.err.println("        Print this and exit");
        System.err.println("    -f <filename>");
        System.err.println("        Filename of Alloy model to run");
        System.err.println("        REQUIRED");
        System.err.println("    -b <bound>");
        System.err.println("        Change the default scope bound.");
        System.err.println("        If value is 0, then the bound defaults to whatever is specified in the Alloy file");
        System.err.println("        Optional, default value = 0");
        System.err.println("    -n <num_instances>");
        System.err.println("        Maximum number of instances to generate for each command.");
        System.err.println("        If value is 0, then all instances are generated.");
        System.err.println("        Optional, default value = 0");
        System.err.println("");
        System.err.println("If no commands to run are included, then all valid command names are printed for the given filename.");
    }

    /*
     * Executes commands in a given Alloy model file.
     *
     * This method parses the file given as the first argument, then executes the commands given in subsequent command line arguments.
     * If no other command line arguments are given, all commands are run.
     *
     * If there are syntax or type errors, it may throw
     * a ErrorSyntax or ErrorType or ErrorAPI or ErrorFatal exception.
     * You should catch them and display them,
     * and they may contain filename/line/column information.
     */
    public static void main(String[] args) throws Err {
        // command line argument parsing
        String filename = "";
        int num_instances_to_gen = 0;
        int bound_override = 0;
        List<String> commands = new ArrayList<String>();
        for (int i = 0 ; i < args.length ; i ++) {
            if (args[i].equals("-f") || args[i].equals("--file")) {
                i++;
                if (i >= args.length) {
                    System.err.println("ERROR: Expected file name after " + args[i-1]);
                    print_usage();
                    System.exit(1);
                } else {
                    filename = args[i];
                }
            } else if (args[i].equals("-n")) {
                i++;
                if (i >= args.length) {
                    System.err.println("ERROR: Expected number after " + args[i-1]);
                    print_usage();
                    System.exit(1);
                } else {
                    try {
                        num_instances_to_gen = Integer.parseInt(args[i]);
                    } catch (NumberFormatException e) {
                        System.err.println("ERROR: Expected integer after " + args[i-1]);
                        print_usage();
                        System.exit(1);
                    }
                }
            } else if (args[i].equals("-b")) {
                i++;
                if (i >= args.length) {
                    System.err.println("ERROR: Expected number after " + args[i-1]);
                    print_usage();
                    System.exit(1);
                } else {
                    try {
                        bound_override = Integer.parseInt(args[i]);
                    } catch (NumberFormatException e) {
                        System.err.println("ERROR: Expected integer after " + args[i-1]);
                        print_usage();
                        System.exit(1);
                    }
                }
            } else {
                // assume it is an alloy run command
                commands.add(args[i]);
            }
        }
        // validate command line arguments
        if (filename.equals("")) {
            System.err.println("ERROR: Filename required");
            print_usage();
            System.exit(1);
        }
        if (num_instances_to_gen < 0) {
            System.err.println("ERROR: Negative number of instances to generate not allowed");
            print_usage();
            System.exit(1);
        }
        if (bound_override < 0) {
            System.err.println("ERROR: Negative scope bound.");
            print_usage();
            System.exit(1);
        }

        // Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.err.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.err.flush();
            }
        };
        
        // Parse+typecheck the model
        Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

        // Choose some default options for how you want to execute the commands
        A4Options options = new A4Options();

        // This requires 32-bit java in windows
        //options.solver = A4Options.SatSolver.MiniSatJNI;

        if (commands.size() == 0) {
            // If there are no commands specified, print all commands
            System.err.println("No commands specified. List of all available commands:");
            for (Command command: world.getAllCommands()) {
                System.err.println("  " + command.label);
            }
        } else {
            // If there are specified commands, run them
            for (String req_command : commands) {
                boolean command_found = false;
                // System.err.println("Looking for \"" + args[i] + "\"");
                for (Command command: world.getAllCommands()) {
                    // System.err.println("    Candidate: " + command.label);
                    if (command.label.equals(req_command)) {
                        System.err.println("  Command match: " + command.label);
                        System.out.println("<command label=\"" + filename + ":" + command.label + "\">");
                        command_found = true;

                        if (bound_override > 0) {
                          System.err.println("Scope bound " + bound_override + " overrides default bound of " + command.overall);
                          command = new Command(
                              command.pos,
                              command.label,
                              command.check,
                              bound_override, // <--
                              command.bitwidth,
                              command.maxseq,
                              command.expects,
                              command.scope,
                              command.additionalExactScopes,
                              command.formula,
                              command.parent);
                        } else {
                          //System.err.println("Scope bound: " + command.overall);
                        }

                        // Execute the command
                        long tStart_all = System.currentTimeMillis();
                        long tStart_one = System.currentTimeMillis();

                        long tEnd_one = System.currentTimeMillis();

                        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
                        // Print the outcome
                        int num_instances = 0;
                        if(ans.satisfiable()) {
                            num_instances = 0;
                            do {
                                // Print the outcome
                                System.out.println(ans);
                                System.out.println("---END INSTANCE---\n");
                                ans = ans.next();
                                if (num_instances == 0) {
                                  tEnd_one = System.currentTimeMillis();
                                }
                                num_instances++;
                            }
                            while(ans.satisfiable() && (num_instances_to_gen == 0 || num_instances < num_instances_to_gen));
                        }
                        long tEnd_all = System.currentTimeMillis();

                        long tDelta_all = tEnd_all - tStart_all; 
                        long tDelta_one = tEnd_one - tStart_one;

                        double elapsedSeconds_all = tDelta_all / 1000.0;
                        double elapsedSeconds_one = tDelta_one / 1000.0;

                        System.out.println("</command>");
                        System.out.println("Time to gen 1 (min): " + Double.toString(elapsedSeconds_one / 60.0)); 
                        System.out.println("Time to gen " + Integer.toString(num_instances) + " (min): " + Double.toString(elapsedSeconds_all / 60.0 )); 
                        
                    }
                }
                if (!command_found) {
                    System.err.println("ERROR! command \"" + req_command + "\" not found. List of all available commands:");
                    for (Command command: world.getAllCommands()) {
                        System.err.println("  " + command.label);
                    }
                    System.exit(1);
                }
            }
        }
    }
}

