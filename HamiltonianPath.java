import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.*;


/**
 * Created by Martin Polacek on 17/11/2016.
 *
 * This code creates the SAT instance for a given un-oriented graph
 *
 * Input:
 * line 1: number_of_vertices number_of_edges
 * lines 2 - number_of_edges: vertex_i vertex_j
 *
 * NOTE: the numbering of vertices is 1-based.
 *
 * Output:
 * line 1: number_of_bool_variables number_of_clauses
 * lines 1-... :  SAT clauses in CNF (conjunctive normal form)
 *
 * you can solve the SAT instance for example using: https://www.msoos.org/2013/09/minisat-in-your-browser/
 */

public class HamiltonianPath {

    /* static fields */

    // counter wil held the over-all number of variables used it goes form 1, because 0 is reserved
    private static int M;

    // N is the overall number of vertices
    private static int N;

    // the overall ID number
    private static int ID = 1;

    /* non-static fields */

    // create the global ID holders, that will be unique for each vertex function x_{ik}
    private Integer[][] x;

    // edge functions
    private HashMap<Edge, Integer> y;

    // vertex --> set of vertices
    private HashMap<Integer, LinkedList<Integer>> edges;

    // anti_edges := the graph complement to the full graph
    private HashSet<Edge> anti_edges;

    private final InputReader reader;

    // printing stack/linked list
    private LinkedList<String> print;

    /* Constructors */
    
    HamiltonianPath(InputReader reader){

        this.reader = reader;
        this.y = new HashMap<>();
        this.edges = new HashMap<>();
        this.print = new LinkedList<>();
        this.anti_edges = new HashSet<>();
    }


    /* INNER CLASSES */

    // class Input Reader
    static class InputReader {
        public BufferedReader reader;
        public StringTokenizer tokenizer;

        public InputReader(InputStream stream) {
            reader = new BufferedReader(new InputStreamReader(stream), 32768);
            tokenizer = null;
        }

        public String next() {
            while (tokenizer == null || !tokenizer.hasMoreTokens()) {
                try {
                    tokenizer = new StringTokenizer(reader.readLine());
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            }
            return tokenizer.nextToken();
        }

        public int nextInt() {
            return Integer.parseInt(next());
        }

        public double nextDouble() {
            return Double.parseDouble(next());
        }

        public long nextLong() {
            return Long.parseLong(next());
        }
    }

    // class Edge
    class Edge{

        int[] a;

        /* constructor */
        private Edge(int a, int b){
            this.a = new int[2];

            this.a[0] = a;
            this.a[1] = b;
        }

        private int[] getValue(){
            return this.a;
        }

        @Override
        public boolean equals(Object o) {
            if ((o instanceof Edge) && (((Edge) o).getValue()[0] == this.a[0]) &&
                    (((Edge) o).getValue()[1] == this.a[1])) {
                return true;
            } else {
                return false;
            }
        }
        /* this looks a bit dangerous but ok */
        @Override
        public int hashCode() {
                /* final int prime = 31;
                int result = 1;
                result = prime * result + (this.a == null ? 0 : this.a.hashCode());
                return result;
                */
            return 31;
        }

    }

    /* METHODS */

    /* axioms */
    private void axiomA(){
        StringBuilder temp;
        this.createAntiEdges();

        for(int k = 0; k<HamiltonianPath.N-1; k++) {
            for (Edge edo : this.anti_edges) {
                temp = new StringBuilder();

                temp.append(-this.x[edo.getValue()[0]][k]);
                temp.append(" ");
                temp.append(-this.x[edo.getValue()[1]][(k + 1)]);
                temp.append(" 0");

                this.print.add(temp.toString());

                temp = new StringBuilder();

                temp.append(-this.x[edo.getValue()[1]][k]);
                temp.append(" ");
                temp.append(-this.x[edo.getValue()[0]][(k + 1)]);
                temp.append(" 0");

                this.print.add(temp.toString());
            }
        }
    }

    private void axiomI(){
        StringBuilder temp;
        // now lets try only the Path
        for(int j = 0; j<HamiltonianPath.N; j++){
            temp = new StringBuilder();
            for(int i = 0; i<HamiltonianPath.N; i++){
                temp.append(this.x[j][i]);
                temp.append(" ");
            }
            temp.append(0);
            this.print.add(temp.toString());
        }

        // x_i 1 V x_i 2 V x_ i 3 ... (- x_ i 1 - x_i 2 ) (-x_i 1 -x_i 3)...
        for(int i = 0; i<HamiltonianPath.N; i++){
            for(int j = 0; j<HamiltonianPath.N;j++){
                for(int k = j+1; k<HamiltonianPath.N; k++){
                    temp = new StringBuilder();
                    temp.append(-this.x[i][j]);
                    temp.append(" ");

                    temp.append(-this.x[i][k]);
                    temp.append(" 0");
                    this.print.add(temp.toString());
                }
            }
        }
    }

    private void axiomII(){
        StringBuilder temp;
        for(int k = 0; k<HamiltonianPath.N; k++){
            temp = new StringBuilder();
            for(int i = 0; i<HamiltonianPath.N; i++){
                temp.append(this.x[i][k]);
                temp.append(" ");
            }
            temp.append(0);
            this.print.add(temp.toString());
        }

        for(int k = 0; k<HamiltonianPath.N; k++){
            for(int i = 0; i<HamiltonianPath.N;i++){
                for(int s = i + 1; s<HamiltonianPath.N; s++){

                    temp = new StringBuilder();
                    temp.append(-this.x[i][k]);
                    temp.append(" ");
                    temp.append(-this.x[s][k]);
                    temp.append(" 0");
                    this.print.add(temp.toString());
                }
            }
        }
    }

    /* helpful methods */
    private void fillX(){
        for(int i =0; i<HamiltonianPath.N ; i++){
            for(int j = 0; j<HamiltonianPath.N; j++){
                this.x[i][j] = HamiltonianPath.ID;
                HamiltonianPath.ID++;
            }
        }
    }

    private void createAntiEdges(){
        Edge anti_edge;
        for(int i = 0; i<HamiltonianPath.N; i++){
            for(int j = i+1; j<HamiltonianPath.N; j++){
                anti_edge = new Edge(i,j);

                if(!this.y.containsKey(anti_edge)){
                    this.anti_edges.add(anti_edge);
                }

            }
        }
    }

    private void fillEdges(){
        LinkedList<Integer> temp;

        for(int i = 0; i<HamiltonianPath.N; i++){
            temp = new LinkedList<>();
            this.edges.put(i,temp);
        }
    }

    private void addEdge(int start, int stop){
        //System.out.println(start);
        this.edges.get(start).push(stop);
        //System.out.println(stop);
        this.edges.get(stop).push(start);

        Edge temp = new Edge(start, stop);
        Edge temp2 =  new Edge(stop, start);

        //System.out.println("temp[0] " + start);
        //System.out.println("temp[1] " + stop);

        // assigning the unique ID to Edge functions:
        this.y.put(temp,HamiltonianPath.ID);
        this.y.put(temp2,HamiltonianPath.ID);

        HamiltonianPath.ID++;
    }

    private void print(){
        //System.out.println("print method unfinished!!!!");

        /* axioms */
        this.axiomI();
        this.axiomII();
        //this.axiomIII();
        //this.axiomIV();
        this.axiomA();

        /* how many variables and clauses */
        System.out.println( (HamiltonianPath.ID-1) + " " + this.print.size());


        /* print statements */
        this.print.forEach((x) -> System.out.println(x));
    }

    public void run() {

        // read real number of vertices first
        HamiltonianPath.N = reader.nextInt();

        //HamiltonianPath.counter = N;

        // read real number of edges first
        HamiltonianPath.M = reader.nextInt();

        // the x will hold vertices and their Ham. path positions
        this.x = new Integer[HamiltonianPath.N][HamiltonianPath.N];
        this.fillX();

        // filling the edges with empty linked lists:
        this.fillEdges();

        // adding real edges:
        for (int i = 0; i < M; i++) {

            int start = reader.nextInt()-1;
            int stop = reader.nextInt()-1;
            //System.out.println("start is "+ start + " stop is " + stop);
            this.addEdge(start,stop);
        }

    }


    /* main method */
    public static void main(String[] args){

        InputReader reader = new InputReader(System.in);
        HamiltonianPath g = new HamiltonianPath(reader);
        g.run();
        g.print();
    }
}
