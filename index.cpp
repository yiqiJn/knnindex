#include<cstdio>
#include<cstring>
#include<iostream>
#include<fstream>
#include<cstdlib>
#include<vector>
#include<set>
#include<map>
#include<queue>
#include<algorithm>
#include<ctime>
using namespace std;

clock_t ct;
int cnt, tree_width = 0;
const int INF = 999999999;

// initialize graph data
struct Graph{
    int n, m;
    vector<int> V;
    vector<map<int,int>> E;
    vector<vector<pair<int,int>>> Edge;
    vector<int> D;
    Graph(){
        n = m = 0;
        V.clear();
        E.clear();
    }
    Graph(char *file){
        //    cout << "file:" << file << endl;
        Graph();
        FILE *fin = fopen(file, "r");
        fscanf(fin, "%d", &n);
        fscanf(fin, "%d", &m);
        //    printf("n m: %d %d\n", n, m);
        
        //initialize E
        for (int i = 0; i <= n; i++){
            map<int, int> v;
            v.clear();
            E.push_back(v);
        }

        for (int i = 0; i < m; i++){
            int x, y, z = 0;
            fscanf(fin, "%d%d%d", &x, &y, &z);
            //printf("x y z: %d %d %d\n", x, y, z);
            if (x > n || y > n)
                continue;
            //update the weight of edge <x,y> to make w(x,y) is minimized
            if (E[x].find(y) != E[x].end()){
                if (E[x][y] > z){
                    E[x][y] = z;
                    E[y][x] = z;
                }
            }
            else{
                E[x].insert(make_pair(y, z));
                E[y].insert(make_pair(x, z));
            }
        }
        D.clear();
        D.push_back(0);
        for (int i = 1; i <= n; i++)
            D.push_back(E[i].size());
    }

    void EdgeInitialize(){
        Edge.clear();
        for (int i = 0; i <= n; i++){
            vector<pair<int, int>> Ed;
            Ed.clear();
            for (map<int, int>::iterator it = E[i].begin(); it != E[i].end(); it++){
                Ed.push_back(*it);
            }
            Edge.push_back(Ed);
        }
    }

    bool isEdgeExist(int u, int v){
        if (E[u].find(v) == E[u].end())
            return false;
        else return true;
    }

    void insertEdge(int u, int v, int k){
        if (E[u].find(v) != E[u].end()) return;
        E[u].insert(make_pair(v, k));
        E[v].insert(make_pair(u, k));
        D[u]++;
        D[v]++;
    }
    
    void deleteEdge(int u, int v){
        if (E[u].find(v) == E[u].end()) return;
        E[u].erase(E[u].find(v));
        E[v].erase(E[v].find(u));
        D[u]--;
        D[v]--;
    }
};

int *DD, *DD2, *NUM;
int *_DD, *_DD2;
bool *changed;

struct SelEle{
    int x;
    SelEle();
    SelEle(int _x){
        x = _x;
    }
    bool operator < (const SelEle se)const{
        if (DD[x] != DD[se.x])
            return DD[x] < DD[se.x];
        if (DD2[x] != DD2[se.x])
            return DD2[x] < DD2[se.x];
        return x < se.x;
    }
};

struct Node{
    vector<int> VL, KVL, pv, pvd, kfvd, kpv, kpvd;
    vector<int> vert, kfv;
    //, pos, pos2, dis
    //new code
    map<int,int> v_d;

    vector<int> ch;

    int height;
    int pa;
    int uniqueVertex;
    Node(){
        vert.clear();
        VL.clear();
        KVL.clear();
        kfv.clear();
        kfvd.clear();
        kpv.clear();
        kpvd.clear();
        ch.clear();
        pv.clear();
        pvd.clear();
        v_d.clear();
        pa = -1;
        uniqueVertex = -1;
        height = 0;
    }
};

class Tree_Decomposition{
public:
    FILE *fout, *fin;
    Graph G, H;
    set<SelEle> deg;
    int maxSize;
    Tree_Decomposition(){
    }
    vector<vector<int>> length, neighbor;
    //new code instead of vector<vector<map<int,int>>> n_l
    //vector<map<int,int>> n_l;

    vector<int> ord;
    int heightMax;

    //MDE
    void reduce(){
        deg.clear();
        neighbor.clear();
        length.clear();

        vector<int> vectmp;
        vectmp.clear();
        for (int i = 0; i <= G.n; i++){
            neighbor.push_back(vectmp);
            length.push_back(vectmp);
        }
        DD = (int *)malloc(sizeof(int) * (G.n + 1));
        DD2 = (int *)malloc(sizeof(int) * (G.n + 1));
        _DD = (int *)malloc(sizeof(int) * (G.n + 1));
        _DD2 = (int *)malloc(sizeof(int) * (G.n + 1));
        NUM = (int *)malloc(sizeof(int) * (G.n + 1));
        changed = (bool*)malloc(sizeof(bool) * (G.n + 1));
        for (int i = 0; i <= G.n; i++)
            NUM[i] = i;
        //??? 交换 num[i] 和 num[j]的值 目的是啥
        for (int i = 1; i <= G.n; i++){
            int j = rand() % G.n + 1;
            int x = NUM[i];
            NUM[i] = NUM[j];
            NUM[j] = x;
        }

        for (int i = 1; i <= G.n; i++){
            DD[i] = G.D[i];
            DD2[i] = G.D[i];
            _DD[i] = G.D[i];
            _DD2[i] = G.D[i];
            changed[i] = false;
            deg.insert(SelEle(i));
        }
        bool *exist;
        exist = (bool*)malloc(sizeof(bool) * (G.n + 1));
        for (int i = 1; i <= G.n; i++)
            exist[i] = true;
        ord.clear();
        int cnt = 0;
        while (!deg.empty()){
            cnt++;
            int x = (*deg.begin()).x;
            while (true){
                if (changed[x]){
                    deg.erase(SelEle(x));
                    DD[x] = _DD[x];
                    DD2[x] = _DD2[x];
                    deg.insert(SelEle(x));
                    changed[x] = false;
                    x = (*deg.begin()).x;
                }
                else break;
            }
            ord.push_back(x);
            deg.erase(deg.begin());
            exist[x] = false;
            vector<int> neigh, leng;
            neigh.clear();
            leng.clear();
            for (map<int,int>::iterator it = G.E[x].begin(); it != G.E[x].end(); it++){
                int y = (*it).first;
                if (exist[y]){
                    neigh.push_back(y);
                    leng.push_back((*it).second);
                }
            }
            int k = -1;
            for (int i = 0; i < neigh.size(); i++){
                int y = neigh[i];
                G.deleteEdge(x, y);
                _DD[y] = G.D[y];
                changed[y] = true;
            }
            for (int pu = 0; pu < neigh.size(); pu++){
                for (int pv = 0; pv < neigh.size(); pv++)
                    if (pu != pv){
                        int u = neigh[pu], v = neigh[pv];
                        if (G.isEdgeExist(u, v)){
                            if (G.E[u][v] > leng[pu] + leng[pv])
                                G.E[u][v] = leng[pu] + leng[pv];
                            if (G.E[v][u] > leng[pu] + leng[pv])
                                G.E[v][u] = leng[pu] + leng[pv];
                        }
                        else {
                            G.insertEdge(u, v, leng[pu] + leng[pv]);
                            _DD[u] = G.D[u];
                            _DD[v] = G.D[v];
                            ++_DD2[u];
                            ++_DD2[v];
                            changed[u] = true;
                            changed[v] = true;
                        }
                    }
            }
            //tree_width: represent tree width
            if (neigh.size() > tree_width)
                tree_width = neigh.size();
            neighbor[x] = neigh;
            length[x] = leng;
            //new code 最后看看能不能放在前面 感觉感觉 leng 和 neigh也没变
            //for(int i=0; i< neigh.size(); i++){
            //    n_l[x].insert(make_pair(neigh[i], leng[i]));
            //}
        }
        free(DD);
        free(DD2);
        free(exist);
    }
    //找 x 的 parent
    int match(int x, vector<int> & neigh){
        //选出rank最高的nbr，也就是nbr中的parent
        int nearest = neigh[0];
        //nod.pv.push_back(belong[neigh[0]]);
        for (int i = 1; i < neigh.size(); i++){
            //nod.pv.push_back(belong[neigh[i]]);
            if (rank[neigh[i]] > rank[nearest]) nearest = neigh[i];
        }
        
        //p 指的是 vertex id in tree
        int p = belong[nearest];
        vector<int> a = Tree[p].vert;
        if (Tree[p].uniqueVertex >= 0){
            a.push_back(Tree[p].uniqueVertex);
        }
        sort(a.begin(), a.end());
        int i, j = 0;
        for (; (i < neigh.size()) && (j < a.size());){
            if (neigh[i] == a[j]){
                i++; j++;
            }
            else if (neigh[i] < a[j])
                break;
                else j++;
        }
        if (i >= neigh.size()) {
            return p;
        }
        printf("no match!\n");
    }
    
    vector<Node> Tree;
    int root;
    int * belong, *rank;
    void makeTree(){
        belong = (int*) malloc(sizeof(int) * (H.n + 1));
        rank = (int*) malloc(sizeof(int) * (H.n + 1));
        int len = ord.size() - 1;
        Node rootn;
        Tree.clear();
        heightMax = 0;
        
        //从后往前取
        int x = ord[len];
        cout<<x<<endl;
        rootn.vert = neighbor[x];
        rootn.VL = length[x];
        cout<<"rootn.vert.size "<<rootn.vert.size()<<""<<endl;
        
        //new code
        
        rootn.uniqueVertex = x;
        rootn.pa = -1;
        rootn.height = 1;
        rank[x] = 0;
        belong[x] = 0;
        Tree.push_back(rootn);
        len--;
        int pit = 1;
        for (; len >= 0; len--){
            int x = ord[len];
            Node nod;
            nod.vert = neighbor[x];
            nod.VL = length[x];
            nod.uniqueVertex = x;
            cout<<"x: "<<x<<endl;
            //if(pit) cout<<"len: "<<len<<endl;
            ///if(pit) cout<<"belong: "<<belong[x]<<endl;
            //if(pit) cout<<"ux:"<<x<<endl;
            //if(pit) cout<<"rank[x]: "<<rank[len]<<endl;
            //if(pit) cout<<"rank[x]: "<<rank[x]<<endl;

            int nearest = neighbor[x][0];
            int fv = rank[neighbor[x][0]];
            Tree[fv].pv.push_back(x);
            Tree[fv].pvd.push_back(length[x][0]);
            cout<<"nbr,dis: ("<< neighbor[x][0]<<", "<<length[x][0]<<") ";
            for (int i = 1; i < neighbor[x].size(); i++){
                if (rank[neighbor[x][i]] > rank[nearest]) nearest = neighbor[x][i];
                fv = rank[neighbor[x][i]];
                Tree[fv].pv.push_back(x);
                Tree[fv].pvd.push_back(length[x][i]);
                cout<<"("<< neighbor[x][i]<<", "<<length[x][i]<<") ";
                //if(pit) cout<<"fv: "<<fv<<endl;
                //cout<<" "<< neighbor[x][i];
            }cout<<endl;
            int pa = belong[nearest];
            cout<<"pa: "<<nearest<<endl;
            Tree[pa].ch.push_back(Tree.size());
            nod.pa = pa;
            nod.height = Tree[pa].height + 1;
            // update heightMax 数据
            if (nod.height > heightMax)
                heightMax = nod.height;
            rank[x] = Tree.size();
            belong[x] = Tree.size();
            Tree.push_back(nod);
        }
        root = 0;
    }
    
    int distance(int p, int q){
        if (p == q) return 0;
        int x = belong[p], y = belong[q];
        if (Tree[x].height < Tree[y].height) return Tree[y].v_d[p];
        else if (Tree[x].height > Tree[y].height) return Tree[x].v_d[q];
        return 0;
    }
    
    void makeIndex2(){
        int print_tr = 0;
        if(print_tr){
            fwrite(&root, SIZEOFINT, 1, fout);
            for(int i =0; i<Tree[root].vert.size(); i++){
                Tree[root].v_d.insert(make_pair(Tree[root].vert[i],Tree[root].VL[i]));
            }
            Tree[root].vert.push_back(Tree[root].uniqueVertex);
            printIntVector(Tree[root].vert);
            Tree[root].vert.pop_back();
            printIntVector(Tree[root].VL);
            Tree[root].KVL = Tree[root].VL;
        }
        
        cnt = 0;
        //new code
        queue<int> Q;
        while (!Q.empty()) Q.pop();

        for (int i = 0; i < Tree[root].ch.size(); i++){
            Q.push(Tree[root].ch[i]);
        }
        while(!Q.empty()){

            auto v = Q.front();
            Q.pop();

            Tree[v].KVL = Tree[v].VL;
            
            for(auto a: Tree[v].ch){
                Q.push(a);
            }
            //cout<<"cur_v: "<<Tree[v].uniqueVertex<<endl;
            //instead of j=0 目的是减少获取dis的次数
            for(int i = 0; i<Tree[v].vert.size(); i++){
                for(int j=i+1; j<Tree[v].vert.size(); j++){
                    int dis = distance(Tree[v].vert[i], Tree[v].vert[j]);
                    //int dis = distq(Tree[v].vert[i], Tree[v].vert[j]);
                    if (Tree[v].VL[i] > (Tree[v].VL[j] + dis)){
                        Tree[v].VL[i] = Tree[v].VL[j] + dis;
                    }else if (Tree[v].VL[j] > (Tree[v].VL[i] + dis)){
                        Tree[v].VL[j] = Tree[v].VL[i] + dis;
                    }
                    //cout<<"finish update"<<endl;
                }
            }
            for(int i = 0; i<Tree[v].vert.size(); i++){
                //if (Tree[v].vert[i] == 15) cout<< "come 15"<<endl;
                if(Tree[v].VL[i] == Tree[v].KVL[i]){
                    int fv = Tree[v].vert[i];
                    Tree[v].kfv.push_back(Tree[v].vert[i]);
                    Tree[v].kfvd.push_back(Tree[v].KVL[i]);
                    Tree[rank[fv]].kpv.push_back(Tree[v].uniqueVertex);
                    Tree[rank[fv]].kpvd.push_back(Tree[v].KVL[i]);
                }
                //if (Tree[v].vert[i] == 15 && Tree[v].VL[i] == Tree[v].KVL[i]) cout<<"anc: "<<Tree[v].vert[i]<<endl;
            }
            
            for(int i =0; i<Tree[v].vert.size(); i++){
                Tree[v].v_d.insert(make_pair(Tree[v].vert[i],Tree[v].VL[i]));
             }

            int print_sh=0;
            if(print_sh) cout<<"current v: "<<Tree[v].uniqueVertex<<endl;
            for(int i = 0; i<Tree[v].vert.size() && print_sh; i++){
                cout<<"Tree[v].vert[i]: "<<Tree[v].vert[i]<<endl;
                cout<<"Tree[v].VL[i]: "<<Tree[v].VL[i]<<endl;
            }
            if(print_tr){
                fwrite(&v, SIZEOFINT, 1, fout);
                Tree[v].vert.push_back(Tree[v].uniqueVertex);
                   printIntVector(Tree[v].vert);
                Tree[v].vert.pop_back();
                printIntVector(Tree[v].VL);
            }
        }
    }

    void printIntVector(vector<int> &a){
        if (a.size() == 0){
            int x = 0;
            fwrite(&x, SIZEOFINT, 1, fout);
            return;
        }
        int x = a.size();
        fwrite(&x, SIZEOFINT, 1, fout);
        for (int i = 0; i < a.size(); i++){
            fwrite(&a[i], SIZEOFINT, 1, fout);
        }
    }
    
    void saveIndex(){

        int pin = 1;

        int cnt_fv = 0;
        int cnt_pv = 0;
        int cnt_kfv = 0;
        int cnt_kpv = 0;

        fwrite(&root, SIZEOFINT, 1, fout);
        Tree[root].vert.push_back(Tree[root].uniqueVertex);
        printIntVector(Tree[root].vert);
        Tree[root].vert.pop_back();
        printIntVector(Tree[root].KVL);

        printIntVector(Tree[root].VL);

        printIntVector(Tree[root].pv);
        printIntVector(Tree[root].pvd);
        printIntVector(Tree[root].kpv);
        printIntVector(Tree[root].kpvd);
        Tree[root].kfv.push_back(Tree[root].uniqueVertex);
        printIntVector(Tree[root].kfv);
        Tree[root].kfv.pop_back();
        printIntVector(Tree[root].kfvd);
        if(pin){
            cout<<"current v: "<<Tree[root].uniqueVertex<<endl;
            for(int i = 0; i<Tree[root].pv.size(); i++) cout<<"Tree[root].pv[i]: "<<Tree[root].pv[i]<<endl;
            for(int i = 0; i<Tree[root].kpv.size(); i++) cout<<"Tree[root].kpv[i]: "<<Tree[root].kpv[i]<<endl;
        }
        cnt = 0;

        cnt_fv = Tree[root].vert.size();
        cnt_pv = Tree[root].pv.size();
        cnt_kfv = Tree[root].kfv.size();
        cnt_kpv = Tree[root].kpv.size();

        //new code
        queue<int> Q;
        while (!Q.empty()) Q.pop();

        for (int i = 0; i < Tree[root].ch.size(); i++) Q.push(Tree[root].ch[i]);

        while(!Q.empty()){

            auto v = Q.front();
            Q.pop();

            cnt_fv += Tree[v].vert.size();
            cnt_pv += Tree[v].pv.size();
            cnt_kfv += Tree[v].kfv.size();
            cnt_kpv += Tree[v].kpv.size();

            for(auto a: Tree[v].ch){
                Q.push(a);
            }
            
            fwrite(&v, SIZEOFINT, 1, fout);
            if(pin){
                cout<<"current v: "<<Tree[v].uniqueVertex<<endl;
                for(int i = 0; i<Tree[v].pv.size(); i++) cout<<"Tree[v].pv[i]: "<<Tree[v].pv[i]<<endl;
                for(int i = 0; i<Tree[v].kpv.size(); i++) cout<<"Tree[v].kpv[i]: "<<Tree[v].kpv[i]<<endl;
                for(int i = 0; i<Tree[v].vert.size(); i++) cout<<"Tree[v].vert[i]: "<<Tree[v].vert[i]<<endl;
                for(int i = 0; i<Tree[v].kfv.size(); i++) cout<<"Tree[v].kfv[i]: "<<Tree[v].kfv[i]<<endl;
            }
            
            Tree[v].vert.push_back(Tree[v].uniqueVertex);
            printIntVector(Tree[v].vert);
            Tree[v].vert.pop_back();
            printIntVector(Tree[v].KVL);

            printIntVector(Tree[root].VL);

            printIntVector(Tree[v].pv);
            printIntVector(Tree[v].pvd);
            printIntVector(Tree[v].kpv);
            printIntVector(Tree[v].kpvd);
            Tree[v].kfv.push_back(Tree[v].uniqueVertex);
            printIntVector(Tree[v].kfv);
            Tree[v].kfv.pop_back();
            printIntVector(Tree[v].kfvd);
            //printMapVector(Tree[v].v_d);
        }
        int pin_cnt=1;
        if(pin_cnt){
            cout<<"cnt_fv: "<<cnt_fv<<endl;
            cout<<"cnt_pv: "<<cnt_pv<<endl;
            cout<<"cnt_kfv: "<<cnt_kfv<<endl;
            cout<<"cnt_kpv: "<<cnt_kpv<<endl;
        }
    }

    void cntSize(){
        long long s_nonroot = 0;
        long long s_size = 0;
        
        long long s_dis = 0;
        for( int i = 0; i < Tree.size(); ++i ) {
            s_nonroot += Tree[i].height - 1;
            s_size += Tree[i].vert.size();
            s_dis += Tree[i].height;
        }
        long long s_root = (long long) Tree[0].vert.size() * (long long) G.n;
        printf( "tree width: %d\n", tree_width);
        printf( "nonroot idx size = %0.3lfGB, avg node size=%0.3lf, avg label size=%0.3lf\n",
                s_size * 4.0 / 1000000000.0, s_size * 1.0 / G.n, s_dis * 1.0 / G.n);
    }
    
    static const int SIZEOFINT = 4;
    void printIntArray(int * a, int n){
        fwrite(a, SIZEOFINT, n, fout);
    }
    
    void print(){
        //G.n
        fwrite(&G.n, SIZEOFINT, 1, fout);
        printf("G.n %d\n", G.n);
        //Tree.size() Tree.height
        int x = Tree.size();
        fwrite(&x, SIZEOFINT, 1, fout);
        for (int i = 0; i < Tree.size(); i++){
            fwrite(&Tree[i].height, SIZEOFINT, 1, fout);
        }
        cout<<"pa: ";
        for (int i = 0; i < Tree.size(); i++){
            fwrite(&Tree[i].pa, SIZEOFINT, 1, fout);
            cout<<Tree[i].pa<<" ";
        }
        cout<<endl;
        for (int i = 0; i < Tree.size(); i++){
            fwrite(&Tree[i].uniqueVertex, SIZEOFINT, 1, fout);
        }
        //belong
        printIntArray(belong, H.n + 1);
        int pt=0;

        //rootDistance
        fwrite(&root, SIZEOFINT, 1, fout);
        for (int i = 0; i < Tree.size(); i++){
            if(pt) cout<<"ch[]"<<Tree[i].uniqueVertex<<": ";
            int t = Tree[i].ch.size();
            fwrite(&t, SIZEOFINT, 1, fout);
            for (int j = 0; j < t; j++){
                fwrite(&Tree[i].ch[j], SIZEOFINT, 1, fout);
                if(pt) cout<<Tree[i].ch[j]<<" ";
            }
            if(pt) cout<<endl;
        }
    }
};

// floyd deal with vertices which is deleted
int main(int argc, char *argv[])
{
    srand(time(0));
    int operation = 1;
    if (operation == 1){ // index
        string filest;
        char *file, *fileout;
        int i;
        file = argv[1];
        cout << "file: " << file << endl;
        fileout = argv[2];
        Tree_Decomposition td;
        td.fout = fopen(fileout, "wb");
        // read graph data
        td.G = Graph(file);
        td.H = td.G;
        
        clock_t start = clock();
        td.reduce();
        td.makeTree();
        cout << "MakeIndex time: " << (double)(clock() - start) / CLOCKS_PER_SEC << endl;
        //td.makeIndex();
        //cout << "MakeIndex time: " << (double)(clock() - start) / CLOCKS_PER_SEC << endl;
        td.print();

        td.makeIndex2();

        td.saveIndex();
        cout << "Tree height: " << td.heightMax << endl;
        /// CLOCKS_PER_SEC
        //(double) * 1e3
        //cout << "MakeIndex time: " << (double)(clock() - start) / CLOCKS_PER_SEC<< endl;
        td.cntSize();
        fclose(stdout);
    }

}
