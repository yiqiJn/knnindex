#include<cstdio>
#include<cstring>
#include<iostream>
#include<cstdlib>
#include<queue>
#include <sys/time.h>
#include<vector>
#include <xmmintrin.h>
#include<cmath>
#include<set>
#include<algorithm>
#include<fstream>
#include<map>
#include "oyd.dynamic_graph.h"
#include "flatten_hash_map.h"
using namespace std;
#define MAX_K 20
#define INT_MAX 999999999
#define RESERVE_TIME 1

int reset_times = 0;

const int infinity = 999999999;
const int SIZEOFINT = 4;

double cnt_pre_query_time = 0;
char * insert_type, * query_type;

//*toRMQ, , **RMQIndex
//, **pos2 , *pos2Size
int *height, *pa, *uniqueVertex;
int *belong;
int root, TreeSize;
int **rootToRoot, *rootSite;
int **dis, **pos, **gdis;
int *posSize;
int *chSize;
int ** ch;
int *LOG2, *LOGD;
int rootSize;
int *DFSList, *toDFS;
int ***BS;

int **pv;
int *pvSize;

int **pvd;
int *pvdSize;

int **kpv;
int *kpvSize;

int **kpvd;
int *kpvdSize;

int **kfv;
int *kfvSize;

int **kfvd;
int *kfvdSize;
int *kpa;

vector<map<int,int>> v_d;
//vector<hash_map<int,int>> v_d_hm;
//koala::my_openadd_hashmap<unsigned int> edges

struct HASH_NODE{
    int a, b, c;
    int next;
    HASH_NODE(){}
    HASH_NODE(int _a, int _b, int _c){
        a = _a;
        b = _b;
        c = _c;
    }
};
class HASH{
public:
    static const int P = 100000007;
    vector<HASH_NODE> nodes;
    vector<int> start;
    HASH(){
        nodes.clear();
        nodes.push_back(HASH_NODE());
        start.resize(P);
        for (int i = 0; i < P; i++)
            start[i] = 0;
    }
    inline int get_id(int a, int b){
        return ((long long )(a) * b) % P;
    }
    inline bool is_exist(int a, int b){
        int t = get_id(a, b);
        int p = start[t];
        while (p != 0){
            if (nodes[p].a == a && nodes[p].b == b)
                return true;
            p = nodes[p].next;
        }
        return false;
    }
    inline int get_value(int a, int b){
    
        int t = get_id(a, b);
        int p = start[t];
        while (p != 0){
            if (nodes[p].a == a && nodes[p].b == b)
                return nodes[p].c;
            p = nodes[p].next;
        }
        return -1;
    }
    inline bool insert_node(int a, int b, int c){
        if (is_exist(a, b) == true)
            return false;
        int t = get_id(a, b);
        HASH_NODE hn = HASH_NODE(a,b,c);
        hn.next = start[t];
        nodes.push_back(hn);
        start[t] = nodes.size() - 1;
        return true;
    }
    inline bool delete_node(int a, int b){
        int t = get_id(a, b);
        int p = start[t];
        int pre = -1;
        while (p != 0){
            if (nodes[p].a == a && nodes[p].b == b){
                if (pre < 0)
                    start[t] = nodes[p].next;
                else nodes[pre].next = nodes[p].next;
                return true;
            }
            pre = p;
            p = nodes[p].next;
        }
        return false;
    }
};

struct DN{
    int* dis;
    int x;
    DN(){}
    DN(int* _dis, int _x){
        dis = _dis;
        x = _x;
    }
    //根据dis 指向的地址的数值排序
    bool operator < (const DN _pt) const{
        if (*dis == *_pt.dis) return x < _pt.x;
        return *dis < *_pt.dis;
        //if(x == _pt.x) return *dis > *_pt.dis;
        //return x > _pt.x;
    }
        //~DN()
};

class prio_queue{
    private:
        deque<DN> data;
    public:
        void push(DN pt){
            //cout<<"push"<<endl;
            data.push_back(pt);
            //push_heap(data.begin(),data.end()); //O(logn)
        }
        void pop(){
            //cout<<"pop"<<endl;
            //pop_heap(data.begin(), data.end());//delete
            data.pop_front();
        }
        DN top(){
            //cout<<"top"<<endl;
            sort(data.begin(),data.end());//pop_heap(data.begin(), data.end()); //添加+pop_heap
            return data.front();
        }
        bool empty(){
            //cout<<"empty"<<endl;
            return data.empty();
        }
};

    long long queryCnt;
    //long long aCnt;

    FILE *fin;
    string TT = "";
    void scanIntArray(int *a, int n){
        fread(a, SIZEOFINT, n, fin);
    }
    int* scanIntVector(int *a){
        int _n;
        fread(&_n, SIZEOFINT, 1, fin);
        a = (int*)malloc(sizeof(int) * _n);
        scanIntArray(a, _n);
        return a;
    }

    int n;
    int tree_height = 0;
    void readIndex(char *file){
        //cout<<"com read index"<<endl;
        double _time = GetTime();
        int tree_width = 0, most_sp = 0;
        fin = fopen(file, "rb");
        fread(&n, SIZEOFINT, 1, fin);
        //printf("n: %d\n", n);
        int ts;
        fread(&ts, SIZEOFINT, 1, fin);
        TreeSize = ts;
        height = (int*)malloc(sizeof(int) * (ts + 1));
        pa = (int*)malloc(sizeof(int) * (ts + 1));
        kpa = (int*)malloc(sizeof(int) * (ts + 1));
        uniqueVertex = (int*)malloc(sizeof(int) * (ts + 1));
        int print = 0;
        int pit = 0;
        //if(pit) cout<<"height: ";
        for (int i = 0; i < ts; i++){
            fread(&height[i], SIZEOFINT, 1, fin);
            //if(pit) cout<<height[i]<<" ";
            if (height[i] > tree_height)
                tree_height = height[i];
        }
        //if(pit) cout<<endl;
        if(pit) cout<<"pa: "<<pa[0];
        
        for (int i = 0; i < ts; i++){
            fread(&pa[i], SIZEOFINT, 1, fin);
            //if(pit) cout<<pa[i]<<" ";
        }
        pa[0] =-1;
        if(pit) cout<<endl;
        for (int i = 0; i < ts; i++){
            fread(&uniqueVertex[i], SIZEOFINT, 1, fin);
        }
        belong = (int*)malloc(sizeof(int) * (n + 1));
          fread(belong, SIZEOFINT, n + 1, fin);
        fread(&root, SIZEOFINT, 1, fin);

        //cout<<"belo: "<<height[belong[102167]]<<endl;
        //cout<<"uni: "<<height[102167]<<endl;
        posSize = (int*)malloc(sizeof(int) * (n + 1));
        pos = (int**)malloc(sizeof(int*) * (TreeSize));

        pvSize = (int*)malloc(sizeof(int) * (n + 1));
        pv = (int**)malloc(sizeof(int*) * (TreeSize));

        pvdSize = (int*)malloc(sizeof(int) * (n + 1));
        pvd = (int**)malloc(sizeof(int*) * (TreeSize));

        kpvSize = (int*)malloc(sizeof(int) * (n + 1));
        kpv = (int**)malloc(sizeof(int*) * (TreeSize));

        kpvdSize = (int*)malloc(sizeof(int) * (n + 1));
        kpvd = (int**)malloc(sizeof(int*) * (TreeSize));

        kfvSize = (int*)malloc(sizeof(int) * (n + 1));
        kfv = (int**)malloc(sizeof(int*) * (TreeSize));

        kfvdSize = (int*)malloc(sizeof(int) * (n + 1));
        kfvd = (int**)malloc(sizeof(int*) * (TreeSize));

        dis = (int**)malloc(sizeof(int*) * (TreeSize));
        chSize = (int*)malloc(sizeof(int) * (TreeSize));
        ch = (int**)malloc(sizeof(int*) * (TreeSize));

        v_d.clear();
        map<int,int> vemp;
        vemp.clear();
        for (int i = 0; i <= n; i++){
            v_d.push_back(vemp);
        }
        for (int i = 0; i < TreeSize; i++){
            fread(&chSize[i], SIZEOFINT, 1, fin);
            ch[i] = (int*)malloc(sizeof(int) * chSize[i]);
            for (int j = 0; j < chSize[i]; j++){
                int x;
                fread(&x, SIZEOFINT, 1, fin);
                ch[i][j] = x;
            }
        }
        //cout<<"ch finish"<<endl;

        for (int i = 0; i < TreeSize; i++){
            // read vert[]
            int x =0;
            fread(&x, SIZEOFINT, 1, fin);
            //cout<<"x: "<<x<<" uniqueVertex[x]: "<<uniqueVertex[x]<<endl;
            fread(&posSize[x], SIZEOFINT, 1, fin);
            if (posSize[x] > tree_width) tree_width = posSize[x];
            // (posSize[x] + 1)
            //posSize[x]
            pos[x] = (int*)malloc(sizeof(int) * (posSize[x] + 1));
            fread(pos[x], SIZEOFINT, posSize[x], fin);
            //cout<<"(pos, belong): ";
            //for(int j =0;j<posSize[x];j++) cout<<" ("<<pos[x][j]<<", "<<belong[pos[x][j]]<<") ";
            //cout<<endl;
            //cout<<"uni[x]: "<< uniqueVertex[x]<<" pa: "<<uniqueVertex[pa[x]]<<" belong[pa]: "<< pa[x]<<endl;
            //read VL[]
            int _n;
            fread(&_n, SIZEOFINT, 1, fin);
            dis[x] = (int*)malloc(sizeof(int) * _n);
            fread(dis[x], SIZEOFINT, _n, fin);

            fread(&pvSize[x], SIZEOFINT, 1, fin);
            pv[x] = (int*)malloc(sizeof(int) * pvSize[x]);
            fread(pv[x], SIZEOFINT, pvSize[x], fin);

            fread(&pvdSize[x], SIZEOFINT, 1, fin);
            pvd[x] = (int*)malloc(sizeof(int) * pvdSize[x]);
            fread(pvd[x], SIZEOFINT, pvdSize[x], fin);

            fread(&kpvSize[x], SIZEOFINT, 1, fin);
            kpv[x] = (int*)malloc(sizeof(int) * kpvSize[x]);
            fread(kpv[x], SIZEOFINT, kpvSize[x], fin);
         
            fread(&kpvdSize[x], SIZEOFINT, 1, fin);
            kpvd[x] = (int*)malloc(sizeof(int) * kpvdSize[x]);
            fread(kpvd[x], SIZEOFINT, kpvdSize[x], fin);

            fread(&kfvSize[x], SIZEOFINT, 1, fin);
            kfv[x] = (int*)malloc(sizeof(int) * kfvSize[x]);
            fread(kfv[x], SIZEOFINT, kfvSize[x], fin);

            fread(&kfvdSize[x], SIZEOFINT, 1, fin);
            kfvd[x] = (int*)malloc(sizeof(int) * kfvdSize[x]);
            fread(kfvd[x], SIZEOFINT, kfvdSize[x], fin);
            
            kpa[x] = -1;
            for (int i=0;i<kfvdSize[x];i++){
                if(belong[kfv[x][i]]> kpa[x]) kpa[x] = belong[kfv[x][i]];
            }

            //read v_d
            //v_d[i] = (map<int,int>*)malloc(2*sizeof(int) * (_n));
            for(int j=0; j<_n; j++){
                v_d[x].insert(make_pair(pos[x][j],dis[x][j]));
            }

            if(print) cout<<"x: "<< uniqueVertex[x] <<" pv[x][j]: ";
            if(print) for(int j=0; j<pvSize[x]; j++) cout<<" ("<<pv[x][j]<<","<<pvd[x][j]<<") ";
            if(print) cout<<endl;
            
            if(print) cout<<"x: "<< uniqueVertex[x] <<"kpv[x][j]: ";
            if(print) for(int j=0; j<kpvSize[x]; j++) cout<<" ("<<kpv[x][j]<<","<<kpvd[x][j]<<") ";
            if(print) cout<<endl;

            if(print) cout<<"x: "<< uniqueVertex[x] <<"fv[x][j]: ";
            if(print) for(int j=0; j<posSize[x]; j++) cout<<" ("<<pos[x][j]<<","<<dis[x][j]<<") ";
            if(print) cout<<endl;

            if(print) cout<<"x: "<< uniqueVertex[x] <<"kfv[x][j]: ";
            if(print) for(int j=0; j<kfvSize[x]; j++) cout<<" ("<<kfv[x][j]<<","<<kfvd[x][j]<<") ";
            if(print) cout<<endl;
        }
        //for(int i = 0; i < TreeSize; i++) cout<<" ("<<uniqueVertex[i]<<", "<<uniqueVertex[kpa[i]]<<") ";
        //cout<<endl;
        
        fclose(fin);
        //printf("Load Index Time : %lf sec\n", (GetTime() - _time));
        //printf("tree height: %d\n", tree_height);
        //printf("tree width: %d\n", tree_width);
        //printf("most search space: %d\n", most_sp);
    }

    void readIndex_up(char *file){
        //cout<<"com read index"<<endl;
        double _time = GetTime();
        int tree_width = 0, most_sp = 0;
        fin = fopen(file, "rb");
        fread(&n, SIZEOFINT, 1, fin);
        //printf("n: %d\n", n);
        int ts;
        fread(&ts, SIZEOFINT, 1, fin);
        TreeSize = ts;
        height = (int*)malloc(sizeof(int) * (ts + 1));
        pa = (int*)malloc(sizeof(int) * (ts + 1));
        uniqueVertex = (int*)malloc(sizeof(int) * (ts + 1));
        int print = 0;
        if(print) cout<<"height: ";
        for (int i = 0; i < ts; i++){
            fread(&height[i], SIZEOFINT, 1, fin);
            if(print) cout<<height[i]<<" ";
            if (height[i] > tree_height)
                tree_height = height[i];
        }
        if(print) cout<<endl;
        for (int i = 0; i < ts; i++){
            fread(&pa[i], SIZEOFINT, 1, fin);
        }
        for (int i = 0; i < ts; i++){
            fread(&uniqueVertex[i], SIZEOFINT, 1, fin);
        }
        belong = (int*)malloc(sizeof(int) * (n + 1));
          fread(belong, SIZEOFINT, n + 1, fin);
        fread(&root, SIZEOFINT, 1, fin);
        posSize = (int*)malloc(sizeof(int) * (n + 1));
        pos = (int**)malloc(sizeof(int*) * (TreeSize));

        pvSize = (int*)malloc(sizeof(int) * (n + 1));
        pv = (int**)malloc(sizeof(int*) * (TreeSize));

        pvdSize = (int*)malloc(sizeof(int) * (n + 1));
        pvd = (int**)malloc(sizeof(int*) * (TreeSize));

        kpvSize = (int*)malloc(sizeof(int) * (n + 1));
        kpv = (int**)malloc(sizeof(int*) * (TreeSize));

        kpvdSize = (int*)malloc(sizeof(int) * (n + 1));
        kpvd = (int**)malloc(sizeof(int*) * (TreeSize));

        kfvSize = (int*)malloc(sizeof(int) * (n + 1));
        kfv = (int**)malloc(sizeof(int*) * (TreeSize));

        kfvdSize = (int*)malloc(sizeof(int) * (n + 1));
        kfvd = (int**)malloc(sizeof(int*) * (TreeSize));

        dis = (int**)malloc(sizeof(int*) * (TreeSize));
        gdis = (int**)malloc(sizeof(int*) * (TreeSize));
        chSize = (int*)malloc(sizeof(int) * (TreeSize));
        ch = (int**)malloc(sizeof(int*) * (TreeSize));

        v_d.clear();
        map<int,int> vemp;
        vemp.clear();
        for (int i = 0; i <= n; i++){
            v_d.push_back(vemp);
        }
        for (int i = 0; i < TreeSize; i++){
            fread(&chSize[i], SIZEOFINT, 1, fin);
            ch[i] = (int*)malloc(sizeof(int) * chSize[i]);
            for (int j = 0; j < chSize[i]; j++){
                int x;
                fread(&x, SIZEOFINT, 1, fin);
                ch[i][j] = x;
            }
        }
        //cout<<"ch finish"<<endl;

        for (int i = 0; i < TreeSize; i++){
            // read vert[]
            int x =0;
            fread(&x, SIZEOFINT, 1, fin);
            //cout<<"x: "<<x<<" uniqueVertex[x]: "<<uniqueVertex[x]<<endl;
            fread(&posSize[x], SIZEOFINT, 1, fin);
            if (posSize[x] > tree_width) tree_width = posSize[x];
            // (posSize[x] + 1)
            //posSize[x]
            pos[x] = (int*)malloc(sizeof(int) * (posSize[x] + 1));
            fread(pos[x], SIZEOFINT, posSize[x], fin);
            //read VL[]
            int _n;
            fread(&_n, SIZEOFINT, 1, fin);
            dis[x] = (int*)malloc(sizeof(int) * _n);
            fread(dis[x], SIZEOFINT, _n, fin);

            fread(&_n, SIZEOFINT, 1, fin);
            gdis[x] = (int*)malloc(sizeof(int) * _n);
            fread(gdis[x], SIZEOFINT, _n, fin);

            fread(&pvSize[x], SIZEOFINT, 1, fin);
            pv[x] = (int*)malloc(sizeof(int) * pvSize[x]);
            fread(pv[x], SIZEOFINT, pvSize[x], fin);

            fread(&pvdSize[x], SIZEOFINT, 1, fin);
            pvd[x] = (int*)malloc(sizeof(int) * pvdSize[x]);
            fread(pvd[x], SIZEOFINT, pvdSize[x], fin);

            fread(&kpvSize[x], SIZEOFINT, 1, fin);
            kpv[x] = (int*)malloc(sizeof(int) * kpvSize[x]);
            fread(kpv[x], SIZEOFINT, kpvSize[x], fin);
         
            fread(&kpvdSize[x], SIZEOFINT, 1, fin);
            kpvd[x] = (int*)malloc(sizeof(int) * kpvdSize[x]);
            fread(kpvd[x], SIZEOFINT, kpvdSize[x], fin);

            fread(&kfvSize[x], SIZEOFINT, 1, fin);
            kfv[x] = (int*)malloc(sizeof(int) * kfvSize[x]);
            fread(kfv[x], SIZEOFINT, kfvSize[x], fin);

            fread(&kfvdSize[x], SIZEOFINT, 1, fin);
            kfvd[x] = (int*)malloc(sizeof(int) * kfvdSize[x]);
            fread(kfvd[x], SIZEOFINT, kfvdSize[x], fin);

            //read v_d
            //v_d[i] = (map<int,int>*)malloc(2*sizeof(int) * (_n));
            for(int j=0; j<_n; j++){
                v_d[x].insert(make_pair(pos[x][j],gdis[x][j]));
                //v_d_hm[x].insert(make_pair(pos[x][j],gdis[x][j]));
            }

            if(print) cout<<"x: "<< uniqueVertex[x] <<" pv[x][j]: ";
            if(print) for(int j=0; j<pvSize[x]; j++) cout<<" ("<<pv[x][j]<<","<<pvd[x][j]<<") ";
            if(print) cout<<endl;
            
            if(print) cout<<"x: "<< uniqueVertex[x] <<"kpv[x][j]: ";
            if(print) for(int j=0; j<kpvSize[x]; j++) cout<<" ("<<kpv[x][j]<<","<<kpvd[x][j]<<") ";
            if(print) cout<<endl;

            if(print) cout<<"x: "<< uniqueVertex[x] <<"fv[x][j]: ";
            if(print) for(int j=0; j<posSize[x]; j++) cout<<" ("<<pos[x][j]<<","<<dis[x][j]<<") ";
            if(print) cout<<endl;

            if(print) cout<<"x: "<< uniqueVertex[x] <<"kfv[x][j]: ";
            if(print) for(int j=0; j<kfvSize[x]; j++) cout<<" ("<<kfv[x][j]<<","<<kfvd[x][j]<<") ";
            if(print) cout<<endl;
        }
        fclose(fin);
        //printf("Load Index Time : %lf sec\n", (GetTime() - _time));
        //printf("tree height: %d\n", tree_height);
        //printf("tree width: %d\n", tree_width);
        //printf("most search space: %d\n", most_sp);
    }


    void readIndex_ori(char *file){
        //cout<<"com read index"<<endl;
        double _time = GetTime();
        int tree_height = 0, tree_width = 0, most_sp = 0;
        fin = fopen(file, "rb");
        fread(&n, SIZEOFINT, 1, fin);
        //printf("n: %d\n", n);
        int ts;
        fread(&ts, SIZEOFINT, 1, fin);
        TreeSize = ts;
        height = (int*)malloc(sizeof(int) * (ts + 1));
        pa = (int*)malloc(sizeof(int) * (ts + 1));
        uniqueVertex = (int*)malloc(sizeof(int) * (ts + 1));
        for (int i = 0; i < ts; i++){
            fread(&height[i], SIZEOFINT, 1, fin);
            if (height[i] > tree_height)
                tree_height = height[i];
        }
        for (int i = 0; i < ts; i++){
            fread(&pa[i], SIZEOFINT, 1, fin);
        }
        for (int i = 0; i < ts; i++){
            fread(&uniqueVertex[i], SIZEOFINT, 1, fin);
        }
        //cout<<"111"<<endl;
        belong = (int*)malloc(sizeof(int) * (n + 1));
          fread(belong, SIZEOFINT, n + 1, fin);
        //cout<<"111"<<endl;
        fread(&root, SIZEOFINT, 1, fin);
        cout << "root: " << root << endl;
        posSize = (int*)malloc(sizeof(int) * (n + 1));
        pos = (int**)malloc(sizeof(int*) * (TreeSize));
        dis = (int**)malloc(sizeof(int*) * (TreeSize));
        chSize = (int*)malloc(sizeof(int) * (TreeSize));
        ch = (int**)malloc(sizeof(int*) * (TreeSize));
        //初始化！！
        //v_d = (map<int,int>*)malloc(2*sizeof(int) * (TreeSize));
        v_d.clear();
        map<int,int> vemp;
        vemp.clear();
        for (int i = 0; i <= n; i++){
            v_d.push_back(vemp);
        }
        for (int i = 0; i < TreeSize; i++){
            fread(&chSize[i], SIZEOFINT, 1, fin);
            ch[i] = (int*)malloc(sizeof(int) * chSize[i]);
            for (int j = 0; j < chSize[i]; j++){
                int x;
                fread(&x, SIZEOFINT, 1, fin);
                ch[i][j] = x;
            }
        }
        //cout<<"ch finish"<<endl;

        for (int i = 0; i < TreeSize; i++){
            // read vert[]
            int x =0;
            fread(&x, SIZEOFINT, 1, fin);
            //cout<<"x: "<<x<<" uniqueVertex[x]: "<<uniqueVertex[x]<<endl;
            fread(&posSize[x], SIZEOFINT, 1, fin);
            if (posSize[x] > tree_width)
                tree_width = posSize[x];
            pos[x] = (int*)malloc(sizeof(int) * (posSize[x] + 1));
            fread(pos[x], SIZEOFINT, posSize[x], fin);
            //read VL[]
            int _n;
            fread(&_n, SIZEOFINT, 1, fin);
            dis[x] = (int*)malloc(sizeof(int) * _n);
            fread(dis[x], SIZEOFINT, _n, fin);
            //read v_d
            //v_d[i] = (map<int,int>*)malloc(2*sizeof(int) * (_n));
            for(int j=0; j<_n; j++){
                v_d[x].insert(make_pair(pos[x][j],dis[x][j]));
                //cout<<"pos[x][j]: "<<pos[x][j]<<endl;
                //cout<<"dis[x][j]: "<<dis[x][j]<<endl;
            }
        }
        fclose(fin);
        
        printf("Load Index Time : %lf sec\n", (GetTime() - _time));
        //printf("tree height: %d\n", tree_height);
        //printf("tree width: %d\n", tree_width);
        //printf("most search space: %d\n", most_sp);
        
    }
    
    int cnt;
    void getDFSListDFS(int p){
        toDFS[p] = cnt;
        DFSList[cnt++] = p;
        for (int i = 0; i < chSize[p]; i++){
            getDFSListDFS(ch[p][i]);
        }
        BS[p] = (int**)malloc(sizeof(int*) * chSize[p]);
        for (int i = 0; i < chSize[p]; i++){
            BS[p][i] = (int*)malloc(sizeof(int) * chSize[p]);
            for (int j = 0; j < chSize[p]; j++){
                if (posSize[ch[p][i]] < posSize[ch[p][j]])
                    BS[p][i][j] = ch[p][i];
                else BS[p][i][j] = ch[p][j];
            }
        }
    }
    void getDFSList(){
        DFSList = (int*) malloc(sizeof(int) * (TreeSize + 1));
        toDFS = (int*) malloc(sizeof(int) * (TreeSize + 1));
        BS = (int***)malloc(sizeof(int**) * (TreeSize + 1));
        cnt = 0;
        getDFSListDFS(root);
    }
    
    int *tmp_dis, *higher, *cloest_higher;
    bool anc_compare(int p, int q){
        if (tmp_dis[p] < tmp_dis[q])
            return true;
        return false;
    }

    bool cmp (const pair<int,int> &p1, const pair<int,int> &p2){
        return p1.second<p2.second;
    }
    //map
    inline int distanceQuery(int p, int q){
        double start_time = GetTime();
        if (p == q) return 0;
        int x = belong[p], y = belong[q];
        if (height[x] < height[y]) return v_d[y][p];
        else return v_d[x][q];
        //else if (height[x] > height[y]) return v_d[x][q];
        //return 0;
        double end_time = GetTime();
        printf("distanceQuery time Map: %.6lf ms\n", (end_time - start_time) * 1e3);
    }

    //iter
    inline int distQuery_iterate(int p, int q){
        double start_time = GetTime();
        if (p == q) return 0;
        int x = belong[p], y = belong[q];
        if(height[x] < height[y]){
            for(int i=0;i<posSize[y]-1;i++){
                if(pos[y][i] == p) return dis[y][i];
            }
        }else{
            for(int i=0;i<posSize[x]-1;i++){
                if(pos[x][i] == q) return dis[x][i];
            }
        }
        return 0;
        double end_time = GetTime();
        printf("distanceQuery time Iterate: %.6lf ms\n", (end_time - start_time) * 1e3);
    }
    //hash_map
    /*inline int distQuery_hm(int p, int q){
        double start_time = GetTime();
        if (p == q) return 0;
        int x = belong[p], y = belong[q];
        if (height[x] < height[y]) return v_d_hm[y][p];
        else return v_d_hm[x][q];
        double end_time = GetTime();
        printf("distanceQuery time HashMap: %.6lf ms\n", (end_time - start_time) * 1e3);
    }*/

    int *cur_gdis, *gdist_state, gdist_stamp;

    inline int LCA(int s, int t){
        int sAncestor = s, tAncestor = t;
        while (true) {
            if (height[sAncestor] > height[tAncestor]) {
                if (tAncestor == pa[sAncestor]) return tAncestor;
                sAncestor = pa[sAncestor];
            } else if (height[sAncestor] < height[tAncestor]) {
                if (sAncestor == pa[tAncestor]) return sAncestor;
                tAncestor = pa[tAncestor];
            } else {
                if (pa[sAncestor] == -1 || sAncestor == tAncestor)return sAncestor;
                sAncestor = pa[sAncestor];
                tAncestor = pa[tAncestor];
            }
        }
    }

    inline vector<int> gdist_bu_kpro(int bottom, int up){
        vector<int> result;
        if (bottom != up) {
            int anc = pa[bottom], ancc = bottom;
            while (anc != up) {
                for(int i = 0;i<posSize[ancc];i++){
                    cur_gdis[pos[ancc][i]] = gdis[ancc][i];
                    gdist_state[pos[ancc][i]] = gdist_stamp;
                }
                for(int i=0; i< posSize[anc];i++){
                    if(gdist_state[pos[anc][i]] == gdist_stamp){
                        int cur_mdist = cur_gdis[uniqueVertex[anc]] + gdis[anc][i];
                        if (cur_mdist < cur_gdis[pos[anc][i]]) cur_gdis[pos[anc][i]] = cur_mdist;
                    }else{
                        cur_gdis[pos[anc][i]] = cur_gdis[uniqueVertex[anc]] + gdis[anc][i];
                    }
                }
                ancc = anc; anc = pa[anc];
            }
            for(int i = 0;i<posSize[ancc];i++){
                result.emplace_back(cur_gdis[pos[ancc][i]]);
            }
        } else {
            for(int i = 0;i<posSize[up];i++){
                result.emplace_back(gdis[up][i]);
            }
        }
        return result;
    }

    inline int gdistQuery_kpro(int s, int t){
        int lca = LCA(s, t);
        gdist_state++;
        auto s_result = gdist_bu_kpro(s, lca);
        auto t_result = gdist_bu_kpro(t, lca);
        if (false) {//debug
            printf("query(%u,%u) lca(%u)\n", s, t, lca);
            printf("dist(%u):", s);
            for (auto &a:s_result)printf("%u, ", a);
            printf("\n");
            printf("dist(%u):", t);
            for (auto &a:t_result)printf("%u, ", a);
            printf("\n");
        }
        int mindist = UINT32_MAX;
        for(int i=0;i<posSize[lca];i++){
            int mdis = s_result[i] + t_result[i];
            if (mdis < mindist){
                mindist = mdis;
            }
        }
        return mindist;
    }

    inline vector<int> gdist_bu(int bottom, int up){
        vector<int> result;
        int anc = pa[bottom], ancc = bottom;
        int cur_dist_v_bo = 0;
        for(int i = 0; i<posSize[ancc]-1; i++){
            cur_gdis[pos[ancc][i]] = gdis[ancc][i];
            gdist_state[pos[ancc][i]] = gdist_stamp;
        }
        if (bottom != up) {
            while (anc != up) {
                for(int i=0; i< posSize[anc]-1;i++){
                    //这里的逻辑可能不太对
                    if(gdist_state[pos[anc][i]] == gdist_stamp) continue;
                    else{
                        cur_gdis[pos[anc][i]] = UINT32_MAX;
                        for(int j = 0; j<posSize[ancc]-1; j++){
                            // v \in X(ancc) 公共部分 dist(v,bo) done
                            // 非公共部分 X(anc)\X(ancc)
                            cur_dist_v_bo = cur_gdis[pos[ancc][j]] + distanceQuery(pos[anc][i],pos[ancc][j]);
                            //gdis[anc][i];
                            if(cur_dist_v_bo < cur_gdis[pos[anc][i]]) cur_gdis[pos[anc][i]] = cur_dist_v_bo;
                        }
                        gdist_state[pos[anc][i]] = gdist_stamp;
                    }
                }
                ancc = anc; anc = pa[anc];
            }
            for(int i = 0;i<posSize[ancc];i++){
                result.emplace_back(cur_gdis[pos[ancc][i]]);
            }
        } else {
            for(int i = 0;i<posSize[up];i++){
                result.emplace_back(gdis[up][i]);
            }
        }
        return result;
    }

    inline int gdistQuery(int s, int t){
        auto lca = LCA(s, t);
        auto s_result = gdist_bu(s, lca);
        auto t_result = gdist_bu(t, lca);
        if (false) {//debug
            printf("query(%u,%u) lca(%u)\n", s, t, lca);
            printf("dist(%u):", s);
            for (auto &a:s_result)printf("%u, ", a);
            printf("\n");
            printf("dist(%u):", t);
            for (auto &a:t_result)printf("%u, ", a);
            printf("\n");
        }
        //debug
        if(s_result.size()!=t_result.size()) {
            cout<<"amazing;"<<endl;
            return 0;
        }
        unsigned int min_dist = s_result[0] + t_result[0];
        for(int i=1; i<s_result.size(); i++){
            unsigned int cur_dist = s_result[i] + t_result[i];
            if (cur_dist < min_dist) min_dist = cur_dist;
        }
        return min_dist;
    }

int *is_current_object, *current_distance, current_stamp, *current_state;

int *curup_dist, curup_stamp, *curup_state, *curup_affect, highest_all_up, highest_up, highest_up_anc;

int *curqu_dist, *curqu_affect, *curqu_state,curqu_stamp;
 


//int *distanceInt, *keyInt;

class kNN{
public:
int M_K;
//FILE *fout;
kNN(int x){
    M_K = x;
}
//双向链表
struct list_node{
    int previous, next, key, dist;
    list_node(){
        previous = -1;
        next = -1;
        key = -1;         // vertex
        dist = -1;        // distance
    }
};

struct object_saveing_structure{
    vector<list_node> a;
    vector<int> trash_can;
    int current, size_num;
    object_saveing_structure(){
        a.clear();
        list_node _a;
        _a.key = -1;
        _a.dist = -1;
        _a.previous = 0;
        _a.next = 0;
        a.push_back(_a);
        trash_can.clear();
        current = 0;
        size_num = 0;
    }
};

    HASH hash;
    vector<double> times_period[10];
    int period = 8;
    vector<object_saveing_structure> OSS;
     vector<object_saveing_structure> OSS_global;
    vector<int> object_number;
    vector<vector<pair<int, int>>> path_from_root;

    void create_kNN_index(){
        //initialize _v
        vector<pair<int, int>> _v;
        _v.clear();
        for (int i = 0; i <= TreeSize; i++)
            path_from_root.push_back(_v);
        
        //initialize OSS
        OSS.clear();
        for (int i = 0; i < TreeSize; i++){
            object_saveing_structure oss;
            OSS.push_back(oss);
        }

        //initialize OSS_global
        OSS_global.clear();
        for (int i = 0; i < TreeSize; i++){
            object_saveing_structure oss;
            OSS_global.push_back(oss);
        }
        //printf("TreeSize: %d\n", TreeSize);

    }
    void delete_element(int p, int x){
        OSS[p].size_num--;
        int pre = OSS[p].a[x].previous;
        int ne = OSS[p].a[x].next;
        OSS[p].a[ne].previous = pre;
        OSS[p].a[pre].next = ne;
    }
    void delete_element_global(int p, int x){
        OSS_global[p].size_num--;
        int pre = OSS_global[p].a[x].previous;
        int ne = OSS_global[p].a[x].next;
        OSS_global[p].a[ne].previous = pre;
        OSS_global[p].a[pre].next = ne;
    }


// update_ori
    inline void insert_ori(int p, int x){
        //    printf("p, x: %d %d\n", p, x);
         //  if (x == 30137)
        //       cout << "(--" << p << ", " << x << "--)";
        
        int y = uniqueVertex[p];
        //    if (p == 59532)
        //        printf("p, y, x: %d %d %d\n", p, y, x);
        //    printf("y: %d\n", y);
        
        //    if (p == 1476 && x == 30137)
        //        cout << "heihei" << endl;
        int disxy = distanceQuery(y, x);
        if (OSS[p].size_num >= int(M_K))
            if (OSS[p].a[OSS[p].a[0].previous].dist <= disxy)
                return;
        //    printf("y, x, distanceQuery(y, x): %d %d %d\n", y, x, disxy);
        //    if (y == 9817)
        //        printf("y, disxy: %d %d\n", y, disxy);
        int i = 0;
        //    printf("OSS.size(): %d\n", OSS.size());
        //    printf("OSS[p].a.size(): %d\n", OSS[p].a.size());
        //    printf("(*a)[0].key (*a)[0].dist, (*a)[0].next, (*a)[0].previous: %d %d %d %d\n", OSS[p].a[0].key, OSS[p].a[0].dist, OSS[p].a[0].next, OSS[p].a[0].previous);
        while (OSS[p].a[i].previous != 0 && OSS[p].a[ OSS[p].a[i].previous ].dist > disxy)
            i = OSS[p].a[i].previous;
        list_node _a;
        _a.next = i;
        _a.previous = OSS[p].a[i].previous;
        _a.key = x;
        _a.dist = disxy;
        
        OSS[p].a.push_back(_a);
        //
        hash.insert_node(p, x, OSS[p].a.size() - 1);
        //
        OSS[p].a[_a.previous].next = OSS[p].a.size() - 1;
        OSS[p].a[_a.next].previous = OSS[p].a.size() - 1;
        OSS[p].size_num++;
        if (OSS[p].size_num > M_K * RESERVE_TIME)
            delete_element(p, OSS[p].a[0].previous);
    }
    inline void insert_ori(int x){
        if (is_current_object[x] == 1)
            return;
        is_current_object[x] = 1;
        
        int p = belong[x];
        while (p>=0){
            object_number[p] ++;
            insert_ori(p, x);
            p = pa[p];
        }
    }

    void delete_ori(int p, int x){
        int y = uniqueVertex[p];
        int disxy = distanceQuery(y, x);

        //hash.delete_node(p, x);

        if (OSS[p].a[OSS[p].a[0].previous].dist < disxy){
            return;
        }
        int i = 0;
        while (OSS[p].a[i].next != 0 && OSS[p].a[ OSS[p].a[i].next ].dist <= disxy){
            i = OSS[p].a[i].next;
            if (OSS[p].a[i].key == x)
                break;
        }

        if (OSS[p].a[i].key == x){
            delete_element(p, i);
        }else {
            return;
        }

        if (OSS[p].size_num >= M_K){
            return;
        }
        
        if (object_number[p] <= OSS[p].size_num ){
            if (object_number[p] < OSS[p].size_num ) while (1);
            return;
        }
        reset_times++;
        for (int i = OSS[p].a[0].next; i != 0; i = OSS[p].a[i].next)
            delete_element(p, i);
        vector<int> a;
        a.clear();
        if (is_current_object[x] == 1)
            OSS_push_front(p, x, 0);
        if (strcmp(insert_type, "sort") == 0){
            vector<int> a;
            a.clear();
            get_all_object(p, a);
            for (int i = 0; i < a.size(); i++)
                current_distance[a[i]] = distanceQuery(y, a[i]);
            int _MAX = int(MAX_K * RESERVE_TIME);
            int current_k;
            if (_MAX < a.size()){
                nth_element(a.begin(), a.begin() + _MAX, a.end(), object_compare);
                current_k = _MAX;
            }
            else {
                current_k = a.size();
            }
            sort(a.begin(), a.end(), object_compare);
            for (int i = 0; i < current_k; i++){
                OSS_push_back(p, a[i], current_distance[a[i]]);
            }
        }else {
            get_subtree_ori(p, uniqueVertex[p], a);
            join_subtree_ori(p, uniqueVertex[p], a);
        }
    }
    inline void delete_ori(int x){
        if (is_current_object[x] == 0)
            return;
        is_current_object[x] = 0;

        int p = belong[x];
        while (p>=0){
            object_number[p]--;
            delete_ori(p, x);
            p = pa[p];
        }
    }
    
    
    inline void Dir_query_after_insert(int q, int insert_vector){
        if(q == insert_vector) {
            OSS_global_push_front(belong[q], q, 0); return;
        }
        int p = belong[q], y = belong[insert_vector];
        int distxy = gdistQuery(p,y); // hw
        if (OSS_global[p].size_num >= int(M_K))
            if (OSS_global[p].a[OSS_global[p].a[0].previous].dist <= distxy)
                return;
        // k
        int i = 0;
        while (OSS_global[p].a[i].previous != 0 && OSS_global[p].a[OSS_global[p].a[i].previous].dist > distxy)
            i = OSS_global[p].a[i].previous;
        list_node _a;
        _a.next = i;
        _a.previous = OSS_global[p].a[i].previous;
        _a.key = insert_vector;
        _a.dist = distxy;
        
        OSS_global[p].a.push_back(_a);
        
        OSS_global[p].a[_a.previous].next = OSS_global[p].a.size() - 1;
        OSS_global[p].a[_a.next].previous = OSS_global[p].a.size() - 1;
        OSS_global[p].size_num++;
        if (OSS_global[p].size_num > M_K * RESERVE_TIME)
            delete_element_global(p, OSS_global[p].a[0].previous);

    }

    inline void qu_obj_insert(int x){
    }

    void get_all_object(int p, vector<int> &a){
        int x = uniqueVertex[p];
        if (is_current_object[x]){
            a.push_back(x);
        }
        for (int i = 0; i < chSize[p]; i++){
            get_all_object(ch[p][i], a);
        }
    }
    void delete_object_ori(int p, int x){
        int y = uniqueVertex[p];
        int disxy = distanceQuery(y, x);

        hash.delete_node(p, x);

        if (OSS[p].a[OSS[p].a[0].previous].dist < disxy){
            return;
        }
        int i = 0;
        while (OSS[p].a[i].next != 0 && OSS[p].a[ OSS[p].a[i].next ].dist <= disxy){
            i = OSS[p].a[i].next;
            if (OSS[p].a[i].key == x)
                break;
        }

        if (OSS[p].a[i].key == x){
            delete_element(p, i);
        }else {
            return;
        }

        if (OSS[p].size_num >= M_K){
            return;
        }
        
        if (object_number[p] <= OSS[p].size_num ){
            if (object_number[p] < OSS[p].size_num ) while (1);
            return;
        }
        reset_times++;
        for (int i = OSS[p].a[0].next; i != 0; i = OSS[p].a[i].next)
            delete_element(p, i);
        vector<int> a;
        a.clear();
        if (is_current_object[x] == 1)
            OSS_push_front(p, x, 0);
        if (strcmp(insert_type, "sort") == 0){
            vector<int> a;
            a.clear();
            get_all_object(p, a);
            for (int i = 0; i < a.size(); i++)
                current_distance[a[i]] = distanceQuery(y, a[i]);
            int _MAX = int(MAX_K * RESERVE_TIME);
            int current_k;
            if (_MAX < a.size()){
                nth_element(a.begin(), a.begin() + _MAX, a.end(), object_compare);
                current_k = _MAX;
            }
            else {
                current_k = a.size();
            }
            sort(a.begin(), a.end(), object_compare);
            for (int i = 0; i < current_k; i++){
                OSS_push_back(p, a[i], current_distance[a[i]]);
            }
        }else {
            get_subtree_ori(p, uniqueVertex[p], a);
            join_subtree_ori(p, uniqueVertex[p], a);
        }
    }
    inline void delete_object_ori(int x){
        if (is_current_object[x] == 0)
            return;
        is_current_object[x] = 0;

        int p = belong[x];
        while (p>=0){
            object_number[p]--;
            delete_object_ori(p, x);
            p = pa[p];
        }
    }
    inline void query_obj(int x){
    }

/////Lazy Update

    inline bool insert_lazy(int p, int x, int disxy){
        //insert vertex: x
        //int y = uniqueVertex[p];
        //int disxy = distanceQuery(y, x);
        //取index中的最后一个item
        if (OSS[p].size_num >= int(MAX_K))
            if (OSS[p].a[OSS[p].a[0].previous].dist <= disxy)
                return false;
        int i = 0;
        while (OSS[p].a[i].previous != 0 && OSS[p].a[OSS[p].a[i].previous].dist > disxy)
            i = OSS[p].a[i].previous;
        list_node _a;
        _a.next = i;
        _a.previous = OSS[p].a[i].previous;
        _a.key = x;
        _a.dist = disxy;
        
        OSS[p].a.push_back(_a);
        //hash.insert_node(p, x, OSS[p].a.size() - 1);
        //双向链表更新一下
        OSS[p].a[_a.previous].next = OSS[p].a.size() - 1;
        OSS[p].a[_a.next].previous = OSS[p].a.size() - 1;
        OSS[p].size_num++;
        if (OSS[p].size_num > M_K * RESERVE_TIME)
            delete_element(p, OSS[p].a[0].previous);
        return true;
    }

    inline void insert_lazy(int x){
        //highest_aff=tree_height;
        //看看x是否在object中
        if(is_current_object[x] == 1) return; //(tree_height+1);
        is_current_object[x] = 1;
        int p = belong[x];
        curup_stamp++;
        //cout<<"x: "<<"before "<<endl;
        // x 到 fv

        /*for(int i=0;i<posSize[p]-1;i++){
            curup_dist[pos[p][i]] = dis[p][i];
            curup_affect[pos[p][i]] = curup_stamp;
        }*/
        for(int i=0;i<kfvdSize[p];i++){
            curup_dist[kfv[p][i]] = kfvd[p][i];
            curup_affect[kfv[p][i]] = curup_stamp;
        }
        curup_affect[x] = curup_stamp;
        //curup_affect 记录是否dist被赋值过
        while (p>=0){
            //printf("insert p, x: %d %d\n", p, x);
            //第一次进来 p = x 自己 下一次就是x 的pa
            object_number[p]++;
            insert_lazy(p, x, curup_dist[uniqueVertex[p]]);
            //if(insert_lazy(p, x, curup_dist[uniqueVertex[p]])){
                //curup_state[p] = curup_stamp;
                //for query_optimize
                //highest_up = height[p];
                //highest_up_anc = p;
            //}
            p = kpa[p];
            /*
            for(int i=0;i<posSize[p]-1;i++){
                if (curup_affect[pos[p][i]] == curup_stamp) {
                    int cur_dis = dis[p][i] + curup_dist[uniqueVertex[p]];
                    if (curup_dist[pos[p][i]] > cur_dis) curup_dist[pos[p][i]] = cur_dis;
                    //continue;
                }else{
                    //curup_dist[uniqueVertex[p]] 是 此时fv到x的距离
                    curup_dist[pos[p][i]] = dis[p][i] + curup_dist[uniqueVertex[p]];
                    curup_affect[pos[p][i]] = curup_stamp;
                }
            }*/
            for(int i=0;i<kfvdSize[p];i++){
                if (curup_affect[kfv[p][i]] == curup_stamp) {
                    int cur_dis = kfvd[p][i] + curup_dist[uniqueVertex[p]];
                    if (curup_dist[kfv[p][i]] > cur_dis) curup_dist[kfv[p][i]] = cur_dis;
                    //continue;
                }else{
                    //curup_dist[uniqueVertex[p]] 是 此时fv到x的距离
                    curup_dist[kfv[p][i]] = kfvd[p][i] + curup_dist[uniqueVertex[p]];
                    curup_affect[kfv[p][i]] = curup_stamp;
                }
            }
        }
        //return highest_up;
    }

    //先lca -> 算distance
    inline int query_af_in_smart_kpro(int x, int ins){
        vector<int> anc; anc.clear();
        int p = belong[x];
        curqu_stamp++;
        for(int i=0;i<kfvdSize[p];i++){
            curqu_dist[kfv[p][i]] = kfvd[p][i];
            curqu_affect[kfv[p][i]] = curqu_stamp;
        }
        curqu_affect[x] = curup_stamp;
        while (p>=0){
            p = kpa[p];
            for(int i=0;i<kfvdSize[p];i++){
                if (curup_affect[kfv[p][i]] == curup_stamp) {
                    int cur_dis = kfvd[p][i] + curup_dist[uniqueVertex[p]];
                    if (curup_dist[kfv[p][i]] > cur_dis) curup_dist[kfv[p][i]] = cur_dis;
                }else{
                    //curup_dist[uniqueVertex[p]] 是 此时fv到x的距离
                    curup_dist[kfv[p][i]] = kfvd[p][i] + curup_dist[uniqueVertex[p]];
                    curup_affect[kfv[p][i]] = curup_stamp;
                }
            }
        }
        return 0;
    }
    inline int query_af_in_smart(int x, int ins){
        vector<int> anc; anc.clear();
        int p = belong[x];
        curqu_stamp++;
        for(int i=0;i<kfvdSize[p];i++){
            curqu_dist[kfv[p][i]] = kfvd[p][i];
            curqu_affect[kfv[p][i]] = curqu_stamp;
        }
        curqu_affect[x] = curup_stamp;
        while (p>=0){
            p = kpa[p];
            for(int i=0;i<kfvdSize[p];i++){
                if (curup_affect[kfv[p][i]] == curup_stamp) {
                    int cur_dis = kfvd[p][i] + curup_dist[uniqueVertex[p]];
                    if (curup_dist[kfv[p][i]] > cur_dis) curup_dist[kfv[p][i]] = cur_dis;
                }else{
                    //curup_dist[uniqueVertex[p]] 是 此时fv到x的距离
                    curup_dist[kfv[p][i]] = kfvd[p][i] + curup_dist[uniqueVertex[p]];
                    curup_affect[kfv[p][i]] = curup_stamp;
                }
            }
        }
        return 0;
    }


    bool delete_lazy(int p, int x, int disxy){

        if (OSS[p].a[OSS[p].a[0].previous].dist < disxy){
            return false;
        }
        int i = 0;
        while (OSS[p].a[i].next != 0 && OSS[p].a[OSS[p].a[i].next].dist <= disxy){
            i = OSS[p].a[i].next;
            if (OSS[p].a[i].key == x) break;
        }

        if (OSS[p].a[i].key == x){
            delete_element(p, i);
        }else {
            return false;
        }

        if (OSS[p].size_num >= M_K){
            return false;
        }
        //cout<<uniqueVertex[p]<<" before: "<<object_number[p]<<" "<<OSS[p].size_num<<endl;
        if (object_number[p] <= OSS[p].size_num ){
            //if (object_number[p] < OSS[p].size_num ) while (1);
            return false;
        }
        //cout<<"after"<<endl;
        reset_times++;
        for (int i = OSS[p].a[0].next; i != 0; i = OSS[p].a[i].next)
            delete_element(p, i);
        vector<int> a;
        a.clear();

        //get_subtree_ori(p, uniqueVertex[p], a);
        //join_subtree_ori(p, uniqueVertex[p], a);
        //join_sbt_up_kpv_pro(p, x, kpv[p], kpvd[p], kpvSize[p]);
        join_sbt_up_kpv_pro(p, x, pv[p], pvd[p], pvSize[p]);
        
        return true;
    }

    inline void delete_lazy(int x){
        if (is_current_object[x] == 0) return;
            //return (tree_height+1);
        is_current_object[x] = 0;

        int p = belong[x];
        curup_stamp++;

        for(int i=0;i<posSize[p]-1;i++){
            curup_dist[pos[p][i]] = dis[p][i];
            curup_affect[pos[p][i]] = curup_stamp;//curup_affect 存在的意义是计算disxy
        }
        curup_affect[x] = curup_stamp;
        //int i =0;
        //cout<<"delete x: "<<x<<endl;
        while (p>=0){
            object_number[p]--;
            delete_lazy(p, x, curup_dist[uniqueVertex[p]]);
            p = pa[p];
            for(int i=0;i<posSize[p]-1;i++){
                //是不是fv
                if (curup_affect[pos[p][i]] == curup_stamp) {
                    int cur_dis = dis[p][i] + curup_dist[uniqueVertex[p]];
                    if (curup_dist[pos[p][i]] > cur_dis) curup_dist[pos[p][i]] = cur_dis;
                    //continue;
                }else{
                    //curup_dist[uniqueVertex[p]] 是 此时fv到x的距离
                    curup_dist[pos[p][i]] = dis[p][i] + curup_dist[uniqueVertex[p]];
                    curup_affect[pos[p][i]] = curup_stamp;
                }
                
            }
        }
        //cout<<"reset:"<< reset_times <<endl;

        return; //return highest_up;
    }

    /// after delete x 然后 query
    inline int query_af_delete_k(int q, int x){
        vector<int> anc; anc.clear();
        int p = belong[q];
        //int i =0;
        //cout<<"delete x: "<<x<<endl;
        while (p>=0){
            anc.push_back(p);
            p = pa[p];
        }
        int j = anc.size()-1;
        for(;j>=0;j--){
            //join_sbt_down_kfv_pro

            int i = 0;
            while (OSS[p].a[i].next != 0){
                i = OSS[p].a[i].next;
                if (OSS[p].a[i].key == x) break;
            }

            if (OSS[p].a[i].key == x){
                delete_element(p, i);
            }else {
                return 0;
            }

            if (OSS[p].size_num >= M_K){
                return false;
               }
            if (object_number[p] <= OSS[p].size_num ){
                return 0;
            }
            //cout<<"after"<<endl;
            for (int i = OSS[p].a[0].next; i != 0; i = OSS[p].a[i].next)
                delete_element(p, i);
            join_sbt_down_kfv_pro(anc[j], uniqueVertex[anc[j]], kfv[anc[j]], kfvd[anc[j]], kfvSize[anc[j]]);
        }
        
        return 0; //return highest_up;
        
    }
    // x : deleted vertex
    // return false: 不需要进行重新遍历进行query
    inline bool query_af_smart_delete(int q, int x){
        int p = belong[q];
        int i = 0;
        while (OSS[p].a[i].next != 0){
            i = OSS[p].a[i].next;
            if (OSS[p].a[i].key == x) break;
        }

        if (OSS[p].a[i].key == x){
            delete_element(p, i);
        }else {
            return false;
        }

        if (OSS[p].size_num >= M_K){
            return false;
        }
        if (object_number[p] <= OSS[p].size_num ){
            return false;
        }
        reset_times++;
        for (int i = OSS[p].a[0].next; i != 0; i = OSS[p].a[i].next)
            delete_element(p, i);

        //get_subtree_ori(p, uniqueVertex[p], a);
        //join_subtree_ori(p, uniqueVertex[p], a);
        join_sbt_up_kpv_pro(p, x, kpv[p], kpvd[p], kpvSize[p]);
        //join_sbt_up_kpv_pro(p, x, pv[p], pvd[p], pvSize[p]);
        
        return true;
    }



    inline int query_af_mix(){
        return 0;
    }





    static bool object_compare(int a, int b){
        if (current_distance[a] < current_distance[b])
            return true;
        else return false;
    }
    void OSS_push_back(int p, int key, int dist){
        //    printf("p, key, dist: %d %d %d\n", p, key, dist);
        list_node _a;
        _a.previous = OSS[p].a[0].previous;
        _a.next = 0;
        _a.key = key;
        _a.dist = dist;
        OSS[p].a.push_back(_a);
        OSS[p].a[_a.previous].next = OSS[p].a.size() - 1;
        OSS[p].a[_a.next].previous = OSS[p].a.size() - 1;
        OSS[p].size_num++;
    }
    void OSS_push_front(int p, int key, int dist){
        list_node _a;
        _a.previous = 0;
        _a.next = OSS[p].a[0].next;
        _a.key = key;
        _a.dist = dist;
        OSS[p].a.push_back(_a);
        OSS[p].a[_a.previous].next = OSS[p].a.size() - 1;
        OSS[p].a[_a.next].previous = OSS[p].a.size() - 1;
        OSS[p].size_num++;
    }
    void OSS_global_push_back(int p, int key, int dist){
        //    printf("p, key, dist: %d %d %d\n", p, key, dist);
        list_node _a;
        _a.previous = OSS_global[p].a[0].previous;
        _a.next = 0;
        _a.key = key;
        _a.dist = dist;
        OSS_global[p].a.push_back(_a);
        OSS_global[p].a[_a.previous].next = OSS_global[p].a.size() - 1;
        OSS_global[p].a[_a.next].previous = OSS_global[p].a.size() - 1;
        OSS_global[p].size_num++;
    }
    void OSS_global_push_front(int p, int key, int dist){
        list_node _a;
        _a.previous = 0;
        _a.next = OSS_global[p].a[0].next;
        _a.key = key;
        _a.dist = dist;
        OSS_global[p].a.push_back(_a);
        OSS_global[p].a[_a.previous].next = OSS_global[p].a.size() - 1;
        OSS_global[p].a[_a.next].previous = OSS_global[p].a.size() - 1;
        OSS_global[p].size_num++;
    }
    
    //delete -- change
    void get_subtree(int p, int key, vector<int> &a){
        //printf("subtree p, key, a.size(): %d %d %d\n", p, key, a.size());
        bool is_containing = false;
        int x = uniqueVertex[p];
        if (x == key)
            is_containing = true;
        else {
            for (int i = 0; i < posSize[p]; i++){
                //printf("pos[p][i]: %d\n", pos[p][i]);
                if (pos[p][i] == key){
                    is_containing = true;
                    break;
                }
            }
        }
        //printf("is_containing: %d\n", is_containing);
        if (is_containing){
            a.push_back(p);

        //printf("a.size(), chSize[p]: %d %d\n", a.size(), chSize[p]);
        for (int i = 0; i < chSize[p]; i++)
            get_subtree(ch[p][i], key, a);
        }

        //int x = uniqueVertex[p];
        

    }
    void get_subtree_ori(int p, int key, vector<int> &a){
        //printf("subtree p, key, a.size(): %d %d %d\n", p, key, a.size());
        
        bool is_containing = false;
        int x = uniqueVertex[p];
        if (x == key)
            is_containing = true;
        else {
            for (int i = 0; i < posSize[p]; i++){
                //printf("pos[p][i]: %d\n", pos[p][i]);
                if (pos[p][i] == key){
                    is_containing = true;
                    break;
                }
            }
        }
        //printf("is_containing: %d\n", is_containing);
        if (is_containing){
            a.push_back(p);

        //printf("a.size(), chSize[p]: %d %d\n", a.size(), chSize[p]);
        for (int i = 0; i < chSize[p]; i++)
            get_subtree(ch[p][i], key, a);
        }
    }
    void join_subtree_ori(int p, int x, vector<int> &a){
        //printf("join_subtree  x, a.size():  %d %d\n",  x, a.size());
        //priority_queue<PT> Q;
        int pin =1;
        prio_queue Q;
        while (!Q.empty())
            Q.pop();
        vector<int> iter;
        iter.clear();
        iter.push_back(0);
        current_stamp++;
        //如果 x \notin candidate set
        current_distance[x] = 0;

        //cout<<"before circle current_stamp: "<<current_stamp<<endl;
        //取all 第一个
        //if(p == 67086) cout<< "X(u): ";
        for (int i = 1; i < a.size(); i++){
            int a_x = uniqueVertex[a[i]];
            //if(p == 67086) cout<<uniqueVertex[a[i]]<<" "<<endl;
            iter.push_back(OSS[a[i]].a[0].next);
            int t;

            int dis_orgt_x = distanceQuery(a_x,x);
            //if(p == 67086) cout<<"weight: "<<dis_orgt_x<<endl;
            int con =0;
            while (iter[i] != 0){
                con++;
                t = OSS[a[i]].a[iter[i]].key;
                //if(p == 67086) cout<<a_x<<"' "<<con<<"st key"<< t<<endl;
                //第一个元素是自己 distanceQuery 直接取  如果第一个元素不是自己呢？就 [p, org_t] + [org_t, t]
                if (t == uniqueVertex[a[i]]){
                    if(current_state[t] != current_stamp){
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_orgt_x;
                        break;// else if 这边确认一下是否有distance需要更新的情况！！！！！！
                    }else if(current_distance[t] > dis_orgt_x){
                        current_distance[t] = dis_orgt_x;
                        iter[i] = OSS[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS[a[i]].a[iter[i]].next;
                }else{
                    if(con==1) current_distance[a_x] = dis_orgt_x;
                    int dis_t_x = current_distance[a_x] + OSS[a[i]].a[iter[i]].dist;
                    if(current_state[t] != current_stamp){
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_t_x;
                        break;
                    }else if(current_distance[t] > dis_t_x){
                        current_distance[t] = dis_t_x;
                        iter[i] = OSS[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS[a[i]].a[iter[i]].next;
                }
                //if(p == 67086) cout<<a_x<<"' "<<con<<"st dist"<< current_distance[t]<<endl;
            }
            if (iter[i] != 0){
                //Q.push(PT(current_distance[t], i));
                Q.push(DN(&current_distance[t], i));
                //cout << "push: " << p << ", " << a[i] << ", " << current_distance[t] << ", " << OSS[a[i]].a[iter[i]].dist << endl;
                
            }
        }
        //if(p == 67086) cout<<endl;

        vector<int> b;
        b.clear();
        for (int i = 0; i < int( RESERVE_TIME * M_K ); i++){
            if (!Q.empty()){
                //PT pt = Q.top();
                DN pt = Q.top();
                Q.pop();
                //这个 org_t 是对的 如果从OSS 取第一个不总是对的
                int org_t = uniqueVertex[a[pt.x]];
                //a中 元素 对应的OSS
                b.push_back(OSS[a[pt.x]].a[iter[pt.x]].key);
                //cout << "pop: " << p << ", " << OSS[a[pt.x]].a[iter[pt.x]].key << ", " << pt.dis << endl;
                int t;
                while (iter[pt.x] != 0){
                    t = OSS[a[pt.x]].a[iter[pt.x]].key;
                    //cout << "a[pt.x]: " << a[pt.x] << ", iter[pt.x]: " << iter[pt.x] << endl;
                    //cout << current_state[t] << " " << current_stamp << " " << current_distance[t] << " " << distanceQuery(t, x) << endl;
                    // x, org_t + org_t, t
                    int pdis = current_distance[org_t] + OSS[a[pt.x]].a[iter[pt.x]].dist;
                    if (current_state[t] != current_stamp){
                        current_state[t] = current_stamp;
                        current_distance[t] = pdis;
                        break;
                    }else if(current_distance[t] > pdis){
                        current_distance[t] = pdis;
                        iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                    }
                    else iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                }
                if (iter[pt.x] != 0){
                    //Q.push((current_distance[t], pt.x));
                    Q.push(DN(&current_distance[t], pt.x));
                    //cout << "push: " << p << ", " << a[pt.x] << ", " << current_distance[t]<< ", " << OSS[a[pt.x]].a[iter[pt.x]].dist << endl;
                    //        if (OSS[a[pt.x]].a[iter[pt.x]].key == 258384){
                    //        cout << a[pt.x] << " " << uniqueVertex[a[pt.x]] << endl;
                    //        }
                    }
                //    else cout << pt.x << " " << a[pt.x] << " end " << endl;
            }
            else break;
        }
        //    cout << endl;
        //sort(b.begin(), b.end(), object_compare);
        if(pin) cout<<x<<" P: ";
        for (int i = 0; i < b.size(); i++){
            //cout <<" key: "<< b[i] << " dist: "<< current_distance[b[i]]<<endl;
            OSS_push_back(p, b[i], current_distance[b[i]]);
            if(pin) cout<<"("<<b[i]<<","<<current_distance[b[i]]<<") ";
            //hash.insert_node(p, b[i], OSS[p].a.size() - 1);
        }if(pin) cout<<endl;
    }
    void dfs_neighbor_ori(int p){//dfs_nbr_down_ori
        //printf("dfs_neighbor: %d\n", p);
        vector<int> a;
        a.clear();
        // p: tree construction order
        // x: original vertex id
        int x = uniqueVertex[p];
        if (is_current_object[x] == 1){
            OSS_push_front(p, x, 0);
        }
        for (int i = 0; i < chSize[p]; i++){
            dfs_neighbor_ori(ch[p][i]);
        }
        get_subtree_ori(p, x, a);
        //if(p == 13424) cout<< "coming join_subtree_ori"<<endl;
        join_subtree_ori(p, x, a);
        //double_objects: double check
        
        if (!double_objects(p)){
            cout<<"p:"<<p<<endl;
            print(p);
            stop();
        }
    }
    void get_sbt_ori(int p, int key, vector<int> &a){
        //printf("p, key, a.size(): %d %d %d\n", p, key, a.size());
        //int x = uniqueVertex[p];
        //a.push_back(belong[pos[p][posSize[p]-1]]);
        //if(belong[pos[p][posSize[p]-1]] != p) cout<<"fail";

        a.push_back(p);
        for (int i=0; i<posSize[p]-1; i++){
            a.push_back(belong[pos[p][i]]);
        }
    }
    void join_sbt_ori(int p, int x, vector<int> &a){
        //printf("join_sbt p, x, a.size(): %d %d %d\n", p, x, a.size());
        int pin =1;
        //priority_queue<PT> Q;
        prio_queue Q;
        while (!Q.empty())
            Q.pop();
        current_stamp++;
        vector<int> uV;
        uV.clear();
        for (int i =0; i<a.size(); i++ ){
            uV.push_back(uniqueVertex[a[i]]);
        }
        vector<int> iter;
        iter.clear();
        iter.push_back(OSS[a[0]].a[0].next);
        //cout<<"OSS[a[0]].a[0].next: "<< OSS[a[0]].a[0].next<<endl;
        //iter.push_back(0);
        int t;

        //初始化 把自己partial 的第一个存进去
        //存在这一步是为了防止当前p 不在candidateset里面
        current_distance[x] = 0;
        //current_state[x]= current_stamp; 不需要 是因为 就是记录距离
        //cout<<"x:"<<x<<endl;
        while (iter[0] != 0){
                t = OSS[a[0]].a[iter[0]].key;
                if (current_state[t] != current_stamp){
                    current_state[t] = current_stamp;
                    current_distance[t] = OSS[a[0]].a[iter[0]].dist;
                    break;
                }
                else iter[0] = OSS[a[0]].a[iter[0]].next;
            }
        if (iter[0] != 0){
            Q.push(DN(&current_distance[t], 0));
        }
        
        
        //直接subtree
        for (int i = 1; i < a.size(); i++){
            //cout<<"i:"<<i<<endl;
            iter.push_back(OSS_global[a[i]].a[0].next);
            int dis_orgt_x = distanceQuery(x,uV[i]);
            int x_a = uV[i];
            
            int con =0;
            while (iter[i] != 0){
                con++;
                t = OSS_global[a[i]].a[iter[i]].key;
                if (t == uV[i]){ // t \in X(i)
                    if(current_state[t] != current_stamp){
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_orgt_x;
                        break;
                    }else if(current_distance[t] > dis_orgt_x){
                        current_distance[t] = dis_orgt_x;
                        iter[i] = OSS_global[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS_global[a[i]].a[iter[i]].next;
                }else{
                    if (con ==1) current_distance[x_a] = dis_orgt_x;
                    int dis_t_x = current_distance[x_a] + OSS_global[a[i]].a[iter[i]].dist;
                    if(current_state[t] != current_stamp){
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_t_x;
                        break;
                    }else if(current_distance[t] > dis_t_x){
                        current_distance[t] = dis_t_x;
                        iter[i] = OSS_global[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS_global[a[i]].a[iter[i]].next;
                }
            }
            if (iter[i] != 0){
                Q.push(DN(&current_distance[t], i));
            }
        }
        
        vector<int> b;
        b.clear();
        for (int i = 0; i < int( RESERVE_TIME * M_K ); i++){
            if (!Q.empty()){
                DN pt = Q.top();
                Q.pop();
                int org_t = uV[pt.x]; // 是 key
                
                if (a[pt.x] == p){
                    b.push_back(OSS[a[pt.x]].a[iter[pt.x]].key);
                }else{
                    b.push_back(OSS_global[a[pt.x]].a[iter[pt.x]].key);
                }
                int t;
                while (iter[pt.x] != 0){
                    if (a[pt.x] == p){
                        t = OSS[a[pt.x]].a[iter[pt.x]].key;
                        int pdis = current_distance[org_t] + OSS[a[pt.x]].a[iter[pt.x]].dist;
                        if (current_state[t] != current_stamp){
                            current_state[t] = current_stamp;
                            current_distance[t] = pdis;
                            break;
                        }else if(current_distance[t] > pdis){
                            current_distance[t] = pdis;
                            iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                        }else iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                    }else{
                        t = OSS_global[a[pt.x]].a[iter[pt.x]].key;
                        int pdis = current_distance[org_t] + OSS_global[a[pt.x]].a[iter[pt.x]].dist;
                        if (current_state[t] != current_stamp){
                            current_state[t] = current_stamp;
                            current_distance[t] = pdis;
                            break;
                        }else if(current_distance[t] > pdis){
                            current_distance[t] = pdis;
                            iter[pt.x] = OSS_global[a[pt.x]].a[iter[pt.x]].next;
                        }else iter[pt.x] = OSS_global[a[pt.x]].a[iter[pt.x]].next;
                    }
                }
                if (iter[pt.x] != 0){
                    Q.push(DN(&current_distance[t], pt.x));
                }
            }else break;
        }
        //sort(b.begin(), b.end(), object_compare);
        //distanceInt = (int*)malloc(sizeof(int) * (M_K));
        //keyInt = (int*)malloc(sizeof(int) * (M_K));
        if(pin) cout<<"p: "<<p <<" x: "<<x<<" G: ";
        for (int i = 0; i < b.size(); i++){
            OSS_global_push_back(p, b[i], current_distance[b[i]]);
            //distanceInt[i] = current_distance[b[i]];
            //keyInt[i] = b[i];
            if(pin) cout<<"("<<b[i]<<","<<current_distance[b[i]]<<") ";
            //if(pin) cout<<"("<<keyInt[i]<<","<<distanceInt[i]<<") ";
            //hash.insert_node(p, b[i], OSS_global[p].a.size() - 1);
        }
        if(pin) cout<<endl;
        //fwrite(distanceInt, SIZEOFINT, M_K, fout);
        //fwrite(keyInt, SIZEOFINT, M_K, fout);
    }
    void dfs_nbr_down_ori(int p){
        //printf("dfs_nbr: %d\n", p);
        vector<int> a;
        a.clear();
        int x = uniqueVertex[p];

        get_sbt_ori(p, x, a);
        join_sbt_ori(p, x, a);

        if (!double_objects_ori(p)){
            print(p);
            stop();
        }
        for (int i = 0; i < chSize[p]; i++){
            dfs_nbr_down_ori(ch[p][i]);
        }
    }
    void get_sbt_down(int p, int key, vector<int> &a){
        //printf("p, key, a.size(): %d %d %d\n", p, key, a.size());
        a.push_back(p);
        for (int i=0; i<posSize[p]-1; i++){
            a.push_back(belong[pos[p][i]]);
        }
    }
    void join_sbt_down(int p, int x, vector<int> &a){
        //printf("join_sbt p, x, a.size(): %d %d %d\n", p, x, a.size());
        int pin =0;
        prio_queue Q;
        while (!Q.empty())
            Q.pop();
        current_stamp++;
        vector<int> uV;
        uV.clear();
        for (int i =0; i<a.size(); i++ ){
            uV.push_back(uniqueVertex[a[i]]);
        }
        vector<int> iter;
        iter.clear();
        iter.push_back(OSS[a[0]].a[0].next);
        int t;

        //初始化 把自己partial 的第一个存进去  存在这一步是为了防止当前p 不在candidateset里面
        current_distance[x] = 0;
        while (iter[0] != 0){
                t = OSS[a[0]].a[iter[0]].key;
                if (current_state[t] != current_stamp){
                    current_state[t] = current_stamp;
                    current_distance[t] = OSS[a[0]].a[iter[0]].dist;
                    break;
                }
                else iter[0] = OSS[a[0]].a[iter[0]].next;
            }
        if (iter[0] != 0){
            Q.push(DN(&current_distance[t], 0));
        }
        
        //直接subtree
        for (int i = 1; i < a.size(); i++){
            //cout<<"i:"<<i<<endl;
            iter.push_back(OSS_global[a[i]].a[0].next);
            int dis_orgt_x = distanceQuery(x,uV[i]);
            int x_a = uV[i];
            
            int con =0;
            while (iter[i] != 0){
                con++;
                t = OSS_global[a[i]].a[iter[i]].key;
                if (t == uV[i]){ // t \in X(i)
                    if(current_state[t] != current_stamp){
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_orgt_x;
                        break;
                    }else if(current_distance[t] > dis_orgt_x){
                        current_distance[t] = dis_orgt_x;
                        iter[i] = OSS_global[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS_global[a[i]].a[iter[i]].next;
                }else{
                    if (con ==1) current_distance[x_a] = dis_orgt_x;
                    int dis_t_x = current_distance[x_a] + OSS_global[a[i]].a[iter[i]].dist;
                    if(current_state[t] != current_stamp){
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_t_x;
                        break;
                    }else if(current_distance[t] > dis_t_x){
                        current_distance[t] = dis_t_x;
                        iter[i] = OSS_global[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS_global[a[i]].a[iter[i]].next;
                }
            }
            if (iter[i] != 0){
                Q.push(DN(&current_distance[t], i));
            }
        }
        
        vector<int> b;
        b.clear();
        for (int i = 0; i < int( RESERVE_TIME * M_K ); i++){
            if (!Q.empty()){
                DN pt = Q.top();
                Q.pop();
                int org_t = uV[pt.x]; // 是 key
                
                if (a[pt.x] == p){
                    b.push_back(OSS[a[pt.x]].a[iter[pt.x]].key);
                }else{
                    b.push_back(OSS_global[a[pt.x]].a[iter[pt.x]].key);
                }
                int t;
                while (iter[pt.x] != 0){
                    if (a[pt.x] == p){
                        t = OSS[a[pt.x]].a[iter[pt.x]].key;
                        int pdis = current_distance[org_t] + OSS[a[pt.x]].a[iter[pt.x]].dist;
                        if (current_state[t] != current_stamp){
                            current_state[t] = current_stamp;
                            current_distance[t] = pdis;
                            break;
                        }else if(current_distance[t] > pdis){
                            current_distance[t] = pdis;
                            iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                        }else iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                    }else{
                        t = OSS_global[a[pt.x]].a[iter[pt.x]].key;
                        int pdis = current_distance[org_t] + OSS_global[a[pt.x]].a[iter[pt.x]].dist;
                        if (current_state[t] != current_stamp){
                            current_state[t] = current_stamp;
                            current_distance[t] = pdis;
                            break;
                        }else if(current_distance[t] > pdis){
                            current_distance[t] = pdis;
                            iter[pt.x] = OSS_global[a[pt.x]].a[iter[pt.x]].next;
                        }else iter[pt.x] = OSS_global[a[pt.x]].a[iter[pt.x]].next;
                    }
                }
                if (iter[pt.x] != 0){
                    Q.push(DN(&current_distance[t], pt.x));
                }
            }else break;
        }
        //sort(b.begin(), b.end(), object_compare);
        //distanceInt = (int*)malloc(sizeof(int) * (M_K));
        //keyInt = (int*)malloc(sizeof(int) * (M_K));
        if(pin) cout<<"p: "<<p <<" x: "<<x<<" G: ";
        for (int i = 0; i < b.size(); i++){
            OSS_global_push_back(p, b[i], current_distance[b[i]]);
            //distanceInt[i] = current_distance[b[i]];
            //keyInt[i] = b[i];
            if(pin) cout<<"("<<b[i]<<","<<current_distance[b[i]]<<") ";
            //if(pin) cout<<"("<<keyInt[i]<<","<<distanceInt[i]<<") ";
            //hash.insert_node(p, b[i], OSS_global[p].a.size() - 1);
        }
        if(pin) cout<<endl;
        //fwrite(distanceInt, SIZEOFINT, M_K, fout);
        //fwrite(keyInt, SIZEOFINT, M_K, fout);
    }

    int up_cand_size, up_cand_time;
    long down_cand_size, down_cand_time;
    
    void join_sbt_up_kpv(int p, int x, int* pv, int* pvd, int pvsize){
        int pin =0;

        vector<int> a; a.clear();
        deque<DN> Q; Q.clear();
        vector<int> iter; iter.clear();

        current_stamp++;
        current_distance[x] = 0;

        //取all 第一个
        for (int i = 0; i < pvsize; i++){
            a.push_back(belong[pv[i]]);
            iter.push_back(OSS[a[i]].a[0].next);
            int t;
            int dis_orgt_x = pvd[i];
            int con =0;
            while (iter[i] != 0){
                up_cand_time++;
                con++;
                t = OSS[a[i]].a[iter[i]].key;
                //第一个元素是自己 distanceQuery 直接取  如果第一个元素不是自己呢？就 [p, org_t] + [org_t, t]
                if (t == uniqueVertex[a[i]]){
                    if(current_state[t] != current_stamp){
                        up_cand_size++;
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_orgt_x;
                        break; //else if 这边确认一下是否有distance需要更新的情况！！！！！！
                    }else if(current_distance[t] > dis_orgt_x){
                        current_distance[t] = dis_orgt_x;
                        iter[i] = OSS[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS[a[i]].a[iter[i]].next;
                }else{
                    if(con==1) current_distance[pv[i]] = dis_orgt_x;
                    int dis_t_x = current_distance[pv[i]] + OSS[a[i]].a[iter[i]].dist;
                    if(current_state[t] != current_stamp){
                        up_cand_size++;
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_t_x;
                        break;
                    }else if(current_distance[t] > dis_t_x){
                        current_distance[t] = dis_t_x;
                        iter[i] = OSS[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS[a[i]].a[iter[i]].next;
                }
            }
            if (iter[i] != 0){
                Q.push_back(DN(&current_distance[t], i));
            }
        }
        vector<int> b; b.clear();

        for (int i = 0; i < int( RESERVE_TIME * M_K ); i++){
            if (!Q.empty()){
                sort(Q.begin(),Q.end());
                DN pt = Q.front();
                Q.pop_front();
                //这个 org_t 是对的 如果从OSS 取第一个不总是对的
                //int org_t = uniqueVertex[a[pt.x]];
                int org_t = pv[pt.x];
                b.push_back(OSS[a[pt.x]].a[iter[pt.x]].key);
                int t;
                while (iter[pt.x] != 0){
                    up_cand_time++;
                    t = OSS[a[pt.x]].a[iter[pt.x]].key;
                    // x, org_t + org_t, t
                    int pdis = current_distance[org_t] + OSS[a[pt.x]].a[iter[pt.x]].dist;
                    if (current_state[t] != current_stamp){
                        up_cand_size++;
                        current_state[t] = current_stamp;
                        current_distance[t] = pdis;
                        break;
                    }else if(current_distance[t] > pdis){
                        current_distance[t] = pdis;
                        iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                    }else iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                }
                if (iter[pt.x] != 0){
                    Q.push_back(DN(&current_distance[t], pt.x));
                }
            } else break;
        }
        if(pin) cout<<x<<" P: ";
        for (int i = 0; i < b.size(); i++){
            OSS_push_back(p, b[i], current_distance[b[i]]);
            if(pin) cout<<"("<<b[i]<<","<<current_distance[b[i]]<<") ";
        }if(pin) cout<<endl;
    }
    void dfs_up(int p){

        int x = uniqueVertex[p];
        if (is_current_object[x] == 1){
            OSS_push_front(p, x, 0);
        }
        for (int i = 0; i < chSize[p]; i++){
            dfs_up(ch[p][i]);
        }
        join_sbt_up_kpv(p, x, kpv[p], kpvd[p], kpvSize[p]);
        /*if (!double_objects(p)){
            cout<<"p:"<<p<<endl;
            print(p);
            stop();
        }*/
    }
    void join_sbt_down_kfv(int p, int x, int* fv, int* fvd, int fvSize){
        //printf("join_sbt p, key, a.size(): %d %d %d\n", p, x, fvSize);
        int pin = 0;
        deque<DN> Q;
        Q.clear();
        vector<int> a;
        a.clear();
        current_stamp++;
        vector<int> iter;
        iter.clear();
        iter.push_back(OSS[p].a[0].next);
        int t;
        //初始化 把自己partial 的第一个存进去 //存在这一步是为了防止当前p 不在candidateset里面
        current_distance[x] = 0;
        //current_state[x]= current_stamp; 不需要 是因为 就是记录距离
        
        a.push_back(belong[fv[fvSize-1]]);
        while (iter[0] != 0){
            down_cand_time++;
            t = OSS[p].a[iter[0]].key;
            if (current_state[t] != current_stamp){
                down_cand_size++;
                current_state[t] = current_stamp;
                current_distance[t] = OSS[p].a[iter[0]].dist;
                break;
            }else iter[0] = OSS[p].a[iter[0]].next;
        }
        if (iter[0] != 0){
            Q.push_back(DN(&current_distance[t], 0));
        }
        //如果 p 本身index为空 iter怎么办？？
        
        //直接subtree
        for (int i = 1; i < fvSize; i++){
            a.push_back(belong[fv[i-1]]);
            iter.push_back(OSS_global[a[i]].a[0].next);
            int dis_orgt_x = fvd[i-1];//= distanceQuery(x,uV[i]);'
            int x_a = fv[i-1];
            int con =0;
            while (iter[i] != 0){
                down_cand_time++;
                con++;
                t = OSS_global[a[i]].a[iter[i]].key;
                if (t == x_a){ // t \in X(i)
                    if(current_state[t] != current_stamp){
                        down_cand_size++;
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_orgt_x;
                        break;
                    }else if(current_distance[t] > dis_orgt_x){
                        current_distance[t] = dis_orgt_x;
                        iter[i] = OSS_global[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS_global[a[i]].a[iter[i]].next;
                }else{
                    if (con ==1) current_distance[x_a] = dis_orgt_x;
                    int dis_t_x = current_distance[x_a] + OSS_global[a[i]].a[iter[i]].dist;
                    if(current_state[t] != current_stamp){
                        down_cand_size++;
                        current_state[t] = current_stamp;
                        current_distance[t] = dis_t_x;
                        break;
                    }else if(current_distance[t] > dis_t_x){
                        current_distance[t] = dis_t_x;
                        iter[i] = OSS_global[a[i]].a[iter[i]].next;
                    }else iter[i] = OSS_global[a[i]].a[iter[i]].next;
                }
            }
            if (iter[i] != 0){
                Q.push_back(DN(&current_distance[t], i));
            }
        }
        int k =0;
        for (int i = 0; i < int( RESERVE_TIME * M_K ); i++){
            if (!Q.empty()){
                sort(Q.begin(),Q.end());
                DN pt = Q.front();
                Q.pop_front();
                int org_t = uniqueVertex[a[pt.x]]; // 是 key
                
                if (a[pt.x] == p){
                    //b.push_back(OSS[a[pt.x]].a[iter[pt.x]].key);
                    k = OSS[a[pt.x]].a[iter[pt.x]].key;
                    OSS_global_push_back(p, k, current_distance[k]);
                }else{
                    //b.push_back(OSS_global[a[pt.x]].a[iter[pt.x]].key);
                    k = OSS_global[a[pt.x]].a[iter[pt.x]].key;
                    OSS_global_push_back(p, k, current_distance[k]);
                }
                int t;
                while (iter[pt.x] != 0){
                    down_cand_time++;
                    if (a[pt.x] == p){
                        //if(p == 152770) cout<<"come p"<<endl;
                        t = OSS[a[pt.x]].a[iter[pt.x]].key;
                        int pdis = current_distance[org_t] + OSS[a[pt.x]].a[iter[pt.x]].dist;
                        if (current_state[t] != current_stamp){
                            down_cand_size++;
                            current_state[t] = current_stamp;
                            current_distance[t] = pdis;
                            break;
                        }else if(current_distance[t] > pdis){
                            current_distance[t] = pdis;
                            iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                        }else iter[pt.x] = OSS[a[pt.x]].a[iter[pt.x]].next;
                    }else{
                        t = OSS_global[a[pt.x]].a[iter[pt.x]].key;
                        int pdis = current_distance[org_t] + OSS_global[a[pt.x]].a[iter[pt.x]].dist;
                        if (current_state[t] != current_stamp){
                            down_cand_size++;
                            current_state[t] = current_stamp;
                            current_distance[t] = pdis;
                            break;
                        }else if(current_distance[t] > pdis){
                            current_distance[t] = pdis;
                            iter[pt.x] = OSS_global[a[pt.x]].a[iter[pt.x]].next;
                        }else iter[pt.x] = OSS_global[a[pt.x]].a[iter[pt.x]].next;
                    }
                }
                if (iter[pt.x] != 0){
                    Q.push_back(DN(&current_distance[t], pt.x));
                }
            }else break;
        }
        //int pri_out =1;
        //if(pri_out) distanceInt = (int*)malloc(sizeof(int) * (M_K));
        //if(pri_out) keyInt = (int*)malloc(sizeof(int) * (M_K));
        if(pin )  cout<<"p: "<<p <<" x: "<<x<<" G: ";
        //for (int i = 0; i < b.size(); i++){
            //OSS_global_push_back(p, b[i], current_distance[b[i]]);
            //if(pri_out) distanceInt[i] = current_distance[b[i]];
            //if(pri_out) keyInt[i] = b[i];
            //if(pin) cout<<"("<<b[i]<<","<<current_distance[b[i]]<<") ";
        //}
        if(pin) cout<<endl;
        //if(pri_out) fwrite(distanceInt, SIZEOFINT, M_K, fout);
        //if(pri_out) fwrite(keyInt, SIZEOFINT, M_K, fout);
    }
    void dfs_down(int p){
        //printf("dfs_nbr: %d\n", p);

        join_sbt_down_kfv(p, uniqueVertex[p], kfv[p], kfvd[p], kfvSize[p]);

        /*if (!double_objects_ori(p)){
            //cout<<"p: "<<p<<endl;
            print(p);
            stop();
        }*/
        for (int i = 0; i < chSize[p]; i++){
            dfs_down(ch[p][i]);
        }
    }

    void join_sbt_up_kpv_pro(int p, int x, int* pv, int* pvd, int pvsize){
        //int pin =1;
        //if(pin) printf("join_sub_up p, x, a.size(): %d %d %d\n", p, x, pvsize);
        current_stamp++;
        //如果 x \notin candidate set
        current_distance[x] = 0;
        vector<int> b; b.clear();
        //vector<int> a; a.clear();
        for (int i = 0; i < pvsize; i++){
            int org_t = pv[i];//uniqueVertex[a[i]];
            //if(pin) cout<<"org_t: "<<org_t<<endl;
            int t;
            int dis_orgt_x = pvd[i];// 这个distance 可以progress
            int pdis = 0;
            int a_i = belong[pv[i]];
            for(int j = 1; j < (OSS[a_i].size_num+1); j++ ){
                up_cand_time++;
                t = OSS[a_i].a[j].key;
                pdis = dis_orgt_x + OSS[a_i].a[j].dist;
                //if(pin) cout<<"t: "<<t<<" pdis: "<<pdis<<endl;
                if(current_state[t] != current_stamp){
                    up_cand_size++;
                    current_state[t] = current_stamp;
                    current_distance[t] = pdis;
                    b.push_back(t);
                }else if(current_distance[t] > pdis){
                    current_distance[t] = pdis;
                }
            }
        }
        sort(b.begin(), b.end(), object_compare);

        //if(pin) cout<<x<<" P: ";
        for (int i = 0; (i < b.size()) && (i < M_K); i++){
            //cout <<" key: "<< b[i] << " dist: "<< current_distance[b[i]]<<endl;
            OSS_push_back(p, b[i], current_distance[b[i]]);
            //if(pin) cout<<"("<<b[i]<<","<<current_distance[b[i]]<<") ";
        }//if(pin) cout<<endl;
    }
    void dfs_up_pro(int p){
        int x = uniqueVertex[p];
        if (is_current_object[x] == 1){
            OSS_push_front(p, x, 0);
        }
        for (int i = 0; i < chSize[p]; i++){
            dfs_up_pro(ch[p][i]);
        }
        join_sbt_up_kpv_pro(p, x, kpv[p], kpvd[p], kpvSize[p]);
        if (!double_objects(p)){
            cout<<"p:"<<p<<endl;
            print(p);
            stop();
        }
    }
    void join_sbt_down_kfv_pro(int p, int x, int* fv, int* fvd, int fvSize){
        int pin = 0;
        //if(pin) printf("join_sbt_down p, x, a.size(): %d %d %d\n", p, x, fvSize);
        
        current_stamp++;
        int t;
        int pdis;
        current_distance[x] = 0;

        vector<int> b; b.clear();
        int a_0 = belong[fv[fvSize-1]];
        for(int j = 1; j < (OSS[a_0].size_num+1); j++ ){
            down_cand_time++;
            t = OSS[a_0].a[j].key;
            pdis = OSS[a_0].a[j].dist;
            if(current_state[t] != current_stamp){
                down_cand_size++;
                current_state[t] = current_stamp;
                current_distance[t] = pdis;
                b.push_back(t);
            }else if(current_distance[t] > pdis){
                current_distance[t] = pdis;
            }
        }
        
        for (int i = 0; i < fvSize-1; i++){
            int org_t = fv[i];//uniqueVertex[a[i]];
            int dis_orgt_x = fvd[i];//distanceQuery(org_t,x);// 这个distance 可以progress
            pdis = 0;
            int a_i = belong[fv[i]];
            for(int k = 1; k <= OSS_global[a_i].size_num; k++ ){
                down_cand_time++;
                t = OSS_global[a_i].a[k].key;
                pdis = dis_orgt_x + OSS_global[a_i].a[k].dist;
                if(current_state[t] != current_stamp){
                    down_cand_size++;
                    current_state[t] = current_stamp;
                    current_distance[t] = pdis;
                    b.push_back(t);
                }else if(current_distance[t] > pdis){
                    current_distance[t] = pdis;
                }
            }
        }
        sort(b.begin(), b.end(), object_compare);

        //distanceInt = (int*)malloc(sizeof(int) * (M_K));
        //keyInt = (int*)malloc(sizeof(int) * (M_K));
        if(pin) cout<<x<<" G: ";
        for (int i = 0; (i < b.size()) && (i < M_K); i++){
            OSS_global_push_back(p, b[i], current_distance[b[i]]);
            //distanceInt[i] = current_distance[b[i]];
            //keyInt[i] = b[i];
            if(pin) cout<<"("<<b[i]<<","<<current_distance[b[i]]<<") ";
        }
        if(pin) cout<<endl;
        //fwrite(distanceInt, SIZEOFINT, M_K, fout);
        //fwrite(keyInt, SIZEOFINT, M_K, fout);
    }
    void dfs_down_pro(int p){
        //printf("dfs_nbr: %d\n", p);
        join_sbt_down_kfv_pro(p, uniqueVertex[p], kfv[p], kfvd[p], kfvSize[p]);
        
        for (int i = 0; i < chSize[p]; i++){
            dfs_down_pro(ch[p][i]);
        }
    }

    void dfs_up_vc(int p){
        //cout<<"come vc"<<endl;
        int x = uniqueVertex[p];
        if (is_current_object[x] == 1){
            OSS_push_front(p, x, 0);
        }
        for (int i = 0; i < chSize[p]; i++){
            dfs_up_vc(ch[p][i]);
        }
        join_sbt_up_kpv_pro(p, x, pv[p], pvd[p], pvSize[p]);
        if (!double_objects(p)){
            //cout<<"p:"<<p<<endl;
            print(p);
            stop();
        }
    }
    void dfs_down_vc(int p){
        //printf("dfs_nbr: %d\n", p);
        join_sbt_down_kfv_pro(p, uniqueVertex[p], pos[p], dis[p], posSize[p]);
        
        for (int i = 0; i < chSize[p]; i++){
            dfs_down_vc(ch[p][i]);
        }
    }

    void initialize_object_ori(){
        compute_object_number();
        //printf("start initialize:\n");
        
        for (int i = 0; i < n; i++)
            for (int j = OSS[i].a[0].next; j != 0; j = OSS[i].a[j].next )
                delete_element(i, j);
        for (int i = 0; i < n; i++)
            for (int j = OSS_global[i].a[0].next; j != 0; j = OSS_global[i].a[j].next )
                delete_element_global(i, j);
        
        up_cand_size = 0;
        up_cand_time = 0;

        down_cand_size = 0;
        down_cand_time = 0;

        //if (strcmp(insert_type, "sort") == 0) dfs_sort(root, a);else
        if(strcmp(insert_type, "kvc") == 0){
            //kvc naive
            dfs_up_pro(root);
            dfs_down_pro(root);
        }else if(strcmp(insert_type, "okvc") == 0){
            //optimized kvc
            dfs_up(root);
            dfs_down(root);
        }else if(strcmp(insert_type, "vc") == 0){
            //vc naive
            dfs_up_vc(root);
            dfs_down_vc(root);
        }else{
            dfs_neighbor_ori(root);//dfs_neighbor_ori(int p){dfs_nbr_down_ori
            //cout<<"finish up"<<endl;
            dfs_nbr_down_ori(root);
        }

        float avg_up_cand_size = ((float)up_cand_size)/TreeSize;
        float avg_up_cand_time = ((float)up_cand_time)/TreeSize;
        float avg_down_cand_size = ((float)down_cand_size)/TreeSize;
        float avg_down_cand_time = ((float)down_cand_time)/TreeSize;

        cout<<"up_cand_size: "<<up_cand_size<<endl;
        cout<<"up_cand_time: "<<up_cand_time<<endl;
        cout<<"down_cand_size: "<<down_cand_size<<endl;
        cout<<"down_cand_time: "<<down_cand_time<<endl;

        printf("avg_up_cand_size: %.3lf \n", avg_up_cand_size);
        printf("avg_up_cand_time: %.3lf \n", avg_up_cand_time );
        printf("avg_down_cand_size: %.3lf \n", avg_down_cand_size );
        printf("avg_down_cand_time: %.3lf \n", avg_down_cand_time);

        /*
        vector<int> a;
        if (strcmp(insert_type, "sort") == 0) dfs_sort(root, a);
        else{
            dfs_up(root);
            dfs_down(root);
        }*/
    }

    void object_setting_ori(int n){
        //cout<<"n:" <<endl;
        is_current_object = (int*)malloc(sizeof(int) * (n + 1));
        current_distance = (int*)malloc(sizeof(int) * (n + 1));
        //group_height = (int*)malloc(sizeof(int) * (n + 1));
        current_state = (int*)malloc(sizeof(int) * (n + 1));
        current_stamp = 0;
        for (int i = 0; i <= n; i++){
            current_state[i] = 0;
            is_current_object[i] = 0;
        }
    }

    void update_setting(int n){
        //compute_object_number();
        curup_dist = (int*)malloc(sizeof(int) * (n + 1));
        curup_affect = (int*)malloc(sizeof(int) * (n + 1));
        curup_state = (int*)malloc(sizeof(int) * (n + 1));
        curup_stamp = 0;
        current_state = (int*)malloc(sizeof(int) * (n + 1));
        current_stamp = 0;
        for (int i = 0; i <= n; i++){
            curup_state[i] = 0;
            current_state[i] = 0;
        }
            
        highest_all_up = tree_height+1;
    }
    void query_setting(int n){
        //compute_object_number();
        curqu_dist = (int*)malloc(sizeof(int) * (n + 1));
        curqu_affect = (int*)malloc(sizeof(int) * (n + 1));
        curqu_state = (int*)malloc(sizeof(int) * (n + 1));
        curqu_stamp = 0;
        for (int i = 0; i <= n; i++){
            curqu_state[i] = 0;
        }
            
        //highest_all_up = tree_height+1;
    }
    void update_dist(int n){
        cur_gdis = (int*)malloc(sizeof(int) * (n + 1));
        gdist_stamp = 0;
        for (int i = 0; i <= n; i++) gdist_state[i] = 0;
    }

    void traversal(int p){
        //m = uniqueVertex[n] n: MDE逆序 m: 从根节点对应的original vertex id
        int x = uniqueVertex[p];
        if (is_current_object[x] == 1)
            object_number[p]++;
        for (int i = 0; i < chSize[p]; i++){
            traversal(ch[p][i]);
            object_number[p] += object_number[ch[p][i]];
        }
    }
    //计算 object_number 真的有用么？？？？？？ insert_object()  和 delete_object() 用了
    void compute_object_number(){
        //初始化 object_number
        object_number.resize(n + 1);
        for (int i = 0; i <= n; i++)
            object_number[i] = 0;
        //cout<<"start traveral"<<endl;
        traversal(root);
    }
    
    int * query_mark;
    int query_mark_stamp;
    vector<double> time_save;
    vector<pair<int, int>> query_o(int x, int top_k){
        time_save.clear();
        double pre_time = GetTime();
        double start_time = pre_time;
        query_mark_stamp++;
        int cnt1 = 0, cnt2 = 0, cnt3= 0;
        //printf("path_from_root[1].size(): %d\n", path_from_root[1].size());
        vector<pair<int, int> > result;
        result.clear();
        int p = belong[x];
        
        printf("x, top_k, p: %d %d %d\n", x, top_k, p);
        //printf("OSS[p].size_num, OSS[p].a[1].dist, height[p]: %d %d %d\n", OSS[p].size_num, OSS[p].a[OSS[p].a[0].next].dist, height[p]);
        vector<int> anc;
        anc.clear();
        //printf("OSS[7745].a.size(), OSS[7745].a[0].next: %d %d\n", OSS[7745].a.size(), OSS[7745].a[0].next);
        int MAX_DIS = INT_MAX;
        //return result;
        vector<int> a;
        a.clear();
        a.push_back(p);
        // 找k点所在的anc
        //cout<<
        for (int i = 0; i < posSize[p]-1; i++)
            a.push_back(belong[pos[p][i]]);
        //printf("a.size(): %d\n", a.size());
        //printf("MAX_DIS: %d\n", MAX_DIS);
        
        for (int i = 0; i < a.size(); i++){
            int q = a[i];
            if (OSS[q].size_num <= top_k)
                continue;
            tmp_dis[q] = distanceQuery(uniqueVertex[q], x);
            if (tmp_dis[q] >= MAX_DIS)
                continue;
            //如果这个anc 的OSS是除自己外空集
            if (OSS[q].a[0].next == 0)
                continue;
            int j = OSS[q].a[0].next;
            int _cnt = 1;
            while (_cnt < top_k){
                _cnt++;
                j = OSS[q].a[j].next;
                cnt2++;
            }
            //找到第topk的dis 来更新MAX_DIS
            if (MAX_DIS > tmp_dis[q] + OSS[q].a[j].dist)
                MAX_DIS = tmp_dis[q] + OSS[q].a[j].dist;
        }
        //来找MAX_DIS
        //cnt2 代表 从anc找 初步符合条件的candidate 个数 ——> 没啥用
        //cout<<"MAX_DIS !!!"<<endl;
        int max_height = height[p];
        while (p >= 0 && height[p] >= max_height){
            cnt3++;
            int t = OSS[p].a[0].next;
            
            tmp_dis[p] = distanceQuery(uniqueVertex[p], x);
            if (x==2 && p==1 ){
                tmp_dis[p] = 6;
            }
            if (x==4 && p==0 ){
                tmp_dis[p] = 6;
            }
            //printf("tmp_dis[%d] %d\n",uniqueVertex[p], tmp_dis[p]);
            if (t > 0 &&  MAX_DIS >= tmp_dis[p] + OSS[p].a[t].dist){
                anc.push_back(p);
                OSS[p].current = OSS[p].a[0].next;
                if (OSS[p].size_num >= top_k){
                    int v = OSS[p].a[0].previous;
                    int tmp = tmp_dis[p] + OSS[p].a[v].dist;
                    if (tmp < MAX_DIS)
                        MAX_DIS = tmp;
                }
            }
            if (tmp_dis[p] + cloest_higher[p] < MAX_DIS)
                if (max_height > higher[p]){
                    max_height = higher[p];
                }
            p = pa[p];
        }
        sort(anc.begin(), anc.end(), anc_compare);
        //通过利用MAX_DIS 找sub_anc的点OSS 中的candidate 并存放在anc中
        
        //    printf("anc.size(): %d\n", anc.size());
        p = belong[x];
        cnt_pre_query_time += GetTime() - pre_time;
        int _cnt = 0;
        //cout<<"topk:!!!"<<endl;
        for (int i = 0; i < top_k; i++){
            //printf("i result.size(): %d %d\n", i, result.size());
            //--------------find minimum-------------
            int k = -1, dist_k = -1;
            for (int j = 0; j < anc.size(); j++){
                _cnt++;
                int q = anc[j];
                //    printf("q: %d\n", q);
                while (OSS[q].current != 0 && query_mark[OSS[q].a[OSS[q].current].key] == query_mark_stamp)
                    OSS[q].current = OSS[q].a[OSS[q].current].next;
                if (OSS[q].current == 0)
                    continue;
                int _dist = tmp_dis[q] + OSS[q].a[OSS[q].current].dist;
                if (k < 0 || (dist_k > _dist)){
                    k = q;
                    dist_k = _dist;
                }
            }
            if (k < 0)
                break;
            result.push_back(make_pair(OSS[k].a[OSS[k].current].key, dist_k));
            
            //--------------delete and update ------------------
        
            int y = OSS[k].a[ OSS[k].current ].key;
            query_mark[y] = query_mark_stamp;
            double current_time = GetTime();
            time_save.push_back(current_time - pre_time);
            if ((i + 1) % 5 == 0)
                times_period[((i + 1) / 5) - 1].push_back(current_time - start_time);
                 //   printf("---%.6lf\n", current_time - pre_time);
            pre_time = current_time;
        }
         //   cout << "_cnt: " << _cnt << endl;
        
        return result;
    }
    
    vector<pair<int,int>> query(int x, int top_k){
        
        vector<pair<int,int>> result;
        result.clear();
        int p = belong[x];
        p = belong[x];
        for (int i = 1; i <= top_k; i++){
            result.push_back(make_pair(OSS_global[p].a[i].key, OSS_global[p].a[i].dist));
        }
        
        return result;
    }

    vector<pair<int, int>> query_naive(int x, int top_k){
        time_save.clear();
        double pre_time = GetTime();
        query_mark_stamp++;
        int cnt1 = 0, cnt2 = 0, cnt3= 0;
        vector<pair<int, int> > result;
        result.clear();
        int p = belong[x];
        
        vector<int> anc;
        anc.clear();
        int MAX_DIS = INT_MAX;
        vector<int> a;
        a.clear();
        a.push_back(p);
        for (int i = 0; i < posSize[p]; i++)
            a.push_back(belong[pos[p][i]]);
        for (int i = 0; i < a.size(); i++){
            int q = a[i];
            if (OSS[q].size_num <= top_k)
                continue;
            tmp_dis[q] = distanceQuery(uniqueVertex[q], x);
            if (tmp_dis[q] >= MAX_DIS)
                continue;
            if (OSS[q].a[0].next == 0)
                continue;
            int j = OSS[q].a[0].next;
            int _cnt = 1;
            while (_cnt < top_k){
                _cnt++;
                j = OSS[q].a[j].next;
                cnt2++;
            }
            if (MAX_DIS > tmp_dis[q] + OSS[q].a[j].dist)
                MAX_DIS = tmp_dis[q] + OSS[q].a[j].dist;
        }
        
        int max_height = height[p];
        while (p >= 0 && height[p] >= max_height){
            cnt3++;
            int t = OSS[p].a[0].next;
            tmp_dis[p] = distanceQuery(uniqueVertex[p], x);
            if (t > 0 &&  MAX_DIS >= tmp_dis[p] + OSS[p].a[t].dist){
                anc.push_back(p);
                OSS[p].current = OSS[p].a[0].next;
                if (OSS[p].size_num >= top_k){
                    int v = OSS[p].a[0].previous;
                    int tmp = tmp_dis[p] + OSS[p].a[v].dist;
                    if (tmp < MAX_DIS)
                        MAX_DIS = tmp;
                }
            }
            if (tmp_dis[p] + cloest_higher[p] < MAX_DIS)
                if (max_height > higher[p]){
                    max_height = higher[p];
                }
            p = pa[p];
        }
        sort(anc.begin(), anc.end(), anc_compare);
        p = belong[x];
        cnt_pre_query_time += GetTime() - pre_time;
        
        //--------------find minimum-------------
        //    int k = -1, dist_k = -1;
       
        a.clear();
        for (int j = 0; j < anc.size(); j++){
            cnt1++;
            int q = anc[j];
            //    printf("q: %d\n", q);
            int i = 0;
            OSS[q].current = OSS[q].a[0].next;
            while (OSS[q].current != 0 && i < top_k){
                i++;
                 //   if (OSS[q].current == 0)
                   //     break;
                int t_t = tmp_dis[q] +OSS[q].a[OSS[q].current].dist;
                //distanceQuery(q, OSS[q].a[OSS[q].current].key);
                  //  cout << t_t << " " << tmp_dis[q] << " " <<  OSS[q].a[OSS[q].current].dist << endl;
                   //     cout << q << " " << OSS[q].a[OSS[q].current].key << endl;
                  //  cout << OSS[q].a[OSS[q].current].dist << " " << endl;
                int v = OSS[q].a[OSS[q].current].key;
                //   if (v == -1){
                //        cout << q << " " << OSS[q].current << " " << OSS[q].a[OSS[q].current].key << endl;
                 //       while (1);
                 //   }
                //    cout << "q: " << q << "  v: " << v << endl;
                if (query_mark[OSS[q].a[OSS[q].current].key] == query_mark_stamp){
                    if (t_t < tmp_dis[v])
                        tmp_dis[v] = t_t;
                }
                else {
                    query_mark[v] = query_mark_stamp;
                    a.push_back(v);
                    tmp_dis[v] = t_t;
                }
                OSS[q].current = OSS[q].a[OSS[q].current].next;
                
            }
        }
        /*
        for (int i = 0; i < a.size(); i++){
            tmp_dis[a[i]] = distanceQuery(x, a[i]);
            cout << x << " " << a[i] << " " << distanceQuery(a[i], x) << endl;
        }
        */
        //    cout << "a.size(): " << a.size() << endl;
          //  for (int i = 0; i < a.size(); i++)
           //     cout << a[i] << " " << tmp_dis[a[i]] << endl;
        sort(a.begin(), a.end(), anc_compare);
        for (int i = 0; i < a.size(); i++){
            if (i >= top_k)
                break;
            result.push_back(make_pair(a[i], tmp_dis[a[i]]));
        }
        
        double current_time = GetTime();
        time_save.push_back(current_time - pre_time);

        return result;
    }
    vector<pair<int, int>> query_delay(int x, int top_k){
        time_save.clear();
        double pre_time = GetTime();
        double start_time = pre_time;
        vector<pair<int, int> > result;
        result.clear();
        int p = belong[x];
        
        //    printf("x, k, p: %d %d %d\n", x, k, p);
        vector<int> anc;
        anc.clear();
        //    printf("OSS[7745].a.size(), OSS[7745].a[0].next: %d %d\n", OSS[7745].a.size(), OSS[7745].a[0].next);
        int MAX_DIS = INT_MAX;
        vector<int> a;
        a.clear();
        a.push_back(p);
        
         //   cout << "step2"<< endl;
        for (int i = 0; i < posSize[p]; i++)
            a.push_back(belong[pos[p][i]]);
        for (int i = 0; i < a.size(); i++){
            int q = a[i];
            if (OSS[q].size_num <= top_k)
                continue;
            tmp_dis[q] = distanceQuery(uniqueVertex[q], x);
            if (tmp_dis[q] >= MAX_DIS)
                continue;
            if (OSS[q].a[0].next == 0)
                continue;
            int j = OSS[q].a[0].next;
            int _cnt = 1;
            while (j != 0 && _cnt < top_k){
                j = OSS[q].a[j].next;
            }
            if (MAX_DIS > tmp_dis[q] + OSS[q].a[j].dist)
                MAX_DIS = tmp_dis[q] + OSS[q].a[j].dist;
        }
        
         //   cout << "step3"<< endl;
        int max_height = height[p];
        while (p >= 0 && height[p] >= max_height){
            int t = OSS[p].a[0].next;
            tmp_dis[p] = distanceQuery(uniqueVertex[p], x);
            if (t > 0 &&  MAX_DIS >= tmp_dis[p] + OSS[p].a[t].dist){
                anc.push_back(p);
                OSS[p].current = OSS[p].a[0].next;
                if (OSS[p].size_num >= top_k){
                    int v = OSS[p].a[0].previous;
                    int tmp = tmp_dis[p] + OSS[p].a[v].dist;
                    if (tmp < MAX_DIS)
                        MAX_DIS = tmp;
                }
            }
            if (tmp_dis[p] + cloest_higher[p] < MAX_DIS)
                if (max_height > higher[p]){
                    max_height = higher[p];
                }
            p = pa[p];
        }
          //     printf("anc.size(): %d\n", anc.size());
        //    printf("OSS[7745].current: %d\n", OSS[7745].current);
        sort(anc.begin(), anc.end(), anc_compare);
        
          //      cout << "step4"<< endl;
        p = belong[x];
        int _cnt = 0;
        for (int i = 0; i < top_k; i++){
            /*
            while (anc.size() > 0){
                int p = anc[anc.size() - 1], t = OSS[p].a[0].next;
                if ((t == 0) || (tmp_dis[p] + OSS[p].a[t].dist > MAX_DIS))
                anc.pop_back();
                else break;
            }
             */
            //--------------find minimum-------------
            int k = -1, dist_k = -1;
            for (int j = 0; j < anc.size(); j++){
                _cnt++;
                  //      cnt1++;
                int q = anc[j];
                //        printf("q: %d\n", q);
                if (OSS[q].current == 0)
                continue;
                int _dist = distanceQuery(uniqueVertex[q], x) + OSS[q].a[OSS[q].current].dist;
                if (k < 0 || (dist_k > _dist)){
                    k = q;
                    dist_k = _dist;
                }
            }
            //    printf("k dist_k: %d %d\n", k, dist_k);
            if (k < 0)
            break;
            int y = OSS[k].a[ OSS[k].current ].key;
             //   cout << y << " " << dist_k << " " << k << endl;
            result.push_back(make_pair(y, dist_k));
            
            //--------------delete and update ------------------
            
            //-----------------------------------
            
            for (int j = 0; j < anc.size(); j++){
                _cnt++;
                int t = anc[j];
                
                if (OSS[t].a[OSS[t].current].key == y)
                    OSS[t].current = OSS[t].a[OSS[t].current].next;
                int pos = hash.get_value(t, y);
                  //         if (t == 1476 && y == 30137)
                //            cout << t << " " << pos << endl;
                if (pos >= 0){
                    OSS[t].a[ OSS[t].a[pos].previous ].next = OSS[t].a[pos].next;
                    OSS[t].a[ OSS[t].a[pos].next ].previous = OSS[t].a[pos].previous;
                    OSS[t].trash_can.push_back(pos);
                }
               
            }
            
            double current_time = GetTime();
            time_save.push_back(current_time - pre_time);
            if ((i + 1) % 5 == 0){
                times_period[((i + 1) / 5) - 1].push_back(current_time - start_time);
              //      printf("%.6lf\n", current_time - start_time);
            }
               //    printf("%.6lf\n", current_time - pre_time);
            pre_time = current_time;
        }
        //    cout << "_cnt: " << _cnt << endl;
         //   get_min_double(time_save);
        
        for (int i = 0; i < anc.size(); i++){
            int q = anc[i];
            for (int j = OSS[q].trash_can.size() - 1; j >= 0; j--){
                int pos = OSS[q].trash_can[j];
                OSS[q].a[ OSS[q].a[pos].next ].previous = pos;
                OSS[q].a[ OSS[q].a[pos].previous ].next = pos;
            }
            OSS[q].trash_can.clear();
        }
        
        return result;
    }
    void print(int root){
        //cout<<"current_p: "<<root<<endl;
        int cnt = 0;
        for (int i = OSS[root].a[0].next; i != 0; i = OSS[root].a[i].next){
            printf("(%d, %d)", OSS[root].a[i].key, OSS[root].a[i].dist);
            cnt++;
        }
        printf("\n");

        if (cnt != OSS[root].size_num){
            cout << "cnt: " << cnt << "     " << "OSS[root].size_num: " << OSS[root].size_num << endl;
            while (1);
        }
    }
    bool double_objects(int p){
        for (int i = OSS[p].a[0].next; i != 0; i = OSS[p].a[i].next){
            //a[i] 当前的 和 previous 如果相等-- 是一个vertex，return false
            //a[i] 不重复
            if (OSS[p].a[i].key == OSS[p].a[OSS[p].a[i].previous].key)
                return false;
            //保证a[i] dist 前面的比后面的小
            if ((OSS[p].a[i].next != 0) && (OSS[p].a[OSS[p].a[i].next].dist < OSS[p].a[i].dist))
                return false;
        }
        return true;
    }
    bool double_objects_ori(int p){
        for (int i = OSS_global[p].a[0].next; i != 0; i = OSS_global[p].a[i].next){
            //a[i] 当前的 和 previous 如果相等-- 是一个vertex，return false
            //a[i] 不重复
            if (OSS_global[p].a[i].key == OSS_global[p].a[OSS_global[p].a[i].previous].key)
                return false;
            //保证a[i] dist 前面的比后面的小
            if ((OSS_global[p].a[i].next != 0) && (OSS_global[p].a[OSS_global[p].a[i].next].dist < OSS_global[p].a[i].dist))
                return false;
        }
        return true;
    }
    bool check_everyone(){
        for (int i = 0; i < n; i++){
            if (double_objects(i) == false) return false;
            if (double_objects_ori(i) == false) return false;
        }
            
        return true;
    }
    void dfs_sort(int p, vector<int> &a){
        int _MAX = int(MAX_K * RESERVE_TIME);
        vector<int> b;
        a.clear();
        int x = uniqueVertex[p];
        if (is_current_object[x] == 1)
            a.push_back(x);
        for (int i = 0; i < chSize[p]; i++){
            dfs_sort(ch[p][i], b);
            a.insert(a.end(), b.begin(), b.end());
        }
        int current_k;
        for (int i = 0; i < a.size(); i++)
            current_distance[a[i]] = distanceQuery(x, a[i]);
        if (_MAX < a.size()){
            nth_element(a.begin(), a.begin() + _MAX, a.end(), object_compare);
            current_k = _MAX;
        }
        else {
            current_k = a.size();
        }
        //    printf("a.size(), current_k: %d %d\n", a.size(), current_k);
        //sort(a.begin(), a.begin() + current_k, object_compare);
        sort(a.begin(), a.end(), object_compare);
        
        //    if (OSS[p].size_num > MAX_K)
        //        delete_element(p, OSS[p].a[0].previous);
        if (p == root){
        //        for (int i = 0; i < a.size(); i++)
        //            printf("%d ", a[i]);
        //        printf("\n");
        }
        for (int i = 0; i < current_k; i++){
            OSS_push_back(p, a[i], current_distance[a[i]]);
            
        }
        if (!double_objects(p)){
            print(p);
            stop();
        }
        //    printf("p, a.size()):%d %d\n", p, a.size());
    }
    void stop(){
        while (1);
    }
    void cnt_oss(){
        int sum_oss = 0;
        int max_oss = 0;
        int avg_oss = 0;
        int oss_size = 0;

        for (int i=0;i<TreeSize;i++){
            oss_size = OSS_global[i].size_num;
            if(oss_size > max_oss) max_oss = oss_size;
            sum_oss += oss_size;
        }
        cout<<"sum_oss: "<<sum_oss<<endl;
        cout<<"max_oss: "<<max_oss<<endl;
        cout<<"avg_oss: "<<(sum_oss/TreeSize)<<endl;
    }
};

double get_mean_double(vector<double>& times) {
    double mean = 0.0;
    for (double val : times) {
        mean += val;
    }
    return mean / times.size();
}
double get_var_double(vector<double>& times) {
    double mean = get_mean_double(times);
    double var = 0.0;
    for (double val : times) {
        var += (val - mean) * (val - mean);
    }
    return var / times.size();
}
double get_max_double(vector<double>& times) {
    double max = 0.0;
    for (double val : times) {
        if (max < val)
            max = val;
    }
    return max;
}

    //-- query NY-t.index NY-t.obj NY-t.query sort
    //./querychscomp example.index1 example.obj1 -q example.query2 neighbor optimal vcgindex topk
    //                 1              2             3 4              5        6       7        8
    //out_file 改三处: main // kNN // vct
int main(int argc, char *argv[]){
    srand((int)(time(0)));
    cout << argv[1] << " " << argv[2] << " " << argv[3] << " " << argv[4] << " " << argv[5] << endl;
    readIndex(argv[1]);
    cout<<"finish readindex"<<endl;

    higher = (int*)malloc(sizeof(int) * (n + 1));
    cloest_higher = (int*)malloc(sizeof(int) * (n + 1));
    for (int i = 0; i < n; i++){
        higher[i] = n;
        cloest_higher[i] = INT_MAX;
        for (int j = 0; j < posSize[i]; j++){
            if (height[belong[pos[i][j]]] < higher[i])
                higher[i] = height[belong[pos[i][j]]];
            int _d = distanceQuery(uniqueVertex[i], pos[i][j]);
            if (cloest_higher[i] > _d)
                cloest_higher[i] = _d;
        }
    }
    //cout<<"index read finish "<<endl;
    //----------------------prepare-------------
    //why？？
    LOG2 = (int*)malloc(sizeof(int) * (n * 2 + 10));
    LOGD = (int*)malloc(sizeof(int) * (n * 2 + 10));
    int k = 0, j = 1;
    for (int i = 0; i < n * 2 + 10; i++){
        if (i > j * 2){
            j *= 2;
            k++;
        }
        LOG2[i] = k;
        LOGD[i] = j;
    }
    insert_type = argv[5];
    query_type = argv[6];

    //---------------------------------
    //-------------test------------------
    //int topk = atoi(argv[8]);
    int pit_out =1;
    int topk = atoi(argv[7]);
    cout<<"topk: "<<topk<<endl;
    kNN knn(topk);
    //initialize knn
    knn.create_kNN_index();
    //printf("finish create knn index\n");
    FILE *fobj = fopen(argv[2], "r");
    int number_object;
    fscanf(fobj, "%d", &number_object);
    double start_time = GetTime();
    knn.object_setting_ori(n);
    //for (int i = 0; i <= n; i++) is_current_object[i] = 0;
    //record object via is_current_object
    for (int i = 0; i < number_object; i++){
        int x;
        fscanf(fobj, "%d", &x);
        is_current_object[x] = 1;
    }
    // record object number
    int cnt_object = 0;
    for (int i = 1; i <= n; i++) if (is_current_object[i] == 1) cnt_object ++;
    
    
    //printf("cnt_object: %d\n", cnt_object);
    /*char *fileout;
    fileout = argv[7];
    cout << "fileout: " << fileout << endl;
    knn.fout = fopen(fileout, "wb");
    fwrite(&topk, SIZEOFINT, 1, knn.fout);
    fwrite(&n, SIZEOFINT, 1, knn.fout);*/

    knn.initialize_object_ori();

    //printf("knn.object_number[root]: %d\n", knn.object_number[root]);
    //cout<<"knn.object_number[root]: "<<knn.object_number[root]<<endl;
    double end_time = GetTime();
    printf("object initialization time: %.6lf ms\n", (end_time - start_time) * 1e3);

    /*for(int p =0;p<n;p++){
        if (knn.object_number[p] <= knn.OSS[p].size_num ){
            if (knn.object_number[p] < knn.OSS[p].size_num ) cout<<"p: "<<p<<" x: "<<uniqueVertex[p]<<"amazing"<<endl;
            else cout<<"p: "<<p<<" x: "<<uniqueVertex[p]<<"equal"<<endl;
            //return false;
        }
    }*/
    //knn.cnt_oss();
    //----------------------query------------------------------
    
    /*if (knn.check_everyone()){
        printf("right\n");
    }else printf("wrong\n");*/

    vector<double> times;
    times.clear();
    for (int i = 0; i < knn.period; i++)
        knn.times_period[i].clear();
    
    if (argv[3][1] == 'q'){
        FILE *fquery = fopen(argv[4], "r");
        int q_n;
        // query number
        fscanf(fquery, "%d", &q_n);
        //printf("n: %d\n", n);
        
        knn.query_mark = (int*)malloc(sizeof(int) * (n + 1));
        knn.query_mark_stamp = 0;
        
        for (int i = 0; i <= n; i++)
            knn.query_mark[i] = 0;
        
        start_time = GetTime();
        vector<double> time_array;
        time_array.clear();
        
        double cnt_delay_time = 0;
        tmp_dis = (int*)malloc(sizeof(int) * (n + 1));
        vector<pair<int,int>> res;

         //   q_n = 1;
        for (int i = 0; i < q_n; i++){
            int x, k;
            fscanf(fquery, "%d %d", &x, &k);
            //printf("x, k: %d %d\n", x, k);
            double _start_time = GetTime();
            start_time = GetTime();
            if (strcmp(query_type, "delay") == 0){
                res = knn.query_delay(x, k);
            }
            else if (strcmp(query_type, "naive") == 0){
                res = knn.query_naive(x, k);
            }
            else {
                //cout<<"coming query:"<<endl;
                //MAX_K = k;
                res = knn.query(x, k);
            }
            //record query time
            times.push_back(GetTime() - start_time);
            /*for (int i = 0; i < knn.period; i++)
                if (knn.times_period[i].size() < times.size())
                    knn.times_period[i].push_back(GetTime() - start_time);
            double _end_time = GetTime();
            time_array.push_back(_end_time-_start_time);*/
            //cout<<"query result:!!!"<< " res.size():"<< res.size()<<endl;
            bool to_print = true;
            if (to_print){
                for (int j = 0; j < res.size(); j++)
                    printf("(%d, %d) ", res[j].first, res[j].second);
                printf("\n");
            }
        
        }
        
        //end_time = GetTime();
        //double ave_time = (end_time - start_time) / q_n;
        printf("Average query time: %.6lf ms\n", get_mean_double(times) * 1e3);
        //printf("Var query time: %.6lf ms\n", get_var_double(times) * 1e3);
        
    }
    else if (argv[3][1] == 'u'){
        //cout<<"com up"<<endl;
        knn.update_setting(n);
        //knn.update_dist(n);
        FILE *fupdate = fopen(argv[4], "r");
        int u_n;
        fscanf(fupdate, "%d", &u_n);
        //u_n = 100;
        char st[20];

        //start_time = GetTime();
        double sum_time = 0.0;
        double sum_del_qu =0.0;
        double sum_sca_del_qu =0.0;
        int del_scan =0;
        for (int i = 0; i < u_n; i++){
            fscanf(fupdate, "%s", st);
            int x;
            fscanf(fupdate, "%d", &x);
            
            start_time = GetTime();
            if (st[0] == 'i'){
                //cout << "insert: " << x << endl;
                //int height =
                knn.insert_lazy(x);
                //if (height<highest_all_up) highest_all_up = height;
            }else{
            //else if (st[0] == 'd'){
                //cout << "delete: " << x << endl;
                //int height =
                knn.delete_lazy(x);
                int q =0;
                
                double be_sca_qu = GetTime();
                //requ
                knn.query_af_delete_k(x,x);
                knn.query(x,40);
                sum_sca_del_qu += (GetTime() - be_sca_qu);
                double be_qu = GetTime();
                for (int y =0;y<10;y++){
                    q  = rand() % n;
                    knn.query_af_delete_k(q,x);
                    knn.query(q,40);
                    //if(requ) del_scan++;
                }
                //double en_qu = GetTime();
                sum_del_qu += (GetTime() - be_qu);
                
            }
            sum_time += (GetTime() - start_time);
            //if (knn.check_everyone()){
            //    printf("right\n");
            //}
            //else {
            //    printf("wrong\n");
            //    while (1);
             //}
            //fscanf(fupdate, "%s", st);
        }
        //cout<<"Average Update Time: "<< ((GetTime() - start_time)/u_n)<<endl;
        double ave_del_query = sum_del_qu/(u_n*10);
        cout<<"Average smart delete Time(us) : "<< (ave_del_query * 1e6) <<endl;
        //cout<<"Need to scan: "<< del_scan<<endl;
        double avg_sca_del_qu = sum_sca_del_qu/ u_n;
        cout<<"Average scan delete Time(us) : "<< (ave_del_query * 1e6) <<endl;
        //end_time = GetTime();    (end_time - start_time)
        //double ave_time = (end_time - start_time) / u_n;
        double ave_time = sum_time / u_n;
        cout<<"Average Update Time(us) : "<< (ave_time * 1e6) <<endl;
        //printf("Average update time: %.6lf ms\n", get_mean_double(times) * 1e3);
        //printf("Var update time: %.6lf ms\n", get_var_double(times) * 1e3);
        //cout << reset_times << endl;
        
        bool check = false;
        if (check){
            //!!
            kNN knn2(topk);
            knn2.create_kNN_index();
            //knn2.initialize_object();
            knn2.initialize_object_ori();
            for (int i = 0; i < n; i++){
                int v = knn2.OSS[i].a[0].next;
                int cnt = 0;
                for (int j = knn.OSS[i].a[0].next; j != 0; j = knn.OSS[i].a[j].next){
                    cnt++;
                    printf("i, j, v, cnt: %d %d %d %d\n", i, j, v, cnt);
                    printf("(%d, %d) :(%d, %d)\n",knn.OSS[i].a[j].key,
                           knn.OSS[i].a[j].dist, knn2.OSS[i].a[v].key,knn2.OSS[i].a[v].dist);
                    if (cnt >= MAX_K)
                        break;
                    if (knn.OSS[i].a[j].dist != knn2.OSS[i].a[v].dist){
                        printf("%d %d\n", knn.OSS[0].size_num, knn2.OSS[0].size_num);
                        char c;
                        cin >> c;
                    }
                    v = knn2.OSS[i].a[v].next;
                }
            }
        }
    }
    else{
        //update 重头算update之后的index
        knn.update_setting(n);
        FILE *fupdate = fopen(argv[4], "r");
        int u_n;
        fscanf(fupdate, "%d", &u_n);
        char st[20];

        start_time = GetTime();
        for (int i = 0; i < u_n; i++){
            fscanf(fupdate, "%s", st);
            int x;
            fscanf(fupdate, "%d", &x);
            if (st[0] == 'i'){
                is_current_object[x] = 1;
            }
            else {
                is_current_object[x] = 0;
            }
        }
        /*for (int i = 1; i <= n; i++)
            if (is_current_object[i] == 1)
                cnt_object ++;
        cout << "cnt_object: " << cnt_object << endl;*/
         //    cout << "is_current_object[190524]: " << is_current_object[190524] << endl;
        
        knn.initialize_object_ori();
    
        //    knn.print(root);
        if (knn.check_everyone()){
            printf("right\n");
        }else printf("wrong\n");
    }

    //fclose(knn.fout);

}
