#include <bits/stdc++.h>
#include <chrono>
#include <filesystem>
#include <cmath>
#include <algorithm>
#include <random>

#define ll long long
#define pb push_back
#define mp make_pair
#define pii pair<int,int>
#define vi vector<int>
#define vvi vector<vector<int>>
#define vpi vector<pair<int,int>>
#define all(v) v.begin(),v.end()
#define FOR(i,a,b) for(int i=a;i<b;i++)
#define RFOR(i,a,b) for(int i=a-1;i>=b;i--)

using namespace std;

int n, m; //number of customers and vehicles
int depot = 0; // depot node index (usually 0)
vector<vector<double>> dist; // dist[i][j]: Euclidean distance from i to j
vi demand; // demand[i]: demand of customer i
vi Qk; // Qk[k]: capacity of vehicle k
vi Dk; // Dk[k]: max duration of vehicle k
vi ei, li; // ei[i], li[i]: time window for customer i
vector<double> di; // di[i]: service duration at customer i
int eo, lo; // time window for depot
vpi loc; // loc[i]: location (x, y) of customer i
vvi routes; // routes[k]: sequence of customer indices for vehicle k (start/end with depot)
vi load; // load[k]: current load of vehicle k
vi duration; // duration[k]: current duration of vehicle k
vi arrival_time; // arrival_time[i]: arrival time at customer i
vvi tabu_list; // for Tabu Search memory
double best_cost; // best total travel time found
vector<pair<double, int>> angle_customer; // (angle, customer index)

struct Solution {
    vvi routes; // routes for each vehicle
    vi load;           // load for each vehicle
    vi duration;       // duration for each vehicle
    vi arrival_time;   // arrival time at each customer
    double total_cost; // total travel time/distance
};

// Compute Euclidean distance between two points
double euclidean(int x1, int y1, int x2, int y2) {
    return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2));
}

// Build distance matrix: dist[i][j] = Euclidean distance from i to j
void build_distance_matrix() {
    dist.assign(n+5, vector<double>(n+5, 0.0));
    for (int i = 0; i <= n; ++i) {
        for (int j = 0; j <= n; ++j) {
            if (i == j) {
                dist[i][j] = 0.0;
            } else {
                dist[i][j] = euclidean(loc[i].first, loc[i].second, loc[j].first, loc[j].second);
            }
        }
    }}

Solution generate_initial_solution() {
    Solution sol;
    // 1. Compute angles
    int depot_x = loc[0].first, depot_y = loc[0].second;
    for (int i = 1; i <= n; ++i) {
        double dx = loc[i].first - depot_x;
        double dy = loc[i].second - depot_y;
        double angle = atan2(dy, dx);
        angle_customer.push_back({angle, i});
    }
    sort(angle_customer.begin(), angle_customer.end());

    // 2. Randomly choose starting customer
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> dis(0, n-1);
    int start_idx = dis(gen);

    // 3. Build sequence
    vector<int> seq;
    for (int i = 0; i < n; ++i)
        seq.push_back(angle_customer[(start_idx + i) % n].second);

    // 4. Construct routes
    routes.assign(m+1, vector<int>());
    load.assign(m+1, 0);
    duration.assign(m+1, 0);
    int k = 1;
    for (int idx : seq) {
        // Try to insert idx into route k at best position
        int best_pos = -1, best_incr = INT_MAX;
        if (routes[k].empty()) {
            routes[k].push_back(0);
            routes[k].push_back(0);
        } // start and end at depot
        for (int pos = 1; pos < routes[k].size(); ++pos) {
            // Try inserting at pos
            int jl = routes[k][pos-1];
            int j2 = routes[k][pos];
            if ((ei[jl] < ei[idx] && ei[idx] < ei[j2] && j2 != 0) || j2 == 0) {
                auto temp = routes[k];
                temp.insert(temp.begin() + pos, idx);
                // Compute new load and duration
                int new_load = load[k] + demand[idx];
                double new_dur = 0;
                for (int p = 1; p < temp.size(); ++p){
                    new_dur += di[temp[p]];
                    new_dur += dist[temp[p-1]][temp[p]];
                }
                // Check constraints
                if (new_load <= Qk[k] && new_dur <= Dk[k]) {
                    int incr = new_dur - duration[k];
                    if (incr < best_incr) {
                        best_incr = incr;
                        best_pos = pos;
                    }
                }
            }
        }
        // Insert at best position if found
        if (best_pos != -1) {
            routes[k].insert(routes[k].begin() + best_pos, idx);
            load[k] += demand[idx];
            // Recompute duration
            duration[k] = 0;
            for (int p = 1; p < routes[k].size(); ++p)
                duration[k] += dist[routes[k][p-1]][routes[k][p]];
        }
        //cout routes for debug prints
        for (int i = 0; i < routes[k].size(); i++){
            cout << routes[k][i] << " ";
        }
        cout << endl;
        // If constraints violated, move to next route
        if (best_pos == -1) {
            k = min(k+1, m);
            routes[k].clear();
            routes[k].push_back(0);
            routes[k].push_back(idx);
            routes[k].push_back(0);
            load[k] = demand[idx];
            duration[k] = 0;
            for (int p = 1; p < routes[k].size(); ++p)
                duration[k] += dist[routes[k][p-1]][routes[k][p]];
        }
    }
    // End each route at depot
    for (int k = 1; k <= m; ++k){
        if (!routes[k].empty() && routes[k].back() != 0)
            routes[k].push_back(0);
    }
    sol.routes = routes;
    sol.load = load;
    sol.duration = duration;
    return sol;
}

void init() {
    build_distance_matrix();
}

void tabu_search(){

}

void output(){
    Solution sol;
    sol = generate_initial_solution();
    //Print the solution:
    for (int k = 1; k <= m; ++k) {
        cout << "Route " << k << ": ";
        for (int idx : sol.routes[k]) {
            cout << idx << " ";
        }
        cout << endl;
    }
}

void input(){
    cin >> n >> m;

    demand.resize(n+5);
    Qk.resize(m+5);
    Dk.resize(m+5);
    di.resize(n+5);
    ei.resize(n+5);
    li.resize(n+5);
    routes.resize(m+5);
    load.resize(m+5);
    duration.resize(m+5);
    arrival_time.resize(n+5);
    tabu_list.resize(m+5, vi(n+5, 0));

    for(int i=1; i<=n; i++){
        cin >> demand[i] >> ei[i] >> li[i] >> di[i];
    }
    cin >> eo >> lo;
    for(int i=1; i<=m; i++){
        cin >> Qk[i] >> Dk[i];
    }
    for (int i=0; i<=n; i++) {
        int x, y;
        cin >> x >> y;
        loc.push_back(mp(x, y));
    }
}

int main(){
    freopen("input.txt", "r", stdin);
//    freopen("output.txt", "w", stdout);
    input();
    init();
    tabu_search();
    output();
}