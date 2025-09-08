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
#define vd vector<double>
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
vd di; // di[i]: service duration at customer i
int eo, lo; // time window for depot
vpi loc; // loc[i]: location (x, y) of customer i
vvi routes; // routes[k]: sequence of customer indices for vehicle k (start/end with depot)
vi load; // load[k]: current load of vehicle k
vd duration; // duration[k]: current duration of vehicle k
vd arrival_time; // arrival_time[i]: arrival time at customer i
vvi tabu_list; // for Tabu Search memory
double best_cost; // best total travel time found
vector<pair<double, int>> angle_customer; // (angle, customer index)
vvi closest_neighbors; // closest_neighbors[i]: list of closest neighbors to customer i

struct Solution {
    vvi routes; // routes for each vehicle
    vi load;           // load for each vehicle
    vd duration;       // duration for each vehicle
    vd arrival_time;   // arrival time at each customer
    double total_cost; // total travel time/distance
    vi customer_vehicle; // customer_vehicle[i] = k means customer i is assigned to vehicle k
};

// Compute Euclidean distance between two points
double euclidean(int x1, int y1, int x2, int y2) {
    return sqrt((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2));
}

// Build distance matrix: dist[i][j] = Euclidean distance from i to j
void build_distance_matrix() {
    dist.assign(n+5, vd(n+5, 0.0));
    for (int i = 0; i <= n; ++i) {
        for (int j = 0; j <= n; ++j) {
            if (i == j) {
                dist[i][j] = 0.0;
            } else {
                dist[i][j] = euclidean(loc[i].first, loc[i].second, loc[j].first, loc[j].second);
            }
        }
    }
}

// Generate an initial feasible solution using a sweep-like heuristic
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
    vi seq;
    for (int i = 0; i < n; ++i)
        seq.push_back(angle_customer[(start_idx + i) % n].second);

    // 4. Construct routes
    routes.assign(m+1, vi());
    load.assign(m+1, 0);
    duration.assign(m+1, 0);
    int k = 1;
    for (int idx : seq) {
        // Try to insert idx into route k at best position
        int best_feas_pos = -1, best_feas_incr = INT_MAX;
        int best_infeas_pos = -1;
        double best_infeas_incr = 1e18;
        if (routes[k].empty()) {
            routes[k].push_back(0);
            routes[k].push_back(0);
        } // start and end at depot
        int new_load = load[k] + demand[idx];
        for (int pos = 1; pos < routes[k].size(); ++pos) {
            if (new_load > Qk[k]) break;
            // Try inserting at pos
            int prev = routes[k][pos-1];
            int next = routes[k][pos];
            if ((ei[prev] < ei[idx] && ei[idx] < ei[next] && next != 0) || next == 0) {
                auto temp = routes[k];
                temp.insert(temp.begin() + pos, idx);
                // Compute new load and incremental duration
                // Remove old segment, add new segments
                double delta = dist[prev][idx] + di[idx] + dist[idx][next] - dist[prev][next];
                double new_dur = duration[k] + delta;
                double incr = delta;
                if (new_load <= Qk[k] && new_dur <= Dk[k]) {
                    if (incr < best_feas_incr) {
                        best_feas_incr = incr;
                        best_feas_pos = pos;
                    }
                } else {
                    if (incr < best_infeas_incr) {
                        best_infeas_incr = incr;
                        best_infeas_pos = pos;
                    }
                }
            }
        }
        // Insert at best feasible position if found
        if (best_feas_pos != -1) {
            routes[k].insert(routes[k].begin() + best_feas_pos, idx);
            load[k] += demand[idx];
            // Recompute duration
            duration[k] = 0;
            for (int p = 1; p < routes[k].size(); ++p)
                duration[k] += dist[routes[k][p-1]][routes[k][p]];
        }
        // If constraints violated, move to next route
        if (best_feas_pos == -1) {
            if (k < m) {
                k++;
                routes[k].clear();
                routes[k].push_back(0);
                routes[k].push_back(idx);
                routes[k].push_back(0);
                load[k] = demand[idx];
                duration[k] = 0;
                for (int p = 1; p < routes[k].size(); ++p)
                    duration[k] += dist[routes[k][p-1]][routes[k][p]];
            } else {
                // Insert idx into route m (k==m) at the best infeasible position found above
                if (best_infeas_pos == -1) best_infeas_pos = 1;
                routes[m].insert(routes[m].begin() + best_infeas_pos, idx);
                load[m] += demand[idx];
                duration[m] = 0;
                for (int p = 1; p < routes[m].size(); ++p) {
                    duration[m] += di[routes[m][p]];
                    duration[m] += dist[routes[m][p-1]][routes[m][p]];
                }
            }
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

    // Calculate arrival times for each customer in each route
    sol.arrival_time.assign(n+1, 0.0);
    for (int k = 1; k <= m; ++k) {
        double t = 0;
        for (int p = 1; p < routes[k].size(); ++p) {
            int prev = routes[k][p-1];
            int curr = routes[k][p];
            t += dist[prev][curr];
            if (curr != 0) {
                sol.arrival_time[curr] = max((double)ei[curr], t);
                t = sol.arrival_time[curr] + di[curr];
            }
        }
    }

    sol.total_cost = 0;
    for (int k = 1; k <= m; ++k) {
        sol.total_cost += duration[k];
    }

    sol.customer_vehicle.assign(n+1, 0);
    for (int k = 1; k <= m; ++k) {
        for (int cust : routes[k]) {
            if (cust != 0) sol.customer_vehicle[cust] = k;
        }
    }
    return sol;
}

// Penalty objective function F2(S) for a solution
double F2(Solution sol, double alpha, double beta, double gamma) {
    double f1 = sol.total_cost;
    double penalty_capacity = 0.0;
    double penalty_duration = 0.0;
    double penalty_time_window = 0.0;
    // Capacity and duration penalties
    for (int k = 1; k <= m; ++k) {
        double Q = Qk[k];
        double L = Dk[k];
        double excess_cap = max(0.0, (double)sol.load[k] - Q);
        penalty_capacity += excess_cap;
        double route_duration = sol.duration[k];
        double excess_dur = max(0.0, route_duration - L);
        penalty_duration += excess_dur;
    }
    // Time window penalties
    for (int i = 1; i <= n; ++i) {
        double at = sol.arrival_time[i];
        if (at > li[i]) {
            penalty_time_window += at - li[i];
        }
    }
    return f1 + alpha * penalty_capacity + beta * penalty_duration + gamma * penalty_time_window;
}

// Did exactly what it says
void print_solution(const Solution& sol) {
    for (int k = 1; k <= m; ++k) {
        cout << "Route " << k << ": ";
        for (int idx : sol.routes[k]) {
            cout << idx << " ";
        }
        cout << endl;
        cout << "Load: " << sol.load[k] << ", Duration: " << sol.duration[k] << endl;
    }
    cout << "Arrival Times: ";
    for (int i = 1; i <= n; ++i) {
            cout << sol.arrival_time[i] << " ";
    }
    cout << endl;
    cout << "Total Cost: " << sol.total_cost << endl;
}


// Precompute closest neighbors for all customers
void compute_closest_neighbors(int p1) {
    closest_neighbors.assign(n+1, vector<int>());
    for (int i = 1; i <= n; ++i) {
        vector<pair<double, int>> neigh;
        for (int j = 1; j <= n; ++j) {
            if (i == j) continue;
            neigh.push_back({dist[i][j], j});
        }
        sort(neigh.begin(), neigh.end());
        for (int t = 0; t < min(p1, (int)neigh.size()); ++t)
            closest_neighbors[i].push_back(neigh[t].second);
    }
}

// Randomly pick a customer, find suitable routes, evaluate all moves and return best neighbor
Solution best_neighbor(const Solution& sol, double alpha, double beta, double gamma, double p1=0.2*n, double p2=0.2*n) {
    // 1. Randomly pick a customer i (not depot)
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> dis(1, n);
    int i = dis(gen);
    int from_route = sol.customer_vehicle[i];
    cout << "Considering moving customer " << i << " from route " << from_route << endl;

    // 2. Use precomputed closest neighbors
    set<int> close_neighbors(closest_neighbors[i].begin(), closest_neighbors[i].end());
    // 3. Find suitable routes: empty or containing one of the p1 closest neighbors
    vector<int> suitable_routes;
    for (int k = 1; k <= m; ++k) {
        if (k == from_route) continue;
        bool empty = (sol.routes[k].size() == 2); // only depot at start/end
        bool has_neighbor = false;
        for (int idx = 1; idx < (int)sol.routes[k].size() - 1; ++idx) {
            if (close_neighbors.count(sol.routes[k][idx])) {
                has_neighbor = true;
                break;
            }
        }
        if (empty || has_neighbor) suitable_routes.push_back(k);
    }

    cout << "Suitable routes for insertion: ";
    for (int k : suitable_routes) cout << k << " ";
    cout << endl;

    // 4. For each suitable route, try all possible insertions
    double best_cost = 1e18;
    Solution best_sol = sol;
    // GENI algorithm: only consider insertions adjacent to P2 closest nodes in route k
    for (int k : suitable_routes) {
        set<int> geni_positions;
        // Use closest_neighbors[i] to find positions in route k adjacent to those nodes
        for (int idx = 1; idx < (int)sol.routes[k].size() - 1; ++idx) {
            int cust = sol.routes[k][idx];
            if (close_neighbors.count(cust)) {
                geni_positions.insert(idx);     // after idx (between idx and idx+1)
                geni_positions.insert(idx + 1); // after idx+1 (between idx+1 and idx+2)
            }
        }
        // Always allow insertion at position 1 (after depot) and at the end (before depot)
        geni_positions.insert(1);
        geni_positions.insert((int)sol.routes[k].size() - 1);
        for (int pos : geni_positions) {
            if (pos < 1 || pos >= (int)sol.routes[k].size()) continue;
            Solution cand = sol;
            // Find position of i in from_route before removing
            auto& r1 = cand.routes[from_route];
            int pos_rm = -1;
            for (int p = 1; p < (int)r1.size() - 1; ++p) {
                if (r1[p] == i) { pos_rm = p; break; }
            }
            // Remove i from from_route
            if (pos_rm != -1) r1.erase(r1.begin() + pos_rm);
            cand.load[from_route] -= demand[i];
            // Insert i into route k at pos
            auto& r2 = cand.routes[k];
            r2.insert(r2.begin() + pos, i);
            cand.load[k] += demand[i];
            // Incrementally update durations for from_route and k
            // Now pos_rm is the position where i was in from_route before removal
            // Update duration for from_route
            double delta_from = 0.0;
            if (pos_rm != -1) {
                int prev = r1[pos_rm - 1];
                int next = (pos_rm < (int)r1.size()) ? r1[pos_rm] : 0;
                delta_from -= dist[prev][i] + di[i] + dist[i][next];
                delta_from += dist[prev][next];
            }
            cand.duration[from_route] += delta_from;

            // For k: i was inserted at pos
            // We know where i was inserted: pos
            double delta_k = 0.0;
            {
                int prev = r2[pos - 1];
                int next = (pos < (int)r2.size() - 1) ? r2[pos + 1] : 0;
                delta_k += dist[prev][i] + di[i] + dist[i][next];
                delta_k -= dist[prev][next];
            }
            cand.duration[k] += delta_k;
            // Efficiently update arrival times only from affected positions
            // For from_route: update from pos_rm (first node after removed i)
            for (int t : {from_route, k}) {
                int start = 1;
                if (t == from_route && pos_rm != -1) start = pos_rm;
                if (t == k) start = pos; // pos is where i was inserted
                // Set arrival time for node before start (if not already set)
                if (start > 1 && cand.arrival_time[cand.routes[t][start-1]] == 0.0) {
                    // Compute up to start-1
                    double tt = 0.0;
                    for (int p = 1; p < start; ++p) {
                        int prev = cand.routes[t][p-1];
                        int curr = cand.routes[t][p];
                        tt += dist[prev][curr];
                        if (curr != 0) {
                            cand.arrival_time[curr] = max((double)ei[curr], tt);
                            tt = cand.arrival_time[curr] + di[curr];
                        }
                    }
                }
                // Now update from start onward
                double tt = cand.arrival_time[cand.routes[t][start-1]];
                for (int p = start; p < (int)cand.routes[t].size(); ++p) {
                    int prev = cand.routes[t][p-1];
                    int curr = cand.routes[t][p];
                    tt += dist[prev][curr];
                    if (curr != 0) {
                        cand.arrival_time[curr] = max((double)ei[curr], tt);
                        tt = cand.arrival_time[curr] + di[curr];
                    }
                }
            }
            // Recompute total cost
            cand.total_cost += delta_from + delta_k;
            // Update customer_vehicle
            cand.customer_vehicle[i] = k;
            // Evaluate penalized cost
            double f2 = F2(cand, alpha, beta, gamma);
            print_solution(cand);
            cout << "F2: " << f2 << endl;
            if (f2 < best_cost) {
                best_cost = f2;
                best_sol = cand;
            }
        }
    }
    return best_sol;
}

Solution tabu_search(Solution sol, double alpha, double beta, double gamma) {
    // Evaluate all possible moves: move customer i from route k to route k', insert at best position
    double best_cost = 1e18;
    Solution best_sol = sol;
    for (int k = 1; k <= m; ++k) {
        for (int pos = 1; pos < (int)sol.routes[k].size() - 1; ++pos) { // skip depot at start/end
            int cust = sol.routes[k][pos];
            // Try removing cust from route k
            for (int kp = 1; kp <= m; ++kp) {
                if (k == kp && sol.routes[k].size() <= 3) continue; // can't remove last customer
                for (int posp = 1; posp < (int)sol.routes[kp].size(); ++posp) { // insert after depot
                    if (k == kp && (posp == pos || posp == pos+1)) continue; // skip no-op
                    // Build new solution
                    Solution cand = sol;
                    // Remove cust from k
                    cand.routes[k].erase(cand.routes[k].begin() + pos);
                    cand.load[k] -= demand[cust];
                    // Insert cust into kp at posp
                    cand.routes[kp].insert(cand.routes[kp].begin() + posp, cust);
                    cand.load[kp] += demand[cust];
                    // Recompute durations for k and kp
                    for (int t : {k, kp}) {
                        cand.duration[t] = 0;
                        for (int p = 1; p < (int)cand.routes[t].size(); ++p) {
                            int prev = cand.routes[t][p-1];
                            int curr = cand.routes[t][p];
                            cand.duration[t] += dist[prev][curr];
                            if (curr != 0) cand.duration[t] += di[curr];
                        }
                    }
                    // Recompute arrival times for all customers in k and kp
                    cand.arrival_time.assign(n+1, 0.0);
                    for (int t : {k, kp}) {
                        double tt = 0;
                        for (int p = 1; p < (int)cand.routes[t].size(); ++p) {
                            int prev = cand.routes[t][p-1];
                            int curr = cand.routes[t][p];
                            tt += dist[prev][curr];
                            if (curr != 0) {
                                cand.arrival_time[curr] = max((double)ei[curr], tt);
                                tt = cand.arrival_time[curr] + di[curr];
                            }
                        }
                    }
                    // Recompute total cost
                    cand.total_cost = 0;
                    for (int t = 1; t <= m; ++t) cand.total_cost += cand.duration[t];
                    // Update customer_vehicle
                    cand.customer_vehicle[cust] = kp;
                    // Evaluate penalized cost
                    double f2 = F2(cand, alpha, beta, gamma);
                    if (f2 < best_cost) {
                        best_cost = f2;
                        best_sol = cand;
                    }
                }
            }
        }
    }
    return best_sol;
}

void init() {
    build_distance_matrix();
    compute_closest_neighbors(int(0.2 * n)); // p1 = 20% of n
}

void tabu_search(){

}

void output(){
    Solution sol;
    sol = generate_initial_solution();
    // Print the distance matrix with headers and formatting:
    cout << fixed << setprecision(2);
    cout << "Distance Matrix (rows/cols: 0=depot, 1..n=customers):\n";
    cout << "     ";
    for (int j = 0; j <= n; ++j) cout << setw(7) << j;
    cout << endl;
    for (int i = 0; i <= n; ++i) {
        cout << setw(4) << i << " ";
        for (int j = 0; j <= n; ++j) {
            cout << setw(7) << dist[i][j];
        }
        cout << endl;
    }
    //Print the solution:
    print_solution(sol);
    double alpha = 10.0, beta = 10.0, gamma = 10.0;
    cout << "Initial penalized cost F2: " << F2(sol, alpha, beta, gamma) << endl;
    Solution best_sol = best_neighbor(sol, alpha, beta, gamma, 0.3*n, 0.3*n);
    cout << "Best neighbor solution:" << endl;
    print_solution(best_sol);
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
    freopen("output.txt", "w", stdout);
    input();
    init();
    tabu_search();
    output();
}