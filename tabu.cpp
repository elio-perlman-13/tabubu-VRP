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
vvi freq; // freq[k][i]: how many times customer i inserted into route k for diversification

const int MAX_ITER = 20000; // max iterations for Tabu Search
const double lambda = 0.01; // scaling factor for frequency penalty (tune as needed)
const int nmax = 500; // for early stopping if no improvement

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
    cout << endl;
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

// Randomly pick a customer, find suitable routes, evaluate all moves (considering tabu moves) and return best neighbor
Solution best_neighbor(const Solution& sol, int i, int current_iter, int from_route, double alpha, double beta, double gamma, double p1, double p2, double best_f2=1e18, double best_cost=1e18) {

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

    // 4. For each suitable route, try all possible insertions
    double best_neighbor_cost = 1e18;
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
            // Remove i from all routes to prevent duplication
            for (int r = 1; r <= m; ++r) {
                auto& route = cand.routes[r];
                auto it = std::find(route.begin(), route.end(), i);
                if (it != route.end()) {
                    route.erase(it);
                    cand.load[r] -= demand[i];
                }
            }
            // Insert i into route k at pos (adjust pos if needed)
            auto& r2 = cand.routes[k];
            int insert_pos = pos;
            // If i was before pos in r2, pos--
            for (int p = 0; p < (int)r2.size() && p < pos; ++p) {
                if (r2[p] == i) insert_pos--;
            }
            r2.insert(r2.begin() + insert_pos, i);
            cand.load[k] += demand[i];
            // Update durations and arrival times for both affected routes
            // First, find which route i was removed from (other than k)
            int src_route = -1;
            for (int r = 1; r <= m; ++r) {
                if (r == k) continue;
                auto it = std::find(sol.routes[r].begin(), sol.routes[r].end(), i);
                if (it != sol.routes[r].end()) {
                    src_route = r;
                    break;
                }
            }
            // Update duration for destination route k
            double delta_k = 0.0;
            int new_pos = insert_pos;
            int prev = r2[new_pos - 1];
            int next = (new_pos < (int)r2.size() - 1) ? r2[new_pos + 1] : 0;
            delta_k += dist[prev][i] + di[i] + dist[i][next];
            delta_k -= dist[prev][next];
            cand.duration[k] += delta_k;
            // Recompute duration for src_route (from which i was removed), if any
            if (src_route != -1) {
                double dur = 0.0;
                auto& rsrc = cand.routes[src_route];
                for (int p = 1; p < (int)rsrc.size(); ++p) {
                    dur += dist[rsrc[p-1]][rsrc[p]];
                }
                cand.duration[src_route] = dur;
            }
            // Efficiently update arrival times for both routes
            // For k (destination route)
            if (!cand.routes[k].empty()) cand.arrival_time[cand.routes[k][0]] = 0.0;
            double tt = 0.0;
            for (int p = 1; p < (int)cand.routes[k].size(); ++p) {
                int prev = cand.routes[k][p-1];
                int curr = cand.routes[k][p];
                tt += dist[prev][curr];
                if (curr != 0) {
                    cand.arrival_time[curr] = max((double)ei[curr], tt);
                    tt = cand.arrival_time[curr] + di[curr];
                }
            }
            // For src_route (if any)
            if (src_route != -1 && !cand.routes[src_route].empty()) {
                cand.arrival_time[cand.routes[src_route][0]] = 0.0;
                double tts = 0.0;
                for (int p = 1; p < (int)cand.routes[src_route].size(); ++p) {
                    int prev = cand.routes[src_route][p-1];
                    int curr = cand.routes[src_route][p];
                    tts += dist[prev][curr];
                    if (curr != 0) {
                        cand.arrival_time[curr] = max((double)ei[curr], tts);
                        tts = cand.arrival_time[curr] + di[curr];
                    }
                }
            }
            // Recompute total cost
            cand.total_cost = 0.0;
            for (int r = 1; r <= m; ++r) cand.total_cost += cand.duration[r];
            // Update customer_vehicle
            cand.customer_vehicle[i] = k;
            // Evaluate penalized cost
            double f2 = F2(cand, alpha, beta, gamma);
            // Tabu check: skip if tabu unless aspiration (improves best_cost)
            bool is_tabu = (tabu_list[k][i] > current_iter);
            if (is_tabu && (f2 >= best_f2 && f2 > cand.total_cost || cand.total_cost >= best_cost && f2 == cand.total_cost)){
                // ...removed debug cout...
                continue;
            }
            // Frequency penalty for diversification (only for non-improving moves)
            double freq_penalty = 0.0;
            if (f2 > best_f2){
                for (int r = 1; r <= n; ++r) {
                    freq_penalty += freq[cand.customer_vehicle[r]][r];
                }
                freq_penalty *= lambda * sqrt(n * m) * cand.total_cost;
            }
            double penalized_f2 = f2 + freq_penalty;
            if (penalized_f2 < best_neighbor_cost) {
                best_neighbor_cost = penalized_f2;
                best_sol = cand;
            }
        }
    }
    return best_sol;
}

// Placeholder for TSP with Time Windows post-optimization (GENIUS adaptation)
// This should be replaced with a real implementation for best results
void post_optimize_route(vector<int>& route, vector<double>& arrival_time, int k) {
    // TODO: Implement GENIUS or other TSPTW heuristic for a single route
    // For now, this is a no-op (identity)
    // route: route[k], arrival_time: arrival_time for route k, k: vehicle index
}

Solution tabu_search(Solution sol, double delta = 0, double p1=0.2*n, double p2=0.2*n) {
    // ...removed debug cout...
    // Evaluate all possible moves: move customer i from route k to route k', insert at best position
    double best_f2 = 1e18;
    double best_cost = 1e18;
    Solution best_sol = sol;
    Solution current_sol = sol;
    int current_iter = 0;
    int tabu_min = 5, tabu_max = 10;
    double alpha = 1, beta = 1, gamma = 1;
    // Initialize frequency matrix
    freq.assign(m+1, vector<int>(n+1, 0));
    double current_f2 = F2(current_sol, alpha, beta, gamma);
    if (current_f2 == current_sol.total_cost){
        best_cost = current_sol.total_cost;
    }
    best_f2 = current_f2;
    int no_improve_iters = 0;
    double last_best_f2 = best_f2, last_best_cost = best_cost;

    // Open file to log f2 and total_cost per iteration
    static int log_counter = 0;
    std::ofstream log_file;
    std::string log_filename = "tabu_log_" + std::to_string(log_counter++) + ".csv";
    log_file.open(log_filename);
    log_file << "iter,f2,total_cost\n";
    while (current_iter < MAX_ITER) {
        Solution best_neighbor_sol = current_sol;
        double best_neighbor_f2 = 1e18;
        int best_i = -1, best_from_route = -1, best_to_route = -1;
        // Loop over all customers to find the best neighbor
        for (int i = 1; i <= n; ++i) {
            int from_route = current_sol.customer_vehicle[i];
            Solution neighbor = best_neighbor(current_sol, i, current_iter, from_route, alpha, beta, gamma, p1, p2, best_f2, best_cost);
            double f2 = F2(neighbor, alpha, beta, gamma);
            if (f2 < best_neighbor_f2) {
                best_neighbor_f2 = f2;
                best_neighbor_sol = neighbor;
                best_i = i;
                best_from_route = from_route;
                best_to_route = neighbor.customer_vehicle[i];
            }
        }
        // print the best move found
        cout << "Iter " << current_iter << ": Move customer " << best_i << " from route " << best_from_route << " to route " << best_to_route << ", F2: " << best_neighbor_f2 << ", Cost: " << best_neighbor_sol.total_cost << endl;
        // Print both penalized and unpenalized costs for clarity
        double best_f2_val = F2(best_neighbor_sol, alpha, beta, gamma);
        cout << "Best neighbor after moving customer " << best_i << ": penalized cost = " << best_neighbor_sol.total_cost
            << ", f2 = " << best_f2_val
            << ", total_cost = " << best_neighbor_sol.total_cost << endl;
        cout << "alpha: " << alpha << ", beta: " << beta << ", gamma: " << gamma << endl;
        // If the customer was actually moved to a new route, set tabu tenure
        if (best_from_route != best_to_route && best_i != -1) {
            random_device rd;
            mt19937 gen(rd());
            uniform_int_distribution<> tabu_dist(tabu_min, tabu_max);
            int theta = tabu_dist(gen);
            tabu_list[best_from_route][best_i] = current_iter + theta;
        }
        // Update frequency for diversification
        if (best_i != -1) freq[best_to_route][best_i]++;
        // update best solution found
        if (best_neighbor_f2 < best_f2 || (best_neighbor_f2 == best_f2 && best_neighbor_sol.total_cost < best_cost)) {
            best_f2 = best_neighbor_f2;
            best_cost = best_neighbor_sol.total_cost;
            best_sol = best_neighbor_sol;
        }

        if (best_neighbor_f2 < current_f2 || (best_neighbor_f2 == current_f2 && best_neighbor_sol.total_cost < current_sol.total_cost)) {
            current_sol = best_neighbor_sol;
            current_f2 = best_neighbor_f2;
        }

        // Early stopping: check if best_f2 and best_cost have improved
        if (best_f2 < last_best_f2 || best_cost < last_best_cost) {
            no_improve_iters = 0;
            last_best_f2 = best_f2;
            last_best_cost = best_cost;
        } else {
            no_improve_iters++;
        }
        if (no_improve_iters >= nmax) {
            break;
        }

        // Adaptive penalty parameter update
        // Check feasibility for each constraint
        bool load_feas = true, dur_feas = true, tw_feas = true;
        for (int k = 1; k <= m; ++k) {
            if (current_sol.load[k] > Qk[k]) load_feas = false;
            if (current_sol.duration[k] > Dk[k]) dur_feas = false;
        }
        for (int j = 1; j <= n; ++j) {
            if (current_sol.arrival_time[j] > li[j]) tw_feas = false;
        }
        // Update alpha (load penalty)
        if (load_feas) {
            alpha /= (1.0 + delta);
        } else {
            alpha *= (1.0 + delta);
        }
        // Update beta (duration penalty)
        if (dur_feas) {
            beta /= (1.0 + delta);
        } else {
            beta *= (1.0 + delta);
        }
        // Update gamma (time window penalty)
        if (tw_feas) {
            gamma /= (1.0 + delta);
        } else {
            gamma *= (1.0 + delta);
        }

        // Log best_f2 and best_cost for this iteration
        log_file << current_iter << "," << best_f2 << "," << best_cost << "\n";
        ++current_iter;
    }
    // Post-optimization: apply TSPTW heuristic to each route of best_sol
    for (int k = 1; k <= m; ++k) {
        post_optimize_route(best_sol.routes[k], best_sol.arrival_time, k);
    }
    log_file.close();
    return best_sol;
}

void init() {
    build_distance_matrix();
    compute_closest_neighbors(int(0.2 * n)); // p1 = 20% of n
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
    Solution step_1_sol = tabu_search(sol, 0.003, int(0.2*n), int(0.2*n));
    Solution best_sol = tabu_search(step_1_sol, 0.006, int(0.1*n), int(0.1*n));
    print_solution(best_sol);
}

void input(){
    // Parse Solomon C101 format
    string line;
    // Skip first line (instance name)
    getline(cin, line);
    // Skip blank line
    getline(cin, line);
    // Skip VEHICLE
    getline(cin, line);
    // Skip NUMBER CAPACITY
    getline(cin, line);
    // Read vehicle count and capacity
    int vehicle_count, vehicle_capacity;
    cin >> vehicle_count >> vehicle_capacity;
    m = vehicle_count;
    Qk.resize(m+5);
    for (int i = 1; i <= m; ++i) Qk[i] = vehicle_capacity;
    // Skip blank line
    getline(cin, line);
    getline(cin, line);
    // Skip CUSTOMER
    getline(cin, line);
    // Skip header
    getline(cin, line);
    // Skip blank line
    getline(cin, line);
    // Read customer table
    vector<tuple<int,int,int,int,int,int,int>> customers;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        istringstream iss(line);
        int id, x, y, demand, ready, due, service;
        if (!(iss >> id >> x >> y >> demand >> ready >> due >> service)) break;
        customers.push_back({id, x, y, demand, ready, due, service});
    }
    n = customers.size() - 1; // depot is 0
    demand.resize(n+5);
    di.resize(n+5);
    ei.resize(n+5);
    li.resize(n+5);
    loc.clear();
    for (auto& tup : customers) {
        int id, x, y, dem, ready, due, service;
        tie(id, x, y, dem, ready, due, service) = tup;
        if (id == 0) {
            eo = ready; lo = due;
        }
        demand[id] = dem;
        di[id] = service;
        ei[id] = ready;
        li[id] = due;
        loc.push_back(mp(x, y));
    }
    Dk.resize(m+5);
    // Set max duration for each vehicle as depot's due date (lo)
    for (int i = 1; i <= m; ++i) Dk[i] = lo;
    routes.resize(m+5);
    load.resize(m+5);
    duration.resize(m+5);
    arrival_time.resize(n+5);
    tabu_list.resize(m+5, vi(n+5, 0));
}

int main(){
    freopen("C101.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    input();
    init();
    output();
}