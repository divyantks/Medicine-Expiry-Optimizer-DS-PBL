#include <bits/stdc++.h>
using namespace std;

struct Batch {
    string medicineName,batchId, expiry;
    int quantity = 0;
    double unitPrice = 0.0;
    bool active = true;
};

class FibonacciHeap {
public:
    struct Node {
        shared_ptr<Batch> batch;
        Node *parent = nullptr, *child = nullptr, *left = this, *right = this;
        int degree = 0;
        bool mark = false;
        explicit Node(shared_ptr<Batch> b) : batch(move(b)) {}
    };

private:
    Node *minNode = nullptr;
    int nodeCount = 0;

    static bool earlier(const Node *a, const Node *b) {
        if (a->batch->expiry != b->batch->expiry)
            return a->batch->expiry < b->batch->expiry;
        return a->batch->batchId < b->batch->batchId;
    }

    static void removeFromList(Node *x) {
        x->left->right = x->right;
        x->right->left = x->left;
        x->left = x->right = x;
    }

    void addRoot(Node *x) {
        x->parent = nullptr;
        x->mark = false;
        if (!minNode) {
            x->left = x->right = x;
            minNode = x;
        } else {
            x->left = minNode;
            x->right = minNode->right;
            minNode->right->left = x;
            minNode->right = x;
            if (earlier(x, minNode)) minNode = x;
        }
    }

    void link(Node *y, Node *x) {
        removeFromList(y);
        y->parent = x;
        y->mark = false;
        if (!x->child) {
            x->child = y;
            y->left = y->right = y;
        } else {
            y->left = x->child;
            y->right = x->child->right;
            x->child->right->left = y;
            x->child->right = y;
        }
        x->degree++;
    }

    void consolidate() {
        if (!minNode) return;
        vector<Node*> roots;
        Node *start = minNode, *cur = start;
        do {
            roots.push_back(cur);
            cur = cur->right;
        } while (cur != start);

        vector<Node*> degreeTable(2 * (int)log2(max(2, nodeCount)) + 10, nullptr);
        for (Node *w : roots) {
            if (w->parent != nullptr) continue;
            Node *x = w;
            int d = x->degree;
            while (true) {
                if (d >= (int)degreeTable.size()) degreeTable.resize(d + 10, nullptr);
                if (!degreeTable[d]) break;
                Node *y = degreeTable[d];
                if (earlier(y, x)) swap(x, y);
                link(y, x);
                degreeTable[d] = nullptr;
                d = x->degree;
            }
            degreeTable[d] = x;
        }

        vector<Node*> survivors;
        for (Node *x : degreeTable) if (x) survivors.push_back(x);
        minNode = nullptr;
        for (Node *x : survivors) x->left = x->right = x;
        for (Node *x : survivors) addRoot(x);
    }

    void cut(Node *x, Node *y) {
        if (y->child == x) {
            if (x->right == x) y->child = nullptr;
            else y->child = x->right;
        }
        removeFromList(x);
        y->degree--;
        addRoot(x);
    }

    void cascadingCut(Node *y) {
        Node *z = y->parent;
        if (z) {
            if (!y->mark) y->mark = true;
            else {
                cut(y, z);
                cascadingCut(z);
            }
        }
    }

    static void destroyList(Node *start) {
        if (!start) return;
        vector<Node*> nodes;
        Node *cur = start;
        do {
            nodes.push_back(cur);
            cur = cur->right;
        } while (cur != start);
        for (Node *n : nodes) {
            destroyList(n->child);
            delete n;
        }
    }

public:
    FibonacciHeap() = default;
    FibonacciHeap(const FibonacciHeap&) = delete;
    FibonacciHeap& operator=(const FibonacciHeap&) = delete;
    ~FibonacciHeap() { destroyList(minNode); }

    bool empty() const { return minNode == nullptr; }
    int size() const { return nodeCount; }

    Node* insert(shared_ptr<Batch> batch) {
        Node *node = new Node(move(batch));
        addRoot(node);
        nodeCount++;
        return node;
    }

    shared_ptr<Batch> peek() const {
        return minNode ? minNode->batch : nullptr;
    }

    shared_ptr<Batch> extractMin() {
        if (!minNode) return nullptr;
        Node *z = minNode;
        if (z->child) {
            vector<Node*> children;
            Node *c = z->child, *p = c;
            do {
                children.push_back(p);
                p = p->right;
            } while (p != c);
            for (Node *x : children) {
                removeFromList(x);
                addRoot(x);
            }
            z->child = nullptr;
            z->degree = 0;
        }

        if (z->right == z) minNode = nullptr;
        else {
            Node *next = z->right;
            removeFromList(z);
            minNode = next;
            consolidate();
        }
        auto result = z->batch;
        delete z;
        nodeCount--;
        return result;
    }

    // True Fibonacci Heap Node Removal (O(log N) amortized)
    void remove(Node *x) {
        if (!x) return;
        Node *y = x->parent;
        if (y) {
            cut(x, y);
            cascadingCut(y);
        }
        minNode = x;
        auto dummy = extractMin();
    }

    void clear() {
        destroyList(minNode);
        minNode = nullptr;
        nodeCount = 0;
    }
};

struct DistributionRequest {
    string medicineName;
    int quantity;
};

class MedicineSystem {
    unordered_map<string, shared_ptr<Batch>> byBatch;
    unordered_map<string, list<shared_ptr<Batch>>> byMedicine;
    unordered_map<string, FibonacciHeap> medicineHeaps; // Per-medicine heaps!
    unordered_map<string, FibonacciHeap::Node*> batchNodeMap; // batchId -> Node* pointer
    queue<DistributionRequest> requests;

    static string lowerText(string s) {
        transform(s.begin(), s.end(), s.begin(),
                  [](unsigned char c) { return (char)tolower(c); });
        return s;
    }

    static bool validDate(const string& s) {
        if (s.size() != 10 || s[4] != '-' || s[7] != '-') return false;
        for (int i = 0; i < 10; ++i)
            if (i != 4 && i != 7 && !isdigit((unsigned char)s[i])) return false;
        int y = stoi(s.substr(0, 4)), m = stoi(s.substr(5, 2)), d = stoi(s.substr(8, 2));
        if (m < 1 || m > 12 || d < 1) return false;
        static const int days[] = {31,28,31,30,31,30,31,31,30,31,30,31};
        int maxDay = days[m - 1];
        bool leap = (y % 400 == 0 || (y % 4 == 0 && y % 100 != 0));
        if (m == 2 && leap) maxDay++;
        return d <= maxDay;
    }

    static int daysUntil(const string& date) {
        tm expiryTm = {};
        expiryTm.tm_year = stoi(date.substr(0, 4)) - 1900;
        expiryTm.tm_mon = stoi(date.substr(5, 2)) - 1;
        expiryTm.tm_mday = stoi(date.substr(8, 2));
        expiryTm.tm_hour = 12;
        time_t expiryTime = mktime(&expiryTm);
        time_t now = time(nullptr);
        tm nowTm = *localtime(&now);
        nowTm.tm_hour = 12; nowTm.tm_min = 0; nowTm.tm_sec = 0;
        time_t todayTime = mktime(&nowTm);
        return (int)difftime(expiryTime, todayTime) / (60 * 60 * 24);
    }

public:
    void addBatch() {
        string name, id, expiry;
        int quantity;
        double price;
        cout << "Medicine name: ";
        getline(cin >> ws, name);
        cout << "Batch ID: ";
        getline(cin, id);
        if (byBatch.count(id)) {
            cout << "Batch ID already exists.\n";
            return;
        }
        cout << "Expiry date (YYYY-MM-DD): ";
        cin >> expiry;
        if (!validDate(expiry)) {
            cout << "Invalid date format/date.\n";
            return;
        }
        cout << "Quantity: ";
        if (!(cin >> quantity) || quantity <= 0) {
            cin.clear(); cin.ignore(numeric_limits<streamsize>::max(), '\n');
            cout << "Quantity must be positive.\n";
            return;
        }
        cout << "Unit price: ";
        if (!(cin >> price) || price < 0) {
            cin.clear(); cin.ignore(numeric_limits<streamsize>::max(), '\n');
            cout << "Price cannot be negative.\n";
            return;
        }
        auto b = make_shared<Batch>();
        b->medicineName = name; b->batchId = id; b->expiry = expiry;
        b->quantity = quantity; b->unitPrice = price;
        
        byBatch[id] = b;
        string medKey = lowerText(name);
        byMedicine[medKey].push_back(b);
        
        if (daysUntil(expiry) >= 0) {
            FibonacciHeap::Node* node = medicineHeaps[medKey].insert(b);
            batchNodeMap[id] = node;
        }
        
        save();
        cout << "Batch added successfully.\n";
    }

    void listInventory() {
        if (byBatch.empty()) { cout << "Inventory is empty.\n"; return; }
        cout << left << setw(22) << "Medicine" << setw(14) << "Batch ID"
             << setw(13) << "Expiry" << setw(10) << "Quantity" << "Unit Price\n";
        cout << string(75, '-') << '\n';
        vector<shared_ptr<Batch>> all;
        for (auto &e : byBatch) all.push_back(e.second);
        sort(all.begin(), all.end(), [](const auto& a, const auto& b) {
            if (a->expiry != b->expiry) return a->expiry < b->expiry;
            return a->batchId < b->batchId;
        });
        for (auto &b : all) {
            cout << left << setw(22) << b->medicineName << setw(14) << b->batchId
                 << setw(13) << b->expiry << setw(10) << b->quantity
                 << fixed << setprecision(2) << b->unitPrice;
            if (!b->active) cout << " [INACTIVE]";
            cout << '\n';
        }
    }

    void searchBatch() {
        string id;
        cout << "Enter batch ID: ";
        cin >> id;
        auto it = byBatch.find(id);
        if (it == byBatch.end()) { cout << "Batch not found.\n"; return; }
        auto b = it->second;
        cout << "Medicine: " << b->medicineName << "\nBatch: " << b->batchId
             << "\nExpiry: " << b->expiry << "\nQuantity: " << b->quantity
             << "\nUnit price: " << fixed << setprecision(2) << b->unitPrice
             << "\nStatus: " << (b->active ? "Active" : "Inactive") << '\n';
    }

    void searchMedicine() {
        string name;
        cout << "Enter medicine name: ";
        getline(cin >> ws, name);
        auto it = byMedicine.find(lowerText(name));
        if (it == byMedicine.end()) { cout << "Medicine not found.\n"; return; }
        cout << "Batches for " << name << ":\n";
        for (auto &b : it->second) {
            if (b->active)
                cout << b->batchId << " | expiry " << b->expiry
                     << " | quantity " << b->quantity << '\n';
        }
    }

    void requestDistribution() {
        string name;
        int quantity;
        cout << "Medicine name requested: ";
        getline(cin >> ws, name);
        cout << "Quantity requested: ";
        if (!(cin >> quantity) || quantity <= 0) {
            cin.clear(); cin.ignore(numeric_limits<streamsize>::max(), '\n');
            cout << "Quantity must be positive.\n";
            return;
        }
        requests.push({name, quantity});
        cout << "Distribution request added to queue.\n";
    }

    void processRequest() {
        if (requests.empty()) {
            cout << "No pending distribution requests.\n";
            return;
        }

        auto req = requests.front();
        requests.pop();
        string medKey = lowerText(req.medicineName);
        
        int available = 0;
        auto medIt = byMedicine.find(medKey);
        if (medIt != byMedicine.end()) {
            for (const auto& batch : medIt->second) {
                if (batch->active && batch->quantity > 0 && daysUntil(batch->expiry) >= 0)
                    available += batch->quantity;
            }
        }

        if (available < req.quantity) {
            cout << "Insufficient unexpired stock. Available: " << available
                 << ". Request removed from queue.\n";
            return;
        }

        auto heapIt = medicineHeaps.find(medKey);
        if (heapIt == medicineHeaps.end()) {
            cout << "Insufficient unexpired stock in heap.\n";
            return;
        }

        FibonacciHeap& heap = heapIt->second;
        int remaining = req.quantity;

        while (remaining > 0 && !heap.empty()) {
            auto batch = heap.peek();
            if (!batch || !batch->active || batch->quantity <= 0 || daysUntil(batch->expiry) < 0) {
                // Clean up stale/expired batch from heap
                auto nodeIt = batchNodeMap.find(batch ? batch->batchId : "");
                if (nodeIt != batchNodeMap.end()) {
                    heap.remove(nodeIt->second);
                    batchNodeMap.erase(nodeIt);
                }
                continue;
            }

            int take = min(remaining, batch->quantity);
            batch->quantity -= take;
            remaining -= take;

            cout << "Distributed " << take << " of " << batch->medicineName
                 << " from batch " << batch->batchId << " (expiry "
                 << batch->expiry << ").\n";

            // If batch is fully exhausted, remove it directly using heap.remove() in O(log K)
            if (batch->quantity == 0) {
                auto nodeIt = batchNodeMap.find(batch->batchId);
                if (nodeIt != batchNodeMap.end()) {
                    heap.remove(nodeIt->second);
                    batchNodeMap.erase(nodeIt);
                }
            }
            // Note: If quantity > 0, expiry hasn't changed, so it stays valid at peek() O(1)!
        }

        if (remaining > 0)
            cout << "Warning: could not distribute " << remaining << " units.\n";

        save();
    }

    void expiryAlerts() {
        int threshold;
        cout << "Alert window in days (default 90; enter 0 to use 90): ";
        if (!(cin >> threshold) || threshold < 0) {
            cin.clear(); cin.ignore(numeric_limits<streamsize>::max(), '\n');
            threshold = 90;
        }
        if (threshold == 0) threshold = 90;
        vector<shared_ptr<Batch>> alerts;
        for (auto &e : byBatch) {
            auto b = e.second;
            if (b->active && b->quantity > 0 && daysUntil(b->expiry) <= threshold)
                alerts.push_back(b);
        }
        sort(alerts.begin(), alerts.end(), [](const auto& a, const auto& b) {
            return a->expiry < b->expiry;
        });
        if (alerts.empty()) { cout << "No batches expiring within " << threshold << " days.\n"; return; }
        cout << "Expiry alerts (within " << threshold << " days):\n";
        for (auto &b : alerts) {
            int days = daysUntil(b->expiry);
            cout << b->medicineName << " | " << b->batchId << " | " << b->expiry
                 << " | qty " << b->quantity << " | ";
            if (days < 0) cout << "EXPIRED " << -days << " day(s) ago";
            else if (days == 0) cout << "EXPIRES TODAY";
            else cout << "expires in " << days << " day(s)";
            cout << '\n';
        }
    }

    void deleteBatch() {
        string id;
        cout << "Enter batch ID to deactivate: ";
        cin >> id;
        auto it = byBatch.find(id);
        if (it == byBatch.end()) { cout << "Batch not found.\n"; return; }
        
        auto b = it->second;
        b->active = false;
        b->quantity = 0;

        // Direct O(log K) removal from the medicine's Fibonacci Heap
        auto nodeIt = batchNodeMap.find(id);
        if (nodeIt != batchNodeMap.end()) {
            string medKey = lowerText(b->medicineName);
            auto heapIt = medicineHeaps.find(medKey);
            if (heapIt != medicineHeaps.end()) {
                heapIt->second.remove(nodeIt->second);
            }
            batchNodeMap.erase(nodeIt);
        }

        save();
        cout << "Batch deactivated.\n";
    }

    void save() {
        ofstream out("inventory.csv");
        if (!out) { cout << "Warning: could not save inventory file.\n"; return; }
        out << "medicineName,batchId,expiry,quantity,unitPrice,active\n";
        for (auto &e : byBatch) {
            auto b = e.second;
            out << '"' << b->medicineName << "\"," << b->batchId << ','
                << b->expiry << ',' << b->quantity << ',' << b->unitPrice << ','
                << (b->active ? 1 : 0) << '\n';
        }
    }

    void load() {
        ifstream in("inventory.csv");
        if (!in) return;
        string line;
        getline(in, line);
        while (getline(in, line)) {
            string name, id, expiry;
            int quantity, active;
            double price;
            stringstream ss(line);
            if (!getline(ss, name, ',')) continue;
            if (name.size() >= 2 && name.front() == '"' && name.back() == '"')
                name = name.substr(1, name.size() - 2);
            if (!getline(ss, id, ',') || !getline(ss, expiry, ',')) continue;
            string q, p, a;
            if (!getline(ss, q, ',') || !getline(ss, p, ',') || !getline(ss, a, ',')) continue;
            try {
                quantity = stoi(q); price = stod(p); active = stoi(a);
            } catch (...) { continue; }
            if (!validDate(expiry)) continue;
            
            auto b = make_shared<Batch>();
            b->medicineName = name; b->batchId = id; b->expiry = expiry;
            b->quantity = quantity; b->unitPrice = price; b->active = active != 0;
            
            byBatch[id] = b;
            string medKey = lowerText(name);
            byMedicine[medKey].push_back(b);
            
            if (b->active && b->quantity > 0 && daysUntil(expiry) >= 0) {
                FibonacciHeap::Node* node = medicineHeaps[medKey].insert(b);
                batchNodeMap[id] = node;
            }
        }
    }

    void run() {
        load();
        while (true) {
            cout << "\n========== MEDICINE EXPIRY & DISTRIBUTION OPTIMIZER ==========\n"
                 << "1. Add medicine batch\n"
                 << "2. View inventory\n"
                 << "3. Search by batch ID\n"
                 << "4. Search by medicine name\n"
                 << "5. Add distribution request\n"
                 << "6. Process next distribution request (FEFO)\n"
                 << "7. Expiry alerts\n"
                 << "8. Deactivate batch\n"
                 << "9. Save inventory\n"
                 << "0. Exit\n"
                 << "Choose option: " << flush;
            int choice;
            if (!(cin >> choice)) break;
            switch (choice) {
                case 1: addBatch(); break;
                case 2: listInventory(); break;
                case 3: searchBatch(); break;
                case 4: searchMedicine(); break;
                case 5: requestDistribution(); break;
                case 6: processRequest(); break;
                case 7: expiryAlerts(); break;
                case 8: deleteBatch(); break;
                case 9: save(); cout << "Inventory saved.\n"; break;
                case 0: save(); cout << "Inventory saved. Goodbye.\n"; return;
                default: cout << "Invalid option.\n";
            }
        }
    }
};

int main() {
    
    MedicineSystem app;
    app.run();
    return 0;
}