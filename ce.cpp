#include<iostream>
#include<string>
#include<vector>
#include<list>
#include<bitset>
#include<unordered_map>
#include<set>
#include<map>
#include<queue>
#include<stack>
using namespace std;

#define REP(I,N) for(int (I)=0;(I)<(N);(I)++)
#define FOR(I,A,B) for(int (I)=(A);(I)<=(B);(I)++)

#define MAX_N 702
#define MAX_M 246052 
#define INF 500000
#define NONE -1

enum class Op {
	DEL = 0,
	JOIN,
	MERGE
};

typedef pair<int, int> Pair;
typedef tuple<int, int, int> Tuple;

struct BackInfo {
	BackInfo(Op _op, Pair _e1, Pair _e2, int _w1, int _w2, int _temp) :
		op(_op), e1(_e1), e2(_e2), w1(_w1), w2(_w2), temp(_temp) {};
	BackInfo(Op _op, Pair _e1, int _w1, int _temp) :
		op(_op), e1(_e1), w1(_w1), temp(_temp) {};
	BackInfo(Op _op, Pair _e1, int _w1) :
		op(_op), e1(_e1), w1(_w1) {};
	Op op;
	Pair e1, e2;
	int w1, w2;
	int temp;
};

bool IG[MAX_N][MAX_N];
int IGN, IGM;
int IDEG[MAX_N];

bool G[MAX_N][MAX_N];
bool V[MAX_N];
int GN, GM;
int DEG[MAX_N];
int W[MAX_N][MAX_N];
list<int> M[MAX_N];
stack<stack<BackInfo>> BKSTK;

bool OG[MAX_N][MAX_N];
list<list<int>> OC;
list<Pair> OF;

void AddV(int _v);
void DelV(int _v);
void AddE(Pair _e, bool _b_update_w = false);
void DelE(Pair _e, bool _b_update_w = false, bool _b_bkinfo = false);
bool Quot();
void Weighten();
bool Search(int _k);

#pragma region Init

void InitG() {
	FOR(i, 1, IGN) {
		DEG[i] = IDEG[i];
		V[i] = 1;
		M[i].clear();
		M[i].push_back(i);
		FOR(j, 1, IGN) {
			G[i][j] = IG[i][j];
			W[i][j] = 0;
		}
	}
	GN = IGN;
	GM = IGM;
	while (!BKSTK.empty()) {
		BKSTK.pop();
	}
	OC.clear();
}

void InitOG() {
	FOR(i, 1, IGN) {
		FOR(j, 1, IGN) {
			OG[i][j] = 0;
		}
	}
}

#pragma endregion

#pragma region Get

int GetW(Pair _e) {
	return W[_e.first][_e.second];
}

int GetJoinCost(Pair _e1, Pair _e2) {
	int w1 = GetW(_e1);
	int w2 = GetW(_e2);
	if (w1 * w2 < 0) {
		return min(abs(w1), abs(w2));
	}
	else {
		return 0;
	}
}

int GetMergeCost(int _rep, int _v) {
	int cost = 0;

	FOR(i, 1, IGN) {
		if (V[i] == 0 || i == _rep || i == _v)continue;
		cost += GetJoinCost({ _rep,i }, { _v,i });
	}

	return cost;
}

#pragma endregion

#pragma region Set

void SetW(Pair _e, int _val) {
	W[_e.first][_e.second] = _val;
	W[_e.second][_e.first] = _val;
}

void SetWF(Pair _e) {
	SetW(_e, -INF);
}

void SetWP(Pair _e) {
	SetW(_e, INF);
}

#pragma endregion

#pragma region Graph

void Back() {
	stack<BackInfo> stk = BKSTK.top();
	BKSTK.pop();
	while (!stk.empty()) {
		BackInfo bi = stk.top();
		stk.pop();
		if (bi.op == Op::JOIN) {
			if (bi.temp == 1) {
				AddE(bi.e2);
			}
			else if (bi.temp == 2) {
				DelE(bi.e1);
				AddE(bi.e2);
			}
			else if (bi.temp == 3) {
				AddE(bi.e1);
			}
			SetW(bi.e1, bi.w1);
			SetW(bi.e2, bi.w2);
		}
		else if (bi.op == Op::MERGE) {
			int rep = bi.e1.first;
			int v = bi.e1.second;
			AddV(v);
			AddE({ rep,v });
			SetW({ rep,v }, bi.w1);

			int ofs = M[rep].size() - bi.temp;
			M[v].splice(M[v].end(), move(M[rep]), prev(M[rep].end(), ofs), M[rep].end());
		}
		else if (bi.op == Op::DEL) {
			AddE(bi.e1);
			SetW(bi.e1, bi.w1);
		}
	}
}

void AddV(int _v) {
	V[_v] = 1;
	GN++;
}

void DelV(int _v) {
	V[_v] = 0;
	GN--;
}

void AddE(Pair _e, bool _b_update_w) {
	G[_e.first][_e.second] = 1; G[_e.second][_e.first] = 1;
	DEG[_e.first]++; DEG[_e.second]++;
	GM++;
	if (_b_update_w)SetWP(_e);
}

void DelE(Pair _e, bool _b_update_w, bool _b_bkinfo) {
	if (_b_bkinfo) {
		stack<BackInfo> bkstk;
		bkstk.push(BackInfo(Op::DEL, _e, GetW(_e)));
		BKSTK.push(bkstk);
	}

	G[_e.first][_e.second] = 0; G[_e.second][_e.first] = 0;
	DEG[_e.first]--; DEG[_e.second]--;
	GM--;
	if (_b_update_w)SetWF(_e);
}

void CombineV(int _rep, int _v) {
	M[_rep].insert(M[_rep].end(), M[_v].begin(), M[_v].end());
	FOR(i, 1, IGN) {
		if (V[i] == 0 || i == _v)continue;
		if (G[_v][i] == 1) {
			DelE({ _v,i });
		}
	}
	DelV(_v);
}

void Join(Pair _e1, Pair _e2, stack<BackInfo>& _cont) {
	int w1 = GetW(_e1);
	int w2 = GetW(_e2);
	BackInfo info(Op::JOIN, _e1, _e2, w1, w2, 0);

	int w;
	if (abs(w1) == INF)w = w1;
	else if (abs(w2) == INF)w = w2;
	else { w = w1 + w2; }
	SetW(_e1, w);

	if (w1 > 0 && w2 > 0) {
		DelE(_e2);
		info.temp = 1;
	}
	else if (w1 <= 0 && w2 <= 0) {

	}
	else {
		if (w1 > 0) {
			if (abs(w1) > abs(w2)) {

			}
			else {
				DelE(_e1);
				info.temp = 3;
			}
		}
		else {
			if (abs(w1) < abs(w2)) {
				DelE(_e2);
				AddE(_e1);
				info.temp = 2;
			}
			else {
				DelE(_e2);
				info.temp = 1;
			}
		}
	}

	_cont.push(info);
}

void Merge(int _rep, int _v) {
	stack<BackInfo> bkstk;
	FOR(i, 1, IGN) {
		if (V[i] == 0 || i == _rep || i == _v)continue;
		Join({ _rep,i }, { _v,i }, bkstk);
	}
	list<int>& cont1 = M[_rep];
	list<int>& cont2 = M[_v];
	bkstk.push(BackInfo(Op::MERGE, { _rep,_v }, GetW({ _rep,_v }), M[_rep].size()));
	BKSTK.push(bkstk);
	M[_rep].splice(M[_rep].end(), move(M[_v]));
	DelE({ _rep, _v });
	DelV(_v);
}

bool Quot() {
	bool hit = false;
	vector<list<int>> cc;
	cc.resize(MAX_N);

	int index = 0;
	unordered_map<bitset<MAX_N>, int> mp;

	FOR(i, 1, IGN) {
		if (V[i] == 0)continue;
		bitset<MAX_N> bs;
		bs.set(i);
		FOR(j, 1, IGN) {
			if (V[j] == 0 || i == j)continue;
			else if (G[i][j] == 0) continue;
			bs.set(j);
		}
		if (mp.count(bs) == 0) {
			mp[bs] = index;
			cc[index].push_back(i);
			index++;
		}
		else {
			cc[mp[bs]].push_back(i);
		}
	}

	for (auto& lst : cc) {
		if (lst.size() == 1)continue;
		else if (lst.size() == 0)break;
		hit = true;
		int rep = MAX_N;
		for (int v : lst) {
			if (rep > v) {
				rep = v;
			}
		}
		for (int v : lst) {
			if (v == rep)continue;
			CombineV(rep, v);
		}
	}
	return hit;
}

void Weighten() {
	for (int i = 1; i <= IGN; i++) {
		if (V[i] == 0)continue;
		for (int j = i + 1; j <= IGN; j++) {
			if (V[j] == 0) continue;
			if (G[i][j] == 0) {
				if (GetW({ i,j }) != -INF) {
					SetW({ i,j }, -(int(M[i].size() * M[j].size())));
				}
			}
			else {
				SetW({ i,j }, M[i].size() * M[j].size());
			}
		}
	}
}

#pragma endregion

#pragma region ClusterEditing

void Kernelization(int& _k) {
	while (true) {
		if (GN == 0 || GM == 0)break;
		bool apply = false;
		FOR(i, 1, IGN) {

			if (V[i] == 0)continue;
			if (DEG[i] == 0) {
				list<int> C;
				C.push_back(i);
				OC.push_back(C);
				DelV(i);
				apply = true;
				continue;
			}

			list<int> nei[4];
			vector<int> dist;
			dist.resize(IGN + 1, -1);
			queue<int> q;

			nei[0].push_back(i);
			dist[i] = 0;
			q.push(i);
			while (!q.empty()) {
				int front = q.front();
				q.pop();

				FOR(j, 1, IGN) {
					if (V[j] == 0 || front == j) continue;
					if (G[front][j] == 1 && dist[j] == -1) {
						if (dist[front] + 1 == 4) {
							while (!q.empty()) {
								q.pop();
							}
							break;
						}
						dist[j] = dist[front] + 1;
						nei[dist[j]].push_back(j);
						q.push(j);
					}
				}
			}
			int ori_n1_size = 0;
			int ori_n2_size = 0;
			for (int v : nei[1])ori_n1_size += M[v].size();
			for (int v : nei[2])ori_n2_size += M[v].size();

			if (M[i].size() >= ori_n1_size + ori_n2_size) {
				list<int> C = nei[1];
				C.push_back(i);
				OC.push_back(C);

				int p, q;
				p = q = 0;
				for (int u : nei[1]) {
					DelE({ i,u });
					for (int v : nei[2]) {
						if (G[u][v] == 1) {
							p += M[u].size() * M[v].size();
							DelE({ u,v });
						}
					}
				}
				for (auto itr1 = nei[1].begin(); itr1 != nei[1].end(); itr1++) {
					for (auto itr2 = next(itr1); itr2 != nei[1].end(); itr2++) {
						if (G[*itr1][*itr2] == 0) {
							q += M[*itr1].size() * M[*itr2].size();
						}
						else {
							DelE({ *itr1,*itr2 });
						}
					}
				}

				_k = _k - p - q;
				for (int u : C) {
					DelV(u);
				}
				apply = true;
				break;
			}

			if (M[i].size() >= ori_n1_size) {
				for (int u : nei[1]) {
					list<Pair> e1, e2;
					int e1_size, e2_size;
					e1_size = e2_size = 0;
			
					for (int v : nei[2]) {
						if (G[u][v] == 1) {
							e2.push_back({ u,v });
							e2_size += M[u].size() * M[v].size();
						}
					}
					if (e2.empty())continue;
					for (int v : nei[1]) {
						if (u == v)continue;
						if (G[u][v] == 0) {
							e1.push_back({ u,v });
							e1_size += M[u].size() * M[v].size();
						}
					}
			
					int left = M[i].size() * M[u].size();
					int right = e1_size + e2_size;
					if (left >= right) {
			
						for (Pair e : e2) {
							DelE(e, true);
						}
						_k -= e2_size;
			
						apply = true;
					}
				}
				if (apply == true)break;
			}

			if (M[i].size() >= ori_n1_size && ori_n2_size == 0) {
				list<int> C = nei[1];
				C.push_back(i);
				OC.push_back(C);

				int p = 0;
				for (auto itr1 = nei[1].begin(); itr1 != nei[1].end(); itr1++) {
					DelE({ i,*itr1 });
					for (auto itr2 = next(itr1); itr2 != nei[1].end(); itr2++) {
						if (G[*itr1][*itr2] == 0) {
							p += M[*itr1].size()*M[*itr2].size();
						}
						else {
							DelE({ *itr1,*itr2 });
						}
					}
				}
				_k -= p;

				for (int u : C) {
					DelV(u);
				}

				apply = true;
				break;
			}

			if (M[i].size() > _k) {
				list<int> C = nei[1];
				C.push_back(i);
				OC.push_back(C);

				int p, q;
				p = q = 0;
				for (int u : nei[1]) {
					DelE({ i,u });
					for (int v : nei[2]) {
						if (G[u][v] == 1) {
							p += M[u].size() * M[v].size();
							DelE({ u,v });
						}
					}
				}
				for (auto itr1 = nei[1].begin(); itr1 != nei[1].end(); itr1++) {
					for (auto itr2 = next(itr1); itr2 != nei[1].end(); itr2++) {
						if (G[*itr1][*itr2] == 0) {
							q += M[*itr1].size() * M[*itr2].size();
						}
						else {
							DelE({ *itr1,*itr2 });
						}
					}
				}

				_k = _k - p - q;
				for (int u : C) {
					DelV(u);
				}
				apply = true;
				break;
			}

			if (M[i].size() >= ori_n1_size) {
				list<Pair> del_e;
				int a, b, c;
				a = b = c = 0;

				for (auto itr1 = nei[1].begin(); itr1 != nei[1].end(); itr1++) {
					del_e.push_back({ i,*itr1 });
					for (auto itr2 = next(itr1); itr2 != nei[1].end(); itr2++) {
						if (G[*itr1][*itr2] == 1) {
							a += M[*itr1].size()*M[*itr2].size();
							del_e.push_back({ *itr1,*itr2 });
						}
						else {
							b += M[*itr1].size()*M[*itr2].size();
						}
					}
					for (auto itr3 = nei[2].begin(); itr3 != nei[2].end(); itr3++) {
						if (G[*itr1][*itr3] == 1) {
							c += M[*itr1].size()*M[*itr3].size();
							del_e.push_back({ *itr1,*itr3 });
						}
					}
				}
				int ed = b * 2 + c;

				if (M[i].size() + ori_n1_size > ed) {
					list<int> C = nei[1];
					C.push_back(i);
					OC.push_back(C);

					_k = _k - b - c;
					for (Pair e : del_e) {
						DelE(e);
					}
					for (int u : C) {
						DelV(u);
					}
					apply = true;
					break;
				}
			}
			else {
				list<Pair> del_e;
				int a, b, c;
				a = b = c = 0;

				for (auto itr1 = nei[1].begin(); itr1 != nei[1].end(); itr1++) {
					del_e.push_back({ i,*itr1 });
					for (auto itr2 = next(itr1); itr2 != nei[1].end(); itr2++) {
						if (G[*itr1][*itr2] == 1) {
							a += M[*itr1].size()*M[*itr2].size();
							del_e.push_back({ *itr1,*itr2 });
						}
						else {
							b += M[*itr1].size()*M[*itr2].size();
						}
					}
					for (auto itr3 = nei[2].begin(); itr3 != nei[2].end(); itr3++) {
						if (G[*itr1][*itr3] == 1) {
							c += M[*itr1].size()*M[*itr3].size();
							del_e.push_back({ *itr1,*itr3 });
						}
					}
				}
				int ed = b * 2 + c;

				if (M[i].size() + ori_n1_size > ed) {
					int right = (M[i].size() + ori_n1_size);
					int left = 0;
					int t = -1;
					int m = -1;
					for (int u : nei[2]) {
						list<int> nei_u;
						FOR(j, 1, IGN)if (V[j] == 1 && G[u][j] == 1)nei_u.push_back(j);
						for (int v : nei[1]) {
							for (int w : nei_u) {
								if (v == w) {
									left += M[v].size();
									m = w;
									continue;
								}
							}
						}
						if (left * 2 > right) {
							t = u;
							break;
						}
					}
					if (t == -1) {
						list<int> C = nei[1];
						C.push_back(i);
						OC.push_back(C);

						_k = _k - b - c;
						for (Pair e : del_e) {
							DelE(e);
						}
						for (int u : C) {
							DelV(u);
						}

						apply = true;
						break;
					}

					if (M[i].size() >= ori_n1_size) {
						list<int> C = nei[1];
						C.push_back(i);
						OC.push_back(C);

						_k = _k - ori_n1_size;
						for (Pair e : del_e) {
							DelE(e);
						}
						for (int u : C) {
							DelV(u);
						}

						apply = true;
						break;
					}
				}
			}
		}

		if (apply == false)break;
		else {
			Quot();
		}
	}
}

void Found() {
	InitOG();
	list<Pair> F;
	for (auto& c : OC) {
		for (auto itr1 = c.begin(); itr1 != c.end(); itr1++) {
			if (M[*itr1].size() > 1) {
				for (int u : M[*itr1]) {
					for (int v : M[*itr1]) {
						if (u == v)continue;
						OG[u][v] = 1;
						OG[v][u] = 1;
					}
				}
			}
			for (auto itr2 = next(itr1); itr2 != c.end(); itr2++) {
				for (int u : M[*itr1]) {
					for (int v : M[*itr2]) {
						OG[u][v] = 1;
						OG[v][u] = 1;
					}
				}
			}
		}
	}

	for (int i = 1; i <= IGN; i++) {
		if (V[i] == 0)continue;
		if (M[i].size() > 1) {
			for (int u : M[i]) {
				for (int v : M[i]) {
					if (u == v)continue;
					OG[u][v] = 1;
					OG[v][u] = 1;
				}
			}
		}
		for (int j = i + 1; j <= IGN; j++) {
			if (V[j] == 0)continue;
			if (G[i][j] == 1) {
				for (int u : M[i]) {
					for (int v : M[j]) {
						OG[u][v] = 1;
						OG[v][u] = 1;
					}
				}
			}
		}
	}
	for (int i = 1; i <= IGN; i++) {
		for (int j = i + 1; j <= IGN; j++) {
			if (OG[i][j] != IG[i][j]) {
				F.push_back({ i,j });
			}
		}
	}

	OF = F;
}

bool BranchUV(int _k, Pair _uv) {
	int a = GetW(_uv);
	int b = GetMergeCost(_uv.first, _uv.second);

	Merge(_uv.first, _uv.second);
	bool ans = Search(_k - b);
	Back();
	if (ans) return true;

	DelE(_uv, true, true);
	ans = Search(_k - a);
	Back();
	if (ans)return true;

	return false;
}

bool Search(int _k) {
	if (_k < 0) return false;

	int max_ct_cnt = 0;
	Pair max_uv = { -1,-1 };
	for (int i = 1; i <= IGN; i++) {
		if (V[i] == 0)continue;
		for (int j = i + 1; j <= IGN; j++) {
			if (V[j] == 0 || G[i][j] == 0)continue;
			Pair uv_temp = { i,j };
			int ct_cnt = 0;
			for (int k = 1; k <= IGN; k++) {
				if (V[k] == 0 || i == k || j == k)continue;
				if ((G[i][k] == 1 && G[j][k] == 0) ||
					(G[i][k] == 0 && G[j][k] == 1)) {
					ct_cnt++;
				}
			}
			if (ct_cnt > max_ct_cnt) {
				max_ct_cnt = ct_cnt;
				max_uv = uv_temp;
				if (max_ct_cnt >= 4) {
					i = IGN;
					j = IGN;
					break;
				}
			}
		}
	}

	Pair uv = max_uv;
	if (max_ct_cnt == 0) {
		Found();
		return true;
	}
	else {
		return BranchUV(_k, uv);
	}
}

void SolveBi() {
	int l = 0;
	int r = (IGN * (IGN - 1) / 2);
	list<Pair> ans;

	while (l <= r) {
		int k = (r + l) / 2;
		int k_temp = k;

		InitG();
		Quot();
		Kernelization(k_temp);
		Weighten();
		if (k_temp < 0) {
			l = k + 1;
		}
		else if (Search(k_temp) == false) {
			l = k + 1;
		}
		else {
			ans = OF;
			r = ans.size() - 1;
		}

	}

	for (Pair uv : ans) {
		cout << uv.first << " " << uv.second << endl;
	}
}

#pragma endregion

int main(int argc, char *argv[]) {
	REP(i, MAX_N) {
		V[i] = 0;
		DEG[i] = 0;
		M[i].push_back(i);
		REP(j, MAX_N) {
			G[i][j] = 0;
			W[i][j] = 0;
		}
	}

	string str, line;
	int n, m;
	cin >> str;
	while (true) {
		if (str == "p") {
			cin >> str >> n >> m;
			break;
		}
		else {
			getline(cin, line);
			cin >> str;
		}
	}

	FOR(i, 1, n) {
		AddV(i);
	}
	REP(i, m) {
		int u, v;
		cin >> str;
		if (str == "c") {
			getline(cin, line);
			i--;
		}
		else {
			u = atoi(str.c_str());
			cin >> v;
			AddE({ u,v });
		}
	}
	IGN = GN; IGM = GM;

	REP(i, MAX_N) {
		IDEG[i] = DEG[i];
		REP(j, MAX_N) {
			IG[i][j] = G[i][j];
		}
	}

	SolveBi();

	return 0;
}
