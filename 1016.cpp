//I will chase the meteor for you, a thousand times over.
//Please wait for me.

#include <bits/stdc++.h>
#define rep(i,a,b) for (int i = a , _ = b ; i <= _ ; i ++)
#define per(i,a,b) for (int i = a , _ = b ; i >= _ ; i --)
#define fore(i,u)  for (int i = head[u] ; i ; i = nxt[i])

#define pii pair<int , int>
#define fir first
#define sec second
#define ms(x,a) memset(x , (a) , sizeof (x))

#define gprintf(...) fprintf(stderr , __VA_ARGS__)
#define gout(x) std::cerr << #x << "=" << x << std::endl
#define gout1(a,i) std::cerr << #a << '[' << i << "]=" << a[i] << std::endl
#define gout2(a,i,j) std::cerr << #a << '[' << i << "][" << j << "]=" << a[i][j] << std::endl

template <class T> inline void upmax(T&a , T b) { if (a < b) a = b ; }
template <class T> inline void upmin(T&a , T b) { if (a > b) a = b ; }

const int maxn = 107;
const int maxm = 1007;
const int mod = 31011;

typedef long long ll;

typedef int arr[maxn];
typedef int adj[maxm];

inline int add(int a , int b) { return ((ll) a + b) % mod ; }
inline int mul(int a , int b) { return ((ll) a * b) % mod ; }
inline int dec(int a , int b) { return add(a , mod - b % mod) ; }
inline int Pow(int a , int b , int P = mod) {
	int t = 1;
	while (b) {
		if (b & 1) t = 1ll * t * a % P;
		a = 1ll * a * a % P , b >>= 1;
	}
	return t;
}
void exgcd(int a , int b , ll&x , ll&y) {
	if (!b) {
		x = 1 , y = 0;
		return;
	}
	exgcd(b , a % b , y , x);
	y -= a / b * x;
}

#define gc getchar
#define idg isdigit
#define rd RD<int>
#define rdll RD<long long>
template <typename Type>
inline Type RD() {
	char c = getchar(); Type x = 0 , flag = 1;
	while (!idg(c) && c != '-') c = getchar();
	if (c == '-') flag = -1; else x = c - '0';
	while (idg(c = gc()))x = x * 10 + c - '0';
	return x * flag;
}
inline char rdch() {
	char c = gc();
	while (!isalpha(c)) c = gc();
	return c;
}
#undef idg
#undef gc

// beginning

struct edge {
	int u , v , w;
	edge(int u = 0 , int v = 0 , int w = 0): u(u) , v(v) , w(w)
		{ }
};

edge E[maxm];

int n , m;

struct UFS {
	arr fa;
	int cnt;

	int find(int u) { return u == fa[u] ? u : fa[u] = find(fa[u]) ; }

	inline bool link(int u , int v) {
		u = find(u) , v = find(v);
		if (u == v) return 0;
		cnt ++ , fa[u] = v;
		return 1;
	}

	inline void init(int n) {
		rep (i , 1 , n) fa[i] = i;
		cnt = 1;
	}

	inline bool same(int u , int v) {
		return find(u) == find(v);
	}
};

UFS ufs_all;

void input() {
	n = rd() , m = rd();
	rep (i , 1 , m)
		E[i].u = rd() , E[i].v = rd() , E[i].w = rd();
}

struct matrix_tree {

	int a[101][101];
	int n;
	int id[101];

	inline void clear() {
		ms(id , 0) , ms(a , 0);
		n = 0;
	}

	inline void add(int u , int v , int w) {
//		gprintf("add %d %d %d\n" , u , v , w);
		if (!id[u]) id[u] = ++ n;
		if (!id[v]) id[v] = ++ n;
		u = id[u] , v = id[v];
		a[u][u] += w , a[v][v] += w , a[u][v] -= w , a[v][u] -= w;
	}

	inline int calc(int P) {
		int flag = 1;
		n --;
//		rep (i , 1 , n) rep (j , 1 , n) gprintf("%d%c" , a[i][j] , j == _ ? '\n' : ' ');
		rep (i , 1 , n) rep (j , 1 , n) a[i][j] %= P;
		rep (i , 1 , n) {
			int j = i;
			while (j <= n && !a[j][i]) j ++;
			if (j > n) break;
			if (i != j) {
				flag *= -1;
				rep (k , 1 , n) std::swap(a[j][k] , a[i][k]);
			}
			int v = Pow(a[i][i] , P - 2 , P);
//			gout2(a , i , i);
//			gout(v);
//			assert(v * a[i][i] % P == 1);
			rep (j , i + 1 , n) if (a[j][i]) {
				int t = 1ll * a[j][i] * v % P;
				rep (k , i , n) {
					(a[j][k] -= 1ll * t * a[i][k] % P) %= P;
					if (a[j][k] < 0)
						a[j][k] += P;
				}
			}
		}
		int res = 1;
		rep (i , 1 , n)
			(res *= a[i][i]) %= P;
		if (flag == -1)
			res *= -1;
		if (res < 0)
			res += P;
//		gout(res);
		return res % P;
	}
};

namespace Graph {
	using namespace std;

	UFS ufs;
	vector<edge> E;
	map<int , int> id;
	matrix_tree Matrix[maxn];
	int vis[maxn] , tot;
	arr G[maxn] , idx;
	set<pii> exi;

	inline bool exist(int u , int v) {
		return exi.find(pii(min(u , v) , max(u , v))) != exi.end();
	}

	inline void append(int u , int v) {
		exi.insert(pii(min(u , v) , max(u , v)));
	}

	inline void init(int N) {
		id.clear() , E.clear();
		rep (i , 1 , n) vis[i] = 0;
		rep (i , 1 , tot) idx[i] = 0;
		tot = 0 , exi.clear();
		ufs.init(n);
	}

	inline void Link(int u , int v) {
//		u = id[u] , v = id[v];
//		gprintf("link %d %d\n" , u , v);
		if (ufs_all.same(u , v))
			return;
		u = ufs_all.find(u) , v = ufs_all.find(v);
		if (!id[u]) id[u] = ++ tot , idx[tot] = u;
		if (!id[v]) id[v] = ++ tot , idx[tot] = v;
		ufs.link(u , v);
		G[u][v] ++ , G[v][u] ++;
		if (!exist(u , v))
			E.push_back(edge(u , v , 0)),
			append(u , v);
	}

	matrix_tree tmp;

	inline int calc() {
		rep (i , 1 , n)
			Matrix[i].clear();
		for (__typeof(E.begin()) it = E.begin() ; it != E.end() ; it ++)
			Matrix[ufs.find(it->u)].add(it->u , it->v , G[it->u][it->v]);

		int res = 1;
		rep (i , 1 , tot) {
			int u = ufs.find(idx[i]);
			if (!vis[u]) {
				tmp = Matrix[u];
				int cur = 0;
				int b1 = Matrix[u].calc(3);
				int b2 = tmp.calc(mod / 3);
//				gout(b1);
//				gout(b2);
				ll a1 , a2 , d;
				exgcd(3 , mod / 3 , d , a1);
				cur = (mod / 3 * a1 * b1) % mod;
				exgcd(mod / 3 , 3 , d , a2);
				(cur += 3ll * a2 * b2 % mod) %= mod;
				if (cur < 0)
					cur += mod;
				res = mul(res , cur);
//				gout(res);
				vis[u] = 1;
			}
		}

		for (__typeof(E.begin()) it = E.begin() ; it != E.end() ; it ++)
			ufs_all.link(it->u , it->v);
//		gprintf("end of calculating det\n");
		return res;
	}
}

inline bool cmp(const edge a , const edge b) {
	return a.w < b.w;
}

void solve() {
	std::sort(E + 1 , E + m + 1 , cmp);
	int ans = 1;
	ufs_all.init(n);

	for (int i = 1 , j ; i <= m ; i = j + 1) {
		j = i;
		while (j < m && E[i].w == E[j + 1].w) j ++;
		Graph::init(std::min((j - i + 1) * 2 , n));
		rep (k , i , j) Graph::Link(E[k].u , E[k].v);
		int cnt = Graph::calc();
//		gout(cnt);
		ans = mul(ans , cnt);
//		gout(ans);
//		assert(ans >= 0);
	}

	if (ufs_all.cnt != n) {
//		assert(0);
		puts("0");
		return;
	}
	printf("%d\n" , ans);
}

int main() {
	#ifndef ONLINE_JUDGE
		freopen("data.txt" , "r" , stdin);
	#endif
	input();
	solve();
	return 0;
}
