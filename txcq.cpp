#define _CRT_SECURE_NO_WARNINGS
#include<malloc.h>
#include<iostream>
#include<fstream>
#include<cstring>
#include<string>
#include<vector>
#include<cstdio>
#include<unordered_map>
#include<unordered_set>
#include<set>
#include<algorithm>
#include<chrono>
#include<array>
#include<map>
#include<queue>
#include"ef.h"
using namespace std;
using std::chrono::duration_cast;
using std::chrono::milliseconds;
using std::chrono::nanoseconds;
using std::chrono::system_clock;
using std::chrono::high_resolution_clock;

void buildtel_fast(int l, int r);
void initMH_fast(int l, int r);
void InitOrderArcSet();
void ArcBetwIntval(int ts, int te, vector<int>& output);

/*** TEL Ultra ***/
const int VMAX = 4000000;  //Default:4000000
const int EMAX = 50000000;//Default:130000000
const int TMAX = 50000000;//Default:1665000000


int vern = 0;
int arcn = 0;
int tmax = 0;//max orginal timestamps
int tmin = 0x7fffffff; //min orginal timestamps
int span = 0;//orignial time span of input graph

struct arc {
	int src, dst, t;
}arcs[EMAX];

int *hs = 0;
int *hd = 0;
int *ht = 0;
int *spre = 0, *snxt = 0;
int *dpre = 0, *dnxt = 0;
int *tpre = 0, *tnxt = 0;
int *telarc = 0;
int idx = 0;

int head = -1, tail = -1;
int *tsarc = 0;
int *tsnxt = 0, *tspre = 0;
int idt = 0;

vector<int> consecutive_timestamp;

int num_of_distinct_ts;

#define _init_arr(name,size) name = new int[size]

void initmem()
{
	_init_arr(hs, VMAX);
	_init_arr(hd, VMAX);
	_init_arr(ht, TMAX);
	_init_arr(spre, EMAX), _init_arr(snxt, EMAX);
	_init_arr(dpre, EMAX), _init_arr(dnxt, EMAX);
	_init_arr(tpre, EMAX), _init_arr(tnxt, EMAX);
	_init_arr(telarc, EMAX);

	_init_arr(tsarc, EMAX);
	_init_arr(tsnxt, EMAX);
	_init_arr(tspre, EMAX);
}

void addt(int t)
{
	if (head == -1) head = idt;
	tsarc[idt] = t;
	tspre[idt] = tail, tsnxt[idt] = -1; 
	if (tail >= 0) tsnxt[tail] = idt; tail = idt;
	idt++;
}

void delt(int t)
{
	int i = (lower_bound(tsarc, tsarc + idt, t) - tsarc);
	if (head == i) head = tsnxt[i];
	else if (tsnxt[i] == -1) tsnxt[tspre[i]] = -1, tail = tspre[i];
	else {
		tsnxt[tspre[i]] = tsnxt[i];
		tspre[tsnxt[i]] = tspre[i];
	}
}

void addarc(int id, int src, int dst, int t)
{
	telarc[idx] = id;
	snxt[idx] = hs[src]; if (hs[src] >= 0) spre[hs[src]] = idx; hs[src] = idx;
	dnxt[idx] = hd[dst]; if (hd[dst] >= 0) dpre[hd[dst]] = idx; hd[dst] = idx;
	tnxt[idx] = ht[t]; if (ht[t] >= 0) tpre[ht[t]] = idx; ht[t] = idx;
	idx++;
}

void delarc_l(int *head, int *next, int* pre, int i, int idx)
{
	if (head[i] == idx) head[i] = next[idx];
	else if (next[idx] == -1) next[pre[idx]] = -1;
	else {
		next[pre[idx]] = next[idx];
		pre[next[idx]] = pre[idx];
	}
}

/*** DataSet***/
const int QMAX = 45000;
struct Q {
	int l, r, k;
}q[QMAX];
int qcnt = 0;

//read the graph file
void loadgraph(const char* name)
{
	ifstream fin(name, ios::in);
#ifdef _DEBUG
	if (fin.is_open() == false) { printf("open graph %s fail\n", name); exit(1); }
#endif
	vector<int> v;

	string l;
	while (getline(fin, l))
	{
		int uvt[3] = { 0 };
		int p = -1, np = -1;
		for (int i = 0; i < 3; ++i)
		{
			p = np + 1, np = l.find(' ', np + 1);
			if (np == -1) np = l.size();
			uvt[i] = stoi(l.substr(p, np - p));
		}
		v.push_back(uvt[0]), v.push_back(uvt[1]);
		tmin = min(tmin, uvt[2]);
		tmax = max(tmax, uvt[2]);
		consecutive_timestamp.push_back(uvt[2]);
		arcs[arcn++] = { uvt[0], uvt[1], uvt[2] };
	}

	span = tmax - tmin;

	sort(v.begin(), v.end());
	v.erase(unique(v.begin(), v.end()), v.end());
	vern = v.size();

	sort(consecutive_timestamp.begin(), consecutive_timestamp.end());
	consecutive_timestamp.erase(unique(consecutive_timestamp.begin(), consecutive_timestamp.end()), consecutive_timestamp.end());
	num_of_distinct_ts = consecutive_timestamp.size();

	auto get_v = [&](int v_raw) {//节点编号连续化的映射函数,从1开始
		return (lower_bound(v.begin(), v.end(), v_raw) - v.begin()) + 1;
	};

	auto get_t = [&](int t_raw) {//时间戳连续化的映射函数,从1开始
		return (lower_bound(consecutive_timestamp.begin(), consecutive_timestamp.end(), t_raw) - consecutive_timestamp.begin()) + 1;
	};

	for (int i = 0; i < arcn; ++i)
	{
		arcs[i].src = get_v(arcs[i].src), arcs[i].dst = get_v(arcs[i].dst);
		if (arcs[i].src > arcs[i].dst) swap(arcs[i].src, arcs[i].dst);
		arcs[i].t = get_t(arcs[i].t);
	}

	InitOrderArcSet();

}

//read the test file
void loadtest(const char* name)
{
	ifstream fin(name, ios::in);
#ifdef _DEBUG
	if (fin.is_open() == false) { printf("open test %s fail\n", name); exit(1); }
#endif

	string l;
	while (getline(fin, l))
	{
		int lrk[3] = { 0 };
		int p = -1, np = -1;
		for (int i = 0; i < 3; ++i)
		{
			p = np + 1, np = l.find('\t', np + 1);
			if (np == -1) np = l.size();
			lrk[i] = stoi(l.substr(p, np - p));
		}
		q[qcnt++] = { lrk[0], lrk[1], lrk[2] };
	}

}


/*** TCD Operation Part ***/
template<typename T>
void hash_combine(size_t& seed, T const& v)
{
	seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

struct pair_hash
{
	template<typename T1, typename T2>
	size_t operator()(std::pair<T1, T2>const& p) const
	{
		size_t seed = 0;
		hash_combine(seed, p.first);
		hash_combine(seed, p.second);
		return seed;
	}
};

unordered_map<int, int> Mv;
unordered_map<pair<int, int>, int, pair_hash> Mc;
set<pair<int, int>> Hv;

//remove edge (src, dst) and update 3 auxiliary structures in TCQ
bool cUpd(int src, int dst)
{
	bool ret = false;
	Mc[{src, dst}] --;
	if (Mc[{src, dst}] == 0) { Mc.erase({ src, dst }); ret = true; }
	return ret;
}

//decrease degree of v by 1 and update auxiliary structures
void vUpd(int v)
{
	int d = Mv[v];
	Hv.erase({ d, v });
	Hv.insert({ d - 1, v });
	Mv[v] --;
}

//Truncation of TCQ
void trunc(int l, int r)
{
	int hh = head, tt = tail;
	while (hh >= 0 && tsarc[hh] < l)
	{
		int t = tsarc[hh];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			if (cUpd(arcs[id].src, arcs[id].dst)) {
				vUpd(arcs[id].src);
				vUpd(arcs[id].dst);
			}
		}
		hh = tsnxt[hh];
	}
	while (tt >= 0 && tsarc[tt] > r)
	{
		int t = tsarc[tt];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			if (cUpd(arcs[id].src, arcs[id].dst)) {
				vUpd(arcs[id].src);
				vUpd(arcs[id].dst);
			}
		}
		tt = tspre[tt];
	}
	head = hh, tail = tt;
}

//Decomposition of TCQ
void decomp(int k)
{
	while (Hv.size() && (Hv.begin()->first<k))
	{
		auto nv = *(Hv.begin());
		Hv.erase(Hv.begin());
		int n = nv.first, v = nv.second;
		Mv.erase(v);
		unordered_set<int> nbr;
		for (int i = hs[v]; ~i; i = snxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			cUpd(arcs[id].src, arcs[id].dst);
			int u = arcs[id].src == v ? arcs[id].dst : arcs[id].src;
			nbr.insert(u);
		}
		for (int i = hd[v]; ~i; i = dnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			cUpd(arcs[id].src, arcs[id].dst);
			int u = arcs[id].src == v ? arcs[id].dst : arcs[id].src;
			nbr.insert(u);
		}
		for (auto u : nbr) vUpd(u);
	}
}

//TCD Operation
void tcdop(int l, int r, int k)
{
	trunc(l, r);
	decomp(k);
}


/*** TCD Algorithm Part ***/
//Two TEL objects exist in memory during TCQ
int *_hs = 0;
int *_hd = 0;
int *_ht = 0;
int *_spre = 0, *_snxt = 0;
int *_dpre = 0, *_dnxt = 0;
int *_tpre = 0, *_tnxt = 0;
int *_telarc = 0;
int _idx = 0;

int _head = -1, _tail = -1;
int *_tsarc = 0;
int *_tsnxt = 0, *_tspre = 0;
int _idt = 0;

unordered_map<int, int> _Mv;
unordered_map<pair<int, int>, int, pair_hash> _Mc;
set<pair<int, int>> _Hv;

int vbytes = 0; //sizeof hd and hs
int cbytes = 0; //sizeof telarc
int tsbytes = 0;//sizeof tsarc
int htbytes = 0;//sizeof ht

void _initmem()//init memories on heap
{
	_init_arr(_hs, VMAX);
	_init_arr(_hd, VMAX);
	_init_arr(_ht, TMAX);
	_init_arr(_spre, EMAX), _init_arr(_snxt, EMAX);
	_init_arr(_dpre, EMAX), _init_arr(_dnxt, EMAX);
	_init_arr(_tpre, EMAX), _init_arr(_tnxt, EMAX);
	_init_arr(_telarc, EMAX);

	_init_arr(_tsarc, EMAX);
	_init_arr(_tsnxt, EMAX);
	_init_arr(_tspre, EMAX);
}

void bkp()//back up the TEL at the beginning of a new TCD
{
	memcpy(_hs, hs, vbytes);
	memcpy(_hd, hd, vbytes);
	memcpy(_ht, ht, htbytes);
	memcpy(_spre, spre, cbytes); memcpy(_snxt, snxt, cbytes);
	memcpy(_dpre, dpre, cbytes); memcpy(_dnxt, dnxt, cbytes);
	memcpy(_tpre, tpre, cbytes); memcpy(_tnxt, tnxt, cbytes);
	memcpy(_telarc, telarc, cbytes);

	_head = head, _tail = tail;
	memcpy(_tsarc, tsarc, tsbytes);
	memcpy(_tsnxt, tsnxt, tsbytes);
	memcpy(_tspre, tspre, tsbytes);

	_Mv.clear();
	_Mc.clear();
	_Hv.clear();

	_Mv = Mv;
	_Mc = Mc;
	_Hv = Hv;
}

void rst()//restore the TEL after the TCD of the row
{
	memcpy(hs, _hs, vbytes);
	memcpy(hd, _hd, vbytes);
	memcpy(ht, _ht, htbytes);
	memcpy(spre, _spre, cbytes); memcpy(snxt, _snxt, cbytes);
	memcpy(dpre, _dpre, cbytes); memcpy(dnxt, _dnxt, cbytes);
	memcpy(tpre, _tpre, cbytes); memcpy(tnxt, _tnxt, cbytes);
	memcpy(telarc, _telarc, cbytes);

	head = _head, tail = _tail;
	memcpy(tsarc, _tsarc, tsbytes);
	memcpy(tsnxt, _tsnxt, tsbytes);
	memcpy(tspre, _tspre, tsbytes);

	Mv.clear();
	Mc.clear();
	Hv.clear();

	Mv = _Mv;
	Mc = _Mc;
	Hv = _Hv;
}

//Informations for collected in some experiments (may not in paper)
const int infosum =  12;
enum INFO
{
	CELL,
	SQZ,
	RLC,
	TAG,
	PoR,
	PoU,
	PoL,
	CPoR,
	CPoU,
	CPoL,
	TOTALSIZE,
	SCCNUM,
};
long long cntinfo[infosum] = {0ll};

const int MAX_SPAN = 11000;
//auto prune_flag = new array<array<int, MAX_SPAN>, MAX_SPAN>; 

//the function that processes each enumerated temporal k-core during TCD/OTCD
void proc(int ts, int te, int ts_i, int te_i);//tailored processing function

void tcd(int ql, int qr, int qk)
{
	int ts = ql;
	while (ts <= qr)
	{
		int te = qr;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		while (te >= ts)
		{
			proc(ts, te, tsarc[head], tsarc[tail]);
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		ts++;
		rst();
	}
}

set<pair<int, int>> tti_set;//all distinct TTI of temporal k-cores

//OTCD function
void otcd(int ql, int qr, int qk)
{
	tti_set.clear();
	unordered_map<int, int> endr; //end_pos for RoU
	int ts = 0, te = 0;      //current cell
	int _ts = ql, _te = qr;	 //first cell in next row
	auto rlc = [&](int __te) { 
		if (__te < te)
		{
			te = __te;//PoR
		}
	}; //PoR
	auto sqz = [&](int __ts, int __te) {
		if (ts < __ts || te > __te) { //Overline Trigger
			_ts = __ts;  //PoU
			_te = __te;  //PoL
		}
	};
	auto tag = [&](int __ts)
	{
		if (ts < __ts) //Overline Triggered
		{
			for (int r = ts + 1; r <= __ts; ++r)
			{
				if (endr.count(r) == 0)
					endr[r] = -1;
				endr[r] = max(endr[r], te + 1); //Tag for PoU
			}
		}
	};
	auto pou = [&](int ts, int te) { return endr.count(ts) && endr[ts] >= te; };//PoU

	while (_ts <= _te)
	{
		ts = _ts, te = _te;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		sqz(tsarc[head], tsarc[tail]);
		while (ts <= te)
		{
			proc(ts, te, tsarc[head], tsarc[tail]);
			rlc(tsarc[tail]);
			tag(tsarc[head]);
			if (pou(ts, te)) break;
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		_ts++;
		rst();
	}
}

//contruct the TEL for projection graph over [l,r]
void buildtel(int l, int r)
{
	memset(hs, -1, VMAX * sizeof(int));
	memset(hd, -1, VMAX * sizeof(int));
	memset(ht, -1, TMAX * sizeof(int));
	head = -1, tail = -1;
	idx = 0, idt = 0;
	vector<int> ts;
	for (int i = 0; i < arcn; ++i)
		if (arcs[i].t >= l && arcs[i].t <= r)
		{
			addarc(i, arcs[i].src, arcs[i].dst, arcs[i].t);
			ts.push_back(arcs[i].t);
		}

	sort(ts.begin(), ts.end());
	ts.erase(unique(ts.begin(), ts.end()), ts.end());
	for (auto t : ts) addt(t);
	
	vbytes = (vern + 1) * sizeof(int);
	cbytes = idx * sizeof(int);
	tsbytes = idt * sizeof(int);
	htbytes = (num_of_distinct_ts + 1) * sizeof(int);
}

bool cAdd(int src, int dst)
{
	if (Mc.count({ src, dst }) == 0)
	{
		Mc[{src, dst}] = 1;
		return true;
	}
	Mc[{src, dst}] ++;
	return false;
}

void vAdd(int v)
{
	if (Mv.count(v) == 0) Mv[v] = 0;
	Hv.erase({ Mv[v], v });
	Mv[v] ++;
	Hv.insert({ Mv[v], v });
}

//init the auxiliary structures for projection graph over [l,r]
void initMH(int l, int r)
{
	Mv.clear();
	Mc.clear();
	Hv.clear();
	for (int i = 0; i < arcn; ++i)
	{
		int src = arcs[i].src;
		int dst = arcs[i].dst;
		int t = arcs[i].t;
		if (t < l || t > r) continue;
		if (cAdd(src, dst))
		{
			vAdd(src);
			vAdd(dst);
		}
	}
}


void proc(int ts, int te, int ts_i, int te_i)
{//implement the processing of an obtained core	
}


enum X_PROPERTY {
	TIME_INSENSITIVE,
	TIME_INCREASING,
	TIME_DECREASING,
};	//temporal property of X

enum T_QUERY {
	OPTIMIZING,
	CONSTRAINING,
};//TxCQ query type

const char* QUERY_TYPE[2] = {
	"OPTIMIZING",
	"CONSTRAINING",
};

/*** Phase 1 ***/
typedef std::pair<int, int> TTI;
typedef std::vector<pair<int, int>> LTI;
typedef std::pair<const TTI, LTI> ZONE;
std::unordered_map<TTI, LTI, pair_hash> zone_set;

const int XTYPE_NUM = 10;
enum X_MEANING {
	USER_ENGAGEMENT,
	CONNECTION_STRENTH,
	PERIODICITY,
	PERSISTENCY,
	SIZE,
};//possible X
const char* XMEAN_S[XTYPE_NUM] = {
	"USER_ENGAGEMENT",
	"CONNECTION_STRENTH",
	"PERIODICITY",
	"PERSISTENCY",
	"SIZE"
};//name of possible X

typedef double (*xcomputefunc)(int start_time, int end_time, int tti_ts, int tti_te);

std::unordered_map<pair<int, int>, std::unordered_map<int, int>, pair_hash> zone_core_deg;

//functions that can be implemented
xcomputefunc XValueComputeFunc[XTYPE_NUM] = {
	CompEngagementVal,
	CompConnStrength,
	CompPeriodicity,
	CompPersistency,
	CompSize,
	NULL,
	NULL,
	NULL,
	NULL,
	NULL,
};

//Optimizing Local Search
void OptLocalSearch(ZONE& z, X_MEANING x, X_PROPERTY xp, int k)
{
	TTI tti = z.first;
	LTI lti = z.second;
	if (xp == X_PROPERTY::TIME_INSENSITIVE || xp == X_PROPERTY::TIME_INCREASING)
	{
		double local_optx = XValueComputeFunc[x](tti.first, tti.second, tti.first, tti.second);
		if (qinterval_start == -1 || local_optx > global_optx)//如果要找X最小的就<，最大的就>
		{
			global_optx = local_optx;
			qinterval_start = tti.first;
			qinterval_end = tti.second;
		}
	}
	else if (xp == X_PROPERTY::TIME_DECREASING)
	{
		double local_optx = -1.0;
		int l = -1, r = -1;
		for (auto lst : lti)
		{
			double xvalue = XValueComputeFunc[x](lst.first, lst.second, tti.first, tti.second);
			if (xvalue > local_optx)
			{
				local_optx = xvalue;
				l = lst.first, r = lst.second;
			}
		}
		if (local_optx > global_optx)
		{
			global_optx = local_optx;
			qinterval_start = l;
			qinterval_end = r;
		}
	}
}

/*** Constraining Query***/
struct Area {
	int sfrom, sto;
	int efrom, eto;
};
vector<Area> R;

//Constraining Local Search
void ConLocalSearch(ZONE& z, X_MEANING x, X_PROPERTY xp, int k, double sigma)
{
	TTI tti = z.first;
	LTI lti = z.second;
	sort(lti.begin(),lti.end());
	size_t n = lti.size();
	//重新存储n个loosest time interval:[ts1,te1],[ts2,te2],...,[tsn,ten]，满足ts1 < ts2 < ... < tsn
	int* ts = new int[n + 1]; //ts[1-n]
	int* te = new int[n + 1]; //te[1-n]
	for (size_t i = 0; i < n; ++i)
	{
		ts[i + 1] = lti[i].first;
		te[i + 1] = lti[i].second;
	}
	int start_t = tti.first;
	int end_t = te[n];
	while (start_t >= ts[1] && end_t >= tti.second)
	{
		
		int* tsi = upper_bound(ts + 1, ts + 1 + n, start_t);
		tsi -= 1;
		int i = tsi - ts;
		if (te[i] < end_t) end_t = te[i];
		double xVal = XValueComputeFunc[x](start_t, end_t, tti.first, tti.second);
		switch (xp) {
			case X_PROPERTY::TIME_DECREASING:
				if (xVal >= sigma)
				{
					R.push_back({ ts[i], end_t, start_t, end_t });
					end_t--;
				}
				else 
				{
					start_t--;
				}
				break;
			case X_PROPERTY::TIME_INCREASING:
				if (xVal >= sigma)
				{
					R.push_back({ start_t,end_t,start_t,tti.second });
					start_t--;
				}
				else
				{
					end_t--;
				}
				break;
		}
	}

	delete[] ts;
	delete[] te;

}

/*** Phase 2 Zone Revisit ***/
void ZRev(X_MEANING x, X_PROPERTY xp, T_QUERY tq, int k, double sigma)
{
  //clear the result set
	global_optx = 0.0;
	qinterval_start = -1, qinterval_end = -1;
	R.clear();
	for (ZONE& z : zone_set)
	{
		if (tq == T_QUERY::OPTIMIZING)
		{
			OptLocalSearch(z, x, xp, k);
		}
		else if (tq == T_QUERY::CONSTRAINING)
		{
			ConLocalSearch(z, x, xp, k, sigma);
		}
	}
}

std::map<int, vector<int>> ordered_arc_set;

//Init the ordered arc set (if needed)
void InitOrderArcSet()
{
	for (int i = 0; i < arcn; ++i)
	{
		int eId = i;
		int tVal = arcs[i].t;
		ordered_arc_set[tVal].push_back(eId);
	}
}

//Get edges between an interval
void ArcBetwIntval(int start_time, int end_time, vector<int>& output)
{
	if (start_time > end_time) return;
	auto start_it = ordered_arc_set.lower_bound(start_time);
	auto end_it = ordered_arc_set.upper_bound(end_time);
	if (end_it == ordered_arc_set.begin()) return;
	end_it--;
	while (start_it != ordered_arc_set.end() && start_it->first <= end_it->first)
	{
		for (int eid : start_it->second)
		{
			output.push_back(eid);
		}
		start_it++;
	}
}

/*** accelerated TEL building ***/
void buildtel_fast(int l, int r)
{
	memset(hs, -1, VMAX * sizeof(int));
	memset(hd, -1, VMAX * sizeof(int));
	memset(ht, -1, TMAX * sizeof(int));
	head = -1, tail = -1;
	idx = 0, idt = 0;
	vector<int> ts;
	vector<int> valid_arcs;
	ArcBetwIntval(l, r, valid_arcs);
	for(auto i:valid_arcs)
	{
		addarc(i, arcs[i].src, arcs[i].dst, arcs[i].t);
		ts.push_back(arcs[i].t);
	}

	sort(ts.begin(), ts.end());
	ts.erase(unique(ts.begin(), ts.end()), ts.end());
	for (auto t : ts) addt(t);
}

/*** accelerated TEL building ***/
void initMH_fast(int l, int r)
{
	Mv.clear();
	Mc.clear();
	Hv.clear();
	vector<int> valid_arcs;
	ArcBetwIntval(l, r, valid_arcs);
	for(int i:valid_arcs)
	{
		int src = arcs[i].src;
		int dst = arcs[i].dst;
		int t = arcs[i].t;
		if (cAdd(src, dst))
		{
			vAdd(src);
			vAdd(dst);
		}
	}
}

//Zone Partition of Phase 1, TEL must have been built
void ZPar_O(int ql, int qr, int qk)
{
	zone_set.clear();//all time zones
	unordered_map<int, int> endr; //end_pos for RoU
	int ts = 0, te = 0;      //current cell
	int _ts = ql, _te = qr;	 //first cell in next row
	auto rlc = [&](int __te) {
		if (__te < te)
		{
			cntinfo[INFO::RLC]++;
			te = __te;//PoR
		}
	}; //PoR
	auto sqz = [&](int __ts, int __te) {//Rectangle Pruning
		if (ts < __ts) { //Overline Trigger
			_ts = __ts;  //PoU
		}
	};
	auto tag = [&](int __ts)
	{
		if (ts < __ts) //Overline Triggered
		{
			cntinfo[INFO::TAG]++;
			//cntinfo[INFO::PoU]++;
			for (int r = ts + 1; r <= __ts; ++r)
			{
				if (endr.count(r) == 0)
					endr[r] = -1;
				endr[r] = max(endr[r], te + 1); //Tag for PoU
			}
		}
	};
	auto pou = [&](int ts, int te) { return endr.count(ts) && endr[ts] >= te; };//PoU

	while (_ts <= _te)
	{
		ts = _ts, te = _te;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		sqz(tsarc[head], tsarc[tail]);
		while (ts <= te)
		{
			//collect TTIs of a time zone
			zone_set[{tsarc[head], tsarc[tail]}].push_back({ts, te});
			rlc(tsarc[tail]);
			tag(tsarc[head]);
			if (pou(ts, te)) break;
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		_ts++;
		rst();
	}
}

