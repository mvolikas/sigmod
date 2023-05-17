#include <math.h>
#include <stdio.h>
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <queue>
#include <string>
#include <vector>
#include <sstream>
#include <numeric>
#include <iostream>
#include <algorithm>
#include <unordered_set>
#include <unordered_map>

#include <thread>
#include <tbb/tbb.h>
using namespace std;
using namespace tbb;

typedef vector <int> vi;
typedef vector <uint64_t> vl;
typedef pair <int,int> ii;
typedef pair <int,uint64_t> il;
typedef vector <ii> vii;
typedef vector <pair <char,il>> vil;
typedef vector <pair <int,ii>> viii;

#define REL 100
#define COL 100
#define BATCH 100

int rows[REL],cols[REL];
uint64_t* relation[REL][COL];

vi relations[BATCH];
vii aggregates[BATCH];
vector <viii> graph[BATCH];
vector <vil> filters[BATCH];

vi prelations[BATCH];
vector <viii> bindings[BATCH];

void splits(string& s,vector <string> &res,char del) {
  string token;
  stringstream ss(s);
  while (getline(ss,token,del)) res.push_back(token);
	}

void parse(string s,int bid) {
	vector <string> part,rel,prd,sel;
	splits(s,part,'|');
	splits(part[0],rel,' ');
	splits(part[1],prd,'&');
	splits(part[2],sel,' ');
	
	relations[bid].clear();
	aggregates[bid].clear();
	for (int i=0; i<rel.size(); ++i) relations[bid].push_back(stoul(rel[i]));
	graph[bid].assign(rel.size(),viii());
	filters[bid].assign(rel.size(),vil());
	
	for (auto &p : prd) {
			vector <string> pair,rc,tmp;
			char type='=';
			splits(p,pair,'=');
			if (pair.size()==1) { pair.clear(); splits(p,pair,'<'); type='<'; }
			if (pair.size()==1) { pair.clear(); splits(p,pair,'>'); type='>'; }
			splits(pair[0],rc,'.');
			splits(pair[1],tmp,'.');
			int r=stoul(rc[0]),a=stoul(rc[1]);
			
			if (tmp.size()==1) filters[bid][r].push_back({type,{a,stoul(tmp[0])}});
			else {
					int s=stoul(tmp[0]),b=stoul(tmp[1]);
					graph[bid][r].push_back({s,{a,b}}),graph[bid][s].push_back({r,{b,a}});
					}
			}
	for (auto &p : sel) {
			vector <string> rc;
			splits(p,rc,'.');
			aggregates[bid].push_back({stoul(rc[0]),stoul(rc[1])});
			}
	}

int NR=0;

void load_relation(const char *file) {
	int fd;
	void *addr;
	struct stat sb;
	fd=open(file,O_RDONLY);
	fstat(fd,&sb);
	addr=mmap(0,sb.st_size,PROT_READ,MAP_PRIVATE,fd,0);
	uint64_t *a=(uint64_t*)addr;
	rows[NR]=a[0];
	cols[NR]=a[1];
	for (int i=0; i<a[1]; ++i) relation[NR][i]=a+2+a[0]*i;
	NR++;
	}

#define gete(r,c,i) relation[r][c][i]

inline bool valid(int r,int i,vil &f) {
	for (pair <char,il> &c : f) {
			uint64_t v=gete(r,c.second.first,i);
			if (c.first=='=' && v!=c.second.second) return 0;
			else if (c.first=='<' && v>=c.second.second) return 0;
			else if (c.first=='>' && v<=c.second.second) return 0;
			}
	return 1;
	}

int size[BATCH][4];

void search(int i,int bid) {
	bindings[bid].clear();
	prelations[bid].clear();
	unordered_map <int,int> id;
	vi visited(relations[bid].size(),0);
	priority_queue <ii,vector <ii>,greater <ii>> pq;
	
	int k=0;
	visited[i]=1;
	pq.push({0,i});
	while (!pq.empty()) {
			ii u=pq.top(); pq.pop();
			bindings[bid].push_back(viii());
			prelations[bid].push_back(u.second);
			for (auto &v : graph[bid][u.second]) {
					if (!visited[v.first]) {
							visited[v.first]=1;
							pq.push({size[bid][v.first],v.first});
							}
					if (id.count(v.first)) bindings[bid][k].push_back({id[v.first],v.second});
					}
			id[u.second]=k++;
			}
	}

#define THREADS 400
#define RSIZE 100000000
#define HSIZE 10000000000

uint64_t sum[BATCH][THREADS][REL];
int bst[BATCH][THREADS];
int ben[BATCH][THREADS];
bool flag[BATCH][THREADS];
int *buffer[BATCH][THREADS];

int n[BATCH];
vl result[BATCH];
int id[BATCH][REL];
int *real[BATCH][4];
int *hasha[REL][COL];
int *hashe[REL][COL];
int *hasht[REL][COL];

void work(int tid,int bid) {
	int i,j,k,l,ls,r,s,a,b,ri;
	if (bst[bid][tid]>ben[bid][tid]) { flag[bid][tid]=0; return; }
	
	flag[bid][tid]=1;
	for (i=1; i<n[bid]; ++i) {
			s=prelations[bid][i];
			b=bindings[bid][i][0].second.first;
			a=bindings[bid][i][0].second.second;
			r=prelations[bid][bindings[bid][i][0].first];
			int rs=relations[bid][s];
			vil &fs=filters[bid][s];

			int nen=ben[bid][tid];
			for (k=bst[bid][tid]; k<=ben[bid][tid]; ++k) {
					ri=buffer[bid][tid][(k<<2)+bindings[bid][i][0].first];
					uint64_t value=gete(relations[bid][r],a,ri);
					int hid=value%HSIZE;
					
					for (int m=hasht[rs][b][hid]; m; m=hasha[rs][b][m]) {
							int si=hasha[rs][b][m-1];
							if (value!=gete(rs,b,si) || !valid(rs,si,fs)) continue;
							
							bool valid=1;
							for (j=1; j<bindings[bid][i].size(); ++j) {
									int bb=bindings[bid][i][j].second.first;
									int aa=bindings[bid][i][j].second.second;
									int rr=prelations[bid][bindings[bid][i][j].first];
									if (gete(relations[bid][rr],aa,buffer[bid][tid][(k<<2)+bindings[bid][i][j].first])!=gete(rs,bb,si)) {
											valid=0;
											break;
											}
									}
							if (valid) {
									++nen;
									if (i<n[bid]-1) {
											for (l=0; l<i; ++l)	buffer[bid][tid][(nen<<2)+l]=buffer[bid][tid][(k<<2)+l];
											buffer[bid][tid][(nen<<2)+i]=si;
											}
									else {
											buffer[bid][tid][(k<<2)+i]=si;
											int f=0;
											for (ii &agr : aggregates[bid]) {
													sum[bid][tid][f]+=gete(agr.first,agr.second,buffer[bid][tid][(k<<2)+id[bid][f]]);
													++f;
													}
											}
									}
							}
					}
			bst[bid][tid]=ben[bid][tid]+1;
			ben[bid][tid]=nen;
			if (bst[bid][tid]>ben[bid][tid]) { flag[bid][tid]=0; return; }
			}
	}

bool join(int bid) {
	bool ok=0;
	vi ind(n[bid]);
	int i,j,r,tasks=0;
	memset(bst[bid],0,sizeof bst[bid]);
	memset(ben[bid],-1,sizeof ben[bid]);
	memset(sum[bid],0,sizeof sum[bid]);
	r=prelations[bid][0];
	
	int chunk=size[bid][r]/THREADS+1;
	for (i=0; i<n[bid]; ++i) ind[prelations[bid][i]]=i;
	for (i=0; i<aggregates[bid].size(); ++i) {
			id[bid][i]=ind[aggregates[bid][i].first];
			aggregates[bid][i].first=relations[bid][aggregates[bid][i].first];
			}
	
	for (i=0; i<size[bid][r]; ++i) {
			if (i%chunk==0 && i>0) tasks++;
			buffer[bid][tasks][(++ben[bid][tasks])<<2]=real[bid][r][i];
			}

	task_group g;
	for (i=0; i<=tasks; ++i) g.run([=]{work(i,bid);});
	g.wait();

	for (i=0; i<=tasks; ++i) {
			ok|=flag[bid][i];
			for (j=0; j<aggregates[bid].size(); ++j) result[bid][j]+=sum[bid][i][j];
			}

	return ok;
	}

string output[BATCH];

void launch(string s,int bid) {
	int i,j,k;
	parse(s,bid);
	n[bid]=relations[bid].size();

	for (i=0; i<n[bid]; ++i) {
			size[bid][i]=k=0;
			for (j=0; j<rows[relations[bid][i]]; ++j)
					if (valid(relations[bid][i],j,filters[bid][i])) real[bid][i][k++]=j;
			size[bid][i]=k;
			}
	
	vi order(n[bid],0);
	iota(order.begin(),order.end(),0);
	sort(order.begin(),order.end(),[&](int a,int b){return size[bid][a]<size[bid][b];});
	search(order[0],bid);

	for (i=0; i<n[bid]; ++i)
			sort(bindings[bid][i].begin(),bindings[bid][i].end(),[&](pair <int,ii> &a,pair <int,ii> &b){
																									return filters[bid][relations[bid][a.first]].size()>filters[bid][relations[bid][b.first]].size();});

	ostringstream o;	
	result[bid].assign(aggregates[bid].size(),0);
	if (join(bid)==0) {
			o<<"NULL";
			for (j=1; j<result[bid].size(); ++j) o<<" NULL";
			output[bid]=o.str();
			return;
			}

	o<<result[bid][0];
	char buf[200];
	for (i=1; i<result[bid].size(); ++i) o<<" "<<result[bid][i];
	output[bid]=o.str();
	}

void indexw(int r,int c) {
	int nhe=0;
	for (int i=0; i<rows[r]; ++i) {
			int hid=relation[r][c][i]%HSIZE;
			hasha[r][c][nhe]=i;
			hasha[r][c][nhe+1]=hasht[r][c][hid];
			hasht[r][c][hid]=nhe+1;			
			nhe+=2;
			}
	}

int main() {
	string line;
	char buf[100];
	vector <string> lines;
	while (getline(cin,line) && line!="Done")	load_relation(line.c_str());
	
	for (int r=0; r<NR; ++r)
	for (int c=0; c<cols[r]; ++c) {
			hasht[r][c]=(int*)mmap(0,HSIZE*sizeof(int),PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
			hasha[r][c]=(int*)mmap(0,RSIZE*2*sizeof(int),PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
			}

	vector <thread> threads;
	task_group g;
	for (int r=0; r<NR; ++r)
	for (int c=0; c<cols[r]; ++c) g.run([=]{indexw(r,c);});
	g.wait();

	for (int j=0; j<BATCH; ++j) {
			for (int i=0; i<THREADS; ++i) buffer[j][i]=(int*)mmap(0,4000000000,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
			for (int i=0; i<4; ++i) real[j][i]=(int*)mmap(0,100000000,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
			}

	while (getline(cin,line)) {
			if (line!="F") lines.push_back(line);
			else {
					task_group g;
					for (int i=0; i<lines.size(); ++i) g.run([=]{launch(lines[i],i);});
					g.wait();
					for (int i=0; i<lines.size(); ++i) {
							printf("%s\n",output[i].c_str());
							}
					lines.clear();
					}
			}
			
	return 0;
	}

