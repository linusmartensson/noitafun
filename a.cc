
#include<cstring>
#include <codecvt>

#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <set>
#include <unordered_set>
#include <sstream>
#include <vector>
#include <atomic>
#include<random>

using namespace std;
//#define CHECK

int mv = 1;
int modval(){
    return mv;
}

void getdigits(){
    for(int i=0;i < 140;++i){
        wcout<<(i/10)%10;
    }
    wcout<<endl;
    for(int i=0;i < 140;++i){
        wcout<<(i%10);
    }
    wcout<<endl;
}

void permutations(wstring &s, vector<wstring> &ps, int start=0){
    if(start == s.size()) ps.push_back(s);
    else for(int i=start;i < s.size();++i){
        swap(s[start], s[i]);
        permutations(s, ps, start+1);
        swap(s[start], s[i]);
    }

}

template<typename T, typename T2>
T alphabetize(T c, T2 al){
    return al[c%al.size()];
}
template<typename T>
T alphabetize(T c, T al, int ofs = 0){
    wstring o;

    for(auto e : c){
        o.push_back(al[((int)e+ofs)%al.size()]);
    }

    return o;
}

struct C{
    int offset;
    int value;
    constexpr C(int o , int v) : offset(o), value(v) {}
    constexpr C() : offset(0), value(0) {}
};
struct EQD {
    C a;
    C b;
    constexpr EQD(C a, C b) : a(a), b(b) {}
};

int R = 0;
int decrypt(int c, int k, int i){
    return (c - k + modval()) % modval();
}

int constrain(const vector<EQD> &eqds, vector<C> &open_key, vector<C> &fixed_key, C c, int keylen, map<int, int> &observations){
    //Find any constraint edges affected by new constraint c
	//
	int coupling = 0;
    for(auto &e : eqds){
        C o;
        C l;
        bool match = false;
        if(e.a.offset%keylen == c.offset){
            match = true;
            o = e.b;
            l = e.a;
        } else if(e.b.offset%keylen == c.offset) {
            match = true;
            o = e.a;
            l = e.b;
        }
        if(!match) continue;
#ifdef CHECK
        wcout<<"Found constraint: "<<c.offset<<" mod "<<keylen<<" => "<<o.offset<<endl;
#endif
        //Matching constraint found
        //Determine required value
        
        //int new_value = ((o.value - l.value) + c.value + modval()*1000)%modval();
        int new_value = -1;
        for(int i=0;i < modval() ; ++i){
            if(decrypt(l.value, c.value, l.offset) - decrypt(o.value, i, o.offset) == 0) {
                new_value = i;
                break;
            }
        }

        //Verify constraint legality against any previously fixed states
        for(auto &e : fixed_key){
            if(e.offset == o.offset%keylen){
                if(new_value != e.value) {
                    //broken constraint, impossible condition requested
#ifdef CHECK
                    wcout<<"Can't resolve!"<<endl;
                    wcout<<e.offset%keylen<<", "<<e.offset<<", "<<l.offset<<", "<<c.offset<<", "<<o.offset<<endl;
                    wcout<<e.value<<", "<<c.value<<", "<<l.value<<", "<<new_value<<endl;
                    wcout<<o.value-l.value<<endl;
                    wcout<<o.value-l.value+c.value<<endl;
                    wcout<<"error: "<<new_value-e.value<<endl;
#endif
                    return -1;
                } else {
					coupling++;
					observations[e.offset]++;
				}
            }
        }
#ifdef CHECK
        wcout<<"Constraint seems legal."<<endl;
#endif


        //Constrain any previously unconstrained key value
        for( auto f = open_key.begin(); f != open_key.end();f++ ){
            if(o.offset%keylen == f->offset){

                //Our character fixation constrained this value
                C t = *f;
                //So remove it from uconstrained key components
                open_key.erase(f);

                //Determine its new value
                t.value = new_value;

                //Constrain it
                fixed_key.push_back(t);

#ifdef CHECK
                wcout<<"Bound open key "<<t.offset<<" to value "<<new_value<<endl;
#endif
                //Resolve new constraints from this criteria
				observations[t.offset]++;
                int cs = constrain(eqds, open_key, fixed_key, t, keylen, observations);
                if(cs<0) return -1; else coupling = std::max(coupling, cs)+1;
                break;
            }
        }
    }
    return coupling;
}

bool slv(const vector<EQD> &eqds, vector<C> &open_key, vector<C> &fixed_key, int keylen, map<int,int> &observations){

    int independents = 0;
    while(open_key.size()){

        //Get the first unconstrained character
        C c = open_key.back();
        open_key.pop_back();
#ifdef CHECK
        wcout<<"Added "<<c.offset<<", "<<c.value<<" as unbounded constraint"<<endl;
#endif
        //Constrain it to any value
        c.value = 1;
        fixed_key.push_back(c);

        //Resolve the constraint graph
		//
		int coupling = constrain(eqds, open_key, fixed_key, c, keylen, observations);
        if(coupling < 0){
#ifdef CHECK
            wcout<<"Resolution failed"<<endl;
#endif
            return false;
        } else {
#ifdef CHECK
            wcout<<"Constraint "<<c.offset<<", "<<c.value<<" was resolved."<<endl;
#endif
        }

		if(coupling == 0){
			fixed_key.back().value = -1;
		} else if(coupling > 0) {

        	independents++;
		}
		
    }
#ifdef CHECK
    for(auto c : fixed_key){
        wcout<<c.offset<<": "<<c.value<<" \t";
    }
    wcout<<endl;
#endif
    return true;
}

int main(int argc, char **argv) {
    setlocale(LC_ALL, "en_US.UTF-8");

    wstring s = L"";

    wifstream cfs("./constraints");
    vector<EQD> constraints;
    while(getline(cfs,s)){
        if(s[0]=='-') continue;
        wistringstream iss(s);
        vector<C> ls;
        int i;
        wchar_t w;
        while(iss>>i>>noskipws>>w>>w>>skipws){
            ls.push_back(C(i,(int)w));
        }
        for(int a=0;a < ls.size();++a){
            for(int b=a+1;b < ls.size(); ++b){
                constraints.emplace_back(ls[a],ls[b]);
            }
        }
    }

    int nc = constraints.size();
    auto *pp = constraints.data();
    wcout<<constraints.size()<<" constraints loaded"<<endl;

    wifstream ifs("./input");

    vector<wstring> lines;

    wcout<<"Encoded data: "<<endl;
    while (getline(ifs, s)) {
        //wcout << s << endl;

        int a = 0;
        wistringstream iss(s);
        wstring q;
        while (iss >> a) {
            q.push_back(a);
        }
        if (q.size() > 0) {
            lines.push_back(q);
            getdigits();
            for(auto &i : q) i+=32;
            wcout<<q<<endl;
            for(auto &i : q) i-=32;
            wcout<<endl;
        }

    }
    wstring falphabet = L"abcdefghijklmnopqrstuvwxyz??????";

    for(int k=83;k > 82;--k){ 
        mv = k;
		int i=137;
        {
            vector<C> open_key;
            vector<C> fixed_key;
			map<int,int> obs;
            for(int j=0;j < i;++j) open_key.emplace_back(j, 0);
            if(!slv(constraints, open_key, fixed_key, i, obs)){
                continue;
            }
            /*wcout<<"mv="<<mv;
            wcout<<" \tkl="<<i;*/
			wcout<<" \tR="<<R;

            vector<int> data;
            data.resize(i, 0);
            for(int j=0;j < i; ++j){
                for(auto e : fixed_key){
                    if(e.offset==j) data[j] = e.value;
                }
            }



            for(int ofs=0;ofs < 1;++ofs){
                map<int, int> hist;
                getdigits();
                wcout<<"repeating key:"<<endl;
				for(int c=0; c < 137;++c){
					if(obs[c]<10)
						wcout<<(obs[c]);
					else
						wcout<<'+';
				}
				wcout<<endl;
				for(int c = 0; c < 137;++c){
					if(data[c%i] >= 0)
						wcout<<(wchar_t)(32 + data[c%i]);
						//wcout<<(wchar_t)alphabetize(((data[c%i]+ofs)%modval()),falphabet);
					else 
						wcout<<" ";
				}
				wcout<<endl;

                wcout<<"decoded outputs:"<<endl;
                int ccc = 0;
                for(auto e : lines){
                    int p=0;

                    for(auto c : e){
                        //int d = alphabetize(decrypt(c, data[p%i]+ofs, p)%modval(), falphabet);
						int d = 32 + decrypt(c, data[p%i]+ofs, p);
						if(data[p%i] >= 0){
                        	wcout<<(wchar_t)d;
                        	hist[d]++;
						}else
							wcout<<" ";
                        ++p;
                    }
                    wcout<<endl;
                    ccc++;
                }
                float avg = 0;
                float var = 0;
                /*for(auto e : hist){
                    wcout<<(wchar_t)e.first<<": "<<e.second<<" ";
                    for(int i=0;i < e.second;++i) wcout<<"#";
                    wcout<<endl;
                    avg += e.second;
                }
                avg /= modval();
                for(auto e : hist){
                    var += (e.second-avg)*(e.second-avg)/(modval()-1);
                }
                wcout<<"var: "<<var<<"; avg: "<<avg<<endl;*/
            }
        }
    }
}
