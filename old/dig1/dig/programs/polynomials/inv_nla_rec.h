/*
NLA testsuite in recursive format
*/
int sqrt1rec_helper(const int a, const int t, const int s, const int n){
  printf("li0: a n t s\n");
  printf("li0: %d %d %d %d\n",a,n,t,s);
  assert(t==2*a+1);
  assert(4*s==t*t+2*t+1);
  assert(s == (a+1)*(a+1));
  assert(s >= t);

  if (!(s<=n)) 
    return a;
  else
    return sqrt1rec_helper(a+1,t+2,s+t+2,n);
}


int sqrt1rec(const int n){
  return sqrt1rec_helper(0,1,1,n);
}


