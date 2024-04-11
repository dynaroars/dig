// //Orig C code
// int mylen(const int k,int arr[], const int arr_siz){
//   int i = 0;
//   for(; i < arr_siz; ++i){
//     if (arr[i] == '\0'){return i;}
//   }

//   return arr_siz - 1 ;
//   //return randrange_i(k, arr_siz - 1, INCLUDE);
// }


// void mk_rand_list(int arr[], const int arr_siz){
//   int i = 0 ;
//   for (;i< arr_siz; ++i){arr[i] = ' ';}


//   int null_idx = randrange_i(0, arr_siz -1, INCLUDE);
//   arr[null_idx]='\0';
// }

// 	assert (1 <= siz);
// 	assert (0 <= n);
// 	assert (n <= siz-1);
	
// 	int src[siz];
// 	int dst[siz];
// 	mk_rand_list(src, siz);
// 	mk_rand_list(dst, siz);
  
// 	int i = 0;
// 	while(i < n && src[i] != '\0'){
// 	    dst[i] = src[i];
// 	    i = i + 1;
// 	}
// 	while(i < n){
// 	    dst[i] = '\0';
// 	    i = i + 1;
// 	}

// 	int ls = mylen(n,src,siz);
// 	int ld = mylen(n,dst,siz);

// 	printf("l_post: n s d\n");
// 	printf("l_post: %d %d %d\n", n, ls, ld);

// 	//inv
// 	assert(!(n <= ls) || ld >= n);
// 	assert(!(n > ls) || ld == ls);

// 	/*
// 	  DIG:
// 	  11: lambda d,n,s: d >= min(n,s)  ***
// 	  12: lambda d,n,s: s >= min(d,n)  ***
// 	*/
	
    


// /* package whatever; // don't place package name! */
// /*
// import java.util.*;
// import java.lang.*;
// import java.io.*;

// /* Name of the class has to be "Main" only if the class is public. */
// class Ideone
// {
// 	static int getchar(int str, int idx, int siz) {
// 		assert 0 <= idx && idx < siz && 0 <= str & str <= siz;
// 		return idx == str ? 0 : ' ';
// 	}
// 	static int setchar(int str, int idx, int siz, int c) {
// 		assert 0 <= idx && idx < siz && 0 <= str & str <= siz;
// 		if (c == 0) {
// 			if (idx < str) return idx;
// 		} else if(str == idx) {
// 			return siz;
// 		}
// 		return str; // no change
// 	}
// 	static void strncopy(int n, int siz, int srcsiz, int destsiz){
// 		assert (1 <= siz);
// 		assert (0 <= n);
// 		assert (n <= siz-1);
		
// 		int src = srcsiz;
// 		int dst = destsiz;
		
// 		int i = 0;
// 		while(i < n && getchar(src, i, siz) != 0 /*src[i] != '\0'*/){
// 		    //dst[i] = src[i];
// 		    dst = setchar(dst, i, siz, getchar(src, i, siz));
// 		    i = i + 1;
// 		}
// 		while(i < n){
// 		    //dst[i] = '\0';
// 		    dst = setchar(dst, i, siz, 0);
// 		    i = i + 1;
// 		}
		
// 		int ls = mylen(n,src,siz);
// 		int ld = mylen(n,dst,siz);
// 		System.out.printf("l_post: n s d\n");
// 		System.out.printf("l_post: %d %d %d\n", n, ls, ld);
// 		//inv
// 		assert(!(n <= ls) || ld >= n);
// 		assert(!(n > ls) || ld == ls);
// 	}
// 	static int mylen(int k, int str, int siz){
// 		assert 0 <= str & str <= siz;
// 		if (str == siz) {
// 			return siz-1;
// 		}
// 		return str;
// 	}
	
	
// 	public static void main (String[] args) throws java.lang.Exception
// 	{
// 		strncopy(4, 10, 7, 1);
// 	}
// }
// */
