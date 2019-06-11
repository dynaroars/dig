# 1 "bug1.c"
# 1 "<command-line>"
# 1 "bug1.c"
# 11 "bug1.c"
# 1 "/usr/include/stdio.h" 1 3 4
# 28 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/features.h" 1 3 4
# 323 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/predefs.h" 1 3 4
# 324 "/usr/include/features.h" 2 3 4
# 356 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 1 3 4
# 359 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 360 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 2 3 4
# 357 "/usr/include/features.h" 2 3 4
# 388 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 1 3 4



# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 5 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 2 3 4




# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs-64.h" 1 3 4
# 10 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 2 3 4
# 389 "/usr/include/features.h" 2 3 4
# 29 "/usr/include/stdio.h" 2 3 4





# 1 "/home/Storage/Src/Software/usr/bin/../lib/gcc/x86_64-linux-gnu/4.7/include/stddef.h" 1 3 4
# 213 "/home/Storage/Src/Software/usr/bin/../lib/gcc/x86_64-linux-gnu/4.7/include/stddef.h" 3 4
typedef long unsigned int size_t;
# 35 "/usr/include/stdio.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/types.h" 1 3 4
# 28 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 29 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;


typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;

typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;







typedef long int __quad_t;
typedef unsigned long int __u_quad_t;
# 131 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/typesizes.h" 1 3 4
# 132 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;

typedef int __daddr_t;
typedef long int __swblk_t;
typedef int __key_t;


typedef int __clockid_t;


typedef void * __timer_t;


typedef long int __blksize_t;




typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;


typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;


typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;

typedef long int __ssize_t;



typedef __off64_t __loff_t;
typedef __quad_t *__qaddr_t;
typedef char *__caddr_t;


typedef long int __intptr_t;


typedef unsigned int __socklen_t;
# 37 "/usr/include/stdio.h" 2 3 4
# 45 "/usr/include/stdio.h" 3 4
struct _IO_FILE;



typedef struct _IO_FILE FILE;





# 65 "/usr/include/stdio.h" 3 4
typedef struct _IO_FILE __FILE;
# 75 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/libio.h" 1 3 4
# 32 "/usr/include/libio.h" 3 4
# 1 "/usr/include/_G_config.h" 1 3 4
# 15 "/usr/include/_G_config.h" 3 4
# 1 "/home/Storage/Src/Software/usr/bin/../lib/gcc/x86_64-linux-gnu/4.7/include/stddef.h" 1 3 4
# 16 "/usr/include/_G_config.h" 2 3 4




# 1 "/usr/include/wchar.h" 1 3 4
# 83 "/usr/include/wchar.h" 3 4
typedef struct
{
     int __count;
     union
     {

	  unsigned int __wch;



	  char __wchb[4];
     } __value;
} __mbstate_t;
# 21 "/usr/include/_G_config.h" 2 3 4

typedef struct
{
     __off_t __pos;
     __mbstate_t __state;
} _G_fpos_t;
typedef struct
{
     __off64_t __pos;
     __mbstate_t __state;
} _G_fpos64_t;
# 53 "/usr/include/_G_config.h" 3 4
typedef int _G_int16_t __attribute__ ((__mode__ (__HI__)));
typedef int _G_int32_t __attribute__ ((__mode__ (__SI__)));
typedef unsigned int _G_uint16_t __attribute__ ((__mode__ (__HI__)));
typedef unsigned int _G_uint32_t __attribute__ ((__mode__ (__SI__)));
# 33 "/usr/include/libio.h" 2 3 4
# 53 "/usr/include/libio.h" 3 4
# 1 "/home/Storage/Src/Software/usr/bin/../lib/gcc/x86_64-linux-gnu/4.7/include/stdarg.h" 1 3 4
# 40 "/home/Storage/Src/Software/usr/bin/../lib/gcc/x86_64-linux-gnu/4.7/include/stdarg.h" 3 4
typedef __builtin_va_list __gnuc_va_list;
# 54 "/usr/include/libio.h" 2 3 4
# 170 "/usr/include/libio.h" 3 4
struct _IO_jump_t; struct _IO_FILE;
# 180 "/usr/include/libio.h" 3 4
typedef void _IO_lock_t;





struct _IO_marker {
     struct _IO_marker *_next;
     struct _IO_FILE *_sbuf;



     int _pos;
# 203 "/usr/include/libio.h" 3 4
};


enum __codecvt_result
{
     __codecvt_ok,
     __codecvt_partial,
     __codecvt_error,
     __codecvt_noconv
};
# 271 "/usr/include/libio.h" 3 4
struct _IO_FILE {
     int _flags;




     char* _IO_read_ptr;
     char* _IO_read_end;
     char* _IO_read_base;
     char* _IO_write_base;
     char* _IO_write_ptr;
     char* _IO_write_end;
     char* _IO_buf_base;
     char* _IO_buf_end;

     char *_IO_save_base;
     char *_IO_backup_base;
     char *_IO_save_end;

     struct _IO_marker *_markers;

     struct _IO_FILE *_chain;

     int _fileno;



     int _flags2;

     __off_t _old_offset;



     unsigned short _cur_column;
     signed char _vtable_offset;
     char _shortbuf[1];



     _IO_lock_t *_lock;
# 319 "/usr/include/libio.h" 3 4
     __off64_t _offset;
# 328 "/usr/include/libio.h" 3 4
     void *__pad1;
     void *__pad2;
     void *__pad3;
     void *__pad4;
     size_t __pad5;

     int _mode;

     char _unused2[15 * sizeof (int) - 4 * sizeof (void *) - sizeof (size_t)];

};


typedef struct _IO_FILE _IO_FILE;


struct _IO_FILE_plus;

extern struct _IO_FILE_plus _IO_2_1_stdin_;
extern struct _IO_FILE_plus _IO_2_1_stdout_;
extern struct _IO_FILE_plus _IO_2_1_stderr_;
# 364 "/usr/include/libio.h" 3 4
typedef __ssize_t __io_read_fn (void *__cookie, char *__buf, size_t __nbytes);







typedef __ssize_t __io_write_fn (void *__cookie, __const char *__buf,
				 size_t __n);







typedef int __io_seek_fn (void *__cookie, __off64_t *__pos, int __w);


typedef int __io_close_fn (void *__cookie);
# 416 "/usr/include/libio.h" 3 4
extern int __underflow (_IO_FILE *);
extern int __uflow (_IO_FILE *);
extern int __overflow (_IO_FILE *, int);
# 460 "/usr/include/libio.h" 3 4
extern int _IO_getc (_IO_FILE *__fp);
extern int _IO_putc (int __c, _IO_FILE *__fp);
extern int _IO_feof (_IO_FILE *__fp) __attribute__ ((__nothrow__));
extern int _IO_ferror (_IO_FILE *__fp) __attribute__ ((__nothrow__));

extern int _IO_peekc_locked (_IO_FILE *__fp);





extern void _IO_flockfile (_IO_FILE *) __attribute__ ((__nothrow__));
extern void _IO_funlockfile (_IO_FILE *) __attribute__ ((__nothrow__));
extern int _IO_ftrylockfile (_IO_FILE *) __attribute__ ((__nothrow__));
# 490 "/usr/include/libio.h" 3 4
extern int _IO_vfscanf (_IO_FILE * __restrict, const char * __restrict,
			__gnuc_va_list, int *__restrict);
extern int _IO_vfprintf (_IO_FILE *__restrict, const char *__restrict,
			 __gnuc_va_list);
extern __ssize_t _IO_padn (_IO_FILE *, int, __ssize_t);
extern size_t _IO_sgetn (_IO_FILE *, void *, size_t);

extern __off64_t _IO_seekoff (_IO_FILE *, __off64_t, int, int);
extern __off64_t _IO_seekpos (_IO_FILE *, __off64_t, int);

extern void _IO_free_backup_area (_IO_FILE *) __attribute__ ((__nothrow__));
# 76 "/usr/include/stdio.h" 2 3 4




typedef __gnuc_va_list va_list;
# 91 "/usr/include/stdio.h" 3 4
typedef __off_t off_t;
# 103 "/usr/include/stdio.h" 3 4
typedef __ssize_t ssize_t;







typedef _G_fpos_t fpos_t;




# 161 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/stdio_lim.h" 1 3 4
# 162 "/usr/include/stdio.h" 2 3 4



extern struct _IO_FILE *stdin;
extern struct _IO_FILE *stdout;
extern struct _IO_FILE *stderr;







extern int remove (__const char *__filename) __attribute__ ((__nothrow__));

extern int rename (__const char *__old, __const char *__new) __attribute__ ((__nothrow__));




extern int renameat (int __oldfd, __const char *__old, int __newfd,
		     __const char *__new) __attribute__ ((__nothrow__));








extern FILE *tmpfile (void) ;
# 206 "/usr/include/stdio.h" 3 4
extern char *tmpnam (char *__s) __attribute__ ((__nothrow__)) ;





extern char *tmpnam_r (char *__s) __attribute__ ((__nothrow__)) ;
# 224 "/usr/include/stdio.h" 3 4
extern char *tempnam (__const char *__dir, __const char *__pfx)
     __attribute__ ((__nothrow__)) __attribute__ ((__malloc__)) ;








extern int fclose (FILE *__stream);




extern int fflush (FILE *__stream);

# 249 "/usr/include/stdio.h" 3 4
extern int fflush_unlocked (FILE *__stream);
# 263 "/usr/include/stdio.h" 3 4






extern FILE *fopen (__const char *__restrict __filename,
		    __const char *__restrict __modes) ;




extern FILE *freopen (__const char *__restrict __filename,
		      __const char *__restrict __modes,
		      FILE *__restrict __stream) ;
# 292 "/usr/include/stdio.h" 3 4

# 303 "/usr/include/stdio.h" 3 4
extern FILE *fdopen (int __fd, __const char *__modes) __attribute__ ((__nothrow__)) ;
# 316 "/usr/include/stdio.h" 3 4
extern FILE *fmemopen (void *__s, size_t __len, __const char *__modes)
     __attribute__ ((__nothrow__)) ;




extern FILE *open_memstream (char **__bufloc, size_t *__sizeloc) __attribute__ ((__nothrow__)) ;






extern void setbuf (FILE *__restrict __stream, char *__restrict __buf) __attribute__ ((__nothrow__));



extern int setvbuf (FILE *__restrict __stream, char *__restrict __buf,
		    int __modes, size_t __n) __attribute__ ((__nothrow__));





extern void setbuffer (FILE *__restrict __stream, char *__restrict __buf,
		       size_t __size) __attribute__ ((__nothrow__));


extern void setlinebuf (FILE *__stream) __attribute__ ((__nothrow__));








extern int fprintf (FILE *__restrict __stream,
		    __const char *__restrict __format, ...);




extern int printf (__const char *__restrict __format, ...);

extern int sprintf (char *__restrict __s,
		    __const char *__restrict __format, ...) __attribute__ ((__nothrow__));





extern int vfprintf (FILE *__restrict __s, __const char *__restrict __format,
		     __gnuc_va_list __arg);




extern int vprintf (__const char *__restrict __format, __gnuc_va_list __arg);

extern int vsprintf (char *__restrict __s, __const char *__restrict __format,
		     __gnuc_va_list __arg) __attribute__ ((__nothrow__));





extern int snprintf (char *__restrict __s, size_t __maxlen,
		     __const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 4)));

extern int vsnprintf (char *__restrict __s, size_t __maxlen,
		      __const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 0)));

# 414 "/usr/include/stdio.h" 3 4
extern int vdprintf (int __fd, __const char *__restrict __fmt,
		     __gnuc_va_list __arg)
     __attribute__ ((__format__ (__printf__, 2, 0)));
extern int dprintf (int __fd, __const char *__restrict __fmt, ...)
     __attribute__ ((__format__ (__printf__, 2, 3)));








extern int fscanf (FILE *__restrict __stream,
		   __const char *__restrict __format, ...) ;




extern int scanf (__const char *__restrict __format, ...) ;

extern int sscanf (__const char *__restrict __s,
		   __const char *__restrict __format, ...) __attribute__ ((__nothrow__));
# 445 "/usr/include/stdio.h" 3 4
extern int fscanf (FILE *__restrict __stream, __const char *__restrict __format, ...) __asm__ ("" "__isoc99_fscanf")

     ;
extern int scanf (__const char *__restrict __format, ...) __asm__ ("" "__isoc99_scanf")
     ;
extern int sscanf (__const char *__restrict __s, __const char *__restrict __format, ...) __asm__ ("" "__isoc99_sscanf") __attribute__ ((__nothrow__))

     ;
# 465 "/usr/include/stdio.h" 3 4








extern int vfscanf (FILE *__restrict __s, __const char *__restrict __format,
		    __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;





extern int vscanf (__const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;


extern int vsscanf (__const char *__restrict __s,
		    __const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__scanf__, 2, 0)));
# 496 "/usr/include/stdio.h" 3 4
extern int vfscanf (FILE *__restrict __s, __const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vfscanf")



     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (__const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vscanf")

     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (__const char *__restrict __s, __const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vsscanf") __attribute__ ((__nothrow__))



     __attribute__ ((__format__ (__scanf__, 2, 0)));
# 524 "/usr/include/stdio.h" 3 4









extern int fgetc (FILE *__stream);
extern int getc (FILE *__stream);





extern int getchar (void);

# 552 "/usr/include/stdio.h" 3 4
extern int getc_unlocked (FILE *__stream);
extern int getchar_unlocked (void);
# 563 "/usr/include/stdio.h" 3 4
extern int fgetc_unlocked (FILE *__stream);











extern int fputc (int __c, FILE *__stream);
extern int putc (int __c, FILE *__stream);





extern int putchar (int __c);

# 596 "/usr/include/stdio.h" 3 4
extern int fputc_unlocked (int __c, FILE *__stream);







extern int putc_unlocked (int __c, FILE *__stream);
extern int putchar_unlocked (int __c);






extern int getw (FILE *__stream);


extern int putw (int __w, FILE *__stream);








extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     ;






extern char *gets (char *__s) ;

# 658 "/usr/include/stdio.h" 3 4
extern __ssize_t __getdelim (char **__restrict __lineptr,
			     size_t *__restrict __n, int __delimiter,
			     FILE *__restrict __stream) ;
extern __ssize_t getdelim (char **__restrict __lineptr,
			   size_t *__restrict __n, int __delimiter,
			   FILE *__restrict __stream) ;







extern __ssize_t getline (char **__restrict __lineptr,
			  size_t *__restrict __n,
			  FILE *__restrict __stream) ;








extern int fputs (__const char *__restrict __s, FILE *__restrict __stream);





extern int puts (__const char *__s);






extern int ungetc (int __c, FILE *__stream);






extern size_t fread (void *__restrict __ptr, size_t __size,
		     size_t __n, FILE *__restrict __stream) ;




extern size_t fwrite (__const void *__restrict __ptr, size_t __size,
		      size_t __n, FILE *__restrict __s);

# 730 "/usr/include/stdio.h" 3 4
extern size_t fread_unlocked (void *__restrict __ptr, size_t __size,
			      size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite_unlocked (__const void *__restrict __ptr, size_t __size,
			       size_t __n, FILE *__restrict __stream);








extern int fseek (FILE *__stream, long int __off, int __whence);




extern long int ftell (FILE *__stream) ;




extern void rewind (FILE *__stream);

# 766 "/usr/include/stdio.h" 3 4
extern int fseeko (FILE *__stream, __off_t __off, int __whence);




extern __off_t ftello (FILE *__stream) ;
# 785 "/usr/include/stdio.h" 3 4






extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos);




extern int fsetpos (FILE *__stream, __const fpos_t *__pos);
# 808 "/usr/include/stdio.h" 3 4

# 817 "/usr/include/stdio.h" 3 4


extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__));

extern int feof (FILE *__stream) __attribute__ ((__nothrow__)) ;

extern int ferror (FILE *__stream) __attribute__ ((__nothrow__)) ;




extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__)) ;
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__)) ;








extern void perror (__const char *__s);






# 1 "/usr/include/x86_64-linux-gnu/bits/sys_errlist.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/sys_errlist.h" 3 4
extern int sys_nerr;
extern __const char *__const sys_errlist[];
# 847 "/usr/include/stdio.h" 2 3 4




extern int fileno (FILE *__stream) __attribute__ ((__nothrow__)) ;




extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__)) ;
# 866 "/usr/include/stdio.h" 3 4
extern FILE *popen (__const char *__command, __const char *__modes) ;





extern int pclose (FILE *__stream);





extern char *ctermid (char *__s) __attribute__ ((__nothrow__));
# 906 "/usr/include/stdio.h" 3 4
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__));



extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__)) ;


extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__));
# 936 "/usr/include/stdio.h" 3 4

# 12 "bug1.c" 2


int ALIM (int Cur_Vertical_Sep,
	  int High_Confidence,
	  int Two_of_Three_Reports_Valid,
	  int Own_Tracked_Alt,
	  int Own_Tracked_Alt_Rate,
	  int Other_Tracked_Alt,
	  int Alt_Layer_Value,
	  int Up_Separation,
	  int Down_Separation,
	  int Other_RAC,
	  int Other_Capability,
	  int Climb_Inhibit)
{






     if (Alt_Layer_Value == 0) return 400;
     else if (Alt_Layer_Value == 1) return 500;
     else if (Alt_Layer_Value == 2) return 640;
     else return 740;

}

int Inhibit_Biased_Climb (int Cur_Vertical_Sep,
			  int High_Confidence,
			  int Two_of_Three_Reports_Valid,
			  int Own_Tracked_Alt,
			  int Own_Tracked_Alt_Rate,
			  int Other_Tracked_Alt,
			  int Alt_Layer_Value,
			  int Up_Separation,
			  int Down_Separation,
			  int Other_RAC,
			  int Other_Capability,
			  int Climb_Inhibit)
{
     int result =  (Climb_Inhibit ? 
		    100 + Up_Separation
		    : Up_Separation);
     //%%%traces: int result, int Climb_Inhibit, int Up_Separation, int Up_Separation
     return result;
}

int Non_Crossing_Biased_Climb(int Cur_Vertical_Sep,
			      int High_Confidence,
			      int Two_of_Three_Reports_Valid,
			      int Own_Tracked_Alt,
			      int Own_Tracked_Alt_Rate,
			      int Other_Tracked_Alt,
			      int Alt_Layer_Value,
			      int Up_Separation,
			      int Down_Separation,
			      int Other_RAC,
			      int Other_Capability,
			      int Climb_Inhibit)
{
     int upward_preferred;
     int upward_crossing_situation;
     int result;

     upward_preferred = Inhibit_Biased_Climb(Cur_Vertical_Sep,
					     High_Confidence,
					     Two_of_Three_Reports_Valid,
					     Own_Tracked_Alt,
					     Own_Tracked_Alt_Rate,
					     Other_Tracked_Alt,
					     Alt_Layer_Value,
					     Up_Separation,
					     Down_Separation,
					     Other_RAC,
					     Other_Capability,
					     Climb_Inhibit) > Down_Separation;
     if (upward_preferred)
     {
	  result = !(Own_Below_Threat(Cur_Vertical_Sep,
				      High_Confidence,
				      Two_of_Three_Reports_Valid,
				      Own_Tracked_Alt,
				      Own_Tracked_Alt_Rate,
				      Other_Tracked_Alt,
				      Alt_Layer_Value,
				      Up_Separation,
				      Down_Separation,
				      Other_RAC,
				      Other_Capability,
				      Climb_Inhibit)) || ((Own_Below_Threat(Cur_Vertical_Sep,
									    High_Confidence,
									    Two_of_Three_Reports_Valid,
									    Own_Tracked_Alt,
									    Own_Tracked_Alt_Rate,
									    Other_Tracked_Alt,
									    Alt_Layer_Value,
									    Up_Separation,
									    Down_Separation,
									    Other_RAC,
									    Other_Capability,
									    Climb_Inhibit)) && (!(Down_Separation >= ALIM(Cur_Vertical_Sep,
															  High_Confidence,
															  Two_of_Three_Reports_Valid,
															  Own_Tracked_Alt,
															  Own_Tracked_Alt_Rate,
															  Other_Tracked_Alt,
															  Alt_Layer_Value,
															  Up_Separation,
															  Down_Separation,
															  Other_RAC,
															  Other_Capability,
															  Climb_Inhibit))));
     }
     else
     {
	  result = Own_Above_Threat(Cur_Vertical_Sep,
				    High_Confidence,
				    Two_of_Three_Reports_Valid,
				    Own_Tracked_Alt,
				    Own_Tracked_Alt_Rate,
				    Other_Tracked_Alt,
				    Alt_Layer_Value,
				    Up_Separation,
				    Down_Separation,
				    Other_RAC,
				    Other_Capability,
				    Climb_Inhibit) && (Cur_Vertical_Sep >= 300) && (Up_Separation >= ALIM(Cur_Vertical_Sep,
													  High_Confidence,
													  Two_of_Three_Reports_Valid,
													  Own_Tracked_Alt,
													  Own_Tracked_Alt_Rate,
													  Other_Tracked_Alt,
													  Alt_Layer_Value,
													  Up_Separation,
													  Down_Separation,
													  Other_RAC,
													  Other_Capability,
													  Climb_Inhibit));
     }
     return result;
}

int Non_Crossing_Biased_Descend(int Cur_Vertical_Sep,
				int High_Confidence,
				int Two_of_Three_Reports_Valid,
				int Own_Tracked_Alt,
				int Own_Tracked_Alt_Rate,
				int Other_Tracked_Alt,
				int Alt_Layer_Value,
				int Up_Separation,
				int Down_Separation,
				int Other_RAC,
				int Other_Capability,
				int Climb_Inhibit)
{
     int upward_preferred;
     int upward_crossing_situation;
     int result;

     upward_preferred = Inhibit_Biased_Climb(Cur_Vertical_Sep,
					     High_Confidence,
					     Two_of_Three_Reports_Valid,
					     Own_Tracked_Alt,
					     Own_Tracked_Alt_Rate,
					     Other_Tracked_Alt,
					     Alt_Layer_Value,
					     Up_Separation,
					     Down_Separation,
					     Other_RAC,
					     Other_Capability,
					     Climb_Inhibit) > Down_Separation;
     if (upward_preferred)
     {
	  result = Own_Below_Threat(Cur_Vertical_Sep,
				    High_Confidence,
				    Two_of_Three_Reports_Valid,
				    Own_Tracked_Alt,
				    Own_Tracked_Alt_Rate,
				    Other_Tracked_Alt,
				    Alt_Layer_Value,
				    Up_Separation,
				    Down_Separation,
				    Other_RAC,
				    Other_Capability,
				    Climb_Inhibit) && (Cur_Vertical_Sep >= 300) && (Down_Separation >= ALIM(Cur_Vertical_Sep,
													    High_Confidence,
													    Two_of_Three_Reports_Valid,
													    Own_Tracked_Alt,
													    Own_Tracked_Alt_Rate,
													    Other_Tracked_Alt,
													    Alt_Layer_Value,
													    Up_Separation,
													    Down_Separation,
													    Other_RAC,
													    Other_Capability,
													    Climb_Inhibit));
     }
     else
     {
	  result = !(Own_Above_Threat(Cur_Vertical_Sep,
				      High_Confidence,
				      Two_of_Three_Reports_Valid,
				      Own_Tracked_Alt,
				      Own_Tracked_Alt_Rate,
				      Other_Tracked_Alt,
				      Alt_Layer_Value,
				      Up_Separation,
				      Down_Separation,
				      Other_RAC,
				      Other_Capability,
				      Climb_Inhibit)) || ((Own_Above_Threat(Cur_Vertical_Sep,
									    High_Confidence,
									    Two_of_Three_Reports_Valid,
									    Own_Tracked_Alt,
									    Own_Tracked_Alt_Rate,
									    Other_Tracked_Alt,
									    Alt_Layer_Value,
									    Up_Separation,
									    Down_Separation,
									    Other_RAC,
									    Other_Capability,
									    Climb_Inhibit)) && (Up_Separation >= ALIM(Cur_Vertical_Sep,
														      High_Confidence,
														      Two_of_Three_Reports_Valid,
														      Own_Tracked_Alt,
														      Own_Tracked_Alt_Rate,
														      Other_Tracked_Alt,
														      Alt_Layer_Value,
														      Up_Separation,
														      Down_Separation,
														      Other_RAC,
														      Other_Capability,
														      Climb_Inhibit)));
     }
     return result;
}

int Own_Below_Threat(int Cur_Vertical_Sep,
		     int High_Confidence,
		     int Two_of_Three_Reports_Valid,
		     int Own_Tracked_Alt,
		     int Own_Tracked_Alt_Rate,
		     int Other_Tracked_Alt,
		     int Alt_Layer_Value,
		     int Up_Separation,
		     int Down_Separation,
		     int Other_RAC,
		     int Other_Capability,
		     int Climb_Inhibit)
{
     int rs = Own_Tracked_Alt < Other_Tracked_Alt;
     //%%%traces: int rs, int Own_Tracked_Alt, int Other_Tracked_Alt
     return rs;
}

int Own_Above_Threat(int Cur_Vertical_Sep,
		     int High_Confidence,
		     int Two_of_Three_Reports_Valid,
		     int Own_Tracked_Alt,
		     int Own_Tracked_Alt_Rate,
		     int Other_Tracked_Alt,
		     int Alt_Layer_Value,
		     int Up_Separation,
		     int Down_Separation,
		     int Other_RAC,
		     int Other_Capability,
		     int Climb_Inhibit)
{
     int rs = Other_Tracked_Alt < Own_Tracked_Alt;
     //%%%traces: int rs, int Own_Tracked_Alt, int Other_Tracked_Alt
     return rs;
}

int alt_sep_test(int Cur_Vertical_Sep,
		 int High_Confidence,
		 int Two_of_Three_Reports_Valid,
		 int Own_Tracked_Alt,
		 int Own_Tracked_Alt_Rate,
		 int Other_Tracked_Alt,
		 int Alt_Layer_Value,
		 int Up_Separation,
		 int Down_Separation,
		 int Other_RAC,
		 int Other_Capability,
		 int Climb_Inhibit)
{
     int enabled, tcas_equipped, intent_not_known;
     int need_upward_RA, need_downward_RA;
     int alt_sep;

     enabled = High_Confidence && (Own_Tracked_Alt_Rate <= 600) && (Cur_Vertical_Sep > 600);
     tcas_equipped = Other_Capability == 1;
     intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == 0;

     alt_sep = 0;

     if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped))
     {
	  need_upward_RA = Non_Crossing_Biased_Climb(Cur_Vertical_Sep,
						     High_Confidence,
						     Two_of_Three_Reports_Valid,
						     Own_Tracked_Alt,
						     Own_Tracked_Alt_Rate,
						     Other_Tracked_Alt,
						     Alt_Layer_Value,
						     Up_Separation,
						     Down_Separation,
						     Other_RAC,
						     Other_Capability,
						     Climb_Inhibit) &&
	       Own_Below_Threat(Cur_Vertical_Sep,
				High_Confidence,
				Two_of_Three_Reports_Valid,
				Own_Tracked_Alt,
				Own_Tracked_Alt_Rate,
				Other_Tracked_Alt,
				Alt_Layer_Value,
				Up_Separation,
				Down_Separation,
				Other_RAC,
				Other_Capability,
				Climb_Inhibit);
	  need_downward_RA = Non_Crossing_Biased_Descend(Cur_Vertical_Sep,
							 High_Confidence,
							 Two_of_Three_Reports_Valid,
							 Own_Tracked_Alt,
							 Own_Tracked_Alt_Rate,
							 Other_Tracked_Alt,
							 Alt_Layer_Value,
							 Up_Separation,
							 Down_Separation,
							 Other_RAC,
							 Other_Capability,
							 Climb_Inhibit) && Own_Above_Threat(Cur_Vertical_Sep,
											    High_Confidence,
											    Two_of_Three_Reports_Valid,
											    Own_Tracked_Alt,
											    Own_Tracked_Alt_Rate,
											    Other_Tracked_Alt,
											    Alt_Layer_Value,
											    Up_Separation,
											    Down_Separation,
											    Other_RAC,
											    Other_Capability,
											    Climb_Inhibit);
	  if (need_upward_RA && need_downward_RA)
	       alt_sep = 0;
	  else if (need_upward_RA)
	       alt_sep = 1;
	  else if (need_downward_RA)
	       alt_sep = 2;
	  else
	       alt_sep = 0;
     }

     return alt_sep;
}





int mainQ(int Cur_Vertical_Sep, int High_Confidence, int Two_of_Three_Reports_Valid, int Own_Tracked_Alt, int Own_Tracked_Alt_Rate, int Other_Tracked_Alt, int Alt_Layer_Value, int Up_Separation, int Down_Separation, int Other_RAC, int Other_Capability, int Climb_Inhibit){
     return alt_sep_test(Cur_Vertical_Sep,
			 High_Confidence,
			 Two_of_Three_Reports_Valid,
			 Own_Tracked_Alt,
			 Own_Tracked_Alt_Rate,
			 Other_Tracked_Alt,
			 Alt_Layer_Value,
			 Up_Separation,
			 Down_Separation,
			 Other_RAC,
			 Other_Capability,
			 Climb_Inhibit);
}

int main(int argc, char*argv[])
{
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]),atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), atoi(argv[7]), atoi(argv[8]), atoi(argv[9]), atoi(argv[10]), atoi(argv[11]), atoi(argv[12]));
	  
     return 0;
}
