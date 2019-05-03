import vcommon as CM
import os
import os.path
import time


# def vcmd(cmd, inp=None, shell=True):
#     proc = sp.Popen(cmd, shell=shell, stdin=sp.PIPE,
#                     stdout=sp.PIPE, stderr=sp.PIPE)
#     return proc.communicate(input=inp)


def run(dir_, ntimes):
    print ("**** Benchmark dir '{}' {} times".format(dir_, ntimes))

    fs = sorted(f for f in os.listdir(dir_) if f.endswith(".java"))
    fs = [os.path.join(dir_, f) for f in fs]

    for f in fs:
        if not os.path.isfile(f):
            print "File {} does not exist".format(f)
            continue

        run_cmd = "sage -python -O dig.py {} -log 2 -octmaxv 20 -seed {}"
        for i in range(ntimes):
            print "##### Running {} with seed {}, {}".format(
                f, i, time.strftime("%c"))
            cmd = run_cmd.format(f, i)
            print cmd
            stdout, stderr = CM.vcmd(cmd)
            print stdout
            print stderr


ntimes = 1

# NLA
dir_nla = "../tests/nla/"
run(dir_nla, ntimes)


# dirComplexity = "programs/complexity/gulwani_cav09"
# run(dirComplexity, ntimes)

# dirComplexity = "programs/complexity/gulwani_pldi09"
# run(dirComplexity, ntimes)

# dirComplexity = "programs/complexity/gulwani_popl09"
# run(dirComplexity, ntimes)


#dirHola = "programs/hola/"
#run(dirHola, ntimes)

#dirBm_oopsla = "programs/PIE/bm_oopsla/"
#run(dirBm_oopsla, ntimes)

#dirBm_ice = "programs/PIE/bm_ice/"
#run(dirBm_ice, ntimes)
