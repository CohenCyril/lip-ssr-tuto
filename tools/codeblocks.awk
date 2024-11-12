BEGIN {
    proofRestarted = 0
    coqCode = 0
    print "(**"
}

{   if ($0 ~ /^```coq[:space:]*/) {
        coqCode = 1
        print "*)"
    } else if ($0 ~ /^```[:space:]*$/) {
        if (coqCode) {
            coqCode = 0
            print "(**"
        } else print $0
    } else if ($0 ~ /^Restart.[:space:]*$/) {
        if (coqCode && !proofRestarted) {
            proofRestarted = 1
            print "(*"
            print "Restart."
        } else print $0
    } else if ($0 ~ /^(Qed|Abort|Defined|Admitted).[:space:]*$/) {
        if (proofRestarted) print "*)"
        proofRestarted = 0
        print $0
    } else {
        print $0
    }
}

END {
    print "*)"
}