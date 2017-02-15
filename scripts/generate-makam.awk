BEGIN { inmakam = 0;
        outputfile = gensub(/.md$/, ".makam", "g", ARGV[1]);
        print "Generating", outputfile;
        print "(*" > outputfile }

/^```makam$/ { print "*)" >> outputfile; print "" >> outputfile; inmakam = 1 }
/^```$/ { if (inmakam) { inmakam = 0; print "" >> outputfile; print "(*" >> outputfile;} else { print $0 >> outputfile } }
/^>>/ { if (inmakam) { printf "(* %s *)\n", $0 >> outputfile; } }
!(/^```$/ || /^```makam$/ || /^>>/) { print $0 >> outputfile }

END { if (!inmakam) { print "*)" >> outputfile } }
