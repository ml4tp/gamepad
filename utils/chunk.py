if __name__=="__main__":
    filename = "/Users/dehuang/Documents/research/pnh/mathcomp-odd-order-1.6.1/mathcomp/odd_order/build.log.bak"
    with open(filename, 'r') as f:
        out = None
        while True:
            line = f.readline()
            if line == "":
                print("EOF")
                break
            elif line.startswith("COQDEP"):
                print("COQDEP")
                continue
            elif line.startswith("COQC"):
                # close open file if open
                if out:
                    out.close()

                # open file for writing
                toks = line.split(" ")
                v_file = toks[1].strip()
                print("COQC", v_file)
                out = open("./data/{}.dump".format(v_file), 'w')
            else:
                out.write(line)


