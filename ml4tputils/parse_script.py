import argparse
import json
import os.path as op


from lib.myfile import MyFile


def create_lemma(f_out, hdr, body):
    # print("Header", hdr)
    # print("Body", body)

    # Unpack
    s_hdr = "\n".join(hdr)
    toks = s_hdr.split()
    kind = toks[0].strip()
    name = toks[1].strip()
    stmt = " ".join(toks[2:])
    proof = "\n".join(body)

    # Emit
    msg = json.dumps({"kind": kind,
                      "name": name,
                      "stmt": stmt,
                      "proof": proof})
    f_out.write(msg)
    f_out.write("\n")

    return (kind, name, stmt, proof)


def parse_file(inpath, filename, outpath):
    in_filename = op.join(inpath, filename)
    print("PARSING: {}".format(in_filename))
    f = MyFile(in_filename)

    out_filename = op.join(outpath, filename)
    out = open("{}.parse".format(out_filename), 'w')

    hdr = []
    body = []
    acc = []
    f_hdr = False
    f_let = False
    f_proof = False

    while f.raw_peek_line() != "":
        line = f.consume_line()
        print("Parsing", line)
        if line.startswith("Fact") or \
           line.startswith("Remark") or \
           line.startswith("Proposition") or \
           line.startswith("Corollary") or \
           line.startswith("Lemma") or \
           line.startswith("Theorem"):
            f_hdr = True
            hdr += [line]
        elif line.startswith("Let"):
            if f_let:
                hdr = []
            f_let = True
            f_hdr = True
            hdr += [line]
        elif line.startswith("Proof"):
            f_proof = True
            f_hdr = False
            if line != "Proof.":
                if line.endswith("Qed."):
                    end = len(line) - 6 - 4
                    body += [line[6:end]]
                    acc += [create_lemma(out, hdr, body)]

                    hdr = []
                    body = []
                    f_proof = False
                else:
                    body += [line[6:]]
        elif line.startswith("Qed"):
            if not f_proof:
                out.close()
                raise NameError("Expected to be in proof mode parsing {}".
                                format(line))
            acc += [create_lemma(out, hdr, body)]
            hdr = []
            body = []
            f_proof = False
        else:
            if f_hdr:
                hdr += [line]
            elif f_proof:
                body += [line]

    out.close()


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-p", "--path", default="odd-order/mathcomp/odd_order",
                           type=str, help="Path to files")
    argparser.add_argument("-op", "--outpath", default="data/odd-order",
                           type=str, help="Path to files")
    args = argparser.parse_args()

    files = ["BGsection1.v",
             "BGsection2.v",
             "BGsection3.v",
             "BGsection4.v",
             "BGsection5.v",
             "BGsection6.v",
             "BGsection7.v",
             "BGsection8.v",
             "BGsection9.v",
             "BGsection10.v",
             "BGsection11.v",
             "BGsection12.v",
             "BGsection13.v",
             "BGsection14.v",
             "BGsection15.v",
             "BGsection16.v",
             "BGappendixAB.v",
             "BGappendixC.v",
             "PFsection1.v",
             "PFsection2.v",
             "PFsection3.v",
             "PFsection4.v",
             "PFsection5.v",
             "PFsection6.v",
             "PFsection7.v",
             "PFsection8.v",
             "PFsection9.v",
             "PFsection10.v",
             "PFsection11.v",
             "PFsection12.v",
             "PFsection13.v",
             "PFsection14.v",
             "stripped_odd_order_theorem.v",
             "wielandt_fixpoint.v"]
    
    for file in files:
        parse_file(args.path, file, args.outpath)
