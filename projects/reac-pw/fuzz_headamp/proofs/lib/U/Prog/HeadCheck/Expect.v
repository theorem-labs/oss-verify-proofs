(** expect_of (fuzz_headamp.c:109-157) inlined in the UBSan LLVMFuzzerTestOneInput, 0x14198 -> 0x14784: U/Prog/HeadCheck/
    Cut.v [expect_stmt], from memset_contract, strncmp_contract and [key_stmt] (the pair with the prefix, another
    piece). The head (memset(x), the NULL flag, is_props, params_struct, the constants and the early exits,
    ExpectHead.v [head_holds]) reaches the pair loop's first head, whose walk to the store of x->rc is Pair.v
    [loop_holds]; PairInv.v [loop_stmt] joins them. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import memset_c strncmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut PairInv ExpectHead Pair.

Theorem expect_holds : memset_contract -> strncmp_contract -> key_stmt -> expect_stmt.
Proof. intros MSET STRN KEY. exact (head_holds MSET (loop_holds STRN KEY)). Qed.
