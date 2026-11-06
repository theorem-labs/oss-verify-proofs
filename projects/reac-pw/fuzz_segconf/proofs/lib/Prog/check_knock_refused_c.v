From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_knock_refused (fuzz_segconf.c:502-514; at 0x149b0 in the image 3776ca44d75c; frame 16 bytes).
    was_knock (a1, `beqz a1`) and strstr(got, "takes no plan") = NULL aborts (the needle at seg_spec.STR_TNP in
    .rodata; `jal strstr` with sp lowered by the 16-byte frame).

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. With gs the reader's refusal text and k the model's kept_knock, the premise is check_kept's second conjunct:
    negb k || strstr_found gs TNP = true. strstr's own needs (its 2256 bytes of stack below the check's sp - 16,
    the haystack's slack, the stack-protector GOT cell and guard, all apart from the stack) are premises whatever
    k is.

    Callee contracts its walk takes as premises: strstr_contract (Prog/strstr_c.v, STRSTR = 0x1f0c4; Spec/StrStr.strstr_val: found iff
    SegModel.strstr_found, Spec/SegBridge.v).

    Call site (LLVMFuzzerTestOneInput): 0x13be4 `jal check_knock_refused` with a0 = c->refusal[i], a1 = m->kept_knock[i] (`lw`, 0 or 1). *)
Definition CHECK_KNOCK_REFUSED : Z := 0x149b0.
Definition CHECK_KNOCK_REFUSED_STACK : Z := 2272.

Definition check_knock_refused_pre (m : word -> option byte) (sp lo got kn : Z) (gs : list Z) (k : bool) : Prop :=
  got <> 0 /\ cstr_at rsegs m got gs /\ apart got (Z.of_nat (length gs) + 1) lo sp /\
  kn = b2z k /\ (negb k || strstr_found gs TNP) = true /\
  bytes_at rsegs m (sa_got_guard SEG_PLAIN) (le8 (Z_to_bv 64 (sa_guard SEG_PLAIN))) /\
  (exists g, bytes_at rsegs m (sa_guard SEG_PLAIN) (le8 g)) /\
  sa_guard SEG_PLAIN + 8 <= lo /\ sa_got_guard SEG_PLAIN + 8 <= lo /\
  stack_ok rsegs m lo sp CHECK_KNOCK_REFUSED_STACK /\ mem_inv rsegs m.

Definition check_knock_refused_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (gs : list Z) (k : bool),
    check_knock_refused_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) gs k ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned sp - CHECK_KNOCK_REFUSED_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_KNOCK_REFUSED) fc None m (seg_rom rsegs)).
