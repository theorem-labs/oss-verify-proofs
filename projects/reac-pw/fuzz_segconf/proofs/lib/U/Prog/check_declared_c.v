From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_declared (fuzz_segconf.c:375-388, 556-577; at 0x14e0c in the UBSan image 1696d6c34ffd; frame 96 bytes).
    vlans_are(got, want, tab, n, mt, mn, cap) = 0 aborts: got <> want or n <> mn (full registers); for i < n,
    tab[i].vid (`lhu` tab + 18 i + 16) <> mt[i].vid (`lw` mt + 20 i + 16) or strcmp(tab[i].parent, mt[i].parent)
    <> 0; then the 18 bytes of tab[cap] (tab + 18 cap) each 0x5a.
    UBSan: every check traps to the function's own `unimp`; the alignment, bounds and no-wrap facts of the premise
    (pointers 16- or 4-aligned, n <= 32, the objects inside the address space) make each trap branch fall through.

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. With (gv, gt) the reader's answer and table and (wv, wt) the model's, the premise is the spine's vlans_are
    (gv, gt) (wv, wt) cap = true (whose last conjunct, length gt <= cap, is the model of the guard) and the guard
    entry itself in memory (seg_spec.guard_at).

    Callee contracts its walk takes as premises: strcmp_contract (Prog/strcmp_c.v under lib/U, 0x1f594).

    Call site (LLVMFuzzerTestOneInput): 0x141e8 `jal check_declared` with a0 = got (reac_segconf_declared's result), a1 = want (m_declared's,
    inline), a2 = tab (calloc(cap + 1, 18)), a3 = n, a4 = mt (calloc(cap + 1, 20)), a5 = mn, a6 = cap = u8 % 40;
    tab[cap] was set to 0x5a x 18 (memset) and reac_segconf_declared writes only entries below cap. *)
Definition CHECK_DECLARED : Z := 0x14e0c.
Definition CHECK_DECLARED_STACK : Z := 96.

Definition check_declared_pre (m : word -> option byte) (sp lo got want tab n mt mn cap : Z)
    (gv wv : Z) (gt wt : list (list Z * Z)) : Prop :=
  got = gv mod 2 ^ 64 /\ want = wv mod 2 ^ 64 /\ - 2 ^ 31 <= gv < 2 ^ 31 /\ - 2 ^ 31 <= wv < 2 ^ 31 /\
  0 <= cap < 40 /\
  tab <> 0 /\ tab mod 16 = 0 /\ rtab_at rsegs m tab gt /\ guard_at rsegs m tab cap /\
  apart tab (RVLAN_SIZE * (cap + 1)) lo sp /\ n = Z.of_nat (length gt) /\
  mt <> 0 /\ mt mod 16 = 0 /\ mtab_at rsegs m mt wt /\ apart mt (MVLAN_SIZE * (cap + 1)) lo sp /\
  Z.of_nat (length wt) <= cap /\ mn = Z.of_nat (length wt) /\
  vlans_are (gv, gt) (wv, wt) cap = true /\
  stack_ok rsegs m lo sp CHECK_DECLARED_STACK /\ mem_inv rsegs m.

Definition check_declared_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo gv wv : Z) (gt wt : list (list Z * Z)),
    check_declared_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3)
      (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) gv wv gt wt ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned sp - CHECK_DECLARED_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_DECLARED) fc None m (seg_rom rsegs)).
