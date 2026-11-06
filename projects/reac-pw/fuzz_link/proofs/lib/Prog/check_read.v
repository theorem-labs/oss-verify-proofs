(* check_read (fuzz_link.c:533-552), PLAIN build: the walk of its contract
   (lib/Prog/check_read_c.v) on the plain image.
   0x15210, 116 bytes, 29 instructions: push a 32-byte frame (ra, s0, s1), keep a5/a4 in s0/s1,
   a4 = 1000000 (RC_FAILS); `beq a1, a4` picks same_rc's test (want = RC_FAILS: `seqz a1, a0`;
   else `xor`/`snez`), `bnez a1` to abort (0x15280); `bnez a0` skips both strcmp calls (0x1f274)
   when rc <> 0; each strcmp result goes through `bnez a0` to abort; pop, ret.

   The abort branches are not taken: the contract's two same_rc clauses make the first test 0
   (want = RC_FAILS -> rc <> 0; otherwise rc = want, so rc xor want = 0), and on rc = 0 its last
   clause gives kind = want_kind and alias = want_alias, so strcmp answers 0 both times. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf check_read_c strcmp_c strcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* the three ways the register-level same_rc of the contract can hold *)
Lemma cr_cases : forall (a0 a1 : word),
  (a1 = wz RC_FAILS -> a0 <> wz 0) -> (a1 <> wz RC_FAILS -> a0 = a1) ->
  (bv_unsigned a1 = 1000000 /\ bv_unsigned a0 <> 0) \/
  (bv_unsigned a1 <> 1000000 /\ a0 = a1 /\ bv_unsigned a0 <> 0) \/
  (a0 = wz 0 /\ a1 = wz 0).
Proof.
  intros a0 a1 RF RE.
  destruct (Z.eq_dec (bv_unsigned a1) 1000000) as [W|W].
  - left. split; [exact W|]. intros HZ. apply RF.
    + apply bv_eq. rewrite W. reflexivity.
    + apply bv_eq. rewrite HZ. reflexivity.
  - assert (E : a0 = a1).
    { apply RE. intros H. apply W. rewrite H. reflexivity. }
    destruct (Z.eq_dec (bv_unsigned a0) 0) as [HZ|HZ].
    + right; right. split; apply bv_eq.
      * rewrite HZ. reflexivity.
      * rewrite <- E, HZ. reflexivity.
    + right; left. split; [exact W|]. split; [exact E|exact HZ].
Qed.

(* a branch: split on its test and drop the side the hypotheses refute *)
Ltac cr_br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; zify_cond K; rewrite ?Z.lxor_nilpotent in K; try (exfalso; lia)
  | _ => idtac
  end.

(* the return address a callee answers to is the literal pc after the call *)
Ltac cr_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* ld ra; ld s0; ld s1; addi sp; ret, then the leaf post *)
Ltac cr_epilogue FR ST sp :=
  do 4 zstep;
  release_frame FR ST (bv_unsigned sp);
  zstep;
  finish; first [ exact I | apply regs_preserved_mkR | assumption ].

Section Walk.
Hypothesis SC : strcmp_contract.

Theorem check_read_walk : check_read_contract.
Proof.
  unfold check_read_contract. apply leaf_intro.
  - intros r1 r2 m E (k & k' & a & a' & H). exists k, k', a, a'.
    unfold arg, apart_frame, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ _ H. exact H.
  - unfold leaf_walk, CHECK_READ.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros (sk & sk2 & sa & sa2 & CK & CK2 & CA & CA2 & P2 & P3 & P4 & P5 & RF & RE & EQ) MI ST LO SP.
    change (cstr_at m (bv_unsigned a2) sk) in CK.
    change (cstr_at m (bv_unsigned a3) sk2) in CK2.
    change (cstr_at m (bv_unsigned a4) sa) in CA.
    change (cstr_at m (bv_unsigned a5) sa2) in CA2.
    change (bv_unsigned a2 + (Z.of_nat (length sk) + 1) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2) in P2.
    change (bv_unsigned a3 + (Z.of_nat (length sk2) + 1) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a3) in P3.
    change (bv_unsigned a4 + (Z.of_nat (length sa) + 1) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a4) in P4.
    change (bv_unsigned a5 + (Z.of_nat (length sa2) + 1) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a5) in P5.
    change (a1 = wz RC_FAILS -> a0 <> wz 0) in RF.
    change (a1 <> wz RC_FAILS -> a0 = a1) in RE.
    change (a0 = wz 0 -> sk = sk2 /\ sa = sa2) in EQ.
    unfold writes_nothing, only_frame.
    destruct CK as [BK NK]. destruct CK2 as [BK2 NK2]. destruct CA as [BA NA]. destruct CA2 as [BA2 NA2].
    pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1. pose proof (zr_word sp) as Rsp.
    unfold inr64 in Ra0, Ra1, Rsp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    destruct (cr_cases a0 a1 RF RE) as [(W1 & HZ) | [(W1 & E01 & HZ) | (-> & ->)]]; clear RF RE.
    + (* want = RC_FAILS and rc <> 0: seqz gives 0, `bnez a0` skips the strcmp calls *)
      clear EQ.
      carve_frame 32%nat ST.
      (* addi sp; sd ra; sd s0; sd s1; mv s0, a5; mv s1, a4; lui a4; addiw a4 *)
      do 8 zstep.
      zstep. cr_br.               (* beq a1, a4: taken *)
      zstep.                      (* seqz a1, a0 *)
      zstep. cr_br.               (* bnez a1, abort: not taken *)
      zstep. cr_br.               (* bnez a0: taken, to the epilogue *)
      cr_epilogue FR ST sp.
    + (* want <> RC_FAILS, rc = want <> 0: xor gives 0, `bnez a0` skips the strcmp calls *)
      subst a1. clear EQ.
      carve_frame 32%nat ST.
      do 8 zstep.
      zstep. cr_br.               (* beq a1, a4: not taken *)
      zstep. rewrite ?Z.lxor_nilpotent.   (* xor a1, a0, a1 *)
      zstep. zstep.               (* snez a1, a1; j *)
      zstep. cr_br.               (* bnez a1, abort: not taken *)
      zstep. cr_br.               (* bnez a0: taken, to the epilogue *)
      cr_epilogue FR ST sp.
    + (* rc = want = 0: both strcmp calls run, on equal strings *)
      destruct (EQ eq_refl) as [<- <-]. clear EQ.
      unfold wz in *.
      carve_frame 32%nat ST.
      do 8 zstep.
      zstep. cr_br.               (* beq a1, a4: not taken *)
      zstep. rewrite ?Z.lxor_nilpotent.   (* xor a1, a0, a1 *)
      zstep. zstep.               (* snez a1, a1; j *)
      zstep. cr_br.               (* bnez a1, abort: not taken *)
      zstep. cr_br.               (* bnez a0: not taken *)
      do 3 zstep.                 (* mv a0, a2; mv a1, a3; jal strcmp *)
      eapply evt_cut; [ eapply SC; [ exact BK | exact NK | exact BK2 | exact NK2 ] | ].
      intros ms' (r & x11 & x12 & x13 & -> & HR).
      assert (Hr : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
      cr_ret.
      zstep. cr_br.               (* bnez a0, abort: not taken *)
      do 3 zstep.                 (* mv a0, s1; mv a1, s0; jal strcmp *)
      eapply evt_cut; [ eapply SC; [ exact BA | exact NA | exact BA2 | exact NA2 ] | ].
      intros ms' (r & y11 & y12 & y13 & -> & HR2).
      assert (Hr : r = Z_to_bv 64 0) by (apply HR2; reflexivity). subst r.
      cr_ret.
      zstep. cr_br.               (* bnez a0, abort: not taken *)
      cr_epilogue FR ST sp.
Qed.

End Walk.

Theorem check_read_holds : check_read_contract.
Proof. exact (check_read_walk strcmp_holds). Qed.

About check_read_walk.
Print Assumptions check_read_walk.
Print Assumptions check_read_holds.
