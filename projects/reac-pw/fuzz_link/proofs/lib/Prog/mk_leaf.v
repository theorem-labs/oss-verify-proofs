(* reac-pw/fuzz_link, PLAIN build: from a walk over named registers to the `leaf` shape of
   lib/Prog/link_mem.v.

   The released walk tactics (lib/Lib/Step.v `step`) run on a register file written as `mkR` of 31
   words. `leaf` quantifies over any register map, so `leaf_intro` takes a walk stated for
   `mkR ra sp ... t6` and gives the `leaf` contract: the machine runs the same instructions from any
   map that agrees with it register by register (lib/Lib/RegisterBridge.v
   `canonical_contract_transport`), and the contract's Pre, Wr and Post read registers only through
   `getr`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
Local Open Scope Z_scope.

Lemma getr_eqv : forall R R', xregs_eqv R R' -> forall r, getr R r = getr R' r.
Proof.
  intros R R' H r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply H. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r.
  rewrite bv_eqb_refl in E. discriminate.
Qed.

(* the three readings a contract makes of a register map agree for maps that agree on `getr` *)
Definition getr_same (r1 r2 : bvmap 5 word) : Prop := forall r, getr r1 r = getr r2 r.

Definition pre_ext (Pre : bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall r1 r2 m, getr_same r1 r2 -> Pre r1 m -> Pre r2 m.
Definition wr_ext (Wr : bvmap 5 word -> (word -> option byte) -> list ivl) : Prop :=
  forall r1 r2 m, getr_same r1 r2 -> Wr r1 m = Wr r2 m.
Definition post_ext (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop)
  : Prop :=
  forall r1 r2 m q1 q2 m', getr_same r1 r2 -> getr_same q1 q2 -> Post r1 m q1 m' -> Post r2 m q2 m'.

Lemma regs_preserved_same : forall r1 r2 q1 q2,
  getr_same r1 r2 -> getr_same q1 q2 -> regs_preserved r1 q1 -> regs_preserved r2 q2.
Proof.
  intros r1 r2 q1 q2 Hr Hq HP r Hc. specialize (HP r Hc).
  change (getr q2 (Z_to_bv 5 r) = getr r2 (Z_to_bv 5 r)).
  rewrite <- (Hq (Z_to_bv 5 r)), <- (Hr (Z_to_bv 5 r)). exact HP.
Qed.

Definition leaf_walk (pc K : Z)
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list ivl)
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop)
  : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    let regs := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
    Pre regs m ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
    evt rsegs
      (fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         regs_preserved regs regs' /\
         munch ((bv_unsigned sp - K, bv_unsigned sp) :: Wr regs m) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         Post regs m regs' m')
      (MS regs F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma mkR_of_same : forall regs, getr_same regs (mkR_of regs).
Proof. intros regs r. apply getr_eqv, mkR_of_eqv. Qed.

Lemma leaf_intro : forall pc K Pre Wr Post,
  pre_ext Pre -> wr_ext Wr -> post_ext Post ->
  leaf_walk pc K Pre Wr Post -> leaf pc K Pre Wr Post.
Proof.
  intros pc K Pre Wr Post HP HW HQ H. unfold leaf.
  intros regs F fc m lo Hpre MI ST LO SP.
  pose proof (mkR_of_same regs) as E.
  assert (E2 : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  assert (E1 : getr regs 1 = reg_get regs 1) by reflexivity.
  specialize (H (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
                (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
                (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
                (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
                (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
                (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
                (reg_get regs 31) F fc m lo).
  cbv zeta in H. fold (mkR_of regs) in H.
  rewrite E2 in ST, LO, SP.
  specialize (H (HP _ _ _ E Hpre) MI ST LO SP).
  pose proof (canonical_contract_transport rsegs _ (MS regs F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)) H) as T.
  eapply evt_mono; [exact T|].
  intros actual (c & (regs' & m' & Hc & RP & MU & WM & MI' & ST' & PO) & EQ).
  subst c. destruct actual as [Ra Fa pca svca rva fca ma roa].
  destruct EQ as (ER & EF & EP & ES & EV & EC & EM & EO). cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending
    ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst Fa pca svca rva fca ma roa.
  assert (ES' : getr_same regs' Ra) by (intros r; apply getr_eqv, ER).
  assert (ESy : getr_same (mkR_of regs) regs) by (intros r; symmetry; apply E).
  exists Ra, m'. split; [rewrite E1; reflexivity|].
  split; [exact (regs_preserved_same _ _ _ _ ESy ES' RP)|].
  rewrite E2. rewrite (HW _ _ m ESy) in MU.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  exact (HQ _ _ _ _ _ _ ESy ES' PO).
Qed.

(* the reading of each named register out of `mkR` *)
Section Get.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Let R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Lemma mkR_sp : spZ R = bv_unsigned sp. Proof. reflexivity. Qed.
Lemma mkR_ra : getr R 1 = ra. Proof. reflexivity. Qed.
Lemma mkR_tp : getr R 4 = tp. Proof. reflexivity. Qed.
Lemma mkR_a0 : arg R 0 = bv_unsigned a0. Proof. reflexivity. Qed.
Lemma mkR_a1 : arg R 1 = bv_unsigned a1. Proof. reflexivity. Qed.
Lemma mkR_a2 : arg R 2 = bv_unsigned a2. Proof. reflexivity. Qed.
Lemma mkR_a3 : arg R 3 = bv_unsigned a3. Proof. reflexivity. Qed.
Lemma mkR_a4 : arg R 4 = bv_unsigned a4. Proof. reflexivity. Qed.
Lemma mkR_a5 : arg R 5 = bv_unsigned a5. Proof. reflexivity. Qed.
Lemma mkR_a6 : arg R 6 = bv_unsigned a6. Proof. reflexivity. Qed.
Lemma mkR_a7 : arg R 7 = bv_unsigned a7. Proof. reflexivity. Qed.
Lemma mkR_errno : errno_at R = bv_unsigned tp + ERRNO_TP_OFF. Proof. reflexivity. Qed.
End Get.

(* the callee-saved registers of two mkR maps agree when the eleven saved words and sp, gp, tp do *)
Lemma regs_preserved_mkR :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
  regs_preserved
    (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
    (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6').
Proof.
  intros. intros r Hr. unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity..|].
  assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.
