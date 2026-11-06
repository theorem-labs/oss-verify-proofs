From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcFrag RcFragLib
  RcParseLib memcpy_c bcmp_c reac_ctrl_identity_fragment_c.
Import ListNotations.
Open Scope Z_scope.

Lemma fq_le1_zxb : forall b : byte, le1 (zxb b) = [b].
Proof. exact le1_zxb. Qed.

Ltac mem_after_store_opt ::=
  try rewrite fq_le1_zxb;
  try rewrite rf_le1_0;
  try rewrite rf_le1_1;
  try fix_lit_store;
  try rewrite rf_le1_0;
  try rewrite rf_le1_1;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Lemma fq_beq : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma fq_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma fq_rw_bytes : forall m A cs bs, rw_cells rsegs m A cs -> cells_bytes cs = bs -> bytes_at rsegs m A bs.
Proof. intros m A cs bs [[_ H] _] E. subst. exact H. Qed.

Lemma fq_app4 : forall m A B C D a b c d,
  bytes_at rsegs m A a -> bytes_at rsegs m B b -> bytes_at rsegs m C c -> bytes_at rsegs m D d ->
  B = A + Z.of_nat (length a) -> C = B + Z.of_nat (length b) -> D = C + Z.of_nat (length c) ->
  bytes_at rsegs m A (a ++ b ++ c ++ d).
Proof.
  intros m A B C D a b c d HA HB HC HD -> -> ->.
  apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact HA|].
  apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact HB|].
  apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact HC | exact HD].
Qed.

Lemma fq_mcmp : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  exists v, memcmp_model l r n = Some v /\ -255 <= v <= 255 /\
    (v = 0 <-> forall i, (i < n)%nat -> bv_unsigned (nth i l (Z_to_bv 8 0)) = bv_unsigned (nth i r (Z_to_bv 8 0))).
Proof.
  induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; [lia|]. split; [intros _ i Hi; lia | reflexivity].
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [memcmp_model]. pose proof (byte_range a) as Ra. pose proof (byte_range b) as Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r ltac:(cbn in Hl; lia) ltac:(cbn in Hr; lia)) as (v & Hv & Rv & Iv).
      exists v. split; [exact Hv|]. split; [exact Rv|]. rewrite Iv. split.
      * intros Hall i Hi. destruct i as [|i]; [exact E|]. cbn [nth]. apply Hall. lia.
      * intros Hall i Hi. apply (Hall (S i)). lia.
    + exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      split; [intros; lia|]. intros Hall. specialize (Hall 0%nat ltac:(lia)). cbn [nth] in Hall. lia.
Qed.

(* The block-sum loop 0x14b10 .. 0x14b1c: a1 sums, a2 walks to a3. *)
Lemma loopB : forall (Q : machine_state -> Prop)
  (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 e r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
  (Ff : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (bs : list byte) (c : nat),
  bytes_at rsegs m A bs -> (c <= length bs)%nat -> 0 < A -> A + Z.of_nat c <= 2^64 ->
  e = Z_to_bv 64 (A + Z.of_nat c) ->
  (forall x14, evt rsegs Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 (Z_to_bv 64 (psum bs c)) (Z_to_bv 64 (A + Z.of_nat c)) e x14
              r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x14b20) fc None m (seg_rom rsegs))) ->
  forall n i p s x14, (i + n = c)%nat -> (0 < n)%nat -> p = A + Z.of_nat i -> s = psum bs i ->
  evt rsegs Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 (Z_to_bv 64 s) (Z_to_bv 64 p) e x14
              r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x14b10) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 e r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    Ff fc m A bs c HB Hl HA HAc He HK.
  subst e.
  induction n as [|n IH]; intros i p s x14 Hin Hn Hp Hs; [lia|]. subst p s.
  pose proof (rd_byte rsegs m A bs i HB ltac:(lia)) as RD.
  pose proof (psum_range bs i) as PR.
  do 4 step.
  rewrite psum_S_zxb.
  rewrite (eqb_le64 (A + Z.of_nat i + 1) (A + Z.of_nat c)) by lia.
  destruct n as [|n].
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat c) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. replace (A + Z.of_nat i + 1) with (A + Z.of_nat c) by lia.
    replace (S i) with c by lia. apply HK.
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat c) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. apply (IH (S i)); lia.
Qed.

(* The record-sum loop 0x14c58 .. 0x14c64: a0 sums, a1 walks to a2. *)
Lemma loopR : forall (Q : machine_state -> Prop)
  (r1 r2 r3 r4 r5 r6 r7 r8 r9 e r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
  (Ff : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (bs : list byte) (c : nat),
  bytes_at rsegs m A bs -> (c <= length bs)%nat -> 0 < A -> A + Z.of_nat c <= 2^64 ->
  e = Z_to_bv 64 (A + Z.of_nat c) ->
  (forall x13, evt rsegs Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 (Z_to_bv 64 (psum bs c)) (Z_to_bv 64 (A + Z.of_nat c)) e x13
              r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x14c68) fc None m (seg_rom rsegs))) ->
  forall n i p s x13, (i + n = c)%nat -> (0 < n)%nat -> p = A + Z.of_nat i -> s = psum bs i ->
  evt rsegs Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 (Z_to_bv 64 s) (Z_to_bv 64 p) e x13
              r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x14c58) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 r2 r3 r4 r5 r6 r7 r8 r9 e r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    Ff fc m A bs c HB Hl HA HAc He HK.
  subst e.
  induction n as [|n IH]; intros i p s x13 Hin Hn Hp Hs; [lia|]. subst p s.
  pose proof (rd_byte rsegs m A bs i HB ltac:(lia)) as RD.
  pose proof (psum_range bs i) as PR.
  do 4 step.
  rewrite psum_S_zxb.
  rewrite (eqb_le64 (A + Z.of_nat i + 1) (A + Z.of_nat c)) by lia.
  destruct n as [|n].
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat c) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. replace (A + Z.of_nat i + 1) with (A + Z.of_nat c) by lia.
    replace (S i) with c by lia. apply HK.
  - replace (A + Z.of_nat i + 1 =? A + Z.of_nat c) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. apply (IH (S i)); lia.
Qed.

Lemma fq_store_ok : forall m a n (j : nat), wr_at rsegs m a n -> Z.of_nat j <= n -> store_ok rsegs m (wa a) j = true.
Proof.
  intros m a n j H Hj. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  apply (wr_at_store_ok rsegs m a n 0 j H); lia.
Qed.

Lemma fq_rw_of : forall m A bs, bytes_at rsegs m A bs -> wr_at rsegs m A (Z.of_nat (length bs)) ->
  rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma fq_clear_app : forall P X : list byte, (7 <= length P)%nat -> fg_clear (P ++ X) = fg_clear P ++ X.
Proof.
  intros P X HP. unfold fg_clear. rewrite firstn_app, skipn_app.
  replace (6 - length P)%nat with 0%nat by lia. replace (7 - length P)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma fq_clear_join : forall st g, length st = 72%nat -> 1 <= fg_n g -> fg_T st g <= 64 ->
  fg_clear (fg_join st g) =
  firstn 6 st ++ [Z_to_bv 8 0] ++ bsl st 7 (1 + fg_lf st) ++ fg_body g ++ skipn (Z.to_nat (8 + fg_T st g)) st.
Proof.
  intros st g HL Hn HT.
  pose proof (byte_range (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as R.
  change (bv_unsigned (nth (Z.to_nat 7) st (Z_to_bv 8 0))) with (fg_lf st) in R.
  unfold fg_join. rewrite fq_clear_app by (rewrite length_firstn; unfold fg_T in HT; lia).
  unfold fg_clear. rewrite firstn_firstn, skipn_firstn_comm.
  replace (Nat.min 6 (Z.to_nat (8 + fg_lf st))) with 6%nat by lia.
  unfold bsl. replace (Z.to_nat (8 + fg_lf st) - 7)%nat with (Z.to_nat (1 + fg_lf st)) by lia.
  change (Z.to_nat 7) with 7%nat. rewrite !app_assoc. reflexivity.
Qed.

Section P.
Hypothesis MEMC : memcpy_contract.
Hypothesis BCMP : bcmp_contract.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Ff : bvmap 5 word) (fc : bv 32)
  (mE : word -> option byte) (f fr len pa pp pn S : Z) (st g : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rfr : 0 <= fr < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis Rpa : 0 <= pa < 2^64.
Hypothesis Rpp : 0 <= pp < 2^64.
Hypothesis Rpn : 0 <= pn < 2^64.
Hypothesis RS : 80 <= S < 2^64.
Hypothesis Hg : length g = 50%nat.
Hypothesis Hst : length st = 72%nat.

Local Notation CL := (fg_class f fr pa pp pn len st g).
Local Notation FRc j := [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Qf : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret CL))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             Ff (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (fg_fp 80 f pa pp pn S CL) mE m' /\ wmono rsegs mE m' /\ mem_inv rsegs m' /\
    stk rsegs m' (S - 80) S /\ fg_mem f pa pp pn st g CL m'.

Definition NZ : Prop := f <> 0 /\ fr <> 0 /\ pa <> 0 /\ pp <> 0 /\ pn <> 0.
Definition DJA : Prop := (f + 72 <= fr \/ fr + 50 <= f) /\ (f + 72 <= S - 80 \/ S <= f) /\ (fr + 50 <= S - 80 \/ S <= fr).
Definition DJB : Prop :=
  (f + 72 <= pa \/ pa + 2 <= f) /\ (f + 72 <= pp \/ pp + 8 <= f) /\ (f + 72 <= pn \/ pn + 8 <= f) /\
  (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
  (pa + 2 <= S - 80 \/ S <= pa) /\ (pp + 8 <= S - 80 \/ S <= pp) /\ (pn + 8 <= S - 80 \/ S <= pn).
Definition OUT : Prop :=
  wr_at rsegs mE pa 2 /\ wr_at rsegs mE pp 8 /\ wr_at rsegs mE pn 8 /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0.

Lemma dj_of : all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50); (S - 80, S)] ->
  DJA /\ DJB.
Proof.
  intros H. cbn [all_dj dj_from] in H.
  destruct H as ((Dfa & Dfp & Dfn & Dff & DfS & _) & (Dap & Dan & Daf & DaS & _) & (Dpn & Dpf & DpS & _) &
                 (Dnf & DnS & _) & (DrS & _) & _).
  split; [exact (conj Dff (conj DfS DrS))|].
  exact (conj Dfa (conj Dfp (conj Dfn (conj Dap (conj Dan (conj Dpn (conj DaS (conj DpS DnS)))))))).
Qed.

Lemma cl_nn : NZ -> CL =
  if negb (fg_fr len g) then FgNone
  else if bat g 19 =? 1 then FgFirst
  else if negb (fg_keep st g) then FgDrop
  else if negb (fg_close st g) then FgJoin
  else FgClose.
Proof. intros (H1 & H2 & H3 & H4 & H5). apply rf_class_nn; assumption. Qed.

Lemma L_epi : forall c j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                         x28 x29 x30 x31 : word) m,
  c = CL -> x10 = Z_to_bv 64 (fg_ret c) ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch (fg_fp 80 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14b2c) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 m
    Hc Hx FR MU WM MI FM.
  subst c x10.
  assert (ST0 : stk rsegs m (S - 80) (S + -80)) by (split; [lia|]; split; [lia|]; intros a Ha; exfalso; lia).
  pose proof (stk_release rsegs m _ _ _ ST0 FR ltac:(lia)) as ST.
  cbn [cells_size csize Nat.add] in ST. replace (S + -80 + Z.of_nat 80) with S in ST by lia. clear ST0.
  do 11 step.
  try replace (S + -80 + 80) with S by lia.
  apply evt_done. unfold Qf.
  do 14 eexists. exists m. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST | exact FM].
Qed.

Lemma L_ret0 : forall c j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                          x28 x29 x30 x31 : word) m,
  c = CL -> fg_ret c = 0 ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch (fg_fp 80 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14b28) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 m
    Hc Hr FR MU WM MI FM.
  step.
  eapply L_epi; [exact Hc | | exact FR | exact MU | exact WM | exact MI | exact FM].
  rewrite Hr. reflexivity.
Qed.

Lemma L_none : forall j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                        x28 x29 x30 x31 : word) m,
  NZ -> fg_fr len g = false ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(S - 80, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14b28) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 m
    NZh HF FR MU WM MI.
  eapply (L_ret0 FgNone); [ | reflexivity | exact FR | exact MU | exact WM | exact MI | exact I].
  rewrite (cl_nn NZh), HF. reflexivity.
Qed.

Lemma L_drop : forall j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                        x28 x29 x30 x31 : word) m,
  CL = FgDrop -> (f + 72 <= S - 80 \/ S <= f) ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(f, f + 72); (S - 80, S)] mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> rw_cells rsegs m f [CB 72 st] ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 (Z_to_bv 64 f) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14bbc) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 m
    Hc DfS FR MU WM MI HS.
  step. step. step.
  eapply (L_epi FgDrop); [symmetry; exact Hc | reflexivity | exact FR | exact MU | exact WM | exact MI | ].
  cbn [fg_mem]. eapply fq_rw_bytes; [exact HS|].
  cbn [cells_bytes cbytes]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma L_first : forall j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x28 x29 x30 x31 : word) m,
  CL = FgFirst -> 1 <= fg_n g <= 22 -> DJA ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(S - 80, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 (Z_to_bv 64 f) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             (Z_to_bv 64 fr) (zxb (nth 26 g (Z_to_bv 8 0))) (Z_to_bv 64 1) x23 s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14b60) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x28 x29 x30 x31 m
    Hc Hn (Dff & DfS & DrS) FR MU WM MI HS HG.
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (rw_cells_bound rsegs m f _ HS) as BF. cbn [cells_size csize Nat.add] in BF.
  destruct (rf_rw_parts rsegs m f 72 st HS) as (HSb & HSw & _). clear HS.
  rewrite <- Hst in HSw.
  pose proof (rf_rw_sub rsegs m f st 0 6 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P0.
  pose proof (rf_rw_sub rsegs m f st 6 2 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P6.
  pose proof (rf_rw_sub rsegs m f st 8 (fg_n g) HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P8.
  pose proof (rf_bytes_skip rsegs m f st (8 + fg_n g) HSb ltac:(rewrite Hst; lia)) as PR.
  clear HSb HSw.
  rewrite Z.add_0_r in P0. change (Z.to_nat 6) with 6%nat in P0. change (Z.to_nat 2) with 2%nat in P6.
  pose proof (rf_bytes_bsl rsegs m fr g 6 6 HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GS.
  pose proof (rf_bytes_bsl rsegs m fr g 27 (fg_n g) HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GB.
  assert (LGB : length (bsl g 27 (fg_n g)) = Z.to_nat (fg_n g)) by (apply rf_bsl_length; rewrite ?Hg; lia).
  clear HG.
  apply (munch_weaken [(S - 80, S)] [(f, f + 72); (S - 80, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  step. step. step. step.
  assert (U0 : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  call MEMC.
  { rewrite U1. exact GS. }
  { rewrite U2. apply rf_bsl_length; rewrite ?Hg; lia. }
  { rewrite U0, U2. exact P0. }
  { rewrite U0, U1, U2. lia. }
  { exact MI. }
  match goal with H : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 f)) _ |- _ =>
    rewrite U0, U2 in H; change (Z.to_nat 6) with 6%nat in H; rename H into Q0 end.
  match goal with H : bytes_at rsegs ?mm (bv_unsigned (Z_to_bv 64 (fr + 6))) _ |- _ => clear H end.
  step. step. step. step.
  assert (U3 : bv_unsigned (Z_to_bv 64 (f + 8)) = f + 8) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  assert (U5 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  call MEMC.
  { rewrite U4. exact GB. }
  { rewrite U5. apply rf_bsl_length; rewrite ?Hg; lia. }
  { rewrite U3, U5. exact P8. }
  { rewrite U3, U4, U5. lia. }
  { assumption. }
  match goal with H : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (f + 8))) _ |- _ =>
    rewrite U3, U5 in H; rename H into Q8 end.
  match goal with H : bytes_at rsegs ?mm (bv_unsigned (Z_to_bv 64 (fr + 27))) _ |- _ => clear H end.
  step. step. step. step.
  eapply (L_epi FgFirst); [symmetry; exact Hc | reflexivity | exact FR | exact MU | assumption | assumption | ].
  cbn [fg_mem]. unfold fg_first.
  pose proof (proj1 (rf_rw_parts rsegs _ f 6 _ Q0)) as B0.
  pose proof (proj1 (rf_rw_parts rsegs _ (f + 8) _ _ Q8)) as B8.
  pose proof (fq_rw_bytes _ _ _ [Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)] P6 ltac:(cbn [cells_bytes cbytes]; reflexivity))
    as B6.
  apply (fq_app4 _ f (f + 6) (f + 8) (f + (8 + fg_n g)) _ _ _ _ B0 B6 B8 PR).
  - rewrite rf_bsl_length by (rewrite ?Hg; lia). lia.
  - cbn [length]. lia.
  - unfold fg_body. rewrite rf_bsl_length by (rewrite ?Hg; lia). lia.
Qed.

Local Notation JN := (fg_join st g).

Lemma fr_iff : fg_fr len g = true <->
  50 <= len /\ bat g 16 = 205 /\ bat g 17 = 234 /\ bat g 18 = 4 /\ (bat g 19 = 1 \/ bat g 19 = 2) /\
  bat g 22 = 0 /\ bat g 23 = 2 /\ bat g 24 = 0 /\ bat g 25 = 254 /\ 1 <= fg_n g /\ fg_n g <= 22 /\
  blocksum (skipn 18 g) = 0.
Proof. unfold fg_fr. rewrite !andb_true_iff, !orb_true_iff, !Z.eqb_eq, !Z.leb_le. tauto. Qed.

Lemma close_iff : fg_close st g = true <->
  14 <= fg_T st g /\ bat JN 8 = 240 /\ bat JN 9 = 65 /\ bat JN 11 = 0 /\ bat JN 12 = 0 /\ bat JN 13 = 18 /\
  bat JN 14 = 18 /\ bat JN 15 = 5 /\ bat JN 16 = 0 /\ bat JN (7 + fg_T st g) = 247 /\
  recsum (bsl JN 15 (fg_T st g - 8)) = 0.
Proof. unfold fg_close. rewrite !andb_true_iff, !Z.eqb_eq, !Z.leb_le. tauto. Qed.

Lemma keep_iff : fg_keep st g = true <-> fg_hf st <> 0 /\ fg_src_eq st g = true /\ fg_T st g <= 64.
Proof. unfold fg_keep. rewrite !andb_true_iff, negb_true_iff, Z.eqb_neq, Z.leb_le. tauto. Qed.

Lemma cl_k : NZ -> fg_fr len g = true -> bat g 19 <> 1 ->
  CL = if negb (fg_keep st g) then FgDrop else if fg_close st g then FgClose else FgJoin.
Proof.
  intros NZh FRT B19. rewrite (cl_nn NZh), FRT, (proj2 (Z.eqb_neq _ _) B19). cbn [negb].
  destruct (fg_keep st g), (fg_close st g); reflexivity.
Qed.

Ltac fz := rewrite ?length_le8, ?length_le2; cbn [cells_size csize Nat.add length inside]; lia.

(* lia case-splits every disjunction in context; [hide] keeps one out until [fzu] needs it. *)
Definition hide (P : Prop) : Prop := P.
Lemma hide_i : forall P : Prop, P -> hide P. Proof. intros P H. exact H. Qed.
Ltac fzu D := let H := fresh "DU" in pose proof D as H; unfold hide in H; fz.

(* 0x14c70 .. 0x14c98: store the three outputs, return 1. *)
Lemma L_close : forall j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x28 x29 x30 x31 : word) m,
  CL = FgClose -> 14 <= fg_T st g <= 64 -> length JN = 72%nat -> DJB ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(f, f + 72); (S - 80, S)] mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> bytes_at rsegs m f (fg_clear JN) -> OUT ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pa) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pn) (Z_to_bv 64 pp) x20 x21 (Z_to_bv 64 (fg_T st g)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14c70) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x28 x29 x30 x31 m
    Hc HT LJ DJBh FR MU WM MI CJ (WA & WP & WN & Ma & Mp & Mn).
  destruct DJBh as (Dfa & Dfp & Dfn & Dap & Dan & Dpn & DaS & DpS & DnS).
  apply hide_i in Dfa. apply hide_i in Dfp. apply hide_i in Dfn. apply hide_i in Dap. apply hide_i in Dan.
  apply hide_i in Dpn. apply hide_i in DaS. apply hide_i in DpS. apply hide_i in DnS.
  apply (wr_at_transport rsegs mE m) in WA; [|exact WM].
  apply (wr_at_transport rsegs mE m) in WP; [|exact WM].
  apply (wr_at_transport rsegs mE m) in WN; [|exact WM].
  pose proof WA as (BA0 & BA1 & _). pose proof WP as (BP0 & BP1 & _). pose proof WN as (BN0 & BN1 & _).
  pose proof (rf_clear_length _ LJ) as LCJ.
  pose proof (bytes_at_bound rsegs m f _ CJ) as BF. rewrite LCJ in BF.
  pose proof (rf_rd1 rsegs m f _ 17 CJ ltac:(lia) ltac:(rewrite LCJ; lia)) as R17.
  change (Z.to_nat 17) with 17%nat in R17. rewrite (rf_clear_nth _ 17 _ LJ ltac:(lia)) in R17.
  apply (munch_weaken [(f, f + 72); (S - 80, S)]
           [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 80, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  step. clear R17.
  pose proof (rf_rd1 rsegs _ f _ 18 CJ ltac:(lia) ltac:(rewrite LCJ; lia)) as R18.
  change (Z.to_nat 18) with 18%nat in R18. rewrite (rf_clear_nth _ 18 _ LJ ltac:(lia)) in R18.
  step. clear R18. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (fq_store_ok mm pp 8 8 WP ltac:(lia)) as SP end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (fq_store_ok mm pn 8 8 (wr_at_write rsegs _ pn 8 _ _ WN) ltac:(lia)) as SN end.
  step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (fq_store_ok mm pa 2 2 (wr_at_write rsegs _ pa 2 _ _ (wr_at_write rsegs _ pa 2 _ _ WA)) ltac:(lia))
      as SA end.
  step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem (write_to_mem _ _ ?b1) _ ?b2) _ ?b3) _) =>
    assert (E3 : b3 = le2 (Z_to_bv 64 (fg_addr st g)))
  end.
  { rewrite rc_le2_pack. unfold fg_addr, bat. change (Z.to_nat 17) with 17%nat. change (Z.to_nat 18) with 18%nat.
    rewrite Z.mul_comm. symmetry. apply rc_le2_pair. }
  rewrite E3.
  eapply (L_epi FgClose); [symmetry; exact Hc | reflexivity | | | | | ].
  - apply rw_cells_frame;
      [apply rw_cells_frame; [apply rw_cells_frame; [exact FR | fz | fz | fzu DpS] | fz | fz | fzu DnS]
      | fz | fz | fzu DaS].
  - change (fg_fp 80 f pa pp pn S FgClose) with [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 80, S)].
    apply munch_write; [apply munch_write; [apply munch_write; [exact MU | fz | fz | fz] | fz | fz | fz]
                       | fz | fz | fz].
  - apply wmono_write, wmono_write, wmono_write, WM.
  - apply mem_inv_store; [apply mem_inv_store; [apply mem_inv_store; [exact MI | rewrite length_le8; exact SP]
                                                | rewrite length_le8; exact SN]
                         | rewrite length_le2; exact SA].
  - cbn [fg_mem]. split; [|split; [|split]].
    + apply bytes_at_write_other;
        [apply bytes_at_write_other; [apply bytes_at_write_other; [exact CJ | fz | fz | fzu Dfp] | fz | fz | fzu Dfn]
        | fz | fz | fzu Dfa].
    + apply bytes_at_write_same; fz.
    + apply bytes_at_write_other;
        [apply bytes_at_write_other; [apply bytes_at_write_same; fz | fz | fz | fzu Dpn] | fz | fz | fzu Dap].
    + apply bytes_at_write_other; [apply bytes_at_write_same; fz | fz | fz | fzu Dan].
Qed.

Ltac jfail := eapply (L_ret0 FgJoin);
  [ symmetry; match goal with H : CL = _ |- _ => rewrite H end;
    let EC := fresh "EC" in destruct (fg_close st g) eqn:EC; [exfalso; apply close_iff in EC; lia | reflexivity]
  | reflexivity | eassumption | match goal with H : munch _ mE _ |- _ => exact H end | eassumption | eassumption
  | match goal with H : bytes_at _ _ f (fg_clear _) |- _ => exact H end ].

Ltac jld i :=
  let R := fresh "RDJ" in
  match goal with CJ : bytes_at _ _ f (fg_clear _), LJ : length (fg_join st g) = _ |- _ =>
    pose proof (rd_byte rsegs _ f _ i CJ ltac:(rewrite rf_clear_length by exact LJ; lia)) as R;
    rewrite (rf_clear_nth _ i _ LJ ltac:(lia)) in R
  end;
  step; clear R.

Ltac jbyte i z c :=
  rewrite (rf_beq (nth i (fg_join st g) (Z_to_bv 8 0)) c) by lia;
  change (bv_unsigned (nth i (fg_join st g) (Z_to_bv 8 0))) with (bat (fg_join st g) z);
  let B := fresh "B" in destruct (Z.eqb_spec (bat (fg_join st g) z) c) as [B|B]; cbn [negb]; cbv iota; [|jfail].

(* 0x14be4 .. 0x14c6c: the close checks on the joined record, the record-sum loop. *)
Lemma L_tail : forall j (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) m,
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJB ->
  (f + 72 <= S - 80 \/ S <= f) -> 0 < f ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(f, f + 72); (S - 80, S)] mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> bytes_at rsegs m f (fg_clear JN) -> OUT ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pa) (Z_to_bv 64 14) x11 x12 x13 x14
             x15 x16 x17 (Z_to_bv 64 pn) (Z_to_bv 64 pp) x20 x21 (Z_to_bv 64 (fg_T st g)) (Z_to_bv 64 (f + 8))
             s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14be4) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 m
    HCL Hn HT DJBh DfS Hf0 FR MU WM MI CJ OUTh.
  pose proof (rf_fg_join_length st g Hst Hg Hn HT) as LJ.
  pose proof (rf_clear_length _ LJ) as LCJ.
  pose proof (bytes_at_bound rsegs m f _ CJ) as BF. rewrite LCJ in BF.
  assert (T0 : 0 <= fg_T st g).
  { unfold fg_T, fg_lf, bat. pose proof (byte_range (nth (Z.to_nat 7) st (Z_to_bv 8 0))). lia. }
  step.
  rewrite (fq_ltu (fg_T st g) 14) by lia.
  destruct (Z.ltb_spec (fg_T st g) 14) as [T14|T14]; cbv iota; [jfail|].
  jld 8%nat. step. step. jbyte 8%nat 8 240.
  jld 9%nat. step. step. jbyte 9%nat 9 65.
  jld 11%nat. step. jbyte 11%nat 11 0.
  jld 12%nat. step. jbyte 12%nat 12 0.
  jld 13%nat. step. step. jbyte 13%nat 13 18.
  jld 14%nat. step. jbyte 14%nat 14 18.
  jld 15%nat. step. step. jbyte 15%nat 15 5.
  jld 16%nat. step. jbyte 16%nat 16 0.
  step.
  pose proof (rd_byte rsegs _ f _ (Z.to_nat (7 + fg_T st g)) CJ ltac:(rewrite LCJ; lia)) as RDJ.
  rewrite (rf_clear_nth _ (Z.to_nat (7 + fg_T st g)) _ LJ ltac:(lia)) in RDJ.
  step. clear RDJ. step. step.
  rewrite (rf_beq (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)) 247) by lia.
  change (bv_unsigned (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)))
    with (bat (fg_join st g) (7 + fg_T st g)).
  destruct (Z.eqb_spec (bat (fg_join st g) (7 + fg_T st g)) 247) as [B7T|B7T]; cbn [negb]; cbv iota; [|jfail].
  step. step. step. step.
  pose proof (rf_bytes_skip rsegs _ f _ 15 CJ ltac:(rewrite LCJ; lia)) as HBr.
  change (Z.to_nat 15) with 15%nat in HBr. rewrite (rf_clear_skipn _ 15 LJ ltac:(lia)) in HBr.
  eapply (loopR Qf) with (A := f + 15) (bs := skipn 15 (fg_join st g)) (c := Z.to_nat (fg_T st g - 8))
                         (n := Z.to_nat (fg_T st g - 8)) (i := 0%nat);
    [ exact HBr | rewrite length_skipn, LJ; lia | lia | lia | first [f_equal; lia | word_eq_tac] | | lia | lia | lia
    | reflexivity ].
  intros x13'.
  pose proof (psum_range (skipn 15 (fg_join st g)) (Z.to_nat (fg_T st g - 8))) as PR.
  step. step.
  rewrite rf_land127 by lia.
  pose proof (rf_recsum_bsl (fg_join st g) 15 (fg_T st g - 8) ltac:(lia) ltac:(lia) ltac:(rewrite LJ; lia)) as ER.
  change (Z.to_nat 15) with 15%nat in ER. rewrite <- ER.
  destruct (Z.eqb_spec (recsum (bsl (fg_join st g) 15 (fg_T st g - 8))) 0) as [RS0|RS0]; cbn [negb]; cbv iota;
    [|jfail].
  assert (EC : fg_close st g = true) by (apply close_iff; repeat split; first [assumption | lia]).
  eapply L_close; [ rewrite HCL, EC; reflexivity | lia | exact LJ | exact DJBh | exact FR | exact MU
                  | exact WM | exact MI | exact CJ | exact OUTh ].
Qed.

(* 0x14bc8 .. 0x14be0: append the body at f+8+lf, clear byte 6. *)
Lemma L_join : forall j (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) m,
  x22 = Z_to_bv 64 (fg_T st g) ->
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJA -> DJB -> OUT ->
  0 < f ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(f, f + 72); (S - 80, S)] mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> bytes_at rsegs m f st -> wr_at rsegs m f (Z.of_nat (length st)) -> bytes_at rsegs m fr g ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pa) (zxb (nth 7 st (Z_to_bv 8 0)))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr)
             (zxb (nth 26 g (Z_to_bv 8 0))) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14bc8) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 m
    E22 HCL Hn HT (Dff & DfS & _) DJBh OUTh Hf0 FR MU WM MI HSb HSw HG.
  subst x22.
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (bytes_at_bound rsegs m f st HSb) as BF. rewrite Hst in BF.
  pose proof (byte_range (nth 7 st (Z_to_bv 8 0))) as R7.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st) in R7.
  assert (TT : fg_T st g = fg_lf st + fg_n g) by reflexivity.
  pose proof (rf_rw_sub rsegs m f st 6 1 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P6.
  pose proof (rf_rw_sub rsegs m f st (8 + fg_lf st) (fg_n g) HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia))
    as P8.
  pose proof (rf_bytes_first rsegs m f st 6 HSb) as B0.
  pose proof (rf_bytes_bsl rsegs m f st 7 (1 + fg_lf st) HSb ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as B7.
  pose proof (rf_bytes_skip rsegs m f st (8 + fg_T st g) HSb ltac:(rewrite Hst; lia)) as BR.
  pose proof (rf_bytes_bsl rsegs m fr g 27 (fg_n g) HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GB.
  assert (LGB : length (bsl g 27 (fg_n g)) = Z.to_nat (fg_n g)) by (apply rf_bsl_length; rewrite ?Hg; lia).
  assert (LB7 : length (bsl st 7 (1 + fg_lf st)) = Z.to_nat (1 + fg_lf st))
    by (apply rf_bsl_length; rewrite ?Hst; lia).
  assert (LB0 : length (firstn 6 st) = 6%nat) by (rewrite length_firstn; lia).
  assert (LBR : length (skipn (Z.to_nat (8 + fg_T st g)) st) = (72 - Z.to_nat (8 + fg_T st g))%nat)
    by (rewrite length_skipn; lia).
  clear HSb HSw HG.
  change (Z.to_nat 1) with 1%nat in P6.
  step. step. step. step. step.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  match goal with |- context [Z_to_bv 64 ?e] =>
    lazymatch e with context [fg_lf st] =>
      assert (U0 : bv_unsigned (Z_to_bv 64 e) = f + (8 + fg_lf st)) by (rewrite unsigned_lit by lia; lia) end end.
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  call MEMC.
  { rewrite U1. exact GB. }
  { rewrite U2. exact LGB. }
  { rewrite U0, U2. exact P8. }
  { rewrite U0, U1, U2. lia. }
  { assumption. }
  match goal with H : rw_cells rsegs ?mm (bv_unsigned _) [CB _ (bsl g 27 (fg_n g))] |- _ =>
    rewrite U0, U2 in H; rename H into Q8 end.
  match goal with H : bytes_at rsegs ?mm (bv_unsigned (Z_to_bv 64 (fr + 27))) _ |- _ => clear H end.
  step. step.
  pose proof (fq_rw_bytes _ _ _ [Z_to_bv 8 0] P6 ltac:(cbn [cells_bytes cbytes]; reflexivity)) as B6.
  pose proof (fq_rw_bytes _ _ _ (bsl g 27 (fg_n g)) Q8 ltac:(cbn [cells_bytes cbytes]; apply app_nil_r)) as BB.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (CJ : bytes_at rsegs mm f (fg_clear JN)) end.
  { rewrite fq_clear_join by (first [exact Hst | lia]).
    apply (rf_app _ _ f _ (f + 6)); [exact B0 | | rewrite LB0; lia].
    apply (rf_app _ _ (f + 6) _ (f + 7)); [exact B6 | | cbn [length]; lia].
    apply (rf_app _ _ (f + 7) _ (f + (8 + fg_lf st))); [exact B7 | | rewrite LB7; lia].
    apply (rf_app _ _ (f + (8 + fg_lf st)) _ (f + (8 + fg_T st g)));
      [exact BB | exact BR | unfold fg_body; rewrite LGB; lia]. }
  eapply L_tail; [ exact HCL | exact Hn | exact HT | exact DJBh | exact DfS | exact Hf0 | eassumption | eassumption
                 | eassumption | eassumption | exact CJ | exact OUTh ].
Qed.

(* 0x14b90 .. 0x14bc4: g[19] = 2; keep or drop the partial record. *)
Lemma L_second : forall j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) m,
  NZ -> fg_fr len g = true -> bat g 19 <> 1 -> DJA -> DJB -> OUT ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(S - 80, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pa) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (zxb (nth 26 g (Z_to_bv 8 0))) x22 x23 s8 s9 s10 s11
             x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14b90) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 m
    NZh FRT B19 DJAh DJBh OUTh FR MU WM MI HS HG.
  pose proof DJAh as (_ & DfS & _).
  assert (Hf0 : 0 < f) by (destruct NZh as (Nf & _); lia).
  pose proof (proj1 fr_iff FRT) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hn1 & Hn2 & _).
  pose proof (cl_k NZh FRT B19) as HCL0. clear B19.
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (rw_cells_bound rsegs m f _ HS) as BF. cbn [cells_size csize Nat.add] in BF.
  destruct (rf_rw_parts rsegs m f 72 st HS) as (HSb & HSw & _). clear HS.
  apply (munch_weaken [(S - 80, S)] [(f, f + 72); (S - 80, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  pose proof (byte_range (nth 7 st (Z_to_bv 8 0))) as RL.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st) in RL.
  pose proof (byte_range (nth 26 g (Z_to_bv 8 0))) as RN.
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g) in RN.
  pose proof (rd_byte rsegs m f st 6 HSb ltac:(lia)) as R6.
  step. step. clear R6.
  rewrite (rf_beq (nth 6 st (Z_to_bv 8 0)) 0) by lia.
  change (bv_unsigned (nth 6 st (Z_to_bv 8 0))) with (fg_hf st).
  destruct (Z.eqb_spec (fg_hf st) 0) as [H6|H6]; cbv iota.
  { eapply L_drop; [ | exact DfS | exact FR | exact MU | exact WM | exact MI | ].
    - rewrite HCL0. destruct (fg_keep st g) eqn:EK; [|reflexivity]. exfalso.
      apply keep_iff in EK. destruct EK as (EK & _ & _). lia.
    - rewrite <- Hst. apply fq_rw_of; [exact HSb | rewrite Hst; exact HSw]. }
  destruct (fq_mcmp 6 st (skipn 6 g) ltac:(lia) ltac:(rewrite length_skipn; lia)) as (v & Hv & Rv & Iv).
  pose proof (rf_bytes_skip rsegs m fr g 6 HG ltac:(rewrite Hg; lia)) as G6.
  change (Z.to_nat 6) with 6%nat in G6.
  step. step. step. step.
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U6' : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  call BCMP.
  { rewrite UF. exact HSb. }
  { rewrite U6. exact G6. }
  { rewrite U6'. exact Hv. }
  { assumption. }
  step.
  rewrite (rf_eqb_s v) by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb]; cbv iota.
  2:{ eapply L_drop; [ | exact DfS | exact FR | exact MU | exact WM | eassumption | ].
      - rewrite HCL0. destruct (fg_keep st g) eqn:EK; [|reflexivity]. exfalso.
        apply keep_iff in EK. destruct EK as (_ & ES & _). apply V0, Iv. exact (proj1 (rf_src_eq st g) ES).
      - rewrite <- Hst. apply fq_rw_of; [exact HSb | rewrite Hst; exact HSw]. }
  pose proof (rd_byte rsegs _ f st 7 HSb ltac:(lia)) as R7.
  step. clear R7. step. step. step.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  rewrite (fq_ltu (fg_lf st + fg_n g) 65) by lia.
  change (fg_lf st + fg_n g) with (fg_T st g).
  destruct (Z.ltb_spec (fg_T st g) 65) as [T65|T65]; cbv iota.
  - eapply L_join; [ reflexivity | | exact (conj Hn1 Hn2) | lia | exact DJAh | exact DJBh | exact OUTh | lia
                   | exact FR | exact MU | exact WM | eassumption | exact HSb | rewrite Hst; exact HSw | exact HG ].
    rewrite HCL0. replace (fg_keep st g) with true; [reflexivity|]. symmetry. apply keep_iff.
    split; [exact H6|]. split; [exact (proj2 (rf_src_eq st g) (proj1 Iv V0)) | lia].
  - eapply L_drop; [ | exact DfS | exact FR | exact MU | exact WM | eassumption | ].
    + rewrite HCL0. destruct (fg_keep st g) eqn:EK; [|reflexivity]. exfalso.
      apply keep_iff in EK. destruct EK as (_ & _ & ET). lia.
    + rewrite <- Hst. apply fq_rw_of; [exact HSb | rewrite Hst; exact HSw].
Qed.

Ltac nfail := eapply L_none;
  [ eassumption
  | let EF := fresh "EF" in destruct (fg_fr len g) eqn:EF; [exfalso; apply fr_iff in EF; lia | reflexivity]
  | eassumption | eassumption | eassumption | eassumption ].

Ltac gld i :=
  let R := fresh "RDG" in
  match goal with HG : bytes_at _ _ fr g |- _ => pose proof (rd_byte rsegs _ fr g i HG ltac:(rewrite Hg; lia)) as R end;
  step; clear R.

Ltac gchk i z c :=
  rewrite (rf_beq (nth i g (Z_to_bv 8 0)) c) by lia;
  change (bv_unsigned (nth i g (Z_to_bv 8 0))) with (bat g z);
  let B := fresh "B" in destruct (Z.eqb_spec (bat g z) c) as [B|B]; cbn [negb]; cbv iota; [|nfail].

(* 0x14a90 .. 0x14b5c: the frame checks, the block-sum loop, the first/second dispatch. *)
Lemma L_chk : forall j (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 : word) m,
  NZ -> (50 <= len -> bytes_at rsegs mE fr g) -> rw_cells rsegs mE f [CB 72 st] -> OUT -> DJA -> DJB ->
  rw_cells rsegs m (S + -80) (FRc j) -> munch [(S - 80, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  evt rsegs Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -80)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pa) x10 x11 (Z_to_bv 64 len)
             x13 x14 x15 x16 x17 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) x21 x22 x23 s8 s9 s10 s11
             x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x14a90) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 m
    NZh HF HS0 OUTh DJAh DJBh FR MU WM MI.
  step. step.
  rewrite (fq_ltu len 50) by lia.
  destruct (Z.ltb_spec len 50) as [L50|L50]; cbv iota; [nfail|].
  pose proof (bytes_at_transport rsegs [(S - 80, S)] mE m fr g (HF L50) MU
                ltac:(cbn [disjoint_from]; rewrite Hg; destruct DJAh as (_ & _ & DrS); slia)) as HG.
  pose proof (rw_cells_transport rsegs [(S - 80, S)] mE m f _ HS0 MU WM
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; destruct DJAh as (_ & DfS & _); slia)) as HS.
  clear HF HS0.
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  gld 16%nat. step. step. gchk 16%nat 16 205.
  gld 17%nat. step. step. gchk 17%nat 17 234.
  gld 18%nat. step. step. gchk 18%nat 18 4.
  gld 19%nat. step. step. step.
  rewrite rf_b1. change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct ((bat g 19 =? 1) || (bat g 19 =? 2)) eqn:E19; cbn [negb]; cbv iota.
  2:{ apply orb_false_iff in E19. destruct E19 as [E19a E19b]. apply Z.eqb_neq in E19a, E19b. nfail. }
  apply orb_true_iff in E19. rewrite !Z.eqb_eq in E19.
  gld 22%nat. step. gchk 22%nat 22 0.
  gld 23%nat. step. step. gchk 23%nat 23 2.
  gld 24%nat. step. gchk 24%nat 24 0.
  gld 25%nat. step. step. gchk 25%nat 25 254.
  gld 26%nat. step. step. step.
  rewrite rf_n. change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  destruct ((1 <=? fg_n g) && (fg_n g <=? 22)) eqn:EN; cbn [negb]; cbv iota.
  2:{ apply andb_false_iff in EN. destruct EN as [EN|EN]; apply Z.leb_gt in EN; nfail. }
  apply andb_true_iff in EN. destruct EN as [EN1 EN2]. apply Z.leb_le in EN1, EN2.
  step. step. step.
  pose proof (rf_bytes_skip rsegs m fr g 18 HG ltac:(rewrite Hg; lia)) as HBk.
  change (Z.to_nat 18) with 18%nat in HBk.
  eapply (loopB Qf) with (A := fr + 18) (bs := skipn 18 g) (c := 32%nat) (n := 32%nat) (i := 0%nat);
    [ exact HBk | rewrite length_skipn, Hg; lia | lia | lia | first [f_equal; lia | word_eq_tac] | | lia | lia | lia
    | reflexivity ].
  intros x14'.
  remember (psum (skipn 18 g) 32) as ps eqn:Eps.
  assert (PB : 0 <= ps <= 255 * 32) by (rewrite Eps; pose proof (psum_range (skipn 18 g) 32); lia).
  step. step.
  rewrite rf_land255 by lia.
  replace (ps mod 256) with (blocksum (skipn 18 g)) by (unfold blocksum; rewrite Eps; reflexivity).
  clear Eps.
  destruct (Z.eqb_spec (blocksum (skipn 18 g)) 0) as [BS|BS]; cbv iota; [|nfail].
  assert (FRT : fg_fr len g = true) by (apply fr_iff; repeat split; first [assumption | lia]).
  step. step.
  rewrite (rf_beq (nth 19 g (Z_to_bv 8 0)) 1) by lia.
  change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct (Z.eqb_spec (bat g 19) 1) as [G1|G1]; cbn [negb]; cbv iota.
  - eapply L_first; [ | lia | exact DJAh | exact FR | exact MU | exact WM | exact MI | exact HS | exact HG ].
    rewrite (cl_nn NZh), FRT, (proj2 (Z.eqb_eq _ _) G1). reflexivity.
  - eapply L_second; [ exact NZh | exact FRT | exact G1 | exact DJAh | exact DJBh | exact OUTh
                     | exact FR | exact MU | exact WM | exact MI | exact HS | exact HG ].
Qed.

Ltac rfail := eapply (L_epi FgRefuse); [ symmetry; apply rf_class_refuse; tauto | reflexivity
                                       | eassumption | match goal with H : munch _ mE _ |- _ => exact H end
                                       | eassumption | eassumption | exact I ].

(* 0x14a3c .. 0x14a8c: prologue and the argument checks. *)
Lemma L_top : forall (sp0 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) junk,
  sp0 = Z_to_bv 64 S ->
  rw_cells rsegs mE (S + -80) [CB 80 junk] -> mem_inv rsegs mE ->
  (NZ -> 50 <= len -> bytes_at rsegs mE fr g) ->
  (NZ -> rw_cells rsegs mE f [CB 72 st] /\ OUT /\ DJA /\ DJB) ->
  evt rsegs Qf
    (MS (mkR ra sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
             (Z_to_bv 64 pp) (Z_to_bv 64 pn) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x14a3c) fc None mE (seg_rom rsegs)).
Proof.
  intros sp0 t0 t1 t2 a6 a7 t3 t4 t5 t6 junk -> HR MI HF HO.
  pose proof (munch_refl [(S - 80, S)] mE) as MU.
  pose proof (wmono_refl rsegs mE) as WM.
  do 10 step.
  step. step. step.
  rewrite (fq_beq f 0) by lia.
  destruct (Z.eqb_spec f 0) as [Z0|Z0]; cbv iota; [rfail|].
  step. step.
  rewrite (fq_beq fr 0) by lia.
  destruct (Z.eqb_spec fr 0) as [Z1|Z1]; cbv iota; [rfail|].
  step. step.
  rewrite (fq_beq pa 0) by lia.
  destruct (Z.eqb_spec pa 0) as [Z2|Z2]; cbv iota; [rfail|].
  step. step.
  rewrite (fq_beq pp 0) by lia.
  destruct (Z.eqb_spec pp 0) as [Z3|Z3]; cbv iota; [rfail|].
  step. step.
  rewrite (fq_beq pn 0) by lia.
  destruct (Z.eqb_spec pn 0) as [Z4|Z4]; cbv iota; [rfail|].
  assert (NZh : NZ) by (unfold NZ; tauto).
  destruct (HO NZh) as (HS0 & OUTh & DJAh & DJBh).
  eapply L_chk; [ exact NZh | exact (HF NZh) | exact HS0 | exact OUTh | exact DJAh | exact DJBh
                | eassumption | exact MU | exact WM | exact MI ].
Qed.

End P.

Theorem reac_ctrl_identity_fragment_holds : memcpy_contract -> bcmp_contract -> reac_ctrl_identity_fragment_contract.
Proof.
  intros MEMC BCMP. unfold reac_ctrl_identity_fragment_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f fr len pa pp pn st g -> -> -> -> -> -> Hf Hfr Hlen Hpa Hpp Hpn HS16 ST Hg Hst HF HO MI.
  unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME in *. unfold REAC_CTRL_IDENTITY_FRAGMENT.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (STlo & _ & _).
  assert (Esp : sp = Z_to_bv 64 (bv_unsigned sp)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
  destruct (stk_carve rsegs m (bv_unsigned sp - 80) (bv_unsigned sp) 80 ST ltac:(lia)) as [_ [junk HR]].
  replace (bv_unsigned sp - Z.of_nat 80) with (bv_unsigned sp + -80) in HR by lia.
  eapply evt_mono.
  - eapply L_top with (S := bv_unsigned sp) (st := st) (g := g) (mE := m); try eassumption; try lia.
    + unfold NZ. intros (N1 & N2 & N3 & N4 & N5). exact (HF N1 N2 N3 N4 N5).
    + unfold NZ. intros (N1 & N2 & N3 & N4 & N5).
      destruct (HO N1 N2 N3 N4 N5) as (HS & M2 & M8 & M8' & W2 & W8 & W8' & DJ).
      apply dj_of in DJ. destruct DJ as [DA DB].
      split; [exact HS|]. split; [unfold OUT; tauto|]. split; assumption.
  - intros ms' Hq. unfold Qf in Hq.
    destruct Hq as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & R).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    rewrite <- Esp in E. split; [exact E | exact R].
Qed.
