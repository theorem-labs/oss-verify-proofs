From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YC88 YCjr YCj1 YCja YXcalls YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacBoxName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma pfc_rbn_globs :
  In (0xa06a0, 24) tfib_globs /\ In (0x211c0, 7) tfib_globs /\ In (0x211e0, 7) tfib_globs /\
  In (0x21200, 8) tfib_globs /\ In (0x21220, 5) tfib_globs /\ In (0x21240, 3) tfib_globs /\
  In (0x21260, 7) tfib_globs /\ In (0x21280, 6) tfib_globs.
Proof.
  unfold tfib_globs. repeat split; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

Lemma pfc_rbn_lens :
  length (bn_STEM 0) = 4%nat /\ length (bn_STEM 1) = 6%nat /\ length (bn_STEM 2) = 6%nat /\
  length (bn_STEM 3) = 7%nat.
Proof. repeat split; reflexivity. Qed.

Lemma pfc_rbn_tails :
  In (0x211c7, 1) tfib_glob_tails /\ In (0x211e7, 1) tfib_glob_tails /\ In (0x21225, 3) tfib_glob_tails.
Proof.
  unfold tfib_glob_tails. repeat split; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

Section d. Context {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {POV : PAObjVal lib_both3_0_listing (PI := PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfc_rbn_vals :
  VAL (A_OBJ 26) = 0xa06a0 /\ VAL (A_OBJ 27) = 0x21220 /\ VAL (A_OBJ 28) = 0x21240 /\
  VAL (A_OBJ 29) = 0x21260 /\ VAL (A_OBJ 30) = 0x21280.
Proof.
  rewrite (@pa_obj_val rc lib_both3_0_listing PI POV 26%nat ltac:(unfold tfib_nobj; lia)).
  rewrite (@pa_obj_val rc lib_both3_0_listing PI POV 27%nat ltac:(unfold tfib_nobj; lia)).
  rewrite (@pa_obj_val rc lib_both3_0_listing PI POV 28%nat ltac:(unfold tfib_nobj; lia)).
  rewrite (@pa_obj_val rc lib_both3_0_listing PI POV 29%nat ltac:(unfold tfib_nobj; lia)).
  rewrite (@pa_obj_val rc lib_both3_0_listing PI POV 30%nat ltac:(unfold tfib_nobj; lia)).
  repeat split; reflexivity.
Qed.

Lemma pfc_rbn_ro_y2 :
  ReacBoxName.rbn_ro (VAL (A_OBJ 26)) 24 /\ ReacBoxName.rbn_ro 0x211c0 7 /\ ReacBoxName.rbn_ro 0x211e0 7 /\
  ReacBoxName.rbn_ro 0x21200 8 /\ ReacBoxName.rbn_ro (VAL (A_OBJ 27)) 5 /\ ReacBoxName.rbn_ro (VAL (A_OBJ 28)) 3 /\
  ReacBoxName.rbn_ro (VAL (A_OBJ 29)) 7 /\ ReacBoxName.rbn_ro (VAL (A_OBJ 30)) 6.
Proof.
  destruct pfc_rbn_vals as (E26 & E27 & E28 & E29 & E30).
  rewrite E26, E27, E28, E29, E30. unfold ReacBoxName.rbn_ro. exact pfc_rbn_globs.
Qed.

Lemma pfc_rbn_word_eq : forall (W : world SEGS) (mem : word -> option byte) a v1 v2,
  val_mem SEGS (rd W mem) a 8 v1 -> 0 <= v1 < 2 ^ 64 ->
  val_mem SEGS (rd W mem) a 8 v2 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros W mem a v1 v2 H1 R1 H2 R2.
  pose proof (rdword_of_val_mem SEGS (w_H W) mem a v1 H1 R1) as E1.
  pose proof (rdword_of_val_mem SEGS (w_H W) mem a v2 H2 R2) as E2.
  rewrite E1 in E2. injection E2 as E. exact E.
Qed.

Lemma pfc_rbn_stem_range : forall (W : world SEGS) (mem : word -> option byte) a s,
  DiscoYEntryInv.rbn_stem W mem a s -> 0 <= a < 2 ^ 64.
Proof.
  intros W mem a s ((_ & _ & Ha & Hb & _) & _). pose proof (Zle_0_nat (length s)). lia.
Qed.

Lemma pfc_rbn_pinned : forall (W : world SEGS) (mem : word -> option byte) t1 t2 t3,
  val_mem SEGS (rd W mem) (VAL (A_OBJ 26)) 8 t1 -> DiscoYEntryInv.rbn_stem W mem t1 (bn_STEM 1) ->
  val_mem SEGS (rd W mem) (VAL (A_OBJ 26) + 8) 8 t2 -> DiscoYEntryInv.rbn_stem W mem t2 (bn_STEM 2) ->
  val_mem SEGS (rd W mem) (VAL (A_OBJ 26) + 16) 8 t3 -> DiscoYEntryInv.rbn_stem W mem t3 (bn_STEM 3) ->
  dimg_ro W mem ->
  t1 = 0x211c0 /\ t2 = 0x211e0 /\ t3 = 0x21200.
Proof.
  intros W mem t1 t2 t3 V1 S1 V2 S2 V3 S3 (D1 & D2 & D3 & _).
  destruct pfc_rbn_vals as (_ & E27 & _). rewrite E27 in D1, D2, D3.
  pose proof (pfc_rbn_word_eq W mem _ _ _ V1 (pfc_rbn_stem_range W mem _ _ S1) D1 ltac:(lia)).
  pose proof (pfc_rbn_word_eq W mem _ _ _ V2 (pfc_rbn_stem_range W mem _ _ S2) D2 ltac:(lia)).
  pose proof (pfc_rbn_word_eq W mem _ _ _ V3 (pfc_rbn_stem_range W mem _ _ S3) D3 ltac:(lia)).
  lia.
Qed.

Lemma pfc_rbn_old_pinned : forall (W : world SEGS) (mem : word -> option byte),
  DiscoYEntryInv.rbn_img W mem -> dimg_ro W mem ->
  DiscoYEntryInv.rbn_stem W mem 0x211c0 (bn_STEM 1) /\ DiscoYEntryInv.rbn_stem W mem 0x211e0 (bn_STEM 2) /\
  DiscoYEntryInv.rbn_stem W mem 0x21200 (bn_STEM 3) /\ DiscoYEntryInv.rbn_stem W mem 0x21220 (bn_STEM 0).
Proof.
  intros W mem (t1 & t2 & t3 & _ & _ & _ & V1 & V2 & V3 & S1 & S2 & S3 & S0 & _) HO.
  destruct (pfc_rbn_pinned W mem t1 t2 t3 V1 S1 V2 S2 V3 S3 HO) as (-> & -> & ->).
  destruct pfc_rbn_vals as (_ & E27 & _). rewrite E27 in S0.
  exact (conj S1 (conj S2 (conj S3 S0))).
Qed.

Lemma pfc_rbn_glob_unowned : forall B, d_ro_hyps (PI := PI) B ->
  forall q sz, In (q, sz) tfib_globs -> forall x, q <= x < q + sz ->
  ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
  intros B (HU & _ & _) q sz Hin x Hx.
  exact (tfib_ro_unowned_at B q sz HU (in_or_app tfib_globs tfib_ro_extra (q, sz) (or_introl Hin)) x Hx).
Qed.

Lemma pfc_rbn_stem_own : forall B (W : world SEGS) (mem : word -> option byte) a s,
  d_ro_hyps (PI := PI) B -> In (a, Z.of_nat (length s) + 1) tfib_globs ->
  DiscoYEntryInv.rbn_stem W mem a s ->
  forall x, a <= x < a + Z.of_nat (length s) + 1 ->
    in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
  intros B W mem a s HD Hin (_ & HI) x Hx. split; [exact (HI x Hx)|].
  apply (pfc_rbn_glob_unowned B HD a (Z.of_nat (length s) + 1) Hin x). lia.
Qed.

Lemma pfc_rbn_stems_own : forall B (W : world SEGS) (mem : word -> option byte),
  d_ro_hyps (PI := PI) B -> DiscoYEntryInv.rbn_img W mem -> dimg_ro W mem ->
  (forall x, 0x211c0 <= x < 0x211c0 + 7 ->
     in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
  (forall x, 0x211e0 <= x < 0x211e0 + 7 ->
     in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
  (forall x, 0x21200 <= x < 0x21200 + 8 ->
     in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
  (forall x, 0x21220 <= x < 0x21220 + 5 ->
     in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)).
Proof.
  intros B W mem HD HR HO.
  destruct (pfc_rbn_old_pinned W mem HR HO) as (S1 & S2 & S3 & S0).
  destruct pfc_rbn_globs as (_ & G1 & G2 & G3 & G0 & _).
  split; [|split; [|split]].
  - exact (pfc_rbn_stem_own B W mem 0x211c0 (bn_STEM 1) HD G1 S1).
  - exact (pfc_rbn_stem_own B W mem 0x211e0 (bn_STEM 2) HD G2 S2).
  - exact (pfc_rbn_stem_own B W mem 0x21200 (bn_STEM 3) HD G3 S3).
  - exact (pfc_rbn_stem_own B W mem 0x21220 (bn_STEM 0) HD G0 S0).
Qed.

Lemma pfc_rbn_stem_y2_t3 : forall B (W : world SEGS) (mem : word -> option byte),
  d_ro_hyps (PI := PI) B -> DiscoYEntryInv.rbn_img W mem -> dimg_ro W mem ->
  ReacBoxName.rbn_stem B W mem 0x21200 (bn_STEM 3).
Proof.
  intros B W mem HD HR HO.
  destruct (pfc_rbn_old_pinned W mem HR HO) as (_ & _ & S3 & _).
  destruct (pfc_rbn_stems_own B W mem HD HR HO) as (_ & _ & O3 & _).
  split; [exact (proj1 S3)|]. split; [exact O3|].
  intros x Hx. change (Z.of_nat (length (bn_STEM 3))) with 7 in Hx. lia.
Qed.

Context {PR : PARoPresent lib_both3_0_listing}.

Lemma pfc_rbn_img_y2 : forall B (W : world SEGS) (mem : word -> option byte),
  d_ro_hyps (PI := PI) B -> dimg_consts W mem -> ReacBoxName.rbn_img B W mem.
Proof.
  intros B W mem HD HC.
  pose proof HC as (HR & _ & _ & _ & _ & _ & _ & HO).
  pose proof HR as (t1 & t2 & t3 & M8 & IM & RA & V1 & V2 & V3 & S1 & S2 & S3 & S0 & L28 & L29 & L30).
  destruct (pfc_rbn_pinned W mem t1 t2 t3 V1 S1 V2 S2 V3 S3 HO) as (-> & -> & ->).
  destruct (pfc_rbn_stems_own B W mem HD HR HO) as (O1 & O2 & _ & O0).
  destruct pfc_rbn_ro_y2 as (R26 & R1 & R2 & R3 & R27 & R28 & R29 & R30).
  destruct pfc_rbn_vals as (_ & E27 & _). rewrite E27 in S0.
  destruct pfc_rbn_tails as (G1 & G2 & G0).
  assert (TL : forall q sz x, In (q, sz) tfib_glob_tails -> q <= x < q + sz ->
    seg_rom SEGS (Z_to_bv 64 x) <> None) by exact (pa_ro_present (L := lib_both3_0_listing) (PI := PI)).
  exists 0x211c0, 0x211e0, 0x21200.
  split; [exact M8|]. split; [exact IM|]. split; [exact RA|].
  split; [exact V1|]. split; [exact V2|]. split; [exact V3|].
  split.
  { split; [exact (proj1 S1)|]. split; [exact O1|].
    intros x Hx. change (Z.of_nat (length (bn_STEM 1))) with 6 in Hx.
    apply (TL 0x211c7 1 x); [exact G1 | lia]. }
  split.
  { split; [exact (proj1 S2)|]. split; [exact O2|].
    intros x Hx. change (Z.of_nat (length (bn_STEM 2))) with 6 in Hx.
    apply (TL 0x211e7 1 x); [exact G2 | lia]. }
  split; [exact (pfc_rbn_stem_y2_t3 B W mem HD HR HO)|].
  split.
  { rewrite E27. split; [exact (proj1 S0)|]. split; [exact O0|].
    intros x Hx. change (Z.of_nat (length (bn_STEM 0))) with 4 in Hx.
    apply (TL 0x21225 3 x); [exact G0 | lia]. }
  split; [exact L28|]. split; [exact L29|]. split; [exact L30|].
  split; [exact R26|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [exact R27|]. split; [exact R28|]. split; [exact R29|]. exact R30.
Qed.

End f.
End d.
