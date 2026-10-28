(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs L5Core FrmInv FpBridge CutVF CutVFX.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecScanPure_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutL5 CutOpsD CutAutoD DecAssume.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DOK.
(* [comment removed for export] *)
Inductive cls : Type := CDig | CDot | CStopS | CStopN | CStop2.
Inductive flg : Type := G0 | G1 | GS4.          (* [comment removed for export] *)
Inductive kind : Type :=
| KEnt                        (* [comment removed for export] *)
| KSc (f : flg) (cl : cls)    (* [comment removed for export] *)
| KRXa                        (* [comment removed for export] *)
| KPost                       (* [comment removed for export] *)
| KDead.

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).
Definition reg_e (c : CC.cutpoint) (r : nat) : expr := nth r (CC.cp_regs c) (ELit 0).
Definition has (kn : list kentry) (K : kentry) : bool := existsb (APC.kentry_eqb K) kn.
Lemma has_In : forall kn K, has kn K = true -> In K kn.
Proof. intros kn K H. unfold has in H. apply existsb_exists in H as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y. exact HY. Qed.

(* [comment removed for export] *)
Definition NF : nat := 48.
Definition NMAX : Z := 67108864.
Definition rpos_e : expr := APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 47)) 1) (EVar 48).
Definition named_a : saddr := SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 47)) (EVar 48)) (-1)) 1.
Definition nk_e : expr := APC.esub (EVar 47) (EVar 48).
Definition rpos_a : saddr := SA (EVar 21) 8.
Definition region_eqb (a b : SGP.region) : bool :=
  let '(b1, o1, n1) := a in let '(b2, o2, n2) := b in (expr_eqb b1 b2 && Z.eqb o1 o2 && expr_eqb n1 n2)%bool.
Fixpoint regions_eqb (a b : list SGP.region) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (region_eqb x y && regions_eqb a' b')%bool
  | _, _ => false
  end.
Lemma regions_eqb_eq : forall a b, regions_eqb a b = true -> a = b.
Proof.
  induction a as [|[[b1 o1] n1] a IH]; intros [|[[b2 o2] n2] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H3]. apply andb_prop in H1 as [H1 H4].
  apply expr_eqb_eq in H1, H3. apply Z.eqb_eq in H4. subst. f_equal. exact (IH _ H2).
Qed.
Fixpoint find_cell (kn : list kentry) : option expr :=
  match kn with
  | [] => None
  | KWord (SA b o) 8 v :: r => if (expr_eqb b (EVar 21) && Z.eqb o 8)%bool then Some v else find_cell r
  | _ :: r => find_cell r
  end.
Lemma find_cell_In : forall kn v, find_cell kn = Some v -> In (KWord rpos_a 8 v) kn.
Proof.
  induction kn as [|K r IH]; intros v H; [discriminate|]. cbn [find_cell] in H.
  destruct K as [[b o] w v'| | | | | | | | |]; try (right; exact (IH _ H)).
  do 9 (destruct w as [|w]; try (right; exact (IH _ H))).
  destruct (expr_eqb b (EVar 21) && Z.eqb o 8)%bool eqn:Hb; [|right; exact (IH _ H)].
  apply andb_prop in Hb as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst b o. injection H as ->. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mem.
Variable segs : list Segment.
Lemma u64_at_inj : forall M a x y, L5.u64_at segs M a x -> L5.u64_at segs M a y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
  intros M a x y Hx Hy Rx Ry. unfold L5.u64_at in *. rewrite Hx in Hy. assert (Hy' : word_to_le_bytes 8 (Z_to_bv 64 x) = word_to_le_bytes 8 (Z_to_bv 64 y)) by congruence.
  clear Hy. rename Hy' into Hy. unfold word_to_le_bytes in Hy.
  assert (Q : forall z, 0 <= z < 2 ^ 64 -> bytes_le_to_Z (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 z))) = z).
  { intros z Rz. rewrite L5.unsigned_lit by exact Rz. rewrite bytes_le_to_Z_of_le_bytes by lia. apply Z.mod_small. exact Rz. }
  rewrite <- (Q x Rx), <- (Q y Ry), Hy. reflexivity.
Qed.
Lemma u8_at_inj : forall M a x y, L5.u8_at segs M a x -> L5.u8_at segs M a y -> 0 <= x < 256 -> 0 <= y < 256 -> x = y.
Proof.
  intros M a x y Hx Hy Rx Ry. unfold L5.u8_at in *. rewrite Hx in Hy. assert (Hy' : Z_to_bv 8 x = Z_to_bv 8 y) by congruence. clear Hy. rename Hy' into Hy.
  assert (Q : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z).
  { intros z Rz. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact Rz. }
  rewrite <- (Q x Rx), <- (Q y Ry), Hy. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rdn_same : forall (M M' : word -> option byte) n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M' x = M x) -> rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros M M' n a Ha Hn Hsame.
  apply (L5.rdn_frame segs M M' [(0, a); (a + Z.of_nat n, 2 ^ 64)]); [| exact Ha | exact Hn |].
  - intros x Hx. apply Hsame. pose proof (bv_unsigned_in_range _ x) as B. change (bv_modulus 64) with (2 ^ 64) in B.
    destruct (Z_lt_le_dec (bv_unsigned x) a) as [Hl|Hl]; [exfalso; apply (Hx (0, a)); [left; reflexivity | unfold L5.in_rng; cbn; lia]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (a + Z.of_nat n)) as [Hh|Hh]; [lia|].
    exfalso. apply (Hx (a + Z.of_nat n, 2 ^ 64)); [right; left; reflexivity | unfold L5.in_rng; cbn; lia].
  - intros i Hi r [<- | [<- | []]]; unfold L5.in_rng; cbn; lia.
Qed.
Lemma u64_at_same : forall (M M' : word -> option byte) a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + 8 -> M' x = M x) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros M M' a v Ha H8 Hs Hu. unfold L5.u64_at. rewrite (rdn_same M M' 8%nat a Ha ltac:(cbn; lia)); [exact Hu|]. intros x Hx. apply Hs. cbn in Hx. lia. Qed.
Lemma u8_at_same : forall (M M' : word -> option byte) a v, 0 <= a -> a + 1 <= 2 ^ 64 ->
  (forall x : word, bv_unsigned x = a -> M' x = M x) -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros M M' a v Ha H8 Hs Hu. unfold L5.u8_at. rewrite (rdn_same M M' 1%nat a Ha ltac:(cbn; lia)); [exact Hu|]. intros x Hx. apply Hs. cbn in Hx. lia. Qed.
(* [comment removed for export] *)
Lemma kword8_elim : forall E M a v A, kentry_ok segs E M (KWord a 1 v) -> estart E a = A -> L5.u8_at segs M A (bv_unsigned (edenot E v) mod 256).
Proof.
  intros E M a v A (_ & Hfl & Hr) Ha. unfold L5.u8_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End Mem.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma regs_ok_tmpl : forall regs E R, (forall n, (0 < n < 32)%nat -> edenot E (nth n regs (ELit 0)) = getr R (Z_to_bv 5 (Z.of_nat n))) -> regs_ok E regs R.
Proof.
  intros regs E R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er). cbn [edenot]. apply getr_zero.
  - assert (Hr : (0 < ridx r < 32)%nat).
    { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B. unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
    rewrite (H _ Hr). rewrite CC.reg_of_ridx. reflexivity.
Qed.
Lemma rz_word : forall R n z, PDC.rz R n = z -> getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z.
Proof. intros R n z H. unfold PDC.rz, PDC.reg_of in H. rewrite <- H. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma kword8_intro : forall (segs : list Segment) E M a v A z, estart E a = A -> 0 <= A -> A + 1 <= 2 ^ 64 -> bv_unsigned (edenot E v) = z -> 0 <= z < 256 ->
  L5.u8_at segs M A z -> kentry_ok segs E M (KWord a 1 v).
Proof.
  intros segs E M a v A z Ha H0 H1 Hv Hz Hu. cbn [kentry_ok].
  assert (Hfl : flat E a (Z.of_nat 1)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha. unfold L5.u8_at in Hu. rewrite Hu.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite Hv. reflexivity.
Qed.
Lemma kzero1_intro : forall (segs : list Segment) E (M : word -> option byte) a A, estart E a = A -> 0 <= A -> A + 1 <= 2 ^ 64 ->
  L5.u8_at segs M A 0 -> M (Z_to_bv 64 A) <> None -> kentry_ok segs E M (KZero a (ELit 1)).
Proof.
  intros segs E M a A Ha H0 H1 Hu Hd. cbn [kentry_ok]. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. rewrite Ha.
  split; [unfold flat; rewrite Ha; lia|]. intros i Hi. replace (A + i) with A by lia. exact (CL5.overlay_byte segs M _ _ Hu Hd).
Qed.
Lemma kwr_of_writable : forall (segs : list Segment) E M a n A N, estart E a = A -> elenZ E n = N -> 0 <= A -> 0 <= N -> A + N <= 2 ^ 64 -> A < 2 ^ 64 ->
  L5.writable segs M A N -> kentry_ok segs E M (KWr a n).
Proof.
  intros segs E M a n A N Ha Hn H0 HN H1 H2 Hw. cbn [kentry_ok]. rewrite Ha, Hn. split; [unfold flat; rewrite Ha; lia|]. intros d m Hd Hm. apply Hw; assumption.
Qed.

End DOK.
