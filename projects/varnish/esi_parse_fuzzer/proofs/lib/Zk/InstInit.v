(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import InstDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import KInv MI_Inv MI_Ccma KNodes KLink MSafe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Own LB_Init.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_le_bytes_nth : forall n z i, (i < n)%nat -> 0 <= z ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (z / 2 ^ (8 * Z.of_nat i))).
Proof.
  induction n as [|n IH]; intros z i Hi Hz; [lia|].
  cbn [Z_to_le_bytes]. destruct i as [|i].
  - cbn [nth_error]. f_equal. f_equal. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity.
  - cbn [nth_error]. rewrite IH; [| lia| apply Z.shiftr_nonneg; exact Hz]. f_equal. f_equal.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. f_equal.
    rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma le8_byte : forall v i, 0 <= v < 2 ^ 64 -> (i < 8)%nat ->
  nth_error (Mem.le8 (wz v)) i = Some (DriverKit.le8 v (Z.of_nat i)).
Proof.
  intros v i Hv Hi. unfold Mem.le8, word_to_le_bytes. rewrite unsigned_lit by lia.
  rewrite Z_to_le_bytes_nth by (lia || assumption). f_equal. unfold DriverKit.le8.
  apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2 ^ 8). cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma rw_cells_CB_of (m : mem) A bs :
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> mrd segs m (wa (A + Z.of_nat i)) = nth_error bs i /\ wview segs m (wa (A + Z.of_nat i)) <> None) ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros HA Hl H. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H i Hi)).
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (proj2 (H (Z.to_nat i) ltac:(lia))).
Qed.

Lemma rw_cells_recast : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
Fixpoint rw_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A), wview segs (fun _ => None) (wa A) with
      | Some b', Some _ => bv_eqb b b' && rw_bytes_b (A + 1) bs'
      | _, _ => false
      end
  end.

(* [comment removed for export] *)
Lemma rw_bytes_b_sound : forall bs A (m : mem),
  rw_bytes_b A bs = true ->
  (forall i b, nth_error bs i = Some b -> m (wa (A + Z.of_nat i)) = None \/ m (wa (A + Z.of_nat i)) = Some b) ->
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  forall i b, nth_error bs i = Some b ->
    mrd segs m (wa (A + Z.of_nat i)) = Some b /\ wview segs m (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs as [|b0 bs IH]; intros A m Hb Hm HA Hl i b Hn; [destruct i; discriminate|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom segs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [Hbe Hb]. unfold bv_eqb in Hbe. apply Z.eqb_eq in Hbe. apply bv_eq in Hbe. subst b'.
  cbn [length] in Hl.
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. rewrite Z.add_0_r.
    destruct (Hm 0%nat b eq_refl) as [Hnone|Hsame]; rewrite Z.add_0_r in *.
    + split. { unfold mrd. rewrite Hnone. exact Er. }
      unfold wview in *. rewrite Hnone. intros C. rewrite C in Ew. discriminate.
    + split. { unfold mrd. rewrite Hsame. reflexivity. }
      unfold wview. rewrite Hsame. discriminate.
  - cbn in Hn. replace (A + Z.of_nat (S i)) with ((A + 1) + Z.of_nat i) by lia.
    apply (IH (A + 1) m Hb); try lia; [|exact Hn].
    intros j bj Hj. replace (A + 1 + Z.of_nat j) with (A + Z.of_nat (S j)) by lia. apply Hm. cbn. exact Hj.
Qed.

Lemma rw_cells_image : forall (m : mem) A bs,
  (forall i b, nth_error bs i = Some b -> m (wa (A + Z.of_nat i)) = None \/ m (wa (A + Z.of_nat i)) = Some b) ->
  rw_bytes_b A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs Hm Hb HA Hl. pose proof (rw_bytes_b_sound bs A m Hb Hm HA Hl) as G.
  apply rw_cells_CB_of; [exact HA| exact Hl|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [exact (G i b E)|]. apply nth_error_None in E. lia.
Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition byte_at (m : mem) (a : Z) : byte := match m (wz a) with Some b => b | None => Z_to_bv 8 0 end.
Definition bytes_from (m : mem) (a : Z) (n : nat) : list byte := map (fun i => byte_at m (a + Z.of_nat i)) (seq 0 n).

Lemma bytes_from_length m a n : length (bytes_from m a n) = n.
Proof. unfold bytes_from. rewrite length_map, length_seq. reflexivity. Qed.

Lemma bytes_from_nth m a n i : (i < n)%nat -> nth_error (bytes_from m a n) i = Some (byte_at m (a + Z.of_nat i)).
Proof.
  intros Hi. unfold bytes_from. rewrite nth_error_map, (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma bytes_le_to_Z_range (bs : list byte) : 0 <= bytes_le_to_Z bs < 256 ^ Z.of_nat (length bs).
Proof.
  rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as H.
  rewrite length_map in H. exact H.
Qed.

Lemma Z_to_le_bytes_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  pose proof (proj1 (bytes_le_to_Z_range bs)) as Hr.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8)%Z with 256%Z.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256)%Z with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma le8_of_bytes (bs : list byte) : length bs = 8%nat -> Mem.le8 (wz (bytes_le_to_Z bs)) = bs.
Proof.
  intros Hl. pose proof (bytes_le_to_Z_range bs) as R. rewrite Hl in R. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in R.
  unfold Mem.le8, word_to_le_bytes. cbv delta [MRep.wz]. rewrite ?wz_unsigned, ?unsigned_lit by exact R. rewrite <- Hl. apply Z_to_le_bytes_roundtrip.
Qed.

Lemma secret_range (m : mem) (rnd : Z) : 0 <= bytes_le_to_Z (bytes_from m (rnd + 8) 8) < 2^64.
Proof.
  pose proof (bytes_le_to_Z_range (bytes_from m (rnd + 8) 8)) as R. rewrite bytes_from_length in R. exact R.
Qed.

(* [comment removed for export] *)
Definition rr_init (m : mem) (rnd g : Z) (Hg : 0 <= g < 2^64) : RunRandom :=
  {| run_secret := bytes_le_to_Z (bytes_from m (rnd + 8) 8);
     run_guard := g;
     run_secret_range := secret_range m rnd;
     run_guard_range := Hg |}.

(* [comment removed for export] *)
Section RR.
Context {Clg : Ceiling} {Rr : RunRandom}.
Definition rr_ok (lo : Z) (m : mem) : Prop :=
  DriverKit.cell8 m (il_guard InitP0) run_guard /\
  exists av rnd x3 x4 x5 hw x6 x11 x12 x23,
         DriverKit.cell8 m (il_libc InitP0 + 8) av /\ 0 <= av /\ av mod 8 = 0 /\ av + 160 <= 2^64 /\ 0 <= rnd /\ rnd + 16 <= 2^64
      /\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= hw < 2^64 /\ 0 <= x6 < 2^64
      /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64
      /\ DriverKit.cell8 m av 3 /\ DriverKit.cell8 m (av + 8) x3 /\ DriverKit.cell8 m (av + 16) 4 /\ DriverKit.cell8 m (av + 24) x4
      /\ DriverKit.cell8 m (av + 32) 5 /\ DriverKit.cell8 m (av + 40) x5 /\ DriverKit.cell8 m (av + 48) 16 /\ DriverKit.cell8 m (av + 56) hw
      /\ DriverKit.cell8 m (av + 64) 6 /\ DriverKit.cell8 m (av + 72) x6
      /\ DriverKit.cell8 m (av + 80) 11 /\ DriverKit.cell8 m (av + 88) x11 /\ DriverKit.cell8 m (av + 96) 12 /\ DriverKit.cell8 m (av + 104) x12
      /\ DriverKit.cell8 m (av + 112) 23 /\ DriverKit.cell8 m (av + 120) x23 /\ DriverKit.cell8 m (av + 128) 25 /\ DriverKit.cell8 m (av + 136) rnd
      /\ DriverKit.cell8 m (av + 144) 0 /\ DriverKit.cell8 m (av + 152) 0
      /\ bytes_at rsegs m (rnd + 8) (Mem.le8 (wz run_secret))
      /\ lo <= av /\ lo <= rnd.
End RR.

(* [comment removed for export] *)
Theorem init_rr {Clg : Ceiling} lo m md : init_ok LayoutP0 InitP0 lo m md -> exists Rr : RunRandom, rr_ok lo m.
Proof.
  intros IOK. pose proof IOK as (_ & _ & _ & AUX & _ & GU & _).
  (first [ dex1 GU as g; destruct GU as [Hg Cg] | dand3 GU as g Hg Cg | destruct GU as (g & Hg & Cg) ]).
  (first [ dex10 AUX as av rnd x3 x4 x5 hw x6 x11 x12 x23; dand15 AUX as Cav Hav0 Hav8 Hav160 Hr0 Hr16 R3 R4 R5 RHW R6 R11 R12 R23 CELLS | dand25 AUX as av rnd x3 x4 x5 hw x6 x11 x12 x23 Cav Hav0 Hav8 Hav160 Hr0 Hr16 R3 R4 R5 RHW R6 R11 R12 R23 CELLS | destruct AUX as (av & rnd & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & Cav & Hav0 & Hav8 & Hav160 & Hr0 & Hr16
                   & R3 & R4 & R5 & RHW & R6 & R11 & R12 & R23 & CELLS) ]).
  exists (rr_init m rnd g Hg). split; [exact Cg|].
  exists av, rnd, x3, x4, x5, hw, x6, x11, x12, x23.
  repeat match goal with |- _ /\ _ => split; [assumption|] end || idtac.
  all: try assumption.
  decompose [and] CELLS.
  repeat (split; [assumption|]).
  split; [| split; assumption].
  (* [comment removed for export] *)
  cbn [run_secret rr_init]. rewrite (le8_of_bytes _ (bytes_from_length m (rnd + 8) 8)).
  split; [lia|]. split; [rewrite bytes_from_length; lia|].
  intros i Hi. rewrite bytes_from_length in Hi. rewrite (bytes_from_nth m (rnd + 8) 8 i Hi).
  unfold byte_at. change (wa (rnd + 8 + Z.of_nat i)) with (wz (rnd + 8 + Z.of_nat i)). unfold mrd.
  match goal with H : forall i0 : Z, 0 <= i0 < 16 -> m (wz (rnd + i0)) <> None |- _ =>
    pose proof (H (8 + Z.of_nat i) ltac:(lia)) as NN end.
  replace (rnd + 8 + Z.of_nat i) with (rnd + (8 + Z.of_nat i)) by lia.
  destruct (m (wz (rnd + (8 + Z.of_nat i)))) as [b|]; [reflexivity| exfalso; apply NN; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section PRISTINE.
Context {Rr : RunRandom}.
Definition st_init : mstate := minit run_secret p0_reserved.
Definition s_init : PState := mkPS (strip st_init) 0 (0, 0) tt.
Definition A_init : ias := mkIAS s_init [] Rr.
End PRISTINE.

Lemma nth_error_zeros n i b : nth_error (zeros n) i = Some b -> b = b8 0.
Proof. unfold zeros. intros H. apply nth_error_In in H. apply repeat_spec in H. exact H. Qed.

Section INIT.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (lo : Z) (m : mem) (md : Model).
Hypothesis IOK : init_ok LayoutP0 InitP0 lo m md.
Hypothesis RROK : rr_ok lo m.

#[using="IOK md lo Clg"] Lemma init_statics : forall a, 0x62458 <= a < 0x62804 -> m (wz a) = None \/ m (wz a) = Some (b8 0).
Proof.
  intros a Ha. destruct IOK as (ST & _). destruct (ST a Ha) as [H|[H _]]; [right; exact H| left; exact H].
Qed.

(* [comment removed for export] *)
#[using="IOK md lo Clg"] Lemma init_zero_chunk A n : 0x62458 <= A -> A + Z.of_nat n <= 0x62804 ->
  rw_bytes_b rsegs A (zeros n) = true -> rw_cells rsegs m A [CB n (zeros n)].
Proof.
  intros H1 H2 Hb. pose proof (rw_cells_image rsegs m A (zeros n)) as R. unfold zeros in R at 1 3 4. rewrite repeat_length in R.
  apply R; [| exact Hb| lia| lia].
  intros i b Hi. pose proof (nth_error_zeros _ _ _ Hi) as ->. assert (Hi' : (i < n)%nat).
  { destruct (Nat.lt_ge_cases i n) as [Y|Y]; [exact Y|]. exfalso. pose proof (proj2 (nth_error_None (repeat (b8 0) n) i) ltac:(rewrite repeat_length; lia)) as E. unfold zeros in Hi. rewrite E in Hi. discriminate. }
  change (wa (A + Z.of_nat i)) with (wz (A + Z.of_nat i)). apply init_statics. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_C8_of_cell8 a v : DriverKit.cell8 m a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rw_cells rsegs m a [C8 (wz v)].
Proof.
  intros C Hv Ha Hl. apply (rw_cells_recast rsegs m a [CB 8 (Mem.le8 (wz v))]); [| cbn; split; exact I| reflexivity| reflexivity].
  apply (rw_cells_CB_of rsegs m a (Mem.le8 (wz v))); [exact Ha| rewrite length_le8; exact Hl|].
  rewrite length_le8. intros i Hi. pose proof (C (Z.of_nat i) ltac:(lia)) as E.
  change (wa (a + Z.of_nat i)) with (Z_to_bv 64 (a + Z.of_nat i)).
  unfold mrd, wview. rewrite E. rewrite (le8_byte v i Hv Hi). split; [reflexivity| discriminate].
Qed.

Lemma bytes_at_cell8 a v : DriverKit.cell8 m a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at rsegs m a (Mem.le8 (wz v)).
Proof.
  intros C Hv Ha Hl. destruct (rw_C8_of_cell8 a v C Hv Ha Hl) as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma u64arr_of_rw_cells' A n bs k : rw_cells rsegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
  u64arr rsegs m A (repeat (wz 0) k).
Proof.
  intros [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

(* [comment removed for export] *)
#[using="RROK IOK md lo"] Theorem mrep_init : mrep st_init m.
Proof.
  pose proof IOK as (ST & NL & PS & AUX & GOT & GU & HZ & _).
  split; [| split; [| split; [| split; [| split]]]].
  - (* [comment removed for export] *) split; [reflexivity|]. split; [intros rid r H; cbn in H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
  - (* [comment removed for export] *) unfold mrep_ctx. split; [| split; [| split; [| split; [| split]]]].
    + apply (rw_cells_recast rsegs m CTX [CB 80 (zeros 80)]); [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| vm_compute; reflexivity| reflexivity].
      apply init_zero_chunk; [unfold CTX; lia| unfold CTX; cbn; lia| vm_compute; reflexivity].
    + replace (actives st_init) with (repeat (wz 0) 48) by reflexivity.
      eapply (u64arr_of_rw_cells' _ 384 (zeros 384) 48); [| vm_compute; reflexivity| reflexivity].
      apply init_zero_chunk; [unfold CTX; lia| unfold CTX; cbn; lia| vm_compute; reflexivity].
    + replace (usages st_init) with (repeat (wz 0) 48) by reflexivity.
      eapply (u64arr_of_rw_cells' _ 384 (zeros 384) 48); [| vm_compute; reflexivity| reflexivity].
      apply init_zero_chunk; [unfold CTX; lia| unfold CTX; cbn; lia| vm_compute; reflexivity].
    + replace (unmap_seqs st_init) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32).
      apply init_zero_chunk; [unfold CTX; lia| unfold CTX; cbn; lia| vm_compute; reflexivity].
    + replace (bouncess st_init) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32).
      apply init_zero_chunk; [unfold CTX; lia| unfold CTX; cbn; lia| vm_compute; reflexivity].
    + apply (rw_cells_recast rsegs m (CTX + 912) [CB 16 (zeros 16)]); [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| vm_compute; reflexivity| reflexivity].
      apply init_zero_chunk; [unfold CTX; lia| unfold CTX; cbn; lia| vm_compute; reflexivity].
  - (* [comment removed for export] *) unfold mrep_globals. split; [| split; [| split; [| split]]].
    + apply (rw_cells_recast rsegs m MLOCK [CB 4 (zeros 4)]); [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| vm_compute; reflexivity| reflexivity].
      apply init_zero_chunk; [unfold MLOCK; lia| unfold MLOCK; cbn; lia| vm_compute; reflexivity].
    + apply (rw_cells_recast rsegs m NEED_LOCKS [CB 1 (zeros 1)]); [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| vm_compute; reflexivity| reflexivity].
      apply (rw_cells_image rsegs m NEED_LOCKS (zeros 1)); [| vm_compute; reflexivity| unfold NEED_LOCKS; lia| unfold NEED_LOCKS; cbn; lia].
      intros i b Hi. destruct i as [|[|i]]; cbn in Hi; [| discriminate| discriminate]. injection Hi as <-. rewrite Z.add_0_r.
      change (wa NEED_LOCKS) with (Z_to_bv 64 (il_libc InitP0 + 3)).
      destruct NL as [H|[H _]]; [right; exact H| left; exact H].
    + change PAGE_SIZE_A with (il_libc InitP0 + 48). apply rw_C8_of_cell8; [exact PS| lia| cbn; lia| cbn; lia].
    + apply (rw_cells_recast rsegs m GOT_SSP [CB 8 (Mem.le8 (wz SSP_GUARD))]); [| cbn; split; exact I| reflexivity| reflexivity].
      apply (rw_cells_image rsegs m GOT_SSP (Mem.le8 (wz SSP_GUARD))); [| vm_compute; reflexivity| unfold GOT_SSP; lia| rewrite length_le8; unfold GOT_SSP; lia].
      intros i b Hi. assert (Hi8 : (i < 8)%nat) by (apply nth_error_Some_length in Hi || (destruct (Nat.lt_ge_cases i 8) as [Y|Y]; [exact Y| exfalso; rewrite (proj2 (nth_error_None _ _)) in Hi by (rewrite length_le8; lia); discriminate]); exact Hi8 || idtac).
      rewrite (le8_byte SSP_GUARD i ltac:(unfold SSP_GUARD; lia) Hi8) in Hi. injection Hi as <-.
      change (wa (GOT_SSP + Z.of_nat i)) with (Z_to_bv 64 (il_got InitP0 + Z.of_nat i)). change SSP_GUARD with (il_guard InitP0).
      destruct (GOT (Z.of_nat i) ltac:(lia)) as [H|[H _]]; [right; exact H| left; exact H].
    + (* [comment removed for export] *)
      change SSP_GUARD with (il_guard InitP0). apply rw_C8_of_cell8; [exact (proj1 RROK)| apply run_guard_range| cbn; lia| cbn; lia].
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

#[using="IOK md lo Clg"] Lemma repl0_init : repl0 m.
Proof.
  unfold repl0. apply (rw_cells_recast rsegs m MALLOC_REPLACED [CB 4 (zeros 4)]); [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| vm_compute; reflexivity| reflexivity].
  apply init_zero_chunk; [unfold MALLOC_REPLACED; lia| unfold MALLOC_REPLACED; cbn; lia| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="IOK m lo"] Theorem KL_init : KL (led_init p0_reserved) 0 md.
Proof.
  pose proof IOK as (_ & _ & _ & _ & _ & _ & _ & VM & NA & LZ & MAT & BRK & HI & RESV & CEIL & ALG & LIM & HALT & CEILOK).   (* [comment removed for export] *)
  cbn [al_image_hi LayoutP0] in HI. cbn [il_resv InitP0] in RESV.
  constructor; cbn [ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live led_init].
  - exact LZ.
  - exact HALT.
  - rewrite VM. split; [intros e []| constructor].
  - unfold p0_reserved. rewrite <- RESV. unfold wwZ. reflexivity.
  - intros e He. pose proof (in_map (fun e => (bv_unsigned (fst e), bv_unsigned (snd e))) _ _ He) as Hin. rewrite RESV in Hin.
    unfold ehi. cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; rewrite E1, E2 || rewrite <- E1, <- E2; lia.
  - split; [lia|]. split; [unfold PGSZ; exact ALG|]. split; [rewrite BRK; lia|]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold PGSZ. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - intros b l [].
  - intros b l k [].
  - cbn. constructor.
  - intros b l H. discriminate H.
  - split; [| reflexivity]. symmetry. apply bv_eq. rewrite BRK. reflexivity.
  - rewrite VM. intros e [].
  - rewrite NA. intros e [].
  - intros b l [].
  - exact MAT.
  - rewrite VM. intros e [].
  - unfold brk_extent. cbn. rewrite BRK. unfold PGSZ. lia.
  - exact LIM.
  - (* [comment removed for export] *) exact CEILOK.
Qed.

#[using="IOK m lo"] Theorem OWN_init : OWN [] G0 s_init md.
Proof.
  split; [| split; [constructor| exact I]].
  exists (led_init p0_reserved). split; [| split; [exact KL_init| intros c []]].
  (* [comment removed for export] *)
  exists st_init, [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; pose proof run_secret_range; lia| reflexivity].
Qed.

#[using="RROK IOK md lo"] Theorem HEAP_init : HEAP s_init [] m.
Proof.
  exists st_init, []. split; [apply Permutation_refl|]. split; [reflexivity|]. split; [exact mrep_init|]. apply HINV_init.
Qed.

#[using="RROK IOK lo"] Theorem p0_ainv_init : p0_ainv A_init m md.
Proof. split; [exact HEAP_init| split; [exact OWN_init| split; [exact repl0_init| exact (QV_minit _ _)]]]. Qed.

(* [comment removed for export] *)
#[using="RROK"] Theorem auxv_ok_init (B : Z) : alloc_ceiling <= B -> B <= lo -> auxv_ok m B.
Proof.
  intros HB HBlo. destruct RROK as [_ AUX].
  (first [ dex10 AUX as av rnd x3 x4 x5 hw x6 x11 x12 x23; dand36 AUX as Cav Hav0 Hav8 Hav160 Hr0 Hr16 R3 R4 R5 RHW R6 R11 R12 R23 K0 V0 K1 V1 K2 V2 K3 V3 K4 V4 K5 V5 K6 V6 K7 V7 K8 V8 K9 V9 RND dR_AUX_t0; destruct dR_AUX_t0 as [LOav LOrnd] | dand36 AUX as av rnd x3 x4 x5 hw x6 x11 x12 x23 Cav Hav0 Hav8 Hav160 Hr0 Hr16 R3 R4 R5 RHW R6 R11 R12 R23 K0 V0 K1 V1 K2 V2 K3 V3 K4 V4 K5 dR_AUX_t0; dand12 dR_AUX_t0 as V5 K6 V6 K7 V7 K8 V8 K9 V9 RND LOav LOrnd | destruct AUX as (av & rnd & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & Cav & Hav0 & Hav8 & Hav160 & Hr0 & Hr16
                   & R3 & R4 & R5 & RHW & R6 & R11 & R12 & R23
                   & K0 & V0 & K1 & V1 & K2 & V2 & K3 & V3 & K4 & V4 & K5 & V5 & K6 & V6 & K7 & V7 & K8 & V8 & K9 & V9 & RND & LOav & LOrnd) ]).
  exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd.
  split; [| split; [| split]].
  - change AUXV_CELL with (il_libc InitP0 + 8). apply rw_C8_of_cell8; [exact Cav| lia| cbn; lia| cbn; lia].
  - unfold auxv_list. cbn [map u64s].
    repeat (apply (proj2 (bytes_at_app rsegs m _ _ _)); split;
            [apply bytes_at_cell8; [assumption| lia| lia| lia]
            | rewrite length_le8; rewrite <- ?Z.add_assoc; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]]).
    apply bytes_at_nil. lia.
  - exact RND.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.
End INIT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell8_agree (m m' : mem) a v : (forall i, 0 <= i < 8 -> m' (wz (a + i)) = m (wz (a + i))) -> DriverKit.cell8 m a v -> DriverKit.cell8 m' a v.
Proof. intros E C i Hi. rewrite (E i Hi). exact (C i Hi). Qed.
Lemma cell8_img_agree (m m' rom : mem) a v : (forall i, 0 <= i < 8 -> m' (wz (a + i)) = m (wz (a + i))) -> cell8_img m rom a v -> cell8_img m' rom a v.
Proof. intros E C i Hi. unfold cell8_img in C. rewrite (E i Hi). exact (C i Hi). Qed.
Lemma zero_img_agree (m m' rom : mem) a : m' (wz a) = m (wz a) -> zero_img m rom a -> zero_img m' rom a.
Proof. intros E Z0. unfold zero_img in *. rewrite E. exact Z0. Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem p0_dk_init_frame : forall lo m m' md md',
  init_ok LayoutP0 InitP0 lo m md ->
  (forall a, il_static_lo InitP0 <= a < il_static_hi InitP0 -> m' (wz a) = m (wz a)) ->
  (forall a, il_libc InitP0 <= a < il_libc InitP0 + 56 -> m' (wz a) = m (wz a)) ->
  (forall a, il_got InitP0 <= a < il_got InitP0 + 8 -> m' (wz a) = m (wz a)) ->
  (forall a, il_guard InitP0 <= a < il_guard InitP0 + 8 -> m' (wz a) = m (wz a)) ->
  (forall a, lo <= a -> m' (wz a) = m (wz a)) ->
  (forall a, heap_zone LayoutP0 a -> m' (wz a) = None) ->
  m_vm md' = m_vm md -> m_halted md' = None ->
  init_ok LayoutP0 InitP0 lo m' md'.
Proof.
  intros lo m m' md md' IOK ES EL EG EU EUP HZ' EVM HALT'.
  pose proof IOK as (ST & NL & PS & AUX & GOT & GU & HZ & VM & NA & LZ & MAT & BRK & HI & RESV & CEIL & ALG & LIM & HALT & CEILOK).
  assert (EVMM : m_vmmaps md' = m_vmmaps md) by (unfold m_vmmaps; rewrite EVM; reflexivity).
  unfold init_ok. rewrite EVMM. unfold m_vm_lazy, m_vm_materialized in *. rewrite EVM.
  split; [intros a Ha; apply (zero_img_agree m m'); [apply ES; exact Ha| exact (ST a Ha)]|].
  split; [apply (zero_img_agree m m'); [apply EL; cbn; lia| exact NL]|].
  split; [apply (cell8_agree m m'); [intros i Hi; apply EL; cbn; lia| exact PS]|].
  split.
  { (first [ dex10 AUX as av rnd x3 x4 x5 hw x6 x11 x12 x23; dand15 AUX as Cav Hav0 Hav8 Hav160 Hr0 Hr16 R3 R4 R5 RHW R6 R11 R12 R23 REST | dand25 AUX as av rnd x3 x4 x5 hw x6 x11 x12 x23 Cav Hav0 Hav8 Hav160 Hr0 Hr16 R3 R4 R5 RHW R6 R11 R12 R23 REST | destruct AUX as (av & rnd & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & Cav & Hav0 & Hav8 & Hav160 & Hr0 & Hr16
                     & R3 & R4 & R5 & RHW & R6 & R11 & R12 & R23 & REST) ]).
    exists av, rnd, x3, x4, x5, hw, x6, x11, x12, x23.
    split; [apply (cell8_agree m m'); [intros i Hi; apply EL; cbn; lia| exact Cav]|].
    repeat (split; [assumption|]).
    (first [ dand23 REST as K0 V0 K1 V1 K2 V2 K3 V3 K4 V4 K5 V5 K6 V6 K7 V7 K8 V8 K9 V9 RND LOav LOrnd | destruct REST as (K0 & V0 & K1 & V1 & K2 & V2 & K3 & V3 & K4 & V4 & K5 & V5 & K6 & V6 & K7 & V7 & K8 & V8 & K9 & V9 & RND & LOav & LOrnd) ]).
    repeat (split; [apply (cell8_agree m m'); [intros i Hi; apply EUP; lia| assumption]|]).
    split; [| split; assumption]. intros i Hi. rewrite (EUP (rnd + i)) by lia. exact (RND i Hi). }
  split; [apply (cell8_img_agree m m'); [intros i Hi; apply EG; lia| exact GOT]|].
  split. { (first [ dex1 GU as g; destruct GU as [Hg Cg] | dand3 GU as g Hg Cg | destruct GU as (g & Hg & Cg) ]). exists g. split; [exact Hg|]. apply (cell8_agree m m'); [intros i Hi; apply EU; lia| exact Cg]. }
  split; [exact HZ'|].
  repeat (split; [assumption|]).
  (* [comment removed for export] *) eapply ceil_ok_same_vmmaps; [exact EVMM| exact CEILOK].
Qed.

End CEIL.
