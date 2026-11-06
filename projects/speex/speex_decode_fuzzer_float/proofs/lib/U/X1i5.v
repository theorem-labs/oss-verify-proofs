(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3 X1i4.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma scal3_cell : forall m q, mem_inv rsegs m -> 0 <= q < 8 -> exists bs, length bs = 4%nat /\ ro_cells rsegs m (68700 + 4 * q) [CB 4 bs].
Proof.
intros m q MEM QR.
pose (slot := fun i => match image_bytes rsegs (68700 + 4 * i) 4 with Some raw => raw | None => [] end).
assert (TABLE : forallb (fun i => (length (slot i) =? 4)%nat && ro_bytes_b rsegs (68700 + 4 * i) (slot i))
  (map Z.of_nat (seq 0 8)) = true) by (subst slot; vm_compute; reflexivity).
assert (IDX : In q (map Z.of_nat (seq 0 8))).
{ apply in_map_iff. exists (Z.to_nat q). split; [lia|]. apply in_seq. lia. }
rewrite forallb_forall in TABLE. apply TABLE, andb_true_iff in IDX. destruct IDX as [WIDTH ROM].
apply Nat.eqb_eq in WIDTH.
exists (slot q). split; [exact WIDTH|].
pose proof (ro_cells_image rsegs m _ _ MEM ROM ltac:(lia) ltac:(rewrite WIDTH; lia)) as CELL.
rewrite WIDTH in CELL. exact CELL.
Qed.
Lemma scal1_cell : forall m q, mem_inv rsegs m -> 0 <= q < 2 -> exists bs, length bs = 4%nat /\ ro_cells rsegs m (68736 + 4 * q) [CB 4 bs].
Proof.
intros m q MEM QR.
pose (slot := fun i => match image_bytes rsegs (68736 + 4 * i) 4 with Some raw => raw | None => [] end).
assert (TABLE : forallb (fun i => (length (slot i) =? 4)%nat && ro_bytes_b rsegs (68736 + 4 * i) (slot i))
  (map Z.of_nat (seq 0 2)) = true) by (subst slot; vm_compute; reflexivity).
assert (IDX : In q (map Z.of_nat (seq 0 2))).
{ apply in_map_iff. exists (Z.to_nat q). split; [lia|]. apply in_seq. lia. }
rewrite forallb_forall in TABLE. apply TABLE, andb_true_iff in IDX. destruct IDX as [WIDTH ROM].
apply Nat.eqb_eq in WIDTH.
exists (slot q). split; [exact WIDTH|].
pose proof (ro_cells_image rsegs m _ _ MEM ROM ltac:(lia) ltac:(rewrite WIDTH; lia)) as CELL.
rewrite WIDTH in CELL. exact CELL.
Qed.

Lemma smr_ptr_al8 : forall r, In r nb_smrecs -> smr_ptr r mod 8 = 0.
Proof. intros r Hr. unfold nb_smrecs in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr. Qed.

Section Seg.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable notify : list Z -> X1qx.M PState unit.
Variable STR_TOP : Z.
Variable X : nbinv ptr.
Hypothesis NH : nb_hyps notify STR_TOP X.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation ISV := (x_isv X). Local Notation lo := (x_lo X).
Local Notation st0 := (x_st0 X). Local Notation b0 := (x_b0 X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X). Local Notation canary := (x_canary X).
Local Notation usp := (bv_unsigned (x_sp X)).

Definition at_E3b (r : smrec) (mo olp bp bp2 sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (fv : bvmap 5 word) (fcsr : bv 32) (mem1 : mem) (cl : iclob) (wra wa0 ws5 : word)
  (jk : nb_junk) (outw isvw stw : list word) (fm : frame),
ms = MS (mkR wra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 cl) (c_t1 cl) (c_t2 cl)
      (Z_to_bv 64 (isv_sub X sub st)) (Z_to_bv 64 (usp + -256))
      wa0 (c_a1 cl) (c_a2 cl) (c_a3 cl) (c_a4 cl) (c_a5 cl) (c_a6 cl) (c_a7 cl)
      (Z_to_bv 64 1) (Z_to_bv 64 (usp + -416)) (Z_to_bv 64 (ST + 1368)) ws5 (Z_to_bv 64 160)
      (Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 bp2) (Z_to_bv 64 olp)
      (c_t3 cl) (c_t4 cl) (c_t5 cl) (c_t6 cl))
    fv (Z_to_bv 64 0x21864) fcsr None mem1 (seg_rom rsegs)
/\ frm0 fcsr /\ nbctx X mem1 st b jk outw isvw stw /\ frame_ok fm /\ frame_at X mem1 fm
/\ f_v48 fm = Z_to_bv 64 (ST + 2047) /\ f_v56 fm = Z_to_bv 64 69156 /\ f_v72 fm = Z_to_bv 64 (ST + 2228)
/\ f_v80 fm = Z_to_bv 64 OUT /\ f_v88 fm = Z_to_bv 64 ST /\ f_v96 fm = Z_to_bv 64 (40 * sub)
/\ f_v104 fm = Z_to_bv 64 (ST + 2040) /\ f_v112 fm = Z_to_bv 64 A /\ f_v120 fm = Z_to_bv 64 0
/\ f_v128 fm = Z_to_bv 64 (olp + 1073741824) /\ j_exc jk = ST + 1368
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144 /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save st0.

Ltac do_unpack b n :=
call (X1g7.speex_bits_unpack_unsigned_spec A D b n); [eassumption | eassumption | lia | eassumption |];
rewrite (unpack_eta b n) in *; cbn [fst snd] in *;
try rename MI0 into MI;
match goal with H : bits_rep _ _ _ _ (ub b n) |- _ => rename H into REP end;
match goal with H : ?v = Z_to_bv 64 (uv b n) |- _ => subst v end;
lazymatch goal with BOK : bits_ok b |- _ =>
let B1 := fresh "BOK" in let R1 := fresh "Huv" in let S1 := fresh "Hbs" in
pose proof (speex_bits_unpack_unsigned_ok b n _ _ BOK ltac:(lia) (unpack_eta b n)) as sfP_; sf_curry 6%nat sfP_; intros B1 R1 _ _ S1 _; sf_clear sfP_; sf_fix_order
end.

#[using="notify STR_TOP NH"] Lemma nbE3a : forall r mo olp bp bp2 sub st b ms, at_E3 X r mo olp bp bp2 sub st b ms ->
evt rsegs (at_E3b r mo olp bp bp2 sub st (hsg_bits (smr_sm r) b)) ms.
Proof.
intros r mo olp bp bp2 sub st b ms PRE.
sf_destruct 35%nat PRE as fv fcsr mem1 cl wra wa0 ws5 jk outw isvw stw fm -> RNDM NBC FROK FRAT
  V48 V56 V72 V80 V88 V96 V104 V112 V120 V128 EXCP SMR SMID BPR BP2R OLPR SUBR ISV0.
open_hyps NH. open_ctx NBC. open_frame FRAT. open_fok FROK.
destruct (smrec_at_in mo r SMR) as (INr & _ & MOR).
destruct (smrec_sub_facts mo r SMR) as (_ & _ & _ & _ & _ & _ & HSG & _ & _ & _ & PTRR & SUBPTR & _).
pose proof (smr_ptr_al8 r INr) as AL8.
zstep. zstep. zstep. zstep.
call (nmemset_specZ (usp + -416) 160 0 (cells_bytes (f32 (f_inn fm))));
  [ exact (f32_as_blob _ _ _ 40 FI Lfinn) | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI.
lazymatch goal with ZERO : rw_cells _ ?mz (usp + -416) [CB _ _] |- _ =>
  change (Z.to_nat 160) with (4 * 40)%nat in ZERO;
  destruct (rw_cells_CB_f32 rsegs mz _ 40 _ ZERO) as (zinn & Lzinn & FI); clear ZERO
end.
pose proof (ctx_tables _ _ X NH _ MU) as TAB.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SUBP. unfold NB_SUBMODES_PTR in SUBP.
pose proof (proj1 (proj2 TAB) r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC.
zstep. rewrite SMID, sx32_ssmall by lia.
zstep. unfold NB_SUBMODES_PTR.
zstep. rewrite (Z.shiftl_mul_pow2 mo 3) by lia. replace (mo * 2 ^ 3) with (8 * mo) by lia.
zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. rewrite (lxor_sign_nn mo) by lia. if_false_z.
zstep. if_false_z. zstep. zstep. if_false_z.
zstep. rewrite SUBPTR. zstep. if_false_z. zstep. zstep. if_false_z.
zstep.
destruct (Z.eq_dec (sm_have_subframe_gain (smr_sm r)) 1) as [GAIN1 | GAIN_NOT1].
- rewrite GAIN1, sx32_ssmall by lia. zstep. zstep. if_true_z.
  zstep. zstep. rewrite V112. zstep.
  do_unpack b 1.
  destruct (scal1_cell _ (uv b 1) MI ltac:(lia)) as (gbytes & Lg & GCELL).
  zstep. zstep. if_false_z. zstep.
  rewrite (Z.shiftl_mul_pow2 (uv b 1) 2) by lia. replace (uv b 1 * 2 ^ 2) with (4 * uv b 1) by lia.
  zstep. zstep. zstep. zstep. if_false_z. zstep.
  rewrite (Z.shiftl_mul_pow2 (uv b 1) 2) by lia. replace (uv b 1 * 2 ^ 2) with (4 * uv b 1) by lia.
  zstep. set (gaddr := 68736 + 4 * uv b 1) in *. zstep. zstep.
  replace (hsg_bits (smr_sm r) b) with (ub b 1) by (unfold hsg_bits; rewrite GAIN1; reflexivity).
  apply evt_done. close_cut 3.
- rewrite sx32_ssmall by lia. zstep. zstep. if_false_z. zstep. zstep. zstep.
  destruct (Z.eq_dec (sm_have_subframe_gain (smr_sm r)) 3) as [GAIN3 | GAIN_NOT3].
  + rewrite GAIN3. if_false_z. zstep. zstep. rewrite V112. zstep.
    do_unpack b 3.
    destruct (scal3_cell _ (uv b 3) MI ltac:(lia)) as (gbytes & Lg & GCELL).
    zstep. zstep. if_false_z. zstep.
    rewrite (Z.shiftl_mul_pow2 (uv b 3) 2) by lia. replace (uv b 3 * 2 ^ 2) with (4 * uv b 3) by lia.
    zstep. zstep. zstep. zstep. zstep. if_false_z. zstep.
    rewrite (Z.shiftl_mul_pow2 (uv b 3) 2) by lia. replace (uv b 3 * 2 ^ 2) with (4 * uv b 3) by lia.
    zstep. set (gaddr := 68700 + 4 * uv b 3) in *. zstep. zstep.
    replace (hsg_bits (smr_sm r) b) with (ub b 3) by (unfold hsg_bits; rewrite GAIN3; reflexivity).
    apply evt_done. close_cut 3.
  + assert (GAIN0 : sm_have_subframe_gain (smr_sm r) = 0) by lia.
    rewrite GAIN0. if_true_z.
    replace (hsg_bits (smr_sm r) b) with b by (unfold hsg_bits; rewrite GAIN0; reflexivity).
    apply evt_done. close_cut 3.
Qed.
End Seg.
