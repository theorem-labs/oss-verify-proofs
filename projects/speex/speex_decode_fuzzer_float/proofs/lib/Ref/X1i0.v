(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma smrec_at_cases : forall mo r, smrec_at mo = Some r ->
(mo = 1 /\ r = nb_smrec1) \/ (mo = 2 /\ r = nb_smrec2) \/ (mo = 3 /\ r = nb_smrec3) \/ (mo = 4 /\ r = nb_smrec4) \/
(mo = 5 /\ r = nb_smrec5) \/ (mo = 6 /\ r = nb_smrec6) \/ (mo = 7 /\ r = nb_smrec7) \/ (mo = 8 /\ r = nb_smrec8).
Proof.
intros mo r E. pose proof (smrec_at_in mo r E) as (_ & _ & Hm).
assert (C : mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn in E; injection E as <-; tauto.
Qed.

Lemma smrec_facts : forall mo r, smrec_at mo = Some r ->
let sm := smr_sm r in
((sm_lbr_pitch sm = 0 /\ sm_forced_pitch_gain sm = 1 /\ (mo = 1 \/ mo = 8))
\/ (sm_lbr_pitch sm = 0 /\ sm_forced_pitch_gain sm = 0 /\ mo = 2)
\/ (sm_lbr_pitch sm = -1 /\ sm_forced_pitch_gain sm = 0 /\ 3 <= mo <= 7))
/\ lsp_order (sm_lsp_unquant sm) = 10 /\ In r nb_smrecs /\ 0x341e8 <= smr_ptr r <= 0x34580 /\ sub_ptr mo = smr_ptr r.
Proof.
intros mo r E.
destruct (smrec_at_cases mo r E) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; cbn; intuition lia.
Qed.

Lemma seqz15 : forall u, 0 <= u < 16 -> Z.b2z ((u + -15) mod 18446744073709551616 <? 1) = (if u =? 15 then 1 else 0).
Proof.
intros u Hu. destruct (Z.eq_dec u 15) as [-> | NE]; [reflexivity|].
replace ((u + -15) mod 18446744073709551616) with (u + -15 + 18446744073709551616)
by (apply Z.mod_unique with (q := -1); lia).
replace (u =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (u + -15 + 18446744073709551616 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Section Pure.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Definition segD_olp (sm : submode) (b : bits_st ptr) : Z :=
if negb (sm_lbr_pitch sm =? -1) then uv b 7 + 17 else 0.
Definition segD_b1 (sm : submode) (b : bits_st ptr) : bits_st ptr :=
if negb (sm_lbr_pitch sm =? -1) then ub b 7 else b.
Definition segD_b2 (sm : submode) (b : bits_st ptr) : bits_st ptr :=
if negb (sm_forced_pitch_gain sm =? 0) then ub (segD_b1 sm b) 4 else segD_b1 sm b.
Definition segD_b3 (sm : submode) (b : bits_st ptr) : bits_st ptr := ub (segD_b2 sm b) 5.
Definition segD_st (st : nb_state ptr) (sm : submode) (b : bits_st ptr) : nb_state ptr :=
if nb_submodeID st =? 1 then set_nb_dtx_enabled st (if uv (segD_b3 sm b) 4 =? 15 then 1 else 0)
else if 1 <? nb_submodeID st then set_nb_dtx_enabled st 0 else st.
Definition segD_bits (st : nb_state ptr) (sm : submode) (b : bits_st ptr) : bits_st ptr :=
if nb_submodeID st =? 1 then ub (segD_b3 sm b) 4 else segD_b3 sm b.
End Pure.

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

Definition at_D1 (r : smrec) (mo : Z) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs3 xs4 xs8 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 A) xs3 xs4 (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 OUT) (Z_to_bv 64 0) xs8 (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 ST) (Z_to_bv 64 mo)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1f230) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m (set_nb_submodeID st0 mo) b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v56 fr = Z_to_bv 64 OUT /\ f_v64 fr = Z_to_bv 64 0x1008c /\ f_v104 fr = Z_to_bv 64 A /\ f_v112 fr = Z_to_bv 64 0
/\ smrec_at mo = Some r /\ j_exc j = ST + 1368.

Definition at_D2 (r : smrec) (mo olp : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs3 xs4 xs8 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 A) xs3 xs4 (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 OUT) (Z_to_bv 64 0) xs8 (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 olp) (Z_to_bv 64 mo)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1f30c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v56 fr = Z_to_bv 64 OUT /\ f_v64 fr = Z_to_bv 64 0x1008c /\ f_v88 fr = Z_to_bv 64 ST /\ f_v104 fr = Z_to_bv 64 A /\ f_v112 fr = Z_to_bv 64 0
/\ smrec_at mo = Some r /\ j_exc j = ST + 1368 /\ nb_submodeID st = mo
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ nb_innov_save st = nb_innov_save (x_st0 X).

Ltac nbred_all :=
cbn [nb_first nb_count_lost nb_sampling_rate nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID
nb_lpc_enh_enabled nb_stereo_cb nb_voc_offset nb_dtx_enabled nb_isWideband nb_highpass_enabled nb_isave_ptr
set_nb_first set_nb_count_lost set_nb_submodeID set_nb_voc_offset set_nb_dtx_enabled set_nb_pitch_gain_buf_idx] in *.

#[using="notify STR_TOP NH"] Lemma nbC : forall r mo b ms, at_C X r mo b ms -> evt rsegs (at_D1 r mo b) ms.
Proof.
intros r mo b ms AT.
first [ sf_destruct 24%nat AT as Fx fc m k xra xa0 xs3 xs4 xs8 j ows iws sws fr -> FRM CTX FOK FRA E56 E104 E112 SAT JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs3 & xs4 & xs8 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E56 & E104 & E112 & SAT & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK. nbred_all.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ]. cbn in Icl, Ies, Ihp, Ifi, Ivo, Iix, Idt, Iwb, Ien, Isr, Iis.
zstep. rewrite Icl. zstep. lstep. zstep. if_true.
zstep. destruct Ifi as [EF | EF]; rewrite EF; zstep.
-
if_true. apply evt_done. close_cut 5.
-
if_false. zstep. zstep. zstep. zstep.
pose proof (f32_as_blob _ _ _ 10%nat P3 Loq) as DSTB. clear P3.
pose proof (rw_cells_bound _ _ _ _ DSTB) as BD. cbn [cells_size csize Nat.add Z.to_nat Z.of_nat Pos.to_nat Pos.iter_op Nat.mul] in BD.
call (nmemcpy_specZ (ST + 2040) (usp + -256) 40 (cells_bytes (f32 (f_ql fr))) _);
[ apply f32_bytes_at; exact FS | rewrite f32_bytes_length, Lfql; reflexivity | exact DSTB
| pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. try clear DSTB.
match goal with H : rw_cells _ ?mm (ST + 2040) [CB _ _] |- _ =>
assert (P3 : rw_cells rsegs mm (ST + 2040) (f32 (f_ql fr)))
by (eapply rw_cells_recast; [exact H | apply cells_wf_f32 | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]);
clear H end.
match goal with H : bytes_at _ _ (usp + -256) _ |- _ => clear H end.
apply evt_done. close_cut 5.
Qed.
End Seg.
