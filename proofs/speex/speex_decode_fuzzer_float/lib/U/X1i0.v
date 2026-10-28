(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
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
/\ lsp_order (sm_lsp_unquant sm) = 10 /\ In r nb_smrecs /\ 0x3b6f8 <= smr_ptr r <= 0x3ba90 /\ sub_ptr mo = smr_ptr r.
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
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x20f20) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m (set_nb_submodeID st0 mo) b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ smrec_at mo = Some r /\ j_exc j = ST + 1368.

Definition at_D2 (r : smrec) (mo olp : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 (Z_to_bv 64 olp)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x2120c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ smrec_at mo = Some r /\ j_exc j = ST + 1368 /\ nb_submodeID st = mo
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ nb_innov_save st = nb_innov_save (x_st0 X).

Ltac nbred_all :=
cbn [nb_first nb_count_lost nb_sampling_rate nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID
nb_lpc_enh_enabled nb_stereo_cb nb_voc_offset nb_dtx_enabled nb_isWideband nb_highpass_enabled nb_isave_ptr
set_nb_first set_nb_count_lost set_nb_submodeID set_nb_voc_offset set_nb_dtx_enabled set_nb_pitch_gain_buf_idx] in *.

Local Ltac ucond_rw := unfold_cond; fold_lit_ux; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Local Ltac uif b := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
replace c with b; [cbv iota | symmetry; ucond_rw; solve_cond_rec] end.
Local Ltac cpy b := zstep; uif true; zstep; step; zstep; zstep; zstep; step; zstep; uif b.

#[using="notify STR_TOP NH"] Lemma nbC : forall r mo b ms, at_C X r mo b ms -> evt rsegs (at_D1 r mo b) ms.
Proof.
intros r mo b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m k xra xa0 xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 SAT JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs2 & xs3 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & SAT & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK. nbred_all.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ]. cbn in Icl, Ies, Ihp, Ifi, Ivo, Iix, Idt, Iwb, Ien, Isr, Iis.
pose proof (h_sthi _ _ _ NH) as STHI. unfold NBSTATE_SIZEOF in STHI.
zstep. rewrite E88. zstep. rewrite Icl. zstep. lstep. zstep. lstep. zstep. uif true.
zstep. rewrite E88. zstep. destruct Ifi as [EF | EF]; rewrite EF; zstep; zstep.
-
uif true. apply evt_done. close_cut 12.
-
uif false. zstep. zstep. zstep. zstep. zstep.
remember (f_ql fr) as ql eqn:Eql.
destruct ql as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|q8 [|q9 [|qq ql']]]]]]]]]]]; try (cbn in Lfql; lia).
rewrite !f32_cons, f32_nil in FS.
remember (j_old_qlsp j) as oq eqn:Eoq.
destruct oq as [|o0 [|o1 [|o2 [|o3 [|o4 [|o5 [|o6 [|o7 [|o8 [|o9 [|oo oq']]]]]]]]]]]; try (cbn in Loq; lia).
rewrite !f32_cons, f32_nil in P3.
rewrite zb_lxor_ones by lia.
cpy true. cpy true. cpy true. cpy true. cpy true. cpy true. cpy true. cpy true. cpy true. cpy false.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of P3 with rw_cells _ _ _ [C4 ?v0; C4 ?v1; C4 ?v2; C4 ?v3; C4 ?v4; C4 ?v5; C4 ?v6; C4 ?v7; C4 ?v8; C4 ?v9] =>
assert (P3' : rw_cells rsegs mm (ST + 2040) (f32 [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9])) by (rewrite !f32_cons, f32_nil; exact P3) end;
assert (FS' : rw_cells rsegs mm (usp + -256) (f32 [q0; q1; q2; q3; q4; q5; q6; q7; q8; q9])) by (rewrite !f32_cons, f32_nil; exact FS)
end.
clear P3 FS. rename P3' into P3. rename FS' into FS.
lazymatch type of P3 with rw_cells _ _ _ (f32 ?l) => assert (Loq' : length l = 10%nat) by reflexivity end.
apply evt_done. close_cut 12.
Qed.
End Seg.
