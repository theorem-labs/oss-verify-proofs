(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3 X1i4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma scal3_cell : forall m q, mem_inv rsegs m -> 0 <= q < 8 -> exists bs, length bs = 4%nat /\ ro_cells rsegs m (68700 + 4 * q) [CB 4 bs].
Proof.
intros m q MI Hq. assert (C : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
- exists [Z_to_bv 8 115; Z_to_bv 8 99; Z_to_bv 8 122; Z_to_bv 8 61]. split; [reflexivity|]. change (68700 + 4 * 0) with 68700.
apply (ro_cells_image rsegs m 68700 [Z_to_bv 8 115; Z_to_bv 8 99; Z_to_bv 8 122; Z_to_bv 8 61] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 154; Z_to_bv 8 120; Z_to_bv 8 39; Z_to_bv 8 62]. split; [reflexivity|]. change (68700 + 4 * 1) with 68704.
apply (ro_cells_image rsegs m 68704 [Z_to_bv 8 154; Z_to_bv 8 120; Z_to_bv 8 39; Z_to_bv 8 62] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 116; Z_to_bv 8 238; Z_to_bv 8 158; Z_to_bv 8 62]. split; [reflexivity|]. change (68700 + 4 * 2) with 68708.
apply (ro_cells_image rsegs m 68708 [Z_to_bv 8 116; Z_to_bv 8 238; Z_to_bv 8 158; Z_to_bv 8 62] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 167; Z_to_bv 8 63; Z_to_bv 8 219; Z_to_bv 8 62]. split; [reflexivity|]. change (68700 + 4 * 3) with 68712.
apply (ro_cells_image rsegs m 68712 [Z_to_bv 8 167; Z_to_bv 8 63; Z_to_bv 8 219; Z_to_bv 8 62] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 156; Z_to_bv 8 78; Z_to_bv 8 14; Z_to_bv 8 63]. split; [reflexivity|]. change (68700 + 4 * 4) with 68716.
apply (ro_cells_image rsegs m 68716 [Z_to_bv 8 156; Z_to_bv 8 78; Z_to_bv 8 14; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 253; Z_to_bv 8 19; Z_to_bv 8 56; Z_to_bv 8 63]. split; [reflexivity|]. change (68700 + 4 * 5) with 68720.
apply (ro_cells_image rsegs m 68720 [Z_to_bv 8 253; Z_to_bv 8 19; Z_to_bv 8 56; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 64; Z_to_bv 8 78; Z_to_bv 8 112; Z_to_bv 8 63]. split; [reflexivity|]. change (68700 + 4 * 6) with 68724.
apply (ro_cells_image rsegs m 68724 [Z_to_bv 8 64; Z_to_bv 8 78; Z_to_bv 8 112; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 2; Z_to_bv 8 215; Z_to_bv 8 169; Z_to_bv 8 63]. split; [reflexivity|]. change (68700 + 4 * 7) with 68728.
apply (ro_cells_image rsegs m 68728 [Z_to_bv 8 2; Z_to_bv 8 215; Z_to_bv 8 169; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
Qed.
Lemma scal1_cell : forall m q, mem_inv rsegs m -> 0 <= q < 2 -> exists bs, length bs = 4%nat /\ ro_cells rsegs m (68736 + 4 * q) [CB 4 bs].
Proof.
intros m q MI Hq. assert (C : q = 0 \/ q = 1) by lia.
destruct C as [-> | ->].
- exists [Z_to_bv 8 144; Z_to_bv 8 102; Z_to_bv 8 52; Z_to_bv 8 63]. split; [reflexivity|]. change (68736 + 4 * 0) with 68736.
apply (ro_cells_image rsegs m 68736 [Z_to_bv 8 144; Z_to_bv 8 102; Z_to_bv 8 52; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 4; Z_to_bv 8 144; Z_to_bv 8 134; Z_to_bv 8 63]. split; [reflexivity|]. change (68736 + 4 * 1) with 68740.
apply (ro_cells_image rsegs m 68740 [Z_to_bv 8 4; Z_to_bv 8 144; Z_to_bv 8 134; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
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
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs5 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (isv_sub X sub st)) (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 1) (Z_to_bv 64 (usp + -416)) (Z_to_bv 64 (ST + 1368)) xs5 (Z_to_bv 64 160) (Z_to_bv 64 (ST + 1368 + 160 * sub))
(Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 bp2) (Z_to_bv 64 olp)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21864) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v72 fr = Z_to_bv 64 (ST + 2228)
/\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (40 * sub)
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ f_v128 fr = Z_to_bv 64 (olp + 1073741824)
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144 /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

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
intros r mo olp bp bp2 sub st b ms AT.
first [ sf_destruct 35%nat AT as Fx fc m kc xra xa0 xs5 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E72 E80 E88 E96 E104 E112 E120 E128 JEXC SAT SID BP BP2 OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs5 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E72 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & JEXC & SAT & SID & BP & BP2 & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
box OLP.
pose proof (smrec_sub_facts mo r SAT) as sfP_; first [ sf_destruct 16%nat sfP_ as k ki HK HKI _ _ HSG _ _ INr SPlo SPE _ _ _ _ | sf_fb; destruct sfP_ as (k & ki & HK & HKI & _ & _ & HSG & _ & _ & INr & SPlo & SPE & _ & _ & _ & _) ].
pose proof (smrec_at_in mo r SAT) as (_ & _ & Hmo).
pose proof (h_sp16 _ _ _ NH) as SP16. pose proof (h_stal _ _ _ NH) as STAL. pose proof (smr_ptr_al8 r INr) as SPAL.

zstep. zstep. zstep. zstep.
pose proof (rw_cells_bound _ _ _ _ FI) as BFI. rewrite cells_size_f32, Lfinn in BFI.
pose proof (f32_as_blob _ _ _ 40%nat FI Lfinn) as FIB. clear FI.
call (nmemset_specZ (usp + -416) 160 0 _ _); [exact FIB | assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. clear BFI.
match goal with H : rw_cells _ ?mm (usp + -416) [CB _ _] |- _ =>
destruct (rw_cells_CB_f32 rsegs _ _ 40 _ H) as (inn0 & Linn0 & FI); clear H end.

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC.
unfold smrec_cells in SMC. cbv zeta in SMC.
pose proof (ro_cells_bound _ _ _ _ SMC) as SMB. cbn [cells_size csize Nat.add] in SMB.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR. rewrite SPE in SPR. clear TAB TB2.
unfold NB_SUBMODES_PTR in P14.
zstep. rewrite SID. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. rewrite (Z.mul_comm mo 8).
bato 0x217e0%Z.
zstep.
bato 0x217f0%Z.
zstep.
unfold hsg_bits.
destruct HSG as [EH | [EH | EH]]; rewrite EH; cbn [Z.eqb Pos.eqb].
-
zstep. zstep. if_false. step. zstep. zstep. if_true.
apply evt_done. unfold boxed in OLP. close_cut 3.
-
zstep. zstep. if_true. zstep. zstep. rewrite E112. zstep. do_unpack b 1.
bato 0x21840%Z.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
bato 0x21854%Z.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep.
destruct (scal1_cell _ (uv b 1) MI ltac:(lia)) as (tbs & Ltbs & TRO).
replace (68736 + uv b 1 * 4) with (68736 + 4 * uv b 1) by lia.
remember (68736 + 4 * uv b 1) as TQ eqn:ETQ.
step. subst TQ. clear TRO. step.
apply evt_done. unfold boxed in OLP. close_cut 3.
-
zstep. zstep. if_false. step. zstep. zstep. if_false.
zstep. zstep. rewrite E112. zstep. do_unpack b 3.
bato 0x2181c%Z.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
bato 0x21854%Z.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep.
destruct (scal3_cell _ (uv b 3) MI ltac:(lia)) as (tbs & Ltbs & TRO).
replace (68700 + uv b 3 * 4) with (68700 + 4 * uv b 3) by lia.
remember (68700 + 4 * uv b 3) as TQ eqn:ETQ.
step. subst TQ. clear TRO. step.
apply evt_done. unfold boxed in OLP. close_cut 3.
Qed.
End Seg.
