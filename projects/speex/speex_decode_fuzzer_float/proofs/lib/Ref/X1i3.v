(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1hn X1hp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma smrec_at_cases_E : forall mo r, smrec_at mo = Some r ->
(mo = 1 /\ r = nb_smrec1) \/ (mo = 2 /\ r = nb_smrec2) \/ (mo = 3 /\ r = nb_smrec3) \/ (mo = 4 /\ r = nb_smrec4) \/
(mo = 5 /\ r = nb_smrec5) \/ (mo = 6 /\ r = nb_smrec6) \/ (mo = 7 /\ r = nb_smrec7) \/ (mo = 8 /\ r = nb_smrec8).
Proof.
intros mo r E. pose proof (smrec_at_in mo r E) as (_ & _ & Hm).
assert (C : mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn in E; injection E as <-; tauto.
Qed.

Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox H := unfold boxed in H.

Lemma sx32_ssmall : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sx32. rewrite Z_to_bv_unsigned.
replace (bv_swrap 32 (bv_wrap 64 v)) with v; [reflexivity|].
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (4294967296 / 2) with 2147483648.
symmetry. Z.to_euclidean_division_equations. lia.
Qed.

Definition ltp_bits_nonneg (k : ltp_kind) : Prop :=
match k with LtpPitchUnquant3tap p => 0 <= ltp_pitch_bits p | LtpForcedPitchUnquant => True end.

Lemma smrec_sub_facts : forall mo r, smrec_at mo = Some r ->
let sm := smr_sm r in
exists k ki, sm_ltp_unquant sm = Some k /\ sm_innovation_unquant sm = Some ki
/\ ((sm_lbr_pitch sm = -1 /\ 17 + ltp_pitch_span k <= 144) \/ (sm_lbr_pitch sm = 0 /\ ltp_pitch_span k = 0))
/\ ltp_bits_nonneg k
/\ (sm_have_subframe_gain sm = 0 \/ sm_have_subframe_gain sm = 1 \/ sm_have_subframe_gain sm = 3)
/\ (sm_double_codebook sm = 0 \/ sm_double_codebook sm = 1 /\ mo = 7)
/\ (mo = 1 <-> k = LtpForcedPitchUnquant /\ ki = InnovNoiseCodebookUnquant)
/\ In r nb_smrecs /\ 0x341e8 <= smr_ptr r <= 0x34580 /\ sub_ptr mo = smr_ptr r
/\ 0 < ltp_entry k < 2^64 /\ ltp_entry k mod 2 = 0 /\ 0 < innov_entry ki < 2^64 /\ innov_entry ki mod 2 = 0.
Proof.
intros mo r E.
destruct (smrec_at_cases_E mo r E) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]];
cbn -[Z.pow Z.lt Z.le Z.add Z.modulo]; sf_eexists 2%nat; (split; [reflexivity|]); (split; [reflexivity|]);
unfold A_forced_pitch_unquant, A_pitch_unquant_3tap, A_noise_codebook_unquant, A_split_cb_shape_sign_unquant;
cbn; intuition (try lia; try discriminate).
all: unfold A_forced_pitch_unquant, A_pitch_unquant_3tap, A_noise_codebook_unquant, A_split_cb_shape_sign_unquant; lia.
Qed.

Lemma ltp_pitch_range : forall {ptr} (k : ltp_kind) start (b : bits_st ptr),
bits_ok b -> ltp_bits_nonneg k -> 17 <= start -> start + ltp_pitch_span k <= 144 -> 17 <= ltp_pitch k start b <= 144.
Proof.
intros ptr k start b OK NN H1 H2. destruct k as [|p]; cbn [ltp_pitch ltp_pitch_span ltp_bits_nonneg] in *; [lia|].
unfold ltp3_pitch, uv.
pose proof (speex_bits_unpack_unsigned_ok b (ltp_pitch_bits p) _ _ OK NN (unpack_eta b _)) as (_ & R & _).
unfold uv in R. lia.
Qed.

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

Definition at_E2 (r : smrec) (mo olp bp sub pit : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 4) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 (160 * sub)) (Z_to_bv 64 (nb_isave_ptr OUT st)) (Z_to_bv 64 (40 * sub)) (Z_to_bv 64 bp) (Z_to_bv 64 (ST + 1368)) (Z_to_bv 64 (ST + 1368 + 160 * sub))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -576)) (Z_to_bv 64 olp) (Z_to_bv 64 sub)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1f4ac) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 OUT /\ f_v64 fr = Z_to_bv 64 0x1008c
/\ f_v80 fr = Z_to_bv 64 (ST + 2228) /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (160 * sub)
/\ f_v104 fr = Z_to_bv 64 A /\ f_v112 fr = Z_to_bv 64 0 /\ f_pv fr = Z_to_bv 64 pit
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144 /\ 17 <= pit <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Ltac e1_args :=
zstep; zstep;
lazymatch goal with E88 : f_v88 _ = _ |- _ => rewrite E88 end; zstep;
lazymatch goal with Icl : nb_count_lost _ = 0 |- _ => rewrite Icl end; change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0);
step; lstep; zstep; zstep; zstep; zstep;
zstep; lazymatch goal with E104 : f_v104 _ = _ |- _ => rewrite E104 end; zstep;
zstep; lazymatch goal with E112 : f_v112 _ = _ |- _ => rewrite E112 end; lstep;
lstep; zstep; zstep; step; zstep;
lazymatch goal with EK1 : 0 < ltp_entry ?k < _, EK2 : ltp_entry ?k mod 2 = 0 |- _ =>
replace (ret_pc (Z_to_bv 64 (ltp_entry k))) with (Z_to_bv 64 (ltp_entry k)) by (symmetry; apply ret_pc_even; [lia | exact EK2]) end.

Ltac e1_close k start :=
cbv beta delta [callR]; try rename MI0 into MI; unfold boxed in *;
lazymatch goal with USP : bv_unsigned _ = _ |- _ => rewrite USP in * end;

lazymatch goal with FA : rw_cells _ ?mm (_ + -896) [C8 ?a0; C8 ?a1; C8 ?a2; C8 ?a3; C8 ?a4], FA6 : rw_cells _ ?mm' (_ + -856) [C8 ?a5] |- _ =>
chunk_cat FA FA6 end;
lazymatch goal with G : rw_cells _ ?mm (_ + -216) (f32 ?pg), L : length ?pg = 3%nat, V : rw_cells _ ?mm' (_ + -204) [C4 ?pv] |- _ =>
destruct pg as [|g0 [|g1 [|g2 [|gx grest]]]]; try (cbn in L; lia);
rewrite !f32_cons, f32_nil in G; chunk_cat G V; clear L; rename G into FP end;
match goal with Lx : length ?eb0 = 500%nat, L : length ?eb' = length ?eb0 |- _ => rewrite Lx in L end;
lazymatch goal with B : bits_ok (ltp_bits k ?bb) |- _ =>
lazymatch goal with B0 : bits_ok bb, KN : ltp_bits_nonneg k |- _ =>
pose proof (ltp_pitch_range k start bb B0 KN ltac:(lia) ltac:(lia)) as PR end end;
apply evt_done; eexists; close_cut 2.

#[using="notify STR_TOP NH"] Lemma nbE1 : forall r mo olp bp sub st b k ms, at_E X r mo olp bp sub st b ms -> sub < 4 ->
sm_ltp_unquant (smr_sm r) = Some k ->
evt rsegs (fun ms' => exists pit, at_E2 r mo olp bp sub pit st (ltp_bits k b) ms') ms.
Proof.
intros r mo olp bp sub st b k ms AT Hsub HK.
first [ sf_destruct 35%nat AT as Fx fc m kc xra xa0 xs3 xs4 xs6 xs7 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E64 E80 E88 E96 E104 E112 JEXC SAT SID BP OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs3 & xs4 & xs6 & xs7 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & JEXC & SAT & SID & BP & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof INV as (Icl & _).
pose proof (smrec_sub_facts mo r SAT) as sfP_; first [ sf_destruct 16%nat sfP_ as k' ki HK' HKI SPAN KNN _ _ _ INr SPlo SPE EK1 EK2 EI1 EI2 | sf_fb; destruct sfP_ as (k' & ki & HK' & HKI & SPAN & KNN & _ & _ & _ & INr & SPlo & SPE & EK1 & EK2 & EI1 & EI2) ].
rewrite HK in HK'. injection HK' as <-. clear EI1 EI2 HKI ki.
pose proof (smrec_at_in mo r SAT) as (_ & _ & Hmo).

box SPAN. box OLP.

zstep. rewrite E88. zstep. rewrite JEXC. zstep. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep.
zstep. zstep. zstep. zstep.
replace (sub * 40 * 4) with (160 * sub) by lia. replace (sub * 40) with (40 * sub) by lia.
first [ pose proof (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as sfP_; sf_destruct 6%nat sfP_ as PE1 PE2 PE3 LE1 LE2 LE3 | sf_fb; destruct (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as (PE1 & PE2 & PE3 & LE1 & LE2 & LE3) ]. clear P1.
rewrite Z2Nat.id in PE2, PE3 by lia. rewrite Lexc in LE3.
replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) in PE2, PE3 by lia.
pose proof (rw_cells_bound _ _ _ _ PE2) as BPE. rewrite cells_size_f32, LE2 in BPE.
pose proof (f32_as_blob _ _ _ 40%nat PE2 LE2) as PEB. clear PE2.
call (nmemset_specZ (ST + 1368 + 160 * sub) 160 0 _ _); [exact PEB | assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. clear BPE.
match goal with H : rw_cells _ ?mm (ST + 1368 + 160 * sub) [CB _ _] |- _ =>
destruct (rw_cells_CB_f32 rsegs _ _ 40 _ H) as (ez & Lez & PE2); clear H end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
destruct (f32_join3 rsegs mm (ST + 32) (firstn (Z.to_nat (334 + 40 * sub)) (j_excbuf j)) ez (skipn (Z.to_nat (334 + 40 * sub) + 40) (j_excbuf j)))
as [P1 Lexc'];
[ exact PE1 | rewrite LE1, Z2Nat.id by lia; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by lia; exact PE2
| rewrite LE1, Lez, Z2Nat.id by lia; replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 4 * Z.of_nat 40) by lia; exact PE3
| clear PE1 PE2 PE3 ]
end.
rewrite LE1, Lez, LE3 in Lexc'.
replace (Z.to_nat (334 + 40 * sub) + 40 + (500 - Z.to_nat (334 + 40 * sub) - 40))%nat with 500%nat in Lexc' by lia.
lazymatch type of P1 with rw_cells _ _ _ (f32 ?l) => remember l as eb1 eqn:Eeb; clear Eeb end. clear LE1 Lez LE3 Lexc. rename Lexc' into Lexc.

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as sfP_; first [ sf_destruct 4%nat sfP_ as _ TB2 TB3 _ | sf_fb; destruct sfP_ as (_ & TB2 & TB3 & _) ]. pose proof (TB2 r INr) as SMC.
unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HK in SMC.
pose proof (ro_cells_bound _ _ _ _ SMC) as SMB. cbn [cells_size csize Nat.add] in SMB.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR. rewrite SPE in SPR. clear TAB TB2.
unfold NB_SUBMODES_PTR in P14.
zstep. rewrite SID. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. replace (213512 + mo * 8) with (213512 + 8 * mo) by lia.
zstep. zstep. zstep. if_false_x.
zstep. rewrite sx32_ssmall by (unbox SPAN; lia). zstep.

change ([C8 (f_a0 fr); C8 (f_a1 fr); C8 (f_a2 fr); C8 (f_a3 fr); C8 (f_a4 fr); C8 (f_a5 fr)])
with ([C8 (f_a0 fr); C8 (f_a1 fr); C8 (f_a2 fr); C8 (f_a3 fr); C8 (f_a4 fr)] ++ [C8 (f_a5 fr)]) in FA.
apply rw_cells_app in FA. destruct FA as [FA FA6]. cbn [cells_size csize Nat.add app] in FA6.
replace (usp + -896 + Z.of_nat 40) with (usp + -856) in FA6 by lia.

change ([C4 (f_g0 fr); C4 (f_g1 fr); C4 (f_g2 fr); C4 (f_pv fr)]) with (f32 [f_g0 fr; f_g1 fr; f_g2 fr] ++ [C4 (f_pv fr)]) in FP.
apply rw_cells_app in FP. destruct FP as [FPG FPV]. rewrite cells_size_f32 in FPV. cbn [length Nat.mul Nat.add] in FPV.
replace (usp + -216 + Z.of_nat 12) with (usp + -204) in FPV by lia.
unbox SPAN. unbox OLP.

lazymatch goal with |- evt _ ?Q (MS ?R ?F _ ?fcx ?rv ?mm ?rom) =>
apply (evt_cut rsegs (fun ms => exists start fin, 17 <= start /\ start + ltp_pitch_span k <= 144 /\ start <= fin <= 144 /\
ms = MS (@bvmap_set 5 word (Z_to_bv 5 13) (Z_to_bv 64 fin) (@bvmap_set 5 word (Z_to_bv 5 12) (Z_to_bv 64 start) R)) F (Z_to_bv 64 0x1f464) fcx rv mm rom) Q)
end.
{ destruct SPAN as [[ELBR SPN] | [ELBR SPN]]; rewrite ELBR.
-
zstep. if_true_x. zstep. zstep.
apply evt_done. exists 17, 144. split; [lia|]. split; [lia|]. split; [lia|]. reflexivity.
-
destruct OLP as [[C _] | [_ OLR]]; [lia|].
zstep. if_false_x. zstep. zstep. zstep. if_true_x.
apply evt_done. exists olp, olp. split; [lia|]. split; [lia|]. split; [lia|]. reflexivity. }
clear SPAN. box OLP. intros ms' sfH_; first [ sf_destruct 6%nat sfH_ as start fin ST1 ST2 ST3 -> | sf_fb; destruct sfH_ as (start & fin & ST1 & ST2 & ST3 & ->) ]. simp_regs.
e1_args.
pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ TB3' _ | sf_fb; destruct sfP_ as (_ & _ & TB3' & _) ].
call ((h_ltp _ _ _ NH k (smr_ltp_wf r k INr HK)) A D b (ST + 32) (ST + 1368 + 160 * sub) (usp + -576) (usp + -204) (usp + -216) start fin (smr_ltp_par r) (40 * sub) lo
eb1 (f_e32 fr) [f_g0 fr; f_g1 fr; f_g2 fr] (f_pv fr) (Z_to_bv 64 0));
[ exact REP | exact BOK | exact P1 | lia | rewrite Lexc; lia | Z.to_euclidean_division_equations; lia
| exact FE | exact Lfe32 | exact FPV | exact FPG | reflexivity
| destruct k as [|p]; [exact I | apply TB3'; [exact INr | exact HK]]
| exact (smr_ltp_par_top r INr) | unfold NB_GLOBALS_TOP; lia
| rewrite USP; exact FA
| lia | lia | lia | lia
| rewrite USP; exact STK | rewrite USP; unfold LTP_DEPTH; lia | exact T0
| rewrite USP; unfold apart; slia | rewrite USP; unfold apart; slia | rewrite USP; unfold apart; slia | rewrite USP; unfold apart; slia
| rewrite USP; unfold apart; slia | rewrite USP; unfold apart; slia
| unfold apart; slia | unfold apart; slia | unfold apart; slia | unfold apart; slia | unfold apart; slia
| unfold apart; slia | unfold apart; slia | unfold apart; slia | unfold apart; slia
| unfold apart; slia | unfold apart; slia | unfold apart; slia | unfold apart; slia | unfold apart; slia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| assumption | assumption | ].
e1_close k start.
Qed.
End Seg.
