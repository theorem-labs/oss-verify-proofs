(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3 X1i5.
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

Lemma f32_snoc1' : forall segs m A done v, rw_cells segs m A (f32 done ++ [C4 v]) -> rw_cells segs m A (f32 (done ++ [v])).
Proof. intros segs m A done v H. rewrite f32_app, f32_cons, f32_nil. exact H. Qed.

Lemma smr_ptr_al8 : forall r, In r nb_smrecs -> smr_ptr r mod 8 = 0.
Proof. intros r Hr. unfold nb_smrecs in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr. Qed.

Lemma smr_innov_par_al8 : forall r p, In r nb_smrecs -> sm_innovation_unquant (smr_sm r) = Some (InnovSplitCbShapeSignUnquant p) ->
smr_innov_par r mod 8 = 0 /\ 0 < smr_innov_par r.
Proof.
intros r p Hr Hp. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hp; first [discriminate | vm_compute; split; reflexivity] |]). destruct Hr.
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

Definition at_E4 (r : smrec) (mo olp bp2 sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs5 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (isv_sub X sub st)) (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 1) (Z_to_bv 64 (usp + -416)) (Z_to_bv 64 (ST + 1368)) xs5 (Z_to_bv 64 160) (Z_to_bv 64 (ST + 1368 + 160 * sub))
(Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 bp2) (Z_to_bv 64 olp)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x219c4) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v72 fr = Z_to_bv 64 (ST + 2228)
/\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (40 * sub)
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ f_v128 fr = Z_to_bv 64 (olp + 1073741824)
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Definition dcb_post (xra xsp s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws ks : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -256)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (usp + -576)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x219c4) fc' None m' (seg_rom rsegs)
/\ munch [(usp + -416, usp + -256)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' (usp + -416) (f32 ws) /\ length ws = 40%nat
/\ rw_cells rsegs m' (usp + -736) (f32 ks) /\ length ks = 40%nat.

#[using="Type"] Lemma dcb_loop : forall (xra xsp s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done krest kdone q p F fc m,
(length done + S (length rest) = 40)%nat -> length kdone = length done -> length krest = length rest ->
q = usp + -416 + 4 * Z.of_nat (length done) -> p = usp + -736 + 4 * Z.of_nat (length done) ->
frm0 fc -> mem_inv rsegs m -> munch [(usp + -416, usp + -256)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m (usp + -416) (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m q (f32 (x :: rest'))) ->
rw_cells rsegs m (usp + -736) (f32 kdone) -> (exists y krest', krest' = krest /\ rw_cells rsegs m p (f32 (y :: krest'))) ->
evt rsegs (dcb_post xra xsp s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 s0 (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 p) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x219a8) fc None m (seg_rom rsegs)).
Proof.
intros until mN.
induction rest as [|x' rest IH]; intros done krest kdone q p F fc m HL LKD LKR Hq Hp FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ]; intros KDONE sfH2_; first [ sf_destruct 4%nat sfH2_ as y krest' -> KR | sf_fb; destruct sfH2_ as (y & krest' & -> & KR) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ KR) as BK; rewrite cells_size_f32 in BK; cbn [length] in BK;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL, LKR, LKD;
rewrite !f32_cons, ?f32_nil in XR; rewrite f32_cons in KR.
-
destruct krest; [| cbn in LKR; lia]. rewrite f32_nil in KR.
step. step. step. step. zstep. zstep. zstep. if_false_x.
replace (p + 4) with (usp + -576) by lia. replace (q + 4) with (usp + -256) by lia.
unfold dcb_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1' in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc KDONE KR. apply f32_snoc1' in KDONE. exact KDONE.
+ rewrite length_app. cbn [length]. lia.
- destruct krest as [|y' krest'']; [cbn in LKR; lia|]. cbn [length] in LKR.
step. step. step. step. zstep. zstep. zstep. if_true_x.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1' in DONE.
rewrite f32_cons in KR. chunk_uncons KR as K1. rewrite <- f32_cons in KR. chunk_snoc KDONE K1. apply f32_snoc1' in KDONE.
eapply (IH (done ++ [_]) krest'' (kdone ++ [_]) (q + 4) (p + 4)); try eassumption.
+ rewrite length_app. cbn [length] in *. lia.
+ rewrite !length_app. cbn [length]. lia.
+ cbn [length] in LKR. lia.
+ rewrite length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
+ sf_eexists 2%nat. split; [reflexivity|]. rewrite f32_cons. exact XR.
+ sf_eexists 2%nat. split; [reflexivity|]. exact KR.
Qed.

Ltac innov_call r ki bcur INN inn :=
lazymatch goal with REP : bits_rep _ _ _ _ bcur, P13 : rw_cells _ _ (_ + 2228) [C4 ?sd], MU : munch _ (x_m0 _) _,
USP : bv_unsigned (Z_to_bv 64 _) = _, BSZ : sb_buf_size _ = sb_buf_size _, T0 : 450560 <= x_lo _,
INr : In r nb_smrecs, HKI : sm_innovation_unquant (smr_sm r) = Some ki, SPX : bv_unsigned (x_sp _) < 2 ^ 63 |- _ =>
lazymatch type of INN with rw_cells _ _ _ (f32 ?is0) =>
let TAB4 := fresh "TAB4" in let TB4 := fresh "TB4" in
pose proof (ctx_tables _ _ X NH _ MU) as TAB4; pose proof TAB4 as sfP_; sf_curry 5%nat sfP_; intros _ _ _ TB4 _; sf_clear sfP_; sf_fix_order;
call ((h_innov _ _ _ NH ki (smr_innov_wf r ki INr HKI)) A D bcur inn (ST + 2228) (smr_innov_par r) lo is0 sd (Z_to_bv 64 0));
[ exact REP | assumption | exact INN | lazymatch goal with L : length is0 = 40%nat |- _ => exact L end | exact P13
| destruct ki as [|p]; [exact I | apply TB4; [assumption | assumption]]
| exact (smr_innov_par_top r INr) | unfold NB_GLOBALS_TOP; lia
| rewrite USP; eassumption | rewrite USP; unfold INNOV_DEPTH; lia | exact T0
| rewrite USP; clear -SPX; lia
| rewrite USP; unfold apart; slia | rewrite USP; unfold apart; slia | rewrite USP; unfold apart; slia
| rewrite BSZ, USP; unfold apart; slia
| unfold apart; slia | unfold apart; slia | rewrite BSZ; unfold apart; slia | unfold apart; slia | rewrite BSZ; unfold apart; slia
| rewrite ?USP; lia | rewrite ?USP; lia | destruct ki as [|p]; cbv iota; [split; lia | exact (smr_innov_par_al8 r p INr HKI)]
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| assumption | assumption | ];
clear TAB4 TB4;
let BS := fresh "BSZ" in
assert (BS : sb_buf_size (innov_bits ki bcur) = sb_buf_size (x_b0 X)) by (rewrite innov_bits_size; first [exact BSZ | rewrite ?innov_bits_size; exact BSZ])
end end.

#[using="notify STR_TOP NH"] Lemma nbE3b : forall r mo olp bp bp2 sub st b ms, at_E3b X r mo olp bp bp2 sub st b ms ->
evt rsegs (at_E4 r mo olp bp2 sub st
(match sm_innovation_unquant (smr_sm r) with
| Some ki => if negb (sm_double_codebook (smr_sm r) =? 0) then innov_bits ki (innov_bits ki b) else innov_bits ki b
| None => b end)) ms.
Proof.
intros r mo olp bp bp2 sub st b ms AT.
first [ sf_destruct 35%nat AT as Fx fc m kc xra xa0 xs5 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E72 E80 E88 E96 E104 E112 E120 E128 JEXC SAT SID BP BP2 OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs5 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E72 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & JEXC & SAT & SID & BP & BP2 & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
box OLP.
pose proof (smrec_sub_facts mo r SAT) as sfP_; first [ sf_destruct 16%nat sfP_ as k ki HK HKI _ _ _ DCB _ INr SPlo SPE _ _ EI1 EI2 | sf_fb; destruct sfP_ as (k & ki & HK & HKI & _ & _ & _ & DCB & _ & INr & SPlo & SPE & _ & _ & EI1 & EI2) ].
pose proof (smrec_at_in mo r SAT) as (_ & _ & Hmo). rewrite HKI. box DCB.
pose proof (h_sp16 _ _ _ NH) as SP16. pose proof (h_stal _ _ _ NH) as STAL. pose proof (smr_ptr_al8 r INr) as SPAL.

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC.
unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HKI in SMC.
pose proof (ro_cells_bound _ _ _ _ SMC) as SMB. cbn [cells_size csize Nat.add] in SMB.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR. rewrite SPE in SPR. clear TAB TB2.
unfold NB_SUBMODES_PTR in P14.
zstep. rewrite SID. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. rewrite (Z.mul_comm mo 8).
bato 0x218a0%Z.
zstep.
bato 0x218b0%Z.
zstep. zstep. if_false_x.
bato 0x218bc%Z.
zstep. zstep. zstep. zstep. rewrite E112. zstep. rewrite E120. zstep. rewrite E72. zstep.
replace (ret_pc (Z_to_bv 64 (innov_entry ki))) with (Z_to_bv 64 (innov_entry ki)) by (symmetry; apply ret_pc_even; [lia | exact EI2]).
innov_call r ki b FI (usp + -416).
cbv beta delta [callR]. try rename MI0 into MI. rewrite USP in *. try clear Linn0.
match goal with H : rw_cells _ _ (usp + -416) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FI; rename L into Linn end.
match goal with H : rw_cells _ _ (ST + 2228) [C4 ?sd] |- _ => rename H into P13 end.
match goal with H : bits_rep _ _ _ _ (innov_bits ki b) |- _ => rename H into REP end.

zstep. zstep. zstep. step. zstep.
lazymatch type of FI with rw_cells _ _ _ (f32 ?is1) =>
call ((h_smul _ _ _ NH) (usp + -416) is1); [exact FI | exact Linn | lia | lia | reflexivity | reflexivity | reflexivity | assumption | assumption | ]
end.
cbv beta delta [callR]. try rename MI0 into MI. try clear FI. clear Linn.
match goal with H : rw_cells _ _ (usp + -416) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FI; rename L into Linn end.

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC2.
unfold smrec_cells in SMC2. cbv zeta in SMC2. rewrite HKI in SMC2.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR2. unfold NB_SUBMODES_PTR in SPR2. rewrite SPE in SPR2. clear TAB TB2.
zstep. rewrite SID. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. rewrite (Z.mul_comm mo 8).
bato 0x21928%Z.
zstep.
bato 0x21938%Z.
zstep.
unbox DCB. destruct DCB as [ED | [ED M7]]; rewrite ED; cbn [Z.eqb negb].
-
zstep. if_true. apply evt_done. unfold boxed in OLP. close_cut 3.
-
zstep. if_false.

zstep. zstep. zstep. zstep.
pose proof (rw_cells_bound _ _ _ _ FK) as BFK. rewrite cells_size_f32, Lfak in BFK.
pose proof (f32_as_blob _ _ _ 40%nat FK Lfak) as FKB. clear FK.
call (nmemset_specZ (usp + -736) 160 0 _ _); [exact FKB | assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. clear BFK.
match goal with H : rw_cells _ ?mm (usp + -736) [CB _ _] |- _ =>
destruct (rw_cells_CB_f32 rsegs _ _ 40 _ H) as (in2 & Lin2 & FK); clear H end.

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC3.
unfold smrec_cells in SMC3. cbv zeta in SMC3. rewrite HKI in SMC3.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR3. unfold NB_SUBMODES_PTR in SPR3. rewrite SPE in SPR3. clear TAB TB2.
bato 0x21954%Z.
zstep.
bato 0x21964%Z.
zstep. zstep. zstep. zstep. zstep. zstep. rewrite E112. zstep. rewrite E120. zstep. rewrite E72. zstep.
replace (ret_pc (Z_to_bv 64 (innov_entry ki))) with (Z_to_bv 64 (innov_entry ki)) by (symmetry; apply ret_pc_even; [lia | exact EI2]).
innov_call r ki (innov_bits ki b) FK (usp + -736).
cbv beta delta [callR]. try rename MI0 into MI. rewrite USP in *. clear Lin2.
match goal with H : rw_cells _ _ (usp + -736) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FK; rename L into Lin2 end.
match goal with H : rw_cells _ _ (ST + 2228) [C4 ?sd] |- _ => rename H into P13 end.

zstep. step. step. zstep. zstep. zstep. zstep.
lazymatch type of FK with rw_cells _ _ _ (f32 ?is1) =>
call ((h_smul _ _ _ NH) (usp + -736) is1); [exact FK | exact Lin2 | lia | lia | reflexivity | reflexivity | reflexivity | assumption | assumption | ]
end.
cbv beta delta [callR]. try rename MI0 into MI. try clear FK. clear Lin2.
match goal with H : rw_cells _ _ (usp + -736) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FK; rename L into Lin2 end.

zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FI with rw_cells _ _ _ (f32 ?ws) =>
lazymatch type of FK with rw_cells _ _ _ (f32 ?ks) =>
destruct ws as [|iw0 irest] eqn:Ews; [cbn in Linn; lia|];
destruct ks as [|kw0 krest0] eqn:Eks; [cbn in Lin2; lia|];
call (dcb_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc irest [] krest0 [] (usp + -416) (usp + -736));
[ cbn [length] in *; lia | reflexivity | cbn [length] in *; lia | cbn [length]; lia | cbn [length]; lia
| assumption | assumption | apply munch_refl | apply wmono_refl
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact FI]
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact FK] | ]
end end end.
try clear FI. try clear FK. clear Linn Lin2 Ews Eks. try rename MI0 into MI.
match goal with H : rw_cells _ _ (usp + -416) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FI; rename L into Linn end.
match goal with H : rw_cells _ _ (usp + -736) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FK; rename L into Lfak2 end.
apply evt_done. unfold boxed in OLP. close_cut 3.
Qed.
End Seg.
