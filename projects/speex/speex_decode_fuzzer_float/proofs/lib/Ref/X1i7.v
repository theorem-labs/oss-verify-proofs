(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3 X1i6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma f32_snoc1'' : forall segs m A done v, rw_cells segs m A (f32 done ++ [C4 v]) -> rw_cells segs m A (f32 (done ++ [v])).
Proof. intros segs m A done v H. rewrite f32_app, f32_cons, f32_nil. exact H. Qed.

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

Definition at_E5 (r : smrec) (mo olp bp2 sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs3 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 40) xs3 (Z_to_bv 64 bp2) (Z_to_bv 64 (160 * sub + 160)) (Z_to_bv 64 (ST + 1368)) (Z_to_bv 64 (ST + 1368 + 160 * sub))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -576)) (Z_to_bv 64 olp) (Z_to_bv 64 sub)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1f824) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 OUT /\ f_v64 fr = Z_to_bv 64 0x1008c
/\ f_v80 fr = Z_to_bv 64 (ST + 2228) /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (160 * sub)
/\ f_v104 fr = Z_to_bv 64 A /\ f_v112 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Definition exc_post (W : Z) (xra xsp s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws is es : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (W + 160)) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (W + 160)) (Z_to_bv 64 (usp + -416)) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x1f800) fc' None m' (seg_rom rsegs)
/\ munch [(W, W + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' W (f32 ws) /\ length ws = 40%nat
/\ rw_cells rsegs m' (usp + -416) (f32 is) /\ length is = 40%nat
/\ rw_cells rsegs m' (usp + -576) (f32 es) /\ length es = 40%nat.

#[using="Type"] Lemma exc_loop : forall (W : Z) (xra xsp s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done irest idone erest edone qw qi qe F fc m,
(length done + S (length rest) = 40)%nat -> length idone = length done -> length irest = length rest ->
length edone = length done -> length erest = length rest ->
qw = W + 4 * Z.of_nat (length done) -> qi = usp + -416 + 4 * Z.of_nat (length done) -> qe = usp + -576 + 4 * Z.of_nat (length done) ->
W + 160 <= usp + -896 \/ usp <= W ->
frm0 fc -> mem_inv rsegs m -> munch [(W, W + 160)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m W (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m qw (f32 (x :: rest'))) ->
rw_cells rsegs m (usp + -416) (f32 idone) -> (exists y irest', irest' = irest /\ rw_cells rsegs m qi (f32 (y :: irest'))) ->
rw_cells rsegs m (usp + -576) (f32 edone) -> (exists z erest', erest' = erest /\ rw_cells rsegs m qe (f32 (z :: erest'))) ->
evt rsegs (exc_post W xra xsp s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 qw) (Z_to_bv 64 qi) (Z_to_bv 64 (W + 160)) (Z_to_bv 64 qe) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1f7e0) fc None m (seg_rom rsegs)).
Proof.
intros until mN.
induction rest as [|x' rest IH]; intros done irest idone erest edone qw qi qe F fc m HL LID LIR LED LER Hqw Hqi Hqe SEPW FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ]; intros IDONE sfH2_; first [ sf_destruct 4%nat sfH2_ as y irest' -> IR | sf_fb; destruct sfH2_ as (y & irest' & -> & IR) ]; intros EDONE sfH3_; first [ sf_destruct 4%nat sfH3_ as z erest' -> ER | sf_fb; destruct sfH3_ as (z & erest' & -> & ER) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL, LID, LED;
rewrite !f32_cons, ?f32_nil in XR; rewrite f32_cons in IR; rewrite f32_cons in ER.
- destruct irest; [| cbn in LIR; lia]. destruct erest; [| cbn in LER; lia]. rewrite f32_nil in IR, ER.
step. step. step. step. zstep. zstep. zstep. zstep. if_false_x.
replace (qw + 4) with (W + 160) by lia. replace (qi + 4) with (usp + -256) by lia. replace (qe + 4) with (usp + -416) by lia.
unfold exc_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1'' in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc IDONE IR. apply f32_snoc1'' in IDONE. exact IDONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc EDONE ER. apply f32_snoc1'' in EDONE. exact EDONE.
+ rewrite length_app. cbn [length]. lia.
- destruct irest as [|y' irest'']; [cbn in LIR; lia|]. cbn [length] in LIR.
destruct erest as [|z' erest'']; [cbn in LER; lia|]. cbn [length] in LER.
step. step. step. step. zstep. zstep. zstep. zstep. if_true_x.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1'' in DONE.
rewrite f32_cons in IR. chunk_uncons IR as I1. rewrite <- f32_cons in IR. chunk_snoc IDONE I1. apply f32_snoc1'' in IDONE.
rewrite f32_cons in ER. chunk_uncons ER as E1. rewrite <- f32_cons in ER. chunk_snoc EDONE E1. apply f32_snoc1'' in EDONE.
eapply (IH (done ++ [_]) irest'' (idone ++ [_]) erest'' (edone ++ [_]) (qw + 4) (qi + 4) (qe + 4)); try eassumption.
+ rewrite length_app. cbn [length] in *. lia.
+ rewrite !length_app. cbn [length]. lia.
+ lia.
+ rewrite !length_app. cbn [length]. lia.
+ lia.
+ rewrite length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
+ sf_eexists 2%nat. split; [reflexivity|]. rewrite f32_cons. exact XR.
+ sf_eexists 2%nat. split; [reflexivity|]. exact IR.
+ sf_eexists 2%nat. split; [reflexivity|]. exact ER.
Qed.

Definition isv_post (W : Z) (xra xsp s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws is : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (W + 160)) (Z_to_bv 64 (W + 160)) (Z_to_bv 64 (usp + -256)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x1f824) fc' None m' (seg_rom rsegs)
/\ munch [(W, W + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' W (f32 ws) /\ length ws = 40%nat
/\ rw_cells rsegs m' (usp + -416) (f32 is) /\ length is = 40%nat.

#[using="Type"] Lemma isv_loop : forall (W : Z) (xra xsp s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done irest idone qw qi F fc m,
(length done + S (length rest) = 40)%nat -> length idone = length done -> length irest = length rest ->
qw = W + 4 * Z.of_nat (length done) -> qi = usp + -416 + 4 * Z.of_nat (length done) ->
W + 160 <= usp + -896 \/ usp <= W ->
frm0 fc -> mem_inv rsegs m -> munch [(W, W + 160)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m W (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m qw (f32 (x :: rest'))) ->
rw_cells rsegs m (usp + -416) (f32 idone) -> (exists y irest', irest' = irest /\ rw_cells rsegs m qi (f32 (y :: irest'))) ->
evt rsegs (isv_post W xra xsp s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 qw) (Z_to_bv 64 (W + 160)) (Z_to_bv 64 qi) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1f810) fc None m (seg_rom rsegs)).
Proof.
intros until mN.
induction rest as [|x' rest IH]; intros done irest idone qw qi F fc m HL LID LIR Hqw Hqi SEPW FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ]; intros IDONE sfH2_; first [ sf_destruct 4%nat sfH2_ as y irest' -> IR | sf_fb; destruct sfH2_ as (y & irest' & -> & IR) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL, LID;
rewrite !f32_cons, ?f32_nil in XR; rewrite f32_cons in IR.
- destruct irest; [| cbn in LIR; lia]. rewrite f32_nil in IR.
step. step. zstep. zstep. zstep. if_false_x.
replace (qw + 4) with (W + 160) by lia. replace (qi + 4) with (usp + -256) by lia.
unfold isv_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1'' in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc IDONE IR. apply f32_snoc1'' in IDONE. exact IDONE.
+ rewrite length_app. cbn [length]. lia.
- destruct irest as [|y' irest'']; [cbn in LIR; lia|]. cbn [length] in LIR.
step. step. zstep. zstep. zstep. if_true_x.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1'' in DONE.
rewrite f32_cons in IR. chunk_uncons IR as I1. rewrite <- f32_cons in IR. chunk_snoc IDONE I1. apply f32_snoc1'' in IDONE.
eapply (IH (done ++ [_]) irest'' (idone ++ [_]) (qw + 4) (qi + 4)); try eassumption.
+ rewrite length_app. cbn [length] in *. lia.
+ rewrite !length_app. cbn [length]. lia.
+ lia.
+ rewrite length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
+ sf_eexists 2%nat. split; [reflexivity|]. rewrite f32_cons. exact XR.
+ sf_eexists 2%nat. split; [reflexivity|]. exact IR.
Qed.

#[using="notify STR_TOP NH"] Lemma nbE4 : forall r mo olp bp2 sub st b ms, at_E4 X r mo olp bp2 sub st b ms -> evt rsegs (at_E5 r mo olp bp2 sub st b) ms.
Proof.
intros r mo olp bp2 sub st b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m kc xra xa0 xs0 xs5 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E64 E80 E88 E96 E104 E112 JEXC SAT SID BP2 OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs0 & xs5 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & JEXC & SAT & SID & BP2 & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
box OLP.
pose proof (h_isv _ _ _ NH) as HISV. rewrite <- ISAVE in HISV.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as _ _ _ _ _ _ _ _ _ _ _ Iis | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Iis) ]. rewrite ?ISAVE in Iis.

unfold nb_isave_ptr.
zstep. rewrite E96. zstep. zstep. zstep. step. zstep. zstep. zstep. zstep. zstep. zstep.
replace (ST + 1368 + (160 * sub + 160)) with (ST + 1368 + 160 * sub + 160) by lia.

first [ pose proof (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as sfP_; sf_destruct 6%nat sfP_ as PE1 PE2 PE3 LE1 LE2 LE3 | sf_fb; destruct (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as (PE1 & PE2 & PE3 & LE1 & LE2 & LE3) ]. clear P1.
rewrite Z2Nat.id in PE2, PE3 by lia. rewrite Lexc in LE3.
replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) in PE2, PE3 by lia.
pose proof (rw_cells_bound _ _ _ _ PE2) as BPE. rewrite cells_size_f32, LE2 in BPE.
pose proof (rw_cells_bound _ _ _ _ FI) as BFI. rewrite cells_size_f32, Lfinn in BFI.
pose proof (rw_cells_bound _ _ _ _ FE) as BFE. rewrite cells_size_f32, Lfe32 in BFE.
pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY) as LSS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of PE2 with rw_cells _ _ _ (f32 ?ws) =>
lazymatch type of FI with rw_cells _ _ _ (f32 ?is0) =>
lazymatch type of FE with rw_cells _ _ _ (f32 ?es0) =>
destruct ws as [|xw0 wrest] eqn:Ews; [cbn in LE2; lia|];
destruct is0 as [|iw0 irest] eqn:Eis; [cbn in Lfinn; lia|];
destruct es0 as [|ew0 erest] eqn:Ees; [cbn in Lfe32; lia|];
call (exc_loop (ST + 1368 + 160 * sub) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc wrest [] irest [] erest []
(ST + 1368 + 160 * sub) (usp + -416) (usp + -576));
[ cbn [length] in *; lia | reflexivity | cbn [length] in *; lia | reflexivity | cbn [length] in *; lia
| cbn [length]; lia | cbn [length]; lia | cbn [length]; lia | unfold NBSTATE_SIZEOF in LSS; lia
| assumption | assumption | apply munch_refl | apply wmono_refl
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact PE2]
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact FI]
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact FE] | ]
end end end end.
try clear PE2. try clear FI. try clear FE. clear LE2 Lfinn Lfe32 Ews Eis Ees BPE BFI BFE LSS. try rename MI0 into MI.
match goal with H : rw_cells _ _ (ST + 1368 + 160 * sub) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into PE2; rename L into LE2 end.
match goal with H : rw_cells _ _ (usp + -416) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FI; rename L into Lfinn end.
match goal with H : rw_cells _ _ (usp + -576) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FE; rename L into Lfe32 end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of PE2 with rw_cells _ _ _ (f32 ?ez) =>
destruct (f32_join3 rsegs mm (ST + 32) (firstn (Z.to_nat (334 + 40 * sub)) (j_excbuf j)) ez (skipn (Z.to_nat (334 + 40 * sub) + 40) (j_excbuf j)))
as [P1 Lexc'];
[ exact PE1 | rewrite LE1, Z2Nat.id by lia; replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) by lia; exact PE2
| rewrite LE1, LE2, Z2Nat.id by lia; replace (ST + 32 + 4 * (334 + 40 * sub) + 4 * Z.of_nat 40) with (ST + 1368 + 160 * sub + 4 * Z.of_nat 40) by lia; exact PE3
| clear PE1 PE2 PE3 ]
end end.
rewrite LE1, LE2, LE3 in Lexc'.
replace (Z.to_nat (334 + 40 * sub) + 40 + (500 - Z.to_nat (334 + 40 * sub) - 40))%nat with 500%nat in Lexc' by lia.
lazymatch type of P1 with rw_cells _ _ _ (f32 ?l) => remember l as eb1 eqn:Eeb; clear Eeb end. clear LE1 LE3 Lexc. rename Lexc' into Lexc.

zstep.
destruct (nb_innov_save st) as [kk|] eqn:EIS.
-
rewrite <- HISV in *.
pose proof (rw_cells_bound _ _ _ _ XI) as BXI. rewrite cells_size_f32, Liws in BXI.
replace ((Z.b2z (ISV mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64)
by (rewrite (Z.mod_small ISV) by lia; replace (ISV <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
rewrite Z.land_comm, Z.land_ones, Z.mod_mod by lia. rewrite Z.mod_small by lia.
zstep. if_false_x. zstep. zstep.

first [ pose proof (f32_split3 rsegs _ ISV iws (Z.to_nat (40 * sub)) 40 ltac:(rewrite Liws; lia) XI) as sfP_; sf_destruct 6%nat sfP_ as XI1 XI2 XI3 LI1 LI2 LI3 | sf_fb; destruct (f32_split3 rsegs _ ISV iws (Z.to_nat (40 * sub)) 40 ltac:(rewrite Liws; lia) XI) as (XI1 & XI2 & XI3 & LI1 & LI2 & LI3) ]. clear XI.
rewrite Z2Nat.id in XI2, XI3 by lia. rewrite Liws in LI3.
replace (ISV + 4 * (40 * sub)) with (ISV + 160 * sub) in XI2, XI3 by lia.
pose proof (rw_cells_bound _ _ _ _ XI2) as BX2. rewrite cells_size_f32, LI2 in BX2.
pose proof (rw_cells_bound _ _ _ _ FI) as BFI. rewrite cells_size_f32, Lfinn in BFI.
pose proof (lay_ISV_stk _ _ _ _ _ _ _ _ _ LAY) as LIS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of XI2 with rw_cells _ _ _ (f32 ?ws) =>
lazymatch type of FI with rw_cells _ _ _ (f32 ?is0) =>
destruct ws as [|xw1 wrest1] eqn:Ews; [cbn in LI2; lia|];
destruct is0 as [|iw1 irest1] eqn:Eis; [cbn in Lfinn; lia|];
call (isv_loop (ISV + 160 * sub) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc wrest1 [] irest1 [] (ISV + 160 * sub) (usp + -416));
[ cbn [length] in *; lia | reflexivity | cbn [length] in *; lia
| cbn [length]; lia | cbn [length]; lia | lia
| assumption | assumption | apply munch_refl | apply wmono_refl
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact XI2]
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact FI] | ]
end end end.
try clear XI2. try clear FI. clear LI2 Lfinn Ews Eis BX2 BFI LIS. try rename MI0 into MI.
match goal with H : rw_cells _ _ (ISV + 160 * sub) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into XI2; rename L into LI2 end.
match goal with H : rw_cells _ _ (usp + -416) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FI; rename L into Lfinn end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of XI2 with rw_cells _ _ _ (f32 ?iz) =>
destruct (f32_join3 rsegs mm ISV (firstn (Z.to_nat (40 * sub)) iws) iz (skipn (Z.to_nat (40 * sub) + 40) iws)) as [XI Liws'];
[ exact XI1 | rewrite LI1, Z2Nat.id by lia; replace (ISV + 4 * (40 * sub)) with (ISV + 160 * sub) by lia; exact XI2
| rewrite LI1, LI2, Z2Nat.id by lia; replace (ISV + 4 * (40 * sub) + 4 * Z.of_nat 40) with (ISV + 160 * sub + 4 * Z.of_nat 40) by lia; exact XI3
| clear XI1 XI2 XI3 ]
end end.
rewrite LI1, LI2, LI3 in Liws'.
replace (Z.to_nat (40 * sub) + 40 + (160 - Z.to_nat (40 * sub) - 40))%nat with 160%nat in Liws' by lia.
lazymatch type of XI with rw_cells _ _ _ (f32 ?l) => remember l as iws1 eqn:Eiw; clear Eiw end.
pose proof (eq_trans EIS ISAVE) as ISAVE'. apply evt_done. unfold boxed in OLP. close_cut 4.
-
match goal with |- context [Z.land ?a ?bb] => replace (Z.land a bb) with 0 by (replace a with 0 by reflexivity; symmetry; apply Z.land_0_l) end.
zstep. if_true_x.
pose proof (eq_trans EIS ISAVE) as ISAVE'. apply evt_done. unfold boxed in OLP. close_cut 4.
Qed.
End Seg.
