(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3 X1i6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
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
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs2 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 (Z_to_bv 64 (usp + -416)) (Z_to_bv 64 (ST + 1368)) (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 160) (Z_to_bv 64 (ST + 1368 + 160 * sub))
(Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 bp2) (Z_to_bv 64 olp)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21a5c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v72 fr = Z_to_bv 64 (ST + 2228)
/\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (40 * sub)
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ f_v128 fr = Z_to_bv 64 (olp + 1073741824)
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Local Ltac ucond_rw := unfold_cond; fold_lit_ux; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Local Ltac uifh b H := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
replace c with b; [cbv iota | symmetry; ucond_rw; rewrite H; solve_cond_rec] end.
Local Ltac uif b := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
replace c with b; [cbv iota | symmetry; ucond_rw; solve_cond_rec] end.

Definition exc_post (W : Z) (xra xsp s0 s1 a7 s3 s4 s5 s6 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (c0 c1 c2 c3 c4 c5 c6 : word) (ws is es : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 c0 c1 c2 c3 c4 c5 c6 a7
(Z_to_bv 64 1) s3 s4 s5 s6 (Z_to_bv 64 W) s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x21a2c) fc' None m' (seg_rom rsegs)
/\ munch [(W, W + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' W (f32 ws) /\ length ws = 40%nat
/\ rw_cells rsegs m' (usp + -416) (f32 is) /\ length is = 40%nat
/\ rw_cells rsegs m' (usp + -576) (f32 es) /\ length es = 40%nat.

#[using="Type"] Lemma exc_loop : forall (W : Z) (xra xsp s0 s1 a7 s3 s4 s5 s6 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done irest idone erest edone qw qi qe kz (a6 : word) F fc m,
(length done + S (length rest) = 40)%nat -> length idone = length done -> length irest = length rest ->
length edone = length done -> length erest = length rest ->
qw = W + 4 * Z.of_nat (length done) -> qi = usp + -416 + 4 * Z.of_nat (length done) -> qe = usp + -576 + 4 * Z.of_nat (length done) ->
kz = Z.of_nat (S (length rest)) -> 0 < W ->
W + 160 <= usp + -896 \/ usp <= W ->
frm0 fc -> mem_inv rsegs m -> munch [(W, W + 160)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m W (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m qw (f32 (x :: rest'))) ->
rw_cells rsegs m (usp + -416) (f32 idone) -> (exists y irest', irest' = irest /\ rw_cells rsegs m qi (f32 (y :: irest'))) ->
rw_cells rsegs m (usp + -576) (f32 edone) -> (exists z erest', erest' = erest /\ rw_cells rsegs m qe (f32 (z :: erest'))) ->
evt rsegs (exc_post W xra xsp s0 s1 a7 s3 s4 s5 s6 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 qe) (Z_to_bv 64 qi) (Z_to_bv 64 qw) (Z_to_bv 64 1) (Z_to_bv 64 kz) (Z_to_bv 64 qw) a6 a7
(Z_to_bv 64 1) s3 s4 s5 s6 (Z_to_bv 64 W) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x219f0) fc None m (seg_rom rsegs)).
Proof.
intros until mN.
induction rest as [|x' rest IH]; intros done irest idone erest edone qw qi qe kz a6 F fc m HL LID LIR LED LER Hqw Hqi Hqe Hkz WPOS SEPW FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ]; intros IDONE sfH2_; first [ sf_destruct 4%nat sfH2_ as y irest' -> IR | sf_fb; destruct sfH2_ as (y & irest' & -> & IR) ]; intros EDONE sfH3_; first [ sf_destruct 4%nat sfH3_ as z erest' -> ER | sf_fb; destruct sfH3_ as (z & erest' & -> & ER) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL, LID, LED;
rewrite !f32_cons, ?f32_nil in XR; rewrite f32_cons in IR; rewrite f32_cons in ER; subst kz.
- destruct irest; [| cbn in LIR; lia]. destruct erest; [| cbn in LER; lia]. rewrite f32_nil in IR, ER. cbn [length] in *.
zstep. uif false. zstep. zstep.
rewrite (proj2 (Z.ltb_ge qw 1) ltac:(lia)). cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
zstep. if_false_x. zstep. if_false_x.
step. step. zstep. zstep. zstep. zstep. step. zstep. zstep. zstep. uif false.
replace (qw + 4) with (W + 160) by lia. replace (qi + 4) with (usp + -256) by lia. replace (qe + 4) with (usp + -416) by lia.
unfold exc_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1'' in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc IDONE IR. apply f32_snoc1'' in IDONE. exact IDONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc EDONE ER. apply f32_snoc1'' in EDONE. exact EDONE.
+ rewrite length_app. cbn [length]. lia.
- destruct irest as [|y' irest'']; [cbn in LIR; lia|]. cbn [length] in LIR.
destruct erest as [|z' erest'']; [cbn in LER; lia|]. cbn [length] in *.
zstep. uif false. zstep. zstep.
rewrite (proj2 (Z.ltb_ge qw 1) ltac:(lia)). cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
zstep. if_false_x. zstep. if_false_x.
step. step. zstep. zstep. zstep. zstep. step. zstep. zstep. zstep. uif true.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1'' in DONE.
rewrite f32_cons in IR. chunk_uncons IR as I1. rewrite <- f32_cons in IR. chunk_snoc IDONE I1. apply f32_snoc1'' in IDONE.
rewrite f32_cons in ER. chunk_uncons ER as E1. rewrite <- f32_cons in ER. chunk_snoc EDONE E1. apply f32_snoc1'' in EDONE.
eapply (IH (done ++ [_]) irest'' (idone ++ [_]) erest'' (edone ++ [_]) (qw + 4) (qi + 4) (qe + 4)); try eassumption.
all: first [ rewrite ?length_app; cbn [length] in *; lia
| sf_eexists 2%nat; split; [reflexivity|]; first [ rewrite f32_cons; exact XR | exact IR | exact ER ] ].
Qed.

Definition isv_post (W : Z) (xra xsp s1 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (c0 c1 c2 c3 : word) (ws is : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 (Z_to_bv 64 W) s1 c0 c1 c2 c3 a4 a5 a6 a7
s2 (Z_to_bv 64 (usp + -416)) s4 s5 (Z_to_bv 64 160) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x21a5c) fc' None m' (seg_rom rsegs)
/\ munch [(W, W + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' W (f32 ws) /\ length ws = 40%nat
/\ rw_cells rsegs m' (usp + -416) (f32 is) /\ length is = 40%nat.

#[using="Type"] Lemma isv_loop : forall (W : Z) (xra xsp s1 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done irest idone qo qw qi (a1 a3 : word) F fc m,
(length done + S (length rest) = 40)%nat -> length idone = length done -> length irest = length rest ->
qo = 4 * Z.of_nat (length done) -> qw = W + qo -> qi = usp + -416 + qo ->
0 < W -> bv_unsigned a1 = 2^64 - 1 - W ->
W + 160 <= usp + -896 \/ usp <= W ->
frm0 fc -> mem_inv rsegs m -> munch [(W, W + 160)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m W (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m qw (f32 (x :: rest'))) ->
rw_cells rsegs m (usp + -416) (f32 idone) -> (exists y irest', irest' = irest /\ rw_cells rsegs m qi (f32 (y :: irest'))) ->
evt rsegs (isv_post W xra xsp s1 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 (Z_to_bv 64 W) s1 (Z_to_bv 64 qo) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (usp + -416)) s4 s5 (Z_to_bv 64 160) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21a3c) fc None m (seg_rom rsegs)).
Proof.
intros until mN.
induction rest as [|x' rest IH]; intros done irest idone qo qw qi a1 a3 F fc m HL LID LIR Hqo Hqw Hqi WPOS HA1 SEPW FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ]; intros IDONE sfH2_; first [ sf_destruct 4%nat sfH2_ as y irest' -> IR | sf_fb; destruct sfH2_ as (y & irest' & -> & IR) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL, LID;
rewrite !f32_cons, ?f32_nil in XR; rewrite f32_cons in IR.
- destruct irest; [| cbn in LIR; lia]. rewrite f32_nil in IR. cbn [length] in *.
zstep. uifh false HA1. zstep. if_false_x. zstep. replace (usp + -416 + qo) with qi by lia.
step. zstep. replace (W + qo) with qw by lia. zstep. step. zstep. uif false.
replace (qw + 4) with (W + 160) by lia. replace (qi + 4) with (usp + -256) by lia.
unfold isv_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1'' in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc IDONE IR. apply f32_snoc1'' in IDONE. exact IDONE.
+ rewrite length_app. cbn [length]. lia.
- destruct irest as [|y' irest'']; [cbn in LIR; lia|]. cbn [length] in *.
zstep. uifh false HA1. zstep. if_false_x. zstep. replace (usp + -416 + qo) with qi by lia.
step. zstep. replace (W + qo) with qw by lia. zstep. step. zstep. uif true.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1'' in DONE.
rewrite f32_cons in IR. chunk_uncons IR as I1. rewrite <- f32_cons in IR. chunk_snoc IDONE I1. apply f32_snoc1'' in IDONE.
eapply (IH (done ++ [_]) irest'' (idone ++ [_]) (qo + 4) (qw + 4) (qi + 4)); try eassumption.
all: first [ rewrite ?length_app; cbn [length] in *; lia
| sf_eexists 2%nat; split; [reflexivity|]; first [ rewrite f32_cons; exact XR | exact IR ] ].
Qed.

#[using="notify STR_TOP NH"] Lemma nbE4 : forall r mo olp bp2 sub st b ms, at_E4 X r mo olp bp2 sub st b ms -> evt rsegs (at_E5 r mo olp bp2 sub st b) ms.
Proof.
intros r mo olp bp2 sub st b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m kc xra xa0 xs5 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E72 E80 E88 E96 E104 E112 E120 E128 JEXC SAT SID BP2 OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs5 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E72 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & JEXC & SAT & SID & BP2 & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
box OLP.
pose proof (h_isv _ _ _ NH) as HISV. rewrite <- ISAVE in HISV.
pose proof (h_stal _ _ _ NH) as STAL. pose proof (h_out4 _ _ _ NH) as OUT4.
remember (isv_sub X sub st) as P eqn:EP.
pose proof (h_sthi _ _ _ NH) as STHI. unfold NBSTATE_SIZEOF in STHI.
zstep. rewrite E96. zstep. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
replace (Z.shiftl (40 * sub) 2) with (160 * sub) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia).
replace (Z.land (ST + 1368) 3) with 0 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia).
change (Z.land (Z.b2z (0 <? 1)) 1) with 1.

first [ pose proof (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as sfP_; sf_destruct 6%nat sfP_ as PE1 PE2 PE3 LE1 LE2 LE3 | sf_fb; destruct (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as (PE1 & PE2 & PE3 & LE1 & LE2 & LE3) ].
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
call (exc_loop (ST + 1368 + 160 * sub) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc wrest [] irest [] erest []
(ST + 1368 + 160 * sub) (usp + -416) (usp + -576) 40);
[ cbn [length] in *; lia | reflexivity | cbn [length] in *; lia | reflexivity | cbn [length] in *; lia
| cbn [length]; lia | cbn [length]; lia | cbn [length]; lia | cbn [length] in *; lia | lia | unfold NBSTATE_SIZEOF in LSS; lia
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
unfold isv_sub in EP. destruct (nb_innov_save st) as [kk|] eqn:EIS.
-
rewrite <- HISV in *. subst P.
pose proof (rw_cells_bound _ _ _ _ XI) as BXI. rewrite cells_size_f32, Liws in BXI.
uif false. zstep. zstep. zstep.
rewrite (zb_lxor_ones (ISV + 160 * sub)) by lia.
replace (Z.land (ISV + 160 * sub) 3) with 0 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia).

first [ pose proof (f32_split3 rsegs _ ISV iws (Z.to_nat (40 * sub)) 40 ltac:(rewrite Liws; lia) XI) as sfP_; sf_destruct 6%nat sfP_ as XI1 XI2 XI3 LI1 LI2 LI3 | sf_fb; destruct (f32_split3 rsegs _ ISV iws (Z.to_nat (40 * sub)) 40 ltac:(rewrite Liws; lia) XI) as (XI1 & XI2 & XI3 & LI1 & LI2 & LI3) ].
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
call (isv_loop (ISV + 160 * sub) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc wrest1 [] irest1 [] 0 (ISV + 160 * sub) (usp + -416));
[ cbn [length] in *; lia | reflexivity | cbn [length] in *; lia
| reflexivity | lia | lia | lia | rewrite unsigned_lit by lia; lia | lia
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
- subst P. if_true_x.
pose proof (eq_trans EIS ISAVE) as ISAVE'. apply evt_done. unfold boxed in OLP. close_cut 4.
Qed.
End Seg.
