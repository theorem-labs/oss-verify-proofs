(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3 X1i7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma f32_snoc1x : forall segs m A done v, rw_cells segs m A (f32 done ++ [C4 v]) -> rw_cells segs m A (f32 (done ++ [v])).
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

Definition at_E6 (r : smrec) (mo olp bp2 sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs2 xs4 xs5 xs7 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 (Z_to_bv 64 (usp + -416)) xs4 xs5 (Z_to_bv 64 160) xs7
(Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 bp2) (Z_to_bv 64 olp)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21b68) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v72 fr = Z_to_bv 64 (ST + 2228)
/\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (40 * sub)
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ f_v128 fr = Z_to_bv 64 (olp + 1073741824)
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Local Ltac ucond_rw := unfold_cond; fold_lit_ux; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Local Ltac uifn NA b := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
replace c with b; [cbv iota | symmetry; ucond_rw; rewrite NA; solve_cond_rec] end.

Definition vmix_post (W : Z) (xra xsp s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (a1' a2' a3' a4' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws is vc : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x21b68) fc' None m' (seg_rom rsegs)
/\ munch [(W, W + 160); (ST + 2936, ST + 2948)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' W (f32 ws) /\ length ws = 40%nat
/\ rw_cells rsegs m' (usp + -416) (f32 is) /\ length is = 40%nat
/\ rw_cells rsegs m' (ST + 2936) (f32 vc) /\ length vc = 3%nat.

#[using="notify STR_TOP NH"] Lemma vmix_loop : forall (W : Z) (xra xsp s0 s1 na a5 a6 a7 s2 s5 s7 s8 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done irest idone qo qw qi (a2 a3 a4 v0 v1 v2 : word) F fc m,
(length done + S (length rest) = 40)%nat -> length idone = length done -> length irest = length rest ->
qo = 4 * Z.of_nat (length done) -> qw = W + qo -> qi = usp + -416 + qo -> bv_unsigned na = 18446744073709551615 - W ->
W + 160 <= usp + -896 \/ usp <= W -> ST + 1368 <= W -> W + 160 <= ST + 2008 ->
frm0 fc -> mem_inv rsegs m -> munch [(W, W + 160); (ST + 2936, ST + 2948)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m W (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m qw (f32 (x :: rest'))) ->
rw_cells rsegs m (usp + -416) (f32 idone) -> (exists y irest', irest' = irest /\ rw_cells rsegs m qi (f32 (y :: irest'))) ->
rw_cells rsegs m (ST + 2936) [C4 v0; C4 v1; C4 v2] ->
evt rsegs (vmix_post W xra xsp s0 s1 na a5 a6 a7 s2 (Z_to_bv 64 (usp + -416)) (Z_to_bv 64 W) s5 (Z_to_bv 64 160) s7 s8 (Z_to_bv 64 (ST + 2184)) s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 na (Z_to_bv 64 qo) a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (usp + -416)) (Z_to_bv 64 W) s5 (Z_to_bv 64 160) s7 s8 (Z_to_bv 64 (ST + 2184)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21adc) fc None m (seg_rom rsegs)).
Proof.
intros until mN. open_hyps NH.
pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY) as LSS. unfold NBSTATE_SIZEOF in LSS.
induction rest as [|x' rest IH]; intros done irest idone qo qw qi a2 a3 a4 v0 v1 v2 F fc m HL LID LIR Hqo Hqw Hqi NA SEPW WLO WHI FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ]; intros IDONE sfH2_; first [ sf_destruct 4%nat sfH2_ as y irest' -> IR | sf_fb; destruct sfH2_ as (y & irest' & -> & IR) ]; intros VC;
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL, LID;
rewrite !f32_cons, ?f32_nil in XR; rewrite f32_cons in IR.
- destruct irest; [| cbn in LIR; lia]. rewrite f32_nil in IR.
zstep. uifn NA false. zstep. rewrite <- Hqw. zstep. zstep. step. step. step. step. step. step.
zstep. rewrite <- Hqi. step. step. zstep. step. step. step. step. step. step.
zstep. step. step. step. step. step. step. step. step. step. step. step.
zstep. step. zstep. if_false_x.
unfold vmix_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1x in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc IDONE IR. apply f32_snoc1x in IDONE. exact IDONE.
+ rewrite length_app. cbn [length]. lia.
+ rewrite <- f32_nil, <- !f32_cons in VC. exact VC.
+ reflexivity.
- destruct irest as [|y' irest'']; [cbn in LIR; lia|]. cbn [length] in LIR.
zstep. uifn NA false. zstep. rewrite <- Hqw. zstep. zstep. step. step. step. step. step. step.
zstep. rewrite <- Hqi. step. step. zstep. step. step. step. step. step. step.
zstep. step. step. step. step. step. step. step. step. step. step. step.
zstep. step. zstep. if_true_x.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1x in DONE.
rewrite f32_cons in IR. chunk_uncons IR as I1. rewrite <- f32_cons in IR. chunk_snoc IDONE I1. apply f32_snoc1x in IDONE.
eapply (IH (done ++ [_]) irest'' (idone ++ [_]) (qo + 4) (qw + 4) (qi + 4)); try eassumption;
first [ solve [rewrite ?length_app; cbn [length] in *; lia]
| sf_eexists 2%nat; split; [reflexivity|]; first [ rewrite f32_cons; exact XR | exact IR ] ].
Qed.

Definition vocl_post (W vf : Z) (xra xsp s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 d1 d2 d3 : word)
(pad : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (a1' a3' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws : list word) (y : word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 a0 a1' (Z_to_bv 64 vf) a3' a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 W) s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x21acc) fc' None m' (seg_rom rsegs)
/\ munch [(W, W + 160); (ST + 2948, ST + 2952)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' W (f32 ws) /\ length ws = 40%nat
/\ rw_cells rsegs m' (ST + 2948) [C4 y; C4 d1; C4 d2; C4 d3; CB 4 pad].

#[using="notify STR_TOP NH"] Lemma voc_pulse_loop : forall (W olp vf : Z) (xra s0 s1 na a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 t0 t1 t2 t3 t4 t5 t6 d1 d2 d3 : word)
(pad : list byte) (fr : frame) (mN : mem) fuel v (a2 a3 y : word) ws F fc m,
0 <= v < 40 -> 17 <= olp <= 144 -> voc_loop fuel (v + olp) olp = Some vf -> bv_unsigned na = 18446744073709551615 - W ->
W + 160 <= usp + -896 \/ usp <= W -> ST + 1368 <= W -> W + 160 <= ST + 2008 ->
frm0 fc -> mem_inv rsegs m -> munch [(W, W + 160); (ST + 2948, ST + 2952)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m W (f32 ws) -> length ws = 40%nat ->
rw_cells rsegs m (ST + 2948) [C4 y; C4 d1; C4 d2; C4 d3; CB 4 pad] ->
rw_cells rsegs m (usp + -864) (fl_cells fr) -> f_v128 fr = Z_to_bv 64 (olp + 1073741824) ->
evt rsegs (vocl_post W vf xra (Z_to_bv 64 (usp + -912)) s0 s1 na a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 (Z_to_bv 64 (ST + 2184)) s10 (Z_to_bv 64 olp)
t0 t1 t2 t3 t4 t5 t6 d1 d2 d3 pad mN)
(MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp t0 t1 t2 s0 s1 na (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 W) s8 (Z_to_bv 64 (ST + 2184)) s10 (Z_to_bv 64 olp) t3 t4 t5 t6)
F (Z_to_bv 64 0x21a88) fc None m (seg_rom rsegs)).
Proof.
intros until mN. open_hyps NH.
pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY) as LSS. unfold NBSTATE_SIZEOF in LSS.
induction fuel as [|fuel IH]; intros v a2 a3 y ws F fc m Hv Holp HVL NA SEPW WLO WHI FRM MI MU WM XW LW TL FL E128; [discriminate|].
cbn [voc_loop] in HVL. unfold NB_SUBFRAME_SIZE in HVL. unfold fl_cells in FL.
pose proof (rw_cells_bound _ _ _ _ XW) as BW. rewrite cells_size_f32, LW in BW.
zstep. unfold bv_lts. rewrite !zb_signed_small by lia. if_false_x.
zstep. rewrite E128.
zstep. unfold bv_lts. rewrite !zb_signed_small by lia. if_false_x.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
zstep. uifn NA false.
zstep.

first [ pose proof (f32_split_at rsegs _ _ ws (Z.to_nat v) ltac:(rewrite LW; lia) XW) as sfP_; sf_destruct 6%nat sfP_ as xv _ XW1 XW2 XW3 LW1 | sf_fb; destruct (f32_split_at rsegs _ _ ws (Z.to_nat v) ltac:(rewrite LW; lia) XW) as (xv & _ & XW1 & XW2 & XW3 & LW1) ]. clear XW.
rewrite Z2Nat.id in XW2, XW3 by lia.
replace (W + v * 4) with (W + 4 * v) by lia.
remember (W + 4 * v) as PVA eqn:EPVA.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with H : rw_cells _ mm PVA [C4 ?nv] |- _ =>
subst PVA;
destruct (f32_join_at rsegs mm W (firstn (Z.to_nat v) ws) nv (skipn (S (Z.to_nat v)) ws)) as [XW LW'];
[ exact XW1 | rewrite LW1, Z2Nat.id by lia; exact H | rewrite LW1, Z2Nat.id by lia; exact XW3 | clear XW1 H XW3 ]
end end.
rewrite LW1, length_skipn, LW in LW'. replace (S (Z.to_nat v + (40 - S (Z.to_nat v))))%nat with 40%nat in LW' by lia.
lazymatch type of XW with rw_cells _ _ _ (f32 ?l) => remember l as ws1 eqn:Ews; clear Ews end. clear LW1.

zstep.
zstep. rewrite swrap32_small by lia.
zstep. if_false_x.
zstep. rewrite Z.add_0_r, swrap32_small by lia.
zstep.
zstep. rewrite swrap32_small by lia.
zstep.
zstep. unfold bv_lts. rewrite !zb_signed_small by lia.
destruct (Z_lt_ge_dec (v + olp) 40) as [LT | GE].
- if_true_x. replace (v + olp <? 40) with true in HVL by (symmetry; apply Z.ltb_lt; lia).
eapply (IH (v + olp) _ _ _ ws1); try eassumption; try lia.
- if_false_x. replace (v + olp <? 40) with false in HVL by (symmetry; apply Z.ltb_ge; lia). injection HVL as <-.
zstep.
unfold vocl_post. finish; try first [ eexact XW | exact LW' | eassumption ].
Qed.

#[using="notify STR_TOP NH"] Lemma nbE5 : forall r mo olp bp2 sub st b ms, at_E5 X r mo olp bp2 sub st b ms ->
evt rsegs (at_E6 r mo olp bp2 sub
(if mo =? 1 then match voc_loop VOC_FUEL (nb_voc_offset st) olp with
| Some v => set_nb_voc_offset st (v - NB_SUBFRAME_SIZE) | None => st end
else st) b) ms.
Proof.
intros r mo olp bp2 sub st b ms AT.
first [ sf_destruct 35%nat AT as Fx fc m kc xra xa0 xs0 xs2 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E72 E80 E88 E96 E104 E112 E120 E128 JEXC SAT SID BP2 OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs0 & xs2 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E72 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & JEXC & SAT & SID & BP2 & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof (h_sthi _ _ _ NH) as STHI. unfold NBSTATE_SIZEOF in STHI.
pose proof (smrec_at_in mo r SAT) as (INr & _ & Hmo).
pose proof INV as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ Ivo _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Ivo & _) ].

zstep. rewrite SID. rewrite sx32_small by (unfold int31; lia). zstep. zstep.
destruct (Z.eq_dec mo 1) as [M1 | M1].
2: {
if_true_x. replace (mo =? 1) with false by (symmetry; apply Z.eqb_neq; exact M1).
apply evt_done. close_cut 7. }
rewrite M1 in *. cbn [Z.eqb Pos.eqb]. if_false_x.
pose proof (smrec_sub_facts 1 r SAT) as sfP_; first [ sf_destruct 9%nat sfP_ as k ki HK HKI SPAN _ _ _ _ | sf_fb; destruct sfP_ as (k & ki & HK & HKI & SPAN & _ & _ & _ & _) ].
assert (OLR : 17 <= olp <= 144).
{ destruct OLP as [[EL _] | [_ H]]; [| exact H]. exfalso. destruct SPAN as [[EL2 _] | [EL2 _]]; [| congruence].
destruct (smrec_at_cases_E 1 r SAT) as [[_ ->]|[[? _]|[[? _]|[[? _]|[[? _]|[[? _]|[[? _]|[? _]]]]]]]]; try lia. cbn in EL2. lia. }
box OLP. clear SPAN.

zstep. zstep. zstep. zstep.
first [ pose proof (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as sfP_; sf_destruct 6%nat sfP_ as PE1 PE2 PE3 LE1 LE2 LE3 | sf_fb; destruct (f32_split3 rsegs _ (ST + 32) (j_excbuf j) (Z.to_nat (334 + 40 * sub)) 40 ltac:(rewrite Lexc; lia) P1) as (PE1 & PE2 & PE3 & LE1 & LE2 & LE3) ]. clear P1.
rewrite Z2Nat.id in PE2, PE3 by lia. rewrite Lexc in LE3.
replace (ST + 32 + 4 * (334 + 40 * sub)) with (ST + 1368 + 160 * sub) in PE2, PE3 by lia.
pose proof (rw_cells_bound _ _ _ _ PE2) as BPE. rewrite cells_size_f32, LE2 in BPE.
pose proof (f32_as_blob _ _ _ 40%nat PE2 LE2) as PEB. clear PE2.
call (nmemset_specZ (ST + 1368 + 160 * sub) 160 0 _ _); [exact PEB | assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. clear BPE.
match goal with H : rw_cells _ ?mm (ST + 1368 + 160 * sub) [CB _ _] |- _ =>
destruct (rw_cells_CB_f32 rsegs _ _ 40 _ H) as (ez & Lez & PE2); clear H end.
clear LE2.

zstep. rewrite sx32_small by (unfold int31; lia).
zstep.
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a0v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
remember a0v as na eqn:Ena end.
assert (NA : bv_unsigned na = 18446744073709551615 - (ST + 1368 + 160 * sub)).
{ subst na. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia. }
zstep.
destruct (voc_loop_inv (nb_voc_offset st) olp ltac:(lia) OLR) as (vf & HV & RV). rewrite HV. unfold NB_SUBFRAME_SIZE in RV |- *.
pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY) as LSS. unfold NBSTATE_SIZEOF in LSS.
zstep. unfold bv_lts. rewrite !zb_signed_small by lia.
lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) =>
eapply (evt_cut rsegs (vocl_post (ST + 1368 + 160 * sub) vf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) Q)
end.
{ destruct (Z_lt_ge_dec 39 (nb_voc_offset st)) as [GE40 | LT40].
- if_true_x. unfold VOC_FUEL in HV. rewrite voc_loop_step in HV.
replace (nb_voc_offset st <? NB_SUBFRAME_SIZE) with false in HV by (symmetry; apply Z.ltb_ge; unfold NB_SUBFRAME_SIZE; lia).
cbv beta iota in HV. injection HV as <-.
zstep.
apply evt_done. unfold vocl_post. sf_eexists 7%nat. split; [reflexivity|].
split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [assumption|]. split; [assumption|].
split; [exact PE2|]. split; [exact Lez| exact P18].
- if_false_x. unfold VOC_FUEL in HV. rewrite voc_loop_step in HV.
replace (nb_voc_offset st <? NB_SUBFRAME_SIZE) with true in HV by (symmetry; apply Z.ltb_lt; unfold NB_SUBFRAME_SIZE; lia).
cbv beta iota in HV.
eapply voc_pulse_loop with (fuel := 63%nat); try eassumption; try lia.
+ apply munch_refl. + apply wmono_refl. }
lazymatch type of PE1 with rw_cells _ ?mm _ _ => post_call rsegs mm end.
cbv beta delta [callR]. try rename MI0 into MI. try clear PE2. try clear Lez. try clear P18.
match goal with H : rw_cells _ _ (ST + 1368 + 160 * sub) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into PE2; rename L into LE2' end.
match goal with H : rw_cells _ _ (ST + 2948) _ |- _ => rename H into P18 end.

zstep. zstep. zstep. zstep.
lazymatch type of P17 with rw_cells _ _ _ (f32 ?vc) =>
destruct vc as [|v0 [|v1 [|v2 [|vx vrest]]]]; try (cbn in Lvoc; lia) end.
rewrite !f32_cons, f32_nil in P17.
pose proof (rw_cells_bound _ _ _ _ PE2) as BPE. rewrite cells_size_f32, LE2' in BPE.
pose proof (rw_cells_bound _ _ _ _ FI) as BFI. rewrite cells_size_f32, Lfinn in BFI.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of PE2 with rw_cells _ _ _ (f32 ?ws) =>
lazymatch type of FI with rw_cells _ _ _ (f32 ?is0) =>
destruct ws as [|xw0 wrest] eqn:Ews; [cbn in LE2'; lia|];
destruct is0 as [|iw0 irest] eqn:Eis; [cbn in Lfinn; lia|];
call (vmix_loop (ST + 1368 + 160 * sub) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc wrest [] irest [] 0
(ST + 1368 + 160 * sub) (usp + -416));
[ cbn [length] in *; lia | reflexivity | cbn [length] in *; lia | reflexivity | lia | lia | exact NA
| lia | lia | lia
| assumption | assumption | apply munch_refl | apply wmono_refl
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact PE2]
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact FI]
| exact P17 | ]
end end end.
try clear PE2. try clear FI. try clear P17. clear LE2' Lfinn Ews Eis BPE BFI Lvoc. try rename MI0 into MI.
match goal with H : rw_cells _ _ (ST + 1368 + 160 * sub) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into PE2; rename L into LE2 end.
match goal with H : rw_cells _ _ (usp + -416) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FI; rename L into Lfinn end.
match goal with H : rw_cells _ _ (ST + 2936) (f32 ?ws), L : length ?ws = 3%nat |- _ => rename H into P17; rename L into Lvoc end.

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
replace (vf + -40) with (vf - 40) by lia. unfold boxed in OLP.
apply evt_done. close_cut 7.
Qed.
End Seg.
