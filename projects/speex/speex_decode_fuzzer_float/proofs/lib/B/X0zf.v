(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X09f X09e X091.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X08o.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0sz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0wg X0wh X0w8 X0yt X0x2
X0zp X0zs X0zc X0zd X0zu X0ze.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).
Ltac slia1h := first [ lia | match goal with H : hid (_ \/ _) |- _ => unfold hid in H; lia end ].
Ltac slia_ch := lazymatch goal with |- _ /\ _ => split; [slia1h | slia_ch] | |- True => exact I | |- _ => slia1h end.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); slia_ch.
Local Ltac tlia ::= tlia_one.
Definition PC_NBD_D : Z := 0xa2000.

Section QCopy.
Variables (ST f usp : Z).
Variables (ra gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variable fc : bv 32.
Variable m : mem.
Variable s : nbslots.
Variable ql : list word.
Hypothesis LQL : length ql = 10%nat.
Hypothesis OBQ : aobj bsegs m (ST + 2040) 40.
Hypothesis Q8 : (ST + 2040) mod 8 = 0.
Hypothesis QP : 0 < ST.
Hypothesis FP0 : 0 < f.
Hypothesis FQ : f + 200 < 2^63.
Hypothesis SFQ : ST + 2080 <= f + 160 \/ f + 200 <= ST + 2040.
Hypothesis QLO : ST + 2080 <= usp + -576.
Hypothesis E272 : v272 s = Z_to_bv 64 (f + 160).
Hypothesis E280 : v280 s = Z_to_bv 64 (ST + 2040).
Local Notation W := [(ST + 2040, ST + 2080)].
Definition qcopy_R (a0 a1 a4 a5 : word) : bvmap 5 word :=
mkR ra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 (Z_to_bv 64 (18446744073709551615 - (ST + 2040))) (Z_to_bv 64 40)
a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6.
Definition qcopy_post : machine_state -> Prop :=
fun ms' => exists (a0' a4' a5' : word) (F' : bvmap 5 word) (m' : mem) (oq : list word),
ms' = MS (qcopy_R a0' (Z_to_bv 64 40) a4' a5') F' (Z_to_bv 64 0xa2000) fc None m' (seg_rom bsegs)
/\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ rw_cells bsegs m' (ST + 2040) (f32 oq) /\ length oq = 10%nat.

Lemma qcopy_loop : forall (rest dn qd qr : list word) (x q a0 a4 a5 : word) (off : Z) F m1,
ql = qd ++ q :: qr -> length qd = length dn -> length rest = length qr -> off = 4 * Z.of_nat (length dn) ->
munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 (usp + -576) (slot_cells s) ->
rw_cells bsegs m1 (f + 160) (f32 qd) -> rw_cells bsegs m1 (f + 160 + off) (f32 (q :: qr)) ->
rw_cells bsegs m1 (ST + 2040) (f32 dn) -> rw_cells bsegs m1 (ST + 2040 + off) (f32 (x :: rest)) ->
evt bsegs qcopy_post (MS (qcopy_R a0 (Z_to_bv 64 off) a4 a5) F (Z_to_bv 64 0xa1fb4) fc None m1 (seg_rom bsegs)).
Proof using LQL OBQ Q8 QP FP0 FQ SFQ QLO E272 E280.
induction rest as [|x' rest IH]; intros dn qd qr x q a0 a4 a5 off F m1 Hql LQD LR Hoff MU OF WM MI FR QD QX DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ QX) as BQX; rewrite cells_size_f32 in BQX; cbn [length] in BQX;
pose proof (f_equal (@length word) Hql) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *;
unfold qcopy_R; rewrite !f32_cons, ?f32_nil in X;
pose proof FR as FR0; unfold slot_cells in FR0; rewrite E272, E280 in FR0.
- destruct qr; [|cbn [length] in LR; lia]. cbn [length] in HL, LR.
chk_hint OBQ.
pose proof QX as QH. rewrite f32_cons in QH. chunk_uncons QH as Q1. clear QH.
bato 0xa1fdc. astep. chk_merge OBQ 4.
bato 0xa1fe8. astep. try sh_if.
bato 0xa2000.
replace (off + 4) with 40 by lia.
unfold qcopy_post, qcopy_R. finish.
+ chunk_snoc DONE X. f32_fold_snoc DONE. exact DONE.
+ rewrite length_app. cbn [length] in *. lia.
- destruct qr as [|q' qr]; [cbn [length] in LR; lia|]. cbn [length] in HL, LR.
chk_hint OBQ.
pose proof QX as QH. rewrite f32_cons in QH. chunk_uncons QH as Q1. clear QH.
bato 0xa1fdc. astep. chk_merge OBQ 4.
bato 0xa1fe8. astep. cbn [length]. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
clear Q1. rewrite f32_cons in QX. chunk_uncons QX as QX1. chunk_snoc QD QX1.
replace (ST + 2040 + off + 4) with (ST + 2040 + (off + 4)) in * by lia.
replace (f + 160 + off + 4) with (f + 160 + (off + 4)) in * by lia.
rewrite <- f32_cons in X. f32_fold_snoc DONE. f32_fold_snoc QD.
clear FR0.
eapply (IH _ (qd ++ [q]) qr x' q' _ _ _ (off + 4)); try eassumption.
all: try (rewrite Hql, <- app_assoc; reflexivity).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End QCopy.

Lemma nbd_c1 : forall {ptr : Type} (usp lo ST A f : Z) (gp tp : word) (st : nb_state ptr) (s : nbslots) (last_ol_gain : word) (ql oq0 : list word)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) F fc (m : mem),
usp < 2^63 -> lo <= usp + -576 -> SH_HI <= lo -> aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo ->
hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
0 < f -> f mod 64 = 0 -> f + 2048 <= lo -> hidp (ST + NBSTATE_SIZEOF <= f \/ f + 2048 <= ST) ->
rw_cells bsegs m (usp + -576) (slot_cells s) -> v88 s = Z_to_bv 64 ST -> v272 s = Z_to_bv 64 (f + 160) -> v280 s = Z_to_bv 64 (ST + 2040) ->
rw_cells bsegs m ST (nb_hdr_cells A_speex_nb_mode st last_ol_gain) ->
rw_cells bsegs m (f + 160) (f32 ql) -> length ql = 10%nat ->
rw_cells bsegs m (ST + 2040) (f32 oq0) -> length oq0 = 10%nat ->
(nb_first st = 0 \/ nb_first st = 1) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m' : mem) (a0' a1' a2' a3' a4' a5' : word) F' (oq : list word),
ms = MS (R_B2c usp ST A gp tp xra t0 t1 t2 a0' a1' a2' a3' a4' a5' a6 t3 t4 t5 t6) F' (Z_to_bv 64 PC_NBD_D) fc None m' (seg_rom bsegs)
/\ munch [(usp + -544, usp + -528); (ST + 2040, ST + 2080)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' (usp + -576) (slot_cells (sset 40 (Z_to_bv 64 (ST + 8)) (sset 32 (Z_to_bv 64 (Z.shiftr (ST + 8) 3 + SHB)) s)))
/\ rw_cells bsegs m' ST (nb_hdr_cells A_speex_nb_mode st last_ol_gain)
/\ rw_cells bsegs m' (f + 160) (f32 ql)
/\ rw_cells bsegs m' (ST + 2040) (f32 oq) /\ length oq = 10%nat)
(MS (R_B2c usp ST A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_C) fc None m (seg_rom bsegs)).
Proof.
intros ptr usp lo ST A f gp tp st s last_ol_gain ql oq0 xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 F fc m SPH LO LOS OBS S8 SP0 SLO SSH F0 F64 FLO SFA
FR E88 E272 E280 HDR QL LQL OQ LOQ FST MI.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof (SSH : _ \/ _) as SSH'. pose proof (SFA : _ \/ _) as SFA'.
unfold R_B2c, PC_NBD_C, PC_NBD_D, NBSTATE_SIZEOF, nb_hdr_cells in *.
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v88 v272 v280] in E88, E272, E280. subst w88 w272 w280.
unfold slot_cells in *. cbn [sset Z.eqb Pos.eqb v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232
v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in *.
pose proof (munch_refl [(usp + -544, usp + -528); (ST + 2040, ST + 2080)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -528); (ST + 2040, ST + 2080)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
pose proof (rw_cells_bound _ _ _ _ FR) as BFR. cbn [cells_size csize Nat.add] in BFR.
chk_hint OBS.
bato 0xa1f9c. destruct FST as [E0|E1].
- rewrite E0. rewrite sx32_small by (unfold int31; lia).
bato 0xa2000.
apply evt_done. do 9 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact FR|]. split; [rewrite E0 in HDR; exact HDR|]. split; [exact QL|]. split; [exact OQ| exact LOQ].
- rewrite E1. rewrite sx32_small by (unfold int31; lia).
bato 0xa1fb4.
rewrite (zb_lxor_ones (ST + 2040)) by lia.
assert (Eql : exists q qr, ql = q :: qr) by (destruct ql as [|q qr]; [cbn in LQL; lia| eauto]). destruct Eql as (q & qr & Eql).
destruct oq0 as [|x rest]; [cbn in LOQ; lia|].
replace (ST + 2040) with (ST + 2040 + 0) in OQ at 1 by lia.
pose proof QL as QLc. rewrite Eql in QLc. replace (f + 160) with (f + 160 + 0) in QLc at 1 by lia.
pose proof LQL as LQLc. rewrite Eql in LQLc. cbn [length] in LQLc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc ST 2968 OBS MUc (shfree_of_aobj bsegs W m ST 2968 OF OBS)) as OBSc;
assert (OBQc : aobj bsegs mc (ST + 2040) 40) by (eapply aobj_sub; [exact OBSc | lia | lia]);
pose proof (munch_refl [(ST + 2040, ST + 2080)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
callc (qcopy_loop ST f usp xra gp tp t0 t1 t2 a6 (Z_to_bv 64 (ST + 2248)) (Z_to_bv 64 0) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32))
(Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5) (Z_to_bv 64 ((ST + 2904) ≫ 3 + SHB)) (Z_to_bv 64 146592) (Z_to_bv 64 (ST + 2184)) t3 t4 t5 t6 fc mc
(sset 40 (Z_to_bv 64 (ST + 8)) (sset 32 (Z_to_bv 64 (Z.shiftr (ST + 8) 3 + SHB))
(NBS w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 ST) w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232
w240 w248 w256 w264 (Z_to_bv 64 (f + 160)) (Z_to_bv 64 (ST + 2040)) w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368)))
ql LQL OBQc ltac:(clear - S8; Z.div_mod_to_equations; lia) SP0 F0 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl eq_refl
rest [] [] qr x q _ _ _ 0 _ mc Eql eq_refl ltac:(cbn in LOQ |- *; lia) eq_refl MU0 ltac:(cbn; unfold SH_LO, SH_HI in *; lia) WM0 ltac:(assumption)
FR ltac:(rewrite f32_nil; apply rw_cells_nil; lia) QLc ltac:(rewrite f32_nil; apply rw_cells_nil; lia) OQ) (clear OQ QLc)
end
end.
rename PC into OQ1. rename POST into LOQ1.
apply evt_done. do 9 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact FR|]. split; [rewrite E1 in HDR; exact HDR|]. split; [exact QL|]. split; [exact OQ1| exact LOQ1].
Qed.

Notation segD_olp := A.X08o.segD_olp.
Notation segD_b1 := A.X08o.segD_b1.
Notation segD_b2 := A.X08o.segD_b2.
Notation segD_b3 := A.X08o.segD_b3.
Notation segD_st := A.X08o.segD_st.
Notation segD_bits := A.X08o.segD_bits.
Notation segD4_st := A.X08o.segD4_st.

Lemma seqz15 : forall u, 0 <= u < 16 -> Z.b2z ((u + -15) mod 18446744073709551616 <? 1) = (if u =? 15 then 1 else 0).
Proof.
intros u Hu. destruct (Z.eq_dec u 15) as [-> | NE]; [reflexivity|].
replace ((u + -15) mod 18446744073709551616) with (u + -15 + 18446744073709551616) by (apply Z.mod_unique with (q := -1); lia).
replace (u =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (u + -15 + 18446744073709551616 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma smrec_ints : forall mo r, smrec_at mo = Some r ->
let sm := smr_sm r in
(sm_lbr_pitch sm = 0 /\ sm_forced_pitch_gain sm = 1 /\ (mo = 1 \/ mo = 8))
\/ (sm_lbr_pitch sm = 0 /\ sm_forced_pitch_gain sm = 0 /\ mo = 2)
\/ (sm_lbr_pitch sm = -1 /\ sm_forced_pitch_gain sm = 0 /\ 3 <= mo <= 7).
Proof.
intros mo r H. unfold smrec_at in H. destruct (mo <? 1) eqn:K; [discriminate|]. apply Z.ltb_ge in K.
assert (C : mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8 \/ 9 <= mo) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | C]]]]]]]].
1-8: cbn in H; injection H as <-; cbn; lia.
exfalso. assert (Hx : nth_error nb_smrecs (Z.to_nat (mo - 1)) <> None) by congruence. apply nth_error_Some in Hx. cbn in Hx. lia.
Qed.
Lemma sx32_m1 : sx32 (Z_to_bv 64 (-1)) = Z_to_bv 64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Definition exp_postZ (elo eq : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mm : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(elo, eq)] mm m' /\ wmono bsegs mm m' /\ mem_inv bsegs m' /\ frm0 fc' /\ stk bsegs m' elo eq.
Lemma exp_specZ : forall (elo eq : Z)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FF : bvmap 5 word) (fcc : bv 32) (mm : mem),
stk bsegs mm elo eq -> elo + 16 <= eq -> 0 <= eq < 2^64 -> mem_inv bsegs mm -> frm0 fcc ->
evt bsegs (exp_postZ elo eq ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mm)
(MS (mkR ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FF (Z_to_bv 64 X0sz.A_exp) fcc None mm (seg_rom bsegs)).
Proof.
intros until mm. intros XSTK XLO XHq XMI XFRM.
pose proof (X0sz.exp_proofA elo ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FF fcc mm) as H.
rewrite !unsigned_lit in H by lia. unfold X0sz.EXP_DEPTH in H. specialize (H XSTK XLO XMI XFRM).
eapply evt_mono; [exact H|]. intros ms' P. unfold X0sz.exp_postA in P. rewrite !unsigned_lit in P by lia.
destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & E & MU & WM & MI' & FRM' & STK' & _).
unfold exp_postZ. do 18 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'| exact STK'].
Qed.

Section D.
Context {ptr : Type}.
Variables (usp lo ST A D f sf BSZ : Z).
Variables gp tp : word.
Variable m : mem.
Hypothesis LO : lo <= usp - 576 - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis F0 : 0 < f.
Hypothesis F64 : f mod 64 = 0.
Hypothesis FLO : f + 2048 <= lo.
Hypothesis FAT : f + 2048 <= APP_TOP.
Hypothesis FTOP : IMG_TOP_B <= f.
Hypothesis FSH : hidp (f + 2048 <= SH_LO \/ SH_HI <= f).
Hypothesis Esf : sf = Z.shiftr f 3 + SHB.
Hypothesis OBS : aobj bsegs m ST NBSTATE_SIZEOF.
Hypothesis S8 : ST mod 8 = 0.
Hypothesis SP0 : 0 < ST.
Hypothesis SLO : ST + NBSTATE_SIZEOF <= lo.
Hypothesis STTOP : IMG_TOP_B <= ST.
Hypothesis SSH : hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST).
Hypothesis SFA : hidp (ST + NBSTATE_SIZEOF <= f \/ f + 2048 <= ST).
Hypothesis SSA : hidp (ST + NBSTATE_SIZEOF <= sf \/ sf + 256 <= ST).
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis ATOP : IMG_TOP_B <= A.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis AFA : hidp (A + BITS_SIZEOF <= f \/ f + 2048 <= A).
Hypothesis ASA : hidp (A + BITS_SIZEOF <= sf \/ sf + 256 <= A).
Hypothesis SAA : hidp (ST + NBSTATE_SIZEOF <= A \/ A + BITS_SIZEOF <= ST).
Hypothesis OBD : aobj bsegs m D BSZ.
Hypothesis DLO : D + BSZ <= lo.
Hypothesis DFA : hidp (D + BSZ <= f \/ f + 2048 <= D).
Hypothesis DSA : hidp (D + BSZ <= sf \/ sf + 256 <= D).
Hypothesis SDA : hidp (ST + NBSTATE_SIZEOF <= D \/ D + BSZ <= ST).
Hypothesis LC : lib_consts m.
Hypothesis NTA : nb_tabs_acc m.

Definition nbD_W : list (Z * Z) := [(usp + -704, usp + -200); (A, A + 48); (ST + 2952, ST + 2956); (sf, sf + 256)].

Lemma nbD_shf : forall o n, 0 <= o -> o + n <= 140737488355328 -> (o + n <= f \/ f + 2048 <= o) -> shfree nbD_W o n.
Proof using LO LOS SPH F0 F64 FAT FSH Esf ASH SSH OBS.
intros o n O0 O1 OFA. pose proof (ASH : _ \/ _) as ASH'. pose proof (SSH : _ \/ _) as SSH'. pose proof OBS as (OS0 & OS1 & _).
unfold nbD_W, NBSTATE_SIZEOF, APP_TOP, BITS_SIZEOF in *.
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply (shfree_cons_sh _ _ _ _ _ f 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite Esf, shad_shiftr; lia | rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact OFA |].
apply shfree_nil.
Qed.
Lemma nbD_fw : Forall (fun iv : Z * Z => snd iv <= 0xf8380 \/ 0xfce00 <= fst iv) nbD_W.
Proof using LO LOS FTOP ATOP STTOP SP0 F0 F64 FAT Esf.
unfold nbD_W, IMG_TOP_B, SH_HI, APP_TOP in *.
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. unfold SH_LO in SW.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.
Ltac nbD_setup ST0 CC :=
unfold nbD_W, NBSTATE_SIZEOF, BITS_SIZEOF, nb_cfg_cells, nb_tail_cells in *;
pose proof LOS as LOS'; unfold SH_HI in LOS'; pose proof ST0 as (STa & STb & _);
pose proof OBS as (OS0 & OS1 & _); pose proof OBA as (OA0 & OA1 & _); pose proof OBD as (OD0 & OD1 & _); unfold APP_TOP in *;
pose proof FTOP as FTOP'; unfold IMG_TOP_B in FTOP'; pose proof ATOP as ATOP'; unfold IMG_TOP_B in ATOP'; pose proof STTOP as STTOP'; unfold IMG_TOP_B in STTOP';
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW;
rewrite <- shad_shiftr, <- Esf in SW; change (2048 / 8) with 256 in SW; unfold SH_LO, SH_HI in SW;
pose proof CC as (G1 & G2 & G3 & G4);
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *;
pose proof nbD_shf as SHF; unfold nbD_W in SHF;
pose proof (SHF ST 2968 ltac:(lia) ltac:(lia) SFA) as SFR;
pose proof (SHF A 48 ltac:(lia) ltac:(lia) AFA) as SFRA;
pose proof (SHF D BSZ ltac:(lia) ltac:(lia) DFA) as SFRD;
pose proof nbD_fw as FW; unfold nbD_W in FW;
repeat match goal with H : hidp ?P |- _ => change (hid P) in H end; unfold SH_LO, SH_HI in FSH, SSH, ASH.
Ltac nbD_cc G1 G2 G3 G4 := unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))).
Ltac slots_open s FR :=
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368];
unfold slot_cells in *;
cbn [sset Z.eqb Pos.eqb v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232
v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in *.

Lemma nbd_d1 : forall (st : nb_state ptr) (b : bits_st ptr) (r : smrec) (s : nbslots) (pad : list byte)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -576) -> client_constsB m1 ->
bits_rep bsegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells bsegs m1 (usp + -576) (slot_cells s) ->
v288 s = Z_to_bv 64 A -> v312 s = Z_to_bv 64 (ST + 2248) -> v328 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v336 s = Z_to_bv 64 (ST + 2240) ->
v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells bsegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
smrec_at (nb_submodeID st) = Some r ->
evt bsegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a6' t3' t4' t5' t6' : word),
ms = MS (R_B2c usp ST A gp tp xra' t0' t1' t2' a0' a1' a2' a3' a4' (Z_to_bv 64 (segD_olp (smr_sm r) b)) a6' t3' t4' t5' t6')
F (Z_to_bv 64 0xa236c) fc None m2 (seg_rom bsegs)
/\ munch [(usp + -704, usp + -200); (A, A + 48)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -576) /\ client_constsB m2
/\ bits_rep bsegs m2 A D (segD_b1 (smr_sm r) b) /\ bits_ok (segD_b1 (smr_sm r) b) /\ sb_buf_size (segD_b1 (smr_sm r) b) = BSZ
/\ rw_cells bsegs m2 (usp + -576) (slot_cells s)
/\ rw_cells bsegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad))
(MS (R_B2c usp ST A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_D) fc None m1 (seg_rom bsegs)).
Proof using All.
intros st b r s pad xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC REP OKB SZ FR E288 E312 E328 E336 E344 CFG SAT.
nbD_setup ST0 CC. unfold PC_NBD_D, R_B2c in *.
set (mo := nb_submodeID st) in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SPz & SP1 & SP8 & LORD & SMC). clear SMC.
pose proof (smrec_ints mo r SAT) as INTS. cbv zeta in INTS.
destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR. clear NTR.
unfold IMG_TOP_B in SP1. set (SP := smr_ptr r) in *. set (sm := smr_sm r) in *.
pose proof (SHF 1016704 208 ltac:(lia) ltac:(lia) ltac:(lia)) as SFM.
pose proof (SHF SP 88 ltac:(lia) ltac:(lia) ltac:(lia)) as SFP.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof (aobj_munch bsegs _ m m1 _ _ OBS MU0 SFR) as OBS1. pose proof (aobj_munch bsegs _ m m1 _ _ NTM MU0 SFM) as NTM1.
pose proof (aobj_munch bsegs _ m m1 _ _ OBR MU0 SFP) as OBR1.
slots_open s FR. subst w288 w312 w328 w336 w344.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof (munch_refl [(usp + -704, usp + -200); (A, A + 48)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
bato 0xa202c.
rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small mo) by lia.
bato 0xa2034. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa2070.
chk_hint NTM. bato 0xa207c.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa2084.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (lib_consts_munch W m mc LC MUc FW) as LCc; pose proof (sub_ptr_read mc mo LCc ltac:(lia)) as RD;
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (smrec_facts mo r SAT))))))) mc LCc) as SMCc end.
unfold NB_SUBMODES_PTR, A_nb_mode in RD. replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia. rewrite EP in RD. fold SP in RD, SMCc.
unfold smrec_cells in SMCc. cbv zeta in SMCc. fold sm in SMCc.
astep. clear RD.
bato 0xa20bc.
assert (LBR : sm_lbr_pitch sm = 0 \/ sm_lbr_pitch sm = -1) by (clear - INTS; lia).
unfold A.X08o.segD_olp, A.X08o.segD_b1. fold sm.
destruct LBR as [LBR|LBR]; rewrite LBR; cbn [Z.eqb negb].
2: { rewrite sx32_m1. bato 0xa236c.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OKB|]. split; [exact SZ|].
split; [exact FR| exact CFG]. }
rewrite sx32_small by (unfold int31; lia).
bato 0xa20c4. astep.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MUc SFRA) as OBAc;
pose proof (aobj_munch bsegs W m mc _ _ OBD MUc SFRD) as OBDc;
assert (REPc : bits_rep bsegs mc A D b) by (exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE)));
assert (CCc : client_constsB mc) by (nbD_cc G1 G2 G3 G4)
end.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
callc (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 7 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REPc OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb) (clear REPc OBJ DAT).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 7)) |- _ => subst x end.
fold (uv b 7). fold (ub b 7) in *.
pose proof (ub_ok b 7 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^7) with 128 in VR.
bato 0xa20d0. rewrite swrap32_small by lia. bato 0xa236c.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact POST|]. split; [exact OK1|]. split; [exact (eq_trans SZ1 SZ)|].
split; [exact FR| exact CFG].
Qed.

Definition R_DB (s2 s3 s4 s5 s7 s8 s10 s11 : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 s2) (Z_to_bv 64 s3) (Z_to_bv 64 s4) (Z_to_bv 64 s5) (Z_to_bv 64 SHB) (Z_to_bv 64 s7) (Z_to_bv 64 s8)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 s10) (Z_to_bv 64 s11) t3 t4 t5 t6.

Lemma nbd_d2 : forall (st : nb_state ptr) (b : bits_st ptr) (r : smrec) (s : nbslots) (pad : list byte) (olp : Z)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a6 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -576) -> client_constsB m1 -> frm0 fc ->
bits_rep bsegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells bsegs m1 (usp + -576) (slot_cells s) ->
v192 s = Z_to_bv 64 (ST + 2184) -> v288 s = Z_to_bv 64 A -> v328 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v336 s = Z_to_bv 64 (ST + 2240) ->
v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells bsegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
smrec_at (nb_submodeID st) = Some r ->
evt bsegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ms = MS (R_DB 0 (ST + 2912) A A (ST + 2184) 5 0x23ca0 (ST + 2184) xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 0xa245c) fc' None m2 (seg_rom bsegs)
/\ munch [(usp + -704, usp + -200); (A, A + 48)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -576) /\ client_constsB m2 /\ frm0 fc'
/\ bits_rep bsegs m2 A D (if negb (sm_forced_pitch_gain (smr_sm r) =? 0) then ub b 4 else b)
/\ bits_ok (if negb (sm_forced_pitch_gain (smr_sm r) =? 0) then ub b 4 else b)
/\ sb_buf_size (if negb (sm_forced_pitch_gain (smr_sm r) =? 0) then ub b 4 else b) = BSZ
/\ rw_cells bsegs m2 (usp + -576) (slot_cells (sset 208 (Z_to_bv 64 olp) s))
/\ rw_cells bsegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad))
(MS (R_B2c usp ST A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 olp) a6 t3 t4 t5 t6) F (Z_to_bv 64 0xa236c) fc None m1 (seg_rom bsegs)).
Proof using All.
intros st b r s pad olp xra t0 t1 t2 a0 a1 a2 a3 a4 a6 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM REP OKB SZ FR E192 E288 E328 E336 E344 CFG SAT.
nbD_setup ST0 CC. unfold R_B2c, R_DB in *.
set (mo := nb_submodeID st) in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SPz & SP1 & SP8 & LORD & SMC). clear SMC.
pose proof (smrec_ints mo r SAT) as INTS. cbv zeta in INTS.
destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR. clear NTR.
unfold IMG_TOP_B in SP1. set (SP := smr_ptr r) in *. set (sm := smr_sm r) in *.
pose proof (SHF 1016704 208 ltac:(lia) ltac:(lia) ltac:(lia)) as SFM.
pose proof (SHF SP 88 ltac:(lia) ltac:(lia) ltac:(lia)) as SFP.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof (aobj_munch bsegs _ m m1 _ _ OBS MU0 SFR) as OBS1. pose proof (aobj_munch bsegs _ m m1 _ _ NTM MU0 SFM) as NTM1.
pose proof (aobj_munch bsegs _ m m1 _ _ OBR MU0 SFP) as OBR1.
slots_open s FR. subst w192 w288 w328 w336 w344.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof (munch_refl [(usp + -704, usp + -200); (A, A + 48)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
bato 0xa2398. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small mo) by lia.
bato 0xa23a0. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa23dc.
chk_hint NTM. bato 0xa23e8.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa23f0.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (lib_consts_munch W m mc LC MUc FW) as LCc; pose proof (sub_ptr_read mc mo LCc ltac:(lia)) as RD;
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (smrec_facts mo r SAT))))))) mc LCc) as SMCc end.
unfold NB_SUBMODES_PTR, A_nb_mode in RD. replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia. rewrite EP in RD. fold SP in RD, SMCc.
unfold smrec_cells in SMCc. cbv zeta in SMCc. fold sm in SMCc.
astep. clear RD.
bato 0xa2430.
assert (FPG : sm_forced_pitch_gain sm = 0 \/ sm_forced_pitch_gain sm = 1) by (clear - INTS; lia).
destruct FPG as [FPG|FPG]; rewrite FPG; cbn [Z.eqb negb]; rewrite sx32_small by (unfold int31; lia).
{ bato 0xa245c.
apply evt_done. do 19 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [nbD_cc G1 G2 G3 G4|]. split; [eassumption|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OKB|]. split; [exact SZ|].
split; [exact FR| exact CFG]. }
bato 0xa243c. astep.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MUc SFRA) as OBAc;
pose proof (aobj_munch bsegs W m mc _ _ OBD MUc SFRD) as OBDc;
assert (REPc : bits_rep bsegs mc A D b) by (exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE)));
assert (CCc : client_constsB mc) by (nbD_cc G1 G2 G3 G4)
end.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
callc (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REPc OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb) (clear REPc OBJ DAT).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 4)) |- _ => subst x end.
fold (uv b 4). fold (ub b 4) in *.
pose proof (ub_ok b 4 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^4) with 16 in VR.
bato 0xa245c.
apply evt_done. do 19 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|]. split; [eassumption|].
split; [exact POST|]. split; [exact OK1|]. split; [exact (eq_trans SZ1 SZ)|].
split; [exact FR| exact CFG].
Qed.

Lemma nbd_seg_unpoison : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rs : list byte) F fc (m1 : mem),
rw_cells bsegs m1 sf (nbd_shadow_g true false true false false false false false rs) -> mem_inv bsegs m1 ->
evt bsegs (fun ms => exists (m2 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa2538) fc None m2 (seg_rom bsegs)
/\ munch [(sf, sf + 256)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ rw_cells bsegs m2 sf (nbd_shadow_g true false true true true true false false rs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa2484) fc None m1 (seg_rom bsegs)).
Proof using ST f sf.
intros until m1. intros FRS MI.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 256)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
bato 0xa2538.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma nbd_d3 : forall (b : bits_st ptr) (rs : list byte) (s : nbslots)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -576) -> client_constsB m1 -> frm0 fc ->
bits_rep bsegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells bsegs m1 (usp + -576) (slot_cells s) -> v200 s = Z_to_bv 64 sf ->
rw_cells bsegs m1 sf (nbd_shadow_g true false true false false false false false rs) ->
evt bsegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ms = MS (R_DB 0 (ST + 2912) A A (ST + 2184) 5 0x23ca0 (ST + 2184) xra' t0' t1' t2' (Z_to_bv 64 sf) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 0xa2538) fc' None m2 (seg_rom bsegs)
/\ munch [(usp + -704, usp + -576); (A, A + 48); (sf, sf + 256)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -576) /\ client_constsB m2 /\ frm0 fc'
/\ bits_rep bsegs m2 A D (ub b 5) /\ bits_ok (ub b 5) /\ sb_buf_size (ub b 5) = BSZ
/\ rw_cells bsegs m2 sf (nbd_shadow_g true false true true true true false false rs))
(MS (R_DB 0 (ST + 2912) A A (ST + 2184) 5 0x23ca0 (ST + 2184) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa245c) fc None m1 (seg_rom bsegs)).
Proof using All.
intros b rs s xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM REP OKB SZ FR E200 FRS.
nbD_setup ST0 CC. unfold R_DB in *.
slots_open s FR. subst w200.
pose proof FRS as FRS0. unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS. cbn [map repeat app] in FRS. clear FRS0.
pose proof (munch_refl [(usp + -704, usp + -576); (A, A + 48); (sf, sf + 256)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
bato 0xa2464. astep.
pose proof (aobj_munch bsegs _ m m1 _ _ OBA MU0 SFRA) as OBAc. pose proof (aobj_munch bsegs _ m m1 _ _ OBD MU0 SFRD) as OBDc.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
assert (CCc : client_constsB m1) by (nbD_cc G1 G2 G3 G4).
call (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 5)) |- _ => subst x end.
fold (uv b 5). fold (ub b 5) in *.
pose proof (ub_ok b 5 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^5) with 32 in VR.
destruct POST as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OK1 as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
bato 0xa2478.
match goal with H : stk bsegs _ lo (usp + -576) |- _ => destruct (stk_split bsegs _ lo (usp + -704) (usp + -576) H ltac:(lia)) as [STKa STKb]; clear H end.
astep.
call (exp_specZ (usp + -704) (usp + -576)).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: eassumption.
match goal with H : stk bsegs _ (usp + -704) (usp + -576) |- _ => pose proof (stk_merge bsegs _ lo (usp + -704) (usp + -576) STKa H ltac:(lia)) as STK3; clear H STKa end.
replace (ret_pc (Z_to_bv 64 664700)) with (Z_to_bv 64 664700) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bato 0xa2484.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => call (nbd_seg_unpoison _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rs _ _ mc FRS) end.
{ assumption. }
rename POST into FRS'.
apply evt_done. do 18 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|]. split; [eassumption|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OK1|]. split; [exact (eq_trans SZ1 SZ)|].
exact FRS'.
Qed.

Lemma nbd_d4 : forall (st : nb_state ptr) (b : bits_st ptr) (s : nbslots) (pad pad2 : list byte) (olp : Z)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -576) -> client_constsB m1 ->
bits_rep bsegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells bsegs m1 (usp + -576) (slot_cells s) ->
v56 s = Z_to_bv 64 f -> v208 s = Z_to_bv 64 olp -> v312 s = Z_to_bv 64 (ST + 2248) -> v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells bsegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
rw_cells bsegs m1 (ST + 2948) (nb_tail_cells st pad2) ->
1 <= nb_submodeID st <= 8 ->
evt bsegs (fun ms => exists (m2 : mem) (xra' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F',
ms = MS (R_DB 0 f (ST + 2952) A (ST + 2184) 5 0x23ca0 (ST + 2184) xra' (Z_to_bv 64 olp) t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F'
(Z_to_bv 64 0xa25d0) fc None m2 (seg_rom bsegs)
/\ munch [(usp + -704, usp + -200); (A, A + 48); (ST + 2952, ST + 2956)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -576) /\ client_constsB m2
/\ bits_rep bsegs m2 A D (if nb_submodeID st =? 1 then ub b 4 else b) /\ bits_ok (if nb_submodeID st =? 1 then ub b 4 else b)
/\ sb_buf_size (if nb_submodeID st =? 1 then ub b 4 else b) = BSZ
/\ rw_cells bsegs m2 (usp + -576) (slot_cells s)
/\ rw_cells bsegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad)
/\ rw_cells bsegs m2 (ST + 2948) (nb_tail_cells (segD4_st st b) pad2))
(MS (R_DB 0 (ST + 2912) A A (ST + 2184) 5 0x23ca0 (ST + 2184) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa2538) fc None m1 (seg_rom bsegs)).
Proof using All.
intros st b s pad pad2 olp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC REP OKB SZ FR E56 E208 E312 E344 CFG TAIL MO1.
nbD_setup ST0 CC. unfold R_DB in *.
set (mo := nb_submodeID st) in *.
pose proof (aobj_munch bsegs _ m m1 _ _ OBS MU0 SFR) as OBS1.
slots_open s FR. subst w56 w208 w312 w344.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof (munch_refl [(usp + -704, usp + -200); (A, A + 48); (ST + 2952, ST + 2956)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
bato 0xa2558. rewrite sx32_small by (unfold int31; lia).
replace (Z.land (ST + 2248) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; clear - S8; Z.div_mod_to_equations; lia).
bato 0xa2564.
astep.
unfold A.X08o.segD4_st. fold mo.
destruct (mo =? 1) eqn:K1; [apply Z.eqb_eq in K1 | apply Z.eqb_neq in K1]; sh_if.
-
bato 0xa2570. astep.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MUc SFRA) as OBAc;
pose proof (aobj_munch bsegs W m mc _ _ OBD MUc SFRD) as OBDc;
assert (REPc : bits_rep bsegs mc A D b) by (exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE)));
assert (CCc : client_constsB mc) by (nbD_cc G1 G2 G3 G4)
end.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
callc (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REPc OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb) (clear REPc OBJ DAT).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 4)) |- _ => subst x end.
fold (uv b 4). fold (ub b 4) in *.
pose proof (ub_ok b 4 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^4) with 16 in VR.
destruct POST as ((rj1 & Lrj1 & OBJ1) & (bs1 & DAT1 & Hbs1) & SIDE1). unfold bits_cells in OBJ1.
assert (Lbs1 : Z.of_nat (length bs1) = BSZ) by (pose proof OK1 as OK'; unfold bits_ok in OK'; rewrite Hbs1, zlength_map_unsigned in OK'; lia).
bato 0xa2590. rewrite ?(Z.mod_small (uv b 4)) by lia. rewrite (seqz15 (uv b 4) VR).
bato 0xa25ac. rewrite sx32_small by (unfold int31; lia).
bato 0xa25d0.
apply evt_done. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact (conj (ex_intro _ rj1 (conj Lrj1 OBJ1)) (conj (ex_intro _ bs1 (conj DAT1 Hbs1)) SIDE1))|]. split; [exact OK1|]. split; [exact (eq_trans SZ1 SZ)|].
split; [exact FR|]. split; [exact CFG|]. destruct st; exact TAIL.
-
replace (1 <? mo) with true by (symmetry; apply Z.ltb_lt; lia).
bato 0xa25d0.
apply evt_done. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OKB|]. split; [exact SZ|].
split; [exact FR|]. split; [exact CFG|]. destruct st; exact TAIL.
Qed.

Definition slots_D5 (olp : Z) (s : nbslots) : nbslots :=
sset 296 (Z_to_bv 64 40) (sset 320 (Z_to_bv 64 (olp + 1073741824)) (sset 136 (Z_to_bv 64 (Z.shiftr (ST + 2184) 3 + SHB)) (sset 24 (Z_to_bv 64 3)
(sset 80 (Z_to_bv 64 (f + 480)) (sset 72 (Z_to_bv 64 (ST + 2948)) (sset 216 (Z_to_bv 64 (ST + 2228)) (sset 128 (Z_to_bv 64 (ST + 2208))
(sset 104 (Z_to_bv 64 (f + 992)) (sset 184 (Z_to_bv 64 (f + 768)) (sset 232 (Z_to_bv 64 (f + 544)) (sset 152 (Z_to_bv 64 (f + 240))
(sset 120 (Z_to_bv 64 (f + 48)) (sset 256 (Z_to_bv 64 (f + 32)) (sset 264 (Z_to_bv 64 0) s)))))))))))))).

Lemma nbd_d5 : forall (s : nbslots) (olp : Z)
(xra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -576) -> client_constsB m1 -> frm0 fc ->
rw_cells bsegs m1 (usp + -576) (slot_cells s) ->
v56 s = Z_to_bv 64 f -> v64 s = Z_to_bv 64 (ST + 2047) -> v168 s = Z_to_bv 64 (ST + 2032) -> v176 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB) ->
0 <= olp <= 144 ->
evt bsegs (fun ms => exists (m2 : mem) (xra' t0' t1' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word) F' fc',
ms = MS (mkR xra' (Z_to_bv 64 (usp + -576)) gp tp t0' t1' (Z_to_bv 64 0) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5'
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
(Z_to_bv 64 3) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2952)) (Z_to_bv 64 (f + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6') F' (Z_to_bv 64 0xa2700) fc' None m2 (seg_rom bsegs)
/\ munch [(usp + -704, usp + -200)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -576) /\ client_constsB m2 /\ frm0 fc'
/\ rw_cells bsegs m2 (usp + -576) (slot_cells (slots_D5 olp s)))
(MS (R_DB 0 f (ST + 2952) A (ST + 2184) 5 0x23ca0 (ST + 2184) xra (Z_to_bv 64 olp) t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa25d0) fc None m1 (seg_rom bsegs)).
Proof using All.
intros s olp xra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM FR E56 E64 E168 E176 OLP.
nbD_setup ST0 CC. unfold slots_D5, R_DB in *.
slots_open s FR. subst w56 w64 w168 w176.
pose proof (munch_refl [(usp + -704, usp + -200)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
bato 0xa25f4. astep. join 0xa25fc 0 1.
bato 0xa261c. astep. join 0xa2624 0 1.
bato 0xa2700.
rewrite (swrap32_small (olp + 1073741824)) in FR by lia.
apply evt_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|]. split; [eassumption|]. exact FR.
Qed.

Ltac slia ::= (try unfold BITS_SIZEOF, nbD_W in * ); cbn [outside] in *; slia_ch.

Definition slots_D (olp : Z) (s : nbslots) : nbslots := slots_D5 olp (sset 208 (Z_to_bv 64 olp) s).

Theorem nbd_cd : forall (st : nb_state ptr) (b : bits_st ptr) (r : smrec) (s : nbslots) (pad pad2 rs : list byte)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -576) -> client_constsB m1 -> frm0 fc ->
bits_rep bsegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells bsegs m1 (usp + -576) (slot_cells s) ->
v56 s = Z_to_bv 64 f -> v64 s = Z_to_bv 64 (ST + 2047) -> v168 s = Z_to_bv 64 (ST + 2032) -> v176 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB) ->
v192 s = Z_to_bv 64 (ST + 2184) -> v200 s = Z_to_bv 64 sf -> v288 s = Z_to_bv 64 A -> v312 s = Z_to_bv 64 (ST + 2248) ->
v328 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v336 s = Z_to_bv 64 (ST + 2240) -> v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells bsegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
rw_cells bsegs m1 (ST + 2948) (nb_tail_cells st pad2) ->
rw_cells bsegs m1 sf (nbd_shadow_g true false true false false false false false rs) ->
smrec_at (nb_submodeID st) = Some r ->
evt bsegs (fun ms => exists (m2 : mem) (xra' t0' t1' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word) F' fc',
ms = MS (mkR xra' (Z_to_bv 64 (usp + -576)) gp tp t0' t1' (Z_to_bv 64 0) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5'
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
(Z_to_bv 64 3) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2952)) (Z_to_bv 64 (f + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6') F' (Z_to_bv 64 0xa2700) fc' None m2 (seg_rom bsegs)
/\ munch nbD_W m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -576) /\ client_constsB m2 /\ frm0 fc'
/\ bits_rep bsegs m2 A D (segD_bits st (smr_sm r) b) /\ bits_ok (segD_bits st (smr_sm r) b) /\ sb_buf_size (segD_bits st (smr_sm r) b) = BSZ
/\ rw_cells bsegs m2 (usp + -576) (slot_cells (slots_D (segD_olp (smr_sm r) b) s))
/\ rw_cells bsegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad)
/\ rw_cells bsegs m2 (ST + 2948) (nb_tail_cells (segD_st st (smr_sm r) b) pad2)
/\ rw_cells bsegs m2 sf (nbd_shadow_g true false true true true true false false rs))
(MS (R_B2c usp ST A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_D) fc None m1 (seg_rom bsegs)).
Proof using All.
intros st b r s pad pad2 rs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM REP OKB SZ FR E56 E64 E168 E176 E192 E200 E288 E312 E328 E336 E344
CFG TAIL FRS SAT.
pose proof (smrec_facts _ r SAT) as (_ & MO1 & _).
pose proof (smrec_ints _ r SAT) as INTS. cbv zeta in INTS.
nbD_setup ST0 CC. unfold PC_NBD_D in *.
set (sm := smr_sm r) in *.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS. cbn [map repeat app] in FRS.
pose proof (munch_refl [(usp + -704, usp + -200); (A, A + 48); (ST + 2952, ST + 2956); (sf, sf + 256)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
callc (nbd_d1 st b r s pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 MU0 WM0 MI ST0 CC REP OKB SZ FR E288 E312 E328 E336 E344 CFG SAT) (clear REP FR CFG).
rename PC1 into REP1. rename PC2 into OK1. rename PC3 into SZ1. rename PC4 into FR1. rename POST into CFG1. rename PC into ST1. rename PC0 into CC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with MIc : mem_inv bsegs mc |- _ =>
callc (nbd_d2 st (segD_b1 sm b) r s pad (segD_olp sm b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc MU0 WM0 MIc ST1 CC1 FRM REP1 OK1 SZ1 FR1 E192 E288 E328 E336 E344 CFG1 SAT)
(clear REP1 FR1 CFG1) end end.
rename PC2 into REP2. rename PC3 into OK2. rename PC4 into SZ2. rename PC5 into FR2. rename POST into CFG2. rename PC into ST2. rename PC0 into CC2. rename PC1 into FRM2.
fold sm in REP2, OK2, SZ2. fold (A.X08o.segD_b2 sm b) in REP2, OK2, SZ2.
unfold nb_cfg_cells in CFG2.
lazymatch goal with |- evt _ _ (MS _ ?Fc _ ?fcc _ ?mc _) => match goal with MIc : mem_inv bsegs mc |- _ =>
callc (nbd_d3 (segD_b2 sm b) rs (sset 208 (Z_to_bv 64 (segD_olp sm b)) s) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fcc mc MU0 WM0 MIc ST2 CC2 FRM2 REP2 OK2 SZ2 FR2 E200 FRS)
(clear REP2 FRS) end end.
rename PC2 into REP3. rename PC3 into OK3. rename PC4 into SZ3. rename POST into FRS3. rename PC into ST3. rename PC0 into CC3. rename PC1 into FRM3.
fold (A.X08o.segD_b3 sm b) in REP3, OK3, SZ3.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS3. cbn [map repeat app] in FRS3.
lazymatch goal with |- evt _ _ (MS _ ?Fc _ ?fcc _ ?mc _) => match goal with MIc : mem_inv bsegs mc |- _ =>
callc (nbd_d4 st (segD_b3 sm b) (sset 208 (Z_to_bv 64 (segD_olp sm b)) s) pad pad2 (segD_olp sm b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fcc mc MU0 WM0 MIc ST3 CC3
REP3 OK3 SZ3 FR2 E56 eq_refl E312 E344 CFG2 TAIL MO1)
(clear REP3 FR2 CFG2 TAIL) end end.
rename PC1 into REP4. rename PC2 into OK4. rename PC3 into SZ4. rename PC4 into FR4. rename PC5 into CFG4. rename POST into TAIL4. rename PC into ST4. rename PC0 into CC4.
fold (A.X08o.segD_bits st sm b) in REP4, OK4, SZ4.
unfold nb_cfg_cells in CFG4. unfold nb_tail_cells in TAIL4.
destruct REP4 as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OK4 as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
assert (OLP : 0 <= segD_olp sm b <= 144).
{ unfold A.X08o.segD_olp. destruct (negb (sm_lbr_pitch sm =? -1)); [| lia]. pose proof (A.X082.ub_ok b 7 OKB ltac:(lia)) as (_ & _ & VR). change (2^7) with 128 in VR. lia. }
lazymatch goal with |- evt _ _ (MS _ ?Fc _ ?fcc _ ?mc _) => match goal with MIc : mem_inv bsegs mc |- _ =>
callc (nbd_d5 _ (segD_olp sm b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fcc mc MU0 WM0 MIc ST4 CC4 FRM3 FR4 E56 E64 E168 E176 OLP) (clear FR4) end end.
rename POST into FR5.
apply evt_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OK4|]. split; [exact SZ4|].
split; [exact FR5|]. split; [exact CFG4|]. split; [exact TAIL4| exact FRS3].
Qed.
End D.
