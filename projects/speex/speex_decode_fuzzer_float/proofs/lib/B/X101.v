(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X05m X09f X06d X09e X091.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0x2 X0yt
X0zq X0zp X0zs X0zc X0zu X0wh X0yu X124 X0yd X11g.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition R_EL (usp ST FF sub : Z) (gp tp xra t0 t1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 (Z_to_bv 64 sub) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
s2 s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6.

Definition slots_EL (ST OUT A FF SF olp bp sub : Z) (s : nbslots) : Prop :=
v0 s = Z_to_bv 64 0 /\ v24 s = Z_to_bv 64 3 /\ v32 s = Z_to_bv 64 (Z.shiftr (ST + 8) 3 + SHB) /\ v40 s = Z_to_bv 64 (ST + 8)
/\ v48 s = Z_to_bv 64 FF /\ v56 s = Z_to_bv 64 FF /\ v64 s = Z_to_bv 64 (ST + 2047) /\ v72 s = Z_to_bv 64 (ST + 2948) /\ v80 s = Z_to_bv 64 (FF + 480)
/\ v88 s = Z_to_bv 64 ST /\ v96 s = Z_to_bv 64 0xfe6c /\ v104 s = Z_to_bv 64 (FF + 992) /\ v120 s = Z_to_bv 64 (FF + 48) /\ v128 s = Z_to_bv 64 (ST + 2208)
/\ v136 s = Z_to_bv 64 (Z.shiftr (ST + 2184) 3 + SHB) /\ v144 s = Z_to_bv 64 (ST + 12) /\ v152 s = Z_to_bv 64 (FF + 240)
/\ v160 s = Z_to_bv 64 (Z.shiftr (ST + 12) 3 + SHB) /\ v168 s = Z_to_bv 64 (ST + 2032) /\ v176 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)
/\ v184 s = Z_to_bv 64 (FF + 768) /\ v192 s = Z_to_bv 64 (ST + 2184) /\ v200 s = Z_to_bv 64 SF /\ v208 s = Z_to_bv 64 olp /\ v216 s = Z_to_bv 64 (ST + 2228)
/\ v232 s = Z_to_bv 64 (FF + 544) /\ v240 s = Z_to_bv 64 OUT /\ v256 s = Z_to_bv 64 (FF + 32) /\ v264 s = Z_to_bv 64 (40 * sub) /\ v272 s = Z_to_bv 64 (FF + 160)
/\ v280 s = Z_to_bv 64 (ST + 2040) /\ v288 s = Z_to_bv 64 A /\ v296 s = Z_to_bv 64 bp /\ v304 s = Z_to_bv 64 0 /\ v312 s = Z_to_bv 64 (ST + 2248)
/\ v320 s = Z_to_bv 64 (olp + 1073741824) /\ v328 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) /\ v336 s = Z_to_bv 64 (ST + 2240)
/\ v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) /\ v368 s = Z_to_bv 64 FF.

Lemma slots_EL_of_E : forall ST OUT A FF SF olp s, slots_E ST OUT A FF SF olp 40 s -> slots_EL ST OUT A FF SF olp 40 0 s.
Proof.
intros ST OUT A FF SF olp s H. unfold slots_E, slots_EL in *. decompose [and] H. repeat split; try assumption.
Qed.

Section CutEL.
Context {ptr : Type}.

Definition at_EL (X : @nbinvA ptr) (r : smrec) (mo olp bp sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t0 t1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff),
ms = MS (R_EL (x_usp X) (x_st X) (x_ff X) sub (x_gp X) (x_tp X) xra t0 t1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6)
Fx (Z_to_bv 64 PC_NBD_E) fc None m (seg_rom bsegs)
/\ frm0 fc /\ nbctx X m st b j ows sws s ff SC_E /\ slots_EL (x_st X) (x_out X) (x_A X) (x_ff X) (x_sf X) olp bp sub s
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub <= 4.

Lemma at_EL_of_E : forall X r mo olp st b ms, at_E_A X r mo olp 40 0 st b ms -> at_EL X r mo olp 40 0 st b ms.
Proof.
intros X r mo olp st b ms (Fx & fc & m & xra & t0 & t1 & a0 & a1 & a2 & a3 & a4 & a5 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & E & FRM & CTX & SL & SM & MO & BP & OLP & SUB).
exists Fx, fc, m, xra, t0, t1, a0, a1, a2, a3, a4, a5, (Z_to_bv 64 3), (Z_to_bv 64 (x_ff X)), (Z_to_bv 64 (x_st X + 2952)), (Z_to_bv 64 (x_st X + 2184)),
(Z_to_bv 64 (Z.shiftr (x_st X + 2904) 3 + SHB)), t3, t4, t5, t6, j, ows, sws, s, ff.
split; [rewrite E; reflexivity|]. split; [exact FRM|]. split; [exact CTX|]. split; [exact (slots_EL_of_E _ _ _ _ _ _ _ SL)|].
split; [exact SM|]. split; [exact MO|]. split; [exact BP|]. split; [exact OLP| exact SUB].
Qed.
End CutEL.

Definition nbe_e_asan_memset : Z := 0x6689c.
Definition RA_nbe_mset1 : Z := 0xa279c.

Definition isv_cur (isv sub : Z) : Z := if isv =? 0 then 0 else isv + 160 * sub.

Definition slots_Ea (excp sub : Z) (s : nbslots) : nbslots :=
sset 224 (Z_to_bv 64 sub) (sset 248 (Z_to_bv 64 excp) s).

Lemma nbe_a : forall (usp lo ST OUT A FF SF olp bp sub isv : Z) (gp tp xra t0 t1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> slots_EL ST OUT A FF SF olp bp sub s ->
rw_cells bsegs m (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))] -> rw_cells bsegs m (ST + 2184) [C8 (Z_to_bv 64 isv)] ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
0 <= isv < 2^63 -> 0 <= sub < 4 ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_nbe_mset1) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 (Z_to_bv 64 sub) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 0) (Z_to_bv 64 160) a3 a4 a5
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
(Z_to_bv 64 1) s3 (Z_to_bv 64 (40 * sub)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 nbe_e_asan_memset) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -576, usp + -200)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -576)
/\ rw_cells bsegs m1 (usp + -576) (slot_cells (slots_Ea (ST + 1368) sub s)))
(MS (R_EL usp ST FF sub gp tp xra t0 t1 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_E) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL SLE EXC ISV OBS S8 SPOS SLO SOFF ISB SUB ST0 LO LOS SPH MI.
unfold R_EL, PC_NBD_E, RA_nbe_mset1, nbe_e_asan_memset, NBSTATE_SIZEOF in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SLE.
destruct SLE as (E0 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192 & E200 & E208 & E216
& E232 & E240 & E256 & E264 & E272 & E280 & E288 & E296 & E304 & E312 & E320 & E328 & E336 & E344 & E368).
subst w0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w232 w240 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w368.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
bato 0xa2768.
unfold isv_cur. rewrite ?Z.shiftl_mul_pow2 in * by lia. change (2 ^ 2) with 4 in *.
destruct (Z.eqb_spec isv 0) as [I0 | I0].
- subst isv. astep. cbn [Z.eqb]. bato 0x6689c.
replace (sub * 40 * 4) with (160 * sub) in * by lia. replace (sub * 40) with (40 * sub) in * by lia.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. exact SL.
- astep. sh_if. bato 0x6689c.
replace (sub * 40 * 4) with (160 * sub) in * by lia. replace (sub * 40) with (40 * sub) in * by lia.
replace (160 * sub + isv) with (isv + 160 * sub) by lia.
replace (isv =? 0) with false by (symmetry; apply Z.eqb_neq; exact I0).
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. exact SL.
Qed.

Definition RA_nbe_ltp : Z := 0xa2a2c.

Definition nbe_pmin (lbr olp : Z) : Z := if lbr =? -1 then 17 else if lbr =? 0 then olp else Z.max 16 (olp - lbr) + 1.
Definition nbe_pmax (lbr olp : Z) : Z := if lbr =? -1 then 144 else if lbr =? 0 then olp else Z.min 144 (olp + lbr).

Definition slots_Eb (ST : Z) (s : nbslots) : nbslots := sset 112 (Z_to_bv 64 (Z.shiftr (ST + 2208) 3 + SHB)) s.

Lemma nbe_row_lbr : forall r, In r nb_smrecs -> sm_lbr_pitch (smr_sm r) = -1 \/ sm_lbr_pitch (smr_sm r) = 0.
Proof. intros r H. cbn [nb_smrecs In] in H. repeat (destruct H as [<- | H]; [cbn; tauto|]). destruct H. Qed.

Lemma nbe_b : forall {ptr : Type} (usp lo ST OUT A FF SF olp bp sub isv mo : Z) (r : smrec) (k : ltp_kind) (st : nb_state ptr) (pad : list byte) (lpg lp0 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells (slots_Ea (ST + 1368) sub s)) -> slots_EL ST OUT A FF SF olp bp sub s ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
sm_ltp_unquant (smr_sm r) = Some k ->
rw_cells bsegs m (ST + 12) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m (ST + 2204) [C4 lp0; C4 lpg] ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_constsB m ->
(sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144) -> 0 <= sub < 4 ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 48 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) F1 (t0' t2' : word) (jk : list byte),
ms = MS (mkR (Z_to_bv 64 RA_nbe_ltp) (Z_to_bv 64 (usp + -624)) gp tp t0' (Z_to_bv 64 (ltp_entryA k)) t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp))
(Z_to_bv 64 (nbe_pmax (sm_lbr_pitch (smr_sm r)) olp)) (Z_to_bv 64 (smr_ltp_par r)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48))
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F1 (Z_to_bv 64 (ltp_entryA k)) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -624, usp + -576); (usp + -576, usp + -200)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -624)
/\ rw_cells bsegs m1 (usp + -576) (slot_cells (slots_Eb ST (slots_Ea (ST + 1368) sub s)))
/\ rw_cells bsegs m1 (usp + -624) (ltp_args_cells A (Z_to_bv 64 0) (40 * sub) ++ [CB 8 jk]))
(MS (mkR (Z_to_bv 64 RA_nbe_mset1) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 (Z_to_bv 64 (40 * sub)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL SLE CFG EMO SAT LTK CL LPG OBS S8 SPOS SLO SOFF LC NTA CC HOLP SUB F0 F64 FLO ST0 LO LOS SPH U32 MI.
unfold RA_nbe_ltp, RA_nbe_mset1, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa279c)) with (Z_to_bv 64 0xa279c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -624, usp + -576); (usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -624, usp + -576); (usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SLE.
destruct SLE as (E0 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192 & E200 & E208 & E216
& E232 & E240 & E256 & E264 & E272 & E280 & E288 & E296 & E304 & E312 & E320 & E328 & E336 & E344 & E368).
subst w0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w232 w240 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w368.
unfold slots_Ea, slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC).
unfold IMG_TOP_B in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof ST0 as (STa & STb & _).
carve_frame 48%nat ST0. rename FR into SA.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in SA; [| reflexivity]. cbn [mk_CB_cells app] in SA.
bato 0xa27cc. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small mo) by lia.
bato 0xa27d4. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa2810.
chk_hint NTM.
bato 0xa281c.
rewrite EMO.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa2824.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
unfold smrec_cells in ROW. cbv zeta in ROW. rewrite LTK in ROW.
set (SP := smr_ptr r) in *.
bato 0xa2840.
rewrite ?(Z.mod_small (SP + 40)) by lia.
chk_hint OBR.
bato 0xa284c.
bato 0xa2854.
assert (LEP : 0x10000 <= ltp_entryA k < 0x630200 /\ ltp_entryA k mod 2 = 0) by (destruct k; (cbv [ltp_entryA A_forced_pitch_unquant A_pitch_unquant_3tap]; split; [lia| reflexivity])).
astep. bato 0xa285c. astep. sh_if.
bato 0xa2884.
bato 0xa2888. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
bato 0xa2890. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa28cc.
chk_hint NTM.
bato 0xa28d8.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa28e0.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
bato 0xa2900. rewrite ?(Z.mod_small SP) by lia.
chk_hint OBR.
bato 0xa2904.
bato 0xa2910.
destruct (nbe_row_lbr r INR) as [LB | LB]; rewrite LB in *.
- destruct HOLP as [(_ & ->) | (HN & _)]; [| exfalso; exact (HN eq_refl)].
bato 0xa298c. rewrite ?(Z.mod_small (SP + 40)) by lia.
chk_hint OBR.
bato 0xa29bc. rewrite ?(Z.mod_small (SP + 48)) by lia.
chk_hint OBR.
bato 0xa2a28.
astep.
replace (ret_pc (Z_to_bv 64 (ltp_entryA k))) with (Z_to_bv 64 (ltp_entryA k)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 LEP)]).
change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in SA.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. split; [exact SL| exact SA].
- destruct HOLP as [(HN & _) | (_ & HOL)]; [discriminate HN|].
bato 0xa298c. rewrite ?(Z.mod_small (SP + 40)) by lia.
chk_hint OBR.
bato 0xa29bc. rewrite ?(Z.mod_small (SP + 48)) by lia.
chk_hint OBR.
bato 0xa2a28.
astep.
replace (ret_pc (Z_to_bv 64 (ltp_entryA k))) with (Z_to_bv 64 (ltp_entryA k)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 LEP)]).
change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in SA.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. split; [exact SL| exact SA].
Qed.

Definition nbe_san_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo p : Z) (n : nat) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(p, p + 4 * Z.of_nat n); (usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc' /\ rw_cells bsegs m' p (f32 xs') /\ length xs' = n.

Ltac nsan_leaf K :=
try (match goal with
| X : rw_cells _ _ _ (C4 _ :: C4 _ :: _) |- _ => chunk_uncons X as X1
| X : rw_cells _ _ _ (C4 _ :: f32 (_ :: _)) |- _ => chunk_uncons X as X1
end);
eapply K; eassumption.
Ltac nsan_store OB K :=
ato 0xa5ce4; astep; chk_merge OB 4;
ato 0xa5cec; nsan_leaf K.
Ltac nsan_low OB K :=
ato 0xa5ccc; astep; let B3 := fresh "B3" in if_cases B3;
[ nsan_store OB K
| ato 0xa5cd8; astep; let B4 := fresh "B4" in if_cases B4; [ nsan_store OB K | nsan_store OB K ] ].
Ltac nsan_elem OB K :=
astep; sh_if; astep;
(lazymatch goal with NZ : (_ <? 1) = false |- _ => rewrite NZ end); cbn [Z.b2z];
ato 0xa5cac; astep; chk_merge OB 4;
ato 0xa5cb8; astep; let B1 := fresh "B1" in if_cases B1;
[ nsan_low OB K
| ato 0xa5cc0; astep; let B2 := fresh "B2" in if_cases B2;
[ ato 0xa5cec; nsan_leaf K | nsan_low OB K ] ].

Section SG.
Variables (xs : list word) (p usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation n := (length xs).
Hypothesis N1 : 1 <= Z.of_nat n < 2^31.
Hypothesis OBX : aobj bsegs m p (4 * Z.of_nat n).
Hypothesis X4 : p mod 4 = 0.
Hypothesis XPOS : 0 < p.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : p + 4 * Z.of_nat n <= SH_LO \/ SH_HI <= p.
Hypothesis XAP : p + 4 * Z.of_nat n <= lo \/ usp <= p.
Local Notation POST := (nbe_san_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo p n m).
Local Notation W := [(p, p + 4 * Z.of_nat n); (usp + -16, usp)].

Lemma nsan_loop : forall (rest dn : list word) x (kz off : Z) (j0 : list byte) (t0 t1 t2 a7 t3 t4 t5 t6 : word) (Fz : bvmap 5 word) fc m1,
n = (length dn + S (length rest))%nat -> kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -16) -> rw_cells bsegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells bsegs m1 p (f32 dn) -> rw_cells bsegs m1 (p + off) (f32 (x :: rest)) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 kz) (Z_to_bv 64 (p + off)) (Z_to_bv 64 1) (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 (p + off)) a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fz (Z_to_bv 64 0xa5c8c) fc None m1 (seg_rom bsegs)).
Proof using N1 OBX X4 XPOS LO SPH XAP XSH.
induction rest as [|x' rest IH]; intros dn x kz off j0 t0 t1 t2 a7 t3 t4 t5 t6 Fz fc m1 Hn Hkz Hoff FRM MU OF WM MI ST FR DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
assert (NZ : (p + off <? 1) = false) by (apply Z.ltb_ge; lia).
-
assert (TAIL : forall (y0 y1 y7 : word) (Fy : bvmap 5 word) fc' m' (w : word),
frm0 fc' -> mem_inv bsegs m' -> munch W m m' -> wmono bsegs m m' ->
stk bsegs m' lo (usp + -16) -> rw_cells bsegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells bsegs m' p (f32 dn) -> rw_cells bsegs m' (p + off) [C4 w] ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (S (length (@nil word))))) (Z_to_bv 64 (p + off)) (Z_to_bv 64 1) (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 (p + off)) y7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fy (Z_to_bv 64 0xa5cec) fc' None m' (seg_rom bsegs))).
{ clear FRM MI MU WM ST FR DONE X BX fc m1 STa STb NZ. intros y0 y1 y7 Fy fc m1 w FRM MI MU WM ST FR DONE X.
pose proof ST as (STa & STb & _).
ato 0xa5cf8. astep. try sh_if.
ato 0xa5d24. astep. release_frame FR ST usp. astep. astep.
unfold nbe_san_post. finish.
all: try (chunk_snoc DONE X; change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE; exact DONE).
all: try (rewrite ?length_app; cbn [length] in *; lia). }
rewrite !f32_cons, ?f32_nil in X.
nsan_elem OBX TAIL.
-
assert (TAIL : forall (y0 y1 y7 : word) (Fy : bvmap 5 word) fc' m' (w : word),
frm0 fc' -> mem_inv bsegs m' -> munch W m m' -> wmono bsegs m m' ->
stk bsegs m' lo (usp + -16) -> rw_cells bsegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells bsegs m' p (f32 dn) -> rw_cells bsegs m' (p + off) [C4 w] ->
rw_cells bsegs m' (p + off + 4) (f32 (x' :: rest)) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (S (length (x' :: rest))))) (Z_to_bv 64 (p + off)) (Z_to_bv 64 1) (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 (p + off)) y7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fy (Z_to_bv 64 0xa5cec) fc' None m' (seg_rom bsegs))).
{ clear FRM MI MU WM ST FR DONE X BX fc m1 STa STb NZ. intros y0 y1 y7 Fy fc m1 w FRM MI MU WM ST FR DONE X X'.
pose proof ST as (STa & STb & _).
pose proof (rw_cells_bound _ _ _ _ X') as BX'. rewrite cells_size_f32 in BX'. cbn [length] in BX'.
ato 0xa5cf8. astep. cbn [length]. sh_if.
chunk_snoc DONE X. change [C4 w] with (f32 [w]) in DONE. rewrite <- f32_app in DONE.
replace (p + off + 4) with (p + (off + 4)) in * by lia.
eapply (IH (dn ++ [w]) x' _ (off + 4)); try eassumption.
all: try (rewrite ?length_app; cbn [length] in *; lia). }
rewrite f32_cons in X.
nsan_elem OBX TAIL.
Qed.

Lemma nsan_walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells bsegs m p (f32 xs) -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= p -> client_constsB m -> mem_inv bsegs m ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat n)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_sanitize_values32) fc None m (seg_rom bsegs)).
Proof using N1 OBX X4 XPOS LO LOS SPH XSH XAP.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc X FRM ST PTOP (G1 & G2 & _) MI.
unfold B_sanitize_values32, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. unfold IMG_TOP_B in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
assert (P0 : (0 <? p) = true) by (apply Z.ltb_lt; lia).
assert (P3 : (Z.land p 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - X4; Z.div_mod_to_equations; lia).
ato 0xa5c8c. rewrite ?P0, ?P3. cbn [Z.b2z]. change (Z.land 1 1) with 1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (p + 0)) (Z_to_bv 64 1) (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 (p + 0)) a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) by (rewrite Z.add_0_r; reflexivity)
end.
replace p with (p + 0) in X at 1 by lia. rewrite Exs in X.
eapply (nsan_loop rest [] x _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs; cbn [length]; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End SG.

Definition R_BPX (usp ST FF isv sub : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6.
Definition nbe_bp_post (usp ST FF isv sub lo bp p : Z) (gp tp xra t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) (m : mem) : machine_state -> Prop :=
fun ms => exists (a0 a1 a2 a3 a4 a5 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (bp' : Z),
ms = MS (R_BPX usp ST FF isv sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0xa2dfc) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ munch [(usp + -576, usp + -200)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (usp + -576) (slot_cells (sset 296 (Z_to_bv 64 bp') s)) /\ (bp' = bp \/ bp' = p).

Definition JXA (segs : list Segment) (pc : Z) (m : mem) (F : bvmap 5 word) (fc : bv 32)
(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 v x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : machine_state -> Prop :=
fun ms => exists (y3 y4 : word),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 v y3 y4 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom segs).
Ltac absjoin pcJ v :=
lazymatch goal with |- evt ?segs _ (MS ?R ?F _ ?fc _ ?mc _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 _ _ _ ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
eapply (evt_cut segs (JXA segs pcJ mc F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 v x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31))
end
end.

Lemma negw_guard : forall x, -2^31 < x < 0 ->
bv_swrap 32 (0 - x mod 18446744073709551616) = - x /\ Z_to_bv 64 (0 - x mod 18446744073709551616) = Z_to_bv 64 (- x).
Proof.
intros x Hx. split.
- unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.modulo Z.div]. Z.div_mod_to_equations. lia.
- rewrite <- (Z_to_bv_mod64 (0 - x mod 18446744073709551616)), <- (Z_to_bv_mod64 (- x)). f_equal. Z.div_mod_to_equations. lia.
Qed.

Ltac absd pcJ :=
try change (2 ^ 1) with 2; try change (2 ^ 2) with 4; try change (2 ^ 3) with 8;
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?x) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
absjoin pcJ (Z_to_bv 64 (Z.abs x));
[ astep; let B0 := fresh "B0" in if_cases B0;
[ zify_cond B0; apply evt_done; do 2 eexists; rewrite Z.abs_eq by lia; reflexivity
| zify_cond B0; astep; astep;
let NG1 := fresh "NG1" in let NG2 := fresh "NG2" in
destruct (negw_guard x ltac:(lia)) as [NG1 NG2]; rewrite NG1, NG2;
bato pcJ; apply evt_done; do 2 eexists; rewrite Z.abs_neq by lia; reflexivity ]
| let y3 := fresh "y3" in let y4 := fresh "y4" in intros ? (y3 & y4 & ->) ]
end
end.

Lemma srl30_guard : forall x, 0 <= x < 2^29 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (x + 536870912)) 30) = 0.
Proof.
intros x Hx. unfold bv_wrap, bv_modulus. cbn -[Z.modulo Z.shiftr].
rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Definition JXA13 (segs : list Segment) (pc : Z) (m : mem) (F : bvmap 5 word) (fc : bv 32)
(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 v x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : machine_state -> Prop :=
fun ms => exists (y1 y3 : word),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y1 v y3 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom segs).
Ltac absjoin13 pcJ v :=
lazymatch goal with |- evt ?segs _ (MS ?R ?F _ ?fc _ ?mc _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 _ _ _ ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
eapply (evt_cut segs (JXA13 segs pcJ mc F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 v x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31))
end
end.
Ltac absd13 pcJ :=
try change (2 ^ 1) with 2; try change (2 ^ 2) with 4; try change (2 ^ 3) with 8;
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?x) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
absjoin13 pcJ (Z_to_bv 64 (Z.abs x));
[ astep; let B0 := fresh "B0" in if_cases B0;
[ zify_cond B0; apply evt_done; do 2 eexists; rewrite Z.abs_eq by lia; reflexivity
| zify_cond B0; astep; astep;
let NG1 := fresh "NG1" in let NG2 := fresh "NG2" in
destruct (negw_guard x ltac:(lia)) as [NG1 NG2]; rewrite NG1, NG2;
bato pcJ; apply evt_done; do 2 eexists; rewrite Z.abs_neq by lia; reflexivity ]
| let y3 := fresh "y3" in let y4 := fresh "y4" in intros ? (y3 & y4 & ->) ]
end
end.
Definition JXA23 (segs : list Segment) (pc : Z) (m : mem) (F : bvmap 5 word) (fc : bv 32)
(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 v x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : machine_state -> Prop :=
fun ms => exists (y2 y3 : word),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 v y2 y3 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom segs).
Ltac absjoin23 pcJ v :=
lazymatch goal with |- evt ?segs _ (MS ?R ?F _ ?fc _ ?mc _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 _ _ _ ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
eapply (evt_cut segs (JXA23 segs pcJ mc F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 v x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31))
end
end.

Ltac absd23 pcJ :=
try change (2 ^ 1) with 2; try change (2 ^ 2) with 4; try change (2 ^ 3) with 8;
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?x) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
absjoin23 pcJ (Z_to_bv 64 (Z.abs x));
[ astep; let B0 := fresh "B0" in if_cases B0;
[ zify_cond B0; apply evt_done; do 2 eexists; rewrite Z.abs_eq by lia; reflexivity
| zify_cond B0; astep; astep;
let NG1 := fresh "NG1" in let NG2 := fresh "NG2" in
destruct (negw_guard x ltac:(lia)) as [NG1 NG2]; rewrite NG1, NG2;
bato pcJ; apply evt_done; do 2 eexists; rewrite Z.abs_neq by lia; reflexivity ]
| let y3 := fresh "y3" in let y4 := fresh "y4" in intros ? (y3 & y4 & ->) ]
end
end.

Section BP.
Variables (usp ST FF isv sub lo bp p : Z) (gp tp xra t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) (m : mem).
Hypothesis SL : rw_cells bsegs m (usp + -576) (slot_cells s).
Hypothesis E256 : v256 s = Z_to_bv 64 (FF + 32).
Hypothesis E96 : v96 s = Z_to_bv 64 0xfe6c.
Hypothesis E296 : v296 s = Z_to_bv 64 bp.
Hypothesis PIT : rw_cells bsegs m (FF + 32) [C4 (Z_to_bv 64 p)].
Hypothesis BPR : 17 <= bp <= 144.
Hypothesis PR : 17 <= p <= 144.
Hypothesis FLO : FF + 2048 <= lo.
Hypothesis FTOP : IMG_TOP_B <= FF.
Hypothesis ST0 : stk bsegs m lo (usp + -576).
Hypothesis LO : lo <= usp - 576.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis MI : mem_inv bsegs m.
Local Notation POST := (nbe_bp_post usp ST FF isv sub lo bp p gp tp xra t0 t1 t2 a6 a7 t3 t4 t5 t6 s m).

Ltac bp_open :=
unfold R_BPX; pose proof LOS as LOS'; unfold SH_HI in LOS'; pose proof FTOP as FTOP'; unfold IMG_TOP_B in FTOP';
pose proof ST0 as (STa & STb & _); pose proof SL as SL'; pose proof PIT as PIT';
pose proof E256 as E256'; pose proof E96 as E96'; pose proof E296 as E296';
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368];
cbn [v256 v96 v296] in E256', E96', E296'; subst w256 w96 w296;
unfold slot_cells in SL'; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL'.

Lemma nbe_rA : forall (a0 a1 a2 a3 a4 a5 : word) F fc, frm0 fc ->
evt bsegs POST (MS (R_BPX usp ST FF isv sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa2de8) fc None m (seg_rom bsegs)).
Proof using SL E256 E96 E296 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 a5 F fc FRM.
pose proof (munch_refl [(usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
bp_open.
bato 0xa2df0. rewrite sx32_small by (unfold int31; lia).
bato 0xa2df4. astep. if_cases B.
- bato 0xa2dfc. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [exact SL'| right; reflexivity].
- bato 0xa2dfc. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [exact SL'| right; reflexivity].
Qed.

Lemma nbe_r3 : forall (a0 a1 a2 a3 a4 a5 : word) F fc, frm0 fc ->
evt bsegs POST (MS (R_BPX usp ST FF isv sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa2cd8) fc None m (seg_rom bsegs)).
Proof using SL E256 E96 E296 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 a5 F fc FRM. pose proof (nbe_rA) as RA.
pose proof (munch_refl [(usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
unfold R_BPX in RA. bp_open.
bato 0xa2ce8. astep. if_cases B.
- bato 0xa2dfc. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [| left; reflexivity].
exact SL.
- bato 0xa2d08. rewrite sx32_small by (unfold int31; lia).
bato 0xa2d20.
absd 0xa2d38.
bato 0xa2d40. astep. if_cases B1; [apply RA; assumption|].
bato 0xa2d70.
absd 0xa2d88.
bato 0xa2d90. astep. if_cases B2; [apply RA; assumption|].
bato 0xa2da4. rewrite (srl30_guard bp) by lia.
bato 0xa2dc4.
absd13 0xa2ddc.
bato 0xa2de4. astep. if_cases B3; [| apply RA; assumption].
bato 0xa2dfc. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [| left; reflexivity].
exact SL.
Qed.

Lemma nbe_r2 : forall (a0 a1 a2 a3 a4 a5 : word) F fc, frm0 fc ->
evt bsegs POST (MS (R_BPX usp ST FF isv sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa2bc8) fc None m (seg_rom bsegs)).
Proof using SL E256 E96 E296 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 a5 F fc FRM. pose proof (nbe_rA) as RA. pose proof (nbe_r3) as R3.
unfold R_BPX in RA, R3. bp_open.
bato 0xa2be0. astep. if_cases B; [apply R3; assumption|].
bato 0xa2bec. rewrite sx32_small by (unfold int31; lia).
bato 0xa2c14.
absd 0xa2c2c.
bato 0xa2c34. astep. if_cases B1; [apply RA; assumption|].
bato 0xa2c64. absd 0xa2c7c.
bato 0xa2c84. astep. if_cases B2; [apply RA; assumption|].
bato 0xa2c94. rewrite (srl30_guard p) by lia.
bato 0xa2cb4. absd23 0xa2ccc.
bato 0xa2cd4. astep. if_cases B3; [apply RA; assumption| apply R3; assumption].
Qed.

Lemma nbe_r1 : forall (a0 a1 a2 a3 a4 a5 : word) F fc, frm0 fc ->
evt bsegs POST (MS (R_BPX usp ST FF isv sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa2ab8) fc None m (seg_rom bsegs)).
Proof using SL E256 E96 E296 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 a5 F fc FRM. pose proof (nbe_r2) as R2.
pose proof (munch_refl [(usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
unfold R_BPX in R2. bp_open.
astep. if_cases B; [apply R2; assumption|].
bato 0xa2ad8. rewrite sx32_small by (unfold int31; lia).
bato 0xa2af0. absd 0xa2b08.
bato 0xa2b10. astep. if_cases B1; [apply R2; assumption|].
bato 0xa2b40. absd 0xa2b58.
bato 0xa2b60. astep. if_cases B2; [apply R2; assumption|].
bato 0xa2b74. rewrite (srl30_guard bp) by lia.
bato 0xa2b94. absd13 0xa2bac.
bato 0xa2bb4. astep. if_cases B3; [apply R2; assumption|].
bato 0xa2bc0. rewrite sx32_small by (unfold int31; lia).
bato 0xa2dfc. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [exact SL'| right; reflexivity].
Qed.
End BP.

Lemma nbe_san40 : forall (xs : list word) (p usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
length xs = 40%nat -> aobj bsegs m p 160 -> p mod 4 = 0 -> 0 < p -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 160 <= SH_LO \/ SH_HI <= p) -> (p + 160 <= lo \/ usp <= p) ->
rw_cells bsegs m p (f32 xs) -> frm0 fc -> stk bsegs m lo usp -> IMG_TOP_B <= p -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(p, p + 160); (usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc' /\ rw_cells bsegs m' p (f32 xs') /\ length xs' = 40%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 40) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_sanitize_values32) fc None m (seg_rom bsegs)).
Proof.
intros until fc. intros L OB P4 PP LO LOS SPH XSH XAP X FRM ST PTOP CC MI.
replace (Z_to_bv 64 40) with (Z_to_bv 64 (Z.of_nat (length xs))) by (rewrite L; reflexivity).
eapply evt_mono.
- eapply (nsan_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m); rewrite ?L; try eassumption; try (cbn; lia).
- intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & xs' & E & MU & WM & MI' & ST' & FRM' & X' & LX').
rewrite L in MU, LX'. do 19 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact FRM'|]. split; [exact X'| exact LX'].
Qed.

Definition RA_nbe_san : Z := 0xa2a44.
Definition RA_nbe_mset2 : Z := 0xa2e0c.

Tactic Notation "joinb" constr(pcJ) :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut segs (JX segs pcJ mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ let B := fresh "B" in if_cases B; [ bato pcJ; jx_done | bato pcJ; jx_done ]
| try match goal with H : frm0 _ |- _ => clear H end;
let FRM := fresh "FRM" in intros ? (? & ? & ? & -> & FRM) ]
end.

Lemma nbe_c : forall (usp lo ST OUT A FF SF olp bp sub isv p : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) (jk : list byte)
(e32s pgs : list word) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v256 s = Z_to_bv 64 (FF + 32) -> v96 s = Z_to_bv 64 0xfe6c -> v296 s = Z_to_bv 64 bp ->
rw_cells bsegs m (usp + -624) (ltp_args_cells A (Z_to_bv 64 0) (40 * sub) ++ [CB 8 jk]) ->
rw_cells bsegs m (FF + 544) (f32 e32s) -> length e32s = 40%nat -> aobj bsegs m (FF + 544) 160 ->
rw_cells bsegs m (FF + 48) (f32 pgs) -> length pgs = 3%nat -> rw_cells bsegs m (FF + 32) [C4 (Z_to_bv 64 p)] ->
17 <= bp <= 144 -> 17 <= p <= 144 -> 0 <= sub < 4 ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk bsegs m lo (usp + -624) -> lo <= usp - 576 - 48 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv bsegs m -> client_constsB m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) F1 fc1 (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (bp' : Z) (e32' : list word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_mset2) (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (FF + 320)) (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6' a7'
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F1 (Z_to_bv 64 nbe_e_asan_memset) fc1 None m1 (seg_rom bsegs)
/\ frm0 fc1 /\ munch [(FF + 544, FF + 704); (usp + -624, usp + -200)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -576)
/\ rw_cells bsegs m1 (usp + -576) (slot_cells (sset 296 (Z_to_bv 64 bp') s)) /\ (bp' = bp \/ bp' = p)
/\ rw_cells bsegs m1 (FF + 544) (f32 e32') /\ length e32' = 40%nat)
(MS (mkR (Z_to_bv 64 RA_nbe_ltp) (Z_to_bv 64 (usp + -624)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_ltp)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E256 E96 E296 SA E32 LE32 OB32 PG LPG PIT BPR PR SUB F0 F64 FLO FTOP FSH ST0 LO LOS SPH U32 MI CC FRM.
unfold RA_nbe_ltp, RA_nbe_mset2, nbe_e_asan_memset in *. unfold hidp in FSH.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
replace (ret_pc (Z_to_bv 64 0xa2a2c)) with (Z_to_bv 64 0xa2a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(FF + 544, FF + 704); (usp + -624, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(FF + 544, FF + 704); (usp + -624, usp + -200)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
unfold ltp_args_cells in SA. cbn [app] in SA. release_frame SA ST0 (usp + -576).
pose proof ST0 as (STa & STb & _).
bato 0xa2a40.
astep.
call (nbe_san40 e32s (FF + 544) (usp + -576) lo).
all: try eassumption.
all: try (unfold SH_LO, SH_HI, IMG_TOP_B in *; lia).
rename x16 into m1. rename PC into ST1. rename PC0 into FRM1. rename PC1 into E32b. clear FRM.
pose proof SL as SL'. pose proof E256 as E256'. pose proof E96 as E96'. pose proof E296 as E296'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v256 v96 v296] in E256', E96', E296'. subst w256 w96 w296.
unfold slot_cells in SL'. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL'.
destruct pgs as [|g0 [|g1 [|g2 [|]]]]; cbn [length] in LPG; try discriminate LPG. clear LPG.
rewrite !f32_cons, f32_nil in PG.
bato 0xa2a4c. astep. join 0xa2a54 0 1.
bato 0xa2a68. astep. join 0xa2a70 0 1.
bato 0xa2a78. astep. joinb 0xa2aa4.
bato 0xa2ab8.
eapply evt_cut; [eapply (nbe_r1 usp ST FF isv sub lo bp p); try eassumption |].
1: lia.
intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & F' & fc' & m' & bp' & -> & FRM' & MU' & WM' & MI' & ST' & SL2 & HBP).
pose proof (munch_trans _ _ _ _ MU (munch_weaken [(usp + -576, usp + -200)] [(FF + 544, FF + 704); (usp + -624, usp + -200)] m1 m' ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MU')) as MU2.
transport_after_call bsegs m1 m' MU' WM'.
pose proof SL2 as SL3. unfold slot_cells in SL3. cbn in SL3. unfold R_BPX.
bato 0x6689c.
apply evt_done. do 15 eexists. exists bp'. eexists. split; [reflexivity|].
split; [exact FRM'|]. split; [exact MU2|]. split; [eassumption|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact SL2|]. split; [exact HBP|]. split; eassumption.
Qed.

Definition A_scal3 : Z := 0x23b60.
Definition A_scal1 : Z := 0x23bc0.
Definition scal3_bytes : list byte := match image_bytes bsegs A_scal3 32 with Some b => b | None => [] end.
Definition scal1_bytes : list byte := match image_bytes bsegs A_scal1 8 with Some b => b | None => [] end.
Lemma nbe_scal3_at : forall m, mem_inv bsegs m -> exists tab : list word, length tab = 8%nat /\ ro_cells bsegs m A_scal3 (f32 tab).
Proof.
intros m MI.
assert (L : length scal3_bytes = (4 * 8)%nat) by (vm_compute; reflexivity).
pose proof (ro_cells_image bsegs m A_scal3 scal3_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold A_scal3; lia)
ltac:(rewrite L; unfold A_scal3; cbn; lia)) as R.
destruct (bytes_are_f32 8 scal3_bytes L) as (ws & Lws & E).
exists ws. split; [exact Lws|].
destruct R as [_ B]. split; [apply cells_wf_f32|]. rewrite E. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma nbe_scal1_at : forall m, mem_inv bsegs m -> exists tab : list word, length tab = 2%nat /\ ro_cells bsegs m A_scal1 (f32 tab).
Proof.
intros m MI.
assert (L : length scal1_bytes = (4 * 2)%nat) by (vm_compute; reflexivity).
pose proof (ro_cells_image bsegs m A_scal1 scal1_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold A_scal1; lia)
ltac:(rewrite L; unfold A_scal1; cbn; lia)) as R.
destruct (bytes_are_f32 2 scal1_bytes L) as (ws & Lws & E).
exists ws. split; [exact Lws|].
destruct R as [_ B]. split; [apply cells_wf_f32|]. rewrite E. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma nbe_row_hsg : forall r, In r nb_smrecs -> sm_have_subframe_gain (smr_sm r) = 0 \/ sm_have_subframe_gain (smr_sm r) = 1 \/ sm_have_subframe_gain (smr_sm r) = 3.
Proof. intros r H. cbn [nb_smrecs In] in H. repeat (destruct H as [<- | H]; [cbn; tauto|]). destruct H. Qed.

Lemma nbe_rw_f32_nth : forall (m : mem) A ws i, rw_cells bsegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, rw_cells bsegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (rw_cells_f32_mid bsegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.
Lemma nbe_ro_f32_nth : forall (m : mem) A ws i, ro_cells bsegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, ro_cells bsegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (ro_f32_mid bsegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.

Lemma nbe_d1 : forall {ptr : Type} (usp lo ST OUT A D FF SF isv sub mo : Z) (r : smrec) (st : nb_state ptr) (pad : list byte) (b : bits_st ptr)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v328 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v336 s = Z_to_bv 64 (ST + 2240) ->
v312 s = Z_to_bv 64 (ST + 2248) -> v288 s = Z_to_bv 64 A ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_constsB m ->
bits_rep bsegs m A D b -> bits_ok b -> aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) -> (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
aobj bsegs m A_scal3 32 -> aobj bsegs m A_scal1 8 ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 48 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (xra t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' (Z_to_bv 64 (ST + 2248)) a6' a7'
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F' (Z_to_bv 64 0xa2f84) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ munch [(A, A + BITS_SIZEOF); (usp + -624, usp + -576)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ bits_rep bsegs m' A D (hsg_bits (smr_sm r) b))
(MS (mkR (Z_to_bv 64 RA_nbe_mset2) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (FF + 320)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E328 E344 E336 E312 E288 CFG EMO SAT OBS S8 SPOS SLO SOFF LC NTA CC REP OK OBA OBD ASH ALO DLO OB3 OB1 ST0 LO LOS SPH MI FRM.
unfold RA_nbe_mset2, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa2e0c)) with (Z_to_bv 64 0xa2e0c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + BITS_SIZEOF); (usp + -624, usp + -576)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(A, A + BITS_SIZEOF); (usp + -624, usp + -576)]) by (cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v328 v344 v336 v312 v288] in E328, E344, E336, E312, E288. subst w328 w344 w336 w312 w288.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP_B in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
bato 0xa2e38. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
bato 0xa2e40. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa2e7c.
chk_hint NTM.
bato 0xa2e88.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa2e90.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
unfold smrec_cells in ROW. cbv zeta in ROW.
set (SP := smr_ptr r) in *.
bato 0xa2eb4. rewrite ?(Z.mod_small (SP + 8)) by lia.
chk_hint OBR.
bato 0xa2eb8.
bato 0xa2ec0.
pose proof (nbe_row_hsg r INR) as HSG.
unfold A_scal3, A_scal1 in *.
destruct HSG as [HS | [HS | HS]]; unfold hsg_bits; rewrite HS in *; cbn [Z.eqb Pos.eqb].
-
astep. bato 0xa2f84. apply evt_done. do 18 eexists. split; [reflexivity|].
split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0| exact REP].
-
astep. bato 0xa2f38. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: eassumption. 1: unfold client_constsB; exact (conj G1 (conj G2 (conj G3 G4))). 1: eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 1)) with (ub b 1) in *. change (fst (speex_bits_unpack_unsigned b 1)) with (uv b 1) in *.
pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 1) with 2 in V1R.
match goal with MIc : mem_inv bsegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (nbe_scal1_at mc MIc) as (tab1 & LT1 & TAB1) end.
unfold A_scal1 in TAB1.
destruct (nbe_ro_f32_nth _ 146368 tab1 (uv b 1) TAB1 ltac:(lia)) as (wg & WG).
bato 0xa2f6c.
rewrite Z.shiftl_mul_pow2 by lia. replace (146368 + uv b 1 * 2 ^ 2) with (146368 + 4 * uv b 1) by lia.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (aobj_munch bsegs W m mc _ _ OB1 MUc (shfree_of_aobj bsegs W m _ _ OF OB1)) as OB1c end.
bato 0xa2f78. astep. chk_merge OB1 4.
replace (146368 + uv b 1 * 4) with (146368 + 4 * uv b 1) by lia.
bato 0xa2f84. clear WG.
apply evt_done. do 18 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [eassumption| eassumption].
-
astep. bato 0xa2edc. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 3 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: eassumption. 1: unfold client_constsB; exact (conj G1 (conj G2 (conj G3 G4))). 1: eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 3)) with (ub b 3) in *. change (fst (speex_bits_unpack_unsigned b 3)) with (uv b 3) in *.
pose proof (ub_ok b 3 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 3) with 8 in V1R.
match goal with MIc : mem_inv bsegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (nbe_scal3_at mc MIc) as (tab3 & LT3 & TAB3) end.
unfold A_scal3 in TAB3.
destruct (nbe_ro_f32_nth _ 146272 tab3 (uv b 3) TAB3 ltac:(lia)) as (wg & WG).
bato 0xa2f10.
bato 0xa2f18. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite ?(Z.mod_small (146272 + uv b 3 * 4)) by lia.
chk_hint OB3.
bato 0xa2f1c. astep. chk_merge OB3 4.
replace (146272 + uv b 3 * 4) with (146272 + 4 * uv b 3) by lia.
bato 0xa2f84. clear WG.
apply evt_done. do 18 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [eassumption| eassumption].
Qed.

Definition RA_nbe_innov : Z := 0xa3128.

Lemma nbe_d2 : forall {ptr : Type} (usp lo ST OUT A FF SF isv sub mo : Z) (r : smrec) (ki : innov_kind) (st : nb_state ptr) (pad : list byte)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v328 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v336 s = Z_to_bv 64 (ST + 2240) ->
v288 s = Z_to_bv 64 A -> v304 s = Z_to_bv 64 0 -> v216 s = Z_to_bv 64 (ST + 2228) ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
sm_innovation_unquant (smr_sm r) = Some ki ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_constsB m ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (t0' t2' a7' : word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_innov) (Z_to_bv 64 (usp + -576)) gp tp t0' t1 t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (FF + 320)) (Z_to_bv 64 (smr_innov_par r)) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (ST + 2228))
(Z_to_bv 64 (innov_entryA ki)) a7'
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 (innov_entryA ki)) fc None m (seg_rom bsegs))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 (Z_to_bv 64 (ST + 2248)) a6 a7
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa2f84) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E328 E344 E336 E288 E304 E216 CFG EMO SAT INK OBS S8 SPOS SLO SOFF LC NTA CC ST0 LO LOS SPH MI.
unfold RA_nbe_innov, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v328 v344 v336 v288 v304 v216] in E328, E344, E336, E288, E304, E216. subst w328 w344 w336 w288 w304 w216.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP_B in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
unfold smrec_cells in ROW. cbv zeta in ROW. rewrite INK in ROW.
assert (IEP : 0x10000 <= innov_entryA ki < 0x630200 /\ innov_entryA ki mod 2 = 0)
by (destruct ki; (cbv [innov_entryA A_split_cb_shape_sign_unquant A_noise_codebook_unquant]; split; [lia| reflexivity])).
set (SP := smr_ptr r) in *.

bato 0xa2fac. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
bato 0xa2fb4. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa2ff0.
chk_hint NTM.
bato 0xa2ffc.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa3004.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
bato 0xa3020. rewrite ?(Z.mod_small (SP + 64)) by lia.
chk_hint OBR.
bato 0xa3034.
astep. bato 0xa303c. astep. sh_if.

bato 0xa3068. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
bato 0xa3070. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa30ac.
chk_hint NTM.
bato 0xa30b8.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa30c0.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
bato 0xa30dc. rewrite ?(Z.mod_small (SP + 64)) by lia.
chk_hint OBR.
bato 0xa30f4. rewrite ?(Z.mod_small (SP + 72)) by lia.
chk_hint OBR.
bato 0xa3124. astep.
replace (ret_pc (Z_to_bv 64 (innov_entryA ki))) with (Z_to_bv 64 (innov_entryA ki)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 IEP)]).
apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma nbe_smul40 : forall (xs : list word) (p usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
length xs = 40%nat -> aobj bsegs m p 160 -> p mod 4 = 0 -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 160 <= SH_LO \/ SH_HI <= p) -> (p + 160 <= lo \/ usp <= p) ->
rw_cells bsegs m p (f32 xs) -> frm0 fc -> stk bsegs m lo usp -> IMG_TOP_B <= p -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(p, p + 160); (usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc' /\ rw_cells bsegs m' p (f32 xs') /\ length xs' = 40%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 40) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_signal_mul) fc None m (seg_rom bsegs)).
Proof.
intros until fc. intros L OB P4 LO LOS SPH XSH XAP X FRM ST PTOP CC MI.
eapply evt_mono.
- eapply (signal_mul_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m); rewrite ?L; try eassumption; try (cbn; lia); try reflexivity.
- intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & f15 & fc' & m' & E & MU & WM & MI' & ST' & FRM' & X').
rewrite L in MU. do 19 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact FRM'|]. split; [exact X'|]. rewrite length_map. exact L.
Qed.
Lemma nbe_row_dcb : forall r, In r nb_smrecs -> sm_double_codebook (smr_sm r) = 0 \/ sm_double_codebook (smr_sm r) = 1.
Proof. intros r H. cbn [nb_smrecs In] in H. repeat (destruct H as [<- | H]; [cbn; tauto|]). destruct H. Qed.

Definition RA_nbe_smul1 : Z := 0xa313c.
Definition RA_nbe_mset3 : Z := 0xa325c.
Definition NBE_PC_J : Z := 0xa337c.
Definition SC_E2 : nbscope := NBSC true false true true false.

Lemma nbe_e : forall {ptr : Type} (usp lo ST OUT A FF SF isv sub mo : Z) (r : smrec) (st : nb_state ptr) (pad rest : list byte) (is0 : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v328 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v336 s = Z_to_bv 64 (ST + 2240) ->
v312 s = Z_to_bv 64 (ST + 2248) -> v184 s = Z_to_bv 64 (FF + 768) -> v200 s = Z_to_bv 64 SF ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_constsB m ->
rw_cells bsegs m (FF + 320) (f32 is0) -> length is0 = 40%nat -> aobj bsegs m (FF + 320) 160 ->
rw_cells bsegs m SF (nbd_shadow SC_E rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 16 -> SH_HI <= lo -> usp + 16 <= 140737488355328 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (is1 : list word),
frm0 fc' /\ munch [(FF + 320, FF + 480); (SF + 96, SF + 116); (usp + -592, usp + -576)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (FF + 320) (f32 is1) /\ length is1 = 40%nat
/\ ((sm_double_codebook (smr_sm r) = 0
/\ ms = MS (mkR (Z_to_bv 64 RA_nbe_smul1) (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr (1016736 + mo * 8) 3 + SHB)) (Z_to_bv 64 (1016736 + mo * 8)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBE_PC_J) fc' None m' (seg_rom bsegs)
/\ rw_cells bsegs m' SF (nbd_shadow SC_E rest))
\/ (sm_double_codebook (smr_sm r) = 1
/\ ms = MS (mkR (Z_to_bv 64 RA_nbe_mset3) (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (FF + 768)) (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6' a7'
(Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr (1016736 + mo * 8) 3 + SHB)) (Z_to_bv 64 (1016736 + mo * 8)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F' (Z_to_bv 64 nbe_e_asan_memset) fc' None m' (seg_rom bsegs)
/\ rw_cells bsegs m' SF (nbd_shadow SC_E2 rest))))
(MS (mkR (Z_to_bv 64 RA_nbe_innov) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_innov)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E328 E344 E336 E312 E184 E200 CFG EMO SAT OBS S8 SPOS SLO SOFF SFA LC NTA CC IS LIS OBI SH ESF SF0 SF1 F0 F64 FLO FTOP FSH ST0 LO LOS UST MI FRM.
assert (SPH : usp < 2^63) by lia.
unfold RA_nbe_innov, RA_nbe_smul1, RA_nbe_mset3, NBE_PC_J, nbe_e_asan_memset, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp in SOFF, FSH. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
replace (ret_pc (Z_to_bv 64 0xa3128)) with (Z_to_bv 64 0xa3128) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(FF + 320, FF + 480); (SF + 96, SF + 116); (usp + -592, usp + -576)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (SHF : forall o n, 0 <= o -> o + n <= 140737488355328 -> (o + n <= FF \/ FF + 2048 <= o) ->
shfree [(FF + 320, FF + 480); (SF + 96, SF + 116); (usp + -592, usp + -576)] o n).
{ intros o n O0 O1 OFA. pose proof (FSH : _ \/ _) as FSH'. unfold SH_LO, SH_HI in FSH'.
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply (shfree_cons_sh _ _ _ _ _ FF 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite ESF, shad_shiftr; lia | rewrite ESF, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact OFA |].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply shfree_nil. }
pose proof ST0 as (STa & STb & _).
astep. astep. astep. astep. astep.
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
pose proof (SFA : _ \/ _) as SFAu. pose proof (FSH : _ \/ _) as FSHu. pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in FSHu, SF0u, SF1u.
call (nbe_smul40 is0 (FF + 320) (usp + -576) lo).
all: try eassumption.
all: try (unfold SH_LO, SH_HI, IMG_TOP_B in *; lia).
rename x16 into m1. rename x14 into F1. rename x15 into fc1.
lazymatch goal with H : rw_cells bsegs m1 (FF + 320) (f32 ?l) |- _ => rename l into is1; rename H into IS1 end.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v328 v344 v336 v312 v184 v200] in E328, E344, E336, E312, E184, E200. subst w328 w344 w336 w312 w184 w200.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP_B in SP1.
assert (LC1 : lib_consts m1) by (apply (lib_consts_munch _ m m1 LC ltac:(eassumption)); repeat (apply Forall_cons; [cbn [fst snd]; unfold SH_LO, SH_HI in *; lia|]); apply Forall_nil).
pose proof (SMC m1 LC1) as ROW.
destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
pose proof SFAu as SFA'. pose proof (FSH : _ \/ _) as FSH'. unfold SH_LO, SH_HI in FSH'.
lazymatch goal with MUc : munch ?W m m1 |- _ =>
pose proof (aobj_munch bsegs W m m1 _ _ OBS MUc (SHF ST 2968 ltac:(lia) ltac:(lia) SFA')) as OBS1;
pose proof (aobj_munch bsegs W m m1 _ _ NTM MUc (SHF 1016704 208 ltac:(lia) ltac:(lia) ltac:(lia))) as NTM1;
pose proof (aobj_munch bsegs W m m1 _ _ OBR MUc (SHF (smr_ptr r) 88 ltac:(lia) ltac:(lia) ltac:(lia))) as OBR1 end.
clear OBS NTM OBR. rename OBS1 into OBS. rename NTM1 into NTM. rename OBR1 into OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
unfold smrec_cells in ROW. cbv zeta in ROW.
set (SP := smr_ptr r) in *.
bato 0xa316c. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
bato 0xa3174. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa31b0.
chk_hint NTM.
bato 0xa31bc.
rewrite (shb_zero bsegs m1 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa31c4.
pose proof (sub_ptr_read m1 mo LC1 ltac:(lia)) as RD.
rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
bato 0xa31e8. rewrite ?(Z.mod_small (SP + 12)) by lia.
chk_hint OBR.
bato 0xa31f4.
pose proof (nbe_row_dcb r INR) as HDCB.
destruct HDCB as [HD | HD]; rewrite HD.
-
astep. sh_if.
apply evt_done. do 17 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. left. split; [reflexivity|]. split; [reflexivity|].
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq]. exact SH.
-
astep. sh_if.
bato 0x6689c.
apply evt_done. do 17 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. right. split; [reflexivity|]. split; [reflexivity|].
unfold nbd_shadow, nbd_shadow_bytes, SC_E2, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq]. exact SH.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition RA_nbe_innov2 : Z := 0xa32dc.

Lemma nbe_f : forall {ptr : Type} (usp lo ST OUT A FF SF isv sub mo : Z) (r : smrec) (ki : innov_kind)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v304 s = Z_to_bv 64 0 -> v288 s = Z_to_bv 64 A -> v184 s = Z_to_bv 64 (FF + 768) -> v216 s = Z_to_bv 64 (ST + 2228) ->
smrec_at mo = Some r -> sm_innovation_unquant (smr_sm r) = Some ki ->
lib_consts m -> nb_tabs_acc m ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (t0' t2' a7' : word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_innov2) (Z_to_bv 64 (usp + -576)) gp tp t0' t1 t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (FF + 768)) (Z_to_bv 64 (smr_innov_par r)) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (ST + 2228))
(Z_to_bv 64 (innov_entryA ki)) a7'
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 768)) (Z_to_bv 64 (1016736 + mo * 8)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 (innov_entryA ki)) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_nbe_mset3) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr (1016736 + mo * 8) 3 + SHB)) (Z_to_bv 64 (1016736 + mo * 8)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset3)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E304 E288 E184 E216 SAT INK LC NTA ST0 LO LOS SPH MI.
unfold RA_nbe_mset3, RA_nbe_innov2 in *. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa325c)) with (Z_to_bv 64 0xa325c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v304 v288 v184 v216] in E304, E288, E184, E216. subst w304 w288 w184 w216.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP_B in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold smrec_cells in ROW. cbv zeta in ROW. rewrite INK in ROW.
assert (IEP : 0x10000 <= innov_entryA ki < 0x630200 /\ innov_entryA ki mod 2 = 0)
by (destruct ki; (cbv [innov_entryA A_split_cb_shape_sign_unquant A_noise_codebook_unquant]; split; [lia| reflexivity])).
set (SP := smr_ptr r) in *.
unfold A_nb_mode in NTM.
bato 0xa3264.
chk_hint NTM.
bato 0xa3268.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa3270.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
bato 0xa328c. rewrite ?(Z.mod_small (SP + 64)) by lia.
chk_hint OBR.
bato 0xa32a4. rewrite ?(Z.mod_small (SP + 72)) by lia.
chk_hint OBR.
bato 0xa32d8. astep.
replace (ret_pc (Z_to_bv 64 (innov_entryA ki))) with (Z_to_bv 64 (innov_entryA ki)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 IEP)]).
apply evt_done. do 3 eexists. reflexivity.
Qed.

Definition RA_nbe_smul2 : Z := 0xa32f8.

Lemma nbe_g : forall (usp lo ST FF SF isv sub mo : Z) (rest : list byte) (is0 i2 : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v80 s = Z_to_bv 64 (FF + 480) -> v200 s = Z_to_bv 64 SF -> v312 s = Z_to_bv 64 (ST + 2248) ->
rw_cells bsegs m (FF + 320) (f32 is0) -> length is0 = 40%nat ->
rw_cells bsegs m (FF + 768) (f32 i2) -> length i2 = 40%nat -> aobj bsegs m (FF + 768) 160 ->
rw_cells bsegs m SF (nbd_shadow SC_E2 rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
client_constsB m -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 16 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (xra t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (is1 i2' : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (1016736 + mo * 8)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBE_PC_J) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ munch [(FF + 320, FF + 480); (FF + 768, FF + 928); (SF + 96, SF + 116); (usp + -592, usp + -576)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (FF + 320) (f32 is1) /\ length is1 = 40%nat /\ rw_cells bsegs m' (FF + 768) (f32 i2') /\ length i2' = 40%nat
/\ rw_cells bsegs m' SF (nbd_shadow SC_E rest))
(MS (mkR (Z_to_bv 64 RA_nbe_innov2) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) (Z_to_bv 64 (FF + 768)) (Z_to_bv 64 (1016736 + mo * 8)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB)
(Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_innov2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E80 E200 E312 IS LIS I2C LI2 OBI2 SH ESF SF0 SF1 F0 F64 FLO FTOP FSH CC ST0 LO LOS SPH MI FRM.
unfold RA_nbe_innov2, RA_nbe_smul2, NBE_PC_J in *. unfold hidp in FSH. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
replace (ret_pc (Z_to_bv 64 0xa32dc)) with (Z_to_bv 64 0xa32dc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(FF + 320, FF + 480); (FF + 768, FF + 928); (SF + 96, SF + 116); (usp + -592, usp + -576)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v80 v200 v312] in E80, E200, E312. subst w80 w200 w312.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
unfold nbd_shadow, nbd_shadow_bytes, SC_E2, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in SF0u, SF1u.
bato 0xa32f4. astep.
call (nbe_smul40 i2 (FF + 768) (usp + -576) lo).
all: try eassumption.
all: try (unfold SH_LO, SH_HI, IMG_TOP_B in *; lia).
rename PC1 into I2C'. rename POST into LI2'.
lazymatch type of LI2' with length ?l = _ => do 40 (destruct l as [|? l]; [discriminate LI2'|]); destruct l; [| discriminate LI2'] end. cbn [f32 map] in I2C'.
do 40 (destruct is0 as [|? is0]; [discriminate LIS|]). destruct is0; [| discriminate LIS]. cbn [f32 map] in IS.
do 40 (bato 0xa3318; astep; sh_if).
bato 0xa337c.
apply evt_done. do 17 eexists.
lazymatch goal with H : rw_cells bsegs m1 (FF + 320) ?cs |- _ => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
lazymatch goal with H : rw_cells bsegs m1 (FF + 768) ?cs |- _ => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [reflexivity|]. split; [eassumption|]. split; [reflexivity|].
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq]. exact SH.
Qed.

Lemma nbe_f32_win : forall (m : mem) A (ws : list word) (i k : nat), rw_cells bsegs m A (f32 ws) -> (i + k <= length ws)%nat ->
rw_cells bsegs m A (f32 (firstn i ws)) /\ rw_cells bsegs m (A + 4 * Z.of_nat i) (f32 (firstn k (skipn i ws)))
/\ rw_cells bsegs m (A + 4 * Z.of_nat i + 4 * Z.of_nat k) (f32 (skipn (i + k) ws)).
Proof.
intros m A ws i k H Hk.
destruct (rw_cells_f32_split bsegs m A ws i H) as [H1 H2]. rewrite length_firstn in H2. replace (Nat.min i (length ws)) with i in H2 by lia.
destruct (rw_cells_f32_split bsegs m _ (skipn i ws) k H2) as [H3 H4]. rewrite length_firstn, length_skipn in H4. replace (Nat.min k (length ws - i)) with k in H4 by lia.
rewrite skipn_skipn in H4. replace (k + i)%nat with (i + k)%nat in H4 by lia.
split; [exact H1|]. split; [replace (A + 4 * Z.of_nat i) with (A + Z.of_nat (4 * i)) by lia; exact H3|].
replace (A + 4 * Z.of_nat i + 4 * Z.of_nat k) with (A + Z.of_nat (4 * i) + Z.of_nat (4 * k)) by lia. exact H4.
Qed.
Lemma nbe_f32_join_win : forall (m : mem) A (l1 l2 l3 : list word), rw_cells bsegs m A (f32 l1) -> rw_cells bsegs m (A + 4 * Z.of_nat (length l1)) (f32 l2) ->
rw_cells bsegs m (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) (f32 l3) -> rw_cells bsegs m A (f32 (l1 ++ l2 ++ l3)).
Proof.
intros m A l1 l2 l3 H1 H2 H3. rewrite !f32_app. apply rw_cells_join; [exact H1|]. rewrite cells_size_f32.
replace (A + Z.of_nat (4 * length l1)) with (A + 4 * Z.of_nat (length l1)) by lia.
apply rw_cells_join; [exact H2|]. rewrite cells_size_f32. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 * length l2)) with (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) by lia. exact H3.
Qed.

Ltac f32_of_cells H :=
lazymatch type of H with rw_cells _ _ _ ?cs => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.

Section EXC.
Variables (EXW FF lo : Z) (e32 inn : list word) (xra sp gp tp t0 t1 t2 s0 s1 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) (m : mem).
Hypothesis LE32 : length e32 = 40%nat.
Hypothesis LINN : length inn = 40%nat.
Hypothesis OBX : aobj bsegs m EXW 160.
Hypothesis X8 : EXW mod 8 = 0.
Hypothesis XPOS : 0 < EXW.
Hypothesis XSH : EXW + 160 <= SH_LO \/ SH_HI <= EXW.
Hypothesis XTOP : IMG_TOP_B <= EXW.
Hypothesis F0 : 0 < FF.
Hypothesis FLO : FF + 2048 <= lo.
Hypothesis FTOP : IMG_TOP_B <= FF.
Hypothesis XFA : EXW + 160 <= FF \/ FF + 2048 <= EXW.
Hypothesis XLO : EXW + 160 <= lo.
Hypothesis LOS : SH_HI <= lo.
Local Notation POST := (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (a0' a1' a2' a3' a4' a5' a6' a7' : word) (xw' : list word),
ms = MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 1) s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 (Z_to_bv 64 EXW) s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa3418) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ munch [(EXW, EXW + 160)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' EXW (f32 xw') /\ length xw' = 40%nat).

Lemma nbe_exc_loop : forall (rest dn : list word) (x : word) (kz off : Z) (a6 a7 : word) (Fz : bvmap 5 word) fc m1,
(length dn + S (length rest) = 40)%nat -> kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch [(EXW, EXW + 160)] m m1 -> offsh [(EXW, EXW + 160)] -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 EXW (f32 dn) -> rw_cells bsegs m1 (EXW + off) (f32 (x :: rest)) ->
rw_cells bsegs m1 (FF + 544) (f32 e32) -> rw_cells bsegs m1 (FF + 320) (f32 inn) ->
evt bsegs POST
(MS (mkR xra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (EXW + off)) (Z_to_bv 64 (EXW + off)) (Z_to_bv 64 1) (Z_to_bv 64 kz) (Z_to_bv 64 (FF + 320 + off))
(Z_to_bv 64 (FF + 544 + off)) a6 a7 (Z_to_bv 64 1) s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 (Z_to_bv 64 EXW) s10 s11 t3 t4 t5 t6)
Fz (Z_to_bv 64 0xa33ac) fc None m1 (seg_rom bsegs)).
Proof using LE32 LINN OBX X8 XPOS XSH XTOP F0 FLO FTOP XFA XLO LOS.
induction rest as [|x' rest IH]; intros dn x kz off a6 a7 Fz fc m1 Hn Hkz Hoff FRM MU OF WM MI DONE X E32 INN;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *; pose proof LOS as LOS'; unfold SH_HI in LOS'; pose proof XSH as XSH'; unfold SH_LO, SH_HI in XSH';
pose proof XTOP as XTOP'; unfold IMG_TOP_B in XTOP'; pose proof FTOP as FTOP'; unfold IMG_TOP_B in FTOP';
subst kz;
assert (NZ : (EXW + off <? 1) = false) by (apply Z.ltb_ge; lia);
destruct (nbe_rw_f32_nth m1 (FF + 544) e32 (Z.of_nat (length dn)) E32 ltac:(lia)) as (we & WE);
destruct (nbe_rw_f32_nth m1 (FF + 320) inn (Z.of_nat (length dn)) INN ltac:(lia)) as (wi & WI);
replace (FF + 544 + 4 * Z.of_nat (length dn)) with (FF + 544 + off) in WE by lia;
replace (FF + 320 + 4 * Z.of_nat (length dn)) with (FF + 320 + off) in WI by lia;
rewrite f32_cons in X.
-
bato 0xa33b4. astep. rewrite NZ. cbn [Z.b2z].
bato 0xa33e0. clear WE WI. astep. chk_merge OBX 4.
bato 0xa3400. astep. cbn [length]. sh_if.
bato 0xa3418.
rewrite f32_nil in X.
chunk_snoc DONE X.
lazymatch type of DONE with rw_cells _ _ _ (f32 dn ++ [C4 ?w]) => change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE;
apply evt_done; do 12 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [exact DONE| rewrite length_app; cbn [length] in *; lia] end.
-
bato 0xa33b4. astep. rewrite NZ. cbn [Z.b2z].
bato 0xa33e0. clear WE WI. astep. chk_merge OBX 4.
bato 0xa3400. astep. cbn [length]. sh_if.
chunk_uncons X as X1.
chunk_snoc DONE X1.
lazymatch type of DONE with rw_cells _ _ _ (f32 dn ++ [C4 ?w]) => change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE;
replace (EXW + off + 4) with (EXW + (off + 4)) in * by lia;
replace (FF + 320 + off + 4) with (FF + 320 + (off + 4)) by lia; replace (FF + 544 + off + 4) with (FF + 544 + (off + 4)) by lia;
eapply (IH (dn ++ [w]) x' _ (off + 4)); try eassumption; try (rewrite ?length_app; cbn [length] in *; lia) end.
Qed.
End EXC.

Lemma nbe_h1 : forall (usp lo ST FF SF isv sub EXW : Z) (xw e32 inn : list word)
(gp tp xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v264 s = Z_to_bv 64 (40 * sub) -> v248 s = Z_to_bv 64 (ST + 1368) -> v232 s = Z_to_bv 64 (FF + 544) ->
EXW = ST + 1368 + 160 * sub -> 0 <= sub < 4 ->
rw_cells bsegs m EXW (f32 xw) -> length xw = 40%nat -> aobj bsegs m EXW 160 -> ST mod 8 = 0 -> 0 < ST -> (EXW + 160 <= SH_LO \/ SH_HI <= EXW) -> IMG_TOP_B <= EXW ->
rw_cells bsegs m (FF + 544) (f32 e32) -> length e32 = 40%nat -> rw_cells bsegs m (FF + 320) (f32 inn) -> length inn = 40%nat ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) -> (EXW + 160 <= FF \/ FF + 2048 <= EXW) ->
EXW + 160 <= lo -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> usp < 2^63 -> SH_HI <= lo ->
client_constsB m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (a0' a1' a2' a3' a4' a5' a6' a7' : word) (xw' : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 1) s3 (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F' (Z_to_bv 64 0xa3418) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ munch [(EXW, EXW + 160)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' EXW (f32 xw') /\ length xw' = 40%nat)
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_J) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E264 E248 E232 EEX SUB XW LXW OBX S8 SPOS XSH XTOP E32 LE32 INN LINN F0 F64 FLO FTOP FSH XFA XLO ST0 LO SPH LOS CC MI FRM.
unfold NBE_PC_J. pose proof LOS as LOS'. unfold SH_HI in LOS'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v264 v248 v232] in E264, E248, E232. subst w264 w248 w232.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
assert (A4 : (ST + 1368) mod 4 = 0) by (clear - S8; Z.div_mod_to_equations; lia).
bato 0xa33ac.
rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (land3_al (ST + 1368) A4). cbn [Z.b2z Z.ltb Z.compare]. change (Z.land 1 1) with 1.
replace (40 * sub * 4) with (160 * sub) by lia. rewrite <- EEX.
pose proof (munch_refl [(EXW, EXW + 160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(EXW, EXW + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct xw as [|x rest] eqn:Exw; [cbn [length] in LXW; lia|].
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (EXW + 0)) (Z_to_bv 64 (EXW + 0)) (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (S (length rest)))) (Z_to_bv 64 (FF + 320 + 0)) (Z_to_bv 64 (FF + 544 + 0)) a6 a7
(Z_to_bv 64 1) s3 (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
by (rewrite !Z.add_0_r; cbn [length] in LXW; replace (Z.of_nat (S (length rest))) with 40 by lia; reflexivity)
end.
replace EXW with (EXW + 0) in XW at 1 by lia.
eapply evt_cut; [eapply (nbe_exc_loop EXW FF lo e32 inn xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
s3 (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936))
t3 t4 t5 t6 m) with (rest := rest) (dn := []) (x := x); try eassumption; try reflexivity |].
all: try (unfold SH_LO, SH_HI, IMG_TOP_B in *; cbn [length] in *; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
intros ms' (m' & F' & fc' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & xw' & -> & FRM' & MU' & WM' & MI' & XW' & LXW').
apply evt_done. do 12 eexists. split; [reflexivity|].
split; [exact FRM'|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact XW'| exact LXW'].
Qed.

Section ISV.
Variables (ISW FF lo : Z) (inn : list word) (xra sp gp tp t1 t2 s0 s1 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem).
Hypothesis LINN : length inn = 40%nat.
Hypothesis OBY : aobj bsegs m ISW 160.
Hypothesis Y4 : ISW mod 4 = 0.
Hypothesis YPOS : 0 < ISW.
Hypothesis YSH : ISW + 160 <= SH_LO \/ SH_HI <= ISW.
Hypothesis YTOP : IMG_TOP_B <= ISW.
Hypothesis F0 : 0 < FF.
Hypothesis FLO : FF + 2048 <= lo.
Hypothesis FTOP : IMG_TOP_B <= FF.
Hypothesis YFA : ISW + 160 <= FF \/ FF + 2048 <= ISW.
Hypothesis YLO : ISW + 160 <= lo.
Hypothesis LOS : SH_HI <= lo.
Local Notation POST := (fun ms => exists (m' : mem) (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word) (yw' : list word),
ms = MS (mkR xra sp gp tp (Z_to_bv 64 160) t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 ISW)
s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa3474) fc None m' (seg_rom bsegs)
/\ munch [(ISW, ISW + 160)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' ISW (f32 yw') /\ length yw' = 40%nat).

Lemma nbe_isv_loop : forall (rest dn : list word) (x : word) (off : Z) (a0 a4 a5 : word) (Fz : bvmap 5 word) m1,
(length dn + S (length rest) = 40)%nat -> off = 4 * Z.of_nat (length dn) ->
munch [(ISW, ISW + 160)] m m1 -> offsh [(ISW, ISW + 160)] -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 ISW (f32 dn) -> rw_cells bsegs m1 (ISW + off) (f32 (x :: rest)) -> rw_cells bsegs m1 (FF + 320) (f32 inn) ->
evt bsegs POST
(MS (mkR xra sp gp tp (Z_to_bv 64 160) t1 t2 s0 s1 a0 (Z_to_bv 64 off) (Z_to_bv 64 (18446744073709551615 - ISW)) (Z_to_bv 64 0) a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 ISW) s8 s9 s10 s11 t3 t4 t5 t6)
Fz (Z_to_bv 64 0xa3428) fc None m1 (seg_rom bsegs)).
Proof using LINN OBY Y4 YPOS YSH YTOP F0 FLO FTOP YFA YLO LOS.
induction rest as [|x' rest IH]; intros dn x off a0 a4 a5 Fz m1 Hn Hoff MU OF WM MI DONE X INN;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *; pose proof LOS as LOS'; unfold SH_HI in LOS'; pose proof YSH as YSH'; unfold SH_LO, SH_HI in YSH';
pose proof YTOP as YTOP'; unfold IMG_TOP_B in YTOP'; pose proof FTOP as FTOP'; unfold IMG_TOP_B in FTOP';
destruct (nbe_rw_f32_nth m1 (FF + 320) inn (Z.of_nat (length dn)) INN ltac:(lia)) as (wi & WI);
replace (FF + 320 + 4 * Z.of_nat (length dn)) with (FF + 320 + off) in WI by lia;
rewrite f32_cons in X.
-
bato 0xa3450. clear WI. astep. chk_merge OBY 4.
bato 0xa345c. astep. cbn [length] in *. sh_if.
bato 0xa3474.
rewrite f32_nil in X.
chunk_snoc DONE X.
lazymatch type of DONE with rw_cells _ _ _ (f32 dn ++ [C4 ?w]) => change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE;
apply evt_done; do 9 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [exact DONE| rewrite length_app; cbn [length] in *; lia] end.
-
bato 0xa3450. clear WI. astep. chk_merge OBY 4.
bato 0xa345c. astep. cbn [length] in *. sh_if.
chunk_uncons X as X1.
chunk_snoc DONE X1.
lazymatch type of DONE with rw_cells _ _ _ (f32 dn ++ [C4 ?w]) => change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE;
replace (ISW + off + 4) with (ISW + (off + 4)) in * by lia;
eapply (IH (dn ++ [w]) x' (off + 4)); try eassumption; try (rewrite ?length_app; cbn [length] in *; lia) end.
Qed.
End ISV.

Definition NBE_PC_H3 : Z := 0xa3474.

Lemma nbe_h2 : forall (usp lo ST FF SF isv sub EXW : Z) (yw inn : list word)
(gp tp xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) F fc (m : mem),
(isv = 0 \/ 0 < isv /\ isv + 160 * sub < 2^63) -> 0 <= sub < 4 ->
(isv <> 0 -> rw_cells bsegs m (isv + 160 * sub) (f32 yw) /\ length yw = 40%nat /\ aobj bsegs m (isv + 160 * sub) 160 /\ (isv + 160 * sub) mod 4 = 0
/\ (isv + 160 * sub + 160 <= SH_LO \/ SH_HI <= isv + 160 * sub) /\ IMG_TOP_B <= isv + 160 * sub
/\ (isv + 160 * sub + 160 <= FF \/ FF + 2048 <= isv + 160 * sub) /\ isv + 160 * sub + 160 <= lo) ->
rw_cells bsegs m (FF + 320) (f32 inn) -> length inn = 40%nat ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
lo <= usp - 576 -> usp < 2^63 -> SH_HI <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5' a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F' (Z_to_bv 64 NBE_PC_H3) fc None m' (seg_rom bsegs)
/\ munch [(isv + 160 * sub, isv + 160 * sub + 160)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ (isv <> 0 -> exists yw', rw_cells bsegs m' (isv + 160 * sub) (f32 yw') /\ length yw' = 40%nat))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa3418) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros HIS SUB HYW INN LINN F0 F64 FLO FTOP FSH LO SPH LOS MI.
unfold NBE_PC_H3, isv_cur in *. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof (munch_refl [(isv + 160 * sub, isv + 160 * sub + 160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep.
destruct HIS as [HI0 | (HI1 & HI2)].
- subst isv. cbn [Z.eqb] in *. sh_if.
apply evt_done. do 8 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
intros HN. exfalso. exact (HN eq_refl).
- replace (isv =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). sh_if.
destruct (HYW ltac:(lia)) as (YW & LYW & OBY & Y4 & YSH & YTOP & YFA & YLO).
assert (OF : offsh [(isv + 160 * sub, isv + 160 * sub + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
bato 0xa3428.
rewrite (zb_lxor_ones (isv + 160 * sub)) by lia. rewrite (land3_al (isv + 160 * sub) Y4).
destruct yw as [|y rest] eqn:Eyw; [cbn [length] in LYW; lia|].
replace (isv + 160 * sub) with (isv + 160 * sub + 0) in YW at 1 by lia.
eapply evt_cut; [eapply (nbe_isv_loop (isv + 160 * sub) FF lo inn xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
a6 a7 (Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6 fc m)
with (rest := rest) (dn := []) (x := y) (off := 0); try eassumption; try reflexivity |].
all: try (unfold SH_LO, SH_HI, IMG_TOP_B in *; cbn [length] in *; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
intros ms' (m' & F' & a0' & a1' & a2' & a3' & a4' & a5' & yw' & -> & MU' & WM' & MI' & YW' & LYW').
apply evt_done. do 8 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
intros _. exists yw'. split; [exact YW'| exact LYW'].
Qed.

Definition RA_nbe_mset4 : Z := 0xa349c.
Definition NBE_PC_EXIT : Z := 0xa37fc.

Lemma nbe_h3 : forall {ptr : Type} (usp lo ST FF SF isv sub EXW mo : Z) (st : nb_state ptr) (pad : list byte)
(gp tp xra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v344 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v224 s = Z_to_bv 64 sub -> v264 s = Z_to_bv 64 (40 * sub) ->
v168 s = Z_to_bv 64 (ST + 2032) -> v176 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB) ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> 0 <= mo <= 8 -> 0 <= sub < 4 ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> usp < 2^63 -> SH_HI <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m' : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch [(usp + -576, usp + -200)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ ((mo <> 1 /\ rw_cells bsegs m' (usp + -576) (slot_cells (sset 264 (Z_to_bv 64 (40 * (sub + 1))) s))
/\ ((sub < 3 /\ ms = MS (R_EL usp ST FF (sub + 1) gp tp xra' t0' t1' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 EXW)
t3' t4' t5' t6')
F (Z_to_bv 64 PC_NBD_E) fc None m' (seg_rom bsegs))
\/ (sub = 3 /\ ms = MS (mkR xra' (Z_to_bv 64 (usp + -576)) gp tp t0' (Z_to_bv 64 (ST + 2248)) t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5'
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F (Z_to_bv 64 NBE_PC_EXIT) fc None m' (seg_rom bsegs))))
\/ (mo = 1 /\ rw_cells bsegs m' (usp + -576) (slot_cells s)
/\ ms = MS (mkR (Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 EXW) (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6' a7'
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F (Z_to_bv 64 nbe_e_asan_memset) fc None m' (seg_rom bsegs))))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 160) (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_H3) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E344 E224 E264 E168 E176 CFG EMO MO SUB OBS S8 SPOS SLO SOFF ST0 LO SPH LOS MI.
unfold RA_nbe_mset4, NBE_PC_EXIT, NBE_PC_H3, nbe_e_asan_memset, PC_NBD_E, R_EL, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v344 v224 v264 v168 v176] in E344, E224, E264, E168, E176. subst w344 w224 w264 w168 w176.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
subst mo.
bato 0xa3484. rewrite sx32_small by (unfold int31; lia).
bato 0xa3488. astep.
destruct (Z.eq_dec (nb_submodeID st) 1) as [M1 | M1].
- rewrite M1 in *. sh_if.
bato 0x6689c.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. right.
split; [reflexivity|]. split; [exact SL| reflexivity].
- sh_if.
bato 0xa3724. rewrite ?Z.add_0_r.
rewrite (swrap32_small (sub + 1)) by lia.
replace (40 * sub + 40) with (40 * (sub + 1)) in * by lia.
rewrite (swrap32_small (40 * (sub + 1))) in SL by lia.
astep.
destruct (Z.eq_dec sub 3) as [S3 | S3].
+ subst sub. sh_if.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. left.
split; [exact M1|]. split; [exact SL|]. right. split; [reflexivity| reflexivity].
+ sh_if. astep.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. left.
split; [exact M1|]. split; [exact SL|]. left. split; [lia| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbe_f32_split3 : forall (m : mem) A (ws : list word) i, rw_cells bsegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) ->
rw_cells bsegs m A (f32 (firstn (Z.to_nat i) ws)) /\ rw_cells bsegs m (A + 4 * i) [C4 (nth (Z.to_nat i) ws (Z_to_bv 64 0))]
/\ rw_cells bsegs m (A + 4 * i + 4) (f32 (skipn (S (Z.to_nat i)) ws)).
Proof.
intros m A ws i H Hi.
rewrite <- (firstn_skipn (Z.to_nat i) ws) in H. rewrite f32_app in H. apply rw_cells_app in H as [H1 H2].
rewrite cells_size_f32, length_firstn in H2. replace (Z.of_nat (4 * Nat.min (Z.to_nat i) (length ws))) with (4 * i) in H2 by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- rewrite f32_cons in H2. apply rw_cells_uncons in H2 as [H3 H4]. cbn [csize] in H4.
assert (EN : nth (Z.to_nat i) ws (Z_to_bv 64 0) = w).
{ rewrite <- (firstn_skipn (Z.to_nat i) ws), E. rewrite app_nth2; rewrite length_firstn; [|lia]. replace (Z.to_nat i - Nat.min (Z.to_nat i) (length ws))%nat with 0%nat by lia. reflexivity. }
assert (ES : skipn (S (Z.to_nat i)) ws = r).
{ rewrite <- (skipn_skipn 1 (Z.to_nat i)), E. reflexivity. }
rewrite EN, ES. refine (conj H1 (conj H3 _)). replace (A + 4 * i + 4) with (A + 4 * i + Z.of_nat 4) by lia. exact H4.
Qed.
Lemma nbe_f32_join3 : forall (m : mem) A (l1 l2 : list word) (x : word),
rw_cells bsegs m A (f32 l1) -> rw_cells bsegs m (A + 4 * Z.of_nat (length l1)) [C4 x] -> rw_cells bsegs m (A + 4 * Z.of_nat (length l1) + 4) (f32 l2) ->
rw_cells bsegs m A (f32 (l1 ++ x :: l2)).
Proof.
intros m A l1 l2 x H1 H2 H3. rewrite f32_app, f32_cons. apply rw_cells_join; [exact H1|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length l1)) with (4 * Z.of_nat (length l1)) by lia.
change (C4 x :: f32 l2) with ([C4 x] ++ f32 l2). apply rw_cells_join; [exact H2|]. cbn [cells_size csize]. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 + 0)) with (A + 4 * Z.of_nat (length l1) + 4) by lia. exact H3.
Qed.

Lemma nbe_win_len : forall (ws : list word) i (x : word), 0 <= i < Z.of_nat (length ws) ->
length (firstn (Z.to_nat i) ws ++ x :: skipn (S (Z.to_nat i)) ws) = length ws.
Proof. intros ws i x Hi. rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. lia. Qed.

Definition NBE_PC_VOC : Z := 0xa3578.

Lemma nbe_i1 : forall {ptr : Type} (usp lo ST FF SF olp isv sub EXW : Z) (st : nb_state ptr) (pad : list byte) (xw : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v72 s = Z_to_bv 64 (ST + 2948) -> v208 s = Z_to_bv 64 olp -> v320 s = Z_to_bv 64 (olp + 1073741824) -> v312 s = Z_to_bv 64 (ST + 2248) ->
v248 s = Z_to_bv 64 (ST + 1368) ->
EXW = ST + 1368 + 160 * sub -> 0 <= sub < 4 ->
rw_cells bsegs m (ST + 2948) (nb_tail_cells st pad) -> 0 <= nb_voc_offset st <= 143 -> 17 <= olp <= 144 ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
rw_cells bsegs m EXW (f32 xw) -> length xw = 40%nat -> aobj bsegs m EXW 160 ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> usp < 2^63 -> SH_HI <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m' : mem) (t0' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (vfin : Z) (xw' : list word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -576)) gp tp t0' (Z_to_bv 64 (ST + 2248)) (Z_to_bv 64 160) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
a0' (Z_to_bv 64 (18446744073709551615 - EXW)) (Z_to_bv 64 0) a3' a4' a5' a6' a7'
(Z_to_bv 64 1) s3 (Z_to_bv 64 EXW) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F (Z_to_bv 64 NBE_PC_VOC) fc None m' (seg_rom bsegs)
/\ munch [(EXW, EXW + 160); (ST + 2948, ST + 2952)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ voc_loop VOC_FUEL (nb_voc_offset st) olp = Some vfin
/\ rw_cells bsegs m' (ST + 2948) (nb_tail_cells (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE)) pad)
/\ rw_cells bsegs m' EXW (f32 xw') /\ length xw' = 40%nat)
(MS (mkR (Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 1) s3 (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) (Z_to_bv 64 (isv_cur isv sub)) (Z_to_bv 64 (ST + 2944))
(Z_to_bv 64 EXW) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset4)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E72 E208 E320 E312 E248 EEX SUB TL VR OLP OBS S8 SPOS SLO SOFF XW LXW OBX ST0 LO SPH LOS MI.
subst EXW.
unfold RA_nbe_mset4, NBE_PC_VOC, NBSTATE_SIZEOF, nb_tail_cells in *. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa349c)) with (Z_to_bv 64 0xa349c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(ST + 1368 + 160 * sub, ST + 1368 + 160 * sub + 160); (ST + 2948, ST + 2952)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(ST + 1368 + 160 * sub, ST + 1368 + 160 * sub + 160); (ST + 2948, ST + 2952)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v72 v208 v320 v312 v248] in E72, E208, E320, E312, E248. subst w72 w208 w320 w312 w248.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
assert (X8 : (ST + 1368 + 160 * sub) mod 8 = 0) by (clear - S8; Z.div_mod_to_equations; lia).
set (v0 := nb_voc_offset st) in *.
bato 0xa34b4. rewrite sx32_small by (unfold int31; lia).
bato 0xa34c0. rewrite (zb_lxor_ones (ST + 1368 + 160 * sub)) by lia. astep.
destruct (Z_lt_ge_dec v0 40) as [L0 | L0].
2: { sh_if.
bato 0xa3570.
bato 0xa3578.
apply evt_done. do 12 eexists. exists v0. eexists. split; [reflexivity|].
split; [exact MU|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite voc_loop_step; unfold NB_SUBFRAME_SIZE; replace (v0 <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; exact TL|]. split; [exact XW| exact LXW]. }
sh_if.
bato 0xa34cc. astep. sh_if.
bato 0xa34e8. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
astep. replace (ST + 1368 + 160 * sub + v0 * 4) with (ST + 1368 + 160 * sub + 4 * v0) by lia.
destruct (nbe_f32_split3 _ (ST + 1368 + 160 * sub) xw v0 XW ltac:(lia)) as (W1 & W2 & W3). clear XW.
remember (firstn (Z.to_nat v0) xw) as l1 eqn:EL1. remember (skipn (S (Z.to_nat v0)) xw) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = v0) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 39 - v0) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
bato 0xa34f8. astep. chk_merge OBX 4.
astep.
assert (XW : rw_cells bsegs m0 (ST + 1368 + 160 * sub) (f32 (l1 ++ reg_get F 24 :: l3))).
{ apply nbe_f32_join3; [exact W1| rewrite LL1; exact W2| rewrite LL1; exact W3]. }
assert (LXW1 : length (l1 ++ reg_get F 24 :: l3) = 40%nat) by (rewrite length_app; cbn [length]; lia).
clear W1 W2 W3. clear LXW. set (xw1 := l1 ++ reg_get F 24 :: l3) in *. clearbody xw1. clear l1 l3 LL1 LL3.
bato 0xa3528. rewrite ?swrap32_small by lia.
rewrite ?Z.add_0_r in *. astep.
destruct (Z_lt_ge_dec (v0 + olp) 40) as [L1 | L1].
2: { sh_if.
bato 0xa3578.
apply evt_done. do 12 eexists. exists (v0 + olp). eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite !voc_loop_step; unfold NB_SUBFRAME_SIZE;
replace (v0 <? 40) with true by (symmetry; apply Z.ltb_lt; lia); replace (v0 + olp <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; eassumption|]. split; [eassumption| exact LXW1]. }
sh_if.
bato 0xa34cc. astep. sh_if.
bato 0xa34e8. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
astep. replace (ST + 1368 + 160 * sub + (v0 + olp) * 4) with (ST + 1368 + 160 * sub + 4 * (v0 + olp)) by lia.
destruct (nbe_f32_split3 _ (ST + 1368 + 160 * sub) xw1 (v0 + olp) XW ltac:(lia)) as (W1 & W2 & W3). clear XW.
remember (firstn (Z.to_nat (v0 + olp)) xw1) as l1 eqn:EL1. remember (skipn (S (Z.to_nat (v0 + olp))) xw1) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = v0 + olp) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 39 - (v0 + olp)) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
bato 0xa34f8. astep. chk_merge OBX 4.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (XW : rw_cells bsegs mc (ST + 1368 + 160 * sub) (f32 (l1 ++ reg_get F 24 :: l3)))
by (apply nbe_f32_join3; [exact W1| rewrite LL1; exact W2| rewrite LL1; exact W3]) end.
assert (LXW2 : length (l1 ++ reg_get F 24 :: l3) = 40%nat) by (rewrite length_app; cbn [length]; lia).
clear W1 W2 W3. clear LXW1. set (xw2 := l1 ++ reg_get F 24 :: l3) in *. clearbody xw2. clear l1 l3 LL1 LL3.
bato 0xa3528. rewrite ?swrap32_small by lia.
rewrite ?Z.add_0_r in *. astep.
destruct (Z_lt_ge_dec (v0 + olp + olp) 40) as [L2 | L2].
2: { sh_if.
bato 0xa3578.
apply evt_done. do 12 eexists. exists (v0 + olp + olp). eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite !voc_loop_step; unfold NB_SUBFRAME_SIZE;
replace (v0 <? 40) with true by (symmetry; apply Z.ltb_lt; lia); replace (v0 + olp <? 40) with true by (symmetry; apply Z.ltb_lt; lia);
replace (v0 + olp + olp <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; eassumption|]. split; [eassumption| exact LXW2]. }
sh_if.
bato 0xa34cc. astep. sh_if.
bato 0xa34e8. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
astep. replace (ST + 1368 + 160 * sub + (v0 + olp + olp) * 4) with (ST + 1368 + 160 * sub + 4 * (v0 + olp + olp)) by lia.
destruct (nbe_f32_split3 _ (ST + 1368 + 160 * sub) xw2 (v0 + olp + olp) XW ltac:(lia)) as (W1 & W2 & W3). clear XW.
remember (firstn (Z.to_nat (v0 + olp + olp)) xw2) as l1 eqn:EL1. remember (skipn (S (Z.to_nat (v0 + olp + olp))) xw2) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = v0 + olp + olp) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 39 - (v0 + olp + olp)) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
bato 0xa34f8. astep. chk_merge OBX 4.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (XW : rw_cells bsegs mc (ST + 1368 + 160 * sub) (f32 (l1 ++ reg_get F 24 :: l3)))
by (apply nbe_f32_join3; [exact W1| rewrite LL1; exact W2| rewrite LL1; exact W3]) end.
assert (LXW3 : length (l1 ++ reg_get F 24 :: l3) = 40%nat) by (rewrite length_app; cbn [length]; lia).
clear W1 W2 W3. clear LXW2. set (xw3 := l1 ++ reg_get F 24 :: l3) in *. clearbody xw3. clear l1 l3 LL1 LL3.
bato 0xa3528. rewrite ?swrap32_small by lia.
rewrite ?Z.add_0_r in *. astep. sh_if.
bato 0xa3578.
apply evt_done. do 12 eexists. exists (v0 + olp + olp + olp). eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite !voc_loop_step; unfold NB_SUBFRAME_SIZE;
replace (v0 <? 40) with true by (symmetry; apply Z.ltb_lt; lia); replace (v0 + olp <? 40) with true by (symmetry; apply Z.ltb_lt; lia);
replace (v0 + olp + olp <? 40) with true by (symmetry; apply Z.ltb_lt; lia);
replace (v0 + olp + olp + olp <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; eassumption|]. split; [eassumption| exact LXW3].
Qed.

Section VOC.
Variables (ST EXW FF lo usp : Z) (inn : list word) (m : mem).
Variables xra sp gp tp t1 s0 s1 s2 s3 s7 s9 t3 t4 t5 t6 : word.
Hypothesis OBX : aobj bsegs m EXW 160.
Hypothesis X8 : EXW mod 8 = 0.
Hypothesis XPOS : 0 < EXW.
Hypothesis XSH : EXW + 160 <= SH_LO \/ SH_HI <= EXW.
Hypothesis XTOP : IMG_TOP_B <= EXW.
Hypothesis OBS : aobj bsegs m ST 2968.
Hypothesis S8 : ST mod 8 = 0.
Hypothesis SPOS : 0 < ST.
Hypothesis SSH : ST + 2968 <= SH_LO \/ SH_HI <= ST.
Hypothesis SX : ST <= EXW.
Hypothesis XS : EXW + 160 <= ST + 2032.
Hypothesis LINN : length inn = 40%nat.
Hypothesis FTOP : IMG_TOP_B <= FF.
Hypothesis FSH : FF + 2048 <= SH_LO \/ SH_HI <= FF.
Hypothesis XFA : EXW + 160 <= FF \/ FF + 2048 <= EXW.
Hypothesis SFA : ST + 2968 <= FF \/ FF + 2048 <= ST.
Hypothesis SLO : ST + 2968 <= lo.
Hypothesis FLO : FF + 2048 <= lo.
Hypothesis LO : lo <= usp.
Hypothesis SPH : usp < 2^63.
Hypothesis LOS : SH_HI <= lo.
Definition RVOC (off : Z) (t0 a0 a3 a4 a5 a6 a7 : word) : bvmap 5 word :=
mkR xra sp gp tp t0 t1 (Z_to_bv 64 160) s0 s1 a0 (Z_to_bv 64 (18446744073709551615 - EXW)) (Z_to_bv 64 off) a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 EXW) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6.
Definition voc_post : machine_state -> Prop :=
fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (xw' vs' : list word),
ms = MS (mkR xra sp gp tp t0' t1 (Z_to_bv 64 160) s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 EXW) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7
(Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F' (Z_to_bv 64 0xa3704) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ munch [(EXW, EXW + 160); (ST + 2936, ST + 2948)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' EXW (f32 xw') /\ length xw' = 40%nat /\ rw_cells bsegs m' (ST + 2936) (f32 vs') /\ length vs' = 3%nat.
Local Notation W := [(EXW, EXW + 160); (ST + 2936, ST + 2948)].

Lemma voc_loop_walk : forall (rest dn : list word) (x v1 v2 v3 : word) (off : Z) (t0 a0 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) fc m1,
(length dn + S (length rest))%nat = 40%nat -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 EXW (f32 dn) -> rw_cells bsegs m1 (EXW + off) (f32 (x :: rest)) ->
rw_cells bsegs m1 (ST + 2936) [C4 v1; C4 v2; C4 v3] -> rw_cells bsegs m1 (FF + 320) (f32 inn) ->
evt bsegs voc_post (MS (RVOC off t0 a0 a3 a4 a5 a6 a7) F (Z_to_bv 64 0xa3578) fc None m1 (seg_rom bsegs)).
Proof using OBX X8 XPOS XSH XTOP OBS S8 SPOS SSH SX XS LINN FTOP FSH XFA SFA SLO FLO LO SPH LOS.
induction rest as [|x' rest IH]; intros dn x v1 v2 v3 off t0 a0 a3 a4 a5 a6 a7 F fc m1 HL Hoff FRM MU OF WM MI DONE X VS INN;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof LOS as LOS'; unfold SH_HI in LOS'; pose proof FTOP as FTOP'; unfold IMG_TOP_B in FTOP'; pose proof XTOP as XTOP';
unfold IMG_TOP_B in XTOP'; pose proof XSH as XSH'; pose proof FSH as FSH'; pose proof SSH as SSH'; unfold SH_LO, SH_HI in XSH', FSH', SSH';
destruct (nbe_rw_f32_nth m1 (FF + 320) inn (Z.of_nat (length dn)) INN ltac:(lia)) as (wi & WI);
replace (FF + 320 + 4 * Z.of_nat (length dn)) with (FF + 320 + off) in WI by lia;
unfold RVOC; rewrite f32_cons in X; chunk_uncons X as X1; cbn [length] in *.
-
bato 0xa3590. astep. chk_merge OBX 4.
bato 0xa35a4. astep. try chk_merge OBS 4.
bato 0xa35c0. astep. try chk_merge OBS 4.
bato 0xa35cc. astep. chk_merge OBX 4.
bato 0xa3600. astep. try chk_merge OBS 4.
bato 0xa3610. astep. try chk_merge OBS 4.
bato 0xa3624. astep. try chk_merge OBS 4.
bato 0xa3634. astep. try chk_merge OBS 4.
bato 0xa3658. astep. chk_merge OBX 4.
bato 0xa366c. astep. try sh_if.
astep.
unfold voc_post. apply evt_done. do 12 eexists.
lazymatch goal with H : rw_cells bsegs ?mc (EXW + off) [C4 ?w] |- _ => exists (dn ++ [w]) end.
lazymatch goal with H : rw_cells bsegs ?mc (ST + 2936) [C4 ?w1; C4 ?w2; C4 ?w3] |- _ => exists [w1; w2; w3] end.
split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [chunk_snoc DONE X1; change [C4 ?w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE; exact DONE|].
split; [rewrite length_app; cbn [length]; lia|]. split; [eassumption| reflexivity].
-
bato 0xa3590. astep. chk_merge OBX 4.
bato 0xa35a4. astep. try chk_merge OBS 4.
bato 0xa35c0. astep. try chk_merge OBS 4.
bato 0xa35cc. astep. chk_merge OBX 4.
bato 0xa3600. astep. try chk_merge OBS 4.
bato 0xa3610. astep. try chk_merge OBS 4.
bato 0xa3624. astep. try chk_merge OBS 4.
bato 0xa3634. astep. try chk_merge OBS 4.
bato 0xa3658. astep. chk_merge OBX 4.
bato 0xa366c. astep. sh_if.
lazymatch goal with H : rw_cells bsegs ?mc (EXW + off) [C4 ?w] |- _ =>
chunk_snoc DONE H; change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE end.
lazymatch goal with H : rw_cells bsegs ?mc (ST + 2936) [C4 ?w1; C4 ?w2; C4 ?w3] |- _ => rename H into VS' end.
replace (EXW + off + 4) with (EXW + (off + 4)) in * by lia.
eapply (IH (dn ++ _) x' _ _ _ (off + 4)); try eassumption.
all: try (rewrite ?length_app; cbn [length]; lia).
Qed.
End VOC.

Definition NBE_PC_BK : Z := 0xa3704.
Lemma nbe_bk : forall (usp lo ST FF sub : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s9 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) ->
v224 s = Z_to_bv 64 sub -> v264 s = Z_to_bv 64 (40 * sub) -> v168 s = Z_to_bv 64 (ST + 2032) -> v176 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB) -> 0 <= sub < 4 ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> usp < 2^63 -> SH_HI <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m' : mem) (t2' a0' : word),
munch [(usp + -576, usp + -200)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (usp + -576) (slot_cells (sset 264 (Z_to_bv 64 (40 * (sub + 1))) s))
/\ ((sub < 3 /\ ms = MS (R_EL usp ST FF (sub + 1) gp tp xra t0 t1 a0' a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6)
F (Z_to_bv 64 PC_NBD_E) fc None m' (seg_rom bsegs))
\/ (sub = 3 /\ ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1 a2 a3 a4 a5
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
s2 s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_EXIT) fc None m' (seg_rom bsegs))))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_BK) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E224 E264 E168 E176 SUB ST0 LO SPH LOS MI.
unfold NBE_PC_EXIT, NBE_PC_BK, PC_NBD_E, R_EL in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v224 v264 v168 v176] in E224, E264, E168, E176. subst w224 w264 w168 w176.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
bato 0xa3724. rewrite ?Z.add_0_r.
rewrite (swrap32_small (sub + 1)) by lia.
replace (40 * sub + 40) with (40 * (sub + 1)) in * by lia.
rewrite (swrap32_small (40 * (sub + 1))) in SL by lia.
astep.
destruct (Z.eq_dec sub 3) as [S3 | S3].
+ subst sub. sh_if.
apply evt_done. do 3 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [exact SL|]. right. split; [reflexivity| reflexivity].
+ sh_if. astep.
apply evt_done. do 3 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [exact SL|]. left. split; [lia| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

