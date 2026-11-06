(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X09f X09e X091.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0yt X0wi X0wk X0yd X0x2
X0zp X0zs X0zu X0ze.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Section NRand.
Variables (X0 usp : Z).
Variables (ra gp tp s0 s1 a0 a3 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word).
Variable m : mem.
Hypothesis OBX : aobj bsegs m X0 640.
Hypothesis X4 : X0 mod 4 = 0.
Hypothesis XP : 0 < X0.
Local Notation W := [(X0, X0 + 640)].
Definition nrand_R (a1 a2 a6 t4 t5 t6 : word) : bvmap 5 word :=
mkR ra (Z_to_bv 64 (usp + -576)) gp tp (Z_to_bv 64 1013904223) (Z_to_bv 64 8388607) (Z_to_bv 64 1664525) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 X0) (Z_to_bv 64 1) a6
(Z_to_bv 64 1065353216) s2 s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 (Z_to_bv 64 1) t4 t5 t6.
Definition nrand_post : machine_state -> Prop :=
fun ms' => exists (a2' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws : list word),
ms' = MS (nrand_R (Z_to_bv 64 (X0 + 640)) a2' (Z_to_bv 64 0) (Z_to_bv 64 (X0 + 640)) t5' t6') F' (Z_to_bv 64 0xa2234) fc' None m' (seg_rom bsegs)
/\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ frm0 fc' /\ rw_cells bsegs m' X0 (f32 ws) /\ length ws = 160%nat.

Lemma nrand_loop : forall (rest dn : list word) (x a2 t5 t6 : word) (kz off xa : Z) F fc m1,
Z.of_nat (length dn) + Z.of_nat (S (length rest)) = 160 ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length dn) -> xa = X0 + off ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 X0 (f32 dn) -> rw_cells bsegs m1 (X0 + off) (f32 (x :: rest)) ->
evt bsegs nrand_post
(MS (nrand_R (Z_to_bv 64 xa) a2 (Z_to_bv 64 kz) (Z_to_bv 64 xa) t5 t6) F (Z_to_bv 64 0xa21b4) fc None m1 (seg_rom bsegs)).
Proof using OBX X4 XP.
induction rest as [|x' rest IH]; intros dn x a2 t5 t6 kz off xa F fc m1 HL Hkz Hoff Hxa FRM MU OF WM MI DONE X; subst xa;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *; subst kz;
unfold nrand_R; rewrite !f32_cons, ?f32_nil in X.
- bato 0xa21e8. astep. chk_merge OBX 4.
bato 0xa2218. astep. try sh_if.
bato 0xa2234.
replace (X0 + off + 4) with (X0 + 640) by (cbn [length] in HL; lia).
replace (Z.of_nat (S (length (@nil word))) + -1) with 0 by reflexivity.
unfold nrand_post, nrand_R. finish.
+ chunk_snoc DONE X. f32_fold_snoc DONE. exact DONE.
+ rewrite length_app. cbn [length] in *. lia.
- bato 0xa21e8. astep. chk_merge OBX 4.
bato 0xa2218. astep. cbn [length]. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
replace (X0 + off + 4) with (X0 + (off + 4)) in * by lia.
rewrite <- f32_cons in X. f32_fold_snoc DONE.
eapply (IH _ x' _ _ _ _ (off + 4) (X0 + (off + 4))); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End NRand.

Local Ltac slia ::= slia_ch.
Local Ltac tlia ::= tlia_one.

Definition PC_asan_memset : Z := 0x6689c.
Definition RA_nbd_n_memset : Z := 0xa22c0.

Definition R_N (usp ST f : Z) (gp tp : word) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (f + 80)) (Z_to_bv 64 ST) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) (Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 0x23ca0) (Z_to_bv 64 (ST + 2184)) t3 t4 t5 t6.
Definition nbN_W (usp ST OUT f sf : Z) : list (Z * Z) :=
[(usp + -704, usp + -576); (sf, sf + 256); (f + 80, f + 120); (ST + 8, ST + 12); (ST + 1368, ST + 2008); (ST + 2120, ST + 2160); (ST + 2228, ST + 2232); (OUT, OUT + 640)].

Lemma nbd_n1 : forall {ptr : Type} (usp lo ST A OUT f sf : Z) (gp tp : word) (st : nb_state ptr) (s : nbslots) (rs : list byte) (lg seed : word)
(lpc0 exc0 iq msp ows : list word) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 128 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 2048 <= lo -> f + 2048 <= APP_TOP -> IMG_TOP_B <= f -> hidp (f + 2048 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP_B <= ST ->
hidp (ST + NBSTATE_SIZEOF <= f \/ f + 2048 <= ST) -> hidp (ST + NBSTATE_SIZEOF <= sf \/ sf + 256 <= ST) ->
aobj bsegs m OUT 640 -> OUT mod 4 = 0 -> IMG_TOP_B <= OUT -> OUT + 640 <= lo -> hidp (OUT + 640 <= SH_LO \/ SH_HI <= OUT) ->
hidp (ST + NBSTATE_SIZEOF <= OUT \/ OUT + 640 <= ST) -> hidp (OUT + 640 <= f \/ f + 2048 <= OUT) -> hidp (OUT + 640 <= sf \/ sf + 256 <= OUT) ->
rw_cells bsegs m (usp + -576) (slot_cells s) -> v56 s = Z_to_bv 64 f -> v64 s = Z_to_bv 64 (ST + 2047) -> v88 s = Z_to_bv 64 ST ->
v168 s = Z_to_bv 64 (ST + 2032) -> v176 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB) -> v192 s = Z_to_bv 64 (ST + 2184) -> v200 s = Z_to_bv 64 sf ->
v240 s = Z_to_bv 64 OUT ->
rw_cells bsegs m sf (nbd_shadow_g true false false false false false false false rs) ->
rw_cells bsegs m (f + 80) (f32 lpc0) -> length lpc0 = 10%nat ->
rw_cells bsegs m ST (nb_hdr_cells A_speex_nb_mode st lg) ->
rw_cells bsegs m (ST + 1368) (f32 exc0) -> length exc0 = 160%nat ->
rw_cells bsegs m (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))] ->
rw_cells bsegs m (ST + 2080) (f32 iq) -> length iq = 10%nat ->
rw_cells bsegs m (ST + 2120) (f32 msp) -> length msp = 10%nat ->
rw_cells bsegs m (ST + 2184) [C8 (Z_to_bv 64 (nb_isave_ptr OUT st))] -> (match nb_innov_save st with Some k => 160 <= k /\ 4 * (k + 160) <= 8000 | None => True end) ->
rw_cells bsegs m (ST + 2228) [C4 seed] ->
rw_cells bsegs m OUT (f32 ows) -> length ows = 160%nat ->
client_constsB m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc' (lpc' exc' msp' ows' : list word) (seed' : word),
munch (nbN_W usp ST OUT f sf) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576) /\ frm0 fc' /\ client_constsB m'
/\ rw_cells bsegs m' sf (nbd_shadow_g true true false false false false false false rs)
/\ rw_cells bsegs m' (f + 80) (f32 lpc') /\ length lpc' = 10%nat
/\ rw_cells bsegs m' ST (nb_hdr_cells A_speex_nb_mode (set_nb_first st 1) lg)
/\ rw_cells bsegs m' (ST + 1368) (f32 exc') /\ length exc' = 160%nat
/\ rw_cells bsegs m' (ST + 2120) (f32 msp') /\ length msp' = 10%nat
/\ rw_cells bsegs m' (ST + 2228) [C4 seed']
/\ rw_cells bsegs m' OUT (f32 ows') /\ length ows' = 160%nat
/\ match nb_innov_save st with
| None => exists xra' a0' a1' a2' : word,
ms = MS (R_N usp ST f gp tp xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 RA_nbd_n_memset) fc' None m' (seg_rom bsegs)
| Some k => ms = MS (R_N usp ST f gp tp (Z_to_bv 64 RA_nbd_n_memset) t0' t1' t2' (Z_to_bv 64 (OUT + 4 * k)) (Z_to_bv 64 0) (Z_to_bv 64 640) a3' a4' a5' a6' a7' t3' t4' t5' t6')
F' (Z_to_bv 64 PC_asan_memset) fc' None m' (seg_rom bsegs)
end)
(MS (R_B2 usp ST A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_N) fc None m (seg_rom bsegs)).
Proof.
intros ptr usp lo ST A OUT f sf gp tp st s rs lg seed lpc0 exc0 iq msp ows xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m.
intros ST0 LO LOS SPH F0 F64 FLO FAT FTOP FSH Esf OBS S8 SP0 SLO SSH STTOP SFA SSA OBO O4 OTOP OLO OSH SOA OFA OSA FR E56 E64 E88 E168 E176 E192 E200 E240
FRS LP LLP HDR EXC LEXC EXP IQ LIQ MSP LMSP ISV ISVR SEED OW LOW CC MI FRM.
unfold R_B2, R_N, PC_NBD_N, RA_nbd_n_memset, PC_asan_memset, NBSTATE_SIZEOF, nbN_W, nb_hdr_cells in *.
pose proof OBS as (OS0 & OS1 & _). pose proof OBO as (OO0 & OO1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof STTOP as STTOP'. unfold IMG_TOP_B in STTOP'. pose proof OTOP as OTOP'. unfold IMG_TOP_B in OTOP'.
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (2048 / 8) with 256 in SW. unfold SH_LO, SH_HI in SW.
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v56 v64 v88 v168 v176 v192 v200 v240] in E56, E64, E88, E168, E176, E192, E200, E240. subst w56 w64 w88 w168 w176 w192 w200 w240.
unfold slot_cells in FR. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232
v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in FR.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(usp + -704, usp + -576); (sf, sf + 256); (f + 80, f + 120); (ST + 8, ST + 12); (ST + 1368, ST + 2008); (ST + 2120, ST + 2160); (ST + 2228, ST + 2232); (OUT, OUT + 640)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (SHF : forall o n, 0 <= o -> o + n <= 140737488355328 -> (o + n <= f \/ f + 2048 <= o) ->
shfree [(usp + -704, usp + -576); (sf, sf + 256); (f + 80, f + 120); (ST + 8, ST + 12); (ST + 1368, ST + 2008); (ST + 2120, ST + 2160); (ST + 2228, ST + 2232); (OUT, OUT + 640)] o n).
{ intros o n O0 O1 OFA'. pose proof (FSH : _ \/ _) as FSH'. pose proof (SSH : _ \/ _) as SSH'. pose proof (OSH : _ \/ _) as OSH'.
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply (shfree_cons_sh _ _ _ _ _ f 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite Esf, shad_shiftr; lia | rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact OFA' |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_nil. }
pose proof (SHF ST 2968 ltac:(lia) ltac:(lia) SFA) as SFR.
pose proof (SHF OUT 640 ltac:(lia) ltac:(lia) OFA) as SFO.
repeat match goal with H : hidp ?P |- _ => change (hid P) in H end. unfold SH_LO, SH_HI in FSH, SSH, OSH.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS. cbn [map repeat app] in FRS.
bato 0xa210c.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc ST 2968 OBS MUc SFR) as OBSc;
assert (ACL : acc bsegs mc (f + 80) 40) by
(refine (shadow_acc mc f sf _ (map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; 0; 4; -14; -14]) _ 5%nat FRS eq_refl Esf F64 _); lia);
assert (OBIQ : aobj bsegs mc (ST + 2080) (4 * Z.of_nat (length iq))) by (rewrite LIQ; eapply aobj_sub; [exact OBSc | lia | lia]);
assert (OBLP : aobj bsegs mc (f + 80) (4 * Z.of_nat (length iq))) by (rewrite LIQ; split; [lia|]; split; [unfold APP_TOP; lia| exact ACL]);
assert (CCc : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))))
end
end.
call (bw_lpc_walk iq (ST + 2080) (f + 80) (usp + -576) lo).
{ rewrite LIQ; cbn; lia. }
{ exact OBIQ. }
{ exact OBLP. }
{ clear - S8; Z.div_mod_to_equations; lia. }
{ clear - F64; Z.div_mod_to_equations; lia. }
{ lia. }
{ exact LOS. }
{ lia. }
{ rewrite LIQ. unfold hid in FSH. unfold SH_LO, SH_HI. cbn. clear - FSH. lia. }
{ left. rewrite LIQ. cbn. lia. }
{ left. rewrite LIQ. cbn. lia. }
{ rewrite LIQ. unfold hid in SFA. cbn. clear - SFA. lia. }
{ lia. }
{ eassumption. }
{ eassumption. }
{ rewrite LLP, LIQ. reflexivity. }
{ eassumption. }
{ eassumption. }
{ unfold IMG_TOP_B. lia. }
{ exact CCc. }
{ eassumption. }
{ rewrite LIQ. reflexivity. }
rename PC1 into LP1. rename PC0 into FRM1. rename PC into ST1. clear POST FRM.
lazymatch type of LP1 with rw_cells _ _ _ (f32 ?l) =>
assert (LLP1 : length l = 10%nat) by (rewrite A.X05n.length_bw_outs; exact LIQ); generalize dependent l; intros lpc1 LP1 LLP1 end.
bato 0xa212c.
clear OBSc OBIQ OBLP CCc.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc ST 2968 OBS MUc SFR) as OBSc2;
assert (OBEX : aobj bsegs mc (ST + 1368) (4 * Z.of_nat (length exc0))) by (rewrite LEXC; eapply aobj_sub; [exact OBSc2 | lia | lia])
end
end.
replace (Z_to_bv 64 160) with (Z_to_bv 64 (Z.of_nat (length exc0))) by (rewrite LEXC; reflexivity).
call (compute_rms16_walk exc0 (ST + 1368) (usp + -576) lo).
{ rewrite LEXC; cbn; lia. }
{ exact OBEX. }
{ clear - S8; Z.div_mod_to_equations; lia. }
{ lia. }
{ lia. }
{ exact LOS. }
{ lia. }
{ left. rewrite LEXC. cbn. lia. }
{ eassumption. }
{ eassumption. }
{ eassumption. }
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
{ eassumption. }
rename PC into ST2. rename POST into FRM2. clear FRM1 OBSc2 OBEX.
bato 0xa21b4.
assert (B1 : (0 <? ST + 1368) = true) by (apply Z.ltb_lt; lia).
assert (B2 : (Z.land (ST + 1368) 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - S8; Z.div_mod_to_equations; lia).
rewrite B1, B2. cbn [Z.b2z]. change (Z.land 1 1) with 1.
destruct exc0 as [|xe0 rest0]; [cbn in LEXC; lia|].
replace (ST + 1368) with (ST + 1368 + 0) in EXC at 1 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc ST 2968 OBS MUc SFR) as OBSc3;
assert (OBX0 : aobj bsegs mc (ST + 1368) 640) by (eapply aobj_sub; [exact OBSc3 | lia | lia]);
assert (X04 : (ST + 1368) mod 4 = 0) by (clear - S8; Z.div_mod_to_equations; lia);
call (nrand_loop (ST + 1368) usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc OBX0 X04 ltac:(lia) rest0 [] xe0 _ _ _ _ 0 (ST + 1368) _ _ mc)
end
end.
{ cbn in LEXC |- *. lia. }
{ cbn in LEXC |- *. lia. }
{ reflexivity. }
{ lia. }
{ eassumption. }
{ apply munch_refl. }
{ cbn. unfold hid in SSH. unfold SH_LO, SH_HI. clear - SSH. lia. }
{ apply wmono_refl. }
{ eassumption. }
{ rewrite f32_nil. apply rw_cells_nil. lia. }
{ exact EXC. }
rename PC0 into EXC1. rename POST into LEXC1. rename PC into FRM3. clear FRM OBSc3 OBX0.
unfold nrand_R.
bato 0xa2294.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc ST 2968 OBS MUc SFR) as OBSc4;
pose proof (aobj_munch bsegs W m mc OUT 640 OBO MUc SFO) as OBOc4;
assert (ACL4 : acc bsegs mc (f + 80) 40) by
(refine (shadow_acc mc f sf _ (map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; 0; 4; -14; -14]) _ 5%nat FRS eq_refl Esf F64 _); lia);
assert (OBX4 : aobj bsegs mc (ST + 1368) (4 * Z.of_nat (length x43))) by (rewrite LEXC1; eapply aobj_sub; [exact OBSc4 | lia | lia]);
assert (OBD4 : aobj bsegs mc (f + 80) (4 * Z.of_nat (length lpc1))) by (rewrite LLP1; split; [lia|]; split; [unfold APP_TOP; lia| exact ACL4]);
assert (OBM4 : aobj bsegs mc (ST + 2120) (4 * Z.of_nat (length lpc1))) by (rewrite LLP1; eapply aobj_sub; [exact OBSc4 | lia | lia]);
assert (OBY4 : aobj bsegs mc OUT (4 * Z.of_nat (length x43))) by (rewrite LEXC1; exact OBOc4)
end
end.
clear OBSc4 OBOc4 ACL4.
replace (Z_to_bv 64 160) with (Z_to_bv 64 (Z.of_nat (length x43))) by (rewrite LEXC1; reflexivity).
replace (Z_to_bv 64 10) with (Z_to_bv 64 (Z.of_nat (length lpc1))) by (rewrite LLP1; reflexivity).
call (iir_mem16_walk_dj x43 lpc1 msp (ST + 1368) (f + 80) (ST + 2120) (usp + -576) lo).
{ rewrite LMSP, LLP1. reflexivity. }
{ rewrite LEXC1. cbn. lia. }
{ rewrite LLP1. cbn. lia. }
{ exact OBX4. }
{ exact OBD4. }
{ exact OBM4. }
{ clear - S8; Z.div_mod_to_equations; lia. }
{ clear - F64; Z.div_mod_to_equations; lia. }
{ clear - S8; Z.div_mod_to_equations; lia. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ exact LOS. }
{ lia. }
{ rewrite LLP1. unfold hid in SSH. unfold SH_LO, SH_HI. cbn. clear - SSH. lia. }
{ left. rewrite LEXC1. cbn. lia. }
{ left. rewrite LLP1. cbn. lia. }
{ left. rewrite LLP1. cbn. lia. }
{ rewrite LLP1. unfold hid in SFA. cbn. clear - SFA. lia. }
{ rewrite LEXC1, LLP1. cbn. lia. }
{ rewrite LEXC1, LLP1. unfold hid in SFA. cbn. clear - SFA. lia. }
{ exact OBY4. }
{ exact O4. }
{ lia. }
{ rewrite LEXC1. unfold hid in OSH. unfold SH_LO, SH_HI. cbn. clear - OSH. lia. }
{ left. rewrite LEXC1. cbn. lia. }
{ rewrite LEXC1. unfold hid in SOA. cbn. clear - SOA. lia. }
{ rewrite LEXC1, LLP1. unfold hid in SOA. cbn. clear - SOA. lia. }
{ rewrite LEXC1, LLP1. unfold hid in OFA. cbn. clear - OFA. lia. }
{ eassumption. }
{ eassumption. }
{ eassumption. }
{ eassumption. }
{ rewrite LOW, LEXC1. reflexivity. }
{ eassumption. }
{ eassumption. }
{ exact OTOP. }
{ unfold IMG_TOP_B. lia. }
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
{ eassumption. }
rename PC into ST3. rename PC0 into FRM4. rename PC2 into OW1. rename PC1 into LOW1. rename PC4 into MSP1. rename PC3 into LMSP1. clear POST PC5 FRM3 OBX4 OBD4 OBM4 OBY4.
unfold nb_isave_ptr in ISV.
cbn [nb_first nb_count_lost nb_sampling_rate set_nb_first].
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [map repeat app].
destruct (nb_innov_save st) as [k|] eqn:EIS.
- bato 0xa22b0. astep. sh_if.
bato 0xa22bc. astep.
apply evt_done. do 20 eexists.
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3|]. split; [exact FRM4|].
split; [unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))|].
split; [exact FRS|]. split; [exact LP1|]. split; [exact LLP1|]. split; [exact HDR|].
split; [exact EXC1|]. split; [exact LEXC1|]. split; [exact MSP1|]. split; [rewrite LMSP1; exact LLP1|].
split; [exact SEED|]. split; [exact OW1|]. split; [rewrite LOW1; exact LEXC1|].
reflexivity.
- bato 0xa22b0. astep.
apply evt_done. do 20 eexists.
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3|]. split; [exact FRM4|].
split; [unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))|].
split; [exact FRS|]. split; [exact LP1|]. split; [exact LLP1|]. split; [exact HDR|].
split; [exact EXC1|]. split; [exact LEXC1|]. split; [exact MSP1|]. split; [rewrite LMSP1; exact LLP1|].
split; [exact SEED|]. split; [exact OW1|]. split; [rewrite LOW1; exact LEXC1|].
do 4 eexists. reflexivity.
Qed.

Lemma nbd_n2 : forall {ptr : Type} (usp ST f sf : Z) (gp tp : word) (st : nb_state ptr) (rs : list byte) (lg : word) (s : nbslots)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= 2^47 ->
hidp (ST + NBSTATE_SIZEOF <= sf \/ sf + 256 <= ST) -> 0 <= sf -> sf + 256 <= 2^47 ->
usp < 2^63 -> ST + NBSTATE_SIZEOF <= usp + -576 -> sf + 256 <= usp + -576 ->
rw_cells bsegs m (usp + -576) (slot_cells s) -> v200 s = Z_to_bv 64 sf ->
rw_cells bsegs m ST (nb_hdr_cells A_speex_nb_mode st lg) ->
rw_cells bsegs m sf (nbd_shadow_g true true false false false false false false rs) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m' : mem) (xra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR xra' (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' (Z_to_bv 64 sf) a3' a4' a5' a6' a7'
(Z_to_bv 64 0) (Z_to_bv 64 ST) s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 PC_NBD_X) fc None m' (seg_rom bsegs)
/\ munch [(ST + 12, ST + 16); (sf, sf + 256)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' ST (nb_hdr_cells A_speex_nb_mode (set_nb_count_lost st 0) lg)
/\ rw_cells bsegs m' sf (nbd_shadow SC_X rs)
/\ rw_cells bsegs m' (usp + -576) (slot_cells s))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 ST) s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RA_nbd_n_memset) fc None m (seg_rom bsegs)).
Proof.
intros ptr usp ST f sf gp tp st rs lg s xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OBS S8 S0 S1 SSA SF0 SF1 SPH SU SFU FR E200 HDR FRS MI.
unfold PC_NBD_X, RA_nbd_n_memset, NBSTATE_SIZEOF, nb_hdr_cells, nbd_shadow, nbd_shadow_g, nbd_shg, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8 in *.
cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in *.
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
pose proof (SSA : _ \/ _) as SSA'.
unfold slot_cells in FR. rewrite E200 in FR.
pose proof (rw_cells_bound _ _ _ _ FR) as BL. cbn [cells_size csize Nat.add] in BL.
pose proof (munch_refl [(ST + 12, ST + 16); (sf, sf + 256)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xa4450.
apply evt_done. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HDR|]. split; [exact FRS|].
unfold slot_cells. rewrite E200. exact FR.
Qed.
