(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X09f X09e X091.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0wg X0wh X0w8 X0yt
X0z3 X0z4 X0z2 X0x2 X0zp X0zs X0zc X0zd X0zu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).
Definition PC_asan_memmove : Z := 0x66adc.
Definition RA_nbd_memmove : Z := 0xa1d18.

Section B.
Context {ptr : Type}.
Variables (usp lo ST A f sf : Z).
Variables gp tp : word.
Hypothesis ST8 : ST mod 8 = 0.
Hypothesis SB : 0 < ST /\ ST + 2968 <= 140737488355328.
Hypothesis STSH : hidp (ST + 2968 <= SH_LO \/ SH_HI <= ST).
Hypothesis STTOP : IMG_TOP_B <= ST.

Lemma nbd_b1 : forall (st : nb_state ptr) (pad : list byte) (s : nbslots) mo (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
aobj bsegs m ST 2968 -> rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> 0 <= mo <= 8 ->
rw_cells bsegs m (usp + -576) (slot_cells s) -> v88 s = Z_to_bv 64 ST -> usp < 2^63 -> SH_HI <= usp + -576 -> ST + 2968 <= usp + -576 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a3' a4' : word),
ms = MS (mkR (Z_to_bv 64 RA_nbd_memmove) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (ST + 32)) (Z_to_bv 64 (ST + 672)) (Z_to_bv 64 1360) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) (Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 0x23ca0) (Z_to_bv 64 (ST + 2184)) t3 t4 t5 t6)
F (Z_to_bv 64 PC_asan_memmove) fc None m1 (seg_rom bsegs)
/\ munch [(ST + 2248, ST + 2252)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR (set_nb_submodeID st mo) pad) /\ rw_cells bsegs m1 (usp + -576) (slot_cells s))
(MS (R_AB usp ST A gp tp mo xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_B) fc None m (seg_rom bsegs)).
Proof.
intros st pad s mo xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m OBST CFG MO SL E88 SPH SHL STU MI.
unfold R_AB, PC_NBD_B, PC_asan_memmove, RA_nbd_memmove, nb_cfg_cells in *.
pose proof SB as (SB0 & SB1). pose proof OBST as (O0 & O1 & _). unfold APP_TOP in *.
pose proof STTOP as STTOP'. unfold IMG_TOP_B in STTOP'. pose proof (STSH : _ \/ _) as STSH'. unfold SH_LO, SH_HI in STSH'. unfold SH_HI in SHL.
unfold slot_cells in SL. rewrite E88 in SL.
pose proof (munch_refl [(ST + 2248, ST + 2252)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xa1d14. astep.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [destruct st; exact CFG| unfold slot_cells; rewrite E88; exact SL].
Qed.
End B.
Ltac slia1h := first [ lia | match goal with H : hid (_ \/ _) |- _ => unfold hid in H; lia end ].
Ltac slia_ch := lazymatch goal with |- _ /\ _ => split; [slia1h | slia_ch] | |- True => exact I | |- _ => slia1h end.
Local Ltac slia ::= (try unfold BITS_SIZEOF, LSPQ_DEPTH in * ); slia_ch.
Local Ltac tlia ::= tlia_one.

Lemma lsp_unquant_all : forall ptr k, @lsp_unquant_stmtA ptr k.
Proof. intros ptr []; [apply lsp_unquant_lbr_stmt | apply lsp_unquant_nb_stmt | apply lsp_unquant_high_stmt]. Qed.

Definition R_B2 (usp ST A : Z) (gp tp : word) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) (Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 0x23ca0) (Z_to_bv 64 (ST + 2184)) t3 t4 t5 t6.

Definition R_B2c (usp ST A : Z) (gp tp : word) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (ST + 2248))
(Z_to_bv 64 0) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) (Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 0x23ca0) (Z_to_bv 64 (ST + 2184)) t3 t4 t5 t6.

Definition slots_B2n (ST : Z) (s : nbslots) : nbslots :=
sset 344 (Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB)) (sset 336 (Z_to_bv 64 (ST + 2240)) (sset 328 (Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB)) s)).
Definition slots_B2 (ST f : Z) (s : nbslots) : nbslots :=
sset 96 (Z_to_bv 64 0xfe6c) (sset 280 (Z_to_bv 64 (ST + 2040)) (sset 144 (Z_to_bv 64 (ST + 12)) (sset 160 (Z_to_bv 64 (Z.shiftr (ST + 12) 3 + SHB))
(sset 272 (Z_to_bv 64 (f + 160)) (sset 312 (Z_to_bv 64 (ST + 2248)) (slots_B2n ST s)))))).
Definition PC_NBD_N : Z := 0xa20d4.
Definition PC_NBD_C : Z := 0xa1f74.
Lemma nbd_b2 : forall {ptr : Type} (usp lo ST A D f sf BSZ : Z) (gp tp : word) (st : nb_state ptr) (b : bits_st ptr) (s : nbslots) (pad rs : list byte) (old : list word)
(last_ol_gain : word) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 128 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 2048 <= lo -> f + 2048 <= APP_TOP -> IMG_TOP_B <= f -> hidp (f + 2048 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
hidp (ST + NBSTATE_SIZEOF <= f \/ f + 2048 <= ST) -> hidp (ST + NBSTATE_SIZEOF <= sf \/ sf + 256 <= ST) ->
aobj bsegs m A BITS_SIZEOF -> IMG_TOP_B <= A -> A + BITS_SIZEOF <= lo -> hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
hidp (A + BITS_SIZEOF <= f \/ f + 2048 <= A) -> hidp (A + BITS_SIZEOF <= sf \/ sf + 256 <= A) -> hidp (ST + NBSTATE_SIZEOF <= A \/ A + BITS_SIZEOF <= ST) ->
aobj bsegs m D BSZ -> D + BSZ <= lo -> hidp (D + BSZ <= f \/ f + 2048 <= D) -> hidp (D + BSZ <= sf \/ sf + 256 <= D) -> sb_buf_size b = BSZ ->
bits_rep bsegs m A D b -> bits_ok b ->
rw_cells bsegs m (usp + -576) (slot_cells s) -> v288 s = Z_to_bv 64 A -> v88 s = Z_to_bv 64 ST -> v56 s = Z_to_bv 64 f -> v200 s = Z_to_bv 64 sf ->
v192 s = Z_to_bv 64 (ST + 2184) ->
rw_cells bsegs m ST (nb_hdr_cells A_speex_nb_mode st last_ol_gain) ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
rw_cells bsegs m sf (nbd_shadow_g true false false false false false false false rs) ->
rw_cells bsegs m (f + 160) (f32 old) -> length old = 10%nat ->
lib_consts m -> lsp_tabs m -> nb_tabs_acc m -> client_constsB m -> mem_inv bsegs m -> frm0 fc ->
nb_count_lost st = 0 -> 0 <= nb_submodeID st <= 8 ->
evt bsegs (fun ms => exists (m' : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) F' fc',
munch [(usp + -704, usp + -200); (A, A + 48); (f + 160, f + 200); (sf, sf + 256)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ frm0 fc' /\ client_constsB m'
/\ rw_cells bsegs m' ST (nb_hdr_cells A_speex_nb_mode st last_ol_gain) /\ rw_cells bsegs m' (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad)
/\ match smrec_at (nb_submodeID st) with
| None =>
(exists a7' : word, ms = MS (R_B2 usp ST A gp tp xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 PC_NBD_N) fc' None m' (seg_rom bsegs))
/\ bits_rep bsegs m' A D b /\ rw_cells bsegs m' (usp + -576) (slot_cells (slots_B2n ST s))
/\ rw_cells bsegs m' sf (nbd_shadow_g true false false false false false false false rs) /\ rw_cells bsegs m' (f + 160) (f32 old)
| Some r =>
ms = MS (R_B2c usp ST A gp tp xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6') F' (Z_to_bv 64 PC_NBD_C) fc' None m' (seg_rom bsegs)
/\ bits_rep bsegs m' A D (lsp_bits (sm_lsp_unquant (smr_sm r)) b) /\ bits_ok (lsp_bits (sm_lsp_unquant (smr_sm r)) b)
/\ rw_cells bsegs m' (usp + -576) (slot_cells (slots_B2 ST f s))
/\ rw_cells bsegs m' sf (nbd_shadow_g true false true false false false false false rs)
/\ exists ql, rw_cells bsegs m' (f + 160) (f32 ql) /\ length ql = 10%nat
end)
(MS (R_B2 usp ST A gp tp (Z_to_bv 64 RA_nbd_memmove) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 RA_nbd_memmove)) fc None m (seg_rom bsegs)).
Proof.
intros ptr usp lo ST A D f sf BSZ gp tp st b s pad rs old last_ol_gain xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m.
intros ST0 LO LOS SPH F0 F64 FLO FAT FTOP FSH Esf OBS S8 SP0 SLO SSH SFA SSA OBA ATOP ALO ASH AFA ASA SAA OBD DLO DFA DSA SZ REP OKB FR E288 E88 E56 E200 E192
HDR CFG FRS QL LQL LC LT NTA CC MI FRM CL0 MO.
unfold R_B2, R_B2c, RA_nbd_memmove, PC_NBD_N, PC_NBD_C, NBSTATE_SIZEOF, BITS_SIZEOF, nb_hdr_cells, nb_cfg_cells in *.
set (mo := nb_submodeID st) in *.
pose proof OBS as (OS0 & OS1 & _). pose proof OBA as (OA0 & OA1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'. pose proof ATOP as ATOP'. unfold IMG_TOP_B in ATOP'.
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (2048 / 8) with 256 in SW. unfold SH_LO, SH_HI in SW.
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368]. cbn [v288 v88 v56 v200 v192] in E288, E88, E56, E200, E192. subst w288 w88 w56 w200 w192.
unfold slot_cells in FR. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232
v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in FR.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(usp + -704, usp + -200); (A, A + 48); (f + 160, f + 200); (sf, sf + 256)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (SHF : forall o n, 0 <= o -> o + n <= 140737488355328 -> (o + n <= f \/ f + 2048 <= o) -> shfree [(usp + -704, usp + -200); (A, A + 48); (f + 160, f + 200); (sf, sf + 256)] o n).
{ intros o n O0 O1 OFA. pose proof (ASH : _ \/ _) as ASH'. pose proof (FSH : _ \/ _) as FSH'.
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |].
apply (shfree_cons_sh _ _ _ _ _ f 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite Esf, shad_shiftr; lia | rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact OFA |].
apply shfree_nil. }
pose proof (SHF ST 2968 ltac:(lia) ltac:(lia) SFA) as SFR.
repeat match goal with H : hidp ?P |- _ => change (hid P) in H end. unfold SH_LO, SH_HI in FSH, SSH, ASH.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS. cbn [map repeat app] in FRS.
replace (ret_pc (Z_to_bv 64 0xa1d18)) with (Z_to_bv 64 0xa1d18) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct NTA as (NTM & NTR). unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof (SHF 1016704 208 ltac:(lia) ltac:(lia) ltac:(lia)) as SFM.
bato 0xa1d60. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small mo) by lia.
bato 0xa1d68. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa1da4.
chk_hint NTM. bato 0xa1db0.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa1db8.
assert (FW : Forall (fun iv : Z * Z => snd iv <= 0xf8380 \/ 0xfce00 <= fst iv) [(usp + -704, usp + -200); (A, A + 48); (f + 160, f + 200); (sf, sf + 256)]).
{ clear - LOS' LO FTOP' ATOP' SW. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
lazymatch goal with MUc : munch ?W m ?mc |- _ =>
pose proof (lib_consts_munch W m mc LC MUc FW) as LCc; pose proof (sub_ptr_read mc mo LCc MO) as RD end.
unfold NB_SUBMODES_PTR, A_nb_mode in RD. replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
destruct (smrec_at mo) as [r|] eqn:SAT.
2: { assert (E0 : smr_ptr_at mo = 0) by (unfold smr_ptr_at; rewrite SAT; reflexivity). rewrite E0.
astep.
apply evt_done. do 18 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. split; [exact FRM|].
split; [unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))|].
split; [exact HDR|]. split; [exact CFG|]. split; [eexists; reflexivity|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|].
split; [exact FR|]. split; [exact FRS| exact QL]. }
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SPz & SP1 & SP8 & LORD & SMC).
specialize (SMC m LC). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
rewrite EP. unfold IMG_TOP_B in SP1.
set (SP := smr_ptr r) in *. set (kq := sm_lsp_unquant (smr_sm r)) in *.
pose proof (SHF SP 88 ltac:(lia) ltac:(lia) ltac:(lia)) as SFP.
astep. sh_if.
bato 0xa1de0. astep.
rewrite (shb_zero bsegs m 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa1dec.
lazymatch goal with MUc : munch ?W m ?mc |- _ =>
pose proof (lib_consts_munch W m mc LC MUc FW) as LCc2; pose proof (sub_ptr_read mc mo LCc2 MO) as RD;
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (smrec_facts mo r SAT))))))) mc LCc2) as SMCc end.
unfold NB_SUBMODES_PTR, A_nb_mode in RD. replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia. rewrite EP in RD. fold SP in RD, SMCc.
astep. clear RD.
unfold smrec_cells in SMCc. cbv zeta in SMCc. fold kq in SMCc.
bato 0xa1e14. astep.
bato 0xa1e38.
astep.
pose proof (lsp_entryA_even kq) as [EV ER].
replace (ret_pc (Z_to_bv 64 (lsp_entryA kq))) with (Z_to_bv 64 (lsp_entryA kq)) by (symmetry; apply ret_pc_even; [exact ER| exact EV]).
pose proof OBD as (OD0 & OD1 & _). unfold APP_TOP in OD1.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MUc (SHF A 48 ltac:(lia) ltac:(lia) AFA)) as OBAc;
pose proof (aobj_munch bsegs W m mc _ _ OBD MUc (SHF D BSZ ltac:(lia) ltac:(lia) DFA)) as OBDc;
pose proof (lib_consts_munch W m mc LC MUc FW) as LCc3;
pose proof (lsp_tabs_munch W m mc LT MUc (fun o n H1 H2 => SHF o n ltac:(lia) ltac:(lia) ltac:(lia))) as LTc;
assert (ACQ : acc bsegs mc (f + 160) 40) by
(exact (shadow_acc mc f sf _ (map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; 0; 4; -14; -14; -8; -8; -8; -8; -8; -14; -14; -14; -14; -14]) _ 5%nat FRS eq_refl Esf F64 ltac:(lia)))
end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REPc : bits_rep bsegs mc A D b) by (exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE)));
assert (OBQ : aobj bsegs mc (f + 160) (4 * lsp_order kq)) by (rewrite LORD; split; [lia|]; split; [unfold APP_TOP; lia| exact ACQ]);
assert (CCc : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))))
end.
rewrite <- SZ in OBDc.
assert (LQ' : length old = Z.to_nat (lsp_order kq)) by (rewrite LORD; exact LQL).
assert (Q4 : (f + 160) mod 4 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
assert (H1 : hidp (f + 160 + 4 * lsp_order kq <= SH_LO \/ SH_HI <= f + 160)) by (rewrite LORD; pose proof (FSH : _ \/ _) as FSH'; unfold hidp, SH_LO, SH_HI in *; clear - FSH'; lia).
assert (H2 : hidp (f + 160 + 4 * lsp_order kq <= lo \/ usp + -576 <= f + 160)) by (rewrite LORD; unfold hidp; left; clear - FLO; lia).
assert (H3 : hidp (f + 160 + 4 * lsp_order kq <= A \/ A + BITS_SIZEOF <= f + 160)) by (rewrite LORD; pose proof (AFA : _ \/ _) as AFA'; unfold hidp, BITS_SIZEOF; clear - AFA'; lia).
assert (H4 : hidp (f + 160 + 4 * lsp_order kq <= D \/ D + sb_buf_size b <= f + 160)) by (rewrite LORD, SZ; pose proof (DFA : _ \/ _) as DFA'; unfold hidp; clear - DFA'; lia).
assert (TQ : IMG_TOP_B <= f + 160) by (unfold IMG_TOP_B; lia).
assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
replace (Z_to_bv 64 10) with (Z_to_bv 64 (lsp_order kq)) by (rewrite LORD; reflexivity).
callc (lsp_unquant_all ptr kq A D (f + 160) (usp + -576) lo b old _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
REPc OKB OBAc OBDc OBQ LTc LCc3 CCc QL LQ' Q4 ASH H1 ATOP TQ ALO DLOb H2 H3 H4) (clear REPc OBJ DAT QL).
all: try eassumption. all: try (unfold LSPQ_DEPTH; lia).
rename PC3 into REP1. rename POST into OK1. rename PC1 into QL1. rename PC2 into LQ1. rename PC0 into FRM1. rename PC into ST1.
destruct REP1 as ((rj1 & Lrj1 & OBJ1) & (bs1 & DAT1 & Hbs1) & SIDE1). unfold bits_cells in OBJ1.
pose proof (ub_size b 6) as _.
assert (SZ1 : sb_buf_size (lsp_bits kq b) = BSZ).
{ rewrite <- SZ. unfold lsp_bits. destruct kq; rewrite ?ub_size; reflexivity. }
assert (Lbs1 : Z.of_nat (length bs1) = BSZ) by (pose proof OK1 as OK'; unfold bits_ok in OK'; rewrite Hbs1, zlength_map_unsigned in OK'; lia).
rewrite LORD in LQ1. change (Z.to_nat 10) with 10%nat in LQ1.
bato 0xa1e64.
rewrite CL0. rewrite sx32_small by (unfold int31; lia).
bato 0xa1e78. astep.
apply evt_done. do 18 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; [exact FRM1|].
split; [unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))|].
split; [rewrite CL0 in HDR; exact HDR|]. split; [exact CFG|]. split; [reflexivity|].
split; [exact (conj (ex_intro _ rj1 (conj Lrj1 OBJ1)) (conj (ex_intro _ bs1 (conj DAT1 Hbs1)) SIDE1))|]. split; [exact OK1|].
split; [exact FR|]. split; [exact FRS|]. eexists. split; [exact QL1| exact LQ1].
Qed.
