(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X081 X05l X05j X05k X05b X082
X09f X069 X09e X06m X08y X091 X08x X090 X08l X08m X094 X08n.
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
Definition PC_asan_memcpy : Z := 0x66314.
Definition RA_nbd_memcpy : Z := 0xa0048.
Definition PC_NBD_D : Z := 0xa0048.

Lemma nbd_c1 : forall {ptr : Type} (usp lo ST f sf : Z) (gp tp : word) (st : nb_state ptr) (s : nbslots) (last_ol_gain : word)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
usp < 2^63 -> lo <= usp + -544 -> SH_HI <= lo -> aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> ST + NBSTATE_SIZEOF <= lo ->
rw_cells asegs m (usp + -544) (slot_cells s) -> v160 s = Z_to_bv 64 (f + 160) ->
rw_cells asegs m ST (nb_hdr_cells A_speex_nb_mode st last_ol_gain) ->
(nb_first st = 0 \/ nb_first st = 1) -> mem_inv asegs m ->
evt asegs (fun ms => exists (m' : mem),
munch [(usp + -536, usp + -528)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (usp + -544) (slot_cells (sset 8 (Z_to_bv 64 (ST + 8)) s))
/\ rw_cells asegs m' ST (nb_hdr_cells A_speex_nb_mode st last_ol_gain)
/\ if nb_first st =? 0
then exists (a0' a1' a2' : word), ms = MS (R_B2 usp ST f sf gp tp xra t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_D) fc None m' (seg_rom asegs)
else ms = MS (R_B2 usp ST f sf gp tp (Z_to_bv 64 RA_nbd_memcpy) t0 t1 t2 (Z_to_bv 64 (ST + 2040)) (Z_to_bv 64 (f + 160)) (Z_to_bv 64 40) a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (Z_to_bv 64 PC_asan_memcpy) fc None m' (seg_rom asegs))
(MS (R_B2 usp ST f sf gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_C) fc None m (seg_rom asegs)).
Proof.
intros ptr usp lo ST f sf gp tp st s last_ol_gain xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m SPH LO LOS OBS S8 SLO FR E160 HDR FST MI.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
unfold R_B2, PC_NBD_C, PC_NBD_D, PC_asan_memcpy, RA_nbd_memcpy, NBSTATE_SIZEOF, nb_hdr_cells in *.
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v160] in E160. subst w160.
unfold slot_cells in *. cbn [sset Z.eqb Pos.eqb v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in *.
pose proof (munch_refl [(usp + -536, usp + -528)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -536, usp + -528)]) by (cbn; unfold SH_LO, SH_HI; lia).
ato 0xa0034. rewrite sx32_small by (unfold int31; lia). astep.
destruct FST as [E0|E1].
- rewrite E0. cbn [Z.eqb]. sh_if.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [rewrite E0 in HDR; exact HDR| do 3 eexists; reflexivity].
- rewrite E1. cbn [Z.eqb]. sh_if. ato 0xa0044. astep.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [rewrite E1 in HDR; exact HDR| reflexivity].
Qed.

Lemma nbd_seg_unpoison : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rs : list byte) F fc (m : mem),
rw_cells asegs m sf (nbd_shadow_g true false true false false false false false rs) -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa0254) fc None m1 (seg_rom asegs)
/\ munch [(sf, sf + 256)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 sf (nbd_shadow_g true false true true true true false false rs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sf) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa01a0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FRS MI.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 256)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xa0254.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
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

Section PureD.
Context {ptr : Type}.
Definition segD_olp (sm : submode) (b : bits_st ptr) : Z := if negb (sm_lbr_pitch sm =? -1) then uv b 7 + 17 else 0.
Definition segD_b1 (sm : submode) (b : bits_st ptr) : bits_st ptr := if negb (sm_lbr_pitch sm =? -1) then ub b 7 else b.
Definition segD_b2 (sm : submode) (b : bits_st ptr) : bits_st ptr := if negb (sm_forced_pitch_gain sm =? 0) then ub (segD_b1 sm b) 4 else segD_b1 sm b.
Definition segD_b3 (sm : submode) (b : bits_st ptr) : bits_st ptr := ub (segD_b2 sm b) 5.
Definition segD_st (st : nb_state ptr) (sm : submode) (b : bits_st ptr) : nb_state ptr :=
if nb_submodeID st =? 1 then set_nb_dtx_enabled st (if uv (segD_b3 sm b) 4 =? 15 then 1 else 0)
else if 1 <? nb_submodeID st then set_nb_dtx_enabled st 0 else st.
Definition segD_bits (st : nb_state ptr) (sm : submode) (b : bits_st ptr) : bits_st ptr :=
if nb_submodeID st =? 1 then ub (segD_b3 sm b) 4 else segD_b3 sm b.
End PureD.

Definition R_D (usp ST f sf : Z) (gp tp : word) (s5 s7 s8 : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 sf) (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 s5) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 s7) (Z_to_bv 64 s8)
(Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6.
Section D.
Context {ptr : Type}.
Variables (usp lo ST A D f sf BSZ : Z).
Variables gp tp : word.
Variable m : mem.
Hypothesis LO : lo <= usp - 544 - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis F0 : 0 < f.
Hypothesis F64 : f mod 64 = 0.
Hypothesis FLO : f + 2048 <= lo.
Hypothesis FAT : f + 2048 <= APP_TOP.
Hypothesis FTOP : IMG_TOP <= f.
Hypothesis FSH : hidp (f + 2048 <= SH_LO \/ SH_HI <= f).
Hypothesis Esf : sf = Z.shiftr f 3 + SHB.
Hypothesis OBS : aobj asegs m ST NBSTATE_SIZEOF.
Hypothesis S8 : ST mod 8 = 0.
Hypothesis SLO : ST + NBSTATE_SIZEOF <= lo.
Hypothesis STTOP : IMG_TOP <= ST.
Hypothesis SSH : hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST).
Hypothesis SFA : hidp (ST + NBSTATE_SIZEOF <= f \/ f + 2048 <= ST).
Hypothesis SSA : hidp (ST + NBSTATE_SIZEOF <= sf \/ sf + 256 <= ST).
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis ATOP : IMG_TOP <= A.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis AFA : hidp (A + BITS_SIZEOF <= f \/ f + 2048 <= A).
Hypothesis ASA : hidp (A + BITS_SIZEOF <= sf \/ sf + 256 <= A).
Hypothesis SAA : hidp (ST + NBSTATE_SIZEOF <= A \/ A + BITS_SIZEOF <= ST).
Hypothesis OBD : aobj asegs m D BSZ.
Hypothesis DLO : D + BSZ <= lo.
Hypothesis DFA : hidp (D + BSZ <= f \/ f + 2048 <= D).
Hypothesis DSA : hidp (D + BSZ <= sf \/ sf + 256 <= D).
Hypothesis SDA : hidp (ST + NBSTATE_SIZEOF <= D \/ D + BSZ <= ST).
Hypothesis LC : lib_consts m.
Hypothesis NTA : nb_tabs_acc m.

Definition nbD_W : list (Z * Z) := [(usp + -672, usp + -200); (A, A + 48); (ST + 2952, ST + 2956); (sf, sf + 256)].

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
Lemma nbD_fw : Forall (fun iv : Z * Z => snd iv <= 0xefb00 \/ 0xf4580 <= fst iv) nbD_W.
Proof using LO LOS FTOP ATOP STTOP F0 F64 FAT Esf.
unfold nbD_W, IMG_TOP, SH_HI, APP_TOP in *.
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. unfold SH_LO in SW.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.
Ltac nbD_setup ST0 CC :=
unfold R_D, nbD_W, NBSTATE_SIZEOF, BITS_SIZEOF, nb_cfg_cells, nb_tail_cells in *;
pose proof LOS as LOS'; unfold SH_HI in LOS'; pose proof ST0 as (STa & STb & _);
pose proof OBS as (OS0 & OS1 & _); pose proof OBA as (OA0 & OA1 & _); pose proof OBD as (OD0 & OD1 & _); unfold APP_TOP in *;
pose proof FTOP as FTOP'; unfold IMG_TOP in FTOP'; pose proof ATOP as ATOP'; unfold IMG_TOP in ATOP'; pose proof STTOP as STTOP'; unfold IMG_TOP in STTOP';
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW;
rewrite <- shad_shiftr, <- Esf in SW; change (2048 / 8) with 256 in SW; unfold SH_LO, SH_HI in SW;
pose proof CC as (G1 & G2 & G3 & G4);
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *;
pose proof nbD_shf as SHF; unfold nbD_W in SHF;
pose proof (SHF ST 2968 ltac:(lia) ltac:(lia) SFA) as SFR;
pose proof (SHF A 48 ltac:(lia) ltac:(lia) AFA) as SFRA;
pose proof (SHF D BSZ ltac:(lia) ltac:(lia) DFA) as SFRD;
pose proof nbD_fw as FW; unfold nbD_W in FW;
repeat match goal with H : hidp ?P |- _ => change (hid P) in H end; unfold SH_LO, SH_HI in FSH, SSH, ASH.
Ltac nbD_cc G1 G2 G3 G4 := unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))).
Ltac slots_open s FR :=
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336];
unfold slot_cells in *;
cbn [sset Z.eqb Pos.eqb v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in *.

Lemma sx32_m1 : sx32 (Z_to_bv 64 (-1)) = Z_to_bv 64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma nbd_d1 : forall (st : nb_state ptr) (b : bits_st ptr) (r : smrec) (s : nbslots) (pad : list byte)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -544) -> client_consts m1 ->
bits_rep asegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells asegs m1 (usp + -544) (slot_cells s) ->
v256 s = Z_to_bv 64 A -> v288 s = Z_to_bv 64 (ST + 2248) -> v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v304 s = Z_to_bv 64 (ST + 2240) ->
v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells asegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
smrec_at (nb_submodeID st) = Some r ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (R_D usp ST f sf gp tp (ST + 2120) 0 (segD_olp (smr_sm r) b) xra' t0' t1' t2' a0' a1' a2' (Z_to_bv 64 (ST + 2248)) a4' a5' a6' a7' t3' t4' t5' t6')
F (Z_to_bv 64 0xa00e0) fc None m2 (seg_rom asegs)
/\ munch [(usp + -672, usp + -200); (A, A + 48)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544) /\ client_consts m2
/\ bits_rep asegs m2 A D (segD_b1 (smr_sm r) b) /\ bits_ok (segD_b1 (smr_sm r) b) /\ sb_buf_size (segD_b1 (smr_sm r) b) = BSZ
/\ rw_cells asegs m2 (usp + -544) (slot_cells (sset 16 (Z_to_bv 64 ST) (sset 152 (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) s)))
/\ rw_cells asegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad))
(MS (R_D usp ST f sf gp tp (ST + 2120) (Z.shiftr (ST + 2032) 3 + SHB) ST xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_D) fc None m1 (seg_rom asegs)).
Proof using All.
intros st b r s pad xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC REP OKB SZ FR E256 E288 E296 E304 E312 CFG SAT.
nbD_setup ST0 CC. unfold PC_NBD_D in *.
set (mo := nb_submodeID st) in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). clear SMC.
pose proof (smrec_ints mo r SAT) as INTS. cbv zeta in INTS.
destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR. clear NTR.
unfold IMG_TOP in SP1. set (SP := smr_ptr r) in *. set (sm := smr_sm r) in *.
pose proof (SHF 981760 208 ltac:(lia) ltac:(lia) ltac:(lia)) as SFM.
pose proof (SHF SP 88 ltac:(lia) ltac:(lia) ltac:(lia)) as SFP.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof (aobj_munch asegs _ m m1 _ _ OBS MU0 SFR) as OBS1. pose proof (aobj_munch asegs _ m m1 _ _ NTM MU0 SFM) as NTM1.
pose proof (aobj_munch asegs _ m m1 _ _ OBR MU0 SFP) as OBR1.
slots_open s FR. subst w256 w288 w296 w304 w312.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof (munch_refl [(usp + -672, usp + -200); (A, A + 48)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
chk_hint NTM.
ato 0xa0080.
replace (Z.land (ST + 2248) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; clear - S8; Z.div_mod_to_equations; lia).
rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small mo) by lia.
ato 0xa0084. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
ato 0xa0094.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa009c.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (lib_consts_munch W m mc LC MUc FW) as LCc; pose proof (sub_ptr_read mc mo LCc ltac:(lia)) as RD;
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (smrec_facts mo r SAT))))))) mc LCc) as SMCc end.
unfold NB_SUBMODES_PTR, A_nb_mode in RD. replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia. rewrite EP in RD. fold SP in RD, SMCc.
astep. clear RD.
unfold smrec_cells in SMCc. cbv zeta in SMCc. fold sm in SMCc.
ato 0xa00c0.
assert (LBR : sm_lbr_pitch sm = 0 \/ sm_lbr_pitch sm = -1) by (clear - INTS; lia).
unfold segD_olp, segD_b1. fold sm.
destruct LBR as [LBR|LBR]; rewrite LBR; cbn [Z.eqb negb].
2: { rewrite sx32_m1. astep. rewrite ?sx32_m1. fold_lit_if. astep.
apply evt_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OKB|]. split; [exact SZ|].
split; [exact FR| exact CFG]. }
rewrite sx32_small by (unfold int31; lia). astep.
ato 0xa00cc. astep.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs W m mc _ _ OBA MUc SFRA) as OBAc;
pose proof (aobj_munch asegs W m mc _ _ OBD MUc SFRD) as OBDc;
assert (REPc : bits_rep asegs mc A D b) by (exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE)));
assert (CCc : client_consts mc) by (nbD_cc G1 G2 G3 G4)
end.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
callc (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 7 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REPc OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb) (clear REPc OBJ DAT).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 7)) |- _ => subst x end.
fold (uv b 7). fold (ub b 7) in *.
pose proof (ub_ok b 7 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^7) with 128 in VR.
ato 0xa00d4. astep. rewrite swrap32_small by lia. astep.
apply evt_done. do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact POST|]. split; [exact OK1|]. split; [congruence|].
split; [exact FR| exact CFG].
Qed.

Lemma nbd_d2 : forall (st : nb_state ptr) (b : bits_st ptr) (r : smrec) (s : nbslots) (pad : list byte) (olp : Z)
(xra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -544) -> client_consts m1 -> frm0 fc ->
bits_rep asegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells asegs m1 (usp + -544) (slot_cells s) ->
v256 s = Z_to_bv 64 A -> v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v304 s = Z_to_bv 64 (ST + 2240) ->
v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells asegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
smrec_at (nb_submodeID st) = Some r ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ms = MS (R_D usp ST f sf gp tp (ST + 2120) A olp xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 0xa0180) fc' None m2 (seg_rom asegs)
/\ munch [(usp + -672, usp + -200); (A, A + 48)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544) /\ client_consts m2 /\ frm0 fc'
/\ bits_rep asegs m2 A D (if negb (sm_forced_pitch_gain (smr_sm r) =? 0) then ub b 4 else b)
/\ bits_ok (if negb (sm_forced_pitch_gain (smr_sm r) =? 0) then ub b 4 else b)
/\ sb_buf_size (if negb (sm_forced_pitch_gain (smr_sm r) =? 0) then ub b 4 else b) = BSZ
/\ rw_cells asegs m2 (usp + -544) (slot_cells (sset 264 (Z_to_bv 64 0) s))
/\ rw_cells asegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad))
(MS (R_D usp ST f sf gp tp (ST + 2120) 0 olp xra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (ST + 2248)) a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa00e0) fc None m1 (seg_rom asegs)).
Proof using All.
intros st b r s pad olp xra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM REP OKB SZ FR E256 E296 E304 E312 CFG SAT.
nbD_setup ST0 CC.
set (mo := nb_submodeID st) in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). clear SMC.
pose proof (smrec_ints mo r SAT) as INTS. cbv zeta in INTS.
destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR. clear NTR.
unfold IMG_TOP in SP1. set (SP := smr_ptr r) in *. set (sm := smr_sm r) in *.
pose proof (SHF 981760 208 ltac:(lia) ltac:(lia) ltac:(lia)) as SFM.
pose proof (SHF SP 88 ltac:(lia) ltac:(lia) ltac:(lia)) as SFP.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof (aobj_munch asegs _ m m1 _ _ OBS MU0 SFR) as OBS1. pose proof (aobj_munch asegs _ m m1 _ _ NTM MU0 SFM) as NTM1.
pose proof (aobj_munch asegs _ m m1 _ _ OBR MU0 SFP) as OBR1.
slots_open s FR. subst w256 w296 w304 w312.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof (munch_refl [(usp + -672, usp + -200); (A, A + 48)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
chk_hint NTM.
ato 0xa010c. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small mo) by lia.
astep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
ato 0xa0120.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa0128.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (lib_consts_munch W m mc LC MUc FW) as LCc; pose proof (sub_ptr_read mc mo LCc ltac:(lia)) as RD;
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (smrec_facts mo r SAT))))))) mc LCc) as SMCc end.
unfold NB_SUBMODES_PTR, A_nb_mode in RD. replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia. rewrite EP in RD. fold SP in RD, SMCc.
astep. clear RD.
unfold smrec_cells in SMCc. cbv zeta in SMCc. fold sm in SMCc.
ato 0xa014c.
assert (FPG : sm_forced_pitch_gain sm = 0 \/ sm_forced_pitch_gain sm = 1) by (clear - INTS; lia).
destruct FPG as [FPG|FPG]; rewrite FPG; cbn [Z.eqb negb]; rewrite sx32_small by (unfold int31; lia); astep.
{ ato 0xa0180.
apply evt_done. do 19 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [nbD_cc G1 G2 G3 G4|]. split; [exact FRM|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OKB|]. split; [exact SZ|].
split; [exact FR| exact CFG]. }
ato 0xa015c. astep.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs W m mc _ _ OBA MUc SFRA) as OBAc;
pose proof (aobj_munch asegs W m mc _ _ OBD MUc SFRD) as OBDc;
assert (REPc : bits_rep asegs mc A D b) by (exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE)));
assert (CCc : client_consts mc) by (nbD_cc G1 G2 G3 G4)
end.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
callc (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REPc OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb) (clear REPc OBJ DAT).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 4)) |- _ => subst x end.
fold (uv b 4). fold (ub b 4) in *.
pose proof (ub_ok b 4 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^4) with 16 in VR.
ato 0xa0180.
apply evt_done. do 19 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|]. split; [exact FRM|].
split; [exact POST|]. split; [exact OK1|]. split; [congruence|].
split; [exact FR| exact CFG].
Qed.

Lemma nbd_d3 : forall (b : bits_st ptr) (rs : list byte) (olp : Z)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -544) -> client_consts m1 -> frm0 fc ->
bits_rep asegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells asegs m1 sf (nbd_shadow_g true false true false false false false false rs) ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ms = MS (R_D usp ST f sf gp tp (ST + 2120) A olp xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 0xa0254) fc' None m2 (seg_rom asegs)
/\ munch [(usp + -672, usp + -544); (A, A + 48); (sf, sf + 256)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544) /\ client_consts m2 /\ frm0 fc'
/\ bits_rep asegs m2 A D (ub b 5) /\ bits_ok (ub b 5) /\ sb_buf_size (ub b 5) = BSZ
/\ rw_cells asegs m2 sf (nbd_shadow_g true false true true true true false false rs))
(MS (R_D usp ST f sf gp tp (ST + 2120) A olp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa0180) fc None m1 (seg_rom asegs)).
Proof using All.
intros b rs olp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM REP OKB SZ FRS.
nbD_setup ST0 CC.
pose proof FRS as FRS0. unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS. cbn [map repeat app] in FRS. clear FRS0.
pose proof (munch_refl [(usp + -672, usp + -544); (A, A + 48); (sf, sf + 256)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
ato 0xa0188. astep.
pose proof (aobj_munch asegs _ m m1 _ _ OBA MU0 SFRA) as OBAc. pose proof (aobj_munch asegs _ m m1 _ _ OBD MU0 SFRD) as OBDc.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
assert (CCc : client_consts m1) by (nbD_cc G1 G2 G3 G4).
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 5)) |- _ => subst x end.
fold (uv b 5). fold (ub b 5) in *.
pose proof (ub_ok b 5 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^5) with 32 in VR.
destruct POST as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OK1 as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
ato 0xa019c.
destruct (stk_split asegs _ lo (usp + -672) (usp + -544) PC ltac:(lia)) as [STKa STKb]. clear PC.
astep.
call (exp_specZ (usp + -672) (usp + -544)).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: exact FRM.
match goal with H : stk asegs _ (usp + -672) (usp + -544) |- _ => pose proof (stk_merge asegs _ lo (usp + -672) (usp + -544) STKa H ltac:(lia)) as STK3; clear H STKa end.
clear FRM. match goal with H : frm0 _ |- _ => rename H into FRM3 end.
replace (ret_pc (Z_to_bv 64 655776)) with (Z_to_bv 64 655776) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => call (nbd_seg_unpoison sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rs _ _ mc FRS) end.
{ assumption. }
rename POST into FRS'.
apply evt_done. do 19 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|]. split; [exact FRM3|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OK1|]. split; [congruence|].
exact FRS'.
Qed.

Lemma seqz15 : forall u, 0 <= u < 16 -> Z.b2z ((u + -15) mod 18446744073709551616 <? 1) = (if u =? 15 then 1 else 0).
Proof.
intros u Hu. destruct (Z.eq_dec u 15) as [-> | NE]; [reflexivity|].
replace ((u + -15) mod 18446744073709551616) with (u + -15 + 18446744073709551616) by (apply Z.mod_unique with (q := -1); lia).
replace (u =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (u + -15 + 18446744073709551616 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Definition segD4_st (st : nb_state ptr) (b : bits_st ptr) : nb_state ptr :=
if nb_submodeID st =? 1 then set_nb_dtx_enabled st (if uv b 4 =? 15 then 1 else 0)
else if 1 <? nb_submodeID st then set_nb_dtx_enabled st 0 else st.

Lemma nbd_d4 : forall (st : nb_state ptr) (b : bits_st ptr) (s : nbslots) (pad pad2 : list byte) (olp : Z)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -544) -> client_consts m1 ->
bits_rep asegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells asegs m1 (usp + -544) (slot_cells s) ->
v256 s = Z_to_bv 64 A -> v288 s = Z_to_bv 64 (ST + 2248) -> v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells asegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
rw_cells asegs m1 (ST + 2948) (nb_tail_cells st pad2) ->
1 <= nb_submodeID st <= 8 ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F',
ms = MS (R_D usp ST f sf gp tp (ST + 2952) A olp xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 0xa02e0) fc None m2 (seg_rom asegs)
/\ munch [(usp + -672, usp + -200); (A, A + 48); (ST + 2952, ST + 2956)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544) /\ client_consts m2
/\ bits_rep asegs m2 A D (if nb_submodeID st =? 1 then ub b 4 else b) /\ bits_ok (if nb_submodeID st =? 1 then ub b 4 else b)
/\ sb_buf_size (if nb_submodeID st =? 1 then ub b 4 else b) = BSZ
/\ rw_cells asegs m2 (usp + -544) (slot_cells s)
/\ rw_cells asegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad)
/\ rw_cells asegs m2 (ST + 2948) (nb_tail_cells (segD4_st st b) pad2))
(MS (R_D usp ST f sf gp tp (ST + 2120) A olp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa0254) fc None m1 (seg_rom asegs)).
Proof using All.
intros st b s pad pad2 olp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC REP OKB SZ FR E256 E288 E312 CFG TAIL MO1.
nbD_setup ST0 CC.
set (mo := nb_submodeID st) in *.
pose proof (aobj_munch asegs _ m m1 _ _ OBS MU0 SFR) as OBS1.
slots_open s FR. subst w256 w288 w312.
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof (munch_refl [(usp + -672, usp + -200); (A, A + 48); (ST + 2952, ST + 2956)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
ato 0xa0270. rewrite sx32_small by (unfold int31; lia).
ato 0xa0278. astep.
unfold segD4_st. fold mo.
destruct (mo =? 1) eqn:K1; [apply Z.eqb_eq in K1 | apply Z.eqb_neq in K1]; sh_if.
-
ato 0xa0284. astep.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs W m mc _ _ OBA MUc SFRA) as OBAc;
pose proof (aobj_munch asegs W m mc _ _ OBD MUc SFRD) as OBDc;
assert (REPc : bits_rep asegs mc A D b) by (exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE)));
assert (CCc : client_consts mc) by (nbD_cc G1 G2 G3 G4)
end.
rewrite <- SZ in OBDc. assert (DLOb : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
callc (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REPc OKB ltac:(lia) OBAc OBDc ASH ltac:(lia) LOS ltac:(lia) ALO DLOb) (clear REPc OBJ DAT).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 4)) |- _ => subst x end.
fold (uv b 4). fold (ub b 4) in *.
pose proof (ub_ok b 4 OKB ltac:(lia)) as (OK1 & SZ1 & VR). change (2^4) with 16 in VR.
destruct POST as ((rj1 & Lrj1 & OBJ1) & (bs1 & DAT1 & Hbs1) & SIDE1). unfold bits_cells in OBJ1.
assert (Lbs1 : Z.of_nat (length bs1) = BSZ) by (pose proof OK1 as OK'; unfold bits_ok in OK'; rewrite Hbs1, zlength_map_unsigned in OK'; lia).
ato 0xa02a4. rewrite ?(Z.mod_small (uv b 4)) by lia. rewrite (seqz15 (uv b 4) VR).
ato 0xa02c0. rewrite sx32_small by (unfold int31; lia).
ato 0xa02c4. astep. sh_if.
apply evt_done. do 18 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact (conj (ex_intro _ rj1 (conj Lrj1 OBJ1)) (conj (ex_intro _ bs1 (conj DAT1 Hbs1)) SIDE1))|]. split; [exact OK1|]. split; [congruence|].
split; [exact FR|]. split; [exact CFG|]. destruct st; exact TAIL.
-
replace (1 <? mo) with true by (symmetry; apply Z.ltb_lt; lia).
ato 0xa02c4. astep. sh_if.
ato 0xa02e0.
apply evt_done. do 18 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [nbD_cc G1 G2 G3 G4|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OKB|]. split; [exact SZ|].
split; [exact FR|]. split; [exact CFG|]. destruct st; exact TAIL.
Qed.
Definition slots_D5 (s : nbslots) : nbslots :=
sset 96 (Z_to_bv 64 (ST + 2208)) (sset 136 (Z_to_bv 64 (ST + 2032)) (sset 192 (Z_to_bv 64 40) (sset 104 (Z_to_bv 64 (Z.shiftr (ST + 2184) 3 + SHB))
(sset 0 (Z_to_bv 64 3) (sset 56 (Z_to_bv 64 (ST + 2948)) (sset 184 (Z_to_bv 64 (ST + 2228)) (sset 40 (Z_to_bv 64 (ST + 2047)) (sset 80 (Z_to_bv 64 (f + 992))
(sset 32 (Z_to_bv 64 f) (sset 224 (Z_to_bv 64 (f + 544)) (sset 280 (Z_to_bv 64 (f + 320)) (sset 112 (Z_to_bv 64 (f + 240)) (sset 88 (Z_to_bv 64 (f + 48))
(sset 248 (Z_to_bv 64 (f + 32)) (sset 272 (Z_to_bv 64 0) (sset 120 (Z_to_bv 64 (ST + 2184)) (sset 176 (Z_to_bv 64 (f + 768)) (sset 24 (Z_to_bv 64 f) s)))))))))))))))))).

Lemma nbd_d5 : forall (s : nbslots) (olp : Z)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -544) -> client_consts m1 -> frm0 fc ->
rw_cells asegs m1 (usp + -544) (slot_cells s) ->
v48 s = Z_to_bv 64 (ST + 2120) -> v264 s = Z_to_bv 64 0 -> 0 <= olp <= 144 ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word) F' fc',
ms = MS (mkR xra' (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' (Z_to_bv 64 (ST + 2208)) (Z_to_bv 64 0)
(Z_to_bv 64 sf) (Z_to_bv 64 0) (Z_to_bv 64 (f + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6') F' (Z_to_bv 64 PC_NBD_E) fc' None m2 (seg_rom asegs)
/\ munch [(usp + -672, usp + -200)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544) /\ client_consts m2 /\ frm0 fc'
/\ rw_cells asegs m2 (usp + -544) (slot_cells (slots_D5 s)))
(MS (R_D usp ST f sf gp tp (ST + 2952) A olp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa02e0) fc None m1 (seg_rom asegs)).
Proof using All.
intros s olp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM FR E48 E264 OLP.
nbD_setup ST0 CC. unfold slots_D5, PC_NBD_E in *.
slots_open s FR. subst w48 w264.
pose proof (munch_refl [(usp + -672, usp + -200)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
ato 0xa0304. astep. join 0xa030c 0 1.
ato 0xa0338. astep. join 0xa0340 0 1.
ato 0xa0420.
apply evt_done. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [nbD_cc G1 G2 G3 G4|]. split; [assumption|]. exact FR.
Qed.
Ltac slia ::= (try unfold BITS_SIZEOF, nbD_W in * ); cbn [outside] in *; slia_ch.

Definition slots_D (s : nbslots) : nbslots :=
slots_D5 (sset 264 (Z_to_bv 64 0) (sset 16 (Z_to_bv 64 ST) (sset 152 (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) s))).

Theorem nbd_cd : forall (st : nb_state ptr) (b : bits_st ptr) (r : smrec) (s : nbslots) (pad pad2 rs : list byte)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m1 : mem),
munch nbD_W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -544) -> client_consts m1 -> frm0 fc ->
bits_rep asegs m1 A D b -> bits_ok b -> sb_buf_size b = BSZ ->
rw_cells asegs m1 (usp + -544) (slot_cells s) ->
v48 s = Z_to_bv 64 (ST + 2120) -> v256 s = Z_to_bv 64 A -> v288 s = Z_to_bv 64 (ST + 2248) -> v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) ->
v304 s = Z_to_bv 64 (ST + 2240) -> v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) ->
rw_cells asegs m1 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) ->
rw_cells asegs m1 (ST + 2948) (nb_tail_cells st pad2) ->
rw_cells asegs m1 sf (nbd_shadow_g true false true false false false false false rs) ->
smrec_at (nb_submodeID st) = Some r ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word) F' fc',
ms = MS (mkR xra' (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' (Z_to_bv 64 (ST + 2208)) (Z_to_bv 64 0)
(Z_to_bv 64 sf) (Z_to_bv 64 0) (Z_to_bv 64 (f + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 (segD_olp (smr_sm r) b))
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6') F' (Z_to_bv 64 PC_NBD_E) fc' None m2 (seg_rom asegs)
/\ munch nbD_W m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544) /\ client_consts m2 /\ frm0 fc'
/\ bits_rep asegs m2 A D (segD_bits st (smr_sm r) b) /\ bits_ok (segD_bits st (smr_sm r) b) /\ sb_buf_size (segD_bits st (smr_sm r) b) = BSZ
/\ rw_cells asegs m2 (usp + -544) (slot_cells (slots_D s))
/\ rw_cells asegs m2 (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad)
/\ rw_cells asegs m2 (ST + 2948) (nb_tail_cells (segD_st st (smr_sm r) b) pad2)
/\ rw_cells asegs m2 sf (nbd_shadow_g true false true true true true false false rs))
(MS (R_D usp ST f sf gp tp (ST + 2120) (Z.shiftr (ST + 2032) 3 + SHB) ST xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_D) fc None m1 (seg_rom asegs)).
Proof using All.
intros st b r s pad pad2 rs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 MU0 WM0 MI ST0 CC FRM REP OKB SZ FR E48 E256 E288 E296 E304 E312 CFG TAIL FRS SAT.
pose proof (smrec_facts _ r SAT) as (_ & MO1 & _).
pose proof (smrec_ints _ r SAT) as INTS. cbv zeta in INTS.
nbD_setup ST0 CC. unfold PC_NBD_D in *.
set (sm := smr_sm r) in *.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS. cbn [map repeat app] in FRS.
pose proof (munch_refl [(usp + -672, usp + -200); (A, A + 48); (ST + 2952, ST + 2956); (sf, sf + 256)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
callc (nbd_d1 st b r s pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 MU0 WM0 MI ST0 CC REP OKB SZ FR E256 E288 E296 E304 E312 CFG SAT) (clear REP FR CFG).
rename PC1 into REP1. rename PC2 into OK1. rename PC3 into SZ1. rename PC4 into FR1. rename POST into CFG1. rename PC into ST1. rename PC0 into CC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with MIc : mem_inv asegs mc |- _ =>
callc (nbd_d2 st (segD_b1 sm b) r _ pad (segD_olp sm b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc MU0 WM0 MIc ST1 CC1 FRM REP1 OK1 SZ1 FR1 E256 E296 E304 E312 CFG1 SAT) (clear REP1 FR1 CFG1) end end.
rename PC2 into REP2. rename PC3 into OK2. rename PC4 into SZ2. rename PC5 into FR2. rename POST into CFG2. rename PC into ST2. rename PC0 into CC2. rename PC1 into FRM2.
fold sm in REP2, OK2, SZ2. fold (segD_b2 sm b) in REP2, OK2, SZ2.
unfold nb_cfg_cells in CFG2.
lazymatch goal with |- evt _ _ (MS _ ?Fc _ ?fcc _ ?mc _) => match goal with MIc : mem_inv asegs mc |- _ =>
callc (nbd_d3 (segD_b2 sm b) rs (segD_olp sm b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fcc mc MU0 WM0 MIc ST2 CC2 FRM2 REP2 OK2 SZ2 FRS) (clear REP2 FRS) end end.
rename PC2 into REP3. rename PC3 into OK3. rename PC4 into SZ3. rename POST into FRS3. rename PC into ST3. rename PC0 into CC3. rename PC1 into FRM3.
fold (segD_b3 sm b) in REP3, OK3, SZ3.
unfold nbd_shadow_g, nbd_shg, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS3. cbn [map repeat app] in FRS3.
lazymatch goal with |- evt _ _ (MS _ ?Fc _ ?fcc _ ?mc _) => match goal with MIc : mem_inv asegs mc |- _ =>
callc (nbd_d4 st (segD_b3 sm b) _ pad pad2 (segD_olp sm b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fcc mc MU0 WM0 MIc ST3 CC3 REP3 OK3 SZ3 FR2 E256 E288 E312 CFG2 TAIL MO1)
(clear REP3 FR2 CFG2 TAIL) end end.
rename PC1 into REP4. rename PC2 into OK4. rename PC3 into SZ4. rename PC4 into FR4. rename PC5 into CFG4. rename POST into TAIL4. rename PC into ST4. rename PC0 into CC4.
fold (segD_bits st sm b) in REP4, OK4, SZ4.
unfold nb_cfg_cells in CFG4. unfold nb_tail_cells in TAIL4.
destruct REP4 as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = BSZ) by (pose proof OK4 as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
assert (OLP : 0 <= segD_olp sm b <= 144).
{ unfold segD_olp. destruct (negb (sm_lbr_pitch sm =? -1)); [| lia]. pose proof (ub_ok b 7 OKB ltac:(lia)) as (_ & _ & VR). change (2^7) with 128 in VR. lia. }
lazymatch goal with |- evt _ _ (MS _ ?Fc _ ?fcc _ ?mc _) => match goal with MIc : mem_inv asegs mc |- _ =>
callc (nbd_d5 _ (segD_olp sm b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fcc mc MU0 WM0 MIc ST4 CC4 FRM3 FR4 E48 eq_refl OLP) (clear FR4) end end.
rename POST into FR5.
apply evt_done. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|].
split; [exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj DAT Hbs)) SIDE))|]. split; [exact OK4|]. split; [exact SZ4|].
split; [exact FR5|]. split; [exact CFG4|]. split; [exact TAIL4| exact FRS3].
Qed.
End D.
