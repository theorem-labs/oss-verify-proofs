(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X081 X05l X07y X05m X09f X06d X069
X082 X09e X08y X091 X08x X090 X08l X094 X05k X083 X0bh X07l X0aw X07k.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition R_EL (usp ST SF FF olp sub : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 sub)
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6.

Definition slots_EL (ST OUT A FF bp sub : Z) (s : nbslots) : Prop :=
v0 s = Z_to_bv 64 (3)
/\ v8 s = Z_to_bv 64 (ST + 8)
/\ v16 s = Z_to_bv 64 (ST)
/\ v24 s = Z_to_bv 64 (FF)
/\ v32 s = Z_to_bv 64 (FF)
/\ v40 s = Z_to_bv 64 (ST + 2047)
/\ v48 s = Z_to_bv 64 (ST + 2120)
/\ v56 s = Z_to_bv 64 (ST + 2948)
/\ v64 s = Z_to_bv 64 (0xfce8)
/\ v80 s = Z_to_bv 64 (FF + 992)
/\ v88 s = Z_to_bv 64 (FF + 48)
/\ v96 s = Z_to_bv 64 (ST + 2208)
/\ v104 s = Z_to_bv 64 (Z.shiftr (ST + 2184) 3 + SHB)
/\ v112 s = Z_to_bv 64 (FF + 240)
/\ v120 s = Z_to_bv 64 (ST + 2184)
/\ v128 s = Z_to_bv 64 (ST + 12)
/\ v136 s = Z_to_bv 64 (ST + 2032)
/\ v144 s = Z_to_bv 64 (Z.shiftr (ST + 12) 3 + SHB)
/\ v152 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)
/\ v160 s = Z_to_bv 64 (FF + 160)
/\ v168 s = Z_to_bv 64 (OUT)
/\ v176 s = Z_to_bv 64 (FF + 768)
/\ v184 s = Z_to_bv 64 (ST + 2228)
/\ v192 s = Z_to_bv 64 bp
/\ v224 s = Z_to_bv 64 (FF + 544)
/\ v240 s = Z_to_bv 64 (0)
/\ v248 s = Z_to_bv 64 (FF + 32)
/\ v256 s = Z_to_bv 64 (A)
/\ v272 s = Z_to_bv 64 (160 * sub)
/\ v280 s = Z_to_bv 64 (FF + 320)
/\ v288 s = Z_to_bv 64 (ST + 2248)
/\ v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB)
/\ v304 s = Z_to_bv 64 (ST + 2240)
/\ v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB)
/\ v336 s = Z_to_bv 64 (FF).

Lemma slots_EL_of_E : forall ST OUT A FF s, slots_E ST OUT A FF s -> slots_EL ST OUT A FF 40 0 s.
Proof.
intros ST OUT A FF s H. unfold slots_E, slots_EL in *. decompose [and] H. repeat split; assumption.
Qed.

Section CutEL.
Context {ptr : Type}.

Definition at_EL (X : @nbinvA ptr) (r : smrec) (mo olp bp sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff),
ms = MS (R_EL (x_usp X) (x_st X) (x_sf X) (x_ff X) olp sub (x_gp X) (x_tp X) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6)
Fx (Z_to_bv 64 PC_NBD_E) fc None m (seg_rom asegs)
/\ frm0 fc /\ nbctx X m st b j ows sws s ff SC_E /\ slots_EL (x_st X) (x_out X) (x_A X) (x_ff X) bp sub s
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub <= 4.

Lemma at_EL_of_E : forall X r mo olp st b ms, at_E_A X r mo olp 40 0 st b ms -> at_EL X r mo olp 40 0 st b ms.
Proof.
intros X r mo olp st b ms (Fx & fc & m & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & E & FRM & CTX & SL & SM & MO & BP & OLP & SUB).
exists Fx, fc, m, xra, t0, t1, t2, a0, a1, a2, a3, a4, a5, (Z_to_bv 64 (x_st X + 2208)), t3, t4, t5, t6, j, ows, sws, s, ff.
split; [rewrite E; reflexivity|]. split; [exact FRM|]. split; [exact CTX|]. split; [exact (slots_EL_of_E _ _ _ _ _ SL)|].
split; [exact SM|]. split; [exact MO|]. split; [exact BP|]. split; [exact OLP| exact SUB].
Qed.
End CutEL.

Definition nbe_e_asan_memset : Z := 0x667b0.
Definition RA_nbe_mset1 : Z := 0xa0474.

Definition slots_Ea (isv excp sub : Z) (s : nbslots) : nbslots :=
sset 208 (Z_to_bv 64 isv) (sset 216 (Z_to_bv 64 sub) (sset 232 (Z_to_bv 64 excp) (sset 264 (Z_to_bv 64 (excp + 160 * sub)) s))).

Lemma nbe_a : forall (usp lo ST OUT A FF SF olp bp sub isv : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> slots_EL ST OUT A FF bp sub s ->
rw_cells asegs m (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))] -> rw_cells asegs m (ST + 2184) [C8 (Z_to_bv 64 isv)] ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
0 <= isv < 2^63 -> 0 <= sub < 4 ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_nbe_mset1) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 0) (Z_to_bv 64 160) a3 a4 a5 a6 (Z_to_bv 64 sub)
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (40 * sub)) t3 t4 t5 t6)
F (Z_to_bv 64 nbe_e_asan_memset) fc None m1 (seg_rom asegs)
/\ munch [(usp + -544, usp + -200)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -544)
/\ rw_cells asegs m1 (usp + -544) (slot_cells (slots_Ea isv (ST + 1368) sub s)))
(MS (R_EL usp ST SF FF olp sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6) F (Z_to_bv 64 PC_NBD_E) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL SLE EXC ISV OBS S8 SPOS SLO SOFF ISB SUB ST0 LO LOS SPH MI.
unfold R_EL, PC_NBD_E, RA_nbe_mset1, nbe_e_asan_memset, NBSTATE_SIZEOF in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SLE.
destruct SLE as (E0 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192
& E224 & E240 & E248 & E256 & E272 & E280 & E288 & E296 & E304 & E312 & E336).
subst w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w224 w240 w248 w256 w272 w280 w288 w296 w304 w312 w336.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
ato 0x667b0.
rewrite ?Z.shiftl_mul_pow2 in * by lia. rewrite (Z.mul_comm sub 40) in *. replace (40 * sub * 2 ^ 2) with (160 * sub) in * by lia.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. exact SL.
Qed.

Definition RA_nbe_ltp : Z := 0xa0638.

Definition nbe_pmin (lbr olp : Z) : Z := if lbr =? -1 then 17 else if lbr =? 0 then olp else Z.max 16 (olp - lbr) + 1.
Definition nbe_pmax (lbr olp : Z) : Z := if lbr =? -1 then 144 else if lbr =? 0 then olp else Z.min 144 (olp + lbr).
Definition slots_Eb (ST : Z) (sub : Z) (s : nbslots) : nbslots := sset 72 (Z_to_bv 64 (Z.shiftr (ST + 2208) 3 + SHB)) (sset 200 (Z_to_bv 64 (160 * sub)) s).

Lemma nbe_row_lbr : forall r, In r nb_smrecs -> sm_lbr_pitch (smr_sm r) = -1 \/ sm_lbr_pitch (smr_sm r) = 0.
Proof. intros r H. cbn [nb_smrecs In] in H. repeat (destruct H as [<- | H]; [cbn; tauto|]). destruct H. Qed.

Lemma nbe_b : forall {ptr : Type} (usp lo ST OUT A FF SF olp bp sub isv mo : Z) (r : smrec) (k : ltp_kind) (st : nb_state ptr) (pad : list byte) (lpg lp0 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells (slots_Ea isv (ST + 1368) sub s)) -> slots_EL ST OUT A FF bp sub s ->
rw_cells asegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
sm_ltp_unquant (smr_sm r) = Some k ->
rw_cells asegs m (ST + 12) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m (ST + 2204) [C4 lp0; C4 lpg] ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_consts m ->
(sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144) -> 0 <= sub < 4 ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 - 48 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) F1 (t0' t2' : word) (jk : list byte),
ms = MS (mkR (Z_to_bv 64 RA_nbe_ltp) (Z_to_bv 64 (usp + -592)) gp tp t0' (Z_to_bv 64 (ltp_entryA k)) t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (ST + 1368 + 160 * sub)) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (nbe_pmin (sm_lbr_pitch (smr_sm r)) olp))
(Z_to_bv 64 (nbe_pmax (sm_lbr_pitch (smr_sm r)) olp)) (Z_to_bv 64 (smr_ltp_par r)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48))
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 olp) (Z_to_bv 64 0)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (FF + 48)) t3 t4 t5 t6)
F1 (Z_to_bv 64 (ltp_entryA k)) fc None m1 (seg_rom asegs)
/\ munch [(usp + -592, usp + -544); (usp + -544, usp + -200)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -592)
/\ rw_cells asegs m1 (usp + -544) (slot_cells (slots_Eb ST sub (slots_Ea isv (ST + 1368) sub s)))
/\ rw_cells asegs m1 (usp + -592) (ltp_args_cells A (Z_to_bv 64 0) (40 * sub) ++ [CB 8 jk]))
(MS (mkR (Z_to_bv 64 RA_nbe_mset1) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 (160 * sub)) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (40 * sub)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL SLE CFG EMO SAT LTK CL LPG OBS S8 SPOS SLO SOFF LC NTA CC HOLP SUB ST0 LO LOS SPH U32 MI.
unfold RA_nbe_ltp, RA_nbe_mset1, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa0474)) with (Z_to_bv 64 0xa0474) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -592, usp + -544); (usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -592, usp + -544); (usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SLE.
destruct SLE as (E0 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192
& E224 & E240 & E248 & E256 & E272 & E280 & E288 & E296 & E304 & E312 & E336).
subst w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w224 w240 w248 w256 w272 w280 w288 w296 w304 w312 w336.
unfold slots_Ea, slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC).
unfold IMG_TOP in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof ST0 as (STa & STb & _).
carve_frame 48%nat ST0. rename FR into SA.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in SA; [| reflexivity]. cbn [mk_CB_cells app] in SA.
ato 0xa049c.
ato 0xa04a0. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small mo) by lia.
ato 0xa04a8. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
chk_hint NTM.
ato 0xa04b4.
rewrite EMO.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa04bc.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
unfold smrec_cells in ROW. cbv zeta in ROW. rewrite LTK in ROW.
set (SP := smr_ptr r) in *.
chk_hint OBR.
ato 0xa04cc.
rewrite ?(Z.mod_small (SP + 40)) by lia.
ato 0xa04d0.
ato 0xa04dc.
assert (LEP : 0x10000 <= ltp_entryA k < 0x630380 /\ ltp_entryA k mod 2 = 0) by (destruct k; (cbv [ltp_entryA A_forced_pitch_unquant A_pitch_unquant_3tap]; split; [lia| reflexivity])).
astep. sh_if.
ato 0xa050c. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
ato 0xa0514. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO.
chk_hint NTM.
ato 0xa0520.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa0528.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
ato 0xa0534. rewrite ?(Z.mod_small SP) by lia.
chk_hint OBR.
ato 0xa0538.
ato 0xa0540.
destruct (nbe_row_lbr r INR) as [LB | LB]; rewrite LB in *.
- destruct HOLP as [(_ & ->) | (HN & _)]; [| exfalso; exact (HN eq_refl)].
ato 0xa0584.
ato 0xa0590. rewrite ?(Z.mod_small (SP + 40)) by lia.
chk_hint OBR.
ato 0xa05a8. rewrite ?(Z.mod_small (SP + 48)) by lia.
chk_hint OBR.
ato 0xa05bc.
ato 0xa05f4.
ato 0xa0634.
astep.
replace (ret_pc (Z_to_bv 64 (ltp_entryA k))) with (Z_to_bv 64 (ltp_entryA k)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 LEP)]).
change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in SA.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. split; [exact SL| exact SA].
- destruct HOLP as [(HN & _) | (_ & HOL)]; [discriminate HN|].
ato 0xa0584.
ato 0xa0590. rewrite ?(Z.mod_small (SP + 40)) by lia.
chk_hint OBR.
ato 0xa05a8. rewrite ?(Z.mod_small (SP + 48)) by lia.
chk_hint OBR.
ato 0xa05bc.
ato 0xa05f4.
ato 0xa0634.
astep.
replace (ret_pc (Z_to_bv 64 (ltp_entryA k))) with (Z_to_bv 64 (ltp_entryA k)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 LEP)]).
change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in SA.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. split; [exact SL| exact SA].
Qed.

Definition nbe_san_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo p : Z) (n : nat) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(p, p + 4 * Z.of_nat n); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ rw_cells asegs m' p (f32 xs') /\ length xs' = n.

Ltac nsan_leaf K :=
try (match goal with
| X : rw_cells _ _ _ (C4 _ :: C4 _ :: _) |- _ => chunk_uncons X as X1
| X : rw_cells _ _ _ (C4 _ :: f32 (_ :: _)) |- _ => chunk_uncons X as X1
end);
eapply K; eassumption.
Ltac nsan_store OB K :=
ato 0xa3040; astep; chk_merge OB 4;
ato 0xa3048; nsan_leaf K.
Ltac nsan_low OB K :=
ato 0xa3028; astep; let B3 := fresh "B3" in if_cases B3;
[ nsan_store OB K
| ato 0xa3034; astep; let B4 := fresh "B4" in if_cases B4; [ nsan_store OB K | nsan_store OB K ] ].
Ltac nsan_elem OB K :=
ato 0xa3008; astep; chk_merge OB 4;
ato 0xa3014; astep; let B1 := fresh "B1" in if_cases B1;
[ nsan_low OB K
| ato 0xa301c; astep; let B2 := fresh "B2" in if_cases B2;
[ ato 0xa3048; nsan_leaf K | nsan_low OB K ] ].

Section SG.
Variables (xs : list word) (p usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation n := (length xs).
Hypothesis N1 : 1 <= Z.of_nat n < 2^31.
Hypothesis OBX : aobj asegs m p (4 * Z.of_nat n).
Hypothesis X4 : p mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : p + 4 * Z.of_nat n <= SH_LO \/ SH_HI <= p.
Hypothesis XAP : p + 4 * Z.of_nat n <= lo \/ usp <= p.
Local Notation POST := (nbe_san_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo p n m).
Local Notation W := [(p, p + 4 * Z.of_nat n); (usp + -16, usp)].

Lemma nsan_loop : forall (rest dn : list word) x (kz off : Z) (j0 : list byte) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fz : bvmap 5 word) fc m1,
n = (length dn + S (length rest))%nat -> kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m1 p (f32 dn) -> rw_cells asegs m1 (p + off) (f32 (x :: rest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 kz) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fz (Z_to_bv 64 0xa2ffc) fc None m1 (seg_rom asegs)).
Proof using N1 OBX X4 LO SPH XAP XSH.
induction rest as [|x' rest IH]; intros dn x kz off j0 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Fz fc m1 Hn Hkz Hoff FRM MU OF WM MI ST FR DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz.
-
assert (TAIL : forall (y4 y5 y6 y7 : word) (Fy : bvmap 5 word) fc' m' (w : word),
frm0 fc' -> mem_inv asegs m' -> munch W m m' -> wmono asegs m m' ->
stk asegs m' lo (usp + -16) -> rw_cells asegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m' p (f32 dn) -> rw_cells asegs m' (p + off) [C4 w] ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (Z.of_nat (S (length (@nil word))))) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) y4 y5 y6 y7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fy (Z_to_bv 64 0xa3048) fc' None m' (seg_rom asegs))).
{ clear FRM MI MU WM ST FR DONE X BX fc m1 STa STb. intros y4 y5 y6 y7 Fy fc m1 w FRM MI MU WM ST FR DONE X.
pose proof ST as (STa & STb & _).
ato 0xa3054. astep. try sh_if.
ato 0xa3080. astep. release_frame FR ST usp. astep. astep.
unfold nbe_san_post. finish.
all: try (chunk_snoc DONE X; change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE; exact DONE).
all: try (rewrite ?length_app; cbn [length] in *; lia). }
rewrite !f32_cons, ?f32_nil in X.
nsan_elem OBX TAIL.
-
assert (TAIL : forall (y4 y5 y6 y7 : word) (Fy : bvmap 5 word) fc' m' (w : word),
frm0 fc' -> mem_inv asegs m' -> munch W m m' -> wmono asegs m m' ->
stk asegs m' lo (usp + -16) -> rw_cells asegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m' p (f32 dn) -> rw_cells asegs m' (p + off) [C4 w] ->
rw_cells asegs m' (p + off + 4) (f32 (x' :: rest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (Z.of_nat (S (length (x' :: rest))))) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) y4 y5 y6 y7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fy (Z_to_bv 64 0xa3048) fc' None m' (seg_rom asegs))).
{ clear FRM MI MU WM ST FR DONE X BX fc m1 STa STb. intros y4 y5 y6 y7 Fy fc m1 w FRM MI MU WM ST FR DONE X X'.
pose proof ST as (STa & STb & _).
pose proof (rw_cells_bound _ _ _ _ X') as BX'. rewrite cells_size_f32 in BX'. cbn [length] in BX'.
ato 0xa3054. astep. cbn [length]. sh_if.
chunk_snoc DONE X. change [C4 w] with (f32 [w]) in DONE. rewrite <- f32_app in DONE.
replace (p + off + 4) with (p + (off + 4)) in * by lia.
eapply (IH (dn ++ [w]) x' _ (off + 4)); try eassumption.
all: try (rewrite ?length_app; cbn [length] in *; lia). }
rewrite f32_cons in X.
nsan_elem OBX TAIL.
Qed.

Lemma nsan_walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells asegs m p (f32 xs) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= p -> client_consts m -> mem_inv asegs m ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat n)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sanitize_values32) fc None m (seg_rom asegs)).
Proof using N1 OBX X4 LO LOS SPH XSH XAP.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc X FRM ST PTOP (G1 & G2 & _) MI.
unfold A_sanitize_values32, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. unfold IMG_TOP in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa2ffc.
replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 0)) by (rewrite Z.add_0_r; reflexivity).
replace p with (p + 0) in X at 1 by lia. rewrite Exs in X.
eapply (nsan_loop rest [] x _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs; cbn [length]; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End SG.

Definition R_BPX (usp ST SF FF olp A : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 A) t3 t4 t5 t6.
Definition nbe_bp_post (usp ST SF FF olp A lo bp p : Z) (gp tp xra t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) (m : mem) : machine_state -> Prop :=
fun ms => exists (a0 a1 a2 a3 a4 a5 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (bp' : Z),
ms = MS (R_BPX usp ST SF FF olp A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0xa0828) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ munch [(usp + -544, usp + -200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (usp + -544) (slot_cells (sset 192 (Z_to_bv 64 bp') s)) /\ (bp' = bp \/ bp' = p).

Section BP.
Variables (usp ST SF FF olp A lo bp p : Z) (gp tp xra t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) (m : mem).
Hypothesis SL : rw_cells asegs m (usp + -544) (slot_cells s).
Hypothesis E248 : v248 s = Z_to_bv 64 (FF + 32).
Hypothesis E64 : v64 s = Z_to_bv 64 0xfce8.
Hypothesis E192 : v192 s = Z_to_bv 64 bp.
Hypothesis PIT : rw_cells asegs m (FF + 32) [C4 (Z_to_bv 64 p)].
Hypothesis BPR : 17 <= bp <= 144.
Hypothesis PR : 17 <= p <= 144.
Hypothesis FLO : FF + 2048 <= lo.
Hypothesis FTOP : IMG_TOP <= FF.
Hypothesis ST0 : stk asegs m lo (usp + -544).
Hypothesis LO : lo <= usp - 544.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis MI : mem_inv asegs m.
Local Notation POST := (nbe_bp_post usp ST SF FF olp A lo bp p gp tp xra t0 t1 t2 a6 a7 t3 t4 t5 t6 s m).

Lemma nbe_rA : forall (a0 a1 a2 a3 a4 : word) F fc, frm0 fc ->
evt asegs POST (MS (R_BPX usp ST SF FF olp A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 bp) a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa0814) fc None m (seg_rom asegs)).
Proof using SL E248 E64 E192 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 F fc FRM.
unfold R_BPX. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof (munch_refl [(usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _). pose proof SL as SL'. pose proof PIT as PIT'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v248 v64 v192] in E248, E64, E192. subst w248 w64 w192.
unfold slot_cells in SL'. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL'.
ato 0xa081c. rewrite sx32_small by (unfold int31; lia).
ato 0xa0820. astep. if_cases B.
- ato 0xa0828. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [exact SL'| right; reflexivity].
- ato 0xa0828. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [exact SL'| right; reflexivity].
Qed.
Lemma sset192_id : forall (s0 : nbslots) w, v192 s0 = w -> sset 192 w s0 = s0.
Proof. intros s0 w <-. destruct s0; reflexivity. Qed.

Lemma nbe_r3 : forall (a0 a1 a2 a3 a4 : word) F fc, frm0 fc ->
evt asegs POST (MS (R_BPX usp ST SF FF olp A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 bp) a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa07a4) fc None m (seg_rom asegs)).
Proof using SL E248 E64 E192 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 F fc FRM. pose proof (nbe_rA) as RA.
unfold R_BPX in RA |- *. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof (munch_refl [(usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _). pose proof SL as SL'. pose proof PIT as PIT'.
pose proof E248 as E248'. pose proof E64 as E64'. pose proof E192 as E192'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v248 v64 v192] in E248', E64', E192'. subst w248 w64 w192.
unfold slot_cells in SL'. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL'.
ato 0xa07b4. astep. if_cases B.
- ato 0xa0828. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [| left; reflexivity].
exact SL.
- ato 0xa07d8. astep. if_cases B1; [apply RA; assumption|].
ato 0xa07f4. astep. if_cases B2; [apply RA; assumption|].
ato 0xa0810. astep. if_cases B3; [| apply RA; assumption].
ato 0xa0828. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [| left; reflexivity].
exact SL.
Qed.

Lemma nbe_r2 : forall (a0 a1 a2 a3 a4 : word) F fc, frm0 fc ->
evt asegs POST (MS (R_BPX usp ST SF FF olp A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 bp) a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa072c) fc None m (seg_rom asegs)).
Proof using SL E248 E64 E192 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 F fc FRM. pose proof (nbe_rA) as RA. pose proof (nbe_r3) as R3.
unfold R_BPX in RA, R3 |- *. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof ST0 as (STa & STb & _). pose proof SL as SL'. pose proof PIT as PIT'.
pose proof E248 as E248'. pose proof E64 as E64'. pose proof E192 as E192'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v248 v64 v192] in E248', E64', E192'. subst w248 w64 w192.
unfold slot_cells in SL'. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL'.
ato 0xa0744. astep. if_cases B; [apply R3; assumption|].
ato 0xa0768. astep. if_cases B1; [apply RA; assumption|].
ato 0xa0784. astep. if_cases B2; [apply RA; assumption|].
ato 0xa07a0. astep. if_cases B3; [apply RA; assumption| apply R3; assumption].
Qed.

Lemma nbe_r1 : forall (a0 a1 a2 a3 a4 : word) F fc, frm0 fc ->
evt asegs POST (MS (R_BPX usp ST SF FF olp A gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 bp) a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa06bc) fc None m (seg_rom asegs)).
Proof using SL E248 E64 E192 PIT BPR PR FLO FTOP ST0 LO LOS SPH MI.
intros a0 a1 a2 a3 a4 F fc FRM. pose proof (nbe_r2) as R2.
unfold R_BPX in R2 |- *. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof (munch_refl [(usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _). pose proof SL as SL'. pose proof PIT as PIT'.
pose proof E248 as E248'. pose proof E64 as E64'. pose proof E192 as E192'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v248 v64 v192] in E248', E64', E192'. subst w248 w64 w192.
unfold slot_cells in SL'. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL'.
astep. if_cases B; [apply R2; assumption|].
ato 0xa06e0. astep. if_cases B1; [apply R2; assumption|].
ato 0xa06fc. astep. if_cases B2; [apply R2; assumption|].
ato 0xa0718. astep. if_cases B3; [apply R2; assumption|].
ato 0xa0724. rewrite sx32_small by (unfold int31; lia).
ato 0xa0828. apply evt_done. do 10 eexists. split; [reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact ST0|]. split; [exact SL'| right; reflexivity].
Qed.
End BP.

Lemma nbe_san40 : forall (xs : list word) (p usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
length xs = 40%nat -> aobj asegs m p 160 -> p mod 4 = 0 -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 160 <= SH_LO \/ SH_HI <= p) -> (p + 160 <= lo \/ usp <= p) ->
rw_cells asegs m p (f32 xs) -> frm0 fc -> stk asegs m lo usp -> IMG_TOP <= p -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(p, p + 160); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ rw_cells asegs m' p (f32 xs') /\ length xs' = 40%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 40) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sanitize_values32) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros L OB P4 LO LOS SPH XSH XAP X FRM ST PTOP CC MI.
replace (Z_to_bv 64 40) with (Z_to_bv 64 (Z.of_nat (length xs))) by (rewrite L; reflexivity).
eapply evt_mono.
- eapply (nsan_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m); rewrite ?L; try eassumption; try (cbn; lia).
- intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & xs' & E & MU & WM & MI' & ST' & FRM' & X' & LX').
rewrite L in MU, LX'. do 19 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact FRM'|]. split; [exact X'| exact LX'].
Qed.

Definition RA_nbe_san : Z := 0xa0650.
Definition RA_nbe_mset2 : Z := 0xa0838.

Lemma nbe_c : forall (usp lo ST OUT A FF SF olp bp sub p : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) (jk : list byte)
(e32s pgs : list word) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v248 s = Z_to_bv 64 (FF + 32) -> v64 s = Z_to_bv 64 0xfce8 -> v192 s = Z_to_bv 64 bp ->
v256 s = Z_to_bv 64 A -> v280 s = Z_to_bv 64 (FF + 320) ->
rw_cells asegs m (usp + -592) (ltp_args_cells A (Z_to_bv 64 0) (40 * sub) ++ [CB 8 jk]) ->
rw_cells asegs m (FF + 544) (f32 e32s) -> length e32s = 40%nat -> aobj asegs m (FF + 544) 160 ->
rw_cells asegs m (FF + 48) (f32 pgs) -> length pgs = 3%nat -> rw_cells asegs m (FF + 32) [C4 (Z_to_bv 64 p)] ->
17 <= bp <= 144 -> 17 <= p <= 144 -> 0 <= sub < 4 ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk asegs m lo (usp + -592) -> lo <= usp - 544 - 48 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv asegs m -> client_consts m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) F1 fc1 (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (bp' : Z) (e32' : list word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_mset2) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (FF + 320)) (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 A) t3' t4' t5' t6')
F1 (Z_to_bv 64 nbe_e_asan_memset) fc1 None m1 (seg_rom asegs)
/\ frm0 fc1 /\ munch [(FF + 544, FF + 704); (usp + -592, usp + -200)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -544)
/\ rw_cells asegs m1 (usp + -544) (slot_cells (sset 192 (Z_to_bv 64 bp') s)) /\ (bp' = bp \/ bp' = p)
/\ rw_cells asegs m1 (FF + 544) (f32 e32') /\ length e32' = 40%nat)
(MS (mkR (Z_to_bv 64 RA_nbe_ltp) (Z_to_bv 64 (usp + -592)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 olp) (Z_to_bv 64 0)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (FF + 48)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_ltp)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E248 E64 E192 E256 E280 SA E32 LE32 OB32 PG LPG PIT BPR PR SUB F0 F64 FLO FTOP FSH ST0 LO LOS SPH U32 MI CC FRM.
unfold RA_nbe_ltp, RA_nbe_mset2, nbe_e_asan_memset in *. unfold hidp in FSH.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
replace (ret_pc (Z_to_bv 64 0xa0638)) with (Z_to_bv 64 0xa0638) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(FF + 544, FF + 704); (usp + -592, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(FF + 544, FF + 704); (usp + -592, usp + -200)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
unfold ltp_args_cells in SA. cbn [app] in SA. release_frame SA ST0 (usp + -544).
pose proof ST0 as (STa & STb & _).
astep. astep. astep. astep. astep.
astep.
call (nbe_san40 e32s (FF + 544) (usp + -544) lo).
all: try eassumption.
all: try (unfold SH_LO, SH_HI, IMG_TOP in *; lia).
rename x16 into m1. rename PC into ST1. rename PC0 into FRM1. rename PC1 into E32b. clear FRM.
pose proof SL as SL'. pose proof E248 as E248'. pose proof E64 as E64'. pose proof E192 as E192'. pose proof E256 as E256'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v248 v64 v192 v256 v280] in E248', E64', E192', E256', E280. subst w248 w64 w192 w256 w280.
unfold slot_cells in SL'. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL'.
destruct pgs as [|g0 [|g1 [|g2 [|]]]]; cbn [length] in LPG; try discriminate LPG. clear LPG.
rewrite !f32_cons, f32_nil in PG.
ato 0xa065c. astep. join 0xa0664 0 1.
ato 0xa0684. astep. join 0xa068c 0 1.
ato 0xa06a0. astep. join 0xa06a8 0 1.
ato 0xa06bc.
eapply evt_cut; [eapply (nbe_r1 usp ST SF FF olp A lo bp p); try eassumption |].
1: lia.
intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & F' & fc' & m' & bp' & -> & FRM' & MU' & WM' & MI' & ST' & SL2 & HBP).
pose proof (munch_trans _ _ _ _ MU (munch_weaken [(usp + -544, usp + -200)] [(FF + 544, FF + 704); (usp + -592, usp + -200)] m1 m' ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MU')) as MU2.
transport_after_call asegs m1 m' MU' WM'.
pose proof SL2 as SL3. unfold slot_cells in SL3. cbn in SL3. unfold R_BPX.
ato 0x667b0.
apply evt_done. do 15 eexists. exists bp'. eexists. split; [reflexivity|].
split; [exact FRM'|]. split; [exact MU2|]. split; [eassumption|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact SL2|]. split; [exact HBP|]. split; eassumption.
Qed.

Definition A_scal3 : Z := 0x23b40.
Definition A_scal1 : Z := 0x23ba0.
Definition scal3_bytes : list byte := match image_bytes asegs A_scal3 32 with Some b => b | None => [] end.
Definition scal1_bytes : list byte := match image_bytes asegs A_scal1 8 with Some b => b | None => [] end.
Lemma nbe_scal3_at : forall m, mem_inv asegs m -> exists tab : list word, length tab = 8%nat /\ ro_cells asegs m A_scal3 (f32 tab).
Proof.
intros m MI.
assert (L : length scal3_bytes = (4 * 8)%nat) by (vm_compute; reflexivity).
pose proof (ro_cells_image asegs m A_scal3 scal3_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold A_scal3; lia)
ltac:(rewrite L; unfold A_scal3; cbn; lia)) as R.
destruct (bytes_are_f32 8 scal3_bytes L) as (ws & Lws & E).
exists ws. split; [exact Lws|].
destruct R as [_ B]. split; [apply cells_wf_f32|]. rewrite E. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma nbe_scal1_at : forall m, mem_inv asegs m -> exists tab : list word, length tab = 2%nat /\ ro_cells asegs m A_scal1 (f32 tab).
Proof.
intros m MI.
assert (L : length scal1_bytes = (4 * 2)%nat) by (vm_compute; reflexivity).
pose proof (ro_cells_image asegs m A_scal1 scal1_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold A_scal1; lia)
ltac:(rewrite L; unfold A_scal1; cbn; lia)) as R.
destruct (bytes_are_f32 2 scal1_bytes L) as (ws & Lws & E).
exists ws. split; [exact Lws|].
destruct R as [_ B]. split; [apply cells_wf_f32|]. rewrite E. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma nbe_row_hsg : forall r, In r nb_smrecs -> sm_have_subframe_gain (smr_sm r) = 0 \/ sm_have_subframe_gain (smr_sm r) = 1 \/ sm_have_subframe_gain (smr_sm r) = 3.
Proof. intros r H. cbn [nb_smrecs In] in H. repeat (destruct H as [<- | H]; [cbn; tauto|]). destruct H. Qed.

Lemma nbe_rw_f32_nth : forall (m : mem) A ws i, rw_cells asegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, rw_cells asegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (rw_cells_f32_mid asegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.
Lemma nbe_ro_f32_nth : forall (m : mem) A ws i, ro_cells asegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, ro_cells asegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (ro_f32_mid asegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.

Lemma nbe_d1 : forall {ptr : Type} (usp lo ST OUT A D FF SF olp mo : Z) (r : smrec) (st : nb_state ptr) (pad : list byte) (b : bits_st ptr)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v304 s = Z_to_bv 64 (ST + 2240) ->
v288 s = Z_to_bv 64 (ST + 2248) ->
rw_cells asegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_consts m ->
bits_rep asegs m A D b -> bits_ok b -> aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) -> (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
aobj asegs m A_scal3 32 -> aobj asegs m A_scal1 8 ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 - 32 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (xra t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' (Z_to_bv 64 (ST + 2248)) a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 A) t3' t4' t5' t6')
F' (Z_to_bv 64 0xa0924) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ munch [(A, A + BITS_SIZEOF); (usp + -576, usp + -544)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ bits_rep asegs m' A D (hsg_bits (smr_sm r) b))
(MS (mkR (Z_to_bv 64 RA_nbe_mset2) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (FF + 320)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 A) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E296 E312 E304 E288 CFG EMO SAT OBS S8 SPOS SLO SOFF LC NTA CC REP OK OBA OBD ASH ALO DLO OB3 OB1 ST0 LO LOS SPH MI FRM.
unfold RA_nbe_mset2, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa0838)) with (Z_to_bv 64 0xa0838) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + BITS_SIZEOF); (usp + -576, usp + -544)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(A, A + BITS_SIZEOF); (usp + -576, usp + -544)]) by (cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v296 v312 v304 v288] in E296, E312, E304, E288. subst w296 w312 w304 w288.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
ato 0xa0864. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
ato 0xa086c. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO.
chk_hint NTM.
ato 0xa0878.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa0880.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
unfold smrec_cells in ROW. cbv zeta in ROW.
set (SP := smr_ptr r) in *.
ato 0xa088c. rewrite ?(Z.mod_small (SP + 8)) by lia.
chk_hint OBR.
ato 0xa0898.
pose proof (nbe_row_hsg r INR) as HSG.
unfold A_scal3, A_scal1 in *.
destruct HSG as [HS | [HS | HS]]; unfold hsg_bits; rewrite HS in *; cbn [Z.eqb Pos.eqb].
-
astep. ato 0xa0924. apply evt_done. do 18 eexists. split; [reflexivity|].
split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0| exact REP].
-
astep. ato 0xa08f4. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: eassumption. 1: unfold client_consts; exact (conj G1 (conj G2 (conj G3 G4))). 1: eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 1)) with (ub b 1) in *. change (fst (speex_bits_unpack_unsigned b 1)) with (uv b 1) in *.
pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 1) with 2 in V1R.
match goal with MIc : mem_inv asegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (nbe_scal1_at mc MIc) as (tab1 & LT1 & TAB1) end.
unfold A_scal1 in TAB1.
destruct (nbe_ro_f32_nth _ 146336 tab1 (uv b 1) TAB1 ltac:(lia)) as (wg & WG).
ato 0xa0904. rewrite Z.shiftl_mul_pow2 by lia. replace (146336 + uv b 1 * 2 ^ 2) with (146336 + 4 * uv b 1) by lia.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (aobj_munch asegs W m mc _ _ OB1 MUc (shfree_of_aobj asegs W m _ _ OF OB1)) as OB1c end.
ato 0xa0914. astep. chk_merge OB1 4.
replace (146336 + uv b 1 * 4) with (146336 + 4 * uv b 1) by lia.
ato 0xa0924. clear WG.
apply evt_done. do 18 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [eassumption| eassumption].
-
astep. ato 0xa08b8. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 3 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: eassumption. 1: unfold client_consts; exact (conj G1 (conj G2 (conj G3 G4))). 1: eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 3)) with (ub b 3) in *. change (fst (speex_bits_unpack_unsigned b 3)) with (uv b 3) in *.
pose proof (ub_ok b 3 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 3) with 8 in V1R.
match goal with MIc : mem_inv asegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (nbe_scal3_at mc MIc) as (tab3 & LT3 & TAB3) end.
unfold A_scal3 in TAB3.
destruct (nbe_ro_f32_nth _ 146240 tab3 (uv b 3) TAB3 ltac:(lia)) as (wg & WG).
ato 0xa08d4. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite ?(Z.mod_small (146240 + uv b 3 * 4)) by lia.
chk_hint OB3.
ato 0xa08d8. astep. chk_merge OB3 4.
replace (146240 + uv b 3 * 4) with (146240 + 4 * uv b 3) by lia.
ato 0xa0924. clear WG.
apply evt_done. do 18 eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [eassumption| eassumption].
Qed.

Definition RA_nbe_innov : Z := 0xa0a2c.

Lemma nbe_d2 : forall {ptr : Type} (usp lo ST OUT A FF SF olp mo : Z) (r : smrec) (ki : innov_kind) (st : nb_state ptr) (pad : list byte)
(gp tp xra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v304 s = Z_to_bv 64 (ST + 2240) ->
v288 s = Z_to_bv 64 (ST + 2248) -> v280 s = Z_to_bv 64 (FF + 320) -> v184 s = Z_to_bv 64 (ST + 2228) ->
rw_cells asegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
sm_innovation_unquant (smr_sm r) = Some ki ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_consts m ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (t0' t2' a7' : word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_innov) (Z_to_bv 64 (usp + -544)) gp tp t0' t1 t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (FF + 320)) (Z_to_bv 64 (smr_innov_par r)) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (ST + 2228))
(Z_to_bv 64 (innov_entryA ki)) a7'
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 A) t3 t4 t5 t6)
F (Z_to_bv 64 (innov_entryA ki)) fc None m (seg_rom asegs))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 (Z_to_bv 64 (ST + 2248)) a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 A) t3 t4 t5 t6)
F (Z_to_bv 64 0xa0924) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E296 E312 E304 E288 E280 E184 CFG EMO SAT INK OBS S8 SPOS SLO SOFF LC NTA CC ST0 LO LOS SPH MI.
unfold RA_nbe_innov, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp, SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v296 v312 v304 v288 v280 v184] in E296, E312, E304, E288, E280, E184. subst w296 w312 w304 w288 w280 w184.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
unfold smrec_cells in ROW. cbv zeta in ROW. rewrite INK in ROW.
assert (IEP : 0x10000 <= innov_entryA ki < 0x630380 /\ innov_entryA ki mod 2 = 0)
by (destruct ki; (cbv [innov_entryA A_split_cb_shape_sign_unquant A_noise_codebook_unquant]; split; [lia| reflexivity])).
set (SP := smr_ptr r) in *.

ato 0xa094c. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
ato 0xa0954. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO.
chk_hint NTM.
ato 0xa0960.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa0968.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
ato 0xa0974. rewrite ?(Z.mod_small (SP + 64)) by lia.
chk_hint OBR.
ato 0xa0988.
astep. sh_if.

ato 0xa09b8. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
ato 0xa09c0. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO.
chk_hint NTM.
ato 0xa09cc.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa09d4.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
ato 0xa09e0. rewrite ?(Z.mod_small (SP + 64)) by lia.
chk_hint OBR.
ato 0xa09f8. rewrite ?(Z.mod_small (SP + 72)) by lia.
chk_hint OBR.
ato 0xa0a28. astep.
replace (ret_pc (Z_to_bv 64 (innov_entryA ki))) with (Z_to_bv 64 (innov_entryA ki)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 IEP)]).
apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma nbe_smul40 : forall (xs : list word) (p usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
length xs = 40%nat -> aobj asegs m p 160 -> p mod 4 = 0 -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 160 <= SH_LO \/ SH_HI <= p) -> (p + 160 <= lo \/ usp <= p) ->
rw_cells asegs m p (f32 xs) -> frm0 fc -> stk asegs m lo usp -> IMG_TOP <= p -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(p, p + 160); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ rw_cells asegs m' p (f32 xs') /\ length xs' = 40%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 40) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_signal_mul) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros L OB P4 LO LOS SPH XSH XAP X FRM ST PTOP CC MI.
eapply evt_mono.
- eapply (signal_mul_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m); rewrite ?L; try eassumption; try (cbn; lia); try reflexivity.
- intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & f15 & fc' & m' & E & MU & WM & MI' & ST' & FRM' & X').
rewrite L in MU. do 18 eexists. exists (map (smul (reg_get F (Z_to_bv 5 10))) xs). split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact FRM'|]. split; [exact X'|]. rewrite length_map. exact L.
Qed.
Lemma nbe_row_dcb : forall r, In r nb_smrecs -> sm_double_codebook (smr_sm r) = 0 \/ sm_double_codebook (smr_sm r) = 1.
Proof. intros r H. cbn [nb_smrecs In] in H. repeat (destruct H as [<- | H]; [cbn; tauto|]). destruct H. Qed.

Definition RA_nbe_smul1 : Z := 0xa0a40.
Definition RA_nbe_mset3 : Z := 0xa0b08.
Definition NBE_PC_J : Z := 0xa0bfc.
Definition SC_E2 : nbscope := NBSC true false true true false.

Lemma nbe_e : forall {ptr : Type} (usp lo ST OUT A FF SF olp mo : Z) (r : smrec) (st : nb_state ptr) (pad rest : list byte) (is0 : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB) -> v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v304 s = Z_to_bv 64 (ST + 2240) ->
v288 s = Z_to_bv 64 (ST + 2248) -> v176 s = Z_to_bv 64 (FF + 768) ->
rw_cells asegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_consts m ->
rw_cells asegs m (FF + 320) (f32 is0) -> length is0 = 40%nat -> aobj asegs m (FF + 320) 160 ->
rw_cells asegs m SF (nbd_shadow SC_E rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 - 16 -> SH_HI <= lo -> usp + 16 <= 140737488355328 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (is1 : list word),
frm0 fc' /\ munch [(FF + 320, FF + 480); (SF + 96, SF + 116); (usp + -560, usp + -544)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (FF + 320) (f32 is1) /\ length is1 = 40%nat
/\ ((sm_double_codebook (smr_sm r) = 0
/\ ms = MS (mkR (Z_to_bv 64 RA_nbe_smul1) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 (Z.shiftr (981792 + mo * 8) 3 + SHB)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (981792 + mo * 8)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBE_PC_J) fc' None m' (seg_rom asegs)
/\ rw_cells asegs m' SF (nbd_shadow SC_E rest))
\/ (sm_double_codebook (smr_sm r) = 1
/\ ms = MS (mkR (Z_to_bv 64 RA_nbe_mset3) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (FF + 768)) (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 (Z.shiftr (981792 + mo * 8) 3 + SHB)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (981792 + mo * 8)) t3' t4' t5' t6')
F' (Z_to_bv 64 nbe_e_asan_memset) fc' None m' (seg_rom asegs)
/\ rw_cells asegs m' SF (nbd_shadow SC_E2 rest))))
(MS (mkR (Z_to_bv 64 RA_nbe_innov) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 A) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_innov)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E296 E312 E304 E288 E176 CFG EMO SAT OBS S8 SPOS SLO SOFF SFA LC NTA CC IS LIS OBI SH ESF SF0 SF1 F0 F64 FLO FTOP FSH ST0 LO LOS UST MI FRM.
assert (SPH : usp < 2^63) by lia.
unfold RA_nbe_innov, RA_nbe_smul1, RA_nbe_mset3, NBE_PC_J, nbe_e_asan_memset, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp in SOFF, FSH. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
replace (ret_pc (Z_to_bv 64 0xa0a2c)) with (Z_to_bv 64 0xa0a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(FF + 320, FF + 480); (SF + 96, SF + 116); (usp + -560, usp + -544)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (SHF : forall o n, 0 <= o -> o + n <= 140737488355328 -> (o + n <= FF \/ FF + 2048 <= o) ->
shfree [(FF + 320, FF + 480); (SF + 96, SF + 116); (usp + -560, usp + -544)] o n).
{ intros o n O0 O1 OFA. pose proof (FSH : _ \/ _) as FSH'. unfold SH_LO, SH_HI in FSH'.
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply (shfree_cons_sh _ _ _ _ _ FF 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite ESF, shad_shiftr; lia | rewrite ESF, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact OFA |].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply shfree_nil. }
pose proof ST0 as (STa & STb & _).
astep. astep. astep. astep. astep.
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
pose proof (SFA : _ \/ _) as SFAu. pose proof (FSH : _ \/ _) as FSHu. pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in FSHu, SF0u, SF1u.
call (nbe_smul40 is0 (FF + 320) (usp + -544) lo).
all: try eassumption.
all: try (unfold SH_LO, SH_HI, IMG_TOP in *; lia).
rename x16 into m1. rename x14 into F1. rename x15 into fc1.
lazymatch goal with H : rw_cells asegs m1 (FF + 320) (f32 ?l) |- _ => rename l into is1; rename H into IS1 end.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v296 v312 v304 v288 v176] in E296, E312, E304, E288, E176. subst w296 w312 w304 w288 w176.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP in SP1.
pose proof (SMC m1 (lib_consts_munch _ m m1 LC ltac:(eassumption) ltac:(repeat (apply Forall_cons; [cbn [fst snd]; unfold SH_LO, SH_HI in *; lia|]); apply Forall_nil))) as ROW.
destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
pose proof SFAu as SFA'. pose proof (FSH : _ \/ _) as FSH'. unfold SH_LO, SH_HI in FSH'.
lazymatch goal with MUc : munch ?W m m1 |- _ =>
pose proof (aobj_munch asegs W m m1 _ _ OBS MUc (SHF ST 2968 ltac:(lia) ltac:(lia) SFA')) as OBS1;
pose proof (aobj_munch asegs W m m1 _ _ NTM MUc (SHF 981760 208 ltac:(lia) ltac:(lia) ltac:(lia))) as NTM1;
pose proof (aobj_munch asegs W m m1 _ _ OBR MUc (SHF (smr_ptr r) 88 ltac:(lia) ltac:(lia) ltac:(lia))) as OBR1 end.
clear OBS NTM OBR. rename OBS1 into OBS. rename NTM1 into NTM. rename OBR1 into OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
unfold smrec_cells in ROW. cbv zeta in ROW.
set (SP := smr_ptr r) in *.
ato 0xa0a6c. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
ato 0xa0a74. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO.
chk_hint NTM.
ato 0xa0a80.
rewrite (shb_zero asegs m1 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa0a88.
pose proof (sub_ptr_read m1 mo (lib_consts_munch _ m m1 LC ltac:(eassumption) ltac:(repeat (apply Forall_cons; [cbn [fst snd]; unfold SH_LO, SH_HI in *; lia|]); apply Forall_nil)) ltac:(lia)) as RD.
rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
ato 0xa0a98. rewrite ?(Z.mod_small (SP + 12)) by lia.
chk_hint OBR.
ato 0xa0aa4.
pose proof (nbe_row_dcb r INR) as HDCB.
destruct HDCB as [HD | HD]; rewrite HD.
-
astep. sh_if.
apply evt_done. do 19 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. left. split; [reflexivity|]. split; [reflexivity|].
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq]. exact SH.
-
astep. sh_if.
ato 0x667b0.
apply evt_done. do 19 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [eassumption|]. right. split; [reflexivity|]. split; [reflexivity|].
unfold nbd_shadow, nbd_shadow_bytes, SC_E2, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq]. exact SH.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition RA_nbe_innov2 : Z := 0xa0b6c.

Lemma nbe_f : forall {ptr : Type} (usp lo ST OUT A FF SF olp mo : Z) (r : smrec) (ki : innov_kind)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v240 s = Z_to_bv 64 0 -> v256 s = Z_to_bv 64 A -> v176 s = Z_to_bv 64 (FF + 768) -> v184 s = Z_to_bv 64 (ST + 2228) ->
smrec_at mo = Some r -> sm_innovation_unquant (smr_sm r) = Some ki ->
lib_consts m -> nb_tabs_acc m ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (t0' t2' a7' : word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_innov2) (Z_to_bv 64 (usp + -544)) gp tp t0' t1 t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (FF + 768)) (Z_to_bv 64 (smr_innov_par r)) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (ST + 2228))
(Z_to_bv 64 (innov_entryA ki)) a7'
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 768)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (981792 + mo * 8)) t3 t4 t5 t6)
F (Z_to_bv 64 (innov_entryA ki)) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_nbe_mset3) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 (Z.shiftr (981792 + mo * 8) 3 + SHB)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (981792 + mo * 8)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset3)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E240 E256 E176 E184 SAT INK LC NTA ST0 LO LOS SPH MI.
unfold RA_nbe_mset3, RA_nbe_innov2 in *. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa0b08)) with (Z_to_bv 64 0xa0b08) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v240 v256 v176 v184] in E240, E256, E176, E184. subst w240 w256 w176 w184.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC). unfold IMG_TOP in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold smrec_cells in ROW. cbv zeta in ROW. rewrite INK in ROW.
assert (IEP : 0x10000 <= innov_entryA ki < 0x630380 /\ innov_entryA ki mod 2 = 0)
by (destruct ki; (cbv [innov_entryA A_split_cb_shape_sign_unquant A_noise_codebook_unquant]; split; [lia| reflexivity])).
set (SP := smr_ptr r) in *.
unfold A_nb_mode in NTM.
chk_hint NTM.
ato 0xa0b0c.
rewrite (shb_zero asegs m 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa0b14.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD. rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
ato 0xa0b1c. rewrite ?(Z.mod_small (SP + 64)) by lia.
chk_hint OBR.
ato 0xa0b38. rewrite ?(Z.mod_small (SP + 72)) by lia.
chk_hint OBR.
ato 0xa0b68. astep.
replace (ret_pc (Z_to_bv 64 (innov_entryA ki))) with (Z_to_bv 64 (innov_entryA ki)) by (symmetry; apply ret_pc_even; [lia | exact (proj2 IEP)]).
apply evt_done. do 3 eexists. reflexivity.
Qed.

Definition RA_nbe_smul2 : Z := 0xa0b88.

Lemma nbe_g : forall (usp lo ST FF SF olp mo : Z) (rest : list byte) (is0 i2 : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v280 s = Z_to_bv 64 (FF + 320) ->
rw_cells asegs m (FF + 320) (f32 is0) -> length is0 = 40%nat ->
rw_cells asegs m (FF + 768) (f32 i2) -> length i2 = 40%nat -> aobj asegs m (FF + 768) 160 ->
rw_cells asegs m SF (nbd_shadow SC_E2 rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
client_consts m -> stk asegs m lo (usp + -544) -> lo <= usp - 544 - 16 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (is1 i2' : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (981792 + mo * 8)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBE_PC_J) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ munch [(FF + 320, FF + 480); (FF + 768, FF + 928); (SF + 96, SF + 116); (usp + -560, usp + -544)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (FF + 320) (f32 is1) /\ length is1 = 40%nat /\ rw_cells asegs m' (FF + 768) (f32 i2') /\ length i2' = 40%nat
/\ rw_cells asegs m' SF (nbd_shadow SC_E rest))
(MS (mkR (Z_to_bv 64 RA_nbe_innov2) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 768)) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (981792 + mo * 8)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_innov2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E280 IS LIS I2C LI2 OBI2 SH ESF SF0 SF1 F0 F64 FLO FTOP FSH CC ST0 LO LOS SPH MI FRM.
unfold RA_nbe_innov2, RA_nbe_smul2, NBE_PC_J in *. unfold hidp in FSH. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
replace (ret_pc (Z_to_bv 64 0xa0b6c)) with (Z_to_bv 64 0xa0b6c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(FF + 320, FF + 480); (FF + 768, FF + 928); (SF + 96, SF + 116); (usp + -560, usp + -544)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v280] in E280. subst w280.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
unfold nbd_shadow, nbd_shadow_bytes, SC_E2, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in SF0u, SF1u.
ato 0xa0b84. astep.
call (nbe_smul40 i2 (FF + 768) (usp + -544) lo).
all: try eassumption.
all: try (unfold SH_LO, SH_HI, IMG_TOP in *; lia).
rename PC1 into I2C'. rename POST into LI2'.
lazymatch type of LI2' with length ?l = _ => do 40 (destruct l as [|? l]; [discriminate LI2'|]); destruct l; [| discriminate LI2'] end. cbn [f32 map] in I2C'.
do 40 (destruct is0 as [|? is0]; [discriminate LIS|]). destruct is0; [| discriminate LIS]. cbn [f32 map] in IS.
do 40 (ato 0xa0ba4; astep; sh_if).
ato 0xa0bfc.
apply evt_done. do 19 eexists.
lazymatch goal with H : rw_cells asegs m1 (FF + 320) ?cs |- _ => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
lazymatch goal with H : rw_cells asegs m1 (FF + 768) ?cs |- _ => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [reflexivity|]. split; [eassumption|]. split; [reflexivity|].
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq]. exact SH.
Qed.

Lemma nbe_f32_win : forall (m : mem) A (ws : list word) (i k : nat), rw_cells asegs m A (f32 ws) -> (i + k <= length ws)%nat ->
rw_cells asegs m A (f32 (firstn i ws)) /\ rw_cells asegs m (A + 4 * Z.of_nat i) (f32 (firstn k (skipn i ws)))
/\ rw_cells asegs m (A + 4 * Z.of_nat i + 4 * Z.of_nat k) (f32 (skipn (i + k) ws)).
Proof.
intros m A ws i k H Hk.
destruct (rw_cells_f32_split asegs m A ws i H) as [H1 H2]. rewrite length_firstn in H2. replace (Nat.min i (length ws)) with i in H2 by lia.
destruct (rw_cells_f32_split asegs m _ (skipn i ws) k H2) as [H3 H4]. rewrite length_firstn, length_skipn in H4. replace (Nat.min k (length ws - i)) with k in H4 by lia.
rewrite skipn_skipn in H4. replace (k + i)%nat with (i + k)%nat in H4 by lia.
split; [exact H1|]. split; [replace (A + 4 * Z.of_nat i) with (A + Z.of_nat (4 * i)) by lia; exact H3|].
replace (A + 4 * Z.of_nat i + 4 * Z.of_nat k) with (A + Z.of_nat (4 * i) + Z.of_nat (4 * k)) by lia. exact H4.
Qed.
Lemma nbe_f32_join_win : forall (m : mem) A (l1 l2 l3 : list word), rw_cells asegs m A (f32 l1) -> rw_cells asegs m (A + 4 * Z.of_nat (length l1)) (f32 l2) ->
rw_cells asegs m (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) (f32 l3) -> rw_cells asegs m A (f32 (l1 ++ l2 ++ l3)).
Proof.
intros m A l1 l2 l3 H1 H2 H3. rewrite !f32_app. apply rw_cells_join; [exact H1|]. rewrite cells_size_f32.
replace (A + Z.of_nat (4 * length l1)) with (A + 4 * Z.of_nat (length l1)) by lia.
apply rw_cells_join; [exact H2|]. rewrite cells_size_f32. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 * length l2)) with (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) by lia. exact H3.
Qed.

Ltac f32_of_cells H :=
lazymatch type of H with rw_cells _ _ _ ?cs => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.

Lemma nbe_exc_loop : forall (EXW FF lo usp : Z) (xw e32 inn : list word) (xra sp gp tp t0 t1 t2 s0 s1 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m EXW (f32 xw) -> length xw = 40%nat -> aobj asegs m EXW 160 -> EXW mod 8 = 0 -> (EXW + 160 <= SH_LO \/ SH_HI <= EXW) -> IMG_TOP <= EXW ->
rw_cells asegs m (FF + 544) (f32 e32) -> length e32 = 40%nat -> rw_cells asegs m (FF + 320) (f32 inn) -> length inn = 40%nat ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) -> (EXW + 160 <= FF \/ FF + 2048 <= EXW) ->
EXW + 160 <= lo -> lo <= usp -> usp < 2^63 -> SH_HI <= lo ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (a0' a2' a3' a4' a5' a6' a7' : word) (xw' : list word),
ms = MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa0c84) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ munch [(EXW, EXW + 160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' EXW (f32 xw') /\ length xw' = 40%nat)
(MS (mkR xra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 EXW) a1 (Z_to_bv 64 EXW) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 544)) (Z_to_bv 64 (FF + 320)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0c38) fc None m (seg_rom asegs)).
Proof.
intros until m. intros XW LXW OBX X8 XSH XTOP E32 LE32 INN LINN F0 F64 FLO FTOP FSH XFA XLO LO SPH LOS CC MI FRM.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'. pose proof XTOP as XTOP'. unfold IMG_TOP in XTOP'.
unfold SH_LO, SH_HI in XSH, FSH.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(EXW, EXW + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(EXW, EXW + 160)]) by (cbn; unfold SH_LO, SH_HI; lia).
do 40 (destruct xw as [|? xw]; [discriminate LXW|]). destruct xw; [| discriminate LXW]. cbn [f32 map] in XW.
do 40 (destruct e32 as [|? e32]; [discriminate LE32|]). destruct e32; [| discriminate LE32]. cbn [f32 map] in E32.
do 40 (destruct inn as [|? inn]; [discriminate LINN|]). destruct inn; [| discriminate LINN]. cbn [f32 map] in INN.
do 40 (ato 0xa0c6c; astep; try sh_if).
ato 0xa0c84.
apply evt_done. do 10 eexists. f32_of_cells XW.
split; [reflexivity|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact XW| reflexivity].
Qed.

Lemma nbe_h1 : forall (usp lo ST FF SF olp sub isv EXW : Z) (xw e32 inn : list word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v208 s = Z_to_bv 64 isv -> v200 s = Z_to_bv 64 (160 * sub) -> v272 s = Z_to_bv 64 (160 * sub) -> v232 s = Z_to_bv 64 (ST + 1368) ->
v224 s = Z_to_bv 64 (FF + 544) -> v280 s = Z_to_bv 64 (FF + 320) -> v136 s = Z_to_bv 64 (ST + 2032) ->
EXW = ST + 1368 + 160 * sub -> (isv = 0 \/ 0 < isv /\ isv + 160 * sub < 2^63) -> 0 <= sub < 4 ->
rw_cells asegs m EXW (f32 xw) -> length xw = 40%nat -> aobj asegs m EXW 160 -> ST mod 8 = 0 -> (EXW + 160 <= SH_LO \/ SH_HI <= EXW) -> IMG_TOP <= EXW ->
rw_cells asegs m (FF + 544) (f32 e32) -> length e32 = 40%nat -> rw_cells asegs m (FF + 320) (f32 inn) -> length inn = 40%nat ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) -> (EXW + 160 <= FF \/ FF + 2048 <= EXW) ->
EXW + 160 <= lo -> stk asegs m lo (usp + -544) -> lo <= usp - 544 -> usp < 2^63 -> SH_HI <= lo ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (a0' a2' a3' a4' a5' a6' a7' : word) (xw' : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0'
(Z_to_bv 64 (if isv =? 0 then 0 else isv + 160 * sub)) a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F' (Z_to_bv 64 0xa0c84) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ munch [(EXW, EXW + 160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' EXW (f32 xw') /\ length xw' = 40%nat)
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_J) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E208 E200 E272 E232 E224 E280 E136 EEX HIS SUB XW LXW OBX S8 XSH XTOP E32 LE32 INN LINN F0 F64 FLO FTOP FSH XFA XLO ST0 LO SPH LOS CC MI FRM.
unfold NBE_PC_J. pose proof LOS as LOS'. unfold SH_HI in LOS'.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v208 v200 v272 v232 v224 v280 v136] in E208, E200, E272, E232, E224, E280, E136. subst w208 w200 w272 w232 w224 w280 w136.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
ato 0xa0c38.
replace (Z.land ((Z.b2z (isv <? 1) + -1) mod 18446744073709551616) (isv + 160 * sub)) with (if isv =? 0 then 0 else isv + 160 * sub).
2: { destruct HIS as [-> | (H1 & H2)].
- cbn. reflexivity.
- replace (isv <? 1) with false by (symmetry; apply Z.ltb_ge; lia). replace (isv =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
rewrite Z.mod_small by lia. reflexivity. }
subst EXW.
eapply evt_cut; [eapply (nbe_exc_loop (ST + 1368 + 160 * sub) FF lo (usp + -544) xw e32 inn); try eassumption |].
all: try (unfold SH_LO, SH_HI, IMG_TOP in *; lia).
intros ms' (m' & F' & fc' & a0' & a2' & a3' & a4' & a5' & a6' & a7' & xw' & -> & FRM' & MU' & WM' & MI' & XW' & LXW').
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact FRM'|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact XW'| exact LXW'].
Qed.

Lemma nbe_isv_loop : forall (ISW FF lo usp : Z) (yw inn : list word) (xra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m ISW (f32 yw) -> length yw = 40%nat -> aobj asegs m ISW 160 -> ISW mod 4 = 0 -> (ISW + 160 <= SH_LO \/ SH_HI <= ISW) -> IMG_TOP <= ISW ->
rw_cells asegs m (FF + 320) (f32 inn) -> length inn = 40%nat ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) -> (ISW + 160 <= FF \/ FF + 2048 <= ISW) ->
ISW + 160 <= lo -> lo <= usp -> usp < 2^63 -> SH_HI <= lo ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word) (yw' : list word),
ms = MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa0cd8) fc None m' (seg_rom asegs)
/\ munch [(ISW, ISW + 160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' ISW (f32 yw') /\ length yw' = 40%nat)
(MS (mkR xra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ISW) (Z_to_bv 64 ISW) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 320)) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0c98) fc None m (seg_rom asegs)).
Proof.
intros until m. intros YW LYW OBY Y4 YSH YTOP INN LINN F0 F64 FLO FTOP FSH YFA YLO LO SPH LOS CC MI FRM.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'. pose proof YTOP as YTOP'. unfold IMG_TOP in YTOP'.
unfold SH_LO, SH_HI in YSH, FSH.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(ISW, ISW + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(ISW, ISW + 160)]) by (cbn; unfold SH_LO, SH_HI; lia).
do 40 (destruct yw as [|? yw]; [discriminate LYW|]). destruct yw; [| discriminate LYW]. cbn [f32 map] in YW.
do 40 (destruct inn as [|? inn]; [discriminate LINN|]). destruct inn; [| discriminate LINN]. cbn [f32 map] in INN.
do 40 (ato 0xa0ca8; astep; try chk_merge OBY 4; ato 0xa0cc0; astep; try sh_if).
ato 0xa0cd8.
apply evt_done. do 8 eexists. f32_of_cells YW.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact YW| reflexivity].
Qed.

Definition RA_nbe_mset4 : Z := 0xa0d08.
Definition NBE_PC_EXIT : Z := 0xa1010.
Definition NBE_PC_H3 : Z := 0xa0cd8.

Lemma nbe_h3 : forall {ptr : Type} (usp lo ST FF SF olp sub mo : Z) (st : nb_state ptr) (pad : list byte)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB) -> v288 s = Z_to_bv 64 (ST + 2248) -> v240 s = Z_to_bv 64 0 -> v216 s = Z_to_bv 64 sub ->
v272 s = Z_to_bv 64 (160 * sub) ->
rw_cells asegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> 0 <= mo <= 8 -> 0 <= sub < 4 ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> usp < 2^63 -> SH_HI <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m' : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch [(usp + -544, usp + -200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ ((mo <> 1 /\ rw_cells asegs m' (usp + -544) (slot_cells (sset 272 (Z_to_bv 64 (160 * (sub + 1))) s))
/\ ((sub < 3 /\ ms = MS (R_EL usp ST SF FF olp (sub + 1) gp tp xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6')
F (Z_to_bv 64 PC_NBD_E) fc None m' (seg_rom asegs))
\/ (sub = 3 /\ ms = MS (mkR xra' (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40)
(Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6')
F (Z_to_bv 64 NBE_PC_EXIT) fc None m' (seg_rom asegs))))
\/ (mo = 1 /\ rw_cells asegs m' (usp + -544) (slot_cells s)
/\ ms = MS (mkR (Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
a6 (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6 a7'
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40)
(Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6')
F (Z_to_bv 64 nbe_e_asan_memset) fc None m' (seg_rom asegs))))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_H3) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E312 E288 E240 E216 E272 CFG EMO MO SUB OBS S8 SPOS SLO SOFF ST0 LO SPH LOS MI.
unfold RA_nbe_mset4, NBE_PC_EXIT, NBE_PC_H3, nbe_e_asan_memset, PC_NBD_E, R_EL, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v312 v288 v240 v216 v272] in E312, E288, E240, E216, E272. subst w312 w288 w240 w216 w272.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
subst mo.
ato 0xa0cf0. rewrite sx32_small by (unfold int31; lia).
ato 0xa0cf4. astep.
destruct (Z.eq_dec (nb_submodeID st) 1) as [M1 | M1].
- rewrite M1 in *. sh_if.
ato 0x667b0.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. right.
split; [reflexivity|]. split; [exact SL| reflexivity].
- sh_if.
ato 0xa0f30. rewrite ?Z.add_0_r.
replace (160 * sub + 160) with (160 * (sub + 1)) in * by lia.
astep.
destruct (Z.eq_dec sub 3) as [S3 | S3].
+ subst sub. sh_if. astep.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. left.
split; [exact M1|]. split; [exact SL|]. right. split; [reflexivity| reflexivity].
+ sh_if.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. left.
split; [exact M1|]. split; [exact SL|]. left. split; [lia| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbe_h2 : forall (usp lo ST FF SF olp sub isv EXW : Z) (yw inn : list word)
(gp tp xra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v264 s = Z_to_bv 64 EXW -> v280 s = Z_to_bv 64 (FF + 320) ->
(isv = 0 \/ 0 < isv /\ isv + 160 * sub < 2^63) -> 0 <= sub < 4 ->
(isv <> 0 -> rw_cells asegs m (isv + 160 * sub) (f32 yw) /\ length yw = 40%nat /\ aobj asegs m (isv + 160 * sub) 160 /\ (isv + 160 * sub) mod 4 = 0
/\ (isv + 160 * sub + 160 <= SH_LO \/ SH_HI <= isv + 160 * sub) /\ IMG_TOP <= isv + 160 * sub
/\ (isv + 160 * sub + 160 <= FF \/ FF + 2048 <= isv + 160 * sub) /\ isv + 160 * sub + 160 <= lo) ->
rw_cells asegs m (FF + 320) (f32 inn) -> length inn = 40%nat ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> usp < 2^63 -> SH_HI <= lo ->
client_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' (Z_to_bv 64 EXW) a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F' (Z_to_bv 64 NBE_PC_H3) fc None m' (seg_rom asegs)
/\ munch [(isv + 160 * sub, isv + 160 * sub + 160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ (isv <> 0 -> exists yw', rw_cells asegs m' (isv + 160 * sub) (f32 yw') /\ length yw' = 40%nat))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0
(Z_to_bv 64 (if isv =? 0 then 0 else isv + 160 * sub)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) s3 (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa0c84) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E264 E280 HIS SUB HYW INN LINN F0 F64 FLO FTOP FSH ST0 LO SPH LOS CC MI FRM.
unfold NBE_PC_H3 in *. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof (munch_refl [(isv + 160 * sub, isv + 160 * sub + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v264 v280] in E264, E280. subst w264 w280.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
ato 0xa0c88. astep.
destruct HIS as [HI0 | (HI1 & HI2)].
- subst isv. cbn [Z.eqb] in *. sh_if.
apply evt_done. do 8 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
intros HN. exfalso. exact (HN eq_refl).
- replace (isv =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). sh_if.
destruct (HYW ltac:(lia)) as (YW & LYW & OBY & Y4 & YSH & YTOP & YFA & YLO).
ato 0xa0c98.
eapply evt_cut; [eapply (nbe_isv_loop (isv + 160 * sub) FF lo (usp + -544) yw inn); try eassumption |].
all: try (unfold SH_LO, SH_HI, IMG_TOP in *; lia).
intros ms' (m' & F' & a0' & a1' & a2' & a3' & a4' & a5' & yw' & -> & MU' & WM' & MI' & YW' & LYW').
apply evt_done. do 8 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
intros _. exists yw'. split; [exact YW'| exact LYW'].
Qed.

Lemma nbe_f32_split3 : forall (m : mem) A (ws : list word) i, rw_cells asegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) ->
rw_cells asegs m A (f32 (firstn (Z.to_nat i) ws)) /\ rw_cells asegs m (A + 4 * i) [C4 (nth (Z.to_nat i) ws (Z_to_bv 64 0))]
/\ rw_cells asegs m (A + 4 * i + 4) (f32 (skipn (S (Z.to_nat i)) ws)).
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
rw_cells asegs m A (f32 l1) -> rw_cells asegs m (A + 4 * Z.of_nat (length l1)) [C4 x] -> rw_cells asegs m (A + 4 * Z.of_nat (length l1) + 4) (f32 l2) ->
rw_cells asegs m A (f32 (l1 ++ x :: l2)).
Proof.
intros m A l1 l2 x H1 H2 H3. rewrite f32_app, f32_cons. apply rw_cells_join; [exact H1|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length l1)) with (4 * Z.of_nat (length l1)) by lia.
change (C4 x :: f32 l2) with ([C4 x] ++ f32 l2). apply rw_cells_join; [exact H2|]. cbn [cells_size csize]. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 + 0)) with (A + 4 * Z.of_nat (length l1) + 4) by lia. exact H3.
Qed.

Lemma nbe_win_len : forall (ws : list word) i (x : word), 0 <= i < Z.of_nat (length ws) ->
length (firstn (Z.to_nat i) ws ++ x :: skipn (S (Z.to_nat i)) ws) = length ws.
Proof. intros ws i x Hi. rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. lia. Qed.

Definition NBE_PC_VOC : Z := 0xa0d90.

Lemma nbe_i1 : forall {ptr : Type} (usp lo ST FF SF olp sub EXW : Z) (st : nb_state ptr) (pad : list byte) (xw : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v56 s = Z_to_bv 64 (ST + 2948) -> v264 s = Z_to_bv 64 EXW -> v272 s = Z_to_bv 64 (160 * sub) -> v232 s = Z_to_bv 64 (ST + 1368) -> v280 s = Z_to_bv 64 (FF + 320) ->
EXW = ST + 1368 + 160 * sub -> 0 <= sub < 4 ->
rw_cells asegs m (ST + 2948) (nb_tail_cells st pad) -> 0 <= nb_voc_offset st <= 143 -> 17 <= olp <= 144 ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
rw_cells asegs m EXW (f32 xw) -> length xw = 40%nat -> aobj asegs m EXW 160 ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> usp < 2^63 -> SH_HI <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m' : mem) (t0' t1' t2' a4' a6' a7' t3' t4' t5' t6' : word) (vfin : Z) (xw' : list word),
ms = MS (mkR (Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 EXW) (Z_to_bv 64 EXW) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 320)) a4' (Z_to_bv 64 (ST + 2948)) a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40)
(Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6')
F (Z_to_bv 64 NBE_PC_VOC) fc None m' (seg_rom asegs)
/\ munch [(EXW, EXW + 160); (ST + 2948, ST + 2952)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ voc_loop VOC_FUEL (nb_voc_offset st) olp = Some vfin
/\ rw_cells asegs m' (ST + 2948) (nb_tail_cells (set_nb_voc_offset st (vfin - NB_SUBFRAME_SIZE)) pad)
/\ rw_cells asegs m' EXW (f32 xw') /\ length xw' = 40%nat)
(MS (mkR (Z_to_bv 64 RA_nbe_mset4) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40)
(Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbe_mset4)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E56 E264 E272 E232 E280 EEX SUB TL VR OLP OBS S8 SPOS SLO SOFF XW LXW OBX ST0 LO SPH LOS MI.
subst EXW.
unfold RA_nbe_mset4, NBE_PC_VOC, NBSTATE_SIZEOF, nb_tail_cells in *. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa0d08)) with (Z_to_bv 64 0xa0d08) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(ST + 1368 + 160 * sub, ST + 1368 + 160 * sub + 160); (ST + 2948, ST + 2952)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(ST + 1368 + 160 * sub, ST + 1368 + 160 * sub + 160); (ST + 2948, ST + 2952)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v56 v264 v272 v232 v280] in E56, E264, E272, E232, E280. subst w56 w264 w272 w232 w280.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
assert (X8 : (ST + 1368 + 160 * sub) mod 8 = 0) by (clear - S8; Z.div_mod_to_equations; lia).
set (v0 := nb_voc_offset st) in *.
ato 0xa0d20. rewrite sx32_small by (unfold int31; lia).
ato 0xa0d24. astep.
destruct (Z_lt_ge_dec v0 40) as [L0 | L0].
2: { sh_if.
ato 0xa0d90.
apply evt_done. do 11 eexists. exists v0. eexists. split; [reflexivity|].
split; [exact MU|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite voc_loop_step; unfold NB_SUBFRAME_SIZE; replace (v0 <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; exact TL|]. split; [exact XW| exact LXW]. }
sh_if.
ato 0xa0d2c. astep. sh_if.
ato 0xa0d38. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite ?Z.mod_small by lia.
replace (ST + 1368 + 160 * sub + v0 * 4) with (ST + 1368 + 160 * sub + 4 * v0) by lia.
destruct (nbe_f32_split3 _ (ST + 1368 + 160 * sub) xw v0 XW ltac:(lia)) as (W1 & W2 & W3). clear XW.
remember (firstn (Z.to_nat v0) xw) as l1 eqn:EL1. remember (skipn (S (Z.to_nat v0)) xw) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = v0) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 39 - v0) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
ato 0xa0d44. astep. chk_merge OBX 4.
astep.
assert (XW : rw_cells asegs m0 (ST + 1368 + 160 * sub) (f32 (l1 ++ reg_get F 24 :: l3))).
{ apply nbe_f32_join3; [exact W1| rewrite LL1; exact W2| rewrite LL1; exact W3]. }
assert (LXW1 : length (l1 ++ reg_get F 24 :: l3) = 40%nat) by (rewrite length_app; cbn [length]; lia).
clear W1 W2 W3. clear LXW. set (xw1 := l1 ++ reg_get F 24 :: l3) in *. clearbody xw1. clear l1 l3 LL1 LL3.
ato 0xa0d50. rewrite ?swrap32_small by lia. astep.
destruct (Z_lt_ge_dec (v0 + olp) 40) as [L1 | L1].
2: { sh_if.
ato 0xa0d90.
apply evt_done. do 11 eexists. exists (v0 + olp). eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite !voc_loop_step; unfold NB_SUBFRAME_SIZE;
replace (v0 <? 40) with true by (symmetry; apply Z.ltb_lt; lia); replace (v0 + olp <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; eassumption|]. split; [eassumption| exact LXW1]. }
sh_if.
ato 0xa0d2c. astep. sh_if.
ato 0xa0d38. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite ?Z.mod_small by lia.
replace (ST + 1368 + 160 * sub + (v0 + olp) * 4) with (ST + 1368 + 160 * sub + 4 * (v0 + olp)) by lia.
destruct (nbe_f32_split3 _ (ST + 1368 + 160 * sub) xw1 (v0 + olp) XW ltac:(lia)) as (W1 & W2 & W3). clear XW.
remember (firstn (Z.to_nat (v0 + olp)) xw1) as l1 eqn:EL1. remember (skipn (S (Z.to_nat (v0 + olp))) xw1) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = v0 + olp) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 39 - (v0 + olp)) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
ato 0xa0d44. astep. chk_merge OBX 4.
astep.
assert (XW : rw_cells asegs m1 (ST + 1368 + 160 * sub) (f32 (l1 ++ reg_get F 24 :: l3))).
{ apply nbe_f32_join3; [exact W1| rewrite LL1; exact W2| rewrite LL1; exact W3]. }
assert (LXW2 : length (l1 ++ reg_get F 24 :: l3) = 40%nat) by (rewrite length_app; cbn [length]; lia).
clear W1 W2 W3. clear LXW1. set (xw2 := l1 ++ reg_get F 24 :: l3) in *. clearbody xw2. clear l1 l3 LL1 LL3.
ato 0xa0d50. rewrite ?swrap32_small by lia. astep.
destruct (Z_lt_ge_dec (v0 + olp + olp) 40) as [L2 | L2].
2: { sh_if.
ato 0xa0d90.
apply evt_done. do 11 eexists. exists (v0 + olp + olp). eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite !voc_loop_step; unfold NB_SUBFRAME_SIZE;
replace (v0 <? 40) with true by (symmetry; apply Z.ltb_lt; lia); replace (v0 + olp <? 40) with true by (symmetry; apply Z.ltb_lt; lia);
replace (v0 + olp + olp <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; eassumption|]. split; [eassumption| exact LXW2]. }
sh_if.
ato 0xa0d2c. astep. sh_if.
ato 0xa0d38. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite ?Z.mod_small by lia.
replace (ST + 1368 + 160 * sub + (v0 + olp + olp) * 4) with (ST + 1368 + 160 * sub + 4 * (v0 + olp + olp)) by lia.
destruct (nbe_f32_split3 _ (ST + 1368 + 160 * sub) xw2 (v0 + olp + olp) XW ltac:(lia)) as (W1 & W2 & W3). clear XW.
remember (firstn (Z.to_nat (v0 + olp + olp)) xw2) as l1 eqn:EL1. remember (skipn (S (Z.to_nat (v0 + olp + olp))) xw2) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = v0 + olp + olp) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 39 - (v0 + olp + olp)) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
ato 0xa0d44. astep. chk_merge OBX 4.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (XW : rw_cells asegs mc (ST + 1368 + 160 * sub) (f32 (l1 ++ reg_get F 24 :: l3)))
by (apply nbe_f32_join3; [exact W1| rewrite LL1; exact W2| rewrite LL1; exact W3]) end.
assert (LXW3 : length (l1 ++ reg_get F 24 :: l3) = 40%nat) by (rewrite length_app; cbn [length]; lia).
clear W1 W2 W3. clear LXW2. set (xw3 := l1 ++ reg_get F 24 :: l3) in *. clearbody xw3. clear l1 l3 LL1 LL3.
ato 0xa0d50. rewrite ?swrap32_small by lia. astep. sh_if.
ato 0xa0d90.
apply evt_done. do 11 eexists. exists (v0 + olp + olp + olp). eexists. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [unfold VOC_FUEL; rewrite !voc_loop_step; unfold NB_SUBFRAME_SIZE;
replace (v0 <? 40) with true by (symmetry; apply Z.ltb_lt; lia); replace (v0 + olp <? 40) with true by (symmetry; apply Z.ltb_lt; lia);
replace (v0 + olp + olp <? 40) with true by (symmetry; apply Z.ltb_lt; lia);
replace (v0 + olp + olp + olp <? 40) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
split; [unfold nb_tail_cells; eassumption|]. split; [eassumption| exact LXW3].
Qed.

Section VOC.
Variables (ST EXW FF lo usp : Z) (inn : list word) (m : mem).
Variables xra sp gp tp t1 t2 s0 s1 s2 s3 s4 s7 s8 s11 t3 t4 t5 t6 : word.
Hypothesis OBX : aobj asegs m EXW 160.
Hypothesis X8 : EXW mod 8 = 0.
Hypothesis XSH : EXW + 160 <= SH_LO \/ SH_HI <= EXW.
Hypothesis XTOP : IMG_TOP <= EXW.
Hypothesis OBS : aobj asegs m ST 2968.
Hypothesis S8 : ST mod 8 = 0.
Hypothesis SPOS : 0 < ST.
Hypothesis SSH : ST + 2968 <= SH_LO \/ SH_HI <= ST.
Hypothesis SX : ST <= EXW.
Hypothesis XS : EXW + 160 <= ST + 2032.
Hypothesis LINN : length inn = 40%nat.
Hypothesis FTOP : IMG_TOP <= FF.
Hypothesis FSH : FF + 2048 <= SH_LO \/ SH_HI <= FF.
Hypothesis XFA : EXW + 160 <= FF \/ FF + 2048 <= EXW.
Hypothesis SFA : ST + 2968 <= FF \/ FF + 2048 <= ST.
Hypothesis SLO : ST + 2968 <= lo.
Hypothesis FLO : FF + 2048 <= lo.
Hypothesis LO : lo <= usp.
Hypothesis SPH : usp < 2^63.
Hypothesis LOS : SH_HI <= lo.
Definition RVOC (off kz : Z) (t0 a4 a5 a6 a7 : word) : bvmap 5 word :=
mkR xra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (EXW + off)) (Z_to_bv 64 (EXW + off)) (Z_to_bv 64 kz) (Z_to_bv 64 (FF + 320 + off)) a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) s7 s8 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) s11 t3 t4 t5 t6.
Definition voc_post : machine_state -> Prop :=
fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (xw' vs' : list word),
ms = MS (mkR xra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) s7 s8
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa0f18) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ munch [(EXW, EXW + 160); (ST + 2936, ST + 2948)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' EXW (f32 xw') /\ length xw' = 40%nat /\ rw_cells asegs m' (ST + 2936) (f32 vs') /\ length vs' = 3%nat.
Local Notation W := [(EXW, EXW + 160); (ST + 2936, ST + 2948)].

Lemma voc_loop_walk : forall (rest dn : list word) (x v1 v2 v3 : word) (kz off : Z) (t0 a4 a5 a6 a7 : word) (F : bvmap 5 word) fc m1,
(length dn + S (length rest))%nat = 40%nat -> kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 -> client_consts m1 ->
rw_cells asegs m1 EXW (f32 dn) -> rw_cells asegs m1 (EXW + off) (f32 (x :: rest)) ->
rw_cells asegs m1 (ST + 2936) [C4 v1; C4 v2; C4 v3] -> rw_cells asegs m1 (FF + 320) (f32 inn) ->
evt asegs voc_post (MS (RVOC off kz t0 a4 a5 a6 a7) F (Z_to_bv 64 0xa0d90) fc None m1 (seg_rom asegs)).
Proof using OBX X8 XSH XTOP OBS S8 SPOS SSH SX XS LINN FTOP FSH XFA SFA SLO FLO LO SPH LOS.
induction rest as [|x' rest IH]; intros dn x v1 v2 v3 kz off t0 a4 a5 a6 a7 F fc m1 HL Hkz Hoff FRM MU OF WM MI CC DONE X VS INN;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *; subst kz;
pose proof LOS as LOS'; unfold SH_HI in LOS'; pose proof FTOP as FTOP'; unfold IMG_TOP in FTOP'; pose proof XTOP as XTOP';
unfold IMG_TOP in XTOP'; pose proof XSH as XSH'; pose proof FSH as FSH'; pose proof SSH as SSH'; unfold SH_LO, SH_HI in XSH', FSH', SSH';
pose proof CC as (G1 & G2 & G3 & G4);
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *;
destruct (nbe_rw_f32_nth m1 (FF + 320) inn (Z.of_nat (length dn)) INN ltac:(lia)) as (wi & WI);
unfold RVOC; rewrite !f32_cons in X; cbn [length] in *.
-
subst off. rewrite ?f32_nil in X.
assert (XB : EXW + 4 * Z.of_nat (length dn) + 4 <= ST + 2032) by lia. assert (XB0 : EXW <= EXW + 4 * Z.of_nat (length dn)) by lia.
ato 0xa0d9c. astep. chk_merge OBX 4.
ato 0xa0db0. astep. try chk_merge OBS 4.
ato 0xa0dc8. astep. try chk_merge OBS 4.
ato 0xa0dd4. astep. chk_merge OBX 4.
ato 0xa0e08. astep. try chk_merge OBS 4.
ato 0xa0e18. astep. try chk_merge OBS 4.
ato 0xa0e2c. astep. try chk_merge OBS 4.
ato 0xa0e3c. astep. try chk_merge OBS 4.
ato 0xa0e60. astep. chk_merge OBX 4.
ato 0xa0e80. astep. try sh_if.
astep.
unfold voc_post. apply evt_done. do 12 eexists.
lazymatch goal with H : rw_cells asegs ?mc (EXW + 4 * Z.of_nat (length dn)) [C4 ?w] |- _ => exists (dn ++ [w]) end.
lazymatch goal with H : rw_cells asegs ?mc (ST + 2936) [C4 ?w1; C4 ?w2; C4 ?w3] |- _ => exists [w1; w2; w3] end.
split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [chunk_snoc DONE X; change [C4 ?w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE; exact DONE|].
split; [rewrite length_app; cbn [length]; lia|]. split; [eassumption| reflexivity].
-
subst off. chunk_uncons X as X1.
assert (XB : EXW + 4 * Z.of_nat (length dn) + 4 <= ST + 2032) by lia. assert (XB0 : EXW <= EXW + 4 * Z.of_nat (length dn)) by lia.
assert (XB1 : EXW + 4 * Z.of_nat (length dn) + 4 + 4 * Z.of_nat (S (length rest)) <= EXW + 160) by lia.
ato 0xa0d9c. astep. chk_merge OBX 4.
ato 0xa0db0. astep. try chk_merge OBS 4.
ato 0xa0dc8. astep. try chk_merge OBS 4.
ato 0xa0dd4. astep. chk_merge OBX 4.
ato 0xa0e04.
rewrite <- f32_cons in X.
ato 0xa0e08. astep. try chk_merge OBS 4.
ato 0xa0e18. astep. try chk_merge OBS 4.
ato 0xa0e2c. astep. try chk_merge OBS 4.
ato 0xa0e3c. astep. try chk_merge OBS 4.
ato 0xa0e60. astep. chk_merge OBX 4.
ato 0xa0e80. astep. cbn [length]. sh_if.
lazymatch goal with H : rw_cells asegs ?mc (EXW + 4 * Z.of_nat (length dn)) [C4 ?w] |- _ =>
chunk_snoc DONE H; change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE end.
lazymatch goal with H : rw_cells asegs ?mc (ST + 2936) [C4 ?w1; C4 ?w2; C4 ?w3] |- _ => rename H into VS' end.
replace (EXW + 4 * Z.of_nat (length dn) + 4) with (EXW + (4 * Z.of_nat (length dn) + 4)) in * by lia.
replace (FF + 320 + 4 * Z.of_nat (length dn) + 4) with (FF + 320 + (4 * Z.of_nat (length dn) + 4)) by lia.
eapply (IH (dn ++ _) x' _ _ _ _ (4 * Z.of_nat (length dn) + 4)); try eassumption.
all: try (rewrite ?length_app; cbn [length]; lia).
all: try (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; repeat split; eassumption).
all: try (rewrite f32_cons; eassumption).
exact (conj G1 (conj G2 (conj G3 G4))).
Qed.
End VOC.

Definition NBE_PC_BK : Z := 0xa0f18.
Lemma nbe_bk : forall (usp lo ST FF SF olp sub : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) ->
v216 s = Z_to_bv 64 sub -> v272 s = Z_to_bv 64 (160 * sub) -> 0 <= sub < 4 ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> usp < 2^63 -> SH_HI <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m' : mem) (a0' a7' : word),
munch [(usp + -544, usp + -200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (usp + -544) (slot_cells (sset 272 (Z_to_bv 64 (160 * (sub + 1))) s))
/\ ((sub < 3 /\ ms = MS (R_EL usp ST SF FF olp (sub + 1) gp tp xra t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 t3 t4 t5 t6)
F (Z_to_bv 64 PC_NBD_E) fc None m' (seg_rom asegs))
\/ (sub = 3 /\ ms = MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1 a2 a3 a4 a5 a6 a7'
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40)
(Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_EXIT) fc None m' (seg_rom asegs))))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_BK) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E216 E272 SUB ST0 LO SPH LOS MI.
unfold NBE_PC_EXIT, NBE_PC_BK, PC_NBD_E, R_EL in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v216 v272] in E216, E272. subst w216 w272.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
ato 0xa0f30. rewrite ?Z.add_0_r.
replace (160 * sub + 160) with (160 * (sub + 1)) in * by lia.
astep.
destruct (Z.eq_dec sub 3) as [S3 | S3].
+ subst sub. sh_if. astep.
apply evt_done. do 3 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [exact SL|]. right. split; [reflexivity| reflexivity].
+ sh_if.
apply evt_done. do 3 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [exact SL|]. left. split; [lia| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

