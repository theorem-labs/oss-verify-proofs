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
X0zq X0zp X0zs X0zc X0zu X0wh X0yu X124 X0yd X11g X101.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition NBF_memcpy : Z := 0x66400.
Definition NBF_multicomb : Z := 0xa8f7c.
Definition RA_nbf_cpy : Z := 0xa393c.
Definition RA_nbf_mc1 : Z := 0xa4548.
Definition SC_F : nbscope := NBSC true false true false true.

Lemma lor_al4 : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
Proof.
intros a b Ha Hb HA HB. rewrite Z.land_lor_distr_l.
change 3 with (Z.ones 2). rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite HA, HB. reflexivity.
Qed.

Lemma nbf_1 : forall {ptr : Type} (usp lo ST OUT A FF SF olp bp mo : Z) (r : smrec) (st : nb_state ptr) (pad rest : list byte)
(gp tp xra t0 t2 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> slots_EL ST OUT A FF SF olp bp 4 s ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
rw_cells bsegs m (ST + 12) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))] ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
OUT mod 4 = 0 -> 0 < OUT -> OUT + 640 < 2^64 ->
lib_consts m -> nb_tabs_acc m -> client_constsB m ->
rw_cells bsegs m SF (nbd_shadow SC_E rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
frm0 fc' /\ munch [(SF + 124, SF + 129)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' SF (nbd_shadow SC_F rest)
/\ ((ms = MS (mkR (Z_to_bv 64 RA_nbf_cpy) (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 OUT) (Z_to_bv 64 (ST + 1208)) (Z_to_bv 64 640) a3' a4' a5' a6' a7'
s2 s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_memcpy) fc' None m' (seg_rom bsegs))
\/ (ms = MS (mkR (Z_to_bv 64 RA_nbf_mc1) (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (ST + 1208)) (Z_to_bv 64 OUT) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 10) (Z_to_bv 64 80) (Z_to_bv 64 bp) (Z_to_bv 64 40) (Z_to_bv 64 0)
(Z_to_bv 64 (ST + 2080)) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936))
t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_multicomb) fc' None m' (seg_rom bsegs))))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 (Z_to_bv 64 (ST + 2248)) t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5
(Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
s2 s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_EXIT) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL SLE CFG EMO SAT CL EXP OBS S8 SPOS SLO SOFF SFA O4 OP OB LC NTA CC SH ESF SF0 SF1 F0 F64 FLO FTOP FSH ST0 LO LOS SPH U32 MI FRM.
unfold RA_nbf_cpy, RA_nbf_mc1, NBF_memcpy, NBF_multicomb, NBE_PC_EXIT, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp in SOFF, FSH. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof (munch_refl [(SF + 124, SF + 129)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SLE.
destruct SLE as (E0 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192 & E200 & E208 & E216
& E232 & E240 & E256 & E264 & E272 & E280 & E288 & E296 & E304 & E312 & E320 & E328 & E336 & E344 & E368).
subst w0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w232 w240 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w368.
unfold slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC).
unfold IMG_TOP_B in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof ST0 as (STa & STb & _).
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in SF0u, SF1u.
astep. astep. astep. astep. astep. astep.
assert (SHF : forall o n, (o + n <= FF \/ FF + 2048 <= o) -> shfree [(SF + 124, SF + 129)] o n).
{ intros o n OFA.
apply (shfree_cons_sh _ _ _ _ _ FF 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite ESF, shad_shiftr; lia | rewrite ESF, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact OFA |].
apply shfree_nil. }
pose proof (SFA : _ \/ _) as SFA'.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBS MUc (SHF ST 2968 SFA')) as OBS1;
pose proof (aobj_munch bsegs W m mc _ _ NTM MUc (SHF 1016704 208 ltac:(lia))) as NTM1;
pose proof (aobj_munch bsegs W m mc _ _ OBR MUc (SHF (smr_ptr r) 88 ltac:(lia))) as OBR1;
pose proof (lib_consts_munch _ m mc LC MUc ltac:(repeat (apply Forall_cons; [cbn [fst snd]; unfold SH_LO, SH_HI in *; lia|]); apply Forall_nil)) as LC1;
rename MUc into MUF; pose proof (munch_refl [] mc) as MU end.
assert (OF : offsh []) by exact I.
clear OBS NTM OBR. rename OBS1 into OBS. rename NTM1 into NTM. rename OBR1 into OBR.
clear LC. rename LC1 into LC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (SMC mc LC) as ROW end.
unfold smrec_cells in ROW. cbv zeta in ROW.
bato 0xa3828. astep. try chk_merge OBS 4.
bato 0xa3830.
astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
-
bato 0xa3924.
astep. astep. rewrite (lor_al4 OUT (ST + 1208)) by (try lia; clear - S8; Z.div_mod_to_equations; lia).
bato 0x66400.
apply evt_done. do 15 eexists. split; [exact FRM|]. split; [exact MUF|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|].
split; [exact SH|]. left. reflexivity.
-
bato 0xa3860. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
bato 0xa3868. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa3894.
chk_hint NTM.
bato 0xa38a0.
rewrite (shb_zero bsegs _ 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa38a8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (sub_ptr_read mc mo LC ltac:(lia)) as RD end.
rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD.
set (SP := smr_ptr r) in *.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
bato 0xa38c4. rewrite ?(Z.mod_small (SP + 80)) by lia.
chk_hint OBR.
bato 0xa38c8.
bato 0xa38e0.
astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
+
bato 0xa3924. astep. astep. rewrite (lor_al4 OUT (ST + 1208)) by (try lia; clear - S8; Z.div_mod_to_equations; lia).
bato 0x66400.
apply evt_done. do 15 eexists. split; [exact FRM|]. split; [exact MUF|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|].
split; [exact SH|]. left. reflexivity.
+
bato 0xa8f7c.
apply evt_done. do 15 eexists. split; [exact FRM|]. split; [exact MUF|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|].
split; [exact SH|]. right. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition RA_nbf_mc2 : Z := 0xa4638.

Lemma nbf_2 : forall {ptr : Type} (usp lo ST OUT A FF SF olp bp mo : Z) (r : smrec) (st : nb_state ptr) (pad : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s9 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> slots_EL ST OUT A FF SF olp bp 4 s ->
rw_cells bsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
rw_cells bsegs m (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))] ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
0 < OUT -> OUT + 640 < 2^64 ->
lib_consts m -> nb_tabs_acc m -> client_constsB m ->
lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' t3' t4' t5' t6' : word),
frm0 fc'
/\ ms = MS (mkR (Z_to_bv 64 RA_nbf_mc2) (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (ST + 1528)) (Z_to_bv 64 (OUT + 320)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 10) (Z_to_bv 64 80) (Z_to_bv 64 bp) (Z_to_bv 64 40) (Z_to_bv 64 0)
(Z_to_bv 64 (ST + 2080)) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936))
t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_multicomb) fc' None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_nbf_mc1) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (ST + 2080)) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936))
t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbf_mc1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL SLE CFG EMO SAT EXP OBS S8 SPOS SLO SOFF OP OB LC NTA CC LO LOS SPH MI FRM.
unfold RA_nbf_mc1, RA_nbf_mc2, NBF_multicomb, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp in SOFF. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa4548)) with (Z_to_bv 64 0xa4548) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. assert (OF : offsh []) by exact I.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SLE.
destruct SLE as (E0 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192 & E200 & E208 & E216
& E232 & E240 & E256 & E264 & E272 & E280 & E288 & E296 & E304 & E312 & E320 & E328 & E336 & E344 & E368).
subst w0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w232 w240 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w368.
unfold slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC).
unfold IMG_TOP_B in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
unfold smrec_cells in ROW. cbv zeta in ROW.
set (SP := smr_ptr r) in *.
bato 0xa45a4. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
bato 0xa45ac. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO. rewrite ?(Z.mod_small (1016736 + mo * 8)) by lia.
bato 0xa45d8.
chk_hint NTM.
bato 0xa45e4.
rewrite (shb_zero bsegs _ 1016704 208 (1016736 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
bato 0xa45e8.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD.
rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (1016704 + 32 + 8 * mo) with (1016736 + mo * 8) in RD by lia.
astep. clear RD.
bato 0xa4604. rewrite ?(Z.mod_small (SP + 80)) by lia.
chk_hint OBR.
bato 0xa8f7c.
apply evt_done. do 9 eexists. split; [exact FRM|]. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition NBF_PC_J : Z := 0xa393c.
Definition NBG_PC : Z := 0xa3af8.

Definition R_G (usp ST FF sub : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 sub) s3 (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB) s7
(Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3 (Z_to_bv 64 (FF + 240)) t5 t6.

Definition slots_G (ST FF : Z) (s : nbslots) : nbslots :=
sset 336 (Z_to_bv 64 (18446744073709551615 - (ST + 2168))) (sset 344 (Z_to_bv 64 (FF + 244)) (sset 328 (Z_to_bv 64 (ST + 2120)) s)).

Lemma nbf_3m : forall (usp ST OUT FF : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s9 t3 t4 t5 t6 : word) F fc (m : mem),
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 RA_nbf_mc2) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (ST + 2080)) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936))
t3 t4 t5 t6)
F (Z_to_bv 64 NBF_PC_J) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_nbf_mc2) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (ST + 2080)) s3 s4 (Z_to_bv 64 (FF + 320)) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (ST + 2944)) s9 (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 (ST + 2936))
t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbf_mc2)) fc None m (seg_rom bsegs)).
Proof.
intros. unfold RA_nbf_mc2, NBF_PC_J.
replace (ret_pc (Z_to_bv 64 0xa4638)) with (Z_to_bv 64 0xa4638) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. apply evt_done. reflexivity.
Qed.

Lemma nbf_3 : forall (usp lo ST OUT A FF SF olp bp : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> slots_EL ST OUT A FF SF olp bp 4 s ->
rw_cells bsegs m (ST + 12) [C4 (Z_to_bv 64 0)] ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
client_constsB m ->
stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s7' t3' t5' t6' : word),
frm0 fc' /\ munch [(usp + -576, usp + -200)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (usp + -576) (slot_cells (slots_G ST FF s))
/\ ms = MS (R_G usp ST FF 0 gp tp xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s7' t3' t5' t6') F' (Z_to_bv 64 NBG_PC) fc' None m' (seg_rom bsegs))
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 NBF_PC_J) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL SLE CL OBS S8 SPOS SLO SOFF CC ST0 LO LOS SPH MI FRM.
unfold NBF_PC_J, NBG_PC, R_G, slots_G, NBSTATE_SIZEOF in *. unfold hidp in SOFF. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -576, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -576, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SLE.
destruct SLE as (E0 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192 & E200 & E208 & E216
& E232 & E240 & E256 & E264 & E272 & E280 & E288 & E296 & E304 & E312 & E320 & E328 & E336 & E344 & E368).
subst w0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w232 w240 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w368.
unfold slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
bato 0xa3aac.
bato 0xa3af8.
rewrite !(zb_lxor_ones (ST + 2168)) in * by lia. rewrite !(zb_lxor_ones (ST + 2080)) by lia.
apply evt_done. do 19 eexists. split; [exact FRM|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [eassumption|].
split; [eassumption|]. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbg_lspi10 : forall (OLD NEW IQ usp lo sub : Z) (os ns qs : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
aobj bsegs m OLD 40 -> aobj bsegs m NEW 40 -> aobj bsegs m IQ 40 ->
OLD mod 4 = 0 -> NEW mod 4 = 0 -> IQ mod 4 = 0 -> 0 < OLD -> 0 < NEW ->
rw_cells bsegs m OLD (f32 os) -> length os = 10%nat -> rw_cells bsegs m NEW (f32 ns) -> length ns = 10%nat ->
rw_cells bsegs m IQ (f32 qs) -> length qs = 10%nat ->
(IQ + 40 <= SH_LO \/ SH_HI <= IQ) -> IMG_TOP_B <= IQ ->
(IQ + 40 <= lo \/ usp <= IQ) -> (OLD + 40 <= lo \/ usp <= OLD) -> (NEW + 40 <= lo \/ usp <= NEW) ->
(IQ + 40 <= OLD \/ OLD + 40 <= IQ) -> (IQ + 40 <= NEW \/ NEW + 40 <= IQ) ->
client_constsB m -> stk bsegs m lo usp -> lo <= usp - 64 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (qs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(IQ, IQ + 40); (usp + -64, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc' /\ rw_cells bsegs m' IQ (f32 qs') /\ length qs' = 10%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 10) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros O1 O2 O3 A1 A2 A3 P1 P2 C1 L1 C2 L2 C3 L3 SH IMG D1 D2 D3 D4 D5 CC ST LO LOS SPH MI FRM.
eapply evt_mono.
- eapply (lsp_interpolate_stmt OLD NEW IQ usp lo sub 10%nat os ns qs); try eassumption; try (cbn; lia).
- intros ms' POST. exact POST.
Qed.

Definition RA_nbg_lspi : Z := 0xa3b34.
Definition RA_nbg_l2l : Z := 0xa3b48.
Definition NBG_lsp_to_lpc : Z := 0xae6d8.

Lemma nbg_1 : forall (usp lo ST OUT FF sub : Z) (os ns qs : list word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v280 s = Z_to_bv 64 (ST + 2040) -> v272 s = Z_to_bv 64 (FF + 160) -> v240 s = Z_to_bv 64 OUT ->
v304 s = Z_to_bv 64 0 -> 0 <= sub < 4 ->
rw_cells bsegs m (ST + 2040) (f32 os) -> length os = 10%nat -> aobj bsegs m (ST + 2040) 40 ->
rw_cells bsegs m (FF + 160) (f32 ns) -> length ns = 10%nat -> aobj bsegs m (FF + 160) 40 ->
rw_cells bsegs m (FF + 992) (f32 qs) -> length qs = 10%nat -> aobj bsegs m (FF + 992) 40 ->
ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
0 < OUT -> OUT + 640 < 2^64 ->
client_constsB m -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 64 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (qs' : list word),
frm0 fc' /\ munch [(FF + 992, FF + 1032); (usp + -640, usp + -576)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (FF + 992) (f32 qs') /\ length qs' = 10%nat
/\ ms = MS (mkR (Z_to_bv 64 RA_nbg_l2l) (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 10) (Z_to_bv 64 0) a4' a5' a6' a7'
(Z_to_bv 64 sub) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB)
(Z_to_bv 64 (OUT + 160 * sub)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBG_lsp_to_lpc) fc' None m' (seg_rom bsegs))
(MS (R_G usp ST FF sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t5 t6) F (Z_to_bv 64 NBG_PC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E280 E272 E240 E304 SUB OS LOS0 OBO NS LNS OBN QS LQS OBQ S8 SPOS SLO SFA F0 F64 FLO FTOP FSH OP OB CC ST0 LO LOS SPH MI FRM.
unfold NBG_PC, R_G, RA_nbg_l2l, NBG_lsp_to_lpc, NBSTATE_SIZEOF in *. unfold hidp in SFA, FSH.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (munch_refl [(FF + 992, FF + 1032); (usp + -640, usp + -576)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(FF + 992, FF + 1032); (usp + -640, usp + -576)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v280 v272 v240 v304] in E280, E272, E240, E304. subst w280 w272 w240 w304.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
bato 0xa3b30.
rewrite (Z.mul_comm sub 160).
astep.
call (nbg_lspi10 (ST + 2040) (FF + 160) (FF + 992) (usp + -576) lo sub os ns qs).
all: try eassumption.
all: try (unfold IMG_TOP_B, SH_LO, SH_HI in *; lia).
bato 0xae6d8.
lazymatch goal with H : rw_cells bsegs ?mc (FF + 992) (f32 ?l) |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename l into qs1; rename H into QS1 end.
apply evt_done. do 14 eexists. exists qs1. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [exact QS1|]. split; [assumption| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbg_iir10 : forall (PX PD PM usp lo : Z) (xs den mem0 : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
length xs = 40%nat -> length den = 10%nat -> length mem0 = 10%nat ->
aobj bsegs m PX 160 -> aobj bsegs m PD 40 -> aobj bsegs m PM 40 -> PX mod 4 = 0 -> PD mod 4 = 0 -> PM mod 4 = 0 ->
0 < PX -> 0 < PD -> 0 < PM -> lo <= usp - 128 -> SH_HI <= lo -> usp < 2^63 ->
(PX + 160 <= SH_LO \/ SH_HI <= PX) -> (PM + 40 <= SH_LO \/ SH_HI <= PM) ->
(PX + 160 <= lo \/ usp <= PX) -> (PM + 40 <= lo \/ usp <= PM) -> (PD + 40 <= lo \/ usp <= PD) ->
(PD + 40 <= PM \/ PM + 40 <= PD) -> (PX + 160 <= PM \/ PM + 40 <= PX) -> (PX + 160 <= PD \/ PD + 40 <= PX) ->
rw_cells bsegs m PX (f32 xs) -> rw_cells bsegs m PD (f32 den) -> rw_cells bsegs m PM (f32 mem0) -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= PX -> IMG_TOP_B <= PM -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (ys mv : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(PX, PX + 160); (PM, PM + 40); (usp + -128, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc' /\ length ys = 40%nat /\ rw_cells bsegs m' PX (f32 ys)
/\ length mv = 10%nat /\ rw_cells bsegs m' PM (f32 mv) /\ rw_cells bsegs m' PD (f32 den))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PX) (Z_to_bv 64 PD) (Z_to_bv 64 PX) (Z_to_bv 64 40) (Z_to_bv 64 10) (Z_to_bv 64 PM) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 B_iir_mem16) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros LX LD LM OX OD OM X4 D4 M4 XP DP MP LO LOS SPH XSH MSH XAP MAP DAP SDM SXM SXD CX CD CM FRM ST XI MI' CC MI.
assert (LMEM : length mem0 = length den) by (rewrite LM, LD; reflexivity).
assert (EN : Z.of_nat (length xs) = 40) by (rewrite LX; reflexivity).
assert (EO : Z.of_nat (length den) = 10) by (rewrite LD; reflexivity).
assert (N1 : 1 <= Z.of_nat (length xs) < 2^31) by (rewrite EN; lia).
assert (ORD : 2 <= Z.of_nat (length den) < 2^31) by (rewrite EO; lia).
pose proof (iir_mem16_walk_ip xs den mem0 PX PD PM usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LMEM N1 ORD
ltac:(rewrite EN; exact OX) ltac:(rewrite EO; exact OD) ltac:(rewrite EO; exact OM) X4 D4 M4 XP DP MP LO LOS SPH
ltac:(rewrite EN; exact XSH) ltac:(rewrite EO; exact MSH) ltac:(rewrite EN; exact XAP) ltac:(rewrite EO; exact MAP) ltac:(rewrite EO; exact DAP)
ltac:(rewrite EO; exact SDM) ltac:(rewrite EN, EO; exact SXM) ltac:(rewrite EN, EO; exact SXD)
F t0 t1 t2 a6 a7 t3 t4 t5 t6 fc CX CD CM FRM ST XI MI' CC MI) as W.
rewrite EN, EO in W.
eapply evt_mono; [exact W|].
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & ys & mv & EQ & MU & WM & MI2 & ST2 & FR2 & LYS' & CY2 & LMV & CM2 & CD2 & _).
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m', ys, mv.
replace (PX + 4 * 40) with (PX + 160) in MU by lia. replace (PM + 4 * 10) with (PM + 40) in MU by lia.
split; [exact EQ|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FR2|].
split; [rewrite LYS'; exact LX|]. split; [exact CY2|]. split; [rewrite LMV; exact LD|]. split; [exact CM2| exact CD2].
Qed.
Definition RA_nbg_iir : Z := 0xa3bac.
Definition NBG_PC_CPYE : Z := 0xa3bf4.

Lemma nbg_2 : forall (usp lo ST OUT FF sub : Z) (aks pg xo iq msp : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v344 s = Z_to_bv 64 (FF + 244) -> v336 s = Z_to_bv 64 (18446744073709551615 - (ST + 2168)) ->
v328 s = Z_to_bv 64 (ST + 2120) -> v304 s = Z_to_bv 64 0 -> v152 s = Z_to_bv 64 (FF + 240) -> 0 <= sub < 4 ->
rw_cells bsegs m (FF + 240) (f32 aks) -> length aks = 10%nat ->
rw_cells bsegs m (ST + 2168) (f32 pg) -> length pg = 4%nat ->
rw_cells bsegs m (OUT + 160 * sub) (f32 xo) -> length xo = 40%nat -> aobj bsegs m (OUT + 160 * sub) 160 -> OUT mod 4 = 0 -> 0 < OUT -> IMG_TOP_B <= OUT ->
hidp (OUT + 160 * sub + 160 <= SH_LO \/ SH_HI <= OUT + 160 * sub) -> OUT + 160 * sub + 160 <= lo ->
hidp (ST + NBSTATE_SIZEOF <= OUT + 160 * sub \/ OUT + 160 * sub + 160 <= ST) ->
hidp (OUT + 160 * sub + 160 <= FF \/ FF + 2048 <= OUT + 160 * sub) -> hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
rw_cells bsegs m (ST + 2080) (f32 iq) -> length iq = 10%nat -> rw_cells bsegs m (ST + 2120) (f32 msp) -> length msp = 10%nat ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
IMG_TOP_B <= ST ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
client_constsB m -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 - 128 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t5' t6' : word) (pg' xo' msp' iq' : list word),
frm0 fc' /\ munch [(ST + 2168, ST + 2184); (OUT + 160 * sub, OUT + 160 * sub + 160); (ST + 2120, ST + 2160); (ST + 2080, ST + 2120); (usp + -704, usp + -576)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (ST + 2168) (f32 pg') /\ length pg' = 4%nat /\ rw_cells bsegs m' (OUT + 160 * sub) (f32 xo') /\ length xo' = 40%nat
/\ rw_cells bsegs m' (ST + 2120) (f32 msp') /\ length msp' = 10%nat /\ rw_cells bsegs m' (ST + 2080) (f32 iq') /\ length iq' = 10%nat
/\ rw_cells bsegs m' (FF + 240) (f32 aks)
/\ ms = MS (mkR (Z_to_bv 64 RA_nbg_iir) (Z_to_bv 64 (usp + -576)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 sub) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB)
(Z_to_bv 64 (OUT + 160 * sub)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3' (Z_to_bv 64 (FF + 240)) t5' t6')
F' (Z_to_bv 64 NBG_PC_CPYE) fc' None m' (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_nbg_l2l) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 sub) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB)
(Z_to_bv 64 (OUT + 160 * sub)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbg_l2l)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E344 E336 E328 E304 E152 SUB AK LAK PG LPG XO LXO OBX OUT4 OPOS OTOP OSH OLO SOA OFA SFA IQ LIQ MSP LMSP OBS S8 SPOS SLO SOFF SIMG F0 F64 FLO FTOP FSH
CC ST0 LO LOS SPH MI FRM.
unfold RA_nbg_l2l, RA_nbg_iir, NBG_PC_CPYE, NBSTATE_SIZEOF in *. unfold hidp in SOFF, FSH, OSH, SOA, OFA, SFA. pose proof SIMG as SIMG'. unfold IMG_TOP_B in SIMG'.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'. pose proof OTOP as OTOP'. unfold IMG_TOP_B in OTOP'.
pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'. pose proof OSH as OSH'. unfold SH_LO, SH_HI in OSH'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
replace (ret_pc (Z_to_bv 64 0xa3b48)) with (Z_to_bv 64 0xa3b48) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(ST + 2168, ST + 2184); (OUT + 160 * sub, OUT + 160 * sub + 160); (ST + 2120, ST + 2160); (ST + 2080, ST + 2120); (usp + -704, usp + -576)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(ST + 2168, ST + 2184); (OUT + 160 * sub, OUT + 160 * sub + 160); (ST + 2120, ST + 2160); (ST + 2080, ST + 2120); (usp + -704, usp + -576)])
by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v344 v336 v328 v304 v152] in E344, E336, E328, E304, E152. subst w344 w336 w328 w304 w152.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
destruct aks as [|k0 [|k1 [|k2 [|k3 [|k4 [|k5 [|k6 [|k7 [|k8 [|k9 [|k10 aks]]]]]]]]]]]; cbn [length] in LAK; try discriminate.
rewrite !f32_cons, f32_nil in AK.
do 5 (bato 0xa3b64; astep; sh_if).
bato 0xa3b74.
astep.
replace (ST + 2168 + sub * 4) with (ST + 2168 + 4 * sub) by lia.
destruct (nbe_f32_split3 _ (ST + 2168) pg sub PG ltac:(lia)) as (P1 & P2 & P3). clear PG.
remember (firstn (Z.to_nat sub) pg) as l1 eqn:EL1. remember (skipn (S (Z.to_nat sub)) pg) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = sub) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 3 - sub) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
bato 0xa3b84. astep. chk_merge OBS 4.
bato 0xa3b8c.
lazymatch goal with H : rw_cells bsegs ?mc (ST + 2168 + 4 * sub) [C4 ?w] |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PG : rw_cells bsegs mc (ST + 2168) (f32 (l1 ++ w :: l3))) by (apply nbe_f32_join3; [exact P1| rewrite LL1; exact H| rewrite LL1; exact P3]);
assert (LPG' : length (l1 ++ w :: l3) = 4%nat) by (rewrite length_app; cbn [length]; lia);
set (pg1 := l1 ++ w :: l3) in *; clearbody pg1; clear H end.
clear P1 P3 l1 l3 LL1 LL3 LPG.
bato 0xa3ba8.
astep.
call (nbg_iir10 (OUT + 160 * sub) (ST + 2080) (ST + 2120) (usp + -576) lo xo iq msp).
all: try eassumption.
all: try (unfold IMG_TOP_B, SH_LO, SH_HI in *; lia).
{ exact (aobj_munch bsegs _ m m0 _ 160 OBX MU (shfree_of_aobj bsegs _ m _ 160 OF OBX)). }
{ pose proof (aobj_sub bsegs _ _ _ (ST + 2080) 40 OBS ltac:(lia) ltac:(lia)) as OB'. exact (aobj_munch bsegs _ m m0 _ 40 OB' MU (shfree_of_aobj bsegs _ m _ 40 OF OB')). }
{ pose proof (aobj_sub bsegs _ _ _ (ST + 2120) 40 OBS ltac:(lia) ltac:(lia)) as OB'. exact (aobj_munch bsegs _ m m0 _ 40 OB' MU (shfree_of_aobj bsegs _ m _ 40 OF OB')). }
{ exact (conj G1 (conj G2 (conj G3 G4))). }
clear POST.
destruct iq as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|q8 [|q9 [|q10 iq]]]]]]]]]]]; cbn [length] in LIQ; try discriminate.
rewrite !f32_cons, f32_nil in IQ.
bato 0xa3bdc.
bato 0xa3bf4.
apply evt_done. do 17 eexists. exists pg1, x18, x19.
f32_of_cells IQ.
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [exact PG|]. split; [exact LPG'|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [exact IQ|]. split; [reflexivity|]. split; [rewrite !f32_cons, f32_nil; exact AK|]. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition NBH_PC : Z := 0xa3c14.

Lemma nbg_3 : forall (usp ST OUT FF sub : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t5 t6 : word) F fc (m : mem),
0 <= sub < 4 ->
evt bsegs (fun ms => exists (a0' : word),
(sub < 3 /\ ms = MS (R_G usp ST FF (sub + 1) gp tp (Z_to_bv 64 RA_nbg_iir) t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (OUT + 160 * sub)) t3 t5 t6)
F (Z_to_bv 64 NBG_PC) fc None m (seg_rom bsegs))
\/ (sub = 3 /\ ms = MS (R_G usp ST FF 4 gp tp (Z_to_bv 64 RA_nbg_iir) t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (OUT + 160 * sub)) t3 t5 t6)
F (Z_to_bv 64 NBH_PC) fc None m (seg_rom bsegs)))
(MS (mkR (Z_to_bv 64 RA_nbg_iir) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 sub) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB)
(Z_to_bv 64 (OUT + 160 * sub)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3 (Z_to_bv 64 (FF + 240)) t5 t6)
F (Z_to_bv 64 NBG_PC_CPYE) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SUB.
unfold NBG_PC_CPYE, NBG_PC, NBH_PC, R_G.
astep. astep.
destruct (Z.eq_dec sub 3) as [S3 | S3].
- subst sub. astep. try sh_if. bato 0xa3c14. apply evt_done. eexists. right. split; [reflexivity| reflexivity].
- astep. sh_if. apply evt_done. eexists. left. split; [lia| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition NBH_PC_LV : Z := 0xa3c74.
Definition NBH_highpass : Z := 0xa5d3c.

Definition hp_filt (w : Z) : Z := if w =? 0 then 1 else 3.

Definition R_H (usp ST OUT FF : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB)
(Z_to_bv 64 (OUT + 160 * 3)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3 t4 t5 t6.

Lemma nbh_1a : forall {ptr : Type} (usp lo ST OUT FF : Z) (st : nb_state ptr) (pad : list byte)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v192 s = Z_to_bv 64 (ST + 2184) -> v64 s = Z_to_bv 64 (ST + 2047) -> v240 s = Z_to_bv 64 OUT ->
rw_cells bsegs m (ST + 2948) (nb_tail_cells st pad) ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
client_constsB m -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
nb_highpass_enabled st = 1 -> (nb_isWideband st = 0 \/ nb_isWideband st = 1) ->
evt bsegs (fun ms => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (R_H usp ST OUT FF gp tp (Z_to_bv 64 NBH_PC_LV) t0' t1' t2' (Z_to_bv 64 OUT) (Z_to_bv 64 OUT) (Z_to_bv 64 160) (Z_to_bv 64 (hp_filt (nb_isWideband st)))
(Z_to_bv 64 (ST + 2160)) a5' a6' a7' t3' t4' t5' t6')
F (Z_to_bv 64 NBH_highpass) fc None m (seg_rom bsegs))
(MS (R_G usp ST FF 4 gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (OUT + 160 * 3)) t3 t5 t6) F (Z_to_bv 64 NBH_PC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E192 E64 E240 TL OBS S8 SPOS SLO SOFF CC ST0 LO LOS SPH MI FRM HPE ISW.
unfold NBH_PC, NBH_PC_LV, NBH_highpass, R_G, R_H, hp_filt, NBSTATE_SIZEOF, nb_tail_cells in *. unfold hidp in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v192 v64 v240] in E192, E64, E240. subst w192 w64 w240.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [] m) as MU. assert (OF : offsh []) by exact I.
bato 0xa3c28. astep. try chk_merge OBS 4.
bato 0xa3c30. rewrite HPE in *. cbn [sx32] in *.
bato 0xa3c4c. rewrite sx32_small by (unfold int31; lia).
destruct ISW as [W0 | W1].
- rewrite W0 in *. bato 0xa5d3c. apply evt_done. do 10 eexists. reflexivity.
- rewrite W1 in *. bato 0xa5d3c. apply evt_done. do 10 eexists. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition NBH_PC_QC : Z := 0xa3d30.
Definition NBH_PC_H2 : Z := 0xa3d88.

Lemma nbh_qcopy : forall (usp lo ST FF : Z) (oq ql : list word) (xra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v280 s = Z_to_bv 64 (ST + 2040) -> v272 s = Z_to_bv 64 (FF + 160) ->
rw_cells bsegs m (ST + 2040) (f32 oq) -> length oq = 10%nat -> rw_cells bsegs m (FF + 160) (f32 ql) -> length ql = 10%nat ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP_B <= ST ->
0 < FF -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
client_constsB m -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (a0' a1' a2' a3' a4' a5' : word) (oq' : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' a2' a3' a4' a5' a6 a7
s2 s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 NBH_PC_H2) fc None m' (seg_rom bsegs)
/\ munch [(ST + 2040, ST + 2080)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' (ST + 2040) (f32 oq') /\ length oq' = 10%nat)
(MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 NBH_PC_QC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E280 E272 OQ LOQ QL LQL OBS S8 SPOS SLO SOFF SIMG F0 FLO FTOP SFA CC LO LOS SPH MI.
unfold NBH_PC_QC, NBH_PC_H2, NBSTATE_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof SIMG as SIMG'. unfold IMG_TOP_B in SIMG'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(ST + 2040, ST + 2080)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(ST + 2040, ST + 2080)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v280 v272] in E280, E272. subst w280 w272.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
destruct oq as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|q8 [|q9 [|q10 oq]]]]]]]]]]]; cbn [length] in LOQ; try discriminate.
destruct ql as [|k0 [|k1 [|k2 [|k3 [|k4 [|k5 [|k6 [|k7 [|k8 [|k9 [|k10 ql]]]]]]]]]]]; cbn [length] in LQL; try discriminate.
rewrite !f32_cons, f32_nil in OQ, QL.
bato 0xa3d3c. rewrite (zb_lxor_ones (ST + 2040)) by lia.
bato 0xa3d88.
apply evt_done. do 8 eexists. f32_of_cells OQ.
split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact OQ| reflexivity].
Qed.

Definition JXF (segs : list Segment) (pc : Z) (m : mem) (R : bvmap 5 word) : machine_state -> Prop :=
fun ms => exists (F' : bvmap 5 word) (fc' : bv 32), ms = MS R F' (Z_to_bv 64 pc) fc' None m (seg_rom segs) /\ frm0 fc'.
Ltac jxf_done := apply evt_done; do 2 eexists; split; [reflexivity| assumption].
Tactic Notation "joinF" constr(pcJ) integer(n1) integer(n2) :=
lazymatch goal with |- evt ?segs _ (MS ?R _ _ _ _ ?mc _) =>
eapply (evt_cut segs (JXF segs pcJ mc R));
[ let B := fresh "B" in if_cases B;
[ do n1 astep; jxf_done | do n2 astep; jxf_done ]
| try match goal with H : frm0 _ |- _ => clear H end;
let FRM := fresh "FRM" in intros ? (? & ? & -> & FRM) ]
end.

Lemma nbh_1b : forall (usp lo ST OUT FF : Z) (lv oq ql : list word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v280 s = Z_to_bv 64 (ST + 2040) -> v272 s = Z_to_bv 64 (FF + 160) ->
rw_cells bsegs m (ST + 2192) (f32 lv) -> length lv = 3%nat ->
rw_cells bsegs m (ST + 2040) (f32 oq) -> length oq = 10%nat -> rw_cells bsegs m (FF + 160) (f32 ql) -> length ql = 10%nat ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP_B <= ST ->
0 < FF -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
client_constsB m -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (a0' a1' a2' a3' a4' a5' : word) (lv' oq' : list word),
frm0 fc' /\ munch [(ST + 2192, ST + 2204); (ST + 2040, ST + 2080)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (ST + 2192) (f32 lv') /\ length lv' = 3%nat /\ rw_cells bsegs m' (ST + 2040) (f32 oq') /\ length oq' = 10%nat
/\ ms = MS (R_H usp ST OUT FF gp tp xra t0 t1 t2 a0' a1' a2' a3' a4' a5' a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 NBH_PC_H2) fc' None m' (seg_rom bsegs))
(MS (R_H usp ST OUT FF gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 NBH_PC_LV) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E280 E272 LV LLV OQ LOQ QL LQL OBS S8 SPOS SLO SOFF SIMG F0 FLO FTOP SFA CC ST0 LO LOS SPH MI FRM.
unfold NBH_PC_LV, NBH_PC_H2, R_H, NBSTATE_SIZEOF in *. unfold hidp in SOFF, SFA.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof SIMG as SIMG'. unfold IMG_TOP_B in SIMG'.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(ST + 2192, ST + 2204); (ST + 2040, ST + 2080)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(ST + 2192, ST + 2204); (ST + 2040, ST + 2080)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
destruct lv as [|l0 [|l1 [|l2 [|]]]]; cbn [length] in LLV; try discriminate. clear LLV.
rewrite !f32_cons, f32_nil in LV.
bato 0xa3c84. astep. try chk_merge OBS 4.
bato 0xa3cc0. astep. joinF 0xa3cc8 0 1.
bato 0xa3cfc. astep. joinF 0xa3d04 0 1.
bato 0xa3d20. astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
all: bato 0xa3d30.
all: lazymatch goal with MUc : munch ?W _ ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBS MUc (shfree_of_aobj bsegs W m _ _ OF OBS)) as OBSc;
assert (CCc : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
eapply evt_cut; [eapply (nbh_qcopy usp lo ST FF oq ql); try eassumption; try (unfold SH_LO, SH_HI, IMG_TOP_B in *; lia) |] end.
- intros ms' (m' & F' & a0' & a1' & a2' & a3' & a4' & a5' & oq' & -> & MU' & WM' & MI' & OQ' & LOQ').
lazymatch goal with MUq : munch [(ST + 2040, ST + 2080)] ?mc ?mq, MUc : munch ?W ?m0 ?mc |- _ =>
pose proof (munch_trans _ _ _ _ MUc (munch_weaken [(ST + 2040, ST + 2080)] W mc mq ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUq)) as MU2;
transport_after_call bsegs mc mq MUq WM' end.
lazymatch goal with H : rw_cells bsegs ?mq (ST + 2192) [C4 ?x; C4 ?y; C4 ?z], OQq : rw_cells bsegs ?mq (ST + 2040) (f32 ?oqq) |- _ =>
apply evt_done; do 9 eexists; exists [x; y; z], oqq; split; [eassumption|]; split; [exact MU2|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [rewrite !f32_cons, f32_nil; exact H|]; split; [reflexivity|]; split; [exact OQq|]; split; [eassumption| reflexivity] end.
- intros ms' (m' & F' & a0' & a1' & a2' & a3' & a4' & a5' & oq' & -> & MU' & WM' & MI' & OQ' & LOQ').
lazymatch goal with MUq : munch [(ST + 2040, ST + 2080)] ?mc ?mq, MUc : munch ?W ?m0 ?mc |- _ =>
pose proof (munch_trans _ _ _ _ MUc (munch_weaken [(ST + 2040, ST + 2080)] W mc mq ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUq)) as MU2;
transport_after_call bsegs mc mq MUq WM' end.
lazymatch goal with H : rw_cells bsegs ?mq (ST + 2192) [C4 ?x; C4 ?y; C4 ?z], OQq : rw_cells bsegs ?mq (ST + 2040) (f32 ?oqq) |- _ =>
apply evt_done; do 9 eexists; exists [x; y; z], oqq; split; [eassumption|]; split; [exact MU2|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [rewrite !f32_cons, f32_nil; exact H|]; split; [reflexivity|]; split; [exact OQq|]; split; [eassumption| reflexivity] end.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbh_2tail : forall (usp lo ST OUT FF SF : Z) (rest : list byte) (lol : word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 t3 t4 t5 t6 : word) (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 : word) F fc (m : mem),
rw_cells bsegs m (usp + -576) [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 (Z_to_bv 64 SF); C8 w208; C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368] ->
rw_cells bsegs m (ST + 20) [C4 lol] ->
rw_cells bsegs m SF (nbd_shadow SC_F rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP_B <= ST ->
(ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
client_constsB m -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (a0' a1' a3' a4' a5' a6' a7' : word) (lol' : word),
frm0 fc' /\ munch [(ST + 20, ST + 24); (SF + 20, SF + 129)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (ST + 20) [C4 lol'] /\ rw_cells bsegs m' SF (nbd_shadow SC_X rest)
/\ ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' (Z_to_bv 64 SF) a3' a4' a5' a6' a7'
(Z_to_bv 64 0) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB)
(Z_to_bv 64 (OUT + 160 * 3)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3 t4 t5 t6)
F' (Z_to_bv 64 PC_NBD_X) fc' None m' (seg_rom bsegs))
(MS (R_H usp ST OUT FF gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 ST) a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa3e64) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL LOL SH ESF SF0 SF1 F0 F64 FLO FTOP FSH OBS S8 SPOS SLO SOFF SIMG SFA CC ST0 LO LOS SPH MI FRM.
unfold R_H, PC_NBD_X, NBSTATE_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof SIMG as SIMG'. unfold IMG_TOP_B in SIMG'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in SF0u, SF1u.
pose proof (munch_refl [(ST + 20, ST + 24); (SF + 20, SF + 129)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof ST0 as (STa & STb & _).
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
unfold nbd_shadow, nbd_shadow_bytes, SC_F, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
bato 0xa4450.
lazymatch goal with |- evt _ _ (MS _ ?F1 _ ?fcx _ ?mc _) =>
lazymatch goal with L1 : rw_cells bsegs mc (ST + 20) [C4 ?lv] |- _ =>
apply evt_done; exists mc, F1, fcx; do 7 eexists; exists lv;
split; [eassumption|]; split; [exact MU|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [exact L1|]; split; [unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8; cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq]; exact SH|]; reflexivity end end.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbh_2 : forall (usp lo ST OUT FF SF bp idx first cl : Z) (rest : list byte) (lol lp lpg : word) (pgb : list word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells bsegs m (usp + -576) (slot_cells s) -> v32 s = Z_to_bv 64 (Z.shiftr (ST + 8) 3 + SHB) -> v40 s = Z_to_bv 64 (ST + 8) ->
v160 s = Z_to_bv 64 (Z.shiftr (ST + 12) 3 + SHB) -> v88 s = Z_to_bv 64 ST -> v192 s = Z_to_bv 64 (ST + 2184) -> v296 s = Z_to_bv 64 bp ->
v112 s = Z_to_bv 64 (Z.shiftr (ST + 2208) 3 + SHB) -> v64 s = Z_to_bv 64 (ST + 2047) -> v200 s = Z_to_bv 64 SF -> 17 <= bp <= 144 ->
rw_cells bsegs m (ST + 8) [C4 (Z_to_bv 64 first); C4 (Z_to_bv 64 cl)] -> rw_cells bsegs m (ST + 20) [C4 lol] ->
rw_cells bsegs m (ST + 2204) [C4 lp; C4 lpg] -> rw_cells bsegs m (ST + 2212) (f32 pgb) -> length pgb = 3%nat ->
rw_cells bsegs m (ST + 2224) [C4 (Z_to_bv 64 idx)] -> 0 <= idx <= 2 ->
rw_cells bsegs m SF (nbd_shadow SC_F rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP_B <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP_B <= ST ->
hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
client_constsB m -> stk bsegs m lo (usp + -576) -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (a0' a1' a3' a4' a5' a6' a7' : word)
(lol' lpg' : word) (pgb' : list word),
frm0 fc' /\ munch [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (usp + -576)
/\ rw_cells bsegs m' (ST + 8) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m' (ST + 20) [C4 lol']
/\ rw_cells bsegs m' (ST + 2204) [C4 (Z_to_bv 64 bp); C4 lpg'] /\ rw_cells bsegs m' (ST + 2212) (f32 pgb') /\ length pgb' = 3%nat
/\ rw_cells bsegs m' (ST + 2224) [C4 (Z_to_bv 64 (if 2 <? idx + 1 then 0 else idx + 1))]
/\ rw_cells bsegs m' SF (nbd_shadow SC_X rest)
/\ ms = MS (mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0' a1' (Z_to_bv 64 SF) a3' a4' a5' a6' a7'
(Z_to_bv 64 0) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) (Z_to_bv 64 SHB)
(Z_to_bv 64 (OUT + 160 * 3)) (Z_to_bv 64 40) (Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 (ST + 2168)) t3 t4 t5 t6)
F' (Z_to_bv 64 PC_NBD_X) fc' None m' (seg_rom bsegs))
(MS (R_H usp ST OUT FF gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 NBH_PC_H2) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E32 E40 E160 E88 E192 E296 E112 E64 E200 BP HDR LOL LPP PGB LPGB IDX HIDX SH ESF SF0 SF1 F0 F64 FLO FTOP FSH OBS S8 SPOS SLO SOFF SIMG SFA
CC ST0 LO LOS SPH MI FRM.
unfold NBH_PC_H2, R_H, PC_NBD_X, NBSTATE_SIZEOF in *. unfold hidp in SOFF, FSH, SFA.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof SIMG as SIMG'. unfold IMG_TOP_B in SIMG'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in SF0u, SF1u.
pose proof (munch_refl [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368].
cbn [v32 v40 v160 v88 v192 v296 v112 v64 v200] in E32, E40, E160, E88, E192, E296, E112, E64, E200. subst w32 w40 w160 w88 w192 w296 w112 w64 w200.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
unfold nbd_shadow, nbd_shadow_bytes, SC_F, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
destruct pgb as [|p0 [|p1 [|p2 [|]]]]; cbn [length] in LPGB; try discriminate. clear LPGB.
rewrite !f32_cons, f32_nil in PGB.
bato 0xa3dc4. astep. try chk_merge OBS 4.
bato 0xa3dfc. astep. try chk_merge OBS 4.
bato 0xa3e04. rewrite ?sx32_small by (unfold int31; lia).
assert (HI3 : idx = 0 \/ idx = 1 \/ idx = 2) by lia.
destruct HI3 as [-> | [-> | ->]].
- bato 0xa3e64.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBS MUc (shfree_of_aobj bsegs W m _ _ OF OBS)) as OBSc;
assert (CCc : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
eapply evt_cut; [eapply (nbh_2tail usp lo ST OUT FF SF rest lol); try eassumption; try (unfold NBSTATE_SIZEOF, SH_LO, SH_HI, IMG_TOP_B in *; lia) |] end.
intros ms' (m' & F' & fc' & a0' & a1' & a3' & a4' & a5' & a6' & a7' & lol' & FRM' & MU' & WM' & MI' & ST' & LOL' & SH' & ->).
lazymatch goal with MUq : munch _ ?mc m', MUc : munch ?W m ?mc |- _ =>
pose proof (munch_weaken [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228)] [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] m mc ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUc) as MUcw;
pose proof (munch_trans _ _ _ _ MUcw (munch_weaken [(ST + 20, ST + 24); (SF + 20, SF + 129)] [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] mc m'
ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUq)) as MU2;
pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2;
clear OBSc MUc; transport_after_call bsegs mc m' MUq WM' end.
lazymatch goal with L2 : rw_cells bsegs m' (ST + 2204) [C4 _; C4 ?lg] |- _ =>
lazymatch goal with L3 : rw_cells bsegs m' (ST + 2212) [C4 ?q0; C4 ?q1; C4 ?q2] |- _ =>
apply evt_done; exists m', F', fc', a0', a1', a3', a4', a5', a6', a7', lol', lg, [q0; q1; q2];
split; [exact FRM'|]; split; [exact MU2|]; split; [exact WM2|]; split; [exact MI'|]; split; [exact ST'|];
split; [exact HDR|]; split; [exact LOL'|]; split; [exact L2|]; split; [rewrite !f32_cons, f32_nil; exact L3|]; split; [reflexivity|];
split; [exact IDX|]; split; [exact SH'|]; reflexivity end end.
- bato 0xa3e64.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBS MUc (shfree_of_aobj bsegs W m _ _ OF OBS)) as OBSc;
assert (CCc : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
eapply evt_cut; [eapply (nbh_2tail usp lo ST OUT FF SF rest lol); try eassumption; try (unfold NBSTATE_SIZEOF, SH_LO, SH_HI, IMG_TOP_B in *; lia) |] end.
intros ms' (m' & F' & fc' & a0' & a1' & a3' & a4' & a5' & a6' & a7' & lol' & FRM' & MU' & WM' & MI' & ST' & LOL' & SH' & ->).
lazymatch goal with MUq : munch _ ?mc m', MUc : munch ?W m ?mc |- _ =>
pose proof (munch_weaken [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228)] [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] m mc ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUc) as MUcw;
pose proof (munch_trans _ _ _ _ MUcw (munch_weaken [(ST + 20, ST + 24); (SF + 20, SF + 129)] [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] mc m'
ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUq)) as MU2;
pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2;
clear OBSc MUc; transport_after_call bsegs mc m' MUq WM' end.
lazymatch goal with L2 : rw_cells bsegs m' (ST + 2204) [C4 _; C4 ?lg] |- _ =>
lazymatch goal with L3 : rw_cells bsegs m' (ST + 2212) [C4 ?q0; C4 ?q1; C4 ?q2] |- _ =>
apply evt_done; exists m', F', fc', a0', a1', a3', a4', a5', a6', a7', lol', lg, [q0; q1; q2];
split; [exact FRM'|]; split; [exact MU2|]; split; [exact WM2|]; split; [exact MI'|]; split; [exact ST'|];
split; [exact HDR|]; split; [exact LOL'|]; split; [exact L2|]; split; [rewrite !f32_cons, f32_nil; exact L3|]; split; [reflexivity|];
split; [exact IDX|]; split; [exact SH'|]; reflexivity end end.
- bato 0xa3e64.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs W m mc _ _ OBS MUc (shfree_of_aobj bsegs W m _ _ OF OBS)) as OBSc;
assert (CCc : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
eapply evt_cut; [eapply (nbh_2tail usp lo ST OUT FF SF rest lol); try eassumption; try (unfold NBSTATE_SIZEOF, SH_LO, SH_HI, IMG_TOP_B in *; lia) |] end.
intros ms' (m' & F' & fc' & a0' & a1' & a3' & a4' & a5' & a6' & a7' & lol' & FRM' & MU' & WM' & MI' & ST' & LOL' & SH' & ->).
lazymatch goal with MUq : munch _ ?mc m', MUc : munch ?W m ?mc |- _ =>
pose proof (munch_weaken [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228)] [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] m mc ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUc) as MUcw;
pose proof (munch_trans _ _ _ _ MUcw (munch_weaken [(ST + 20, ST + 24); (SF + 20, SF + 129)] [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] mc m'
ltac:(unfold sub_fp; intros y Hy; cbn [outside] in *; lia) MUq)) as MU2;
pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2;
clear OBSc MUc; transport_after_call bsegs mc m' MUq WM' end.
lazymatch goal with L2 : rw_cells bsegs m' (ST + 2204) [C4 _; C4 ?lg] |- _ =>
lazymatch goal with L3 : rw_cells bsegs m' (ST + 2212) [C4 ?q0; C4 ?q1; C4 ?q2] |- _ =>
apply evt_done; exists m', F', fc', a0', a1', a3', a4', a5', a6', a7', lol', lg, [q0; q1; q2];
split; [exact FRM'|]; split; [exact MU2|]; split; [exact WM2|]; split; [exact MI'|]; split; [exact ST'|];
split; [exact HDR|]; split; [exact LOL'|]; split; [exact L2|]; split; [rewrite !f32_cons, f32_nil; exact L3|]; split; [reflexivity|];
split; [exact IDX|]; split; [exact SH'|]; reflexivity end end.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

