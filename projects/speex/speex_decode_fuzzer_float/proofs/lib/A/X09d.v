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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X09c.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).
Definition NBF_memcpy : Z := 0x66314.
Definition NBF_multicomb : Z := 0xa5388.
Definition RA_nbf_cpy : Z := 0xa10fc.
Definition RA_nbf_mc1 : Z := 0xa1b00.
Definition SC_F : nbscope := NBSC true false true false true.

Lemma nbf_1 : forall {ptr : Type} (usp lo ST OUT A FF SF olp bp mo : Z) (r : smrec) (st : nb_state ptr) (pad rest : list byte)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> slots_EL ST OUT A FF bp 4 s ->
rw_cells asegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
rw_cells asegs m (ST + 12) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))] ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_consts m ->
rw_cells asegs m SF (nbd_shadow SC_E rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' : word),
frm0 fc' /\ munch [(SF + 124, SF + 129)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' SF (nbd_shadow SC_F rest)
/\ ((ms = MS (mkR (Z_to_bv 64 RA_nbf_cpy) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 OUT) (Z_to_bv 64 (ST + 1208)) (Z_to_bv 64 640) a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) s5' (Z_to_bv 64 (ST + 2047))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_memcpy) fc' None m' (seg_rom asegs))
\/ (ms = MS (mkR (Z_to_bv 64 RA_nbf_mc1) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (ST + 1208)) (Z_to_bv 64 OUT) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 10) (Z_to_bv 64 80) (Z_to_bv 64 bp) (Z_to_bv 64 40) (Z_to_bv 64 0)
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2047))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_multicomb) fc' None m' (seg_rom asegs))))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40)
(Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 NBE_PC_EXIT) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL SLE CFG EMO SAT CL EXP OBS S8 SPOS SLO SOFF SFA LC NTA CC SH ESF SF0 SF1 F0 F64 FLO FTOP FSH ST0 LO LOS SPH U32 MI FRM.
unfold RA_nbf_cpy, RA_nbf_mc1, NBF_memcpy, NBF_multicomb, NBE_PC_EXIT, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp in SOFF, FSH. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof (munch_refl [(SF + 124, SF + 129)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SLE.
destruct SLE as (E0 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192
& E224 & E240 & E248 & E256 & E272 & E280 & E288 & E296 & E304 & E312 & E336).
subst w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w224 w240 w248 w256 w272 w280 w288 w296 w304 w312 w336.
unfold slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC).
unfold IMG_TOP in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
pose proof ST0 as (STa & STb & _).
unfold nbd_shadow, nbd_shadow_bytes, SC_E, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in SF0u, SF1u.
astep. astep. astep. astep. astep.
assert (SHF : forall o n, (o + n <= FF \/ FF + 2048 <= o) -> shfree [(SF + 124, SF + 129)] o n).
{ intros o n OFA.
apply (shfree_cons_sh _ _ _ _ _ FF 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite ESF, shad_shiftr; lia | rewrite ESF, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact OFA |].
apply shfree_nil. }
pose proof (SFA : _ \/ _) as SFA'.
lazymatch goal with MUc : munch ?W m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs W m mc _ _ OBS MUc (SHF ST 2968 SFA')) as OBS1;
pose proof (aobj_munch asegs W m mc _ _ NTM MUc (SHF 981760 208 ltac:(lia))) as NTM1;
pose proof (aobj_munch asegs W m mc _ _ OBR MUc (SHF (smr_ptr r) 88 ltac:(lia))) as OBR1;
pose proof (lib_consts_munch _ m mc LC MUc ltac:(repeat (apply Forall_cons; [cbn [fst snd]; unfold SH_LO, SH_HI in *; lia|]); apply Forall_nil)) as LC1;
rename MUc into MUF; pose proof (munch_refl [] mc) as MU end.
assert (OF : offsh []) by exact I.
clear OBS NTM OBR. rename OBS1 into OBS. rename NTM1 into NTM. rename OBR1 into OBR.
clear LC. rename LC1 into LC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (SMC mc LC) as ROW end.
unfold smrec_cells in ROW. cbv zeta in ROW.
ato 0xa103c. astep. try chk_merge OBS 4.
ato 0xa1054.
astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
-
ato 0x66314.
apply evt_done. do 16 eexists. split; [exact FRM|]. split; [exact MUF|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|].
split; [exact SH|]. left. reflexivity.
-
ato 0xa107c. astep. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
ato 0xa1084. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO.
chk_hint NTM.
ato 0xa1094.
rewrite (shb_zero asegs _ 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa109c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (sub_ptr_read mc mo LC ltac:(lia)) as RD end.
rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD.
set (SP := smr_ptr r) in *.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
ato 0xa10a8. rewrite ?(Z.mod_small (SP + 80)) by lia.
chk_hint OBR.
ato 0xa10b8.
astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
+
ato 0x66314.
apply evt_done. do 16 eexists. split; [exact FRM|]. split; [exact MUF|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|].
split; [exact SH|]. left. reflexivity.
+
ato 0xa5388.
apply evt_done. do 16 eexists. split; [exact FRM|]. split; [exact MUF|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|].
split; [exact SH|]. right. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition RA_nbf_mc2 : Z := 0xa1b90.

Lemma nbf_2 : forall {ptr : Type} (usp lo ST OUT A FF SF olp bp mo : Z) (r : smrec) (st : nb_state ptr) (pad : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> slots_EL ST OUT A FF bp 4 s ->
rw_cells asegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st pad) -> nb_submodeID st = mo -> smrec_at mo = Some r ->
rw_cells asegs m (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))] ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
lib_consts m -> nb_tabs_acc m -> client_consts m ->
lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' t3' t4' t5' t6' : word),
frm0 fc'
/\ ms = MS (mkR (Z_to_bv 64 RA_nbf_mc2) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (ST + 1528)) (Z_to_bv 64 (OUT + 320)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 10) (Z_to_bv 64 80) (Z_to_bv 64 bp) (Z_to_bv 64 40) (Z_to_bv 64 0)
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2047))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_multicomb) fc' None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_nbf_mc1) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2047))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbf_mc1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL SLE CFG EMO SAT EXP OBS S8 SPOS SLO SOFF LC NTA CC LO LOS SPH MI FRM.
unfold RA_nbf_mc1, RA_nbf_mc2, NBF_multicomb, NBSTATE_SIZEOF, nb_cfg_cells in *. unfold hidp in SOFF. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xa1b00)) with (Z_to_bv 64 0xa1b00) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. assert (OF : offsh []) by exact I.
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SLE.
destruct SLE as (E0 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192
& E224 & E240 & E248 & E256 & E272 & E280 & E288 & E296 & E304 & E312 & E336).
subst w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w224 w240 w248 w256 w272 w280 w288 w296 w304 w312 w336.
unfold slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (smrec_facts mo r SAT) as (INR & MO1 & EP & SP0 & SP1 & SP8 & LORD & SMC).
unfold IMG_TOP in SP1.
pose proof (SMC m LC) as ROW. destruct NTA as (NTM & NTR). rewrite Forall_forall in NTR. pose proof (NTR r INR) as OBR.
unfold NB_SUBMODES_PTR, A_nb_mode in *.
unfold smrec_cells in ROW. cbv zeta in ROW.
set (SP := smr_ptr r) in *.
ato 0xa1b30. astep. rewrite sx32_small by (unfold int31; lia). rewrite ?(Z.mod_small (nb_submodeID st)) by lia.
ato 0xa1b38. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite EMO.
chk_hint NTM.
ato 0xa1b48.
rewrite (shb_zero asegs _ 981760 208 (981792 + mo * 8) (proj2 (proj2 NTM)) ltac:(lia) ltac:(clear - MO1; Z.div_mod_to_equations; lia)).
change (bv_unsigned z8) with 0.
ato 0xa1b4c.
pose proof (sub_ptr_read m mo LC ltac:(lia)) as RD.
rewrite EP in RD. unfold NB_SUBMODES_PTR, A_nb_mode in RD. fold SP in RD.
replace (981760 + 32 + 8 * mo) with (981792 + mo * 8) in RD by lia.
astep. clear RD.
ato 0xa1b58. rewrite ?(Z.mod_small (SP + 80)) by lia.
chk_hint OBR.
ato 0xa5388.
apply evt_done. do 9 eexists. split; [exact FRM|]. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition NBF_PC_J : Z := 0xa10fc.
Definition NBG_PC : Z := 0xa1248.

Definition R_G (usp ST SF FF sub : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3 t4 t5 t6.

Lemma nbf_3m : forall (usp ST OUT FF SF olp bp : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 RA_nbf_mc2) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2047))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 NBF_PC_J) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_nbf_mc2) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2047))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbf_mc2)) fc None m (seg_rom asegs)).
Proof.
intros. unfold RA_nbf_mc2, NBF_PC_J.
replace (ret_pc (Z_to_bv 64 0xa1b90)) with (Z_to_bv 64 0xa1b90) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. apply evt_done. reflexivity.
Qed.

Lemma nbf_3 : forall (usp lo ST OUT A FF SF olp bp : Z) (gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> slots_EL ST OUT A FF bp 4 s ->
rw_cells asegs m (ST + 12) [C4 (Z_to_bv 64 0)] ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
client_consts m ->
stk asegs m lo (usp + -544) -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
frm0 fc' /\ munch [(usp + -544, usp + -200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (usp + -544) (slot_cells (sset 304 (Z_to_bv 64 (ST + 2168)) (sset 312 (Z_to_bv 64 (ST + 2040)) s)))
/\ ms = MS (R_G usp ST SF FF 0 gp tp xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F' (Z_to_bv 64 NBG_PC) fc' None m' (seg_rom asegs))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) s5 (Z_to_bv 64 (ST + 2047))
(Z_to_bv 64 40) (Z_to_bv 64 olp) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 NBF_PC_J) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL SLE CL OBS S8 SPOS SLO SOFF CC ST0 LO LOS SPH MI FRM.
unfold NBF_PC_J, NBG_PC, R_G, NBSTATE_SIZEOF in *. unfold hidp in SOFF. unfold SH_LO, SH_HI in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -544, usp + -200)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -544, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
unfold slots_EL in SLE; cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SLE.
destruct SLE as (E0 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184 & E192
& E224 & E240 & E248 & E256 & E272 & E280 & E288 & E296 & E304 & E312 & E336).
subst w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w224 w240 w248 w256 w272 w280 w288 w296 w304 w312 w336.
unfold slot_cells in SL. cbn in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
ato 0xa1208.
ato 0xa1248.
apply evt_done. do 18 eexists. split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|].
split; [exact SL|]. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbg_lspi10 : forall (OLD NEW IQ usp lo sub : Z) (os ns qs : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
aobj asegs m OLD 40 -> aobj asegs m NEW 40 -> aobj asegs m IQ 40 ->
OLD mod 4 = 0 -> NEW mod 4 = 0 -> IQ mod 4 = 0 -> 0 < OLD -> 0 < NEW ->
rw_cells asegs m OLD (f32 os) -> length os = 10%nat -> rw_cells asegs m NEW (f32 ns) -> length ns = 10%nat ->
rw_cells asegs m IQ (f32 qs) -> length qs = 10%nat ->
(IQ + 40 <= SH_LO \/ SH_HI <= IQ) -> IMG_TOP <= IQ ->
(IQ + 40 <= lo \/ usp <= IQ) -> (OLD + 40 <= lo \/ usp <= OLD) -> (NEW + 40 <= lo \/ usp <= NEW) ->
(IQ + 40 <= OLD \/ OLD + 40 <= IQ) -> (IQ + 40 <= NEW \/ NEW + 40 <= IQ) ->
client_consts m -> stk asegs m lo usp -> lo <= usp - 64 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (qs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(IQ, IQ + 40); (usp + -64, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ rw_cells asegs m' IQ (f32 qs') /\ length qs' = 10%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 10) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom asegs)).
Proof.
intros until m. intros O1 O2 O3 A1 A2 A3 P1 P2 C1 L1 C2 L2 C3 L3 SH IMG D1 D2 D3 D4 D5 CC ST LO LOS SPH MI FRM.
eapply evt_mono.
- eapply (lsp_interpolate_stmt OLD NEW IQ usp lo sub 10%nat os ns qs); try eassumption; try (cbn; lia).
- intros ms' POST. exact POST.
Qed.

Definition RA_nbg_lspi : Z := 0xa1268.
Definition RA_nbg_l2l : Z := 0xa127c.
Definition NBG_lsp_to_lpc : Z := 0xa95ec.

Lemma nbg_1 : forall (usp lo ST FF SF sub : Z) (os ns qs : list word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v312 s = Z_to_bv 64 (ST + 2040) -> v160 s = Z_to_bv 64 (FF + 160) -> 0 <= sub < 4 ->
rw_cells asegs m (ST + 2040) (f32 os) -> length os = 10%nat -> aobj asegs m (ST + 2040) 40 ->
rw_cells asegs m (FF + 160) (f32 ns) -> length ns = 10%nat -> aobj asegs m (FF + 160) 40 ->
rw_cells asegs m (FF + 992) (f32 qs) -> length qs = 10%nat -> aobj asegs m (FF + 992) 40 ->
ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
client_consts m -> stk asegs m lo (usp + -544) -> lo <= usp - 544 - 64 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (qs' : list word),
frm0 fc' /\ munch [(FF + 992, FF + 1032); (usp + -608, usp + -544)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (FF + 992) (f32 qs') /\ length qs' = 10%nat
/\ ms = MS (mkR (Z_to_bv 64 RA_nbg_l2l) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (FF + 992)) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 10) (Z_to_bv 64 0) a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3' t4' t5' t6')
F' (Z_to_bv 64 NBG_lsp_to_lpc) fc' None m' (seg_rom asegs))
(MS (R_G usp ST SF FF sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 NBG_PC) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E312 E160 SUB OS LOS0 OBO NS LNS OBN QS LQS OBQ S8 SPOS SLO SFA F0 F64 FLO FTOP FSH CC ST0 LO LOS SPH MI FRM.
unfold NBG_PC, R_G, RA_nbg_l2l, NBG_lsp_to_lpc, NBSTATE_SIZEOF in *. unfold hidp in SFA, FSH.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (munch_refl [(FF + 992, FF + 1032); (usp + -608, usp + -544)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(FF + 992, FF + 1032); (usp + -608, usp + -544)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v312 v160] in E312, E160. subst w312 w160.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
ato 0xa1264. astep.
call (nbg_lspi10 (ST + 2040) (FF + 160) (FF + 992) (usp + -544) lo sub os ns qs).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; lia).
ato 0xa95ec.
lazymatch goal with H : rw_cells asegs ?mc (FF + 992) (f32 ?l) |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename l into qs1; rename H into QS1 end.
apply evt_done. do 14 eexists. exists qs1. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [exact QS1|]. split; [assumption| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbg_iir10 : forall (PX PD PM usp lo : Z) (xs den mem0 : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
length xs = 40%nat -> length den = 10%nat -> length mem0 = 10%nat ->
aobj asegs m PX 160 -> aobj asegs m PD 40 -> aobj asegs m PM 40 -> PX mod 4 = 0 -> PD mod 4 = 0 -> PM mod 4 = 0 ->
lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 ->
(PX + 160 <= SH_LO \/ SH_HI <= PX) -> (PM + 40 <= SH_LO \/ SH_HI <= PM) ->
(PX + 160 <= lo \/ usp <= PX) -> (PM + 40 <= lo \/ usp <= PM) -> (PD + 40 <= lo \/ usp <= PD) ->
(PD + 40 <= PM \/ PM + 40 <= PD) -> (PX + 160 <= PM \/ PM + 40 <= PX) -> (PX + 160 <= PD \/ PD + 40 <= PX) ->
rw_cells asegs m PX (f32 xs) -> rw_cells asegs m PD (f32 den) -> rw_cells asegs m PM (f32 mem0) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= PX -> IMG_TOP <= PM -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (ys mv : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(PX, PX + 160); (PM, PM + 40); (usp + -80, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ length ys = 40%nat /\ rw_cells asegs m' PX (f32 ys)
/\ length mv = 10%nat /\ rw_cells asegs m' PM (f32 mv) /\ rw_cells asegs m' PD (f32 den))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PX) (Z_to_bv 64 PD) (Z_to_bv 64 PX) (Z_to_bv 64 40) (Z_to_bv 64 10) (Z_to_bv 64 PM) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_iir_mem16) fc None m (seg_rom asegs)).
Proof.
intros until m. intros LX LD LM OX OD OM X4 D4 M4 LO LOS SPH XSH MSH XAP MAP DAP SDM SXM SXD CX CD CM FRM ST XI MI' CC MI.
assert (LMEM : length mem0 = length den) by (rewrite LM, LD; reflexivity).
assert (EN : Z.of_nat (length xs) = 40) by (rewrite LX; reflexivity).
assert (EO : Z.of_nat (length den) = 10) by (rewrite LD; reflexivity).
assert (N1 : 1 <= Z.of_nat (length xs) < 2^31) by (rewrite EN; lia).
assert (ORD : 2 <= Z.of_nat (length den) < 2^31) by (rewrite EO; lia).
pose proof (iir_mem16_walk_ip xs den mem0 PX PD PM usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LMEM N1 ORD
ltac:(rewrite EN; exact OX) ltac:(rewrite EO; exact OD) ltac:(rewrite EO; exact OM) X4 D4 M4 LO LOS SPH
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
Definition RA_nbg_iir : Z := 0xa12ec.
Definition RA_nbg_cpy : Z := 0xa1300.

Lemma nbg_2 : forall (usp lo ST OUT FF SF sub : Z) (aks pg xo iq msp : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v304 s = Z_to_bv 64 (ST + 2168) -> v168 s = Z_to_bv 64 OUT -> v240 s = Z_to_bv 64 0 ->
v112 s = Z_to_bv 64 (FF + 240) -> 0 <= sub < 4 ->
rw_cells asegs m (FF + 240) (f32 aks) -> length aks = 10%nat ->
rw_cells asegs m (ST + 2168) (f32 pg) -> length pg = 4%nat ->
rw_cells asegs m (OUT + 160 * sub) (f32 xo) -> length xo = 40%nat -> aobj asegs m (OUT + 160 * sub) 160 -> OUT mod 4 = 0 -> IMG_TOP <= OUT ->
hidp (OUT + 160 * sub + 160 <= SH_LO \/ SH_HI <= OUT + 160 * sub) -> OUT + 160 * sub + 160 <= lo ->
hidp (ST + NBSTATE_SIZEOF <= OUT + 160 * sub \/ OUT + 160 * sub + 160 <= ST) ->
hidp (OUT + 160 * sub + 160 <= FF \/ FF + 2048 <= OUT + 160 * sub) -> hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
rw_cells asegs m (ST + 2080) (f32 iq) -> length iq = 10%nat -> rw_cells asegs m (ST + 2120) (f32 msp) -> length msp = 10%nat ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
IMG_TOP <= ST ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
client_consts m -> stk asegs m lo (usp + -544) -> lo <= usp - 544 - 80 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (pg' xo' msp' : list word),
frm0 fc' /\ munch [(ST + 2168, ST + 2184); (OUT + 160 * sub, OUT + 160 * sub + 160); (ST + 2120, ST + 2160); (usp + -624, usp + -544)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (ST + 2168) (f32 pg') /\ length pg' = 4%nat /\ rw_cells asegs m' (OUT + 160 * sub) (f32 xo') /\ length xo' = 40%nat
/\ rw_cells asegs m' (ST + 2120) (f32 msp') /\ length msp' = 10%nat /\ rw_cells asegs m' (ST + 2080) (f32 iq) /\ rw_cells asegs m' (FF + 240) (f32 aks)
/\ ms = MS (mkR (Z_to_bv 64 RA_nbg_cpy) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 40) a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_memcpy) fc' None m' (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_nbg_l2l) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbg_l2l)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E304 E168 E240 E112 SUB AK LAK PG LPG XO LXO OBX OUT4 OTOP OSH OLO SOA OFA SFA IQ LIQ MSP LMSP OBS S8 SPOS SLO SOFF SIMG F0 F64 FLO FTOP FSH
CC ST0 LO LOS SPH MI FRM.
unfold RA_nbg_l2l, RA_nbg_cpy, NBF_memcpy, NBSTATE_SIZEOF in *. unfold hidp in SOFF, FSH, OSH, SOA, OFA, SFA. pose proof SIMG as SIMG'. unfold IMG_TOP in SIMG'.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'. pose proof OTOP as OTOP'. unfold IMG_TOP in OTOP'.
pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'. pose proof OSH as OSH'. unfold SH_LO, SH_HI in OSH'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
replace (ret_pc (Z_to_bv 64 0xa127c)) with (Z_to_bv 64 0xa127c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(ST + 2168, ST + 2184); (OUT + 160 * sub, OUT + 160 * sub + 160); (ST + 2120, ST + 2160); (usp + -624, usp + -544)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(ST + 2168, ST + 2184); (OUT + 160 * sub, OUT + 160 * sub + 160); (ST + 2120, ST + 2160); (usp + -624, usp + -544)])
by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v304 v168 v240 v112] in E304, E168, E240, E112. subst w304 w168 w240 w112.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
destruct aks as [|k0 [|k1 [|k2 [|k3 [|k4 [|k5 [|k6 [|k7 [|k8 [|k9 [|k10 aks]]]]]]]]]]]; cbn [length] in LAK; try discriminate.
rewrite !f32_cons, f32_nil in AK.
do 5 (ato 0xa1298; astep; sh_if).
ato 0xa129c.
ato 0xa12a0. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite ?Z.mod_small by lia.
ato 0xa12a8.
replace (ST + 2168 + sub * 4) with (ST + 2168 + 4 * sub) by lia.
destruct (nbe_f32_split3 _ (ST + 2168) pg sub PG ltac:(lia)) as (P1 & P2 & P3). clear PG.
remember (firstn (Z.to_nat sub) pg) as l1 eqn:EL1. remember (skipn (S (Z.to_nat sub)) pg) as l3 eqn:EL3.
assert (LL1 : Z.of_nat (length l1) = sub) by (subst l1; rewrite length_firstn; lia).
assert (LL3 : Z.of_nat (length l3) = 3 - sub) by (subst l3; rewrite length_skipn; lia).
clear EL1 EL3.
ato 0xa12b4. astep. chk_merge OBS 4.
ato 0xa12cc.
lazymatch goal with H : rw_cells asegs ?mc (ST + 2168 + 4 * sub) [C4 ?w] |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PG : rw_cells asegs mc (ST + 2168) (f32 (l1 ++ w :: l3))) by (apply nbe_f32_join3; [exact P1| rewrite LL1; exact H| rewrite LL1; exact P3]);
assert (LPG' : length (l1 ++ w :: l3) = 4%nat) by (rewrite length_app; cbn [length]; lia);
set (pg1 := l1 ++ w :: l3) in *; clearbody pg1; clear H end.
clear P1 P3 l1 l3 LL1 LL3 LPG.
ato 0xa12e8.
replace (OUT + sub * 160) with (OUT + 160 * sub) by lia.
astep.
call (nbg_iir10 (OUT + 160 * sub) (ST + 2080) (ST + 2120) (usp + -544) lo xo iq msp).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; lia).
{ exact (aobj_munch asegs _ m m0 _ 160 OBX MU (shfree_of_aobj asegs _ m _ 160 OF OBX)). }
{ pose proof (aobj_sub asegs _ _ _ (ST + 2080) 40 OBS ltac:(lia) ltac:(lia)) as OB'. exact (aobj_munch asegs _ m m0 _ 40 OB' MU (shfree_of_aobj asegs _ m _ 40 OF OB')). }
{ pose proof (aobj_sub asegs _ _ _ (ST + 2120) 40 OBS ltac:(lia) ltac:(lia)) as OB'. exact (aobj_munch asegs _ m m0 _ 40 OB' MU (shfree_of_aobj asegs _ m _ 40 OF OB')). }
{ exact (conj G1 (conj G2 (conj G3 G4))). }
ato 0x66314.
apply evt_done. do 15 eexists. exists pg1, x18, x19.
split; [exact PC0|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|].
split; [exact PG|]. split; [exact LPG'|]. split; [exact PC2|]. split; [exact PC1|]. split; [exact PC4|]. split; [exact PC3|].
split; [exact POST|]. split; [rewrite !f32_cons, f32_nil; exact AK|]. reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition NBH_PC : Z := 0xa1320.

Lemma nbg_3 : forall (usp ST FF SF sub : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
0 <= sub < 4 ->
evt asegs (fun ms => exists (a0' : word),
(sub < 3 /\ ms = MS (R_G usp ST SF FF (sub + 1) gp tp (Z_to_bv 64 RA_nbg_cpy) t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 NBG_PC) fc None m (seg_rom asegs))
\/ (sub = 3 /\ ms = MS (R_G usp ST SF FF 4 gp tp (Z_to_bv 64 RA_nbg_cpy) t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 NBH_PC) fc None m (seg_rom asegs)))
(MS (mkR (Z_to_bv 64 RA_nbg_cpy) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 (FF + 240)) (Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 (FF + 284)) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbg_cpy)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SUB.
unfold RA_nbg_cpy, NBG_PC, NBH_PC, R_G.
replace (ret_pc (Z_to_bv 64 0xa1300)) with (Z_to_bv 64 0xa1300) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. astep.
destruct (Z.eq_dec sub 3) as [S3 | S3].
- subst sub. astep. try sh_if. ato 0xa1320. apply evt_done. eexists. right. split; [reflexivity| reflexivity].
- astep. sh_if. apply evt_done. eexists. left. split; [lia| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbh_hp160 : forall (PX PM usp lo filtID : Z) (xs : list word) (m0 m1 : word)
(ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
length xs = 160%nat -> aobj asegs m PX 640 -> aobj asegs m PM 8 -> aobj asegs m 0x24780 60 -> aobj asegs m 0x24720 60 -> PX mod 4 = 0 -> PM mod 4 = 0 ->
lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(PX + 640 <= SH_LO \/ SH_HI <= PX) -> (PM + 8 <= SH_LO \/ SH_HI <= PM) -> (PX + 640 <= lo \/ usp <= PX) -> (PM + 8 <= lo \/ usp <= PM) ->
(PX + 640 <= PM \/ PM + 8 <= PX) ->
rw_cells asegs m PX (f32 xs) -> rw_cells asegs m PM (f32 [m0; m1]) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= PX -> IMG_TOP <= PM -> client_consts m -> mem_inv asegs m -> filtID = 1 \/ filtID = 3 ->
evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (ys : list word) (h0 h1 : word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(PX, PX + 640); (PM, PM + 8); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ length ys = 160%nat /\ rw_cells asegs m' PX (f32 ys) /\ rw_cells asegs m' PM (f32 [h0; h1]))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PX) (Z_to_bv 64 PX) (Z_to_bv 64 160) (Z_to_bv 64 filtID) (Z_to_bv 64 PM) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_highpass) fc None m (seg_rom asegs)).
Proof.
intros until m. intros LX OX OM OP OZ X4 M4 LO LOS SPH XSH MSH XAP MAP SEP CX CM FRM ST XI MI' CC MI FID.
assert (EN : Z.of_nat (length xs) = 160) by (rewrite LX; reflexivity).
assert (N1 : 1 <= Z.of_nat (length xs) < 2^31) by (rewrite EN; lia).
pose proof (highpass_walk xs m0 m1 PX PM usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m N1
ltac:(rewrite EN; exact OX) OM OP OZ X4 M4 LO LOS SPH ltac:(rewrite EN; exact XSH) MSH ltac:(rewrite EN; exact XAP) MAP ltac:(rewrite EN; exact SEP)
filtID t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 fc CX CM FRM ST XI MI' CC MI FID) as W.
rewrite EN in W.
eapply evt_mono; [exact W|].
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & g0 & g1 & g10 & fc' & m' & EQ & MU & WM & MI2 & ST2 & FR2 & CY & CM2).
do 16 eexists. exists fc', m', (hp_ys (hp_coefs filtID) (m0, m1) xs), (fst (hp_st (hp_coefs filtID) (m0, m1) xs)), (snd (hp_st (hp_coefs filtID) (m0, m1) xs)).
rewrite EN in MU. replace (PX + 4 * 160) with (PX + 640) in MU by lia.
split; [exact EQ|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FR2|].
split; [rewrite length_hp_ys; exact LX|]. split; [exact CY| exact CM2].
Qed.

Definition NBH_PC_LV : Z := 0xa138c.

Lemma nbh_1a : forall {ptr : Type} (usp lo ST OUT FF SF : Z) (st : nb_state ptr) (pad : list byte) (xs : list word) (h0 h1 : word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v48 s = Z_to_bv 64 (ST + 2120) -> v24 s = Z_to_bv 64 FF -> v32 s = Z_to_bv 64 FF ->
v16 s = Z_to_bv 64 ST -> v40 s = Z_to_bv 64 (ST + 2047) -> v168 s = Z_to_bv 64 OUT ->
rw_cells asegs m (ST + 2948) (nb_tail_cells st pad) ->
rw_cells asegs m OUT (f32 xs) -> length xs = 160%nat -> aobj asegs m OUT 640 -> OUT mod 4 = 0 -> IMG_TOP <= OUT ->
hidp (OUT + 640 <= SH_LO \/ SH_HI <= OUT) -> OUT + 640 <= lo -> hidp (ST + NBSTATE_SIZEOF <= OUT \/ OUT + 640 <= ST) ->
rw_cells asegs m (ST + 2160) (f32 [h0; h1]) -> aobj asegs m 0x24780 60 -> aobj asegs m 0x24720 60 ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP <= ST ->
client_consts m -> stk asegs m lo (usp + -544) -> lo <= usp - 544 - 16 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ys : list word) (h0' h1' : word),
frm0 fc' /\ munch [(OUT, OUT + 640); (ST + 2160, ST + 2168); (usp + -560, usp + -544)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' OUT (f32 ys) /\ length ys = 160%nat /\ rw_cells asegs m' (ST + 2160) (f32 [h0'; h1'])
/\ ms = MS (mkR xra' (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 FF) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3' t4' t5' t6')
F' (Z_to_bv 64 NBH_PC_LV) fc' None m' (seg_rom asegs))
(MS (R_G usp ST SF FF 4 gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 NBH_PC) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E48 E24 E32 E16 E40 E168 TL XS LXS OBX OUT4 OTOP OSH OLO SOA HP OTP OTZ OBS S8 SPOS SLO SOFF SIMG CC ST0 LO LOS SPH MI FRM.
unfold NBH_PC, NBH_PC_LV, R_G, NBSTATE_SIZEOF, nb_tail_cells in *. unfold hidp in SOFF, OSH, SOA.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof OTOP as OTOP'. unfold IMG_TOP in OTOP'. pose proof SIMG as SIMG'. unfold IMG_TOP in SIMG'.
pose proof OSH as OSH'. unfold SH_LO, SH_HI in OSH'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(OUT, OUT + 640); (ST + 2160, ST + 2168); (usp + -560, usp + -544)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(OUT, OUT + 640); (ST + 2160, ST + 2168); (usp + -560, usp + -544)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v48 v24 v32 v16 v40 v168] in E48, E24, E32, E16, E40, E168. subst w48 w24 w32 w16 w40 w168.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
ato 0xa134c. astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
-
apply evt_done. do 22 eexists. split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|].
split; [exact XS|]. split; [exact LXS|]. split; [exact HP| reflexivity].
- ato 0xa136c. astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
+ ato 0xa1388. astep.
call (nbh_hp160 OUT (ST + 2160) (usp + -544) lo 1 xs h0 h1).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; lia).
{ exact (aobj_sub asegs _ _ _ (ST + 2160) 8 OBS ltac:(lia) ltac:(lia)). }
lazymatch goal with H : rw_cells asegs ?mc OUT (f32 ?l) |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename l into ys1; rename H into YS1 end.
apply evt_done. do 19 eexists. exists ys1. do 2 eexists. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
split; [exact YS1|]. split; [eassumption|]. split; [eassumption| reflexivity].
+ ato 0xa1388. astep.
call (nbh_hp160 OUT (ST + 2160) (usp + -544) lo 3 xs h0 h1).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; lia).
{ exact (aobj_sub asegs _ _ _ (ST + 2160) 8 OBS ltac:(lia) ltac:(lia)). }
lazymatch goal with H : rw_cells asegs ?mc OUT (f32 ?l) |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename l into ys1; rename H into YS1 end.
apply evt_done. do 19 eexists. exists ys1. do 2 eexists. split; [eassumption|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
split; [exact YS1|]. split; [eassumption|]. split; [eassumption| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition RA_nbh_cpy : Z := 0xa1458.

Lemma nbh_1b : forall (usp lo ST FF SF : Z) (lv : list word)
(gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v312 s = Z_to_bv 64 (ST + 2040) -> v160 s = Z_to_bv 64 (FF + 160) ->
rw_cells asegs m (ST + 2192) (f32 lv) -> length lv = 3%nat ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP <= ST ->
client_consts m -> stk asegs m lo (usp + -544) -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (lv' : list word),
frm0 fc' /\ munch [(ST + 2192, ST + 2204)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (ST + 2192) (f32 lv') /\ length lv' = 3%nat
/\ ms = MS (mkR (Z_to_bv 64 RA_nbh_cpy) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 (ST + 2040)) (Z_to_bv 64 (FF + 160)) (Z_to_bv 64 40) a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 FF) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3' t4' t5' t6')
F' (Z_to_bv 64 NBF_memcpy) fc' None m' (seg_rom asegs))
(MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 FF) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3 t4 t5 t6)
F (Z_to_bv 64 NBH_PC_LV) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E312 E160 LV LLV OBS S8 SPOS SLO SOFF SIMG CC ST0 LO LOS SPH MI FRM.
unfold NBH_PC_LV, RA_nbh_cpy, NBF_memcpy, NBSTATE_SIZEOF in *. unfold hidp in SOFF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof SIMG as SIMG'. unfold IMG_TOP in SIMG'.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(ST + 2192, ST + 2204)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(ST + 2192, ST + 2204)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v312 v160] in E312, E160. subst w312 w160.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
destruct lv as [|l0 [|l1 [|l2 [|]]]]; cbn [length] in LLV; try discriminate. clear LLV.
rewrite !f32_cons, f32_nil in LV.
ato 0xa13d8. astep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
all: ato 0xa1414. all: astep.
all: lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
all: ato 0xa1438. all: astep.
all: lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
all: ato 0x66314.
all: lazymatch goal with H : rw_cells asegs ?mc (?S0 + 2192) [C4 ?x; C4 ?y; C4 ?z] |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_done; do 15 eexists; exists [x; y; z]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [rewrite !f32_cons, f32_nil; exact H|]; split; [reflexivity| reflexivity] end.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma nbh_2 : forall (usp lo ST FF SF bp idx first cl : Z) (rest : list byte) (lol lp lpg : word) (pgb : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s : nbslots) F fc (m : mem),
rw_cells asegs m (usp + -544) (slot_cells s) -> v8 s = Z_to_bv 64 (ST + 8) -> v144 s = Z_to_bv 64 (Z.shiftr (ST + 12) 3 + SHB) -> v192 s = Z_to_bv 64 bp ->
v72 s = Z_to_bv 64 (Z.shiftr (ST + 2208) 3 + SHB) -> 17 <= bp <= 144 ->
rw_cells asegs m (ST + 8) [C4 (Z_to_bv 64 first); C4 (Z_to_bv 64 cl)] -> rw_cells asegs m (ST + 20) [C4 lol] ->
rw_cells asegs m (ST + 2204) [C4 lp; C4 lpg] -> rw_cells asegs m (ST + 2212) (f32 pgb) -> length pgb = 3%nat ->
rw_cells asegs m (ST + 2224) [C4 (Z_to_bv 64 idx)] -> 0 <= idx <= 2 ->
rw_cells asegs m SF (nbd_shadow SC_F rest) -> SF = Z.shiftr FF 3 + SHB -> SH_LO <= SF -> SF + 256 <= SH_HI ->
0 < FF -> FF mod 64 = 0 -> FF + 2048 <= lo -> IMG_TOP <= FF -> hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
aobj asegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) -> IMG_TOP <= ST ->
hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST) ->
client_consts m -> stk asegs m lo (usp + -544) -> lo <= usp - 544 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
(lol' lpg' : word) (pgb' : list word),
frm0 fc' /\ munch [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (usp + -544)
/\ rw_cells asegs m' (ST + 8) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\ rw_cells asegs m' (ST + 20) [C4 lol']
/\ rw_cells asegs m' (ST + 2204) [C4 (Z_to_bv 64 bp); C4 lpg'] /\ rw_cells asegs m' (ST + 2212) (f32 pgb') /\ length pgb' = 3%nat
/\ rw_cells asegs m' (ST + 2224) [C4 (Z_to_bv 64 (if 2 <? idx + 1 then 0 else idx + 1))]
/\ rw_cells asegs m' SF (nbd_shadow SC_X rest)
/\ ms = MS (mkR (Z_to_bv 64 RA_nbh_cpy) (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 FF) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3' t4' t5' t6')
F' (Z_to_bv 64 PC_NBD_X) fc' None m' (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_nbh_cpy) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 ST) (Z_to_bv 64 FF) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (FF + 992))
(Z_to_bv 64 (FF + 244)) (Z_to_bv 64 FF) (Z_to_bv 64 SHB) (Z_to_bv 64 0) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbh_cpy)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL E8 E144 E192 E72 BP HDR LOL LPP PGB LPGB IDX HIDX SH ESF SF0 SF1 F0 F64 FLO FTOP FSH OBS S8 SPOS SLO SOFF SIMG SFA
CC ST0 LO LOS SPH MI FRM.
unfold RA_nbh_cpy, PC_NBD_X, NBSTATE_SIZEOF in *. unfold hidp in SOFF, FSH, SFA.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof SIMG as SIMG'. unfold IMG_TOP in SIMG'. pose proof FTOP as FTOP'. unfold IMG_TOP in FTOP'.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof SF0 as SF0u. pose proof SF1 as SF1u. unfold SH_LO, SH_HI in SF0u, SF1u.
replace (ret_pc (Z_to_bv 64 0xa1458)) with (Z_to_bv 64 0xa1458) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof ST0 as (STa & STb & _).
destruct s as [w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336].
cbn [v8 v144 v192 v72] in E8, E144, E192, E72. subst w8 w144 w192 w72.
unfold slot_cells in SL. cbn [v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336] in SL.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
unfold nbd_shadow, nbd_shadow_bytes, SC_F, sh_run, bF1, bF2, bF3, bF8, b04, z8 in SH. cbn [map repeat app sc_top sc_lpc sc_main sc_innov2 sc_iq] in SH.
destruct pgb as [|p0 [|p1 [|p2 [|]]]]; cbn [length] in LPGB; try discriminate. clear LPGB.
rewrite !f32_cons, f32_nil in PGB.
ato 0xa149c.
assert (HI3 : idx = 0 \/ idx = 1 \/ idx = 2) by lia.
destruct HI3 as [-> | [-> | ->]].
all: ato 0xa14d0.
all: rewrite ?sx32_small by (unfold int31; lia).
all: ato 0xa14e4.
all: rewrite ?Z.shiftl_mul_pow2 by lia.
all: change (2 ^ 2) with 4.
all: rewrite ?Z.mod_small by lia.
- ato 0xa1528.
apply (munch_weaken _ [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)]) in MU;
[| intros x Hx; cbn [outside] in *; lia].
clear OF.
ato 0xa1a1c.
lazymatch goal with |- evt _ _ (MS _ ?F1 _ ?fcx _ ?mc _) =>
lazymatch goal with L1 : rw_cells asegs mc (ST + 20) [C4 ?lv] |- _ =>
lazymatch goal with L2 : rw_cells asegs mc (ST + 2204) [C4 _; C4 ?lg] |- _ =>
lazymatch goal with L3 : rw_cells asegs mc (ST + 2212) [C4 ?q0; C4 ?q1; C4 ?q2] |- _ =>
apply evt_done; exists mc, F1, fcx; do 15 eexists; exists lv, lg, [q0; q1; q2];
split; [eassumption|]; split; [exact MU|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [exact HDR|]; split; [exact L1|]; split; [exact L2|]; split; [rewrite !f32_cons, f32_nil; exact L3|]; split; [reflexivity|];
split; [exact IDX|]; split; [exact SH|]; reflexivity end end end end.
- ato 0xa1528.
apply (munch_weaken _ [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)]) in MU;
[| intros x Hx; cbn [outside] in *; lia].
clear OF.
ato 0xa1a1c.
lazymatch goal with |- evt _ _ (MS _ ?F1 _ ?fcx _ ?mc _) =>
lazymatch goal with L1 : rw_cells asegs mc (ST + 20) [C4 ?lv] |- _ =>
lazymatch goal with L2 : rw_cells asegs mc (ST + 2204) [C4 _; C4 ?lg] |- _ =>
lazymatch goal with L3 : rw_cells asegs mc (ST + 2212) [C4 ?q0; C4 ?q1; C4 ?q2] |- _ =>
apply evt_done; exists mc, F1, fcx; do 15 eexists; exists lv, lg, [q0; q1; q2];
split; [eassumption|]; split; [exact MU|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [exact HDR|]; split; [exact L1|]; split; [exact L2|]; split; [rewrite !f32_cons, f32_nil; exact L3|]; split; [reflexivity|];
split; [exact IDX|]; split; [exact SH|]; reflexivity end end end end.
- ato 0xa1528.
apply (munch_weaken _ [(ST + 8, ST + 16); (ST + 20, ST + 24); (ST + 2204, ST + 2228); (SF + 20, SF + 129)]) in MU;
[| intros x Hx; cbn [outside] in *; lia].
clear OF.
ato 0xa1a1c.
lazymatch goal with |- evt _ _ (MS _ ?F1 _ ?fcx _ ?mc _) =>
lazymatch goal with L1 : rw_cells asegs mc (ST + 20) [C4 ?lv] |- _ =>
lazymatch goal with L2 : rw_cells asegs mc (ST + 2204) [C4 _; C4 ?lg] |- _ =>
lazymatch goal with L3 : rw_cells asegs mc (ST + 2212) [C4 ?q0; C4 ?q1; C4 ?q2] |- _ =>
apply evt_done; exists mc, F1, fcx; do 15 eexists; exists lv, lg, [q0; q1; q2];
split; [eassumption|]; split; [exact MU|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [exact HDR|]; split; [exact L1|]; split; [exact L2|]; split; [rewrite !f32_cons, f32_nil; exact L3|]; split; [reflexivity|];
split; [exact IDX|]; split; [exact SH|]; reflexivity end end end end.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

