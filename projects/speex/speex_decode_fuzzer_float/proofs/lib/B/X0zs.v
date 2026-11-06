(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X09f X09e.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0x2 X0zp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition RA_nbd_smalloc : Z := 0xa1750.
Definition PC_stack_malloc_5 : Z := 0x517b4.

Definition nbd_saves (F : bvmap 5 word) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 (reg_get F (Z_to_bv 5 27)); C8 (reg_get F (Z_to_bv 5 26)); C8 (reg_get F (Z_to_bv 5 25)); C8 (reg_get F (Z_to_bv 5 24));
C8 (reg_get F (Z_to_bv 5 23)); C8 (reg_get F (Z_to_bv 5 22)); C8 (reg_get F (Z_to_bv 5 21)); C8 (reg_get F (Z_to_bv 5 20));
C8 (reg_get F (Z_to_bv 5 19)); C8 (reg_get F (Z_to_bv 5 18)); C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8));
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma nbd_w1 : forall (usp lo ST A OUT : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk bsegs m lo usp -> lo <= usp - 576 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j1 j2 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_nbd_smalloc) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 1088) (Z_to_bv 64 gB_shadow_memory_dynamic_address) (Z_to_bv 64 1) a3 a4 a5 a6 a7
(Z_to_bv 64 ST) (Z_to_bv 64 A) s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_stack_malloc_5) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -576, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -576)
/\ rw_cells bsegs m1 (usp + -576) ([C8 (Z_to_bv 64 0); CB 232 j1; C8 (Z_to_bv 64 OUT); CB 128 j2] ++ nbd_saves F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ST) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_nb_decode) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST0 LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_nb_decode, RA_nbd_smalloc, PC_stack_malloc_5, nbd_saves,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl [(usp + -576, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 576%nat ST0.
apply (rw_cells_split_CB bsegs _ _ [] 576 _ [] [8; 232; 8; 128; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
ato 0xa1718. astep. rewrite land_m32_al by lia.
ato 0xa1744. rewrite sx32_small by (unfold int31; lia).
ato 0x517b4.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0| exact FR].
Qed.

Lemma nbd_seg_poison : forall (sf sp1 : Z) (ra sp gp tp t0 t1 t2 s0 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(js jsl : list byte) F fc (m : mem),
rw_cells bsegs m sf [CB 256 js] -> rw_cells bsegs m (sp1 + 200) [CB 8 jsl] -> 0 <= sp1 -> sp1 + 208 < 2^64 -> 0 <= sf -> sf + 256 < 2^64 ->
(sf + 256 <= sp1 + 200 \/ sp1 + 208 <= sf) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (rs : list byte),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sp1) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-8)) (Z_to_bv 64 4) a3 (Z_to_bv 64 sf) (Z_to_bv 64 (-15)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa19f0) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 256); (sp1 + 200, sp1 + 208)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf (nbd_shadow SC_X rs)
/\ rw_cells bsegs m1 (sp1 + 200) [C8 (Z_to_bv 64 sf)])
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 sp1) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-8)) a2 a3 (Z_to_bv 64 sf) (Z_to_bv 64 (-15)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa17c4) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FRS FSL SP0 SP1 SF0 SF1 APT MI.
unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8 in *. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 256); (sp1 + 200, sp1 + 208)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
apply (rw_cells_split_CB bsegs _ _ [] 256 _ [] (repeat 1%nat 136 ++ [120%nat])) in FRS; [| reflexivity].
cbn [mk_CB_cells app repeat] in FRS.
ato 0xa19f0.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRS| exact FSL].
Qed.

Definition nbd_fhdr (rest : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x205cf); C8 (Z_to_bv 64 0xa16a8); CB 2016 rest].

Definition nbd_frame_w2 (ST A OUT f sf : Z) (ja jb jc jd je jf jg jh : list byte) (sv : list cell) : list cell :=
[C8 (Z_to_bv 64 0); CB 40 ja; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (ST + 2047)); CB 16 jb; C8 (Z_to_bv 64 ST); CB 72 jc;
C8 (Z_to_bv 64 (ST + 2032)); C8 (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)); CB 8 jd; C8 (Z_to_bv 64 (ST + 2184)); C8 (Z_to_bv 64 sf); CB 32 je;
C8 (Z_to_bv 64 OUT); CB 40 jf; C8 (Z_to_bv 64 A); CB 8 jg; C8 (Z_to_bv 64 0); CB 56 jh; C8 (Z_to_bv 64 f)] ++ sv.

Lemma nbd_w2 : forall (usp lo ST A OUT f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(sv : list cell) (j1 j2 jb js pad : list byte) (mode first cl srate log exc0 sid enh : word) F fc (m : mem),
stk bsegs m lo (usp + -576) -> lo <= usp + -576 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 2048 <= lo -> f + 2048 <= APP_TOP -> IMG_TOP_B <= f -> hidp (f + 2048 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
aobj bsegs m ST NBSTATE_SIZEOF -> ST mod 8 = 0 -> 0 < ST -> ST + NBSTATE_SIZEOF <= lo -> hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) ->
hidp (ST + NBSTATE_SIZEOF <= 0x10000 \/ IMG_TOP_B <= ST) -> hidp (ST + NBSTATE_SIZEOF <= f \/ f + 2048 <= ST) -> hidp (ST + NBSTATE_SIZEOF <= sf \/ sf + 256 <= ST) ->
0 < A < 2^47 -> length sv = 25%nat -> Forall (fun c => csize c = 8%nat) sv ->
rw_cells bsegs m (usp + -576) ([C8 (Z_to_bv 64 0); CB 232 j1; C8 (Z_to_bv 64 OUT); CB 128 j2] ++ sv) ->
rw_cells bsegs m f [CB 2040 jb] -> rw_cells bsegs m sf [CB 256 js] ->
rw_cells bsegs m ST [C8 mode; C4 first; C4 cl; C4 srate; C4 log; C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m (ST + 2032) [C8 exc0] ->
rw_cells bsegs m (ST + 2232) [C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 NB_SUBMODES_PTR); C4 sid; C4 enh] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' : word) (ja jb' jc jd je jf jg jh rb rs : list byte),
ms = MS (mkR (Z_to_bv 64 RA_nbd_smalloc) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 A) a1' (Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) (Z_to_bv 64 sf) (Z_to_bv 64 (-15)) (Z_to_bv 64 f) a7
(Z_to_bv 64 ST) (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) s7 s8 s9 (Z_to_bv 64 ST) (Z_to_bv 64 (ST + 2184)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa1ad0) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -576, usp); (f, f + 2040); (sf, sf + 256); (ST + 2032, ST + 2040)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -576)
/\ rw_cells bsegs m1 (usp + -576) (nbd_frame_w2 ST A OUT f sf ja jb' jc jd je jf jg jh sv)
/\ rw_cells bsegs m1 f (nbd_fhdr rb) /\ rw_cells bsegs m1 sf (nbd_shadow SC_X rs)
/\ rw_cells bsegs m1 ST [C8 mode; C4 first; C4 cl; C4 srate; C4 log; C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m1 (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))]
/\ rw_cells bsegs m1 (ST + 2232) [C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 NB_SUBMODES_PTR); C4 sid; C4 enh])
(MS (mkR (Z_to_bv 64 RA_nbd_smalloc) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ST) (Z_to_bv 64 A) s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbd_smalloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST0 LO LOS SPH F0 F64 FLO FAT FTOP FSH Esf OBS S8 SP0 SLO SSH SIM SFA SSA A0 LSV SVS FR FRB FRS HDR EXC CFG MI.
unfold nbd_frame_w2, nbd_fhdr, RA_nbd_smalloc, NBSTATE_SIZEOF, NB_SUBMODES_PTR in *.
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FTOP as FTOP'. unfold IMG_TOP_B in FTOP'.
pose proof (shad_range_al f 2048 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (2048 / 8) with 256 in SW. unfold SH_LO, SH_HI in SW.
pose proof (FSH : _ \/ _) as FSH'. unfold SH_LO, SH_HI in FSH'. pose proof (SFA : _ \/ _) as SFA'. pose proof (SSA : _ \/ _) as SSA'.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl [(usp + -576, usp); (f, f + 2040); (sf, sf + 256); (ST + 2032, ST + 2040)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (SFR : shfree [(usp + -576, usp); (f, f + 2040); (sf, sf + 256); (ST + 2032, ST + 2040)] ST 2968).
{ apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply shfree_cons_off; [unfold SH_LO, SH_HI; lia | lia | unfold APP_TOP; lia |].
apply (shfree_cons_sh _ _ _ _ _ f 2048); [clear - F64; Z.div_mod_to_equations; lia | rewrite Esf, shad_shiftr; lia | rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia | exact SFA' |].
apply shfree_cons_off; [pose proof (SSH : _ \/ _) as Y; unfold SH_LO, SH_HI in *; lia | lia | unfold APP_TOP; lia |]. apply shfree_nil. }
replace (ret_pc (Z_to_bv 64 0xa1750)) with (Z_to_bv 64 0xa1750) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (rw_cells_split_CB bsegs _ _ [] 2040 _ [] [8; 8; 8; 2016]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0)] 232 _ ([C8 (Z_to_bv 64 OUT); CB 128 j2] ++ sv) [40; 8; 8; 8; 16; 8; 72; 8; 8; 8; 8; 8; 32]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
change ([C8 (Z_to_bv 64 0)] ++ _ ++ [C8 (Z_to_bv 64 OUT); CB 128 j2] ++ sv) with
((C8 (Z_to_bv 64 0) :: mk_CB_cells [40; 8; 8; 8; 16; 8; 72; 8; 8; 8; 8; 8; 32]%nat j1 ++ [C8 (Z_to_bv 64 OUT)]) ++ CB 128 j2 :: sv) in FR.
apply (rw_cells_split_CB bsegs _ _ (C8 (Z_to_bv 64 0) :: mk_CB_cells [40; 8; 8; 8; 16; 8; 72; 8; 8; 8; 8; 8; 32]%nat j1 ++ [C8 (Z_to_bv 64 OUT)]) 128 _ sv
[40; 8; 8; 8; 56; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
bato 0xa1764. astep. sh_if.
bato 0xa17c4.
rewrite <- Esf.
lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?cs :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: cs :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [cs] ++ rest) in FR end.
apply rw_cells_app in FR as [FRa FR']. apply rw_cells_app in FR' as [FSL FRb].
cbn [cells_size csize Nat.add] in FSL, FRb. change (Z.of_nat 200) with 200 in FSL, FRb. change (Z.of_nat 8) with 8 in FRb.
replace (usp + -576 + 200 + 8) with (usp + -576 + 208) in FRb by lia.
call (nbd_seg_poison sf (usp + -576)).
{ exact FRS. } { exact FSL. } { lia. } { lia. } { unfold SHB in *; lia. } { lia. } { left. lia. } { assumption. }
rename PC into FRS'. rename POST into FSL'.
pose proof (rw_cells_join bsegs x (usp + -576 + 200) _ _ FSL' ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; replace (usp + -576 + 200 + 8) with (usp + -576 + 208) by lia; exact FRb)) as FR2.
pose proof (rw_cells_join bsegs x (usp + -576) _ _ FRa ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 200) with 200; exact FR2)) as FR.
clear FRa FRb FSL' FR2. cbn [app] in FR.
unfold nbd_shadow, nbd_shadow_bytes, SC_X, sh_run, bF1, bF2, bF3, bF8, b04, z8 in FRS'. cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in FRS'.
bato 0xa1ad0.
apply evt_done. do 12 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST0|]. split; [exact FR|]. split; [exact FRB|]. split; [exact FRS'|].
split; [exact HDR|]. split; [exact EXC| exact CFG].
Qed.
