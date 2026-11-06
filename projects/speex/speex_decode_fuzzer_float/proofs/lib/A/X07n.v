(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X05m X09f X06d X069.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_calloc_L : Z := 0x67e9c.
Definition e_asan_memset_L : Z := 0x667b0.
Definition RA_nbinit_calloc : Z := 0x9e854.
Definition RA_nbinit_ms1 : Z := 0x9e93c.
Definition RA_nbinit_ms2 : Z := 0x9e980.
Definition RA_nbinit_ms3 : Z := 0x9ea4c.

Definition nbinit_frame (j0 : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma nbinit_w1 : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
aobj asegs m A_speex_nb_mode 96 ->
stk asegs m lo usp -> lo <= usp - 64 -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> lib_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j0 : list byte) (xt1 xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_nbinit_calloc) (Z_to_bv 64 (usp + -64)) gp tp t0 xt1 t2 s0 s1
(Z_to_bv 64 2968) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 A_speex_nb_mode) (Z_to_bv 64 SHB) s4 (Z_to_bv 64 A_nb_mode) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_L) fc None m1 (seg_rom asegs)
/\ munch [(usp + -64, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -64)
/\ rw_cells asegs m1 (usp + -64) (nbinit_frame j0 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_speex_nb_mode) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_speex_decoder_init) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OBM ST LO LOS SPH (G1 & G2 & _) LC MI.
unfold A_speex_decoder_init, RA_nbinit_calloc, e_calloc_L, nbinit_frame, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof (lib_const m A_speex_nb_mode LC_speex_nb_mode LC ltac:(lc_in)) as ND. unfold LC_speex_nb_mode in ND.
assert (AL8 : A_speex_nb_mode mod 8 = 0) by reflexivity.
assert (MPR : 0x10000 <= A_speex_nb_mode < 0x652000) by (unfold A_speex_nb_mode; lia).
set (MP := A_speex_nb_mode) in *. clearbody MP.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -64, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 64%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x9e800.
ato 0x67e9c.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition zb (n : nat) : list byte := repeat (Z_to_bv 8 0) n.
Definition cb_zero : list cell := [CB 8 (zb 8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (zb 16)].
Fixpoint cbs_zero (n : nat) : list cell := match n with O => [] | S n' => cb_zero ++ cbs_zero n' end.
Definition nbz_hdr : list cell := [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Definition nbz_cfg : list cell := [C4 (Z_to_bv 64 0); CB 4 (zb 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition nb_zero_cells : list cell :=
nbz_hdr ++ [CB 1216 (zb 1216)] ++ [CB 956 (zb 956)] ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [CB 16 (zb 16)] ++ [C4 (Z_to_bv 64 0)]
++ nbz_cfg ++ cbs_zero 16 ++ cb_zero ++ [CB 24 (zb 24)] ++ [C4 (Z_to_bv 64 0)] ++ [CB 4 (zb 4)].

Lemma nb_zero_cells_bytes : cells_bytes nb_zero_cells = zb 2968.
Proof. vm_compute. reflexivity. Qed.
Lemma nb_zero_cells_wf : cells_wf nb_zero_cells.
Proof. cbn. repeat split; reflexivity. Qed.

Lemma zero_blob_recast : forall m A, rw_cells asegs m A [CB 2968 (zb 2968)] -> rw_cells asegs m A nb_zero_cells.
Proof.
intros m A X. apply (rw_cells_recast asegs m A [CB 2968 (zb 2968)] nb_zero_cells X).
- exact nb_zero_cells_wf.
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact nb_zero_cells_bytes.
Qed.

Lemma nbinit_w2 : forall (usp lo D : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
rw_cells asegs m D nbz_hdr -> rw_cells asegs m (D + 2232) nbz_cfg ->
aobj asegs m D 2968 -> D mod 8 = 0 -> 0 < D -> D + 2968 <= lo -> (D + 2968 <= SH_LO \/ SH_HI <= D) -> (D + 2968 <= 0x10000 \/ IMG_TOP <= D) ->
aobj asegs m A_nb_mode 208 ->
SH_HI <= lo -> lo <= usp + -64 -> usp < 2^63 ->
lib_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_nbinit_ms1) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 (D + 2204))
(Z_to_bv 64 (D + 32)) (Z_to_bv 64 0) (Z_to_bv 64 1216) xa3 a4 a5 a6 a7
(Z_to_bv 64 A_speex_nb_mode) (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 2047)) (Z_to_bv 64 A_nb_mode) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_asan_memset_L) fc None m1 (seg_rom asegs)
/\ munch [(D, D + 32); (D + 2232, D + 2256)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 D [C8 (Z_to_bv 64 A_speex_nb_mode); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
/\ rw_cells asegs m1 (D + 2232) [C4 (Z_to_bv 64 1); CB 4 (zb 4); C8 (Z_to_bv 64 NB_SUBMODES_PTR); C4 (Z_to_bv 64 NB_DEFAULT_SUBMODE); C4 (Z_to_bv 64 1)])
(MS (mkR (Z_to_bv 64 RA_nbinit_calloc) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A_speex_nb_mode) (Z_to_bv 64 SHB) s4 (Z_to_bv 64 A_nb_mode) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbinit_calloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HD CFG OBD D8 D0 DLO DOFF DIMG OBN LOS LO SPH LC MI.
unfold RA_nbinit_calloc, RA_nbinit_ms1, e_asan_memset_L, nbz_hdr, nbz_cfg, NB_SUBMODES_PTR, NB_DEFAULT_SUBMODE in *.
replace (ret_pc (Z_to_bv 64 0x9e854)) with (Z_to_bv 64 0x9e854) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (lib_const m A_nb_mode LC_nb_mode LC ltac:(lc_in)) as NM. unfold LC_nb_mode in NM.
assert (AL8 : A_nb_mode mod 8 = 0) by reflexivity.
assert (NMR : 0x10000 <= A_nb_mode /\ A_nb_mode + 208 <= 0x652000) by (unfold A_nb_mode; lia).
set (NMP := A_nb_mode) in *. clearbody NMP.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof DIMG as DIMG'. unfold IMG_TOP in DIMG'.
pose proof (munch_refl [(D, D + 32); (D + 2232, D + 2256)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(D, D + 32); (D + 2232, D + 2256)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
astep. astep. sh_if.
ato 0x9e908. rewrite sx32_lit by lia.
ato 0x667b0.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD| exact CFG].
Qed.

Lemma nbinit_w3 : forall (usp lo D : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(h0 h1 h3 h4 h5 lp lg : word) F fc (m : mem),
rw_cells asegs m D [C8 h0; C4 h1; C4 (Z_to_bv 64 0); C4 h3; C4 h4; C8 h5] -> rw_cells asegs m (D + 2204) [C4 lp; C4 lg] ->
aobj asegs m D 2968 -> D mod 8 = 0 -> 0 < D -> D + 2968 <= lo -> (D + 2968 <= SH_LO \/ SH_HI <= D) -> (D + 2968 <= 0x10000 \/ IMG_TOP <= D) ->
SH_HI <= lo -> lo <= usp + -64 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_nbinit_ms2) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 (D + 2204))
(Z_to_bv 64 (D + 2212)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
(Z_to_bv 64 (D + 2228)) (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 2047)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_asan_memset_L) fc None m1 (seg_rom asegs)
/\ munch [(D, D + 32); (D + 2204, D + 2212)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 D [C8 h0; C4 h1; C4 (Z_to_bv 64 0); C4 h3; C4 h4; C8 h5]
/\ rw_cells asegs m1 (D + 2204) [C4 (Z_to_bv 64 40); C4 lg])
(MS (mkR (Z_to_bv 64 RA_nbinit_ms1) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 (D + 2204)) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 2047)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbinit_ms1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HD LPG OBD D8 D0 DLO DOFF DIMG LOS LO SPH MI.
unfold RA_nbinit_ms1, RA_nbinit_ms2, e_asan_memset_L in *.
replace (ret_pc (Z_to_bv 64 0x9e93c)) with (Z_to_bv 64 0x9e93c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof DIMG as DIMG'. unfold IMG_TOP in DIMG'.
pose proof (munch_refl [(D, D + 32); (D + 2204, D + 2212)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(D, D + 32); (D + 2204, D + 2212)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0x667b0.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD| exact LPG].
Qed.

Lemma nbinit_w4 : forall (usp lo D : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(h0 h1 h2 h3 h4 h5 sd0 : word) F fc (m : mem),
rw_cells asegs m D [C8 h0; C4 h1; C4 h2; C4 h3; C4 h4; C8 h5] -> rw_cells asegs m (D + 2228) [C4 sd0] ->
rw_cells asegs m (D + 2256) (cbs_zero 16) -> rw_cells asegs m (D + 2896) cb_zero ->
aobj asegs m D 2968 -> D mod 8 = 0 -> 0 < D -> D + 2968 <= lo -> (D + 2968 <= SH_LO \/ SH_HI <= D) -> (D + 2968 <= 0x10000 \/ IMG_TOP <= D) ->
SH_HI <= lo -> lo <= usp + -64 -> usp < 2^63 ->
lib_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_nbinit_ms3) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 (D + 2960))
(Z_to_bv 64 (D + 2936)) (Z_to_bv 64 0) (Z_to_bv 64 24) xa3 a4 a5 a6 a7
(Z_to_bv 64 (D + 2228)) (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 2047)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_asan_memset_L) fc None m1 (seg_rom asegs)
/\ munch [(D, D + 32); (D + 2228, D + 2232); (D + 2256, D + 2936)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 D [C8 h0; C4 h1; C4 h2; C4 (Z_to_bv 64 8000); C4 (Z_to_bv 64 0); C8 h5]
/\ rw_cells asegs m1 (D + 2228) [C4 (Z_to_bv 64 1000)]
/\ rw_cells asegs m1 (D + 2256) (cbs_zero 16)
/\ rw_cells asegs m1 (D + 2896) [CB 8 (zb 8); C8 (Z_to_bv 64 A_speex_default_user_handler); C8 (Z_to_bv 64 0); CB 16 (zb 16)])
(MS (mkR (Z_to_bv 64 RA_nbinit_ms2) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 (D + 2204)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (D + 2228)) (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 2047)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbinit_ms2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HD SEED CBS UCB OBD D8 D0 DLO DOFF DIMG LOS LO SPH LC MI.
unfold RA_nbinit_ms2, RA_nbinit_ms3, e_asan_memset_L, cb_zero, A_speex_default_user_handler in *.
replace (ret_pc (Z_to_bv 64 0x9e980)) with (Z_to_bv 64 0x9e980) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
cbn [cbs_zero app] in CBS. unfold cb_zero in CBS. cbn [app] in CBS.
pose proof (lib_const m GOT_f41f8 LC_GOT_f41f8 LC ltac:(lc_in)) as GH. unfold GOT_f41f8, LC_GOT_f41f8 in GH.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof DIMG as DIMG'. unfold IMG_TOP in DIMG'.
pose proof (munch_refl [(D, D + 32); (D + 2228, D + 2232); (D + 2256, D + 2936)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(D, D + 32); (D + 2228, D + 2232); (D + 2256, D + 2936)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0x667b0.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact SEED|]. split; [| exact UCB].
cbn [cbs_zero app]. unfold cb_zero. cbn [app]. exact CBS.
Qed.

Lemma nbinit_w5 : forall (usp lo D : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(hp0 : word) (j0 : list byte) (c5 c4 c3 c2 c1 c0 cra : word) F fc (m : mem),
rw_cells asegs m (D + 2960) [C4 hp0] -> rw_cells asegs m (usp + -64) (nbinit_frame j0 c5 c4 c3 c2 c1 c0 cra) ->
aobj asegs m D 2968 -> D mod 8 = 0 -> 0 < D -> D + 2968 <= lo -> (D + 2968 <= SH_LO \/ SH_HI <= D) -> (D + 2968 <= 0x10000 \/ IMG_TOP <= D) ->
stk asegs m lo (usp + -64) -> SH_HI <= lo -> lo <= usp + -64 -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa1 xa2 xa3 : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 D) xa1 xa2 xa3 a4 a5 a6 a7 c2 c3 c4 c5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(D + 2960, D + 2964)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 (D + 2960) [C4 (Z_to_bv 64 1)])
(MS (mkR (Z_to_bv 64 RA_nbinit_ms3) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 (D + 2960)) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbinit_ms3)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HP FR OBD D8 D0 DLO DOFF DIMG ST LOS LO SPH MI.
unfold RA_nbinit_ms3, nbinit_frame in *.
replace (ret_pc (Z_to_bv 64 0x9ea4c)) with (Z_to_bv 64 0x9ea4c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof DIMG as DIMG'. unfold IMG_TOP in DIMG'.
pose proof (munch_refl [(D + 2960, D + 2964)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(D + 2960, D + 2964)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0x9ea88.
release_frame FR ST usp. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact HP].
Qed.
