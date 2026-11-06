(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X07y X05m X09f X06d X069 X07q.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation sbst c0 c8 i16 i20 i24 i28 i32 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156 :=
[C8 c0; C8 c8; C4 i16; C4 i20; C4 i24; C4 i28; C4 i32; C4 i36; C4 i40; C4 i44; C8 c48; C8 p56; C8 p64; C8 p72; C8 p80; C8 p88; C8 p96; C8 p104; C8 p112;
C8 c120; C4 f128; C4 i132; C4 i136; CB 4 pad140; C8 c144; C4 i152; CB 4 pad156] (only parsing).
Definition w0 : word := Z_to_bv 64 0.
Definition zb4 : list byte := repeat (Z_to_bv 8 0) 4.
Definition sbst_zero : list cell := sbst w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 zb4 w0 w0 zb4.
Lemma sbst_zero_recast : forall m A, rw_cells asegs m A [CB 160 (repeat (Z_to_bv 8 0) 160)] -> rw_cells asegs m A sbst_zero.
Proof. intros m A X. apply (rw_cells_recast asegs m A _ sbst_zero X); [cbn; repeat split; reflexivity| vm_compute; reflexivity]. Qed.

Notation sbmode_cells nbm fs sfs lpc g1 g2 lf fg pad sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 dsm :=
[C8 (Z_to_bv 64 nbm); C4 (Z_to_bv 64 fs); C4 (Z_to_bv 64 sfs); C4 (Z_to_bv 64 lpc); C4 g1; C4 g2; C4 lf; C4 fg; CB 4 pad;
C8 sm0; C8 sm1; C8 sm2; C8 sm3; C8 sm4; C8 sm5; C8 sm6; C8 sm7; C4 (Z_to_bv 64 dsm)] (only parsing).

Definition RA_sbinit_low : Z := 0xb530c.
Definition RA_sbinit_ctl25 : Z := 0xb542c.
Definition RA_sbinit_ctl105 : Z := 0xb5468.

Lemma sbinit_w3 : forall (usp S MP SM NBM f sf : Z) (fs sfs lpc dsm : Z) (g1 g2 lf fg sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 : word) (pad : list byte)
(c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s8 s9 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m S sbst_zero ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> (S + 160 <= 0x10000 \/ IMG_TOP <= S) ->
ro_cells asegs m MP (sbi_desc_cells (Z_to_bv 64 SM) c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12) -> aobj asegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x652000 ->
ro_cells asegs m SM (sbmode_cells NBM fs sfs lpc g1 g2 lf fg pad sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 dsm) -> aobj asegs m SM 216 -> SM mod 8 = 0 -> 0x10000 <= SM -> SM + 216 <= 0x652000 ->
length pad = 4%nat ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa1 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbinit_low) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 NBM) xa1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 S) (Z_to_bv 64 MP) (Z_to_bv 64 f) (Z_to_bv 64 SM) (Z_to_bv 64 sf) s8 s9 (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_init) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst (Z_to_bv 64 MP) w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 (Z_to_bv 64 1) zb4 w0 w0 zb4))
(MS (mkR (Z_to_bv 64 RA_sbinit_calloc0) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 MP) (Z_to_bv 64 f) s6 (Z_to_bv 64 sf) s8 s9 (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbinit_calloc0)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros X OBS S8 S0 SHI SOFF SIMG ND OBM MP8 MPLO MPHI NS OBSM SM8 SMLO SMHI LPAD MI.
unfold RA_sbinit_calloc0, RA_sbinit_low, A_speex_decoder_init, A_sb_decoder_init, sbst_zero, w0, zb4 in *.
replace (ret_pc (Z_to_bv 64 0xb52a8)) with (Z_to_bv 64 0xb52a8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof SIMG as SIMG'. unfold IMG_TOP in SIMG'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
astep. astep. sh_if.
ato 0x983e8.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact X].
Qed.

Lemma sbinit_w4 : forall (usp lo S MP SM NBM AL f sf : Z) (fs sfs dsm : Z) (g1 g2 lf fg sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 : word) (pad : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j24 j32 j40 j48 j56 j64 j72 : list byte) F fc (m : mem),
(fs = 160 /\ sfs = 40) \/ (fs = 320 /\ sfs = 80) ->
rw_cells asegs m S (sbst (Z_to_bv 64 MP) w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 (Z_to_bv 64 1) zb4 w0 w0 zb4) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> (S + 160 <= 0x10000 \/ IMG_TOP <= S) -> S + 160 <= lo ->
ro_cells asegs m SM (sbmode_cells NBM fs sfs 8 g1 g2 lf fg pad sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 dsm) -> aobj asegs m SM 216 -> SM mod 8 = 0 -> 0x10000 <= SM -> SM + 216 <= 0x652000 ->
length pad = 4%nat ->
rw_cells asegs m (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
stk asegs m lo (usp + -192) -> lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < AL < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa3 xa4 xa5 xa6 xa7 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbinit_ctl25) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 AL) (Z_to_bv 64 25) (Z_to_bv 64 (S + 40)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m1 (seg_rom asegs)
/\ munch [(usp + -192, usp); (S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -192)
/\ rw_cells asegs m1 S (sbst (Z_to_bv 64 MP) (Z_to_bv 64 AL) (Z_to_bv 64 (2 * fs)) (Z_to_bv 64 fs) (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) w0 w0 w0 w0
w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 (Z_to_bv 64 1) zb4 w0 w0 zb4)
/\ rw_cells asegs m1 (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (C8 (Z_to_bv 64 (S + 24))) (C8 (Z_to_bv 64 (S + 28))) (C8 (Z_to_bv 64 (S + 32))) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)))
(C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra))
(MS (mkR (Z_to_bv 64 RA_sbinit_low) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 AL) a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 S) (Z_to_bv 64 MP) (Z_to_bv 64 f) (Z_to_bv 64 SM) (Z_to_bv 64 sf) s8 s9 (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbinit_low)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO X OBS S8 S0 SHI SOFF SIMG SLO NS OBSM SM8 SMLO SMHI LPAD FR ST LO LOS SPH ALR MI.
unfold RA_sbinit_low, RA_sbinit_ctl25, A_speex_decoder_ctl, w0, zb4 in *.
replace (ret_pc (Z_to_bv 64 0xb530c)) with (Z_to_bv 64 0xb530c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof SIMG as SIMG'. unfold IMG_TOP in SIMG'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -192, usp); (S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -192, usp); (S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [[-> ->]|[-> ->]].
all: ato 0x98638.
all: rewrite !sx32_lit in X by lia; rewrite unsigned_lit in X by lia.
1: replace (v_divw (Z_to_bv 64 160) (Z_to_bv 64 40)) with (Z_to_bv 64 4) in X by (apply bv_eq; vm_compute; reflexivity).
2: replace (v_divw (Z_to_bv 64 320) (Z_to_bv 64 80)) with (Z_to_bv 64 4) in X by (apply bv_eq; vm_compute; reflexivity).
1: change (Z.shiftl 160 1) with (2 * 160) in X. 2: change (Z.shiftl 320 1) with (2 * 320) in X.
all: apply evt_done; do 6 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w5 : forall (usp S SM AL f sf lr : Z) (c0 i16 i20 i24 i28 i32 i36 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 l32 : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
length pad140 = 4%nat -> length pad156 = 4%nat -> - 2^30 <= lr < 2^30 -> 0 < AL < 2^63 ->
rw_cells asegs m S (sbst c0 (Z_to_bv 64 AL) i16 i20 i24 i28 i32 i36 (Z_to_bv 64 lr) i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
rw_cells asegs m (f + 32) [CB 4 l32] -> 0 < f -> f + 64 < 2^63 -> (S + 160 <= f \/ f + 64 <= S) -> (f + 64 <= SH_LO \/ SH_HI <= f) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_sbinit_ctl105) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 AL) (Z_to_bv 64 105) (Z_to_bv 64 (f + 32)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160); (f + 32, f + 36)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 (Z_to_bv 64 AL) i16 i20 i24 i28 i32 i36 (Z_to_bv 64 (2 * lr)) i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (f + 32) [C4 (Z_to_bv 64 1)])
(MS (mkR (Z_to_bv 64 RA_sbinit_ctl25) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbinit_ctl25)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros LP1 LP2 LRR ALR X OBS S8 S0 SHI SOFF TMP F0 FHI SFA FOFF MI.
unfold RA_sbinit_ctl25, RA_sbinit_ctl105, A_speex_decoder_ctl in *.
replace (ret_pc (Z_to_bv 64 0xb542c)) with (Z_to_bv 64 0xb542c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof FOFF as FOFF'. unfold SH_LO, SH_HI in FOFF'.
pose proof (munch_refl [(S, S + 160); (f + 32, f + 36)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160); (f + 32, f + 36)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0xb5440. rewrite sx32_lit by lia.
ato 0xb5448.
assert (E : Z_to_bv 64 (Z.shiftl (lr mod 18446744073709551616) 1) = Z_to_bv 64 (2 * lr)).
{ apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
rewrite Zmult_mod_idemp_l. f_equal. lia. }
rewrite E. clear E.
ato 0x98638.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact X| exact TMP].
Qed.

Lemma sbinit_w6 : forall (usp S SM NBM f sf : Z) (fs sfs dsm : Z) (g1 g2 lf fg sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 : word) (pad : list byte)
(c0 c8 i16 i20 i24 i28 i32 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
length pad140 = 4%nat -> length pad156 = 4%nat -> length pad = 4%nat -> - 2^31 <= dsm < 2^31 ->
rw_cells asegs m S (sbst c0 c8 i16 i20 i24 i28 i32 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> (S + 160 <= 0x10000 \/ IMG_TOP <= S) ->
ro_cells asegs m SM (sbmode_cells NBM fs sfs 8 g1 g2 lf fg pad sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 dsm) -> aobj asegs m SM 216 -> SM mod 8 = 0 -> 0x10000 <= SM -> SM + 216 <= 0x652000 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 0xb54dc) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 256) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 i24 i28 i32 (Z_to_bv 64 1) i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 (Z_to_bv 64 (SM + 40)) (Z_to_bv 64 dsm) pad156))
(MS (mkR (Z_to_bv 64 RA_sbinit_ctl105) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbinit_ctl105)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros LP1 LP2 LPAD DSR X OBS S8 S0 SHI SOFF SIMG NS OBSM SM8 SMLO SMHI MI.
unfold RA_sbinit_ctl105, e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 0xb5468)) with (Z_to_bv 64 0xb5468) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof SIMG as SIMG'. unfold IMG_TOP in SIMG'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0xb54ac. rewrite sx32_lit by lia.
ato 0x67e9c.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact X].
Qed.

Lemma sbinit_w7 : forall (usp lo S SM B f sf sfs : Z) (c0 c8 i16 i20 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
sfs = 40 \/ sfs = 80 -> length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 742656) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (if sfs =? 40 then 256 else 256)) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 (Z_to_bv 64 B) p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 742620) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 742620)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 742620)) with (Z_to_bv 64 742620) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [->| ->]; cbn [Z.eqb Pos.eqb].
all: ato 0x67e9c.
all: apply evt_done; do 3 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w8 : forall (usp lo S SM B f sf sfs : Z) (c0 c8 i16 i20 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
sfs = 40 \/ sfs = 80 -> length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 742704) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (if sfs =? 40 then 160 else 320)) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 (Z_to_bv 64 B) p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 742656) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 742656)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 742656)) with (Z_to_bv 64 742656) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [->| ->]; cbn [Z.eqb Pos.eqb].
all: ato 0x67e9c.
all: apply evt_done; do 3 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w9 : forall (usp lo S SM B f sf sfs : Z) (c0 c8 i16 i20 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
sfs = 40 \/ sfs = 80 -> length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 742756) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (if sfs =? 40 then 32 else 32)) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 (Z_to_bv 64 B) p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 742704) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 742704)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 742704)) with (Z_to_bv 64 742704) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [->| ->]; cbn [Z.eqb Pos.eqb].
all: ato 0x67e9c.
all: apply evt_done; do 3 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w10 : forall (usp lo S SM B f sf sfs : Z) (c0 c8 i16 i20 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
sfs = 40 \/ sfs = 80 -> length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 742804) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (if sfs =? 40 then 32 else 32)) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 (Z_to_bv 64 B) p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 742756) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 742756)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 742756)) with (Z_to_bv 64 742756) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [->| ->]; cbn [Z.eqb Pos.eqb].
all: ato 0x67e9c.
all: apply evt_done; do 3 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w11 : forall (usp lo S SM B f sf sfs : Z) (c0 c8 i16 i20 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
sfs = 40 \/ sfs = 80 -> length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 742852) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (if sfs =? 40 then 16 else 16)) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 (Z_to_bv 64 B) p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 742804) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 742804)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 742804)) with (Z_to_bv 64 742804) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [->| ->]; cbn [Z.eqb Pos.eqb].
all: ato 0x67e9c.
all: apply evt_done; do 3 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w12 : forall (usp lo S SM B f sf sfs : Z) (c0 c8 i16 i20 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
sfs = 40 \/ sfs = 80 -> length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 742900) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (if sfs =? 40 then 16 else 16)) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 (Z_to_bv 64 B) p112 c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 742852) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 742852)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 742852)) with (Z_to_bv 64 742852) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [->| ->]; cbn [Z.eqb Pos.eqb].
all: ato 0x67e9c.
all: apply evt_done; do 3 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w13 : forall (usp lo S SM B f sf sfs : Z) (c0 c8 i16 i20 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
sfs = 40 \/ sfs = 80 -> length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 742948) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (if sfs =? 40 then 64 else 64)) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 (Z_to_bv 64 sfs) (Z_to_bv 64 4) (Z_to_bv 64 8) i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 (Z_to_bv 64 B) c120 f128 i132 i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 742900) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 742900)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros GEO LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 742900)) with (Z_to_bv 64 742900) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct GEO as [->| ->]; cbn [Z.eqb Pos.eqb].
all: ato 0x67e9c.
all: apply evt_done; do 3 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact X| exact FR].
Qed.

Lemma sbinit_w14 : forall (usp lo S SM B f sf : Z) (c0 c8 i16 i20 i24 i28 i32 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 c144 i152 : word) (pad140 pad156 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w80 c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra : word) F fc (m : mem),
length pad140 = 4%nat -> length pad156 = 4%nat ->
rw_cells asegs m S (sbst c0 c8 i16 i20 i24 i28 i32 i36 i40 i44 c48 p56 p64 p72 p80 p88 p96 p104 p112 c120 f128 i132 i136 pad140 c144 i152 pad156) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra) ->
lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 -> 0 < B < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa0 xa1 xa2 : word),
ms = MS (mkR (Z_to_bv 64 0xb5624) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
xa0 xa1 xa2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 f) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 A_sbinit_epi) fc None m1 (seg_rom asegs)
/\ munch [(S, S + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S (sbst c0 c8 i16 i20 i24 i28 i32 i36 i40 (Z_to_bv 64 0) c48 p56 p64 p72 p80 p88 (Z_to_bv 64 B) p104 p112 (Z_to_bv 64 0) f128 (Z_to_bv 64 1000) i136 pad140 c144 i152 pad156)
/\ rw_cells asegs m1 (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 (Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB))) (C8 (Z_to_bv 64 f)) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8r c7 c6 c5 c4 c3 c2 c1 c0r cra))
(MS (mkR (Z_to_bv 64 0xb5624) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB)) (Z_to_bv 64 SM) (Z_to_bv 64 sf)
(Z_to_bv 64 (Z.shiftr (S + 24) 3 + SHB)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 0xb5624)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros LP1 LP2 X OBS S8 S0 SHI SOFF SLO FR LO LOS SPH BR MI.
unfold A_sbinit_epi in *.
replace (ret_pc (Z_to_bv 64 0xb5624)) with (Z_to_bv 64 0xb5624) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(S, S + 160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S, S + 160)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0xb568c.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact X| exact FR].
Qed.

