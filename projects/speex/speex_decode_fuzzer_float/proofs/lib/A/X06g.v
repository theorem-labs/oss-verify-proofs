(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X05m X09f X06d X069.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0z5 X0ys X0x2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_free_S : Z := 0x67f80.
Definition RA_sbd_low : Z := 0xbd470.

Definition sbd_desc_cells (c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 : word) : list cell :=
[C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 A_sb_decoder_destroy); C8 c10; C8 c11; C8 c12].

Notation sbptrs mp al i0 i1 i2 i3 i4 i5 i6 i7 stk0 g0 g1 ex oq iq msp pg er :=
[C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 al); C4 i0; C4 i1; C4 i2; C4 i3; C4 i4; C4 i5; C4 i6; C4 i7; C8 stk0; C8 (Z_to_bv 64 g0); C8 (Z_to_bv 64 g1); C8 (Z_to_bv 64 ex);
C8 (Z_to_bv 64 oq); C8 (Z_to_bv 64 iq); C8 (Z_to_bv 64 msp); C8 (Z_to_bv 64 pg); C8 (Z_to_bv 64 er)] (only parsing).

Definition sbd_frame (j0 : list byte) (s1 s0 ra : word) : list cell := [CB 8 j0; C8 s1; C8 s0; C8 ra].

Lemma sbd_w1 : forall (usp lo S MP al : Z) (i0 i1 i2 i3 i4 i5 i6 i7 stk0 : word) (g0 g1 ex oq iq msp pg er : Z) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 : word)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m S (sbptrs MP al i0 i1 i2 i3 i4 i5 i6 i7 stk0 g0 g1 ex oq iq msp pg er) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= lo \/ usp <= S) ->
ro_cells bsegs m MP (sbd_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12) -> aobj bsegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x65b000 ->
stk bsegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j0 : list byte) (xt1 xa1 xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_low) (Z_to_bv 64 (usp + -32)) gp tp t0 xt1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB)
(Z_to_bv 64 al) xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (sbd_frame j0 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros P0 OBS S8 S0 SHI AP ND OBM AL8 MPLO MPHI ST LO LOS SPH (G1 & G2 & _) MI.
unfold A_speex_decoder_destroy, RA_sbd_low, sbd_frame, sbd_desc_cells, A_sb_decoder_destroy, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xbd46c. astep.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition sbd_pc (k : nat) : Z := match k with 0%nat => 0xbd470 | 1%nat => 0xbd48c | 2%nat => 0xbd4a8 | 3%nat => 0xbd4c4 | 4%nat => 0xbd4e0 | 5%nat => 0xbd4fc | 6%nat => 0xbd518 | _ => 0xbd534 end.
Definition sbd_ra (k : nat) : Z := match k with 0%nat => 0xbd48c | 1%nat => 0xbd4a8 | 2%nat => 0xbd4c4 | 3%nat => 0xbd4e0 | 4%nat => 0xbd4fc | 5%nat => 0xbd518 | 6%nat => 0xbd534 | _ => 0xbd550 end.
Definition sbd_arg (k : nat) (g0 g1 ex oq iq msp pg er : Z) : Z := match k with 0%nat => g0 | 1%nat => g1 | 2%nat => ex | 3%nat => oq | 4%nat => iq | 5%nat => pg | 6%nat => er | _ => msp end.

Lemma sbd_free_seg : forall (k : nat) (usp S MP al : Z) (i0 i1 i2 i3 i4 i5 i6 i7 stk0 : word) (g0 g1 ex oq iq msp pg er : Z)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
(k < 8)%nat ->
rw_cells bsegs m S (sbptrs MP al i0 i1 i2 i3 i4 i5 i6 i7 stk0 g0 g1 ex oq iq msp pg er) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (xa1 : word),
ms = MS (mkR (Z_to_bv 64 (sbd_ra k)) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB)
(Z_to_bv 64 (sbd_arg k g0 g1 ex oq iq msp pg er)) xa1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_S) fc None m (seg_rom bsegs))
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 (sbd_pc k))) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros Hk P0 OBS S8 S0 SHI MI.
unfold e_free_S in *.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. assert (OF : offsh []) by exact I.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..| exfalso; lia]; cbn [sbd_pc sbd_ra sbd_arg].
all: match goal with |- context [ret_pc (Z_to_bv 64 ?p)] => replace (ret_pc (Z_to_bv 64 p)) with (Z_to_bv 64 p) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
all: ato 0x67f80.
all: apply evt_done; eexists; reflexivity.
Qed.

Lemma sbd_last : forall (usp lo S : Z) (j0 : list byte) (c1 c0 cra : word)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -32) (sbd_frame j0 c1 c0 cra) ->
stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> usp < 2^63 -> 0 < S -> S + 160 < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_S) fc None m (seg_rom bsegs) /\ stk bsegs m lo usp)
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 0xbd550)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR ST LO SPH S0 SHI MI. unfold sbd_frame, e_free_S in *.
replace (ret_pc (Z_to_bv 64 0xbd550)) with (Z_to_bv 64 0xbd550) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xbd564. release_frame FR ST usp. astep.
apply evt_done. split; [reflexivity| exact ST].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_free_S : Z := 0x67e94.
Definition RA_sbd_low : Z := 0xb599c.

Definition sbd_desc_cells (c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 : word) : list cell :=
[C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 A_sb_decoder_destroy); C8 c10; C8 c11; C8 c12].

Notation sbptrs mp al i0 i1 i2 i3 i4 i5 i6 i7 stk0 g0 g1 ex oq iq msp pg er :=
[C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 al); C4 i0; C4 i1; C4 i2; C4 i3; C4 i4; C4 i5; C4 i6; C4 i7; C8 stk0; C8 (Z_to_bv 64 g0); C8 (Z_to_bv 64 g1); C8 (Z_to_bv 64 ex);
C8 (Z_to_bv 64 oq); C8 (Z_to_bv 64 iq); C8 (Z_to_bv 64 msp); C8 (Z_to_bv 64 pg); C8 (Z_to_bv 64 er)] (only parsing).

Definition sbd_frame (j0 : list byte) (s1 s0 ra : word) : list cell := [CB 8 j0; C8 s1; C8 s0; C8 ra].

Lemma sbd_w1 : forall (usp lo S MP al : Z) (i0 i1 i2 i3 i4 i5 i6 i7 stk0 : word) (g0 g1 ex oq iq msp pg er : Z) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12 : word)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m S (sbptrs MP al i0 i1 i2 i3 i4 i5 i6 i7 stk0 g0 g1 ex oq iq msp pg er) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= lo \/ usp <= S) ->
ro_cells asegs m MP (sbd_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12) -> aobj asegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x652000 ->
stk asegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j0 : list byte) (xt1 xa1 xa2 xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_low) (Z_to_bv 64 (usp + -32)) gp tp t0 xt1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB)
(Z_to_bv 64 al) xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (sbd_frame j0 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m (seg_rom asegs)).
Proof.
intros until m. intros P0 OBS S8 S0 SHI AP ND OBM AL8 MPLO MPHI ST LO LOS SPH (G1 & G2 & _) MI.
unfold A_speex_decoder_destroy, RA_sbd_low, sbd_frame, sbd_desc_cells, A_sb_decoder_destroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb5960.
ato 0xb5998. astep.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition sbd_pc (k : nat) : Z := match k with 0%nat => 0xb599c | 1%nat => 0xb59b8 | 2%nat => 0xb59d4 | 3%nat => 0xb59f0 | 4%nat => 0xb5a0c | 5%nat => 0xb5a28 | 6%nat => 0xb5a44 | _ => 0xb5a60 end.
Definition sbd_ra (k : nat) : Z := match k with 0%nat => 0xb59b8 | 1%nat => 0xb59d4 | 2%nat => 0xb59f0 | 3%nat => 0xb5a0c | 4%nat => 0xb5a28 | 5%nat => 0xb5a44 | 6%nat => 0xb5a60 | _ => 0xb5a7c end.
Definition sbd_arg (k : nat) (g0 g1 ex oq iq msp pg er : Z) : Z := match k with 0%nat => g0 | 1%nat => g1 | 2%nat => ex | 3%nat => oq | 4%nat => iq | 5%nat => pg | 6%nat => er | _ => msp end.

Lemma sbd_free_seg : forall (k : nat) (usp S MP al : Z) (i0 i1 i2 i3 i4 i5 i6 i7 stk0 : word) (g0 g1 ex oq iq msp pg er : Z)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
(k < 8)%nat ->
rw_cells asegs m S (sbptrs MP al i0 i1 i2 i3 i4 i5 i6 i7 stk0 g0 g1 ex oq iq msp pg er) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (xa1 : word),
ms = MS (mkR (Z_to_bv 64 (sbd_ra k)) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB)
(Z_to_bv 64 (sbd_arg k g0 g1 ex oq iq msp pg er)) xa1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_S) fc None m (seg_rom asegs))
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 (sbd_pc k))) fc None m (seg_rom asegs)).
Proof.
intros until m. intros Hk P0 OBS S8 S0 SHI MI.
unfold e_free_S in *.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. assert (OF : offsh []) by exact I.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..| exfalso; lia]; cbn [sbd_pc sbd_ra sbd_arg].
all: match goal with |- context [ret_pc (Z_to_bv 64 ?p)] => replace (ret_pc (Z_to_bv 64 p)) with (Z_to_bv 64 p) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
all: ato 0x67e94.
all: apply evt_done; eexists; reflexivity.
Qed.

Lemma sbd_last : forall (usp lo S : Z) (j0 : list byte) (c1 c0 cra : word)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -32) (sbd_frame j0 c1 c0 cra) ->
stk asegs m lo (usp + -32) -> lo <= usp + -32 -> usp < 2^63 -> 0 < S -> S + 160 < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_S) fc None m (seg_rom asegs) /\ stk asegs m lo usp)
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 SHB) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 0xb5a7c)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR ST LO SPH S0 SHI MI. unfold sbd_frame, e_free_S in *.
replace (ret_pc (Z_to_bv 64 0xb5a7c)) with (Z_to_bv 64 0xb5a7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xb5a90. release_frame FR ST usp. astep.
apply evt_done. split; [reflexivity| exact ST].
Qed.
