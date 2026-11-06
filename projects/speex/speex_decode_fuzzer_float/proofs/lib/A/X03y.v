(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X03z X04v X02a X02b X00b X046 X0jg
X04g X029 X04e X04d.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X0ux X0vt X0t9 X0ta X0ra X0v4 X19x X0ve X0t8 X0vc X0vb.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ve OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation BCMP_DEPTH := 4640%Z (only parsing).

Lemma memcmp_cmpfn : cmpfn_stmt 0xf16c4 0.
Proof.
unfold cmpfn_stmt. intros until m.
intros E0 E1 E2 (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & _ & _ & _ & _ & _ & MI).
eapply evt_mono.
{ eapply (memcmp_spec p1 p2 b1 b2); try eassumption; lia. }
intros ms' (v & a1' & a2' & a3' & a4' & m' & -> & MU & WM & MI' & -> & IFF).
unfold cmp_post. do 16 eexists. split; [reflexivity|].
split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; exact I|].
split; [exact WM|]. split; [exact MI'|]. split; [exact ST| exact IFF].
Qed.

Section Chain.
Hypothesis RIP : rip_stmt.

Lemma icpt_memcmp_cmpfn : forall KC, 16 <= KC -> commonfn_stmt 0xf16c4 KC -> cmpfn_stmt 0x58334 (KC + 48).
Proof using.
intros KC KC0 COMMON.
unfold cmpfn_stmt. intros until m.
intros -> -> -> (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & CS1 & CS2 & M2S & IC & ICC & MI).
unfold kHighShadowEnd in *.
set (n := Z.of_nat (length b1)) in *.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
pose proof (munch_refl [(usp - (KC + 48), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (BY10 : keep (bytes_at bsegs m p1 b1)) by exact BY1. clear BY1.
assert (BY20 : keep (bytes_at bsegs m p2 b2)) by exact BY2. clear BY2.
assert (OFF : forall m', munch [(usp - (KC + 48), usp)] m m' -> wmono bsegs m m' ->
chk_ok m' p1 n /\ chk_ok m' p2 n /\ m2s_cells m' /\ icells m' /\ icells_cmp m' /\ bytes_at bsegs m' p1 b1 /\ bytes_at bsegs m' p2 b2).
{ intros m' MU' WM'.
destruct (cells_off_stack _ m m' MU' WM' ltac:(intros x Hx; cbn [outside]; split; [lia| exact I])) as (T1 & T2 & T3).
split; [apply (chk_ok_agree m m' p1 n CS1 ltac:(lia) H1); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [apply (chk_ok_agree m m' p2 n CS2 ltac:(lia) H2); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [exact (T1 M2S)|]. split; [exact (T2 IC)|]. split; [exact (T3 ICC)|].
split; [unfold keep in BY10; apply (bytes_at_agree bsegs m m' _ _ BY10) | unfold keep in BY20; apply (bytes_at_agree bsegs m m' _ _ BY20)];
apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; rewrite <- ?LEN in Hx; fold n in Hx; (split; [lia| exact I]). }
pose proof ICC as (GCF & GRE & AI & FL).
assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
carve_frame 48%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
xsteps_to 0x6e88c%Z.
call asan_inited_spec; [exact AI| assumption|].
xsteps_to 0x6f79c%Z.
call try_init_spec; [exact AI| rewrite ?EU48; exact ST| rewrite ?EU48; lia| rewrite ?EU48; lia| assumption|].
lazymatch goal with H : stk bsegs _ lo _ |- _ => rewrite ?EU48 in H; rename H into ST2 end.
xsteps_to 0x57aa0%Z.
assert (PRE : forall mm, munch [(usp - (KC + 48), usp)] m mm -> wmono bsegs m mm -> mem_inv bsegs mm -> stk bsegs mm lo (usp + -48) ->
cmp_pre (Z_to_bv 64 (usp + -48)) p1 p2 b1 b2 KC lo mm).
{ intros mm MUm WMm MIm STm. destruct (OFF mm MUm WMm) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
unfold cmp_pre. rewrite EU48. fold n.
split; [exact LEN|]. split; [exact NPOS|]. split; [exact STm|]. split; [lia|]. split; [unfold kHighShadowEnd; lia|]. split; [lia|].
split; [exact P1|]. split; [exact P2|]. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact D6|]. split; [exact D7|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5| exact MIm]. }
call (COMMON p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
do 5 lstep.
release_frame FR ST3 usp.
lstep.
unfold cmp_post. sys_finish.
+ rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
+ rewrite EU. assumption.
Qed.

Lemma musl_bcmp_cmpfn : forall K, cmpfn_stmt 0x58334 K -> cmpfn_stmt 0xf15f4 K.
Proof using.
intros K H. unfold cmpfn_stmt. intros until m. intros E0 E1 E2 PRE.
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
lstep. lstep.
exact (H p1 p2 b1 b2 lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m E0 E1 E2 PRE).
Qed.

Lemma icpt_bcmp_cmpfn : forall KC, 16 <= KC -> commonfn_stmt 0xf15f4 KC -> cmpfn_stmt 0x583f0 (KC + 48).
Proof using.
intros KC KC0 COMMON.
unfold cmpfn_stmt. intros until m.
intros -> -> -> (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & CS1 & CS2 & M2S & IC & ICC & MI).
unfold kHighShadowEnd in *.
set (n := Z.of_nat (length b1)) in *.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
pose proof (munch_refl [(usp - (KC + 48), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (BY10 : keep (bytes_at bsegs m p1 b1)) by exact BY1. clear BY1.
assert (BY20 : keep (bytes_at bsegs m p2 b2)) by exact BY2. clear BY2.
assert (OFF : forall m', munch [(usp - (KC + 48), usp)] m m' -> wmono bsegs m m' ->
chk_ok m' p1 n /\ chk_ok m' p2 n /\ m2s_cells m' /\ icells m' /\ icells_cmp m' /\ bytes_at bsegs m' p1 b1 /\ bytes_at bsegs m' p2 b2).
{ intros m' MU' WM'.
destruct (cells_off_stack _ m m' MU' WM' ltac:(intros x Hx; cbn [outside]; split; [lia| exact I])) as (T1 & T2 & T3).
split; [apply (chk_ok_agree m m' p1 n CS1 ltac:(lia) H1); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [apply (chk_ok_agree m m' p2 n CS2 ltac:(lia) H2); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [exact (T1 M2S)|]. split; [exact (T2 IC)|]. split; [exact (T3 ICC)|].
split; [unfold keep in BY10; apply (bytes_at_agree bsegs m m' _ _ BY10) | unfold keep in BY20; apply (bytes_at_agree bsegs m m' _ _ BY20)];
apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; rewrite <- ?LEN in Hx; fold n in Hx; (split; [lia| exact I]). }
pose proof ICC as (GCF & GRE & AI & FL).
assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
carve_frame 48%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
xsteps_to 0x6e88c%Z.
call asan_inited_spec; [exact AI| assumption|].
xsteps_to 0x6f79c%Z.
call try_init_spec; [exact AI| rewrite ?EU48; exact ST| rewrite ?EU48; lia| rewrite ?EU48; lia| assumption|].
lazymatch goal with H : stk bsegs _ lo _ |- _ => rewrite ?EU48 in H; rename H into ST2 end.
xsteps_to 0x57aa0%Z.
assert (PRE : forall mm, munch [(usp - (KC + 48), usp)] m mm -> wmono bsegs m mm -> mem_inv bsegs mm -> stk bsegs mm lo (usp + -48) ->
cmp_pre (Z_to_bv 64 (usp + -48)) p1 p2 b1 b2 KC lo mm).
{ intros mm MUm WMm MIm STm. destruct (OFF mm MUm WMm) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
unfold cmp_pre. rewrite EU48. fold n.
split; [exact LEN|]. split; [exact NPOS|]. split; [exact STm|]. split; [lia|]. split; [unfold kHighShadowEnd; lia|]. split; [lia|].
split; [exact P1|]. split; [exact P2|]. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact D6|]. split; [exact D7|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5| exact MIm]. }
call (COMMON p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
do 5 lstep.
release_frame FR ST3 usp.
lstep.
unfold cmp_post. sys_finish.
+ rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
+ rewrite EU. assumption.
Qed.

Theorem bcmp_entry_spec : cmpfn_stmt 0x56ce0 BCMP_DEPTH.
Proof using RIP.
assert (C1 : cmpfn_stmt 0x58334 2320).
{ apply (icpt_memcmp_cmpfn 2272 ltac:(lia)).
exact (memcmpc_spec RIP 0xf16c4 0 ltac:(left; reflexivity) ltac:(lia) memcmp_cmpfn). }
assert (C2 : cmpfn_stmt 0x583f0 4640).
{ apply (icpt_bcmp_cmpfn 4592 ltac:(lia)).
exact (memcmpc_spec RIP 0xf15f4 2320 ltac:(right; reflexivity) ltac:(lia) (musl_bcmp_cmpfn 2320 C1)). }
unfold cmpfn_stmt. intros until m. intros E0 E1 E2 PRE.
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
lstep.
exact (C2 p1 p2 b1 b2 lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m E0 E1 E2 PRE).
Qed.
End Chain.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation BCMP_DEPTH := 4640%Z (only parsing).

Lemma memcmp_cmpfn : cmpfn_stmt 0xe8e50 0.
Proof.
unfold cmpfn_stmt. intros until m.
intros E0 E1 E2 (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & _ & _ & _ & _ & _ & MI).
eapply evt_mono.
{ eapply (memcmp_spec p1 p2 b1 b2); try eassumption; lia. }
intros ms' (v & a1' & a2' & a3' & a4' & m' & -> & MU & WM & MI' & -> & IFF).
unfold cmp_post. do 16 eexists. split; [reflexivity|].
split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; exact I|].
split; [exact WM|]. split; [exact MI'|]. split; [exact ST| exact IFF].
Qed.

Section Chain.
Hypothesis RIP : rip_stmt.

Lemma icpt_memcmp_cmpfn : forall KC, 16 <= KC -> commonfn_stmt 0xe8e50 KC -> cmpfn_stmt 0x58248 (KC + 48).
Proof using.
intros KC KC0 COMMON.
unfold cmpfn_stmt. intros until m.
intros -> -> -> (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & CS1 & CS2 & M2S & IC & ICC & MI).
unfold kHighShadowEnd in *.
set (n := Z.of_nat (length b1)) in *.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
pose proof (munch_refl [(usp - (KC + 48), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (BY10 : keep (bytes_at asegs m p1 b1)) by exact BY1. clear BY1.
assert (BY20 : keep (bytes_at asegs m p2 b2)) by exact BY2. clear BY2.
assert (OFF : forall m', munch [(usp - (KC + 48), usp)] m m' -> wmono asegs m m' ->
chk_ok m' p1 n /\ chk_ok m' p2 n /\ m2s_cells m' /\ icells m' /\ icells_cmp m' /\ bytes_at asegs m' p1 b1 /\ bytes_at asegs m' p2 b2).
{ intros m' MU' WM'.
destruct (cells_off_stack _ m m' MU' WM' ltac:(intros x Hx; cbn [outside]; split; [lia| exact I])) as (T1 & T2 & T3).
split; [apply (chk_ok_agree m m' p1 n CS1 ltac:(lia) H1); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [apply (chk_ok_agree m m' p2 n CS2 ltac:(lia) H2); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [exact (T1 M2S)|]. split; [exact (T2 IC)|]. split; [exact (T3 ICC)|].
split; [unfold keep in BY10; apply (bytes_at_agree asegs m m' _ _ BY10) | unfold keep in BY20; apply (bytes_at_agree asegs m m' _ _ BY20)];
apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; rewrite <- ?LEN in Hx; fold n in Hx; (split; [lia| exact I]). }
pose proof ICC as (GCF & GRE & AI & FL).
assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
carve_frame 48%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
xsteps_to 0x6e7a0%Z.
call asan_inited_spec; [exact AI| assumption|].
xsteps_to 0x6f6b0%Z.
call try_init_spec; [exact AI| rewrite ?EU48; exact ST| rewrite ?EU48; lia| rewrite ?EU48; lia| assumption|].
lazymatch goal with H : stk asegs _ lo _ |- _ => rewrite ?EU48 in H; rename H into ST2 end.
xsteps_to 0x579b4%Z.
assert (PRE : forall mm, munch [(usp - (KC + 48), usp)] m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo (usp + -48) ->
cmp_pre (Z_to_bv 64 (usp + -48)) p1 p2 b1 b2 KC lo mm).
{ intros mm MUm WMm MIm STm. destruct (OFF mm MUm WMm) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
unfold cmp_pre. rewrite EU48. fold n.
split; [exact LEN|]. split; [exact NPOS|]. split; [exact STm|]. split; [lia|]. split; [unfold kHighShadowEnd; lia|]. split; [lia|].
split; [exact P1|]. split; [exact P2|]. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact D6|]. split; [exact D7|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5| exact MIm]. }
call (COMMON p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
do 5 lstep.
release_frame FR ST3 usp.
lstep.
unfold cmp_post. sys_finish.
+ rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
+ rewrite EU. assumption.
Qed.

Lemma musl_bcmp_cmpfn : forall K, cmpfn_stmt 0x58248 K -> cmpfn_stmt 0xe8d80 K.
Proof using.
intros K H. unfold cmpfn_stmt. intros until m. intros E0 E1 E2 PRE.
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
lstep. lstep.
exact (H p1 p2 b1 b2 lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m E0 E1 E2 PRE).
Qed.

Lemma icpt_bcmp_cmpfn : forall KC, 16 <= KC -> commonfn_stmt 0xe8d80 KC -> cmpfn_stmt 0x58304 (KC + 48).
Proof using.
intros KC KC0 COMMON.
unfold cmpfn_stmt. intros until m.
intros -> -> -> (LEN & NPOS & ST & LO & LOLO & SPH & P1 & P2 & H1 & H2 & SEP1 & SEP2 & BY1 & BY2 & CS1 & CS2 & M2S & IC & ICC & MI).
unfold kHighShadowEnd in *.
set (n := Z.of_nat (length b1)) in *.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
pose proof (munch_refl [(usp - (KC + 48), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (BY10 : keep (bytes_at asegs m p1 b1)) by exact BY1. clear BY1.
assert (BY20 : keep (bytes_at asegs m p2 b2)) by exact BY2. clear BY2.
assert (OFF : forall m', munch [(usp - (KC + 48), usp)] m m' -> wmono asegs m m' ->
chk_ok m' p1 n /\ chk_ok m' p2 n /\ m2s_cells m' /\ icells m' /\ icells_cmp m' /\ bytes_at asegs m' p1 b1 /\ bytes_at asegs m' p2 b2).
{ intros m' MU' WM'.
destruct (cells_off_stack _ m m' MU' WM' ltac:(intros x Hx; cbn [outside]; split; [lia| exact I])) as (T1 & T2 & T3).
split; [apply (chk_ok_agree m m' p1 n CS1 ltac:(lia) H1); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [apply (chk_ok_agree m m' p2 n CS2 ltac:(lia) H2); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; split; [lia| exact I]|].
split; [exact (T1 M2S)|]. split; [exact (T2 IC)|]. split; [exact (T3 ICC)|].
split; [unfold keep in BY10; apply (bytes_at_agree asegs m m' _ _ BY10) | unfold keep in BY20; apply (bytes_at_agree asegs m m' _ _ BY20)];
apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; rewrite <- ?LEN in Hx; fold n in Hx; (split; [lia| exact I]). }
pose proof ICC as (GCF & GRE & AI & FL).
assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
carve_frame 48%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
xsteps_to 0x6e7a0%Z.
call asan_inited_spec; [exact AI| assumption|].
xsteps_to 0x6f6b0%Z.
call try_init_spec; [exact AI| rewrite ?EU48; exact ST| rewrite ?EU48; lia| rewrite ?EU48; lia| assumption|].
lazymatch goal with H : stk asegs _ lo _ |- _ => rewrite ?EU48 in H; rename H into ST2 end.
xsteps_to 0x579b4%Z.
assert (PRE : forall mm, munch [(usp - (KC + 48), usp)] m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo (usp + -48) ->
cmp_pre (Z_to_bv 64 (usp + -48)) p1 p2 b1 b2 KC lo mm).
{ intros mm MUm WMm MIm STm. destruct (OFF mm MUm WMm) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
unfold cmp_pre. rewrite EU48. fold n.
split; [exact LEN|]. split; [exact NPOS|]. split; [exact STm|]. split; [lia|]. split; [unfold kHighShadowEnd; lia|]. split; [lia|].
split; [exact P1|]. split; [exact P2|]. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact D6|]. split; [exact D7|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5| exact MIm]. }
call (COMMON p1 p2 b1 b2 lo); [reflexivity | reflexivity | reflexivity | reflexivity | apply PRE; assumption |].
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
do 5 lstep.
release_frame FR ST3 usp.
lstep.
unfold cmp_post. sys_finish.
+ rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
+ rewrite EU. assumption.
Qed.

Theorem bcmp_entry_spec : cmpfn_stmt 0x56bf4 BCMP_DEPTH.
Proof using RIP.
assert (C1 : cmpfn_stmt 0x58248 2320).
{ apply (icpt_memcmp_cmpfn 2272 ltac:(lia)).
exact (memcmpc_spec RIP 0xe8e50 0 ltac:(left; reflexivity) ltac:(lia) memcmp_cmpfn). }
assert (C2 : cmpfn_stmt 0x58304 4640).
{ apply (icpt_bcmp_cmpfn 4592 ltac:(lia)).
exact (memcmpc_spec RIP 0xe8d80 2320 ltac:(right; reflexivity) ltac:(lia) (musl_bcmp_cmpfn 2320 C1)). }
unfold cmpfn_stmt. intros until m. intros E0 E1 E2 PRE.
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
lstep.
exact (C2 p1 p2 b1 b2 lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m E0 E1 E2 PRE).
Qed.
End Chain.
