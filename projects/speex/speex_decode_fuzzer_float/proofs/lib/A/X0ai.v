(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh X1rg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X05h X0ak.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0z5 X0we X115.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0we OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X115.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_calloc_p : Z := 0x67f88.
Definition e_asan_memcpy_p : Z := 0x66400.
Definition e_free_p : Z := 0x67f80.

Notation p2h_frame c2 c1 c0 cra := [C8 c2; C8 c1; C8 c0; C8 cra] (only parsing).

Lemma p2h_small : forall (P size usp lo errf : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
- 2^31 <= size < 80 ->
aobj bsegs m RF_STDERR_VAR 8 ->
ro_cells bsegs m RF_GOT_STDERR [C8 (Z_to_bv 64 RF_STDERR_VAR)] -> ro_cells bsegs m RF_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
stk bsegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_p2h_fprintf_small) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 errf) (Z_to_bv 64 P2H_FMT_NOTIFY) (Z_to_bv 64 P2H_MSG_TOO_SMALL) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_fprintf) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (p2h_frame s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_packet_to_header) fc None m (seg_rom bsegs)).

Proof.
intros until m. intros Hsz OBV GOTE VARE ST LO LOS SPH CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_packet_to_header, e_wrap_fprintf, RA_p2h_fprintf_small, RF_GOT_STDERR, RF_STDERR_VAR, P2H_FMT_NOTIFY, P2H_MSG_TOO_SMALL,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
assert (V8 : 1032208 mod 8 = 0) by reflexivity.
ato 0x99e84. astep. sh_if.
ato 0x56d08.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma p2h_tail0 : forall (pc0 usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c2 c1 c0 cra : word) F fc (m : mem),
pc0 = RA_p2h_fprintf_small \/ pc0 = RA_p2h_free ->
stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> usp < 2^63 ->
rw_cells bsegs m (usp + -32) (p2h_frame c2 c1 c0 cra) -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m (seg_rom bsegs)
/\ stk bsegs m lo usp)
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 pc0)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros PC ST LO SPH FR MI.
pose proof ST as (STa & STb & _).
destruct PC as [-> | ->]; unfold RA_p2h_fprintf_small, RA_p2h_free.
- replace (ret_pc (Z_to_bv 64 0x9a068)) with (Z_to_bv 64 0x9a068) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x9a0c0. release_frame FR ST usp. astep.
apply evt_done. split; [reflexivity| exact ST].
- replace (ret_pc (Z_to_bv 64 0x9a0a4)) with (Z_to_bv 64 0x9a0a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x9a0c0. release_frame FR ST usp. astep.
apply evt_done. split; [reflexivity| exact ST].
Qed.

Section Magic.
Variables (P : Z) (pb : list byte) (m : mem).
Variables (rav spv gp tp t0 t1 t2 s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis PK : u8ro bsegs m P pb.
Hypothesis L8 : (8 <= length pb)%nat.
Hypothesis MG : u8ro bsegs m P2H_MAGIC MAGIC_BYTES.
Hypothesis OBP : aobj bsegs m P (Z.of_nat (length pb)).
Hypothesis OBM : aobj bsegs m P2H_MAGIC 9.
Hypothesis Ppos : 0 < P.
Hypothesis MI : mem_inv bsegs m.

Definition p2h_magic_post : machine_state -> Prop := fun ms' =>
exists a0' a1' a2' a6' a7' : word,
(ms' = MS (mkR rav spv gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0' a1' a2' (Z_to_bv 64 1) (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a6' a7'
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_EXIT) fc None m (seg_rom bsegs)
/\ firstn 8 pb <> MAGIC_BYTES)
\/ (ms' = MS (mkR rav spv gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0' a1' a2' (Z_to_bv 64 1) (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a6' a7'
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_ALLOC) fc None m (seg_rom bsegs)
/\ firstn 8 pb = MAGIC_BYTES).

Lemma p2h_magic_loop : forall (k i : nat) (a0v a1v a6v a7v : word),
a0v = Z_to_bv 64 (P + Z.of_nat i) -> (i + k = 8)%nat -> (0 < k)%nat -> firstn i pb = firstn i MAGIC_BYTES ->
evt bsegs p2h_magic_post
(MS (mkR rav spv gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0v a1v (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a6v a7v
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_LOOP) fc None m (seg_rom bsegs)).
Proof using PK L8 MG OBP OBM Ppos MI.
induction k as [|k IH]; intros i a0v a1v a6v a7v E0 Hik Hk PRE; [lia|]. subst a0v.
pose proof (bytes_at_bound _ _ _ _ PK) as BX. pose proof (bytes_at_bound _ _ _ _ MG) as BY.
rewrite MAGIC_BYTES_eq in BY. cbn [length] in BY. unfold P2H_MAGIC in BY.
assert (LM : length MAGIC_BYTES = 8%nat) by reflexivity.
pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
set (x := hb pb i). set (y := hb MAGIC_BYTES i).
pose proof (u8ro_read bsegs m P pb (Z.of_nat i) x (wa (P + Z.of_nat i)) PK
ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) eq_refl) as RX.
pose proof (u8ro_read bsegs m P2H_MAGIC MAGIC_BYTES (Z.of_nat i) y (wa (P2H_MAGIC + Z.of_nat i)) MG
ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) eq_refl) as RY.
unfold P2H_LOOP, P2H_MAGIC in *.
bato 0x99ec4. astep. chk_merge OBP 1.
bato 0x99ee0. astep.
unfold shz. rewrite (shb_zero bsegs m 145312 9 (145312 + Z.of_nat i) (proj2 (proj2 OBM)) ltac:(lia) ltac:(clear - Hik; Z.div_mod_to_equations; lia)).
lit_if.
astep. clear RX RY. astep. if_cases K; zify_cond K.
-
apply evt_done. unfold p2h_magic_post, P2H_EXIT, P2H_MAGIC. do 5 eexists. left. split; [reflexivity|].
intros E. apply K.
enough (Exy : x = y) by (rewrite Exy; reflexivity).
subst x y. unfold hb. rewrite <- E. rewrite nth_firstn. replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- assert (Exy : x = y) by (apply bv_eq; exact K).
astep. astep. astep. if_cases K2; zify_cond K2.
+
apply evt_done. unfold p2h_magic_post, P2H_ALLOC, P2H_MAGIC. do 5 eexists. right. split; [reflexivity|].
replace 8%nat with (S i) by lia.
rewrite <- (firstn_all2 (n := S i) MAGIC_BYTES) by lia.
rewrite (firstn_S_hb pb i), (firstn_S_hb MAGIC_BYTES i) by lia. rewrite PRE. fold x. fold y. rewrite Exy. reflexivity.
+
astep. replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
apply (IH (S i)); [f_equal; lia| lia| lia|].
rewrite (firstn_S_hb pb i), (firstn_S_hb MAGIC_BYTES i) by lia. rewrite PRE. fold x. fold y. rewrite Exy. reflexivity.
Qed.
End Magic.

Lemma p2h_magic : forall (P size usp lo : Z) (pb : list byte)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
80 <= size < 2^31 -> u8ro bsegs m P pb -> (8 <= length pb)%nat -> 0 < P ->
aobj bsegs m P (Z.of_nat (length pb)) -> aobj bsegs m P2H_MAGIC 9 ->
stk bsegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 -> P + Z.of_nat (length pb) <= lo ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (m1 : mem),
munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ ((firstn 8 pb <> MAGIC_BYTES /\ exists (a1' a2' a6' a7' : word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' (Z_to_bv 64 1) (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom bsegs)
/\ stk bsegs m1 lo usp)
\/ (firstn 8 pb = MAGIC_BYTES /\ exists (a2' a6' a7' : word),
ms' = MS (mkR (Z_to_bv 64 RA_p2h_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 P)
(Z_to_bv 64 80) (Z_to_bv 64 1) a2' (Z_to_bv 64 1) (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a6' a7'
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_p) fc None m1 (seg_rom bsegs)
/\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (p2h_frame s2 s1 s0 ra))))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_packet_to_header) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros Hsz PK L8 Ppos OBP OBM ST LO LOS SPH PLO CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_packet_to_header, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (bytes_at_bound _ _ _ _ PK) as PB.
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x99e84. astep. sh_if.
ato 0x99ea4.
replace (0 <? P) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
pose proof (aobj_munch bsegs _ m m1 P _ OBP MU (shfree_of_aobj bsegs _ m P _ OF OBP)) as OBP1;
pose proof (aobj_munch bsegs _ m m1 P2H_MAGIC 9 OBM MU (shfree_of_aobj bsegs _ m P2H_MAGIC 9 OF OBM)) as OBM1;
pose proof (p2h_magic_ro m1 MI) as MG1;
eapply evt_cut;
[ change 0 with (Z.of_nat 0); change 145312 with P2H_MAGIC;
eapply (p2h_magic_loop P pb m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PK L8 MG1 OBP1 OBM1 Ppos MI 8 0); [f_equal; lia| reflexivity| lia| reflexivity] | ]
end.
cbv beta. intros ms' (a0' & a1' & a2' & a6' & a7' & [[-> NE]|[-> EQ]]).
-
unfold P2H_EXIT. pose proof ST as (STa & STb & _).
ato 0x9a0c0. release_frame FR ST usp. astep.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
left. split; [exact NE|]. do 4 eexists. split; [reflexivity| exact ST].
-
unfold P2H_ALLOC, e_calloc_p, RA_p2h_calloc.
ato 0x67f88.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
right. split; [exact EQ|]. do 3 eexists. split; [reflexivity|]. split; [exact ST| exact FR].
Qed.

Lemma land3_lor : forall D P, D mod 4 = 0 -> P mod 4 = 0 -> Z.land (Z.lor D P) 3 = 0.
Proof. intros D P HD HP. rewrite Z.land_lor_distr_l. rewrite (land3_al D HD), (land3_al P HP). reflexivity. Qed.

Lemma p2h_copy : forall (P D usp : Z) (gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
D mod 8 = 0 -> P mod 4 = 0 -> 0 <= D < 2^63 -> 0 <= P < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_p2h_memcpy) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P)
(Z_to_bv 64 D) (Z_to_bv 64 P) (Z_to_bv 64 80) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_asan_memcpy_p) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_p2h_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_p2h_calloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros D8 P4 DR PR MI. unfold RA_p2h_calloc, RA_p2h_memcpy, e_asan_memcpy_p.
replace (ret_pc (Z_to_bv 64 0x99f28)) with (Z_to_bv 64 0x99f28) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (D4 : D mod 4 = 0) by (clear - D8; Z.div_mod_to_equations; lia).
ato 0x99f34. rewrite ?Z.mod_small by lia. rewrite (land3_lor D P D4 P4). astep. try sh_if.
ato 0x66400.
apply evt_done. reflexivity.
Qed.

Lemma p2h_free : forall (P D usp : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_p2h_free) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P)
(Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_p) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_p2h_fprintf_mode) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_p2h_fprintf_mode)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros MI. unfold RA_p2h_fprintf_mode, RA_p2h_free, e_free_p.
replace (ret_pc (Z_to_bv 64 0x9a09c)) with (Z_to_bv 64 0x9a09c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x67f80.
apply evt_done. reflexivity.
Qed.

Lemma p2h_mode : forall (P D usp lo errf : Z) (pb : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c2 c1 c0 cra : word) F fc (m : mem),
(80 <= length pb)%nat ->
rw_cells bsegs m D (hdr_cells pb (Z_to_bv 64 (fw pb 48))) ->
aobj bsegs m D 80 -> D mod 8 = 0 -> 0 < D -> D + 80 <= lo -> (D + 80 <= SH_LO \/ SH_HI <= D) ->
aobj bsegs m RF_STDERR_VAR 8 ->
ro_cells bsegs m RF_GOT_STDERR [C8 (Z_to_bv 64 RF_STDERR_VAR)] -> ro_cells bsegs m RF_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> SH_HI <= lo -> usp < 2^63 ->
rw_cells bsegs m (usp + -32) (p2h_frame c2 c1 c0 cra) -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
(~ (0 <= s32 (fw pb 40) < 3) /\ exists (a3' : word),
ms' = MS (mkR (Z_to_bv 64 RA_p2h_fprintf_mode) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P)
(Z_to_bv 64 errf) (Z_to_bv 64 P2H_FMT_NOTIFY) (Z_to_bv 64 P2H_MSG_BAD_MODE) a3' a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_fprintf) fc None m (seg_rom bsegs))
\/ (0 <= s32 (fw pb 40) < 3 /\ exists (m1 : mem) (a1' a2' a3' : word),
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 D) a1' a2' a3' a4 a5 a6 a7
c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(D, D + 80)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 D (hdr_cells pb (Z_to_bv 64 (clamp_channels (s32 (fw pb 48)))))))
(MS (mkR (Z_to_bv 64 RA_p2h_memcpy) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_p2h_memcpy)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros L80 HDR OBD D8 Dpos DLO DOFF OBV GOTE VARE ST LO LOS SPH FR MI.
unfold RA_p2h_memcpy, RA_p2h_fprintf_mode, e_wrap_fprintf, RF_GOT_STDERR, RF_STDERR_VAR, P2H_FMT_NOTIFY, P2H_MSG_BAD_MODE in *.
replace (ret_pc (Z_to_bv 64 0x99f48)) with (Z_to_bv 64 0x99f48) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof DOFF as DOFF'. unfold SH_LO, SH_HI in DOFF'.
pose proof ST as (STa & STb & _). pose proof OBD as (OD0 & OD1 & _). unfold APP_TOP in *.
pose proof (s32_range (fw pb 40)) as R40. pose proof (fw_range pb 40) as U40.
pose proof (s32_range (fw pb 48)) as R48. pose proof (fw_range pb 48) as U48.
assert (V8 : 1032208 mod 8 = 0) by reflexivity.
assert (DA : forall k, k mod 4 = 0 -> (D + k) mod 4 = 0) by (intros k Hk; clear - D8 Hk; Z.div_mod_to_equations; lia).
pose proof (DA 28 eq_refl) as D28. pose proof (DA 32 eq_refl) as D32. pose proof (DA 36 eq_refl) as D36. pose proof (DA 40 eq_refl) as D40.
pose proof (DA 44 eq_refl) as D44. pose proof (DA 48 eq_refl) as D48. pose proof (DA 52 eq_refl) as D52. pose proof (DA 56 eq_refl) as D56.
pose proof (DA 60 eq_refl) as D60. pose proof (DA 64 eq_refl) as D64. pose proof (DA 68 eq_refl) as D68. clear DA.
pose proof (munch_refl [(D, D + 80)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(D, D + 80)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof HDR as HDRc. unfold hdr_cells in HDRc.
bato 0x99fb4.
rewrite sx32_w by exact U40.
bato 0x99ff8.
assert (CASES : 0 <= s32 (fw pb 40) < 3 \/ ~ (0 <= s32 (fw pb 40) < 3)) by lia.
destruct CASES as [GOOD|BAD].
-
astep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|]. clear K3.
bato 0x9a000. rewrite sx32_w by exact U48.
astep. if_cases K4; zify_cond K4; rewrite ?signed_lit_small in K4 by lia.
+
bato 0x9a020. rewrite sx32_w by exact U48.
astep. rewrite (lts_zero_lit (s32 (fw pb 48))) by lia. if_cases K5; zify_cond K5.
*
bato 0x9a0c0. release_frame FR ST usp. astep.
apply evt_done. right. split; [exact GOOD|]. exists m. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
replace (clamp_channels (s32 (fw pb 48))) with (s32 (fw pb 48))
by (unfold clamp_channels; replace (2 <? s32 (fw pb 48)) with false by (symmetry; apply Z.ltb_ge; lia);
replace (s32 (fw pb 48) <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
eapply rw_cells_samebytes; [exact HDR| | |].
-- cbn. rewrite length_firstn. repeat split; try lia; exact I.
-- unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_s32_fw. reflexivity.
-- cbn. reflexivity.
*
bato 0x9a0c0. release_frame FR ST usp. astep.
apply evt_done. right. split; [exact GOOD|]. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
replace (clamp_channels (s32 (fw pb 48))) with 1
by (unfold clamp_channels; replace (2 <? s32 (fw pb 48)) with false by (symmetry; apply Z.ltb_ge; lia);
replace (s32 (fw pb 48) <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
unfold hdr_cells. exact HDRc.
+
bato 0x9a0c0. release_frame FR ST usp. astep.
apply evt_done. right. split; [exact GOOD|]. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
replace (clamp_channels (s32 (fw pb 48))) with 2
by (unfold clamp_channels; replace (2 <? s32 (fw pb 48)) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
unfold hdr_cells. exact HDRc.
-
assert (TAKEN : exists u, Z_to_bv 64 (s32 (fw pb 40)) = Z_to_bv 64 u /\ 3 <= u < 2^64).
{ destruct (Z_lt_le_dec (s32 (fw pb 40)) 0) as [NEG|NN].
- exists (s32 (fw pb 40) + 2^64). split; [apply lit64_neg_wrap; lia| lia].
- exists (s32 (fw pb 40)). split; [reflexivity| lia]. }
destruct TAKEN as (u & Eu & Hu). rewrite Eu.
astep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [| exfalso; lia]. clear K3.
bato 0x56d08.
apply evt_done. left. split; [exact BAD|]. eexists. reflexivity.
Qed.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_calloc_p : Z := 0x67e9c.
Definition e_asan_memcpy_p : Z := 0x66314.
Definition e_free_p : Z := 0x67e94.

Notation p2h_frame c2 c1 c0 cra := [C8 c2; C8 c1; C8 c0; C8 cra] (only parsing).

Lemma p2h_small : forall (P size usp lo errf : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
- 2^31 <= size < 80 ->
aobj asegs m RF_STDERR_VAR 8 ->
ro_cells asegs m RF_GOT_STDERR [C8 (Z_to_bv 64 RF_STDERR_VAR)] -> ro_cells asegs m RF_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
stk asegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_p2h_fprintf_small) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 errf) (Z_to_bv 64 P2H_FMT_NOTIFY) (Z_to_bv 64 P2H_MSG_TOO_SMALL) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_fprintf) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (p2h_frame s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_packet_to_header) fc None m (seg_rom asegs)).
Proof.
intros until m. intros Hsz OBV GOTE VARE ST LO LOS SPH CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_packet_to_header, e_wrap_fprintf, RA_p2h_fprintf_small, RF_GOT_STDERR, RF_STDERR_VAR, P2H_FMT_NOTIFY, P2H_MSG_TOO_SMALL,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
assert (V8 : 997264 mod 8 = 0) by reflexivity.
ato 0x99440. astep. sh_if.
ato 0x56c1c.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma p2h_tail0 : forall (pc0 usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c2 c1 c0 cra : word) F fc (m : mem),
pc0 = RA_p2h_fprintf_small \/ pc0 = RA_p2h_free ->
stk asegs m lo (usp + -32) -> lo <= usp + -32 -> usp < 2^63 ->
rw_cells asegs m (usp + -32) (p2h_frame c2 c1 c0 cra) -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m (seg_rom asegs)
/\ stk asegs m lo usp)
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 pc0)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros PC ST LO SPH FR MI.
pose proof ST as (STa & STb & _).
destruct PC as [-> | ->]; unfold RA_p2h_fprintf_small, RA_p2h_free.
- replace (ret_pc (Z_to_bv 64 0x99578)) with (Z_to_bv 64 0x99578) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x995d0. release_frame FR ST usp. astep.
apply evt_done. split; [reflexivity| exact ST].
- replace (ret_pc (Z_to_bv 64 0x995b4)) with (Z_to_bv 64 0x995b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x995d0. release_frame FR ST usp. astep.
apply evt_done. split; [reflexivity| exact ST].
Qed.

Section Magic.
Variables (P : Z) (pb : list byte) (m : mem).
Variables (rav spv gp tp t0 t1 t2 s0 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis PK : u8ro asegs m P pb.
Hypothesis L8 : (8 <= length pb)%nat.
Hypothesis MG : u8ro asegs m P2H_MAGIC MAGIC_BYTES.
Hypothesis OBP : aobj asegs m P (Z.of_nat (length pb)).
Hypothesis OBM : aobj asegs m P2H_MAGIC 9.
Hypothesis Ppos : 0 < P.
Hypothesis MI : mem_inv asegs m.

Definition p2h_magic_post : machine_state -> Prop := fun ms' =>
exists a0' a1' a2' a5' a6' : word,
(ms' = MS (mkR rav spv gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0' a1' a2' (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a5' a6' a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_EXIT) fc None m (seg_rom asegs)
/\ firstn 8 pb <> MAGIC_BYTES)
\/ (ms' = MS (mkR rav spv gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0' a1' a2' (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a5' a6' a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_ALLOC) fc None m (seg_rom asegs)
/\ firstn 8 pb = MAGIC_BYTES).

Lemma p2h_magic_loop : forall (k i : nat) (a0v a1v a5v a6v : word),
(i + k = 8)%nat -> (0 < k)%nat -> firstn i pb = firstn i MAGIC_BYTES ->
evt asegs p2h_magic_post
(MS (mkR rav spv gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0v a1v (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a5v a6v a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_LOOP) fc None m (seg_rom asegs)).
Proof using PK L8 MG OBP OBM Ppos MI.
induction k as [|k IH]; intros i a0v a1v a5v a6v Hik Hk PRE; [lia|].
pose proof (bytes_at_bound _ _ _ _ PK) as BX. pose proof (bytes_at_bound _ _ _ _ MG) as BY.
rewrite MAGIC_BYTES_eq in BY. cbn [length] in BY. unfold P2H_MAGIC in BY.
assert (LM : length MAGIC_BYTES = 8%nat) by reflexivity.
pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
set (x := hb pb i). set (y := hb MAGIC_BYTES i).
pose proof (u8ro_read asegs m P pb (Z.of_nat i) x (wa (P + Z.of_nat i)) PK
ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) eq_refl) as RX.
pose proof (u8ro_read asegs m P2H_MAGIC MAGIC_BYTES (Z.of_nat i) y (wa (P2H_MAGIC + Z.of_nat i)) MG
ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) eq_refl) as RY.
unfold P2H_LOOP, P2H_MAGIC in *.
ato 0x99468. astep. chk_merge OBP 1.
ato 0x99480. astep.
unfold shz. rewrite (shb_zero asegs m 145248 9 (145248 + Z.of_nat i) (proj2 (proj2 OBM)) ltac:(lia) ltac:(clear - Hik; Z.div_mod_to_equations; lia)).
lit_if.
astep. clear RX RY. astep. if_cases K; zify_cond K.
-
apply evt_done. unfold p2h_magic_post, P2H_EXIT, P2H_MAGIC. do 5 eexists. left. split; [reflexivity|].
intros E. apply K.
enough (Exy : x = y) by (rewrite Exy; reflexivity).
subst x y. unfold hb. rewrite <- E. rewrite nth_firstn. replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- assert (Exy : x = y) by (apply bv_eq; exact K).
astep. astep. if_cases K2; zify_cond K2.
+
apply evt_done. unfold p2h_magic_post, P2H_ALLOC, P2H_MAGIC. do 5 eexists. right. split; [reflexivity|].
replace 8%nat with (S i) by lia.
rewrite <- (firstn_all2 (n := S i) MAGIC_BYTES) by lia.
rewrite (firstn_S_hb pb i), (firstn_S_hb MAGIC_BYTES i) by lia. rewrite PRE. fold x. fold y. rewrite Exy. reflexivity.
+
astep. replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
apply (IH (S i)); [lia| lia|].
rewrite (firstn_S_hb pb i), (firstn_S_hb MAGIC_BYTES i) by lia. rewrite PRE. fold x. fold y. rewrite Exy. reflexivity.
Qed.
End Magic.

Lemma p2h_magic : forall (P size usp lo : Z) (pb : list byte)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
80 <= size < 2^31 -> u8ro asegs m P pb -> (8 <= length pb)%nat -> 0 < P ->
aobj asegs m P (Z.of_nat (length pb)) -> aobj asegs m P2H_MAGIC 9 ->
stk asegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 -> P + Z.of_nat (length pb) <= lo ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (m1 : mem),
munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ ((firstn 8 pb <> MAGIC_BYTES /\ exists (a1' a2' a5' a6' : word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a5' a6' a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom asegs)
/\ stk asegs m1 lo usp)
\/ (firstn 8 pb = MAGIC_BYTES /\ exists (a2' a5' a6' : word),
ms' = MS (mkR (Z_to_bv 64 RA_p2h_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 P)
(Z_to_bv 64 80) (Z_to_bv 64 1) a2' (Z_to_bv 64 P2H_MAGIC) (Z_to_bv 64 8) a5' a6' a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_p) fc None m1 (seg_rom asegs)
/\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (p2h_frame s2 s1 s0 ra))))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_packet_to_header) fc None m (seg_rom asegs)).
Proof.
intros until m. intros Hsz PK L8 Ppos OBP OBM ST LO LOS SPH PLO CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_packet_to_header, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (bytes_at_bound _ _ _ _ PK) as PB.
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x99440. astep. sh_if.
ato 0x99458.
pose proof (aobj_munch asegs _ m m1 P _ OBP MU (shfree_of_aobj asegs _ m P _ OF OBP)) as OBP1.
pose proof (aobj_munch asegs _ m m1 P2H_MAGIC 9 OBM MU (shfree_of_aobj asegs _ m P2H_MAGIC 9 OF OBM)) as OBM1.
pose proof (p2h_magic_ro m1 MI) as MG1.
eapply evt_cut.
{ change 0 with (Z.of_nat 0). change 145248 with P2H_MAGIC.
eapply (p2h_magic_loop P pb m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PK L8 MG1 OBP1 OBM1 Ppos MI 8 0); [reflexivity| lia| reflexivity]. }
cbv beta. intros ms' (a0' & a1' & a2' & a5' & a6' & [[-> NE]|[-> EQ]]).
-
unfold P2H_EXIT. pose proof ST as (STa & STb & _).
ato 0x995d0. release_frame FR ST usp. astep.
apply evt_done. exists m1. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
left. split; [exact NE|]. do 4 eexists. split; [reflexivity| exact ST].
-
unfold P2H_ALLOC, e_calloc_p, RA_p2h_calloc.
ato 0x67e9c.
apply evt_done. exists m1. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
right. split; [exact EQ|]. do 3 eexists. split; [reflexivity|]. split; [exact ST| exact FR].
Qed.

Lemma p2h_copy : forall (P D usp : Z) (gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_p2h_memcpy) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P)
(Z_to_bv 64 D) (Z_to_bv 64 P) (Z_to_bv 64 80) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_asan_memcpy_p) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_p2h_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_p2h_calloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI. unfold RA_p2h_calloc, RA_p2h_memcpy, e_asan_memcpy_p.
replace (ret_pc (Z_to_bv 64 0x994c4)) with (Z_to_bv 64 0x994c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x66314.
apply evt_done. reflexivity.
Qed.

Lemma p2h_free : forall (P D usp : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_p2h_free) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P)
(Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_free_p) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_p2h_fprintf_mode) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_p2h_fprintf_mode)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI. unfold RA_p2h_fprintf_mode, RA_p2h_free, e_free_p.
replace (ret_pc (Z_to_bv 64 0x995ac)) with (Z_to_bv 64 0x995ac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x67e94.
apply evt_done. reflexivity.
Qed.

Lemma p2h_mode : forall (P D usp lo errf : Z) (pb : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c2 c1 c0 cra : word) F fc (m : mem),
(80 <= length pb)%nat ->
rw_cells asegs m D (hdr_cells pb (Z_to_bv 64 (fw pb 48))) ->
aobj asegs m D 80 -> D mod 8 = 0 -> 0 < D -> D + 80 <= lo -> (D + 80 <= SH_LO \/ SH_HI <= D) ->
aobj asegs m RF_STDERR_VAR 8 ->
ro_cells asegs m RF_GOT_STDERR [C8 (Z_to_bv 64 RF_STDERR_VAR)] -> ro_cells asegs m RF_STDERR_VAR [C8 (Z_to_bv 64 errf)] ->
stk asegs m lo (usp + -32) -> lo <= usp + -32 -> SH_HI <= lo -> usp < 2^63 ->
rw_cells asegs m (usp + -32) (p2h_frame c2 c1 c0 cra) -> mem_inv asegs m ->
evt asegs (fun ms' =>
(~ (0 <= s32 (fw pb 40) < 3)
/\ ms' = MS (mkR (Z_to_bv 64 RA_p2h_fprintf_mode) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P)
(Z_to_bv 64 errf) (Z_to_bv 64 P2H_FMT_NOTIFY) (Z_to_bv 64 P2H_MSG_BAD_MODE) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_fprintf) fc None m (seg_rom asegs))
\/ (0 <= s32 (fw pb 40) < 3 /\ exists (m1 : mem) (a1' a2' : word),
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7
c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(D, D + 80)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 D (hdr_cells pb (Z_to_bv 64 (clamp_channels (s32 (fw pb 48)))))))
(MS (mkR (Z_to_bv 64 RA_p2h_memcpy) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 D) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_p2h_memcpy)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros L80 HDR OBD D8 Dpos DLO DOFF OBV GOTE VARE ST LO LOS SPH FR MI.
unfold RA_p2h_memcpy, RA_p2h_fprintf_mode, e_wrap_fprintf, RF_GOT_STDERR, RF_STDERR_VAR, P2H_FMT_NOTIFY, P2H_MSG_BAD_MODE in *.
replace (ret_pc (Z_to_bv 64 0x994d4)) with (Z_to_bv 64 0x994d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof DOFF as DOFF'. unfold SH_LO, SH_HI in DOFF'.
pose proof ST as (STa & STb & _).
pose proof (s32_range (fw pb 40)) as R40. pose proof (fw_range pb 40) as U40.
pose proof (s32_range (fw pb 48)) as R48. pose proof (fw_range pb 48) as U48.
assert (V8 : 997264 mod 8 = 0) by reflexivity.
pose proof (munch_refl [(D, D + 80)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(D, D + 80)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof HDR as HDRc. unfold hdr_cells in HDRc.
ato 0x994ec. rewrite sx32_w by exact U40.
astep.
assert (CASES : 0 <= s32 (fw pb 40) < 3 \/ ~ (0 <= s32 (fw pb 40) < 3)) by lia.
destruct CASES as [GOOD|BAD].
-
astep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|]. clear K3.
ato 0x9950c. rewrite sx32_w by exact U48.
astep.
astep. if_cases K4; zify_cond K4; rewrite ?signed_lit_small in K4 by lia.
+
ato 0x99530. rewrite sx32_w by exact U48.
astep. rewrite (lts_zero_lit (s32 (fw pb 48))) by lia. if_cases K5; zify_cond K5.
*
ato 0x995d0. release_frame FR ST usp. astep.
apply evt_done. right. split; [exact GOOD|]. exists m. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
replace (clamp_channels (s32 (fw pb 48))) with (s32 (fw pb 48))
by (unfold clamp_channels; replace (2 <? s32 (fw pb 48)) with false by (symmetry; apply Z.ltb_ge; lia);
replace (s32 (fw pb 48) <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
eapply rw_cells_samebytes; [exact HDR| | |].
-- cbn. rewrite length_firstn. repeat split; try lia; exact I.
-- unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_s32_fw. reflexivity.
-- cbn. reflexivity.
*
ato 0x99544.
ato 0x995d0. release_frame FR ST usp. astep.
apply evt_done. right. split; [exact GOOD|]. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
replace (clamp_channels (s32 (fw pb 48))) with 1
by (unfold clamp_channels; replace (2 <? s32 (fw pb 48)) with false by (symmetry; apply Z.ltb_ge; lia);
replace (s32 (fw pb 48) <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
unfold hdr_cells. exact HDRc.
+
ato 0x995d0. release_frame FR ST usp. astep.
apply evt_done. right. split; [exact GOOD|]. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
replace (clamp_channels (s32 (fw pb 48))) with 2
by (unfold clamp_channels; replace (2 <? s32 (fw pb 48)) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
unfold hdr_cells. exact HDRc.
-
assert (TAKEN : exists u, Z_to_bv 64 (s32 (fw pb 40)) = Z_to_bv 64 u /\ 3 <= u < 2^64).
{ destruct (Z_lt_le_dec (s32 (fw pb 40)) 0) as [NEG|NN].
- exists (s32 (fw pb 40) + 2^64). split; [apply lit64_neg_wrap; lia| lia].
- exists (s32 (fw pb 40)). split; [reflexivity| lia]. }
destruct TAKEN as (u & Eu & Hu). rewrite Eu.
astep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [| exfalso; lia]. clear K3.
ato 0x56c1c.
apply evt_done. left. split; [exact BAD| reflexivity].
Qed.
