(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cr X1cs X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nw X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05p X09u X0ae X09j.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cu.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110 X106.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ogg_page_eos_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs)
/\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m
/\ a0 = wz (ogg_page_eos (ubytes hs)).

Lemma ogg_page_eos_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells bsegs m G (page_cells D og) ->
bytes_at bsegs m (D + pg_hdr og) hs ->
(27 <= length hs)%nat ->
mem_inv bsegs m ->
evt bsegs (ogg_page_eos_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_eos) fc None m (seg_rom bsegs)).
Proof.
intros until hs. intros -> PG HDR LEN MI. unfold A_ogg_page_eos, wz. unfold page_cells, wz in PG.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
step.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 5 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R5.
step.
step. step.
finish.
rewrite (unsigned_zxb_nth hs 5) by lia. reflexivity.
Qed.

Definition ogg_page_granulepos_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs)
/\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m
/\ a0 = wz (ogg_page_granulepos (ubytes hs)).

Lemma ogg_page_granulepos_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells bsegs m G (page_cells D og) ->
bytes_at bsegs m (D + pg_hdr og) hs ->
(27 <= length hs)%nat ->
mem_inv bsegs m ->
evt bsegs (ogg_page_granulepos_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_granulepos) fc None m (seg_rom bsegs)).
Proof.
intros until hs. intros -> PG HDR LEN MI. unfold A_ogg_page_granulepos, wz. unfold page_cells, wz in PG.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
step.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 6 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R6.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 7 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R7.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 8 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R8.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 9 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R9.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 10 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R10.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 11 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R11.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 12 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R12.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 13 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R13.
do 8 step.
do 15 ostep.
finish.

unfold ogg_page_granulepos, le64_at. rewrite wz_s64.
change (zslice 6 8 (ubytes hs)) with (zslice 6 (Z.of_nat 8) (ubytes hs)).
rewrite !zslice_S by (rewrite ?zlength_ubytes; lia). rewrite zslice_0.
norm_lit_idx. rewrite !znth_ubytes by lia. cbn [le_val].
word_bits.
Qed.

Definition ogg_page_serialno_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs)
/\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m
/\ a0 = wz (ogg_page_serialno (ubytes hs)).

Lemma ogg_page_serialno_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells bsegs m G (page_cells D og) ->
bytes_at bsegs m (D + pg_hdr og) hs ->
(27 <= length hs)%nat ->
mem_inv bsegs m ->
evt bsegs (ogg_page_serialno_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_serialno) fc None m (seg_rom bsegs)).
Proof.
intros until hs. intros -> PG HDR LEN MI. unfold A_ogg_page_serialno, wz. unfold page_cells, wz in PG.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
step.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 14 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R14.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 15 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R15.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 16 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R16.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 17 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R17.
do 4 step.
do 7 ostep.
finish.
unfold ogg_page_serialno, le32_at.
change (zslice 14 4 (ubytes hs)) with (zslice 14 (Z.of_nat 4) (ubytes hs)).
rewrite !zslice_S by (rewrite ?zlength_ubytes; lia). rewrite zslice_0.
norm_lit_idx. rewrite !znth_ubytes by lia. cbn [le_val].
word_bits.
Qed.

Definition ogg_page_packets_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs)
/\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m
/\ a0 = wz (ogg_page_packets (ubytes hs)).

Section Packets.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte).
Hypothesis PG : rw_cells bsegs m G (page_cells D og).
Hypothesis HDR : bytes_at bsegs m (D + pg_hdr og) hs.
Hypothesis LEN : (27 + Z.to_nat (znth (ubytes hs) 26) <= length hs)%nat.
Hypothesis TOP : D + pg_hdr og + Z.of_nat (length hs) < 2^64.
Hypothesis MI : mem_inv bsegs m.
Let H := D + pg_hdr og.
Let nseg := znth (ubytes hs) 26.

Notation POST := (ogg_page_packets_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m).

#[using="HDR LEN TOP MI"] Lemma packets_loop : forall (k : nat) (i : Z) x5 x6 x7 (va0 va1 va2 : word) x13 x14 x15 x16 x17 x28 x29 x30 x31,
Z.to_nat (nseg - i) = k -> 0 <= i < nseg ->
va0 = wz (count_lt255 (zslice 27 i (ubytes hs))) ->
va1 = wz (H + 27 + i) ->
va2 = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat 26) hs (Z_to_bv 8 0)) + (D + pg_hdr og) + 27) ->
evt bsegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 va0 va1 va2 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xc11b8) fc None m (seg_rom bsegs)).
Proof.
induction k as [|k IH]; intros i x5 x6 x7 va0 va1 va2 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi -> -> ->; [lia|].
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof HDR as (HB0 & HB1 & HB).
assert (Hnseg : nseg = bv_unsigned (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) by (unfold nseg; apply znth_ubytes; lia).
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as R26.
pose proof (count_lt255_bound (zslice 27 i (ubytes hs))) as CB. rewrite zlength_zslice in CB by (rewrite ?zlength_ubytes; lia).
unfold wz. subst H.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs (27 + i) _ HDR ltac:(lia) ltac:(lia) eq_refl) as RR.
replace (D + pg_hdr og + (27 + i)) with (D + pg_hdr og + 27 + i) in RR by lia.
ostep. ostep. ostep. ostep. ostep.
rewrite snez_byte_255 by apply byte_range.
pose proof (byte_range (nth (Z.to_nat (27 + i)) hs (Z_to_bv 8 0))) as Rb.
rewrite swrap32_small by (destruct (_ <? 255); lia).
ostep. if_cases K; zify_cond K; rewrite ?land_ones64, ?Z.mod_small in K by lia.
-
eapply (IH (i + 1)); [lia| lia | | f_equal; lia | reflexivity].
unfold wz. f_equal. rewrite zslice_snoc by (rewrite ?zlength_ubytes; lia). rewrite count_lt255_app. cbn [count_lt255].
rewrite znth_ubytes by lia. rewrite Z.add_0_r. reflexivity.
-
ostep. finish.
unfold ogg_page_packets, wz. fold nseg. replace nseg with (i + 1) by lia.
rewrite zslice_snoc by (rewrite ?zlength_ubytes; lia). rewrite count_lt255_app. cbn [count_lt255].
rewrite znth_ubytes by lia. rewrite Z.add_0_r. reflexivity.
Qed.

#[using="D og PG HDR LEN TOP MI H nseg"] Lemma packets_body : forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
evt bsegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz G) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 A_ogg_page_packets) fc None m (seg_rom bsegs)).
Proof.
intros. unfold A_ogg_page_packets, wz. pose proof PG as PG'. unfold page_cells, wz in PG'.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG') as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
assert (Hnseg : nseg = bv_unsigned (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) by (unfold nseg; apply znth_ubytes; lia).
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as R26.
step.
pose proof (bytes_at_read1 bsegs m (D + pg_hdr og) hs 26 _ HDR ltac:(lia) ltac:(lia) eq_refl) as RR.
ostep. ostep.
if_cases K; zify_cond K.
-   ostep. ostep. finish. unfold ogg_page_packets, wz. fold nseg. rewrite Hnseg, K. reflexivity.
- do 4 ostep.
eapply (packets_loop (Z.to_nat nseg) 0); [lia| lia| | unfold wz, H; f_equal; lia| f_equal; lia].
unfold wz. f_equal.
Qed.
End Packets.

Lemma ogg_page_packets_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells bsegs m G (page_cells D og) ->
bytes_at bsegs m (D + pg_hdr og) hs ->
(27 + Z.to_nat (znth (ubytes hs) 26) <= length hs)%nat ->
D + pg_hdr og + Z.of_nat (length hs) < 2^64 ->
mem_inv bsegs m ->
evt bsegs (ogg_page_packets_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_packets) fc None m (seg_rom bsegs)).
Proof. intros until hs. intros -> PG HDR LEN TOP MI. eapply packets_body; eassumption. Qed.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ogg_page_eos_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
/\ a0 = wz (ogg_page_eos (ubytes hs)).

Lemma ogg_page_eos_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells asegs m G (page_cells D og) ->
bytes_at asegs m (D + pg_hdr og) hs ->
(27 <= length hs)%nat ->
mem_inv asegs m ->
evt asegs (ogg_page_eos_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_eos) fc None m (seg_rom asegs)).
Proof.
intros until hs. intros -> PG HDR LEN MI. unfold A_ogg_page_eos, wz. unfold page_cells, wz in PG.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
step.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 5 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R5.
step.
step. step.
finish.
rewrite (unsigned_zxb_nth hs 5) by lia. reflexivity.
Qed.

Definition ogg_page_granulepos_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
/\ a0 = wz (ogg_page_granulepos (ubytes hs)).

Lemma ogg_page_granulepos_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells asegs m G (page_cells D og) ->
bytes_at asegs m (D + pg_hdr og) hs ->
(27 <= length hs)%nat ->
mem_inv asegs m ->
evt asegs (ogg_page_granulepos_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_granulepos) fc None m (seg_rom asegs)).
Proof.
intros until hs. intros -> PG HDR LEN MI. unfold A_ogg_page_granulepos, wz. unfold page_cells, wz in PG.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
step.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 6 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R6.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 7 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R7.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 8 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R8.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 9 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R9.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 10 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R10.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 11 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R11.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 12 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R12.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 13 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R13.
do 8 step.
do 15 ostep.
finish.

unfold ogg_page_granulepos, le64_at. rewrite wz_s64.
change (zslice 6 8 (ubytes hs)) with (zslice 6 (Z.of_nat 8) (ubytes hs)).
rewrite !zslice_S by (rewrite ?zlength_ubytes; lia). rewrite zslice_0.
norm_lit_idx. rewrite !znth_ubytes by lia. cbn [le_val].
word_bits.
Qed.

Definition ogg_page_serialno_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
/\ a0 = wz (ogg_page_serialno (ubytes hs)).

Lemma ogg_page_serialno_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells asegs m G (page_cells D og) ->
bytes_at asegs m (D + pg_hdr og) hs ->
(27 <= length hs)%nat ->
mem_inv asegs m ->
evt asegs (ogg_page_serialno_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_serialno) fc None m (seg_rom asegs)).
Proof.
intros until hs. intros -> PG HDR LEN MI. unfold A_ogg_page_serialno, wz. unfold page_cells, wz in PG.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
step.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 14 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R14.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 15 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R15.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 16 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R16.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 17 _ HDR ltac:(lia) ltac:(lia) eq_refl) as R17.
do 4 step.
do 7 ostep.
finish.
unfold ogg_page_serialno, le32_at.
change (zslice 14 4 (ubytes hs)) with (zslice 14 (Z.of_nat 4) (ubytes hs)).
rewrite !zslice_S by (rewrite ?zlength_ubytes; lia). rewrite zslice_0.
norm_lit_idx. rewrite !znth_ubytes by lia. cbn [le_val].
word_bits.
Qed.

Definition ogg_page_packets_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(hs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
/\ a0 = wz (ogg_page_packets (ubytes hs)).

Section Packets.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte).
Hypothesis PG : rw_cells asegs m G (page_cells D og).
Hypothesis HDR : bytes_at asegs m (D + pg_hdr og) hs.
Hypothesis LEN : (27 + Z.to_nat (znth (ubytes hs) 26) <= length hs)%nat.
Hypothesis TOP : D + pg_hdr og + Z.of_nat (length hs) < 2^64.
Hypothesis MI : mem_inv asegs m.
Let H := D + pg_hdr og.
Let nseg := znth (ubytes hs) 26.

Notation POST := (ogg_page_packets_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m).

#[using="HDR LEN TOP MI"] Lemma packets_loop : forall (k : nat) (i : Z) x5 x6 x7 (va0 va1 va2 : word) x13 x14 x15 x16 x17 x28 x29 x30 x31,
Z.to_nat (nseg - i) = k -> 0 <= i < nseg ->
va0 = wz (count_lt255 (zslice 27 i (ubytes hs))) ->
va1 = wz (H + 27 + i) ->
va2 = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat 26) hs (Z_to_bv 8 0)) + (D + pg_hdr og) + 27) ->
evt asegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 va0 va1 va2 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xb8a88) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros i x5 x6 x7 va0 va1 va2 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi -> -> ->; [lia|].
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof HDR as (HB0 & HB1 & HB).
assert (Hnseg : nseg = bv_unsigned (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) by (unfold nseg; apply znth_ubytes; lia).
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as R26.
pose proof (count_lt255_bound (zslice 27 i (ubytes hs))) as CB. rewrite zlength_zslice in CB by (rewrite ?zlength_ubytes; lia).
unfold wz. subst H.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs (27 + i) _ HDR ltac:(lia) ltac:(lia) eq_refl) as RR.
replace (D + pg_hdr og + (27 + i)) with (D + pg_hdr og + 27 + i) in RR by lia.
ostep. ostep. ostep. ostep. ostep.
rewrite snez_byte_255 by apply byte_range.
pose proof (byte_range (nth (Z.to_nat (27 + i)) hs (Z_to_bv 8 0))) as Rb.
rewrite swrap32_small by (destruct (_ <? 255); lia).
ostep. if_cases K; zify_cond K; rewrite ?land_ones64, ?Z.mod_small in K by lia.
-
eapply (IH (i + 1)); [lia| lia | | f_equal; lia | reflexivity].
unfold wz. f_equal. rewrite zslice_snoc by (rewrite ?zlength_ubytes; lia). rewrite count_lt255_app. cbn [count_lt255].
rewrite znth_ubytes by lia. rewrite Z.add_0_r. reflexivity.
-
ostep. finish.
unfold ogg_page_packets, wz. fold nseg. replace nseg with (i + 1) by lia.
rewrite zslice_snoc by (rewrite ?zlength_ubytes; lia). rewrite count_lt255_app. cbn [count_lt255].
rewrite znth_ubytes by lia. rewrite Z.add_0_r. reflexivity.
Qed.

#[using="D og PG HDR LEN TOP MI H nseg"] Lemma packets_body : forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
evt asegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz G) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 A_ogg_page_packets) fc None m (seg_rom asegs)).
Proof.
intros. unfold A_ogg_page_packets, wz. pose proof PG as PG'. unfold page_cells, wz in PG'.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG') as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HDR as (HB0 & HB1 & HB).
assert (Hnseg : nseg = bv_unsigned (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) by (unfold nseg; apply znth_ubytes; lia).
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as R26.
step.
pose proof (bytes_at_read1 asegs m (D + pg_hdr og) hs 26 _ HDR ltac:(lia) ltac:(lia) eq_refl) as RR.
ostep. ostep.
if_cases K; zify_cond K.
-   ostep. ostep. finish. unfold ogg_page_packets, wz. fold nseg. rewrite Hnseg, K. reflexivity.
- do 4 ostep.
eapply (packets_loop (Z.to_nat nseg) 0); [lia| lia| | unfold wz, H; f_equal; lia| f_equal; lia].
unfold wz. f_equal.
Qed.
End Packets.

Lemma ogg_page_packets_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (G D : Z) (og : page) (hs : list byte),
a0 = wz G ->
rw_cells asegs m G (page_cells D og) ->
bytes_at asegs m (D + pg_hdr og) hs ->
(27 + Z.to_nat (znth (ubytes hs) 26) <= length hs)%nat ->
D + pg_hdr og + Z.of_nat (length hs) < 2^64 ->
mem_inv asegs m ->
evt asegs (ogg_page_packets_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_packets) fc None m (seg_rom asegs)).
Proof. intros until hs. intros -> PG HDR LEN TOP MI. eapply packets_body; eassumption. Qed.

