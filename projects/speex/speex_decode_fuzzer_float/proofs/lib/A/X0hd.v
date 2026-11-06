(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X03z X04v X00b.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X0ux X0vt X0ra.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition imemmove_entry := 0x79bd4%Z.

Local Ltac store_byte b := change (Z_to_bv 64 (bv_unsigned b)) with (zxb b); rewrite (le1_zxb b); mem_after_store.

Lemma bytes_at_cons1 : forall (m : mem) A (b : byte) bs, bytes_at bsegs m A [b] -> bytes_at bsegs m (A + 1) bs -> bytes_at bsegs m A (b :: bs).
Proof. intros m A b bs H1 H2. change (b :: bs) with ([b] ++ bs). apply (proj2 (bytes_at_app bsegs m A [b] bs)). split; [exact H1 | exact H2]. Qed.
Lemma bytes_at_snoc1 : forall (m : mem) A (b : byte) bs, bytes_at bsegs m A bs -> bytes_at bsegs m (A + Z.of_nat (length bs)) [b] -> bytes_at bsegs m A (bs ++ [b]).
Proof. intros m A b bs H1 H2. apply (proj2 (bytes_at_app bsegs m A bs [b])). split; [exact H1 | exact H2]. Qed.

Lemma imm_fwd_loop : forall (k : nat) (S D e : Z) (rest jk : list byte)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
length rest = Datatypes.S k -> e = D + Z.of_nat (Datatypes.S k) -> D < S -> 0 <= D -> S + Z.of_nat (Datatypes.S k) <= 2^64 ->
bytes_at bsegs m S rest -> rw_cells bsegs m D [CB (Datatypes.S k) jk] -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a1' a3' a4' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79bf8) fc None m' (seg_rom bsegs)
/\ munch [(D, e)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ bytes_at bsegs m' D rest)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) (Z_to_bv 64 e) (Z_to_bv 64 D) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79be4) fc None m (seg_rom bsegs)).
Proof.
induction k as [|k IH]; intros S D e rest jk ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
LR -> DS D0 SB SRC DST MI.
- destruct rest as [|b [|? ?]]; try discriminate LR.
pose proof (ro_C1_of_bytes m S b SRC) as CB0.
pose proof (munch_refl [(D, D + Z.of_nat 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
lstep. lstep. store_byte b.
lstep. lstep. lstep.
replace (bv_eqb (Z_to_bv 64 (D + 1)) (Z_to_bv 64 (D + Z.of_nat 1))) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; reflexivity).
cbv iota. cbn [negb]. cbv iota.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
exact (proj2 (proj1 DST)).
- destruct rest as [|b rest]; [discriminate LR|]. injection LR as LR.
change (b :: rest) with ([b] ++ rest) in SRC. apply (proj1 (bytes_at_app bsegs m S [b] rest)) in SRC. destruct SRC as [SRC1 SRC2].
cbn [length] in SRC2. change (Z.of_nat 1) with 1 in SRC2.
pose proof (ro_C1_of_bytes m S b SRC1) as CB0.
pose proof (rw_cells_bound bsegs m D _ DST) as DBD. cbn [cells_size csize Nat.add] in DBD.
apply (rw_cells_split_CB bsegs m D [] _ jk [] [1%nat; Datatypes.S k]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app bsegs m D [_] [_])) in DST. destruct DST as [DST1 DST2]. cbn [cells_size csize Nat.add] in DST2. change (Z.of_nat 1) with 1 in DST2.
pose proof (munch_refl [(D, D + Z.of_nat (Datatypes.S (Datatypes.S k)))] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
lstep. lstep. store_byte b.
lstep. lstep. lstep.
replace (bv_eqb (Z_to_bv 64 (D + 1)) (Z_to_bv 64 (D + Z.of_nat (Datatypes.S (Datatypes.S k))))) with false.
2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit by lia. lia. }
cbn [negb]. cbv iota.
eapply evt_mono.
{ eapply (IH (S + 1) (D + 1) (D + Z.of_nat (Datatypes.S (Datatypes.S k))) rest); [exact LR | lia | lia | lia | lia | eassumption | eassumption | assumption]. }
intros ms' (a1' & a3' & a4' & m' & -> & MU' & WM' & MI' & BY').
do 4 eexists. split; [reflexivity|].
split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia|].
split; [eapply wmono_trans; eassumption|]. split; [exact MI'|].
apply bytes_at_cons1; [| exact BY'].
lazymatch goal with H : rw_cells bsegs _ D [C1 b] |- _ =>
apply (bytes_at_agree bsegs _ m' _ _ (proj2 (proj1 H))); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; cbn in Hx; lia end.
Qed.

Lemma imm_bwd_loop : forall (k : nat) (i S D : Z) (pre jk : list byte)
(ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
i = Z.of_nat k -> length pre = Datatypes.S k -> S < D -> 0 <= S -> D + Z.of_nat (Datatypes.S k) <= 2^63 ->
bytes_at bsegs m S pre -> rw_cells bsegs m D [CB (Datatypes.S k) jk] -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a3' a4' a5' a6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 1) a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79c28) fc None m' (seg_rom bsegs)
/\ munch [(D, D + Z.of_nat (Datatypes.S k))] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ bytes_at bsegs m' D pre)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 1) (Z_to_bv 64 i) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79c0c) fc None m (seg_rom bsegs)).
Proof.
induction k as [|k IH]; intros i S D pre jk ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
Hi LP DS S0 DB SRC DST MI.
- destruct pre as [|b [|? ?]]; try discriminate LP.
remember (S + i) as Si eqn:ESi. remember (D + i) as Di eqn:EDi.
assert (SRCi : bytes_at bsegs m Si [b]) by (replace Si with S by lia; exact SRC).
assert (DSTi : rw_cells bsegs m Di [CB 1 jk]) by (replace Di with D by lia; exact DST).
pose proof (ro_C1_of_bytes m Si b SRCi) as CB0. clear SRC DST.
pose proof (munch_refl [(D, D + Z.of_nat 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (EUi : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
assert (EUSi : bv_unsigned (Z_to_bv 64 Si) = Si) by (apply unsigned_lit; lia).
assert (EUDi : bv_unsigned (Z_to_bv 64 Di) = Di) by (apply unsigned_lit; lia).
lstep. rewrite <- ESi. lstep. lstep. rewrite <- EDi. lstep. lstep. lstep. store_byte b.
lstep.
replace (bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (i + 1))) with false.
2:{ symmetry. unfold bv_ltu. apply Z.ltb_ge. rewrite !unsigned_lit by lia. lia. }
cbv iota.
apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
replace D with Di by lia. exact (proj2 (proj1 DSTi)).
- assert (NE : pre <> []) by (intros ->; discriminate LP).
destruct (exists_last NE) as (pre' & b & ->). clear NE.
rewrite length_app in LP. cbn [length] in LP. assert (LP' : length pre' = Datatypes.S k) by lia. clear LP.
apply (proj1 (bytes_at_app bsegs m S pre' [b])) in SRC. destruct SRC as [SRC1 SRCi]. rewrite LP' in SRCi.
pose proof (rw_cells_bound bsegs m D _ DST) as DBD. cbn [cells_size csize Nat.add] in DBD.
apply (rw_cells_split_CB bsegs m D [] _ jk [] [Datatypes.S k; 1%nat]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app bsegs m D [_] [_])) in DST. destruct DST as [DST1 DSTi]. cbn [cells_size csize Nat.add] in DSTi.
rewrite Nat.add_0_r in DSTi.
remember (S + i) as Si eqn:ESi. remember (D + i) as Di eqn:EDi.
replace (S + Z.of_nat (Datatypes.S k)) with Si in SRCi by lia. replace (D + Z.of_nat (Datatypes.S k)) with Di in DSTi by lia.
pose proof (ro_C1_of_bytes m Si b SRCi) as CB0.
pose proof (munch_refl [(D, D + Z.of_nat (Datatypes.S (Datatypes.S k)))] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (EUi : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
assert (EUSi : bv_unsigned (Z_to_bv 64 Si) = Si) by (apply unsigned_lit; lia).
assert (EUDi : bv_unsigned (Z_to_bv 64 Di) = Di) by (apply unsigned_lit; lia).
lstep. rewrite <- ESi. lstep. lstep. rewrite <- EDi. lstep. lstep. lstep. store_byte b.
lstep.
replace (bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (i + 1))) with true.
2:{ symmetry. unfold bv_ltu. apply Z.ltb_lt. rewrite !unsigned_lit by lia. lia. }
cbv iota.
eapply evt_mono.
{ eapply (IH (i + -1) S D pre'); [lia | exact LP' | lia | lia | lia | eassumption | eassumption | assumption]. }
intros ms' (a3' & a4' & a5' & a6' & m' & -> & MU' & WM' & MI' & BY').
do 5 eexists. split; [reflexivity|].
split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia|].
split; [eapply wmono_trans; eassumption|]. split; [exact MI'|].
apply bytes_at_snoc1; [exact BY'|]. rewrite LP'. replace (D + Z.of_nat (Datatypes.S k)) with Di by lia.
lazymatch goal with H : rw_cells bsegs _ Di [C1 b] |- _ =>
apply (bytes_at_agree bsegs _ m' _ _ (proj2 (proj1 H))); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; cbn in Hx; lia end.
Qed.

Definition imemmove_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(d : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(d, d + Z.of_nat (length src))] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' d [CB (length src) src].

Lemma rw_CB_of_bytes : forall (m : mem) A (bs : list byte), bytes_at bsegs m A bs -> wr_at bsegs m A (Z.of_nat (length bs)) -> rw_cells bsegs m A [CB (length bs) bs].
Proof.
intros m A bs BY WR. split; [split|].
- cbn. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY.
- cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.

Lemma imemmove_spec : forall (d s : Z) (src junk : list byte) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem),
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length src)) ->
0 <= d -> 0 <= s -> d + Z.of_nat (length src) <= 2^63 -> s + Z.of_nat (length src) <= 2^63 ->
bytes_at bsegs m s src -> rw_cells bsegs m d [CB (length src) junk] -> mem_inv bsegs m ->
evt bsegs (imemmove_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79bd4) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> -> -> D0 S0 DH SH SRC DST MI.
set (n := Z.of_nat (length src)) in *.
pose proof (munch_refl [(d, d + n)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
pose proof (proj2 DST) as WR. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
assert (FIN0 : forall m', m' = m -> d = s \/ n = 0 -> rw_cells bsegs m' d [CB (length src) src]).
{ intros m' -> [E|E].
- subst s. apply rw_CB_of_bytes; [exact SRC | exact WR].
- assert (length src = 0%nat) by lia. destruct src; [| discriminate]. destruct junk; [exact DST|].
destruct DST as [[[X _] _] _]. cbn in X. discriminate X. }
lstep. if_cases K; zify_cond K.
-
lstep. if_cases K2; zify_cond K2.
+
lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
apply FIN0; [reflexivity | left; lia].
+ lstep. if_cases K3; zify_cond K3.
* lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
apply FIN0; [reflexivity | right; lia].
*
lstep. lstep.
eapply evt_cut.
{ eapply (imm_bwd_loop (Nat.pred (length src)) (n + -1) s d src junk); [lia | lia | lia | lia | lia | exact SRC | | exact MI].
replace (Datatypes.S (Nat.pred (length src))) with (length src) by lia. exact DST. }
intros ms' (a3' & a4' & a5' & a6' & m' & -> & MU' & WM' & MI' & BY').
replace (Datatypes.S (Nat.pred (length src))) with (length src) in MU' by lia. fold n in MU'.
lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
apply rw_CB_of_bytes; [exact BY'|]. exact (wr_at_transport bsegs m m' d n WR WM').
-
lstep. if_cases K3; zify_cond K3.
+ lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
apply FIN0; [reflexivity | right; lia].
+
lstep. lstep.
eapply evt_cut.
{ eapply (imm_fwd_loop (Nat.pred (length src)) s d (d + n) src junk); [lia | lia | lia | lia | lia | exact SRC | | exact MI].
replace (Datatypes.S (Nat.pred (length src))) with (length src) by lia. exact DST. }
intros ms' (a1' & a3' & a4' & m' & -> & MU' & WM' & MI' & BY').
lstep. lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
apply rw_CB_of_bytes; [exact BY'|]. exact (wr_at_transport bsegs m m' d n WR WM').
Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition imemmove_entry := 0x79ae8%Z.

Local Ltac store_byte b := change (Z_to_bv 64 (bv_unsigned b)) with (zxb b); rewrite (le1_zxb b); mem_after_store.

Lemma bytes_at_cons1 : forall (m : mem) A (b : byte) bs, bytes_at asegs m A [b] -> bytes_at asegs m (A + 1) bs -> bytes_at asegs m A (b :: bs).
Proof. intros m A b bs H1 H2. change (b :: bs) with ([b] ++ bs). apply (proj2 (bytes_at_app asegs m A [b] bs)). split; [exact H1 | exact H2]. Qed.
Lemma bytes_at_snoc1 : forall (m : mem) A (b : byte) bs, bytes_at asegs m A bs -> bytes_at asegs m (A + Z.of_nat (length bs)) [b] -> bytes_at asegs m A (bs ++ [b]).
Proof. intros m A b bs H1 H2. apply (proj2 (bytes_at_app asegs m A bs [b])). split; [exact H1 | exact H2]. Qed.

Lemma imm_fwd_loop : forall (k : nat) (S D e : Z) (rest jk : list byte)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
length rest = Datatypes.S k -> e = D + Z.of_nat (Datatypes.S k) -> D < S -> 0 <= D -> S + Z.of_nat (Datatypes.S k) <= 2^64 ->
bytes_at asegs m S rest -> rw_cells asegs m D [CB (Datatypes.S k) jk] -> mem_inv asegs m ->
evt asegs (fun ms' => exists (a1' a3' a4' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79b0c) fc None m' (seg_rom asegs)
/\ munch [(D, e)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ bytes_at asegs m' D rest)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) (Z_to_bv 64 e) (Z_to_bv 64 D) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79af8) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros S D e rest jk ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
LR -> DS D0 SB SRC DST MI.
- destruct rest as [|b [|? ?]]; try discriminate LR.
pose proof (ro_C1_of_bytes m S b SRC) as CB0.
pose proof (munch_refl [(D, D + Z.of_nat 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
lstep. lstep. store_byte b.
lstep. lstep. lstep.
replace (bv_eqb (Z_to_bv 64 (D + 1)) (Z_to_bv 64 (D + Z.of_nat 1))) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; reflexivity).
cbv iota. cbn [negb]. cbv iota.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
exact (proj2 (proj1 DST)).
- destruct rest as [|b rest]; [discriminate LR|]. injection LR as LR.
change (b :: rest) with ([b] ++ rest) in SRC. apply (proj1 (bytes_at_app asegs m S [b] rest)) in SRC. destruct SRC as [SRC1 SRC2].
cbn [length] in SRC2. change (Z.of_nat 1) with 1 in SRC2.
pose proof (ro_C1_of_bytes m S b SRC1) as CB0.
pose proof (rw_cells_bound asegs m D _ DST) as DBD. cbn [cells_size csize Nat.add] in DBD.
apply (rw_cells_split_CB asegs m D [] _ jk [] [1%nat; Datatypes.S k]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app asegs m D [_] [_])) in DST. destruct DST as [DST1 DST2]. cbn [cells_size csize Nat.add] in DST2. change (Z.of_nat 1) with 1 in DST2.
pose proof (munch_refl [(D, D + Z.of_nat (Datatypes.S (Datatypes.S k)))] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
lstep. lstep. store_byte b.
lstep. lstep. lstep.
replace (bv_eqb (Z_to_bv 64 (D + 1)) (Z_to_bv 64 (D + Z.of_nat (Datatypes.S (Datatypes.S k))))) with false.
2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit by lia. lia. }
cbn [negb]. cbv iota.
eapply evt_mono.
{ eapply (IH (S + 1) (D + 1) (D + Z.of_nat (Datatypes.S (Datatypes.S k))) rest); [exact LR | lia | lia | lia | lia | eassumption | eassumption | assumption]. }
intros ms' (a1' & a3' & a4' & m' & -> & MU' & WM' & MI' & BY').
do 4 eexists. split; [reflexivity|].
split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia|].
split; [eapply wmono_trans; eassumption|]. split; [exact MI'|].
apply bytes_at_cons1; [| exact BY'].
lazymatch goal with H : rw_cells asegs _ D [C1 b] |- _ =>
apply (bytes_at_agree asegs _ m' _ _ (proj2 (proj1 H))); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; cbn in Hx; lia end.
Qed.

Lemma imm_bwd_loop : forall (k : nat) (i S D : Z) (pre jk : list byte)
(ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
i = Z.of_nat k -> length pre = Datatypes.S k -> S < D -> 0 <= S -> D + Z.of_nat (Datatypes.S k) <= 2^63 ->
bytes_at asegs m S pre -> rw_cells asegs m D [CB (Datatypes.S k) jk] -> mem_inv asegs m ->
evt asegs (fun ms' => exists (a3' a4' a5' a6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 1) a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79b3c) fc None m' (seg_rom asegs)
/\ munch [(D, D + Z.of_nat (Datatypes.S k))] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ bytes_at asegs m' D pre)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 1) (Z_to_bv 64 i) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79b20) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros i S D pre jk ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
Hi LP DS S0 DB SRC DST MI.
- destruct pre as [|b [|? ?]]; try discriminate LP.
remember (S + i) as Si eqn:ESi. remember (D + i) as Di eqn:EDi.
assert (SRCi : bytes_at asegs m Si [b]) by (replace Si with S by lia; exact SRC).
assert (DSTi : rw_cells asegs m Di [CB 1 jk]) by (replace Di with D by lia; exact DST).
pose proof (ro_C1_of_bytes m Si b SRCi) as CB0. clear SRC DST.
pose proof (munch_refl [(D, D + Z.of_nat 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (EUi : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
assert (EUSi : bv_unsigned (Z_to_bv 64 Si) = Si) by (apply unsigned_lit; lia).
assert (EUDi : bv_unsigned (Z_to_bv 64 Di) = Di) by (apply unsigned_lit; lia).
lstep. rewrite <- ESi. lstep. lstep. rewrite <- EDi. lstep. lstep. lstep. store_byte b.
lstep.
replace (bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (i + 1))) with false.
2:{ symmetry. unfold bv_ltu. apply Z.ltb_ge. rewrite !unsigned_lit by lia. lia. }
cbv iota.
apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
replace D with Di by lia. exact (proj2 (proj1 DSTi)).
- assert (NE : pre <> []) by (intros ->; discriminate LP).
destruct (exists_last NE) as (pre' & b & ->). clear NE.
rewrite length_app in LP. cbn [length] in LP. assert (LP' : length pre' = Datatypes.S k) by lia. clear LP.
apply (proj1 (bytes_at_app asegs m S pre' [b])) in SRC. destruct SRC as [SRC1 SRCi]. rewrite LP' in SRCi.
pose proof (rw_cells_bound asegs m D _ DST) as DBD. cbn [cells_size csize Nat.add] in DBD.
apply (rw_cells_split_CB asegs m D [] _ jk [] [Datatypes.S k; 1%nat]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app asegs m D [_] [_])) in DST. destruct DST as [DST1 DSTi]. cbn [cells_size csize Nat.add] in DSTi.
rewrite Nat.add_0_r in DSTi.
remember (S + i) as Si eqn:ESi. remember (D + i) as Di eqn:EDi.
replace (S + Z.of_nat (Datatypes.S k)) with Si in SRCi by lia. replace (D + Z.of_nat (Datatypes.S k)) with Di in DSTi by lia.
pose proof (ro_C1_of_bytes m Si b SRCi) as CB0.
pose proof (munch_refl [(D, D + Z.of_nat (Datatypes.S (Datatypes.S k)))] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (EUi : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
assert (EUSi : bv_unsigned (Z_to_bv 64 Si) = Si) by (apply unsigned_lit; lia).
assert (EUDi : bv_unsigned (Z_to_bv 64 Di) = Di) by (apply unsigned_lit; lia).
lstep. rewrite <- ESi. lstep. lstep. rewrite <- EDi. lstep. lstep. lstep. store_byte b.
lstep.
replace (bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (i + 1))) with true.
2:{ symmetry. unfold bv_ltu. apply Z.ltb_lt. rewrite !unsigned_lit by lia. lia. }
cbv iota.
eapply evt_mono.
{ eapply (IH (i + -1) S D pre'); [lia | exact LP' | lia | lia | lia | eassumption | eassumption | assumption]. }
intros ms' (a3' & a4' & a5' & a6' & m' & -> & MU' & WM' & MI' & BY').
do 5 eexists. split; [reflexivity|].
split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn [outside]; intros; lia|].
split; [eapply wmono_trans; eassumption|]. split; [exact MI'|].
apply bytes_at_snoc1; [exact BY'|]. rewrite LP'. replace (D + Z.of_nat (Datatypes.S k)) with Di by lia.
lazymatch goal with H : rw_cells asegs _ Di [C1 b] |- _ =>
apply (bytes_at_agree asegs _ m' _ _ (proj2 (proj1 H))); apply (agree_of_munch _ _ _ _ MU'); intros x Hx; cbn [outside]; cbn in Hx; lia end.
Qed.

Definition imemmove_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(d : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(d, d + Z.of_nat (length src))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' d [CB (length src) src].

Lemma rw_CB_of_bytes : forall (m : mem) A (bs : list byte), bytes_at asegs m A bs -> wr_at asegs m A (Z.of_nat (length bs)) -> rw_cells asegs m A [CB (length bs) bs].
Proof.
intros m A bs BY WR. split; [split|].
- cbn. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY.
- cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.

Lemma imemmove_spec : forall (d s : Z) (src junk : list byte) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem),
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length src)) ->
0 <= d -> 0 <= s -> d + Z.of_nat (length src) <= 2^63 -> s + Z.of_nat (length src) <= 2^63 ->
bytes_at asegs m s src -> rw_cells asegs m d [CB (length src) junk] -> mem_inv asegs m ->
evt asegs (imemmove_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x79ae8) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> -> -> D0 S0 DH SH SRC DST MI.
set (n := Z.of_nat (length src)) in *.
pose proof (munch_refl [(d, d + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
pose proof (proj2 DST) as WR. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
assert (FIN0 : forall m', m' = m -> d = s \/ n = 0 -> rw_cells asegs m' d [CB (length src) src]).
{ intros m' -> [E|E].
- subst s. apply rw_CB_of_bytes; [exact SRC | exact WR].
- assert (length src = 0%nat) by lia. destruct src; [| discriminate]. destruct junk; [exact DST|].
destruct DST as [[[X _] _] _]. cbn in X. discriminate X. }
lstep. if_cases K; zify_cond K.
-
lstep. if_cases K2; zify_cond K2.
+
lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
apply FIN0; [reflexivity | left; lia].
+ lstep. if_cases K3; zify_cond K3.
* lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
apply FIN0; [reflexivity | right; lia].
*
lstep. lstep.
eapply evt_cut.
{ eapply (imm_bwd_loop (Nat.pred (length src)) (n + -1) s d src junk); [lia | lia | lia | lia | lia | exact SRC | | exact MI].
replace (Datatypes.S (Nat.pred (length src))) with (length src) by lia. exact DST. }
intros ms' (a3' & a4' & a5' & a6' & m' & -> & MU' & WM' & MI' & BY').
replace (Datatypes.S (Nat.pred (length src))) with (length src) in MU' by lia. fold n in MU'.
lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
apply rw_CB_of_bytes; [exact BY'|]. exact (wr_at_transport asegs m m' d n WR WM').
-
lstep. if_cases K3; zify_cond K3.
+ lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
apply FIN0; [reflexivity | right; lia].
+
lstep. lstep.
eapply evt_cut.
{ eapply (imm_fwd_loop (Nat.pred (length src)) s d (d + n) src junk); [lia | lia | lia | lia | lia | exact SRC | | exact MI].
replace (Datatypes.S (Nat.pred (length src))) with (length src) by lia. exact DST. }
intros ms' (a1' & a3' & a4' & m' & -> & MU' & WM' & MI' & BY').
lstep. lstep. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
apply rw_CB_of_bytes; [exact BY'|]. exact (wr_at_transport asegs m m' d n WR WM').
Qed.
