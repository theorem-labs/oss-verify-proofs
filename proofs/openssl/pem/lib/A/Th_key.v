(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Th_tsd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Notation NEXT_KEY := (0xbc5258)%Z (only parsing).
Notation KEY_LOCK := (0xbc5260)%Z (only parsing).
Notation KEYS := (0xbc4e58)%Z (only parsing).
Notation TSD_MAIN := (0xbc5298)%Z (only parsing).
Notation NODTOR := (0x529678)%Z (only parsing).

Lemma th_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma kc_next : forall nk, 0 <= nk < 128 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (nk + 1))) 127) = Z_to_bv 64 ((nk + 1) mod 128).
Proof. intros nk H. rewrite unsigned_lit by lia. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition kc_tail_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SP KP nk j : Z) (dt sh rao s0o s1o s2o s3o s4o kold w : word),
    rw_cells asegs m KP [C4 kold] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    rw_cells asegs m (SP + -48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
    stk asegs m lo (SP + -48) -> 0 <= lo -> lo <= SP - 96 -> SP < 2 ^ 64 ->
    (KP + 4 <= SP - 96 \/ SP <= KP) -> (KP + 4 <= KEYS \/ KEY_LOCK + 12 <= KP) ->
    (KEY_LOCK + 12 <= SP - 96) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR rao (Z_to_bv 64 SP) gp tp t0' t1 t2 s0o s1o z64 a1' a2' a3' a4' a5' a6' a7' s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc rao) fc None m' (seg_rom asegs)
                 /\ munch [(SP - 96, SP); (KP, KP + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo SP
                 /\ rw_cells asegs m' KP [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 dt])
        (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 dt (Z_to_bv 64 KP) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 NEXT_KEY) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5295e8) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Ltac kc_end AMO FR ST SP :=
  do 4 ths;
  do 2 ths; do 14 ths;
  th_amo_step AMO; ths; th_if_lit;
  th_amo_step AMO; ths; th_if_lit;
  do 2 ths; th_if_lit;
  ths; th_if_lit; ths; th_if_lit; ths; th_if_lit;
  do 2 ths;
  do 7 ths; do 2 ths;
  release_frame FR ST SP;
  finish.

Theorem kc_tail_proof : kc_tail_stmt.
Proof.
  unfold kc_tail_stmt. intros until w. intros KC NK HNK KL KJ PROBE CASE FR ST LO0 LO SPH S1 S2 S3 MI.
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(SP - 96, SP); (KP, KP + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (AMO : amo_aligned AW (Z_to_bv 64 0xbc5260) = true) by (vm_compute; reflexivity).
  do 3 ths.
  do 2 ths.
  carve_frame 48%nat ST.
  do 10 ths.
  do 3 ths.
  th_amo_step AMO. ths. th_if_lit.
  th_amo_step AMO. ths. th_if_lit.
  do 4 ths.
  do 2 ths. th_if_lit.
  do 8 ths.
  release_frame FR0 ST (SP + -48).
  ths. rewrite (th_sx32_small nk) by lia.
  do 3 ths.
  do 2 ths. rewrite (key_scale nk HNK).
  ths.
  set (Pn := 12340824 + 8 * nk) in *.
  assert (HPn : 12340824 <= Pn /\ Pn + 8 <= 12341848) by (unfold Pn; lia).
  destruct CASE as [[-> ->] | [EJ WNZ]].
  - (* [comment removed for export] *)
    fold Pn in KJ, MU |- *. clearbody Pn. clear PROBE.
    do 2 ths. th_if_lit.
    kc_end AMO FR ST SP.
  - (* [comment removed for export] *)
    assert (WF : bv_eqb w (Z_to_bv 64 0) = false).
    { destruct (bv_eqb w (Z_to_bv 64 0)) eqn:E; [|reflexivity]. apply Fs.bv_eqb_eq in E. subst w. exfalso. apply WNZ. reflexivity. }
    assert (NJ : j <> nk).
    { intros E. rewrite E in EJ. destruct (Z.eq_dec nk 127) as [-> | N]; [vm_compute in EJ; discriminate | rewrite Z.mod_small in EJ by lia; lia]. }
    assert (NE : bv_eqb (Z_to_bv 64 j) (Z_to_bv 64 nk) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact NJ).
    set (Pj := 12340824 + 8 * j) in *.
    assert (HPj : 12340824 <= Pj /\ Pj + 8 <= 12341848) by (unfold Pj; lia).
    assert (NPj : Pj + 8 <= Pn \/ Pn + 8 <= Pj) by (unfold Pj, Pn; lia).
    assert (EPj : Pj = 12340824 + 8 * j) by reflexivity.
    clearbody Pn Pj.
    do 2 ths. rewrite WF; cbv iota.
    do 2 ths. rewrite (kc_next nk HNK), <- EJ.
    ths. rewrite NE; cbv beta iota delta [negb].
    do 2 ths. rewrite (key_scale j HJ).
    ths. rewrite <- EPj.
    do 2 ths. th_if_lit.
    kc_end AMO FR ST SP.
Qed.

(* [comment removed for export] *)
Definition key_create_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w tsd : word),
    rw_cells asegs m (bv_unsigned a0) [C4 kold] ->
    rw_cells asegs m (bv_unsigned tp + -88) [C8 tsd] -> 88 <= bv_unsigned tp -> (tsd = z64 \/ tsd = Z_to_bv 64 TSD_MAIN) ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk asegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 96 ->
    (bv_unsigned a0 + 4 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + 4 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned a0) ->
    KEY_LOCK + 12 <= bv_unsigned sp - 96 ->
    (bv_unsigned tp + -80 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned tp + -88) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 z64 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (if bv_eqb a1 z64 then Z_to_bv 64 NODTOR else a1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5295a4) fc None m (seg_rom asegs)).

Ltac kc_call dt lo sp KP nk j sh ra s0 s1 s2 s3 s4 kold w :=
  call (kc_tail_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp) KP nk j dt sh ra s0 s1 s2 s3 s4 kold w);
  [ first [eassumption | lia] .. | ];
  rewrite Z_to_bv_bv_unsigned; finish.

Theorem key_create_proof : key_create_stmt.
Proof.
  unfold key_create_stmt. intros until tsd. intros KC TC TP TV NK HNK KL KJ PROBE CASE ST LO0 LO S1 S2 S3 S4 S5 S6 MI.
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  set (KP := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 KP) by (unfold KP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 ths. do 3 ths.
  destruct TV as [-> | ->].
  - (* [comment removed for export] *)
    do 4 ths. th_if_lit. do 3 ths.
    destruct (bv_eqb a1 (Z_to_bv 64 0)) eqn:EA; cbv iota.
    + do 2 ths. kc_call (Z_to_bv 64 5412472) lo sp KP nk j sh ra s0 s1 s2 s3 s4 kold w.
    + ths. kc_call a1 lo sp KP nk j sh ra s0 s1 s2 s3 s4 kold w.
  - do 4 ths. th_if_lit. ths.
    destruct (bv_eqb a1 (Z_to_bv 64 0)) eqn:EA; cbv beta iota delta [negb].
    + do 2 ths. kc_call (Z_to_bv 64 5412472) lo sp KP nk j sh ra s0 s1 s2 s3 s4 kold w.
    + kc_call a1 lo sp KP nk j sh ra s0 s1 s2 s3 s4 kold w.
Qed.
