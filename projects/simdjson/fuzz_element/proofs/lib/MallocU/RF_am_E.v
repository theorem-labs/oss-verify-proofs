(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: musl's AT_RANDOM auxv walk is proved once for any list of key-value pairs (raux_walk) instead of step by step over the fixed twenty-word auxv, and the auxv invariant's walk conjunct, unused here, is dropped where the invariant is taken apart. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.simdjson.fuzz_element.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.U Require Import F_memcpy.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at usegs m S src -> length src = Z.to_nat n ->
  rw_cells usegs m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd06e8) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  do 15 eexists. split; [reflexivity|]. auto.
Qed.

Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at usegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes usegs m a 8 = Some (le8 w).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read usegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) -> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells usegs m A cs1 -> rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells usegs m A (cs1 ++ cs2).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

(* musl's [get_random_secret] auxv walk, proved once for any pair list [L]:
   [for (i=0; auxv[i]; i+=2) if (auxv[i]==AT_RANDOM) memcpy(&secret, auxv[i+1]+8, 8);]
   The loop head is 0xc2a58 (s1 = 16 * pairs done, a0 = av, s4 = 25); the
   AT_RANDOM body is 0xc2a3c (memcpy to the frame cell 0(sp)); the exit is 0xc2a68.
   [aux_cur pre b0] is the frame cell after the pairs [pre]: the secret once an
   AT_RANDOM pair was seen, else the initial bytes [b0]. *)
Definition aux_cur (pre : list (Z * Z)) (b0 : list byte) : list byte :=
  if existsb (fun p => fst p =? 25) pre then le8 rr_secret else b0.

Lemma aux_cur_25 : forall pre v b0, aux_cur (pre ++ [(25, v)]) b0 = le8 rr_secret.
Proof.
  intros pre v b0. unfold aux_cur. rewrite existsb_app.
  replace (existsb (fun p : Z * Z => fst p =? 25) [(25, v)]) with true by reflexivity.
  rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma aux_cur_skip : forall pre k v b0, k <> 25 -> aux_cur (pre ++ [(k, v)]) b0 = aux_cur pre b0.
Proof.
  intros pre k v b0 Hk. unfold aux_cur. rewrite existsb_app.
  replace (existsb (fun p : Z * Z => fst p =? 25) [(k, v)]) with false
    by (symmetry; cbn [existsb fst]; rewrite Bool.orb_false_r; apply Z.eqb_neq; exact Hk).
  rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma aux_cur_last : forall L b0 r, last_assoc 25 L = Some r -> aux_cur L b0 = le8 rr_secret.
Proof.
  intros L b0 r H. apply last_assoc_In in H. unfold aux_cur.
  replace (existsb (fun p : Z * Z => fst p =? 25) L) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists (25, r). split; [exact H| reflexivity].
Qed.

Local Ltac aux_br :=
  lazymatch goal with |- context [bv_eqb ?x ?y] =>
    first [ replace (bv_eqb x y) with true
              by (symmetry; unfold bv_eqb; apply Z.eqb_eq; rewrite ?wz_unsigned, ?unsigned_lit by lia; lia)
          | replace (bv_eqb x y) with false
              by (symmetry; unfold bv_eqb; apply Z.eqb_neq; rewrite ?wz_unsigned, ?unsigned_lit by lia; lia) ]
  end;
  try change (negb true) with false; try change (negb false) with true; cbv iota.

Definition raux_post (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (av : Z) (L : list (Z * Z)) (b0 : list byte) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 1112088) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xc2a68) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned sp + -64) [CB 8 (aux_cur L b0)].

Lemma raux_walk : forall (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (av rnd : Z) (L : list (Z * Z)) (b0 : list byte) (m0 : word -> option byte),
  rw_cells usegs m0 RAUXV_CELL [C8 (wz av)] ->
  bytes_at usegs m0 av (u64s (map wz (flat_pairs L ++ [0; 0]))) ->
  bytes_at usegs m0 (rnd + 8) (le8 rr_secret) ->
  Forall (fun p => fst p <> 0) L -> Forall (fun p => fst p = 25 -> snd p = rnd) L ->
  Forall (fun p => 0 <= fst p < 2^64 /\ 0 <= snd p < 2^64) L ->
  RAUXV_CELL + 8 <= bv_unsigned sp + -64 -> bv_unsigned sp <= av -> av + 16 * (Z.of_nat (length L) + 1) <= 2^64 ->
  bv_unsigned sp <= rnd + 8 -> rnd + 16 <= 2^64 -> 64 <= bv_unsigned sp ->
  forall post pre (m : word -> option byte) (x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  L = pre ++ post -> bv_unsigned s1 = 16 * Z.of_nat (length pre) ->
  munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 (aux_cur pre b0)] ->
  evt usegs (raux_post sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av L b0 m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 1112088) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc2a58) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av rnd L b0 m0 AVC AVL RND NZ R25 RNG HC HAV HAVH HR HRH HSP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAUXV_CELL in HC, AVC.
  assert (WZAV : bv_unsigned (wz av) = av) by (apply wz_unsigned; lia).
  induction post as [|[k v] post IH]; intros pre m x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EL HS1 MU WM MI FR.
  - (* AT_NULL: leave the loop *)
    rewrite app_nil_r in EL. subst L.
    assert (AVLm : bytes_at usegs m av (u64s (map wz (flat_pairs pre ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    st1.
    pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre)) (wz 0) (wa (av + 8 * (2 * Z.of_nat (length pre))))
                  AVLm (flat_pairs_nth_end pre) ltac:(lia) eq_refl) as RD.
    st1. clear RD.
    st1. aux_br.
    st1. aux_br.
    apply evt_done. unfold raux_post. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact FR.
  - assert (IN : In (k, v) L) by (rewrite EL; apply in_or_app; right; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) NZ _ IN) as NZk.
    pose proof (proj1 (Forall_forall _ _) R25 _ IN) as R25k.
    pose proof (proj1 (Forall_forall _ _) RNG _ IN) as RNGk.
    cbn [fst snd] in NZk, R25k, RNGk.
    assert (LL : Z.of_nat (length L) = Z.of_nat (length pre) + 1 + Z.of_nat (length post))
      by (rewrite EL, length_app; cbn [length]; lia).
    assert (AVLm : bytes_at usegs m av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    assert (AVCm : rw_cells usegs m 0x10f820 [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]]).
    assert (RNDm : bytes_at usegs m (rnd + 8) (le8 rr_secret))
      by (eapply bytes_at_transport; [exact RND| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    st1.
    pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre)) (wz k) (wa (av + 8 * (2 * Z.of_nat (length pre))))
                  AVLm (flat_pairs_nth_key L pre k v post EL) ltac:(lia) eq_refl) as RD.
    st1. clear RD.
    st1.
    destruct (Z.eq_dec k 25) as [K25|K25].
    + (* AT_RANDOM: copy the 8 bytes at value+8 into the frame cell *)
      subst k. specialize (R25k eq_refl). subst v.
      aux_br.
      pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre) + 1) (wz rnd) (wa (av + 8 * (2 * Z.of_nat (length pre) + 1)))
                    AVLm (flat_pairs_nth_val L pre 25 rnd post EL) ltac:(lia) eq_refl) as RD.
      st1. clear RD. st1. st1. st1. st1.
      call rmemcpy_callZ3.
      1:{ exact RNDm. } 1:{ reflexivity. } 1:{ exact FR. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      1:{ lazymatch goal with H : mem_inv usegs ?mX |- mem_inv usegs ?mX => exact H end. }
      lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) [CB _ (le8 rr_secret)] |- _ => rename H into DST end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mY _) =>
        assert (AVCy : rw_cells usegs mY 0x10f820 [C8 (wz av)])
          by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]])
      end.
      st1. st1.
      eapply (IH (pre ++ [(25, rnd)])).
      * rewrite <- app_assoc. exact EL.
      * rewrite length_app. cbn [length]. first [rewrite unsigned_lit by lia; lia | rewrite wz_unsigned by lia; lia | lia].
      * exact MU.
      * exact WM.
      * lazymatch goal with H : mem_inv usegs ?mX |- mem_inv usegs ?mX => exact H end.
      * rewrite aux_cur_25. exact DST.
    + (* any other key: skip the pair *)
      aux_br.
      st1. aux_br.
      st1.
      eapply (IH (pre ++ [(k, v)])).
      * rewrite <- app_assoc. exact EL.
      * rewrite length_app. cbn [length]. first [rewrite unsigned_lit by lia; lia | rewrite wz_unsigned by lia; lia | lia].
      * exact MU.
      * exact WM.
      * exact MI.
      * rewrite (aux_cur_skip pre k v b0 K25). exact FR.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xc2a88) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ rmrep (am_init_st st) m'.

Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv usegs m -> rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = 0 -> 0 <= c_secret (ctx st) < 2^64 ->
  evt usegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc29d4) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & _) & _). unfold rctx_head_cells in C1.
  unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE, OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & L & rnd & AVC & AVL & RND & (AB & BAV & AVH & BR & RH & XR) & NZ & LA & R25 & RNG & _).
  pose proof (conj AVC (conj AVL RND)) as AUX0.
  unfold RAUXV_CELL in AVC.

  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.

  st1. st1. st1. st1. st1. st1.

  st1. rewrite sx32_wz by lia. st1. st1.

  st1.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia. }

  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.

  st1. st1. st1. st1. st1. st1. st1. st1. st1.

  (* The auxv walk 0xc2a58..0xc2a68, for any layout: [raux_walk]. *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge usegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  destruct AUX0 as (AVC0 & AVL0 & RND0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (AVCx : rw_cells usegs mX RAUXV_CELL [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC0| exact MUh| exact WM| cbn [disjoint_from cells_size csize]; split; [unfold RAUXV_CELL; lia| exact I]]);
    assert (AVLx : bytes_at usegs mX av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    assert (RNDx : bytes_at usegs mX (rnd + 8) (le8 rr_secret))
      by (eapply bytes_at_transport; [exact RND0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    lazymatch type of FRm with rw_cells _ _ _ [CB _ ?bz] =>
      eapply evt_cut;
      [ eapply (raux_walk sp gp tp _ _ _ _ _ _ _ _ _ F fc av rnd L bz mX AVCx AVLx RNDx NZ R25 RNG
                  ltac:(unfold RAUXV_CELL; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L []);
        [ reflexivity | first [reflexivity | vm_compute; reflexivity] | apply munch_refl | apply wmono_refl | assumption | exact FRm ]
      | post_call usegs mX ]
    end end.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) [CB _ (aux_cur _ _)] |- _ => rename H into DST end.
  rewrite (aux_cur_last L _ rnd LA) in DST.

  lazymatch type of DST with rw_cells _ ?mX _ _ =>
    assert (DST8 : rw_cells usegs mX (bv_unsigned sp + -64) [C8 rr_secret])
      by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
          split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
    clear DST end.
  st1.

  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia);
    pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
  clear MUh. unfold RCTX in MUc.

  st1. st1.
  set (stI := upd_ctx (fun c => set_init_done 1 (set_secret 0 c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
  { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold rctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw stI ?q) with (pw st q).

      replace (wz (rsec 1 0)) with rr_secret by (unfold rsec, wz; cbn [Z.eqb]; rewrite Z.add_0_l; symmetry; apply Z_to_bv_bv_unsigned).
      unfold wz at 1.
      lazymatch goal with H : rw_cells usegs ?mX 1112472 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc MRX.

  st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with Hm : rw_cells usegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells usegs mX (bv_unsigned sp + -56) ?csc |- _ =>
      pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
      cbn [app] in J2; clear Hm Hc;
      lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
        apply (rw_cells_merge usegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
    end end.
  apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
  unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.
End WithCeiling0.

