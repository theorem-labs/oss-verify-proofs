(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the auxv walk of the malloc secret setup is proved once for any pair list (aux_cur, raux_post, raux_walk at this binary's loop addresses) and ram_entry uses it instead of the fixed 10-pair walk, as in fuzz_bigint's copy; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CJ/Ref/RF_am_E.v, lines 92-227, 257-258, 282, 291-307. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Ref Require Import F_memcpy_u.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_malloc_free_u MallocTree_u MallocModel_B_u F_ntf_A_u F_ntf_B_u MallocKit_B_u MallocKit_B3_u F_am_A_u F_am_K_u F_am_E_u.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Ref Require Import RMallocRep_u RMallocTree_u RMallocKit_B_u RMallocKit_B3_u RF_ntf_A_u RF_am_A_u.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastTauto. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
#[using="Type"] Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at rsegs m S src -> length src = Z.to_nat n ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xab480) fc None m (seg_rom rsegs)).
Proof.
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

#[using="Type"] Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

#[using="Type"] Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

(* musl's [get_random_secret] auxv walk, proved once for any pair list [L]:
   [for (i=0; auxv[i]; i+=2) if (auxv[i]==AT_RANDOM) memcpy(&secret, (char* )auxv[i+1]+8, 8);]
   The loop head is 0x9d7f0 (s1 = 16 * pairs done, a0 = av, s4 = 25); the
   AT_RANDOM body is 0x9d7d4 (memcpy to the frame cell 0(sp)); the exit is 0x9d800.
   [aux_cur pre b0] is the frame cell after the pairs [pre]: the secret once an
   AT_RANDOM pair was seen, else the initial bytes [b0]. *)
Definition aux_cur (pre : list (Z * Z)) (b0 : list byte) : list byte :=
  if existsb (fun p => fst p =? 25) pre then le8 (wz secret_val) else b0.

Lemma aux_cur_25 : forall pre v b0, aux_cur (pre ++ [(25, v)]) b0 = le8 (wz secret_val).
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

Lemma aux_cur_last : forall L b0 r, last_assoc 25 L = Some r -> aux_cur L b0 = le8 (wz secret_val).
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
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 959056) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9d800) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) [CB 8 (aux_cur L b0)].

Lemma raux_walk : forall (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (av rnd : Z) (L : list (Z * Z)) (b0 : list byte) (m0 : word -> option byte),
  rw_cells rsegs m0 RAUXV_CELL [C8 (wz av)] ->
  bytes_at rsegs m0 av (u64s (map wz (flat_pairs L ++ [0; 0]))) ->
  bytes_at rsegs m0 (rnd + 8) (le8 (wz secret_val)) ->
  Forall (fun p => fst p <> 0) L -> Forall (fun p => fst p = 25 -> snd p = rnd) L ->
  Forall (fun p => 0 <= fst p < 2^64 /\ 0 <= snd p < 2^64) L ->
  RAUXV_CELL + 8 <= bv_unsigned sp + -64 -> bv_unsigned sp <= av -> av + 16 * (Z.of_nat (length L) + 1) <= 2^64 ->
  bv_unsigned sp <= rnd + 8 -> rnd + 16 <= 2^64 -> 64 <= bv_unsigned sp ->
  forall post pre (m : word -> option byte) (x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  L = pre ++ post -> bv_unsigned s1 = 16 * Z.of_nat (length pre) ->
  munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 (aux_cur pre b0)] ->
  evt rsegs (raux_post sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av L b0 m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 959056) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9d7f0) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av rnd L b0 m0 AVC AVL RND NZ R25 RNG HC HAV HAVH HR HRH HSP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAUXV_CELL in HC, AVC.
  assert (WZAV : bv_unsigned (wz av) = av) by (apply wz_unsigned; lia).
  induction post as [|[k v] post IH]; intros pre m x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EL HS1 MU WM MI FR.
  - (* AT_NULL: leave the loop *)
    rewrite app_nil_r in EL. subst L.
    assert (AVLm : bytes_at rsegs m av (u64s (map wz (flat_pairs pre ++ [0; 0]))))
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
    assert (AVLm : bytes_at rsegs m av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    assert (AVCm : rw_cells rsegs m 0xea258 [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]]).
    assert (RNDm : bytes_at rsegs m (rnd + 8) (le8 (wz secret_val)))
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
      1:{ lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end. }
      lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) [CB _ (le8 (wz secret_val))] |- _ => rename H into DST end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mY _) =>
        assert (AVCy : rw_cells rsegs mY 0xea258 [C8 (wz av)])
          by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]])
      end.
      st1. st1.
      eapply (IH (pre ++ [(25, rnd)])).
      * rewrite <- app_assoc. exact EL.
      * rewrite length_app. cbn [length]. first [rewrite unsigned_lit by lia; lia | rewrite wz_unsigned by lia; lia | lia].
      * exact MU.
      * exact WM.
      * lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end.
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
             F (Z_to_bv 64 0x9d820) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
    /\ stk rsegs m' lo (bv_unsigned sp + -64)
    /\ rmrep (am_init_st st) m'.

#[using="Type"] Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv rsegs m -> rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = secret_val -> 0 <= c_secret (ctx st) < 2^64 ->
  evt rsegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9d76c) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & _) & _). unfold ctx_head_cells in C1.
  (pose_ceil; unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *). unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & L & rnd & AVC & AVL & RND & (AB & BAV & AVH & BR & RH & XR) & NZ & LA & R25 & RNG).
  pose proof (conj AVC (conj AVL RND)) as AUX0.
  unfold RAUXV_CELL in AVC.
  (* [comment removed for export] *)
  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{ (* [comment removed for export] *)
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; pose_ceil; lia. }
  (* [comment removed for export] *)
  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1.

  (* The auxv walk 0x9d7f0..0x9d800, for any layout: [raux_walk]. *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge rsegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  destruct AUX0 as (AVC0 & AVL0 & RND0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (AVCx : rw_cells rsegs mX RAUXV_CELL [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC0| exact MUh| exact WM| cbn [disjoint_from cells_size csize]; split; [unfold RAUXV_CELL; lia| exact I]]);
    assert (AVLx : bytes_at rsegs mX av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    assert (RNDx : bytes_at rsegs mX (rnd + 8) (le8 (wz secret_val)))
      by (eapply bytes_at_transport; [exact RND0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    lazymatch type of FRm with rw_cells _ _ _ [CB _ ?bz] =>
      eapply evt_cut;
      [ eapply (raux_walk sp gp tp _ _ _ _ _ _ _ _ _ F fc av rnd L bz mX AVCx AVLx RNDx NZ R25 RNG
                  ltac:(unfold RAUXV_CELL; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L []);
        [ reflexivity | first [reflexivity | vm_compute; reflexivity] | apply munch_refl | apply wmono_refl | assumption | exact FRm ]
      | post_call rsegs mX ]
    end end.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) [CB _ (aux_cur _ _)] |- _ => rename H into DST end.
  rewrite (aux_cur_last L _ rnd LA) in DST.

  lazymatch type of DST with rw_cells _ ?mX _ _ =>
    assert (DST8 : rw_cells rsegs mX (bv_unsigned sp + -64) [C8 (wz secret_val)])
      by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
          split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
    clear DST end.
  st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; pose_ceil; lia);
    pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  clear MUh. unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1.
  set (stI := upd_ctx (fun c => set_init_done 1 (set_secret secret_val c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
  { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw stI ?q) with (pw st q). unfold wz at 2.
      lazymatch goal with H : rw_cells rsegs ?mX 959440 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc MRX.
  (* [comment removed for export] *)
  st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with Hm : rw_cells rsegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells rsegs mX (bv_unsigned sp + -56) ?csc |- _ =>
      pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
      cbn [app] in J2; clear Hm Hc;
      lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
        apply (rw_cells_merge rsegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
    end end.
  apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
  unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.
End CEIL_WRAP_1.

