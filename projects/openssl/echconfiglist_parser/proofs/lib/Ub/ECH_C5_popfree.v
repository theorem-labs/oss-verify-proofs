(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C5_stmt ECH_C5_small ECH_C5_free ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PF_HEAD : Z := 0xe91d4.      (* [comment removed for export] *)
Definition PF_TAIL : Z := 0xe9234.      (* [comment removed for export] *)
Definition PF_RA_ELEM : Z := 0xe9218.   (* [comment removed for export] *)
Definition PF_FILE : Z := 0x2a3a6.      (* [comment removed for export] *)
Definition pf_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac kill_lts K :=
    exfalso; first [ apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; lia
                   | apply Bool.andb_true_iff in K; destruct K as [K K']; apply Z.ltb_lt in K; lia ].

  (* [comment removed for export] *)
  Lemma pf_segL :
    forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a FN i p lo : Z) (K : skrep) (pad : list byte),
      sk_data K mod 8 = 0 ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> u64arr usegs m (sk_data K) (map wz (sk_elems K)) ->
      nth_error (sk_elems K) (Z.to_nat i) = Some p -> 0 <= i -> 0 < p < 2^64 -> 0 < sk_data K -> sk_data K + 8 * sk_num K <= lo ->
      is_sk_freefunc_thunk (sk_free_thunk K) -> 0 <= FN < 2^64 -> FN mod 2 = 0 ->
      0 < a -> a + SK_SIZE <= lo ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 PF_RA_ELEM) sp gp tp u0 u1 u2 s0 (Z_to_bv 64 a) (Z_to_bv 64 p) b1 b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 FN) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 FN) fc None m1 (seg_rom usegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp) /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 FN) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PF_HEAD) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros ALD HDR ARR NTH I0 PR DP DB TH FNR FNE POS BL ST CEIL LO MI.
    unfold PF_HEAD, PF_RA_ELEM. unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (u64arr_bound _ _ _ _ ARR) as ARB. rewrite length_map in ARB.
    pose proof (nth_error_lt _ _ _ NTH) as IL. unfold sk_num, zlength in DB.
    (* [comment removed for export] *)
    st1. zstep.
    step. ub_dead_by (clear - DP I0 ARB IL).
    zstep. zstep. ub_b2z. step. step. try if_lit.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    zstep. step. ubal_by ALD. step. if_lit.
    pose proof (u64arr_read usegs _ _ _ i (wz p) (wa (sk_data K + i * 8)) ARR ltac:(rewrite nth_error_map, NTH; reflexivity) ltac:(lia) ltac:(f_equal; lia)) as RD. unfold wz in RD. step. clear RD.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    destruct TH as [E | [E | E]]; rewrite E in *; unfold P_sk_OSSL_ECHEXT_freefunc_thunk, P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk, P_sk_X509_BUFFER_freefunc_thunk in *.
    all: st1; step; try if_lit; try if_false; step; step.
    all: carve_frame 16%nat ST; do 4 st1; step; step; st1; st1; step; step.
    all: replace (ret_pc (Z_to_bv 64 FN)) with (Z_to_bv 64 FN) by (symmetry; apply ret_pc_even; [lia| exact FNE]).
    all: release_frame FR ST (bv_unsigned sp); finish.
    all: unfold sk_hdr_cells, wz; rewrite E; exact HDR.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_seg0_more :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a FN lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < sk_num K <= 2^20 -> 0 < a -> a + SK_SIZE <= lo ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0 b1 b2 m1,
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) u0 b1 b2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 FN) (Z_to_bv 64 (0 * 8)) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 PF_HEAD) fc None m1 (seg_rom usegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells usegs m1 (bv_unsigned sp + -48) (pf_frame s4 s3 s2 s1 s0 ra)
          /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 FN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros AL HDR NR POS BL ST CEIL LO MI. unfold P_OPENSSL_sk_pop_free, PF_HEAD, pf_frame.
    pose proof HDR as HDR0. unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    do 8 st1. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. ubal_by AL. step. if_lit.
    st1. rewrite sx32_wz by lia. unfold wz.
    step. if_cases K0; zify_cond K0; try (kill_lts K0); try clear K0.
    step. step. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_seg0_none :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> sk_num K = 0 -> 0 < a -> a + SK_SIZE <= lo ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0 m1,
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) u0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 PF_TAIL) fc None m1 (seg_rom usegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells usegs m1 (bv_unsigned sp + -48) (pf_frame s4 s3 s2 s1 s0 ra)
          /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros AL HDR NR POS BL ST CEIL LO MI. unfold P_OPENSSL_sk_pop_free, PF_TAIL, pf_frame.
    pose proof HDR as HDR0. unfold sk_hdr_cells, wz in HDR. rewrite NR in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    do 8 st1. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. ubal_by AL. step. if_lit.
    st1. step. try if_lit. try if_true.
    finish.
    unfold sk_hdr_cells, wz. rewrite NR. exact HDR.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_segN_more :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a i : Z) (K : skrep) (pad : list byte),
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 <= i -> i + 1 < sk_num K -> sk_num K <= 2^20 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0,
          ms' = MS (mkR (Z_to_bv 64 PF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) u0 a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 ((i + 1) * 8)) (Z_to_bv 64 (i + 1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 PF_HEAD) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 PF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PF_RA_ELEM)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros HDR I0 IL NR MI. unfold PF_RA_ELEM, PF_HEAD.
    replace (ret_pc (Z_to_bv 64 0xe9218)) with (Z_to_bv 64 0xe9218) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold sk_hdr_cells, wz in HDR.
    step. st1. rewrite sx32_wz by lia. unfold wz. zstep. zstep.
    step. if_cases K0; zify_cond K0; try (kill K0); try clear K0.
    replace (i * 8 + 8) with ((i + 1) * 8) by lia.
    apply evt_done. eexists. reflexivity.
  Qed.
  Lemma pf_segN_last :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a i : Z) (K : skrep) (pad : list byte),
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 <= i -> i + 1 = sk_num K -> sk_num K <= 2^20 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0 u3 u4,
          ms' = MS (mkR (Z_to_bv 64 PF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) u0 a1 a2 a3 a4 a5 a6 a7
                       s2 u3 u4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 PF_TAIL) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 PF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PF_RA_ELEM)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros HDR I0 IL NR MI. unfold PF_RA_ELEM, PF_TAIL.
    replace (ret_pc (Z_to_bv 64 0xe9218)) with (Z_to_bv 64 0xe9218) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold sk_hdr_cells, wz in HDR.
    step. st1. rewrite sx32_wz by lia. unfold wz. zstep. zstep.
    step. if_cases K0; zify_cond K0; try (kill K0); try clear K0.
    apply evt_done. do 3 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_tail0 :
    forall (rax sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      rw_cells usegs m (bv_unsigned sp + -48) (pf_frame s4 s3 s2 s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_OPENSSL_sk_free) fc None m (seg_rom usegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PF_TAIL) fc None m (seg_rom usegs)).
  Proof.
    intros until a. intros FR MI. unfold PF_TAIL, P_OPENSSL_sk_free.
    pose proof (word_range sp) as SPR. unfold pf_frame in FR.
    do 9 step. apply evt_done. reflexivity.
  Qed.
End S.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_ids_excl : forall (l1 l2 : list block) b, List.NoDup (map blk_id (l1 ++ l2)) -> In b l1 -> In b l2 -> False.
Proof.
  induction l1 as [|c l1 IH]; intros l2 b ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [->|H1]; [| exact (IH _ _ ND' H1 H2)]. apply NI. rewrite map_app. apply in_or_app. right. apply in_map. exact H2.
Qed.
Lemma nodup_ids_drop_mid : forall (l1 l2 l3 : list block), List.NoDup (map blk_id (l1 ++ l2 ++ l3)) -> List.NoDup (map blk_id (l1 ++ l3)).
Proof.
  intros l1 l2 l3 ND. rewrite !map_app in *. induction (map blk_id l1) as [|c l IH]; cbn in *.
  - induction (map blk_id l2) as [|d l' IH']; cbn in *; [exact ND|]. inversion ND; subst. auto.
  - inversion ND as [|x l0 NI ND']; subst. constructor; [| exact (IH ND')]. intros K. apply NI. apply in_app_or in K. apply in_or_app.
    destruct K as [K|K]; [left; exact K| right; apply in_or_app; right; exact K].
Qed.
Lemma perm_in_rest : forall (Fr L' L : list block) b, Permutation (Fr ++ L') L -> In b L -> ~ In b Fr -> In b L'.
Proof.
  intros Fr L' L b P HI NF. apply Permutation_sym in P. pose proof (Permutation_in _ P HI) as K. apply in_app_or in K. destruct K as [K|K]; [contradiction| exact K].
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Definition pf_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (a : Z) (K : skrep) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : PState) (LB' : list block),
      cfg_ms cf = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model cf) /\ hs_MPRES H mo (cfg_model cf)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' RERRNO [C4 errv] /\ hs_rauxv_ok H m' B
      /\ Permutation (blocks_SK a K ++ LB') LB /\ hs_RHEAP H s' LB' m'
      /\ xpres LB' (bv_unsigned sp) [] m m'
      /\ IMPL_mem m' /\ GOT_mem m'.

  Lemma pf_tail_spec :
    forall (rax sp gp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (a lo B : Z) (K : skrep) (pad : list byte) (errv : word),
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < a -> In (sk_id K, a, SK_SIZE) LB ->
      ((sk_cap K = 0 /\ sk_data K = 0) \/ (4 <= sk_cap K /\ 0 < sk_data K /\ (a + SK_SIZE <= sk_data K \/ sk_data K + 8 * sk_cap K <= a) /\ In (sk_did K, sk_data K, 8 * sk_cap K) LB)) ->
      rw_cells usegs m (bv_unsigned sp + -48) (pf_frame s4 s3 s2 s1 s0 ra) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo -> hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp + -48) -> hceil <= lo -> lo <= bv_unsigned sp - 48 - CFREE_STACK ->
      rw_cells usegs m RERRNO [C4 errv] -> mem_inv usegs m -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (pf_tail_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB a K lo B errv m mo)
        (mkCfg (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                        s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 PF_TAIL) fc None m (seg_rom usegs)) mo).
  Proof using HH.
    intros until errv. intros HDR POS HIN DAT FR HP KREL AUX SPB ST CEIL LO ERR MI IM GM.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CF0 : 0 <= CFREE_STACK) by (unfold CFREE_STACK, RFREE_STACK; lia).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply pf_tail0; [exact FR| exact MI]|].
    intros ms1 ->.
    unfold pf_frame in FR.
    pose proof (stk_release usegs m lo _ _ ST FR ltac:(lia)) as ST'. cbn [cells_size csize Nat.add] in ST'.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in ST' by lia.
    pose proof (skfree_spec_hdr H HH) as SF.
    eapply (sr_mono H HH).
    { eapply SF with (lo := lo) (B := B) (LB := LB) (s := s) (K := K) (pad := pad) (errv := errv); try reflexivity; try eassumption.
      all: first [unfold SKFREE_STACK, FR_sk_free; lia | rewrite errno_RATP; exact ERR]. }
    intros [ms4 mo4] PO. unfold skfree_post, pf_tail_post in *. cbn [cfg_ms cfg_model] in *. rewrite errno_RATP in PO. exact PO.
  Qed.

  Section Elem.
    Context (X : Type) (EP : list block -> mem -> Z -> X -> Prop) (blocks_E : Z -> X -> list block) (G : mem -> Prop).
    Variables (FN estack : Z).
    Hypothesis EF : efree_stmt_at H X EP blocks_E G FN estack.
    Hypothesis EPF : EP_frame X EP blocks_E.
    Hypothesis EPO : EP_owned X EP blocks_E.
    Hypothesis GF : G_frame G.
    Hypothesis FNR : 0 <= FN < 2^64.
    Hypothesis FNE : FN mod 2 = 0.

    Definition eblocks (ps : list Z) (xs : list X) : list block := concat (map (fun px => blocks_E (fst px) (snd px)) (combine ps xs)).

    (* [comment removed for export] *)
    Lemma ep_rest_frame : forall LB LB1 m m2 (SP : Z) (Bp : list block) rest xs,
      Forall2 (fun p x => EP LB m p x) rest xs ->
      (forall b, In b LB -> ~ In b Bp -> In b LB1) ->
      List.NoDup (map blk_id (Bp ++ eblocks rest xs)) ->
      xpres LB1 SP [] m m2 -> (forall b, In b LB -> blk_addr b + blk_size b <= SP) ->
      Forall2 (fun p x => EP LB1 m2 p x) rest xs.
    Proof using EPF EPO.
      intros LB LB1 m m2 SP Bp rest xs F2. induction F2 as [|p' x' r' xs' E' F' IHF]; intros KEEP ND XP BEL; [constructor|].
      cbn [eblocks combine map concat fst snd] in ND. fold (eblocks r' xs') in ND.
      constructor.
      - eapply EPF; [exact E'| | exact XP|].
        + intros b Hb. apply KEEP; [eapply EPO; [exact E'| exact Hb]|]. intros Kb.
          eapply (nodup_ids_excl Bp (blocks_E p' x' ++ eblocks r' xs')); [exact ND| exact Kb| apply in_or_app; left; exact Hb].
        + intros b Hb. apply BEL. eapply EPO; [exact E'| exact Hb].
      - apply IHF; [exact KEEP| eapply nodup_ids_drop_mid; exact ND| exact XP| exact BEL].
    Qed.

    Lemma pf_loop : forall (rest : list Z) (xs : list X) (done : list Z)
        (rax spi gp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (a lo B : Z) (K : skrep) (pad : list byte) (errv : word)
        (fr : list cell) (Q : config -> Prop),
      rest <> [] -> sk_elems K = done ++ rest -> length xs = length rest ->
      Forall2 (fun p x => EP LB m p x) rest xs ->
      List.NoDup (map blk_id (blocks_SK a K ++ eblocks rest xs)) ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < a -> In (sk_id K, a, SK_SIZE) LB ->
      sk_num K <= sk_cap K -> sk_cap K <= 2^20 -> Forall (fun p => 0 < p < 2^64) (sk_elems K) ->
      4 <= sk_cap K -> 0 < sk_data K -> In (sk_did K, sk_data K, 8 * sk_cap K) LB ->
      u64arr usegs m (sk_data K) (map wz (sk_elems K)) -> is_sk_freefunc_thunk (sk_free_thunk K) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo -> hs_rauxv_ok H m B -> bv_unsigned spi <= B ->
      stk usegs m lo (bv_unsigned spi) -> hceil <= lo -> lo <= bv_unsigned spi - (16 + Z.max estack CFREE_STACK) ->
      rw_cells usegs m RERRNO [C4 errv] -> mem_inv usegs m -> IMPL_mem m -> GOT_mem m -> G m ->
      rw_cells usegs m (bv_unsigned spi) fr ->
      (forall (rax' u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 s2x s3x s4x u3 u4 u5 u6 : word) (m' : mem) (mo' : Model) (s' : PState) (LB' : list block),
         Permutation (eblocks rest xs ++ LB') LB -> hs_RHEAP H s' LB' m' -> hs_KREL H s' mo' -> hs_MPRES H mo mo' ->
         hs_rauxv_ok H m' B -> stk usegs m' lo (bv_unsigned spi) -> rw_cells usegs m' RERRNO [C4 errv] -> mem_inv usegs m' ->
         IMPL_mem m' -> GOT_mem m' -> G m' -> rw_cells usegs m' (bv_unsigned spi) fr -> rw_cells usegs m' a (sk_hdr_cells K pad) ->
         xpres LB' (bv_unsigned spi) [] m m' ->
         hs_SR H Q (mkCfg (MS (mkR rax' spi gp (Z_to_bv 64 RATP) u0 u1 u2 s0x (Z_to_bv 64 a) c0 c1 c2 c3 c4 c5 c6 c7
                                   s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 PF_TAIL) fc None m' (seg_rom usegs)) mo')) ->
      hs_SR H Q (mkCfg (MS (mkR rax spi gp (Z_to_bv 64 RATP) t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 FN) (Z_to_bv 64 (Z.of_nat (length done) * 8)) (Z_to_bv 64 (Z.of_nat (length done))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 PF_HEAD) fc None m (seg_rom usegs)) mo).
    Proof using HH EF EPF EPO GF FNR FNE.
      intros rest. induction rest as [|p rest IH]; [intros; congruence|].
      intros xs done rax spi gp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB a lo B K pad errv fr Q.
      intros _ EL XL F2 ND HDR POS HIN NC CAP ELR C4 DP DIN ARR TH HP KREL AUX SPB ST CEIL LO ERR MI IM GM GG FR KONT.
      destruct xs as [|x xs]; [cbn in XL; discriminate|]. cbn [length] in XL. injection XL as XL.
      inversion F2 as [|p0 x0 r0 xs0 EP0 F2' E1 E2]; subst p0 x0 r0 xs0. clear F2.
      hcb. pose proof (word_range spi) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (HB := HH_blocks_below H HH _ _ _ HP).
      pose proof (HB _ HIN) as ABL. pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in ABL, DBL. unfold SK_SIZE in ABL.
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP DIN) as (_ & DAL16 & _). cbn [blk_addr blk_size fst snd] in DAL16.
      assert (DAL8 : sk_data K mod 8 = 0) by (clear - DAL16; lia).   (* [comment removed for export] *)
      set (i := Z.of_nat (length done)) in *.
      assert (NTH : nth_error (sk_elems K) (Z.to_nat i) = Some p).
      { rewrite EL. unfold i. rewrite Nat2Z.id. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      assert (PR : 0 < p < 2^64).
      { apply (proj1 (Forall_forall _ _) ELR p). rewrite EL. apply in_or_app. right. left. reflexivity. }
      assert (NUM : sk_num K = i + 1 + Z.of_nat (length rest)).
      { unfold sk_num, zlength. rewrite EL, length_app. cbn [length]. unfold i. lia. }
      cbn [eblocks combine map concat fst snd] in ND. fold (eblocks rest xs) in ND.
      assert (STK : 16 <= bv_unsigned spi - lo /\ estack <= bv_unsigned spi - lo) by (unfold CFREE_STACK, RFREE_STACK in LO; lia).
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL|
        eapply pf_segL with (lo := lo) (K := K) (pad := pad) (i := i) (p := p); try eassumption; unfold SK_SIZE; try lia|].
      intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & HDR1).
      assert (FW1 : Forall (fun iv : Z * Z => (hceil <= fst iv /\ snd iv <= bv_unsigned spi) \/ (forall a0, fst iv <= a0 < snd iv -> rin_ivs [] a0)) [(lo, bv_unsigned spi)]).
      { apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (XP1 : xpres LB (bv_unsigned spi) [] m m1) by (eapply xpres_of_munch; [exact MU1| exact WM1| exact FW1| exact HB]).
      assert (HP1 : hs_RHEAP H s LB m1).
      { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (AUX1 : hs_rauxv_ok H m1 B).
      { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
      apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
      assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
      assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
      assert (GG1 : G m1) by (eapply GF; [exact GG| exact XP1| lia]).
      assert (EP1 : EP LB m1 p x).
      { eapply EPF; [exact EP0| intros b Hb; eapply EPO; [exact EP0| exact Hb]| exact XP1|].
        intros b Hb. pose proof (HB b (EPO _ _ _ _ EP0 b Hb)). lia. }
      (* [comment removed for export] *)
      assert (NDE : List.NoDup (map blk_id (blocks_E p x))).
      { rewrite map_app in ND. apply NoDup_app_remove_l in ND. rewrite map_app in ND. apply NoDup_app_remove_r in ND. exact ND. }
      eapply (sr_seq H HH).
      { unfold efree_stmt_at in EF.
        eapply EF with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (x := x) (errv := errv); try reflexivity; try eassumption; try lia. }
      intros [ms2 mo2] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4' & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2 & LB1 &
                      -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & PERM2 & HP2 & XP2 & IM2 & GM2 & GG2).
      rewrite errno_RATP in ERR2.
      assert (HB2 := HH_blocks_below H HH _ _ _ HP2).
      assert (SUB1 : forall b, In b LB1 -> In b LB).
      { intros b Hb. eapply Permutation_in; [exact PERM2| apply in_or_app; right; exact Hb]. }
      (* [comment removed for export] *)
      assert (KEEP : forall b, In b LB -> ~ In b (blocks_E p x) -> In b LB1) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM2| exact Hb| exact Nb]).
      assert (HIN1 : In (sk_id K, a, SK_SIZE) LB1).
      { apply KEEP; [exact HIN|]. intros Kb. eapply (nodup_ids_excl (blocks_SK a K) (blocks_E p x ++ eblocks rest xs)); [exact ND| left; reflexivity| apply in_or_app; left; exact Kb]. }
      assert (DIN1 : In (sk_did K, sk_data K, 8 * sk_cap K) LB1).
      { apply KEEP; [exact DIN|]. intros Kb. eapply (nodup_ids_excl (blocks_SK a K) (blocks_E p x ++ eblocks rest xs)); [exact ND| | apply in_or_app; left; exact Kb].
        unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity. }
      assert (XP02 : xpres LB1 (bv_unsigned spi) [] m m2).
      { eapply xpres_trans; [| exact XP2]. eapply xpres_weaken; [exact XP1| lia| exact SUB1| auto]. }
      assert (HDR2 : rw_cells usegs m2 a (sk_hdr_cells K pad)).
      { eapply xpres_rw_cells'; [exact XP2| exact HDR1| | constructor]. right; right. exists (sk_id K, a, SK_SIZE). split; [exact HIN1|].
        cbn [blk_addr blk_size fst snd cells_size csize sk_hdr_cells Nat.add]. unfold SK_SIZE. lia. }
      assert (ARR2 : u64arr usegs m2 (sk_data K) (map wz (sk_elems K))).
      { eapply xpres_u64arr; [exact XP02| exact ARR|]. split; [| constructor]. right; right. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact DIN1|].
        cbn [blk_addr blk_size fst snd]. rewrite length_map. unfold sk_num, zlength in NC. lia. }
      assert (FR2 : rw_cells usegs m2 (bv_unsigned spi) fr).
      { eapply xpres_rw_cells'; [exact XP02| exact FR| left; lia| constructor]. }
      assert (ND' : List.NoDup (map blk_id (blocks_SK a K ++ eblocks rest xs))) by (eapply nodup_ids_drop_mid; exact ND).
      assert (F2'' : Forall2 (fun p' x' => EP LB1 m2 p' x') rest xs).
      { eapply (ep_rest_frame LB LB1 m m2 (bv_unsigned spi) (blocks_E p x)); [exact F2'| exact KEEP| | exact XP02|].
        - rewrite map_app in ND. apply NoDup_app_remove_l in ND. exact ND.
        - intros b Hb. pose proof (HB b Hb). lia. }
      (* [comment removed for export] *)
      destruct rest as [|p2 rest'].
      - (* [comment removed for export] *)
        inversion F2''; subst. cbn [length] in NUM.
        eapply (sr_evt_krel H HH); [exact KREL2| eapply pf_segN_last with (K := K) (pad := pad) (i := i); [exact HDR2| lia| lia| lia| exact MI2]|].
        intros ms3 (w0 & w3 & w4 & ->).
        eapply KONT; try eassumption.
        cbn [eblocks combine map concat fst snd]. rewrite app_nil_r. exact PERM2.
      - (* [comment removed for export] *)
        cbn [length] in NUM.
        eapply (sr_evt_krel H HH); [exact KREL2| eapply pf_segN_more with (K := K) (pad := pad) (i := i); [exact HDR2| lia| lia| lia| exact MI2]|].
        intros ms3 (w0 & ->).
        replace (i + 1) with (Z.of_nat (length (done ++ [p]))) by (rewrite length_app; cbn [length]; unfold i; lia).
        eapply (IH xs (done ++ [p])) with (lo := lo) (B := B) (LB := LB1) (s := s2) (K := K) (pad := pad) (errv := errv) (fr := fr); try eassumption; try congruence.
        + rewrite <- app_assoc. exact EL.
        + intros rax' y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 s2x s3x s4x y3 y4 y5 y6 m' mo' s' LB' PERM' HP' KREL' MP' AUX' ST' ERR' MI' IM' GM' GG' FR' HDR' XP'.
          eapply KONT; try eassumption.
          * change (eblocks (p :: p2 :: rest') (x :: xs)) with (blocks_E p x ++ eblocks (p2 :: rest') xs). rewrite <- app_assoc.
            eapply Permutation_trans; [apply Permutation_app_head; exact PERM'| exact PERM2].
          * eapply (mpres_trans H HH); [exact MP2| exact MP'].
          * eapply xpres_trans; [| exact XP'].
            eapply xpres_weaken; [exact XP02| lia| | auto]. intros b Hb. eapply Permutation_in; [exact PERM'| apply in_or_app; right; exact Hb].
    Qed.

    Lemma skpopfree_spec_in : skpopfree_stmt_gen H X EP blocks_E G FN estack.
    Proof using HH EF EPF EPO GF FNR FNE.
      unfold skpopfree_stmt_gen. intros _ _ _ _ _ _. intros until errv.
      intros A0 A1 SO TH XL F2 ND HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM GG RAE. subst a0 a1 tp.
      rewrite errno_RATP in ERR. fold (eblocks (sk_elems K) xs) in ND |- *.
      unfold SKPOPFREE_STACK, FR_sk_pop_free in LO.
      assert (LO' : lo <= bv_unsigned sp - 48 - 16 - estack /\ lo <= bv_unsigned sp - 48 - 16 - CFREE_STACK) by lia.
      hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (CF0 : 0 <= CFREE_STACK) by (unfold CFREE_STACK, RFREE_STACK; lia).
      assert (HB := HH_blocks_below H HH _ _ _ HP).
      destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & ELR & DAT).
      pose proof (HB _ HIN) as ABL. cbn [blk_addr blk_size fst snd] in ABL.
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as (_ & AL16 & _). cbn [blk_addr blk_size fst snd] in AL16.
      assert (AL8 : a mod 8 = 0) by (clear - AL16; lia).   (* [comment removed for export] *)
      set (spi := Z_to_bv 64 (bv_unsigned sp + -48)).
      assert (SPI : bv_unsigned spi = bv_unsigned sp + -48) by (unfold spi; rewrite unsigned_lit by lia; reflexivity).
      set (Q := skpopfree_post H X blocks_E G ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a K xs lo B errv m mo).
      (* [comment removed for export] *)
      assert (FIN : forall (m1 : mem), xpres LB (bv_unsigned sp) [] m m1 ->
                forall (rax' u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 s2x s3x s4x u3 u4 u5 u6 : word) (m' : mem) (mo' : Model) (s' : PState) (LB' : list block),
         Permutation (eblocks (sk_elems K) xs ++ LB') LB -> hs_RHEAP H s' LB' m' -> hs_KREL H s' mo' -> hs_MPRES H mo mo' ->
         hs_rauxv_ok H m' B -> stk usegs m' lo (bv_unsigned spi) -> rw_cells usegs m' RERRNO [C4 errv] -> mem_inv usegs m' ->
         IMPL_mem m' -> GOT_mem m' -> G m' -> rw_cells usegs m' (bv_unsigned spi) (pf_frame s4 s3 s2 s1 s0 ra) -> rw_cells usegs m' a (sk_hdr_cells K pad) ->
         xpres LB' (bv_unsigned spi) [] m1 m' ->
         hs_SR H Q (mkCfg (MS (mkR rax' spi gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 a) c0 c1 c2 c3 c4 c5 c6 c7
                                   s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 PF_TAIL) fc None m' (seg_rom usegs)) mo')).
      { intros m1 XP01. intros until LB'. intros PERM' HP' KREL' MP' AUX' ST' ERR' MI' IM' GM' GG' FR' HDR' XP'.
        rewrite SPI in ST', FR', XP'.
        assert (KEEP : forall b, In b (blocks_SK a K) -> In b LB -> In b LB').
        { intros b Hb HbL. eapply perm_in_rest; [exact PERM'| exact HbL|]. intros Kb. eapply (nodup_ids_excl (blocks_SK a K) (eblocks (sk_elems K) xs)); [exact ND| exact Hb| exact Kb]. }
        assert (SUB' : forall b, In b LB' -> In b LB) by (intros b Hb; eapply Permutation_in; [exact PERM'| apply in_or_app; right; exact Hb]).
        eapply (sr_mono H HH).
        { eapply pf_tail_spec with (lo := lo) (B := B) (LB := LB') (s := s') (K := K) (pad := pad) (errv := errv); try eassumption; try lia.
          - apply KEEP; [left; reflexivity| exact HIN].
          - destruct DAT as [D0|(D4 & DP & DDJ & DIN & _)]; [left; exact D0| right].
            split; [exact D4|]. split; [exact DP|]. split; [exact DDJ|]. apply KEEP; [| exact DIN].
            unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity. }
        intros [ms4 mo4] PO. unfold pf_tail_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & s4' & LB4 &
                        -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & PERM4 & HP4 & XP4 & IM4 & GM4).
        assert (SUB4 : forall b, In b LB4 -> In b LB') by (intros b Hb; eapply Permutation_in; [exact PERM4| apply in_or_app; right; exact Hb]).
        unfold Q, skpopfree_post. cbn [cfg_ms cfg_model].
        exists v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m4, s4', LB4.
        split; [reflexivity|]. split; [exact KREL4|]. split; [eapply (mpres_trans H HH); [exact MP'| exact MP4]|]. split; [exact MI4|]. split; [exact ST4|].
        split; [rewrite errno_RATP; exact ERR4|]. split; [exact AUX4|].
        split.
        { fold (eblocks (sk_elems K) xs). eapply Permutation_trans; [apply Permutation_app_swap_app|].
          eapply Permutation_trans; [apply Permutation_app_head; exact PERM4| exact PERM']. }
        split; [exact HP4|].
        split.
        { eapply xpres_trans; [eapply xpres_weaken; [exact XP01| lia| intros b Hb; apply SUB', SUB4; exact Hb| auto]|].
          eapply xpres_trans; [eapply xpres_weaken; [exact XP'| lia| exact SUB4| auto]| exact XP4]. }
        split; [exact IM4|]. split; [exact GM4|].
        eapply GF; [exact GG'| exact XP4| lia]. }
      assert (WORLD : forall m1, munch [(lo, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
                xpres LB (bv_unsigned sp) [] m m1 /\ hs_RHEAP H s LB m1 /\ hs_rauxv_ok H m1 B /\ rw_cells usegs m1 RERRNO [C4 errv]
                /\ IMPL_mem m1 /\ GOT_mem m1 /\ G m1).
      { intros m1 MU1 WM1.
        assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
        { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [exact XP1|].
        split. { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split. { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        split. { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| unfold RERRNO; cbn; lia]. }
        split. { eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]. }
        split. { eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]. }
        eapply GF; [exact GG| exact XP1| lia]. }
      destruct (sk_elems K) as [|p0 rest0] eqn:EL.
      - (* [comment removed for export] *)
        assert (N0 : sk_num K = 0) by (unfold sk_num, zlength; rewrite EL; reflexivity).
        eapply (sr_evt_krel H HH); [exact KREL| eapply pf_seg0_none with (lo := lo) (K := K) (pad := pad); [exact AL8| exact HDR| exact N0| exact POS| unfold SK_SIZE in *; lia| exact ST| exact CEIL| lia| exact MI]|].
        intros ms1 (w0 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
        destruct (WORLD m1 MU1 WM1) as (XP1 & HP1 & AUX1 & ERR1 & IM1 & GM1 & GG1).
        eapply (FIN m1 XP1) with (LB' := LB) (s' := s); try eassumption; try (rewrite SPI; eassumption).
        + destruct xs; [| cbn in XL; discriminate]. cbn. apply Permutation_refl.
        + apply (mpres_refl H HH).
        + apply xpres_refl.
      - (* [comment removed for export] *)
        assert (NP : 0 < sk_num K) by (unfold sk_num, zlength; rewrite EL; cbn [length]; lia).
        destruct DAT as [[C0 _]|(D4 & DP & DDJ & DIN & ARR & _)]; [lia|].
        pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL.
        eapply (sr_evt_krel H HH); [exact KREL| eapply pf_seg0_more with (lo := lo) (K := K) (pad := pad); [exact AL8| exact HDR| lia| exact POS| unfold SK_SIZE in *; lia| exact ST| exact CEIL| lia| exact MI]|].
        intros ms1 (w0 & w1 & w2 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
        destruct (WORLD m1 MU1 WM1) as (XP1 & HP1 & AUX1 & ERR1 & IM1 & GM1 & GG1).
        assert (ARR1 : u64arr usegs m1 (sk_data K) (map wz (sk_elems K))).
        { eapply u64arr_across; [exact MU1| exact WM1| | rewrite EL; exact ARR]. rewrite length_map. unfold sk_num, zlength in NC. cbn. lia. }
        assert (F21 : Forall2 (fun p x => EP LB m1 p x) (p0 :: rest0) xs).
        { eapply (ep_rest_frame LB LB m m1 (bv_unsigned sp) []); [exact F2| auto| | exact XP1|].
          - cbn [app]. rewrite map_app in ND. apply NoDup_app_remove_l in ND. exact ND.
          - intros b Hb. pose proof (HB b Hb). lia. }
        fold spi.
        eapply (pf_loop (p0 :: rest0) xs []) with (lo := lo) (B := B) (LB := LB) (s := s) (K := K) (pad := pad) (errv := errv) (fr := pf_frame s4 s3 s2 s1 s0 ra);
          try eassumption; try (rewrite SPI; eassumption); try congruence; try (rewrite SPI; lia); try lia.
        exact (FIN m1 XP1).
    Qed.
  End Elem.

  Theorem skpopfree_spec : forall X EP blocks_E G FN estack, skpopfree_stmt_gen H X EP blocks_E G FN estack.
  Proof using HH.
    intros X EP blocks_E G FN estack EF EPF EPO GF FNR FNE.
    exact (skpopfree_spec_in X EP blocks_E G FN estack EF EPF EPO GF FNR FNE EF EPF EPO GF FNR FNE).
  Qed.
End W.
