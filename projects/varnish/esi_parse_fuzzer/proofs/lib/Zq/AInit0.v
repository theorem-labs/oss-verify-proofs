(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AInioec ASecImg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kun0 := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                    kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFakeStackBytes, kFakeFlagsOffset, kFakeFramesOffset,
                    kChunksBlockCount, kPtrArrayReserve, kRegionInfoSize, kDepotNodesL1, kLowShadowMapBeg in *.

(* [comment removed for export] *)
Lemma bytes_at_mid0 : forall (m : mem) a bs i n, bytes_at rsegs m a bs -> (i + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat i) (firstn n (skipn i bs)).
Proof.
  intros m a bs i n B L. rewrite <- (firstn_skipn i bs) in B. apply bytes_at_app in B as [_ B].
  rewrite firstn_length_le in B by lia.
  rewrite <- (firstn_skipn n (skipn i bs)) in B. apply bytes_at_app in B as [B _]. exact B.
Qed.
Lemma skipn_repeat0 : forall {X} (x : X) i n, skipn i (repeat x n) = repeat x (n - i).
Proof. intros X x i. induction i as [|i IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.
Lemma firstn_repeat0 : forall {X} (x : X) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros X x k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
Lemma repeat_mid0 : forall {X} (x : X) n i k, (i + k <= n)%nat -> firstn k (skipn i (repeat x n)) = repeat x k.
Proof. intros X x n i k H. rewrite skipn_repeat0, firstn_repeat0 by lia. reflexivity. Qed.

Lemma classes_regions_zero0 : forall sb n, classes_regions_ sb (fun _ => region_zero) n = [].
Proof. intros sb n. induction n as [|n IH]; [reflexivity|]. cbn [classes_regions_]. rewrite IH. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Stmt.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Definition depot_init_ok2 : Prop :=
    forall P k1 sp0 FULL md (m : mem), a0_raw P k1 sp0 FULL md -> a0_depot_raw P k1 m ->
      @depot_rep DR AL_pboth ASEGS [k1] (p_nodes0 P) (p_frames0 P) m.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ainit_top_stmt : Prop :=
    forall P k1 sp0 FULL md,
      depot_init_ok2 -> a0_raw P k1 sp0 FULL md -> alloc_top (m_vmmaps md) = alloc_ceiling ->
      exists A0, pa_ainv A0 FULL md /\ a0_facts sp0 A0 /\ A0 = A0_of P k1.
End Stmt.

Section Init.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Variables (P : aplace) (k1 : list Z) (sp0 : Z) (FULL : mem) (md : Model).
  Hypothesis DI : depot_init_ok2.
  Hypothesis RAW : a0_raw P k1 sp0 FULL md.
  Hypothesis TOP : alloc_top (m_vmmaps md) = alloc_ceiling.
  Local Notation A0 := (A0_of P k1).
  Local Notation Hd := (hidc (pa_hull (A0_of P k1))).
  Local Notation v := (aview_of (pa_hull (A0_of P k1)) FULL).

  #[using="RAW md FULL sp0 k1"] Lemma PL : wf_place AL_pboth P. Proof. exact (ar0_place _ _ _ _ _ RAW). Qed.

  (* [comment removed for export] *)
  #[using="RAW md FULL sp0"] Lemma init_WF : WF AL_pboth A0.
  Proof.
    pose proof PL as HPL. pose proof (ar0_bigmaps _ _ _ _ _ RAW) as BM. pose proof (ar0_k1 _ _ _ _ _ RAW) as K1.
    constructor; unfold A0_of; cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact HPL.
    - exact BM.
    - split; [| split; [intros; reflexivity| ((first [ intro dR_20; dex1 dR_20 as c; destruct dR_20 as [Hc X] | intro dR_20; dand3 dR_20 as c Hc X | intros (c & Hc & X) ])); exfalso; apply X; reflexivity]].
      intros c Hc. unfold wf_region, region_zero. cbn [rg_allocated_user rg_mapped_user rg_mapped_fa rg_free length Z.of_nat].
      pose proof (class_size_range c Hc). pose proof (class_slack_range c). unfold kFreeArrayOffset, kUserMapSize, kFreeArraySize, kFreeArrayMapSize.
      rewrite !Z.mod_0_l by lia. rewrite !Z.div_0_l by lia. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try lia; [constructor| intros k []| intros _; split; reflexivity].
    - split; [| split; reflexivity]. intros c Hc. cbv zeta. cbn [pk_chunks length].
      assert (0 <= max_count c) by (destruct (Z.eq_dec c 31) as [->|]; [rewrite max_count_31; lia| pose proof (max_count_range c ltac:(lia)); lia]).
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; [lia| constructor| intros k []| reflexivity].
    - intros c k Hc Hk. exfalso. unfold carved_count_, region_zero in Hk. cbn [rg_allocated_user] in Hk. rewrite Z.div_0_l in Hk by (pose proof (class_size_range c Hc); lia). lia.
    - split; [intros u li Hl; rewrite lookup_empty in Hl; discriminate|]. split; [intros u u' li li' Hl; rewrite lookup_empty in Hl; discriminate|].
      unfold as_livebytes_. rewrite map_fold_empty. rewrite LIVE_MAX_eq. lia.
    - unfold wf_quarantine_. cbn [app]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
        [constructor| constructor| intros b []| unfold kQuarantineCacheSize; cbn; lia| unfold kQuarantineMaxSize; cbn; lia
        | constructor| constructor| intros u li Hl; rewrite lookup_empty in Hl; discriminate].
    - unfold wf_sec_. cbn [sr_chunks sr_reserved map length]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; [constructor| lia| left; reflexivity| intros s []| intros s []].
    - unfold wf_depot_. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; [apply Forall_cons; [exact K1| apply Forall_nil] | constructor; [apply not_elem_of_nil| constructor] | discriminate].
    - split; [intros ff f Hf; rewrite lookup_empty in Hf; discriminate|]. split; [intros k; lia|].
      intros ff ff' f f' Hf. rewrite lookup_empty in Hf. discriminate.
    - unfold wf_budget_, as_livebytes_, as_nlive_, tiny_live_, tiny_quar_. rewrite !map_fold_empty. cbn [q_entries flat_map app filter length Z.of_nat size]. rewrite TINYCRED0_eq, NLIVE_MAX_eq. rewrite map_size_empty || idtac. cbn. lia.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) unfold wf_dead_. cbn [length Z.of_nat hull_bytes sr_chunks]. rewrite SECCRED0_eq. unfold kDeadShadowBytes.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try lia. constructor.
    - (* [comment removed for export] *) apply wf_qcredit_nil.
    - (* [comment removed for export] *)
      unfold wf_prim_. rewrite PRIMCRED0_eq. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; [lia| cbn; lia|].
      intros c k Hc [V|Q].
      + destruct V as (u & n & Hu). rewrite lookup_empty in Hu. discriminate.
      + destruct Q as (n & Hn). cbn in Hn. destruct Hn.
  Qed.

  (* [comment removed for export] *)
  #[using="RAW md FULL sp0 k1"] Lemma PF :
    (aobj (p_thr P) 4096 /\ p_thr P mod 4096 = 0) /\ (aobj (p_ctx P) 0x10000 /\ p_ctx P mod 4096 = 0) /\
    (aobj (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P mod 4096 = 0) /\ (aobj (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P mod 4096 = 0) /\
    (aobj (p_fs P) kFakeStackBytes /\ p_fs P mod 4096 = 0) /\ (aobj (p_pa P) kPtrArrayReserve /\ p_pa P mod 4096 = 0) /\
    (aobj (p_dtls P) 4096 /\ p_dtls P mod 4096 = 0) /\
    (alloc_ceiling + 0x800000 <= p_sp0 P <= 2^47 /\ 0 <= p_stk_span P <= 0x240000 /\ p_sp0 P mod 16 = 0) /\
    (kHighMemBeg <= p_b6 P /\ p_sb P = space_beg_of (p_b6 P) /\ p_sb P + kSpaceSize + 4096 <= alloc_ceiling) /\
    (p_sb P mod 0x10000 = 0 /\ kHighMemBeg <= p_sb P /\ p_b6 P < p_sb P <= p_b6 P + 0x10000).
  Proof.
    pose proof (place_facts A0 init_WF) as X. cbv zeta in X. unfold A0_of in X. cbn [a_pl] in X.
    (first [ dand14 X as Pthr Pctx Pn0 Pf0 Pfs _ _ _ _ _ Pdt Ppa Psp _ | destruct X as (Pthr & Pctx & Pn0 & Pf0 & Pfs & _ & _ & _ & _ & _ & Pdt & Ppa & Psp & _) ]).
    (first [ pose proof ((sb_facts A0 init_WF)) as dR_2; dand5 dR_2 as SB1 SB2 SB3 SB4 SB5 | pose proof (sb_facts A0 init_WF) as (SB1 & SB2 & SB3 & SB4 & SB5) ]). unfold A0_of, a_sb, a_b6 in SB1, SB2, SB3, SB4, SB5. cbn [a_pl] in SB1, SB2, SB3, SB4, SB5.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try (apply (proj1 (aobj_app_rangeA _ _)); tauto); try tauto; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hull0 : pa_hull A0 = pa_image_ivs ++ hull_of (fixed_regions_ AL_pboth P) ++ p_extra P.
  Proof.
    unfold pa_hull, ahull_of, ahull_of_, aregions_, A0_of. cbn [a_pl a_reg a_sec a_deadsh sr_chunks p_extra].
    rewrite classes_regions_zero0. cbn [sec_regions_ flat_map app]. rewrite app_nil_r. reflexivity.
  Qed.
  Lemma vis_img : forall a n, 0x10000 <= a -> a + n <= 0x60a000 -> zrange_visible Hd a n.
  Proof.
    intros a n H1 H2 i Hi. unfold wa. rewrite hull0. apply pa_image_visible. unfold in_image. cbn [cl_image_lo cl_image_hi LPA]. lia.
  Qed.
  Lemma vis_fix : forall b s a n, In (b, s) (fixed_regions_ AL_pboth P) -> b <= a -> a + n <= b + s -> 0 <= a -> b + s <= 2^64 ->
    zrange_visible Hd a n.
  Proof.
    intros b s a n Hin H1 H2 H3 H4. apply (visible_of_region A0 b s a n); [| exact H1| exact H2| exact H3| exact H4].
    apply fixed_in_aregions. unfold A0_of. cbn [a_pl]. exact Hin.
  Qed.
  Tactic Notation "fixed_nth" integer(k) := unfold fixed_regions_; cbn [al_image_lo al_image_hi AL_pboth];
    do k right; left; reflexivity.
  #[using="RAW md FULL sp0"] Lemma vis_stk : zrange_visible Hd (p_sp0 P - 0x800000) 0x800000.
  Proof. pose proof PF. pose proof alloc_ceiling_val. apply (vis_fix (p_sp0 P - 0x800000) (0x800000 + p_stk_span P)); [fixed_nth 0| lia| lia| lia| lia]. Qed.
  Lemma vis_stksh : zrange_visible Hd (fst stack_shadow_iv) (snd stack_shadow_iv).
  Proof.
    (first [ pose proof (stack_shadow_iv_facts) as dR_3; dand4 dR_3 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
    apply (vis_fix (fst stack_shadow_iv) (snd stack_shadow_iv)); [| lia| lia| lia| kun0; lia].
    unfold fixed_regions_. do 1 right. left. destruct stack_shadow_iv; reflexivity.
  Qed.
  Lemma vis_imgsh : zrange_visible Hd 0x7fffa000 0xbf400.
  Proof. apply (vis_fix 0x7fffa000 0xbf400); [| lia| lia| lia| lia]. unfold fixed_regions_. cbn [al_image_lo al_image_hi AL_pboth]. do 2 right. left. reflexivity. Qed.
  #[using="RAW md FULL sp0"] Lemma vis_thr : forall a n, p_thr P <= a -> a + n <= p_thr P + 4096 -> zrange_visible Hd a n.
  Proof. intros. pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 X))). pose proof alloc_ceiling_val. apply (vis_fix (p_thr P) 4096); [fixed_nth 3| lia| lia| lia| lia]. Qed.
  #[using="RAW md FULL sp0"] Lemma vis_ctx : forall a n, p_ctx P <= a -> a + n <= p_ctx P + 0x10000 -> zrange_visible Hd a n.
  Proof. intros. pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 X)))). pose proof alloc_ceiling_val. apply (vis_fix (p_ctx P) 0x10000); [fixed_nth 4| lia| lia| lia| lia]. Qed.
  #[using="RAW md FULL sp0"] Lemma vis_ri : forall a n, p_ri P <= a -> a + n <= p_ri P + 4096 -> zrange_visible Hd a n.
  Proof. intros. pose proof PF. pose proof alloc_ceiling_val. unfold p_ri in *. apply (vis_fix (p_sb P + kSpaceSize) 4096); [fixed_nth 5| lia| lia| kun0; lia| kun0; lia]. Qed.
  #[using="RAW md FULL sp0"] Lemma vis_fs : forall a n, p_fs P <= a -> a + n <= p_fs P + kFakeStackBytes -> zrange_visible Hd a n.
  Proof. intros. pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 X))))))). pose proof alloc_ceiling_val. apply (vis_fix (p_fs P) kFakeStackBytes); [fixed_nth 6| lia| lia| lia| lia]. Qed.
  #[using="RAW md FULL sp0"] Lemma vis_fssh : zrange_visible Hd (sh (p_fs P)) (kFakeStackBytes / 8).
  Proof.
    pose proof PF as X. (first [ dand6 X as _ _ _ _ [FS1 FSM] _ | destruct X as (_ & _ & _ & _ & [FS1 FSM] & _) ]).
    (first [ pose proof ((aobj_facts _ _ FS1)) as dR_5; dand5 dR_5 as G1 _ G3 _ _ | pose proof (aobj_facts _ _ FS1) as (G1 & _ & G3 & _ & _) ]). pose proof alloc_ceiling_val.
    assert (FM : p_fs P mod 64 = 0) by (apply (mod0_down _ 4096 64); [exists 64; reflexivity| exact FSM]).
    pose proof (shadow_region_aligned (p_fs P) kFakeStackBytes FM eq_refl ltac:(kun0; lia)) as E.
    apply (vis_fix (sh (p_fs P)) (kFakeStackBytes / 8)); [| lia| lia| unfold sh; kun0; lia| unfold sh; kun0; lia].
    unfold fixed_regions_. do 7 right. left. rewrite <- E. reflexivity.
  Qed.
  #[using="RAW md FULL sp0"] Lemma vis_n0 : forall a n, p_nodes0 P <= a -> a + n <= p_nodes0 P + kDepotNodesBlock -> zrange_visible Hd a n.
  Proof. intros. pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 X))))). pose proof alloc_ceiling_val. apply (vis_fix (p_nodes0 P) kDepotNodesBlock); [fixed_nth 8| lia| lia| lia| lia]. Qed.
  #[using="RAW md FULL sp0"] Lemma vis_f0 : forall a n, p_frames0 P <= a -> a + n <= p_frames0 P + kStackStoreBlockBytes -> zrange_visible Hd a n.
  Proof. intros. pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 (proj2 X)))))). pose proof alloc_ceiling_val. apply (vis_fix (p_frames0 P) kStackStoreBlockBytes); [fixed_nth 9| lia| lia| lia| lia]. Qed.
  #[using="RAW md FULL sp0"] Lemma vis_dtls : forall a n, p_dtls P <= a -> a + n <= p_dtls P + 4096 -> zrange_visible Hd a n.
  Proof. intros. pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 X))))))))). pose proof alloc_ceiling_val. apply (vis_fix (p_dtls P) 4096); [fixed_nth 13| lia| lia| lia| lia]. Qed.

  (* [comment removed for export] *)
  Lemma T_bytes : forall a bs, bytes_at rsegs FULL a bs -> zrange_visible Hd a (Z.of_nat (length bs)) -> bytes_at rsegs v a bs.
  Proof. intros a bs B V. unfold aview_of. apply (proj1 (bytes_at_mrestrict rsegs _ FULL a bs V)). exact B. Qed.
  Lemma T_u64 : forall a x, u64_at rsegs FULL a x -> zrange_visible Hd a 8 -> u64_at rsegs v a x.
  Proof. intros a x B V. unfold u64_at in *. apply T_bytes; [exact B| rewrite length_le8; exact V]. Qed.
  Lemma T_u32 : forall a x, u32_at rsegs FULL a x -> zrange_visible Hd a 4 -> u32_at rsegs v a x.
  Proof. intros a x B V. unfold u32_at in *. apply T_bytes; [exact B| rewrite length_le4; exact V]. Qed.
  (* [comment removed for export] *)
  Lemma T_u8 : forall a x, u8_at rsegs FULL a x -> zrange_visible Hd a 1 -> u8_at rsegs v a x.
  Proof. intros a x B V. unfold u8_at in *. apply T_bytes; [exact B| exact V]. Qed.
  Lemma T_fill : forall a n x, fill_at rsegs FULL a n x -> zrange_visible Hd a n -> fill_at rsegs v a n x.
  Proof. intros a n x B V. unfold fill_at in *. apply T_bytes; [exact B|]. rewrite repeat_length. intros i Hi. apply V. lia. Qed.
  Lemma T_mapped : forall a n, mapped FULL a n -> zrange_visible Hd a n -> mapped v a n.
  Proof. intros a n M V. unfold aview_of. apply (proj2 (mapped_view_iff _ FULL a n V)). exact M. Qed.
  (* [comment removed for export] *)
  Lemma Z_bytes : forall a n, zero_at FULL a n -> 0 <= a -> a + n <= 2^64 -> 0 <= n -> bytes_at rsegs FULL a (repeat (Z_to_bv 8 0) (Z.to_nat n)).
  Proof.
    intros a n Z0 H1 H2 Hn. split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
    unfold mrd, wa. rewrite (Z0 (Z.of_nat i) ltac:(lia)). rewrite nth_error_repeat by lia. reflexivity.
  Qed.
  Lemma Z_u64 : forall a n, zero_at FULL a n -> 0 <= a -> a + n <= 2^64 ->
    forall off, 0 <= off -> off + 8 <= n -> zrange_visible Hd (a + off) 8 -> u64_at rsegs v (a + off) 0.
  Proof.
    intros a n Z0 H1 H2 off Ho1 Ho2 V. apply T_u64; [| exact V]. unfold u64_at. change (le8 (wz 0)) with (repeat (Z_to_bv 8 0) (Z.to_nat 8)).
    apply Z_bytes; [| lia| lia| lia]. intros i Hi. replace (a + off + i) with (a + (off + i)) by lia. apply Z0. lia.
  Qed.
  Lemma Z_u32 : forall a n, zero_at FULL a n -> 0 <= a -> a + n <= 2^64 ->
    forall off, 0 <= off -> off + 4 <= n -> zrange_visible Hd (a + off) 4 -> u32_at rsegs v (a + off) 0.
  Proof.
    intros a n Z0 H1 H2 off Ho1 Ho2 V. apply T_u32; [| exact V]. unfold u32_at. change (le4 (wz 0)) with (repeat (Z_to_bv 8 0) (Z.to_nat 4)).
    apply Z_bytes; [| lia| lia| lia]. intros i Hi. replace (a + off + i) with (a + (off + i)) by lia. apply Z0. lia.
  Qed.
  Lemma Z_u8 : forall a n, zero_at FULL a n -> 0 <= a -> a + n <= 2^64 ->
    forall off, 0 <= off -> off + 1 <= n -> zrange_visible Hd (a + off) 1 -> u8_at rsegs v (a + off) 0.
  Proof.
    intros a n Z0 H1 H2 off Ho1 Ho2 V. apply T_u8; [| exact V]. unfold u8_at. change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0) (Z.to_nat 1)).
    apply Z_bytes; [| lia| lia| lia]. intros i Hi. replace (a + off + i) with (a + (off + i)) by lia. apply Z0. lia.
  Qed.
  Lemma Z_junk : forall a n, zero_at FULL a n -> 0 <= a -> a + n <= 2^64 ->
    forall off k, 0 <= off -> 0 <= k -> off + k <= n -> zrange_visible Hd (a + off) k -> junk_at rsegs v (a + off) k.
  Proof.
    intros a n Z0 H1 H2 off k Ho1 Hk Ho2 V. exists (repeat (Z_to_bv 8 0) (Z.to_nat k)). rewrite repeat_length. split; [lia|].
    apply T_bytes; [| rewrite repeat_length, Z2Nat.id by lia; exact V]. apply Z_bytes; [| lia| lia| lia].
    intros i Hi. replace (a + off + i) with (a + (off + i)) by lia. apply Z0. lia.
  Qed.
  Lemma Z_mapped : forall a n, zero_at FULL a n -> mapped FULL a n.
  Proof. intros a n Z0 i Hi. rewrite (Z0 i Hi). discriminate. Qed.
  Lemma M_junk : forall a n, mapped FULL a n -> 0 <= a -> (a + n <= 0x10000 \/ 0x60a000 <= a) -> a + n <= 2^64 -> 0 <= n -> zrange_visible Hd a n -> junk_at rsegs v a n.
  Proof. intros a n M H1 H2 H3 Hn V. apply junk_at_of_mapped; [lia| lia| lia|]. apply T_mapped; [exact M| exact V]. Qed.

  (* [comment removed for export] *)
  Lemma vis_pt : forall a, zrange_visible Hd a 1 -> Hd (wa a) = false.
  Proof. intros a V. pose proof (V 0 ltac:(lia)) as Q. rewrite Z.add_0_r in Q. exact Q. Qed.
  Lemma AGv : forall a n i, zrange_visible Hd a n -> 0 <= i < n -> v (wz (a + i)) = FULL (wz (a + i)).
  Proof. intros a n i V Hi. unfold aview_of. apply view_visible. exact (V i Hi). Qed.
  Lemma Vimg : forall a, 0x10000 <= a < 0x60a000 -> v (wz a) = FULL (wz a).
  Proof. intros a Ha. rewrite <- (Z.add_0_r a). apply (AGv a 1 0); [apply vis_img; lia| lia]. Qed.
  #[using="RAW md sp0"] Lemma Vthr : forall a, p_thr P <= a < p_thr P + 4096 -> v (wz a) = FULL (wz a).
  Proof. intros a Ha. rewrite <- (Z.add_0_r a). apply (AGv a 1 0); [apply vis_thr; lia| lia]. Qed.
  #[using="RAW md sp0"] Lemma Vctx : forall a, p_ctx P <= a < p_ctx P + 0x10000 -> v (wz a) = FULL (wz a).
  Proof. intros a Ha. rewrite <- (Z.add_0_r a). apply (AGv a 1 0); [apply vis_ctx; lia| lia]. Qed.
  #[using="RAW md sp0"] Lemma Vri : forall a, p_ri P <= a < p_ri P + 4096 -> v (wz a) = FULL (wz a).
  Proof. intros a Ha. rewrite <- (Z.add_0_r a). apply (AGv a 1 0); [apply vis_ri; lia| lia]. Qed.
  #[using="RAW md sp0"] Lemma Vdtls : forall a, p_dtls P <= a < p_dtls P + 4096 -> v (wz a) = FULL (wz a).
  Proof. intros a Ha. rewrite <- (Z.add_0_r a). apply (AGv a 1 0); [apply vis_dtls; lia| lia]. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma shared_img : forall a, cl_shared LPA a -> 0x10000 <= a < 0x60a000.
  Proof. intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. lia. Qed.

  (* [comment removed for export] *)
  Ltac trim := repeat match goal with H : _ /\ _ /\ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : a0_raw _ _ _ _ _ |- _ => clear H end.
  Ltac by_img := apply Vimg; trim; unfold rt_statics in *; offs; lia.
  Ltac by_thr := apply Vthr; trim; offs; lia.
  Ltac by_ctx := apply Vctx; trim; offs; lia.
  Ltac leaf H AG :=
    lazymatch type of H with
    | u64_at _ _ _ _ => eapply u64_at_agree; [exact H|]; intros i__ Hi__; AG
    | u32_at _ _ _ _ => eapply u32_at_agree; [exact H|]; intros i__ Hi__; AG
    | u16_at _ _ _ _ => eapply u16_at_agree; [exact H|]; intros i__ Hi__; AG
    | u8_at _ _ _ _ => eapply u8_at_agree;  [exact H|]; AG
    | fill_at _ _ _ _ _ => eapply fill_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    | junk_at _ _ _ _ => eapply junk_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    end.
  Ltac walk H AG :=
    lazymatch goal with
    | |- _ /\ _ => let H1 := fresh "L" in let H2 := fresh "L" in destruct H as [H1 H2]; split; [walk H1 AG | walk H2 AG]
    | |- _ => leaf H AG
    end.

  (* [comment removed for export] *)
  #[using="RAW md sp0"] Lemma init_consts : consts_repr_ LPA AL_pboth P v.
  Proof.
    pose proof (ar0_consts _ _ _ _ _ RAW) as C. pose proof PF as X.
    pose proof (aobj_facts _ _ (proj1 (proj1 X))) as THF. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 X)))) as CTF.
    pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 X))))))))) as DTF.
    unfold consts_repr_ in *. cbv zeta in *. destruct C as (CF & C).
    split.
    { apply Forall_forall. intros cst Hc. pose proof (proj1 (Forall_forall _ _) CF cst Hc) as B.
      apply T_bytes; [exact B|]. intros i Hi. cbn [cl_consts LPA] in Hc. apply vis_pt.
      destruct (pa_consts_where cst (fst cst + i) Hc ltac:(lia)) as [S|[S|S]].
      - apply vis_img; [pose proof (shared_img _ S); lia| pose proof (shared_img _ S); lia].
      - unfold pa_image_shadow in S. change (sh 0x10000) with 0x7fffa000 in S. change (sh 0x60a000) with 0x800b9400 in S.
        replace (fst cst + i) with (0x7fffa000 + (fst cst + i - 0x7fffa000)) by lia. intros j Hj. rewrite <- Z.add_assoc. apply vis_imgsh. lia.
      - pose proof (pa_static_low _ S). apply vis_img; [unfold pa_static in S; lia| lia]. }
    assert (TP : bv_unsigned (cl_tp LPA) = 0x5e7bd8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    do 17 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_img |]).
    (first [ dand7 C as K1 K2 K3 KS KE1 KE2 C | destruct C as (K1 & K2 & K3 & KS & KE1 & KE2 & C) ]).
    split; [leaf K1 by_img|]. split; [leaf K2 by_img|]. split; [leaf K3 by_img|].
    split; [exact KS|]. split; [exact KE1|]. split; [exact KE2|].
    do 7 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_img |]).
    do 5 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_thr |]).
    do 2 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_ctx |]).
    destruct C as [(tsd & T1 & T2 & T3) C]. split.
    - exists tsd. split; [|split; [exact T2|]].
      + leaf T1 ltac:(apply Vimg; rewrite TP; lia).
      + leaf T3 ltac:(apply Vimg; apply shared_img; apply T2; lia).
    - (first [ dand5 C as C D1 D2 D3 D4 | destruct C as (C & D1 & D2 & D3 & D4) ]). split; [leaf C ltac:(apply Vimg; rewrite TP; lia)|].
      split; [leaf D1 ltac:(apply Vimg; rewrite TP; lia)|].
      split; [leaf D2 ltac:(apply Vdtls; lia)|].
      split; [leaf D3 by_thr| leaf D4 by_thr].
  Qed.

  #[using="RAW md sp0"] Lemma init_locks : locks_repr_ LPA AL_pboth P [] v.
  Proof.
    pose proof (ar0_locks _ _ _ _ _ RAW) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    split.
    - intros c Hc. destruct (C0 c Hc) as [X Y]. split; [leaf X ltac:(apply Vri; offs; lia) | leaf Y ltac:(apply Vri; offs; lia)].
    - walk C by_img.
  Qed.

  #[using="RAW md sp0"] Lemma init_regions : forall c, 1 <= c <= 30 -> region_repr_ LPA (p_sb P) region_zero v c.
  Proof.
    intros c Hc. pose proof (ar0_ri_zero _ _ _ _ _ RAW) as RZ. pose proof PF as X. pose proof alloc_ceiling_val as CE.
    (first [ dand10 X as _ _ _ _ _ _ _ _ (B6H & SBE & SCE) (SBA & SBH & RSB) | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & (B6H & SBE & SCE) & (SBA & SBH & RSB)) ]).
    unfold region_repr_, region_zero. cbv zeta. cbn [rg_free rg_mapped_fa rg_allocated_user rg_mapped_user length]. unfold region_info_addr. fold (p_ri P).
    assert (ZC : forall off k, 0 <= off -> 0 <= k -> off + k <= 128 -> zrange_visible Hd (p_ri P + (kRegionInfoSize * c + off)) k).
    { intros off k H1 H2 H3. apply vis_ri; kun0; lia. }
    assert (U64 : forall off, 0 <= off -> off + 8 <= 128 -> u64_at rsegs v (p_ri P + kRegionInfoSize * c + off) 0).
    { intros off H1 H2. rewrite <- Z.add_assoc. apply (Z_u64 (p_ri P) 4096 RZ); unfold p_ri in *; kun0; try lia. apply ZC; lia. }
    offs. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try (apply U64; lia).
    - rewrite <- Z.add_assoc. apply (Z_u8 (p_ri P) 4096 RZ); unfold p_ri in *; kun0; try lia. apply ZC; lia.
    - rewrite <- Z.add_assoc. apply (Z_junk (p_ri P) 4096 RZ); unfold p_ri in *; kun0; try lia. apply ZC; lia.
    - rewrite <- Z.add_assoc. apply (Z_junk (p_ri P) 4096 RZ); unfold p_ri in *; kun0; try lia. apply ZC; lia.
    - rewrite <- Z.add_assoc. apply (Z_junk (p_ri P) 4096 RZ); unfold p_ri in *; kun0; try lia. apply ZC; lia.
    - intros i k E. destruct i; discriminate.
    - intros i Hi. lia.
    - intros i Hi. lia.
  Qed.

  #[using="RAW md sp0"] Lemma init_cache : cache_repr_ LPA P (fun _ => PCc []) false v.
  Proof.
    pose proof (ar0_thr_zero _ _ _ _ _ RAW) as TZ. pose proof (ar0_thr_map _ _ _ _ _ RAW) as [TM CM]. pose proof PF as X. pose proof alloc_ceiling_val as CE.
    pose proof (aobj_facts _ _ (proj1 (proj1 X))) as THF. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 X)))) as CTF.
    unfold cache_repr_. cbv zeta. cbn [pk_chunks length andb].
    assert (U32 : forall off, 80 <= off -> off + 4 <= 2800 -> u32_at rsegs v (p_thr P + off) 0).
    { intros off H1 H2. replace (p_thr P + off) with (p_thr P + 80 + (off - 80)) by lia. apply (Z_u32 (p_thr P + 80) (2800 - 80) TZ); kun0; try lia. apply vis_thr; lia. }
    assert (U64 : forall off, 80 <= off -> off + 8 <= 2800 -> u64_at rsegs v (p_thr P + off) 0).
    { intros off H1 H2. replace (p_thr P + off) with (p_thr P + 80 + (off - 80)) by lia. apply (Z_u64 (p_thr P + 80) (2800 - 80) TZ); kun0; try lia. apply vis_thr; lia. }
    assert (JK : forall off k, 0 <= off -> 0 <= k -> off + k <= 4096 -> junk_at rsegs v (p_thr P + off) k).
    { intros off k H1 H2 H3. apply M_junk; [| lia| clear -THF H1 H2 H3; lia| lia| lia| apply vis_thr; lia]. intros i Hi. replace (p_thr P + off + i) with (p_thr P + (off + i)) by lia. apply TM. lia. }
    split; [| split; [apply JK; offs; lia| split; [apply JK; offs; lia| split; [apply T_mapped; [exact TM| apply vis_thr; lia]| apply T_mapped; [exact CM| apply vis_ctx; lia]]]]].
    intros c Hc. offs. split; [lia|]. split; [rewrite Z.add_0_r; apply U32; lia|]. split; [split; [rewrite <- Z.add_assoc; apply U32; lia| rewrite <- Z.add_assoc; apply U64; lia]|].
    split; [intros i k E; destruct i; discriminate|]. rewrite <- Z.add_assoc. apply JK; lia.
  Qed.

  Lemma init_live : live_repr_ LPA (p_sb P) (∅ : gmap Z liveinfo) v.
  Proof. intros u li Hl. rewrite lookup_empty in Hl. discriminate. Qed.

  #[using="RAW md sp0"] Lemma init_quar : quarantine_repr_ LPA AL_pboth P [] [] v.
  Proof.
    pose proof (ar0_thr_zero _ _ _ _ _ RAW) as TZ. pose proof (ar0_qglobal_zero _ _ _ _ _ RAW) as QZ. pose proof PF as X. pose proof alloc_ceiling_val as CE.
    pose proof (aobj_facts _ _ (proj1 (proj1 X))) as THF.
    unfold quarantine_repr_, qcache_repr. cbn [length batches_repr app q_bytes fold_right q_entries flat_map].
    assert (U64 : forall off, 80 <= off -> off + 8 <= 2800 -> u64_at rsegs v (p_thr P + off) 0).
    { intros off H1 H2. replace (p_thr P + off) with (p_thr P + 80 + (off - 80)) by lia. apply (Z_u64 (p_thr P + 80) (2800 - 80) TZ); kun0; try lia. apply vis_thr; lia. }
    assert (QV : fill_at rsegs v (al_instance AL_pboth + off_q_cache_list_size) 32 0).
    { apply T_fill; [exact QZ|]. apply vis_img; cbn [al_instance AL_pboth]; offs; lia. }
    set (QB := al_instance AL_pboth + off_q_cache_list_size) in QV.
    assert (QBE : QB = 726360 + 888) by reflexivity.
    unfold fill_at in QV.
    assert (G64 : forall off, 0 <= off -> off + 8 <= 32 -> u64_at rsegs v (726360 + 888 + off) 0).
    { intros off H1 H2. unfold u64_at. change (le8 (wz 0)) with (repeat (Z_to_bv 8 0) (Z.to_nat 8)). rewrite <- QBE.
      replace (QB + off) with (QB + Z.of_nat (Z.to_nat off)) by lia.
      rewrite <- (repeat_mid0 (Z_to_bv 8 0) (Z.to_nat 32) (Z.to_nat off) (Z.to_nat 8)) by lia. apply bytes_at_mid0; [exact QV| rewrite repeat_length; lia]. }
    offs. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
      first [ rewrite <- ?Z.add_assoc; apply U64; lia
            | replace (726360 + 888) with (726360 + 888 + 0) by lia; apply G64; lia
            | apply G64; lia
            | intros e [] ].
  Qed.

  #[using="RAW md sp0"] Lemma init_sec : sec_repr_ LPA AL_pboth P (SR [] 0) v.
  Proof.
    pose proof (ar0_sec_zero _ _ _ _ _ RAW) as [S1 S2]. unfold sec_repr_. cbv zeta. cbn [sr_reserved sr_chunks length al_instance AL_pboth] in *.
    split; [apply T_u64; [exact S1| apply vis_img; offs; lia]|].
    split; [apply T_u64; [exact S2| apply vis_img; offs; lia]|].
    split; [apply img_junk; offs; lia|]. split; [apply img_junk; offs; lia|]. split; [apply img_junk; offs; lia|].
    split; [intros i sc E; destruct i; discriminate|].
    pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 X)))))))) as PAF.
    intros i Hi. lia.
  Qed.

  #[using="RAW md sp0"] Lemma init_depot_raw : a0_depot_raw P k1 v.
  Proof.
    pose proof (ar0_depot _ _ _ _ _ RAW) as D. pose proof PF as X. destruct D as [K TAB NU M0 MJ N1 NZ SST SSA SSB FR BL].
    cbn [al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore AL_pboth] in *.
    assert (ZV : forall a n, zero_at FULL a n -> (forall i, 0 <= i < n -> zrange_visible Hd (a + i) 1) -> zero_at v a n).
    { intros a n Z0 V i Hi. rewrite (AGv (a + i) 1 0 (V i Hi) ltac:(lia)) || (rewrite <- (Z.add_0_r (a + i)); rewrite (AGv (a + i) 1 0 (V i Hi) ltac:(lia))); rewrite ?Z.add_0_r; apply Z0; lia. }
    constructor; cbn [al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore AL_pboth].
    - exact K.
    - intros b Hb. apply T_u32; [exact (TAB b Hb)| apply vis_img; lia].
    - apply T_u32; [exact NU| apply vis_img; lia].
    - apply T_u64; [exact M0| apply vis_img; lia].
    - intros j Hj. apply T_u64; [exact (MJ j Hj)| apply vis_img; kun0; lia].
    - (first [ dand3 N1 as A1 A2 A3 | destruct N1 as (A1 & A2 & A3) ]). split; [apply T_u64; [exact A1| apply vis_n0; kun0; lia]|].
      split; [apply T_u32; [exact A2| apply vis_n0; kun0; lia]| apply T_u32; [exact A3| apply vis_n0; kun0; lia]].
    - destruct NZ as [Z1 Z2]. split; apply ZV; [exact Z1| | exact Z2|]; intros i Hi; apply vis_n0; kun0; lia.
    - apply T_u64; [exact SST| apply vis_img; lia].
    - apply T_u64; [exact SSA| apply vis_img; lia].
    - (first [ dand3 SSB as B1 B2 B3 | destruct SSB as (B1 & B2 & B3) ]). split; [apply T_u64; [exact B1| apply vis_img; lia]|].
      split; [apply T_u32; [exact B2| apply vis_img; lia]| apply T_u32; [exact B3| apply vis_img; lia]].
    - (first [ dand3 FR as F1 F2 F3 | destruct FR as (F1 & F2 & F3) ]). destruct K as [KL _].
      split; [apply T_u64; [exact F1| apply vis_f0; kun0; lia]|].
      split; [| apply ZV; [exact F3| intros i Hi; apply vis_f0; kun0; lia]].
      intros t w E. pose proof (proj1 (nth_error_Some k1 t) ltac:(rewrite E; discriminate)).
      apply T_u64; [exact (F2 t w E)| apply vis_f0; kun0; lia].
    - destruct BL as [M1 M2]. split; [apply T_mapped; [exact M1| apply vis_n0; lia]| apply T_mapped; [exact M2| apply vis_f0; lia]].
  Qed.
  #[using="RAW DI md sp0"] Lemma init_depot : depot_repr_ LPA AL_pboth P [k1] v.
  Proof. unfold depot_repr_. change (cl_segs LPA) with ASEGS. apply (DI P k1 sp0 FULL md); [exact RAW| exact init_depot_raw]. Qed.

  #[using="RAW md sp0"] Lemma init_ia : ia_repr_ LPA AL_pboth false v.
  Proof.
    pose proof (ar0_ia _ _ _ _ _ RAW) as [I1 I2]. unfold ia_repr_. cbv zeta. cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pboth] in *.
    assert (FV : fill_at rsegs v 744896 0x81030 0) by (apply T_fill; [exact I2| apply vis_img; lia]).
    split; [| split; [apply T_u8; [exact I1| apply vis_img; lia]| exact FV]].
    intros i Hi. unfold fill_at in FV. unfold u64_at. change (le8 (wz 0)) with (repeat (Z_to_bv 8 0) (Z.to_nat 8)).
    replace (744896 + 8 + 8 * i) with (744896 + Z.of_nat (Z.to_nat (8 + 8 * i))) by lia.
    rewrite <- (repeat_mid0 (Z_to_bv 8 0) (Z.to_nat 0x81030) (Z.to_nat (8 + 8 * i)) (Z.to_nat 8)) by (kun0; lia).
    apply bytes_at_mid0; [exact FV| rewrite repeat_length; kun0; lia].
  Qed.

  #[using="RAW md sp0"] Lemma init_fsbase : fs_base_ LPA P (fun _ => 0) v.
  Proof.
    pose proof (ar0_fs_hints _ _ _ _ _ RAW) as FH. pose proof (ar0_fs_log _ _ _ _ _ RAW) as [L1 L2]. pose proof (ar0_fs_map _ _ _ _ _ RAW) as [M1 M2]. pose proof PF as X.
    pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 X))))))) as FSF. pose proof alloc_ceiling_val as CE.
    unfold fs_base_. cbv zeta. split; [| split; [| split; [| split]]].
    - intros k Hk. rewrite ?Z.mod_0_l by lia. apply (Z_u64 (p_fs P) 88 FH); kun0; try lia. apply vis_fs; kun0; lia.
    - apply T_u64; [exact L1| apply vis_fs; kun0; lia].
    - apply T_u8; [exact L2| apply vis_fs; kun0; lia].
    - apply T_mapped; [exact M1| apply vis_fs; lia].
    - apply T_mapped; [exact M2| apply vis_fssh].
  Qed.
  Lemma init_fsptrs : fs_ptrs_ LPA (p_fs P) (fun _ => 0) (∅ : gmap Z fframe) v.
  Proof. intros ff f Hf. rewrite lookup_empty in Hf. discriminate. Qed.
  #[using="RAW md sp0"] Lemma init_fsflags : fs_flags_ LPA (p_fs P) (fun _ => 0) (∅ : gmap Z fframe) v.
  Proof.
    pose proof (ar0_fs_flags _ _ _ _ _ RAW) as FZ. pose proof PF as X. pose proof (aobj_facts _ _ (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 X))))))) as FSF.
    pose proof alloc_ceiling_val as CE. intros k pos Hk Hpos.
    pose proof (fflag_addr_range (p_fs P) k pos Hk Hpos) as R. exists 0. split.
    - unfold fflag_addr in *. replace (p_fs P + kFakeFlagsOffset + fflags_off k + pos) with (p_fs P + kFakeFlagsOffset + (fflags_off k + pos)) by lia.
      apply (Z_u8 (p_fs P + kFakeFlagsOffset) (kFakeFramesOffset - kFakeFlagsOffset) FZ); kun0; try lia. apply vis_fs; kun0; lia.
    - right. split; [reflexivity|]. ((first [ intro dR_21; dex2 dR_21 as ff f; destruct dR_21 as [Hf _] | intro dR_21; dand4 dR_21 as ff f Hf _ | intros (ff & f & Hf & _) ])). rewrite lookup_empty in Hf. discriminate.
  Qed.

  #[using="RAW md sp0"] Lemma init_maps : maps_repr_ AL_pboth P v.
  Proof.
    pose proof (ar0_maps _ _ _ _ _ RAW) as SM. pose proof (ar0_sp0 _ _ _ _ _ RAW) as E0. pose proof (ar0_ri_zero _ _ _ _ _ RAW) as RZ.
    pose proof (ar0_stkshadow_map _ _ _ _ _ RAW) as SS. pose proof (ar0_imgshadow_map _ _ _ _ _ RAW) as IS. pose proof PF as X.
    unfold maps_repr_. cbn [al_image_lo al_image_hi AL_pboth].
    change (shadow_region 65536 (6332416 - 65536)) with (0x7fffa000, 0xbf400). cbn [fst snd].
    split; [rewrite E0; apply T_mapped; [exact SM| rewrite <- E0; apply vis_stk]|].
    split; [apply T_mapped; [apply Z_mapped; exact RZ| apply vis_ri; lia]|].
    split; [apply T_mapped; [exact SS| apply vis_stksh]| apply T_mapped; [exact IS| apply vis_imgsh]].
  Qed.

  #[using="RAW md sp0"] Lemma init_shadow : shadow_repr_ LPA (p_sb P) (fun _ => region_zero) (fun _ => PCc []) (∅ : gmap Z liveinfo) [] [] v.
  Proof.
    pose proof PF as X. (first [ dand10 X as _ _ _ _ _ _ _ _ (B6H & SBE & SCE) (SBA & SBH & RSB) | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & (B6H & SBE & SCE) & (SBA & SBH & RSB)) ]). pose proof alloc_ceiling_val as CE.
    split; [| split; [| split; [| split; [| split]]]].
    - intros c k Hc [F|[C|[E B]]]; [destruct F| destruct C| destruct B].
    - intros u c k n Hl. rewrite lookup_empty in Hl. discriminate.
    - intros c k n [].
    - intros c Hc. unfold region_zero. cbn [rg_allocated_user rg_mapped_user rg_mapped_fa]. cbv zeta.
      pose proof (sh_high_range (region_beg (p_sb P) c) ltac:(unfold region_beg; kun0; nia)) as [R1 R2].
      pose proof (sh_high_range (region_beg (p_sb P) c + kFreeArrayOffset) ltac:(unfold region_beg; kun0; nia)) as [R3 R4].
      unfold fill_at. change (Z.to_nat ((0 - 0) / 8)) with 0%nat. change (Z.to_nat (0 / 8)) with 0%nat. cbn [repeat]. rewrite Z.add_0_r.
      split; apply bytes_at_nil; kun0; lia.
    - intros u mb n Hl. rewrite lookup_empty in Hl. discriminate.
    - intros mb n0 n [].
  Qed.

  #[using="RAW DI md sp0"] Lemma init_arepr : arepr LPA AL_pboth [] A0 v.
  Proof.
    constructor; unfold A0_of; cbn [a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes].
    - exact init_consts. - exact init_locks. - exact init_regions. - exact init_cache. - exact init_live. - exact init_quar. - exact init_sec.
    - exact init_depot. - exact init_ia. - exact init_fsbase. - exact init_fsptrs. - exact init_fsflags. - exact init_maps. - exact init_shadow.
  Qed.

  #[using="RAW md sp0 k1"] Lemma init_hidden : hidden_repr P (fun _ => region_zero) (SR [] 0) FULL.
  Proof.
    split.
    - intros z [Hz NV]. rewrite (ar0_hidden _ _ _ _ _ RAW z Hz NV). split; [discriminate| reflexivity].
    - intros z Hz NV. rewrite (ar0_hidden _ _ _ _ _ RAW z ltac:(left; exact Hz) NV). discriminate.
  Qed.

  #[using="TOP RAW DI sp0"] Theorem init_ainv : pa_ainv A0 FULL md.
  Proof.
    constructor.
    - exact init_WF.
    - exact init_arepr.
    - exact init_hidden.
    - exact (ar0_extra _ _ _ _ _ RAW).
    - exact (ar0_ledger _ _ _ _ _ RAW).
    - exact (ar0_minv _ _ _ _ _ RAW).
    - exact (ar0_halted _ _ _ _ _ RAW).
    - (* [comment removed for export] *)
      unfold A0_of. cbn [a_pl a_sec]. unfold acover_. split; [| split].
      + (first [ pose proof ((ar0_vmmaps _ _ _ _ _ RAW)) as dR_13; dex1 dR_13 as fog; dand5 dR_13 as L1 L2 L3 L4 L5 | pose proof ((ar0_vmmaps _ _ _ _ _ RAW)) as dR_13; dand6 dR_13 as fog L1 L2 L3 L4 L5 | destruct (ar0_vmmaps _ _ _ _ _ RAW) as (fog & L1 & L2 & L3 & L4 & L5) ]).
        exists fog. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
        cbn [cl_image_lo cl_image_hi LPA] in L5 |- *. exact L5.
      + exact (ar0_gap _ _ _ _ _ RAW).
      + exact (ar0_reserved _ _ _ _ _ RAW).
    - exact TOP.
  Qed.

  Lemma init_owned : forall a, pa_owned A0 a ->
       cl_static LPA a \/ pa_image_shadow a
    \/ in_regions [ (p_thr P, 4096); (p_ctx P, 0x10000); (p_ri P, 4096); (p_fs P, kFakeStackBytes); (p_nodes0 P, kDepotNodesBlock);
                    (p_frames0 P, kStackStoreBlockBytes); (p_pa P, 8 * kChunksBlockCount); (p_itab P, 0x38e000); (p_m64k P, 0x10000); (p_dtls P, 4096);
                    (p_gvec P, 4096); (p_dvec P, 4096); (p_m11 P, 4096) ] a
    \/ (sh (p_fs P) <= a < sh (p_fs P) + kFakeStackBytes / 8)
    \/ ghost_hs_ P a.
  Proof.
    intros a H. unfold pa_owned, aowned, aowned_, A0_of in H. cbn [a_pl a_reg a_livemap a_sec a_fframes] in H.
    destruct H as [[S|[[(R & _ & _)|[HS|FS]]|GH]]|I].
    - left. exact S.
    - right; right; left. (first [ dex2 R as b sz; destruct R as [Hin Hb] | dand4 R as b sz Hin Hb | destruct R as (b & sz & Hin & Hb) ]). unfold runtime_maps_ in Hin. cbn [sr_chunks map] in Hin. rewrite app_nil_r in Hin.
      apply in_app_iff in Hin as [Hin|Hin]; [exists b, sz; split; [exact Hin| exact Hb]|].
      exfalso. apply in_flat_map in Hin as (c & _ & Hc). unfold region_zero in Hc. cbn [rg_mapped_user rg_mapped_fa] in Hc.
      destruct Hc as [E|[E|[]]]; injection E as _ <-; lia.
    - exfalso. unfold heap_shadow_, region_zero in HS. cbn [rg_mapped_user rg_mapped_fa sr_chunks] in HS. cbv zeta in HS.
      destruct HS as [(c & _ & Hc)|[(c & _ & Hc)|(sc & [] & _)]]; change (0 / 8) with 0 in Hc; lia.
    - right; right; right; left. destruct FS as [R _]. exact R.
    - right; right; right; right. exact GH.
    - right; left. exact I.
  Qed.

  #[using="RAW md FULL"] Theorem init_facts : a0_facts sp0 A0.
  Proof.
    pose proof PF as X. pose proof (ar0_sp0 _ _ _ _ _ RAW) as E0. pose proof alloc_ceiling_val as CE.
    (first [ pose proof (stack_shadow_iv_facts) as dR_15; dand4 dR_15 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
    constructor.
    - intros p. unfold as_live, as_live_, A0_of. cbn [a_livemap]. rewrite lookup_empty. reflexivity.
    - intros ff. unfold as_fframe, as_fframe_, A0_of. cbn [a_fframes]. rewrite lookup_empty. reflexivity.
    - unfold as_livebytes, as_livebytes_, A0_of. cbn [a_livemap]. rewrite map_fold_empty. reflexivity.
    - unfold as_tinycred, A0_of. cbn [a_tiny]. reflexivity.
    - unfold as_seccred, A0_of. cbn [a_scred]. reflexivity.
    - unfold as_primcred, A0_of. cbn [a_pcred]. reflexivity.
    - unfold as_nlive, as_nlive_, A0_of. cbn [a_livemap]. rewrite map_size_empty. reflexivity.
    - unfold A0_of. cbn [a_pl]. lia.
    - intros a Ha. unfold A0_of in Ha. cbn [a_pl al_image_lo al_image_hi AL_pboth] in Ha. apply vis_pt.
      destruct Ha as [H|[H|[H|H]]].
      + apply vis_img; lia.
      + rewrite <- E0 in H. apply (vis_fix (p_sp0 P - 0x800000) (0x800000 + p_stk_span P)); [fixed_nth 0| lia| lia| lia| lia].
      + change (sh 0x10000) with 0x7fffa000 in H. change (sh 0x60a000) with 0x800b9400 in H.
        intros i Hi. replace (a + i) with (0x7fffa000 + (a + i - 0x7fffa000)) by lia. apply vis_imgsh. lia.
      + intros i Hi. replace (a + i) with (fst stack_shadow_iv + (a + i - fst stack_shadow_iv)) by lia. apply vis_stksh. lia.
    - exact init_owned.
    - intros a Ha O. (first [ dand10 X as [TH _] [CT _] [N0 _] [F0 _] [FS FSM] [PA _] [DT _] SP (B6H & SBE & SCE) (SBA & SBH & RSB) | destruct X as ([TH _] & [CT _] & [N0 _] & [F0 _] & [FS FSM] & [PA _] & [DT _] & SP & (B6H & SBE & SCE) & (SBA & SBH & RSB)) ]).
      pose proof (aobj_facts _ _ TH) as THF. pose proof (aobj_facts _ _ CT) as CTF. pose proof (aobj_facts _ _ N0) as N0F.
      pose proof (aobj_facts _ _ F0) as F0F. pose proof (aobj_facts _ _ FS) as FSF. pose proof (aobj_facts _ _ PA) as PAF. pose proof (aobj_facts _ _ DT) as DTF.
      pose proof PL as W. apply wf_place_cheap in W.
      (first [ dand36 W as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IT1 IT2 _ M1 M2 _ GV1 GV2 _ DV1 DV2 _ M11a dR_W_t0; destruct dR_W_t0 as [M11b _] | destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IT1 & IT2 & _ & M1 & M2 & _ & GV1 & GV2 & _ & DV1 & DV2 & _ & M11a & M11b & _) ]).
      pose proof (fs_shadow_in_maps A0 a init_WF) as FSH. unfold A0_of, a_fs in FSH. cbn [a_pl] in FSH.
      unfold app_rangeA in IT1, M1, GV1, DV1, M11a. cbn [al_image_lo al_image_hi AL_pboth] in IT1, M1, GV1, DV1, M11a.
      destruct (init_owned a O) as [S|[I|[(b & sz & Hin & Hb)|[F|[GR _]]]]].
      + cbn [cl_static LPA] in S. pose proof (pa_static_low _ S). clear -Ha H SP E0 CE. lia.
      + unfold pa_image_shadow in I. change (sh 0x60a000) with 0x800b9400 in I. clear -Ha I SP E0 CE. lia.
      + cbn in Hin. unfold p_ri in *.
        destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-;
        lazymatch type of Hb with
        | p_thr P <= _ < _ => clear -Ha Hb THF SP E0 CE | p_ctx P <= _ < _ => clear -Ha Hb CTF SP E0 CE
        | p_sb P + _ <= _ < _ => clear -Ha Hb SCE SP E0 CE | p_fs P <= _ < _ => clear -Ha Hb FSF SP E0 CE
        | p_nodes0 P <= _ < _ => clear -Ha Hb N0F SP E0 CE | p_frames0 P <= _ < _ => clear -Ha Hb F0F SP E0 CE
        | p_pa P <= _ < _ => clear -Ha Hb PAF SP E0 CE | p_itab P <= _ < _ => clear -Ha Hb IT2 SP E0 CE
        | p_m64k P <= _ < _ => clear -Ha Hb M2 SP E0 CE | p_dtls P <= _ < _ => clear -Ha Hb DTF SP E0 CE
        | p_gvec P <= _ < _ => clear -Ha Hb GV2 SP E0 CE | p_dvec P <= _ < _ => clear -Ha Hb DV2 SP E0 CE
        | p_m11 P <= _ < _ => clear -Ha Hb M11b SP E0 CE
        end; kun0; lia.
      + specialize (FSH F). unfold in_shadow_maps in FSH. clear -Ha FSH SP E0 CE. kun0. lia.
      + unfold in_shadow_maps in GR. clear -Ha GR SP E0 CE. kun0. lia.
    - intros a Ha O. (first [ dand10 X as [TH _] [CT _] [N0 _] [F0 _] [FS FSM] [PA _] [DT _] SP (B6H & SBE & SCE) (SBA & SBH & RSB) | destruct X as ([TH _] & [CT _] & [N0 _] & [F0 _] & [FS FSM] & [PA _] & [DT _] & SP & (B6H & SBE & SCE) & (SBA & SBH & RSB)) ]).
      pose proof (aobj_facts _ _ TH) as THF. pose proof (aobj_facts _ _ CT) as CTF. pose proof (aobj_facts _ _ N0) as N0F.
      pose proof (aobj_facts _ _ F0) as F0F. pose proof (aobj_facts _ _ FS) as FSF. pose proof (aobj_facts _ _ PA) as PAF. pose proof (aobj_facts _ _ DT) as DTF.
      pose proof PL as W. apply wf_place_cheap in W.
      (first [ dand36 W as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IT1 IT2 _ M1 M2 _ GV1 GV2 _ DV1 DV2 _ M11a dR_W_t0; destruct dR_W_t0 as [M11b _] | destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IT1 & IT2 & _ & M1 & M2 & _ & GV1 & GV2 & _ & DV1 & DV2 & _ & M11a & M11b & _) ]).
      unfold app_rangeA in IT1, M1, GV1, DV1, M11a. cbn [al_image_lo al_image_hi AL_pboth] in IT1, M1, GV1, DV1, M11a.
      assert (SHC : 0x10006fef8000 <= sh alloc_ceiling) by (clear -SF2 SF4; lia).
      destruct (init_owned a O) as [S|[I|[(b & sz & Hin & Hb)|[F|[_ NV]]]]].
      + cbn [cl_static LPA] in S. pose proof (pa_static_low _ S). clear -Ha H SHC. kun0. lia.
      + unfold pa_image_shadow in I. change (sh 0x60a000) with 0x800b9400 in I. clear -Ha I SHC. kun0. lia.
      + cbn in Hin. unfold p_ri in *.
        destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-;
        lazymatch type of Hb with
        | p_thr P <= _ < _ => clear -Ha Hb THF SHC CE | p_ctx P <= _ < _ => clear -Ha Hb CTF SHC CE
        | p_sb P + _ <= _ < _ => clear -Ha Hb SCE SBH SHC CE | p_fs P <= _ < _ => clear -Ha Hb FSF SHC CE
        | p_nodes0 P <= _ < _ => clear -Ha Hb N0F SHC CE | p_frames0 P <= _ < _ => clear -Ha Hb F0F SHC CE
        | p_pa P <= _ < _ => clear -Ha Hb PAF SHC CE | p_itab P <= _ < _ => clear -Ha Hb IT1 IT2 SHC CE
        | p_m64k P <= _ < _ => clear -Ha Hb M1 M2 SHC CE | p_dtls P <= _ < _ => clear -Ha Hb DTF SHC CE
        | p_gvec P <= _ < _ => clear -Ha Hb GV1 GV2 SHC CE | p_dvec P <= _ < _ => clear -Ha Hb DV1 DV2 SHC CE
        | p_m11 P <= _ < _ => clear -Ha Hb M11a M11b SHC CE
        end; kun0; lia.
      + (* [comment removed for export] *)
        pose proof (sh_mono (p_fs P + kFakeStackBytes) alloc_ceiling (proj1 (proj2 (proj2 FSF)))) as M.
        rewrite (sh_add (p_fs P) kFakeStackBytes ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact FSM]) eq_refl) in M.
        clear -Ha F M. kun0. lia.
      + (* [comment removed for export] *) apply NV. exists alloc_ceiling, (2^47 - alloc_ceiling). split; [unfold VIS0, stack_band_iv; cbn; do 13 right; left; reflexivity|].
        clear -Ha CE. unfold sh, kShadowOffset, kHighMemBeg in *. replace (alloc_ceiling + (2^47 - alloc_ceiling)) with (2^47) by lia.
        change (2^47 / 8) with 17592186044416. lia.
    - exact PL.
  Qed.
End Init.

(* [comment removed for export] *)
Theorem ainit_of_raw_top {Clg : Ceiling} {DR : DepotRep} : ainit_top_stmt.
Proof.
  intros P k1 sp0 FULL md DI RAW TOP. exists (A0_of P k1).
  split; [exact (init_ainv P k1 sp0 FULL md DI RAW TOP)|]. split; [exact (init_facts P k1 sp0 FULL md RAW)| reflexivity].
Qed.
