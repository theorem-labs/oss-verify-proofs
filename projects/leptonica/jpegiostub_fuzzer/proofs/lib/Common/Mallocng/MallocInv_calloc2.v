(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocCallocFacts MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_live
  MallocInv_tables MallocInv_steps MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_calloc MallocIfaceX.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma replaced_read : forall m, replaced_clear m ->
  rdn ml_segs m A_MALLOC_REPLACED 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros m HC. pose proof (u64_range A_MALLOC_REPLACED) as HR. pose proof (mlo_order_replaced (ML:=ML)) as OR. pose proof layout_nums as LN.
  set (R := u A_MALLOC_REPLACED) in *. rewrite <- (Z_to_bv_bv_unsigned 64 A_MALLOC_REPLACED). fold R.
  assert (G : forall n a, R <= a -> a + Z.of_nat n <= R + 4 -> rdn ml_segs m (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n)).
  { induction n as [|n IH]; intros a Ha Hn; [reflexivity|].
    rewrite Nat2Z.inj_succ in Hn. rewrite rdn_S_split, rdn1_eq.
    rewrite (HC (Z_to_bv 64 a)) by (rewrite uZ by lia; lia).
    rewrite (mlo_ctx_zero (Z_to_bv 64 a)).
    2:{ rewrite uZ by lia. pose proof (mlo_order_ctx (ML:=ML)). pose proof (mlo_ctx (ML:=ML)). unfold LOCKA, CTX_SIZE in *. lia. }
    rewrite u_add1_lit, (IH (a + 1)) by lia. reflexivity. }
  rewrite (G 4%nat R) by (cbn; lia). reflexivity.
Qed.

Lemma replaced_range : RW_LO <= u A_MALLOC_REPLACED /\ u A_MALLOC_REPLACED + 4 <= IMG_HI /\ CTX_END <= u A_MALLOC_REPLACED.
Proof.
  pose proof layout_nums as LN. pose proof (mlo_order_ctx (ML:=ML)). pose proof (mlo_order_replaced (ML:=ML)).
  unfold CTX_END, LOCKA, CTX_SIZE in *. lia.
Qed.

Section Calloc.
  (* [comment removed for export] *)
  Hypothesis malloc_okX : forall A s (sp0 : word) argv envp (sp : word) (n : Z),
    call_env A s sp0 argv envp -> a_xmaps A = [] -> 0 <= n < 2^61 ->
    tsafe (m_malloc sp (Z_to_bv 64 n) s) (malloc_postX A n s).

  Theorem calloc_okX : forall A s (sp0 : word) argv envp (sp : word) (fuel : nat) (cnt sz : Z),
    call_env A s sp0 argv envp -> a_xmaps A = [] -> replaced_clear (ms_mem s) ->
    0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 -> cnt * sz / 4096 < Z.of_nat fuel ->
    tsafe (m_calloc fuel sp (Z_to_bv 64 cnt) (Z_to_bv 64 sz) s) (calloc_postX A (cnt * sz) s).
  Proof.
    intros A s sp0 argv envp sp fuel cnt sz HE Hxm Hrc Hcnt Hsz Hn Hfuel.
    pose proof HE as [HM HWIN HEnv]. pose proof HM as [HW HR HV HL HC H48]. pose proof layout_nums as LN. ceil.
    set (n := cnt * sz) in *.
    apply (tsafe_calloc fuel sp (Z_to_bv 64 cnt) (Z_to_bv 64 sz) s (malloc_postX A n s)).
    - (* [comment removed for export] *)
      intros Hovf. exfalso. apply Bool.andb_true_iff in Hovf. destruct Hovf as [H1 H2].
      rewrite is0_Z in H1 by lia. unfold v_mulhu in H2. rewrite !uZ in H2 by lia.
      rewrite Z.shiftr_div_pow2, Z.div_small in H2 by lia. cbn in H2. discriminate H2.
    - intros _. rewrite v_mul_Z. replace (sz * cnt) with n by (subst n; apply Z.mul_comm).
      assert (HuN : u (Z_to_bv 64 n) = n) by (apply uZ; lia).
      split; [exact (malloc_okX A s sp0 argv envp (at_ sp (-48)) n HE Hxm ltac:(lia))|].
      split.
      + (* [comment removed for export] *)
        intros s' (A' & Hxm' & HM' & Elo & Ehi & Hres & Hframe & Hlive & Hmap & Hfix). exists A'.
        split; [exact Hxm'|]. split; [exact HM'|]. split; [exact Elo|]. split; [exact Ehi|]. split; [| auto].
        destruct Hres as [(E & Hq) | (Hnz & _)]; [left; auto | exfalso; apply Hnz; reflexivity].
      + (* [comment removed for export] *)
        intros p s' HP Hp. pose proof HP as (A' & Hxm' & HM' & Elo & Ehi & Hres & Hframe & Hlive & Hmap & Hfix).
        destruct Hres as [(E & _) | (Hnz & Hfresh & Hl' & Hothers & Hown & Hzero)]; [exfalso; apply Hp; rewrite E; reflexivity|].
        pose proof HM' as [HW' HR' HV' HL' HC' H48'].
        assert (HWIN' : WIN s') by (unfold WIN in *; rewrite Elo, Ehi; exact HWIN).
        destruct (m_live_hull A' (ms_mem s') (ms_vm s') p n HM' Hl') as (Hn0 & Hal & Htop & Hhull).
        pose proof (round16_ge n) as R16. pose proof (u64_range p) as Hpu.
        assert (Eat : forall i, 0 <= i < round16 n -> u (at_ p i) = u p + i) by (intros i Hi; unfold at_; rewrite uZ by lia; lia).
        (* [comment removed for export] *)
        assert (Hrc' : replaced_clear (ms_mem s')).
        { intros a Ha. pose proof replaced_range as RR.
          assert (NO : forall B, WF B -> ~ mowned B a).
          { intros B HWB [Hc | Hd]; [clear - Hc Ha RR; lia|].
            destruct (dom_heap B (u a) HWB Hd) as (l & h & Hh & Hlh). unfold heap_range in Hh. clear - Hh Hlh Ha RR LN. lia. }
          rewrite (Hframe a (NO A HW) (NO A' HW')) by (unfold errno_slot; clear - Ha RR LN; lia). exact (Hrc a Ha). }
        assert (BLK : blk s' (u p) (u p + n)).
        { constructor.
          - lia.
          - left. unfold WIN in HWIN'. lia.
          - destruct (live_heap A' (u p) n HW' Hl') as (_ & _ & _ & Himg & _). clear - Himg R16. lia.
          - intros a Ha. replace a with (at_ p (u a - u p)) by (apply bv_eq; rewrite Eat by lia; lia). exact (proj1 (proj2 (Hhull (u a - u p) ltac:(lia)))). }
        split; [rewrite HuN; exact Hfuel|].
        pose proof (u64_range A_MALLOC_REPLACED) as HRu. pose proof replaced_range as RR.
        split; [rewrite <- (Z_to_bv_bv_unsigned 64 A_MALLOC_REPLACED); apply acc_ok_heap; [exact HWIN' | clear - HRu; lia | clear; lia | clear - RR LN HCEIL; lia]|].
        split; [exact (replaced_read (ms_mem s') Hrc')|].
        assert (HRO' : rodata_clear (ms_mem s')).
        { intros a Ha. pose proof (envok_rodata _ _ _ _ HEnv a Ha) as H0.
          assert (NO : forall B, WF B -> ~ mowned B (Z_to_bv 64 a)).
          { intros B HWB [Hc | Hd]; [rewrite uZ in Hc by (clear - Ha LN; lia); clear - Hc Ha LN; lia|].
            rewrite uZ in Hd by (clear - Ha LN; lia). destruct (dom_heap B a HWB Hd) as (l & h & Hh & Hlh). unfold heap_range in Hh. clear - Hh Hlh Ha LN. lia. }
          rewrite (Hframe (Z_to_bv 64 a) (NO A HW) (NO A' HW')); [exact H0|]. unfold errno_slot. rewrite uZ by (clear - Ha LN; lia).
          pose proof layout_statics as LS. clear - Ha LN LS. unfold ERRNO, GOTA in *. lia. }
        split.
        { rewrite HuN. rewrite <- (Z_to_bv_bv_unsigned 64 p). rewrite !uZ by lia.
          apply (allzerop_live_AZ A' s' (u p) n n HW' HR' HWIN' HRO' Hl').
          intros Hz a Ha. replace a with (at_ p (u a - u p)) by (apply bv_eq; rewrite Eat by lia; lia). apply (Hzero Hz). lia. }
        split; [rewrite HuN; exact BLK|].
        intros s'' Hvm'' Hlo'' Hhi'' BLK'' ZERO SAME. rewrite HuN in *.
        (* [comment removed for export] *)
        assert (OWNB : forall a : word, u p <= u a < u p + n -> mowned A' a).
        { intros a Ha. replace a with (at_ p (u a - u p)) by (apply bv_eq; rewrite Eat by lia; lia). exact (proj1 (Hhull (u a - u p) ltac:(lia))). }
        exists A'. split; [exact Hxm'|]. split.
        { rewrite Hvm''. apply (m_frame A' (ms_mem s') (ms_mem s'') (ms_vm s') HM').
          - intros a Ho Hnl. apply SAME. intros Hin. exact (Hnl p n Hl' Hin).
          - intros a Ho Hm. destruct (Z.lt_ge_cases (u a) (u p)) as [H1|H1]; [rewrite SAME by lia; exact Hm|].
            destruct (Z.lt_ge_cases (u a) (u p + n)) as [H2|H2]; [exact (blk_def _ _ _ BLK'' a ltac:(lia)) | rewrite SAME by lia; exact Hm].
          - intros a Hg Hm''. destruct (Z.lt_ge_cases (u a) (u p)) as [H1|H1]; [rewrite <- SAME by lia; exact Hm''|].
            destruct (Z.lt_ge_cases (u a) (u p + n)) as [H2|H2]; [exact (blk_def _ _ _ BLK a ltac:(lia)) | rewrite <- SAME by lia; exact Hm'']. }
        split; [rewrite Hlo''; exact Elo|]. split; [rewrite Hhi''; exact Ehi|].
        split.
        { right. split; [exact Hnz|]. split; [exact Hfresh|]. split; [exact Hl'|]. split; [exact Hothers|]. split; [exact Hown|].
          intros i Hi. apply ZERO. rewrite Eat by lia. lia. }
        split.
        { intros a Ho Ho' He. destruct (Z.lt_ge_cases (u a) (u p)) as [H1|H1]; [| destruct (Z.lt_ge_cases (u a) (u p + n)) as [H2|H2]; [exfalso; exact (Ho' (OWNB a ltac:(lia)))|]];
            rewrite SAME by lia; exact (Hframe a Ho Ho' He). }
        split.
        { intros q k i Hq Hi. destruct (live_heap A (u q) k HW Hq) as (Hk0 & Hqlo & Hqce & _ & _). pose proof (round16_ge k). pose proof (u64_range q).
          assert (Eq : u (at_ q i) = u q + i) by (unfold at_; rewrite uZ by lia; lia).
          assert (Hq' : mlive A' q = Some k) by (rewrite Hothers; [exact Hq | intros ->; rewrite Hfresh in Hq; discriminate]).
          assert (Hne : p <> q) by (intros ->; rewrite Hfresh in Hq; discriminate).
          destruct (m_live_disjoint A' (ms_mem s') (ms_vm s') p n q k HM' Hl' Hq' Hne) as [D|D];
            rewrite SAME by (rewrite Eq; lia); exact (Hlive q k i Hq Hi). }
        split.
        { intros a Ha. destruct (Hmap a Ha) as [X | [X | X]]; [left; exact X | right; left; exact X | right; right].
          destruct (Z.lt_ge_cases (u a) (u p)) as [H1|H1]; [rewrite SAME by lia; exact X|].
          destruct (Z.lt_ge_cases (u a) (u p + n)) as [H2|H2]; [exact (blk_def _ _ _ BLK'' a ltac:(lia)) | rewrite SAME by lia; exact X]. }
        rewrite Hvm''. exact Hfix.
  Qed.
End Calloc.

End WithLayout.
