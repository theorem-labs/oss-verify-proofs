(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare StoreOk MmapSim AllocSim ShapeAlg PureModel VmLedger AllocIface AsanCeil.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import RefStep RefStmts.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_live MallocInv_wf MallocInv_steps
  MallocInv_coh MallocInv_ops MallocInv_env MallocInv_auxv AllocBase AllocCalloc MallocAllocLayout MallocIfaceX
  MallocInv_ameta_iface MallocInv_ametax_iface.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section Glue.
  Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.
  Local Notation u := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition topH (vm : VmMaps) : Prop := 0x7fff7f800000 <= alloc_top vm <= 0x7fffff800000.
  Definition HTof (vm : VmMaps) (H : topH vm) : HeapTop := {| alloc_ceiling := alloc_top vm; alloc_ceiling_range := H |}.

  Definition g_inv (A : astate) (m : word -> option byte) (vm : VmMaps) : Prop :=
    exists H : topH vm, minv (HT:=HTof vm H) A m vm /\ a_xmaps A = [] /\ replaced_clear m.
  Definition g_live (A : astate) (p : word) : option Z := a_live A (u p).
  Definition g_owned (A : astate) (a : word) : Prop :=
    owned_of A (u a) \/ (u A_MALLOC_REPLACED <= u a < u A_MALLOC_REPLACED + 4).

  (* [comment removed for export] *)
  Definition g_noroom (n : Z) (A : astate) (vm : VmMaps) : Prop :=
    exists H : topH vm, malloc_noroomX (HT:=HTof vm H) n A vm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Existing Instance mallocng_alloc_layout.
  Let AL : AllocLayout := mallocng_alloc_layout.

  (* [comment removed for export] *)
  Let HT0 : HeapTop := {| alloc_ceiling := 0x7fff7f800000; alloc_ceiling_range := ltac:(lia) |}.

  Lemma replaced_range : RW_LO <= u A_MALLOC_REPLACED /\ u A_MALLOC_REPLACED + 4 <= IMG_HI /\ CTX_END <= u A_MALLOC_REPLACED.
  Proof.
    pose proof (layout_nums (HT:=HT0)) as LN. pose proof (mlo_order_ctx (ML:=ML)). pose proof (mlo_order_replaced (ML:=ML)).
    unfold CTX_END, LOCKA, CTX_SIZE in *. lia.
  Qed.

  Lemma g_globals_owned : forall A a, @al_globals AL a -> g_owned A a.
  Proof.
    intros A a [Hc | Hr]; [left | right; exact Hr].
    left. pose proof (layout_nums (HT:=HT0)) as LN. unfold LOCKA, CTX_END, CTX_SIZE in *. lia.
  Qed.

  Lemma alloc_globals_al : forall a, alloc_globals a -> @al_globals AL a.
  Proof. intros a Ha. left. pose proof (layout_nums (HT:=HT0)) as LN. unfold alloc_globals, LOCKA, CTX_END, CTX_SIZE in *. lia. Qed.

  Lemma g_live_hull : forall A m vm p n, g_inv A m vm -> mlive A p = Some n ->
      0 <= n /\ u p mod 16 = 0 /\ u p + round16 n <= alloc_top vm /\
      forall i, 0 <= i < round16 n ->
        g_owned A (at_ p i) /\ m (at_ p i) <> None /\ ~ @al_in_ro AL (at_ p i) /\ ~ @al_in_rw AL (at_ p i).
  Proof.
    intros A m vm p n (H & HM & _ & _) Hl.
    destruct (m_live_hull (HT:=HTof vm H) A m vm p n HM Hl) as (H1 & H2 & H3 & H4).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros i Hi. destruct (H4 i Hi) as (O & M & R & W). split; [left; exact O | auto].
  Qed.

  Lemma g_live_disjoint : forall A m vm p n q k, g_inv A m vm ->
      mlive A p = Some n -> mlive A q = Some k -> p <> q ->
      u p + round16 n <= u q \/ u q + round16 k <= u p.
  Proof. intros A m vm p n q k (H & HM & _ & _). exact (m_live_disjoint (HT:=HTof vm H) A m vm p n q k HM). Qed.

  Lemma g_live_not_globals : forall A m vm p n i, g_inv A m vm -> mlive A p = Some n ->
      0 <= i < round16 n -> ~ @al_globals AL (at_ p i).
  Proof.
    intros A m vm p n i HG Hl Hi [Hg | Hr].
    - destruct HG as (H & HM & _ & _). apply (m_live_not_globals (HT:=HTof vm H) A m vm p n i HM Hl Hi).
      pose proof (layout_nums (HT:=HT0)) as LN. unfold alloc_globals, LOCKA, CTX_END, CTX_SIZE in *. lia.
    - destruct (g_live_hull A m vm p n HG Hl) as (_ & _ & _ & H4). destruct (H4 i Hi) as (_ & _ & _ & W). apply W.
      pose proof replaced_range. cbn [al_in_rw AL mallocng_alloc_layout]. unfold mallocng_in_rw. lia.
  Qed.

  Lemma g_owned_where : forall A m vm a, g_inv A m vm -> g_owned A a ->
      @al_globals AL a \/ (grantable vm a /\ m a <> None).
  Proof.
    intros A m vm a (H & HM & _ & _) [Ho | Hr]; [| left; right; exact Hr].
    destruct (m_owned_where (HT:=HTof vm H) A m vm a HM Ho) as [Hg | [(G1 & G2) Hm]]; [left; exact (alloc_globals_al a Hg) | right].
    split; [| exact Hm]. split; [| exact (proj2 G1)]. split; [exact (proj1 G1) | exact G2].
  Qed.

  Lemma g_frame : forall A m m' vm, g_inv A m vm ->
      (forall a, g_owned A a ->
                 (forall p n, mlive A p = Some n -> ~ (u p <= u a < u p + n)) ->
                 m' a = m a) ->
      (forall a, g_owned A a -> m a <> None -> m' a <> None) ->
      (forall a, grantable vm a -> m' a <> None -> m a <> None) ->
      g_inv A m' vm.
  Proof.
    intros A m m' vm HG Hag Hkeep Hnew. pose proof HG as (H & HM & Hx & Hrc). exists H. split; [| split; [exact Hx|]].
    - apply (m_frame (HT:=HTof vm H) A m m' vm HM).
      + intros a Ho Hl. apply Hag; [left; exact Ho | exact Hl].
      + intros a Ho. apply Hkeep. left. exact Ho.
      + intros a (G1 & G2). apply Hnew. split; [split; [exact (proj1 G1) | exact G2] | exact (proj2 G1)].
    - intros a Ha. rewrite Hag; [exact (Hrc a Ha) | right; exact Ha |].
      intros p n Hl Hin. pose proof replaced_range as RR.
      destruct (m_live_hull (HT:=HTof vm H) A m vm p n HM Hl) as (Hn & _ & Htop & H4). pose proof (round16_ge n).
      assert (Ea : at_ p (u a - u p) = a) by (apply bv_eq; unfold at_; rewrite uZ by (pose proof (u64_range a); lia); lia).
      destruct (H4 (u a - u p) ltac:(lia)) as (_ & _ & _ & W). rewrite Ea in W. apply W. unfold in_rw. lia.
  Qed.

  Lemma g_init_owned : forall a, g_owned MallocInv_defs.A0 a <-> @al_globals AL a.
  Proof.
    intros a. split.
    - intros [Ho | Hr]; [| right; exact Hr]. apply alloc_globals_al. exact (proj1 (m_init_owned a) Ho).
    - exact (g_globals_owned MallocInv_defs.A0 a).
  Qed.

  Lemma init_topH : forall h0, init_ledger h0 -> topH h0.
  Proof.
    intros h0 IL. destruct (il_sp h0 IL) as (S1 & S2 & _). unfold topH, alloc_top, stack_max_size, sp_window_lo, sp_window_hi in *. lia.
  Qed.

  Lemma g_init : forall m h0, init_ledger h0 ->
      (forall a, @al_globals AL a -> m a = None) -> (forall a, grantable h0 a -> m a = None) -> g_inv MallocInv_defs.A0 m h0.
  Proof.
    intros m h0 IL Hg Hgr. exists (init_topH h0 IL). split; [| split; [reflexivity | intros a Ha; apply Hg; right; exact Ha]].
    apply (minv_init (HT:=HTof h0 (init_topH h0 IL)) m h0 (il_maps h0 IL) (il_noaccess h0 IL) (il_reserved h0 IL) (il_start_brk h0 IL) (il_brk h0 IL) eq_refl).
    - intros a Ha. apply Hg. apply alloc_globals_al. exact Ha.
    - intros a (G1 & G2). apply Hgr. split; [split; [exact (proj1 G1) | exact G2] | exact (proj2 G1)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Zle_irrel : forall (a b : Z) (p q : a <= b), p = q.
  Proof.
    intros a b p q. unfold Z.le in p, q.
    apply FunctionalExtensionality.functional_extensionality. intros x. destruct (p x).
  Qed.

  Lemma HT_eq : forall (T1 T2 : HeapTop), @alloc_ceiling T1 = @alloc_ceiling T2 -> T1 = T2.
  Proof.
    intros [c1 [p1 q1]] [c2 [p2 q2]] E. cbn in E. subst c2.
    rewrite (Zle_irrel _ _ p1 p2), (Zle_irrel _ _ q1 q2). reflexivity.
  Qed.

  Lemma minv_transport : forall (T1 T2 : HeapTop) A m vm,
    @alloc_ceiling T1 = @alloc_ceiling T2 -> minv (HT:=T1) A m vm -> minv (HT:=T2) A m vm.
  Proof. intros T1 T2 A m vm E HM. rewrite <- (HT_eq T1 T2 E). exact HM. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma call_env_of : forall vm (H : topH vm) A m (sp sp0 : word) argv envp (D : Z),
    minv (HT:=HTof vm H) A m vm -> mallocng_env sp0 argv envp m ->
    alloc_top vm + D <= u sp -> 0 <= D -> u sp <= u sp0 ->
    call_env (HT:=HTof vm H) A (MS m vm (u sp - D) (u sp)) sp0 argv envp.
  Proof.
    intros vm H A m sp sp0 argv envp D HM (E1 & E2 & E3 & E4 & E5) Htop HD Hsp0. pose proof (u64_range sp).
    constructor; cbn [ms_mem ms_vm ms_lo ms_hi].
    - exact HM.
    - unfold WIN. cbn. lia.
    - constructor; cbn [ms_mem ms_hi].
      + constructor; [intros a Ha; apply E5; exact Ha | exact E1 | exact (mi_lock _ _ _ HM)].
      + exact E3.
      + exact E2.
      + exact E4.
      + exact (mi_lock _ _ _ HM).
      + exact Hsp0.
  Qed.

  (* [comment removed for export] *)
  Lemma g_inv_after : forall vm (H : topH vm) A A' m0 (m' mm' : word -> option byte) vm' (lo hi : Z),
    minv (HT:=HTof vm H) A' m' vm' -> a_xmaps A' = [] ->
    alloc_top vm' = alloc_top vm -> alloc_top vm <= lo ->
    (forall a : word, ~ (lo <= u a < hi) -> mm' a = m' a) ->
    replaced_clear m0 ->
    (forall a : word, ~ mowned A a -> ~ mowned A' a -> ~ errno_slot a -> m' a = m0 a) ->
    WF (HT:=HTof vm H) A ->
    g_inv A' mm' vm'.
  Proof.
    intros vm H A A' m0 m' mm' vm' lo hi HM' Hxm' Etop Hlo Hag Hrc Hfr HWA.
    assert (H' : topH vm') by (unfold topH in *; rewrite Etop; exact H).
    exists H'. split; [| split; [exact Hxm'|]].
    - apply (minv_transport (HTof vm H) (HTof vm' H')); [cbn; symmetry; exact Etop|].
      apply (minv_agree (HT:=HTof vm H) A' m' mm' vm' HM'). intros a Ha. apply Hag. cbn in Ha. lia.
    - intros a Ha. pose proof replaced_range as RR. pose proof (layout_nums (HT:=HTof vm H)) as LN.
      assert (NO : forall B, WF (HT:=HTof vm H) B -> ~ mowned B a).
      { intros B HWB [Hc | Hd]; [unfold LOCKA, CTX_END in *; lia|].
        destruct (dom_heap (HT:=HTof vm H) B (u a) HWB Hd) as (l & h & Hh & Hlh). unfold heap_range in Hh. lia. }
      rewrite Hag by (cbn in *; unfold topH in H; lia).
      rewrite (Hfr a (NO A HWA) (NO A' (mi_wf _ _ _ HM'))) by (unfold errno_slot; unfold ERRNO in *; lia).
      exact (Hrc a Ha).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Ops.
    (* [comment removed for export] *)
    Hypothesis malloc_okX : forall (HT : HeapTop) A s (sp0 : word) argv envp (sp : word) (n : Z),
      call_env (HT:=HT) A s sp0 argv envp -> a_xmaps A = [] -> 0 <= n < 2^61 ->
      tsafe (m_malloc sp (Z_to_bv 64 n) s) (malloc_postX (HT:=HT) A n s).
    Hypothesis free_okX : forall (HT : HeapTop) A s (p sp0 : word) argv envp,
      call_env (HT:=HT) A s sp0 argv envp -> a_xmaps A = [] ->
      (p = Z_to_bv 64 0 \/ exists n, mlive A p = Some n) ->
      tsafe (m_free p s) (free_postX (HT:=HT) A p s).
    Hypothesis calloc_okX : forall (HT : HeapTop) A s (sp0 : word) argv envp (sp : word) (fuel : nat) (cnt sz : Z),
      call_env (HT:=HT) A s sp0 argv envp -> a_xmaps A = [] -> replaced_clear (ms_mem s) ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 -> cnt * sz / 4096 < Z.of_nat fuel ->
      tsafe (m_calloc fuel sp (Z_to_bv 64 cnt) (Z_to_bv 64 sz) s) (calloc_postX (HT:=HT) A (cnt * sz) s).
    (* [comment removed for export] *)
    Hypothesis malloc_refines : forall fx : FPState, malloc_stmt (fx:=fx).
    Hypothesis free_refines : forall fx : FPState, free_stmt (fx:=fx).
    Hypothesis calloc_refines : forall fx : FPState, calloc_stmt (fx:=fx).

    Lemma glue_malloc_g : forall (fx : FPState) A m md regs (n : Z) (ret sp0 : word) argv envp (S : TSet),
      g_inv A m (m_vmmaps md) -> md_pure md ->
      mallocng_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
      u (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= u (getr regs 2) ->
      u (getr regs 2) <= u sp0 ->
      (forall a : word, u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2) ->
                        m a <> None /\ ~ g_owned A a /\ ~ mallocng_in_ro a /\ ~ mallocng_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          g_inv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, mlive A' q = mlive A q))
            \/ (u res <> 0 /\ mlive A res = None /\ mlive A' res = Some n /\
                (forall q, q <> res -> mlive A' q = mlive A q) /\
                (forall i, 0 <= i < round16 n -> g_owned A (at_ res i) \/ m (at_ res i) = None)) ) ->
          (forall a, ~ g_owned A a -> ~ g_owned A' a -> ~ mallocng_errno_slot a ->
                     ~ (u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, mlive A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> u a < IMG_HI \/ g_owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          malloc_growX n A A' (m_vmmaps md) vm' -> (u res = 0 -> g_noroom n A (m_vmmaps md)) ->
          realizes ml_segs (mkCfg (mkst regs' ret m' ml_rom) (with_vmmaps vm' md)) S) ->
      realizes ml_segs (mkCfg (mkst regs PC_MALLOC m ml_rom) md) S.
    Proof.
      intros fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK.
      pose proof HG as (H & HM & Hxm & Hrc). pose proof (u64_range (getr regs 2)) as Hsp.
      set (sp := getr regs 2) in *. set (s := MS m (m_vmmaps md) (u sp - ALLOC_STACK) (u sp)).
      pose proof (call_env_of (m_vmmaps md) H A m sp sp0 argv envp ALLOC_STACK HM Henv ltac:(unfold ALLOC_STACK; lia) ltac:(unfold ALLOC_STACK; lia) Hsp0) as HE.
      fold s in HE.
      pose proof (malloc_okX (HTof (m_vmmaps md) H) A s sp0 argv envp (at_ sp (-48)) n HE Hxm Hn) as HS.
      apply (tshape_const_rz (m_malloc (at_ sp (-48)) (Z_to_bv 64 n) s) S (malloc_postX (HT:=HTof (m_vmmaps md) H) A n s) _ HS).
      eapply (malloc_refines fx md regs m ml_rom s (Z_to_bv 64 n) sp ret (malloc_postX (HT:=HTof (m_vmmaps md) H) A n s) (fun _ _ => S));
        try reflexivity; try eassumption.
      - apply magree_refl.
      - cbn. unfold ALLOC_STACK, topH in *. lia.
      - cbn. lia.
      - unfold RefStep.wtop. cbn. unfold topH, ALLOC_STACK, TASK_SIZE, AsanCeil.alloc_ceiling in *. lia.
      - intros a Ha. exact (proj1 (Hwin a Ha)).
      - intros r s' mm' regs' HP Hag' Hlo' Hhi' Htop' Hr Hsp' Hcs Hfrw Hwin'.
        destruct HP as (A' & Hxm' & HM' & Elo & Ehi & Hres & Hframe & Hlive & Hmap & Hfix & Hgrow & Hnoroom).
        cbn [ms_lo ms_hi ms_mem ms_vm s] in Elo, Ehi, Hres, Hframe, Hlive, Hmap, Hfix, Hgrow, Hnoroom, Htop', Hag'.
        destruct Hfix as (Flim & Ftop & Fisp & Fres).
        assert (Hout : forall a : word, u a < alloc_top (m_vmmaps md) -> mm' a = ms_mem s' a).
        { intros a Ha. apply Hag'. unfold in_win. rewrite Elo. unfold ALLOC_STACK. lia. }
        eapply (HK A' mm' (ms_vm s') regs' r).
        + apply (g_inv_after (m_vmmaps md) H A A' m (ms_mem s') mm' (ms_vm s') (ms_lo s') (ms_hi s') HM' Hxm' Ftop).
          * rewrite Elo. unfold ALLOC_STACK. lia.
          * intros a Ha. apply Hag'. unfold in_win. exact Ha.
          * exact Hrc.
          * exact Hframe.
          * exact (mi_wf _ _ _ HM).
        + exact Hr.
        + exact Hcs.
        + destruct Hres as [(E & Hq) | (Hnz & Hl0 & Hl1 & Hq & Hown & _)].
          * left. split; [exact E | exact Hq].
          * right. split; [exact Hnz|]. split; [exact Hl0|]. split; [exact Hl1|]. split; [exact Hq|].
            intros i Hi. destruct (Hown i Hi) as [Ho | Hm]; [left; left; exact Ho | right; exact Hm].
        + intros a Ho Ho' He Hnw. rewrite Hag'; [apply Hframe; [intros X; exact (Ho (or_introl X)) | intros X; exact (Ho' (or_introl X)) | exact He]|].
          unfold in_win. rewrite Elo, Ehi. lia.
        + intros q k i Hq Hi. pose proof (m_live_hull (HT:=HTof (m_vmmaps md) H) A _ _ q k HM Hq) as (Hk & _ & Hce & _).
          pose proof (round16_ge k). cbn in Hce. pose proof (u64_range q).
          rewrite Hout; [apply (Hlive q k i Hq Hi)|]. rewrite at_uZ by lia. lia.
        + intros a Hm. destruct (Z.lt_ge_cases (u a) (u sp - ALLOC_STACK)) as [Hb | Hb].
          * destruct (Hmap a Hm) as [Hlow | [Ho | Hs']]; [left; exact Hlow | right; left; left; exact Ho | right; right].
            rewrite Hag'; [exact Hs'|]. unfold in_win. rewrite Elo. lia.
          * destruct (Z.lt_ge_cases (u a) (u sp)) as [Hc | Hc].
            -- right; right. apply Hwin'. lia.
            -- destruct (Hmap a Hm) as [Hlow | [Ho | Hs']]; [left; exact Hlow | right; left; left; exact Ho | right; right].
               rewrite Hag'; [exact Hs'|]. unfold in_win. rewrite Ehi. lia.
        + exact Flim. + exact Ftop. + exact Fisp. + exact Fres.
        + exact Hgrow.
        + intros H0. exists H. exact (Hnoroom H0).
    Qed.
    Lemma glue_malloc : forall (fx : FPState) A m md regs (n : Z) (ret sp0 : word) argv envp (S : TSet),
      g_inv A m (m_vmmaps md) -> md_pure md ->
      mallocng_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
      u (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= u (getr regs 2) ->
      u (getr regs 2) <= u sp0 ->
      (forall a : word, u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2) ->
                        m a <> None /\ ~ g_owned A a /\ ~ mallocng_in_ro a /\ ~ mallocng_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          g_inv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, mlive A' q = mlive A q))
            \/ (u res <> 0 /\ mlive A res = None /\ mlive A' res = Some n /\
                (forall q, q <> res -> mlive A' q = mlive A q) /\
                (forall i, 0 <= i < round16 n -> g_owned A (at_ res i) \/ m (at_ res i) = None)) ) ->
          (forall a, ~ g_owned A a -> ~ g_owned A' a -> ~ mallocng_errno_slot a ->
                     ~ (u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, mlive A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> u a < IMG_HI \/ g_owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          realizes ml_segs (mkCfg (mkst regs' ret m' ml_rom) (with_vmmaps vm' md)) S) ->
      realizes ml_segs (mkCfg (mkst regs PC_MALLOC m ml_rom) md) S.
    Proof.
      intros fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK.
      apply (glue_malloc_g fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin).
      intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 _ _. exact (HK A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11).
    Qed.
    Lemma glue_free_g : forall (fx : FPState) A m md regs (p ret sp0 : word) argv envp (S : TSet),
      g_inv A m (m_vmmaps md) -> md_pure md ->
      mallocng_env sp0 argv envp m ->
      getr regs 10 = p -> (p = Z_to_bv 64 0 \/ exists n, mlive A p = Some n) ->
      getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
      u (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= u (getr regs 2) ->
      u (getr regs 2) <= u sp0 ->
      (forall a : word, u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2) ->
                        m a <> None /\ ~ g_owned A a /\ ~ mallocng_in_ro a /\ ~ mallocng_in_rw a) ->
      (forall A' m' vm' regs',
          g_inv A' m' vm' ->
          (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          mlive A' p = None -> (forall q, q <> p -> mlive A' q = mlive A q) ->
          (forall a, ~ g_owned A a -> ~ g_owned A' a -> ~ mallocng_errno_slot a ->
                     ~ (u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, mlive A' q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> g_owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          vm_live_bytes vm' <= vm_live_bytes (m_vmmaps md) ->
          (* [comment removed for export] *)
          sgrow 0 0 0 A A' (m_vmmaps md) vm' ->
          realizes ml_segs (mkCfg (mkst regs' ret m' ml_rom) (with_vmmaps vm' md)) S) ->
      realizes ml_segs (mkCfg (mkst regs PC_FREE m ml_rom) md) S.
    Proof.
      intros fx A m md regs p ret sp0 argv envp S HG Hpure Henv H10 Hp H1 Hret H4 Hal Htop Hsp0 Hwin HK.
      pose proof HG as (H & HM & Hxm & Hrc). pose proof (u64_range (getr regs 2)) as Hsp.
      set (sp := getr regs 2) in *. set (s := MS m (m_vmmaps md) (u sp - ALLOC_STACK) (u sp)).
      pose proof (call_env_of (m_vmmaps md) H A m sp sp0 argv envp ALLOC_STACK HM Henv ltac:(unfold ALLOC_STACK; lia) ltac:(unfold ALLOC_STACK; lia) Hsp0) as HE.
      fold s in HE.
      pose proof (free_okX (HTof (m_vmmaps md) H) A s p sp0 argv envp HE Hxm Hp) as HS.
      apply (tshape_const_rz (m_free p s) S (free_postX (HT:=HTof (m_vmmaps md) H) A p s) _ HS).
      eapply (free_refines fx md regs m ml_rom s p sp ret (free_postX (HT:=HTof (m_vmmaps md) H) A p s) (fun _ _ => S));
        try reflexivity; try eassumption.
      - apply magree_refl.
      - cbn. unfold ALLOC_STACK, topH in *. lia.
      - cbn. lia.
      - unfold RefStep.wtop. cbn. unfold topH, ALLOC_STACK, TASK_SIZE, AsanCeil.alloc_ceiling in *. lia.
      - intros a Ha. exact (proj1 (Hwin a Ha)).
      - intros r s' mm' regs' HP Hag' Hlo' Hhi' Htop' Hsp' Hcs Hfrw Hwin'.
        destruct HP as (A' & Hxm' & HM' & Elo & Ehi & Hl1 & Hl2 & Hframe & Hlive & Hmap & Hfix & Hbud & Hgrow).
        cbn [ms_lo ms_hi ms_mem ms_vm s] in Elo, Ehi, Hl1, Hl2, Hframe, Hlive, Hmap, Hfix, Hbud, Hgrow, Htop', Hag'.
        destruct Hfix as (Flim & Ftop & Fisp & Fres).
        assert (Hout : forall a : word, u a < alloc_top (m_vmmaps md) -> mm' a = ms_mem s' a).
        { intros a Ha. apply Hag'. unfold in_win. rewrite Elo. unfold ALLOC_STACK. lia. }
        eapply (HK A' mm' (ms_vm s') regs').
        + apply (g_inv_after (m_vmmaps md) H A A' m (ms_mem s') mm' (ms_vm s') (ms_lo s') (ms_hi s') HM' Hxm' Ftop).
          * rewrite Elo. unfold ALLOC_STACK. lia.
          * intros a Ha. apply Hag'. unfold in_win. exact Ha.
          * exact Hrc.
          * exact Hframe.
          * exact (mi_wf _ _ _ HM).
        + exact Hcs.
        + exact Hl1.
        + exact Hl2.
        + intros a Ho Ho' He Hnw. rewrite Hag'; [apply Hframe; [intros X; exact (Ho (or_introl X)) | intros X; exact (Ho' (or_introl X)) | exact He]|].
          unfold in_win. rewrite Elo, Ehi. lia.
        + intros q k i Hq Hi.
          assert (HG' : g_inv A' mm' (ms_vm s')).
          { apply (g_inv_after (m_vmmaps md) H A A' m (ms_mem s') mm' (ms_vm s') (ms_lo s') (ms_hi s') HM' Hxm' Ftop);
              [rewrite Elo; unfold ALLOC_STACK; lia | intros a Ha; apply Hag'; unfold in_win; exact Ha | exact Hrc | exact Hframe | exact (mi_wf _ _ _ HM)]. }
          pose proof (g_live_hull A' mm' (ms_vm s') q k HG' Hq) as (Hk & _ & Hce & _). rewrite Ftop in Hce.
          pose proof (round16_ge k). pose proof (u64_range q).
          rewrite Hout; [apply (Hlive q k i Hq Hi)|]. rewrite at_uZ by lia. lia.
        + intros a Hm. destruct (Z.lt_ge_cases (u a) (u sp - ALLOC_STACK)) as [Hb | Hb].
          * destruct (Hmap a Hm) as [Ho | Hs']; [left; left; exact Ho | right]. rewrite Hag'; [exact Hs'|]. unfold in_win. rewrite Elo. lia.
          * destruct (Z.lt_ge_cases (u a) (u sp)) as [Hc | Hc].
            -- right. apply Hwin'. lia.
            -- destruct (Hmap a Hm) as [Ho | Hs']; [left; left; exact Ho | right]. rewrite Hag'; [exact Hs'|]. unfold in_win. rewrite Ehi. lia.
        + exact Flim. + exact Ftop. + exact Fisp. + exact Fres.
        + exact Hbud.
        + exact Hgrow.
    Qed.
    Lemma glue_free : forall (fx : FPState) A m md regs (p ret sp0 : word) argv envp (S : TSet),
      g_inv A m (m_vmmaps md) -> md_pure md ->
      mallocng_env sp0 argv envp m ->
      getr regs 10 = p -> (p = Z_to_bv 64 0 \/ exists n, mlive A p = Some n) ->
      getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
      u (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= u (getr regs 2) ->
      u (getr regs 2) <= u sp0 ->
      (forall a : word, u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2) ->
                        m a <> None /\ ~ g_owned A a /\ ~ mallocng_in_ro a /\ ~ mallocng_in_rw a) ->
      (forall A' m' vm' regs',
          g_inv A' m' vm' ->
          (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          mlive A' p = None -> (forall q, q <> p -> mlive A' q = mlive A q) ->
          (forall a, ~ g_owned A a -> ~ g_owned A' a -> ~ mallocng_errno_slot a ->
                     ~ (u (getr regs 2) - ALLOC_STACK <= u a < u (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, mlive A' q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> g_owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          vm_live_bytes vm' <= vm_live_bytes (m_vmmaps md) ->
          realizes ml_segs (mkCfg (mkst regs' ret m' ml_rom) (with_vmmaps vm' md)) S) ->
      realizes ml_segs (mkCfg (mkst regs PC_FREE m ml_rom) md) S.
    Proof.
      intros fx A m md regs p ret sp0 argv envp S HG Hpure Henv H10 Hp H1 Hret H4 Hal Htop Hsp0 Hwin HK.
      apply (glue_free_g fx A m md regs p ret sp0 argv envp S HG Hpure Henv H10 Hp H1 Hret H4 Hal Htop Hsp0 Hwin).
      intros A' m' vm' regs' X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 _. exact (HK A' m' vm' regs' X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12).
    Qed.
    Lemma glue_calloc_g : forall (fx : FPState) A m md regs (cnt sz : Z) (ret sp0 : word) argv envp (S : TSet),
      g_inv A m (m_vmmaps md) -> md_pure md ->
      mallocng_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
      u (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= u (getr regs 2) ->
      u (getr regs 2) <= u sp0 ->
      (forall a : word, u (getr regs 2) - CALLOC_STACK <= u a < u (getr regs 2) ->
                        m a <> None /\ ~ g_owned A a /\ ~ mallocng_in_ro a /\ ~ mallocng_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          g_inv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, mlive A' q = mlive A q))
            \/ (u res <> 0 /\ mlive A res = None /\ mlive A' res = Some (cnt * sz) /\
                (forall q, q <> res -> mlive A' q = mlive A q) /\
                (forall i, 0 <= i < round16 (cnt * sz) -> g_owned A (at_ res i) \/ m (at_ res i) = None) /\
                (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0))) ) ->
          (forall a, ~ g_owned A a -> ~ g_owned A' a -> ~ mallocng_errno_slot a ->
                     ~ (u (getr regs 2) - CALLOC_STACK <= u a < u (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, mlive A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> u a < IMG_HI \/ g_owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          malloc_growX (cnt * sz) A A' (m_vmmaps md) vm' -> (u res = 0 -> g_noroom (cnt * sz) A (m_vmmaps md)) ->
          realizes ml_segs (mkCfg (mkst regs' ret m' ml_rom) (with_vmmaps vm' md)) S) ->
      realizes ml_segs (mkCfg (mkst regs PC_CALLOC m ml_rom) md) S.
    Proof.
      intros fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK.
      pose proof HG as (H & HM & Hxm & Hrc). pose proof (u64_range (getr regs 2)) as Hsp.
      set (sp := getr regs 2) in *. set (s := MS m (m_vmmaps md) (u sp - CALLOC_STACK) (u sp)).
      pose proof (call_env_of (m_vmmaps md) H A m sp sp0 argv envp CALLOC_STACK HM Henv ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) Hsp0) as HE.
      fold s in HE.
      set (fuel := Z.to_nat (cnt * sz / 4096 + 1)).
      assert (Hfuel : cnt * sz / 4096 < Z.of_nat fuel).
      { subst fuel. pose proof (Z.div_pos (cnt * sz) 4096 ltac:(lia) ltac:(lia)). rewrite Z2Nat.id by lia. lia. }
      pose proof (calloc_okX (HTof (m_vmmaps md) H) A s sp0 argv envp (at_ sp (-32)) fuel cnt sz HE Hxm Hrc Hcnt Hsz Hn Hfuel) as HS.
      apply (tshape_const_rz (m_calloc fuel (at_ sp (-32)) (Z_to_bv 64 cnt) (Z_to_bv 64 sz) s) S (calloc_postX (HT:=HTof (m_vmmaps md) H) A (cnt * sz) s) _ HS).
      eapply (calloc_refines fx md regs m ml_rom s fuel (Z_to_bv 64 cnt) (Z_to_bv 64 sz) sp ret (calloc_postX (HT:=HTof (m_vmmaps md) H) A (cnt * sz) s) (fun _ _ => S));
        try reflexivity; try eassumption.
      - apply magree_refl.
      - cbn. unfold CALLOC_STACK, ALLOC_STACK, topH in *. lia.
      - cbn. lia.
      - unfold RefStep.wtop. cbn. unfold topH, CALLOC_STACK, ALLOC_STACK, TASK_SIZE, AsanCeil.alloc_ceiling in *. lia.
      - intros a Ha. apply (proj1 (Hwin a ltac:(unfold CALLOC_D, CALLOC_STACK in *; lia))).
      - intros r s' mm' regs' HP Hag' Hlo' Hhi' Htop' Hr Hsp' Hcs Hfrw Hwin'.
        destruct HP as (A' & Hxm' & HM' & Elo & Ehi & Hres & Hframe & Hlive & Hmap & Hfix & Hgrow & Hnoroom).
        cbn [ms_lo ms_hi ms_mem ms_vm s] in Elo, Ehi, Hres, Hframe, Hlive, Hmap, Hfix, Hgrow, Hnoroom, Htop', Hag'.
        destruct Hfix as (Flim & Ftop & Fisp & Fres).
        assert (Hout : forall a : word, u a < alloc_top (m_vmmaps md) -> mm' a = ms_mem s' a).
        { intros a Ha. apply Hag'. unfold in_win. rewrite Elo. unfold CALLOC_STACK, ALLOC_STACK. lia. }
        eapply (HK A' mm' (ms_vm s') regs' r).
        + apply (g_inv_after (m_vmmaps md) H A A' m (ms_mem s') mm' (ms_vm s') (ms_lo s') (ms_hi s') HM' Hxm' Ftop).
          * rewrite Elo. unfold CALLOC_STACK, ALLOC_STACK. lia.
          * intros a Ha. apply Hag'. unfold in_win. exact Ha.
          * exact Hrc.
          * exact Hframe.
          * exact (mi_wf _ _ _ HM).
        + exact Hr.
        + exact Hcs.
        + destruct Hres as [(E & Hq) | (Hnz & Hl0 & Hl1 & Hq & Hown & Hz)].
          * left. split; [exact E | exact Hq].
          * right. split; [exact Hnz|]. split; [exact Hl0|]. split; [exact Hl1|]. split; [exact Hq|]. split.
            -- intros i Hi. destruct (Hown i Hi) as [Ho | Hm]; [left; left; exact Ho | right; exact Hm].
            -- intros i Hi. pose proof (m_live_hull (HT:=HTof (m_vmmaps md) H) A' _ _ r (cnt * sz) HM' Hl1) as (Hk & _ & Hce & _).
               pose proof (round16_ge (cnt * sz)). cbn in Hce. pose proof (u64_range r).
               rewrite Hout; [apply (Hz i Hi)|]. rewrite at_uZ by lia. lia.
        + intros a Ho Ho' He Hnw. rewrite Hag'; [apply Hframe; [intros X; exact (Ho (or_introl X)) | intros X; exact (Ho' (or_introl X)) | exact He]|].
          unfold in_win. rewrite Elo, Ehi. unfold CALLOC_D, CALLOC_STACK in *. lia.
        + intros q k i Hq Hi. pose proof (m_live_hull (HT:=HTof (m_vmmaps md) H) A _ _ q k HM Hq) as (Hk & _ & Hce & _).
          pose proof (round16_ge k). cbn in Hce. pose proof (u64_range q).
          rewrite Hout; [apply (Hlive q k i Hq Hi)|]. rewrite at_uZ by lia. lia.
        + intros a Hm. destruct (Z.lt_ge_cases (u a) (u sp - CALLOC_STACK)) as [Hb | Hb].
          * destruct (Hmap a Hm) as [Hlow | [Ho | Hs']]; [left; exact Hlow | right; left; left; exact Ho | right; right].
            rewrite Hag'; [exact Hs'|]. unfold in_win. rewrite Elo. lia.
          * destruct (Z.lt_ge_cases (u a) (u sp)) as [Hc | Hc].
            -- right; right. apply Hwin'. unfold CALLOC_D, CALLOC_STACK in *. lia.
            -- destruct (Hmap a Hm) as [Hlow | [Ho | Hs']]; [left; exact Hlow | right; left; left; exact Ho | right; right].
               rewrite Hag'; [exact Hs'|]. unfold in_win. rewrite Ehi. lia.
        + exact Flim. + exact Ftop. + exact Fisp. + exact Fres.
        + exact Hgrow.
        + intros H0. exists H. exact (Hnoroom H0).
    Qed.
    Lemma glue_calloc : forall (fx : FPState) A m md regs (cnt sz : Z) (ret sp0 : word) argv envp (S : TSet),
      g_inv A m (m_vmmaps md) -> md_pure md ->
      mallocng_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
      u (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= u (getr regs 2) ->
      u (getr regs 2) <= u sp0 ->
      (forall a : word, u (getr regs 2) - CALLOC_STACK <= u a < u (getr regs 2) ->
                        m a <> None /\ ~ g_owned A a /\ ~ mallocng_in_ro a /\ ~ mallocng_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          g_inv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, mlive A' q = mlive A q))
            \/ (u res <> 0 /\ mlive A res = None /\ mlive A' res = Some (cnt * sz) /\
                (forall q, q <> res -> mlive A' q = mlive A q) /\
                (forall i, 0 <= i < round16 (cnt * sz) -> g_owned A (at_ res i) \/ m (at_ res i) = None) /\
                (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0))) ) ->
          (forall a, ~ g_owned A a -> ~ g_owned A' a -> ~ mallocng_errno_slot a ->
                     ~ (u (getr regs 2) - CALLOC_STACK <= u a < u (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, mlive A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> u a < IMG_HI \/ g_owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          realizes ml_segs (mkCfg (mkst regs' ret m' ml_rom) (with_vmmaps vm' md)) S) ->
      realizes ml_segs (mkCfg (mkst regs PC_CALLOC m ml_rom) md) S.
    Proof.
      intros fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK.
      apply (glue_calloc_g fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin).
      intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 _ _. exact (HK A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11).
    Qed.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition mallocng_base : AllocBase := {|
      AS := astate;
      ainv := g_inv;
      live := fun A p => mlive A p;
      owned := g_owned;
      ai_globals_owned := g_globals_owned;
      ai_live_hull := g_live_hull;
      ai_live_disjoint := g_live_disjoint;
      ai_live_not_globals := g_live_not_globals;
      ai_owned_where := g_owned_where;
      ai_frame := g_frame;
      A0 := MallocInv_defs.A0;
      ai_init_live := fun p => eq_refl;
      ai_init_owned := g_init_owned;
      ai_init := g_init;
      ai_malloc := glue_malloc;
      ai_free := glue_free |}.

    Local Existing Instance mallocng_calloc_layout.
    Definition mallocng_calloc : AllocCalloc := {|
      aic_base := mallocng_base;
      ai_calloc := glue_calloc |}.
  End Ops.

End Glue.
