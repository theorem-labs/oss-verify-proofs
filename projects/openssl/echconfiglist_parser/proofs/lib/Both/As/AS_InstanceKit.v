(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the kit's library is a function of the heap-ceiling record, whose hvdso now depends on the run; kit_aux, the auxv claim that ties AT_SYSINFO_EHDR to hvdso, is AsMainIfaceAuxv.auxv_ok_main at the run's mmap base, with the vector's first pair read from the main-entry states and AT_SYSINFO_EHDR from cs_ok's co_ehdr at the run's kernel build and mmap base); the kit is the run instance's: KH k is AsSRRun.KHr at the launch's vDSO pair (its tail Run.vdso_segments (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k) and its two windows Ref.VdsoLaunch.vd_lo / vd_mid / vd_top, whose launch facts Both/As/VdsoLaunch.v proves), its interface facts are time() at that instance (F_timeI.atime_inst_run) and posix_memalign (AsSRRun.khr_memalign_stmt), its driver laws are the run's (AsSRRun.khr_driver_laws) and its tail statements Both/As/AsTailsRun.v's lifts; the instance state keeps the marker byte of the vDSO text's shadow visible (AsSRRun.pw_mark) and its visible memory KM is the main entry's view with that byte opened; kit_vcm2 is the launch's vDSO pair at the main entry, clean, reserved and met by no map, which the instance now records; kit_heap is the entry's heap relation framed over the opened marker byte, which is no byte the relation reads and no allocator footprint byte, and over the visible set the marker joins; kit_rfs is the entry's file frames framed over that byte, which no frame reads. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Vdso Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel LazyRestrict LazyLedger LazySR Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsDrvDefs AsMainPre AsInstance AsAuxv
  AllocWf AllocBudget AllocRep AllocRepX AsDepotInv FakeStackRep AsSR
  AS_InstWF AS_InstMainDefs AS_InstDefs AS_InstLaws1 AS_InstLaws2 AS_InstLaws3 AS_InstTR AS_InstHeap AS_InstFree
  AS_InstMainRep AS_InstMainK AS_InstMainVis AS_InstMainHeap ECH_Iface AsInstanceMain   (* [comment removed for export] *)
  AsIfaceX AS_InstLaws1x AS_InstRealloc   (* [comment removed for export] *)
  F_time F_timeI AsIfaceMemalign AS_InstMemalign AInstFacts   (* [comment removed for export] *)
  AsSRRun AsTailsRun AsMainTop AsMainTails VdsoLaunch.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require VdsoLaunch.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsStartupHSF. From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceDepot AsMainIfaceAlloc AsMainIfaceFS.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainIfaceAuxv.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require EAsChainRun.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AL0 : Z := 2 ^ 39 - 2 ^ 36 - 2 ^ 29.
(* [comment removed for export] *)
Definition ALIB_COST_MAX : Z := 2 ^ 36.

Section KIT.
  Variable L : HeapCeil -> alib.
  Variable LD : list (Z * list Z).
  Hypothesis TRLEN : forall (HC : HeapCeil), (length (trlist_of (all_demands (L HC) LD)) <= TRCAP)%nat.
  Hypothesis DOK : forall (HC : HeapCeil), demands_okb (all_demands (L HC) LD) = true.
  Hypothesis LT : forall (HC : HeapCeil) (H : asr), (forall pc0 t, In (pc0, t) LD -> trace_ok (as_TR H) pc0 t) -> al_tr_ok (L HC) H.
  Hypothesis LCOST : forall (HC : HeapCeil) (H : asr), as_Cm H = ICm -> as_Cf H = ICf -> al_cost (L HC) H (2 ^ 26) <= ALIB_COST_MAX.
  Hypothesis LOK : forall HC : HeapCeil, alib_ok (L HC).
  (* The library reads the instance only through the fields the run instance shares with the
     binary instance ([AsSRRun.KHr]'s [as_Cm], [as_Cf] and [as_TR] are [KHp p]'s), so its cost
     and its trace check are the same at both; for the ECH library (Both/As/ECH_ALib.v [ECHL])
     they hold by [eq_refl] and [fun T => T].  [Both/As/AsTailsRun.v] takes them. *)
  Hypothesis LCOST_R : forall (HC : HeapCeil) (p : iparams) (tail : list Segment) (vlo vb vhi N : Z),
    al_cost (L HC) (AsSRRun.KHr p tail vlo vb vhi) N = al_cost (L HC) (KHp p) N.
  Hypothesis LTR_R : forall (HC : HeapCeil) (p : iparams) (tail : list Segment) (vlo vb vhi : Z),
    al_tr_ok (L HC) (AsSRRun.KHr p tail vlo vb vhi) -> al_tr_ok (L HC) (KHp p).
  Hypothesis K_libx0 : forall (HC : HeapCeil) iv, In iv (al_LIBX0 (L HC)) -> img_check (fst iv) (snd iv) = true.

  Definition kip (k : mctx) : iparams := {| ip_fsb := ps_b16 (KX k); ip_D := ps_b12 (KX k); ip_TR := trlist_of (all_demands (L (KCEIL k)) LD) |}.
  (* the run's tail and the launch's vDSO pair: the vvar entry [Kvlo, Kvb) and the text entry
     [Kvb, Kvhi) ([Run.vdso_segments], [Ref/VdsoLaunch.v]) *)
  Definition Ktail (k : mctx) : list Segment := vdso_segments (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k).
  Definition Kvlo (k : mctx) : Z := Ref.VdsoLaunch.vd_lo (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k).
  Definition Kvb (k : mctx) : Z := Ref.VdsoLaunch.vd_mid (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k).
  Definition Kvhi (k : mctx) : Z := Ref.VdsoLaunch.vd_top (k_sp0 k) (k_mbase k).
  Definition KH (k : mctx) : asr := @AsSRRun.KHr (KCEIL k) (kip k) (Ktail k) (Kvlo k) (Kvb k) (Kvhi k).
  Definition KB (k : mctx) : Z := bv_unsigned (k_sp0 k).
  (* the marker: the shadow byte of the vDSO text's first bytes, on the page of the window
     time()'s first call opens ([AsSRRun.pw_mark], [pw_win]) *)
  Definition KQ (k : mctx) : Z := sh (Kvb k).
  Definition Kcert (k : mctx) : ast := cert_s0 (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k) [] false AL0.
  (* the instance state at main entry: the entry's certificate state with the marker in its
     visible set, which [AsSRRun.pw_ok] asks for *)
  Definition Ks0 (k : mctx) : ast :=
    mkAst (a_st (Kcert k)) (a_thr (Kcert k)) (a_ctx (Kcert k)) (a_fsb (Kcert k))
          (a_L (Kcert k)) (AsSRRun.pw_mark (Kvb k) :: a_S (Kcert k)) (a_Zr (Kcert k))
          (a_AL (Kcert k)) (a_top (Kcert k)) (a_bot (Kcert k)).
  Definition Kd0 (k : mctx) : depot := depot0 (bv_unsigned (k_sp0 k)) (KX k).
  Definition KS0 (k : mctx) : as_St (KH k) := IST (Ks0 k) (Kd0 k).
  (* the visible memory: the entry's view with the marker byte opened *)
  Definition KM (k : mctx) : word -> option byte :=
    fun a => if zin_rangeb (bv_unsigned a) (AsSRRun.pw_mark (Kvb k)) then Some (Z_to_bv 8 0) else KVM k a.

  Lemma kip_TRLEN : forall k, (length (ip_TR (kip k)) <= 4000)%nat.
  Proof. intros k. cbn [kip ip_TR]. exact (TRLEN (KCEIL k)). Qed.

  (* [comment removed for export] *)
  Lemma kit_rt_p : forall k, @asan_rt_hyps (KCEIL k) (@KHp (KCEIL k) (kip k)).
  Proof.
    intros k.
    pose proof (@inst_SR_laws (KCEIL k) (kip k)) as Lsr. pose proof (@inst_MPRES_laws (KCEIL k) (kip k)) as Lmp.
    pose proof (@inst_RHEAP_block_range (KCEIL k) (kip k)) as Lbr. pose proof (@inst_RHEAP_fsb (KCEIL k) (kip k)) as Lfsb.
    pose proof (@inst_rauxv_frame (KCEIL k) (kip k)) as Laux. pose proof (@inst_chain_laws (KCEIL k) (kip k)) as Lch.
    pose proof (@inst_RHEAP_frame (KCEIL k) (kip k)) as Lrf. pose proof (@inst_malloc_stmt (KCEIL k) (kip k) (kip_TRLEN k)) as Lma.
    pose proof (@inst_free_stmt (KCEIL k) (kip k) (kip_TRLEN k)) as Lfr. pose proof (@inst_free_null_stmt (KCEIL k) (kip k)) as Lfn.
    unfold asan_rt_hyps.
    split; [exact Lsr|]. split; [exact (inst_AKREL_laws (kip k))|]. split; [exact Lmp|].
    split; [exact (inst_alloc_ok_of_live (kip k))|]. split; [exact (inst_cost_laws (kip k))|].
    split; [exact Lrf|]. split; [exact Lbr|]. split; [exact (inst_RHEAP_blocks_disjoint (kip k))|]. split; [exact (inst_RHEAP_blocks_nodup (kip k))|].
    split; [exact (inst_RHEAP_shvis (kip k))|]. split; [exact Lfsb|]. split; [exact (inst_RHEAP_thr (kip k))|].
    split; [exact Laux|]. split; [exact (inst_lb_remove_laws (kip k))|].
    split; [exact (inst_RFS_frame (kip k))|]. split; [exact (inst_RFS_ext (kip k))|]. split; [exact (inst_RFS_range (kip k))|].
    split; [exact (inst_RFS_disjoint (kip k))|]. split; [exact (inst_RFS_nodup (kip k))|]. split; [exact (inst_RFS_shvis (kip k))|].
    split; [exact (inst_frame_release (kip k))|].
    split; [exact Lch|].
    split; [exact Lma|]. split; [exact Lfr|]. split; [exact Lfn|].
    split; [exact (inst_stack_malloc_1 (kip k))|]. split; [exact (inst_stack_malloc_4 (kip k))|]. split; [exact inst_set_shadow_f5|].
    split; [exact inst_asan_memcpy|]. split; [exact inst_asan_memset|]. split; [exact inst_asan_memmove|].
    split; [exact inst_memcpy_icpt|].
    split; [exact inst_strlen_icpt|]. exact inst_strncmp_icpt.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_rt_xp : forall k, @asan_rt_hyps_x (KCEIL k) (@KHp (KCEIL k) (kip k)).
  Proof.
    intros k. unfold asan_rt_hyps_x. split; [exact (kit_rt_p k)|].
    split; [exact (@inst_realloc_stmt (KCEIL k) (kip k) (kip_TRLEN k))|].
    split; [exact (@inst_stack_malloc_0 (KCEIL k) (kip k))|]. split; [exact (@inst_stack_malloc_2 (KCEIL k) (kip k))|].
    split; [exact (@inst_stack_malloc_6 (KCEIL k) (kip k))|]. split; [exact (@inst_stack_free_6 (KCEIL k) (kip k))|].
    split; [exact inst_set_shadow_00|]. split; [exact inst_set_shadow_f8|].
    split; [exact (@inst_slack_law (KCEIL k) (kip k))|].   (* [comment removed for export] *)
    split; [exact (@inst_rheap_perm (KCEIL k) (kip k))|].   (* [comment removed for export] *)
    exact (@inst_canary_law (KCEIL k) (kip k)).   (* [comment removed for export] *)
  Qed.

  (** * The launch's vDSO pair

      [Both/As/VdsoLaunch.v] proves these of [Run.vdso_segments (in_kernel inp) sp mbase] from
      the launch, at the entry's stack pointer and the run's mmap base, which [mctx] carries
      ([k_Vsp], [k_Vmb]).  Each is applied by [eapply], because a fact that reads neither
      bound takes neither. *)

  Lemma ktail_nx : forall k s, In s (Ktail k) -> seg_executable s = false.
  Proof. intros k s Hs. exact (RomStable.vdso_segments_nx (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k) s Hs). Qed.
  Lemma ktail_nw : forall k s, In s (Ktail k) -> seg_writable s = false.
  Proof. intros k s Hs. exact (RomStable.vdso_segments_nw (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k) s Hs). Qed.

  Lemma kv_lo : forall k, AIMG_TOP <= Kvlo k /\ page_size <= Kvlo k /\ AHI_LO <= Kvlo k.
  Proof. intros k. unfold Kvlo. eapply av_lo_bounds; first [exact (k_Vsp k) | exact (k_Vmb k)]. Qed.
  Lemma kv_ord : forall k, Kvlo k <= Kvb k.
  Proof. intros k. exact (proj1 (av_order (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k) (k_Vsp k) (k_Vmb k))). Qed.
  Lemma kv_hi64 : forall k, Kvhi k <= 2 ^ 64.
  Proof. intros k. exact (proj2 (proj2 (av_order (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k) (k_Vsp k) (k_Vmb k)))). Qed.
  Lemma kv_mid_top : forall k, Kvb k + 8192 = Kvhi k.
  Proof. intros k. unfold Kvb, Kvhi. eapply Ref.VdsoLaunch.mid_top; first [exact (k_Vsp k) | exact (k_Vmb k)]. Qed.
  Lemma kv_span : forall k, Kvb k + RVDSO_SPAN <= Kvhi k.
  Proof. intros k. rewrite RVDSO_SPAN_val. pose proof (kv_mid_top k). lia. Qed.
  Lemma kv_tw : forall k (x : Z) s, find_segment (Ktail k) x 1 = Some s -> Kvlo k <= x < Kvhi k.
  Proof. intros k x s Hx. unfold Kvlo, Kvhi. eapply av_tail_in_window; first [exact (k_Vsp k) | exact (k_Vmb k) | exact Hx]. Qed.
  Lemma kv_ne : forall k s, In s (Ktail k) -> (0 < seg_size s)%N.
  Proof. intros k s Hs. eapply av_tail_nonempty; first [exact (k_Vsp k) | exact (k_Vmb k) | exact Hs]. Qed.
  Lemma kv_rom : forall k, rvdso_rom (asegs ++ Ktail k) (Kvb k).
  Proof. intros k. unfold Kvb, Ktail. eapply av_rom_pair; first [exact (k_Vsp k) | exact (k_Vmb k)]. Qed.
  Lemma kv_mid_al : forall k, Kvb k mod 4096 = 0.
  Proof. intros k. unfold Kvb. eapply av_mid_al; first [exact (k_Vsp k) | exact (k_Vmb k)]. Qed.
  (* [hvdso] of [KCEIL k] is the launch's AT_SYSINFO_EHDR plus 1460 ([main_ceil_vdso]), which is
     the pair's text base plus 1460 ([Ref/VdsoLaunch.vdso_text_base_pair]) *)
  Lemma kv_hvdso : forall k, Kvb k + 1460 = @hvdso (KCEIL k).
  Proof. intros k. unfold Kvb. eapply av_hvdso; first [exact (k_Vsp k) | exact (k_Vmb k) | reflexivity]. Qed.
  Lemma kv_top_aceil : forall k, Kvhi k <= @aceil (KCEIL k).
  Proof. intros k. unfold Kvhi. eapply av_top_aceil; first [exact (k_Vsp k) | exact (k_Vmb k) | reflexivity]. Qed.
  Lemma kv_ent : forall k, vdso_entry_fn (asegs ++ Ktail k) (Z_to_bv 64 (@hvdso (KCEIL k))) = Some VdsoClockGettime.
  Proof.
    intros k. rewrite <- (kv_hvdso k). unfold Kvb, Ktail.
    eapply av_ent_text; first [exact (k_Vsp k) | exact (k_Vmb k)].
  Qed.
  Lemma kv_unm : forall k ms, ms_pc ms = Z_to_bv 64 (@hvdso (KCEIL k)) ->
    RiscvSemantics.step (asegs ++ Ktail k) ms = MachineUnmodeled.
  Proof.
    intros k ms Hpc. rewrite <- (kv_hvdso k) in Hpc. unfold Kvb in Hpc. unfold Ktail.
    eapply av_unm_text; first [exact (k_Vsp k) | exact (k_Vmb k) | exact Hpc].
  Qed.
  (* [KHr]'s bound on the marker and the window: the text base is 8-aligned, in the high range,
     and its first 832 bytes are below the ceiling and inside the text entry *)
  Lemma kv_vb : forall k, Kvb k mod 8 = 0 /\ AHI_LO <= Kvb k /\ Kvb k + 832 <= @aceil (KCEIL k) /\ Kvb k + 832 <= Kvhi k.
  Proof.
    intros k. pose proof (kv_mid_al k) as M4. pose proof (kv_lo k) as (_ & _ & HL).
    pose proof (kv_ord k) as HO. pose proof (kv_mid_top k) as MT. pose proof (kv_top_aceil k) as TA.
    split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia.
  Qed.

  (** * The run instance's hypotheses *)

  Lemma kit_rt_x : forall k, @asan_rt_hyps_x (KCEIL k) (KH k).
  Proof.
    intros k. unfold KH.
    eapply AsSRRun.khr_rt_hyps_x;
      first [ exact (kit_rt_xp k) | exact (ktail_nx k) | exact (ktail_nw k)
            | exact (proj1 (kv_lo k)) | exact (kv_ord k) | exact (kv_vb k) | exact (kip_TRLEN k) ].
  Qed.

  (* time() at the run instance (Both/As/F_timeI.v) and posix_memalign (Both/As/AsSRRun.v) *)
  Lemma kit_ifacts : forall k, @ainst_facts (KCEIL k) (KH k).
  Proof.
    intros k. split; unfold KH.
    - eapply F_timeI.atime_inst_run;
        first [ exact (ktail_nx k) | exact (ktail_nw k) | exact (proj1 (kv_lo k)) | exact (kv_tw k)
              | exact (kv_ne k) | exact (kv_hi64 k) | exact (kv_rom k) | exact (kv_hvdso k)
              | exact (kv_ent k) | exact (kv_unm k) | exact (proj2 (proj2 (kv_lo k)))
              | exact (kv_ord k) | exact (kv_span k) | exact (kv_top_aceil k) ].
    - eapply AsSRRun.khr_memalign_stmt;
        first [ exact (ktail_nx k) | exact (ktail_nw k) | exact (proj1 (kv_lo k)) | exact (kv_ord k)
              | exact (kv_vb k) | exact (kip_TRLEN k) ].
  Qed.

  Lemma kit_dl : forall k, asan_driver_laws_run (Ktail k) (Kvlo k) (Kvb k) (Kvhi k) (KH k).
  Proof.
    intros k. unfold KH.
    eapply AsSRRun.khr_driver_laws;
      first [ exact (ktail_nx k) | exact (ktail_nw k) | exact (proj1 (kv_lo k)) | exact (kv_ord k)
            | exact (kv_vb k) | exact (kip_TRLEN k) ].
  Qed.

  (* the live bounds are [KHp]'s, by conversion *)
  Lemma kit_live : forall k, ADRV_LIVE <= as_LIVE_MAX (KH k) /\ ADRV_CNT <= as_LIVE_CNT_MAX (KH k).
  Proof. intros k. exact (@inst_live (KCEIL k) (kip k)). Qed.

  (* the three tail statements: [AsMainTails]' at the binary instance, lifted to the run
     instance by [Both/As/AsTailsRun.v] *)
  Lemma kit_tails : forall k, @atail_usage_stmt (KCEIL k) (KH k) (L (KCEIL k))
                           /\ @atail_open_stmt (KCEIL k) (KH k) (L (KCEIL k))
                           /\ @atail_rderr_stmt (KCEIL k) (KH k) (L (KCEIL k)).
  Proof.
    intros k. unfold KH. split; [| split].
    - eapply AsTailsRun.atail_usage_run;
        first [ exact (LCOST_R (KCEIL k) (kip k) (Ktail k) (Kvlo k) (Kvb k) (Kvhi k))
              | exact (LTR_R (KCEIL k) (kip k) (Ktail k) (Kvlo k) (Kvb k) (Kvhi k))
              | exact (AsMainTails.atail_usage (@KHp (KCEIL k) (kip k)) (L (KCEIL k)) (@inst_driver_laws (KCEIL k) (kip k))) ].
    - eapply AsTailsRun.atail_open_run;
        first [ exact (LCOST_R (KCEIL k) (kip k) (Ktail k) (Kvlo k) (Kvb k) (Kvhi k))
              | exact (LTR_R (KCEIL k) (kip k) (Ktail k) (Kvlo k) (Kvb k) (Kvhi k))
              | exact (AsMainTails.atail_open (@KHp (KCEIL k) (kip k)) (L (KCEIL k)) (@inst_driver_laws (KCEIL k) (kip k))) ].
    - eapply AsTailsRun.atail_rderr_run;
        first [ exact (LCOST_R (KCEIL k) (kip k) (Ktail k) (Kvlo k) (Kvb k) (Kvhi k))
              | exact (LTR_R (KCEIL k) (kip k) (Ktail k) (Kvlo k) (Kvb k) (Kvhi k))
              | exact (AsMainTails.atail_rderr (@KHp (KCEIL k) (kip k)) (L (KCEIL k)) (@inst_driver_laws (KCEIL k) (kip k))) ].
  Qed.

  (** * The state at main entry *)

  (* the marker is one byte, so it adds at most one page to the visible set *)
  Lemma kit_mark_pages : forall k, win_npagesZ (AsSRRun.pw_mark (Kvb k)) <= 2.
  Proof.
    intros k. pose proof (cl_bounds (AsSRRun.pw_mark (Kvb k))) as (_ & _ & _ & _ & W & _).
    cbn [AsSRRun.pw_mark snd] in W. rewrite (AsInstanceMain.mk_lit 1 ltac:(lia)) in W.
    unfold page_size in W. change (1 / 4096) with 0 in W. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_budget : forall k, ABUDGET (Ks0 k) (k_model k).
  Proof.
    intros k.
    pose proof (AsMainIfaceAlloc.ak_budget (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as (B1 & B2 & B3 & B4).
    pose proof (kit_mark_pages k) as MP.
    unfold ABUDGET, aPhi, Ks0, Kcert, KX. cbn [a_AL a_S a_st cert_s0]. unfold cert_st0.
    rewrite pages_total_cons. rewrite AllocBudget.pusage_init. rewrite B2. unfold KX in B3. rewrite B4 in B3.
    unfold target_alloc_limit, page_size, AllocBudget.B_PRIM, AL0 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kit_IK : forall k, @IK (KCEIL k) (kip k) (KS0 k) (k_model k).
  Proof.
    intros k. unfold IK. cbn [i_s i_d KS0].
    split; [|split].
    - (* [comment removed for export] *) split; [split; [|split]|].
      + exact (AS_InstMainK.amaps_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0).
      + (* the marker only grows the visible set, and [ashadow_visible] is monotone in it *)
        destruct (AS_InstMainK.ashadow_main (k_sp0 k) (k_brk0 k) (k_h k) (k_E k) [] false AL0) as [AS1 AS2].
        split.
        * intros c x Hc Hx. cbn [Ks0 Kcert a_S]. rewrite in_rangesb_cons. apply orb_true_iff. right.
          exact (AS1 c x Hc Hx).
        * intros sc x Hsc Hx. cbn [Ks0 Kcert a_S]. rewrite in_rangesb_cons. apply orb_true_iff. right.
          exact (AS2 sc x Hsc Hx).
      + exact (kit_budget k).
      + exact (AS_InstMainK.akernel_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0).
    - (* [comment removed for export] *)
      intros x Hx. cbn [Kd0 depot0 d_nb d_sb] in Hx.
      destruct Hx as [Hx|Hx].
      + apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b21 (KX k)) 0x100000); [cbn; tauto | lia].
      + apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b22 (KX k)) 0x800000); [cbn; tauto | lia].
    - (* [comment removed for export] *)
      intros x Hx. cbn [kip ip_D] in Hx. unfold kPageSize in Hx.
      apply (AsMainIfaceAlloc.ak_maps_in (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
               (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (ps_b12 (KX k)) 0x1000); [cbn; tauto | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma kit_al : forall k, AMAIN_COST (KH k) (L (KCEIL k)) <= as_AL (KH k) (KS0 k).
  Proof.
    intros k. pose proof (LCOST (KCEIL k) (KH k) eq_refl eq_refl) as LC.
    unfold AMAIN_COST, fuzz_cost. unfold KH in LC |- *.
    cbn [as_Cm as_Cf as_AL AsSRRun.KHr KHp KS0 i_s a_AL Ks0 Kcert cert_s0] in LC |- *.
    unfold ICm, ICf, ALIB_COST_MAX, AL0 in LC |- *. cbn [Z.leb] . change (2 ^ 26 <=? 64512) with false. cbn [negb].
    lia.
  Qed.

  Lemma kit_tr : forall k, adrv_traces (KH k) (L (KCEIL k)).
  Proof.
    intros k. apply (inst_K_tr (KH k) (L (KCEIL k)) LD eq_refl (DOK (KCEIL k))). apply (LT (KCEIL k) (KH k)). exact (inst_lib_demand (KH k) (L (KCEIL k)) LD eq_refl (DOK (KCEIL k))).
  Qed.

  (* the kit's view differs from the entry's at the marker byte only, which lies in the high
     shadow [sh AHI_LO, sh aceil) *)
  Lemma kit_mem : forall k, @AsInstanceMain.mk_ok (KCEIL k) (KVM k) (KM k) (KQ k).
  Proof.
    intros k. pose proof (kv_vb k) as (V8 & VL & VA & _).
    assert (QL : 0x2008fff7000 <= KQ k).
    { unfold KQ, sh. rewrite ASHADOW_BASE_val.
      assert (D : AHI_LO / 8 <= Kvb k / 8) by (apply Z.div_le_mono; lia).
      change (AHI_LO / 8) with 0x2000ffff000 in D. lia. }
    assert (QH : KQ k + 1 <= sh (@aceil (KCEIL k))).
    { unfold KQ, sh. Z.div_mod_to_equations. lia. }
    assert (QB : 0 <= KQ k < 2 ^ 64).
    { pose proof (@aceil_range (KCEIL k)) as AR. pose proof QH as QH'. unfold sh in QH'. rewrite ASHADOW_BASE_val in QH'.
      Z.div_mod_to_equations. lia. }
    pose proof (AsInstanceMain.mk_lit (KQ k) QB) as QE.
    split; [exact QL|]. split; [exact QH|].
    unfold KM, AsSRRun.pw_mark. split.
    - intros a Ha. cbv beta. cbn [outside] in Ha. destruct Ha as [Hout _].
      destruct (zin_rangeb (bv_unsigned a) (Z_to_bv 64 (sh (Kvb k)), Z_to_bv 64 1)) eqn:E; [exfalso | reflexivity].
      apply Hout. unfold zin_rangeb in E. cbn [fst snd] in E.
      apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      red. unfold wa. unfold KQ in *. rewrite QE in E1, E2 |- *. rewrite (AsInstanceMain.mk_lit 1 ltac:(lia)) in E2. lia.
    - intros a Ha. cbv beta. destruct (zin_rangeb (bv_unsigned a) (Z_to_bv 64 (sh (Kvb k)), Z_to_bv 64 1)); [discriminate | exact Ha].
  Qed.

  (* the file frames: the entry's ([AS_InstMainK.rfs_main]), which no byte of the marker meets *)
  Lemma kit_rfs : forall k, as_RFS (KH k) [] (KM k).
  Proof.
    intros k. unfold KH. cbn [as_RFS AsSRRun.KHr].
    pose proof (AS_InstMainK.rfs_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl) as R0.
    pose proof (RFSI_geom _ _ _ R0) as (G1 & G2 & G3 & G4).
    pose proof (AsInstanceMain.mk_q _ _ _ (kit_mem k)) as (_ & Q1 & Q2).
    change (@RFSI (KCEIL k) (ps_b16 (KX k)) [] (KM k)).
    eapply RFSI_frame_win; [exact R0 | exact (AsInstanceMain.mk_munch _ _ _ (kit_mem k)) | exact (AsInstanceMain.mk_wmono _ _ _ (kit_mem k)) |].
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold KX in *.
    unfold aapp, aapp_lo, aapp_hi in G4.
    unfold AsIface.AFS_HDR, AsIface.AFS_SIZE, AllocRep.AFS_SIZE, AsIface.ATP, AllocRep.ATP, ASegs.AIMG_TOP, AsMainSyms.AIMG_TOP,
      AsShadow.ALOWSH_LO, AsMainSyms.ALOWSH_LO, AsShadow.AHI_LO, AsMainSyms.AHI_LO in *.
    lia.
  Qed.

  (** * The launch's vDSO pair at the main entry *)

  (* each of the pair's two entries clean, reserved and met by no map, the pins well formed
     ([AsDriverLaws.vcm2]): what the start-up carries from the launch to the main entry
     ([EAsChainRun.vcm_run], [EAsChainRun.P_mainK], [k_vcm]) *)
  Lemma kit_vcm2 : forall k, vcm2 (Kvlo k) (Kvb k) (Kvhi k) (Kcfg k).
  Proof. intros k. exact (k_vcm k). Qed.

  (** * The marker in the main entry's views and relations

      The lemmas below place the marker byte against the entry's lazy view, kernel relation and
      heap relation, and give the kit's state, view, kernel relation, heap relation and auxv
      claim at the opened marker. *)

  (* the main-entry lemmas of [AsMainIfaceAlloc]'s Section AT_MAIN and [AsMainLazy]'s Section LZ at
     [k]: [eapply] takes the Section's hypotheses as goals, which [k]'s fields close *)
  Ltac kargs k := first [ exact (k_Vsp k) | exact (k_Vbrk k) | exact (k_Vav k) | exact (k_Vev k)
                        | exact (k_Vfit k) | exact (k_Hh k) | exact (k_HC k) ].

  (* (1).  The marker's shadow bytes [sh vb, sh vb + 104) are in no range of [PM_S] and in the
     high shadow, which [PM_ZR] and [PM_LAZY] cover.  A shadow byte of a range of [PM_S] covers a
     byte of the range, so the range would meet the pair's text entry [vb, vhi): the mapped ranges
     keep off it ([kit_vcm2]: [MapsOff.maps_off]), the image and the stack window lie below and
     above the pair ([kv_lo], [AsMainIfaceAlloc.al_ceil] with [kv_top_aceil]), the 8 MiB band is
     kernel-placed outside the high shadow ([AsMainLazy.KBAND_in]), and a ghost holds no reserved
     byte ([APS.co_gres], over the ghosts [AsMainLazy.VISZ0_eq] names) while the window lies in a
     reserved entry of the pair ([kit_vcm2]: [MmVdso.mm_vinv]). *)
  Lemma kit_mark_off : forall k (y : word), sh (Kvb k) <= bv_unsigned y < sh (Kvb k) + 104 ->
    in_rangesb y (a_S (Kcert k)) = false /\ in_rangesb y (a_Zr (Kcert k)) = true /\ in_rangesb y (a_L (Kcert k)) = true.
  Proof.
    intros k y Hy.
    pose proof (kv_vb k) as (V8 & VL & VA & VH). pose proof VL as VL0. unfold AHI_LO in VL0.
    pose proof (kv_lo k) as (VLI & _ & _). pose proof (kv_ord k) as VO.
    pose proof (kv_top_aceil k) as VT. pose proof (kv_hi64 k) as V64.
    assert (Hh' : @hceil (KCEIL k) = bv_unsigned (k_sp0 k) - 8388608) by reflexivity.
    assert (AC : @aceil (KCEIL k) = AsMainSyms.page_down (bv_unsigned (k_sp0 k)) - 8388608).
    { eapply AsMainIfaceAlloc.al_ceil with (HCEIL := KCEIL k); first [kargs k | exact Hh']. }
    assert (SC : sh (@aceil (KCEIL k)) + 4096 <= 0x10007fff8000 /\ sh AHI_LO = 0x2008fff7000).
    { eapply AsMainIfaceAlloc.ak_sh_ceil with (HCEIL := KCEIL k); first [kargs k | exact Hh']. }
    assert (YB : sh AHI_LO <= bv_unsigned y < sh (@aceil (KCEIL k))).
    { unfold sh in *. split.
      - assert (AHI_LO / 8 <= Kvb k / 8) by (apply Z.div_le_mono; lia). lia.
      - assert ((Kvb k + 832) / 8 <= @aceil (KCEIL k) / 8) by (apply Z.div_le_mono; lia).
        assert ((Kvb k + 832) / 8 = Kvb k / 8 + 104) by (Z.div_mod_to_equations; lia). lia. }
    unfold Kcert, cert_s0. cbn [a_S a_Zr a_L].
    split; [| eapply AsMainIfaceAlloc.ak5_hish_ceil with (HCEIL := KCEIL k) (x := y); first [kargs k | exact Hh' | exact YB]].
    (* the pair's text entry: no map meets it, and it lies in a reserved entry *)
    destruct (k_vcm k) as [_ [[_ [[r [Hr [Hr1 Hr2]]] INC]] [MO _]]].
    cbn [cfg_model APS.cfg_of] in Hr, INC, MO. fold (Kvb k) in Hr1, MO. fold (Kvhi k) in Hr2, MO.
    assert (OFFM : forall b kk z, In (b, kk) (PM_MAPS (bv_unsigned (k_brk0 k)) (KX k)) -> b <= z < b + kk ->
                     Kvb k <= z < Kvhi k -> False).
    { intros b kk z Hin Hz Hw.
      assert (I1 : in_rangesb (Z_to_bv 64 z) (vm_maps (m_vmmaps (k_model k))) = true).
      { eapply AsMainIfaceAlloc.ak_maps_in with (b := b) (k := kk);
          first [kargs k | exact Hin | rewrite (AsInstanceMain.mk_lit z) by lia; exact Hz]. }
      assert (I2 : in_rangesb (Z_to_bv 64 z) (vm_maps (m_vmmaps (k_model k))) = false).
      { apply (AsSRRun.maps_off_in (Kvb k) (Kvhi k)); [exact MO | rewrite (AsInstanceMain.mk_lit z) by lia; exact Hw]. }
      rewrite I2 in I1. discriminate I1. }
    assert (RES : forall z, Kvb k <= z < Kvhi k -> APS.in_ivs z (vm_reserved (m_vmmaps (k_model k))) = true).
    { intros z Hz. unfold APS.in_ivs. apply existsb_exists. exists r. split; [exact (INC r Hr)|].
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    assert (ZS : AsMainLazy.zz_ok (PM_S (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k))).
    { eapply AsMainLazy.zz_ok_S; kargs k. }
    apply (AsMainIfaceAlloc.zz_out (k_sp0 k) (k_brk0 k) _ _ ZS). intros p Hp Hpr.
    unfold PM_S in Hp. destruct Hp as [<-|Hp].
    - (* the 8 MiB band, kernel-placed outside the high shadow *)
      assert (KB22 : In (ps_b22 (KX k), 0x800000) (pm_kernel_placed (KX k))) by (unfold pm_kernel_placed; cbn [In app]; tauto).
      assert (B22 : (fst (ps_b22 (KX k), 0x800000) + snd (ps_b22 (KX k), 0x800000) <= 65536 \/ 12599296 <= fst (ps_b22 (KX k), 0x800000))
                    /\ (fst (ps_b22 (KX k), 0x800000) + snd (ps_b22 (KX k), 0x800000) <= 2147446784
                        \/ 17594333495296 <= fst (ps_b22 (KX k), 0x800000))).
      { eapply AsMainLazy.KBAND_in; first [kargs k | exact KB22]. }
      cbn [fst snd] in B22, Hpr. destruct B22 as [_ B22]. lia.
    - apply in_map_iff in Hp as (q & <- & Hq). unfold SW, SHOFF in Hpr. cbn [fst snd] in Hpr.
      (* a byte of [q] in the text entry, under the shadow byte [y] *)
      assert (Zw : exists z, fst q <= z < fst q + snd q /\ Kvb k <= z < Kvb k + 832).
      { exists (Z.max (fst q) (8 * (bv_unsigned y - 0x7fff8000))). unfold sh, ASHADOW_BASE in Hy.
        split; Z.div_mod_to_equations; lia. }
      destruct Zw as (z & Hz & Hzw).
      unfold VISZ in Hq. apply in_app_iff in Hq as [Hq|Hq].
      + unfold VISZ0 in Hq. cbn [In] in Hq.
        repeat (destruct Hq as [Hq|Hq];
                [ subst q; cbn [fst snd] in Hz;
                  first [ (match type of Hz with ?b <= _ < ?b + ?kk =>
                             apply (OFFM b kk z); [solve [unfold PM_MAPS; cbn [In]; tauto] | exact Hz | lia] end)
                        | (assert (IN9 : In (pm_meta_map (bv_unsigned (k_brk0 k)) (KX k), 0x2000) (PM_MAPS (bv_unsigned (k_brk0 k)) (KX k))) by (unfold PM_MAPS; cbn [In]; tauto);
                           revert Hz; destruct (ps_granted (KX k)) eqn:Eg; cbn [fst snd]; intros Hz; apply (OFFM (pm_meta_map (bv_unsigned (k_brk0 k)) (KX k)) 0x2000 z IN9);
                           first [ solve [unfold pm_meta_map; rewrite Eg; cbv beta iota; lia] | solve [lia] ])
                        | (assert (SB : pm_space_beg (KX k) mod 65536 = 0 /\ ps_b06 (KX k) < pm_space_beg (KX k) <= ps_b06 (KX k) + 65536
                                        /\ pm_region_info (KX k) = pm_space_beg (KX k) + 2 ^ 37
                                        /\ pm_region_info (KX k) + 4096 <= ps_b06 (KX k) + 0x2000011000 /\ 17594333495296 <= ps_b06 (KX k)
                                        /\ ps_b06 (KX k) + 0x2000011000 <= AsMainSyms.page_down (bv_unsigned (k_sp0 k)) - 8388608)
                             by (eapply AsMainIfaceAlloc.al_SB; kargs k);
                           apply (OFFM (ps_b06 (KX k)) 0x2000011000 z); [ solve [unfold PM_MAPS; cbn [In]; tauto] | lia | lia ])
                        | (unfold AIMG_TOP in VLI; lia)
                        | lia ]
                | ]).
        destruct Hq.
      + (* a ghost: it holds no reserved byte, and [z] is one *)
        assert (VZ : map (fun p => (APS.uE (k_E k) (fst p), APS.uE (k_E k) (snd p))) (APC.a_vis (k_ch k))
                       = VISZ0 (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k)
                     /\ map (fun p => (APS.uE (k_E k) (fst p), APS.uE (k_E k) (snd p))) (APC.a_ghost (k_ch k)) = GHZ (KX k)).
        { eapply AsMainLazy.VISZ0_eq; kargs k. }
        destruct VZ as [_ GZ].
        rewrite <- GZ in Hq. apply in_map_iff in Hq as (g0 & Eg0 & Hg0). subst q. cbn [fst snd] in Hz.
        pose proof (proj1 (Forall_forall _ _) (APS.co_gres _ _ _ _ _ _ _ _ _ _ _ (k_HC k)) g0 Hg0 z Hz) as G0.
        rewrite (RES z ltac:(lia)) in G0. discriminate G0.
  Qed.

  (* the marker's byte: in the high shadow, below 2^64 *)
  Lemma kit_mark_byte : forall k (a : word), zin_rangeb (bv_unsigned a) (AsSRRun.pw_mark (Kvb k)) = true ->
    sh (Kvb k) <= bv_unsigned a < sh (Kvb k) + 1.
  Proof.
    intros k a Ha. pose proof (kv_vb k) as (V8 & VL & _ & VH). pose proof (kv_hi64 k) as V64.
    assert (SH : 0 <= sh (Kvb k) < 2 ^ 64) by (unfold sh, ASHADOW_BASE, AHI_LO in *; Z.div_mod_to_equations; lia).
    unfold zin_rangeb, AsSRRun.pw_mark in Ha. cbn [fst snd] in Ha. apply andb_true_iff in Ha as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (AsInstanceMain.mk_lit (sh (Kvb k)) SH) in E1, E2. rewrite (AsInstanceMain.mk_lit 1 ltac:(lia)) in E2. lia.
  Qed.

  (* (3).  The lazy view with the marker opened: the marker is hidden and lazily reserved at the
     entry ([kit_mark_off]), so [LazySR.lzok_open_hidden_window] opens it over the entry's
     [AsMainLazy.lzok_open]: [lzok] holds with the marker in the visible set and the view reads 0
     at the marker.  The budget side condition is [AsMainIfaceAlloc.ak_budget] with
     [kit_mark_pages]. *)
  Lemma kit_open : forall k,
    lzok asegs (a_L (Kcert k)) (AsSRRun.pw_mark (Kvb k) :: a_S (Kcert k)) (a_Zr (Kcert k)) (Kcfg k)
    /\ restrict (a_L (Kcert k)) (AsSRRun.pw_mark (Kvb k) :: a_S (Kcert k)) (cfg_ms (Kcfg k))
       = with_mem (restrict (a_L (Kcert k)) (a_S (Kcert k)) (cfg_ms (Kcfg k)))
           (fun a => if zin_rangeb (bv_unsigned a) (AsSRRun.pw_mark (Kvb k)) then Some (Z_to_bv 8 0)
                     else ms_mem (restrict (a_L (Kcert k)) (a_S (Kcert k)) (cfg_ms (Kcfg k))) a).
  Proof.
    intros k.
    pose proof (AsMainLazy.lzok_open (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as [LZ _].
    pose proof (AsMainIfaceAlloc.ak_budget (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as (B1 & B2 & B3 & B4).
    pose proof (kit_mark_pages k) as MP.
    apply (LazySR.lzok_open_hidden_window asegs (a_L (Kcert k)) (a_S (Kcert k)) (a_Zr (Kcert k))
             (AsSRRun.pw_mark (Kvb k)) (cfg_ms (Kcfg k)) (k_model k)).
    - exact LZ.
    - intros a Ha. pose proof (kit_mark_byte k a Ha) as Hb.
      exact (proj1 (proj2 (kit_mark_off k a ltac:(lia)))).
    - intros a Ha. pose proof (kit_mark_byte k a Ha) as Hb.
      destruct (kit_mark_off k a ltac:(lia)) as (S1 & _ & L1). unfold hiddenb. rewrite L1, S1. reflexivity.
    - rewrite pages_total_cons, B2. unfold Kcert, cert_s0. cbn [a_S]. unfold KX in *.
      unfold target_alloc_limit, page_size in *. lia.
  Qed.

  Lemma kit_vis : forall k, as_VIS (KH k) (KS0 k) (cfg_ms (Kcfg k)) = mkst (k_R k) (Z_to_bv 64 A_MAIN) (KM k) (seg_rom asegs).
  Proof.
    intros k. destruct (kit_open k) as [_ EQ].
    change (as_VIS (KH k) (KS0 k) (cfg_ms (Kcfg k)))
      with (restrict (a_L (Kcert k)) (AsSRRun.pw_mark (Kvb k) :: a_S (Kcert k)) (cfg_ms (Kcfg k))).
    rewrite EQ.
    assert (V0 : restrict (a_L (Kcert k)) (a_S (Kcert k)) (cfg_ms (Kcfg k)) = mkst (k_R k) (Z_to_bv 64 A_MAIN) (KVM k) (seg_rom asegs))
      by exact (AS_InstMainK.vis_main_s0 (k_sp0 k) (k_brk0 k) (k_h k) (k_E k) (k_R k) (k_FULL k) [] false AL0).
    rewrite V0. reflexivity.
  Qed.

  (* (4).  The kernel relation at the run instance: [KHp]'s ([kit_open] and [kit_IK]), the pair's
     invariant [kit_vcm2], and [pw_ok]: the marker visible (by [Ks0]'s construction), the window
     hidden ([kit_mark_off]) and 4096 bytes of budget held back ([AL0]). *)
  Lemma kit_krel : forall k, as_AKREL (KH k) (KS0 k) (Kcfg k).
  Proof.
    intros k. destruct (kit_open k) as [LZ _].
    change (as_AKREL (KH k) (KS0 k) (Kcfg k)) with
      ((lzok asegs (a_L (Kcert k)) (AsSRRun.pw_mark (Kvb k) :: a_S (Kcert k)) (a_Zr (Kcert k)) (Kcfg k)
        /\ @IK (KCEIL k) (kip k) (KS0 k) (cfg_model (Kcfg k)))
       /\ vcm2 (Kvlo k) (Kvb k) (Kvhi k) (Kcfg k) /\ @AsSRRun.pw_ok (KCEIL k) (Kvb k) (KS0 k)).
    split; [split; [exact LZ | exact (kit_IK k)]|]. split; [exact (kit_vcm2 k)|].
    pose proof (kv_vb k) as (V8 & VL & _ & VH). pose proof (kv_hi64 k) as V64.
    assert (SH : 0 <= sh (Kvb k) < 2 ^ 64) by (unfold sh, ASHADOW_BASE, AHI_LO in *; Z.div_mod_to_equations; lia).
    unfold AsSRRun.pw_ok. change (a_S (i_s (KS0 k))) with (AsSRRun.pw_mark (Kvb k) :: a_S (Kcert k)).
    split; [|split].
    - rewrite in_rangesb_cons. apply orb_true_iff. left.
      unfold zin_rangeb, AsSRRun.pw_mark. cbn [fst snd].
      rewrite (AsInstanceMain.mk_lit (sh (Kvb k)) SH), (AsInstanceMain.mk_lit 1 ltac:(lia)).
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    - intros y Hy. rewrite in_rangesb_cons. apply orb_false_iff. split.
      + destruct (zin_rangeb (bv_unsigned y) (AsSRRun.pw_mark (Kvb k))) eqn:Ez; [|reflexivity].
        pose proof (kit_mark_byte k y Ez). lia.
      + exact (proj1 (kit_mark_off k y ltac:(lia))).
    - change (a_AL (i_s (KS0 k))) with AL0. unfold AL0. lia.
  Qed.

  (* (5).  The heap relation at the opened view and the kit's state.  [AS_InstMainHeap.rheap_main]
     gives it at the entry's view [KVM k] and state [Kcert k].  The kit's view differs from the
     entry's at the marker byte [KQ k] only ([kit_mem]): a high-shadow byte, which is no byte the
     relation's cells and depot occupy (those lie in the image, the low range or the application's
     ranges, [AS_InstLaws3.iprotected]) and no allocator footprint byte (no piece of the
     allocator's, and the shadow of a piece of it covers a byte of the primary space or of a
     secondary chunk, both mapped, while the marker covers a byte of the vDSO text, which no map
     holds: [kit_vcm2]'s maps_off), so [AllocRepFacts.ARHEAP_frame_ok] and the transports of
     [AS_InstLaws3.inst_RHEAP_frame] carry every conjunct; the kit's state differs in its visible
     set only, which gains the marker, whose byte [KM k] holds ([awin_vis]) and which only adds
     to [ashadow_visible]. *)
  Lemma kit_heap : forall k, as_RHEAP (KH k) (KS0 k) [] (KM k).
  Proof.
    intros k.
    pose proof (AS_InstMainHeap.rheap_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                  (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0 (kip k) eq_refl eq_refl) as R0.
    change (@IRHEAP (KCEIL k) (kip k) (IST (Kcert k) (Kd0 k)) [] (KVM k)) in R0.
    pose proof R0 as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV).
    cbn [i_s i_d] in HA, AWV, DPL, TLS, ASV.
    pose proof (kit_mem k) as MK.
    pose proof (AsInstanceMain.mk_munch _ _ _ MK) as MU. pose proof (AsInstanceMain.mk_wmono _ _ _ MK) as WM.
    pose proof (AsInstanceMain.mk_q _ _ _ MK) as (_ & QL & QH).
    (* where the marker lies against the ranges the relation names *)
    assert (EH1 : 0x10007fff8000 <= AsShadow.AHI_LO) by (unfold AsShadow.AHI_LO; lia).
    assert (EL1 : AsShadow.ALOWSH_LO < 0x2008fff7000) by (unfold AsShadow.ALOWSH_LO; lia).
    assert (EH2 : 0x10007fff8000 <= AsMainSyms.AHI_LO) by (unfold AsMainSyms.AHI_LO; lia).
    assert (EL2 : AsMainSyms.ALOWSH_LO < 0x2008fff7000) by (unfold AsMainSyms.ALOWSH_LO; lia).
    assert (EI1 : ASegs.AIMG_TOP < 0x2008fff7000) by (unfold ASegs.AIMG_TOP; lia).
    assert (EI2 : ASegs.AIMG_LO < 0x2008fff7000) by (unfold ASegs.AIMG_LO; lia).
    assert (EI3 : AsMainSyms.AIMG_TOP < 0x2008fff7000) by (unfold AsMainSyms.AIMG_TOP; lia).
    assert (EI4 : AsMainSyms.AIMG_LO < 0x2008fff7000) by (unfold AsMainSyms.AIMG_LO; lia).
    (* the entry's view and the kit's agree off the marker *)
    assert (AG : agree_on (fun a => a <> KQ k) (KVM k) (KM k)).
    { intros a Pa Ha. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
    pose proof HA as (AR & ND & EQ). pose proof (proj1 AR) as OK.
    pose proof (proj1 OK) as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof TH as (_ & _ & DB0 & DB8 & DB32 & DKO). unfold kPageSize in DKO.
    pose proof T2 as TKO.
    pose proof DPL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & QSEC & QA1 & QA2 & QA3 & QA4).
    unfold akobj, alow1, aapp, aapp_lo, aapp_hi, kPageSize in DKO, TKO, QA1, QA3.
    (* the marker is no byte of an allocator piece or of the shadow of one *)
    pose proof (AllocRepFacts.ARHEAP_frame_ok _ _ _ _ _ HA MU WM) as HA'.
    match type of HA' with ?F -> _ => assert (FW : F) end.
    { apply Forall_cons; [| apply Forall_nil]. right; right; right; right. cbn [fst snd].
      intros a Ha AF.
      destruct (AllocRepFacts.afoot_cases _ OK a AF) as [(lo & hi & P & R)|[(ch & Hch & R)|[[R _]|(lo & hi & P & R)]]].
      - pose proof (AllocRepFacts.apiece_noshadow _ OK lo hi P) as NS. clear - NS R Ha QL QH EH1 EL1 EH2 EL2. lia.
      - pose proof (AllocRepFacts.ext_band _ OK ch Hch) as EB. pose proof (AllocRepFacts.chunk_geom _ OK ch Hch) as (G1 & G2 & G3 & G4 & _).
        pose proof (AllocRepFacts.ext_facts _ OK ch Hch) as (E1 & E2 & E3 & _).
        unfold aapp, aapp_lo, aapp_hi in EB. clear - R EB G1 G2 G3 G4 E1 E2 E3 Ha QL QH EH1 EL1 EH2 EL2 EI1 EI2 EI3 EI4. lia.
      - clear - R Ha QL EI1 EI2 EI3 EI4. lia.
      - pose proof (AllocRepFacts.spiece_bounds _ OK lo hi P) as (B1 & B2 & B3 & B4 & B5).
        pose proof (kv_vb k) as (V8 & _ & _ & VH). pose proof (kv_hi64 k) as V64. pose proof (kv_mid_top k) as VMT.
        pose proof (kv_lo k) as (VL1 & _ & VL3). pose proof (kv_ord k) as VO.
        assert (VB : lo <= Kvb k < hi).
        { unfold KQ, sh in Ha, R. clear - Ha R B1 B2 B4 B5 V8. Z.div_mod_to_equations. lia. }
        destruct (k_vcm k) as [_ [_ [MO _]]]. cbn [cfg_model APS.cfg_of] in MO. fold (Kvb k) in MO. fold (Kvhi k) in MO.
        assert (OUT : in_rangesb (Z_to_bv 64 (Kvb k)) (vm_maps (m_vmmaps (k_model k))) = false).
        { apply (AsSRRun.maps_off_in (Kvb k) (Kvhi k)); [exact MO | rewrite (AsInstanceMain.mk_lit (Kvb k)) by lia; lia]. }
        pose proof (AS_InstMainK.akernel_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                      (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k) (KCEIL k) eq_refl [] false AL0) as AK.
        destruct (AS_InstLaws3.spiece_loc _ OK lo hi P) as [[L1 L2]|(sc & Hsc & L1 & L2)].
        + assert (SB0 : a_sb (Kcert k) <= Kvb k < a_sb (Kcert k) + kSpaceSize + kPageSize) by lia.
          assert (IN : in_rangesb (Z_to_bv 64 (Kvb k)) (vm_maps (m_vmmaps (k_model k))) = true).
          { apply (ak_sbmaps _ _ AK). rewrite (AsInstanceMain.mk_lit (Kvb k)) by lia. exact SB0. }
          rewrite IN in OUT. discriminate OUT.
        + assert (SEC0 : as_sec (a_st (Kcert k)) = []) by reflexivity.
          rewrite SEC0 in Hsc. destruct Hsc. }
    specialize (HA' FW).
    (* the cells and the depot: off the marker *)
    assert (PROT : forall a, @AS_InstLaws3.iprotected (KCEIL k) (kip k) (IST (Kcert k) (Kd0 k)) a -> a <> KQ k).
    { intros a PR Ea. subst a.
      unfold AS_InstLaws3.iprotected, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRep.ACFLAGS, AsIface.ATP in PR.
      cbn [i_s i_d] in PR. clear - PR QL QH DKO TKO QA1 QA3 EH1 EL1 EH2 EL2 EI1 EI2 EI3 EI4. lia. }
    assert (AGP : agree_on (@AS_InstLaws3.iprotected (KCEIL k) (kip k) (IST (Kcert k) (Kd0 k))) (KVM k) (KM k)).
    { intros a Pa Ha. exact (AG a (PROT a Pa) Ha). }
    unfold KH. cbn [as_RHEAP AsSRRun.KHr KHp]. unfold IRHEAP. cbv zeta. cbn [i_s i_d KS0].
    split; [exact HA'|].
    split; [exact IDS|]. split; [exact LEN|].
    split.
    { (* the visible set gains the marker, whose byte the kit's view holds *)
      intros x Hx. unfold Ks0 in Hx. cbn [a_S] in Hx. rewrite in_rangesb_cons in Hx. apply orb_true_iff in Hx as [Hx|Hx].
      - unfold wview, KM. cbv beta. rewrite Hx. cbv iota. discriminate.
      - exact (awin_vis_wmono _ _ _ AWV WM x Hx). }
    split.
    { destruct FLX as (F1' & F2' & (g & F3') & F4' & (b & F5')).
      split; [| split; [| split; [| split]]].
      - eapply (rw_cells_transport_pt _ _ _ AGP WM); [exact F1'|]. intros a Ha. unfold AS_InstLaws3.iprotected. cbn [i_s i_d].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in Ha. lia.
      - eapply (rw_cells_transport_pt _ _ _ AGP WM); [exact F2'|]. intros a Ha. unfold AS_InstLaws3.iprotected. cbn [i_s i_d].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in Ha. lia.
      - exact (AS_InstLaws3.sspguard_rw_any (KM k)).
      - eapply (rw_cells_transport_pt _ _ _ AGP WM); [exact F4'|]. intros a Ha. unfold AS_InstLaws3.iprotected. cbn [i_s i_d].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in Ha. lia.
      - exists b. eapply (rw_cells_transport_pt _ _ _ AGP WM); [exact F5'|]. intros a Ha. unfold AS_InstLaws3.iprotected. cbn [i_s i_d].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in Ha. lia. }
    split.
    { destruct DEP0 as [DWF DM]. split; [exact DWF|].
      eapply AS_InstLaws3.depot_mem_frame; [exact DWF | exact DM | exact AGP | exact WM | reflexivity | reflexivity]. }
    split; [exact DPL|]. split; [exact DTR|]. split; [exact DJ1|]. split; [exact DJ2|]. split; [exact EF|]. split; [exact MF|]. split; [exact DJD|].
    split.
    { destruct TH as (A1 & A2 & A3). split; [| split; [| exact A3]].
      - eapply (rw_cells_transport_pt _ _ _ AGP WM); [exact A1|]. intros a Ha. unfold AS_InstLaws3.iprotected. cbn [i_s i_d].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in Ha. unfold AsIface.ATP, AllocRep.ATP in *. lia.
      - eapply (rw_cells_transport_pt _ _ _ AGP WM); [exact A2|]. intros a Ha. unfold AS_InstLaws3.iprotected. cbn [i_s i_d].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in Ha. lia. }
    split.
    { destruct TLS as (tb & te & T48). exists tb, te. assert (ET : a_thr (Ks0 k) = a_thr (Kcert k)) by reflexivity.
      eapply (rw_cells_transport_pt _ _ _ AGP WM); [exact T48|]. intros a Ha. unfold AS_InstLaws3.iprotected. cbn [i_s i_d].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length] in Ha. clear - Ha ET. lia. }
    split.
    { (* the marker only grows the visible set, and [ashadow_visible] is monotone in it *)
      destruct ASV as [AS1 AS2]. split.
      - intros c x Hc Hx. cbn [Ks0 Kcert a_S]. rewrite in_rangesb_cons. apply orb_true_iff. right. exact (AS1 c x Hc Hx).
      - intros sc x Hsc Hx. cbn [Ks0 Kcert a_S]. rewrite in_rangesb_cons. apply orb_true_iff. right. exact (AS2 sc x Hsc Hx). }
    split; [exact DAP|]. split; [exact DSEC| exact PINV].
  Qed.

  (* (6).  [aauxv_ok] ties AT_SYSINFO_EHDR to [hvdso], which [KCEIL] builds at the run's mmap base
     [k_mbase] ([AsInstanceMain.main_ceil]).  [AsMainIfaceAuxv.auxv_ok_main] proves the claim at the
     entry's view from the words of the vector's first pair, all of the vector the claim holds
     ([AsAuxv.aauxv_ok]), which [AsMainIfaceAuxv.auxv_pair0_vec] reads from the main-entry states
     once AT_SYSINFO_EHDR's launch variable is the run's vDSO text base: [APS.co_ehdr] at the
     run's kernel build and mmap base ([k_kern]), the model's [vdso_top] there being the pair's
     top [Run.vdso_pair_top] ([AsMainIfaceAlloc.ak_top]).  The value record's other slots are
     not claimed ([AsMainIfaceAuxv.auxv_sys]).  The kit's view differs from the entry's at the
     marker byte only, in the high shadow, far from the libc cell and below the vector
     ([AsAuxv.aauxv_ok_frame] over [kit_mem]). *)
  Lemma kit_aux : forall k, as_rauxv_ok (KH k) (KM k) (KB k) /\ bv_unsigned (k_sp0 k) <= KB k < 2 ^ 64 /\ @aauxv_ok (KCEIL k) (KM k) (KB k).
  Proof.
    intros k. pose proof (k_Vfit k) as F. unfold entry_stack_fits, entry_stack_span, sp_window_hi in F.
    pose proof (total_arg_bytes_nonneg (in_argv (k_inp k))). pose proof (total_arg_bytes_nonneg (in_envp (k_inp k))).
    pose proof (u64_range (k_sp0 k)).
    split; [| split].
    - unfold KH, KB. cbn [as_rauxv_ok AsSRRun.KHr KHp]. unfold Irauxv_ok. lia.
    - unfold KB. lia.
    - apply (@aauxv_ok_frame (KCEIL k) (KVM k) (KM k) (KB k) [(KQ k, KQ k + 1)]);
        [| exact (AsInstanceMain.mk_munch _ _ _ (kit_mem k)) | exact (AsInstanceMain.mk_wmono _ _ _ (kit_mem k)) |].
      2:{ pose proof (AsInstanceMain.mk_q _ _ _ (kit_mem k)) as (_ & Q1 & Q2).
          pose proof (k_Vsp k) as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
          apply Forall_cons; [| apply Forall_nil].
          apply aauxv_win_ok_intro; [unfold KB; lia | right; unfold AAUXV_CELL; lia]. }
      set (vtb := vdso_text_base (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k)).
      (* AT_SYSINFO_EHDR's launch variable is the run's vDSO text base *)
      assert (EHk : Z_to_bv 64 (bv_unsigned vtb) = AX2.ev (k_E k) APC.V_EHDR).
      { rewrite Z_to_bv_bv_unsigned. pose proof (k_HC k) as HCk. apply APS.co_ehdr in HCk. rewrite HCk.
        destruct (k_kern k) as [KK KMB]. rewrite KK. unfold vtb, vdso_text_base. f_equal. f_equal.
        pose proof (AsMainIfaceAlloc.ak_top (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                      (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Hh k) (k_HC k)) as AT.
        unfold vdso_pair_top, vdso_top, mmap_top. rewrite KMB, AT. unfold stack_max_size. reflexivity. }
      pose proof (bv_unsigned_in_range _ vtb) as BR. change (bv_modulus 64) with (2 ^ 64) in BR.
      apply (AsMainIfaceAuxv.auxv_ok_main (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
               (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (KCEIL k) (k_mbase k)
               (AsMainIfaceAuxv.auxv_sys (bv_unsigned vtb)) 0 0 false).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact (AsMainIfaceAuxv.auxv_sys_ok _ BR).
      + lia.
      + lia.
      + exact (AsMainIfaceAuxv.auxv_pair0_vec (k_sp0 k) (k_brk0 k) (k_rdraw k) (k_inp k) (k_h k) (k_ch k) (k_E k) (k_R k) (k_FULL k) (k_model k)
                 (k_Vsp k) (k_Vbrk k) (k_Vav k) (k_Vev k) (k_Vfit k) (k_Hh k) (k_HC k) (AsMainIfaceAuxv.auxv_sys (bv_unsigned vtb)) 0 0 false EHk).
  Qed.

  (* [comment removed for export] *)
  Theorem as_instance_kit : as_instance_stmt EAsChainRun.P_mainK L.
  Proof.
    exact (instance_of_kit KH KS0 KB L Kvlo Kvb Kvhi KM KQ kit_mem kit_rt_x kit_ifacts kit_dl kit_live kit_tails
             kit_vis kit_krel kit_rfs kit_heap kit_aux kit_al kit_tr LOK K_libx0).
  Qed.
End KIT.

(* [comment removed for export] *)
