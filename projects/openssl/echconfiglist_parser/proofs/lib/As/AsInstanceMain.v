(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (main_ceil gives the heap-ceiling record's new hvdso field as the launch's vDSO text base at the run's mmap base plus 1460, the vDSO's clock_gettime entry, and mctx carries that base; mctx is stated over AsanInitL's SINV0L and argH0; the kit's library is a function of the heap-ceiling record; the kit supplies the launch's channel reader by pre_rdr); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); the kit is the run instance's: mctx also carries the launch's mmap base valid, the kit names the launch's vDSO pair vlo vb vhi and takes the run's driver laws and the three tail statements, and its visible memory is the main entry's view with the marker byte of the vDSO text's shadow opened (Section Marker frames every memory field of the main precondition over that one byte); mctx records the run's kernel build and mmap base and the launch's vDSO pair clean, reserved and met by no map at the main entry (k_kern, k_vcm), and the instance is stated at EAsChainRun.P_mainK. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec HeapCeil LazyRestrict LazySR Frame MainMem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsStack0 AsDriverLaws ECH_Xpres ECH_Iface AsDrvDefs AsDrvMem AsMainPre AsMainTop AsInstance FakeStackRep AsAuxv F_time AInstFacts.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import AsImages AsPlanImages.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanInitL
  AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceConst AsMainIfacePre AsMainIfaceArgs AsMainIfaceDepot AsMainIfaceFS
  AsMainIfaceAlloc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import AsMainSyms.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import KernOk.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require StoreOk.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require AsCellOk AsPrintfFirst.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsHole Require EAsChainRun.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main_ceil_range : forall sp0 : word, valid_sp sp0 -> 0x7fff7f800000 <= bv_unsigned sp0 - 8388608 <= 0x7fffff800000.
Proof. intros sp0 [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2. lia. Qed.
(* LPS 727298f3: [hvdso] is the vDSO's clock_gettime entry, the AT_SYSINFO_EHDR the launch writes
   ([Run.launch_auxv]: [vdso_text_base kb sp0 mbase], LPS b84e73ef) plus its offset 1460 in the image
   ([Lib/VdsoImg.rvdso_cgt_off_measured]), as RefTop's [ref_realizes_spec_lim] builds Ref's record. *)
Definition main_ceil (sp0 : word) (V : valid_sp sp0) (kb : KernelBuild) (mbase : word) : HeapCeil :=
  mkHeapCeil (bv_unsigned sp0 - 8388608) (main_ceil_range sp0 V) (bv_unsigned (vdso_text_base kb sp0 mbase) + 1460).
Lemma main_ceil_eq : forall sp0 V kb mbase, @hceil (main_ceil sp0 V kb mbase) = bv_unsigned sp0 - 8388608.
Proof. reflexivity. Qed.
Lemma main_ceil_vdso : forall sp0 V kb mbase, @hvdso (main_ceil sp0 V kb mbase) = bv_unsigned (vdso_text_base kb sp0 mbase) + 1460.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record mctx : Type := MCTX {
  k_sp0 : word; k_brk0 : word; k_rdraw : EntryDraw; k_inp : ProcInput; k_mbase : word;
  k_h : nat; k_ch : acs; k_E : env; k_R : bvmap 5 word; k_FULL : word -> option byte; k_model : Model;
  k_Vsp : valid_sp k_sp0;
  (* #38: the launch's mmap base is valid; the pair [Run.vdso_segments] the run maps is read at
     it ([Ref/VdsoLaunch.v]'s [top_range] and the facts time() takes) *)
  k_Vmb : valid_mmap_base k_mbase;
  k_Vbrk : valid_brk ASEGS k_brk0;
  k_Vav : valid_argv (in_argv k_inp);
  k_Vev : valid_envp (in_envp k_inp);
  k_Vfit : entry_stack_fits k_sp0 (in_argv k_inp) (in_envp k_inp);
  k_Hh : HSF_asan k_h = Some k_ch;
  k_HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT
           (SINV0L APH Asan.M.init_pc k_sp0 k_rdraw k_brk0 k_inp)
           (argH0 k_sp0 k_rdraw k_inp) (in_fs k_inp) k_E k_ch k_R k_FULL k_model;
  (* the run's kernel build and mmap base, and the launch's vDSO pair clean, reserved and met by
     no map with the pins well formed, at the main entry ([EAsChainRun.P_mainK]) *)
  k_kern : kern_ok (in_kernel k_inp) k_mbase k_model;
  k_vcm : EAsChainRun.vcm_run k_inp k_sp0 k_mbase (cfg_of ASEGS k_R A_MAIN k_FULL k_model) }.

(* [comment removed for export] *)
Definition KX (k : mctx) : pm_syms := Xof (hole_granted (k_h k)) (k_E k).
Definition KVM (k : mctx) : word -> option byte := pm_vmem (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k) (k_FULL k).
Definition Kcfg (k : mctx) : config := cfg_of ASEGS (k_R k) A_MAIN (k_FULL k) (k_model k).
Definition KCEIL (k : mctx) : HeapCeil := main_ceil (k_sp0 k) (k_Vsp k) (in_kernel (k_inp k)) (k_mbase k).
Definition KL0 (k : mctx) : list (word * word) := zz2ww (PM_LAZY (bv_unsigned (k_sp0 k)) (KX k)).
Definition KS (k : mctx) : list (word * word) := zz2ww (PM_S (bv_unsigned (k_sp0 k)) (bv_unsigned (k_brk0 k)) (KX k)).
Definition KZr0 (k : mctx) : list (word * word) := zz2ww (PM_ZR (bv_unsigned (k_sp0 k)) (KX k)).

(* The run instance's visible memory at main entry is the entry's view with ONE byte opened: the
   marker [As/AsSRRun.pw_mark vb], the shadow byte of the launch's vDSO text, which the run
   instance's kernel relation ([AsSRRun.pw_ok]) keeps visible so that time()'s first call may
   open the window on its page inside the budget already accounted.  That byte lies in the high
   shadow [sh AHI_LO, sh aceil) = [0x2008fff7000, sh aceil): above the binary's image and its low
   shadow, and below the stack, the stack's shadow and the heap ceiling.  So every memory field
   of the main precondition the entry's view has, its one-byte opening has, each by the frame
   lemma of its shape; the fields that read the instance (the view, the kernel relation, the
   file frames, the heap relation and the auxv) are the kit's at the opened view. *)
Section Marker.
  Context {HCEIL : HeapCeil}.

  (* [M'] is [M] with the one byte at [q] opened *)
  Definition mk_ok (M M' : word -> option byte) (q : Z) : Prop :=
    0x2008fff7000 <= q /\ q + 1 <= sh aceil /\ frame_mod M M' [(wa q, 1)].

  Lemma mk_lit : forall a : Z, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
  Proof. intros a Ha. apply wa_unsigned. exact Ha. Qed.

  Lemma mk_q : forall M M' q, mk_ok M M' q ->
    bv_unsigned (wa q) = q /\ 0x2008fff7000 <= q /\ q + 1 <= 0x10007fff8000.
  Proof.
    intros M M' q (Q1 & Q2 & _). pose proof (@aceil_range HCEIL) as AR.
    assert (EH : sh aceil <= 0x10007fff8000).
    { unfold sh. rewrite ASHADOW_BASE_val.
      assert (DM : aceil / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
      change (0x7fffff800000 / 8) with 0xffffff00000 in DM. lia. }
    split; [apply wa_unsigned; lia|]. split; lia.
  Qed.

  Lemma mk_mono : forall M M' q, mk_ok M M' q -> StoreOk.mem_grows M M'.
  Proof. intros M M' q (_ & _ & FM). exact (proj2 FM). Qed.
  Lemma mk_wmono : forall M M' q, mk_ok M M' q -> wmono asegs M M'.
  Proof. intros M M' q (_ & _ & FM). exact (aframe_mod_wmono _ _ _ FM). Qed.
  Lemma mk_munch : forall M M' q, mk_ok M M' q -> munch [(q, q + 1)] M M'.
  Proof.
    intros M M' q HK. pose proof (mk_q _ _ _ HK) as (QE & _ & _). destruct HK as (_ & _ & FM).
    pose proof (frame_mod_munch _ _ _ FM) as MU. unfold ivls in MU. cbn [map fst snd] in MU.
    rewrite QE in MU. exact MU.
  Qed.

  (* a read that misses the byte: below it, or above the whole high shadow *)
  Lemma mk_rdn : forall M M' q (a : Z) n bs, mk_ok M M' q ->
    0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (a + Z.of_nat n <= 0x2008fff7000 \/ 0x10007fff8000 <= a) ->
    rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros M M' q a n bs HK Ha Hn Hband HR. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2). destruct HK as (_ & _ & FM).
    eapply ardn_frame; [exact FM | exact HR | lia | lia |].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite QE. lia.
  Qed.

  Lemma mk_none : forall M M' q lo hi, mk_ok M M' q -> 0 <= lo -> hi <= 0x2008fff7000 ->
    (forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None) ->
    forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = None.
  Proof.
    intros M M' q lo hi HK Hlo Hhi HN. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2). destruct HK as (_ & _ & FM).
    apply (arange_none_frame M M' [(wa q, 1)] lo hi HN FM); [| lia | lia].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite QE. lia.
  Qed.

  Lemma mk_none_h : forall M M' q lo hi hlo hhi, mk_ok M M' q -> 0 <= lo -> hi <= 0x2008fff7000 ->
    (forall i, lo <= i < hi /\ ~ (hlo <= i < hhi) -> M (Z_to_bv 64 i) = None) ->
    forall i, lo <= i < hi /\ ~ (hlo <= i < hhi) -> M' (Z_to_bv 64 i) = None.
  Proof.
    intros M M' q lo hi hlo hhi HK Hlo Hhi HN. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2). destruct HK as (_ & _ & FM).
    apply (arange_none_frame_hole M M' [(wa q, 1)] lo hi hlo hhi HN FM); [| lia | lia].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite QE. lia.
  Qed.

  Lemma mk_none1 : forall M M' q (a : Z), mk_ok M M' q -> 0 <= a < 0x2008fff7000 ->
    M (Z_to_bv 64 a) = None -> M' (Z_to_bv 64 a) = None.
  Proof.
    intros M M' q a HK Ha HM. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2). destruct HK as (_ & _ & FM).
    rewrite (proj1 FM); [exact HM|]. apply outside_of_disjoint.
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite QE, (mk_lit a ltac:(lia)). lia.
  Qed.

  (* every cell of the list lies below the byte (the second boolean), so the frame keeps them *)
  Lemma mk_cells : forall M M' q cs, mk_ok M M' q ->
    forallb lib.As.AsPrintfFirst.cell_wf_b cs = true ->
    forallb (fun c : Z * nat * Z => Z.leb (fst (fst c) + Z.of_nat (snd (fst c))) 0x2008fff7000) cs = true ->
    lib.As.AsCellOk.cells_ok M cs -> lib.As.AsCellOk.cells_ok M' cs.
  Proof.
    intros M M' q cs HK Hwf Hlo HC. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2). destruct HK as (_ & _ & FM).
    eapply acells_ok_frame; [exact Hwf | exact HC | exact FM |].
    apply Forall_forall. intros [[a w] v] Hin r Hr.
    rewrite forallb_forall in Hlo. pose proof (Hlo _ Hin) as HB. cbn [fst snd] in HB. apply Z.leb_le in HB.
    cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite QE. lia.
  Qed.

  Lemma mk_rw : forall M M' q A cs, mk_ok M M' q -> 0 <= A ->
    A + Z.of_nat (cells_size cs) <= 0x2008fff7000 -> rw_cells asegs M A cs -> rw_cells asegs M' A cs.
  Proof.
    intros M M' q A cs HK HA Hhi HR. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2). destruct HK as (_ & _ & FM).
    eapply arw_cells_frame; [exact HR | exact FM |].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite QE. lia.
  Qed.

  Lemma mk_inv : forall M M' q, mk_ok M M' q -> mem_inv asegs M -> mem_inv asegs M'.
  Proof.
    intros M M' q HK INV. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2). destruct HK as (_ & _ & FM).
    eapply amem_inv_frame; [exact INV | exact FM |].
    constructor; [| constructor]. cbn [fst snd]. rewrite QE. split; [lia | right; lia].
  Qed.

  Lemma mk_stk : forall M M' q lo hi, mk_ok M M' q -> 0x7fff7f800000 <= lo -> hi <= 2 ^ 64 ->
    stk asegs M lo hi -> stk asegs M' lo hi.
  Proof.
    intros M M' q lo hi HK Hlo Hhi ST. apply (astk_grows M M'); [exact ST | lia | lia | exact (mk_mono _ _ _ HK)].
  Qed.

  Lemma mk_sh0 : forall M M' q lo, mk_ok M M' q ->
    (exists shi, stack0 M lo shi /\ 0x800000000000 <= shi) ->
    exists shi, stack0 M' lo shi /\ 0x800000000000 <= shi.
  Proof.
    intros M M' q lo HK [shi [SH0 Hshi]]. pose proof HK as (_ & Qhi & _).
    exists shi. split; [| exact Hshi].
    eapply stack0_transport; [exact SH0 | exact (mk_munch _ _ _ HK) | exact (mk_wmono _ _ _ HK) |].
    constructor; [| constructor]. unfold stack0_ok. cbn [fst snd]. right. exact Qhi.
  Qed.

  Lemma mk_ac : forall M M' q, mk_ok M M' q -> ACONST M -> ACONST M'.
  Proof.
    intros M M' q HK AC. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2).
    eapply ACONST_frame; [exact AC | exact (mk_munch _ _ _ HK) | exact (mk_wmono _ _ _ HK) |].
    constructor; [| constructor]. apply aconst_ok_high; cbn [fst snd].
    - match goal with |- ?x <= _ => assert (T : x <= 0x2008fff7000) by (vm_compute; discriminate) end. lia.
    - lia.
  Qed.

  Lemma mk_musl : forall M M' q, mk_ok M M' q -> amusl0 M -> amusl0 M'.
  Proof.
    intros M M' q HK MU. pose proof (mk_q _ _ _ HK) as (QE & Q1 & Q2).
    eapply amusl0_frame; [exact MU | exact (mk_munch _ _ _ HK) | exact (mk_wmono _ _ _ HK) |].
    intros x Hx. unfold alibx_ok in Hx. cbn. lia.
  Qed.

  (* an argument string: its bytes are at or above the entry's stack pointer, above the byte *)
  Lemma mk_str : forall M M' q sp0 p s, mk_ok M M' q -> 0x10007fff8000 <= bv_unsigned sp0 ->
    astr_at M sp0 p s -> astr_at M' sp0 p s.
  Proof.
    intros M M' q sp0 p s HK Hsp (S1 & S2 & S3 & S4 & t8 & S5).
    split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split.
    - eapply mk_rdn; [exact HK | lia | cbn [length]; lia | right; lia | exact S4].
    - exists t8. eapply mk_rdn; [exact HK | lia | cbn [length]; lia | right; lia | exact S5].
  Qed.
End Marker.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit.
  Variable KH : mctx -> asr.
  Variable KS0 : forall k : mctx, as_St (KH k).
  Variable KB : mctx -> Z.
  Variable L : HeapCeil -> alib.
  (* the launch's vDSO pair at [k]: the vvar entry [Kvlo, Kvb) and the text entry [Kvb, Kvhi) *)
  Variables Kvlo Kvb Kvhi : mctx -> Z.
  (* the instance's visible memory: the main entry's view [KVM] with the marker byte at [KQ]
     opened (As/AS_InstanceKit.v [KM], the shadow byte of the vDSO text) *)
  Variable KM : mctx -> word -> option byte.
  Variable KQ : mctx -> Z.
  Hypothesis K_mem : forall k, @mk_ok (KCEIL k) (KVM k) (KM k) (KQ k).
  Hypothesis K_rt : forall k, @asan_rt_hyps_x (KCEIL k) (KH k).   (* [comment removed for export] *)
  Hypothesis K_ifacts : forall k, @ainst_facts (KCEIL k) (KH k).  (* [comment removed for export] *)
  (* the run's driver laws, over the tail the launch maps *)
  Hypothesis K_dl : forall k, asan_driver_laws_run (vdso_segments (in_kernel (k_inp k)) (k_sp0 k) (k_mbase k))
                                (Kvlo k) (Kvb k) (Kvhi k) (KH k).
  Hypothesis K_live : forall k, ADRV_LIVE <= as_LIVE_MAX (KH k) /\ ADRV_CNT <= as_LIVE_CNT_MAX (KH k).
  (* the three tail statements at the instance (at the run instance, As/AsTailsRun.v's lifts) *)
  Hypothesis K_tails : forall k, @atail_usage_stmt (KCEIL k) (KH k) (L (KCEIL k))
                              /\ @atail_open_stmt (KCEIL k) (KH k) (L (KCEIL k))
                              /\ @atail_rderr_stmt (KCEIL k) (KH k) (L (KCEIL k)).
  Hypothesis K_vis : forall k, as_VIS (KH k) (KS0 k) (cfg_ms (Kcfg k)) = mkst (k_R k) (Z_to_bv 64 A_MAIN) (KM k) (seg_rom asegs).
  Hypothesis K_krel : forall k, as_AKREL (KH k) (KS0 k) (Kcfg k).
  Hypothesis K_rfs : forall k, as_RFS (KH k) [] (KM k).
  Hypothesis K_heap : forall k, as_RHEAP (KH k) (KS0 k) [] (KM k).
  Hypothesis K_aux : forall k, as_rauxv_ok (KH k) (KM k) (KB k) /\ bv_unsigned (k_sp0 k) <= KB k < 2 ^ 64 /\ @aauxv_ok (KCEIL k) (KM k) (KB k).   (* [comment removed for export] *)
  Hypothesis K_al : forall k, AMAIN_COST (KH k) (L (KCEIL k)) <= as_AL (KH k) (KS0 k).
  Hypothesis K_tr : forall k, adrv_traces (KH k) (L (KCEIL k)).
  Hypothesis K_lok : forall HC : HeapCeil, alib_ok (L HC).
  Hypothesis K_libx0 : forall (HC : HeapCeil) iv, In iv (al_LIBX0 (L HC)) -> img_check (fst iv) (snd iv) = true.

  Theorem instance_of_kit : as_instance_stmt EAsChainRun.P_mainK L.
  Proof.
    intros sp0 brk0 mbase rdraw inp c [P [PK PP]].
    destruct (P_main_open sp0 brk0 mbase rdraw inp c P) as (h & ch & E & R & FULL & model & Vsp & Vbrk & Vav & Vev & Vfit & Hh & HC & Hc & HF & PMx & SOK & LZ & PG & MC & VMEQ).
    (* #38: the launch's mmap base is valid, from [P_main]'s first conjunct *)
    pose proof (proj1 (AsMainState.P_main_H sp0 brk0 mbase rdraw inp c P)) as (_ & _ & Vmb & _).
    assert (PKm : kern_ok (in_kernel inp) mbase model) by (rewrite Hc in PK; exact PK).
    assert (PPm : EAsChainRun.vcm_run inp sp0 mbase (cfg_of ASEGS R A_MAIN FULL model)) by (rewrite Hc in PP; exact PP).
    set (k := MCTX sp0 brk0 rdraw inp mbase h ch E R FULL model Vsp Vmb Vbrk Vav Vev Vfit Hh HC PKm PPm).
    destruct (AsMainIfacePre.pre_can sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [can Hcan].
    exists (KCEIL k), (KH k), (Kvlo k), (Kvb k), (Kvhi k), (KS0 k), R, (KM k), (KB k), (ps_tid (KX k)), can.
    split; [exact (K_rt k)|]. split; [exact (K_ifacts k)|]. split; [exact (K_dl k)|]. split; [exact (K_live k)|].
    split; [exact (K_tails k)|].
    assert (Hcfg : c = Kcfg k) by exact Hc.
    split.
    2:{ rewrite Hcfg. cbn [Kcfg cfg_of cfg_model]. exact (AsMainIfacePre.pre_fs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC). }
    pose proof (AsMainIfacePre.pre_regs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (R1 & R2 & R4 & R10 & R11).
    pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    (* the marker byte: where it lies, and that the entry's view and the kit's differ only there *)
    pose proof (mk_q _ _ _ (K_mem k)) as (QE & Q1 & Q2).
    rewrite Hcfg. unfold Kcfg, cfg_of. cbn [cfg_ms cfg_model].
    split.
    - (* [comment removed for export] *) exact (K_vis k).
    - (* [comment removed for export] *) exact (K_krel k).
    - exact R1.
    - exact R2.
    - exact R4.
    - exact R10.
    - exact R11.
    - exact Vsp.
    - (* [comment removed for export] *) cbn [KCEIL main_ceil hceil k k_sp0]. lia.
    - (* the entry's stack view, framed over the marker *)
      eapply (mk_stk _ _ _ _ _ (K_mem k)); [unfold AMLO, ATR_STACK; lia | lia |].
      apply (AsMainIfacePre.pre_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC); unfold AMLO, ATR_STACK; cbn [KCEIL main_ceil hceil k k_sp0]; lia.
    - (* [comment removed for export] *)
      eapply (mk_sh0 _ _ _ _ (K_mem k)).
      apply (AsMainIfacePre.pre_sh0 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC (KCEIL k) eq_refl).
      pose proof (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (PD1 & PD2 & PD3).
      unfold AMLO, ATR_STACK. lia.
    - (* [comment removed for export] *)
      intros i s Hi Hnth.
      destruct (AsMainIfaceArgs.pre_args sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC i s Hi Hnth) as [p [Hp Hstr]].
      exists p. split.
      + eapply (mk_rdn _ _ _ _ _ _ (K_mem k)); [lia | lia | right; lia | exact Hp].
      + eapply (mk_str _ _ _ _ _ _ (K_mem k)); [lia | exact Hstr].
    - exact (mk_inv _ _ _ (K_mem k) (AsMainIfacePre.pre_inv sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC)).
    - unfold arelro_none. eapply (mk_none _ _ _ _ _ (K_mem k)); [lia | lia |].
      exact (AsMainIfacePre.pre_relro sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - destruct (AsMainIfacePre.pre_glb sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) as [G1 G2].
      split.
      + eapply (mk_none _ _ _ _ _ (K_mem k)); [lia | lia | exact G1].
      + eapply (mk_none_h _ _ _ _ _ _ _ (K_mem k)); [lia | lia | exact G2].
    - exact (mk_ac _ _ _ (K_mem k) (AsMainIfaceConst.aconst_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC)).
    - eapply (mk_cells _ _ _ _ (K_mem k));
        [ vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)
        | exact (AsMainIfacePre.pre_cells sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) ].
    - eapply (mk_cells _ _ _ _ (K_mem k));
        [ vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)
        | exact (AsMainIfacePre.pre_out sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) ].
    - destruct (AsMainIfacePre.pre_tid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [T1 T2].
      split; [| exact T2]. eapply (mk_rdn _ _ _ _ _ _ (K_mem k)); [lia | lia | left; lia | exact T1].
    - destruct (AsMainIfacePre.pre_errno sp0 brk0 inp h E FULL) as [e Herr].
      exists e. eapply (mk_rw _ _ _ _ _ (K_mem k)); [unfold AERRNO, ATP; lia | cbn [cells_size csize]; unfold AERRNO, ATP; lia | exact Herr].
    - destruct Hcan as [C1 C2]. split; [| exact C2].
      eapply (mk_rdn _ _ _ _ _ _ (K_mem k)); [lia | lia | left; lia | exact C1].
    - (* [comment removed for export] *) exact (K_rfs k).
    - (* [comment removed for export] *)
      eapply (mk_cells _ _ _ _ (K_mem k));
        [ vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)
        | exact (AsMainIfacePre.pre_reg sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) ].
    - (* [comment removed for export] *)
      intros i Hi.
      pose proof (AsMainIfacePre.pre_lib sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC (al_LIBX0 (L (KCEIL k))) (K_libx0 (KCEIL k)) i Hi) as LN.
      pose proof (alo_libx (L (KCEIL k)) (K_lok (KCEIL k)) i (alo_sub (L (KCEIL k)) (K_lok (KCEIL k)) i Hi)) as LX.
      eapply (mk_none1 _ _ _ _ (K_mem k)); [unfold alibx_ok in LX; lia | exact LN].
    - (* [comment removed for export] *) pose proof (AsMainIfacePre.pre_lib sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC [(0xba9de0, 0xba9de1); (ACLEANUP, ACLEANUP + 1)]%Z
                       ltac:(intros iv Hin; cbn [In] in Hin; destruct Hin as [<-|[<-|[]]]; vm_compute; reflexivity)) as PL.
      split; eapply (mk_none1 _ _ _ _ (K_mem k));
        [ lia | apply PL; cbn; unfold ACLEANUP; lia | unfold ACLEANUP; lia | apply PL; cbn; unfold ACLEANUP; lia ].
    - (* [comment removed for export] *) exact (K_heap k).
    - (* [comment removed for export] *) exact (K_aux k).
    - (* [comment removed for export] *) exact (K_al k).
    - (* [comment removed for export] *) exact (K_tr k).
    - exact (AsMainIfacePre.pre_fds sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    - (* 08b1429: the launch's channel reader *)
      exact (AsMainIfacePre.pre_rdr sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    - (* [comment removed for export] *)
      eapply (mk_musl _ _ _ (K_mem k)).
      apply (AsMainIfaceConst.cellrows_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC AMUSL0_CELLS).
      vm_cast_no_check (@eq_refl bool true).
  Qed.
End Kit.
