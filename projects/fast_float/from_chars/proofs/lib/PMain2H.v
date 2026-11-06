(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StoreOk DriverCfg RefMemcpyLib FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvExit PDrvHeap PDrvHeap2 RefStartup RefStartupDefs PUsageCert POpenCert POpen1 PCant PDirCert PDir PDrvHeapI PLoopInv PHeapIGlue Spec.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert OSSVerify.Proofs.fast_float.from_chars.lib.POpen1 OSSVerify.Proofs.fast_float.from_chars.lib.PCant OSSVerify.Proofs.fast_float.from_chars.lib.PDirCert OSSVerify.Proofs.fast_float.from_chars.lib.PDir OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeapI OSSVerify.Proofs.fast_float.from_chars.lib.PLoopInv OSSVerify.Proofs.fast_float.from_chars.lib.PHeapIGlue OSSVerify.Proofs.fast_float.from_chars.lib.Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Open Scope Z_scope.

Section M2H.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.
Hypothesis Hargc2 : length av = 2%nat.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hl : m_vm_lazy model = [].
Hypothesis Hfds : m_fds model = FDS0.
(* [comment removed for export] *)
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HTOPB : HTOP <= bv_unsigned sp0 - 65536.
Hypothesis HIMG : IMG_LO <= 0x10000 /\ 0x97000 <= IMG_END.
Hypothesis HSTATX : forall x, ~ ioutside EXGX x -> ioutside STATIC x.
Variable HI : heap_iface.
Hypothesis HOK : heap_ok PSEGS DCFG HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.
Hypothesis HNL : forall hs m md, hi_Heap HI hs m md -> NL m.
Hypothesis HSTATI : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC x.
Hypothesis HMV : forall hs m md md', hi_Heap HI hs m md -> m_vmmaps md' = m_vmmaps md -> m_halted md' = None -> m_vm_lazy md' = [] -> hi_Heap HI hs m md'.
(* [comment removed for export] *)
Variable HeapI : hi_HS HI -> (word -> option byte) -> Model -> Prop.
Variable INIT : hi_HS HI -> list ivl.
Hypothesis HOKI : heap_init_ok PSEGS DCFG HI HeapI INIT (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) HTOP CELLS_NE 0x51310 8192.
Hypothesis HOWNI : forall hs m md, HeapI hs m md -> forall x, ~ ioutside (hi_owned HI hs) x ->
  0 <= x < HTOP /\ (~ ioutside STATIC x \/ x < IMG_LO \/ IMG_END <= x).
Hypothesis HERRI : forall hs m m' md, HeapI hs m md -> munch ERRC m m' -> mem_grows m m' -> HeapI hs m' md.
Hypothesis HCELLI : forall hs m m' md, HeapI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> HeapI hs m' md.
Hypothesis HMVI : forall hs m md md', HeapI hs m md -> m_vmmaps md' = m_vmmaps md -> m_halted md' = None -> m_vm_lazy md' = [] -> HeapI hs m md'.
Variable hs_main : hi_HS HI.
Hypothesis HINIT : HeapI hs_main mem model.
Hypothesis HINITO : INITO sp0 av ev HI INIT hs_main.
Hypothesis HU0 : U model <= UB0.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation a1s := (nth 1 av []).

#[using="uid hw mem Hsp Hva Hve ME Hargc2 HTOPB HIMG HSTATI"] Lemma avoid_main2 : forall E' rgs, agree 200 E E' -> shape rgs = shape (s_rgs P_main2) -> avoid_heap3 IMG_LO IMG_END HTOP STATIC E' rgs.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 HTOPB HIMG HSTATI : LiaFast.U) => LiaFast.u0).
  intros E' rgs Ha Hs i R x Hi Hin Hc.
  apply (avoid_od sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI E' (rgs ++ [RPATH]) Ha) with (i := i) (R := R);
    [| | exact Hin | exact Hc].
  - unfold shape. rewrite map_app. change (List.map (fun R0 => (rg_base R0, rg_size R0)) rgs) with (shape rgs). rewrite Hs. vm_compute. reflexivity.
  - rewrite nth_error_app1; [exact Hi|]. apply nth_error_Some. rewrite Hi. discriminate.
Qed.

#[using="uid hw Hsp Hva Hve Hfits Htid ME Hargc2 Hh Hl Hfds IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HOK HNL HSTATI INIT HOKI HOWNI HERRI HCELLI HMVI HINIT HINITO HU0"] Theorem main_argc2H :
  (forall data, path_is_dirref a1s = false -> fs_lookup (m_fs model) a1s = Some data ->
     forall E2 ms2, agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 -> ms_rom ms2 = seg_rom PSEGS ->
     (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) ->
     HeapI hs_main (ms_mem ms2) (with_fds (fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 0))) model) ->
     realizes PSEGS (mkCfg ms2 (with_fds (fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 0))) model)) (t_body data (m_fs model))) ->
  realizes PSEGS (mkCfg (mkst (fx := fx0) regs (Z_to_bv 64 0x22638) mem (seg_rom PSEGS)) model) (spec av (m_fs model)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hfits Htid ME Hargc2 Hh Hl Hfds IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HOK HNL HSTATI INIT HOKI HOWNI HERRI HCELLI HMVI HINIT HINITO HU0 : LiaFast.U) => LiaFast.u0).
  intros KF. pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  assert (Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite Hfds; vm_compute; reflexivity).
  pose proof (handoff2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2) as Hd0.
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 P_main2 LO _ _ model _ TBL_P_ok IMG_P_ok certO Hd0 bases_main2 Hh Hl).
  intros L E1 ms1 HIn Hd1 Ha1 Hrom1 Hfr1 Hgr1. rewrite LO_one in HIn. destruct HIn as [<-|[]].
  cbn [ms_rom mkst] in Hrom1. cbn [ms_mem mkst] in Hfr1, Hgr1.
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  (* [comment removed for export] *)
  assert (Hcel1 : forall a, ~ ioutside CELLS_NE a -> mrd PSEGS (ms_mem ms1) (Z_to_bv 64 a) = mrd PSEGS mem (Z_to_bv 64 a)).
  { intros a Ha. cbn [ioutside CELLS_NE] in Ha.
    assert (Hr : (0x63da0 <= a < 0x63da8) \/ (0x95e40 <= a < 0x95e48)).
    { apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Ha. repeat split; lia. }
    pose proof (sden_0 _ _ _ _ Hd0) as (_ & _ & _ & _ & Hrg0 & _).
    destruct Hr as [Hr|Hr].
    - pose proof (sden_rg _ _ _ _ _ _ Hd1 (rgn_eq L_O 3 ltac:(vm_compute; lia))) as R3.
      destruct R3 as (_ & _ & A3 & _).
      replace (rg_kind (rgn L_O 3)) with RO in A3 by (vm_compute; reflexivity).
      replace (rg_base (rgn L_O 3)) with (lconst 0x63c60) in A3 by (vm_compute; reflexivity).
      rszv_in A3.
      rewrite u_lconst in A3 by lia. destruct (A3 (a - 0x63c60) ltac:(lia)) as [Z3 _].
      replace (0x63c60 + (a - 0x63c60)) with a in Z3 by lia.
      pose proof (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME 0x63c60 344 (a - 0x63c60) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)) as Z0.
      replace (0x63c60 + (a - 0x63c60)) with a in Z0 by lia.
      unfold mrd. rewrite Z3, Z0. reflexivity.
    - pose proof (rdn_trk_c E1 L_O ms1 8 0x95e40 0 8 (bvs_of (lvar 5) 8) Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)
                    ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as X.
      rewrite bvs_of_den_lin, lden_lvar, HE1 in X by lia. change (E 5%positive) with (canary rdraw) in X. rewrite Z.add_0_r in X.
      pose proof (rdn_guard sp0 av ev uid tid hw rdraw regs mem Hsp ME) as Y.
      assert (HY : rdn PSEGS mem (Z_to_bv 64 0x95e40) 8 = Some (Z_to_le_bytes 8 (bv_unsigned (canary rdraw)))).
      { rewrite Y. f_equal. rewrite <- (canary_val rdraw). assert (HL : length (canary_bytes rdraw) = 8%nat) by reflexivity.
        rewrite <- HL at 1. symmetry. apply Z_to_le_bytes_lez. }
      pose proof (rdn_rd1 PSEGS (ms_mem ms1) 0x95e40 8 _ ltac:(lia) ltac:(unfold two64; lia) X (Z.to_nat (a - 0x95e40))) as X1.
      pose proof (rdn_rd1 PSEGS mem 0x95e40 8 _ ltac:(lia) ltac:(unfold two64; lia) HY (Z.to_nat (a - 0x95e40))) as Y1.
      destruct (nth_error (Z_to_le_bytes 8 (bv_unsigned (canary rdraw))) (Z.to_nat (a - 0x95e40))) as [b|] eqn:Hb.
      + specialize (X1 b eq_refl). specialize (Y1 b eq_refl). rewrite Z2Nat.id in X1, Y1 by lia.
        replace (0x95e40 + (a - 0x95e40)) with a in X1, Y1 by lia. unfold rd1 in X1, Y1. unfold mrd. rewrite X1, Y1. reflexivity.
      + exfalso. apply nth_error_None in Hb. rewrite length_Z_to_le_bytes in Hb. lia. }
  assert (Hin1 : forall x, ~ ioutside (INIT hs_main) (bv_unsigned x) -> outside E (s_rgs P_main2) x).
  { intros x Hx. destruct (HINITO _ Hx) as (X1 & X2).
    exact (init_out_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 E (s_rgs P_main2) x (fun _ _ => eq_refl) eq_refl X1 X2). }
  pose proof (heap_seg_init HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HeapI INIT HOKI HOWNI HERRI HCELLI E (s_rgs P_main2) hs_main mem (ms_mem ms1) model
                HINIT Hin1 Hfr1 Hgr1 Hcel1 (avoid_main2 E (s_rgs P_main2) (fun _ _ => eq_refl) eq_refl)) as Hheap1.
  apply (open_node sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 model Hh Hl Hfds E1 ms1 Ha1 Hd1 Hrom1 Hfr1).
  - intros E2 ms2 Ha2 Hd2 Hrom2 Hmf2 _.
    exact (cant_open sp0 av ev uid tid hw rdraw regs mem model Hsp Hva Hve Hfits Htid ME Hargc2 Hh Hl Hfd2 E2 ms2 Ha2 Hd2 Hrom2 Hmf2).
  - intros HDR E2 ms2 Ha2 Hd2 Hrom2 Hmf2 Hm2.
    apply (dir_path sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Hfits Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX
             HI HOK HNL HSTATI HeapI INIT HOKI HOWNI HERRI HCELLI HDR model E2 ms2 hs_main Hh Hl Hfds HU0 Ha2 Hd2 Hrom2 Hmf2).
    + rewrite Hm2. apply (HMVI hs_main (ms_mem ms1) model _ Hheap1); [reflexivity | rewrite with_fds_halted; exact Hh | rewrite with_fds_lazy; exact Hl].
    + exact HINITO.
  - intros data HDR HLK E2 ms2 Ha2 Hd2 Hrom2 Hmf2 Hm2.
    apply (KF data HDR HLK E2 ms2 Ha2 Hd2 Hrom2 Hmf2).
    rewrite Hm2. apply (HMVI hs_main (ms_mem ms1) model _ Hheap1); [reflexivity | rewrite with_fds_halted; exact Hh | rewrite with_fds_lazy; exact Hl].
Qed.
End M2H.
