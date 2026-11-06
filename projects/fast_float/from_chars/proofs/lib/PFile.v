(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StoreOk MemSplit DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require SysNodesCfg AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.SysNodesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxPlan FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PLoop2 PLoop3 PLoop4 PRefused PDrvHeapI PHeapIGlue Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section FP.
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
Hypothesis HSTATR : forall x, RSX x -> ioutside STATIC x.
Variable HeapI : hi_HS HI -> (word -> option byte) -> Model -> Prop.
Variable INIT : hi_HS HI -> list ivl.
Hypothesis HOKI : heap_init_ok PSEGS DCFG HI HeapI INIT (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) HTOP CELLS_NE 0x51310 8192.
Hypothesis HOWNI : forall hs m md, HeapI hs m md -> forall x, ~ ioutside (hi_owned HI hs) x ->
  0 <= x < HTOP /\ (~ ioutside STATIC x \/ x < IMG_LO \/ IMG_END <= x).
Hypothesis HERRI : forall hs m m' md, HeapI hs m md -> munch ERRC m m' -> mem_grows m m' -> HeapI hs m' md.
Hypothesis HCELLI : forall hs m m' md, HeapI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> HeapI hs m' md.
Variable data : list byte.
Variable fs0 : Fs.Fs.
Hypothesis Hlk : fs_lookup fs0 (nth 1 av []) = Some data.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation a1s := (nth 1 av []).
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation HEAPX' := (HEAPX IMG_LO IMG_END HTOP STATIC).
Local Notation LHEAD' := (LHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation FDF' := (FDF av).
Local Notation seg_xfer' := (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).
Local Notation avoid_m2' := (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI).
Local Notation blk_out' := (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HI HOK).
Local Notation mfxr_chg' := (mfxr_chg sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC).

Local Notation CHEAD' := (CHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation loop_all' := (loop_all sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI HMV HSTATR data fs0 Hlk).
Local Notation refused_path' := (refused_path sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HSTATX HI HNL data fs0).
Local Notation heap_fx' := (heap_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).
Local Notation mfxr_munch' := (mfxr_munch sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC HI HOK).
Local Notation heap_fx_init' := (heap_fx_init sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HSTATI HeapI INIT HOKI HOWNI HERRI HCELLI).
Local Notation mfxr_munch_init' := (mfxr_munch_init sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC HI HOK HeapI HOWNI).

#[using="Type"] Lemma fdf0_eq : forall f, m_fds (with_fds (fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 0))) f) = FDF' 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros f. rewrite with_fds_fds. reflexivity. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HMV HSTATR HOKI HOWNI HERRI HCELLI Hlk"] Theorem file_path : forall model E2 ms2 hs0,
  m_halted model = None -> m_vm_lazy model = [] -> m_fs model = fs0 -> U model <= UB0 ->
  agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 -> ms_rom ms2 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) ->
  HeapI hs0 (ms_mem ms2) (with_fds (fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 0))) model) -> INITO sp0 av ev HI INIT hs0 ->
  (forall E3 ms3 md3 hs3 len3 cap3 buf3, CHEAD' E3 ms3 md3 hs3 len3 cap3 buf3 -> realizes PSEGS (mkCfg ms3 md3) (t_body data fs0)) ->
  realizes PSEGS (mkCfg ms2 (with_fds (fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 0))) model)) (t_body data fs0).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HMV HSTATR HOKI HOWNI HERRI HCELLI Hlk : LiaFast.U) => LiaFast.u0).
  intros model E2 ms2 hs0 Hh Hl Hfs HU0 Ha2 Hd2 Hrom2 Hmf2 Hheap Hio KC.
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al. pose proof HIMG as [HI1 HI2].
  pose proof HOK as ((HB1 & HB2) & _ & _ & HFRAME & HBLK).
  set (md0 := with_fds (fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 0))) model) in *.
  assert (Hh0 : m_halted md0 = None) by (unfold md0; rewrite with_fds_halted; exact Hh).
  assert (Hl0 : m_vm_lazy md0 = []) by (unfold md0; rewrite with_fds_lazy; exact Hl).
  assert (Hm2 : MFXR' (ms_mem ms2)) by exact (mfxr_of_mf sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC _ Hmf2).
  (* [comment removed for export] *)
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_ofd LF1 E2 ms2 md0 _ TBL_P_ok IMG_P_ok cert_LF1 Hd2 ltac:(vm_compute; reflexivity) Hh0 Hl0).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LF1_eq in HIn. destruct HIn as [<-|[]].
  assert (Ha3 : agree 200 E E3) by (intros x Hx; etransitivity; [exact (Ha2 x Hx) | apply Ha23; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
  assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha3 x Hx)).
  rewrite Hrom2 in Hrom3.
  pose proof (heap_fx_init' E2 E3 U_ofd Lf1 ms2 ms3 hs0 md0 Ha2 Ha3 ltac:(vm_compute; reflexivity) Hd2 Hd3 ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hfr3 Hgr3 Hheap Hio) as Hh3.
  assert (Hm3 : MFXR' (ms_mem ms3)) by exact (mfxr_fx sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC E2 U_ofd _ _ Ha2 ltac:(vm_compute; reflexivity) Hfr3 Hm2).
  assert (R1 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x2268c) by (apply (getr_leaf_c PSEGS E3 Lf1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
  { rewrite (getr_leaf PSEGS E3 Lf1 ms3 2 (laddc SP0 (-128)) Hd3) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity. }
  assert (R3 : getr (ms_regs ms3) 3 = Z_to_bv 64 0x10800) by (apply (getr_leaf_c PSEGS E3 Lf1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R4 : getr (ms_regs ms3) 4 = Z_to_bv 64 0x75bd0) by (apply (getr_leaf_c PSEGS E3 Lf1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms3) 10 = Z_to_bv 64 65536) by (apply (getr_leaf_c PSEGS E3 Lf1); [exact Hd3 | vm_compute; reflexivity]).
  apply (fx_malloc_init HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK HeapI INIT HOKI HOWNI E3 Lf1 ms3 md0 hs0 65536 0 7 57216
           (bv_unsigned sp0 - 128) (rgn Lf1 7) _ Hd3 eq_refl eq_refl Hrom3 hok_f1 (rgn_eq Lf1 7 ltac:(vm_compute; lia))
           ltac:(replace (rg_base (rgn Lf1 7)) with (lconst 0x75b28) by (vm_compute; reflexivity); apply u_lconst; lia)
           Hh3 (conj Hh0 Hl0) ltac:(unfold md0; rewrite U_with_fds; unfold MCHARGE, UBOUND, UB0 in *; lia) R10 ltac:(lia) ltac:(rewrite R1; vm_compute; reflexivity) R3 R4 R2 ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
  - apply (frame_sp sp0 SL SH E3 Lf1 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity.
  - exact (avoid_m2' E3 (s_rgs Lf1) Ha3 ltac:(vm_compute; reflexivity)).
  - intros x Hx. destruct (Hio x Hx) as [Hx1 _]. lia.
  - intros E4 ms4 md4 hs4 p Ha34 Hd4 Hrom4 Hh4 Hmd4 Hvo HU4 H10' Hp16 Hadd Hnin Hmunch Hcells4.
    destruct Hmd4 as [Hh4l Hl4l].
    rewrite R1 in Hd4. replace (bv_unsigned (Z_to_bv 64 0x2268c)) with 0x2268c in Hd4 by (vm_compute; reflexivity).
    rewrite Hrom3 in Hrom4.
    assert (Ha4 : agree 200 E E4) by (intros x Hx; etransitivity; [exact (Ha3 x Hx) | apply Ha34; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    destruct (HBLK hs4 (ms_mem ms4) md4 Hh4) as (HBL4 & _).
    assert (Hpin : In (p, 65536) (hi_blocks HI hs4)) by (apply Hadd; left; reflexivity).
    destruct (HBL4 p 65536 Hpin) as (_ & Hpr & _).
    assert (Hd4' : sden PSEGS E4 U_f2 ms4).
    { rewrite <- U_f2_eq. apply fx_add_fact; [exact Hd4 | vm_compute; reflexivity |].
      cbn [fact_ok]. rewrite <- (getr_leaf PSEGS E4 _ ms4 10 (lvar (NXF1 + 10)) Hd4) by (vm_compute; reflexivity).
      rewrite H10', u_small64 by (unfold two64; destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia).
      destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia. }
    assert (Hm4 : MFXR' (ms_mem ms4)).
    { apply (mfxr_munch_init' hs0 hs4 (ms_mem ms3) (ms_mem ms4) md0 md4 _ Hh3 Hh4 Hmunch); [|exact Hm3].
      intros x Hx. cbn [ioutside] in Hx.
      assert (Hx' : (p <= x < p + 65536) \/ (bv_unsigned sp0 - 128 - 8192 <= x < bv_unsigned sp0 - 128)) by
        (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
      destruct Hx' as [Hx'|Hx']; [left; split; [destruct Hpr as [Hpr|Hpr]; lia|] | right; lia].
      destruct Hpr as [Hpr|Hpr]; [right; left; lia | right; right; lia]. }
    (* [comment removed for export] *)
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SL1 U_f2 LF2 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LF2 Hd4' ltac:(vm_compute; reflexivity) Hh4l Hl4l).
    intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 Hgr5. rewrite LF2_eq in HIn. destruct HIn as [<-|[]].
    assert (Ha5 : agree 200 E E5) by (intros x Hx; etransitivity; [exact (Ha4 x Hx) | apply Ha45; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    rewrite Hrom4 in Hrom5.
    pose proof (heap_fx' E4 E5 U_f2 Lfirst ms4 ms5 hs4 md4 Ha4 Ha5 ltac:(vm_compute; reflexivity) Hd4' Hd5 ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hfr5 Hgr5 Hh4) as Hh5.
    assert (Hm5 : MFXR' (ms_mem ms5)) by exact (mfxr_fx sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC E4 U_f2 _ _ Ha4 ltac:(vm_compute; reflexivity) Hfr5 Hm4).
    pose proof (entails_sden PSEGS E5 Lfirst LOOPT sig_first ms5 (sden_0 _ _ _ _ Hd5) ent_first LOOPT_wf) as Hd6.
    set (E6 := ecomp E5 sig_first) in *.
    assert (Ha56 : agree 200 E5 E6) by exact (fixed_below_agree E5 sig_first 200 ltac:(vm_compute; reflexivity)).
    assert (HB6 : E6 BUF = Z_to_bv 64 p).
    { unfold E6, ecomp. replace (svar sig_first BUF) with (lvar (NXF1 + 10)) by (vm_compute; reflexivity). rewrite lden_lvar.
      rewrite <- (Ha45 (NXF1 + 10)%positive) by (vm_compute; reflexivity). rewrite <- H10'.
      rewrite (getr_leaf PSEGS E4 _ ms4 10 (lvar (NXF1 + 10)) Hd4) by (vm_compute; reflexivity). rewrite lden_lvar. reflexivity. }
    apply (loop_all' (t_body data fs0) KC (fun E7 ms7 md7 hs7 H => refused_path' E7 ms7 md7 hs7 H) E6 ms5 md4 hs4 0 65536 p).
    split; [intros x Hx; etransitivity; [exact (Ha5 x Hx) | exact (Ha56 x Hx)]|].
    split; [exact Hd6|]. split; [exact Hrom5|].
    split; [unfold E6, ecomp; replace (svar sig_first N0) with (lconst 0) by (vm_compute; reflexivity); apply lden_lconst|].
    split; [unfold E6, ecomp; replace (svar sig_first C0) with (lconst 65536) by (vm_compute; reflexivity); apply lden_lconst|].
    split; [exact HB6|]. split; [exact Hm5|]. split; [exact Hh5|]. split; [exact Hh4l|]. split; [exact Hl4l|].
    split; [rewrite (vm_only_fds md0 md4 Hvo); apply fdf0_eq|]. split; [rewrite (vm_only_fs md0 md4 Hvo); unfold md0; rewrite with_fds_fs; exact Hfs|].
    split; [exact Hpin|]. split; [apply bytes_at_nil; destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia|].
    split; [lia|]. split; [lia|]. split; [exists 0%nat; split; [lia | reflexivity]|].
    exists 0%nat. split; [lia|]. split; [reflexivity|]. unfold md0 in HU4. rewrite U_with_fds in HU4. unfold MCHARGE, UB0 in *. lia.
Qed.

End FP.
