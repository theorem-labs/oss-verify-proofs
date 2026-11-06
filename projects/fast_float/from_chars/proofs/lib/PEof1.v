(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From Ltac2 Require Import Ltac2 Constr Std Control.
Set Default Proof Mode "Classic".
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
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvCall2 RefStdioDefs RefExitBase PUsageCert POpenCert POpen1 PDirCert PUsage3 PUsage4 PDir PLoopCert PLoopInv PLoop1 PLoop2 PLoop3 PLoop4 PRefused PEofCert PDrvExit2 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section E1.
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
Local Notation INVR' := (INVR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation invr_fx' := (invr_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HIMG).
Local Notation invr_sw' := (invr_sw sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC).
Local Notation exit_glob_of_MFXR' := (exit_glob_of_MFXR sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HSTATX).
Local Notation heap_fx' := (heap_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).
Local Notation mfxr_munch' := (mfxr_munch sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC HI HOK).

#[using="Type"] Lemma fdc_eq : forall len, fd_remove (FDF' len) (Z_to_bv 64 3) = FDS0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros len. unfold FDF, fd_insert, fd_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb]. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="av Hargc2 IMG_LO IMG_END STATIC HIMG HOK HSTATI"] Lemma heap_sw : forall hs m m' md su f bufp bufsz, hi_Heap HI hs m md -> sw_post m su f bufp bufsz m' ->
  HTOP <= su - 112 -> su <= 2 ^ 64 -> (f = 0x64e20 \/ f = 0x64f10) -> hi_Heap HI hs m' md.
Proof. LiaFast.lf_pins (fun (av Hargc2 IMG_LO IMG_END STATIC HIMG HOK HSTATI : LiaFast.U) => LiaFast.u0).
  intros hs m m' md su f bufp bufsz Hh Hp Hs1 Hs2 Hf. pose proof HIMG as [HI1 HI2].
  pose proof HOK as (_ & _ & _ & HFRAME & HBLK).
  apply (HFRAME hs m m' md [(su - 112, su); (f + 32, f + 64)] Hh).
  - intros x Hx. cbn [ioutside] in Hx. apply (swp_agree _ _ _ _ _ _ Hp x); lia.
  - exact (swp_grows _ _ _ _ _ _ Hp).
  - intros x Hx. destruct (HIface.outside_dec (hi_owned HI hs) x) as [A|A]; [exact A|]. exfalso.
    destruct (HBLK hs m md Hh) as (_ & Hown). destruct (Hown x A) as (O1 & O2).
    cbn [ioutside] in Hx.
    assert (Hx' : su - 112 <= x < su \/ f + 32 <= x < f + 64) by (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
    destruct Hx' as [Hx'|Hx']; [lia|].
    assert (Hst : ioutside STATIC x).
    { apply HSTATI; [cbn [ioutside IMGIV]; intros Hq; repeat (destruct Hq as [?Hq Hq]); lia | cbn [ioutside CELLS_NE ERRC app]; repeat split; lia]. }
    destruct O2 as [O2|[O2|O2]]; [exact (O2 Hst) | lia | lia].
Qed.

Definition MSG_SH : list byte := s2b "cli: input shorter than header" ++ nl.
#[using="Type"] Lemma msg_sh_eq : msg_short = MSG_SH. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma tail_0 : forall (bs : list byte) fs,
  t_eq (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ bs)) (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs)))
       (t_emit (W 2 bs) (t_exit (exit_code 2) fs)).
Proof. LiaFast.lf_pins LiaFast.u0. intros bs fs. rewrite app_nil_l, <- (app_nil_r bs) at 1. apply tail_1. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI"] Theorem short_path : forall E1 ms md hs cap buf,
  agree 200 E E1 -> sden PSEGS E1 Lsh ms -> ms_rom ms = seg_rom PSEGS -> E1 BUF = Z_to_bv 64 buf ->
  MFXR' (ms_mem ms) -> hi_Heap HI hs (ms_mem ms) md -> m_halted md = None -> m_vm_lazy md = [] ->
  m_fds md = FDS0 -> m_fs md = fs0 -> In (buf, cap) (hi_blocks HI hs) ->
  realizes PSEGS (mkCfg ms md) (t_die msg_short fs0).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs cap buf Ha1 Hd1 Hrom1 HB1 Hm1 Hh1 Hhd Hld Hfd Hfs Hblk.
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al. pose proof HIMG as [HI1 HI2].
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh1) as (HBL & _). destruct (HBL buf cap Hblk) as (_ & Hbr & _).
  rewrite msg_sh_eq. unfold t_die. rewrite <- Hfs.
  assert (HI1r : INVR' (ms_mem ms)) by (split; [exact Hm1 | exact (HNL hs (ms_mem ms) md Hh1)]).
  assert (Hfd2d : fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite Hfd; vm_compute; reflexivity).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  assert (HS1 : lden E1 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE1 by lia; reflexivity).
  assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x53f54) by (apply (getr_leaf_c PSEGS E1 Lsh); [exact Hd1 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms) 2 = Z_to_bv 64 (bv_unsigned sp0 - 192)).
  { rewrite (getr_leaf PSEGS E1 Lsh ms 2 (laddc SP0 (-192)) Hd1) by (vm_compute; reflexivity). apply (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E1 (-192) HE1). lia. }
  assert (R10 : getr (ms_regs ms) 10 = Z_to_bv 64 0x64e20) by (apply (getr_leaf_c PSEGS E1 Lsh); [exact Hd1 | vm_compute; reflexivity]).
  assert (R11 : getr (ms_regs ms) 11 = Z_to_bv 64 0x12bd3) by (apply (getr_leaf_c PSEGS E1 Lsh); [exact Hd1 | vm_compute; reflexivity]).
  assert (R12 : getr (ms_regs ms) 12 = Z_to_bv 64 31) by (apply (getr_leaf_c PSEGS E1 Lsh); [exact Hd1 | vm_compute; reflexivity]).
  assert (F40 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x64e20 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x962a0))).
  { rewrite (rdn_trk_c E1 Lsh ms 5 0x64e20 40 8 (bks 0x962a0 8) Hd1
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F56 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x64e20 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x962a0))).
  { rewrite (rdn_trk_c E1 Lsh ms 5 0x64e20 56 8 (bks 0x962a0 8) Hd1
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F88 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x64e20 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x962a0))).
  { rewrite (rdn_img_c E1 Lsh ms 5 0x64e20 88 8 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F96 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x64e20 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
  { rewrite (rdn_img_c E1 Lsh ms 5 0x64e20 96 8 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F120 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x64e20 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
  { rewrite (rdn_img_c E1 Lsh ms 5 0x64e20 120 4 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F48 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x64e20 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
  { rewrite (rdn_img_c E1 Lsh ms 5 0x64e20 48 8 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (SWF : sw_file (ms_mem ms) 0x64e20 0x962a0 0x962a0 2 (Z_to_bv 64 0x962a0) (Z_to_bv 64 0)) by (constructor; assumption).
  assert (SSP : ssp_cells (ms_mem ms) (lden E1 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x63da0) with (Z_to_bv 64 (0x63c60 + 320)) by reflexivity.
      rewrite (rdn_img_c E1 Lsh ms 3 0x63c60 320 8 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x95e40) with (Z_to_bv 64 (0x95e40 + 0)) by reflexivity.
      rewrite (rdn_trk_c E1 Lsh ms 8 0x95e40 0 8 (bvs_of (lvar 5) 8) Hd1
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (RDE : rdn PSEGS (ms_mem ms) (Z_to_bv 64 0x12bd3) (length MSG_SH) = Some MSG_SH).
  { replace (Z_to_bv 64 0x12bd3) with (Z_to_bv 64 (0x12bcd + 6)) by reflexivity.
    rewrite (rdn_img_c E1 Lsh ms 17 0x12bcd 6 (length MSG_SH) Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(left; vm_compute; reflexivity) ltac:(change (length MSG_SH) with 31%nat; rszv; lia)
               ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (FRM : frame_in E1 Lsh 0 65232 112 (bv_unsigned sp0 - 192 - 112)).
  { apply (frame_sp sp0 SL SH E1 Lsh 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS1 | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia]. }
  assert (HWF : state_wf (sw_template Lsh (bv_unsigned (Z_to_bv 64 0x53f54)) 0 65232 5 (lconst 0x962a0) (lconst 0) (lconst 31)) = true).
  { rewrite u_small64 by (unfold two64; lia). rewrite U_sh2_eq. exact wf_sh2. }
  apply (rzc_conseq PSEGS DCFG _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ MSG_SH)) (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs md)))));
    [| apply tail_0].
  apply (fx_stdio_write E1 Lsh ms md _ (bv_unsigned sp0 - 192) 0x64e20 0x962a0 0x962a0 2
           (Z_to_bv 64 0x12bd3) (Z_to_bv 64 31) (Z_to_bv 64 0x962a0) (Z_to_bv 64 0) (lden E1 (lvar 5)) (Z_to_bv 64 0x53f54) [] MSG_SH
           0 65232 5 (rgn Lsh 5) (lconst 0x962a0) (lconst 0) (lconst 31)
           Hd1 eq_refl eq_refl Hrom1 hok_sh HWF FRM (rgn_eq Lsh 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) R2 R10 R11 R12 R1); try lia.
  + exact SWF.
  + exact SSP.
  + exact F48.
  + exact Hfd2d.
  + exact Hhd.
  + exact Hld.
  + unfold TASK_SIZE. lia.
  + reflexivity.
  + rewrite u_small64 by (unfold two64; lia). reflexivity.
  + cbn [length]. replace (length MSG_SH) with 31%nat by reflexivity. lia.
  + cbn [length]. replace (length MSG_SH) with 31%nat by reflexivity. lia.
  + left. rewrite !u_small64 by (unfold two64; lia). lia.
  + rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE. lia.
  + reflexivity.
  + exact RDE.
  + vm_compute. reflexivity.
  + apply t_emit_has_nil.
  + apply lden_lconst.
  + apply lden_lconst.
  + apply lden_lconst.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + intros E2 ms2 Ha12 Hd2 Hpost2 Hrom2.
    rewrite u_small64 in Hd2 by (unfold two64; lia). rewrite U_sh2_eq in Hd2.
    assert (Ha2 : agree 200 E E2) by (intros x Hx; etransitivity; [exact (Ha1 x Hx) | apply Ha12; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (HJ2 : INVR' (ms_mem ms2)) by exact (invr_sw' (ms_mem ms) (ms_mem ms2) _ _ _ Hpost2 ltac:(lia) ltac:(lia) HI1r).
    assert (Hh2 : hi_Heap HI hs (ms_mem ms2) md) by exact (heap_sw hs (ms_mem ms) (ms_mem ms2) md _ _ _ _ Hh1 Hpost2 ltac:(lia) ltac:(lia) ltac:(left; reflexivity)).
    rewrite Hrom1 in Hrom2.
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_sh2 LSH2 E2 ms2 md _ TBL_P_ok IMG_P_ok cert_LSH2 Hd2 ltac:(vm_compute; reflexivity) Hhd Hld).
    intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LSH2_eq in HIn. destruct HIn as [<-|[]].
    assert (Ha3 : agree 200 E E3) by (intros x Hx; etransitivity; [exact (Ha2 x Hx) | apply Ha23; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha3 x Hx)).
    assert (Hh3 : hi_Heap HI hs (ms_mem ms3) md) by exact (heap_fx' E2 E3 U_sh2 Lsh3 ms2 ms3 hs md Ha2 Ha3 ltac:(vm_compute; reflexivity) Hd2 Hd3
                                                          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr3 Hgr3 Hh2).
    assert (HJ3 : INVR' (ms_mem ms3)) by exact (invr_fx' E2 U_sh2 _ _ Ha2 ltac:(vm_compute; reflexivity) Hfr3 HJ2).
    rewrite Hrom2 in Hrom3.
    assert (Q1 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x22834) by (apply (getr_leaf_c PSEGS E3 Lsh3); [exact Hd3 | vm_compute; reflexivity]).
    assert (Q2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
    { rewrite (getr_leaf PSEGS E3 Lsh3 ms3 2 (laddc SP0 (-128)) Hd3) by (vm_compute; reflexivity). apply (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E3 (-128) HE3). lia. }
    assert (Q3 : getr (ms_regs ms3) 3 = Z_to_bv 64 0x10800) by (apply (getr_leaf_c PSEGS E3 Lsh3); [exact Hd3 | vm_compute; reflexivity]).
    assert (Q4 : getr (ms_regs ms3) 4 = Z_to_bv 64 0x75bd0) by (apply (getr_leaf_c PSEGS E3 Lsh3); [exact Hd3 | vm_compute; reflexivity]).
    assert (Q10 : getr (ms_regs ms3) 10 = Z_to_bv 64 buf).
    { rewrite (getr_leaf PSEGS E3 Lsh3 ms3 10 (lvar BUF) Hd3) by (vm_compute; reflexivity). rewrite lden_lvar.
      rewrite <- (Ha23 BUF) by (vm_compute; reflexivity). rewrite <- (Ha12 BUF) by (vm_compute; reflexivity). exact HB1. }
    apply (fx_free HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK E3 Lsh3 ms3 md hs cap 0 7 57216
             (bv_unsigned sp0 - 128) (rgn Lsh3 7) _ Hd3 eq_refl eq_refl Hrom3 hok_sh3 (rgn_eq Lsh3 7 ltac:(vm_compute; lia))
             ltac:(replace (rg_base (rgn Lsh3 7)) with (lconst 0x75b28) by (vm_compute; reflexivity); apply u_lconst; lia)
             Hh3 (conj Hhd Hld) buf Q10 Hblk ltac:(destruct Hbr as [Hbr|Hbr]; lia) ltac:(rewrite Q1; vm_compute; reflexivity) Q3 Q4 Q2
             ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
    * apply (frame_sp sp0 SL SH E3 Lsh3 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
      unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity.
    * exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI E3 (s_rgs Lsh3) Ha3 ltac:(vm_compute; reflexivity)).
    * intros E4 ms4 md4 hs4 Ha34 Hd4 Hrom4 Hh4 Hmd4 Hvo HU4 Hdel Hmunch Hcells4.
      destruct Hmd4 as [Hh4l Hl4l].
      rewrite Q1 in Hd4. replace (bv_unsigned (Z_to_bv 64 0x22834)) with 0x22834 in Hd4 by (vm_compute; reflexivity).
      assert (Hd4g : sden PSEGS E4 U_sh4 ms4) by (rewrite <- U_sh4_eq; exact Hd4). clear Hd4.
      rewrite Hrom3 in Hrom4.
      assert (Ha4 : agree 200 E E4) by (intros x Hx; etransitivity; [exact (Ha3 x Hx) | apply Ha34; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
      assert (Hm4 : MFXR' (ms_mem ms4)).
      { apply (mfxr_munch' hs hs4 (ms_mem ms3) (ms_mem ms4) md md4 _ Hh3 Hh4 Hmunch); [|exact (proj1 HJ3)].
        intros x Hx. cbn [ioutside] in Hx.
        assert (Hx' : (buf <= x < buf + cap) \/ (bv_unsigned sp0 - 128 - 8192 <= x < bv_unsigned sp0 - 128)) by
          (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
        destruct Hx' as [Hx'|Hx']; [left; split; [destruct Hbr as [Hbr|Hbr]; lia|] | right; lia].
        destruct Hbr as [Hbr|Hbr]; [right; left; lia | right; right; lia]. }
      assert (HJ4 : INVR' (ms_mem ms4)) by (split; [exact Hm4 | exact (HNL hs4 (ms_mem ms4) md4 Hh4)]).
      apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_sh4 LSH4 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LSH4 Hd4g ltac:(vm_compute; reflexivity) Hh4l Hl4l).
      intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 _. rewrite LSH4_eq in HIn. destruct HIn as [<-|[]].
      assert (Ha5 : agree 200 E E5) by (intros x Hx; etransitivity; [exact (Ha4 x Hx) | apply Ha45; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
      assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha5 x Hx)).
      assert (HJ5 : INVR' (ms_mem ms5)) by exact (invr_fx' E4 U_sh4 _ _ Ha4 ltac:(vm_compute; reflexivity) Hfr5 HJ4).
      rewrite Hrom4 in Hrom5.
      rewrite <- (vm_only_fs md md4 Hvo).
      apply (fx_exit E5 Lsh5 ms5 md4 (Z_to_bv 64 2) [] Hd5 eq_refl eq_refl Hrom5).
      assert (FC5 : file_clean (ms_mem ms5) 0x64e20 (Z_to_bv 64 0x962a0) (Z_to_bv 64 0)).
      { split; [|split; [|split; [|split]]].
        - rewrite (rdn_img_c E5 Lsh5 ms5 5 0x64e20 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                     ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
        - rewrite (rdn_trk_c E5 Lsh5 ms5 5 0x64e20 40 8 (bvs_of (lconst 0x962a0) 8) Hd5
                     ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
          rewrite bvs_of_den_lin, lden_lconst. reflexivity.
        - rewrite (rdn_trk_c E5 Lsh5 ms5 5 0x64e20 56 8 (bvs_of (lconst 0x962a0) 8) Hd5
                     ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
          rewrite bvs_of_den_lin, lden_lconst. reflexivity.
        - rewrite (rdn_trk_c E5 Lsh5 ms5 5 0x64e20 8 8 Z8 Hd5
                     ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
        - rewrite (rdn_trk_c E5 Lsh5 ms5 5 0x64e20 16 8 Z8 Hd5
                     ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
      assert (FC6 : file_clean (ms_mem ms5) 0x64f10 (Z_to_bv 64 0) (Z_to_bv 64 0)).
      { split; [|split; [|split; [|split]]];
          [ rewrite (rdn_img_c E5 Lsh5 ms5 6 0x64f10 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                       ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
          | rewrite (rdn_img_c E5 Lsh5 ms5 6 0x64f10 40 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                       ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
          | rewrite (rdn_img_c E5 Lsh5 ms5 6 0x64f10 56 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                       ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
          | rewrite (rdn_img_c E5 Lsh5 ms5 6 0x64f10 8 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                       ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
          | rewrite (rdn_img_c E5 Lsh5 ms5 6 0x64f10 16 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                       ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)) ]; bvlit. }
      apply (exit_pre_gen2 sp0 tid SL SH Htid E5 Lsh5 ms5 md4 (-48) 2 0 3 7 21 65344 (rg_cont (rgn Lsh5 7)) RW (Z_to_bv 64 0x962a0) (Z_to_bv 64 0) [] Hd5).
      -- unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
      -- unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
      -- lia.
      -- lia.
      -- exact (exit_glob_of_MFXR' _ (proj1 HJ5) (proj2 HJ5)).
      -- exact Hh4l.
      -- exact Hl4l.
      -- vm_compute. reflexivity.
      -- vm_compute. reflexivity.
      -- vm_compute. reflexivity.
      -- vm_compute. reflexivity.
      -- vm_compute. reflexivity.
      -- vm_compute. reflexivity.
      -- vm_compute. reflexivity.
      -- apply (frame_sp sp0 SL SH E5 Lsh5 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
         unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
      -- exact FC5.
      -- left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0). exact FC6.
Qed.

(* [comment removed for export] *)
Definition HDHEAD (E2 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf : Z) : Prop :=
  agree 200 E E2 /\ sden PSEGS E2 Lhd ms /\ ms_rom ms = seg_rom PSEGS /\ E2 N0 = Z_to_bv 64 len /\ E2 BUF = Z_to_bv 64 buf /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDS0 /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\ bytes_at PSEGS (ms_mem ms) buf data /\
  len = Z.of_nat (length data) /\ 6 <= len < cap /\ CAPOKU cap md.

Definition FC_hd : fact := Eval vm_compute in nth 0 (s_facts Lhd) (FRange (lconst 0) 0 0).
Definition FC_sh : fact := Eval vm_compute in nth 0 (s_facts Lsh) (FRange (lconst 0) 0 0).
#[using="tid Htid IMG_LO IMG_END HIMG"] Lemma FC_hd_in : In FC_hd (s_facts Lhd). Proof. LiaFast.lf_pins (fun (tid Htid IMG_LO IMG_END HIMG : LiaFast.U) => LiaFast.u0). vm_compute. tauto. Qed.
#[using="tid Htid IMG_LO IMG_END HIMG"] Lemma FC_sh_in : In FC_sh (s_facts Lsh). Proof. LiaFast.lf_pins (fun (tid Htid IMG_LO IMG_END HIMG : LiaFast.U) => LiaFast.u0). vm_compute. tauto. Qed.
#[using="Type"] Lemma FC_hd_eq : FC_hd = FCond BC_GEU (lconst 5) (lvar N0) false. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma FC_sh_eq : FC_sh = FCond BC_GEU (lconst 5) (lvar N0) true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HMV"] Theorem eof_entry : forall E1 ms md hs len cap buf,
  CHEAD' E1 ms md hs len cap buf ->
  (forall E2 ms2 md2, HDHEAD E2 ms2 md2 hs len cap buf -> realizes PSEGS (mkCfg ms2 md2) (t_body data fs0)) ->
  realizes PSEGS (mkCfg ms md) (t_body data fs0).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HMV : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & Hba & HL & Hlen & Hcap) KH.
  pose proof (capoku_bounds cap md Hcap) as Hcb.
  assert (R17 : getr (ms_regs ms) 17 = Z_to_bv 64 57) by (apply (getr_leaf_c PSEGS E1 Lc); [exact Hd1 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms) 10 = Z_to_bv 64 3) by (apply (getr_leaf_c PSEGS E1 Lc); [exact Hd1 | vm_compute; reflexivity]).
  apply (fx_close E1 Lc ms md (FdFile a1s (Z_to_bv 64 len)) _ Hd1 eq_refl eq_refl Hrom1 Hhd Hld R17
           ltac:(rewrite Hfd, R10, fd32_3; unfold FDF, fd_insert; cbn [fd_lookup]; rewrite bv_eqb_refl; reflexivity) hok_c).
  intros E2 ms2 Ha12 Hd2 Hrom2 Hm2'. rewrite U_c_eq in Hd2.
  rewrite R10, fd32_3, Hfd, fdc_eq.
  set (md2 := with_fds FDS0 md).
  assert (Hh2l : m_halted md2 = None) by (unfold md2; rewrite with_fds_halted; exact Hhd).
  assert (Hl2l : m_vm_lazy md2 = []) by (unfold md2; rewrite with_fds_lazy; exact Hld).
  assert (Hh2 : hi_Heap HI hs (ms_mem ms2) md2) by (rewrite Hm2'; apply (HMV hs (ms_mem ms) md md2 Hh1); [reflexivity | exact Hh2l | exact Hl2l]).
  assert (Ha2 : agree 200 E E2) by (intros x Hx; etransitivity; [exact (Ha1 x Hx) | apply Ha12; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
  assert (HE21 : forall x, (x < s_next Lc)%positive -> E2 x = E1 x) by (intros x Hx; symmetry; exact (Ha12 x Hx)).
  assert (Hm2 : MFXR' (ms_mem ms2)) by (rewrite Hm2'; exact Hm1).
  assert (Hba2 : bytes_at PSEGS (ms_mem ms2) buf data) by (rewrite Hm2'; exact Hba).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SHD U_c LC1 E2 ms2 md2 _ TBL_P_ok IMG_P_ok cert_LC1 Hd2 ltac:(vm_compute; reflexivity) Hh2l Hl2l).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3.
  assert (HLc : cells_tmpl L = true) by (rewrite LC1_eq in HIn; destruct HIn as [<-|[<-|[]]]; vm_compute; reflexivity).
  destruct (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI
              E2 E3 U_c L ms2 ms3 hs md2 buf data Ha2 Ha23 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd2 Hd3 ltac:(vm_compute; reflexivity) HLc Hfr3 Hgr3 Hm2 Hh2
              ltac:(exists cap; split; [exact Hblk | lia]) Hba2) as (Ha3 & Hm3 & Hh3 & Hba3).
  rewrite Hrom2 in Hrom3.
  assert (HE32 : forall x, (x < s_next U_c)%positive -> E3 x = E2 x) by (intros x Hx; symmetry; exact (Ha23 x Hx)).
  assert (HN3 : E3 N0 = Z_to_bv 64 len) by (rewrite HE32, HE21 by (vm_compute; reflexivity); exact HN1).
  assert (HB3 : E3 BUF = Z_to_bv 64 buf) by (rewrite HE32, HE21 by (vm_compute; reflexivity); exact HB1).
  rewrite LC1_eq in HIn. destruct HIn as [<-|[<-|[]]].
  - pose proof (sden_fact PSEGS E3 Lhd ms3 _ Hd3 FC_hd_in) as HF. rewrite FC_hd_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_lvar, lden_lconst, HN3 in HF. apply negb_false_iff in HF. unfold bv_ltu in HF. apply Z.ltb_lt in HF.
    rewrite !u_small64 in HF by (unfold two64; lia).
    apply (KH E3 ms3 md2). split; [exact Ha3|]. split; [exact Hd3|]. split; [exact Hrom3|]. split; [exact HN3|]. split; [exact HB3|].
    split; [exact Hm3|]. split; [exact Hh3|]. split; [exact Hh2l|]. split; [exact Hl2l|]. split; [unfold md2; rewrite with_fds_fds; reflexivity|].
    split; [unfold md2; rewrite with_fds_fs; exact Hfs|]. split; [exact Hblk|]. split; [exact Hba3|]. split; [exact HL|]. split; [lia | exact Hcap].
  - pose proof (sden_fact PSEGS E3 Lsh ms3 _ Hd3 FC_sh_in) as HF. rewrite FC_sh_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_lvar, lden_lconst, HN3 in HF. apply negb_true_iff in HF. unfold bv_ltu in HF. apply Z.ltb_ge in HF.
    rewrite !u_small64 in HF by (unfold two64; lia).
    assert (HT : t_body data fs0 = t_die msg_short fs0).
    { unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
      replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    rewrite HT.
    apply (short_path E3 ms3 md2 hs cap buf Ha3 Hd3 Hrom3 HB3 Hm3 Hh3 Hh2l Hl2l ltac:(unfold md2; rewrite with_fds_fds; reflexivity)
             ltac:(unfold md2; rewrite with_fds_fs; exact Hfs) Hblk).
Qed.

End E1.
