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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvCall2 PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PEofCert PEof1 PLoopInv2 PEof3 PTgtCert PLoop2 PLoop3 PTgt1 PTgt2 PDrvFuzz PTgt3 PTgt4 PTgt5 PTgt6 PTgtCert2 PDrvExit2 PDrvExit3 PTgt7 PRefused PDrvCall2 RefStdioDefs Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section T8.
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
Hypothesis HFZ : fuzz_contract PSEGS DCFG (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0)
  IMG_LO IMG_END HTOP STATIC CELLS_NE 0x22b18 8496 PRO.
Hypothesis HSRO : forall x, 0x10000 <= x < 0x22000 \/ 0x64de0 <= x < 0x64de4 -> ~ KRO x -> ioutside STATIC x.
Hypothesis HKRO : forall hs m md, hi_Heap HI hs m md -> pristine m 0x16100 0x16120 /\ pristine m 0x182a8 0x18327.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation ITHEAD' := (ITHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation TLHEAD' := (TLHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation EXHEAD' := (EXHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC data fs0).
Local Notation KREST' := (KREST fs0).
Local Notation free_owned_step' := (free_owned_step sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HSTATI data fs0).
Local Notation free_buf_step' := (free_buf_step sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HNL HSTATI data fs0).
Local Notation tl_fx' := (tl_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).
Local Notation ex_fx' := (ex_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HIMG data fs0).
Local Notation tl_ent' := (tl_ent sp0 av ev tid rdraw regs mem Hargc2 IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation exit_glob_of_MFXR' := (exit_glob_of_MFXR sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HSTATX).

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E"] Theorem exit2 : forall E1 ms md, EXHEAD' EX2 E1 ms md -> realizes PSEGS (mkCfg ms md) (KREST' 1).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E : LiaFast.U) => LiaFast.u0).
  intros E4 ms4 md4 HX4. pose proof HX4 as (Ha4 & Hd4 & Hrom4 & _ & _ & _ & Hh4l & Hl4l & _ & Hfs4).
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. destruct ex2_chk as (Gsh & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 EX2 LEX2 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LEX2 Hd4 ltac:(vm_compute; reflexivity) Hh4l Hl4l).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 _. rewrite LEX2_eq in HIn. destruct HIn as [<-|[]].
  pose proof (ex_fx' EX2 XL2 E4 E5 ms4 ms5 md4 HX4 Ha45 Hd5 Hrom5 Hfr5 Gsh Gnx) as HX5.
  destruct HX5 as (Ha5 & _ & Hrom5' & _ & Hm5 & Hnl5 & _ & _ & Hfd5 & _).
  assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha5 x Hx)).
  unfold KREST. rewrite <- Hfs4, <- exit_code0.
  apply (fx_exit E5 XL2 ms5 md4 (Z_to_bv 64 0) (zero_lines 1) Hd5 eq_refl eq_refl Hrom5').
  assert (FC5 : file_clean (ms_mem ms5) 0x64e20 (Z_to_bv 64 0) (Z_to_bv 64 0)).
  { split; [|split; [|split; [|split]]];
      [ rewrite (rdn_img_c E5 XL2 ms5 5 0x64e20 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL2 ms5 5 0x64e20 40 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL2 ms5 5 0x64e20 56 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL2 ms5 5 0x64e20 8 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL2 ms5 5 0x64e20 16 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)) ]; bvlit. }
  assert (SSP : ssp_cells (ms_mem ms5) (lden E5 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x63da0) with (Z_to_bv 64 (0x63c60 + 320)) by reflexivity.
      rewrite (rdn_img_c E5 XL2 ms5 3 0x63c60 320 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x95e40) with (Z_to_bv 64 (0x95e40 + 0)) by reflexivity.
      rewrite (rdn_trk_c E5 XL2 ms5 8 0x95e40 0 8 (bvs_of (lvar 5) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (SP : stdout_pending (ms_mem ms5) 0x962a8 0x962aa (Z_to_bv 64 0x962a8) (Z_to_bv 64 1024) (Z_to_bv 64 0) (lden E5 (lvar 5)) (zero_lines 1)).
  { constructor.
    - rewrite (rdn_img_c E5 XL2 ms5 6 0x64f10 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL2 ms5 6 0x64f10 40 8 (bks 0x962aa 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL2 ms5 6 0x64f10 56 8 (bvs_of (lconst 0x962a8) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, lden_lconst. reflexivity.
    - rewrite (rdn_trk_c E5 XL2 ms5 6 0x64f10 72 8 (bks 0x54050 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL2 ms5 6 0x64f10 88 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL2 ms5 6 0x64f10 96 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL2 ms5 6 0x64f10 120 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL2 ms5 6 0x64f10 8 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL2 ms5 6 0x64f10 16 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - lia.
    - reflexivity.
    - unfold rw_bytes_max. cbn [length zero_lines]. lia.
    - replace (Z_to_bv 64 0x962a8) with (Z_to_bv 64 (0x962a0 + 8)) by reflexivity. cbn [length zero_lines].
      rewrite (rdn_trk_c E5 XL2 ms5 10 0x962a0 8 2 [BK 48; BK 10] Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - exact SSP. }
  apply (exit_pre_gen2r sp0 tid SL SH Htid E5 XL2 ms5 md4 (-48) 0 0 3 7 9 21 65344 (rg_cont (rgn XL2 7)) (rg_cont (rgn XL2 9)) (rg_cont (rgn XL2 21)) RW RI (Z_to_bv 64 0) (Z_to_bv 64 0) (zero_lines 1) Hd5).
  - unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
  - lia.
  - lia.
  - exact (exit_glob_of_MFXR' _ Hm5 Hnl5).
  - exact Hh4l.
  - exact Hl4l.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold c21_reg. repeat split; vm_compute; reflexivity.
  - apply (frame_sp sp0 SL SH E5 XL2 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - exact FC5.
  - right. exists 0x962a8, 0x962aa, (Z_to_bv 64 0x962a8), (Z_to_bv 64 1024), (Z_to_bv 64 0), (lden E5 (lvar 5)).
    split; [exact SP | rewrite Hfd5; exact fd1_of_fds0].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E"] Theorem tail2 : forall E1 ms md hs len cap buf al ow,
  ITHEAD' X2 2 E1 ms md hs len cap buf al ow -> realizes PSEGS (mkCfg ms md) (KREST' 1).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf al ow HIT.
  apply (free_owned_step' X2 2 E1 ms md hs len cap buf al ow _ fr_x2 HIT).
  intros E2 ms2 md2 hs2 HTL. rewrite TL2_eq in HTL. pose proof HTL as (_ & Hd2 & _ & _ & _ & _ & _ & _ & _ & Hhd & Hld & _).
  destruct tl2_chk as (Gsh & Gc & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 TL2 LTL2 E2 ms2 md2 _ TBL_P_ok IMG_P_ok cert_LTL2 Hd2 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LTL2_eq in HIn.
  assert (K : forall E4, TLHEAD' BJ2 2 E4 ms3 md2 hs2 len cap buf -> realizes PSEGS (mkCfg ms3 md2) (KREST' 1)).
  { intros E4 HT4. apply (free_buf_step' BJ2 2 E4 ms3 md2 hs2 len cap buf _ fr_bj2 HT4).
    intros E5 ms5 md5 HX5. rewrite EX2_eq in HX5. exact (exit2 E5 ms5 md5 HX5). }
  destruct HIn as [<-|[<-|[]]].
  - apply (K (ecomp E3 sig_b2a)). apply (tl_ent' B2a BJ2 sig_b2a 2 E3 ms3 md2 hs2 len cap buf); [| exact ent_b2a | exact wf_bj2 | exact sid_b2a].
    exact (tl_fx' TL2 B2a 2 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b2a Gnx).
  - apply (K (ecomp E3 sig_b2b)). apply (tl_ent' B2b BJ2 sig_b2b 2 E3 ms3 md2 hs2 len cap buf); [| exact ent_b2b | exact wf_bj2 | exact sid_b2b].
    exact (tl_fx' TL2 B2b 2 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b2b Gnx).
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E"] Theorem exit3 : forall E1 ms md, EXHEAD' EX3 E1 ms md -> realizes PSEGS (mkCfg ms md) (KREST' 2).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E : LiaFast.U) => LiaFast.u0).
  intros E4 ms4 md4 HX4. pose proof HX4 as (Ha4 & Hd4 & Hrom4 & _ & _ & _ & Hh4l & Hl4l & _ & Hfs4).
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. destruct ex3_chk as (Gsh & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 EX3 LEX3 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LEX3 Hd4 ltac:(vm_compute; reflexivity) Hh4l Hl4l).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 _. rewrite LEX3_eq in HIn. destruct HIn as [<-|[]].
  pose proof (ex_fx' EX3 XL3 E4 E5 ms4 ms5 md4 HX4 Ha45 Hd5 Hrom5 Hfr5 Gsh Gnx) as HX5.
  destruct HX5 as (Ha5 & _ & Hrom5' & _ & Hm5 & Hnl5 & _ & _ & Hfd5 & _).
  assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha5 x Hx)).
  unfold KREST. rewrite <- Hfs4, <- exit_code0.
  apply (fx_exit E5 XL3 ms5 md4 (Z_to_bv 64 0) (zero_lines 2) Hd5 eq_refl eq_refl Hrom5').
  assert (FC5 : file_clean (ms_mem ms5) 0x64e20 (Z_to_bv 64 0) (Z_to_bv 64 0)).
  { split; [|split; [|split; [|split]]];
      [ rewrite (rdn_img_c E5 XL3 ms5 5 0x64e20 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL3 ms5 5 0x64e20 40 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL3 ms5 5 0x64e20 56 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL3 ms5 5 0x64e20 8 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL3 ms5 5 0x64e20 16 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)) ]; bvlit. }
  assert (SSP : ssp_cells (ms_mem ms5) (lden E5 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x63da0) with (Z_to_bv 64 (0x63c60 + 320)) by reflexivity.
      rewrite (rdn_img_c E5 XL3 ms5 3 0x63c60 320 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x95e40) with (Z_to_bv 64 (0x95e40 + 0)) by reflexivity.
      rewrite (rdn_trk_c E5 XL3 ms5 8 0x95e40 0 8 (bvs_of (lvar 5) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (SP : stdout_pending (ms_mem ms5) 0x962a8 0x962ac (Z_to_bv 64 0x962a8) (Z_to_bv 64 1024) (Z_to_bv 64 0) (lden E5 (lvar 5)) (zero_lines 2)).
  { constructor.
    - rewrite (rdn_img_c E5 XL3 ms5 6 0x64f10 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL3 ms5 6 0x64f10 40 8 (bks 0x962ac 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL3 ms5 6 0x64f10 56 8 (bvs_of (lconst 0x962a8) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, lden_lconst. reflexivity.
    - rewrite (rdn_trk_c E5 XL3 ms5 6 0x64f10 72 8 (bks 0x54050 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL3 ms5 6 0x64f10 88 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL3 ms5 6 0x64f10 96 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL3 ms5 6 0x64f10 120 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL3 ms5 6 0x64f10 8 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL3 ms5 6 0x64f10 16 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - lia.
    - reflexivity.
    - unfold rw_bytes_max. cbn [length zero_lines]. lia.
    - replace (Z_to_bv 64 0x962a8) with (Z_to_bv 64 (0x962a0 + 8)) by reflexivity. cbn [length zero_lines].
      rewrite (rdn_trk_c E5 XL3 ms5 10 0x962a0 8 4 [BK 48; BK 10; BK 48; BK 10] Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - exact SSP. }
  apply (exit_pre_gen2r sp0 tid SL SH Htid E5 XL3 ms5 md4 (-48) 0 0 3 7 9 21 65344 (rg_cont (rgn XL3 7)) (rg_cont (rgn XL3 9)) (rg_cont (rgn XL3 21)) RW RI (Z_to_bv 64 0) (Z_to_bv 64 0) (zero_lines 2) Hd5).
  - unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
  - lia.
  - lia.
  - exact (exit_glob_of_MFXR' _ Hm5 Hnl5).
  - exact Hh4l.
  - exact Hl4l.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold c21_reg. repeat split; vm_compute; reflexivity.
  - apply (frame_sp sp0 SL SH E5 XL3 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - exact FC5.
  - right. exists 0x962a8, 0x962ac, (Z_to_bv 64 0x962a8), (Z_to_bv 64 1024), (Z_to_bv 64 0), (lden E5 (lvar 5)).
    split; [exact SP | rewrite Hfd5; exact fd1_of_fds0].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E"] Theorem tail3 : forall E1 ms md hs len cap buf al ow,
  ITHEAD' X3 3 E1 ms md hs len cap buf al ow -> realizes PSEGS (mkCfg ms md) (KREST' 2).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf al ow HIT.
  apply (free_owned_step' X3 3 E1 ms md hs len cap buf al ow _ fr_x3 HIT).
  intros E2 ms2 md2 hs2 HTL. rewrite TL3_eq in HTL. pose proof HTL as (_ & Hd2 & _ & _ & _ & _ & _ & _ & _ & Hhd & Hld & _).
  destruct tl3_chk as (Gsh & Gc & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 TL3 LTL3 E2 ms2 md2 _ TBL_P_ok IMG_P_ok cert_LTL3 Hd2 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LTL3_eq in HIn.
  assert (K : forall E4, TLHEAD' BJ3 3 E4 ms3 md2 hs2 len cap buf -> realizes PSEGS (mkCfg ms3 md2) (KREST' 2)).
  { intros E4 HT4. apply (free_buf_step' BJ3 3 E4 ms3 md2 hs2 len cap buf _ fr_bj3 HT4).
    intros E5 ms5 md5 HX5. rewrite EX3_eq in HX5. exact (exit3 E5 ms5 md5 HX5). }
  destruct HIn as [<-|[<-|[]]].
  - apply (K (ecomp E3 sig_b3a)). apply (tl_ent' B3a BJ3 sig_b3a 3 E3 ms3 md2 hs2 len cap buf); [| exact ent_b3a | exact wf_bj3 | exact sid_b3a].
    exact (tl_fx' TL3 B3a 3 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b3a Gnx).
  - apply (K (ecomp E3 sig_b3b)). apply (tl_ent' B3b BJ3 sig_b3b 3 E3 ms3 md2 hs2 len cap buf); [| exact ent_b3b | exact wf_bj3 | exact sid_b3b].
    exact (tl_fx' TL3 B3b 3 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b3b Gnx).
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E"] Theorem exit4 : forall E1 ms md, EXHEAD' EX4 E1 ms md -> realizes PSEGS (mkCfg ms md) (KREST' 3).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E : LiaFast.U) => LiaFast.u0).
  intros E4 ms4 md4 HX4. pose proof HX4 as (Ha4 & Hd4 & Hrom4 & _ & _ & _ & Hh4l & Hl4l & _ & Hfs4).
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. destruct ex4_chk as (Gsh & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 EX4 LEX4 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LEX4 Hd4 ltac:(vm_compute; reflexivity) Hh4l Hl4l).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 _. rewrite LEX4_eq in HIn. destruct HIn as [<-|[]].
  pose proof (ex_fx' EX4 XL4 E4 E5 ms4 ms5 md4 HX4 Ha45 Hd5 Hrom5 Hfr5 Gsh Gnx) as HX5.
  destruct HX5 as (Ha5 & _ & Hrom5' & _ & Hm5 & Hnl5 & _ & _ & Hfd5 & _).
  assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha5 x Hx)).
  unfold KREST. rewrite <- Hfs4, <- exit_code0.
  apply (fx_exit E5 XL4 ms5 md4 (Z_to_bv 64 0) (zero_lines 3) Hd5 eq_refl eq_refl Hrom5').
  assert (FC5 : file_clean (ms_mem ms5) 0x64e20 (Z_to_bv 64 0) (Z_to_bv 64 0)).
  { split; [|split; [|split; [|split]]];
      [ rewrite (rdn_img_c E5 XL4 ms5 5 0x64e20 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL4 ms5 5 0x64e20 40 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL4 ms5 5 0x64e20 56 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL4 ms5 5 0x64e20 8 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL4 ms5 5 0x64e20 16 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)) ]; bvlit. }
  assert (SSP : ssp_cells (ms_mem ms5) (lden E5 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x63da0) with (Z_to_bv 64 (0x63c60 + 320)) by reflexivity.
      rewrite (rdn_img_c E5 XL4 ms5 3 0x63c60 320 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x95e40) with (Z_to_bv 64 (0x95e40 + 0)) by reflexivity.
      rewrite (rdn_trk_c E5 XL4 ms5 8 0x95e40 0 8 (bvs_of (lvar 5) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (SP : stdout_pending (ms_mem ms5) 0x962a8 0x962ae (Z_to_bv 64 0x962a8) (Z_to_bv 64 1024) (Z_to_bv 64 0) (lden E5 (lvar 5)) (zero_lines 3)).
  { constructor.
    - rewrite (rdn_img_c E5 XL4 ms5 6 0x64f10 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL4 ms5 6 0x64f10 40 8 (bks 0x962ae 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL4 ms5 6 0x64f10 56 8 (bvs_of (lconst 0x962a8) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, lden_lconst. reflexivity.
    - rewrite (rdn_trk_c E5 XL4 ms5 6 0x64f10 72 8 (bks 0x54050 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL4 ms5 6 0x64f10 88 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL4 ms5 6 0x64f10 96 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_img_c E5 XL4 ms5 6 0x64f10 120 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL4 ms5 6 0x64f10 8 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL4 ms5 6 0x64f10 16 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - lia.
    - reflexivity.
    - unfold rw_bytes_max. cbn [length zero_lines]. lia.
    - replace (Z_to_bv 64 0x962a8) with (Z_to_bv 64 (0x962a0 + 8)) by reflexivity. cbn [length zero_lines].
      rewrite (rdn_trk_c E5 XL4 ms5 10 0x962a0 8 6 [BK 48; BK 10; BK 48; BK 10; BK 48; BK 10] Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - exact SSP. }
  apply (exit_pre_gen2r sp0 tid SL SH Htid E5 XL4 ms5 md4 (-48) 0 0 3 7 9 21 65344 (rg_cont (rgn XL4 7)) (rg_cont (rgn XL4 9)) (rg_cont (rgn XL4 21)) RW RI (Z_to_bv 64 0) (Z_to_bv 64 0) (zero_lines 3) Hd5).
  - unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
  - lia.
  - lia.
  - exact (exit_glob_of_MFXR' _ Hm5 Hnl5).
  - exact Hh4l.
  - exact Hl4l.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold c21_reg. repeat split; vm_compute; reflexivity.
  - apply (frame_sp sp0 SL SH E5 XL4 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - exact FC5.
  - right. exists 0x962a8, 0x962ae, (Z_to_bv 64 0x962a8), (Z_to_bv 64 1024), (Z_to_bv 64 0), (lden E5 (lvar 5)).
    split; [exact SP | rewrite Hfd5; exact fd1_of_fds0].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E"] Theorem tail4 : forall E1 ms md hs len cap buf al ow,
  ITHEAD' X4 4 E1 ms md hs len cap buf al ow -> realizes PSEGS (mkCfg ms md) (KREST' 3).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf al ow HIT.
  apply (free_owned_step' X4 4 E1 ms md hs len cap buf al ow _ fr_x4 HIT).
  intros E2 ms2 md2 hs2 HTL. rewrite TL4_eq in HTL. pose proof HTL as (_ & Hd2 & _ & _ & _ & _ & _ & _ & _ & Hhd & Hld & _).
  destruct tl4_chk as (Gsh & Gc & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 TL4 LTL4 E2 ms2 md2 _ TBL_P_ok IMG_P_ok cert_LTL4 Hd2 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LTL4_eq in HIn.
  assert (K : forall E4, TLHEAD' BJ4 4 E4 ms3 md2 hs2 len cap buf -> realizes PSEGS (mkCfg ms3 md2) (KREST' 3)).
  { intros E4 HT4. apply (free_buf_step' BJ4 4 E4 ms3 md2 hs2 len cap buf _ fr_bj4 HT4).
    intros E5 ms5 md5 HX5. rewrite EX4_eq in HX5. exact (exit4 E5 ms5 md5 HX5). }
  destruct HIn as [<-|[<-|[]]].
  - apply (K (ecomp E3 sig_b4a)). apply (tl_ent' B4a BJ4 sig_b4a 4 E3 ms3 md2 hs2 len cap buf); [| exact ent_b4a | exact wf_bj4 | exact sid_b4a].
    exact (tl_fx' TL4 B4a 4 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b4a Gnx).
  - apply (K (ecomp E3 sig_b4b)). apply (tl_ent' B4b BJ4 sig_b4b 4 E3 ms3 md2 hs2 len cap buf); [| exact ent_b4b | exact wf_bj4 | exact sid_b4b].
    exact (tl_fx' TL4 B4b 4 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b4b Gnx).
Qed.

End T8.
