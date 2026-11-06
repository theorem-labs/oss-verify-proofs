(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From Ltac2 Require Import Ltac2 Constr Std Control.
Set Default Proof Mode "Classic".
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
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
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvCall UDrvExit UDrvSys UDrvHeap UDrvHeap2 UDrvRead UbStartup UbStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.UbStartup OSSVerify.Proofs.fast_float.from_chars.lib.UbStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvCall2 UUsageCert UOpenCert UOpen1 UDirCert UDir ULoopCert ULoopInv ULoop1 UEofCert UEof1 ULoopInv2 UEof3 UTgtCert ULoop2 ULoop3 UTgt1 UTgt2 UDrvFuzz UTgt3 UTgt4 UTgt5 UTgt6 UTgtCert2 UDrvExit2 UDrvExit3 URefused UDrvCall2 UbStdioDefs Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section T7.
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
Hypothesis HIMG : IMG_LO <= 0x10000 /\ 0x99000 <= IMG_END.
Hypothesis HSTATX : forall x, ~ ioutside EXGX x -> ioutside STATIC x.
Variable HI : heap_iface.
Hypothesis HOK : heap_ok PSEGS DCFG HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) IMG_LO IMG_END HTOP STATIC CELLS_NE 0x530c8 8192 0x52f88 8192.
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x65b58 <= a < 0x65b60 \/ 0x97c00 <= a < 0x97c08 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.
Hypothesis HNL : forall hs m md, hi_Heap HI hs m md -> NL m.
Hypothesis HSTATI : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC x.
Hypothesis HMV : forall hs m md md', hi_Heap HI hs m md -> m_vmmaps md' = m_vmmaps md -> m_halted md' = None -> m_vm_lazy md' = [] -> hi_Heap HI hs m md'.
Hypothesis HSTATR : forall x, RSX x -> ioutside STATIC x.
Variable data : list byte.
Variable fs0 : Fs.Fs.
Hypothesis Hlk : fs_lookup fs0 (nth 1 av []) = Some data.
Hypothesis HFZ : fuzz_contract PSEGS DCFG (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990)
  IMG_LO IMG_END HTOP STATIC CELLS_NE 0x22e0c 8592 PRO.
Hypothesis HSRO : forall x, 0x10000 <= x < 0x22000 \/ 0x66b98 <= x < 0x66b9c -> ~ KRO x -> ioutside STATIC x.
Hypothesis HKRO : forall hs m md, hi_Heap HI hs m md -> pristine m 0x18288 0x182a8 /\ pristine m 0x182a8 0x18327.

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
Local Notation exit_glob_of_MFXR' := (exit_glob_of_MFXR sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HSTATX).

(* [comment removed for export] *)
#[using="Hargc2"] Lemma tl_ent : forall (S J : sst) σ kc E1 ms md hs len cap buf,
  TLHEAD' S kc E1 ms md hs len cap buf -> entails S J σ = true -> state_wf J = true -> sig_id_below σ 502 = true ->
  TLHEAD' J kc (ecomp E1 σ) ms md hs len cap buf.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0).
  intros S J σ kc E1 ms md hs len cap buf
    (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1) Hent Hwf Hsid.
  pose proof (ecomp_agree E1 σ 502 Hsid) as Ha12.
  pose proof (entails_sden PSEGS E1 S J σ ms (sden_0 _ _ _ _ Hd1) Hent Hwf) as Hd2.
  refine (conj _ (conj Hd2 (conj Hrom1 (conj _ (conj _ (conj _ (conj _ (conj Hm1 (conj Hh1 (conj Hhd (conj Hld (conj Hfd
           (conj Hfs (conj Hblk (conj HL (conj Hlen (conj Hcap HU1))))))))))))))))).
  - intros x Hx. etransitivity; [exact (Ha1 x Hx) | apply Ha12; lia].
  - rewrite <- (Ha12 N0) by (vm_compute; reflexivity). exact HN1.
  - rewrite <- (Ha12 BUF) by (vm_compute; reflexivity). exact HB1.
  - rewrite <- (Ha12 CLV) by (vm_compute; reflexivity). exact HC1.
  - rewrite <- (Ha12 RV) by (vm_compute; reflexivity). exact HR1.
Qed.

#[using="Type"] Lemma exit_code0 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = exit_code 0. Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E"] Theorem exit1 : forall E1 ms md, EXHEAD' EX1 E1 ms md -> realizes PSEGS (mkCfg ms md) (KREST' 0).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX E : LiaFast.U) => LiaFast.u0).
  intros E4 ms4 md4 HX4. pose proof HX4 as (Ha4 & Hd4 & Hrom4 & _ & _ & _ & Hh4l & Hl4l & _ & Hfs4).
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. destruct ex1_chk as (Gsh & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 EX1 LEX1 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LEX1 Hd4 ltac:(vm_compute; reflexivity) Hh4l Hl4l).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 _. rewrite LEX1_eq in HIn. destruct HIn as [<-|[]].
  pose proof (ex_fx' EX1 XL1 E4 E5 ms4 ms5 md4 HX4 Ha45 Hd5 Hrom5 Hfr5 Gsh Gnx) as HX5.
  destruct HX5 as (Ha5 & _ & Hrom5' & _ & Hm5 & Hnl5 & _ & _ & _ & _).
  assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha5 x Hx)).
  unfold KREST. rewrite <- Hfs4, <- exit_code0.
  apply (fx_exit E5 XL1 ms5 md4 (Z_to_bv 64 0) [] Hd5 eq_refl eq_refl Hrom5').
  assert (FC5 : file_clean (ms_mem ms5) 0x66bd8 (Z_to_bv 64 0) (Z_to_bv 64 0)).
  { split; [|split; [|split; [|split]]];
      [ rewrite (rdn_img_c E5 XL1 ms5 5 0x66bd8 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL1 ms5 5 0x66bd8 40 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL1 ms5 5 0x66bd8 56 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL1 ms5 5 0x66bd8 8 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity))
      | rewrite (rdn_img_c E5 XL1 ms5 5 0x66bd8 16 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                   ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)) ]; bvlit. }
  assert (FC6 : file_clean (ms_mem ms5) 0x66cc8 (Z_to_bv 64 0x98068) (Z_to_bv 64 0)).
  { split; [|split; [|split; [|split]]].
    - rewrite (rdn_img_c E5 XL1 ms5 6 0x66cc8 140 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL1 ms5 6 0x66cc8 40 8 (bks 0x98068 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL1 ms5 6 0x66cc8 56 8 (bvs_of (lconst 0x98068) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin, lden_lconst. reflexivity.
    - rewrite (rdn_trk_c E5 XL1 ms5 6 0x66cc8 8 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit.
    - rewrite (rdn_trk_c E5 XL1 ms5 6 0x66cc8 16 8 Z8 Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  apply (exit_pre_gen2r sp0 tid SL SH Htid E5 XL1 ms5 md4 (-48) 0 0 3 7 9 21 65344 (rg_cont (rgn XL1 7)) (rg_cont (rgn XL1 9)) (rg_cont (rgn XL1 21)) RW RI (Z_to_bv 64 0) (Z_to_bv 64 0) [] Hd5).
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
  - apply (frame_sp sp0 SL SH E5 XL1 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - exact FC5.
  - left. split; [reflexivity|]. exists (Z_to_bv 64 0x98068), (Z_to_bv 64 0). exact FC6.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E"] Theorem tail1 : forall E1 ms md hs len cap buf al ow,
  ITHEAD' X1 1 E1 ms md hs len cap buf al ow -> realizes PSEGS (mkCfg ms md) (KREST' 0).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI E : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf al ow HIT.
  apply (free_owned_step' X1 1 E1 ms md hs len cap buf al ow _ fr_x1 HIT).
  intros E2 ms2 md2 hs2 HTL. rewrite TL1_eq in HTL. pose proof HTL as (_ & Hd2 & _ & _ & _ & _ & _ & _ & _ & Hhd & Hld & _).
  destruct tl1_chk as (Gsh & Gc & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 TL1 LTL1 E2 ms2 md2 _ TBL_P_ok IMG_P_ok cert_LTL1 Hd2 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LTL1_eq in HIn.
  assert (K : forall E4, TLHEAD' BJ1 1 E4 ms3 md2 hs2 len cap buf -> realizes PSEGS (mkCfg ms3 md2) (KREST' 0)).
  { intros E4 HT4. apply (free_buf_step' BJ1 1 E4 ms3 md2 hs2 len cap buf _ fr_bj1 HT4).
    intros E5 ms5 md5 HX5. rewrite EX1_eq in HX5. exact (exit1 E5 ms5 md5 HX5). }
  destruct HIn as [<-|[<-|[]]].
  - apply (K (ecomp E3 sig_b1a)). apply (tl_ent B1a BJ1 sig_b1a 1 E3 ms3 md2 hs2 len cap buf); [| exact ent_b1a | exact wf_bj1 | exact sid_b1a].
    exact (tl_fx' TL1 B1a 1 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b1a Gnx).
  - apply (K (ecomp E3 sig_b1b)). apply (tl_ent B1b BJ1 sig_b1b 1 E3 ms3 md2 hs2 len cap buf); [| exact ent_b1b | exact wf_bj1 | exact sid_b1b].
    exact (tl_fx' TL1 B1b 1 E2 E3 ms2 ms3 md2 hs2 len cap buf HTL Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc cells_b1b Gnx).
Qed.

End T7.
