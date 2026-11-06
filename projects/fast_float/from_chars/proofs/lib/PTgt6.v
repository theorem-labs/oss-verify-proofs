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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvCall2 PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PEofCert PEof1 PLoopInv2 PEof3 PTgtCert PLoop2 PLoop3 PTgt1 PTgt2 PDrvFuzz PTgt3 PTgt4 PTgt5 PRefused PDrvCall2 RefStdioDefs Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section T6.
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
Local Notation TRHEAD' := (TRHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation ITHEAD' := (ITHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation tr_front' := (tr_front sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HNL HSTATI data fs0).
Local Notation j0_to_g0' := (j0_to_g0 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).
Local Notation j1_to_g0' := (j1_to_g0 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).
Local Notation iter1' := (iter1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).

(* [comment removed for export] *)
Definition KREST (n : nat) : TSet := t_emit (W 1 (zero_lines n)) (t_exit (exit_code 0) fs0).

#[using="av Hargc2"] Lemma n_calls_pos : (1 <= n_calls data)%nat.
Proof. LiaFast.lf_pins (fun (av Hargc2 : LiaFast.U) => LiaFast.u0). unfold n_calls. destruct (config_len data); lia. Qed.

#[using="Type"] Lemma krest_front : forall n, t_eq (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) (KREST n)) (KREST (S n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n. unfold KREST. cbn [zero_lines]. unfold W. change (Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines n) with ([Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines n).
  rewrite map_app. apply t_emit_app.
Qed.

#[using="Type"] Lemma krest_nil : forall n, KREST n [].
Proof. LiaFast.lf_pins LiaFast.u0. intros n. unfold KREST, t_emit. left. exact I. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HNL HSTATI HFZ HSRO HKRO"] Theorem target_front : forall E3 ms md hs len cap buf,
  TRHEAD' E3 ms md hs len cap buf ->
  (forall E2 ms2 md2 hs2 al ow, ITHEAD' U_sw1 1 E2 ms2 md2 hs2 len cap buf al ow -> realizes PSEGS (mkCfg ms2 md2) (KREST (n_calls data - 1))) ->
  realizes PSEGS (mkCfg ms md) (t_emit (W 1 (zero_lines (n_calls data))) (t_exit (exit_code 0) fs0)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HNL HSTATI HFZ HSRO HKRO : LiaFast.U) => LiaFast.u0).
  intros E3 ms md hs len cap buf HT K.
  change (realizes PSEGS (mkCfg ms md) (KREST (n_calls data))).
  pose proof n_calls_pos as Hn. replace (n_calls data) with (S (n_calls data - 1)) by lia.
  apply (rzc_conseq PSEGS DCFG _ (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) (KREST (n_calls data - 1)))); [|apply krest_front].
  apply (tr_front' E3 ms md hs len cap buf _ HT).
  - intros E4 ms4 HJ. apply (j0_to_g0' E4 ms4 md hs len cap buf _ HJ).
    intros E5 ms5 HF. apply (iter1' HFZ HSRO HKRO E5 ms5 md hs len cap buf _ _ _ (fz_ithead sp0 av ev tid rdraw regs mem Hargc2 IMG_LO IMG_END HTOP STATIC HI data fs0 E5 ms5 md hs len cap buf _ _ HF)
                           (krest_nil _)).
    intros E2 ms2 md2 hs2 HI2. exact (K E2 ms2 md2 hs2 _ _ HI2).
  - intros E4 ms4 HJ. apply (j1_to_g0' E4 ms4 md hs len cap buf _ HJ).
    intros E5 ms5 md5 hs5 p HF. apply (iter1' HFZ HSRO HKRO E5 ms5 md5 hs5 len cap buf _ _ _ (fz_ithead sp0 av ev tid rdraw regs mem Hargc2 IMG_LO IMG_END HTOP STATIC HI data fs0 E5 ms5 md5 hs5 len cap buf _ _ HF)
                           (krest_nil _)).
    intros E2 ms2 md2 hs2 HI2. exact (K E2 ms2 md2 hs2 _ _ HI2).
Qed.

End T6.
