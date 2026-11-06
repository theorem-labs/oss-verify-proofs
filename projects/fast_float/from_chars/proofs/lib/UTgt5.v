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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvCall2 UUsageCert UOpenCert UOpen1 UDirCert UDir ULoopCert ULoopInv ULoop1 UEofCert UEof1 ULoopInv2 UEof3 UTgtCert ULoop2 ULoop3 UTgt1 UTgt2 UDrvFuzz UTgt3 UTgt4 URefused UDrvCall2 UbStdioDefs Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section T5.
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
Local Notation TRHEAD' := (TRHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation CL := (Z.of_nat (config_len data)).
Local Notation CALLS := (Z.of_nat (n_calls data)).



Local Notation ITHEAD' := (ITHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation fuzz_step' := (fuzz_step sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HSTATI data fs0 HFZ HSRO HKRO).
Local Notation it_fx' := (it_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).

(* [comment removed for export] *)
#[using="Hsp Hargc2 E"] Lemma mfxr_sw : forall m m' su f bufp bufsz, sw_post m su f bufp bufsz m' -> (f = 0x66bd8 \/ f = 0x66cc8) ->
  bv_unsigned sp0 - 65536 <= su - 112 -> su <= bv_unsigned sp0 -> MFXR' m -> MFXR' m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 E : LiaFast.U) => LiaFast.u0).
  intros m m' su f bufp bufsz Hpost Hf Hs1 Hs2 Hm. pose proof (sp0_lo sp0 Hsp). pose proof (sp0_hi sp0 Hsp).
  intros x Hx Hh Hr.
  pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
  pose proof (outside_nth_c E _ x 5 (lconst 0x66bd8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
  pose proof (outside_nth_c E _ x 6 (lconst 0x66cc8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X6r. cbn [RGz rg_base] in X6r.
  rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
  rewrite u_small64 in X0r by (unfold two64; lia). rewrite u_lconst in X5r, X6r by lia.
  rewrite (swp_agree _ _ _ _ _ _ Hpost x); [exact (Hm x Hx Hh Hr) | lia | destruct Hf; subst f; lia | destruct Hf; subst f; lia].
Qed.

(* [comment removed for export] *)
#[using="Hargc2"] Lemma it_mem : forall (S L : sst) kc E1 E2 ms1 ms2 md hs len cap buf al ow,
  ITHEAD' S kc E1 ms1 md hs len cap buf al ow -> agree (s_next S) E1 E2 -> sden PSEGS E2 L ms2 -> ms_rom ms2 = seg_rom PSEGS ->
  ms_mem ms2 = ms_mem ms1 -> (502 <= s_next S)%positive -> ITHEAD' L kc E2 ms2 md hs len cap buf al ow.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0).
  intros S L kc E1 E2 ms1 ms2 md hs len cap buf al ow
    (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & HAV1 & HOV1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1 & Hpay)
    Ha12 Hd2 Hrom2 Hmem Hnx.
  rewrite <- Hmem in Hm1, Hh1.
  refine (conj _ (conj Hd2 (conj Hrom2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hm1 (conj Hh1 (conj Hhd (conj Hld (conj Hfd
           (conj Hfs (conj Hblk (conj HL (conj Hlen (conj Hcap (conj HU1 Hpay)))))))))))))))))))).
  - intros x Hx. etransitivity; [exact (Ha1 x Hx) | apply Ha12; lia].
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HN1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HB1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HC1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HR1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HAV1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HOV1.
Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc2 HTOPB HIMG HOK HSTATI E"] Lemma it_sw : forall (S L : sst) kc E1 E2 ms1 ms2 md hs len cap buf al ow su f bufp bufsz,
  ITHEAD' S kc E1 ms1 md hs len cap buf al ow -> agree (s_next S) E1 E2 -> sden PSEGS E2 L ms2 -> ms_rom ms2 = seg_rom PSEGS ->
  sw_post (ms_mem ms1) su f bufp bufsz (ms_mem ms2) -> (f = 0x66bd8 \/ f = 0x66cc8) ->
  bv_unsigned sp0 - 65536 <= su - 112 -> su <= bv_unsigned sp0 -> (502 <= s_next S)%positive -> ITHEAD' L kc E2 ms2 md hs len cap buf al ow.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 HTOPB HIMG HOK HSTATI E : LiaFast.U) => LiaFast.u0).
  intros S L kc E1 E2 ms1 ms2 md hs len cap buf al ow su f bufp bufsz
    (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & HAV1 & HOV1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1 & Hpay)
    Ha12 Hd2 Hrom2 Hpost Hf Hs1 Hs2 Hnx.
  pose proof (sp0_hi sp0 Hsp).
  pose proof (mfxr_sw _ _ _ _ _ _ Hpost Hf Hs1 Hs2 Hm1) as Hm2.
  pose proof (heap_sw av Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HI HOK HSTATI hs _ _ md su f bufp bufsz Hh1 Hpost ltac:(lia) ltac:(lia) Hf) as Hh2.
  refine (conj _ (conj Hd2 (conj Hrom2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hm2 (conj Hh2 (conj Hhd (conj Hld (conj Hfd
           (conj Hfs (conj Hblk (conj HL (conj Hlen (conj Hcap (conj HU1 Hpay)))))))))))))))))))).
  - intros x Hx. etransitivity; [exact (Ha1 x Hx) | apply Ha12; lia].
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HN1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HB1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HC1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HR1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HAV1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HOV1.
Qed.

#[using="Type"] Lemma fz_G0 : fz_tmpl G0 = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma fd1_of_fds0 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI HFZ HSRO HKRO E"] Theorem iter1 : forall E1 ms md hs len cap buf al ow (KR : TSet),
  ITHEAD' G0 0 E1 ms md hs len cap buf al ow -> KR [] ->
  (forall E2 ms2 md2 hs2, ITHEAD' U_sw1 1 E2 ms2 md2 hs2 len cap buf al ow -> realizes PSEGS (mkCfg ms2 md2) KR) ->
  realizes PSEGS (mkCfg ms md) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) KR).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI HFZ HSRO HKRO E : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf al ow KR HIT HKnil K.
  apply (fuzz_step' G0 0 E1 ms md hs len cap buf al ow _ fz_G0 ltac:(lia) HIT).
  intros E2 ms2 md2 hs2 HIT2. rewrite U_z1_eq in HIT2. pose proof HIT2 as (_ & Hd2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhd & Hld & _).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_z1 LZ1 E2 ms2 md2 _ TBL_P_ok IMG_P_ok cert_LZ1 Hd2 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LZ1_eq in HIn. destruct HIn as [<-|[]].
  pose proof (it_fx' U_z1 Lio1 1 E2 E3 ms2 ms3 md2 hs2 len cap buf al ow HIT2 Ha23 Hd3 Hrom3 Hfr3 Hgr3
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; congruence)) as HIT3.
  pose proof HIT3 as (Ha3 & _ & Hrom3' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfd3 & _).
  (* [comment removed for export] *)
  assert (R17 : getr (ms_regs ms3) 17 = Z_to_bv 64 29) by (apply (getr_leaf_c PSEGS E3 Lio1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms3) 10 = Z_to_bv 64 1) by (apply (getr_leaf_c PSEGS E3 Lio1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R11 : getr (ms_regs ms3) 11 = Z_to_bv 64 21523) by (apply (getr_leaf_c PSEGS E3 Lio1); [exact Hd3 | vm_compute; reflexivity]).
  apply (fx_ioctl E3 Lio1 ms3 md2 (Z_to_bv 64 1) _ Hd3 eq_refl eq_refl Hrom3' Hhd Hld R17
           ltac:(rewrite Hfd3, R10; vm_compute; reflexivity) ltac:(rewrite R11; vm_compute; reflexivity) hok_io1).
  intros E4 ms4 Ha34 Hd4 Hrom4 Hmem4. rewrite U_io1_eq in Hd4.
  pose proof (it_mem Lio1 U_io1 1 E3 E4 ms3 ms4 md2 hs2 len cap buf al ow HIT3 Ha34 Hd4 Hrom4 Hmem4 ltac:(vm_compute; congruence)) as HIT4.
  (* [comment removed for export] *)
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_io1 LIO1 E4 ms4 md2 _ TBL_P_ok IMG_P_ok cert_LIO1 Hd4 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 Hgr5. rewrite LIO1_eq in HIn. destruct HIn as [<-|[]].
  pose proof (it_fx' U_io1 Lsw1 1 E4 E5 ms4 ms5 md2 hs2 len cap buf al ow HIT4 Ha45 Hd5 Hrom5 Hfr5 Hgr5
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; congruence)) as HIT5.
  (* [comment removed for export] *)
  pose proof HIT5 as (Ha5 & _ & Hrom5' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfd5 & _).
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha5 x Hx)).
  assert (HS5 : lden E5 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE5 by lia; reflexivity).
  assert (S1 : getr (ms_regs ms5) 1 = Z_to_bv 64 0x56020) by (apply (getr_leaf_c PSEGS E5 Lsw1); [exact Hd5 | vm_compute; reflexivity]).
  assert (S2 : getr (ms_regs ms5) 2 = Z_to_bv 64 (bv_unsigned sp0 - 1296)).
  { rewrite (getr_leaf PSEGS E5 Lsw1 ms5 2 (laddc SP0 (-1296)) Hd5) by (vm_compute; reflexivity). apply (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E5 (-1296) HE5). lia. }
  assert (S10 : getr (ms_regs ms5) 10 = Z_to_bv 64 0x66cc8) by (apply (getr_leaf_c PSEGS E5 Lsw1); [exact Hd5 | vm_compute; reflexivity]).
  assert (S11 : getr (ms_regs ms5) 11 = Z_to_bv 64 0x10bef) by (apply (getr_leaf_c PSEGS E5 Lsw1); [exact Hd5 | vm_compute; reflexivity]).
  assert (S12 : getr (ms_regs ms5) 12 = Z_to_bv 64 1) by (apply (getr_leaf_c PSEGS E5 Lsw1); [exact Hd5 | vm_compute; reflexivity]).
  assert (F40 : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 (0x66cc8 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x98069))).
  { rewrite (rdn_trk_c E5 Lsw1 ms5 6 0x66cc8 40 8 (bks 0x98069 8) Hd5
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F56 : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 (0x66cc8 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x98068))).
  { rewrite (rdn_trk_c E5 Lsw1 ms5 6 0x66cc8 56 8 (bks 0x98068 8) Hd5
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F88 : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 (0x66cc8 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x98068))).
  { rewrite (rdn_img_c E5 Lsw1 ms5 6 0x66cc8 88 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F96 : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 (0x66cc8 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))).
  { rewrite (rdn_img_c E5 Lsw1 ms5 6 0x66cc8 96 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F120 : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 (0x66cc8 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
  { rewrite (rdn_img_c E5 Lsw1 ms5 6 0x66cc8 120 4 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F48 : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 (0x66cc8 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
  { rewrite (rdn_img_c E5 Lsw1 ms5 6 0x66cc8 48 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (SWF : sw_file (ms_mem ms5) 0x66cc8 0x98068 0x98069 1 (Z_to_bv 64 0x98068) (Z_to_bv 64 1024)) by (constructor; assumption).
  assert (SSP : ssp_cells (ms_mem ms5) (lden E5 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x65b58) with (Z_to_bv 64 (0x65a18 + 320)) by reflexivity.
      rewrite (rdn_img_c E5 Lsw1 ms5 3 0x65a18 320 8 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x97c00) with (Z_to_bv 64 (0x97c00 + 0)) by reflexivity.
      rewrite (rdn_trk_c E5 Lsw1 ms5 8 0x97c00 0 8 (bvs_of (lvar 5) 8) Hd5
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (RDP : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 0x98068) (length [Z_to_bv 8 48]) = Some [Z_to_bv 8 48]).
  { replace (Z_to_bv 64 0x98068) with (Z_to_bv 64 (0x98060 + 8)) by reflexivity. cbn [length].
    rewrite (rdn_trk_c E5 Lsw1 ms5 10 0x98060 8 1 [BK 48] Hd5
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (RDX : rdn PSEGS (ms_mem ms5) (Z_to_bv 64 0x10bef) (length [Z_to_bv 8 10]) = Some [Z_to_bv 8 10]).
  { replace (Z_to_bv 64 0x10bef) with (Z_to_bv 64 (0x10bd5 + 26)) by reflexivity. cbn [length].
    rewrite (rdn_img_c E5 Lsw1 ms5 12 0x10bd5 26 1 Hd5 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (FRM : frame_in E5 Lsw1 0 64128 112 (bv_unsigned sp0 - 1296 - 112)).
  { apply (frame_sp sp0 SL SH E5 Lsw1 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS5 | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia]. }
  assert (HWF : state_wf (sw_template Lsw1 (bv_unsigned (Z_to_bv 64 0x56020)) 0 64128 6 (lconst 0x98068) (lconst 1024) (lconst 1)) = true).
  { rewrite u_small64 by (unfold two64; lia). rewrite U_sw1_eq. exact wf_sw1. }
  change (realizes PSEGS (mkCfg ms5 md2) (t_emit (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])) KR)).
  apply (fx_stdio_write E5 Lsw1 ms5 md2 _ (bv_unsigned sp0 - 1296) 0x66cc8 0x98068 0x98069 1
           (Z_to_bv 64 0x10bef) (Z_to_bv 64 1) (Z_to_bv 64 0x98068) (Z_to_bv 64 1024) (lden E5 (lvar 5)) (Z_to_bv 64 0x56020) [Z_to_bv 8 48] [Z_to_bv 8 10]
           0 64128 6 (rgn Lsw1 6) (lconst 0x98068) (lconst 1024) (lconst 1)
           Hd5 eq_refl eq_refl Hrom5' hok_sw1 HWF FRM (rgn_eq Lsw1 6 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) S2 S10 S11 S12 S1); try lia.
  + exact SWF.
  + exact SSP.
  + exact F48.
  + rewrite Hfd5. exact fd1_of_fds0.
  + exact Hhd.
  + exact Hld.
  + unfold TASK_SIZE. lia.
  + cbn [length]. lia.
  + vm_compute. reflexivity.
  + cbn [length]. lia.
  + cbn [length]. lia.
  + left. rewrite !u_small64 by (unfold two64; lia). lia.
  + rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE. lia.
  + exact RDP.
  + exact RDX.
  + vm_compute. reflexivity.
  + exact HKnil.
  + apply lden_lconst.
  + apply lden_lconst.
  + apply lden_lconst.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + intros E6 ms6 Ha56 Hd6 Hpost6 Hrom6.
    rewrite u_small64 in Hd6 by (unfold two64; lia). rewrite U_sw1_eq in Hd6.
    apply (K E6 ms6 md2 hs2).
    apply (it_sw Lsw1 U_sw1 1 E5 E6 ms5 ms6 md2 hs2 len cap buf al ow _ 0x66cc8 _ _ HIT5 Ha56 Hd6 ltac:(rewrite Hrom6; exact Hrom5') Hpost6
             ltac:(right; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; congruence)).
Qed.

End T5.
