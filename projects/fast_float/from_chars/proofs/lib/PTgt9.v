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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvCall2 PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PEofCert PEof1 PLoopInv2 PEof3 PTgtCert PLoop2 PLoop3 PTgt1 PTgt2 PDrvFuzz PTgt3 PTgt4 PTgt5 PTgt6 PTgtCert2 PDrvExit2 PTgt7 PTgt8 PRefused PDrvCall2 RefStdioDefs Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rv_exit : forall E0 lc k c, lc = 2 ^ 64 - k -> 1 <= k <= 4 -> E0 RV = Z_to_bv 64 c -> 1 <= c <= 4 ->
  fact_ok E0 (FCond BC_NE (LIN lc [(RV, 1)]) (lconst 0) false) -> c = k.
Proof.
  intros E0 lc k c Hlc Hk HR Hc HF. cbn [fact_ok branch_taken] in HF.
  destruct (Z.eq_dec c k) as [->|Hne]; [reflexivity|]. exfalso.
  rewrite bv_eqb_neq in HF; [discriminate HF|].
  intros Heq. apply (f_equal bv_unsigned) in Heq. rewrite lden_lconst in Heq. rewrite u_lin1, HR in Heq.
  rewrite (u_small64 c) in Heq by (unfold two64; lia). rewrite (u_small64 0) in Heq by (unfold two64; lia). subst lc.
  assert (C : (2 ^ 64 - k + c) mod 2 ^ 64 = c - k + (if Z.ltb c k then 2 ^ 64 else 0)).
  { destruct (Z.ltb c k) eqn:Hlt; [apply Z.ltb_lt in Hlt | apply Z.ltb_ge in Hlt].
    - rewrite Z.mod_small by lia. lia.
    - replace (2 ^ 64 - k + c) with ((c - k) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
  rewrite C in Heq. destruct (Z.ltb c k); lia.
Qed.

Lemma rv_ne : forall E0 lc k c, lc = 2 ^ 64 - k -> 1 <= k <= 4 -> E0 RV = Z_to_bv 64 c -> 1 <= c <= 4 ->
  fact_ok E0 (FCond BC_NE (LIN lc [(RV, 1)]) (lconst 0) true) -> c <> k.
Proof.
  intros E0 lc k c Hlc Hk HR Hc HF ->. cbn [fact_ok branch_taken] in HF.
  assert (Heq : lden E0 (LIN lc [(RV, 1)]) = lden E0 (lconst 0)).
  { apply bv_eq. rewrite lden_lconst, u_lin1, HR. rewrite (u_small64 k) by (unfold two64; lia). rewrite (u_small64 0) by (unfold two64; lia). subst lc.
    replace (2 ^ 64 - k + k) with (0 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity. }
  rewrite Heq, bv_eqb_refl in HF. discriminate HF.
Qed.

Lemma n_calls_range : forall d, (1 <= n_calls d <= 4)%nat.
Proof.
  intros d. unfold n_calls. destruct (config_len d); [lia|].
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 d (Z_to_bv 8 0))) 4 ltac:(lia)) as B.
  assert (Z.to_nat (bv_unsigned (nth 2 d (Z_to_bv 8 0)) mod 4) <= 3)%nat by lia. lia.
Qed.

Section T9.
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
Local Notation ITHEAD' := (ITHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation TRHEAD' := (TRHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation KREST' := (KREST fs0).
Local Notation CALLS := (Z.of_nat (n_calls data)).
Local Notation it_fx' := (it_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).
Local Notation fuzz_step' := (fuzz_step sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HSTATI data fs0 HFZ HSRO HKRO).
Local Notation tail1' := (tail1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HI HOK HERR HCELL HNL HSTATI data fs0).
Local Notation tail2' := (tail2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HI HOK HERR HCELL HNL HSTATI data fs0).
Local Notation tail3' := (tail3 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HI HOK HERR HCELL HNL HSTATI data fs0).
Local Notation tail4' := (tail4 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HI HOK HERR HCELL HNL HSTATI data fs0).
Local Notation target_front' := (target_front sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HNL HSTATI data fs0 HFZ HSRO HKRO).

#[using="av Hargc2"] Lemma calls_b : 1 <= CALLS <= 4. Proof. LiaFast.lf_pins (fun (av Hargc2 : LiaFast.U) => LiaFast.u0). pose proof (n_calls_range data). lia. Qed.

(* [comment removed for export] *)
#[using="Hargc2"] Lemma calls_at : forall (X : sst) f k lc kc E1 ms md hs len cap buf al ow,
  ITHEAD' X kc E1 ms md hs len cap buf al ow -> In f (s_facts X) -> f = FCond BC_NE (LIN lc [(RV, 1)]) (lconst 0) false ->
  lc = 2 ^ 64 - k -> 1 <= k <= 4 -> CALLS = k.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0).
  intros X f k lc kc E1 ms md hs len cap buf al ow HIT Hin Hf Hlc Hk.
  pose proof HIT as (_ & Hd & _ & _ & _ & _ & HR & _). pose proof calls_b as Hc.
  pose proof (sden_fact PSEGS E1 X ms f Hd Hin) as HF. rewrite Hf in HF.
  exact (rv_exit E1 lc k CALLS Hlc Hk HR Hc HF).
Qed.

#[using="Hargc2"] Lemma calls_ne : forall (X : sst) f k lc kc E1 ms md hs len cap buf al ow,
  ITHEAD' X kc E1 ms md hs len cap buf al ow -> In f (s_facts X) -> f = FCond BC_NE (LIN lc [(RV, 1)]) (lconst 0) true ->
  lc = 2 ^ 64 - k -> 1 <= k <= 4 -> CALLS <> k.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0).
  intros X f k lc kc E1 ms md hs len cap buf al ow HIT Hin Hf Hlc Hk.
  pose proof HIT as (_ & Hd & _ & _ & _ & _ & HR & _). pose proof calls_b as Hc.
  pose proof (sden_fact PSEGS E1 X ms f Hd Hin) as HF. rewrite Hf in HF.
  exact (rv_ne E1 lc k CALLS Hlc Hk HR Hc HF).
Qed.

#[using="av Hargc2"] Lemma krest_k : forall k, CALLS = Z.of_nat k -> KREST' (n_calls data - 1) = KREST' (k - 1).
Proof. LiaFast.lf_pins (fun (av Hargc2 : LiaFast.U) => LiaFast.u0). intros k H. f_equal. lia. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HFZ HSRO HKRO"] Theorem loop_tail : forall E2 ms2 md2 hs2 len cap buf al ow,
  ITHEAD' U_sw1 1 E2 ms2 md2 hs2 len cap buf al ow -> realizes PSEGS (mkCfg ms2 md2) (KREST' (n_calls data - 1)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HFZ HSRO HKRO : LiaFast.U) => LiaFast.u0).
  intros E2 ms2 md2 hs2 len cap buf al ow HIT.
  pose proof HIT as (_ & Hd2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhd & Hld & _).
  destruct lp1_chk as (Gsh & Gc & GcX & GcF & Gnx).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_sw1 LSW1 E2 ms2 md2 _ TBL_P_ok IMG_P_ok cert_LSW1 Hd2 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E3 ms3 HIn Hd3 Ha23 Hrom3 Hfr3 Hgr3. rewrite LSW1_eq in HIn. destruct HIn as [<-|[<-|[]]].
  { pose proof (it_fx' U_sw1 X1 1 E2 E3 ms2 ms3 md2 hs2 len cap buf al ow HIT Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc GcX Gnx) as HIT3.
    rewrite (krest_k 1 (calls_at X1 FCx1 1 _ 1 E3 ms3 md2 hs2 len cap buf al ow HIT3 FCx1_in FCx1_eq eq_refl ltac:(lia))).
    exact (tail1' E3 ms3 md2 hs2 len cap buf al ow HIT3). }
  pose proof (it_fx' U_sw1 F2 1 E2 E3 ms2 ms3 md2 hs2 len cap buf al ow HIT Ha23 Hd3 Hrom3 Hfr3 Hgr3 Gsh Gc GcF Gnx) as HIT3.
  apply (fuzz_step' F2 1 E3 ms3 md2 hs2 len cap buf al ow _ fz_f2 ltac:(lia) HIT3).
  intros E4 ms4 md4 hs4 HIT4. rewrite U_z2_eq in HIT4.
  pose proof HIT4 as (_ & Hd4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhd4 & Hld4 & _).
  destruct lp2_chk as (Gsh2 & Gc2 & GcX2 & GcF2 & Gnx2).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_z2 LZ2 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LZ2 Hd4 ltac:(vm_compute; reflexivity) Hhd4 Hld4).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 Hgr5. rewrite LZ2_eq in HIn. destruct HIn as [<-|[<-|[]]].
  { pose proof (it_fx' U_z2 X2 2 E4 E5 ms4 ms5 md4 hs4 len cap buf al ow HIT4 Ha45 Hd5 Hrom5 Hfr5 Hgr5 Gsh2 Gc2 GcX2 Gnx2) as HIT5.
    rewrite (krest_k 2 (calls_at X2 FCx2 2 _ 2 E5 ms5 md4 hs4 len cap buf al ow HIT5 FCx2_in FCx2_eq eq_refl ltac:(lia))).
    exact (tail2' E5 ms5 md4 hs4 len cap buf al ow HIT5). }
  pose proof (it_fx' U_z2 F3 2 E4 E5 ms4 ms5 md4 hs4 len cap buf al ow HIT4 Ha45 Hd5 Hrom5 Hfr5 Hgr5 Gsh2 Gc2 GcF2 Gnx2) as HIT5.
  apply (fuzz_step' F3 2 E5 ms5 md4 hs4 len cap buf al ow _ fz_f3 ltac:(lia) HIT5).
  intros E6 ms6 md6 hs6 HIT6. rewrite U_z3_eq in HIT6.
  pose proof HIT6 as (_ & Hd6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhd6 & Hld6 & _).
  destruct lp3_chk as (Gsh3 & Gc3 & GcX3 & GcF3 & Gnx3).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_z3 LZ3 E6 ms6 md6 _ TBL_P_ok IMG_P_ok cert_LZ3 Hd6 ltac:(vm_compute; reflexivity) Hhd6 Hld6).
  intros L E7 ms7 HIn Hd7 Ha67 Hrom7 Hfr7 Hgr7. rewrite LZ3_eq in HIn. destruct HIn as [<-|[<-|[]]].
  { pose proof (it_fx' U_z3 X3 3 E6 E7 ms6 ms7 md6 hs6 len cap buf al ow HIT6 Ha67 Hd7 Hrom7 Hfr7 Hgr7 Gsh3 Gc3 GcX3 Gnx3) as HIT7.
    rewrite (krest_k 3 (calls_at X3 FCx3 3 _ 3 E7 ms7 md6 hs6 len cap buf al ow HIT7 FCx3_in FCx3_eq eq_refl ltac:(lia))).
    exact (tail3' E7 ms7 md6 hs6 len cap buf al ow HIT7). }
  pose proof (it_fx' U_z3 F4 3 E6 E7 ms6 ms7 md6 hs6 len cap buf al ow HIT6 Ha67 Hd7 Hrom7 Hfr7 Hgr7 Gsh3 Gc3 GcF3 Gnx3) as HIT7.
  apply (fuzz_step' F4 3 E7 ms7 md6 hs6 len cap buf al ow _ fz_f4 ltac:(lia) HIT7).
  intros E8 ms8 md8 hs8 HIT8. rewrite U_z4_eq in HIT8.
  pose proof HIT8 as (_ & Hd8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhd8 & Hld8 & _).
  destruct lp4_chk as (Gsh4 & Gc4 & GcX4 & Gnx4).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_z4 LZ4 E8 ms8 md8 _ TBL_P_ok IMG_P_ok cert_LZ4 Hd8 ltac:(vm_compute; reflexivity) Hhd8 Hld8).
  intros L E9 ms9 HIn Hd9 Ha89 Hrom9 Hfr9 Hgr9. rewrite LZ4_eq in HIn. destruct HIn as [<-|[]].
  { pose proof (it_fx' U_z4 X4 4 E8 E9 ms8 ms9 md8 hs8 len cap buf al ow HIT8 Ha89 Hd9 Hrom9 Hfr9 Hgr9 Gsh4 Gc4 GcX4 Gnx4) as HIT9.
    destruct FCx4_in as (I1 & I2 & I3). pose proof calls_b as Hcb.
    pose proof (calls_ne X4 FCx4_1 1 _ 4 E9 ms9 md8 hs8 len cap buf al ow HIT9 I1 eq_refl eq_refl ltac:(lia)) as N1.
    pose proof (calls_ne X4 FCx4_2 2 _ 4 E9 ms9 md8 hs8 len cap buf al ow HIT9 I2 eq_refl eq_refl ltac:(lia)) as N2.
    pose proof (calls_ne X4 FCx4_3 3 _ 4 E9 ms9 md8 hs8 len cap buf al ow HIT9 I3 eq_refl eq_refl ltac:(lia)) as N3.
    rewrite (krest_k 4 ltac:(lia)).
    exact (tail4' E9 ms9 md8 hs8 len cap buf al ow HIT9). }
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HFZ HSRO HKRO"] Theorem target_phase : forall E3 ms md hs len cap buf,
  TRHEAD' E3 ms md hs len cap buf ->
  realizes PSEGS (mkCfg ms md) (t_emit (W 1 (zero_lines (n_calls data))) (t_exit (exit_code 0) fs0)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI HFZ HSRO HKRO : LiaFast.U) => LiaFast.u0).
  intros E3 ms md hs len cap buf HT.
  apply (target_front' E3 ms md hs len cap buf HT).
  intros E2 ms2 md2 hs2 al ow HI2. exact (loop_tail E2 ms2 md2 hs2 len cap buf al ow HI2).
Qed.

End T9.
