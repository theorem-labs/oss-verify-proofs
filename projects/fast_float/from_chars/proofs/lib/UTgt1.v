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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxPlan FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvCall UDrvExit UDrvSys UDrvHeap UDrvHeap2 UDrvRead UbStartup UbStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.UbStartup OSSVerify.Proofs.fast_float.from_chars.lib.UbStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvCall2 UUsageCert UOpenCert UOpen1 UDirCert UDir ULoopCert ULoopInv ULoop1 UEofCert UEof1 ULoopInv2 UEof3 UTgtCert Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Definition FC_cf : fact := Eval vm_compute in nth 0 (s_facts Lcf) (FRange (lconst 0) 0 0).
Definition FC_j0a : fact := Eval vm_compute in nth 0 (s_facts J0a) (FRange (lconst 0) 0 0).
Definition FC_j0a' : fact := Eval vm_compute in nth 1 (s_facts J0a) (FRange (lconst 0) 0 0).
Definition FC_j1a : fact := Eval vm_compute in nth 0 (s_facts J1a) (FRange (lconst 0) 0 0).
Definition FC_j1a' : fact := Eval vm_compute in nth 1 (s_facts J1a) (FRange (lconst 0) 0 0).
Definition FC_j1b : fact := Eval vm_compute in nth 0 (s_facts J1b0) (FRange (lconst 0) 0 0).
Definition FC_j0b : fact := Eval vm_compute in nth 0 (s_facts J0b0) (FRange (lconst 0) 0 0).
Lemma FC_cf_in : In FC_cf (s_facts Lcf). Proof. vm_compute. tauto. Qed.
Lemma FC_j0a_in : In FC_j0a (s_facts J0a). Proof. vm_compute. tauto. Qed.
Lemma FC_j0a'_in : In FC_j0a' (s_facts J0a). Proof. vm_compute. tauto. Qed.
Lemma FC_j1a_in : In FC_j1a (s_facts J1a). Proof. vm_compute. tauto. Qed.
Lemma FC_j1a'_in : In FC_j1a' (s_facts J1a). Proof. vm_compute. tauto. Qed.
Lemma FC_j1b_in : In FC_j1b (s_facts J1b0). Proof. vm_compute. tauto. Qed.
Lemma FC_j0b_in : In FC_j0b (s_facts J0b0). Proof. vm_compute. tauto. Qed.
Definition NF : lin := LIN 18446744073709551610 [(N0, 1); (CLV, 18446744073709551615)].
Lemma FC_cf_eq : FC_cf = FCond BC_EQ (lvar CLV) (lconst 0) false. Proof. vm_compute. reflexivity. Qed.
Lemma FC_j0a_eq : FC_j0a = FCond BC_NE NF (lconst 0) false. Proof. vm_compute. reflexivity. Qed.
Lemma FC_j0a'_eq : FC_j0a' = FCond BC_EQ (lvar CLV) (lconst 0) true. Proof. vm_compute. reflexivity. Qed.
Lemma FC_j1a_eq : FC_j1a = FCond BC_NE NF (lconst 0) true. Proof. vm_compute. reflexivity. Qed.
Lemma FC_j1a'_eq : FC_j1a' = FCond BC_EQ (lvar CLV) (lconst 0) true. Proof. vm_compute. reflexivity. Qed.
Lemma FC_j1b_eq : FC_j1b = FCond BC_EQ NF (lconst 0) false. Proof. vm_compute. reflexivity. Qed.
Lemma FC_j0b_eq : FC_j0b = FCond BC_EQ NF (lconst 0) true. Proof. vm_compute. reflexivity. Qed.

Lemma u_NF : forall E0 len cl, E0 N0 = Z_to_bv 64 len -> E0 CLV = Z_to_bv 64 cl -> 0 <= cl -> 6 + cl <= len < 2 ^ 64 ->
  bv_unsigned (lden E0 NF) = len - 6 - cl.
Proof.
  intros E0 len cl HN HC Hc Hl. unfold NF. rewrite u_lin2k, HN, HC, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small len) by lia. rewrite (Z.mod_small cl) by lia.
  replace (18446744073709551610 + 1 * len + 18446744073709551615 * cl) with ((len - 6 - cl) + (1 + cl) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Section T1.
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

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation TRHEAD' := (TRHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation CL := (Z.of_nat (config_len data)).
Local Notation CALLS := (Z.of_nat (n_calls data)).

#[using="Hargc2"] Lemma agr : forall E1 E2 (L : sst), agree 200 E E1 -> (200 <= s_next L)%positive -> agree (s_next L) E1 E2 -> agree 200 E E2.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). intros E1 E2 L H1 Hn H2 x Hx. etransitivity; [exact (H1 x Hx) | apply H2; lia]. Qed.

(* [comment removed for export] *)
Definition JHEAD (J : sst) (n0 : bool) (E4 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf : Z) : Prop :=
  agree 200 E E4 /\ sden PSEGS E4 J ms /\ ms_rom ms = seg_rom PSEGS /\ E4 N0 = Z_to_bv 64 len /\ E4 BUF = Z_to_bv 64 buf /\
  E4 CLV = Z_to_bv 64 CL /\ E4 RV = Z_to_bv 64 CALLS /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDS0 /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  len = Z.of_nat (length data) /\ 6 + CL <= len < cap /\ CAPOKU cap md /\
  (if n0 then len = 6 + CL else 6 + CL < len).

#[using="Type"] Lemma n_calls_cl0 : config_len data = 0%nat -> n_calls data = 1%nat.
Proof. LiaFast.lf_pins LiaFast.u0. intros H. unfold n_calls. rewrite H. reflexivity. Qed.
#[using="av Hargc2"] Lemma n_calls_cl1 : config_len data <> 0%nat -> Z.of_nat (n_calls data) = bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4 + 1.
Proof. LiaFast.lf_pins (fun (av Hargc2 : LiaFast.U) => LiaFast.u0).
  intros H. unfold n_calls. destruct (config_len data) as [|k]; [exfalso; exact (H eq_refl)|].
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 data (Z_to_bv 8 0))) 4 ltac:(lia)). rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
Definition TRLK (E3 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf : Z) : Prop :=
  agree 200 E E3 /\ sden PSEGS E3 U_lk ms /\ ms_rom ms = seg_rom PSEGS /\ E3 N0 = Z_to_bv 64 len /\ E3 BUF = Z_to_bv 64 buf /\
  E3 CLV = Z_to_bv 64 CL /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDS0 /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  (config_len data <> 0%nat -> mrd PSEGS (ms_mem ms) (Z_to_bv 64 (buf + 2)) = Some (nth 2 data (Z_to_bv 8 0))) /\
  len = Z.of_nat (length data) /\ 6 + CL <= len < cap /\ CAPOKU cap md.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HNL HSTATI"] Lemma tr_lock : forall E3 ms md hs len cap buf T,
  TRHEAD' E3 ms md hs len cap buf ->
  (forall E5 ms5, TRLK E5 ms5 md hs len cap buf -> realizes PSEGS (mkCfg ms5 md) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HNL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E3 ms md hs len cap buf T (Ha3 & Hd3 & Hrom3 & HN3 & HB3 & HCLV3 & Hm3 & Hh3 & Hhd & Hld & Hfd & Hfs & Hblk & Hd2b & HL & Hlen & Hcap) K.
  pose proof (capoku_bounds cap md Hcap) as Hcb. pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  destruct HIMG as [HI1 HI2].
  pose proof HOK as ((HB1' & HB2') & _ & _ & _ & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh3) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & Hstk & _ & _).
  assert (Hbr' : 16 <= buf /\ buf + cap <= HTOP) by (destruct Hbr as [Hbr|Hbr]; lia).
  assert (HO2 : outside E3 (s_rgs Ltr) (Z_to_bv 64 (buf + 2))).
  { apply (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC (conj HI1 HI2) HI HOK E3 (s_rgs Ltr) hs (ms_mem ms) md buf cap); [| exact Hh3 | exact Hblk |].
    - exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HSTATI E3 (s_rgs Ltr) Ha3 ltac:(vm_compute; reflexivity)).
    - rewrite u_small64 by (unfold two64; lia). lia. }
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 STGL Ltr LT0 E3 ms md _ TBL_P_ok IMG_P_ok cert_LT0 Hd3 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E4 ms4 HIn Hd4 Ha34 Hrom4 Hfr4 Hgr4. rewrite LT0_eq in HIn. destruct HIn as [<-|[]].
  destruct (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HI HOK HERR HCELL HSTATI
              E3 E4 Ltr Llk ms ms4 hs md buf [] Ha3 Ha34 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd3 Hd4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr4 Hgr4 Hm3 Hh3
              ltac:(exists cap; split; [exact Hblk | cbn; lia]) ltac:(split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]))
    as (Ha4 & Hm4 & Hh4 & _).
  rewrite Hrom3 in Hrom4.
  apply (fx_nlk E4 Llk ms4 md T 0x52af8 Hd4 eq_refl eq_refl hok_lk ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) (HNL hs _ md Hh4) Hhd Hld).
  intros E5 ms5 Ha45 Hd5 Hmem5 Hrom5. rewrite U_lk_eq in Hd5.
  apply (K E5 ms5).
  assert (HE53 : forall x, (x < s_next Ltr)%positive -> E5 x = E3 x).
  { intros x Hx. rewrite <- (Ha45 x) by (apply (Pos.lt_le_trans _ (s_next Ltr)); [exact Hx | vm_compute; congruence]). symmetry. exact (Ha34 x Hx). }
  split; [intros x Hx; etransitivity; [exact (Ha4 x Hx) | apply Ha45; apply (Pos.lt_le_trans _ 200); [exact Hx | vm_compute; congruence]]|].
  split; [exact Hd5|]. split; [rewrite Hrom5; exact Hrom4|].
  split; [rewrite HE53 by (vm_compute; reflexivity); exact HN3|].
  split; [rewrite HE53 by (vm_compute; reflexivity); exact HB3|].
  split; [rewrite HE53 by (vm_compute; reflexivity); exact HCLV3|].
  rewrite Hmem5.
  split; [exact Hm4|]. split; [exact Hh4|]. split; [exact Hhd|]. split; [exact Hld|]. split; [exact Hfd|]. split; [exact Hfs|].
  split; [exact Hblk|]. split; [| split; [exact HL | split; [exact Hlen | exact Hcap]]].
  intros HCL1. unfold mrd. rewrite (Hfr4 _ HO2). exact (Hd2b HCL1).
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Lemma tr_front_lk : forall E3 ms md hs len cap buf T,
  TRLK E3 ms md hs len cap buf ->
  (forall E4 ms4, JHEAD J0 true E4 ms4 md hs len cap buf -> realizes PSEGS (mkCfg ms4 md) T) ->
  (forall E4 ms4, JHEAD J1 false E4 ms4 md hs len cap buf -> realizes PSEGS (mkCfg ms4 md) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E3 ms md hs len cap buf T (Ha3 & Hd3 & Hrom3 & HN3 & HB3 & HCLV3 & Hm3 & Hh3 & Hhd & Hld & Hfd & Hfs & Hblk & Hd2b & HL & Hlen & Hcap) K0 K1.
  pose proof (capoku_bounds cap md Hcap) as Hcb. pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  destruct HIMG as [HI1 HI2].
  pose proof HOK as ((HB1' & HB2') & _ & _ & _ & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh3) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & Hstk & _ & _).
  assert (Hbr' : 16 <= buf /\ buf + cap <= HTOP) by (destruct Hbr as [Hbr|Hbr]; lia).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 STG U_lk LT1 E3 ms md _ TBL_P_ok IMG_P_ok cert_LT1 Hd3 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E4 ms4 HIn Hd4 Ha34 Hrom4 Hfr4 Hgr4.
  assert (HLc : cells_tmpl L = true) by (rewrite LT1_eq in HIn; destruct HIn as [<-|[<-|[<-|[]]]]; vm_compute; reflexivity).
  destruct (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HI HOK HERR HCELL HSTATI
              E3 E4 U_lk L ms ms4 hs md buf [] Ha3 Ha34 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd3 Hd4 ltac:(vm_compute; reflexivity) HLc Hfr4 Hgr4 Hm3 Hh3
              ltac:(exists cap; split; [exact Hblk | cbn; lia]) ltac:(split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]))
    as (Ha4 & Hm4 & Hh4 & _).
  rewrite Hrom3 in Hrom4.
  assert (HE43 : forall x, (x < s_next U_lk)%positive -> E4 x = E3 x) by (intros x Hx; symmetry; exact (Ha34 x Hx)).
  assert (HN4 : E4 N0 = Z_to_bv 64 len) by (rewrite HE43 by (vm_compute; reflexivity); exact HN3).
  assert (HB4 : E4 BUF = Z_to_bv 64 buf) by (rewrite HE43 by (vm_compute; reflexivity); exact HB3).
  assert (HCLV4 : E4 CLV = Z_to_bv 64 CL) by (rewrite HE43 by (vm_compute; reflexivity); exact HCLV3).
  assert (UCL : bv_unsigned (E4 CLV) = CL) by (rewrite HCLV4; apply u_small64; unfold two64; lia).
  assert (UNF : bv_unsigned (lden E4 NF) = len - 6 - CL) by (apply u_NF; [exact HN4 | exact HCLV4 | lia | lia]).
  assert (Hnb : forall (J : sst) (n0 : bool) (Ls : sst) (σ : tree lin) E7 ms7,
             agree 200 E E7 -> sden PSEGS E7 Ls ms7 -> ms_rom ms7 = seg_rom PSEGS -> entails Ls J σ = true -> state_wf J = true ->
             sig_id_below σ 390 = true -> (300 <= s_next Ls)%positive ->
             E7 N0 = Z_to_bv 64 len -> E7 BUF = Z_to_bv 64 buf -> E7 CLV = Z_to_bv 64 CL -> lden E7 (svar σ RV) = Z_to_bv 64 CALLS ->
             MFXR' (ms_mem ms7) -> hi_Heap HI hs (ms_mem ms7) md -> (if n0 then len = 6 + CL else 6 + CL < len) ->
             JHEAD J n0 (ecomp E7 σ) ms7 md hs len cap buf).
  { intros J n0 Ls σ E7 ms7 Ha7 Hd7 Hrom7 Hent Hwf Hsid Hnx HN7 HB7 HC7 HR7 Hm7 Hh7 Hn0.
    pose proof (ecomp_agree E7 σ 390 Hsid) as Ha78.
    split; [intros x Hx; etransitivity; [exact (Ha7 x Hx) | apply Ha78; lia]|].
    split; [exact (entails_sden PSEGS E7 Ls J σ ms7 (sden_0 _ _ _ _ Hd7) Hent Hwf)|]. split; [exact Hrom7|].
    split; [rewrite <- (Ha78 N0) by (vm_compute; reflexivity); exact HN7|].
    split; [rewrite <- (Ha78 BUF) by (vm_compute; reflexivity); exact HB7|].
    split; [rewrite <- (Ha78 CLV) by (vm_compute; reflexivity); exact HC7|].
    split; [unfold ecomp; exact HR7|]. split; [exact Hm7|]. split; [exact Hh7|]. split; [exact Hhd|]. split; [exact Hld|].
    split; [exact Hfd|]. split; [exact Hfs|]. split; [exact Hblk|]. split; [exact HL|]. split; [lia|]. split; [exact Hcap | exact Hn0]. }
  rewrite LT1_eq in HIn. destruct HIn as [<-|[<-|[<-|[]]]].
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E4 Lcf ms4 _ Hd4 FC_cf_in) as HF. rewrite FC_cf_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_lconst, lden_lvar in HF.
    assert (HCL1 : config_len data <> 0%nat) by (intros Hc; rewrite HCLV4, Hc in HF; vm_compute in HF; discriminate HF).
    pose proof (n_calls_cl1 HCL1) as HNC.
    set (d2 := nth 2 data (Z_to_bv 8 0)) in *. set (u2 := bv_unsigned d2) in *.
    assert (Hu2 : 0 <= u2 < 256) by (pose proof (bv_unsigned_in_range _ d2) as R; unfold bv_modulus in R; exact R).
    assert (HO2 : outside E3 (s_rgs U_lk) (Z_to_bv 64 (buf + 2))).
    { apply (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC (conj HI1 HI2) HI HOK E3 (s_rgs U_lk) hs (ms_mem ms) md buf cap); [| exact Hh3 | exact Hblk |].
      - exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HSTATI E3 (s_rgs U_lk) Ha3 ltac:(vm_compute; reflexivity)).
      - rewrite u_small64 by (unfold two64; lia). lia. }
    assert (HD2 : mrd PSEGS (ms_mem ms4) (Z_to_bv 64 (buf + 2)) = Some d2).
    { unfold mrd. rewrite (Hfr4 _ HO2). exact (Hd2b HCL1). }
    destruct (fx_add_var PSEGS E4 Lcf ms4 (Z_to_bv 64 (u2 mod 4)) Hd4) as (E5 & Ha45 & HJ5 & Hd5).
    destruct (fx_add_var PSEGS E5 (add_var Lcf) ms4 (Z_to_bv 64 (u2 / 4)) Hd5) as (E6 & Ha56 & HH6 & Hd6).
    change (s_next Lcf) with JV in Ha45, HJ5. change (s_next (add_var Lcf)) with HV in Ha56, HH6.
    assert (HJ6 : E6 JV = Z_to_bv 64 (u2 mod 4)) by (rewrite <- (Ha56 JV) by (vm_compute; reflexivity); exact HJ5).
    assert (HE64 : forall x, (x < JV)%positive -> E6 x = E4 x).
    { intros x Hx. rewrite <- (Ha56 x) by (unfold HV, JV in *; lia). rewrite <- (Ha45 x) by exact Hx. reflexivity. }
    assert (HB6 : E6 BUF = Z_to_bv 64 buf) by (rewrite HE64 by (vm_compute; reflexivity); exact HB4).
    assert (Ha6 : agree 200 E E6) by (intros x Hx; etransitivity; [exact (Ha4 x Hx) | symmetry; apply HE64; unfold JV; lia]).
    assert (UB6 : bv_unsigned (lden E6 (laddc (lvar BUF) 2)) = buf + 2).
    { rewrite lden_laddc, lden_lvar, HB6. rewrite (u_small64 buf) by (unfold two64; lia). apply u_small64. unfold two64; lia. }
    assert (Hd7 : sden PSEGS E6 U_cf ms4).
    { rewrite <- U_cf_eq. apply fx_add_rg.
      - apply fx_add_fact; [apply fx_add_fact; [exact Hd6 | vm_compute; reflexivity |] | vm_compute; reflexivity |].
        + pose proof (Z.mod_pos_bound u2 4 ltac:(lia)) as M4.
          cbn [fact_ok]. rewrite lden_lvar, HJ6. rewrite u_small64 by (unfold two64; lia). lia.
        + assert (D4 : 0 <= u2 / 4 < 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
          cbn [fact_ok]. rewrite lden_lvar, HH6. rewrite u_small64 by (unfold two64; lia). lia.
      - rewrite U_cf_eq. exact wf_cf.
      - change CFGR with (track (RGz (laddc (lvar BUF) 2) 1 RW TEmpty) 0 [BV (LIN 0 [(JV, 1); (HV, 4)]) 0]).
        apply rg_track_rdn; [| lia | rsz_simpl; cbn; lia |].
        + apply (rg_rw_stk E6 (ms_mem ms4) (laddc (lvar BUF) 2) 1 (buf + 2) UB6 ltac:(lia) ltac:(unfold two64; lia)).
          split; [lia|]. split; [lia|]. intros a Ha. replace a with (buf + 2) by lia. unfold wa. split.
          * destruct Hstk as (_ & _ & HS). destruct (HS (buf + 2) ltac:(lia)) as [Hw _]. unfold wa in Hw.
            unfold wview in *. rewrite (Hfr4 _ HO2). exact Hw.
          * exists d2. exact HD2.
        + cbn [RGz rg_base track length]. rewrite UB6, Z.add_0_r. rewrite rdn_unfold. rewrite HD2. cbn [rdn map].
          assert (Hbd : bden E6 (BV (LIN 0 [(JV, 1); (HV, 4)]) 0) = d2).
          { pose proof (Z.mod_pos_bound u2 4 ltac:(lia)) as M4. pose proof (Z.div_pos u2 4 ltac:(lia) ltac:(lia)) as D4.
            pose proof (Z.div_mod u2 4 ltac:(lia)) as DM.
            unfold bden. rewrite u_lin2k, HJ6, HH6. rewrite (u_small64 (u2 mod 4)) by (unfold two64; lia).
            rewrite (u_small64 (u2 / 4)) by (unfold two64; lia). rewrite Z.shiftr_0_r.
            replace ((0 + 1 * (u2 mod 4) + 4 * (u2 / 4)) mod 2 ^ 64) with u2 by (rewrite Z.mod_small; lia).
            unfold u2. apply Z_to_bv_bv_unsigned. }
          rewrite Hbd. reflexivity.
      - cbn [s_rgs add_fact add_var]. rewrite Forall_forall. intros R' HR'.
        assert (Hp : 0 < csz R').
        { pose proof (eq_refl : forallb (fun R => Z.ltb 0 (csz R)) (s_rgs Lcf) = true) as X. rewrite forallb_forall in X.
          apply Z.ltb_lt. exact (X R' HR'). }
        pose proof HR' as HR'L. apply In_nth_error in HR'L as (i & Hi).
        apply rg_disj_bytes; [rewrite (csz_rsz E6 R') by lia; lia | unfold CFGR; rsz_simpl; lia |].
        intros j Hj. unfold CFGR in Hj. rsz_simpl_in Hj. unfold CFGR. cbn [RGz rg_base]. rewrite UB6.
        assert (HO : outside E6 (s_rgs Lcf) (Z_to_bv 64 (buf + 2 + j))).
        { apply (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC (conj HI1 HI2) HI HOK E6 (s_rgs Lcf) hs (ms_mem ms) md buf cap); [| exact Hh3 | exact Hblk |].
          - exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HSTATI E6 (s_rgs Lcf) Ha6 ltac:(vm_compute; reflexivity)).
          - rewrite u_small64 by (unfold two64; lia). lia. }
        pose proof (outside_nth E6 _ _ i R' HO Hi) as X. rewrite u_small64 in X by (unfold two64; lia). exact X. }
    (* [comment removed for export] *)
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 STG U_cf LCF E6 ms4 md _ TBL_P_ok IMG_P_ok cert_LCF Hd7 ltac:(vm_compute; reflexivity) Hhd Hld).
    intros L E7 ms7 HIn Hd8 Ha67 Hrom7 Hfr7 Hgr7.
    assert (HE76 : forall x, (x < s_next U_cf)%positive -> E7 x = E6 x) by (intros x Hx; symmetry; exact (Ha67 x Hx)).
    assert (Ha7 : agree 200 E E7) by (intros x Hx; etransitivity; [exact (Ha6 x Hx) | apply Ha67; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (HN7 : E7 N0 = Z_to_bv 64 len) by (rewrite HE76, HE64 by (vm_compute; reflexivity); exact HN4).
    assert (HB7 : E7 BUF = Z_to_bv 64 buf) by (rewrite HE76 by (vm_compute; reflexivity); exact HB6).
    assert (HC7 : E7 CLV = Z_to_bv 64 CL) by (rewrite HE76, HE64 by (vm_compute; reflexivity); exact HCLV4).
    assert (HJ7 : E7 JV = Z_to_bv 64 (u2 mod 4)) by (rewrite HE76 by (vm_compute; reflexivity); exact HJ6).
    assert (UNF7 : bv_unsigned (lden E7 NF) = len - 6 - CL) by (apply u_NF; [exact HN7 | exact HC7 | lia | lia]).
    assert (XB : XBLK HI E6 (s_rgs U_cf) hs).
    { intros R x HR Hin. replace (skipn 22 (s_rgs U_cf)) with [CFGR] in HR by (vm_compute; reflexivity). destruct HR as [<-|[]].
      unfold in_rg in Hin. unfold CFGR in Hin. cbn [RGz rg_base] in Hin. rewrite UB6 in Hin. rsz_simpl_in Hin.
      exists buf, cap. split; [exact Hblk | lia]. }
    assert (S21 : shape21 (s_rgs U_cf)) by (vm_compute; reflexivity).
    assert (Hh7 : hi_Heap HI hs (ms_mem ms7) md).
    { apply (heap_fx_g sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HI HOK HERR HCELL HSTATI
               E6 E7 U_cf L ms4 ms7 hs md Ha6 Ha7 S21 XB Hd7 Hd8 ltac:(vm_compute; reflexivity)); [| exact Hfr7 | exact Hgr7 | exact Hh4].
      rewrite LCF_eq in HIn. destruct HIn as [<-|[<-|[]]]; vm_compute; reflexivity. }
    assert (Hm7 : MFXR' (ms_mem ms7)).
    { apply (mfxr_fx_g sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI HOK E6 U_cf hs (ms_mem ms4) md (ms_mem ms4) (ms_mem ms7) Ha6 S21 XB Hh4 Hfr7 Hm4). }
    rewrite Hrom4 in Hrom7.
    assert (HRV : forall σ, svar σ RV = laddc (lvar JV) 1 -> lden E7 (svar σ RV) = Z_to_bv 64 CALLS).
    { intros σ Hσ. rewrite Hσ, lden_laddc, lden_lvar, HJ7, HNC. rewrite u_small64 by (unfold two64; pose proof (Z.mod_pos_bound u2 4); lia). reflexivity. }
    rewrite LCF_eq in HIn. destruct HIn as [<-|[<-|[]]].
    + (* [comment removed for export] *)
      pose proof (sden_fact PSEGS E7 J1b0 ms7 _ Hd8 FC_j1b_in) as HF1. rewrite FC_j1b_eq in HF1. cbn [fact_ok branch_taken] in HF1.
      rewrite lden_lconst in HF1.
      assert (Hn1 : 6 + CL < len).
      { destruct (Z.eq_dec len (6 + CL)) as [Hc|Hc]; [|lia]. exfalso. assert (X : lden E7 NF = Z_to_bv 64 0) by (apply bv_eq; rewrite UNF7; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
        rewrite X in HF1. vm_compute in HF1. discriminate HF1. }
      pose proof (fx_weaken PSEGS E7 J1b0 ms7 (firstn 22 (s_rgs J1b0)) WS21 Hd8 wk_j1b ltac:(rewrite J1b_eq; exact wf_j1b)) as Hd9. rewrite J1b_eq in Hd9.
      apply (K1 (ecomp E7 sig_j1b) ms7).
      apply (Hnb J1 false J1b sig_j1b E7 ms7 Ha7 Hd9 Hrom7 ent_j1b wf_j1 sid_j1b ltac:(vm_compute; congruence) HN7 HB7 HC7); [| exact Hm7 | exact Hh7 | exact Hn1].
      apply HRV. vm_compute. reflexivity.
    + (* [comment removed for export] *)
      pose proof (sden_fact PSEGS E7 J0b0 ms7 _ Hd8 FC_j0b_in) as HF1. rewrite FC_j0b_eq in HF1. cbn [fact_ok branch_taken] in HF1.
      rewrite lden_lconst in HF1. apply bv_eqb_eq in HF1.
      assert (Hn0 : len = 6 + CL) by (rewrite HF1 in UNF7; change (bv_unsigned (Z_to_bv 64 0)) with 0 in UNF7; lia).
      pose proof (fx_weaken PSEGS E7 J0b0 ms7 (firstn 22 (s_rgs J0b0)) WS21 Hd8 wk_j0b ltac:(rewrite J0b_eq; exact wf_j0b)) as Hd9. rewrite J0b_eq in Hd9.
      apply (K0 (ecomp E7 sig_j0b) ms7).
      apply (Hnb J0 true J0b sig_j0b E7 ms7 Ha7 Hd9 Hrom7 ent_j0b wf_j0 sid_j0b ltac:(vm_compute; congruence) HN7 HB7 HC7); [| exact Hm7 | exact Hh7 | exact Hn0].
      apply HRV. vm_compute. reflexivity.
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E4 J0a ms4 _ Hd4 FC_j0a_in) as HF1. rewrite FC_j0a_eq in HF1. cbn [fact_ok branch_taken] in HF1.
    pose proof (sden_fact PSEGS E4 J0a ms4 _ Hd4 FC_j0a'_in) as HF2. rewrite FC_j0a'_eq in HF2. cbn [fact_ok branch_taken] in HF2.
    rewrite lden_lconst in HF1, HF2. rewrite lden_lvar in HF2. apply negb_false_iff in HF1. apply bv_eqb_eq in HF1. apply bv_eqb_eq in HF2.
    assert (HCL0 : config_len data = 0%nat) by (rewrite HF2 in UCL; change (bv_unsigned (Z_to_bv 64 0)) with 0 in UCL; lia).
    assert (Hn0 : len = 6 + CL) by (rewrite HF1 in UNF; change (bv_unsigned (Z_to_bv 64 0)) with 0 in UNF; lia).
    apply (K0 (ecomp E4 sig_j0a) ms4).
    apply (Hnb J0 true J0a sig_j0a E4 ms4 Ha4 Hd4 Hrom4 ent_j0a wf_j0 sid_j0a ltac:(vm_compute; congruence) HN4 HB4 HCLV4); [| exact Hm4 | exact Hh4 | exact Hn0].
    replace (svar sig_j0a RV) with (lconst 1) by (vm_compute; reflexivity). rewrite lden_lconst, n_calls_cl0 by exact HCL0. reflexivity.
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E4 J1a ms4 _ Hd4 FC_j1a_in) as HF1. rewrite FC_j1a_eq in HF1. cbn [fact_ok branch_taken] in HF1.
    pose proof (sden_fact PSEGS E4 J1a ms4 _ Hd4 FC_j1a'_in) as HF2. rewrite FC_j1a'_eq in HF2. cbn [fact_ok branch_taken] in HF2.
    rewrite lden_lconst in HF1, HF2. rewrite lden_lvar in HF2. apply negb_true_iff in HF1. apply bv_eqb_eq in HF2.
    assert (HCL0 : config_len data = 0%nat) by (rewrite HF2 in UCL; change (bv_unsigned (Z_to_bv 64 0)) with 0 in UCL; lia).
    assert (Hn1 : 6 + CL < len).
    { destruct (Z.eq_dec len (6 + CL)) as [Hc|Hc]; [|lia]. exfalso. assert (X : lden E4 NF = Z_to_bv 64 0) by (apply bv_eq; rewrite UNF; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
      rewrite X in HF1. vm_compute in HF1. discriminate HF1. }
    apply (K1 (ecomp E4 sig_j1a) ms4).
    apply (Hnb J1 false J1a sig_j1a E4 ms4 Ha4 Hd4 Hrom4 ent_j1a wf_j1 sid_j1a ltac:(vm_compute; congruence) HN4 HB4 HCLV4); [| exact Hm4 | exact Hh4 | exact Hn1].
    replace (svar sig_j1a RV) with (lconst 1) by (vm_compute; reflexivity). rewrite lden_lconst, n_calls_cl0 by exact HCL0. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HNL HSTATI"] Theorem tr_front : forall E3 ms md hs len cap buf T,
  TRHEAD' E3 ms md hs len cap buf ->
  (forall E4 ms4, JHEAD J0 true E4 ms4 md hs len cap buf -> realizes PSEGS (mkCfg ms4 md) T) ->
  (forall E4 ms4, JHEAD J1 false E4 ms4 md hs len cap buf -> realizes PSEGS (mkCfg ms4 md) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HNL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E3 ms md hs len cap buf T HT K0 K1. apply (tr_lock E3 ms md hs len cap buf T HT).
  intros E5 ms5 HT5. exact (tr_front_lk E5 ms5 md hs len cap buf T HT5 K0 K1).
Qed.
End T1.
