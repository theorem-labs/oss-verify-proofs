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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvCall2 UbStdioDefs UbExitBase UUsageCert UOpenCert UOpen1 UDirCert UUsage3 UUsage4 UDir ULoopCert ULoopInv ULoop1 ULoop2 ULoop3 ULoop4 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(* [comment removed for export] *)
Lemma hok_rf : havoc_ok Lrf [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_rf2 : sst := Eval vm_compute in sw_template Lrf 0x561c8 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U_rf2_eq : sw_template Lrf 0x561c8 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U_rf2. Proof. cert_refl_vm constr:(U_rf2). Qed.
Set Default Proof Mode "Classic".
Lemma wf_rf2 : state_wf U_rf2 = true. Proof. vm_compute. reflexivity. Qed.
Definition LRF2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_rf2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LRF2 : fx_explore TBL_P IMG_P 4000 S1 U_rf2 [] = LRF2. Proof. cert_refl_vm constr:(LRF2). Qed.
Set Default Proof Mode "Classic".
Definition Lrf3 : sst := Eval vm_compute in nth 0 LRF2 P_main2.
Lemma LRF2_eq : LRF2 = [Lrf3]. Proof. reflexivity. Qed.

Definition MSG_RF : list byte := s2b "cli: input >= 67108864 bytes, refused" ++ nl.
Lemma msg_rf_eq : msg_refused = MSG_RF. Proof. reflexivity. Qed.

Section RF.
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
Local Notation a1s := (nth 1 av []).
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation HEAPX' := (HEAPX IMG_LO IMG_END HTOP STATIC).
Local Notation LHEAD' := (LHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation FDF' := (FDF av).
Local Notation seg_xfer' := (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).
Local Notation avoid_m2' := (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI).
Local Notation blk_out' := (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HI HOK).
Local Notation mfxr_chg' := (mfxr_chg sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC).

Local Notation RFHEAD' := (RFHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).

#[using="Hsp"] Lemma SLr : 0x7fff80000000 <= bv_unsigned sp0. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_lo sp0 Hsp). Qed.
#[using="Hsp"] Lemma SHr : bv_unsigned sp0 <= 0x800000000000. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_hi sp0 Hsp). Qed.

Definition INVR (m : word -> option byte) : Prop := MFXR' m /\ NL m.

#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG"] Lemma invr_fx : forall E' (S : sst) m m', agree 200 E E' -> shape (s_rgs S) = shape (s_rgs P_main2) ->
  (forall x, outside E' (s_rgs S) x -> m' x = m x) -> INVR m -> INVR m'.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG : LiaFast.U) => LiaFast.u0).
  intros E' S m m' Ha Hs Hfr [Hm Hn]. split; [exact (mfxr_fx sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC E' S m m' Ha Hs Hfr Hm)|].
  apply (nl_same av Hargc2 m m'); [|exact Hn]. apply Hfr. apply (outside_m2 sp0 av ev tid rdraw regs E' S _ Ha Hs).
  pose proof (exg_outside2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 0x97c23 1 0 ltac:(unfold EXG_RANGES; cbn; tauto) ltac:(lia)) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

#[using="Hsp Hargc2 E"] Lemma invr_sw : forall m m' su bufp bufsz, sw_post m su 0x66bd8 bufp bufsz m' ->
  bv_unsigned sp0 - 65536 <= su - 112 -> su <= bv_unsigned sp0 -> INVR m -> INVR m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 E : LiaFast.U) => LiaFast.u0).
  intros m m' su bufp bufsz Hpost Hs1 Hs2 [Hm Hn]. pose proof SLr. pose proof SHr. split.
  - intros x Hx Hh Hr.
    pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
    pose proof (outside_nth_c E _ x 5 (lconst 0x66bd8) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
    rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
    rewrite u_small64 in X0r by (unfold two64; lia). rewrite u_lconst in X5r by lia.
    rewrite (swp_agree _ _ _ _ _ _ Hpost x); [exact (Hm x Hx Hh Hr) | lia | lia | lia].
  - apply (nl_same av Hargc2 m m'); [|exact Hn]. apply (swp_agree _ _ _ _ _ _ Hpost); rewrite u_small64 by (unfold two64; lia); lia.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX"] Lemma exit_glob_of_MFXR : forall m, MFXR' m -> NL m -> exit_glob m.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX : LiaFast.U) => LiaFast.u0).
  intros m Hm Hnl. pose proof SLr as L.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  assert (Hx : forall lo n, In (lo, n) EXG_RANGES -> lo <> 0x97c23 -> rdn PSEGS m (Z_to_bv 64 lo) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 lo) n).
  { intros lo n Hin Hne. pose proof exg_miss as HM. rewrite forallb_forall in HM. pose proof (HM _ Hin) as Hmo. cbv beta in Hmo.
    assert (Hb : 0x10000 <= lo /\ lo + Z.of_nat n <= 0x99000 /\ (forall i, 0 <= i < Z.of_nat n -> ~ ioutside EXGX (lo + i)) /\
                 (forall i, 0 <= i < Z.of_nat n -> ~ RSX (lo + i))).
    { unfold EXG_RANGES in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn; split; [lia|]; split; [lia|]; split;
        [intros i Hi Hc; cbn [ioutside EXGX] in Hc; lia | intros i Hi Hc; unfold RSX, RS_LO in Hc; lia]|]). destruct Hin. }
    destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4).
    apply rdn_ext_rd1; [lia | unfold two64; lia |].
    intros i Hi. unfold rd1. rewrite (Hm _ (exg_outside2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 lo n i Hin Hi)).
    - rewrite (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME lo n i) by (lia || exact Hmo). reflexivity.
    - rewrite u_small64 by (unfold two64; lia). intros (Q1 & Q2). pose proof (HSTATX _ (Hb3 i Hi)) as Q3.
      destruct HIMG as [HI1 HI2]. destruct Q2 as [Q2|[Q2|Q2]]; [exact (Q2 Q3) | lia | lia].
    - rewrite u_small64 by (unfold two64; lia). exact (Hb4 i Hi). }
  pose proof exit_glob_pristine as P. unfold exit_glob in *.
  rewrite (Hx 0x97bf8 4%nat), (Hx 0x628d0 8%nat), (Hx 0x66e18 1%nat), (Hx 0x98050 8%nat), (Hx 0x98040 8%nat),
    (Hx 0x66db0 8%nat), (Hx 0x66cc0 8%nat) by (unfold EXG_RANGES; cbn; tauto || lia).
  destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). repeat split; assumption.
Qed.

#[using="Type"] Lemma fd2_of_fdf : forall k, fd_lookup (FDF' k) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k. unfold FDF, fd_insert. cbn [fd_lookup fst].
  replace (bv_eqb (Z_to_bv 64 3) (Z_to_bv 64 2)) with false by (vm_compute; reflexivity). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX HNL E"] Theorem refused_path : forall E1 ms md hs, RFHEAD' E1 ms md hs -> realizes PSEGS (mkCfg ms md) (t_body data fs0).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX HNL E : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs (Ha1 & Hd1 & Hrom1 & Hm1 & Hh1 & Hhd & Hld & Hfs & (k & Hfdk) & Hbig).
  pose proof SLr as SL. pose proof SHr as SH.
  assert (HT : t_body data fs0 = t_emit (W 2 MSG_RF) (t_exit (exit_code 2) (m_fs md))).
  { unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
    rewrite Hfs. reflexivity. }
  rewrite HT.
  assert (HI1 : INVR (ms_mem ms)) by (split; [exact Hm1 | exact (HNL hs (ms_mem ms) md Hh1)]).
  assert (Hfd2d : fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite Hfdk; apply fd2_of_fdf).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  assert (HS1 : lden E1 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE1 by lia; reflexivity).
  assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x561c8) by (apply (getr_leaf_c PSEGS E1 Lrf); [exact Hd1 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms) 2 = Z_to_bv 64 (bv_unsigned sp0 - 576)).
  { rewrite (getr_leaf PSEGS E1 Lrf ms 2 (laddc SP0 (-576)) Hd1) by (vm_compute; reflexivity). apply (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E1 (-576) HE1). lia. }
  assert (R10 : getr (ms_regs ms) 10 = Z_to_bv 64 0x66bd8) by (apply (getr_leaf_c PSEGS E1 Lrf); [exact Hd1 | vm_compute; reflexivity]).
  assert (R11 : getr (ms_regs ms) 11 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E1 Lrf); [exact Hd1 | vm_compute; reflexivity]).
  assert (R12 : getr (ms_regs ms) 12 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E1 Lrf); [exact Hd1 | vm_compute; reflexivity]).
  assert (F40 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x66bd8 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 522)))).
  { rewrite (rdn_trk_c E1 Lrf ms 5 0x66bd8 40 8 (bvs_of (laddc SP0 (-522)) 8) Hd1
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E1 (-522) HE1) by lia. reflexivity. }
  assert (F56 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x66bd8 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite (rdn_trk_c E1 Lrf ms 5 0x66bd8 56 8 (bvs_of (laddc SP0 (-560)) 8) Hd1
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E1 (-560) HE1) by lia. reflexivity. }
  assert (F88 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x66bd8 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite (rdn_trk_c E1 Lrf ms 5 0x66bd8 88 8 (bvs_of (laddc SP0 (-560)) 8) Hd1
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E1 (-560) HE1) by lia. reflexivity. }
  assert (F96 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x66bd8 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
  { rewrite (rdn_trk_c E1 Lrf ms 5 0x66bd8 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd1
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
  assert (F120 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x66bd8 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
  { rewrite (rdn_img_c E1 Lrf ms 5 0x66bd8 120 4 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F48 : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (0x66bd8 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
  { rewrite (rdn_img_c E1 Lrf ms 5 0x66bd8 48 8 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (SWF : sw_file (ms_mem ms) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 522) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
  { constructor; assumption. }
  assert (SSP : ssp_cells (ms_mem ms) (lden E1 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x65b58) with (Z_to_bv 64 (0x65a18 + 320)) by reflexivity.
      rewrite (rdn_img_c E1 Lrf ms 3 0x65a18 320 8 Hd1 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x97c00) with (Z_to_bv 64 (0x97c00 + 0)) by reflexivity.
      rewrite (rdn_trk_c E1 Lrf ms 8 0x97c00 0 8 (bvs_of (lvar 5) 8) Hd1
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (RDP : rdn PSEGS (ms_mem ms) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (length MSG_RF) = Some MSG_RF).
  { replace (bv_unsigned sp0 - 560) with (bv_unsigned sp0 + -65536 + 64976) by lia.
    rewrite (rdn_trk_sp sp0 SL SH E1 Lrf ms 0 (-65536) 64976 (length MSG_RF)
               [BK 99; BK 108; BK 105; BK 58; BK 32; BK 105; BK 110; BK 112; BK 117; BK 116; BK 32; BK 62; BK 61; BK 32; BK 54; BK 55; BK 49; BK 48; BK 56; BK 56;
                BK 54; BK 52; BK 32; BK 98; BK 121; BK 116; BK 101; BK 115; BK 44; BK 32; BK 114; BK 101; BK 102; BK 117; BK 115; BK 101; BK 100; BK 10] Hd1
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) HS1 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (FRM : frame_in E1 Lrf 0 64848 112 (bv_unsigned sp0 - 576 - 112)).
  { apply (frame_sp sp0 SL SH E1 Lrf 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS1 | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia]. }
  assert (HWF : state_wf (sw_template Lrf (bv_unsigned (Z_to_bv 64 0x561c8)) 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0)) = true).
  { rewrite u_small64 by (unfold two64; lia). rewrite U_rf2_eq. exact wf_rf2. }
  apply (rzc_conseq PSEGS DCFG _ (t_emit (map (WriteEv (Z_to_bv 64 2)) (MSG_RF ++ [])) (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs md)))));
    [| apply tail_1].
  apply (fx_stdio_write E1 Lrf ms md _ (bv_unsigned sp0 - 576) 0x66bd8 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 522) 2
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E1 (lvar 5)) (Z_to_bv 64 0x561c8) MSG_RF []
           0 64848 5 (rgn Lrf 5) (laddc SP0 (-560)) (lconst 80) (lconst 0)
           Hd1 eq_refl eq_refl Hrom1 hok_rf HWF FRM (rgn_eq Lrf 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) R2 R10 R11 R12 R1); try lia.
  + exact SWF.
  + exact SSP.
  + exact F48.
  + exact Hfd2d.
  + exact Hhd.
  + exact Hld.
  + unfold TASK_SIZE. lia.
  + replace (length MSG_RF) with 38%nat by reflexivity. lia.
  + vm_compute. reflexivity.
  + replace (length MSG_RF) with 38%nat by reflexivity. cbn [length]. lia.
  + replace (length MSG_RF) with 38%nat by reflexivity. cbn [length]. lia.
  + left. rewrite !u_small64 by (unfold two64; lia). lia.
  + rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE. lia.
  + exact RDP.
  + reflexivity.
  + vm_compute. reflexivity.
  + apply t_emit_has_nil.
  + apply (lden_sp0d sp0 av ev tid rdraw regs Hargc2 E1 (-560) HE1). lia.
  + apply lden_lconst.
  + apply lden_lconst.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + intros E4 ms4 Ha5 Hd4 Hpost4 Hrom4.
    rewrite u_small64 in Hd4 by (unfold two64; lia). rewrite U_rf2_eq in Hd4.
    assert (Ha5' : agree 200 E E4) by (intros x Hx; etransitivity; [exact (Ha1 x Hx) | apply Ha5; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (HI4 : INVR (ms_mem ms4)) by exact (invr_sw (ms_mem ms) (ms_mem ms4) _ _ _ Hpost4 ltac:(lia) ltac:(lia) HI1).
    rewrite Hrom1 in Hrom4.
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_rf2 LRF2 E4 ms4 md _ TBL_P_ok IMG_P_ok cert_LRF2 Hd4
             ltac:(vm_compute; reflexivity) Hhd Hld).
    intros L E5 ms5 HIn Hd5 Ha6 Hrom5 Hfr5 _. rewrite LRF2_eq in HIn. destruct HIn as [<-|[]].
    assert (Ha6' : agree 200 E E5) by (intros x Hx; etransitivity; [exact (Ha5' x Hx) | apply Ha6; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha6' x Hx)).
    assert (HI5 : INVR (ms_mem ms5)) by exact (invr_fx E4 U_rf2 _ _ Ha5' ltac:(vm_compute; reflexivity) Hfr5 HI4).
    rewrite Hrom4 in Hrom5.
    apply (fx_exit E5 Lrf3 ms5 md (Z_to_bv 64 2) [] Hd5 eq_refl eq_refl Hrom5).
    apply (exit_pre_gen sp0 tid SL SH Htid E5 Lrf3 ms5 md (-128) 0 3 5 6 7 21 65264 (rg_cont (rgn Lrf3 5)) (rg_cont (rgn Lrf3 7)) RW Hd5).
    * unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
    * unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
    * lia.
    * exact (exit_glob_of_MFXR _ (proj1 HI5) (proj2 HI5)).
    * exact Hhd.
    * exact Hld.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * unfold c5_clean. repeat split; vm_compute; reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * apply (frame_sp sp0 SL SH E5 Lrf3 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
      unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
Qed.

End RF.
