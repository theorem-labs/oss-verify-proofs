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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvCall2 UUsageCert UOpenCert UOpen1 UDirCert UDir ULoopCert ULoopInv ULoop1 UEofCert UEof1 ULoopInv2 UEof3 UTgtCert ULoop2 ULoop3 UTgt1 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section T2.
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


Local Notation JHEAD' := (JHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation seg_xfer' := (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).
Local Notation avoid_m2' := (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI).
Local Notation blk_out' := (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HI HOK).
Local Notation mfxr_chg' := (mfxr_chg sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC).
Local Notation mfxr_munch' := (mfxr_munch sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC HI HOK).

(* [comment removed for export] *)
Definition UT0 : Z := UCAP + MCHARGE (2 ^ 26).
Definition FZHEAD (E5 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf al ow : Z) : Prop :=
  agree 200 E E5 /\ sden PSEGS E5 G0 ms /\ ms_rom ms = seg_rom PSEGS /\ E5 N0 = Z_to_bv 64 len /\ E5 BUF = Z_to_bv 64 buf /\
  E5 CLV = Z_to_bv 64 CL /\ E5 RV = Z_to_bv 64 CALLS /\ E5 AV = Z_to_bv 64 al /\ E5 OV = Z_to_bv 64 ow /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDS0 /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  len = Z.of_nat (length data) /\ 6 + CL <= len < cap /\ CAPOK cap /\ U md <= UT0 /\
  ((len = 6 + CL /\ al = 0x76e30 /\ ow = 0) \/ (6 + CL < len /\ al = ow /\ In (ow, len - 6 - CL) (hi_blocks HI hs) /\ 16 <= ow)).

#[using="Hargc2"] Lemma agr2 : forall E1 E2 (L : sst), agree 200 E E1 -> (200 <= s_next L)%positive -> agree (s_next L) E1 E2 -> agree 200 E E2.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). intros E1 E2 L H1 Hn H2 x Hx. etransitivity; [exact (H1 x Hx) | apply H2; lia]. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Theorem j0_to_g0 : forall E4 ms md hs len cap buf T,
  JHEAD' J0 true E4 ms md hs len cap buf ->
  (forall E5 ms5, FZHEAD E5 ms5 md hs len cap buf 0x76e30 0 -> realizes PSEGS (mkCfg ms5 md) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E4 ms md hs len cap buf T (Ha4 & Hd4 & Hrom4 & HN4 & HB4 & HC4 & HR4 & Hm4 & Hh4 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & Hn0) K.
  pose proof (capoku_bounds cap md Hcap) as Hcb. pose proof (uok_ucap cap md (proj2 Hcap)) as HUc. destruct HIMG as [HI1 HI2]. pose proof (sp0_hi sp0 Hsp) as SH.
  pose proof HOK as ((HB1' & HB2') & _ & _ & _ & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh4) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & _ & _ & _).
  assert (Hbr' : 16 <= buf /\ buf + cap <= HTOP) by (destruct Hbr as [Hbr|Hbr]; lia).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 J0 LJ0 E4 ms md _ TBL_P_ok IMG_P_ok cert_LJ0 Hd4 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 Hgr5. rewrite LJ0_eq in HIn. destruct HIn as [<-|[]].
  destruct (seg_xfer' E4 E5 J0 F0 ms ms5 hs md buf [] Ha4 Ha45 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd4 Hd5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr5 Hgr5 Hm4 Hh4
              ltac:(exists cap; split; [exact Hblk | cbn; lia]) ltac:(split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]))
    as (Ha5 & Hm5 & Hh5 & _).
  rewrite Hrom4 in Hrom5.
  assert (HE54 : forall x, (x < s_next J0)%positive -> E5 x = E4 x) by (intros x Hx; symmetry; exact (Ha45 x Hx)).
  pose proof (entails_sden PSEGS E5 F0 G0 sig_f0 ms5 (sden_0 _ _ _ _ Hd5) ent_f0 wf_g0) as Hd6.
  pose proof (ecomp_agree E5 sig_f0 420 sid_f0) as Ha56.
  apply (K (ecomp E5 sig_f0) ms5).
  split; [intros x Hx; etransitivity; [exact (Ha5 x Hx) | apply Ha56; lia]|].
  split; [exact Hd6|]. split; [exact Hrom5|].
  split; [rewrite <- (Ha56 N0), HE54 by (vm_compute; reflexivity); exact HN4|].
  split; [rewrite <- (Ha56 BUF), HE54 by (vm_compute; reflexivity); exact HB4|].
  split; [rewrite <- (Ha56 CLV), HE54 by (vm_compute; reflexivity); exact HC4|].
  split; [rewrite <- (Ha56 RV), HE54 by (vm_compute; reflexivity); exact HR4|].
  split; [rewrite (ecomp_at E5 sig_f0 AV (lconst 0x76e30)) by (vm_compute; reflexivity); apply lden_lconst|].
  split; [rewrite (ecomp_at E5 sig_f0 OV (lconst 0)) by (vm_compute; reflexivity); apply lden_lconst|].
  split; [exact Hm5|]. split; [exact Hh5|]. split; [exact Hhd|]. split; [exact Hld|]. split; [exact Hfd|]. split; [exact Hfs|].
  split; [exact Hblk|]. split; [exact HL|]. split; [lia|]. split; [exact (proj1 Hcap)|]. split; [unfold UT0, MCHARGE; lia|].
  left. split; [exact Hn0 | split; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Theorem j1_to_g0 : forall E4 ms md hs len cap buf T,
  JHEAD' J1 false E4 ms md hs len cap buf ->
  (forall E5 ms5 md5 hs5 p, FZHEAD E5 ms5 md5 hs5 len cap buf p p -> realizes PSEGS (mkCfg ms5 md5) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E4 ms md hs len cap buf T (Ha4 & Hd4 & Hrom4 & HN4 & HB4 & HC4 & HR4 & Hm4 & Hh4 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & Hn1) K.
  pose proof (capoku_bounds cap md Hcap) as Hcb. pose proof (uok_ucap cap md (proj2 Hcap)) as HUc.
  destruct HIMG as [HI1 HI2]. pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al.
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh4) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & _ & _ & _).
  assert (Hbr' : 16 <= buf /\ buf + cap <= HTOP) by (destruct Hbr as [Hbr|Hbr]; lia).
  set (n := len - 6 - CL) in *.
  (* [comment removed for export] *)
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 J1 LJ1 E4 ms md _ TBL_P_ok IMG_P_ok cert_LJ1 Hd4 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E5 ms5 HIn Hd5 Ha45 Hrom5 Hfr5 Hgr5. rewrite LJ1_eq in HIn. destruct HIn as [<-|[]].
  destruct (seg_xfer' E4 E5 J1 Lm ms ms5 hs md buf [] Ha4 Ha45 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd4 Hd5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr5 Hgr5 Hm4 Hh4
              ltac:(exists cap; split; [exact Hblk | cbn; lia]) ltac:(split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]))
    as (Ha5 & Hm5 & Hh5 & _).
  rewrite Hrom4 in Hrom5.
  assert (HE54 : forall x, (x < s_next J1)%positive -> E5 x = E4 x) by (intros x Hx; symmetry; exact (Ha45 x Hx)).
  assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha5 x Hx)).
  assert (HN5 : E5 N0 = Z_to_bv 64 len) by (rewrite HE54 by (vm_compute; reflexivity); exact HN4).
  assert (HC5 : E5 CLV = Z_to_bv 64 CL) by (rewrite HE54 by (vm_compute; reflexivity); exact HC4).
  assert (HB5 : E5 BUF = Z_to_bv 64 buf) by (rewrite HE54 by (vm_compute; reflexivity); exact HB4).
  assert (R1 : getr (ms_regs ms5) 1 = Z_to_bv 64 0x22c00) by (apply (getr_leaf_c PSEGS E5 Lm); [exact Hd5 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms5) 2 = Z_to_bv 64 (bv_unsigned sp0 - 208)).
  { rewrite (getr_leaf PSEGS E5 Lm ms5 2 (laddc SP0 (-208)) Hd5) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity. }
  assert (R3 : getr (ms_regs ms5) 3 = Z_to_bv 64 0x10800) by (apply (getr_leaf_c PSEGS E5 Lm); [exact Hd5 | vm_compute; reflexivity]).
  assert (R4 : getr (ms_regs ms5) 4 = Z_to_bv 64 0x77990) by (apply (getr_leaf_c PSEGS E5 Lm); [exact Hd5 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms5) 10 = Z_to_bv 64 n).
  { rewrite (getr_leaf PSEGS E5 Lm ms5 10 NF Hd5) by (vm_compute; reflexivity).
    apply bv_eq. rewrite (u_NF E5 len CL HN5 HC5) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|].
    change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
  apply (fx_malloc HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) IMG_LO IMG_END HTOP STATIC HOK E5 Lm ms5 md hs n 0 7 57136
           (bv_unsigned sp0 - 208) (rgn Lm 7) _ Hd5 eq_refl eq_refl Hrom5 hok_m (rgn_eq Lm 7 ltac:(vm_compute; lia))
           ltac:(replace (rg_base (rgn Lm 7)) with (lconst 0x778e8) by (vm_compute; reflexivity); apply u_lconst; lia)
           Hh5 (conj Hhd Hld) ltac:(unfold UCAP, MCHARGE, UBOUND, UB0 in *; lia) R10 ltac:(lia) ltac:(rewrite R1; vm_compute; reflexivity) R3 R4 R2
           ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
  - apply (frame_sp sp0 SL SH E5 Lm 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
  - exact (avoid_m2' E5 (s_rgs Lm) Ha5 ltac:(vm_compute; reflexivity)).
  - intros E6 ms6 md6 hs6 p Ha56 Hd6 Hrom6 Hh6 Hmd6 Hvo HU6 H10' Hp16 Hadd Hnin Hmunch Hcells6.
    destruct Hmd6 as [Hh6l Hl6l].
    rewrite R1 in Hd6. replace (bv_unsigned (Z_to_bv 64 0x22c00)) with 0x22c00 in Hd6 by (vm_compute; reflexivity).
    rewrite Hrom5 in Hrom6.
    assert (Ha6 : agree 200 E E6) by (intros x Hx; etransitivity; [exact (Ha5 x Hx) | apply Ha56; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (HE65 : forall x, (x < s_next Lm)%positive -> E6 x = E5 x) by (intros x Hx; symmetry; exact (Ha56 x Hx)).
    destruct (HBLK hs6 (ms_mem ms6) md6 Hh6) as (HBL6 & _).
    assert (Hpin : In (p, n) (hi_blocks HI hs6)) by (apply Hadd; left; reflexivity).
    assert (Hbin6 : In (buf, cap) (hi_blocks HI hs6)) by (apply Hadd; right; exact Hblk).
    destruct (HBL6 p n Hpin) as (_ & Hpr & _ & _ & Hpdj).
    assert (Hsep : p + n <= buf \/ buf + cap <= p) by (apply (Hpdj buf cap Hbin6); intros C; injection C; lia).
    assert (Hpr' : 16 <= p /\ p + n <= HTOP) by (destruct Hpr as [Hpr|Hpr]; lia).
    assert (HPV6 : E6 PV = Z_to_bv 64 p).
    { rewrite <- H10'. rewrite (getr_leaf PSEGS E6 _ ms6 10 (lvar PV) Hd6) by (vm_compute; reflexivity). rewrite lden_lvar. reflexivity. }
    assert (Hd6' : sden PSEGS E6 U_m ms6).
    { rewrite <- U_m_eq. apply fx_add_fact; [exact Hd6 | vm_compute; reflexivity |].
      cbn [fact_ok]. rewrite lden_lvar, HPV6, u_small64 by (unfold two64; unfold valid_sp in Hsp; lia). unfold valid_sp in Hsp; lia. }
    assert (Hm6 : MFXR' (ms_mem ms6)).
    { apply (mfxr_munch' hs hs6 (ms_mem ms5) (ms_mem ms6) md md6 _ Hh5 Hh6 Hmunch); [|exact Hm5].
      intros x Hx. cbn [ioutside] in Hx.
      assert (Hx' : (p <= x < p + n) \/ (bv_unsigned sp0 - 208 - 8192 <= x < bv_unsigned sp0 - 208)) by
        (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
      destruct Hx' as [Hx'|Hx']; [left; split; [lia|] | right; lia].
      destruct Hpr as [Hpr|Hpr]; [right; left; lia | right; right; lia]. }
    (* [comment removed for export] *)
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S2 U_m LM1 E6 ms6 md6 _ TBL_P_ok IMG_P_ok cert_LM1 Hd6' ltac:(vm_compute; reflexivity) Hh6l Hl6l).
    intros L E7 ms7 HIn Hd7 Ha67 Hrom7 Hfr7 Hgr7. rewrite LM1_eq in HIn. destruct HIn as [<-|[]].
    destruct (seg_xfer' E6 E7 U_m Lmc ms6 ms7 hs6 md6 buf [] Ha6 Ha67 ltac:(vm_compute; congruence)
                ltac:(vm_compute; reflexivity) Hd6' Hd7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr7 Hgr7 Hm6 Hh6
                ltac:(exists cap; split; [exact Hbin6 | cbn; lia]) ltac:(split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]))
      as (Ha7 & Hm7 & Hh7 & _).
    rewrite Hrom6 in Hrom7.
    assert (HE76 : forall x, (x < s_next U_m)%positive -> E7 x = E6 x) by (intros x Hx; symmetry; exact (Ha67 x Hx)).
    assert (HPV7 : E7 PV = Z_to_bv 64 p) by (rewrite HE76 by (vm_compute; reflexivity); exact HPV6).
    assert (HN7 : E7 N0 = Z_to_bv 64 len) by (rewrite HE76, HE65 by (vm_compute; reflexivity); exact HN5).
    assert (HC7 : E7 CLV = Z_to_bv 64 CL) by (rewrite HE76, HE65 by (vm_compute; reflexivity); exact HC5).
    assert (HB7 : E7 BUF = Z_to_bv 64 buf) by (rewrite HE76, HE65 by (vm_compute; reflexivity); exact HB5).
    assert (Q1 : getr (ms_regs ms7) 1 = Z_to_bv 64 0x22c14) by (apply (getr_leaf_c PSEGS E7 Lmc); [exact Hd7 | vm_compute; reflexivity]).
    assert (Q10 : getr (ms_regs ms7) 10 = Z_to_bv 64 p).
    { rewrite (getr_leaf PSEGS E7 Lmc ms7 10 (lvar PV) Hd7) by (vm_compute; reflexivity). rewrite lden_lvar. exact HPV7. }
    assert (Q11 : getr (ms_regs ms7) 11 = Z_to_bv 64 (buf + 6 + CL)).
    { rewrite (getr_leaf PSEGS E7 Lmc ms7 11 (LIN 6 [(BUF, 1); (CLV, 1)]) Hd7) by (vm_compute; reflexivity).
      apply bv_eq. rewrite u_lin2, HB7, HC7, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite (Z.mod_small buf) by lia. rewrite (Z.mod_small CL) by lia. rewrite !Z.mod_small by lia. lia. }
    assert (Q12 : getr (ms_regs ms7) 12 = Z_to_bv 64 n).
    { rewrite (getr_leaf PSEGS E7 Lmc ms7 12 NF Hd7) by (vm_compute; reflexivity).
      apply bv_eq. rewrite (u_NF E7 len CL HN7 HC7) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|].
      change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
    destruct (HBLK hs6 (ms_mem ms7) md6 Hh7) as (HBL7 & _).
    destruct (HBL7 p n Hpin) as (_ & _ & Hstkp & _). destruct (HBL7 buf cap Hbin6) as (_ & _ & Hstkb & _).
    destruct (u8arr_of_stk (ms_mem ms7) p (p + n) Hstkp ltac:(lia)) as (old & Hol & Hu8).
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_split PSEGS (ms_mem ms7) buf (buf + 6 + CL) (buf + cap) Hstkb ltac:(lia)) as [_ Hsb1].
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_split PSEGS (ms_mem ms7) (buf + 6 + CL) (buf + len) (buf + cap) Hsb1 ltac:(lia)) as [Hsb2 _].
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_bytes PSEGS (ms_mem ms7) (buf + 6 + CL) (buf + len) Hsb2 ltac:(lia)) as (bs & Hbl & Hbs).
    assert (Hres : lden E7 (lvar PV) = Z_to_bv 64 p) by (rewrite lden_lvar; exact HPV7).
    apply (fx_memcpy E7 Lmc ms7 md6 T (Z_to_bv 64 p) (Z_to_bv 64 (buf + 6 + CL)) n bs old [] (lvar PV)
             Hd7 eq_refl eq_refl hok_mc Hrom7 Q10 Q11 Q12 ltac:(rewrite Q1; vm_compute; reflexivity)).
    + rewrite u_small64 by (unfold two64; lia). exact Hbs.
    + rewrite u_small64 by (unfold two64; lia). exact Hu8.
    + rewrite Hol, Hbl. f_equal. lia.
    + rewrite Hbl. lia.
    + rewrite !u_small64 by (unfold two64; lia). lia.
    + rewrite u_small64 by (unfold two64; lia). lia.
    + rewrite u_small64 by (unfold two64; lia). lia.
    + exact Hres.
    + intros i R x Hi Hin Hx. exfalso. rewrite u_small64 in Hx by (unfold two64; lia).
      pose proof (blk_out' E7 (s_rgs Lmc) hs6 (ms_mem ms7) md6 p n x (avoid_m2' E7 (s_rgs Lmc) Ha7 ltac:(vm_compute; reflexivity))
                    Hh7 Hpin ltac:(lia)) as Ho.
      pose proof (outside_nth E7 _ x i R Ho Hi) as Hx'. unfold in_rg in Hin. lia.
    + exact Hh6l.
    + exact Hl6l.
    + intros E8 ms8 Ha78 Hd8 Hmem8 Hgr8 Hba8 Hrom8.
      rewrite Q1, u_small64 in Hd8 by (unfold two64; lia). rewrite U_mc_eq in Hd8.
      rewrite u_small64 in Hmem8, Hba8 by (unfold two64; lia).
      rewrite Hrom7 in Hrom8.
      assert (Ha8 : agree 200 E E8) by (intros x Hx; etransitivity; [exact (Ha7 x Hx) | apply Ha78; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
      assert (HE87 : forall x, (x < s_next Lmc)%positive -> E8 x = E7 x) by (intros x Hx; symmetry; exact (Ha78 x Hx)).
      assert (Hh8 : hi_Heap HI hs6 (ms_mem ms8) md6).
      { apply (HFRAME hs6 (ms_mem ms7) (ms_mem ms8) md6 [(p, p + n)] Hh7).
        - intros x Hx. apply Hmem8. cbn [ioutside] in Hx. lia.
        - exact Hgr8.
        - intros x Hx. destruct (HBL7 p n Hpin) as (_ & _ & _ & Hdj & _).
          apply (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.disjoint_outside (hi_owned HI hs6) p n x Hdj).
          cbn [ioutside] in Hx. apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Hx. split; [lia | exact I]. }
      assert (Hm8 : MFXR' (ms_mem ms8)).
      { apply (mfxr_chg' (ms_mem ms7)); [|exact Hm7].
        intros x Hx _ _. apply Hmem8. intros Hx'. apply Hx. split; [lia|].
        destruct Hpr as [Hpr|Hpr]; [right; left; lia | right; right; lia]. }
      (* [comment removed for export] *)
      apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S2 U_mc LM2 E8 ms8 md6 _ TBL_P_ok IMG_P_ok cert_LM2 Hd8 ltac:(vm_compute; reflexivity) Hh6l Hl6l).
      intros L E9 ms9 HIn Hd9 Ha89 Hrom9 Hfr9 Hgr9. rewrite LM2_eq in HIn. destruct HIn as [<-|[]].
      destruct (seg_xfer' E8 E9 U_mc Fm ms8 ms9 hs6 md6 buf [] Ha8 Ha89 ltac:(vm_compute; congruence)
                  ltac:(vm_compute; reflexivity) Hd8 Hd9 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr9 Hgr9 Hm8 Hh8
                  ltac:(exists cap; split; [exact Hbin6 | cbn; lia]) ltac:(split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]))
        as (Ha9 & Hm9 & Hh9 & _).
      rewrite Hrom8 in Hrom9.
      assert (HE98 : forall x, (x < s_next U_mc)%positive -> E9 x = E8 x) by (intros x Hx; symmetry; exact (Ha89 x Hx)).
      pose proof (entails_sden PSEGS E9 Fm G0 sig_fm ms9 (sden_0 _ _ _ _ Hd9) ent_fm wf_g0) as Hd10.
      pose proof (ecomp_agree E9 sig_fm 420 sid_fm) as Ha910.
      assert (Hsame : forall x, (x < 420)%positive -> ecomp E9 sig_fm x = E5 x).
      { intros x Hx. rewrite <- (Ha910 x Hx).
        rewrite HE98, HE87, HE76, HE65 by (first [exact Hx | apply (Pos.lt_trans _ 420); [exact Hx | vm_compute; reflexivity]]). reflexivity. }
      apply (K (ecomp E9 sig_fm) ms9 md6 hs6 p).
      split; [intros x Hx; etransitivity; [exact (Ha9 x Hx) | apply Ha910; lia]|].
      split; [exact Hd10|]. split; [exact Hrom9|].
      split; [rewrite Hsame by (vm_compute; reflexivity); exact HN5|].
      split; [rewrite Hsame by (vm_compute; reflexivity); exact HB5|].
      split; [rewrite Hsame by (vm_compute; reflexivity); exact HC5|].
      split; [rewrite Hsame, HE54 by (vm_compute; reflexivity); exact HR4|].
      split; [rewrite (ecomp_at E9 sig_fm AV (lvar PV)) by (vm_compute; reflexivity); rewrite lden_lvar, HE98, HE87 by (vm_compute; reflexivity); exact HPV7|].
      split; [rewrite (ecomp_at E9 sig_fm OV (lvar PV)) by (vm_compute; reflexivity); rewrite lden_lvar, HE98, HE87 by (vm_compute; reflexivity); exact HPV7|].
      split; [exact Hm9|]. split; [exact Hh9|]. split; [exact Hh6l|]. split; [exact Hl6l|].
      split; [rewrite (vm_only_fds md md6 Hvo); exact Hfd|]. split; [rewrite (vm_only_fs md md6 Hvo); exact Hfs|].
      split; [exact Hbin6|]. split; [exact HL|]. split; [lia|]. split; [exact (proj1 Hcap)|].
      split; [unfold UT0, MCHARGE in *; lia|].
      right. split; [exact Hn1|]. split; [reflexivity|]. split; [exact Hpin | lia].
Qed.

End T2.
