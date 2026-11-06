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
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PLoop2 PLoop3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Definition FC_h : fact := Eval vm_compute in nth 0 (s_facts Lh) (FRange (lconst 0) 0 0).
Definition FC_q : fact := Eval vm_compute in nth 0 (s_facts Lq) (FRange (lconst 0) 0 0).
Lemma FC_h_in : In FC_h (s_facts Lh). Proof. vm_compute. tauto. Qed.
Lemma FC_q_in : In FC_q (s_facts Lq). Proof. vm_compute. tauto. Qed.
Lemma FC_h_eq : FC_h = FCond BC_EQ LENP (lvar C0) false. Proof. vm_compute. reflexivity. Qed.
Lemma FC_q_eq : FC_q = FCond BC_EQ LENP (lvar C0) true. Proof. vm_compute. reflexivity. Qed.

Section L4.
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

Local Notation MHEAD' := (MHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation grow_a' := (grow_a sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).
Local Notation grow_b' := (grow_b sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).

(* [comment removed for export] *)
Definition RFHEAD (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 Lrf ms /\ ms_rom ms = seg_rom PSEGS /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fs md = fs0 /\ (exists k, m_fds md = FDF' k) /\
  67108864 <= Z.of_nat (length data).

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Theorem m_step : forall E1 ms md hs len cap buf n T,
  MHEAD' E1 ms md hs len cap buf n ->
  (forall E2 ms2 md2 hs2 cap2 buf2, LHEAD' E2 ms2 md2 hs2 (len + n) cap2 buf2 -> realizes PSEGS (mkCfg ms2 md2) T) ->
  (forall E2 ms2 hs2, RFHEAD E2 ms2 md hs2 -> realizes PSEGS (mkCfg ms2 md) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf n T (Ha1 & Hd1 & Hrom1 & HN & HC & HB & HNR & Hm1 & Hh1 & Hhl & Hlz & Hfd & Hfs & Hblk & Hba & Hn & Hnp & Hlen & Hld & Hcap) KL KR.
  pose proof (capoku_bounds cap md Hcap) as Hcb. pose proof HIMG as [HI1 HI2].
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  pose proof HOK as ((HB1 & HB2) & _ & _ & HFRAME & HBLK).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SLG U_m LM E1 ms md _ TBL_P_ok IMG_P_ok cert_LM Hd1 ltac:(vm_compute; reflexivity) Hhl Hlz).
  intros L E2 ms2 HIn Hd2 Ha12 Hrom2 Hfr2 Hgr2.
  assert (HLc : cells_tmpl L = true) by (rewrite LM_eq in HIn; destruct HIn as [<-|[<-|[]]]; vm_compute; reflexivity).
  destruct (seg_xfer' E1 E2 U_m L ms ms2 hs md buf (firstn (Z.to_nat (len + n)) data) Ha1 Ha12 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd1 Hd2 ltac:(vm_compute; reflexivity) HLc Hfr2 Hgr2 Hm1 Hh1
              ltac:(exists cap; split; [exact Hblk | rewrite length_firstn; lia]) Hba) as (Ha2 & Hm2 & Hh2 & Hba2).
  rewrite Hrom1 in Hrom2.
  assert (HE21 : forall x, (x < s_next U_m)%positive -> E2 x = E1 x) by (intros x Hx; symmetry; exact (Ha12 x Hx)).
  assert (HN2 : E2 N0 = Z_to_bv 64 len) by (rewrite HE21 by (vm_compute; reflexivity); exact HN).
  assert (HC2 : E2 C0 = Z_to_bv 64 cap) by (rewrite HE21 by (vm_compute; reflexivity); exact HC).
  assert (HB2' : E2 BUF = Z_to_bv 64 buf) by (rewrite HE21 by (vm_compute; reflexivity); exact HB).
  assert (HNR2 : E2 NR = Z_to_bv 64 n) by (rewrite HE21 by (vm_compute; reflexivity); exact HNR).
  assert (HL2 : bv_unsigned (lden E2 LENP) = len + n).
  { unfold LENP. rewrite u_lin2, HN2, HNR2. rewrite !u_small64 by (unfold two64; lia). apply Z.mod_small. unfold two64; lia. }
  rewrite LM_eq in HIn. destruct HIn as [<-|[<-|[]]].
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E2 Lh ms2 _ Hd2 FC_h_in) as HF. rewrite FC_h_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_lvar, HC2 in HF.
    assert (Hne : len + n <> cap).
    { intros C. assert (X : lden E2 LENP = Z_to_bv 64 cap) by (apply bv_eq; rewrite HL2, u_small64 by (unfold two64; lia); exact C).
      rewrite X, bv_eqb_refl in HF. discriminate. }
    pose proof (entails_sden PSEGS E2 Lh LOOPT sig_h ms2 (sden_0 _ _ _ _ Hd2) ent_h LOOPT_wf) as Hd3.
    set (E3 := ecomp E2 sig_h) in *.
    assert (Ha23 : agree 200 E2 E3) by exact (fixed_below_agree E2 sig_h 200 ltac:(vm_compute; reflexivity)).
    apply (KL E3 ms2 md hs cap buf).
    split; [intros x Hx; etransitivity; [exact (Ha2 x Hx) | exact (Ha23 x Hx)]|].
    split; [exact Hd3|]. split; [exact Hrom2|].
    split; [unfold E3, ecomp; replace (svar sig_h N0) with LENP by (vm_compute; reflexivity); apply bv_eq; rewrite HL2, u_small64 by (unfold two64; lia); reflexivity|].
    split; [unfold E3, ecomp; replace (svar sig_h C0) with (lvar C0) by (vm_compute; reflexivity); rewrite lden_lvar; exact HC2|].
    split; [unfold E3, ecomp; replace (svar sig_h BUF) with (lvar BUF) by (vm_compute; reflexivity); rewrite lden_lvar; exact HB2'|].
    split; [exact Hm2|]. split; [exact Hh2|]. split; [exact Hhl|]. split; [exact Hlz|]. split; [exact Hfd|]. split; [exact Hfs|].
    split; [exact Hblk|]. split; [exact Hba2|]. split; [lia|]. split; [lia | exact Hcap].
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E2 Lq ms2 _ Hd2 FC_q_in) as HF. rewrite FC_q_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_lvar, HC2 in HF. apply bv_eqb_eq in HF.
    assert (Heq : len + n = cap) by (apply (f_equal bv_unsigned) in HF; rewrite HL2, u_small64 in HF by (unfold two64; lia); exact HF).
    destruct Hcap as ((j & Hj & Hcj) & HUk).
    destruct (Nat.le_gt_cases j 9) as [Hj9|Hj9].
    + (* [comment removed for export] *)
      assert (Hc25 : cap <= 33554432) by (rewrite Hcj; assert (2 ^ Z.of_nat j <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia); lia).
      assert (Hd3 : sden PSEGS E2 Lq9 ms2).
      { rewrite <- Lq9_eq. apply fx_add_fact; [exact Hd2 | vm_compute; reflexivity |]. cbn [fact_ok]. rewrite HL2. lia. }
      apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SLG Lq9 LQ9 E2 ms2 md _ TBL_P_ok IMG_P_ok cert_LQ9 Hd3 ltac:(vm_compute; reflexivity) Hhl Hlz).
      intros L E3 ms3 HIn Hd4 Ha23 Hrom3 Hfr3 Hgr3. rewrite LQ9_eq in HIn. destruct HIn as [<-|[]].
      destruct (seg_xfer' E2 E3 Lq9 Lg ms2 ms3 hs md buf (firstn (Z.to_nat (len + n)) data) Ha2 Ha23 ltac:(vm_compute; congruence)
                  ltac:(vm_compute; reflexivity) Hd3 Hd4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr3 Hgr3 Hm2 Hh2
                  ltac:(exists cap; split; [exact Hblk | rewrite length_firstn; lia]) Hba2) as (Ha3 & Hm3 & Hh3 & Hba3).
      rewrite Hrom2 in Hrom3.
      assert (HE32 : forall x, (x < s_next Lq9)%positive -> E3 x = E2 x) by (intros x Hx; symmetry; exact (Ha23 x Hx)).
      apply (grow_a' E3 ms3 md hs len n cap buf T Ha3 Hd4 Hrom3
               ltac:(rewrite HE32 by (vm_compute; reflexivity); exact HN2) ltac:(rewrite HE32 by (vm_compute; reflexivity); exact HNR2)
               ltac:(lia) ltac:(lia) Heq ltac:(rewrite HE32 by (vm_compute; reflexivity); exact HC2) ltac:(rewrite HE32 by (vm_compute; reflexivity); exact HB2')
               Hm3 Hh3 Hhl Hlz ltac:(rewrite Hfd, Heq; reflexivity) Hfs Hblk ltac:(rewrite <- Heq; exact Hba3) ltac:(lia)
               ltac:(split; [exists j; split; [exact Hj | exact Hcj] | exact HUk]) Hc25).
      intros E4 ms4 md4 hs4 nb HG. apply (grow_b' E4 ms4 md4 hs4 cap buf nb T HG).
      intros E5 ms5 md5 hs5 HL5. apply (KL E5 ms5 md5 hs5 (2 * cap) nb). rewrite Heq. exact HL5.
    + (* [comment removed for export] *)
      assert (Hj10 : j = 10%nat) by lia. subst j. cbn in Hcj.
      assert (Hd3 : sden PSEGS E2 Lq10 ms2).
      { rewrite <- Lq10_eq. apply fx_add_fact; [exact Hd2 | vm_compute; reflexivity |]. cbn [fact_ok]. rewrite HL2. lia. }
      apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SLG Lq10 LQ10 E2 ms2 md _ TBL_P_ok IMG_P_ok cert_LQ10 Hd3 ltac:(vm_compute; reflexivity) Hhl Hlz).
      intros L E3 ms3 HIn Hd4 Ha23 Hrom3 Hfr3 Hgr3. rewrite LQ10_eq in HIn. destruct HIn as [<-|[]].
      destruct (seg_xfer' E2 E3 Lq10 Lrf ms2 ms3 hs md buf [] Ha2 Ha23 ltac:(vm_compute; congruence)
                  ltac:(vm_compute; reflexivity) Hd3 Hd4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr3 Hgr3 Hm2 Hh2
                  ltac:(exists cap; split; [exact Hblk | cbn; lia]) ltac:(apply bytes_at_nil; destruct (HBLK hs (ms_mem ms2) md Hh2) as (HBL & _);
                                                                        destruct (HBL buf cap Hblk) as (_ & Hbr & _); destruct Hbr as [Hbr|Hbr]; unfold valid_sp in Hsp; lia))
        as (Ha3 & Hm3 & Hh3 & _).
      rewrite Hrom2 in Hrom3.
      apply (KR E3 ms3 hs). split; [exact Ha3|]. split; [exact Hd4|]. split; [exact Hrom3|]. split; [exact Hm3|]. split; [exact Hh3|].
      split; [exact Hhl|]. split; [exact Hlz|]. split; [exact Hfs|]. split; [exists (len + n); exact Hfd|]. lia.
Qed.

Local Notation head_to_r' := (head_to_r sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI HMV HSTATR data fs0 Hlk).
Local Notation r_step' := (r_step sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI data fs0).
Local Notation CHEAD' := (CHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI HMV HSTATR Hlk"] Theorem loop_all : forall T,
  (forall E2 ms2 md2 hs2 len2 cap2 buf2, CHEAD' E2 ms2 md2 hs2 len2 cap2 buf2 -> realizes PSEGS (mkCfg ms2 md2) T) ->
  (forall E2 ms2 md2 hs2, RFHEAD E2 ms2 md2 hs2 -> realizes PSEGS (mkCfg ms2 md2) T) ->
  forall E1 ms md hs len cap buf, LHEAD' E1 ms md hs len cap buf -> realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI HMV HSTATR Hlk : LiaFast.U) => LiaFast.u0).
  intros T KC KR.
  assert (IND : forall k E1 ms md hs len cap buf, Z.to_nat (Z.of_nat (length data) - len) = k -> LHEAD' E1 ms md hs len cap buf ->
                  realizes PSEGS (mkCfg ms md) T).
  { intros k. induction k as [k IH] using (well_founded_induction lt_wf). intros E1 ms md hs len cap buf Hk HL.
    pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & Hld & _).
    apply (head_to_r' E1 ms md hs len cap buf T HL). intros E2 ms2 md2 n HR.
    apply (r_step' E2 ms2 md2 hs len cap buf n T HR).
    - intros E3 ms3 HC. exact (KC E3 ms3 md2 hs len cap buf HC).
    - intros E3 ms3 HM. pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnp & _).
      apply (m_step E3 ms3 md2 hs len cap buf n T HM).
      + intros E4 ms4 md4 hs4 cap4 buf4 HL4.
        pose proof HL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen4 & Hld4 & _).
        apply (IH (Z.to_nat (Z.of_nat (length data) - (len + n))) ltac:(lia) E4 ms4 md4 hs4 (len + n) cap4 buf4 eq_refl HL4).
      + intros E4 ms4 hs4 HRF. exact (KR E4 ms4 md2 hs4 HRF). }
  intros E1 ms md hs len cap buf HL. exact (IND _ E1 ms md hs len cap buf eq_refl HL).
Qed.

End L4.
