(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UUsageCert UOpenCert UOpen1 UDirCert UDir ULoopCert ULoopInv ULoop1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Definition FC_c : fact := Eval vm_compute in nth 0 (s_facts Lc) (FRange (lconst 0) 0 0).
Definition FC_m : fact := Eval vm_compute in nth 0 (s_facts Lm) (FRange (lconst 0) 0 0).
Lemma FC_c_in : In FC_c (s_facts Lc). Proof. vm_compute. tauto. Qed.
Lemma FC_m_in : In FC_m (s_facts Lm). Proof. vm_compute. tauto. Qed.
Lemma FC_c_eq : FC_c = FCond BC_NE (lvar NR) (lconst 0) false. Proof. vm_compute. reflexivity. Qed.
Lemma FC_m_eq : FC_m = FCond BC_NE (lvar NR) (lconst 0) true. Proof. vm_compute. reflexivity. Qed.

Lemma firstn_add' : forall (A : Type) (a b : nat) (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a. induction a as [|a IH]; intros b l; [reflexivity|].
  destruct l as [|x l]; [cbn; destruct b; reflexivity|]. cbn. f_equal. apply IH.
Qed.

(* [comment removed for export] *)
Lemma u8arr_of_stk : forall m lo hi, stk PSEGS m lo hi -> lo <= hi ->
  exists old, length old = Z.to_nat (hi - lo) /\ u8arr PSEGS m lo old.
Proof.
  intros m lo hi Hs Hle. pose proof Hs as (H1 & H2 & H).
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_bytes PSEGS m lo hi Hs Hle) as (old & Hlen & Hb).
  exists old. split; [exact Hlen|]. split; [exact Hb|]. split; [lia|]. split; [rewrite Hlen; lia|].
  intros i Hi. rewrite Hlen in Hi. apply H. lia.
Qed.

Section L2.
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
Local Notation RHEAD' := (RHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation FDF' := (FDF av).
Local Notation seg_xfer' := (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).

(* [comment removed for export] *)
Definition CHEAD (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf : Z) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 Lc ms /\ ms_rom ms = seg_rom PSEGS /\ E1 N0 = Z_to_bv 64 len /\ E1 BUF = Z_to_bv 64 buf /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDF' len /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  bytes_at PSEGS (ms_mem ms) buf data /\ len = Z.of_nat (length data) /\ 0 <= len < cap /\ CAPOKU cap md.

(* [comment removed for export] *)
Definition MHEAD (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf n : Z) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 U_m ms /\ ms_rom ms = seg_rom PSEGS /\
  E1 N0 = Z_to_bv 64 len /\ E1 C0 = Z_to_bv 64 cap /\ E1 BUF = Z_to_bv 64 buf /\ E1 NR = Z_to_bv 64 n /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDF' (len + n) /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  bytes_at PSEGS (ms_mem ms) buf (firstn (Z.to_nat (len + n)) data) /\
  n = Z.min (Z.min (cap - len) 65536) (Z.of_nat (length data) - len) /\ 0 < n /\
  0 <= len < cap /\ len <= Z.of_nat (length data) /\ CAPOKU cap md.

#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Theorem r_step : forall E1 ms md hs len cap buf n T,
  RHEAD' E1 ms md hs len cap buf n ->
  (forall E2 ms2, CHEAD E2 ms2 md hs len cap buf -> realizes PSEGS (mkCfg ms2 md) T) ->
  (forall E2 ms2, MHEAD E2 ms2 md hs len cap buf n -> realizes PSEGS (mkCfg ms2 md) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf n T (Ha1 & Hd1 & Hrom1 & HN & HC & HB & HNR & Hm1 & Hh1 & Hhl & Hlz & Hfd & Hfs & Hblk & Hba & Hrs & Hn & Hlen & Hld & Hcap) KC KM.
  pose proof (capoku_bounds cap md Hcap) as Hcb. destruct HIMG as [HI1 HI2].
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  pose proof HOK as ((HB1 & HB2) & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh1) as (HBL & HOWN).
  destruct (HBL buf cap Hblk) as (_ & Hbr & Hstk & Hdj & _).
  set (bs := firstn (Z.to_nat n) (skipn (Z.to_nat len) data)) in *.
  assert (Hbsl : Z.of_nat (length bs) = n) by (unfold bs; rewrite length_firstn, length_skipn; lia).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SL2 U_r LR E1 ms md _ TBL_P_ok IMG_P_ok cert_LR Hd1 ltac:(vm_compute; reflexivity) Hhl Hlz).
  intros L E2 ms2 HIn Hd2 Ha12 Hrom2 Hfr2 Hgr2.
  assert (HLc : cells_tmpl L = true) by (rewrite LR_eq in HIn; destruct HIn as [<-|[<-|[]]]; vm_compute; reflexivity).
  destruct (seg_xfer' E1 E2 U_r L ms ms2 hs md buf (firstn (Z.to_nat len) data) Ha1 Ha12 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd1 Hd2 ltac:(vm_compute; reflexivity) HLc Hfr2 Hgr2 Hm1 Hh1
              ltac:(exists cap; split; [exact Hblk | rewrite length_firstn; lia]) Hba) as (Ha2 & Hm2 & Hh2 & Hba2).
  assert (Hrs2 : bytes_at PSEGS (ms_mem ms2) RS_LO bs).
  { destruct Hrs as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. rewrite <- (B3 i Hi).
    unfold mrd. rewrite Hfr2; [reflexivity|].
    apply (rs_out sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 E1 (s_rgs U_r) _ Ha1 ltac:(vm_compute; reflexivity)).
    unfold wa. rewrite u_small64 by (unfold two64, RS_LO; lia). unfold RSX, RS_LO. lia. }
  assert (HE21 : forall x, (x < s_next U_r)%positive -> E2 x = E1 x) by (intros x Hx; symmetry; exact (Ha12 x Hx)).
  assert (HN2 : E2 N0 = Z_to_bv 64 len) by (rewrite HE21 by (vm_compute; reflexivity); exact HN).
  assert (HC2 : E2 C0 = Z_to_bv 64 cap) by (rewrite HE21 by (vm_compute; reflexivity); exact HC).
  assert (HB2' : E2 BUF = Z_to_bv 64 buf) by (rewrite HE21 by (vm_compute; reflexivity); exact HB).
  assert (HNR2 : E2 NR = Z_to_bv 64 n) by (rewrite HE21 by (vm_compute; reflexivity); exact HNR).
  rewrite Hrom1 in Hrom2.
  rewrite LR_eq in HIn. destruct HIn as [<-|[<-|[]]].
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E2 Lc ms2 _ Hd2 FC_c_in) as HF. rewrite FC_c_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_lvar, lden_lconst, HNR2 in HF. apply negb_false_iff in HF. apply bv_eqb_eq in HF.
    assert (Hn0 : n = 0) by (apply (f_equal bv_unsigned) in HF; rewrite !u_small64 in HF by (unfold two64; lia); exact HF).
    assert (HL : len = Z.of_nat (length data)) by lia.
    apply (KC E2 ms2). refine (conj Ha2 (conj Hd2 (conj Hrom2 (conj HN2 (conj HB2' (conj Hm2 (conj Hh2 (conj Hhl (conj Hlz _))))))))).
    split; [rewrite Hfd, Hn0, Z.add_0_r; reflexivity|]. split; [exact Hfs|]. split; [exact Hblk|].
    split; [rewrite HL, Nat2Z.id, firstn_all in Hba2; exact Hba2|]. split; [exact HL|]. split; [lia | exact Hcap].
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E2 Lm ms2 _ Hd2 FC_m_in) as HF. rewrite FC_m_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_lvar, lden_lconst, HNR2 in HF. apply negb_true_iff in HF.
    assert (Hn0 : n <> 0) by (intros C; rewrite C in HF; rewrite bv_eqb_refl in HF; discriminate).
    assert (Hnp : 0 < n) by lia.
    assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x2294c) by (apply (getr_leaf_c PSEGS E2 Lm); [exact Hd2 | vm_compute; reflexivity]).
    assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 (buf + len)).
    { rewrite (getr_leaf PSEGS E2 Lm ms2 10 (LIN 0 [(BUF, 1); (N0, 1)]) Hd2) by (vm_compute; reflexivity).
      apply bv_eq. rewrite u_lin2, HB2', HN2. rewrite !u_small64 by (unfold two64; lia). rewrite Z.mod_small by (unfold two64 in *; lia). lia. }
    assert (R11 : getr (ms_regs ms2) 11 = Z_to_bv 64 RS_LO) by (apply (getr_leaf_c PSEGS E2 Lm); [exact Hd2 | vm_compute; reflexivity]).
    assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 n).
    { rewrite (getr_leaf PSEGS E2 Lm ms2 12 (lvar NR) Hd2) by (vm_compute; reflexivity). rewrite lden_lvar. exact HNR2. }
    destruct (HBLK hs (ms_mem ms2) md Hh2) as (HBL2 & _). destruct (HBL2 buf cap Hblk) as (_ & _ & Hstk2 & _).
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_split PSEGS (ms_mem ms2) buf (buf + len) (buf + cap) Hstk2 ltac:(lia)) as [_ Hstk3].
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_split PSEGS (ms_mem ms2) (buf + len) (buf + len + n) (buf + cap) Hstk3 ltac:(lia)) as [Hstk4 _].
    destruct (u8arr_of_stk (ms_mem ms2) (buf + len) (buf + len + n) Hstk4 ltac:(lia)) as (old & Hol & Hu8).
    assert (Hres : lden E2 (rget (s_regs Lm) (rk 10)) = Z_to_bv 64 (buf + len)) by (rewrite <- R10; symmetry; apply (getr_leaf PSEGS E2 Lm ms2 10 _ Hd2); reflexivity).
    apply (fx_memcpy E2 Lm ms2 md T (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS_LO) n bs old [] (rget (s_regs Lm) (rk 10)) Hd2 eq_refl eq_refl hok_m Hrom2
             R10 R11 R12 ltac:(rewrite R1; vm_compute; reflexivity)).
    + rewrite u_small64 by (unfold two64, RS_LO; lia). exact Hrs2.
    + rewrite u_small64 by (unfold two64; lia). exact Hu8.
    + rewrite Hol. apply Nat2Z.inj. rewrite Hbsl, Z2Nat.id by lia. lia.
    + exact Hbsl.
    + rewrite !u_small64 by (unfold two64, RS_LO; lia). unfold RS_LO. destruct Hbr as [Hbr|Hbr]; lia.
    + rewrite u_small64 by (unfold two64; lia). lia.
    + rewrite u_small64 by (unfold two64, RS_LO; lia). unfold RS_LO. lia.
    + exact Hres.
    + intros i R x Hi Hin Hx. exfalso. rewrite u_small64 in Hx by (unfold two64; lia).
      pose proof (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC (conj HI1 HI2) HI HOK E2 (s_rgs Lm) hs (ms_mem ms2) md buf cap x
                    (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HSTATI E2 (s_rgs Lm) Ha2 ltac:(vm_compute; reflexivity))
                    Hh2 Hblk ltac:(lia)) as Ho.
      pose proof (outside_nth E2 _ x i R Ho Hi) as Hx'. unfold in_rg in Hin. lia.
    + exact Hhl.
    + exact Hlz.
    + intros E3 ms3 Ha23 Hd3 Hmem3 Hgr3 Hba3 Hrom3.
      rewrite R1, u_small64 in Hd3 by (unfold two64; lia). rewrite U_m_eq in Hd3.
      rewrite u_small64 in Hmem3, Hba3 by (unfold two64; lia).
      assert (HE32 : forall x, (x < s_next Lm)%positive -> E3 x = E2 x) by (intros x Hx; symmetry; exact (Ha23 x Hx)).
      apply (KM E3 ms3).
      split; [intros x Hx; etransitivity; [exact (Ha2 x Hx) | apply Ha23; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]|].
      split; [exact Hd3|]. split; [rewrite Hrom3; exact Hrom2|].
      split; [rewrite HE32 by (vm_compute; reflexivity); exact HN2|].
      split; [rewrite HE32 by (vm_compute; reflexivity); exact HC2|].
      split; [rewrite HE32 by (vm_compute; reflexivity); exact HB2'|].
      split; [rewrite HE32 by (vm_compute; reflexivity); exact HNR2|].
      split.
      { apply (mfxr_chg sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC (ms_mem ms2)); [|exact Hm2].
        intros x Hx _ _. apply Hmem3. intros Hx'. apply Hx. split; [destruct Hbr as [Hbr|Hbr]; lia|].
        destruct Hbr as [Hbr|Hbr]; [right; left; lia | right; right; lia]. }
      split.
      { apply (HFRAME hs (ms_mem ms2) (ms_mem ms3) md [(buf + len, buf + len + n)] Hh2).
        - intros x Hx. apply Hmem3. cbn [ioutside] in Hx. lia.
        - exact Hgr3.
        - intros x Hx. destruct (HBLK hs (ms_mem ms2) md Hh2) as (HBL3 & _). destruct (HBL3 buf cap Hblk) as (_ & _ & _ & Hdj3 & _).
          apply (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.disjoint_outside (hi_owned HI hs) buf cap x Hdj3).
          cbn [ioutside] in Hx. apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Hx. split; [lia | exact I]. }
      split; [exact Hhl|]. split; [exact Hlz|]. split; [exact Hfd|]. split; [exact Hfs|]. split; [exact Hblk|].
      split.
      { replace (firstn (Z.to_nat (len + n)) data) with (firstn (Z.to_nat len) data ++ bs).
        - apply bytes_at_app. split.
          + destruct Hba2 as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. rewrite <- (B3 i Hi).
            unfold mrd. rewrite Hmem3; [reflexivity|]. unfold wa. rewrite length_firstn in Hi. rewrite u_small64 by (unfold two64; lia). lia.
          + rewrite length_firstn. replace (buf + Z.of_nat (Nat.min (Z.to_nat len) (length data))) with (buf + len) by lia. exact Hba3.
        - unfold bs. rewrite Z2Nat.inj_add by lia. rewrite firstn_add'. reflexivity. }
      split; [exact Hn|]. split; [exact Hnp|]. split; [exact Hlen|]. split; [exact Hld | exact Hcap].
Qed.

End L2.
