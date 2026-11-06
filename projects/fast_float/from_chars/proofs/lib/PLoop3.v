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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PLoop2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition NB : positive := Eval vm_compute in (NXG + 10)%positive.

(* [comment removed for export] *)
Definition CAPOKG (cap : Z) (md : Model) : Prop := CAPOK cap /\ UOK (2 * cap) md.
Lemma uok_grow : forall cap md md', UOK cap md -> cap <= 33554432 -> U md' <= U md + MCHARGE (2 * cap) -> UOK (2 * cap) md'.
Proof.
  intros cap md md' (j & Hj & Hcj & HU) Hc H. unfold MCHARGE in H.
  assert (Hj9 : (j <= 9)%nat).
  { destruct (Nat.le_gt_cases j 9) as [A|A]; [exact A|]. exfalso.
    assert (X : 2 ^ 10 <= 2 ^ Z.of_nat j) by (apply Z.pow_le_mono_r; lia). rewrite Hcj in Hc. lia. }
  exists (S j). split; [lia|]. split; [rewrite Hcj, Nat2Z.inj_succ, Z.pow_succ_r by lia; lia|].
  rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma uok_malloc_ok : forall cap md, UOK cap md -> cap <= 33554432 -> U md + MCHARGE (2 * cap) <= UBOUND.
Proof.
  intros cap md (j & Hj & Hcj & HU) Hc. unfold MCHARGE, UBOUND. unfold UB0 in HU. lia.
Qed.

Section L3.
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

(* [comment removed for export] *)
Definition GHEAD (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (cap buf nb : Z) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 U_g2 ms /\ ms_rom ms = seg_rom PSEGS /\
  bv_unsigned (lden E1 LENP) = cap /\ E1 C0 = Z_to_bv 64 cap /\ E1 BUF = Z_to_bv 64 buf /\ E1 NB = Z_to_bv 64 nb /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDF' cap /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\ In (nb, 2 * cap) (hi_blocks HI hs) /\
  bytes_at PSEGS (ms_mem ms) nb (firstn (Z.to_nat cap) data) /\ cap <= Z.of_nat (length data) /\ CAPOKG cap md /\ cap <= 33554432.

(* [comment removed for export] *)
#[using="av Hargc2 IMG_LO IMG_END HTOP STATIC HOK"] Lemma munch_blk : forall hs hs' m m' md md' (W : list ivl) p n bs,
  hi_Heap HI hs m md -> hi_Heap HI hs' m' md' -> In (p, n) (hi_blocks HI hs) -> In (p, n) (hi_blocks HI hs') ->
  munch (hi_owned HI hs ++ hi_owned HI hs' ++ W) m m' ->
  (forall x, p <= x < p + n -> ioutside W x) -> Z.of_nat (length bs) <= n ->
  bytes_at PSEGS m p bs -> bytes_at PSEGS m' p bs.
Proof. LiaFast.lf_pins (fun (av Hargc2 IMG_LO IMG_END HTOP STATIC HOK : LiaFast.U) => LiaFast.u0).
  intros hs hs' m m' md md' W p n bs Hh Hh' Hb Hb' Hmu Hw Hn (B1 & B2 & B3).
  pose proof HOK as (_ & _ & _ & _ & HBLK).
  destruct (HBLK hs m md Hh) as (HBL & _). destruct (HBL p n Hb) as (_ & Hr & _ & Hdj & _).
  destruct (HBLK hs' m' md' Hh') as (HBL' & _). destruct (HBL' p n Hb') as (_ & _ & _ & Hdj' & _).
  split; [exact B1|]. split; [exact B2|]. intros i Hi. rewrite <- (B3 i Hi). unfold mrd. rewrite Hmu; [reflexivity|].
  unfold wa. rewrite u_small64 by (unfold two64; lia).
  apply HIface.outside_app. split; [apply (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.disjoint_outside _ p n); [exact Hdj | lia]|].
  apply HIface.outside_app. split; [apply (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.disjoint_outside _ p n); [exact Hdj' | lia]|].
  apply Hw. lia.
Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc2 HOK"] Lemma mfxr_munch : forall hs hs' m m' md md' (W : list ivl),
  hi_Heap HI hs m md -> hi_Heap HI hs' m' md' -> munch (hi_owned HI hs ++ hi_owned HI hs' ++ W) m m' ->
  (forall x, ~ ioutside W x -> HEAPX' x \/ (bv_unsigned sp0 - 65536 <= x < bv_unsigned sp0)) -> MFXR' m -> MFXR' m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 HOK : LiaFast.U) => LiaFast.u0).
  intros hs hs' m m' md md' W Hh Hh' Hmu Hw Hm.
  pose proof HOK as (_ & _ & _ & _ & HBLK).
  destruct (HBLK hs m md Hh) as (_ & Ho). destruct (HBLK hs' m' md' Hh') as (_ & Ho').
  apply (mfxr_chg' m m'); [|exact Hm]. intros x Hx Hr Hs. apply Hmu.
  apply HIface.outside_app. split.
  { destruct (HIface.outside_dec (hi_owned HI hs) (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. apply Hx.
    destruct (Ho _ A) as (A1 & A2). split; [lia | exact A2]. }
  apply HIface.outside_app. split.
  { destruct (HIface.outside_dec (hi_owned HI hs') (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. apply Hx.
    destruct (Ho' _ A) as (A1 & A2). split; [lia | exact A2]. }
  destruct (HIface.outside_dec W (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. destruct (Hw _ A) as [B|B]; [exact (Hx B) | exact (Hs B)].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Theorem grow_a : forall E2 ms2 md hs len n cap buf T,
  agree 200 E E2 -> sden PSEGS E2 Lg ms2 -> ms_rom ms2 = seg_rom PSEGS ->
  E2 N0 = Z_to_bv 64 len -> E2 NR = Z_to_bv 64 n -> 0 <= len -> 0 <= n -> len + n = cap ->
  E2 C0 = Z_to_bv 64 cap -> E2 BUF = Z_to_bv 64 buf ->
  MFXR' (ms_mem ms2) -> hi_Heap HI hs (ms_mem ms2) md -> m_halted md = None -> m_vm_lazy md = [] ->
  m_fds md = FDF' cap -> m_fs md = fs0 -> In (buf, cap) (hi_blocks HI hs) ->
  bytes_at PSEGS (ms_mem ms2) buf (firstn (Z.to_nat cap) data) -> cap <= Z.of_nat (length data) -> CAPOKU cap md -> cap <= 33554432 ->
  (forall E3 ms3 md3 hs3 nb, GHEAD E3 ms3 md3 hs3 cap buf nb -> realizes PSEGS (mkCfg ms3 md3) T) ->
  realizes PSEGS (mkCfg ms2 md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E2 ms2 md hs len n cap buf T Ha2 Hd2 Hrom2 HN2 HNR2 Hl0 Hn0 Hln HC2 HB2 Hm2 Hh2 Hhl Hlz Hfd Hfs Hblk Hba Hcd Hcap Hc25 K.
  pose proof (capok_bounds cap (proj1 Hcap)) as Hcb. pose proof HIMG as [HI1 HI2].
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al.
  pose proof HOK as ((HB1 & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms2) md Hh2) as (HBL & _). destruct (HBL buf cap Hblk) as (_ & Hbr & _).
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  (* [comment removed for export] *)
  assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x226e0) by (apply (getr_leaf_c PSEGS E2 Lg); [exact Hd2 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms2) 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
  { rewrite (getr_leaf PSEGS E2 Lg ms2 2 (laddc SP0 (-128)) Hd2) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. reflexivity. }
  assert (R3 : getr (ms_regs ms2) 3 = Z_to_bv 64 0x10800) by (apply (getr_leaf_c PSEGS E2 Lg); [exact Hd2 | vm_compute; reflexivity]).
  assert (R4 : getr (ms_regs ms2) 4 = Z_to_bv 64 0x75bd0) by (apply (getr_leaf_c PSEGS E2 Lg); [exact Hd2 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 (2 * cap)).
  { rewrite (getr_leaf PSEGS E2 Lg ms2 10 (LIN 0 [(N0, 2); (NR, 2)]) Hd2) by (vm_compute; reflexivity).
    apply bv_eq. rewrite u_lin2k, HN2, HNR2. rewrite !u_small64 by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia). lia. }
  apply (fx_malloc HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK E2 Lg ms2 md hs (2 * cap) 0 7 57216
           (bv_unsigned sp0 - 128) (rgn Lg 7) _ Hd2 eq_refl eq_refl Hrom2 hok_g (rgn_eq Lg 7 ltac:(vm_compute; lia))
           ltac:(replace (rg_base (rgn Lg 7)) with (lconst 0x75b28) by (vm_compute; reflexivity); apply u_lconst; lia)
           Hh2 (conj Hhl Hlz) (uok_malloc_ok cap md (proj2 Hcap) Hc25) R10 ltac:(lia) ltac:(rewrite R1; vm_compute; reflexivity) R3 R4 R2 ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
  - apply (frame_sp sp0 SL SH E2 Lg 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE2 by lia. reflexivity.
  - exact (avoid_m2' E2 (s_rgs Lg) Ha2 ltac:(vm_compute; reflexivity)).
  - intros E3 ms3 md3 hs3 p Ha23 Hd3 Hrom3 Hh3 Hmd3 Hvo HU3 H10' Hp16 Hadd Hnin Hmunch Hcells3.
    destruct Hmd3 as [Hh3l Hl3l].
    rewrite R1 in Hd3. replace (bv_unsigned (Z_to_bv 64 0x226e0)) with 0x226e0 in Hd3 by (vm_compute; reflexivity).
    rewrite Hrom2 in Hrom3.
    assert (Ha3 : agree 200 E E3) by (intros x Hx; etransitivity; [exact (Ha2 x Hx) | apply Ha23; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (HE32 : forall x, (x < s_next Lg)%positive -> E3 x = E2 x) by (intros x Hx; symmetry; exact (Ha23 x Hx)).
    destruct (HBLK hs3 (ms_mem ms3) md3 Hh3) as (HBL3 & _).
    assert (Hpin : In (p, 2 * cap) (hi_blocks HI hs3)) by (apply Hadd; left; reflexivity).
    assert (Hbin3 : In (buf, cap) (hi_blocks HI hs3)) by (apply Hadd; right; exact Hblk).
    destruct (HBL3 p (2 * cap) Hpin) as (_ & Hpr & _ & _ & Hpdj).
    assert (Hsep : p + 2 * cap <= buf \/ buf + cap <= p) by (apply (Hpdj buf cap Hbin3); intros C; injection C; lia).
    assert (Hd3' : sden PSEGS E3 U_g1 ms3).
    { rewrite <- U_g1_eq. apply fx_add_fact; [exact Hd3 | vm_compute; reflexivity |].
      cbn [fact_ok]. rewrite <- (getr_leaf PSEGS E3 _ ms3 10 (lvar (NXG + 10)) Hd3) by (vm_compute; reflexivity).
      rewrite H10', u_small64 by (unfold two64; destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia).
      destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia. }
    assert (Hm3 : MFXR' (ms_mem ms3)).
    { apply (mfxr_munch hs hs3 (ms_mem ms2) (ms_mem ms3) md md3 _ Hh2 Hh3 Hmunch); [|exact Hm2].
      intros x Hx. cbn [ioutside] in Hx.
      assert (Hx' : (p <= x < p + 2 * cap) \/ (bv_unsigned sp0 - 128 - 8192 <= x < bv_unsigned sp0 - 128)) by
        (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
      destruct Hx' as [Hx'|Hx']; [left; split; [destruct Hpr as [Hpr|Hpr]; lia|] | right; lia].
      destruct Hpr as [Hpr|Hpr]; [right; left; lia | right; right; lia]. }
    assert (Hba3 : bytes_at PSEGS (ms_mem ms3) buf (firstn (Z.to_nat cap) data)).
    { apply (munch_blk hs hs3 (ms_mem ms2) (ms_mem ms3) md md3 _ buf cap _ Hh2 Hh3 Hblk Hbin3 Hmunch).
      - intros x Hx. cbn [ioutside]. split; [lia|]. split; [destruct Hbr as [Hbr|Hbr]; lia | exact I].
      - rewrite length_firstn. lia.
      - exact Hba. }
    (* [comment removed for export] *)
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SL2 U_g1 LG1 E3 ms3 md3 _ TBL_P_ok IMG_P_ok cert_LG1 Hd3' ltac:(vm_compute; reflexivity) Hh3l Hl3l).
    intros L E4 ms4 HIn Hd4 Ha34 Hrom4 Hfr4 Hgr4. rewrite LG1_eq in HIn. destruct HIn as [<-|[]].
    destruct (seg_xfer' E3 E4 U_g1 Lg1 ms3 ms4 hs3 md3 buf (firstn (Z.to_nat cap) data) Ha3 Ha34 ltac:(vm_compute; congruence)
                ltac:(vm_compute; reflexivity) Hd3' Hd4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr4 Hgr4 Hm3 Hh3
                ltac:(exists cap; split; [exact Hbin3 | rewrite length_firstn; lia]) Hba3) as (Ha4 & Hm4 & Hh4 & Hba4).
    rewrite Hrom3 in Hrom4.
    assert (HE43 : forall x, (x < s_next U_g1)%positive -> E4 x = E3 x) by (intros x Hx; symmetry; exact (Ha34 x Hx)).
    assert (HNB4 : E4 NB = Z_to_bv 64 p).
    { rewrite HE43 by (vm_compute; reflexivity). rewrite <- H10'.
      rewrite (getr_leaf PSEGS E3 _ ms3 10 (lvar (NXG + 10)) Hd3) by (vm_compute; reflexivity). rewrite lden_lvar. reflexivity. }
    assert (Q1 : getr (ms_regs ms4) 1 = Z_to_bv 64 0x226fc) by (apply (getr_leaf_c PSEGS E4 Lg1); [exact Hd4 | vm_compute; reflexivity]).
    assert (Q10 : getr (ms_regs ms4) 10 = Z_to_bv 64 p).
    { rewrite (getr_leaf PSEGS E4 Lg1 ms4 10 (lvar NB) Hd4) by (vm_compute; reflexivity). rewrite lden_lvar. exact HNB4. }
    assert (Q11 : getr (ms_regs ms4) 11 = Z_to_bv 64 buf).
    { rewrite (getr_leaf PSEGS E4 Lg1 ms4 11 (lvar BUF) Hd4) by (vm_compute; reflexivity). rewrite lden_lvar.
      rewrite HE43, HE32 by (vm_compute; reflexivity). exact HB2. }
    assert (Q12 : getr (ms_regs ms4) 12 = Z_to_bv 64 cap).
    { rewrite (getr_leaf PSEGS E4 Lg1 ms4 12 LENP Hd4) by (vm_compute; reflexivity).
      apply bv_eq. unfold LENP. rewrite u_lin2. rewrite HE43, HE32 by (vm_compute; reflexivity). rewrite HE43, HE32 by (vm_compute; reflexivity).
      rewrite HN2, HNR2. rewrite !u_small64 by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia). lia. }
    destruct (HBLK hs3 (ms_mem ms4) md3 Hh4) as (HBL4 & _). destruct (HBL4 p (2 * cap) Hpin) as (_ & _ & Hstk4 & _).
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_split PSEGS (ms_mem ms4) p (p + cap) (p + 2 * cap) Hstk4 ltac:(lia)) as [Hstk5 _].
    destruct (u8arr_of_stk (ms_mem ms4) p (p + cap) Hstk5 ltac:(lia)) as (old & Hol & Hu8).
    assert (Hres : lden E4 (rget (s_regs Lg1) (rk 10)) = Z_to_bv 64 p) by (rewrite <- Q10; symmetry; apply (getr_leaf PSEGS E4 Lg1 ms4 10 _ Hd4); reflexivity).
    assert (Hbsl : Z.of_nat (length (firstn (Z.to_nat cap) data)) = cap) by (rewrite length_firstn; lia).
    apply (fx_memcpy E4 Lg1 ms4 md3 T (Z_to_bv 64 p) (Z_to_bv 64 buf) cap (firstn (Z.to_nat cap) data) old [] (rget (s_regs Lg1) (rk 10))
             Hd4 eq_refl eq_refl hok_g1 Hrom4 Q10 Q11 Q12 ltac:(rewrite Q1; vm_compute; reflexivity)).
    + rewrite u_small64 by (unfold two64; destruct Hbr as [Hbr|Hbr]; unfold valid_sp in Hsp; lia). exact Hba4.
    + rewrite u_small64 by (unfold two64; destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia). exact Hu8.
    + rewrite Hol. apply Nat2Z.inj. rewrite Hbsl, Z2Nat.id by lia. lia.
    + exact Hbsl.
    + rewrite !u_small64 by (unfold two64; destruct Hpr as [Hpr|Hpr]; destruct Hbr as [Hbr|Hbr]; unfold valid_sp in Hsp; lia). lia.
    + rewrite u_small64 by (unfold two64; destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia). destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia.
    + rewrite u_small64 by (unfold two64; destruct Hbr as [Hbr|Hbr]; unfold valid_sp in Hsp; lia). destruct Hbr as [Hbr|Hbr]; unfold valid_sp in Hsp; lia.
    + exact Hres.
    + intros i R x Hi Hin Hx. exfalso. rewrite u_small64 in Hx by (unfold two64; destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia).
      pose proof (blk_out' E4 (s_rgs Lg1) hs3 (ms_mem ms4) md3 p (2 * cap) x (avoid_m2' E4 (s_rgs Lg1) Ha4 ltac:(vm_compute; reflexivity))
                    Hh4 Hpin ltac:(lia)) as Ho.
      pose proof (outside_nth E4 _ x i R Ho Hi) as Hx'. unfold in_rg in Hin. lia.
    + exact Hh3l.
    + exact Hl3l.
    + intros E5 ms5 Ha45 Hd5 Hmem5 Hgr5 Hba5 Hrom5.
      rewrite Q1, u_small64 in Hd5 by (unfold two64; lia). rewrite U_g2_eq in Hd5.
      rewrite u_small64 in Hmem5, Hba5 by (unfold two64; destruct Hpr as [Hpr|Hpr]; unfold valid_sp in Hsp; lia).
      assert (HE54 : forall x, (x < s_next Lg1)%positive -> E5 x = E4 x) by (intros x Hx; symmetry; exact (Ha45 x Hx)).
      apply (K E5 ms5 md3 hs3 p).
      split; [intros x Hx; etransitivity; [exact (Ha4 x Hx) | apply Ha45; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]|].
      split; [exact Hd5|]. split; [rewrite Hrom5; exact Hrom4|].
      split.
      { unfold LENP. rewrite u_lin2. rewrite HE54, HE43, HE32 by (vm_compute; reflexivity). rewrite HE54, HE43, HE32 by (vm_compute; reflexivity).
        rewrite HN2, HNR2. rewrite !u_small64 by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia). lia. }
      split; [rewrite HE54, HE43, HE32 by (vm_compute; reflexivity); exact HC2|].
      split; [rewrite HE54, HE43, HE32 by (vm_compute; reflexivity); exact HB2|].
      split; [rewrite HE54 by (vm_compute; reflexivity); exact HNB4|].
      split.
      { apply (mfxr_chg' (ms_mem ms4)); [|exact Hm4].
        intros x Hx _ _. apply Hmem5. intros Hx'. apply Hx. split; [destruct Hpr as [Hpr|Hpr]; lia|].
        destruct Hpr as [Hpr|Hpr]; [right; left; lia | right; right; lia]. }
      split.
      { apply (HFRAME hs3 (ms_mem ms4) (ms_mem ms5) md3 [(p, p + cap)] Hh4).
        - intros x Hx. apply Hmem5. cbn [ioutside] in Hx. lia.
        - exact Hgr5.
        - intros x Hx. destruct (HBL4 p (2 * cap) Hpin) as (_ & _ & _ & Hdj5 & _).
          apply (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.disjoint_outside (hi_owned HI hs3) p (2 * cap) x Hdj5).
          cbn [ioutside] in Hx. apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Hx. split; [lia | exact I]. }
      split; [exact Hh3l|]. split; [exact Hl3l|]. split; [rewrite (vm_only_fds md md3 Hvo); exact Hfd|].
      split; [rewrite (vm_only_fs md md3 Hvo); exact Hfs|]. split; [exact Hbin3|]. split; [exact Hpin|].
      split; [exact Hba5|]. split; [exact Hcd|]. split; [split; [exact (proj1 Hcap) | exact (uok_grow cap md md3 (proj2 Hcap) Hc25 HU3)] | exact Hc25].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Theorem grow_b : forall E1 ms md hs cap buf nb T,
  GHEAD E1 ms md hs cap buf nb ->
  (forall E2 ms2 md2 hs2, LHEAD' E2 ms2 md2 hs2 cap (2 * cap) nb -> realizes PSEGS (mkCfg ms2 md2) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs cap buf nb T (Ha1 & Hd1 & Hrom1 & HL1 & HC1 & HB1 & HNB1 & Hm1 & Hh1 & Hhl & Hlz & Hfd & Hfs & Hbin & Hpin & Hba & Hcd & Hcap & Hc25) K.
  pose proof (capok_bounds cap (proj1 Hcap)) as Hcb. pose proof HIMG as [HI1 HI2].
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al.
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh1) as (HBL & _).
  destruct (HBL buf cap Hbin) as (_ & Hbr & _). destruct (HBL nb (2 * cap) Hpin) as (_ & Hpr & _ & _ & Hpdj).
  assert (Hsep : nb + 2 * cap <= buf \/ buf + cap <= nb) by (apply (Hpdj buf cap Hbin); intros C; injection C; lia).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SL2 U_g2 LG2 E1 ms md _ TBL_P_ok IMG_P_ok cert_LG2 Hd1 ltac:(vm_compute; reflexivity) Hhl Hlz).
  intros L E2 ms2 HIn Hd2 Ha12 Hrom2 Hfr2 Hgr2. rewrite LG2_eq in HIn. destruct HIn as [<-|[]].
  destruct (seg_xfer' E1 E2 U_g2 Lg2 ms ms2 hs md nb (firstn (Z.to_nat cap) data) Ha1 Ha12 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd1 Hd2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hfr2 Hgr2 Hm1 Hh1
              ltac:(exists (2 * cap); split; [exact Hpin | rewrite length_firstn; lia]) Hba) as (Ha2 & Hm2 & Hh2 & Hba2).
  rewrite Hrom1 in Hrom2.
  assert (HE21 : forall x, (x < s_next U_g2)%positive -> E2 x = E1 x) by (intros x Hx; symmetry; exact (Ha12 x Hx)).
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x22704) by (apply (getr_leaf_c PSEGS E2 Lg2); [exact Hd2 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms2) 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
  { rewrite (getr_leaf PSEGS E2 Lg2 ms2 2 (laddc SP0 (-128)) Hd2) by (vm_compute; reflexivity).
    rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE2 by lia. reflexivity. }
  assert (R3 : getr (ms_regs ms2) 3 = Z_to_bv 64 0x10800) by (apply (getr_leaf_c PSEGS E2 Lg2); [exact Hd2 | vm_compute; reflexivity]).
  assert (R4 : getr (ms_regs ms2) 4 = Z_to_bv 64 0x75bd0) by (apply (getr_leaf_c PSEGS E2 Lg2); [exact Hd2 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 buf).
  { rewrite (getr_leaf PSEGS E2 Lg2 ms2 10 (lvar BUF) Hd2) by (vm_compute; reflexivity). rewrite lden_lvar, HE21 by (vm_compute; reflexivity). exact HB1. }
  apply (fx_free HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK E2 Lg2 ms2 md hs cap 0 7 57216
           (bv_unsigned sp0 - 128) (rgn Lg2 7) _ Hd2 eq_refl eq_refl Hrom2 hok_g2 (rgn_eq Lg2 7 ltac:(vm_compute; lia))
           ltac:(replace (rg_base (rgn Lg2 7)) with (lconst 0x75b28) by (vm_compute; reflexivity); apply u_lconst; lia)
           Hh2 (conj Hhl Hlz) buf R10 Hbin ltac:(destruct Hbr as [Hbr|Hbr]; lia) ltac:(rewrite R1; vm_compute; reflexivity) R3 R4 R2
           ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
  - apply (frame_sp sp0 SL SH E2 Lg2 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE2 by lia. reflexivity.
  - exact (avoid_m2' E2 (s_rgs Lg2) Ha2 ltac:(vm_compute; reflexivity)).
  - intros E3 ms3 md3 hs3 Ha23 Hd3 Hrom3 Hh3 Hmd3 Hvo HU3 Hdel Hmunch Hcells3.
    destruct Hmd3 as [Hh3l Hl3l].
    rewrite R1 in Hd3. replace (bv_unsigned (Z_to_bv 64 0x22704)) with 0x22704 in Hd3 by (vm_compute; reflexivity).
    assert (Hd3g : sden PSEGS E3 U_g3 ms3) by (rewrite <- U_g3_eq; exact Hd3). clear Hd3. rename Hd3g into Hd3. rewrite Hrom2 in Hrom3.
    assert (HE32 : forall x, (x < s_next Lg2)%positive -> E3 x = E2 x) by (intros x Hx; symmetry; exact (Ha23 x Hx)).
    assert (Ha3 : agree 200 E E3) by (intros x Hx; etransitivity; [exact (Ha2 x Hx) | apply Ha23; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
    assert (Hpin3 : In (nb, 2 * cap) (hi_blocks HI hs3)) by (apply Hdel; split; [exact Hpin | intros C; injection C; lia]).
    (* [comment removed for export] *)
    pose proof (entails_sden PSEGS E3 U_g3 LOOPT sig_g ms3 (sden_0 _ _ _ _ Hd3) ent_g LOOPT_wf) as Hd4.
    set (E4 := ecomp E3 sig_g) in *.
    assert (Ha34 : agree 200 E3 E4) by exact (fixed_below_agree E3 sig_g 200 ltac:(vm_compute; reflexivity)).
    apply (K E4 ms3 md3 hs3).
    split; [intros x Hx; etransitivity; [exact (Ha3 x Hx) | exact (Ha34 x Hx)]|].
    split; [exact Hd4|]. split; [exact Hrom3|].
    split.
    { unfold E4, ecomp. replace (svar sig_g N0) with LENP by (vm_compute; reflexivity). apply bv_eq.
      unfold LENP. rewrite u_lin2. rewrite !HE32, !HE21 by (vm_compute; reflexivity). unfold LENP in HL1. rewrite u_lin2 in HL1. rewrite HL1.
      rewrite u_small64 by (unfold two64; lia). reflexivity. }
    split.
    { unfold E4, ecomp. replace (svar sig_g C0) with (LIN 0 [(N0, 2); (NR, 2)]) by (vm_compute; reflexivity). apply bv_eq.
      rewrite u_lin2k. rewrite !HE32, !HE21 by (vm_compute; reflexivity). unfold LENP in HL1. rewrite u_lin2 in HL1.
      rewrite u_small64 by (unfold two64; lia).
      replace (0 + 2 * bv_unsigned (E1 N0) + 2 * bv_unsigned (E1 NR)) with (2 * (bv_unsigned (E1 N0) + bv_unsigned (E1 NR))) by lia.
      rewrite Z.add_0_l in HL1. rewrite <- Z.mul_mod_idemp_r by (unfold two64; lia). rewrite HL1. apply Z.mod_small. lia. }
    split.
    { unfold E4, ecomp. replace (svar sig_g BUF) with (lvar NB) by (vm_compute; reflexivity). rewrite lden_lvar.
      rewrite HE32, HE21 by (vm_compute; reflexivity). exact HNB1. }
    split.
    { apply (mfxr_munch hs hs3 (ms_mem ms2) (ms_mem ms3) md md3 _ Hh2 Hh3 Hmunch); [|exact Hm2].
      intros x Hx. cbn [ioutside] in Hx.
      assert (Hx' : (buf <= x < buf + cap) \/ (bv_unsigned sp0 - 128 - 8192 <= x < bv_unsigned sp0 - 128)) by
        (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
      destruct Hx' as [Hx'|Hx']; [left; split; [destruct Hbr as [Hbr|Hbr]; lia|] | right; lia].
      destruct Hbr as [Hbr|Hbr]; [right; left; lia | right; right; lia]. }
    split; [exact Hh3|]. split; [exact Hh3l|]. split; [exact Hl3l|].
    split; [rewrite (vm_only_fds md md3 Hvo); exact Hfd|]. split; [rewrite (vm_only_fs md md3 Hvo); exact Hfs|].
    split; [exact Hpin3|].
    split.
    { apply (munch_blk hs hs3 (ms_mem ms2) (ms_mem ms3) md md3 _ nb (2 * cap) _ Hh2 Hh3 Hpin Hpin3 Hmunch).
      - intros x Hx. cbn [ioutside]. split; [lia|]. split; [destruct Hpr as [Hpr|Hpr]; lia | exact I].
      - rewrite length_firstn. lia.
      - exact Hba2. }
    split; [lia|]. split; [exact Hcd|].
    split; [|exact (uok_same (2 * cap) md md3 (proj2 Hcap) HU3)].
    destruct Hcap as ((j & Hj & Hcj) & _). exists (S j). split; [|rewrite Hcj, Nat2Z.inj_succ, Z.pow_succ_r by lia; lia].
    destruct (Nat.le_gt_cases (S j) 10) as [A|A]; [exact A|]. exfalso. assert (j = 10%nat) by lia. subst j. rewrite Hcj in Hc25. cbn in Hc25. lia.
Qed.

End L3.
