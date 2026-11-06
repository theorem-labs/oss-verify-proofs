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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvCall2 UUsageCert UOpenCert UOpen1 UDirCert UDir ULoopCert ULoopInv ULoop1 UEofCert UEof1 ULoopInv2 UEof3 UTgtCert ULoop2 ULoop3 UTgt1 UTgt2 UDrvFuzz UTgt3 URefused Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ag_lt : forall (S : sst) E1 E2 x, agree (s_next S) E1 E2 -> (502 <= s_next S)%positive -> (x < 502)%positive -> E2 x = E1 x.
Proof. intros S E1 E2 x H Hn Hx. symmetry. apply H. lia. Qed.

Section T4.
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



Local Notation avoid_m2' := (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI).
Local Notation mfxr_munch' := (mfxr_munch sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC HI HOK).
Local Notation ITHEAD' := (ITHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).

(* [comment removed for export] *)
Definition TLHEAD (S : sst) (kc : Z) (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf : Z) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 S ms /\ ms_rom ms = seg_rom PSEGS /\ E1 N0 = Z_to_bv 64 len /\ E1 BUF = Z_to_bv 64 buf /\
  E1 CLV = Z_to_bv 64 CL /\ E1 RV = Z_to_bv 64 CALLS /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDS0 /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  len = Z.of_nat (length data) /\ 6 + CL <= len < cap /\ CAPOK cap /\ U md <= UT0 + kc * FUZZ_CHARGE.

(* [comment removed for export] *)
Definition EXHEAD (S : sst) (E1 : valu) (ms : machine_state) (md : Model) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 S ms /\ ms_rom ms = seg_rom PSEGS /\ E1 RV = Z_to_bv 64 CALLS /\
  MFXR' (ms_mem ms) /\ NL (ms_mem ms) /\ m_halted md = None /\ m_vm_lazy md = [] /\ m_fds md = FDS0 /\ m_fs md = fs0.

(* [comment removed for export] *)
Definition fr_tmpl (X : sst) (ra c : Z) (a0l : lin) (FFP : list fpr) : bool :=
  (Z.eqb (s_pc X) 0x52f88 && match s_resv X with RNone => true | _ => false end &&
   lin_eqb (rget (s_regs X) (rk 1)) (lconst ra) && lin_eqb (rget (s_regs X) (rk 2)) (laddc SP0 c) &&
   lin_eqb (rget (s_regs X) (rk 3)) (lconst 0x10800) && lin_eqb (rget (s_regs X) (rk 4)) (lconst 0x77990) &&
   lin_eqb (rget (s_regs X) (rk 10)) a0l && havoc_ok X FFP None && Nat.ltb 21 (length (s_rgs X)) &&
   lin_eqb (rg_base (rgn X 7)) (lconst 0x778e8) && lin_eqb (rg_base (rgn X 0)) (laddc SP0 (-65536)) &&
   match rg_kind (rgn X 0) with RW => true | _ => false end && Z.eqb (csz (rgn X 0)) 65536 &&
   shape_eqb (s_rgs X) (s_rgs P_main2) && Pos.leb 502 (s_next X) && Z.eqb (ra mod 2) 0)%bool.

#[using="Type"] Lemma fr_tmpl_spec : forall X ra c a0l FFP, fr_tmpl X ra c a0l FFP = true ->
  s_pc X = 0x52f88 /\ s_resv X = RNone /\ rget (s_regs X) (rk 1) = lconst ra /\ rget (s_regs X) (rk 2) = laddc SP0 c /\
  rget (s_regs X) (rk 3) = lconst 0x10800 /\ rget (s_regs X) (rk 4) = lconst 0x77990 /\
  rget (s_regs X) (rk 10) = a0l /\ havoc_ok X FFP None = true /\
  (21 < length (s_rgs X))%nat /\ rg_base (rgn X 7) = lconst 0x778e8 /\ rg_base (rgn X 0) = laddc SP0 (-65536) /\
  rg_kind (rgn X 0) = RW /\ csz (rgn X 0) = 65536 /\ shape (s_rgs X) = shape (s_rgs P_main2) /\ (502 <= s_next X)%positive /\ ra mod 2 = 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X ra c a0l FFP H. unfold fr_tmpl in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?H] end.
  repeat match goal with
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
         | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H
         | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
         | H : shape_eqb _ _ = true |- _ => apply shape_eqb_eq in H
         | H : Pos.leb _ _ = true |- _ => apply Pos.leb_le in H
         end.
  destruct (s_resv X); try discriminate. destruct (rg_kind (rgn X 0)); try discriminate.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Local Notation seg_xfer' := (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).
Local Notation invr_fx' := (invr_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HIMG).


#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Lemma it_fx : forall (S L : sst) kc E1 E2 ms1 ms2 md hs len cap buf al ow,
  ITHEAD' S kc E1 ms1 md hs len cap buf al ow -> agree (s_next S) E1 E2 -> sden PSEGS E2 L ms2 -> ms_rom ms2 = ms_rom ms1 ->
  (forall x, outside E1 (s_rgs S) x -> ms_mem ms2 x = ms_mem ms1 x) -> mem_grows (ms_mem ms1) (ms_mem ms2) ->
  shape (s_rgs S) = shape (s_rgs P_main2) -> cells_tmpl S = true -> cells_tmpl L = true -> (502 <= s_next S)%positive ->
  ITHEAD' L kc E2 ms2 md hs len cap buf al ow.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros S L kc E1 E2 ms1 ms2 md hs len cap buf al ow
    (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & HAV1 & HOV1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1 & Hpay)
    Ha12 Hd2 Hrom2 Hfr Hgr Hsh Hc1 Hc2 Hnx.
  pose proof (capok_bounds cap Hcap) as Hcb.
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms1) md Hh1) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & _ & _ & _).
  destruct (seg_xfer' E1 E2 S L ms1 ms2 hs md buf [] Ha1 Ha12 ltac:(lia) Hsh Hd1 Hd2 Hc1 Hc2 Hfr Hgr Hm1 Hh1
              ltac:(exists cap; split; [exact Hblk | cbn; lia]) ltac:(split; [destruct Hbr as [Hbr|Hbr]; lia | split; [cbn; pose proof (sp0_hi sp0 Hsp); destruct Hbr as [Hbr|Hbr]; lia | intros i Hi; cbn in Hi; lia]]))
    as (Ha2 & Hm2 & Hh2 & _).
  refine (conj Ha2 (conj Hd2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hm2 (conj Hh2 (conj Hhd (conj Hld (conj Hfd (conj Hfs (conj Hblk (conj HL (conj Hlen (conj Hcap (conj HU1 Hpay)))))))))))))))))))).
  - rewrite Hrom2. exact Hrom1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HN1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HB1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HC1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HR1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HAV1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HOV1.
Qed.

#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Lemma tl_fx : forall (S L : sst) kc E1 E2 ms1 ms2 md hs len cap buf,
  TLHEAD S kc E1 ms1 md hs len cap buf -> agree (s_next S) E1 E2 -> sden PSEGS E2 L ms2 -> ms_rom ms2 = ms_rom ms1 ->
  (forall x, outside E1 (s_rgs S) x -> ms_mem ms2 x = ms_mem ms1 x) -> mem_grows (ms_mem ms1) (ms_mem ms2) ->
  shape (s_rgs S) = shape (s_rgs P_main2) -> cells_tmpl S = true -> cells_tmpl L = true -> (502 <= s_next S)%positive ->
  TLHEAD L kc E2 ms2 md hs len cap buf.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros S L kc E1 E2 ms1 ms2 md hs len cap buf
    (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1)
    Ha12 Hd2 Hrom2 Hfr Hgr Hsh Hc1 Hc2 Hnx.
  pose proof (capok_bounds cap Hcap) as Hcb.
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms1) md Hh1) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & _ & _ & _).
  destruct (seg_xfer' E1 E2 S L ms1 ms2 hs md buf [] Ha1 Ha12 ltac:(lia) Hsh Hd1 Hd2 Hc1 Hc2 Hfr Hgr Hm1 Hh1
              ltac:(exists cap; split; [exact Hblk | cbn; lia]) ltac:(split; [destruct Hbr as [Hbr|Hbr]; lia | split; [cbn; pose proof (sp0_hi sp0 Hsp); destruct Hbr as [Hbr|Hbr]; lia | intros i Hi; cbn in Hi; lia]]))
    as (Ha2 & Hm2 & Hh2 & _).
  refine (conj Ha2 (conj Hd2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hm2 (conj Hh2 (conj Hhd (conj Hld (conj Hfd (conj Hfs (conj Hblk (conj HL (conj Hlen (conj Hcap HU1))))))))))))))))).
  - rewrite Hrom2. exact Hrom1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HN1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HB1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HC1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HR1.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG"] Lemma ex_fx : forall (S L : sst) E1 E2 ms1 ms2 md,
  EXHEAD S E1 ms1 md -> agree (s_next S) E1 E2 -> sden PSEGS E2 L ms2 -> ms_rom ms2 = ms_rom ms1 ->
  (forall x, outside E1 (s_rgs S) x -> ms_mem ms2 x = ms_mem ms1 x) ->
  shape (s_rgs S) = shape (s_rgs P_main2) -> (502 <= s_next S)%positive ->
  EXHEAD L E2 ms2 md.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG : LiaFast.U) => LiaFast.u0).
  intros S L E1 E2 ms1 ms2 md (Ha1 & Hd1 & Hrom1 & HR1 & Hm1 & Hnl1 & Hhd & Hld & Hfd & Hfs) Ha12 Hd2 Hrom2 Hfr Hsh Hnx.
  destruct (invr_fx' E1 S (ms_mem ms1) (ms_mem ms2) Ha1 Hsh Hfr (conj Hm1 Hnl1)) as [Hm2 Hnl2].
  refine (conj _ (conj Hd2 (conj _ (conj _ (conj Hm2 (conj Hnl2 (conj Hhd (conj Hld (conj Hfd Hfs))))))))).
  - intros x Hx. etransitivity; [exact (Ha1 x Hx) | apply Ha12; lia].
  - rewrite Hrom2. exact Hrom1.
  - rewrite (ag_lt S E1 E2) by (first [exact Ha12 | exact Hnx | vm_compute; reflexivity]). exact HR1.
Qed.

Definition FFP1 : list fpr := [(0%nat, 57136, 8192); (7%nat, 4, 4)].

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HSTATI"] Theorem free_owned_step : forall (X : sst) (kc : Z) E1 ms md hs len cap buf al ow T,
  fr_tmpl X 0x22c94 (-208) (lvar OV) FFP1 = true ->
  ITHEAD' X kc E1 ms md hs len cap buf al ow ->
  (forall E2 ms2 md2 hs2, TLHEAD (havoc_call X 0x22c94 KEEPH FFP1 None) kc E2 ms2 md2 hs2 len cap buf -> realizes PSEGS (mkCfg ms2 md2) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HSTATI : LiaFast.U) => LiaFast.u0).
  intros X kc E1 ms md hs len cap buf al ow T Hft
    (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & HAV1 & HOV1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1 & Hpay) K.
  destruct (fr_tmpl_spec X 0x22c94 (-208) (lvar OV) FFP1 Hft) as (Gpc & Grv & G1 & G2 & G3 & G4 & G10 & Gok & Gln & G7 & G0b & G0k & G0s & Gsh & Gnx & Gev).
  pose proof (capok_bounds cap Hcap) as Hcb. destruct HIMG as [HI1 HI2].
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al.
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh1) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & _ & _ & _).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x22c94) by (exact (getr_leaf_c PSEGS E1 X ms 1 _ Hd1 G1)).
  assert (R2 : getr (ms_regs ms) 2 = Z_to_bv 64 (bv_unsigned sp0 - 208)).
  { rewrite (getr_leaf PSEGS E1 X ms 2 (laddc SP0 (-208)) Hd1 G2). rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE1 by lia. reflexivity. }
  assert (R3 : getr (ms_regs ms) 3 = Z_to_bv 64 0x10800) by (exact (getr_leaf_c PSEGS E1 X ms 3 _ Hd1 G3)).
  assert (R4 : getr (ms_regs ms) 4 = Z_to_bv 64 0x77990) by (exact (getr_leaf_c PSEGS E1 X ms 4 _ Hd1 G4)).
  assert (R10 : getr (ms_regs ms) 10 = Z_to_bv 64 ow) by (rewrite (getr_leaf PSEGS E1 X ms 10 (lvar OV) Hd1 G10), lden_lvar; exact HOV1).
  assert (Hpb : (ow = 0 /\ len - 6 - CL = 0) \/ (In (ow, len - 6 - CL) (hi_blocks HI hs) /\ ow <> 0)).
  { destruct Hpay as [(A & B & C) | (A & B & C & D)]; [left; lia | right; split; [exact C | lia]]. }
  apply (fx_free_g HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) IMG_LO IMG_END HTOP STATIC HOK E1 X ms md hs (len - 6 - CL) 0 7 57136
           (bv_unsigned sp0 - 208) (rgn X 7) T Hd1 Gpc Grv Hrom1 Gok (rgn_eq X 7 ltac:(lia)) ltac:(rewrite G7; apply u_lconst; lia)
           Hh1 (conj Hhd Hld) ow R10 Hpb ltac:(rewrite R1; vm_compute; reflexivity) R3 R4 R2 ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
  - apply (frame_sp sp0 SL SH E1 X 0 (-65536)); [lia | exact G0b | unfold SP0; rewrite lden_lvar, HE1 by lia; reflexivity | lia | rewrite G0k; reflexivity | lia | rewrite (csz_rsz E1 (rgn X 0)) by lia; lia | lia].
  - exact (avoid_m2' E1 (s_rgs X) Ha1 Gsh).
  - intros E2 ms2 md2 hs2 Ha12 Hd2 Hrom2 Hh2 Hmd2 Hvo HU2 Hdel Hmunch Hcells.
    destruct Hmd2 as [Hh2l Hl2l]. rewrite R1, u_small64 in Hd2 by (unfold two64; lia). rewrite Hrom1 in Hrom2.
    assert (HE21 : forall x, (x < s_next X)%positive -> E2 x = E1 x) by (intros x Hx; symmetry; exact (Ha12 x Hx)).
    assert (Hlt : forall x, (x < 502)%positive -> (x < s_next X)%positive) by (intros x Hx; lia).
    apply (K E2 ms2 md2 hs2). split; [intros x Hx; etransitivity; [exact (Ha1 x Hx) | apply Ha12; lia]|].
    split; [exact Hd2|]. split; [exact Hrom2|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HN1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HB1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HC1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HR1|].
    split.
    { apply (mfxr_munch' hs hs2 (ms_mem ms) (ms_mem ms2) md md2 _ Hh1 Hh2 Hmunch); [|exact Hm1].
      intros x Hx. cbn [ioutside] in Hx.
      assert (Hx' : (ow <= x < ow + (len - 6 - CL)) \/ (bv_unsigned sp0 - 208 - 8192 <= x < bv_unsigned sp0 - 208)) by
        (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
      destruct Hx' as [Hx'|Hx']; [|right; lia]. left.
      destruct Hpb as [(A & B) | (A & B)]; [lia|]. destruct (HBL ow (len - 6 - CL) A) as (_ & Hor & _).
      split; [destruct Hor as [Hor|Hor]; lia|]. destruct Hor as [Hor|Hor]; [right; left; lia | right; right; lia]. }
    split; [exact Hh2|]. split; [exact Hh2l|]. split; [exact Hl2l|].
    split; [rewrite (vm_only_fds md md2 Hvo); exact Hfd|]. split; [rewrite (vm_only_fs md md2 Hvo); exact Hfs|].
    split.
    { destruct (ow =? 0) eqn:Hz; [apply Hdel; exact Hblk|]. apply Hdel. split; [exact Hblk|]. intros C. injection C as C1 C2. lia. }
    split; [exact HL|]. split; [lia|]. split; [exact Hcap | lia].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HNL HSTATI"] Theorem free_buf_step : forall (B : sst) (kc : Z) E1 ms md hs len cap buf T,
  fr_tmpl B 0x22ac8 (-128) (lvar BUF) HFP = true ->
  TLHEAD B kc E1 ms md hs len cap buf ->
  (forall E2 ms2 md2, EXHEAD (havoc_call B 0x22ac8 KEEPH HFP None) E2 ms2 md2 -> realizes PSEGS (mkCfg ms2 md2) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HNL HSTATI : LiaFast.U) => LiaFast.u0).
  intros B kc E1 ms md hs len cap buf T Hft (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1) K.
  destruct (fr_tmpl_spec B 0x22ac8 (-128) (lvar BUF) HFP Hft) as (Gpc & Grv & G1 & G2 & G3 & G4 & G10 & Gok & Gln & G7 & G0b & G0k & G0s & Gsh & Gnx & Gev).
  pose proof (capok_bounds cap Hcap) as Hcb. destruct HIMG as [HI1 HI2].
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al.
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh1) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & _ & _ & _).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x22ac8) by (exact (getr_leaf_c PSEGS E1 B ms 1 _ Hd1 G1)).
  assert (R2 : getr (ms_regs ms) 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
  { rewrite (getr_leaf PSEGS E1 B ms 2 (laddc SP0 (-128)) Hd1 G2). rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE1 by lia. reflexivity. }
  assert (R3 : getr (ms_regs ms) 3 = Z_to_bv 64 0x10800) by (exact (getr_leaf_c PSEGS E1 B ms 3 _ Hd1 G3)).
  assert (R4 : getr (ms_regs ms) 4 = Z_to_bv 64 0x77990) by (exact (getr_leaf_c PSEGS E1 B ms 4 _ Hd1 G4)).
  assert (R10 : getr (ms_regs ms) 10 = Z_to_bv 64 buf) by (rewrite (getr_leaf PSEGS E1 B ms 10 (lvar BUF) Hd1 G10), lden_lvar; exact HB1).
  apply (fx_free HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) IMG_LO IMG_END HTOP STATIC HOK E1 B ms md hs cap 0 7 57216
           (bv_unsigned sp0 - 128) (rgn B 7) T Hd1 Gpc Grv Hrom1 Gok (rgn_eq B 7 ltac:(lia)) ltac:(rewrite G7; apply u_lconst; lia)
           Hh1 (conj Hhd Hld) buf R10 Hblk ltac:(destruct Hbr as [Hbr|Hbr]; lia) ltac:(rewrite R1; vm_compute; reflexivity) R3 R4 R2
           ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
  - apply (frame_sp sp0 SL SH E1 B 0 (-65536)); [lia | exact G0b | unfold SP0; rewrite lden_lvar, HE1 by lia; reflexivity | lia | rewrite G0k; reflexivity | lia | rewrite (csz_rsz E1 (rgn B 0)) by lia; lia | lia].
  - exact (avoid_m2' E1 (s_rgs B) Ha1 Gsh).
  - intros E2 ms2 md2 hs2 Ha12 Hd2 Hrom2 Hh2 Hmd2 Hvo HU2 Hdel Hmunch Hcells.
    destruct Hmd2 as [Hh2l Hl2l]. rewrite R1, u_small64 in Hd2 by (unfold two64; lia). rewrite Hrom1 in Hrom2.
    assert (HE21 : forall x, (x < s_next B)%positive -> E2 x = E1 x) by (intros x Hx; symmetry; exact (Ha12 x Hx)).
    apply (K E2 ms2 md2). split; [intros x Hx; etransitivity; [exact (Ha1 x Hx) | apply Ha12; lia]|].
    split; [exact Hd2|]. split; [exact Hrom2|].
    split; [rewrite HE21 by (apply (Pos.lt_le_trans _ 502); [vm_compute; reflexivity | exact Gnx]); exact HR1|].
    split.
    { apply (mfxr_munch' hs hs2 (ms_mem ms) (ms_mem ms2) md md2 _ Hh1 Hh2 Hmunch); [|exact Hm1].
      intros x Hx. cbn [ioutside] in Hx.
      assert (Hx' : (buf <= x < buf + cap) \/ (bv_unsigned sp0 - 128 - 8192 <= x < bv_unsigned sp0 - 128)) by
        (apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia|]; split; [lia | exact I]).
      destruct Hx' as [Hx'|Hx']; [left; split; [destruct Hbr as [Hbr|Hbr]; lia|] | right; lia].
      destruct Hbr as [Hbr|Hbr]; [right; left; lia | right; right; lia]. }
    split; [exact (HNL hs2 (ms_mem ms2) md2 Hh2)|]. split; [exact Hh2l|]. split; [exact Hl2l|].
    split; [rewrite (vm_only_fds md md2 Hvo); exact Hfd | rewrite (vm_only_fs md md2 Hvo); exact Hfs].
Qed.

End T4.
