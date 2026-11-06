(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LGap04.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AHandoffLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AEntryLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kitL.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_init1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_init2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_init2b.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_initP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_init3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LGap04 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMadv.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AHandoffLib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.MainExport OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.MainFactsAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AEntryLib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kitL OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_init1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_init2.RT_initK OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_init2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_init2b OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_initP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt.
Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma zsumf_esz_ivs_sum : forall l, zsumf esz l = ivs_sum l.
Proof. induction l as [|iv l IH]; [reflexivity|]. cbn [zsumf fold_right ivs_sum]. unfold zsumf in IH. rewrite IH. reflexivity. Qed.

Lemma in_rangesb_in_ivs : forall l (x : word), in_rangesb l x = true -> MainExport.in_ivs (bv_unsigned x) l.
Proof. intros l x H. apply in_rangesb_true in H as (lo & sz & Hin & Hb). exists (lo, sz). split; [exact Hin| exact Hb]. Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_in : forall L (x : word), page_in_ranges (page_base x) L = true -> in_rangesb L x = true.
Proof.
  intros L x H. unfold page_in_ranges in H. apply existsb_exists in H as ([lo sz] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply in_rangesb_true. exists lo, sz. split; [exact Hin|].
  pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2^64) in Rx.
  assert (E : bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096).
  { unfold page_base, page_base_of, page_size. apply wa_unsigned.
    pose proof (Z.mul_div_le (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.div_pos (bv_unsigned x) 4096 ltac:(lia) ltac:(lia)). lia. }
  rewrite E in H1, H2. unfold page_size in H2.
  pose proof (Z.mul_div_le (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mul_succ_div_gt (bv_unsigned x) 4096 ltac:(lia)). lia.
Qed.

Section MAIN.
Context {ACEIL : Ceil}.
Variables (w : bool) (V : nat -> Z) (sp0 : word) (fs : Fs.Fs) (m : word -> option byte) (mo : Model) (g : lghost).
Let usp := bv_unsigned sp0.
Hypothesis HU : usp = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.
Hypothesis HPW : Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w).
Hypothesis HFW : Forall (mfact_ok asegs V m) (asan_mem_facts ++ asan_mem_facts_w w).
Hypothesis HM : amodel V sp0 fs mo.
Hypothesis HC : alloc_ceiling = usp - 8388608.
Hypothesis HG : g = mkG (amain_windows V) AMAIN_R0.
Hypothesis HWIN : amain_gwin V m mo.
Hypothesis LK : LOK asegs mo.
Hypothesis BI : BINV mo g.
(* [comment removed for export] *)
Hypothesis NAPOS : noaccess_pos mo.

Let st := st_main (hw w) V usp.
Let IP : init_pure (hw w) V usp := IP_main w V sp0 fs mo HU HPW HM HC.
Let maps := vm_maps (m_vmmaps mo).

Lemma obj_zin : forall k n, In (k, n) OBJK -> zin (4096 * V k) n maps.
Proof. intros k n H. exact (proj1 (obj_facts w V sp0 fs mo HPW HM HC (k, n) H)). Qed.

Lemma lit_zin : forall b n, ledger_has asan_ledger (ZLit b) n = true -> zin b n maps.
Proof. intros b n H. exact (ledger_has_In V _ _ _ _ (am_maps _ _ _ _ HM) H). Qed.

Lemma lazy_shadow : forall b n, In (LMap (ZLit b) n AsanPlan.AP.KRWLAZY) asan_ledger ->
  forall x : word, b <= bv_unsigned x < b + n -> lzf mo x = true.
Proof.
  intros b n Hin x Hx. pose proof (proj1 (Forall_forall _ _) (am_kinds _ _ _ _ HM) _ Hin) as K. cbn [lentry_kind_ok zv] in K.
  destruct (K x Hx) as [K1 K2]. unfold lzf. rewrite (page_in_ranges_in _ _ K2). cbn [andb].
  destruct (in_rangesb (vm_noaccess (m_vmmaps mo)) x) eqn:E; [| reflexivity]. exfalso. apply K1. apply in_rangesb_in_ivs. exact E.
Qed.

Lemma RTMODEL_main : RTMODEL st mo.
Proof.
  unfold RTMODEL. cbn [st_pbase st_pa st_sec st st_main]. fold maps.
  split; [apply obj_zin; repeat first [left; reflexivity | right]|].
  split; [apply obj_zin; repeat first [left; reflexivity | right]|].
  split; [apply lit_zin; vm_compute; reflexivity|].
  split; [apply lit_zin; vm_compute; reflexivity|].
  split. { intros e He. unfold rt_loose in He. cbn in He.
           repeat (destruct He as [<-|He]; [cbn [fst snd]; apply obj_zin; repeat first [left; reflexivity | right]|]). destruct He. }
  split; [apply lit_zin; vm_compute; reflexivity|].
  split. { intros x [Hx|Hx].
           - apply (lazy_shadow 2147446784 268435456); [repeat first [left; reflexivity | right]| unfold KLOWSHADOW_BEG, KLOWSHADOW_END in Hx; lia].
           - apply (lazy_shadow 2201439137792 15392894357504); [repeat first [left; reflexivity | right]| unfold KHIGHSHADOW_BEG, KHIGHMEM_BEG in Hx; lia]. }
  split; [exact (am_limit _ _ _ _ HM)|].
  intros e He. destruct He.
Qed.

Lemma LIMIT_val : target_alloc_limit = 2^39.
Proof. reflexivity. Qed.
Lemma R0_val : AMAIN_R0 = 2^39 - asan_eager - asan_abytes.
Proof. reflexivity. Qed.

Lemma FRONTR_main : FRONTR mo (g_res g).
Proof.
  rewrite HG. cbn [g_res]. pose proof (usp_facts w V sp0 fs mo HU HPW HM HC) as UF. cbv zeta in UF. destruct UF as (U1 & U2 & U3). fold usp in U1, U2, U3.
  apply (FRONTR_intro mo AMAIN_R0 (Z.of_nat (length (segments_reserved asegs)) + 17) asan_totsz).
  - rewrite R0_val. unfold asan_eager, asan_abytes. lia.
  - rewrite (am_reserved _ _ _ _ HM). rewrite length_app. pose proof (ledger_len V _ _ (am_maps _ _ _ _ HM)) as LL.
    change (length asan_ledger) with 17%nat in LL. lia.
  - rewrite zsumf_esz_ivs_sum. exact (am_totsz _ _ _ _ HM).
  - assert (EL : Z.of_nat (length (segments_reserved asegs)) <= 16) by (apply Nat2Z.inj_le with (m := 16%nat); cbv; repeat constructor).
    rewrite R0_val, HC. unfold asan_totsz, asan_eager, asan_abytes, FR_NMAX, FR_COEF. lia.
  - assert (EL : Z.of_nat (length (segments_reserved asegs)) <= 16) by (apply Nat2Z.inj_le with (m := 16%nat); cbv; repeat constructor).
    rewrite R0_val, LIMIT_val. unfold asan_eager, asan_abytes, FR_KW. lia.
  - exact NAPOS.
Qed.

Lemma GWIN_main : GWIN st m mo g.
Proof.
  intros x Hw Hz Hr. destruct Hw as [Hw|Hv].
  - rewrite HG in Hw. cbn [g_win] in Hw. apply (HWIN x Hw Hz).
    destruct Hr as [Hr|[Hr|(b & Hb & Hx)]].
    + left. change (SH AIMG_LO) with 2147459072 in Hr. unfold KLOWSHADOW_END in Hr. lia.
    + right. left. unfold KHIGHSHADOW_BEG, KHIGHMEM_BEG in Hr. lia.
    + right. right. cbn in Hb. destruct Hb as [<-|[]]. unfold STOREBLOCK_SIZE, IX_SSTORE in *. lia.
  - pose proof (usp_facts w V sp0 fs mo HU HPW HM HC) as UF. cbv zeta in UF. destruct UF as (U1 & U2 & U3). fold usp in U1, U2, U3.
    pose proof (pvar_find V _ 6%nat 0 255 (proj1 (proj1 (Forall_app _ _ _) HPW)) ltac:(vm_compute; reflexivity)) as R6.
    pose proof (mfact_find asegs V m _
                  (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
                          (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992)))
                  (proj1 (proj1 (Forall_app _ _ _) HFW)) ltac:(vm_compute; reflexivity)) as SZ.
    cbn [mfact_ok zv] in SZ.
    set (X := bv_unsigned x) in *. unfold SH, SHADOW_OFFSET in Hv.
    assert (E8 : (usp - 8388608) / 8 = 4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat - 1048576).
    { rewrite HU. replace (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608) with ((4096 * V 0%nat + 512 * V 10%nat + 2 * V 6%nat - 1048576) * 8) by lia.
      apply Z.div_mul. lia. }
    rewrite HC, E8 in Hv.
    specialize (SZ (X - (4096 * V 0%nat + 512 * V 10%nat + 2146402304)) ltac:(lia)).
    replace (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (X - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) with X in SZ by lia.
    unfold X in SZ. rewrite wa_unsigned_id in SZ. rewrite SZ. discriminate.
Qed.

Theorem art_init_main : exists B0, DRV_B_MAIN <= B0 /\ ARTd usp (usp - 48) [] [] [] B0 m mo g.
Proof.
  exists (AMAIN_R0 - PROV_MAIN). pose proof PROV_MAIN_small as PS.
  split; [rewrite R0_val; unfold asan_eager, asan_abytes; change DRV_B_MAIN with 517414322432; lia|].
  eapply (ARTd_intro st).
  - exact (st_main_rep w V usp m IP HFW).
  - exact (st_main_wf (hw w) V usp IP).
  - exact RTMODEL_main.
  - exact LK.
  - exact BI.
  - exact GWIN_main.
  - exact FRONTR_main.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - repeat split; reflexivity.
  - rewrite R0_val. unfold asan_eager, asan_abytes. lia.
  - unfold st. rewrite st_main_prov. rewrite HG. cbn [g_res]. lia.
  - lia.
  - apply SWIN_nil. reflexivity.
Qed.
End MAIN.
End RT_init3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMadv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.MainFactsAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_drv RT_init1 RT_init2 RT_init2b RT_initP.
Import RT_init3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_iface2 Drv_stmt.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition amodel_napos_stmt : Prop :=
  forall (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model), amodel V sp fs mo -> noaccess_pos mo.
Lemma amodel_napos : amodel_napos_stmt.
Proof. intros V sp fs mo HM b k Hin. exact (proj1 (Forall_forall _ _) (am_noaccess_pos _ _ _ _ HM) (b, k) Hin). Qed.

Section CeilWrap.
Context {ACEIL : Ceil}.

Lemma st_main_fresh : forall h V usp c, fresh_cls (st_main h V usp) c.
Proof.
  intros h V usp c. unfold fresh_cls, rg, cch, nthz. cbn [st_regions st_cache st_main].
  destruct (c <? 0) eqn:E; [split; reflexivity|]. split; apply nth_repeat.
Qed.

Theorem art_init_d : amodel_napos_stmt ->
  forall (w : bool) (V : nat -> Z) (sp0 brk0 mbase : word) (rdraw : EntryDraw) (argv envp : list (list byte))
         (uid hw : word) (fs : Fs.Fs) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (g : lghost),
    valid_sp sp0 -> valid_brk asegs brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> valid_fs fs -> entry_stack_fits sp0 argv envp -> valid_id uid -> valid_hwcap hw ->
    alloc_ceiling = bv_unsigned sp0 - 8388608 ->
    a_main_entry w V sp0 brk0 rdraw argv envp uid hw fs regs m mo g ->
    LOK asegs mo -> BINV mo g ->
    exists B0, DRV_B_MAIN <= B0
               /\ ARTd (bv_unsigned sp0) (bv_unsigned sp0 - 48) [] [] [] B0 m mo g
               /\ ADRVd DRV_CALLS m mo g.
Proof.
  intros NAP w V sp0 brk0 mbase rdraw argv envp uid hw fs regs m mo g Vsp _ _ _ _ _ _ _ _ HC HE LK BI.
  destruct HE as (HV & _ & HFW & HPW & _ & HM & HG & HWIN & _).
  assert (HU : bv_unsigned sp0 = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat).
  { destruct HV as (_ & _ & _ & _ & H & _). unfold IX_S1, IX_SP, IX_S2 in H. lia. }
  pose proof (IP_main w V sp0 fs mo HU HPW HM HC) as IP.
  destruct (art_init_main w V sp0 fs m mo g HU HPW HFW HM HC HG HWIN LK BI (NAP V sp0 fs mo HM)) as (B0 & HB & HA).
  exists B0. split; [exact HB|]. split; [exact HA|].
  apply (adrvd_keep DRV_CALLS m mo g (st_main (RT_init2.hw w) V (bv_unsigned sp0))).
  - exact (st_main_rep w V (bv_unsigned sp0) m IP HFW).
  - exact (st_main_wf (RT_init2.hw w) V (bv_unsigned sp0) IP).
  - intros c _ _. apply st_main_fresh.
Qed.

(* [comment removed for export] *)
Definition art_init_closed := art_init_d amodel_napos.
End CeilWrap.
