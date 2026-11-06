(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx LibIface LibIfaceAB LibIfaceAE L5Defs L5Core L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmStatics PmStaticsA PmSpecsA PeSpecsAa.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCStaticsA PeCSinkA PeCModelA PeCSpecsA PeCSpecsAa PeTopAL PeTopALChkA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Ea0DrvLibL Ea0DrvLibInit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECTA.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.

Definition STK : Z := 36864.
Definition FRAMES (k : Z) : Z := 14.
Definition LEAK (k : Z) : Z := 0.
Definition CREDIT (tk tb : Z) (n : Z) : credit := (tk, tb).
Definition LayA (tk tb : Z) (L : asan_layout) : lib_layoutA := PNTAL.TopLayA_a STK FRAMES LEAK (CREDIT tk tb) L.
Definition TopLSA : lib_statics := PESTA.TopLSA RSEGS AD AAD EE.

Lemma STK_ok : 4096 <= STK <= 2 ^ 20 /\ STK mod 8 = 0.
Proof. unfold STK. cbn. lia. Qed.
Lemma CREDIT_ok tk tb : 0 <= tk -> 0 <= tb -> forall n, 0 <= n -> 0 <= fst (CREDIT tk tb n) /\ 0 <= snd (CREDIT tk tb n).
Proof. intros Hk Hb n _. cbn. lia. Qed.
Lemma FRAMES_ok : forall k, In k [0; 1; 2; 3; 4; 5] -> 0 <= LEAK k /\ 4 * LEAK k + FRAMES k <= ff_cap k.
Proof.
  intros k Hk. unfold LEAK, FRAMES, ff_cap, ff_bytes.
  destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia.
Qed.
Lemma LayA_L tk tb L : lla_L (LayA tk tb L) = L.
Proof. reflexivity. Qed.
Lemma LayA_credit tk tb L n : lla_credit (LayA tk tb L) n = (tk, tb).
Proof. reflexivity. Qed.

Lemma lib_layout tk tb L : 0 <= tk -> 0 <= tb -> Ea0DrvLibL.drv_lib_layoutA (LayA tk tb L) L.
Proof. intros Hk Hb. exact (PNTALCA.lib_layout_a STK FRAMES LEAK (CREDIT tk tb) STK_ok (CREDIT_ok tk tb Hk Hb) FRAMES_ok L). Qed.
Lemma lib_cells tk tb L : 0 <= tk -> 0 <= tb -> Ea0DrvLibInit.drv_lib_cellsA (LayA tk tb L).
Proof. intros Hk Hb. exact (PNTALCA.lib_cells_a STK FRAMES LEAK (CREDIT tk tb) L). Qed.

Section T.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (tk tb : Z).
Hypothesis LY : PMA.layout L C.
Let LYa := PMA.ly_as0 L C LY.
Local Notation Lay := (LayA tk tb L).

Lemma u8_of_cellz (M : word -> option byte) a : cellz RSEGS M a 1 0 -> L5.u8_at RSEGS M a 0.
Proof. unfold cellz, L5.u8_at. intros H. rewrite H. reflexivity. Qed.

Theorem statics_initA : lib_statics_initA Lay ar TopLSA.
Proof.
  unfold lib_statics_initA. intros av uid rnd tid canary hw M (IF & CELLS).
  unfold lib_init_facts in IF. cbv zeta in IF.
  cbn [lib_view heap_view ll_heap ll_init_img ll_guard HeapIface.hl_segs lla_L lla_init_img lla_guard LayA PNTAL.TopLayA_a] in IF.
  cbn [lla_L lla_init_cells LayA PNTAL.TopLayA_a] in CELLS. unfold PNTAL.init_cells_a in CELLS.
  rewrite (L5A.aly_segs L C LYa) in IF, CELLS.
  destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & _).
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end. clear CELLS.
  cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.
  assert (IC : forall lo hi, In (lo, hi) [(0x10000, 0x13a000); (0x13d8f0, 0x13d998); (0x674055, 0x6759b0)] -> L5.img_clear M lo hi).
  { intros lo hi Hin i Hi. exact (IMG (lo, hi) i Hin Hi). }
  pose proof (IC _ _ ltac:(left; reflexivity)) as I1. pose proof (IC _ _ ltac:(right; right; left; reflexivity)) as I3. clear IC IMG.
  cbn [LibIface.ls_ok ls_g0 TopLSA PESTA.TopLSA]. unfold PESTA.ls_okA, PMST.g0. cbn [PMST.st_loc PMST.st_sys PMST.st_err].
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + cbn [pa_rw_lo AD PeCLayoutA.CADDR_A]. exact I1.
    + exists canary. split; [exact HC| exact GU].
    + apply u8_of_cellz. cbn [pa_need_locks AD PeCLayoutA.CADDR_A]. assumption.
    + cbn [pa_locale_lock AD PeCLayoutA.CADDR_A]. assumption.
  - unfold PMST.loc_ok. intros iv Hin. cbn [pa_loc_foot AD PeCLayoutA.CADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; intros i Hi; apply I3; cbn [fst snd] in *; lia.
  - unfold PMST.sys_ok. cbn [pa_syscat_guard AD PeCLayoutA.CADDR_A]. intros i Hi. apply I3. lia.
  - split.
    + cbn [pa_errcat_guard AD PeCLayoutA.CADDR_A]. intros i Hi. apply I3. lia.
    + unfold PESTA.atexit_stA, HAJ.atexit_cells. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit pe_drv_call pe_drv_guard PESTA.ax_list AD AAD EE PeCLayoutA.CADDR_A PeCLayoutA.CAADDR_A PeCLayoutA.EADDR_A length Z.of_nat Z.mul Z.add].
      split; [apply u8_of_cellz; assumption|]. repeat (split; [assumption|]). intros i f a Hi. destruct i; discriminate.
Qed.

Theorem statics_frameA : lib_statics_frameA Lay ar TopLSA.
Proof.
  unfold lib_statics_frameA, lib_statics_frame. intros g M M' OK FOOT RO INITC.
  cbn [LibIface.ls_ok TopLSA PESTA.TopLSA] in *.
  apply (PESTA.ls_okA_frame RSEGS AD AAD EE PECSA.addrs_wf_A M M'); [| | exact OK].
  - intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
    + apply FOOT; [exact Ha|]. exists iv. cbn [lib_view ll_foot lla_foot LayA PNTAL.TopLayA_a]. unfold PNTAL.foot_a. split; [exact Hin| exact Hr].
    + apply INITC; [exact Ha|]. left. exists (0x695ac0, 0x695ac8). cbn [lib_view ll_initc lla_initc LayA PNTAL.TopLayA_a]. cbn [pa_canary AD PeCLayoutA.CADDR_A] in Hc.
      split; [cbn; tauto| cbn; lia].
    + apply INITC; [exact Ha|]. left. unfold pm_initc in Hin. cbn in Hin.
      cbn [lib_view ll_initc lla_initc LayA PNTAL.TopLayA_a].
      destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [exists (0x695d13, 0x695d14)| exists (0x695df0, 0x695df4)]; (split; [cbn; tauto| cbn; lia]).
  - intros a Ha Hn. apply RO; [| exact Hn]. cbn [lib_view ll_rw_lo lla_rw_lo LayA PNTAL.TopLayA_a]. rewrite L5.unsigned_lit by (cbn [pa_rw_lo AD PeCLayoutA.CADDR_A] in Ha; lia).
    cbn [pa_rw_lo AD PeCLayoutA.CADDR_A] in Ha. lia.
Qed.

Theorem top_iface_okA_x (scfg : SpuriousCfg) (HI : asan_iface) (PayOk PayExport : list byte -> Prop) :
  lib_call_okA_x Lay ar scfg HI TopLSA PayOk PayExport -> lib_iface_okA_x Lay ar scfg HI TopLSA PayOk PayExport.
Proof. intros CALL. constructor; [exact CALL| exact statics_initA| exact statics_frameA]. Qed.

Theorem top_statics_exit : forall g M, ls_ok TopLSA g M -> PESTA.atexit_stA RSEGS AD AAD EE M (PMST.st_err g).
Proof. intros g M H. exact (PESTA.pe_statics_exitA RSEGS AD AAD EE g M H). Qed.
End T.
End PECTA.
