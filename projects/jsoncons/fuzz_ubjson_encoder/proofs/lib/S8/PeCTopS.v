(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmSpecs PeSpecsS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCStatics PeCSpecsS LibIfaceE Es0DrvLibL Es0DrvG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeIfaceS8 HeInst0S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECTS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

Definition TOPK : Z := 60.

Definition TOPB0 : Z := 3 * 2 ^ 30.

Definition TopLay (L : heap_layout) (tb : Z) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x349e4;
  ll_gp := 0x10800;
  ll_empty := 0xc9620;
  ll_initc := [(0xcaf78, 0xcb040); (0xeb2b0, 0xeb2b8); (0xeb2d8, 0xeb2e0); (0xeb308, 0xeb338); (0xeb2d3, 0xeb2d4); (0xeb3a8, 0xeb3ac)];
  ll_init_cells := [(0xeb090, 4, 1); (0xeb098, 8, 0xeb0a0); (0xeb0a8, 8, 0x9bda4); (0xeb1a8, 8, 0x3496c)];
  ll_init_img := [(0x10000, 0xb95c0); (0xc9611, 0xc9614); (0xc9615, 0xcaf70); (0xeb048, 0xeb068);
                  (0xeb080, 0xeb090); (0xeb094, 0xeb098); (0xeb0a0, 0xeb0a8); (0xeb0b0, 0xeb1a8); (0xeb1b0, 0xeb2a8);
                  (0xeb2d3, 0xeb2d4); (0xeb3a8, 0xeb3ac)];
  ll_td_self := 0xcaf78; ll_td_tid := 0xcaf98; ll_td_locale := 0xcb010; ll_locale := 0xeb308; ll_td_canary := 0xcb030;
  ll_guard := 0xeb2b0; ll_auxvp := 0xeb2d8;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xb94a8;
  ll_stack := 65536;
  ll_credit := fun len => (TOPK, tb);
  ll_foot := pm_foot AD |}.

Definition TopLS : lib_statics := PEST.TopLS RSEGS AD EE.

Lemma lay_ok_S L tb : PMS.layout L -> PEST.lay_ok RSEGS AD EE (TopLay L tb).
Proof.
  intros LY. constructor; cbn [TopLay ll_heap ll_foot ll_rw_lo ll_guard ll_initc ll_init_img ll_init_cells].
  - exact (PMS.ly_segs L LY).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exists (0xeb2b0, 0xeb2b8). cbn. split; [auto 14| lia].
  - intros iv [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xeb2d3, 0xeb2d4). cbn. split; [auto 14| lia].
    + exists (0xeb3a8, 0xeb3ac). cbn. split; [auto 14| lia].
  - intros iv [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xeb2d3, 0xeb2d4). cbn. split; [auto 14| lia].
    + exists (0xeb3a8, 0xeb3ac). cbn. split; [auto 14| lia].
  - exists (0x10000, 0xb95c0). cbn. split; [auto 14| lia].
  - intros iv Hin. unfold PEST.pm_foot_lib in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
    + exists (0xc9615, 0xcaf70). cbn. split; [auto 14| lia].
    + exists (0xc9615, 0xcaf70). cbn. split; [auto 14| lia].
    + exists (0xc9615, 0xcaf70). cbn. split; [auto 14| lia].
    + exists (0xc9615, 0xcaf70). cbn. split; [auto 14| lia].
  - intros iv Hin. unfold PEST.ax_img in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd].
    + exists (0xeb080, 0xeb090). cbn. split; [auto 14| lia].
    + exists (0xeb094, 0xeb098). cbn. split; [auto 14| lia].
    + exists (0xeb0a0, 0xeb0a8). cbn. split; [auto 14| lia].
    + exists (0xeb0b0, 0xeb1a8). cbn. split; [auto 14| lia].
    + exists (0xeb1b0, 0xeb2a8). cbn. split; [auto 14| lia].
  - intros c Hin. unfold PEST.ax_cells in Hin. cbn in Hin. cbn.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; auto 14.
Qed.

Section Top.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable tb : Z.
Hypothesis LY : PMS.layout L.

Theorem top_iface_ok : lib_call_ok (TopLay L tb) scfg HI TopLS -> lib_iface_ok (TopLay L tb) scfg HI TopLS.
Proof.
  intros CALL. constructor.
  - exact CALL.
  - exact (PEST.pm_statics_init RSEGS AD EE (TopLay L tb) PECSS.addrs_wf_S (lay_ok_S L tb LY)).
  - exact (PEST.pm_statics_frame RSEGS AD EE (TopLay L tb) PECSS.addrs_wf_S (lay_ok_S L tb LY)).
Qed.

Theorem top_iface_ok_x (PayOk PayExport : list byte -> Prop) :
  lib_call_ok_x (TopLay L tb) scfg HI TopLS PayOk PayExport -> lib_iface_ok_x (TopLay L tb) scfg HI TopLS PayOk PayExport.
Proof.
  intros CALL. constructor.
  - exact CALL.
  - exact (PEST.pm_statics_init RSEGS AD EE (TopLay L tb) PECSS.addrs_wf_S (lay_ok_S L tb LY)).
  - exact (PEST.pm_statics_frame RSEGS AD EE (TopLay L tb) PECSS.addrs_wf_S (lay_ok_S L tb LY)).
Qed.

Theorem top_statics_exit : forall g M, ls_ok TopLS g M -> PEST.atexit_st RSEGS AD EE M (PMST.st_err g).
Proof. intros g M H. exact (PEST.pm_statics_exit RSEGS AD EE g M H). Qed.
End Top.

Lemma drv_lib_layout_top : forall tb, 0 <= tb -> forall sp, valid_sp sp ->
  Es0DrvLibL.drv_lib_layout (TopLay (HeInst0S8.L0 (bv_unsigned sp)) tb) (HeInst0S8.L0 (bv_unsigned sp)).
Proof.
  intros tb Htb sp Hsp. constructor; try reflexivity; try (cbn; lia).
  - intros iv Hin. unfold TopLay, pm_foot in Hin. cbn in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin.
  - intros iv Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia.
  - intros n Hn. cbn. unfold TOPK. lia.
Qed.

Lemma budget_top : forall tb, 0 <= tb <= 2 ^ 36 -> forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
  Es0DrvG.cred (HeInst0S8.L0 (bv_unsigned sp))
    (1 + 4 * fst (ll_credit (TopLay (HeInst0S8.L0 (bv_unsigned sp)) tb) n))
    (n + 2 ^ 20 + 4 * snd (ll_credit (TopLay (HeInst0S8.L0 (bv_unsigned sp)) tb) n)) 0
    (debit (HeInst0S8.L0 (bv_unsigned sp)) (HeInst0S8.K0, HeInst0S8.B0) 65536).
Proof.
  intros tb Htb sp n Hsp Hn. unfold Es0DrvG.cred, Es0DrvG.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead HeInst0S8.L0 ll_credit TopLay].
  unfold TOPK.
  assert (EK : HeInst0S8.K0 = 256) by (vm_compute; reflexivity). assert (EB : HeInst0S8.B0 = 549714697064) by (vm_compute; reflexivity).
  rewrite EK, EB. lia.
Qed.
End PECTS.
