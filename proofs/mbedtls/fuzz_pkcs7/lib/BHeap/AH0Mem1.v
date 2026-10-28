(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX HMLib HM AH0Spec0 AH0Spec AH0Facts AH0Base AH0Layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapFixedNR AW_MmapDie AW_MallocA AW_MallocB AW_MallocC AW_AllocA AW_Poison AW_AllocB AW_DepotTop AW_DepotF AW_DepotCfg AW_Populate AW_Large AW_PoisonBig AW_SMalloc AW_SFree5 AW_DepotA AW_DepotC AW_Blist AW_FakeDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Mem1 () : Init.string Init.list := ["Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.ct"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_img_pristine"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_img_data"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_bss_allocator_instance"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_bss_runtime"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_bss_stackstore"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_bss_depot"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_bss_client"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_bss_musl"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_lowshadow"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_stack"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_stackshadow"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_argblock"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_prim"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_lla"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_ictx"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_thr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_treg"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_tvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_dtls"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_fstk"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_dnodes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_dstore"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_gvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_map_divec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_shadow_divec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_shadow_gvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_shadow_dstore"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_shadow_dnodes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.pv"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.PAGEVARS"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_addi"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryLemmas.Page"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.PG"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell_ok"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CWord"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"].


(* [comment removed for export] *)
Definition CT_COMMON : list ct := ltac2:(CDefT.buildp (gd_tbl_AH0Mem1 ()) "(0.$1.$2.(0.$1.$3.(0.$1.$4.(0.$1.$5.(0.$1.$6.(0.$1.$7.(0.$1.$8.(0.$1.$9.(0.$1.$:.(0.$1.$;.(0.$1.$<.(0.$1.$=.(0.$1.$>.(0.$1.$?.(0.$1.$10.(0.$1.$11.(0.$1.$12.(0.$1.$13.(0.$1.$14.(0.$1.$15.(0.$1.$16.(0.$1.$17.(0.$1.$18.(0.$1.$19.(0.$1.$1:.(0.$1.$1;.(0.$1.$1<.$1=.)))))))))))))))))))))))))))")
(* [comment removed for export] *).
Lemma cells_common_ct : forall p, cells_common p = map (cinst p) CT_COMMON.
Proof.
  intros p. unfold cells_common, CT_COMMON. rewrite !map_app. reflexivity.
Qed.

Section Mem1.
  Context {hAR : arun}.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Hypothesis HCOM : Forall (cell_ok ASEGS mem) (cells_common p).
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.
  Let bp := bp_of p STKHI FOG TF.

  #[using="HCOM"] Lemma HF : Forall (cell_ok ASEGS mem) (map (cinst p) CT_COMMON).
  Proof. rewrite <- cells_common_ct. exact HCOM. Qed.

  (* [comment removed for export] *)
  Local Ltac pv := cbn; tauto.
  #[using="HCN"] Lemma w64_Page : forall v, In v PAGEVARS -> Z_to_bv 64 (PG p v) = Page p v.
  Proof. intros v Hv. rewrite <- (Page_eq p HCN v Hv). apply Z_to_bv_bv_unsigned. Qed.
  #[using="Type"] Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros z Hz. rewrite u_zbv. apply Z.mod_small. exact Hz. Qed.
  #[using="HCN"] Lemma u_addi_Page : ltac2:(CDefT.buildp (gd_tbl_AH0Mem1 ()) "Pv,$1>.Pk,$1?.P,(20.$1>.R2.$21.)P,(22.(23.=R2.)(24.R2.(25.+2.+28.)))(26.$1?.(27.&40.(28.(29.Vp,R4.)R3.))(2:.(2;.Vp,R4.)R3.))")
(* [comment removed for export] *).
  Proof.
    intros v k Hv Hk. unfold ABoot.PropExec.v_addi. rewrite (Page_eq p HCN v Hv). pose proof (PG_range p HCN v Hv) as [G _].
    rewrite u_zbv. apply Z.mod_small. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma cword_C8 : ltac2:(CDefT.buildp (gd_tbl_AH0Mem1 ()) "Pa,(2<.&40.)Pv,(2<.&40.)Pw,(2<.&40.)PA,$1?.P,(2=.$2>.Vmem,(2?.R4.#8.R3.))P,(26.$1?.(27.&40.R5.)R2.)P,(26.(2<.&40.)R4.R5.)P,(23.(2:.R4.+8.)(25.+2.+40.))(30.$31.Vmem,R5.(32.$33.(34.R6.)(35.$33.)))")
(* [comment removed for export] *).
  Proof.
    intros a v w A X HA -> Hhi. rewrite <- HA. apply (cword_ro_cells mem a 8 v [C8 v] X); [reflexivity| cbn; tauto | lia].
  Qed.
  #[using="Type"] Lemma cword_C4 : ltac2:(CDefT.buildp (gd_tbl_AH0Mem1 ()) "Pa,(2<.&40.)Pv,(2<.&40.)Pw,(2<.&40.)PA,$1?.P,(2=.$2>.Vmem,(2?.R4.#4.R3.))P,(26.$1?.(27.&40.R5.)R2.)P,(26.(2<.&40.)R4.R5.)P,(23.(2:.R4.+4.)(25.+2.+40.))(30.$31.Vmem,R5.(32.$33.(36.R6.)(35.$33.)))")
(* [comment removed for export] *).
  Proof.
    intros a v w A X HA -> Hhi. rewrite <- HA. apply (cword_ro_cells mem a 4 v [C4 v] X); [reflexivity| cbn; tauto | lia].
  Qed.

  (* [comment removed for export] *)
  Local Ltac zdec := repeat match goal with |- _ /\ _ => split end;
    first [ apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity | apply Z.eqb_eq; vm_compute; reflexivity ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac orc :=
    lazymatch goal with |- ro_cells asegs ?m ?A ?cs =>
      lazymatch cs with context [p] => fail "orc: symbolic cell" | _ =>
      lazymatch A with context [p] => fail "orc: symbolic address" | _ =>
      apply (chk_ro_cells m p CT_COMMON HF QLit A cs);
      [ vm_compute; reflexivity | cbn; repeat split; reflexivity | zdec | zdec ] end end end.
  Local Ltac orw :=
    lazymatch goal with |- rw_cells asegs ?m ?A ?cs =>
      lazymatch cs with context [p] => fail "orw: symbolic cell" | _ =>
      lazymatch A with context [p] => fail "orw: symbolic address" | _ =>
      apply (chk_rw_cells m p CT_COMMON HF QLit A cs);
      [ vm_compute; reflexivity | cbn; repeat split; reflexivity | zdec | zdec ] end end end.
  (* [comment removed for export] *)

  #[using="p HCOM"] Lemma h0_poison_statics : poison_statics mem.
  Proof. unfold poison_statics. repeat match goal with |- _ /\ _ => split end.
    all: orc. Qed.
  #[using="p HCOM"] Lemma h0_fin_statics : fin_statics mem.
  Proof. unfold fin_statics. repeat match goal with |- _ /\ _ => split end; orc. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
    Open Scope tm_scope.
  #[using="HCN HCOM"] Lemma h0_thr_statics : thr_statics mem (PG p v_treg) (PG p v_thr).
  Proof.
    unfold thr_statics. split; [orc|]. split; [orc|].
    me_word HF (ALit 0x65de38) 8%nat X1. me_word HF ((#0x1000 * v_treg) .+ 152) 8%nat X2.
    split.
    - apply (cword_C8 _ _ _ _ X1); [apply u_lit; zdec | rewrite (w64_Page v_treg) by pv; reflexivity | zdec].
    - apply (cword_C8 _ _ _ _ X2); [exact (u_addi_Page v_treg 152 ltac:(pv) ltac:(lia)) | rewrite (w64_Page v_thr) by pv; reflexivity | pose proof (proj1 (PG_range p HCN v_treg ltac:(pv))); lia].
  Qed.

  (* [comment removed for export] *)
  #[using="HCN HCOM"] Lemma h0_tsd_arr : ro_cells asegs mem A_TSD_ARR [C8 (Z_to_bv 64 (PG p v_treg))].
  Proof. me_word HF (ALit 0x65de38) 8%nat X1. apply (cword_C8 _ _ _ _ X1); [apply u_lit; zdec | rewrite (w64_Page v_treg) by pv; reflexivity | zdec]. Qed.
  #[using="HCN HCOM"] Lemma h0_ctx_thr : ro_cells asegs mem (PG p v_treg + 152) [C8 (Z_to_bv 64 (PG p v_thr))].
  Proof.
    me_word HF ((#0x1000 * v_treg) .+ 152) 8%nat X2.
    apply (cword_C8 _ _ _ _ X2); [exact (u_addi_Page v_treg 152 ltac:(pv) ltac:(lia)) | rewrite (w64_Page v_thr) by pv; reflexivity | pose proof (proj1 (PG_range p HCN v_treg ltac:(pv))); lia].
  Qed.
  #[using="HCN HCOM"] Lemma h0_msegA_statics : msegA_statics mem (PG p v_thr) (PG p v_treg).
  Proof. unfold msegA_statics. repeat match goal with |- _ /\ _ => split end; first [orc | exact h0_tsd_arr | exact h0_ctx_thr]. Qed.
  #[using="HCN HCOM"] Lemma h0_allocA_statics : allocA_statics mem (PG p v_thr) (PG p v_treg).
  Proof. unfold allocA_statics. repeat match goal with |- _ /\ _ => split end; first [orc | exact h0_tsd_arr | exact h0_ctx_thr]. Qed.

  (* [comment removed for export] *)
  #[using="HCN HCOM"] Lemma h0_large_statics : large_statics mem (PG p v_secv).
  Proof.
    unfold large_statics. split; [| split; orc].
    change [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (PG p v_secv)); C8 (Z_to_bv 64 (PG p v_secv))]
      with ([C8 (Z_to_bv 64 4096)] ++ [C8 (Z_to_bv 64 (PG p v_secv))] ++ [C8 (Z_to_bv 64 (PG p v_secv))]).
    apply ro_cells_app; [orc|]. apply ro_cells_app.
    - me_word HF (ALit 0x1063e0) 8%nat X1. apply (cword_C8 _ _ _ _ X1); [apply u_lit; zdec | rewrite (w64_Page v_secv) by pv; reflexivity | zdec].
    - me_word HF (ALit 0x1063e8) 8%nat X2. apply (cword_C8 _ _ _ _ X2); [apply u_lit; zdec | rewrite (w64_Page v_secv) by pv; reflexivity | zdec].
  Qed.

  (* [comment removed for export] *)
  #[using="p HCOM"] Lemma h0_depot_statics : depot_statics mem.
  Proof.
    unfold depot_statics, dstatics, cstatics. split; [repeat match goal with |- _ /\ _ => split end; orc|]. split; [repeat match goal with |- _ /\ _ => split end; orc|].
    destruct (chk_ex_C8 mem p CT_COMMON HF QLit A_MUR1 ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [c1 H1].
    destruct (chk_ex_C8 mem p CT_COMMON HF QLit A_MUR2 ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [c2 H2].
    destruct (chk_ex_C8 mem p CT_COMMON HF QLit A_MUR3 ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [c3 H3].
    dexists c1, c2, c3. split; [exact H1|]. split; [exact H2| exact H3].
  Qed.

  (* [comment removed for export] *)
  #[using="p HCOM"] Lemma h0_rsmr_statics : exists can dd madv, rsmr_statics mem can dd madv.
  Proof.
    me_word HF (ALit 0x65cad0) 8%nat XC.
    destruct (chk_ex_C1 mem p CT_COMMON HF QLit A_CF_DONTDUMP ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [dd Hdd].
    destruct (chk_ex_C1 mem p CT_COMMON HF QLit A_MADV_FLAG ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [madv Hmadv].
    eexists. dexists dd, madv. unfold rsmr_statics.
    repeat match goal with |- _ /\ _ => split end; first [orc | exact Hdd | exact Hmadv | idtac].
    apply (cword_C8 _ _ _ _ XC); [apply u_lit; zdec | reflexivity | zdec].
  Qed.

  (* [comment removed for export] *)
  #[using="HCN HCOM"] Lemma h0_smalloc_statics : smalloc_statics mem (PG p v_fstk) (PG p v_dtls) (PG p v_thr) (PG p v_treg).
  Proof.
    unfold smalloc_statics. repeat match goal with |- _ /\ _ => split end; first [orc | exact h0_tsd_arr | exact h0_ctx_thr | idtac].
    - me_word HF (ALit 0x63ca90) 8%nat X1. apply (cword_C8 _ _ _ _ X1); [apply u_lit; zdec | rewrite (w64_Page v_fstk) by pv; reflexivity | zdec].
    - me_word HF (ALit 0x63ca98) 8%nat X2. apply (cword_C8 _ _ _ _ X2); [apply u_lit; zdec | rewrite (w64_Page v_dtls) by pv; reflexivity | zdec].
    - (* [comment removed for export] *)
      replace (PG p v_dtls + 24)%Z with (qaddr p (QTpl (#0x1000 * v_dtls)%tm) 24) by (cbn [qaddr]; rewrite (u_page p HCN v_dtls) by pv; reflexivity).
      apply (chk_ro_cells mem p CT_COMMON HF); [vm_compute; reflexivity | cbn; tauto | |];
        cbn [qaddr]; rewrite (u_page p HCN v_dtls) by pv; pose proof (proj1 (PG_range p HCN v_dtls ltac:(pv)));
        try match goal with |- context [Z.of_nat (cells_size ?cs)] => let v := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with v end; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="p HCOM"] Lemma h0_rwstat : hm_rwstat mem.
  Proof.
    unfold hm_rwstat. split; [|split].
    - (* [comment removed for export] *)
      destruct (img_ex_C4 mem A_ERRNO ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [e He]. exists e.
      split; [exact He|]. apply (chk_wr_at mem p CT_COMMON HF QLit A_ERRNO 4); [vm_compute; reflexivity | zdec | zdec].
    - destruct (chk_ex_C1w mem p CT_COMMON HF QLit A_OOM ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [o Ho]. exists o. exact Ho.
    - orw.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma w64_zev : forall t z, zev p t = z -> 0 <= z < 2 ^ 64 -> Z_to_bv 64 z = winst p t.
  Proof. intros t z Hz Hr. rewrite <- Hz, <- (zev_exact p t ltac:(rewrite Hz; exact Hr)). apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
  Local Ltac wz t := match goal with |- _ = ?r => change r with (winst p t) end; apply w64_zev; [cbn [zev] | ].

  (* [comment removed for export] *)
  #[using="HCN HCOM"] Theorem h0_hm_statics : hm_statics (L0_of bp) mem.
  Proof.
    pose proof (r_s1 p HCN) as S1. pose proof (r_s2 p HCN) as S2. pose proof (r_tpg p HCN) as TPG. pose proof (r_pslack p HCN) as PS. pose proof (r_prim p HCN) as PR.
    pose proof (proj1 (PG_range p HCN v_thr ltac:(pv))) as Gthr. pose proof (proj1 (PG_range p HCN v_treg ltac:(pv))) as Gtreg.
    split; [| exact h0_rwstat].
    unfold hm_ro. cbn [l_T l_ctx l_pa l_sb l_top l_fs l_errno L0_of bp bp_of bp_T bp_ctx bp_pa bp_sb bp_top bp_fs bp_dtls].
    unfold ri_base, space_end, kSpaceSize. cbn [l_sb L0_of bp bp_of bp_sb].
    split; [exact h0_msegA_statics|]. split; [exact h0_allocA_statics|]. split; [exact h0_poison_statics|]. split; [exact h0_fin_statics|].
    split; [exact h0_depot_statics|]. split; [exact h0_thr_statics|]. split; [exact h0_large_statics|].
    split; [orc|]. split; [orc|]. split; [orc|]. split; [orc|]. split; [orc|]. split; [orc|]. split; [orc|].
    split. { (* [comment removed for export] *) me_word HF (ALit 0x1063b8) 8%nat X. apply (cword_C8 _ _ _ _ X); [apply u_lit; zdec | | zdec].
             wz (((#0x1000 * v_prim) + (#(-0x1000) * v_pslack)) + #0x10000)%tm; unfold SB, PG; lia. }
    split. { (* [comment removed for export] *) me_word HF (ALit 0x1063c8) 8%nat X. apply (cword_C8 _ _ _ _ X); [apply u_lit; zdec | | zdec].
             wz (((#0x1000 * v_prim) + (#(-0x1000) * v_pslack)) + #0x2000010000)%tm; unfold SB, PG; lia. }
    split; [orc|]. split; [orc|]. split; [orc|]. split; [orc|].
    split. { (* [comment removed for export] *)
             replace (PG p v_treg + 8)%Z with (qaddr p (QTpl (#0x1000 * v_treg)%tm) 8) by (cbn [qaddr]; rewrite (u_page p HCN v_treg) by pv; reflexivity).
             apply (chk_ro_cells mem p CT_COMMON HF); [vm_compute; reflexivity | cbn; tauto | |];
               cbn [qaddr]; rewrite (u_page p HCN v_treg) by pv; pose proof (proj1 (PG_range p HCN v_treg ltac:(pv)));
               try match goal with |- context [Z.of_nat (cells_size ?cs)] => let v := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with v end; lia. }
    split. { (* [comment removed for export] *) me_word HF ((#0x1000 * v_thr) .+ 0) 8%nat X.
             apply (cword_C8 _ _ _ _ X); [etransitivity; [exact (u_addi_Page v_thr 0 ltac:(pv) ltac:(lia)) | lia] | rewrite (w64_Page v_treg) by pv; reflexivity | lia]. }
    split. { (* [comment removed for export] *)
             change [C8 (w64 (TOP p)); C8 (w64 (TOP p - 2 ^ 23))] with ([C8 (w64 (TOP p))] ++ [C8 (w64 (TOP p - 2 ^ 23))]).
             apply ro_cells_app; cbn [cells_size csize Z.of_nat Pos.of_succ_nat].
             - me_word HF ((#0x1000 * v_thr) .+ 8) 8%nat X. apply (cword_C8 _ _ _ _ X); [etransitivity; [exact (u_addi_Page v_thr 8 ltac:(pv) ltac:(lia)) | lia] | | lia].
               wz ((#0x8000 * v_s1) + (#0x1000 * v_tpg))%tm; unfold TOP; lia.
             - me_word HF ((#0x1000 * v_thr) .+ 16) 8%nat X.
               apply (cword_C8 _ _ _ _ X); [etransitivity; [exact (u_addi_Page v_thr 16 ltac:(pv) ltac:(lia)) | cbn [Z.of_nat Nat.add Pos.of_succ_nat]; lia] | | cbn [Z.of_nat Nat.add Pos.of_succ_nat]; lia].
               wz (((#0x8000 * v_s1) + (#0x1000 * v_tpg)) + #(-0x800000))%tm; unfold TOP; lia. }
    split. { replace (PG p v_thr + 40)%Z with (qaddr p (QTpl (#0x1000 * v_thr)%tm) 40) by (cbn [qaddr]; rewrite (u_page p HCN v_thr) by pv; reflexivity).
             apply (chk_ro_cells mem p CT_COMMON HF); [vm_compute; reflexivity | cbn; tauto | |];
               cbn [qaddr]; rewrite (u_page p HCN v_thr) by pv; pose proof (proj1 (PG_range p HCN v_thr ltac:(pv)));
               try match goal with |- context [Z.of_nat (cells_size ?cs)] => let v := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with v end; lia. }
    split. { me_word HF ((#0x1000 * v_thr) .+ 72) 8%nat X.
             apply (cword_C8 _ _ _ _ X); [exact (u_addi_Page v_thr 72 ltac:(pv) ltac:(lia)) | rewrite (w64_Page v_fstk) by pv; reflexivity | lia]. }
    split. { destruct (chk_ex_C1 mem p CT_COMMON HF QLit (A_FLAGS + 88) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [f88 Hf]. exists f88. exact Hf. }
    split; [orc|]. split; [orc|].
    split; [exact h0_rsmr_statics|]. split; [exact h0_smalloc_statics|]. split; [orc|].
    split. { dexists (Z_to_bv 64 0x63d1c8), (Z_to_bv 64 0x63d2a4).
             replace (PG p v_thr + 48)%Z with (qaddr p (QTpl (#0x1000 * v_thr)%tm) 48) by (cbn [qaddr]; rewrite (u_page p HCN v_thr) by pv; reflexivity).
             apply (chk_ro_cells mem p CT_COMMON HF); [vm_compute; reflexivity | cbn; tauto | |];
               cbn [qaddr]; rewrite (u_page p HCN v_thr) by pv; pose proof (proj1 (PG_range p HCN v_thr ltac:(pv)));
               try match goal with |- context [Z.of_nat (cells_size ?cs)] => let v := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with v end; lia. }
    split; [orc|]. split; [orc|].
    (* [comment removed for export] *) unfold b12_ro. repeat match goal with |- _ /\ _ => split end; orc.
  Qed.
  Close Scope tm_scope.
End Mem1.
