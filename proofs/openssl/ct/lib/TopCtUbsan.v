(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ModelInvCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling Image Stage Nodes Tac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LB_Sum LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import BnBase BnModel BnTree BgState ApBase ApState ApLogic ApOwner ApBridge CtCaps CtBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInstAp.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RF_malloc_spec RF_free_spec RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Driver_iface Impl_closed.
Require OssFuzzTheorems.openssl.ct.images.Ubsan.
Require OssFuzzTheorems.openssl.ct.images.Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgUct := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) (only parsing).
Notation imgPct := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation RunRnd := OssFuzzTheorems.Proofs.openssl.ct.lib.P.Rnd.RunRnd.

(* [comment removed for export] *)
Definition ct_ops : list lop := CtHXU.HxpInstAp.asn1parse_ops.
Definition LM_ct : LibModel := @LM_ap (ap_ls bptr) ct_ls0 ct_lib_one.

(* [comment removed for export] *)
Definition PcapCt (c : Z) : Z :=
  if (0 <=? c) && (c <? 48) then LRs (sizes_of ct_ops) c + NBC c + 5
  else if c =? 63 then n63s (sizes_of ct_ops) + CT_NB63 + 5 else 0.

Lemma PcapCt_nonneg : forall c, 0 <= PcapCt c.
Proof.
  intros c. unfold PcapCt.
  pose proof (zcount_nonneg (fun n => negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c)) (sizes_of ct_ops)).
  pose proof (zcount_nonneg (fun n => MMAP_THRESHOLD <=? n) (sizes_of ct_ops)).
  unfold LRs, n63s, CT_NB63.
  destruct ((0 <=? c) && (c <? 48)) eqn:E.
  - apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    pose proof (NBC_nonneg c (conj E1 E2)). lia.
  - destruct (c =? 63); lia.
Qed.

Lemma capsCt_ct : capsCt_ok PcapCt (sizes_of ct_ops).
Proof. apply capsCt_ok_b_ok. vm_compute. reflexivity. Qed.

Lemma ops_checked_ct : ops_wf ct_ops [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma H_init_ct : lwf (okT (sizes_of ct_ops)) (lib_init (LibModel := LM_ct)) []
                      (fun ls Li => ct_linv ls [] /\ subms (map snd Li) (sizes_of ct_ops)).
Proof.
  eapply lwf_mono; [apply (init_of_ops_lwf ct_ops (ct_ls0 : @LS LM_ct) ops_checked_ct)|]. intros ls Li [E HS]. split; [|exact HS].
  rewrite E. exact ct_linv_init.
Qed.

Lemma H_one_ct : forall (ls : @LS LM_ct) d X, ct_linv ls X -> zlength d <= MAX_INPUT ->
  lwf okCt (lib_one ls d) X (fun r X' => ct_linv (fst r) X').
Proof. intros ls d X H Hd. exact (ct_H_one ls d X H Hd). Qed.

Lemma H_rc_ct : forall (ls : @LS LM_ct) d, lleaves (lib_one ls d) (fun r => snd r = 0).
Proof. intros ls d. exact (ct_H_rc ls d). Qed.

Section OpenObligations.
(* [comment removed for export] *)
Variable linv : ap_ls bptr -> (word -> option byte) -> list MallocBlocks.block -> Prop.
Hypothesis LINV_INIT : forall m OW, HxpFinal.ap_init_facts m OW -> linv ap_ls0 m OW.
Hypothesis LINV_AGREE : forall ls OW m m', linv ls m OW -> Lib_kit.agree_on (fun a => Lib_iface.rin_ivs HxpInit.LIBW_HX a \/ in_block OW a) m m' -> linv ls m' OW.

(* [comment removed for export] *)
Definition LSP_ct : @LibSpec LM_ct := @LSP_ap (ap_ls bptr) ct_ls0 ct_lib_one linv.

(* [comment removed for export] *)
Hypothesis ALIGNED_P : forall (CE__ : Ceiling) (RN__ : RunRnd), @RAligned_iface.rposix_memalign_stmt CE__ RN__.

(* [comment removed for export] *)
Hypothesis FUZZ_P : forall (CE__ : Ceiling) (RN__ : RunRnd), @Lib_iface.rfuzz_one_stmt CE__ RN__ LM_ct LSP_ct.

(* [comment removed for export] *)
Lemma implG_ubsan_ct : implG_stmt (LM := LM_ct) ctusegs Ubsan.M.init_pc Ubsan.M.phdrs ctustage.
Proof.
  exact (CtU.Impl_closed.implG_U_stmt_closed LM_ct
           (fun CE RN => LSP_ct)
           (fun CE RN => @LL_ap (ap_ls bptr) ct_ls0 ct_lib_one linv LINV_AGREE)
           (fun CE RN => @rinit_ap CE RN (ap_ls bptr) ct_ls0 ct_lib_one linv LINV_INIT (ALIGNED_P CE RN))
           FUZZ_P).
Qed.

(* [comment removed for export] *)
Lemma side_ubsan_ct_lim : forall lim, KLIM + SMALLREQ <= lim -> side_canon_off ncfg Tc imgUct lim.
Proof.
  intros lim Hlim.
  exact (G_side_off (LM := LM_ct) PcapCt (sizes_of ct_ops) okCt ct_linv PcapCt_nonneg
           (capsT_of_capsCt PcapCt (sizes_of ct_ops) capsCt_ct)
           (okCt_bridge PcapCt (sizes_of ct_ops) capsCt_ct)
           H_init_ct H_one_ct H_rc_ct
           ctusegs _ _ ctustage lim image_low_ctusegs Hlim implG_ubsan_ct).
Qed.

Lemma side_ubsan_ct : side_canon_off ncfg Tc imgUct target_alloc_limit.
Proof. apply side_ubsan_ct_lim. exact lim_target_ok. Qed.
End OpenObligations.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarU Require HarTop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RF_aligned_spec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require HxpLinv HxpFinal HxpInit.

Definition linvP : ap_ls bptr -> (word -> option byte) -> list MallocBlocks.block -> Prop := CtHarU.HarTop.linvP.
Lemma linvP_init : forall m OW, HxpFinal.ap_init_facts m OW -> linvP ap_ls0 m OW.
Proof. exact CtHarU.HarTop.linvP_init. Qed.
Lemma linvP_agree : forall ls OW m m', linvP ls m OW ->
  Lib_kit.agree_on (fun a => Lib_iface.rin_ivs HxpInit.LIBW_HX a \/ in_block OW a) m m' -> linvP ls m' OW.
Proof. exact CtHarU.HarTop.linvP_agree. Qed.

(* [comment removed for export] *)
Definition alignedP : forall (CE__ : Ceiling) (RN__ : RunRnd), @RAligned_iface.rposix_memalign_stmt CE__ RN__ :=
  fun CE__ RN__ => @CtMallocU.RF_aligned_spec.rposix_memalign_spec CE__ RN__.

(* [comment removed for export] *)
Lemma FUZZ_P : forall (CE__ : Ceiling) (RN__ : RunRnd), @Lib_iface.rfuzz_one_stmt CE__ RN__ LM_ct (LSP_ct linvP).
Proof. intros CE RN. exact (@CtHarU.HarTop.rfuzz_one_ct_closed CE RN). Qed.

Lemma side_ubsan_ctP : side_canon_off ncfg Tc imgUct target_alloc_limit.
Proof. exact (side_ubsan_ct linvP linvP_init linvP_agree alignedP FUZZ_P). Qed.
Lemma implG_ubsan_ctP : implG_stmt (LM := LM_ct) ctusegs Ubsan.M.init_pc Ubsan.M.phdrs ctustage.
Proof. exact (implG_ubsan_ct linvP linvP_init linvP_agree alignedP FUZZ_P). Qed.

Require OssFuzzTheorems.Proofs.openssl.ct.lib.TopCtPlain.
Theorem base_ct_ubsan :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target imgPct imgUct.
Proof. exact (glue_scfg_budgets ncfg Tc _ _ TopCtPlain.side_plain_ctP side_ubsan_ctP). Qed.
