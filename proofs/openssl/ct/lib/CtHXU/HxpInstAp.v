(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RF_malloc_spec RF_realloc_spec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg LibOps ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxVal HxMem HxStep HxHook HxHookSound.
From OssFuzzTheorems.Proofs.openssl.ct.lib.ApHX Require Import HxFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts HxpInv HxpHkAligned HxpHkAlignedOk HxpMain HxpFinal HxpLaws.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section ApInst.
Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variable St : Type.
Variable st0 : St.
Variable one : St -> list Z -> lprog (St * Z).
(* [comment removed for export] *)
Variable linv : St -> (word -> option byte) -> list block -> Prop.
Hypothesis linv_init : forall m OW, ap_init_facts m OW -> linv st0 m OW.
Hypothesis linv_agree : forall ls OW m m', linv ls m OW -> agree_on (fun a => rin_ivs LIBW_HX a \/ in_block OW a) m m' -> linv ls m' OW.

(* [comment removed for export] *)
Definition asn1parse_ops : list lop := map dec_op OPS.

Definition LM_ap : LibModel := mkLibModel St (init_of_ops asn1parse_ops st0) one.

(* [comment removed for export] *)
Definition LSP_ap : @LibSpec LM_ap := @Build_LibSpec LM_ap hx_pristine linv LIBW_HX 65536.

Lemma LL_ap : @LibLaws LM_ap LSP_ap.
Proof.
  constructor.
  - exact LIBW_HX_img.
  - cbn. lia.
  - cbn. lia.
  - (* [comment removed for export] *)
    intros m Hnone (T1 & T2). split; [exact Hnone|]. split; [exact T1|].
    eapply rw_cells_recast; [exact T2 | cbn; auto | vm_compute; reflexivity | reflexivity].
  - (* [comment removed for export] *)
    intros m m' (H1 & H2 & H3) AG. split; [|split].
    + intros a Ha Hi Hn. rewrite (proj1 (AG a Ha Hi)). exact (H1 a Ha Hi Hn).
    + eapply rw_cells_agree; [exact AG | exact H2 |]. intros a Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha. cbn [LIBW LSP_ap rin_ivs LIBW_HX fst snd]. lia.
    + eapply rw_cells_agree; [exact AG | exact H3 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [LIBW LSP_ap rin_ivs LIBW_HX fst snd]. lia.
  - (* [comment removed for export] *)
    intros ls OW m m' HI AG. exact (linv_agree ls OW m m' HI AG).
Qed.

(* [comment removed for export] *)
Hypothesis ALIGNED : rposix_memalign_stmt.

Lemma ALIGNED_OK : forall (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) (s0 : PState)
    (ls0 : @LS LM_ap) (POST : @LS LM_ap -> PState -> machine_state -> Prop),
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - to_Z STK -> sp0 <= B -> sp0 < 2 ^ 64 ->
  hook_ok' ctusegs ghost (J (LM := LM_ap) ls0 POST) (FInv (LSP := LSP_ap) LB lo B sp0 m0 F0 fc0 s0) hkp_posix_memalign.
Proof.
  intros LB lo B sp0 m0 F0 fc0 s0 ls0 POST H1 H2 H3 H4 H5.
  exact (hkp_posix_memalign_ok (LM := LM_ap) (LSP := LSP_ap) LB lo B sp0 m0 F0 fc0 s0 ls0 POST H1 H2 H3 H4 H5 ALIGNED).
Qed.

(* [comment removed for export] *)
Theorem rinit_ap : @rinit_stmt CE__ RN__ LM_ap LSP_ap.
Proof.
  apply (hx_rinit_ap (LM := LM_ap) (LSP := LSP_ap) RF_malloc_spec.rmalloc_spec RF_realloc_spec.rrealloc_spec ALIGNED_OK (st0 : @LS LM_ap)).
  - reflexivity.
  - reflexivity.
  - cbn. lia.
  - intros m H. exact H.
  - intros m OW H. exact (linv_init m OW H).
Qed.

End ApInst.
