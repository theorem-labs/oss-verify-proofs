(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtCpsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CSK.
Definition mem := (word -> option byte).
Section Rt.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Variable FPI : FPState -> Prop.

Definition strlen_pre (LB : list (Z * Z)) (FF : list fframe) (sp scr s K : Z) (buf : list byte) (R : bvmap 5 word) (M : mem) : Prop :=
  getr R 10%bv = Z_to_bv 64 s /\ 0 <= s /\ s + Z.of_nat (length buf) <= 2 ^ 47 /\ 0 <= K < 2 ^ 27 /\
  rdn (hl_segs L) M (Z_to_bv 64 s) (length buf) = Some buf /\ (s + K) / 8 * 8 + 8 <= s + Z.of_nat (length buf) /\
  nth (Z.to_nat K) buf (Z_to_bv 8 0) = Z_to_bv 8 0 /\ (forall j, (j < Z.to_nat K)%nat -> nth j buf (Z_to_bv 8 0) <> Z_to_bv 8 0) /\
  (forall i, 0 <= i < Z.of_nat (length buf) -> hl_img_lo L <= s + i < hl_img_hi L \/ aclient L ar LB FF sp scr (s + i)) /\
  (forall a, icl_ro_lo IL <= a < icl_ro_hi IL -> M (Z_to_bv 64 a) = None) /\ aacc M s (K + 1) /\ app_rng ar s (K + 1).
Definition strlen_post (LB : list (Z * Z)) (cr : credit) (K : Z)
  (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  getr R' 10%bv = Z_to_bv 64 K /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [].
Lemma strlen_cps : astrlen_spec L ar IL SCFG HI -> forall scr LB FF LK cr A s K buf sp r, 0 <= icl_scr_strlen IL <= scr ->
  CBA.cps_asanG L ar HI FPI (icl_strlen IL) r sp scr LB FF LK cr A 0 (strlen_pre LB FF sp scr s K buf) (strlen_post LB cr K).
Proof.
  intros SPEC scr LB FF LK cr A s K buf sp r Hscr fx R M model Kt HH Hmo HK HFP Hra Hraok Hsp Htp Hstk _ _
         (Ha0 & Hs0 & Hs1 & HK27 & Hrd & Hwd & Hnul & Hnz & Hcl & Hro & Hacc & Happ) CONT.
  pose proof (CRC.usp ar R M sp scr ltac:(lia) Hsp Hstk) as USP.
  apply (SPEC fx R M model LB FF LK cr A s K buf Kt HH (proj1 Hmo) (proj2 Hmo) Ha0 Htp (CRC.ret_ok_of_ra R r Hra Hraok)).
  - rewrite USP. exact (CRC.astack_ok_of_astk L ar M sp scr _ Hscr Hstk).
  - exact Hs0.
  - exact Hs1.
  - exact HK27.
  - exact Hrd.
  - exact Hwd.
  - exact Hnul.
  - exact Hnz.
  - rewrite USP. intros i Hi. destruct (Hcl i Hi) as [X|X]; [left; exact X | right; exact (CRC.aclient_scr0 L ar _ _ _ _ _ _ Hscr X)].
  - exact Hro.
  - exact Hacc.
  - exact Happ.
  - exact HK.
  - rewrite USP. intros R' M' model' Ha0' HRP Hkeep Hdef Hmono Hrt HMI' HH'. rewrite Hra.
    apply (CONT fx R' M' model' LB cr LB [] LK A HFP); [| exact HRP | | exact Hrt | apply incl_refl | exact (CRC.amodel_rt _ _ _ _ Hmo Hrt HMI') | apply incl_refl | exact HH'].
    + split; [exact Ha0'|]. repeat split; reflexivity.
    + apply (CRC.ahpres_scr L ar LB FF sp (icl_scr_strlen IL) scr [] M M' Hscr Hstk); [intros a Ha Hc _; exact (Hkeep a Ha Hc) | exact Hdef | intros w a []].
Qed.
End Rt.
End CSK.
