(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF StepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface APoisonR_iface AFake_iface AFake_arep
     AInstance AInstanceM AInstanceF AU_kit AU_iface AU_parts_iface ALoose ALooseInst ALooseSet ALooseLaws ALoose_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Keyed Unification.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aunw_of5L : forall L RNG0 st LB m RNG lo PC (sp s0 ra : word) tr,
  AHEAP_L L RNG0 st LB m ->
  aunw5 m L PC sp s0 ra tr -> rng RNG lo (al_top L - lo) -> aunw m L RNG lo PC sp s0 ra tr.
Proof.
  intros L RNG0 st LB m RNG lo PC sp s0 ra tr AH H5 HR. pose proof (AHL_layout _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  destruct H5 as [(A & B & C & E)|(A & B & C)]; [left| right].
  - split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact E| exact HR].
  - split; [exact A|]. split; [lia| exact C].
Qed.

(* [comment removed for export] *)
Lemma implMA_afree_callL : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
  AHEAP_L L RNG (aps_m s) LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw5 m L AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  aps_ok L s ->
  implMA RNG (afree_M p) s
    (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
       /\ afree_post aci_I AHEAP_L L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until tr. intros AH HIN MI ST BOT LOS TP A0 U5 NS8 RA4 RAPC SP16 RSTK [ROK AT].
  assert (TOPS : bv_unsigned sp < al_top L) by (destruct U5 as [(A5 & _)|(_ & A5 & _)]; lia).
  pose proof (aunw_of5L _ _ _ _ _ _ _ _ _ _ _ _ AH U5 RSTK) as UW.
  assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
  apply implMA_afree; [exact AT|]. eapply implF_epost_mono; [eapply AHL_free; eauto|].
  cbv beta. intros st' RNG' ms' PO. split; [reflexivity| exact PO].
Qed.

(* [comment removed for export] *)
Lemma implMA_afree_nullL : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (tr : list Z),
  AHEAP_L L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  aunw5 m L AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  evtF asegs RNG (afree_null_post aci_I AHEAP_L L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until tr. intros AH MI ST BOT LOS TP A0 U5 NS8 RA4 RAPC SP16 RSTK.
  pose proof (aunw_of5L _ _ _ _ _ _ _ _ _ _ _ _ AH U5 RSTK) as UW.
  assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; destruct U5 as [(A5 & _)|(_ & A5 & _)]; lia]).
  eapply AHL_free_null; eauto.
Qed.

(* [comment removed for export] *)
Definition opdelete_stmtL (entry : Z) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
  AHEAP_L L RNG (aps_m s) LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  bv_unsigned sp + 16 < al_top L ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr ->
  In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  aps_ok L s ->
  implMA RNG (HarnessM.opdelete afree_M p) s
    (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
       /\ afree_post aci_I AHEAP_L L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Theorem AHL_opdelete_sz : opdelete_stmtL AOPDEL_SZ.
Proof.
  unfold opdelete_stmtL; intros until tr; intros AH HIN MI ST BOT LOS TOP TP A0 UC HU NS8 RA4 RAPC LTR SP16 RSTK ROK;
    unfold HarnessM.opdelete; apply implMA_from_evtF; unfold AOPDEL_SZ, AOPDEL.
  zstep. zstep. apply evtF_done. eapply implMA_afree_callL; eauto using aunw_chain.
Qed.
Theorem AHL_opdelete : opdelete_stmtL AOPDEL.
Proof.
  unfold opdelete_stmtL; intros until tr; intros AH HIN MI ST BOT LOS TOP TP A0 UC HU NS8 RA4 RAPC LTR SP16 RSTK ROK;
    unfold HarnessM.opdelete; apply implMA_from_evtF; unfold AOPDEL_SZ, AOPDEL.
  zstep. apply evtF_done. eapply implMA_afree_callL; eauto using aunw_chain.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem AHL_lblock : forall L RNG st LB m p A n,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  1 <= n <= AREQMAX
  /\ ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7))
  /\ wr_at asegs m A n
  /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n)
  /\ (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
         /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO))).
Proof.
  intros L RNG st LB m p A n AH Hin.
  pose proof (AHL_block L RNG st LB m p A n AH Hin) as (NB & BR & R1 & R2 & _ & WR & _ & AR).
  split; [exact NB|]. split; [exact BR|]. split; [exact R1|]. split; [exact R2|]. split; [exact WR|].
  split; [exact (AHL_chunk L RNG st LB m p A n AH Hin)| exact AR].
Qed.

Lemma set_blk_V_at : forall L p A n e i, al_V (set_blk L p A n e) i = al_V L i.
Proof. intros. rewrite set_blk_V. reflexivity. Qed.
Lemma set_blk_afake_rng_iff : forall L p A n e RNG, afake_rng (set_blk L p A n e) RNG <-> afake_rng L RNG.
Proof. intros. rewrite set_blk_afake_rng. tauto. Qed.

(* [comment removed for export] *)
Lemma AHL_of_AI : forall FREE L RNG st LB m, AHEAP (AI_of FREE) L RNG st LB m -> AHEAP_L L RNG st LB m /\ al_tight L.
Proof. exact AI_of_L. Qed.
Lemma AHL_to_AI : forall FREE L RNG st LB m, AHEAP_L L RNG st LB m -> al_tight L -> AHEAP (AI_of FREE) L RNG st LB m.
Proof. exact AI_of_of_L. Qed.
End CANSEC1.
