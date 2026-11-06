(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA MmapFixedA MmapNodesA MunmapSymA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM.
Import ListNotations.
Open Scope Z_scope.

Record trk (Q : assn) : Type := mkTRK {
  TR : assn -> Prop;
  JOK : jpredA -> Prop;
  tr_stable : forall J, JOK J -> stableA segsA NPRE J;
  tr_conseq : forall (P P' : assn), (forall w, P w -> P' w) -> TR P' -> TR P;
  tr_pure : forall (P : assn) (X : Prop), (forall w, P w -> X) -> (X -> TR P) -> TR P;
  tr_done : forall (P : assn), (forall w, P w -> Q w) -> TR P;
  tr_ex : forall (T : Type) (P : T -> assn) (P0 : assn), (forall w, P0 w -> exists t, P t w) -> (forall t, TR (P t)) -> TR P0;
  tr_piece : forall fuel cuts Pre l Ts,
      runA fuel cuts Pre = l -> chkNM (ss_next (ax_S Pre)) l Ts = true -> ss_lenient (ax_S Pre) = false -> (NPRE <= ss_next (ax_S Pre))%positive ->
      forall J rho tp, JOK J ->
      (forall T M rho', In (T, M) Ts -> keepsM M rho rho' -> TR (SPA segsA J T rho' tp)) -> TR (SPA segsA J Pre rho tp);
  tr_call : forall (Cst Pre : axst) (Posts : list leafA) (s : wsub) (R : list sobj) (T : axst),
      (forall ok (Jx : jpredA) rho tp, ok_frameA segsA ok Jx -> stableA segsA (ss_next (ax_S Pre)) Jx ->
         triple segsA ok (SPA segsA Jx Pre rho tp) (LQA segsA Jx (ss_next (ax_S Pre)) rho tp Posts)) ->
      (forall (Jx : jpredA) rho tp, stableA segsA (ss_next (ax_S Pre)) Jx ->
         etriple segsA (SPA segsA Jx Pre rho tp) (LQA segsA Jx (ss_next (ax_S Pre)) rho tp Posts)) ->
      entails_frA Cst Pre s = Some R -> call_checkA Cst Pre s R (map la_state Posts) = true ->
      (forall P, In P Posts -> import_postA s Pre (la_state P) Cst R = T) ->
      forallb (sprop_below (ss_next (ax_S Cst))) (ss_facts (ax_S Cst)) = true ->
      forallb (sprop_below (ss_next (ax_S T))) (ss_facts (ax_S Cst)) = true ->
      (NPRE <= ss_next (ax_S Cst))%positive ->
      forall J rhoE tp, JOK J ->
      (forall rho', agree_below (ss_next (ax_S Cst)) rhoE rho' -> TR (SPA segsA J (ax_with_facts T (ss_facts (ax_S Cst))) rho' tp)) ->
      TR (SPA segsA J Cst rhoE tp);

  tr_callS : forall (Cst Pre : axst) (Posts : list leafA) (s : wsub) (R : list sobj) (T : axst) (SIDE : valuation -> Prop),
      (forall r r', (forall i, (i < ss_next (ax_S Pre))%positive -> rw r' i = rw r i) -> SIDE r -> SIDE r') ->
      (forall ok (Jx : jpredA) rho tp, ok_frameA segsA ok Jx -> stableA segsA (ss_next (ax_S Pre)) Jx -> SIDE rho ->
         triple segsA ok (SPA segsA Jx Pre rho tp) (LQA segsA Jx (ss_next (ax_S Pre)) rho tp Posts)) ->
      (forall (Jx : jpredA) rho tp, stableA segsA (ss_next (ax_S Pre)) Jx -> SIDE rho ->
         etriple segsA (SPA segsA Jx Pre rho tp) (LQA segsA Jx (ss_next (ax_S Pre)) rho tp Posts)) ->
      entails_frA Cst Pre s = Some R -> call_checkA Cst Pre s R (map la_state Posts) = true ->
      (forall P, In P Posts -> import_postA s Pre (la_state P) Cst R = T) ->
      forallb (sprop_below (ss_next (ax_S Cst))) (ss_facts (ax_S Cst)) = true ->
      forallb (sprop_below (ss_next (ax_S T))) (ss_facts (ax_S Cst)) = true ->
      (NPRE <= ss_next (ax_S Cst))%positive ->
      forall J rhoE tp, JOK J -> SIDE (rho_sub rhoE s) ->
      (forall rho', agree_below (ss_next (ax_S Cst)) rhoE rho' -> TR (SPA segsA J (ax_with_facts T (ss_facts (ax_S Cst))) rho' tp)) ->
      TR (SPA segsA J Cst rhoE tp);

  TRP : assn -> assn -> Prop;
  tr_seqP : forall (P P' : assn), TRP P P' -> TR P' -> TR P;

  tr_callP : forall (J Jp : jpredA) (Cst Pre : axst) (s : wsub) (R : list sobj) (Posts : list (axst * jpostA)) rho tp,
      entails_frA Cst Pre s = Some R ->
      call_checkPA Cst Pre s R (map fst Posts) = true ->
      (forall rho1 tp1, TRP (SPA segsA Jp Pre rho1 tp1) (LQPA segsA (ss_next (ax_S Pre)) rho1 tp1 Posts)) ->
      (forall tr ms md, smatchA segsA rho tp Cst (tr, mkCfg ms md) -> J rho tp tr md ->
         Jp (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp tr md) ->
      (forall L JL tr ms md rhoL tpL tr' ms' md', In (L, JL) Posts ->
         smatchA segsA rho tp Cst (tr, mkCfg ms md) -> J rho tp tr md ->
         agree_vals (ss_next (ax_S Pre)) (rho_sub (rho_absorb rho R (vms md tp ms)) s) rhoL ->
         smatchA segsA rhoL tpL L (tr', mkCfg ms' md') ->
         JL (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp rhoL tpL tr' md' ->
         import_okPA rho (vms md tp ms) R s Pre L Cst rhoL
         /\ forall rho', call_linkP rho (vms md tp ms) R s (ax_S Pre) (ax_S Cst) (ax_S L) rho' rhoL ->
              TR (SPA segsA (J_ofPA JL (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp rhoL tpL) (import_postA s Pre L Cst R) rho' tpL)) ->
      TR (SPA segsA J Cst rho tp);

  tr_munmap : forall (J Jo : jpredA) A rho tp (ea en : sv) nlit,
      JOK J -> (NPRE <= ss_next (ax_S A))%positive ->
      instr_at segsA (ss_pc (ax_S A)) = Some Ecall ->
      reg_sv (ax_S A) 17 = SLit 215 -> reg_sv (ax_S A) 10 = ea -> reg_sv (ax_S A) 11 = en ->
      eval rho en = Z_to_bv 64 nlit -> nlit mod 4096 = 0 -> 0 < nlit < 2 ^ 62 ->
      (forall tr ms md, smatch_pendingA segsA rho tp A (tr, mkCfg ms md) -> J rho tp tr md ->
         let a := ms_gpr ms 0 in
         bv_unsigned a mod page_size = 0
         /\ bv_unsigned a + nlit <= TASK_SIZE
         /\ map_has (vm_maps (m_vmmaps md)) a (Z_to_bv 64 nlit) = true
         /\ (forall s, In (a, s) (vm_maps (m_vmmaps md)) -> s = Z_to_bv 64 nlit)
         /\ region_free (map_remove (vm_maps (m_vmmaps md)) a) a (Z_to_bv 64 nlit) = true
         /\ (forall o, In o (ss_objs (ax_S A)) -> ranges_disjoint (obj_range rho o) (bv_unsigned a, bv_unsigned a + nlit))
         /\ (forall rr y, In rr (ax_X A) ->
               bv_unsigned (eval rho (fst rr)) <= y < bv_unsigned (eval rho (fst rr)) + bv_unsigned (eval rho (snd rr)) ->
               ~ (bv_unsigned a <= bv_unsigned (shadow_addr (bv_unsigned (eval rho (ax_base A))) y) < bv_unsigned a + nlit))
         /\ Jo (set_rm rho (unmap_range (rm rho) a (Z_to_bv 64 nlit)))
               (tp_forget (bv_unsigned a) (bv_unsigned a + nlit) tp) tr (munmap_model md a (Z_to_bv 64 nlit))) ->
      TR (SPA segsA Jo (A_after A (SLit 0))
                (set_rm rho (unmap_range (rm rho) (eval rho ea) (Z_to_bv 64 nlit)))
                (tp_forget (bv_unsigned (eval rho ea)) (bv_unsigned (eval rho ea) + nlit) tp)) ->
      TR (SPA segsA J A rho tp);

  tr_madvise : forall (J Jo : jpredA) A rho tp (kp : word -> bool) (ea elen : sv) nlit,
      JOK J -> (NPRE <= ss_next (ax_S A))%positive ->
      instr_at segsA (ss_pc (ax_S A)) = Some Ecall ->
      reg_sv (ax_S A) 17 = SLit 233 -> reg_sv (ax_S A) 10 = ea -> reg_sv (ax_S A) 11 = elen ->
      bv_unsigned (eval rho elen) = nlit -> nlit mod 4096 = 0 -> 0 < nlit < 2 ^ 62 -> reg_sv (ax_S A) 12 = SLit 4 ->
      madvise_pre segsA J Jo A rho tp kp nlit ->
      TR (madvise_post segsA Jo A rho tp kp ea nlit) ->
      TR (SPA segsA J A rho tp)
}.
Arguments TR {Q}. Arguments JOK {Q}. Arguments tr_stable {Q}. Arguments tr_conseq {Q}. Arguments tr_pure {Q}. Arguments tr_done {Q}.
Arguments tr_piece {Q}. Arguments tr_call {Q}. Arguments tr_ex {Q}. Arguments tr_callS {Q}.
Arguments TRP {Q}. Arguments tr_seqP {Q}. Arguments tr_callP {Q}. Arguments tr_munmap {Q}. Arguments tr_madvise {Q}.

Section SideCall.
Variables (Cst : axst) (Pre : axst) (Posts : list leafA) (s : wsub) (R : list sobj) (T : axst) (g : positive) (SIDE : valuation -> Prop).
Hypothesis HSIDE : forall r r', (forall i, (i < ss_next (ax_S Pre))%positive -> rw r' i = rw r i) -> SIDE r -> SIDE r'.
Hypothesis Hsum : forall ok (Jx : jpredA) rho tp, ok_frameA segsA ok Jx -> stableA segsA (ss_next (ax_S Pre)) Jx -> SIDE rho ->
  triple segsA ok (SPA segsA Jx Pre rho tp) (LQA segsA Jx (ss_next (ax_S Pre)) rho tp Posts).
Hypothesis Hesum : forall (Jx : jpredA) rho tp, stableA segsA (ss_next (ax_S Pre)) Jx -> SIDE rho ->
  etriple segsA (SPA segsA Jx Pre rho tp) (LQA segsA Jx (ss_next (ax_S Pre)) rho tp Posts).
Hypothesis He : entails_frA Cst Pre s = Some R.
Hypothesis Hchk : call_checkA Cst Pre s R (map la_state Posts) = true.
Hypothesis HT : forall P, In P Posts -> import_postA s Pre (la_state P) Cst R = T.
Hypothesis FBC : forallb (sprop_below (ss_next (ax_S Cst))) (ss_facts (ax_S Cst)) = true.
Hypothesis FBT : forallb (sprop_below (ss_next (ax_S T))) (ss_facts (ax_S Cst)) = true.
Hypothesis NXC : (g <= ss_next (ax_S Cst))%positive.

Lemma side_in : forall rhoE ms, SIDE (rho_sub rhoE s) -> SIDE (rho_sub (rho_absorb rhoE R ms) s).
Proof. intros rhoE ms H. apply (HSIDE (rho_sub rhoE s)); [|exact H]. intros i _. cbn [rho_sub rw]. apply eval_absorb. Qed.

Theorem call_contS : forall (J : jpredA) ok rhoE tp (Q : assn),
  ok_frameA segsA ok J -> stableA segsA g J -> SIDE (rho_sub rhoE s) ->
  (forall rho', agree_below (ss_next (ax_S Cst)) rhoE rho' -> triple segsA ok (SPA segsA J (ax_with_facts T (ss_facts (ax_S Cst))) rho' tp) Q) ->
  triple segsA ok (SPA segsA J Cst rhoE tp) Q.
Proof.
  intros J ok rhoE tp Q HOK HST HS HC.
  set (Jf := (fun (r : valuation) t tr md => J rhoE t tr md /\ SIDE r) : jpredA).
  assert (Jf_okf : ok_frameA segsA ok Jf) by (intros r t tr ms md msv' [HJ _]; exact (HOK rhoE t tr ms md msv' HJ)).
  assert (Jf_st : stableA segsA (ss_next (ax_S Pre)) Jf).
  { intros r r' t tr md md' Hag Hme [HJ HSr]. unfold Jf in *. split; [eapply HST; [apply agree_below_refl | exact Hme | exact HJ]|].
    apply (HSIDE r r'); [|exact HSr]. intros i Hi. symmetry. exact (proj1 Hag i Hi). }
  apply (triple_pre_pure segsA ok _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segsA _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_soundA_tp ok J Jf Jf J Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. apply (triple_pre_pure segsA ok _ _ (SIDE rho1)); [intros w Hw; exact (proj2 (proj2 Hw))|]. intros HS1. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st HS1).
  - intros tr ms md Hsm HJ. split; [exact HJ | exact (side_in rhoE _ HS)].
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _].
    eapply HST; [| apply mat_equiv_refl | exact HJ']. eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' HinL Hag. rewrite (HT L HinL).
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC rho' Hag)].
    apply SPA_refacts; [exact Hw | exact FBT | intros _; exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC)].
Qed.
Theorem call_econtS : forall (J : jpredA) rhoE tp (Q : world -> Prop),
  stableA segsA g J -> SIDE (rho_sub rhoE s) ->
  (forall rho', agree_below (ss_next (ax_S Cst)) rhoE rho' -> etriple segsA (SPA segsA J (ax_with_facts T (ss_facts (ax_S Cst))) rho' tp) Q) ->
  etriple segsA (SPA segsA J Cst rhoE tp) Q.
Proof.
  intros J rhoE tp Q HST HS HC.
  set (Jf := (fun (r : valuation) t tr md => J rhoE t tr md /\ SIDE r) : jpredA).
  assert (Jf_st : stableA segsA (ss_next (ax_S Pre)) Jf).
  { intros r r' t tr md md' Hag Hme [HJ HSr]. unfold Jf in *. split; [eapply HST; [apply agree_below_refl | exact Hme | exact HJ]|].
    apply (HSIDE r r'); [|exact HSr]. intros i Hi. symmetry. exact (proj1 Hag i Hi). }
  intros w Hw. pose proof (SPA_facts_hold segsA _ rhoE Cst tp w Hw) as HFC. revert w Hw.
  apply (call_completeA_tp J Jf Jf J Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. apply (etriple_pre_pure segsA _ _ (SIDE rho1)); [intros w Hw; exact (proj2 (proj2 Hw))|]. intros HS1. exact (Hesum Jf rho1 tp1 Jf_st HS1).
  - intros tr ms md Hsm HJ. split; [exact HJ | exact (side_in rhoE _ HS)].
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _].
    eapply HST; [| apply mat_equiv_refl | exact HJ']. eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' HinL Hag. rewrite (HT L HinL).
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC rho' Hag)].
    apply SPA_refacts; [exact Hw | exact FBT | intros _; exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC)].
Qed.
End SideCall.

Definition trS (ok : world -> Prop) (Q : assn) : trk Q.
Proof.
  refine (mkTRK Q (fun P => triple segsA ok P Q) (fun J => ok_frameA segsA ok J /\ ok_pframeA segsA ok J /\ stableA segsA NPRE J) _ _ _ _ _ _ _ _
                (fun P P' => triple segsA ok P P') _ _ _ _).
  - intros J (_ & _ & H). exact H.
  - intros P P' HP HT. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros P X HX HT. exact (triple_pre_pure segsA ok P Q X HX HT).
  - intros P HP. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | apply triple_refl].
  - intros T P P0 HE HT n Hg w Hw. destruct (HE w Hw) as (t & Ht). exact (HT t n Hg w Ht).
  - intros fuel cuts Pre l Ts RUNL CHK HLEN HNX J rho tp (HOK & _ & HST) HC.
    exact (piece_soundM fuel cuts Pre l Ts RUNL CHK HLEN HNX J ok rho tp Q HOK HST HC).
  - intros Cst Pre Posts s R T Hsum Hesum He Hchk HT FBC FBT NXC J rhoE tp (HOK & _ & HST) HC.
    exact (call_cont Cst Pre Posts s R T NPRE Hsum He Hchk HT FBC FBT NXC J ok rhoE tp Q HOK HST HC).
  - intros Cst Pre Posts s R T SIDE HSD Hsum Hesum He Hchk HT FBC FBT NXC J rhoE tp (HOK & _ & HST) HS HC.
    exact (call_contS Cst Pre Posts s R T NPRE SIDE HSD Hsum He Hchk HT FBC FBT NXC J ok rhoE tp Q HOK HST HS HC).
  - intros P P' H1 H2. exact (triple_seq H1 H2).
  - intros J Jp Cst Pre s R Posts rho tp He Hchk Hsum Hin Hout.
    exact (call_soundPA segsA ok J Jp Cst Pre s R Posts Q rho tp He Hchk Hsum Hin Hout).
  - intros J Jo A rho tp ea en nlit (HOK & HOKP & HST) HNX Hi H17 H10 H11 Een Hmod Hn HJ HT.
    eapply triple_seq; [apply triple1_triple; exact (triple1_munmap_symA segsA ok J Jo A rho tp ea en nlit HOK HOKP (stableA_mono segsA NPRE _ J HNX HST) Hi H17 H10 H11 Een Hmod Hn HJ)|].
    exact HT.
  - intros J Jo A rho tp kp ea elen nlit (HOK & HOKP & HST) HNX Hi H17 H10 H11 Helen Hmod Hn H12 HJ HT.
    eapply triple_seq; [apply triple1_triple; exact (triple1_madvise_dontneedA segsA J Jo A rho tp kp ea elen nlit H17 H10 H11 Helen Hmod Hn H12 ok HOK HOKP (stableA_mono segsA NPRE _ J HNX HST) Hi HJ)|].
    exact HT.
Defined.

Definition trC (Q : assn) : trk Q.
Proof.
  refine (mkTRK Q (fun P => etriple segsA P Q) (fun J => stableA segsA NPRE J) _ _ _ _ _ _ _ _ (fun P P' => etriple segsA P P') _ _ _ _).
  - intros J H. exact H.
  - intros P P' HP HT. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros P X HX HT. exact (etriple_pre_pure segsA P Q X HX HT).
  - intros P HP. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | apply etriple_refl].
  - intros T P P0 HE HT w Hw. destruct (HE w Hw) as (t & Ht). exact (HT t w Ht).
  - intros fuel cuts Pre l Ts RUNL CHK HLEN HNX J rho tp HST HC.
    exact (piece_completeM fuel cuts Pre l Ts RUNL CHK HLEN HNX J rho tp Q HST HC).
  - intros Cst Pre Posts s R T Hsum Hesum He Hchk HT FBC FBT NXC J rhoE tp HST HC.
    exact (call_econt Cst Pre Posts s R T NPRE Hesum He Hchk HT FBC FBT NXC J rhoE tp Q HST HC).
  - intros Cst Pre Posts s R T SIDE HSD Hsum Hesum He Hchk HT FBC FBT NXC J rhoE tp HST HS HC.
    exact (call_econtS Cst Pre Posts s R T NPRE SIDE HSD Hesum He Hchk HT FBC FBT NXC J rhoE tp Q HST HS HC).
  - intros P P' H1 H2. exact (etriple_seq H1 H2).
  - intros J Jp Cst Pre s R Posts rho tp He Hchk Hsum Hin Hout.
    exact (call_completePA segsA J Jp Cst Pre s R Posts Q rho tp He Hchk Hsum Hin Hout).
  - intros J Jo A rho tp ea en nlit HST HNX Hi H17 H10 H11 Een Hmod Hn HJ HT.
    eapply etriple_seq; [exact (etriple_munmap_symA segsA J Jo A rho tp ea en nlit (stableA_mono segsA NPRE _ J HNX HST) Hi H17 H10 H11 Een Hmod Hn HJ)|].
    exact HT.
  - intros J Jo A rho tp kp ea elen nlit HST HNX Hi H17 H10 H11 Helen Hmod Hn H12 HJ HT.
    eapply etriple_seq; [exact (etriple_madvise_dontneedA segsA J Jo A rho tp kp ea elen nlit H17 H10 H11 Helen Hmod Hn H12 (stableA_mono segsA NPRE _ J HNX HST) Hi HJ)|].
    exact HT.
Defined.
Lemma trS_TR : forall ok Q P, TR (trS ok Q) P = triple segsA ok P Q. Proof. reflexivity. Qed.
Lemma trC_TR : forall Q P, TR (trC Q) P = etriple segsA P Q. Proof. reflexivity. Qed.
Lemma trS_JOK : forall ok Q J, JOK (trS ok Q) J = (ok_frameA segsA ok J /\ ok_pframeA segsA ok J /\ stableA segsA NPRE J). Proof. reflexivity. Qed.
Lemma trS_TRP : forall ok Q P P', TRP (trS ok Q) P P' = triple segsA ok P P'. Proof. reflexivity. Qed.
Lemma trC_TRP : forall Q P P', TRP (trC Q) P P' = etriple segsA P P'. Proof. reflexivity. Qed.
Lemma trC_JOK : forall Q J, JOK (trC Q) J = stableA segsA NPRE J. Proof. reflexivity. Qed.

Lemma okp_via : forall ok (Kc : list event -> Model -> Prop) (J : jpredA),
  ok_pframeA segsA ok (liftKA Kc) -> (forall rho tp tr md, J rho tp tr md -> Kc tr md) -> ok_pframeA segsA ok J.
Proof. intros ok Kc J Hokp HJK rho tp tr ms md x8 HJ Hp Ho. exact (Hokp rho tp tr ms md x8 (HJK _ _ _ _ HJ) Hp Ho). Qed.
