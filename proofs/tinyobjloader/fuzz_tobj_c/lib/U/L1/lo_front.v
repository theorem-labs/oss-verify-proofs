From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LoFront.
Import LoU.

Definition pc_skip : Z := 0x13f70.
(* token loop cut after the byte test (s6 = pQ holds no separator), before s6 += 1: the first byte is the one the
   skip loop tested, so every token that reaches the dispatch is non-empty (pT0 <= pQ < pQ + 1 = token end) *)
Definition pc_tok : Z := 0x13fa8.

Definition K_loop1 : sstate := add_facts [SPUle (SLit 4096) LD.xLD] K_loop.

Definition eR : sv := SAlu ALU_ADD LD.pLEN (LD.txt LD.pPOS).
Definition ifr : list sprop :=
  [SPUlt LD.pI LD.xLC; SPUle (SLit 4096) LD.xLD; SPUle LD.pE LD.vL; SPUle LD.pLEN (SLit (2 ^ 24));
   SPUle LD.pPOS (SLit (2 ^ 26))].
Definition LI (pc : Z) (regs : list (nat * sv)) (cp : list cell) (facts : list sprop) : sstate :=
  LS pc ((9%nat, SAlu ALU_ADD LD.pI (SLit 1)) :: (23%nat, eR) :: regs)
    (Some (SAlu ALU_ADD LD.pI (SLit 1))) cp (ceC LD.pE) [] (facts ++ ifr).

Definition K_skip : sstate :=
  LI pc_skip [(10%nat, LD.pR); (24%nat, LD.txt LD.pQ)] []
    [SPUle (SLit 1) LD.pR; SPUle LD.pR LD.pLEN; SPEq (SAlu ALU_ADD LD.pQ LD.pR) LD.pE; SPUle LD.pPOS LD.pQ;
     SPUlt LD.pQ LD.pE; SPUle LD.pQ (SLit (2 ^ 26))].

(* a0 = s6 + 1 (incremented at 0x13fa0); written 1 + txt pQ so the binder takes pQ from s6 *)
Definition K_tok : sstate :=
  LI pc_tok [(10%nat, SAlu ALU_ADD (SLit 1) (LD.txt LD.pQ)); (22%nat, LD.txt LD.pQ); (24%nat, LD.txt LD.pT0)] (cpC LD.pQ)
    [SPUle LD.pPOS LD.pT0; SPUle LD.pT0 LD.pQ; SPUlt LD.pQ LD.pE; SPUle LD.pT0 (SLit (2 ^ 26));
     SPUle LD.pQ (SLit (2 ^ 26))].

Definition rL : Z := 500.
Definition n_loop1 : aedesc := ((K_loop1, (tvL, amL)), (rL, LD.VLp 60 LD.z0)).
Definition n_skip : aedesc := ((K_skip, (tvL, amL)), (rL, LD.VLp 30 LD.pR)).
Definition n_tok : aedesc := ((K_tok, (tvL, amL)), (rL, LD.VLp 28 (SAlu ALU_SUB LD.pE LD.pQ))).
Definition front_nodes : list aedesc := [n_loop1; n_skip; n_tok].

Lemma lines_nz : forall Kc FB rho0 rho tr md,
  JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tvL amL rho tr md ->
  Forall (holds rho) (ss_facts K_loop) -> holds rho (SPUle (SLit 4096) LD.xLD).
Proof.
  intros Kc FB rho0 rho tr md HJ HFX.
  assert (Hin : In (LD.xLD, LD.kb 16 LD.xLK) tvL) by (vm_compute; tauto).
  assert (F1 : holds rho (SPUlt LD.pI LD.xLC)) by (eapply (proj1 (Forall_forall _ _) HFX); vm_compute; tauto).
  assert (F2 : holds rho (SPUle LD.xLC LD.xLK)) by (eapply (proj1 (Forall_forall _ _) HFX); vm_compute; tauto).
  assert (F4 : holds rho (SPUle LD.xLK (SLit LD.two47))) by (eapply (proj1 (Forall_forall _ _) HFX); vm_compute; tauto).
  rewrite holds_ult in F1. rewrite holds_ule in F2, F4.
  assert (Hnz : tnz rho (LD.xLD, LD.kb 16 LD.xLK)).
  { pose proof HJ as (Ai & (_ & _ & _ & _ & (_ & _ & HZ) & _) & _).
    pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Z0. unfold tnz, tvv in Z0 |- *. cbn [fst snd] in Z0 |- *.
    intros H0. specialize (Z0 (fun H => H H0)).
    unfold LD.kb in Z0. rewrite U_mul, U_lit in Z0. rewrite U_lit in F4. unfold LD.two47, M64v in *.
    pose proof (urange (eval rho LD.pI)) as R1.
    rewrite (Z.mod_small 16) in Z0 by lia. rewrite Z.mod_small in F4 by lia.
    rewrite Z.mod_small in Z0 by lia. lia. }
  pose proof (JGA_tv_facts segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tvL amL rho tr md _ HJ Hin Hnz) as HT.
  apply (proj1 (Forall_forall _ _) HT). unfold tv_facts. cbn [fst snd]. right; right; right; left; reflexivity.
Qed.

Lemma SPJ_K_loop1 : forall Kc FB rho0 rho w,
  SPJ segsU (JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tvL amL) K_loop rho w ->
  SPJ segsU (JGA segsU C_U LD.NP Kc rho0 (LD.P0_lo FB) FB tvL amL) K_loop1 rho w.
Proof.
  intros Kc FB rho0 rho w H. unfold K_loop1. apply SPJ_refacts_J; [exact H | vm_compute; reflexivity |].
  intros tr md HJ HF. constructor; [exact (lines_nz Kc FB rho0 rho tr md HJ HF) | constructor].
Qed.

End LoFront.
