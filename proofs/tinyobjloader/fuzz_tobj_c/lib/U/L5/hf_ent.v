From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocLaws Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_cuts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ent_cuts : list edesc :=
  [(Pre_hf HF_U, tv_pre, (100, z0)); (T60z_U, tvH, (90, vT60_U)); (T60n_U, tvH, (90, vT60_U));
   (T50_U, tvH, (90, vT50_U))].

Definition ent_exits : list edesc :=
  [(HP_ret HF_U, tvH, (0, z0)); (HP_degen HF_U, tvH, (0, z0))].

Section Ent.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.

Let JGv (tv : list (sv * sv)) : jpred := JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv.

Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis POST : forall (P : sstate) (tv : list (sv * sv)) (rho : valuation) (b : Z),
  In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) -> TR (SPJ segsU (JGv tv) P rho) (FAM b).

Lemma ent_exits_okT : forall X tvX rvX rho,
  In (X, tvX, rvX) ent_exits -> TR (SPJ segsU (JGv tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using POST.
  intros X tvX rvX rho Hin. cbn [ent_exits In] in Hin.
  destruct Hin as [H|[H|[]]]; injection H as <- <- <-; apply POST; cbn; tauto.
Qed.
End Ent.
