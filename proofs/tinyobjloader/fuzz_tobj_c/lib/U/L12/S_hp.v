From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocLaws Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LP := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_lp_defs.

Definition HP_U : hf_consts :=
  HFC 0x1a298 0x1a510 112 0x167f8 0x18abc 0x1dbbc 0x1dbf0 0 0 0x1bf5c 0x1c0c8
      0x13928 0x13934 0x13948
      0x16874 0x18c64 0x18c64 0x1dcc8.

Definition Pre_hp_U : sstate :=
  mkSS (hf_entry HP_U) pre_regs pre_fregs FcsrFrm0 None
    ([O_F HP_U []; O_Dw HP_U] ++ LP.builderP xERR LP.pi0 xHASPRIM ++
     [O_al HP_U; O_c xP0; O_text; LP.dd LP.pi0 12; O_ce])
    (vec_facts LP.pi_d LP.pi_c LP.pi_k 12 152 ++ LP.lp_base_facts HP_U)
    NP false.

Definition FP_saved_U : list cell :=
  [c8 (-8) (SVar 11); c8 (-16) (SVar 28); c8 (-24) (SVar 29); c8 (-32) (SVar 38); c8 (-40) (SVar 39);
   c8 (-48) (SVar 40); c8 (-56) (SVar 41); c8 (-64) (SVar 42); c8 (-72) (SVar 43); c8 (-80) (SVar 44);
   c8 (-88) (SVar 45); c8 (-96) (SVar 46)].

Definition HPP_ret_U : sstate :=
  mkSS (hf_ret HP_U) (setregs hf_xregs (LP.post_regsP (SVar 410))) hf_fregs FcsrFrm0 None
    ([O_F HP_U FP_saved_U; O_Dw HP_U] ++ LP.builderP pERR LP.pi1 pHP ++
     [O_al HP_U; O_c pP; O_text; LP.dd LP.pi1 12; O_ce])
    ([SPUle xP0 pP; SPUle pP xE0; SPUle pHP (SLit 1)] ++ pvec_facts LP.pi1 12 ++ LP.lp_base_facts HP_U)
    HNEXT false.

Definition PD_hp_U : list pdesc := [(HPP_ret_U, LP.tvP)].

Definition Posts_hp_U (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc P0_hf PD_hp_U FB.

Definition handle_p_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB LP.tvP_pre) Pre_hp_U rho0)
      (LQP segsU NP rho0 (Posts_hp_U Kc FB)).

Definition handle_p_sum_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB LP.tvP_pre) Pre_hp_U rho0)
      (LQP segsU NP rho0 (Posts_hp_U Kc FB)).
