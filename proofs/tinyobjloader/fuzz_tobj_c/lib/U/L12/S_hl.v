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

Definition HL_U : hf_consts :=
  HFC 0x19f68 0x1a290 128 0x167f8 0x18abc 0x1dbbc 0x1dbf0 0 0 0x1bf5c 0x1c0c8
      0x13928 0x13934 0x13948
      0x16874 0x18c64 0x18c64 0x1dcc8.

Definition Pre_hl_U : sstate :=
  mkSS (hf_entry HL_U) pre_regs pre_fregs FcsrFrm0 None
    ([O_F HL_U []; O_Dw HL_U] ++ LP.builderL xERR LP.li0 LP.lc0 xHASPRIM ++
     [O_al HL_U; O_c xP0; O_text; LP.dd LP.li0 12; LP.dd LP.lc0 4; O_ce])
    (vec_facts LP.li_d LP.li_c LP.li_k 12 146 ++ vec_facts LP.lc_d LP.lc_c LP.lc_k 4 149 ++ LP.lp_base_facts HL_U)
    NP false.

Definition FL_saved_U : list cell :=
  [c8 (-8) (SVar 11); c8 (-16) (SVar 28); c8 (-24) (SVar 29); c8 (-32) (SVar 38); c8 (-40) (SVar 39);
   c8 (-48) (SVar 40); c8 (-56) (SVar 41); c8 (-64) (SVar 42); c8 (-72) (SVar 43); c8 (-80) (SVar 44);
   c8 (-88) (SVar 45); c8 (-96) (SVar 46); c8 (-104) (SVar 47)].

Definition HLP_ret_U : sstate :=
  mkSS (hf_ret HL_U) (setregs hf_xregs (LP.post_regsL (SVar 410))) hf_fregs FcsrFrm0 None
    ([O_F HL_U FL_saved_U; O_Dw HL_U] ++ LP.builderL pERR LP.li1 LP.lc1 pHP ++
     [O_al HL_U; O_c pP; O_text; LP.dd LP.li1 12; LP.dd LP.lc1 4; O_ce])
    ([SPUle xP0 pP; SPUle pP xE0; SPUle pHP (SLit 1); SPUle LP.li_c (t_c LP.li1)] ++
     pvec_facts LP.li1 12 ++ pvec_facts LP.lc1 4 ++ LP.lp_base_facts HL_U)
    HNEXT false.

Definition PD_hl_U : list pdesc := [(HLP_ret_U, LP.tvL)].

Definition Posts_hl_U (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc P0_hf PD_hl_U FB.

Definition handle_l_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB LP.tvL_pre) Pre_hl_U rho0)
      (LQP segsU NP rho0 (Posts_hl_U Kc FB)).

Definition handle_l_sum_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB LP.tvL_pre) Pre_hl_U rho0)
      (LQP segsU NP rho0 (Posts_hl_U Kc FB)).
