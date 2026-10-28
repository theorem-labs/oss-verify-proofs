From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_load__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs.

Module LoAddrU.
  Definition loU_entry : Z := 0x13a40.
  Definition loU_ret : Z := 0x13ba0.
  Definition FRU : Z := 1856.
  Definition al_w0U : Z := 0x13928.
  Definition al_w1U : Z := 0x13934.
  Definition al_w3U : Z := 0x13948.
End LoAddrU.
Import LoAddrU.

Definition sp1U : sv := LD.spo (- FRU).

Definition O_FU (cells : list cell) : sobj := mkObj (SVar 10) (SLit (- FRU)) (SLit 0) cells DUnknown.
Definition O_DU : sobj := mkObj sp1U LD.vDp (SLit 0) [] DUnknown.
Definition O_cfgU : sobj :=
  mkObj LD.vCFG (SLit 0) (SLit 144) [mkCell (SLit 48) 4 (SLit 65793); mkCell (SLit 56) 4 (SLit 4294967295)] DZero.

Definition base_factsU : list sprop :=
  [SPAlign 10 4;
   SPUle (SAlu ALU_ADD (SVar 30) (SLit 16384)) (SVar 10);
   SPUle (SVar 10) (SLit (LD.two47 - 368));
   SPBranch BC_GE (SLit (-8192)) LD.vDp;
   SPBranch BC_GE LD.vDp (SLit (- 2 ^ 40));
   SPUle (SVar 30) (SAlu ALU_ADD sp1U LD.vDp);
   SPUle (SVar 30) LD.vOUT;
   SPUle LD.vOUT (SLit LD.two47);
   SPAlign 12 3;
   SPUle (SLit 4096) LD.vB;
   SPUle LD.vB (SLit LD.two47);
   SPUle LD.vL (SLit (2 ^ 26));
   SPUle (SVar 30) LD.vCFG;
   SPUle LD.vCFG (SLit LD.two47);
   SPAlign 15 3;
   SPUle (SLit 140735332483072) (SVar 30);
   SPUle (SVar 30) (SLit 140737479966720);
   SPUle (SLit 140735332483072) (SVar 10)].

Definition Pre_lo_U : sstate :=
  mkSS loU_entry (setregs pre_regs [(13%nat, LD.vCFG); (14%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    [O_FU []; O_DU; LD.O_out [] DUnknown; LD.O_text; O_cfgU] base_factsU LD.NP false.

Definition al_cellsU : list cell :=
  [LD.c8 0 (SLit al_w0U); LD.c8 8 (SLit al_w1U); LD.c8 16 (SLit 0); LD.c8 24 (SLit al_w3U);
   LD.c8 32 (SLit 0); LD.c8 40 (SLit 0)].
Definition O_arU (hd : sv) : sobj :=
  mkObj LD.xAR (SLit 0) (SLit 64) (al_cellsU ++ [LD.c8 48 hd; LD.c8 56 (SLit 65536)]) DUnknown.
Definition out_okU (ar : sv) : list cell :=
  [LD.c8 144 (SLit al_w0U); LD.c8 152 (SLit al_w1U); LD.c8 160 (SLit 0); LD.c8 168 (SLit al_w3U);
   LD.c8 176 (SLit 0); LD.c8 184 (SLit 0); LD.c8 192 ar; LD.c8 200 (SLit 0)].

Definition P_ok_U : sstate :=
  mkSS loU_ret (LD.post_xregs (SLit 0)) LD.post_fregs FcsrFrm0 None
    [O_FU []; O_DU; LD.O_out (out_okU LD.xAR) DUnknown; LD.O_text; O_cfgU; O_arU LD.pH]
    (base_factsU ++ LD.ar_facts ++ LD.hd_facts LD.pH) LD.HNEXT false.

Definition P_err_U : sstate :=
  mkSS loU_ret (LD.post_xregs LD.pRC) LD.post_fregs FcsrFrm0 None
    [O_FU []; O_DU; LD.O_out [] DUnknown; LD.O_text; O_cfgU]
    (SPBranch BC_NE LD.pRC (SLit 0) :: base_factsU) LD.HNEXT false.

Definition PDA_lo_U : list (sstate * (list (sv * sv) * amode)) :=
  [(P_ok_U, ([(LD.xAR, SLit 64)], AHead LD.pH)); (P_err_U, ([], ANone))].

Definition Posts_loF_U (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsCA segsU C_U Kc LD.P0_lo PDA_lo_U FB.

Definition load_obj_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc ->
    triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (LD.P0_lo FB) FB [] ANone) Pre_lo_U rho0)
      (LQP segsU LD.NP rho0 (Posts_loF_U Kc FB)).

Definition load_obj_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc ->
    etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (LD.P0_lo FB) FB [] ANone) Pre_lo_U rho0)
      (LQP segsU LD.NP rho0 (Posts_loF_U Kc FB)).
