From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module HfAddrU.
  Definition hfU_entry : Z := 0x19308.
  Definition hfU_ret : Z := 0x19f04.
  Definition hfU_trap : Z := 0x19f40.
  Definition vrU_entry : Z := 0x167f8.
  Definition pcU_entry : Z := 0x18abc.
  Definition pgU_entry : Z := 0x1dbf0.
End HfAddrU.
Import HfAddrU.

Definition FUEL_U : nat := 3000%nat.

Definition F_cells_U : list cell := F_saved ++ [c8 (-208) (SLit 66708)].

Definition HSX_U (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (cur : sv) (co rp : sv * sv * sv)
    (cod trd : odefault) (extra : list sobj) (facts : list sprop) : sstate :=
  mkSS pc (body_regs HF_U regs) hf_fregs FcsrFrm0 None
    ([O_F HF_U fcells; O_Dw HF_U] ++ builder pERR mi1 fv1 mm1 sg1 co rp tr1 ts1 pHP ++
     [O_al HF_U; O_c cur; O_text;
      O_data av_d 4 av_k; O_data (t_d mi1) 12 (t_k mi1); O_data (t_d fv1) 4 (t_k fv1);
      O_data (t_d mm1) 4 (t_k mm1); O_data (t_d sg1) 4 (t_k sg1); O_dataD (t_d co) 12 (t_k co) cod;
      O_data (t_d rp) 4 (t_k rp); O_dataD (t_d tr1) 4 (t_k tr1) trd; O_data (t_d ts1) 1 (t_k ts1)] ++
     extra ++ [O_ce])
    (facts ++ pat_facts2 co rp ++ hf_base_facts HF_U) HNEXT false.

Definition HS_U (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (cur : sv) (co : sv * sv * sv)
    (extra : list sobj) (facts : list sprop) : sstate :=
  HSX_U pc regs (fcells ++ F_cells_U) cur co rp1 DUnknown DUnknown extra facts.

Definition HSt_U (pc : Z) (regs : list (nat * sv)) (fcells : list cell) (trd : odefault) (facts : list sprop)
    : sstate :=
  HSt HF_U pc regs fcells trd facts.
