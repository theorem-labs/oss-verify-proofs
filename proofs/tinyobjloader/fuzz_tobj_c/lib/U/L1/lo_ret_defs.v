From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo4_meas.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* Cut nodes of lo's loop body that the return side adds to t-L1's loop certificate (U/L1/lo_nodes.v): the dispatch join
   after the first slice_eq, the two text loops of the usemtl path, and the latch. Each node is in LoU's canonical loop
   form; its measure follows LoMeas (VLp index below every node it reaches, above every node reaching it). *)
Module LoRet.
  Import LoSite.

  (* 0x140f4: token dispatch, reached from the front (0x13fd4) and from slice_eq #1's returns *)
  Definition N_disp : sstate :=
    LoU.LS 0x140f4 ([(6%nat, LD.hx 6); rI] ++ tok_regs) (Some LD.pLINE) (LoU.cpC LD.pCP) (LoU.ceC LD.pE) []
      (tfacts ++ tok_facts ++ cfacts ++ ifacts).
  Definition k_disp : Z := 24.

  (* 0x146b8: skip blanks after "usemtl"; s6 = scan position pQ, s7 = line end *)
  Definition N_ws : sstate :=
    LoU.LS 0x146b8 (clob ++ [rI; (22%nat, LD.txt LD.pQ); (23%nat, eR)]) (Some LD.pLINE) [] [] []
      ([SPUle LD.pPOS LD.pQ; SPUlt LD.pQ LD.pE] ++ ifacts).
  Definition k_ws : Z := 8.
  Definition v_ws : sv := SAlu ALU_SUB LD.pE LD.pQ.

  (* 0x14934: trim trailing blanks of the material name; s6 = name start pQ, s7 = current end pR, a2 = 1 (the loop's
     null-pointer bound for s7 - 1) *)
  Definition N_trim : sstate :=
    LoU.LS 0x14934 (clob ++ [rI; (12%nat, SLit 1); (22%nat, LD.txt LD.pQ); (23%nat, LD.txt LD.pR)]) (Some LD.pLINE) [] [] []
      ([SPUle LD.pPOS LD.pQ; SPUlt LD.pQ LD.pR; SPUle LD.pR LD.pE] ++ ifacts).
  Definition k_trim : Z := 7.
  Definition v_trim : sv := SAlu ALU_SUB LD.pR LD.pQ.

  (* 0x14a0c: latch; s1 = pI + 1 goes back to K_loop (K_loop1 needs 4096 <= xLD as well) *)
  Definition N_latch : sstate :=
    LoU.LS 0x14a0c [rI] (Some LD.pLINE) [] [] [] [SPUle (SLit 4096) LD.xLD; SPUlt LD.pI LD.xLC].
  Definition k_latch : Z := 0.

  Definition ret_nodes : list aedesc :=
    [(N_disp, (LoU.tvL, LoU.amL), (LoMeas.rT, LD.VLp k_disp LD.z0));
     (N_ws, (LoU.tvL, LoU.amL), (LoMeas.rT, LD.VLp k_ws v_ws));
     (N_trim, (LoU.tvL, LoU.amL), (LoMeas.rT, LD.VLp k_trim v_trim));
     (N_latch, (LoU.tvL, LoU.amL), (LoMeas.rT, LD.VLp k_latch LD.z0))].
End LoRet.
