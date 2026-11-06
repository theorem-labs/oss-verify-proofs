(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore CxPlan CxfRt.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfNodes CxfL1 CxfL2 CxfL3 CxfL4 CxfL15 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFNL.
Import CXFN.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import AX2B.
Import AX2BL.
Import APC.
Import APCL.
Import CAP.
Import CAPL.
Definition respell_okB (bc : bctx) (a e : expr) : bool :=
  match decide_branchB bc BC_EQ a e with
  | Some true => true
  | _ => match erangeB bc (mkAlu ALU_SUB a e) with
         | Some (lo, hi) => if Z.eqb lo 0 then Z.eqb hi 0 else false
         | None => false
         end
  end.
Lemma L_CXFNL_respell_okB : @respell_okB = @CXFN.respell_okB.
Proof. unfold respell_okB. rewrite ?AX2BL.L_AX2BL_decide_branchB, ?AX2BL.L_AX2BL_erangeB, ?AX2L.L_AX2L_mkAlu. reflexivity. Qed.

Definition node_respell_f (cs : acs) (r : nat) (e : expr) : option acs :=
  if (if CXNAT.ltbF 0 r then if CXNAT.ltbF r 32 then if expr_vars_lt (nxt cs) e then respell_okB (mkbc (kn cs)) (reg cs r) e else false else false else false)
  then Some (set_reg cs r e) else None.
Lemma L_CXFNL_node_respell_f : @node_respell_f = @CXFN.node_respell_f.
Proof. unfold node_respell_f. rewrite ?L_CXFNL_respell_okB, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_kn, ?AX2BL.L_AX2BL_mkbc, ?APCL.L_APCL_nxt, ?APCL.L_APCL_reg, ?APCL.L_APCL_set_reg, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition node_respell_c (c : CXFRTL.rtc) (cs : acs) (r : nat) (e : expr) : option acs :=
  if (if CXNAT.ltbF 0 r then if CXNAT.ltbF r 32 then if expr_vars_lt (nxt cs) e then respell_okB (fst (CXFRTL.mkbc_c c (kn cs))) (reg cs r) e else false else false else false)
  then Some (set_reg cs r e) else None.
Lemma L_CXFNL_node_respell_c : @node_respell_c = @CXFN.node_respell_c.
Proof. unfold node_respell_c. rewrite ?L_CXFNL_respell_okB, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_kn, ?CXFRTL.L_CXFRTL_mkbc_c, ?APCL.L_APCL_nxt, ?APCL.L_APCL_reg, ?CXFRTL.L_CXFRTL_rtc, ?APCL.L_APCL_set_reg, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Section Munmap.
Variable segs : list Segment.
Definition node_munmap_pF (cs : acs) : option acs :=
  if negb (is_ecall_at segs cs) then None else
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let bc := mkbc k in
      let '(bb, bk) := split_lit b in
      if (if existsb (amap_matchB bc b ne) (a_maps cs) then if page_alignedB bc b then if flat_xB bc bb bk ne
          then match xhiB bc b with Some hi => Z.ltb (hi + nhi) two64 | None => false end else false else false else false) then
        let k1 := kn_unfillB bc bb bk ne in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_matchB bc b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
End Munmap.
Lemma L_CXFNL_node_munmap_pF : @node_munmap_pF = @CXFN.node_munmap_pF.
Proof. unfold node_munmap_pF. rewrite ?APCL.L_APCL_amap_matchB, ?APCL.L_APCL_flat_xB, ?APCL.L_APCL_is_ecall_at, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_unfillB, ?APCL.L_APCL_mk_ss, ?AX2BL.L_AX2BL_mkbc, ?APCL.L_APCL_mmap_len, ?APCL.L_APCL_page_alignedB, ?APCL.L_APCL_pc, ?APCL.L_APCL_reg, ?APCL.L_APCL_reg_lit, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB. reflexivity. Qed.

End CXFNL.
