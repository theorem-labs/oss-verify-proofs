(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore CxPlan CxfRt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFN.
Import AX2. Import AX2B. Import APC. Import CAP.

Definition respell_okB (bc : bctx) (a e : expr) : bool :=
  match decide_branchB bc BC_EQ a e with
  | Some true => true
  | _ => match erangeB bc (mkAlu ALU_SUB a e) with
         | Some (lo, hi) => if Z.eqb lo 0 then Z.eqb hi 0 else false
         | None => false
         end
  end.
Lemma respell_okB_eq : forall k a e, respell_okB (mkbc k) a e = respell_ok k a e.
Proof.
  intros. unfold respell_okB, respell_ok. rewrite decide_branchB_eqf, erangeB_eqf.
  destruct (decide_branch k BC_EQ a e) as [[|]|]; try reflexivity;
    destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|]; try reflexivity; destruct (Z.eqb lo 0); reflexivity.
Qed.
Definition node_respell_f (cs : acs) (r : nat) (e : expr) : option acs :=
  if (if Nat.ltb 0 r then if Nat.ltb r 32 then if expr_vars_lt (nxt cs) e then respell_okB (mkbc (kn cs)) (reg cs r) e else false else false else false)
  then Some (set_reg cs r e) else None.
Lemma node_respell_f_eq : forall cs r e, node_respell_f cs r e = node_respell cs r e.
Proof.
  intros. unfold node_respell_f, node_respell. rewrite respell_okB_eq.
  destruct (Nat.ltb 0 r), (Nat.ltb r 32), (expr_vars_lt (nxt cs) e); reflexivity.
Qed.
(* [comment removed for export] *)
Definition node_respell_c (c : CXFRT.rtc) (cs : acs) (r : nat) (e : expr) : option acs :=
  if (if Nat.ltb 0 r then if Nat.ltb r 32 then if expr_vars_lt (nxt cs) e then respell_okB (fst (CXFRT.mkbc_c c (kn cs))) (reg cs r) e else false else false else false)
  then Some (set_reg cs r e) else None.
Lemma node_respell_c_eq : forall c cs r e, CXFRT.rtc_ok c -> node_respell_c c cs r e = node_respell_f cs r e.
Proof. intros c cs r e H. unfold node_respell_c, node_respell_f. rewrite (proj1 (CXFRT.mkbc_c_spec c (kn cs) H)). reflexivity. Qed.


(* [comment removed for export] *)
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
Lemma node_munmap_pF_eq : forall cs, node_munmap_pF cs = CAP.node_munmap_p segs cs.
Proof.
  intros cs. unfold node_munmap_pF, CAP.node_munmap_p. destruct (negb (is_ecall_at segs cs)); [reflexivity|].
  destruct (reg_lit cs 17) as [z|]; [|reflexivity]. destruct (mmap_len cs) as [[[ne nlo] nhi]|]; [|destruct z as [|q|q]; reflexivity].
  cbv zeta. rewrite amap_matchB_eqf, page_alignedB_eqf, flat_xB_eqf, xhiB_eqf, kn_unfillB_eqf.
  destruct (split_lit (reg cs 10)) as [bb bk].
  destruct (existsb (amap_match (kn cs) (reg cs 10) ne) (a_maps cs)), (page_aligned (kn cs) (reg cs 10)), (flat_x (kn cs) bb bk ne); reflexivity.
Qed.
End Munmap.

End CXFN.
