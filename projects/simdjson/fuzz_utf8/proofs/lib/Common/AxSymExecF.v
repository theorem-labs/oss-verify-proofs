(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module AX2F.
Import AX2.

Section WithSegs.
Variable segs : list Segment.

Definition rm_okb (rm : bv 3) : bool := (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool.

Definition fmt_bytes (fmt : ffmt) : nat := match fmt with FMT_D => 8%nat | FMT_S => 4%nat end.

Definition is_fp_instr (i : instr) : bool :=
  match i with
  | FLoad _ _ _ _ | FStore _ _ _ _ | Fmv _ _ _ _ | Fsgnj _ _ _ _ _ | Fari _ _ _ _ _ _ | Fcvt _ _ _ _ _
  | Fcmp _ _ _ _ _ | Fclass _ _ _ | Fsqrt _ _ _ _ | Fma _ _ _ _ _ _ _ | Fminmax _ _ _ _ _
  | Csr _ _ _ _ | CsrI _ _ _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Definition sfresh (ss : sym_state) (rd : reg) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (EVar (s_next ss)))
      (s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss).

Definition fcvt_is_fp (t : fcvt_ty) : bool := match t with FC_S | FC_D => true | _ => false end.

(* [comment removed for export] *)
Fixpoint img_bytes_all (lo : Z) (cnt : nat) (n : nat) : bool :=
  match cnt with
  | O => true
  | S c => match img_bytes segs lo n with Some _ => img_bytes_all (lo + 1) c n | None => false end
  end.
Definition fload_img_ok (kn : list kentry) (e : expr) (n : nat) : bool :=
  match erange kn e with
  | Some (lo, hi) =>
      (* [comment removed for export] *)
      if (Z.leb 0 lo && Z.leb lo hi && Z.leb (hi - lo) 4096 && Z.leb (hi + Z.of_nat n) two64)%bool then
        if existsb (fun K => match K with KImg il ih => Z.leb il lo && Z.leb (hi + Z.of_nat n) ih | _ => false end) kn
        then img_bytes_all lo (Z.to_nat (hi - lo + 1)) n else false
      else false
  | None => false
  end.

Definition sym_stepF (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  if negb (is_fp_instr i) then sym_step segs i ss scr else
  if negb (s_clean ss) then SStop else
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let fk := facts_of (s_know ss) in
  match i with
  | FLoad fmt rd rs imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      (* [comment removed for export] *)
      if (match s_log ss with [] => true | _ => false end
          && fload_img_ok (s_know ss) (mkAlu ALU_ADD (g rs) (ELit (bv_signed imm))) n)%bool
      then SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) (s_next ss) (s_resv ss)) [] scr
      else
      match sym_read segs ss fk scr a n false with
      | None => SStop
      | Some (_, scs, scr', nx') => SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | FStore fmt rs1 rs2 imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      SOk (SSR (p + 4) (s_regs ss) (SE a n (EVar (s_next ss)) :: s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss))
          (flat_sc fk a n ++ storeok_sc fk a n) scr
  | Fmv FMV_X_F _ rd _ => SOk (sfresh ss rd (p + 4)) [] scr
  | Fmv FMV_F_X _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fsgnj _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fari _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fcvt dst src rd _ rm =>
      if negb (rm_okb rm) then SStop else
      if fcvt_is_fp dst then SOk (sjump ss (p + 4)) [] scr            (* [comment removed for export] *)
      else if fcvt_is_fp src then SOk (sfresh ss rd (p + 4)) [] scr     (* [comment removed for export] *)
      else SStop                                                       (* [comment removed for export] *)
  | Fcmp _ _ rd _ _ => SOk (sfresh ss rd (p + 4)) [] scr
  | Fclass _ rd _ => SOk (sfresh ss rd (p + 4)) [] scr
  | Csr CSR_RS rd rs1 csr =>      (* [comment removed for export] *)
      if (bv_eqb rs1 0 && Z.eqb (bv_unsigned csr) 2)%bool then SOk (sset ss rd (ELit 0) (p + 4)) [] scr else SStop
  | CsrI CSR_RS rd uimm csr =>    (* [comment removed for export] *)
      if (bv_eqb rd 0 && Z.eqb (bv_unsigned csr) 1)%bool then SOk (sjump ss (p + 4)) [] scr else SStop
  | _ => SStop
  end.

Definition sym_stepXF (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepF i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filter segs ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.

Fixpoint sym_execTXF_go (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXF K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXF_go t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.

Definition sym_execTXF (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXF_go t K fuel first stops (clr ss) (clr ss).

(* [comment removed for export] *)
Lemma sym_stepF_notfp : forall i ss scr, is_fp_instr i = false -> sym_stepF i ss scr = sym_step segs i ss scr.
Proof. intros i ss scr H. unfold sym_stepF. rewrite H. reflexivity. Qed.

Lemma sym_stepXF_notfp : forall K i ss scr, is_fp_instr i = false -> sym_stepXF K i ss scr = sym_stepX segs K i ss scr.
Proof. intros K i ss scr H. unfold sym_stepXF, sym_stepX. rewrite (sym_stepF_notfp _ _ _ H). reflexivity. Qed.

Lemma rd_of_fp : forall i, is_fp_instr i = true -> rd_of i = None.
Proof. intros i H. destruct i; try reflexivity; discriminate. Qed.

Lemma cap_rd_fp : forall K i ss, is_fp_instr i = true -> cap_rd K i ss = ss.
Proof. intros K i ss H. unfold cap_rd. destruct K; [reflexivity|]. rewrite (rd_of_fp i H). reflexivity. Qed.

End WithSegs.
End AX2F.
