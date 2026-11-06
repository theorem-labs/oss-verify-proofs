(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore FContractAsan AsanPGVal AsanNodesFX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module LCN.
(* [comment removed for export] *)
Record lctab : Type := LCT {
  lc_entry : Z;                     (* [comment removed for export] *)
  lc_ret : Z;                       (* [comment removed for export] *)
  lc_a0 : Z;                        (* [comment removed for export] *)
  lc_regs : list (nat * Z);         (* [comment removed for export] *)
  lc_cells : list (Z * nat * Z);    (* [comment removed for export] *)
  lc_vcells : list Z;               (* [comment removed for export] *)
  lc_win : Z;                       (* [comment removed for export] *)
  lc_wr : list (Z * Z);             (* [comment removed for export] *)
  lc_post : list (Z * nat * Z)      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition LC_SPLO : Z := 0x7fff00000000.
Definition LC_SPHI : Z := 0x800000000000 - 16.

Fixpoint first_false (i : nat) (l : list bool) : nat :=
  match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.

Definition post_fact (c : Z * nat * Z) : kentry := let '(a, w, v) := c in KWord (SA (ELit 0) a) w (ELit v).

Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : N.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lc_ws (T : lctab) (spb : expr) (spk : Z) : list (expr * Z * expr) :=
  (spb, spk - lc_win T, ELit (lc_win T)) :: map (fun r : Z * Z => (ELit 0, fst r, ELit (snd r))) (lc_wr T).

(* [comment removed for export] *)
Definition tests (T : lctab) (cs : acs) : list bool :=
  let k := kn cs in
  let sp := reg cs 2 in
  let '(spb, spk) := split_lit sp in
  let '(shb, shk, shn) := shadow_of A k (eaddz sp (- lc_win T)) (ELit (lc_win T)) in
  [ Z.eqb (pc cs) (lc_entry T)
  ; match ret_lit cs with Some r => Z.eqb r (lc_ret T) | None => false end
  ; forallb (fun rv : nat * Z => match reg_lit cs (fst rv) with Some r => Z.eqb r (snd rv) | None => false end) (lc_regs T)
  ; Z.leb 4 (ealign k sp)
  ; match xlo k sp, xhi k sp with Some lo, Some hi => Z.leb (LC_SPLO + lc_win T) lo && Z.leb hi LC_SPHI | _, _ => false end
  ; kwritable k k spb (spk - lc_win T) (lc_win T) && flat_x k spb (spk - lc_win T) (ELit (lc_win T))
  ; kzero_x k k shb shk shn && flat_x k shb shk shn
  ; forallb (fun c : Z * nat * Z => let '(a, w, v) := c in match kreadZ segs k (ELit 0) a w with Some z => Z.eqb z v | None => false end) (lc_cells T)
  ; forallb (fun a : Z => match FN.cell_expr segs k (ELit 0) a with Some _ => true | None => false end) (lc_vcells T)
  ; forallb (fun r : Z * Z => kwritable k k (ELit 0) (fst r) (snd r) && flat_x k (ELit 0) (fst r) (ELit (snd r))) (lc_wr T)
  ]%bool.

Definition node_lc_ref (T : lctab) (cs : acs) : option acs :=
  if forallb (fun b : bool => b) (tests T cs) then
    let '(spb, spk) := split_lit (reg cs 2) in
    after_call nx0 cs (lc_ret T) (Some (ELit (lc_a0 T))) (map post_fact (lc_post T) ++ FN.havocs (kn cs) (lc_ws T spb spk))
  else None.

(* [comment removed for export] *)
Definition testsB (bc : AX2B.bctx) (kx : AX2B.kix) (T : lctab) (cs : acs) : list bool :=
  let k := kn cs in
  let sp := reg cs 2 in
  let '(spb, spk) := split_lit sp in
  let '(shb, shk, shn) := shadow_ofB A bc (eaddz sp (- lc_win T)) (ELit (lc_win T)) in
  [ Z.eqb (pc cs) (lc_entry T)
  ; match ret_lit cs with Some r => Z.eqb r (lc_ret T) | None => false end
  ; forallb (fun rv : nat * Z => match reg_lit cs (fst rv) with Some r => Z.eqb r (snd rv) | None => false end) (lc_regs T)
  ; Z.leb 4 (AX2B.ealignB bc sp)
  ; match AX2B.xloB bc sp, AX2B.xhiB bc sp with Some lo, Some hi => Z.leb (LC_SPLO + lc_win T) lo && Z.leb hi LC_SPHI | _, _ => false end
  ; kwritableB bc k spb (spk - lc_win T) (lc_win T) && flat_xB bc spb (spk - lc_win T) (ELit (lc_win T))
  ; kzero_xB bc k shb shk shn && flat_xB bc shb shk shn
  ; forallb (fun c : Z * nat * Z => let '(a, w, v) := c in match kreadZBX segs bc kx (ELit 0) a w with Some z => Z.eqb z v | None => false end) (lc_cells T)
  ; forallb (fun a : Z => match FN.cell_exprB segs bc kx (ELit 0) a with Some _ => true | None => false end) (lc_vcells T)
  ; forallb (fun r : Z * Z => kwritableB bc k (ELit 0) (fst r) (snd r) && flat_xB bc (ELit 0) (fst r) (ELit (snd r))) (lc_wr T)
  ]%bool.
Lemma testsB_eq : forall T cs, testsB (AX2B.mkbc (kn cs)) (AX2B.mk_kix (kn cs)) T cs = tests T cs.
Proof.
  intros T cs. unfold testsB, tests. cbv zeta.
  rewrite ?shadow_ofB_eqf, ?AX2B.ealignB_eqf, ?AX2B.xloB_eqf, ?AX2B.xhiB_eqf, ?kwritableB_eqf, ?flat_xB_eqf, ?kzero_xB_eqf, ?kreadZBX_eqf, ?FN.cell_exprB_eqf.
  reflexivity.
Qed.

Definition node_lc (T : lctab) (cs : acs) : option acs :=
  let bc := AX2B.mkbc (kn cs) in let kx := AX2B.mk_kix (kn cs) in
  if forallb (fun b : bool => b) (testsB bc kx T cs) then
    let '(spb, spk) := split_lit (reg cs 2) in
    after_call nx0 cs (lc_ret T) (Some (ELit (lc_a0 T))) (map post_fact (lc_post T) ++ FN.havocs (kn cs) (lc_ws T spb spk))
  else None.
Lemma node_lc_eq : forall T cs, node_lc T cs = node_lc_ref T cs.
Proof. intros T cs. unfold node_lc, node_lc_ref. cbv zeta. rewrite testsB_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition diag (T : lctab) (cs : acs) : nat :=
  match first_false 1 (tests T cs) with
  | O => match node_lc T cs with Some _ => 0%nat | None => 200%nat end
  | n => n
  end.

(* [comment removed for export] *)
Definition xn (TS : list lctab) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 122 then
    match args with
    | [ELit i] => match nth_error TS (Z.to_nat i) with Some T => node_lc T cs | None => None end
    | _ => None
    end
  else None.
End WithSegs.
End LCN.
