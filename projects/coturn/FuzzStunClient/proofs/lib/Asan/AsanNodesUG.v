(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module UGN.
(* [comment removed for export] *)
Record ugtab : Type := UGT {
  ug_ret : Z;                      (* [comment removed for export] *)
  ug_exit : Z;                     (* [comment removed for export] *)
  ug_tab : Z;                      (* [comment removed for export] *)
  ug_shoff : Z;                    (* [comment removed for export] *)
  ug_regs : list (nat * Z);        (* [comment removed for export] *)
  ug_cells : list (Z * nat * Z);   (* [comment removed for export] *)
  ug_glob : list (Z * Z * Z)       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition fill_of (sh : Z) (g : Z * Z * Z) : Z * Z :=
  let '(beg, swr, _) := g in (sh + beg / 8, (beg + swr - 8) / 8 + 1 - beg / 8).
Definition ug_fills (T : ugtab) : list (Z * Z) := map (fill_of (ug_shoff T)) (ug_glob T).
Definition ug_n (T : ugtab) : Z := Z.of_nat (length (ug_glob T)).
(* [comment removed for export] *)
Definition ug_hlo (T : ugtab) : Z := fold_right (fun f m => Z.min (fst f) m) (2 ^ 64) (ug_fills T).
Definition ug_hhi (T : ugtab) : Z := fold_right (fun f m => Z.max (fst f + snd f) m) 0 (ug_fills T).
Definition ug_hlen (T : ugtab) : Z := ug_hhi T - ug_hlo T.
(* [comment removed for export] *)
Fixpoint glob_reads (g : Z) (gl : list (Z * Z * Z)) : list (Z * nat * Z) :=
  match gl with
  | [] => []
  | (beg, swr, odr) :: r => (g, 8%nat, beg) :: (g + 16, 8%nat, swr) :: (g + 16, 1%nat, swr mod 256) :: (g + 56, 8%nat, odr) :: glob_reads (g + 64) r
  end.
Definition ug_reads (T : ugtab) : list (Z * nat * Z) := ug_cells T ++ glob_reads (ug_tab T) (ug_glob T).
(* [comment removed for export] *)
Definition ug_s0x (T : ugtab) : Z := match rev (ug_fills T) with f :: _ => fst f + snd f | [] => 0 end.
(* [comment removed for export] *)
Definition UG_REGS : list nat := [10; 11; 12; 13; 14; 15; 16]%nat.

(* [comment removed for export] *)
Definition UG_ASAN : ugtab := UGT 0x41d44 0x41f60 0xaf760 0x7fff8000
  [(9%nat, 0x145128); (18%nat, 0x2); (23%nat, 0xaccf0); (25%nat, 0xb0df8); (26%nat, 0xb35f8)]
  [(0xaccf0, 8%nat, 0xa45b0); (0xb0e10, 4%nat, 0x1); (0xb2e5c, 1%nat, 0x1); (0xb35f8, 8%nat, 0x7fff8000); (0xb42d8, 1%nat, 0x1); (0x1451a0, 8%nat, 2 ^ 64 - 1)]
  [(0x21b80, 32, 2 ^ 64 - 1);
   (0x21ba0, 96, 2 ^ 64 - 1);
   (0x21c00, 64, 2 ^ 64 - 1);
   (0x21c40, 32, 2 ^ 64 - 1);
   (0x21c60, 32, 2 ^ 64 - 1);
   (0x21c80, 32, 2 ^ 64 - 1);
   (0x21ca0, 32, 2 ^ 64 - 1);
   (0x21ec0, 32, 2 ^ 64 - 1);
   (0x21ee0, 32, 2 ^ 64 - 1);
   (0x21f00, 32, 2 ^ 64 - 1);
   (0x21f20, 32, 2 ^ 64 - 1);
   (0x21f40, 32, 2 ^ 64 - 1);
   (0x21f60, 32, 2 ^ 64 - 1);
   (0x21f80, 64, 2 ^ 64 - 1);
   (0x21fc0, 64, 2 ^ 64 - 1);
   (0x22000, 32, 2 ^ 64 - 1);
   (0x22020, 64, 2 ^ 64 - 1);
   (0x22060, 64, 2 ^ 64 - 1);
   (0x220a0, 64, 2 ^ 64 - 1);
   (0x220e0, 64, 2 ^ 64 - 1);
   (0x22120, 64, 2 ^ 64 - 1);
   (0x22160, 64, 2 ^ 64 - 1);
   (0x221a0, 64, 2 ^ 64 - 1);
   (0x221e0, 32, 2 ^ 64 - 1);
   (0x22200, 32, 2 ^ 64 - 1);
   (0x22220, 64, 2 ^ 64 - 1);
   (0x22260, 32, 2 ^ 64 - 1);
   (0xaf420, 32, 2 ^ 64 - 1);
   (0x5e5c80, 32, 2 ^ 64 - 1);
   (0x5e5ca0, 32, 2 ^ 64 - 1);
   (0x5e5cc0, 32, 2 ^ 64 - 1)].

(* [comment removed for export] *)
Definition UG_BOTH : ugtab := UGT 0x41d34 0x41f50 0xadda0 0x7fff8000
  [(9%nat, 0x1436e8); (18%nat, 0x2); (23%nat, 0xab330); (25%nat, 0xaf3b8); (26%nat, 0xb1bb8)]
  [(0xab330, 8%nat, 0xa2bec); (0xaf3d0, 4%nat, 0x1); (0xb141c, 1%nat, 0x1); (0xb1bb8, 8%nat, 0x7fff8000); (0xb2898, 1%nat, 0x1); (0x143760, 8%nat, 2 ^ 64 - 1)]
  [(0x21bc0, 32, 2 ^ 64 - 1);
   (0x21be0, 96, 2 ^ 64 - 1);
   (0x21c40, 64, 2 ^ 64 - 1);
   (0x21c80, 32, 2 ^ 64 - 1);
   (0x21ca0, 32, 2 ^ 64 - 1);
   (0x21f00, 32, 2 ^ 64 - 1);
   (0x21f20, 32, 2 ^ 64 - 1);
   (0x21f40, 32, 2 ^ 64 - 1);
   (0x21f60, 32, 2 ^ 64 - 1);
   (0x21f80, 32, 2 ^ 64 - 1);
   (0x21fa0, 32, 2 ^ 64 - 1);
   (0x21fc0, 64, 2 ^ 64 - 1);
   (0x22000, 64, 2 ^ 64 - 1);
   (0x22040, 32, 2 ^ 64 - 1);
   (0x22060, 64, 2 ^ 64 - 1);
   (0x220a0, 64, 2 ^ 64 - 1);
   (0x220e0, 64, 2 ^ 64 - 1);
   (0x22120, 64, 2 ^ 64 - 1);
   (0x22160, 64, 2 ^ 64 - 1);
   (0x221a0, 64, 2 ^ 64 - 1);
   (0x221e0, 64, 2 ^ 64 - 1);
   (0x22220, 32, 2 ^ 64 - 1);
   (0x22240, 32, 2 ^ 64 - 1);
   (0x22260, 64, 2 ^ 64 - 1);
   (0x222a0, 32, 2 ^ 64 - 1);
   (0xada60, 32, 2 ^ 64 - 1);
   (0x5e4240, 32, 2 ^ 64 - 1);
   (0x5e4260, 32, 2 ^ 64 - 1);
   (0x5e4280, 32, 2 ^ 64 - 1)].

Fixpoint first_false (i : nat) (l : list bool) : nat :=
  match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.

Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable T : ugtab.

Definition ug_tests (cs : acs) : list bool :=
  let k := kn cs in
  let f0 := match ug_fills T with f :: _ => f | [] => (0, 0) end in
  [ Z.eqb (pc cs) (x_memset A)
  ; match reg_lit cs 1 with Some r => Z.eqb r (ug_ret T) | None => false end
  ; match reg_lit cs 20 with Some r => Z.eqb r (ug_tab T) | None => false end
  ; match reg_lit cs 27 with Some r => Z.eqb r (ug_n T) | None => false end
  ; match reg_lit cs 10 with Some r => Z.eqb r (fst f0) | None => false end
  ; match reg_lit cs 11 with Some r => Z.eqb r 0 | None => false end
  ; match reg_lit cs 12 with Some r => Z.eqb r (snd f0) | None => false end
  ; match reg_lit cs 8 with Some r => Z.eqb r (fst f0 + snd f0) | None => false end      (* [comment removed for export] *)
  ; forallb (fun rv : nat * Z => match reg_lit cs (fst rv) with Some r => Z.eqb r (snd rv) | None => false end) (ug_regs T)
  ; forallb (fun c : Z * nat * Z => let '(a, w, v) := c in match kreadZ segs k (ELit 0) a w with Some z => Z.eqb z v | None => false end) (ug_reads T)
  ; Z.leb 1 (ug_n T)
  ; Z.leb 0 (ug_hlo T); Z.ltb (ug_hlo T) (ug_hhi T); Z.ltb (ug_hhi T) two64
  ; kwritable k k (ELit 0) (ug_hlo T) (ug_hlen T)
  ; fresh_ok nx0 cs ]%bool.

Definition node_unreg (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
      if forallb (fun b : bool => b) (ug_tests cs) then
        let nx := nxt cs in
        let sr0 := sr_upd (sr_upd (sr_upd (s_regs (a_ss cs)) 8 (ELit (ug_s0x T))) 20 (ELit (ug_tab T + 64 * ug_n T))) 27 (ELit 0) in
        Some (with_ss cs (mk_ss (ug_exit T) (sr_fresh sr0 UG_REGS nx) (kn_havoc (kn cs) (ELit 0) (ug_hlo T) (ELit (ug_hlen T))) (nx + 7)%N))
      else None
  | _ => None
  end.
Definition diag_unreg (cs : acs) : nat := first_false 1 (ug_tests cs).

(* [comment removed for export] *)
Definition ug_testsB (bc : AX2B.bctx) (kx : AX2B.kix) (cs : acs) : list bool :=
  let k := kn cs in
  let f0 := match ug_fills T with f :: _ => f | [] => (0, 0) end in
  [ Z.eqb (pc cs) (x_memset A)
  ; match reg_lit cs 1 with Some r => Z.eqb r (ug_ret T) | None => false end
  ; match reg_lit cs 20 with Some r => Z.eqb r (ug_tab T) | None => false end
  ; match reg_lit cs 27 with Some r => Z.eqb r (ug_n T) | None => false end
  ; match reg_lit cs 10 with Some r => Z.eqb r (fst f0) | None => false end
  ; match reg_lit cs 11 with Some r => Z.eqb r 0 | None => false end
  ; match reg_lit cs 12 with Some r => Z.eqb r (snd f0) | None => false end
  ; match reg_lit cs 8 with Some r => Z.eqb r (fst f0 + snd f0) | None => false end
  ; forallb (fun rv : nat * Z => match reg_lit cs (fst rv) with Some r => Z.eqb r (snd rv) | None => false end) (ug_regs T)
  ; forallb (fun c : Z * nat * Z => let '(a, w, v) := c in match kreadZBX segs bc kx (ELit 0) a w with Some z => Z.eqb z v | None => false end) (ug_reads T)
  ; Z.leb 1 (ug_n T)
  ; Z.leb 0 (ug_hlo T); Z.ltb (ug_hlo T) (ug_hhi T); Z.ltb (ug_hhi T) two64
  ; kwritable k k (ELit 0) (ug_hlo T) (ug_hlen T)
  ; fresh_ok nx0 cs ]%bool.
Lemma ug_testsB_eq : forall cs, ug_testsB (AX2B.mkbc (kn cs)) (AX2B.mk_kix (kn cs)) cs = ug_tests cs.
Proof. intros cs. unfold ug_testsB, ug_tests. rewrite kreadZBX_eqf. reflexivity. Qed.

Definition node_unregB (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
      let bc := AX2B.mkbc (kn cs) in let kx := AX2B.mk_kix (kn cs) in
      if forallb (fun b : bool => b) (ug_testsB bc kx cs) then
        let nx := nxt cs in
        let sr0 := sr_upd (sr_upd (sr_upd (s_regs (a_ss cs)) 8 (ELit (ug_s0x T))) 20 (ELit (ug_tab T + 64 * ug_n T))) 27 (ELit 0) in
        Some (with_ss cs (mk_ss (ug_exit T) (sr_fresh sr0 UG_REGS nx) (kn_havocB bc (ELit 0) (ug_hlo T) (ELit (ug_hlen T))) (nx + 7)%N))
      else None
  | _ => None
  end.
Lemma node_unregB_eq : forall cs args, node_unregB cs args = node_unreg cs args.
Proof.
  intros cs args. unfold node_unregB, node_unreg. destruct args; [|reflexivity]. cbv zeta.
  rewrite ug_testsB_eq. unfold kn_havoc. reflexivity.
Qed.

Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 121 then node_unregB cs args else None.
End WithSegs.
End UGN.
