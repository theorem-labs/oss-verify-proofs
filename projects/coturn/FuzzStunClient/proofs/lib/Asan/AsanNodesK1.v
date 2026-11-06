(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import CatExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module K1N.
(* [comment removed for export] *)
Definition CLZ_REGS : list nat := [11; 12; 15; 16]%nat.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : N.
Variable T : RPN.rptab.   (* [comment removed for export] *)
Definition CLZ_ENTRY : Z := RPN.rp_clz T.    (* [comment removed for export] *)
Definition CLZ_EXIT : Z := RPN.rp_clzx T.    (* [comment removed for export] *)

Fixpoint first_false (i : nat) (l : list bool) : nat :=
  match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.

(* [comment removed for export] *)
Definition clz_tests (cs : acs) : option (list bool * Z * Z * Z * expr) :=
  let k := kn cs in
  match reg cs 9, xlo k (reg cs 18), xhi k (reg cs 18) with
  | ELit L, Some lo, Some hi =>
      match kread8e segs k (ELit 0) (L + 48) with
      | Some v =>
          Some ([ Z.eqb (pc cs) CLZ_ENTRY; Z.leb 1 lo; Z.leb lo hi; Z.ltb hi two64
                ; Z.leb 0 L; Z.leb (L + 56) two64; expr_vars_lt (nxt cs) v
                ; fresh_ok nx0 cs ]%bool, L, lo, hi, v)
      | None => None
      end
  | _, _, _ => None
  end.

Definition node_clz (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
    match clz_tests cs with
    | Some (ts, L, lo, hi, v) =>
        if forallb (fun b : bool => b) ts then
          let nx := nxt cs in let sr := s_regs (a_ss cs) in
          let Klo := Z.log2 lo in let Khi := Z.log2 hi in
          if Z.eqb Klo Khi then
            Some (with_ss cs (mk_ss CLZ_EXIT (sr_upd (sr_upd (sr_fresh sr CLZ_REGS nx) 19 (ELit (63 - Klo))) 14 v)
                                    (kn cs) (nx + 4)%N))
          else  (* [comment removed for export] *)
            Some (with_ss cs (mk_ss CLZ_EXIT (sr_upd (sr_fresh sr (CLZ_REGS ++ [19%nat]) nx) 14 v)
                                    (KRange (EVar (nx + 4)%N) (63 - Khi) (63 - Klo) :: kn cs) (nx + 5)%N))
        else None
    | None => None
    end
  | _ => None
  end.

Definition diag_clz (cs : acs) (args : list expr) : nat :=
  match clz_tests cs with Some (ts, _, _, _, _) => first_false 1 ts | None => 100%nat end.

(* [comment removed for export] *)
Definition BSL_ENTRY : Z := RPN.rp_bsl T.    (* [comment removed for export] *)
Definition BSL_EXIT : Z := RPN.rp_bslx T.    (* [comment removed for export] *)
Definition BSL_REGS : list nat := [11; 13]%nat.

Definition bsl_tests (cs : acs) : option (list bool * Z * Z * Z) :=
  let k := kn cs in
  match reg cs 9, xlo k (reg cs 11), xhi k (reg cs 11) with
  | ELit L, Some lo, Some hi =>
      Some ([ Z.eqb (pc cs) BSL_ENTRY; Z.leb 0 lo; Z.leb lo hi; Z.leb hi 63
            ; Z.leb 0 L; Z.leb (L + 624) two64
            ; kwritable k k (ELit 0) (L + 96) 8
            ; kwritable k k (ELit 0) (L + 104 + 8 * lo) (8 * (hi - lo) + 8)
            ; expr_vars_lt (nxt cs) (reg cs 12)
            ; fresh_ok nx0 cs ]%bool, L, lo, hi)
  | _, _, _ => None
  end.

Definition bsl_kn (k : list kentry) (L lo hi : Z) (a2 : expr) : list kentry :=
  KWord (SA (ELit 0) (L + 96)) 8 a2
  :: kn_havoc (kn_havoc k (ELit 0) (L + 104 + 8 * lo) (ELit (8 * (hi - lo) + 8))) (ELit 0) (L + 96) (ELit 8).

Definition node_bysizelog (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
    match bsl_tests cs with
    | Some (ts, L, lo, hi) =>
        if forallb (fun b : bool => b) ts then
          let nx := nxt cs in
          Some (with_ss cs (mk_ss BSL_EXIT (sr_fresh (s_regs (a_ss cs)) BSL_REGS nx)
                                  (bsl_kn (kn cs) L lo hi (reg cs 12)) (nx + 2)%N))
        else None
    | None => None
    end
  | _ => None
  end.

Definition diag_bysizelog (cs : acs) (args : list expr) : nat :=
  match bsl_tests cs with Some (ts, _, _, _) => first_false 1 ts | None => 100%nat end.

(* [comment removed for export] *)
Definition IC_ENTRY : Z := RPN.rp_ic T.     (* [comment removed for export] *)
Definition IC_EXIT : Z := RPN.rp_icx T.     (* [comment removed for export] *)
Definition IC_REGS : list nat := [5; 6; 7; 11; 13; 15; 16; 17; 28; 29; 30]%nat.
End WithSegs.
(* [comment removed for export] *)
Definition ic_cnt : list Z := [16;16;16;16;12;10;8;8;6;6;4;4;4;4;4;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;16].
Definition ic_size : list Z := [32;64;96;128;160;192;224;256;288;320;352;384;416;448;480;512;768;1024;1536;2048;3072;4096;6144;8192;
                                12288;16384;24576;32768;49152;65536;64].
Fixpoint ic_mk (k : Z) (cs ss : list Z) : list (Z * nat * Z) :=
  match cs, ss with
  | c1 :: cr, s1 :: sr => (84 + 80 * k, 4%nat, c1) :: (88 + 80 * k, 8%nat, s1) :: ic_mk (k + 1) cr sr
  | _, _ => []
  end.
(* [comment removed for export] *)
Definition ic_tab : list (Z * nat * Z) := ic_mk 0 ic_cnt ic_size.
Definition IC_END : Z := 2496.    (* [comment removed for export] *)
Definition IC_WLEN : Z := 2412.   (* [comment removed for export] *)
Definition ic_mem (c : Z) (mem : word -> option byte) : word -> option byte :=
  fold_left (fun m (t : Z * nat * Z) => let '(o, w, v) := t in wbytes m (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v))) ic_tab mem.
Definition ic_havoc (k : list kentry) (b : expr) (o : Z) : list kentry :=
  fold_left (fun k' (t : Z * nat * Z) => let '(o', w, _) := t in kn_havoc k' b (o + o') (ELit (Z.of_nat w))) ic_tab k.
Definition ic_facts (b : expr) (o : Z) : list kentry :=
  map (fun (t : Z * nat * Z) => let '(o', w, v) := t in KWord (SA b (o + o')) w (ELit v)) ic_tab.
Definition ic_kn (k : list kentry) (b : expr) (o : Z) : list kentry := ic_facts b o ++ ic_havoc k b o.
Section WithSegs2.
Variable segs : list Segment.
Variable nx0 : N.
Variable T : RPN.rptab.
Definition ic_tests (cs : acs) : option (list bool * expr * Z) :=
  let k := kn cs in
  let '(b, o) := split_lit (reg cs 10) in
  match base_range k b with
  | Some (lo, hi) =>
      Some ([ Z.eqb (pc cs) (IC_ENTRY T); Z.leb 0 (lo + o); Z.ltb (hi + o + IC_END) two64
            ; kwritable k k b (o + 84) IC_WLEN
            ; expr_vars_lt (nxt cs) b
            ; fresh_ok nx0 cs ]%bool, b, o)
  | None => None
  end.
Definition node_initcache (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] =>
    match ic_tests cs with
    | Some (ts, b, o) =>
        if forallb (fun x : bool => x) ts then
          let nx := nxt cs in
          Some (with_ss cs (mk_ss (IC_EXIT T) (sr_fresh (s_regs (a_ss cs)) IC_REGS nx) (ic_kn (kn cs) b o) (nx + 11)%N))
        else None
    | None => None
    end
  | _ => None
  end.
Definition diag_initcache (cs : acs) (args : list expr) : nat :=
  match ic_tests cs with Some (ts, _, _) => first_false 1 ts | None => 100%nat end.

Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 111 then node_clz segs nx0 T cs args
  else if Nat.eqb id 112 then node_bysizelog nx0 T cs args
  else None.   (* [comment removed for export] *)
End WithSegs2.
End K1N.
