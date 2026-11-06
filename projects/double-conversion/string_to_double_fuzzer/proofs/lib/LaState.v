(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require BvKH.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL.
Open Scope Z_scope.

Module LAS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition two64z : Z := 18446744073709551616.
Definition two63z : Z := 9223372036854775808.
Definition snorm (k : Z) : Z :=
  if (Z.leb (- two63z) k &&& Z.ltb k two63z)%bool then k
  else let m := k mod two64z in if Z.leb two63z m then m - two64z else m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive cmpk := CK_LTU | CK_LT | CK_EQ.   (* [comment removed for export] *)

Inductive aval :=
| Top
| LV (l : lin)                                (* [comment removed for export] *)
| CV (neg : bool) (k : cmpk) (a b : lin)       (* [comment removed for export] *)
| XV (a b : lin).                              (* [comment removed for export] *)

Definition alit (z : Z) : aval := LV (lconst (snorm z)).
Definition aval_lit (v : aval) : option Z := match v with LV l => is_const l | _ => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record cell := Cell { c_off : Z; c_w : Z; c_val : aval }.   (* [comment removed for export] *)

Definition overlaps (o1 w1 o2 w2 : Z) : bool := (Z.ltb o1 (o2 + w2) &&& Z.ltb o2 (o1 + w1))%bool.

Fixpoint cells_kill (cs : list cell) (off w : Z) : list cell :=
  match cs with
  | [] => []
  | c :: r => if overlaps (c_off c) (c_w c) off w then cells_kill r off w else c :: cells_kill r off w
  end.
Definition cells_store (cs : list cell) (off w : Z) (v : aval) : list cell :=
  Cell off w v :: cells_kill cs off w.
Fixpoint cells_find (cs : list cell) (off w : Z) : option aval :=
  match cs with
  | [] => None
  | c :: r => if (Z.eqb (c_off c) off &&& Z.eqb (c_w c) w)%bool then Some (c_val c) else cells_find r off w
  end.
(* [comment removed for export] *)
Fixpoint cells_find_lit_cover (cs : list cell) (off w : Z) : option (Z * Z * Z) :=
  match cs with
  | [] => None
  | c :: r =>
      if (Z.leb (c_off c) off &&& Z.leb (off + w) (c_off c + c_w c))%bool
      then match aval_lit (c_val c) with Some z => Some (c_off c, c_w c, z) | None => None end
      else cells_find_lit_cover r off w
  end.
Definition cells_any_overlap (cs : list cell) (off w : Z) : bool :=
  existsb (fun c => overlaps (c_off c) (c_w c) off w) cs.
(* [comment removed for export] *)
Definition cells_drop_below (cs : list cell) (b : Z) : list cell :=
  filter (fun c => negb (Z.leb (c_off c + c_w c) b)) cs.

(* [comment removed for export] *)
Definition zbytes (z : Z) (i n : Z) : Z := (z mod two64z) / 2 ^ (8 * i) mod 2 ^ (8 * n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record afact := AFact { af_len : lin; af_blo : Z; af_bhi : Z; af_first : itv }.
(* [comment removed for export] *)
Record arr := Arr { ar_lo : Z; ar_hi : Z; ar_fact : option afact }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SYM_SP0 : sym := 0%nat.
Definition SYM_DATA : sym := 1%nat.
Definition SYM_N : sym := 2%nat.
Definition SYM_RA : sym := 3%nat.
Definition SYM_S32 : sym := 18%nat.
Definition SYM_D16 : sym := 19%nat.
Definition SYM_R32 : sym := 20%nat.
Definition SYM_SC0 : sym := 21%nat.
Definition NGLOB : nat := 22%nat.
(* [comment removed for export] *)
Definition SHB : Z := 0x7fff8000.

(* [comment removed for export] *)
Record frame := Frame { f_sym : sym; f_cls : Z; f_cells : list cell; f_arrs : list arr; f_sh : list Z; f_flag : sym }.
Definition f_size (f : frame) : Z := 2 ^ (6 + f_cls f).
Definition f_shn (f : frame) : Z := 2 ^ (3 + f_cls f).

Record astate := AS {
  s_pc    : Z;
  s_regs  : list aval;          (* [comment removed for export] *)
  s_ctx   : ctx;
  s_next  : sym;                (* [comment removed for export] *)
  s_stk   : list cell;          (* [comment removed for export] *)
  s_arrs  : list arr;
  s_abs   : list (Z * Z);       (* [comment removed for export] *)
  s_pcache: list (lin * Z * sym);  (* [comment removed for export] *)
  s_resv  : option Z;           (* [comment removed for export] *)
  s_depth : nat;                (* [comment removed for export] *)
  s_pay   : list (lin * itv);   (* [comment removed for export] *)
  s_frames: list frame          (* [comment removed for export] *)
}.

Definition set_pc (st : astate) (pc : Z) : astate :=
  AS pc (s_regs st) (s_ctx st) (s_next st) (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_regs (st : astate) (rs : list aval) : astate :=
  AS (s_pc st) rs (s_ctx st) (s_next st) (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_ctx (st : astate) (C : ctx) : astate :=
  AS (s_pc st) (s_regs st) C (s_next st) (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_next (st : astate) (n : sym) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) n (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_stk (st : astate) (cs : list cell) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) cs (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_arrs (st : astate) (a : list arr) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) (s_stk st) a (s_abs st) (s_pcache st) (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_abs (st : astate) (cs : list (Z * Z)) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) (s_stk st) (s_arrs st) cs (s_pcache st) (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_pcache (st : astate) (pcache : list (lin * Z * sym)) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) (s_stk st) (s_arrs st) (s_abs st) pcache (s_resv st) (s_depth st) (s_pay st) (s_frames st).
Definition set_resv (st : astate) (r : option Z) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) r (s_depth st) (s_pay st) (s_frames st).
Definition set_depth (st : astate) (d : nat) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) d (s_pay st) (s_frames st).
Definition set_pay (st : astate) (p : list (lin * itv)) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) (s_depth st) p (s_frames st).
Definition set_frames (st : astate) (fr : list frame) : astate :=
  AS (s_pc st) (s_regs st) (s_ctx st) (s_next st) (s_stk st) (s_arrs st) (s_abs st) (s_pcache st) (s_resv st) (s_depth st) (s_pay st) fr.

(* [comment removed for export] *)
Fixpoint list_get {A} (l : list A) (n : nat) (d : A) : A :=
  match l, n with [], _ => d | x :: _, O => x | _ :: r, S n' => list_get r n' d end.
Fixpoint list_set {A} (l : list A) (n : nat) (v : A) : list A :=
  match l, n with [], _ => [] | _ :: r, O => v :: r | x :: r, S n' => x :: list_set r n' v end.
Definition getreg (st : astate) (r : nat) : aval :=
  if Nat.eqb r 0 then LV (lconst 0) else list_get (s_regs st) r Top.
Definition setreg (st : astate) (r : nat) (v : aval) : astate :=
  if Nat.eqb r 0 then st else set_regs st (list_set (s_regs st) r v).

(* [comment removed for export] *)
Definition fresh (st : astate) (i : itv) : (sym * astate) :=
  let x := s_next st in
  (x, set_next (set_ctx st (set_bound (s_ctx st) x i)) (S x)).
Definition fresh_val (st : astate) (i : itv) : (aval * astate) :=
  let (x, st') := fresh st i in (LV (lvar x), st').

(* [comment removed for export] *)
Definition learn (st : astate) (l : lin) : astate := set_ctx st (add_fact (s_ctx st) l).
Definition learn_eq (st : astate) (l : lin) : astate := learn (learn st l) (lneg l).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive addr :=
| AStk (off : Z)              (* [comment removed for export] *)
| AStkSym (off : lin)         (* [comment removed for export] *)
| APay (off : lin)            (* [comment removed for export] *)
| AAbs (a : Z)                (* [comment removed for export] *)
| AFrm (i : nat) (off : Z)    (* [comment removed for export] *)
| AFrmSym (i : nat) (off : lin) (* [comment removed for export] *)
| AShFrm (i : nat) (t : lin)  (* [comment removed for export] *)
| AShStk (t : lin)            (* [comment removed for export] *)
| AShPay (t : lin)            (* [comment removed for export] *)
| AFlag (i : nat).            (* [comment removed for export] *)

Fixpoint classify_frames (fr : list frame) (i : nat) (l : lin) : option addr :=
  match fr with
  | [] => None
  | f :: r =>
      let c := lcoef (f_sym f) l in
      if Z.eqb c 64 then
        let rest := lsub l (lscale 64 (lvar (f_sym f))) in
        match is_const rest with Some o => Some (AFrm i o) | None => Some (AFrmSym i rest) end
      else if Z.eqb c 8 then Some (AShFrm i (laddc (lsub l (lscale 8 (lvar (f_sym f)))) (- SHB)))
      else if leqb l (lvar (f_flag f)) then Some (AFlag i)
      else classify_frames r (S i) l
  end.

(* [comment removed for export] *)
Definition classify (fr : list frame) (v : aval) : option addr :=
  match v with
  | LV l =>
      match is_const l with
      | Some c => Some (AAbs (c mod two64z))
      | None =>
          if Z.eqb (lcoef SYM_SP0 l) 1 then
            let rest := lsub l (lvar SYM_SP0) in
            if (Z.eqb (lcoef SYM_DATA rest) 0)%bool then
              match is_const rest with Some c => Some (AStk c) | None => Some (AStkSym rest) end
            else None
          else if (Z.eqb (lcoef SYM_DATA l) 1 &&& Z.eqb (lcoef SYM_SP0 l) 0)%bool then
            Some (APay (lsub l (lvar SYM_DATA)))
          else if Z.eqb (lcoef SYM_S32 l) 4 then Some (AShStk (laddc (lsub l (lscale 4 (lvar SYM_S32))) (- SHB)))
          else if Z.eqb (lcoef SYM_D16 l) 2 then Some (AShPay (laddc (lsub l (lscale 2 (lvar SYM_D16))) (- SHB)))
          else classify_frames fr 0 l
      end
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint nth_frame (fr : list frame) (i : nat) : option frame :=
  match fr, i with [], _ => None | f :: _, O => Some f | _ :: r, S i' => nth_frame r i' end.
Fixpoint upd_frame (fr : list frame) (i : nat) (f : frame) : list frame :=
  match fr, i with [], _ => [] | _ :: r, O => f :: r | g :: r, S i' => g :: upd_frame r i' f end.
Fixpoint del_frame (fr : list frame) (i : nat) : list frame :=
  match fr, i with [], _ => [] | _ :: r, O => r | g :: r, S i' => g :: del_frame r i' end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tsyms_app (ts : list (sym * Z)) (acc : list sym) : list sym :=
  match ts with [] => acc | (x, _) :: r => x :: tsyms_app r acc end.
Definition lin_syms_app (l : lin) (acc : list sym) : list sym := tsyms_app (lt l) acc.
Definition aval_syms_app (v : aval) (acc : list sym) : list sym :=
  match v with
  | Top => acc
  | LV l => lin_syms_app l acc
  | CV _ _ a b => lin_syms_app a (lin_syms_app b acc)
  | XV a b => lin_syms_app a (lin_syms_app b acc)
  end.
Definition live_syms (st : astate) : list sym :=
  let l1 := fold_right aval_syms_app [] (s_regs st) in
  let l2 := fold_right (fun c acc => aval_syms_app (c_val c) acc) l1 (s_stk st) in
  let l3 := fold_right (fun a acc => match ar_fact a with Some f => lin_syms_app (af_len f) acc | None => acc end) l2 (s_arrs st) in
  let l4 := fold_right (fun (e : lin * Z * sym) acc => let '(o, _, x) := e in lin_syms_app o (x :: acc)) l3 (s_pcache st) in
  let l5 := fold_right (fun (e : lin * itv) acc => lin_syms_app (fst e) acc) l4 (s_pay st) in
  fold_right (fun f acc =>
     f_sym f :: f_flag f ::
     fold_right (fun c acc' => aval_syms_app (c_val c) acc')
       (fold_right (fun a acc' => match ar_fact a with Some af => lin_syms_app (af_len af) acc' | None => acc' end) acc (f_arrs f))
       (f_cells f)) l5 (s_frames st).
Fixpoint nat_mem (x : nat) (xs : list nat) : bool :=
  match xs with [] => false | y :: r => (Nat.eqb x y ||| nat_mem x r)%bool end.
Definition sym_live (live : list sym) (x : sym) : bool := (Nat.ltb x NGLOB ||| nat_mem x live)%bool.
Fixpoint tsyms_any_live (live : list sym) (ts : list (sym * Z)) : bool :=
  match ts with [] => false | (x, _) :: r => (sym_live live x ||| tsyms_any_live live r)%bool end.
Definition GC_THRESHOLD : nat := 24%nat.
Definition tombstone : lin := Lin 0 [].
Fixpoint count_nontrivial (fs : list lin) : nat :=
  match fs with
  | [] => O
  | f :: r => match lt f with [] => count_nontrivial r | _ => Datatypes.S (count_nontrivial r) end
  end.
Definition gc_fact_list (live : list sym) (fs : list lin) : list lin :=
  map (fun f => if tsyms_any_live live (lt f) then f else tombstone) fs.
Definition gc_facts (st : astate) : astate :=
  let C := s_ctx st in
  if Nat.leb (count_nontrivial (cfacts C)) GC_THRESHOLD then st
  else set_ctx st (Ctx (gc_fact_list (live_syms st) (cfacts C)) (cb C)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tsyms_below (ts : list (sym * Z)) (n : sym) : bool :=
  match ts with [] => true | (x, _) :: r => (Nat.ltb x n &&& tsyms_below r n)%bool end.
Definition lin_below (l : lin) (n : sym) : bool := tsyms_below (lt l) n.
Definition aval_below (v : aval) (n : sym) : bool :=
  match v with Top => true | LV l => lin_below l n | CV _ _ a b => (lin_below a n &&& lin_below b n)%bool
  | XV a b => (lin_below a n &&& lin_below b n)%bool end.
Definition ctx_below (C : ctx) (n : sym) : bool :=
  (forallb (fun f => lin_below f n) (cfacts C) &&& forallb (fun xb : sym * itv => Nat.ltb (fst xb) n) (cb C))%bool.
Definition afact_below (f : option afact) (n : sym) : bool :=
  match f with None => true | Some f => lin_below (af_len f) n end.
(* [comment removed for export] *)
Fixpoint arrs_disjointb (ars : list arr) : bool :=
  match ars with
  | [] => true
  | a :: r => (forallb (fun b => negb (overlaps (ar_lo a) (ar_hi a - ar_lo a) (ar_lo b) (ar_hi b - ar_lo b))) r && arrs_disjointb r)%bool
  end.
Definition frame_wf (n : sym) (f : frame) : bool :=
  (Nat.ltb (f_sym f) n &&& Nat.ltb (f_flag f) n
   &&& (Z.eqb (f_cls f) 1 ||| Z.eqb (f_cls f) 4 ||| Z.eqb (f_cls f) 5)
   &&& Nat.eqb (length (f_sh f)) (Z.to_nat (f_shn f))
   &&& forallb (fun b => Z.leb 0 b &&& Z.ltb b 256) (f_sh f)
   &&& forallb (fun c => aval_below (c_val c) n) (f_cells f)
   &&& forallb (fun a => afact_below (ar_fact a) n) (f_arrs f)
   &&& forallb (fun c => negb (existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) (c_off c) (c_w c)) (f_arrs f))) (f_cells f)
   &&& forallb (fun c => (Z.ltb 0 (c_w c) && Z.leb (c_w c) 8)%bool) (f_cells f)
   &&& arrs_disjointb (f_arrs f))%bool.
(* [comment removed for export] *)
Fixpoint frames_syms_distinct (fr : list frame) : bool :=
  match fr with
  | [] => true
  | f :: r => (negb (Nat.eqb (f_sym f) (f_flag f)) &&& Nat.leb NGLOB (f_sym f) &&& Nat.leb NGLOB (f_flag f)
               &&& forallb (fun g => negb (Nat.eqb (f_sym f) (f_sym g)) &&& negb (Nat.eqb (f_sym f) (f_flag g))
                                    &&& negb (Nat.eqb (f_flag f) (f_sym g)) &&& negb (Nat.eqb (f_flag f) (f_flag g))) r
               &&& frames_syms_distinct r)%bool
  end.
Definition wf_state (st : astate) : bool :=
  let n := s_next st in
  (forallb (fun v => aval_below v n) (s_regs st)
   &&& ctx_below (s_ctx st) n
   &&& forallb (fun c => aval_below (c_val c) n) (s_stk st)
   &&& forallb (fun a => afact_below (ar_fact a) n) (s_arrs st)
   &&& forallb (fun e : lin * Z * sym => let '(o, _, x) := e in (lin_below o n &&& Nat.ltb x n)%bool) (s_pcache st)
   &&& forallb (fun e : lin * itv => lin_below (fst e) n) (s_pay st)
   &&& forallb (fun c => negb (existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) (c_off c) (c_w c)) (s_arrs st))) (s_stk st)
   &&& Nat.leb NGLOB n
   &&& forallb (fun c => (Z.ltb 0 (c_w c) && Z.leb (c_w c) 8)%bool) (s_stk st)
   &&& arrs_disjointb (s_arrs st)
   &&& forallb (frame_wf n) (s_frames st)
   &&& frames_syms_distinct (s_frames st)
   &&& Nat.leb (length (s_frames st)) 3)%bool.

End LAS.
