(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaState LaMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LAS LAM.
Open Scope Z_scope.

Module LAI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive reason :=
| R_FETCH | R_DECODE | R_ECALL | R_EBREAK | R_CSR | R_BADRM | R_UNSUPPORTED
| R_LOAD (w : Z) (a : aval) | R_STORE (w : Z) (a : aval) | R_JALR (a : aval)
| R_AMO | R_FUEL | R_FORKS | R_CUT (c : Z) (what : Z) | R_EXIT (what : Z) | R_SUMMARY (what : Z) | R_CONTRA.

Inductive sres :=
| SNext (st : astate)
| SFork (st_taken st_not : astate)
| SExit (st : astate)
| SFail (pc : Z) (r : reason).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w64 (z : Z) : word := Z_to_bv 64 z.
Definition uw (w : word) : Z := bv_unsigned w.
Definition lit_alu (op : aluop) (a b : Z) : Z := snorm (uw (alu64 op (w64 a) (w64 b))).
Definition lit_aluw (op : aluop) (a b : Z) : Z := snorm (uw (sext 64 (alu32 op (low32 (w64 a)) (low32 (w64 b))) : word)).
Definition lit_md (op : mulop) (a b : Z) : Z := snorm (uw (mul_div op (w64 a) (w64 b))).
Definition lit_mdw (op : mulop) (a b : Z) : Z := snorm (uw (sext 64 (mul_div op (low32 (w64 a)) (low32 (w64 b))) : word)).

Definition two64 : Z := LXL.two64.
Definition two32 : Z := LXL.two32.
Definition two31 : Z := LXL.two31.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition decide_base (C : ctx) (k : cmpk) (x y : lin) : option bool :=
  match k with
  | CK_LTU | CK_LT => decide_ge0 C (laddc (lsub y x) (-1))          (* [comment removed for export] *)
  | CK_EQ =>
      let d := lsub x y in
      match is_const d with
      | Some c => Some (Z.eqb (c mod two64) 0)
      | None =>
          if in_range C d (1 - two64) two64 then
            match decide_ge0 C (laddc d (-1)) with                 (* [comment removed for export] *)
            | Some true => Some false
            | _ => match decide_ge0 C (laddc (lneg d) (-1)) with   (* [comment removed for export] *)
                   | Some true => Some false
                   | _ => (* [comment removed for export] *)
                       if (entails C d None &&& entails C (lneg d) None)%bool then Some true else None
                   end
            end
          else if (entails C d None &&& entails C (lneg d) None)%bool then Some true else None
      end
  end.

Definition to_lin (v : aval) : option lin := match v with LV l => Some l | _ => None end.

(* [comment removed for export] *)
Definition link_facts (C : ctx) (n : bool) (k : cmpk) (x y : lin) (b : sym) : list lin :=
  let e := if n then laddc (lneg (lvar b)) 1 else lvar b in
  let ne := laddc (lneg e) 1 in
  match k with
  | CK_EQ =>
      let d := lsub x y in
      if in_range C d (1 - two64) two64 then
        match lrange C d with
        | Itv lo hi =>
            (match hi with Some h => [lsub (lscale h ne) d] | None => [] end)                              (* [comment removed for export] *)
            ++ (match lo with Some l0 => [lsub d (lscale l0 ne)] | None => [] end)                         (* [comment removed for export] *)
            ++ (match lo with Some l0 => if Z.leb 0 l0 then [ladd (laddc d (-1)) e] else [] | None => [] end)          (* [comment removed for export] *)
            ++ (match hi with Some h => if Z.leb h 0 then [ladd (laddc (lneg d) (-1)) e] else [] | None => [] end)     (* [comment removed for export] *)
        end
      else []
  | CK_LTU | CK_LT =>
      let d := lsub y x in           (* [comment removed for export] *)
      match lrange C d with
      | Itv lo hi =>
          (match lo with Some l0 => [lsub (laddc d (-1)) (lscale (l0 - 1) ne)] | None => [] end)        (* [comment removed for export] *)
          ++ (match hi with Some h => [lsub (lscale h e) d] | None => [] end)                           (* [comment removed for export] *)
      end
  end.
Fixpoint learn_all (st : astate) (ls : list lin) : astate :=
  match ls with [] => st | l :: r => learn_all (learn st l) r end.

(* [comment removed for export] *)
Definition itv_u64 : itv := Itv (Some 0) (Some (two64 - 1)).
Definition degrade (st : astate) (v : aval) : (aval * astate) :=
  match v with
  | Top => fresh_val st itv_u64          (* [comment removed for export] *)
  | CV n k x y =>
      let (b, st1) := fresh st (Itv (Some 0) (Some 1)) in
      (LV (lvar b), learn_all st1 (link_facts (s_ctx st) n k x y b))
  | XV a b =>
      let C := s_ctx st in
      match ihi (lrange C a), ihi (lrange C b) with
      | Some ha, Some hb =>
          if (uexact C a &&& uexact C b &&& Z.leb 0 ha &&& Z.leb 0 hb)%bool then
            let k := Z.max (Z.log2_up (ha + 1)) (Z.log2_up (hb + 1)) in fresh_val st (Itv (Some 0) (Some (2 ^ k - 1)))
          else fresh_val st itop
      | _, _ => fresh_val st itop
      end
  | _ => (v, st)
  end.

Definition itv01 := Itv (Some 0) (Some 1).
Definition itv_s32 := Itv (Some (- two31)) (Some (two31 - 1)).
Definition itv_u (k : Z) := Itv (Some 0) (Some (2 ^ k - 1)).


Definition itv_div (i : itv) (m : Z) : itv :=   (* [comment removed for export] *)
  Itv (option_map (fun a => a / m) (ilo i)) (option_map (fun b => b / m) (ihi i)).

(* [comment removed for export] *)
Fixpoint find_floor (C : ctx) (fs : list lin) (l : lin) (m : Z) : option sym :=
  match fs with
  | [] => None
  | f :: r =>
      let d := lsub l f in                       (* [comment removed for export] *)
      let here := match lt d with
                  | [(v, c)] => if (Z.eqb (lc d) 0 &&& Z.eqb c m
                                    &&& entails12 C (lsub l (lscale m (lvar v)))
                                    &&& entails12 C (laddc (lsub (lscale m (lvar v)) l) (m - 1)))%bool then Some v else None
                  | _ => None
                  end in
      match here with Some v => Some v | None => find_floor C r l m end
  end.

(* [comment removed for export] *)
Definition uview (C : ctx) (l : lin) : option lin :=
  if uexact C l then Some l
  else if in_range C l (- two63) 0 then Some (laddc l two64)
  else None.
(* [comment removed for export] *)
Definition straddles (C : ctx) (l : lin) : bool :=
  match uview C l with Some _ => false | None => sexact C l end.

(* [comment removed for export] *)
Definition lin_litC (C : ctx) (l : lin) : option Z :=
  match is_const l with
  | Some c => Some c
  | None => match lrange C l with
            | Itv (Some a) (Some b) => if Z.eqb a b then Some a else None
            | _ => None
            end
  end.
Definition aval_litC (C : ctx) (v : aval) : option Z := match v with LV l => lin_litC C l | _ => None end.

(* [comment removed for export] *)
Definition sp_res (C : ctx) : option Z := lin_litC C (lvar SYM_R32).
Definition scale_subst (C : ctx) (l : lin) : lin :=
  lsubst (fun x => if Nat.eqb x SYM_SP0 then match sp_res C with Some r => Some (laddc (lscale 32 (lvar SYM_S32)) r) | None => None end
                   else if Nat.eqb x SYM_DATA then Some (lscale 16 (lvar SYM_D16)) else None) l.
Definition unscale (C : ctx) (l : lin) : lin :=
  let cs := lcoef SYM_S32 l in let cd := lcoef SYM_D16 l in
  let l1 := (if (negb (Z.eqb cs 0) &&& Z.eqb (cs mod 32) 0)%bool then
               match sp_res C with
               | Some r => ladd (lsub l (lscale cs (lvar SYM_S32))) (lscale (cs / 32) (laddc (lvar SYM_SP0) (- r)))
               | None => l end
             else l) in
  if (negb (Z.eqb cd 0) &&& Z.eqb (cd mod 16) 0)%bool then ladd (lsub l1 (lscale cd (lvar SYM_D16))) (lscale (cd / 16) (lvar SYM_DATA)) else l1.
(* [comment removed for export] *)
Fixpoint tsplit_div (ts : list (sym * Z)) (m : Z) : (list (sym * Z) * list (sym * Z)) :=
  match ts with
  | [] => ([], [])
  | (x, c) :: rest => let (q, r) := tsplit_div rest m in
                      if Z.eqb (c mod m) 0 then ((x, c / m) :: q, r) else (q, (x, c) :: r)
  end.
Definition lsplit_div (l : lin) (m : Z) : (lin * lin) :=
  let (q, r) := tsplit_div (lt l) m in (Lin (lc l / m) q, Lin (lc l mod m) r).

(* [comment removed for export] *)
Definition shr_floor (st : astate) (l0 : lin) (k : Z) (ri : itv) : (aval * astate) :=
  let m := 2 ^ k in
  let C := s_ctx st in
  let l := (if Z.leb k 5 then scale_subst C l0 else l0) in
  if ldivisible l m then (LV (ldiv l m), st)
  else
    let (q, r) := lsplit_div l m in
    match is_const r with
    | Some _ => (LV q, st)                                     (* [comment removed for export] *)
    | None =>
      match find_floor C (cfacts C) r m with Some v => (LV (ladd q (lvar v)), st) | None =>
        let (x, st1) := fresh st (itv_div (lrange C r) m) in
        let v := lvar x in
        let st2 := learn st1 (lsub r (lscale m v)) in                       (* [comment removed for export] *)
        let st3 := learn st2 (laddc (lsub (lscale m v) r) (m - 1)) in       (* [comment removed for export] *)
        (LV (ladd q v), st3) end
    end.

(* [comment removed for export] *)
Definition and_lowlit (C : ctx) (x : lin) (j : Z) : option Z :=
  let m := 2 ^ j in
  let l := scale_subst C x in
  if forallb (fun t : sym * Z => Z.eqb (snd t mod m) 0) (lt l) then Some (lc l mod m) else None.


(* [comment removed for export] *)
Fixpoint talign16 (ts : list (sym * Z)) : bool :=
  match ts with [] => true | (x, _) :: r => ((Nat.eqb x SYM_SP0 ||| Nat.eqb x SYM_DATA) &&& talign16 r)%bool end.

(* [comment removed for export] *)
Definition in01 (C : ctx) (l : lin) : bool := in_range C l 0 2.

(* [comment removed for export] *)
Definition and_block (C : ctx) (x : lin) (p : Z) : option lin :=
  match lrange2 C x with
  | Itv (Some lo) (Some hi) => let q := lo / p in if Z.eqb q (hi / p) then Some (laddc x (- (q * p))) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition and_split (C : ctx) (x : lin) (p : Z) : option lin :=
  match lrange2 C x with
  | Itv (Some lo) (Some hi) => let q := lo / p in if Z.eqb (q + 1) (hi / p) then Some (laddc x (- ((q + 1) * p))) else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aand_clear (st : astate) (x : lin) (k : Z) : (aval * astate) :=
  let C := s_ctx st in
  let xv := match uview C x with Some x' => Some x' | None => if sexact C x then Some x else None end in
  match xv with
  | Some x' =>
      let (v, st') := shr_floor st x' k (itv_div (lrange C x') (2 ^ k)) in
      (match v with LV q => LV (lscale (2 ^ k) q) | _ => Top end, st')
  | None => (Top, st)
  end.
(* [comment removed for export] *)
Definition aand_low (st : astate) (x : lin) (k : Z) : option (aval * astate) :=
  let C := s_ctx st in
  let xv := match uview C x with Some x' => Some x' | None => if sexact C x then Some x else None end in
  match xv with
  | Some x' =>
      let (v, st') := shr_floor st x' k (itv_div (lrange C x') (2 ^ k)) in
      match v with LV q => Some (LV (lsub x' (lscale (2 ^ k) q)), st') | _ => None end
  | None => None
  end.
Definition aand_gen (st : astate) (x y : lin) : (aval * astate) :=
  let C := s_ctx st in
  match is_const y, is_const x with
  | Some m, _ =>
      let um := m mod two64 in
      (* [comment removed for export] *)
      let k := Z.log2 (two64 - um) in
      if (Z.ltb 0 k &&& Z.ltb k 64 &&& Z.eqb (two64 - um) (2 ^ k))%bool then aand_clear st x k else
      let pow2 := Z.eqb (um + 1) (2 ^ Z.log2 (um + 1)) in
      (* [comment removed for export] *)
      if (pow2 &&& in_range C x 0 (um + 1))%bool then (LV x, st)
      else if (pow2 &&& in_range C x (- (um + 1)) 0)%bool then (LV (laddc x (um + 1)), st)
      else match (if pow2 then and_block C x (um + 1) else None) with Some r => (LV r, st) | None =>
      if (pow2 &&& Z.leb (um + 1) 16 &&& talign16 (lt x))%bool then (alit ((lc x) mod (um + 1)), st)
      else match (if pow2 then and_lowlit C x (Z.log2 (um + 1)) else None) with Some c => (alit c, st) | None =>
      match (if pow2 then aand_low st x (Z.log2 (um + 1)) else None) with
           | Some r => r
           | None => fresh_val st (Itv (Some 0) (Some um))
           end end end
  | None, Some m => fresh_val st (Itv (Some 0) (Some (m mod two64)))
  | None, None =>
      (* [comment removed for export] *)
      if (in01 C x &&& in01 C y)%bool then
        let (r, st1) := fresh st (Itv (Some 0) (Some 1)) in
        (LV (lvar r), learn_all st1 [lsub x (lvar r); lsub y (lvar r); laddc (lsub (lsub (lvar r) x) y) 1])
      else
      (* [comment removed for export] *)
      match ihi (lrange C x), ihi (lrange C y) with
      | Some hx, Some hy => if (uexact C x &&& uexact C y)%bool then fresh_val st (Itv (Some 0) (Some (Z.min hx hy))) else (Top, st)
      | Some hx, None => if (uexact C x &&& uexact C y)%bool then fresh_val st (Itv (Some 0) (Some hx)) else (Top, st)
      | None, Some hy => if (uexact C x &&& uexact C y)%bool then fresh_val st (Itv (Some 0) (Some hy)) else (Top, st)
      | None, None => (Top, st)
      end
  end.
(* [comment removed for export] *)
Definition aor_bit (C : ctx) (x y : lin) : option lin :=
  match is_const y with
  | Some m =>
      let k := Z.log2 m in
      if (Z.ltb 0 m &&& Z.eqb m (2 ^ k) &&& Z.ltb k 63)%bool then
        match lrange C x with
        | Itv (Some lo) (Some hi) =>
            if (Z.leb 0 lo &&& Z.ltb hi two63 &&& Z.eqb (lo / m) (hi / m))%bool
            then Some (if Z.odd (lo / m) then x else laddc x m) else None
        | _ => None
        end
      else None
  | None => None
  end.
(* [comment removed for export] *)
Definition or_split (C : ctx) (x : lin) (m : Z) : option lin :=
  let k := Z.log2 m in
  if (Z.ltb 0 m &&& Z.eqb m (2 ^ k) &&& Z.ltb k 63)%bool then
    match lrange C x with
    | Itv (Some lo) (Some hi) =>
        let qlo := lo / m in let qhi := hi / m in
        if (Z.leb 0 lo &&& Z.ltb hi two63 &&& Z.ltb qlo qhi &&& Z.ltb (qhi - qlo) 8)%bool
        then Some (laddc x (- (((qlo + qhi + 1) / 2) * m)))
        else None
    | _ => None
    end
  else None.

Definition aor_gen (st : astate) (x y : lin) : (aval * astate) :=
  let C := s_ctx st in
  (* [comment removed for export] *)
  if (in01 C x &&& in01 C y)%bool then
    let (r, st1) := fresh st (Itv (Some 0) (Some 1)) in
    (LV (lvar r), learn_all st1 [lsub (lvar r) x; lsub (lvar r) y; lsub (ladd x y) (lvar r)])
  else
  match aor_bit C x y with Some r => (LV r, st) | None =>
  match aor_bit C y x with Some r => (LV r, st) | None =>
  (* [comment removed for export] *)
  match ihi (lrange C x), ihi (lrange C y) with
  | Some hx, Some hy =>
      if (uexact C x &&& uexact C y &&& Z.leb 0 hx &&& Z.leb 0 hy)%bool then
        let k := Z.max (Z.log2_up (hx + 1)) (Z.log2_up (hy + 1)) in fresh_val st (Itv (Some 0) (Some (2 ^ k - 1)))
      else (Top, st)
  | _, _ => (Top, st)
  end end end.

(* [comment removed for export] *)
Definition litze (C : ctx) (v : aval) : aval := match aval_litC C v with Some z => alit z | None => v end.

(* [comment removed for export] *)
Definition asrl_var (st : astate) (x y : lin) : (aval * astate) :=
  let C := s_ctx st in
  match lrange C y with
  | Itv (Some slo) (Some shi) =>
      if (Z.leb 0 slo &&& Z.leb shi 63)%bool then
        let r := match uview C x with
                 | Some x' => let i := lrange C x' in
                              (match ilo i with Some lo => Z.max lo 0 | None => 0 end,
                               match ihi i with Some hi => Z.min hi (two64 - 1) | None => two64 - 1 end)
                 | None => (0, two64 - 1)
                 end in
        fresh_val st (Itv (Some (fst r / 2 ^ shi)) (Some (snd r / 2 ^ slo)))
      else (Top, st)
  | _ => (Top, st)
  end.

(* [comment removed for export] *)
Definition asra_var (st : astate) (x y : lin) : (aval * astate) :=
  let C := s_ctx st in
  match lrange C y with
  | Itv (Some slo) (Some shi) =>
      if (Z.leb 0 slo &&& Z.leb shi 63 &&& sexact C x)%bool then
        match lrange C x with
        | Itv (Some lo) (Some hi) =>
            fresh_val st (Itv (Some (if Z.ltb lo 0 then lo / 2 ^ slo else lo / 2 ^ shi))
                              (Some (if Z.leb 0 hi then hi / 2 ^ slo else hi / 2 ^ shi)))
        | _ => fresh_val st (Itv (Some (- two63)) (Some (two63 - 1)))
        end
      else (Top, st)
  | _ => (Top, st)
  end.

(* [comment removed for export] *)
Definition asll_range (C : ctx) (x y : lin) (smax lim : Z) : option itv :=
  match lrange C y, lrange C x with
  | Itv (Some slo) (Some shi), Itv (Some lo) (Some hi) =>
      if (Z.leb 0 slo &&& Z.leb shi smax &&& Z.leb 0 lo &&& Z.ltb (hi * 2 ^ shi) lim)%bool
      then Some (Itv (Some (lo * 2 ^ slo)) (Some (hi * 2 ^ shi))) else None
  | _, _ => None
  end.
Definition asll_var (st : astate) (x y : lin) (smax lim : Z) : (aval * astate) :=
  match asll_range (s_ctx st) x y smax lim with Some i => fresh_val st i | None => (Top, st) end.

(* [comment removed for export] *)
Definition aalu_gen (st : astate) (op : aluop) (a b : aval) : (aval * astate) :=
    let (a, st) := degrade st a in
    let (b, st) := degrade st b in
    let C := s_ctx st in
    match op, a, b with
    | ALU_ADD, LV x, LV y => (LV (ladd x y), st)
    | ALU_SUB, LV x, LV y => (LV (lsub x y), st)
    | ALU_SLL, LV x, LV y =>
        match is_const y with
        | Some k => let k := k mod 64 in (LV (lscale (2 ^ k) x), st)
        | None => asll_var st x y 63 two64
        end
    | ALU_SRL, LV x, LV y =>
        match is_const y with
        | Some k => let k := k mod 64 in
            if Z.eqb k 0 then (LV x, st)
            else match uview C x with
                 | Some x' => shr_floor st x' k (itv_div (lrange C x') (2 ^ k))
                 | None => fresh_val st (itv_u (64 - k))
                 end
        | None => asrl_var st x y
        end
    | ALU_SRA, LV x, LV y =>
        match is_const y with
        | Some k => let k := k mod 64 in
            if Z.eqb k 0 then (LV x, st)
            else if sexact C x then shr_floor st x k (itv_div (lrange C x) (2 ^ k))
            else fresh_val st (Itv (Some (- 2 ^ (63 - k))) (Some (2 ^ (63 - k) - 1)))
        | None => asra_var st x y
        end
    | ALU_AND, LV x, LV y =>
        match is_const y, is_const x with
        | Some (-1), _ => (LV x, st)
        | _, Some (-1) => (LV y, st)
        | _, _ => aand_gen st x y
        end
    | ALU_XOR, LV x, LV y =>
        match is_const y, is_const x with
        | Some (-1), _ => (LV (laddc (lneg x) (-1)), st)          (* [comment removed for export] *)
        | _, Some (-1) => (LV (laddc (lneg y) (-1)), st)
        | Some 0, _ => (LV x, st)
        | _, Some 0 => (LV y, st)
        | Some 1, _ => if in01 C x then (LV (laddc (lneg x) 1), st) else (XV x y, st)     (* [comment removed for export] *)
        | _, Some 1 => if in01 C y then (LV (laddc (lneg y) 1), st) else (XV x y, st)
        | _, _ =>
            if (in01 C x &&& in01 C y)%bool then
              let (r, st1) := fresh st (Itv (Some 0) (Some 1)) in
              (LV (lvar r), learn_all st1 [lsub (ladd x y) (lvar r); ladd (lsub (lvar r) x) y; lsub (ladd (lvar r) x) y;
                                        laddc (lneg (ladd (ladd x y) (lvar r))) 2])
            else (XV x y, st)
        end
    | ALU_OR, LV x, LV y =>
        match is_const y, is_const x with
        | Some 0, _ => (LV x, st)
        | _, Some 0 => (LV y, st)
        | _, _ => aor_gen st x y
        end
    | ALU_SLTU, LV x, LV y =>
        match uview C x, uview C y with
        | Some x, Some y =>
          match decide_ge0 C (laddc (lsub y x) (-1)) with     (* [comment removed for export] *)
          | Some true => (alit 1, st) | Some false => (alit 0, st)
          | None => (CV false CK_LTU x y, st)
          end
        | _, _ => fresh_val st itv01
        end
    | ALU_SLT, LV x, LV y =>
        if (sexact C x &&& sexact C y)%bool then
          match decide_ge0 C (laddc (lsub y x) (-1)) with
          | Some true => (alit 1, st) | Some false => (alit 0, st)
          | None => (CV false CK_LT x y, st)
          end
        else fresh_val st itv01
    | _, _, _ => (Top, st)
    end.

Definition aalu0 (st : astate) (op : aluop) (a b : aval) : (aval * astate) :=
  match aval_litC (s_ctx st) a, aval_litC (s_ctx st) b with
  | Some x, Some y => (alit (lit_alu op x y), st)
  | _, _ => aalu_gen st op a b
  end.
(* [comment removed for export] *)
Definition aalu (st : astate) (op : aluop) (a b : aval) : (aval * astate) :=
  aalu0 st op (litze (s_ctx st) a) (litze (s_ctx st) b).

(* [comment removed for export] *)
Definition alu_split (st : astate) (op : aluop) (a b : aval) : option lin :=
  let C := s_ctx st in
  match aval_litC C a, aval_litC C b with
  | Some _, Some _ => None
  | _, _ =>
    match op, a, b with
    | ALU_SLTU, LV x, LV y =>
        if straddles C x then Some x else if straddles C y then Some y else None
    | ALU_SRL, LV x, LV y =>
        match is_const y with
        | Some k => if (negb (Z.eqb (k mod 64) 0) &&& straddles C x)%bool then Some x else None
        | None => None
        end
    | ALU_AND, LV x, LV y =>
        match is_const y with
        | Some m =>
            let um := m mod two64 in
            let pow2 := Z.eqb (um + 1) (2 ^ Z.log2 (um + 1)) in
            if (pow2 &&& negb (in_range C x 0 (um + 1)) &&& negb (in_range C x (- (um + 1)) 0)
                &&& in_range C x (- (um + 1)) (um + 1))%bool
            then Some x
            else None     (* [comment removed for export] *)
        | None => None
        end
    | ALU_OR, LV x, LV y =>
        match is_const y, is_const x with
        | Some m, None => match aor_bit C x y with Some _ => None | None => or_split C x m end
        | None, Some m => match aor_bit C y x with Some _ => None | None => or_split C y m end
        | _, _ => None
        end
    | _, _, _ => None
    end
  end.
Definition split_on (st : astate) (l : lin) : sres :=
  SFork (learn st l) (learn st (laddc (lneg l) (-1))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cv_lit (C : ctx) (v : aval) : aval :=
  match v with
  | CV n k a b => match decide_base C k a b with Some bb => alit (if xorb n bb then 1 else 0) | None => v end
  | _ => v
  end.
Definition is_zero_cond0 (st : astate) (v : aval) : (aval * astate) :=    (* [comment removed for export] *)
  match v with
  | CV n k a b => (CV (negb n) k a b, st)
  | XV a b => (CV false CK_EQ a b, st)
  | LV l =>
      match is_const l with
      | Some c => (alit (if Z.eqb (c mod two64) 0 then 1 else 0), st)
      | None => (CV false CK_EQ l (lconst 0), st)
      end
  | Top => fresh_val st itv01
  end.
Definition is_nonzero_cond0 (st : astate) (v : aval) : (aval * astate) :=
  match v with
  | CV n k a b => (CV n k a b, st)
  | XV a b => (CV true CK_EQ a b, st)
  | LV l =>
      match is_const l with
      | Some c => (alit (if Z.eqb (c mod two64) 0 then 0 else 1), st)
      | None => (CV true CK_EQ l (lconst 0), st)
      end
  | Top => fresh_val st itv01
  end.
(* [comment removed for export] *)
Definition is_zero_cond (st : astate) (v : aval) : (aval * astate) :=
  let p := is_zero_cond0 st v in (cv_lit (s_ctx (snd p)) (fst p), snd p).
Definition is_nonzero_cond (st : astate) (v : aval) : (aval * astate) :=
  let p := is_nonzero_cond0 st v in (cv_lit (s_ctx (snd p)) (fst p), snd p).

(* [comment removed for export] *)
Definition norm32 (st : astate) (r : lin) : (aval * astate) :=
  if sexact32 (s_ctx st) r then (LV r, st) else fresh_val st itv_s32.

Definition aaluw_gen (st : astate) (op : aluop) (a b : aval) : (aval * astate) :=
    let (a, st) := degrade st a in
    let (b, st) := degrade st b in
    let C := s_ctx st in
    match op, a, b with
    | ALU_ADD, LV x, LV y => norm32 st (ladd x y)
    | ALU_SUB, LV x, LV y => norm32 st (lsub x y)
    | ALU_SLL, LV x, LV y =>
        match is_const y with
        | Some k => let k := k mod 32 in norm32 st (lscale (2 ^ k) x)
        | None => match asll_range C x y 31 two31 with Some i => fresh_val st i | None => fresh_val st itv_s32 end
        end
    | ALU_SRL, LV x, LV y =>
        match is_const y with
        | Some k => let k := k mod 32 in
            if Z.eqb k 0 then norm32 st x
            else if uexact32 C x then shr_floor st x k (itv_div (lrange C x) (2 ^ k))
            else fresh_val st (itv_u (32 - k))
        | None => fresh_val st itv_s32
        end
    | ALU_SRA, LV x, LV y =>
        match is_const y with
        | Some k => let k := k mod 32 in
            if Z.eqb k 0 then norm32 st x
            else if sexact32 C x then shr_floor st x k (itv_div (lrange C x) (2 ^ k))
            else fresh_val st (Itv (Some (- 2 ^ (31 - k))) (Some (2 ^ (31 - k) - 1)))
        | None => fresh_val st itv_s32
        end
    | _, _, _ => fresh_val st itv_s32
    end.

Definition aaluw0 (st : astate) (op : aluop) (a b : aval) : (aval * astate) :=
  match aval_litC (s_ctx st) a, aval_litC (s_ctx st) b with
  | Some x, Some y => (alit (lit_aluw op x y), st)
  | _, _ => aaluw_gen st op a b
  end.
(* [comment removed for export] *)
Definition aaluw (st : astate) (op : aluop) (a b : aval) : (aval * astate) :=
  aaluw0 st op (litze (s_ctx st) a) (litze (s_ctx st) b).

(* [comment removed for export] *)
Definition amul_itv (st : astate) (x y : lin) : (aval * astate) :=
  let C := s_ctx st in
  match lrange C x, lrange C y with
  | Itv (Some lx) (Some hx), Itv (Some ly) (Some hy) =>
      if (Z.leb 0 lx &&& Z.leb 0 ly &&& Z.ltb (hx * hy) two64)%bool
      then fresh_val st (Itv (Some (lx * ly)) (Some (hx * hy)))
      else (Top, st)
  | _, _ => (Top, st)
  end.
Definition amuldiv_gen (st : astate) (op : mulop) (a b : aval) : (aval * astate) :=
    let (a, st) := degrade st a in
    let (b, st) := degrade st b in
    match op, a, b with
    | M_MUL, LV x, LV y =>
        match is_const x, is_const y with
        | Some c, _ => (LV (lscale c y), st)
        | _, Some c => (LV (lscale c x), st)
        | None, None => amul_itv st x y
        end
    | _, _, _ => (Top, st)
    end.
Definition amuldiv0 (st : astate) (op : mulop) (a b : aval) : (aval * astate) :=
  match aval_litC (s_ctx st) a, aval_litC (s_ctx st) b with
  | Some x, Some y => (alit (lit_md op x y), st)
  | _, _ => amuldiv_gen st op a b
  end.
(* [comment removed for export] *)
Definition amuldiv (st : astate) (op : mulop) (a b : aval) : (aval * astate) :=
  amuldiv0 st op (litze (s_ctx st) a) (litze (s_ctx st) b).
(* [comment removed for export] *)
Definition amuldivw_gen (st : astate) (op : mulop) (a b : aval) : (aval * astate) :=
    let (a, st) := degrade st a in
    let (b, st) := degrade st b in
    match op, a, b with
    | M_MUL, LV x, LV y =>
        match is_const x, is_const y with
        | Some c, _ => norm32 st (lscale c y)
        | _, Some c => norm32 st (lscale c x)
        | None, None => fresh_val st itv_s32
        end
    | _, _, _ => fresh_val st itv_s32
    end.
Definition amuldivw0 (st : astate) (op : mulop) (a b : aval) : (aval * astate) :=
  match aval_litC (s_ctx st) a, aval_litC (s_ctx st) b with
  | Some x, Some y => (alit (lit_mdw op x y), st)
  | _, _ => amuldivw_gen st op a b
  end.
(* [comment removed for export] *)
Definition amuldivw (st : astate) (op : mulop) (a b : aval) : (aval * astate) :=
  amuldivw0 st op (litze (s_ctx st) a) (litze (s_ctx st) b).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cond := (bool * cmpk * lin * lin)%type.

(* [comment removed for export] *)
Definition sign_test (C : ctx) (x y : lin) (n : bool) : option cond :=
  match is_const y with
  | Some 0 => match uview C x with Some x' => Some (n, CK_LTU, lconst (two63 - 1), x') | None => None end
  | _ => None
  end.

Definition cond_of_branch (st : astate) (bc : branch_cond) (a b : aval) : option cond :=
  let C := s_ctx st in
  match bc, a, b with
  | BC_EQ, LV x, LV y => Some (false, CK_EQ, x, y)
  | BC_NE, LV x, LV y => Some (true, CK_EQ, x, y)
  | BC_EQ, CV n k x y, LV z => match is_const z with Some 0 => Some (negb n, k, x, y) | _ => None end   (* [comment removed for export] *)
  | BC_NE, CV n k x y, LV z => match is_const z with Some 0 => Some (n, k, x, y) | _ => None end
  | BC_EQ, LV z, CV n k x y => match is_const z with Some 0 => Some (negb n, k, x, y) | _ => None end
  | BC_NE, LV z, CV n k x y => match is_const z with Some 0 => Some (n, k, x, y) | _ => None end
  | BC_EQ, XV x y, LV z => match is_const z with Some 0 => Some (false, CK_EQ, x, y) | _ => None end
  | BC_NE, XV x y, LV z => match is_const z with Some 0 => Some (true, CK_EQ, x, y) | _ => None end
  | BC_EQ, LV z, XV x y => match is_const z with Some 0 => Some (false, CK_EQ, x, y) | _ => None end
  | BC_NE, LV z, XV x y => match is_const z with Some 0 => Some (true, CK_EQ, x, y) | _ => None end
  | BC_LT, LV x, LV y => if (sexact C x &&& sexact C y)%bool then Some (false, CK_LT, x, y) else sign_test C x y false
  | BC_GE, LV x, LV y => if (sexact C x &&& sexact C y)%bool then Some (true, CK_LT, x, y) else sign_test C x y true
  | BC_LTU, LV x, LV y => match uview C x, uview C y with Some x, Some y => Some (false, CK_LTU, x, y) | _, _ => None end
  | BC_GEU, LV x, LV y => match uview C x, uview C y with Some x, Some y => Some (true, CK_LTU, x, y) | _, _ => None end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition branch_split (st : astate) (bc : branch_cond) (a b : aval) : option lin :=
  let C := s_ctx st in
  match bc, a, b with
  | (BC_LTU | BC_GEU), LV x, LV y => if straddles C x then Some x else if straddles C y then Some y else None
  | _, _, _ => None
  end.


Definition decide_cond (C : ctx) (c : cond) : option bool :=
  let '(n, k, x, y) := c in option_map (fun b => xorb n b) (decide_base C k x y).

(* [comment removed for export] *)
Definition learn_base (st : astate) (k : cmpk) (x y : lin) (b : bool) : astate :=
  match k, b with
  | (CK_LTU | CK_LT), true => learn st (laddc (lsub y x) (-1))
  | (CK_LTU | CK_LT), false => learn st (lsub x y)
  | CK_EQ, true => if in_range (s_ctx st) (lsub x y) (1 - two64) two64 then learn_eq st (lsub x y) else st
  | CK_EQ, false =>
      (* [comment removed for export] *)
      let d := lsub x y in
      if entails (s_ctx st) d None then learn st (laddc d (-1))
      else if entails (s_ctx st) (lneg d) None then learn st (laddc (lneg d) (-1))
      else st
  end.
Definition learn_cond (st : astate) (c : cond) (taken : bool) : astate :=
  let '(n, k, x, y) := c in learn_base st k x y (xorb n taken).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition regn (r : reg) : nat := Z.to_nat (bv_unsigned r).
Definition immz {n} (i : bv n) : Z := bv_signed i.          (* [comment removed for export] *)

Definition msize_w (sz : msize) : Z := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition sp_off (st : astate) : option Z :=
  match classify (s_frames st) (getreg st 2) with Some (AStk k) => Some k | _ => None end.
(* [comment removed for export] *)
Definition wr (st : astate) (rd : nat) (v0 : aval) : astate :=
  let v := match v0 with LV l => LV (unscale (s_ctx st) l) | _ => v0 end in
  let st' := setreg st rd v in
  if Nat.eqb rd 2 then
    match sp_off st, sp_off st' with
    | Some k0, Some k1 => if Z.ltb k0 k1 then drop_below st' k1 else st'
    | _, _ => st'
    end
  else st'.

Definition rm_ok (rm : bv 3) : bool := let z := bv_unsigned rm in (Z.leb z 4 ||| Z.eqb z 7)%bool.

Definition fp_int_result (st : astate) (rd : nat) (i : itv) (npc : Z) : sres :=
  let (v, st1) := fresh_val st i in SNext (set_pc (wr st1 rd v) npc).

(* [comment removed for export] *)
Definition mask_bits (imm : Z) : option Z :=
  if Z.eqb imm 1 then Some 1 else if Z.eqb imm 3 then Some 2 else if Z.eqb imm 7 then Some 3 else if Z.eqb imm 15 then Some 4
  else if Z.eqb imm 31 then Some 5 else if Z.eqb imm 63 then Some 6 else None.
Definition opimm_special (st : astate) (op : aluop) (imm : Z) (v : aval) : option (aval * astate) :=
  if Z.eqb imm 1 then
    match op, v with
    | ALU_SLTU, _ => Some (is_zero_cond st v)
    | ALU_XOR, CV n k x y => Some (CV (negb n) k x y, st)
    | ALU_AND, LV l => match and_lowlit (s_ctx st) l 1 with Some z => Some (alit z, st) | None => None end
    | _, _ => None
    end
  else match op, v, mask_bits imm with
       | ALU_AND, LV l, Some j => match and_lowlit (s_ctx st) l j with Some z => Some (alit z, st) | None => None end
       | _, _, _ => None
       end.
(* [comment removed for export] *)
Definition table_floor (st : astate) (l : lin) (k : Z) (lo hi : Z) : (aval * astate) :=
  let m := 2 ^ k in
  let (x, st1) := fresh st (Itv (Some (lo / m)) (Some (hi / m))) in
  let v := lvar x in
  let st2 := learn st1 (lsub l (lscale m v)) in                       (* [comment removed for export] *)
  let st3 := learn st2 (laddc (lsub (lscale m v) l) (m - 1)) in       (* [comment removed for export] *)
  (LV v, st3).
Definition shift_special (U : uenv) (st : astate) (op : aluop) (k : Z) (v : aval) : option (aval * astate) :=
  match op, v with
  | ALU_SRL, LV x =>
      if (Z.leb 1 k &&& Z.leb k 6)%bool then
        let C := s_ctx st in
        match uview C x with
        | Some x' =>
            let m := 2 ^ k in
            let l := (if Z.leb k 5 then scale_subst C x' else x') in
            if ldivisible l m then None
            else match is_const (snd (lsplit_div l m)) with
                 | Some _ => None
                 | None => match table_span U C x' with
                           | Some (lo, hi) => Some (table_floor st x' k lo hi)
                           | None => None
                           end
                 end
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition op_special (st : astate) (op : aluop) (rs1 : nat) (v2 : aval) : option (aval * astate) :=
  match op, rs1 with
  | ALU_SLTU, O => Some (is_nonzero_cond st v2)
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition resv_after_store (st : astate) (a : aval) : option astate :=
  match s_resv st with
  | None => Some st
  | Some r => match classify (s_frames st) a with
              | Some (AAbs x) => Some (if Z.eqb r x then set_resv st None else st)
              | _ => None
              end
  end.

Definition exec_instr (U : uenv) (st : astate) (i : instr) (sz : Z) : sres :=
  let pc := s_pc st in
  let npc := pc + sz in
  match i with
  | Lui rd imm => SNext (set_pc (wr st (regn rd) (alit (bv_signed imm * 4096))) npc)
  | Auipc rd imm => SNext (set_pc (wr st (regn rd) (alit (pc + bv_signed imm * 4096))) npc)
  | Jal rd imm => SNext (set_pc (wr st (regn rd) (alit npc)) (pc + immz imm))
  | Jalr rd rs1 imm =>
      let t := getreg st (regn rs1) in
      match t with
      | LV l =>
          match is_const l with
          | Some c => let tgt := Z.land ((c + immz imm) mod two64) (two64 - 2) in
                      SNext (set_pc (wr st (regn rd) (alit npc)) tgt)
          | None =>
              match is_var l with
              | Some x => if (Nat.eqb x SYM_RA &&& Z.eqb (immz imm) 0 &&& Nat.eqb (regn rd) 0)%bool then SExit st else SFail pc (R_JALR t)
              | None => SFail pc (R_JALR t)
              end
          end
      | _ => SFail pc (R_JALR t)
      end
  | Branch bc rs1 rs2 imm =>
      let C := s_ctx st in
      let a := cv_lit C (getreg st (regn rs1)) in
      let b := cv_lit C (getreg st (regn rs2)) in
      let tgt := pc + immz imm in
      match aval_litC C a, aval_litC C b with
      | Some x, Some y => SNext (set_pc st (if branch_taken bc (w64 x) (w64 y) then tgt else npc))
      | _, _ =>
        match branch_split st bc a b with Some l => split_on st l | None =>
        match cond_of_branch st bc a b with
        | Some c =>
            match decide_cond (s_ctx st) c with
            | Some true => SNext (set_pc st tgt)
            | Some false => SNext (set_pc st npc)
            | None => SFork (set_pc (learn_cond st c true) tgt) (set_pc (learn_cond st c false) npc)
            end
        | None => SFork (set_pc st tgt) (set_pc st npc)
        end
        end
      end
  | Load sz sx rd rs1 imm =>
      let (a, st0) := aalu st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) in
      match do_load U st0 a (msize_w sz) sx with
      | LDOk v st1 => SNext (set_pc (wr st1 (regn rd) v) npc)
      | LDSplit o p => (* [comment removed for export] *)
          if (lin_below o (s_next st0) &&& lin_below p (s_next st0))%bool
          then SFork (learn st0 (laddc (lsub p o) (-1))) (learn st0 (lsub o p))
          else SFail pc (R_LOAD (msize_w sz) a)
      | LDSplitLin l => (* [comment removed for export] *)
          if lin_below l (s_next st0) then SFork (learn st0 l) (learn st0 (laddc (lneg l) (-1)))
          else SFail pc (R_LOAD (msize_w sz) a)
      | LDFail => SFail pc (R_LOAD (msize_w sz) a)
      end
  | Store sz rs1 rs2 imm =>
      let (a, st0) := aalu st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) in
      match resv_after_store st0 a with
      | None => SFail pc R_AMO
      | Some st0' =>
          match do_store U st0' a (msize_w sz) (getreg st0' (regn rs2)) with
          | Some st1 => SNext (set_pc st1 npc)
          | None => SFail pc (R_STORE (msize_w sz) a)
          end
      end
  | OpImm op rd rs1 imm =>
      let v := getreg st (regn rs1) in
      match opimm_special st op (immz imm) v with
      | Some (r, st1) => SNext (set_pc (wr st1 (regn rd) r) npc)
      | None =>
          match alu_split st op v (alit (immz imm)) with Some l => split_on st l | None =>
          let (r, st1) := aalu st op v (alit (immz imm)) in SNext (set_pc (wr st1 (regn rd) r) npc) end
      end
  | ShiftImm op rd rs1 shamt =>
      match shift_special U st op (bv_unsigned shamt) (getreg st (regn rs1)) with
      | Some (r, st1) => SNext (set_pc (wr st1 (regn rd) r) npc)
      | None =>
      match alu_split st op (getreg st (regn rs1)) (alit (bv_unsigned shamt)) with Some l => split_on st l | None =>
      let (r, st1) := aalu st op (getreg st (regn rs1)) (alit (bv_unsigned shamt)) in SNext (set_pc (wr st1 (regn rd) r) npc) end
      end
  | Op op rd rs1 rs2 =>
      let v1 := getreg st (regn rs1) in
      let v2 := getreg st (regn rs2) in
      match op_special st op (regn rs1) v2 with
      | Some (r, st1) => SNext (set_pc (wr st1 (regn rd) r) npc)
      | None =>
          match alu_split st op v1 v2 with Some l => split_on st l | None =>
          let (r, st1) := aalu st op v1 v2 in SNext (set_pc (wr st1 (regn rd) r) npc) end
      end
  | OpImm32 rd rs1 imm =>
      let (r, st1) := aaluw st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) in SNext (set_pc (wr st1 (regn rd) r) npc)
  | ShiftImm32 op rd rs1 shamt =>
      let (r, st1) := aaluw st op (getreg st (regn rs1)) (alit (bv_unsigned shamt)) in SNext (set_pc (wr st1 (regn rd) r) npc)
  | Op32 op rd rs1 rs2 =>
      let (r, st1) := aaluw st op (getreg st (regn rs1)) (getreg st (regn rs2)) in SNext (set_pc (wr st1 (regn rd) r) npc)
  | Fence _ _ _ _ _ | FenceI _ _ _ => SNext (set_pc st npc)
  | Ecall => SFail pc R_ECALL
  | Ebreak => SFail pc R_EBREAK
  | Mul op rd rs1 rs2 =>
      let (r, st1) := amuldiv st op (getreg st (regn rs1)) (getreg st (regn rs2)) in SNext (set_pc (wr st1 (regn rd) r) npc)
  | Mul32 op rd rs1 rs2 =>
      let (r, st1) := amuldivw st op (getreg st (regn rs1)) (getreg st (regn rs2)) in SNext (set_pc (wr st1 (regn rd) r) npc)
  | Lr wd _ _ rd rs1 =>
      let w := amo_bytes wd in
      match classify (s_frames st) (getreg st (regn rs1)) with
      | Some (AAbs a) =>
          if negb (Z.eqb (a mod w) 0) then SFail pc R_AMO else
          match do_load U st (getreg st (regn rs1)) w true with
          | LDOk v st1 => SNext (set_pc (set_resv (wr st1 (regn rd) v) (Some a)) npc)
          | _ => SFail pc R_AMO
          end
      | _ => SFail pc R_AMO
      end
  | Sc wd _ _ rd rs1 rs2 =>
      let w := amo_bytes wd in
      match classify (s_frames st) (getreg st (regn rs1)) with
      | Some (AAbs a) =>
          if negb (Z.eqb (a mod w) 0) then SFail pc R_AMO else
          match s_resv st with
          | Some r =>
              if Z.eqb r a then
                match do_store U (set_resv st None) (getreg st (regn rs1)) w (getreg st (regn rs2)) with
                | Some st1 => SNext (set_pc (wr st1 (regn rd) (alit 0)) npc)
                | None => SFail pc R_AMO
                end
              else SNext (set_pc (wr (set_resv st None) (regn rd) (alit 1)) npc)
          | None => SNext (set_pc (wr (set_resv st None) (regn rd) (alit 1)) npc)
          end
      | _ => SFail pc R_AMO
      end
  | Amo op wd _ _ rd rs1 rs2 =>
      let w := amo_bytes wd in
      match classify (s_frames st) (getreg st (regn rs1)) with
      | Some (AAbs a) =>
          if negb (Z.eqb (a mod w) 0) then SFail pc R_AMO else
          match do_load U st (getreg st (regn rs1)) w true with
          | LDOk old st1 =>
              if negb (wf_state st1) then SFail pc R_AMO else
              match aval_lit old, aval_lit (getreg st1 (regn rs2)) with
              | Some o, Some s =>
                  let nv := match wd with
                            | AW => snorm (uw (sext 64 (amo_val op (low32 (w64 o)) (low32 (w64 s))) : word))
                            | AD => snorm (uw (amo_val op (w64 o) (w64 s)))
                            end in
                  match resv_after_store st1 (getreg st (regn rs1)) with
                  | Some st2 =>
                      match do_store U st2 (getreg st (regn rs1)) w (alit nv) with
                      | Some st3 => SNext (set_pc (wr st3 (regn rd) old) npc)
                      | None => SFail pc R_AMO
                      end
                  | None => SFail pc R_AMO
                  end
              | _, _ => SFail pc R_AMO
              end
          | _ => SFail pc R_AMO
          end
      | _ => SFail pc R_AMO
      end
  | Csr _ _ _ _ | CsrI _ _ _ _ => SFail pc R_CSR
  | FLoad fmt rd rs1 imm =>
      let w := match fmt with FMT_S => 4 | FMT_D => 8 end in
      let (a, st0) := aalu st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) in
      match do_load U st0 a w false with
      | LDOk _ st1 => SNext (set_pc st1 npc)
      | _ => SFail pc (R_LOAD w a)
      end
  | FStore fmt rs1 rs2 imm =>
      let w := match fmt with FMT_S => 4 | FMT_D => 8 end in
      let (a, st0) := aalu st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) in
      match s_resv st0 with Some _ => SFail pc R_AMO | None =>
      match do_store U st0 a w Top with
      | Some st1 => SNext (set_pc st1 npc)
      | None => SFail pc (R_STORE w a)
      end end
  | Fma _ _ _ _ _ _ rm | Fari _ _ _ _ _ rm | Fsqrt _ _ _ rm =>
      if rm_ok rm then SNext (set_pc st npc) else SFail pc R_BADRM
  | Fsgnj _ _ _ _ _ | Fminmax _ _ _ _ _ => SNext (set_pc st npc)
  | Fcmp _ _ rd _ _ => fp_int_result st (regn rd) itv01 npc
  | Fclass _ rd _ => fp_int_result st (regn rd) (Itv (Some 0) (Some 1023)) npc
  | Fcvt dst src rd rs1 rm =>
      if negb (rm_ok rm) then SFail pc R_BADRM else
      let isf (t : fcvt_ty) := match t with FC_S | FC_D => true | _ => false end in
      match isf dst, isf src, dst with
      | true, _, _ => SNext (set_pc st npc)     (* [comment removed for export] *)
      | false, true, (FC_W | FC_WU) => fp_int_result st (regn rd) itv_s32 npc
      | false, true, _ => fp_int_result st (regn rd) itop npc
      | false, false, _ => SFail pc R_UNSUPPORTED   (* [comment removed for export] *)
      end
  | Fmv dir fmt rd rs1 =>
      match dir, fmt with
      | FMV_X_F, FMT_S => fp_int_result st (regn rd) itv_s32 npc
      | FMV_X_F, FMT_D => fp_int_result st (regn rd) itv_u64 npc
      | FMV_F_X, _ => SNext (set_pc st npc)
      end
  end.

(* [comment removed for export] *)
Definition fetch (U : uenv) (pc : Z) : option (bv 32) := fetch_word (ue_segs U) (w64 pc).

Definition step (U : uenv) (st0 : astate) : sres :=
  let st := gc_facts st0 in          (* [comment removed for export] *)
  let pc := s_pc st in
  match fetch U pc with
  | None => SFail pc R_FETCH
  | Some w =>
      if is_ecall w then SFail pc R_ECALL else
      match decode_any w with
      | Some (i, isz) => exec_instr U st i isz
      | None => SFail pc R_DECODE
      end
  end.

End LAI.
