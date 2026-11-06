(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool PrimString Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanLit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition tok := list Z.
Definition ser (A : Type) := A -> tok -> tok.
Definition des (A : Type) := tok -> option (A * tok).

Definition ser_Z : ser Z := fun z acc => z :: acc.
Definition des_Z : des Z := fun s => match s with z :: r => Some (z, r) | [] => None end.
Definition ser_pos : ser positive := fun p acc => Z.pos p :: acc.
Definition des_pos : des positive := fun s => match s with Z.pos p :: r => Some (p, r) | _ => None end.
Definition ser_nat : ser nat := fun n acc => Z.of_nat n :: acc.
Definition des_nat : des nat := fun s => match s with z :: r => Some (Z.to_nat z, r) | [] => None end.
Definition ser_bool : ser bool := fun b acc => (if b then 1 else 0) :: acc.
Definition des_bool : des bool := fun s => match s with 0 :: r => Some (false, r) | 1 :: r => Some (true, r) | _ => None end.

Definition ser_pair {A B} (f : ser A) (g : ser B) : ser (A * B) := fun '(a, b) acc => f a (g b acc).
Definition des_pair {A B} (f : des A) (g : des B) : des (A * B) :=
  fun s => match f s with Some (a, r) => match g r with Some (b, r') => Some ((a, b), r') | None => None end | None => None end.
Definition ser_opt {A} (f : ser A) : ser (option A) := fun o acc => match o with Some a => 1 :: f a acc | None => 0 :: acc end.
Definition des_opt {A} (f : des A) : des (option A) :=
  fun s => match s with 0 :: r => Some (None, r) | 1 :: r => match f r with Some (a, r') => Some (Some a, r') | None => None end | _ => None end.
Fixpoint ser_els {A} (f : ser A) (l : list A) (acc : tok) : tok := match l with [] => acc | x :: l' => f x (ser_els f l' acc) end.
Definition ser_list {A} (f : ser A) : ser (list A) := fun l acc => Z.of_nat (List.length l) :: ser_els f l acc.
(* [comment removed for export] *)
Fixpoint des_els {A} (f : des A) (n : nat) (s : tok) (racc : list A) : option (list A * tok) :=
  match n with
  | O => Some (List.rev' racc, s)
  | S n' => match f s with Some (a, r) => des_els f n' r (a :: racc) | None => None end
  end.
Definition des_list {A} (f : des A) : des (list A) :=
  fun s => match s with z :: r => des_els f (Z.to_nat z) r [] | [] => None end.
Definition des_map {A B} (f : des A) (g : A -> B) : des B := fun s => match f s with Some (a, r) => Some (g a, r) | None => None end.

(* [comment removed for export] *)
Definition ser_lin : ser lin := fun l acc => ser_Z (l_c l) (ser_list (ser_pair ser_pos ser_Z) (l_t l) acc).
Definition des_lin : des lin := des_map (des_pair des_Z (des_list (des_pair des_pos des_Z))) (fun '(c, t) => LIN c t).
Definition ser_rkind : ser rkind := fun k acc => (match k with RW => 0 | RO => 1 | RZ => 2 | RI => 3 | RT => 4 end) :: acc.
Definition des_rkind : des rkind :=
  fun s => match s with 0 :: r => Some (RW, r) | 1 :: r => Some (RO, r) | 2 :: r => Some (RZ, r) | 3 :: r => Some (RI, r) | 4 :: r => Some (RT, r) | _ => None end.
Definition ser_bc : ser branch_cond :=
  fun c acc => (match c with BC_EQ => 0 | BC_NE => 1 | BC_LT => 2 | BC_GE => 3 | BC_LTU => 4 | BC_GEU => 5 end) :: acc.
Definition des_bc : des branch_cond :=
  fun s => match s with 0 :: r => Some (BC_EQ, r) | 1 :: r => Some (BC_NE, r) | 2 :: r => Some (BC_LT, r) | 3 :: r => Some (BC_GE, r)
                   | 4 :: r => Some (BC_LTU, r) | 5 :: r => Some (BC_GEU, r) | _ => None end.
Definition ser_fact : ser fact :=
  fun f acc =>
    match f with
    | FCond c a b tk => 0 :: ser_bc c (ser_lin a (ser_lin b (ser_bool tk acc)))
    | FRange l lo hi => 1 :: ser_lin l (lo :: hi :: acc)
    | FMod l k r => 2 :: ser_lin l (k :: r :: acc)
    | FBits l m v => 3 :: ser_lin l (m :: v :: acc)
    | FByte x v j => 4 :: ser_lin x (ser_lin v (j :: acc))
    | FBytes x bs => 5 :: ser_lin x (ser_list (ser_pair ser_lin ser_Z) bs acc)
    end.
Definition des_fact : des fact :=
  fun s =>
    match s with
    | 0 :: r => des_map (des_pair des_bc (des_pair des_lin (des_pair des_lin des_bool))) (fun '(c, (a, (b, tk))) => FCond c a b tk) r
    | 1 :: r => des_map (des_pair des_lin (des_pair des_Z des_Z)) (fun '(l, (lo, hi)) => FRange l lo hi) r
    | 2 :: r => des_map (des_pair des_lin (des_pair des_Z des_Z)) (fun '(l, (k, m)) => FMod l k m) r
    | 3 :: r => des_map (des_pair des_lin (des_pair des_Z des_Z)) (fun '(l, (m, v)) => FBits l m v) r
    | 4 :: r => des_map (des_pair des_lin (des_pair des_lin des_Z)) (fun '(x, (v, j)) => FByte x v j) r
    | 5 :: r => des_map (des_pair des_lin (des_list (des_pair des_lin des_Z))) (fun '(x, bs) => FBytes x bs) r
    | _ => None
    end.
Definition ser_rsv : ser rsv := fun v acc => match v with RNone => 0 :: acc | RAt l => 1 :: ser_lin l acc | RUnk => 2 :: acc end.
Definition des_rsv : des rsv :=
  fun s => match s with 0 :: r => Some (RNone, r) | 1 :: r => des_map des_lin RAt r | 2 :: r => Some (RUnk, r) | _ => None end.
Definition ser_bval : ser bval := fun v acc => match v with BK b => 0 :: b :: acc | BV l j => 1 :: ser_lin l (j :: acc) end.
Definition des_bval : des bval :=
  fun s => match s with 0 :: b :: r => Some (BK b, r) | 1 :: r => des_map (des_pair des_lin des_Z) (fun '(l, j) => BV l j) r | _ => None end.
(* [comment removed for export] *)
Fixpoint ser_tree {A} (f : ser A) (t : tree A) (acc : tok) : tok :=
  match t with
  | TEmpty => 0 :: acc
  | TNode l v r => match v with
                   | None => 1 :: ser_tree f l (ser_tree f r acc)
                   | Some x => 2 :: f x (ser_tree f l (ser_tree f r acc))
                   end
  end.
Fixpoint des_tree {A} (f : des A) (fuel : nat) (s : tok) : option (tree A * tok) :=
  match fuel with
  | O => None
  | S fu =>
      match s with
      | 0 :: r => Some (TEmpty, r)
      | 1 :: r => match des_tree f fu r with
                  | Some (l, r1) => match des_tree f fu r1 with Some (rr, r2) => Some (TNode l None rr, r2) | None => None end
                  | None => None
                  end
      | 2 :: r => match f r with
                  | Some (x, r0) => match des_tree f fu r0 with
                                    | Some (l, r1) => match des_tree f fu r1 with Some (rr, r2) => Some (TNode l (Some x) rr, r2) | None => None end
                                    | None => None
                                    end
                  | None => None
                  end
      | _ => None
      end
  end.
Definition ser_region : ser region :=
  fun R acc => ser_lin (rg_base R) (ser_lin (rg_size R) (ser_rkind (rg_kind R) (ser_tree ser_bval (rg_cont R) acc))).
Definition des_region : des region :=
  des_map (des_pair des_lin (des_pair des_lin (des_pair des_rkind (des_tree des_bval 200)))) (fun '(b, (z, (k, c))) => RG b z k c).

(* [comment removed for export] *)
Definition ser_item : ser item :=
  fun i acc => match i with
               | IK o ws tl => 0 :: o :: ser_list ser_Z ws (ser_list ser_Z tl acc)
               | IV o l j n => 1 :: o :: ser_lin l (j :: n :: acc)
               end.
Definition des_item : des item :=
  fun s => match s with
           | 0 :: o :: r => des_map (des_pair (des_list des_Z) (des_list des_Z)) (fun '(ws, tl) => IK o ws tl) r
           | 1 :: o :: r => des_map (des_pair des_lin (des_pair des_Z des_Z)) (fun '(l, (j, n)) => IV o l j n) r
           | _ => None
           end.
Definition ser_erg : ser erg := fun '(b, z, k, is) acc => ser_lin b (ser_lin z (ser_rkind k (ser_list ser_item is acc))).
Definition des_erg : des erg :=
  des_map (des_pair des_lin (des_pair des_lin (des_pair des_rkind (des_list des_item)))) (fun '(b, (z, (k, is))) => (b, z, k, is)).
Definition ser_est : ser est :=
  fun '(pc, regs, rgs, fs, nx, rv) acc =>
    pc :: ser_list (ser_pair ser_pos ser_lin) regs (ser_list ser_erg rgs (ser_list ser_fact fs (ser_pos nx (ser_rsv rv acc)))).
Definition des_est : des est :=
  des_map (des_pair des_Z (des_pair (des_list (des_pair des_pos des_lin)) (des_pair (des_list des_erg) (des_pair (des_list des_fact) (des_pair des_pos des_rsv)))))
          (fun '(pc, (regs, (rgs, (fs, (nx, rv))))) => (pc, regs, rgs, fs, nx, rv)).

(* [comment removed for export] *)
Definition ser_gkind : ser gkind := fun g acc => (match g with GE => 0 | GL => 1 | GN => 2 end) :: acc.
Definition des_gkind : des gkind := fun s => match s with 0 :: r => Some (GE, r) | 1 :: r => Some (GL, r) | 2 :: r => Some (GN, r) | _ => None end.
Definition ser_ll : ser (lin * lin) := ser_pair ser_lin ser_lin.
Definition des_ll : des (lin * lin) := des_pair des_lin des_lin.
Definition ser_smodel : ser smodel :=
  fun M acc =>
    ser_list (fun '(b, z, k) a => ser_lin b (ser_lin z (ser_gkind k a))) (sm_maps M)
      (ser_list (ser_pair ser_lin ser_Z) (sm_allow M)
         (ser_list (ser_pair ser_Z ser_Z) (sm_zr M)
            (ser_opt ser_lin (sm_tid M) (ser_lin (sm_brk M) (ser_lin (sm_sbrk M) (ser_lin (sm_sp M)
               (ser_list ser_ll (sm_frz M) (ser_list ser_ll (sm_own M) acc)))))))).
Definition des_smodel : des smodel :=
  des_map (des_pair (des_list (des_map (des_pair des_lin (des_pair des_lin des_gkind)) (fun '(b, (z, k)) => (b, z, k))))
            (des_pair (des_list (des_pair des_lin des_Z))
               (des_pair (des_list (des_pair des_Z des_Z))
                  (des_pair (des_opt des_lin) (des_pair des_lin (des_pair des_lin (des_pair des_lin (des_pair (des_list des_ll) (des_list des_ll)))))))))
          (fun '(mp, (al, (zr, (tid, (brk, (sbrk, (sp, (frz, own)))))))) => SM mp al zr tid brk sbrk sp frz own).
Definition ser_fstate : ser fstate :=
  fun F acc => match F with
               | FSClosed => 0 :: acc
               | FSOpen o l => 1 :: ser_lin o (ser_lin l acc)
               | FSDone => 2 :: acc
               | FSDir => 3 :: acc
               | FSOpenLB o b => 4 :: ser_lin o (ser_lin b acc)
               end.
Definition des_fstate : des fstate :=
  fun s => match s with
           | 0 :: r => Some (FSClosed, r)
           | 1 :: r => des_map des_ll (fun '(o, l) => FSOpen o l) r
           | 2 :: r => Some (FSDone, r)
           | 3 :: r => Some (FSDir, r)
           | 4 :: r => des_map des_ll (fun '(o, b) => FSOpenLB o b) r
           | _ => None
           end.
Definition ser_src : ser src :=
  fun x acc => match x with
               | SLit bs => 0 :: ser_list ser_Z bs acc
               | SArgs pre j lj suf => 1 :: ser_list ser_Z pre (ser_nat j (ser_lin lj (ser_list ser_Z suf acc)))
               end.
Definition des_src : des src :=
  fun s => match s with
           | 0 :: r => des_map (des_list des_Z) SLit r
           | 1 :: r => des_map (des_pair (des_list des_Z) (des_pair des_nat (des_pair des_lin (des_list des_Z)))) (fun '(pre, (j, (lj, suf))) => SArgs pre j lj suf) r
           | _ => None
           end.
Definition ser_pend : ser pend := fun p acc => pd_ch p :: ser_src (pd_src p) (ser_lin (pd_off p) acc).
Definition des_pend : des pend := des_map (des_pair des_Z (des_pair des_src des_lin)) (fun '(c, (x, o)) => PD c x o).
Fixpoint ser_shp (sh : shp) (acc : tok) : tok :=
  match sh with
  | ShEmit po kc => 0 :: ser_list ser_pend po (kc :: acc)
  | ShAlt2 a b => 1 :: ser_shp a (ser_shp b acc)
  | ShIf l lo hi a b => 2 :: ser_lin l (lo :: hi :: ser_shp a (ser_shp b acc))
  | ShBit l j a b => 3 :: ser_lin l (j :: ser_shp a (ser_shp b acc))
  end.
Fixpoint des_shp (fuel : nat) (s : tok) : option (shp * tok) :=
  match fuel with
  | O => None
  | S fu =>
      let two (k : shp -> shp -> shp) (r : tok) :=
        match des_shp fu r with
        | Some (a, r1) => match des_shp fu r1 with Some (b, r2) => Some (k a b, r2) | None => None end
        | None => None
        end in
      match s with
      | 0 :: r => des_map (des_pair (des_list des_pend) des_Z) (fun '(po, kc) => ShEmit po kc) r
      | 1 :: r => two ShAlt2 r
      | 2 :: r => match des_pair des_lin (des_pair des_Z des_Z) r with Some ((l, (lo, hi)), r0) => two (ShIf l lo hi) r0 | None => None end
      | 3 :: r => match des_pair des_lin des_Z r with Some ((l, j), r0) => two (ShBit l j) r0 | None => None end
      | _ => None
      end
  end.
Definition ser_ast : ser ast :=
  fun a acc =>
    ser_bool (a_on a) (ser_list ser_region (a_rgs a) (ser_list ser_fact (a_fcts a) (ser_list ser_ll (a_own a) (ser_ll (a_dep a)
      (ser_lin (a_nl a) (ser_list ser_ll (a_live a) (ser_list ser_lin (a_pri a) acc))))))).
Definition des_ast : des ast :=
  des_map (des_pair des_bool (des_pair (des_list des_region) (des_pair (des_list des_fact) (des_pair (des_list des_ll) (des_pair des_ll
             (des_pair des_lin (des_pair (des_list des_ll) (des_list des_lin))))))))
          (fun '(on, (rgs, (fc, (own, (dep, (nl, (live, pri))))))) => AST on rgs fc own dep nl live pri).

Definition lit : Type := (est * smodel * fstate * shp * ast)%type.
Definition ser_lit : ser lit :=
  fun '(e, M, F, sh, a) acc => ser_est e (ser_smodel M (ser_fstate F (ser_shp sh (ser_ast a acc)))).
Definition des_lit : des lit :=
  des_map (des_pair des_est (des_pair des_smodel (des_pair des_fstate (des_pair (des_shp 200) des_ast))))
          (fun '(e, (M, (F, (sh, a)))) => (e, M, F, sh, a)).

(* [comment removed for export] *)
Definition int_of_digit (d : Z) : int :=
  match d with 0 => 48 | 1 => 49 | 2 => 50 | 3 => 51 | 4 => 52 | 5 => 53 | 6 => 54 | 7 => 55 | 8 => 56 | _ => 57 end%uint63.
(* [comment removed for export] *)
Fixpoint digits (fuel : nat) (z : Z) (acc : list string) : list string :=
  match fuel with
  | O => acc
  | S fu => let acc' := PrimString.make 1 (int_of_digit (z mod 10)) :: acc in
            if z <? 10 then acc' else digits fu (z / 10) acc'
  end.
Definition tok_strs (z : Z) (acc : list string) : list string :=
  if z <? 0 then PrimString.make 1 45%uint63 :: digits 80 (- z) acc else digits 80 z acc.
(* [comment removed for export] *)
Fixpoint cat_pairs (l : list string) : list string :=
  match l with a :: b :: r => PrimString.cat a b :: cat_pairs r | _ => l end.
Fixpoint cat_all (fuel : nat) (l : list string) : string :=
  match fuel with
  | O => ""%pstring
  | S fu => match l with [] => ""%pstring | [a] => a | _ => cat_all fu (cat_pairs l) end
  end.
Definition str_of_toks (ts : tok) : string :=
  cat_all 64 (List.fold_right (fun z acc => tok_strs z (PrimString.make 1 32%uint63 :: acc)) [] ts).

(* [comment removed for export] *)
Definition P18 : Z := 1000000000000000000.
Fixpoint pow10 (n : nat) : Z := match n with O => 1 | S n' => 10 * pow10 n' end.
(* [comment removed for export] *)
Fixpoint toks_loop (fuel : nat) (s : string) (i : int) (hi : option Z) (cur : int) (nd : nat) (neg any : bool) (racc : tok) : tok :=
  let fin (racc : tok) : tok :=
    if any then
      let v := match hi with Some h => h * pow10 nd + Uint63.to_Z cur | None => Uint63.to_Z cur end in
      (if neg then - v else v) :: racc
    else racc in
  match fuel with
  | O => List.rev' (fin racc)
  | S fu =>
      let c := PrimString.get s i in
      if (c =? 32)%uint63 then toks_loop fu s (i + 1)%uint63 None 0%uint63 O false false (fin racc)
      else if (c =? 45)%uint63 then toks_loop fu s (i + 1)%uint63 hi cur nd true any racc
      else
        let d := (c - 48)%uint63 in
        match nd with
        | 18%nat => let h := match hi with Some h => h * P18 + Uint63.to_Z cur | None => Uint63.to_Z cur end in
                    toks_loop fu s (i + 1)%uint63 (Some h) d 1%nat neg true racc
        | _ => toks_loop fu s (i + 1)%uint63 hi (cur * 10 + d)%uint63 (S nd) neg true racc
        end
  end.
Definition toks_of_str (s : string) : tok :=
  toks_loop (Z.to_nat (Uint63.to_Z (PrimString.length s))) s 0%uint63 None 0%uint63 O false false [].

(* [comment removed for export] *)
Definition lit_enc (x : lit) : string := str_of_toks (ser_lit x []).
Definition lit0 : lit :=
  ((0, [], [], [], 1%positive, RNone), SM [] [] [] None lc0 lc0 lc0 [] [], FSClosed, ShEmit [] 0, ast0).
(* [comment removed for export] *)
Definition lit_dec (s : string) : lit :=
  match des_lit (toks_of_str s) with Some (x, []) => x | _ => lit0 end.
Definition lit_ok (s : string) : bool := match des_lit (toks_of_str s) with Some (_, []) => true | _ => false end.

(* [comment removed for export] *)
Definition enc_with {A} (f : ser A) (x : A) : string := str_of_toks (f x []).
Definition dec_with {A} (f : des A) (dflt : A) (s : string) : A := match f (toks_of_str s) with Some (x, []) => x | _ => dflt end.
Definition ser_regs : ser (tree lin) := ser_tree ser_lin.
Definition des_regs : des (tree lin) := des_tree des_lin 200.
Definition ser_rgs : ser (list region) := ser_list ser_region.
Definition des_rgs : des (list region) := des_list des_region.
Definition ser_facts : ser (list fact) := ser_list ser_fact.
Definition des_facts : des (list fact) := des_list des_fact.
Definition ser_sst : ser sst :=
  fun S acc => s_pc S :: ser_regs (s_regs S) (ser_rgs (s_rgs S) (ser_facts (s_facts S) (ser_pos (s_next S) (ser_rsv (s_resv S) acc)))).
Definition des_sst : des sst :=
  des_map (des_pair des_Z (des_pair des_regs (des_pair des_rgs (des_pair des_facts (des_pair des_pos des_rsv)))))
          (fun '(pc, (R, (rgs, (fs, (nx, rv))))) => SST pc R rgs fs nx rv).
Definition des_shp_top : des shp := des_shp 200.
(* [comment removed for export] *)
