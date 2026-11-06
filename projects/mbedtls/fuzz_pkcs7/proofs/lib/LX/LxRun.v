(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxSum LxStep.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

Record plan : Set := PLANS {
  p_stops : list Z;              (* [comment removed for export] *)
  p_dirs : list (Z * dir);       (* [comment removed for export] *)
  p_fuel : N;
  p_sums : list summary          (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition PLAN (stops : list Z) (dirs : list (Z * dir)) (fuel : N) : plan := PLANS stops dirs fuel [].

Fixpoint zmem (z : Z) (l : list Z) : bool :=
  match l with [] => false | x :: l' => Z.eqb z x || zmem z l' end.

Fixpoint dir_at (l : list (Z * dir)) (pc : Z) : option dir :=
  match l with [] => None | (p, d) :: l' => if Z.eqb p pc then Some d else dir_at l' pc end.

(* [comment removed for export] *)
Fixpoint merge_pcs (l : list (Z * dir)) : list (Z * Z) :=
  match l with [] => [] | (p, DMerge r) :: l' => (p, r) :: merge_pcs l' | _ :: l' => merge_pcs l' end.

Inductive rtree : Set :=
| RLeaf (ss : sstate)
| RBr (c : cond) (t f : rtree)
| RBind (i : positive) (t : rtree)
| RJoin (c : cond) (nx : positive) (k : nat) (t : rtree)   (* [comment removed for export] *)
| RCall (pc : Z) (nx : positive) (k : nat) (nl : positive) (kl : nat) (t : rtree)
                                                            (* [comment removed for export] *)
| RCallL (pc : Z) (nx : positive) (k : nat) (nl : positive) (kl : nat) (nm : nat) (t : rtree)
                                          (* [comment removed for export] *)
| RCallM (pc : Z) (nx : positive) (k : nat) (nl : positive) (kl : nat) (nm : nat) (t1 t2 : rtree)
                                          (* [comment removed for export] *)
| RPark (ss : sstate)                     (* [comment removed for export] *)
| RMerge (nx : positive) (k : nat) (t tm : rtree)
                                          (* [comment removed for export] *)
| RDead                                   (* [comment removed for export] *)
| RFail (pc : Z) (code : Z).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Lin.
  Variable segs : list Segment.
  Variable C : lxcfg.
  Variable D : Z -> option dir.

  (* [comment removed for export] *)
  Fixpoint lin_run (fuel : nat) (target : Z) (ss : sstate) : option sstate :=
    match fuel with
    | O => None
    | S f =>
        match s_pc ss with
        | PCz pc =>
            if Z.eqb pc target then Some ss else
            match fetch_word segs (Z_to_bv 64 pc) with
            | None => None
            | Some w =>
                if is_ecall w then None else
                match decode_any w with
                | None => None
                | Some (i, sz) =>
                    match sym_step C D i sz ss with
                    | SNext ss' => lin_run f target ss'
                    | _ => None
                    end
                end
            end
        | PCret _ => None
        end
    end.
End Lin.

(* [comment removed for export] *)
Fixpoint merge_regs (r1 r2 : list sreg) (nx : positive) : list sreg * nat :=
  match r1, r2 with
  | a :: r1', b :: r2' =>
      if sreg_eqb a b then let '(rs, k) := merge_regs r1' r2' nx in (a :: rs, k)
      else let '(rs, k) := merge_regs r1' r2' (Pos.succ nx) in (RZ (eatom (EZv nx)) :: rs, S k)
  | _, _ => ([], O)
  end.

Fixpoint fresh_facts (nx : positive) (k : nat) : list pfact :=
  match k with
  | O => []
  | S k' => FGe (eatom (EZv nx)) :: FGe (eadd (ELit (two64 - 1)) (emulc (-1) (eatom (EZv nx)))) :: fresh_facts (Pos.succ nx) k'
  end.

Fixpoint mfs_eqb (a b : list mfact) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => mfact_eqb x y && mfs_eqb a' b'
  | _, _ => false
  end.

Definition spc_eqb (a b : spc) : bool :=
  match a, b with PCz x, PCz y => Z.eqb x y | _, _ => false end.

(* [comment removed for export] *)
Definition merge (C : lxcfg) (s1 s2 : sstate) : option (sstate * positive * nat) :=
  let nx := Pos.max (s_nx s1) (s_nx s2) in
  if ss_wf C s1 && ss_wf C s2 && mfs_eqb (s_mf s1) (s_mf s2) && spc_eqb (s_pc s1) (s_pc s2)
     && ws_eqb (s_W s1) (s_W s2) && Nat.eqb (s_ref s1) (s_ref s2) && Nat.eqb (s_nm s1) (s_nm s2) && Pos.eqb (s_nl s1) (s_nl s2) && bklist_eqb (s_bl s1) (s_bl s2)
     && Nat.eqb (length (s_rs s1)) 31 && Nat.eqb (length (s_rs s2)) 31 then
    let '(rs, k) := merge_regs (s_rs s1) (s_rs s2) nx in
    Some (SSTX (s_pc s1) rs (s_mf s1) (pf_inter (s_pf s1) (s_pf s2) ++ fresh_facts nx k) (s_W s1) (Pos.add nx (Pos.of_nat k)) (s_same s1 && s_same s2) (s_ref s1) (s_nm s1) (s_nl s1) (s_bl s1), nx, k)
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint paddn (n : positive) (k : nat) : positive :=
  match k with O => n | S k' => paddn (Pos.succ n) k' end.

Definition reg_keep (nx0 : positive) (r : sreg) (rs : list sreg) : bool :=
  rvars_lt nx0 r && forallb (sreg_eqb r) rs.

(* [comment removed for export] *)
Fixpoint lits_of (rs : list sreg) : option (list Z) :=
  match rs with
  | [] => Some []
  | RZ e :: rs' => match is_lit e, lits_of rs' with Some z, Some zs => Some (z :: zs) | _, _ => None end
  | RW _ :: _ => None
  end.

Definition all_u64 (sts : list sstate) (rs : list sreg) : bool :=
  forallb (fun sr => match sr with
                     | (ss, RZ e) => e_u64 (oracle_of ss) e
                     | (_, RW _) => true
                     end) (combine sts rs).

Definition havoc_facts (sts : list sstate) (rs : list sreg) (v : positive) : list pfact :=
  let ev := eatom (EZv v) in
  match lits_of rs with
  | Some (z :: zs) =>
      let lo := fold_left Z.min zs z in let hi := fold_left Z.max zs z in
      FGe (eadd ev (ELit (- lo))) :: FGe (eadd (ELit hi) (emulc (-1) ev))
        :: (if Z.ltb lo 0 && Z.ltb 0 hi && forallb (fun x => negb (Z.eqb x 0)) (z :: zs)
            then [FSep ev (ELit 0) (ELit (-1)) (ELit 2)] else [])
  | _ => if all_u64 sts rs then [FGe ev; FGe (eadd (ELit (two64 - 1)) (emulc (-1) ev))] else []
  end.

(* [comment removed for export] *)
Fixpoint merge_cols (nx0 : positive) (sts : list sstate) (cols : list (list sreg)) (v : positive) : list sreg * list pfact * nat :=
  match cols with
  | [] => ([], [], O)
  | col :: cols' =>
      match col with
      | [] => ([], [], O)
      | r :: rs =>
          if reg_keep nx0 r rs then let '(ms, fs, k) := merge_cols nx0 sts cols' v in (r :: ms, fs, k)
          else let '(ms, fs, k) := merge_cols nx0 sts cols' (Pos.succ v) in
               (RZ (eatom (EZv v)) :: ms, havoc_facts sts col v ++ fs, S k)
      end
  end.

(* [comment removed for export] *)
Fixpoint reg_cols (n : nat) (rss : list (list sreg)) : list (list sreg) :=
  match n with
  | O => []
  | S n' => map (fun rs => hd (RW 1%positive) rs) rss :: reg_cols n' (map (fun rs => tl rs) rss)
  end.

Definition pf_common (nx0 : positive) (sts : list sstate) (pf : list pfact) : list pfact :=
  List.filter (fun f => pfvars_lt nx0 f && forallb (fun ss => pf_mem f (s_pf ss)) sts) pf.
Definition mf_common (nx0 : positive) (sts : list sstate) (mf : list mfact) : list mfact :=
  List.filter (fun f => mfvars_lt nx0 f && forallb (fun ss => mf_mem f (s_mf ss)) sts) mf.
Fixpoint w_mem (lh : expr * expr) (W : list (expr * expr)) : bool :=
  match W with [] => false | (l, h) :: W' => (expr_eqb (fst lh) l && expr_eqb (snd lh) h) || w_mem lh W' end.
Fixpoint w_union (W acc : list (expr * expr)) : list (expr * expr) :=
  match W with [] => acc | lh :: W' => w_union W' (if w_mem lh acc then acc else acc ++ [lh]) end.
Definition w_all (sts : list sstate) : list (expr * expr) :=
  fold_left (fun acc ss => w_union (s_W ss) acc) sts [].

(* [comment removed for export] *)
Definition same_mem (a b : sstate) : bool :=
  mfs_eqb (s_mf a) (s_mf b) && ws_eqb (s_W a) (s_W b) && Bool.eqb (s_same a) (s_same b)
  && Nat.eqb (s_ref a) (s_ref b) && Nat.eqb (s_nm a) (s_nm b) && bklist_eqb (s_bl a) (s_bl b).

(* [comment removed for export] *)
Definition same_key (nx0 : positive) (r : Z) (a b : sstate) : bool :=
  same_mem a b &&
  (Z.eqb r 0 || match is_lit (rd_expr a r), is_lit (rd_expr b r) with
                | Some x, Some y => Z.eqb x y
                | None, None => sreg_eqb (rd_reg a r) (rd_reg b r) && rvars_lt nx0 (rd_reg a r)
                | _, _ => false
                end).

Fixpoint group_insert (nx0 : positive) (r : Z) (ss : sstate) (gs : list (list sstate)) : list (list sstate) :=
  match gs with
  | [] => [[ss]]
  | g :: gs' =>
      match g with
      | s1 :: _ => if same_key nx0 r ss s1 then (ss :: g) :: gs' else g :: group_insert nx0 r ss gs'
      | [] => g :: group_insert nx0 r ss gs'
      end
  end.

Fixpoint group_states (nx0 : positive) (r : Z) (sts : list sstate) : list (list sstate) :=
  match sts with [] => [] | ss :: sts' => group_insert nx0 r ss (group_states nx0 r sts') end.

(* [comment removed for export] *)
Fixpoint pdist (n m : positive) (fuel : nat) : nat :=   (* [comment removed for export] *)
  match fuel with O => O | S f => if Pos.leb m n then O else S (pdist (Pos.succ n) m f) end.

Definition merge_n (C : lxcfg) (nx0 nl0 : positive) (sts : list sstate) : option (sstate * nat) :=
  match sts with
  | [] => None
  | [p] =>
      (* [comment removed for export] *)
      if ss_wf C p && Nat.eqb (length (s_rs p)) 31 && Pos.leb nx0 (s_nx p)
         && match s_pc p with PCz _ => true | _ => false end && mrefs_ok p && lrefs_ok nl0 p
      then Some (p, pdist nx0 (s_nx p) (Pos.to_nat (s_nx p))) else None
  | s1 :: rest =>
      let W := w_all sts in
      if forallb (fun ss => Nat.eqb (length (s_rs ss)) 31 && spc_eqb (s_pc ss) (s_pc s1) && Nat.eqb (s_ref ss) (s_ref s1) && mrefs_ok ss && lrefs_ok nl0 ss) sts
         && match s_pc s1 with PCz _ => true | _ => false end
         && forallb (fun lh => evars_lt nx0 (fst lh) && evars_lt nx0 (snd lh)) W
      then
        let '(rs, hf, k) := merge_cols nx0 sts (reg_cols 31 (map s_rs sts)) nx0 in
        Some (SSTX (s_pc s1) rs (mf_common nx0 rest (s_mf s1)) (pf_common nx0 rest (s_pf s1) ++ hf) W
                  (paddn nx0 k) (forallb s_same sts) (s_ref s1) (s_nm s1) (s_nl s1) (s_bl s1), k)
      else None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint absorb (hi : expr) (mf : list mfact) : option (expr * list mfact) :=
  match mf with
  | [] => None
  | f :: mf' =>
      let skip := match absorb hi mf' with Some (h, r) => Some (h, f :: r) | None => None end in
      match f with
      | MRw b cs => match ediff_lit b hi with
                    | Some 0 => Some (eadd hi (ELit (Z.of_N (cells_sizeN cs))), mf')
                    | _ => skip end
      | MStk b h2 => match ediff_lit b hi with
                     | Some 0 => Some (h2, mf')
                     | _ => skip end
      | _ => skip
      end
  end.

(* [comment removed for export] *)
Fixpoint release_pass (spx : expr) (pf : list pfact) (mf acc : list mfact) : list mfact :=
  match mf with
  | [] => rev acc
  | MStk lo hi :: mf' =>
      match absorb hi (rev acc ++ mf') with
      | Some (hi', rest) => if (if (if dec_le pf lo hi then dec_le pf hi hi' else false) then dec_le pf hi' spx else false) then MStk lo hi' :: rest else release_pass spx pf mf' (MStk lo hi :: acc)
      | None => release_pass spx pf mf' (MStk lo hi :: acc)
      end
  | f :: mf' => release_pass spx pf mf' (f :: acc)
  end.

Fixpoint release_iter (n : nat) (spx : expr) (pf : list pfact) (mf : list mfact) : list mfact :=
  match n with O => mf | S n' => release_iter n' spx pf (release_pass spx pf mf []) end.

Definition release_stk (ss : sstate) : sstate :=
  set_mf ss (release_iter (length (s_mf ss)) (rd_expr ss 2) (s_pf ss) (s_mf ss)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint pos_mem (v : positive) (l : list positive) : bool :=
  match l with [] => false | x :: l' => if Pos.eqb x v then true else pos_mem v l' end.

Fixpoint evars (e : expr) (acc : list positive) : list positive :=
  match e with
  | EZv v => if pos_mem v acc then acc else v :: acc
  | ELit _ | EUv _ => acc
  | EAdd a b | EOp _ a b => evars a (evars b acc)
  | EMulC _ a => evars a acc
  end.

Fixpoint cvars (c : cellx) (acc : list positive) : list positive :=
  match c with XZ _ e | XRep _ e => evars e acc | XSl c' _ _ => cvars c' acc | _ => acc end.

Fixpoint lvars (l : lexpr) (acc : list positive) : list positive :=
  match l with LBase _ => acc | LUpd l' i _ v => lvars l' (evars i (evars v acc)) end.

Fixpoint blvars (bl : bklist) (acc : list positive) : list positive :=
  match bl with BL0 | BLV _ => acc | BCons a n bl' => evars a (evars n (blvars bl' acc)) end.
Definition mfvars (f : mfact) (acc : list positive) : list positive :=
  match f with
  | MRw a cs | MRo a cs => evars a (fold_right cvars acc cs)
  | MBy a n _ => evars a (evars n acc)
  | MStk a b | MAobj a b => evars a (evars b acc)
  | MOpq _ ok sh => fold_right (fun lh acc' => evars (fst lh) (evars (snd lh) acc')) acc (ok ++ sh)
  | MArr a _ l n _ => evars a (lvars l (evars n acc))
  | MMunch W _ _ | MLaw _ W _ _ => fold_right (fun lh acc' => evars (fst lh) (evars (snd lh) acc')) acc W
  | MWmono _ _ => acc
  | MCli _ a b | MCobj _ a b => evars a (evars b acc)
  | MCliH _ s a b => evars s (evars a (evars b acc))
  | MHeap bl ok => blvars bl (fold_right (fun lh acc' => evars (fst lh) (evars (snd lh) acc')) acc ok)
  | MLawH _ bl sp X _ _ => blvars bl (evars sp (fold_right (fun lh acc' => evars (fst lh) (evars (snd lh) acc')) acc X))
  | MApartBl a b bl => evars a (evars b (blvars bl acc))
  | MOqH _ _ => acc
  | MHpr _ o b xs ok => blvars o (blvars b (fold_right evars (fold_right (fun lh acc' => evars (fst lh) (evars (snd lh) acc')) acc ok) xs))
  end.

Definition pfvars (f : pfact) (acc : list positive) : list positive :=
  match f with
  | FGe e => evars e acc
  | FAl a _ => evars a acc
  | FCr a b | FLe a b | FLt a b | FEq a b => evars a (evars b acc)
  | FSep a b c d | FOr2 a b c d => evars a (evars b (evars c (evars d acc)))
  | FSep0 z a b c d | FOr3z z a b c d => evars z (evars a (evars b (evars c (evars d acc))))
  | FProp _ xs => fold_right evars acc xs
  | FShb v c oa on => (if pos_mem v acc then (fun l => l) else cons v) (evars c (evars oa (evars on acc)))
  end.

(* [comment removed for export] *)
Definition pfatoms (f : pfact) : list expr :=
  match f with
  | FGe e => atoms_of e []
  | FAl a _ => atoms_of a []
  | FCr a b | FLe a b | FLt a b | FEq a b => atoms_of_list [a; b] []
  | FSep a b c d | FOr2 a b c d => atoms_of_list [a; b; c; d] []
  | FSep0 z a b c d | FOr3z z a b c d => atoms_of_list [z; a; b; c; d] []
  | FProp _ xs => atoms_of_list xs []
  | FShb v c oa on => EZv v :: atoms_of_list [c; oa; on] []
  end.

(* [comment removed for export] *)
Definition v_local (v : positive) (f : pfact) : bool :=
  match f with
  | FShb k _ _ _ => Pos.eqb k v
  | _ => match pfatoms f with [EZv v'] => Pos.eqb v' v | _ => false end
  end.

Definition live_vars (ss : sstate) : list positive :=
  let acc := match s_pc ss with PCret (RZ e) => evars e [] | _ => [] end in
  let acc := fold_right (fun r acc' => match r with RZ e => evars e acc' | RW _ => acc' end) acc (s_rs ss) in
  let acc := fold_right (fun lh acc' => evars (fst lh) (evars (snd lh) acc')) acc (s_W ss) in
  let acc := blvars (s_bl ss) acc in
  fold_right mfvars acc (s_mf ss).

Definition gc_var (pf : list pfact) (v : positive) : list pfact :=
  if forallb (fun f => if pos_mem v (pfvars f []) then v_local v f else true) pf
  then List.filter (fun f => negb (pos_mem v (pfvars f []))) pf else pf.

Definition gc_facts (nx0 : positive) (ss : sstate) : sstate :=
  let live := live_vars ss in
  let cands := List.filter (fun v => Pos.leb nx0 v && negb (pos_mem v live)) (fold_right pfvars [] (s_pf ss)) in
  match cands with
  | [] => ss
  | _ => set_pf ss (fold_left gc_var cands (s_pf ss))
  end.

Section Run.
  Variable segs : list Segment.
  Variable C : lxcfg.
  Variable pl : plan.
  Variable genv : list expr.     (* [comment removed for export] *)

  Variable nx0 : positive.       (* [comment removed for export] *)
  Variable nl0 : positive.       (* [comment removed for export] *)

  Definition guard (k : sstate -> rtree) (ss : sstate) : rtree :=
    if contradictory (s_pf ss) then RDead else k ss.

  (* [comment removed for export] *)
  Fixpoint lx_go (mps : list Z) (fuel : nat) (first : bool) (ss : sstate) : rtree :=
    match fuel with
    | O => RFail (-1) 100
    | S f =>
        match s_pc ss with
        | PCret _ => RLeaf ss
        | PCz pc =>
            if negb first && zmem pc (p_stops pl) then RLeaf ss else
            (* [comment removed for export] *)
            if negb first && zmem pc mps && Nat.eqb (s_nm ss) 1 && mrefs_ok ss && lrefs_ok nl0 ss then RPark ss else
            match sums_at (p_sums pl) pc with
            | su :: more =>
                (* [comment removed for export] *)
                if ss_wf C ss && Pos.leb nx0 (s_nx ss) && Pos.leb nl0 (s_nl ss) then
                  match apply_sums C genv (su :: more) ss with
                  | SumOk k kl ss' => RCall pc (s_nx ss) k (s_nl ss) kl (lx_go mps f false ss')
                  | SumOkL k kl ss' => RCallL pc (s_nx ss) k (s_nl ss) kl (s_nm ss) (lx_go mps f false ss')
                  (* [comment removed for export] *)
                  | SumOkM k kl ss1 oss2 => RCallM pc (s_nx ss) k (s_nl ss) kl (s_nm ss) (lx_go [] f false ss1)
                                                   (match oss2 with Some ss2 => lx_go [] f false ss2 | None => RDead end)
                  | SumFail code => RFail pc code
                  end
                else RFail pc 104
            | [] =>
            match fetch_word segs (Z_to_bv 64 pc) with
            | None => RFail pc 101
            | Some w =>
                if is_ecall w then RFail pc 102 else
                match decode_any w with
                | None => RFail pc 103
                | Some (i, sz) =>
                    match sym_step C (dir_at (p_dirs pl)) i sz ss with
                    | SNext ss' => lx_go mps f false ss'
                    | SBind ss' => if ss_wf C ss && forallb (evars_lt (s_nx ss)) genv && Pos.leb nx0 (s_nx ss)
                                   then RBind (s_nx ss) (lx_go mps f false (gc_facts nx0 ss')) else RFail pc 104
                    | SBranch c st sf =>
                        (* [comment removed for export] *)
                        match dir_at (p_dirs pl) pc, s_pc sf, s_pc st with
                        | Some DJoin, PCz tgt, PCz tgt' =>
                            (* [comment removed for export] *)
                            match lin_run segs C (dir_at (p_dirs pl)) 16 tgt st with
                            | Some st' =>
                                match merge C st' sf with
                                | Some (sm, nx, k) => if forallb (evars_lt nx) genv && Pos.leb nx0 nx then RJoin c nx k (lx_go mps f false (gc_facts nx0 sm)) else RFail pc 107
                                | None => RBr c (guard (lx_go mps f false) st) (guard (lx_go mps f false) sf)
                                end
                            | None =>
                                match lin_run segs C (dir_at (p_dirs pl)) 16 tgt' sf with
                                | Some sf' =>
                                    match merge C st sf' with
                                    | Some (sm, nx, k) => if forallb (evars_lt nx) genv && Pos.leb nx0 nx then RJoin c nx k (lx_go mps f false (gc_facts nx0 sm)) else RFail pc 107
                                    | None => RBr c (guard (lx_go mps f false) st) (guard (lx_go mps f false) sf)
                                    end
                                | None => RBr c (guard (lx_go mps f false) st) (guard (lx_go mps f false) sf)
                                end
                            end
                        | _, _, _ => RBr c (guard (lx_go mps f false) st) (guard (lx_go mps f false) sf)
                        end
                    | SStop ss' => RLeaf (release_stk ss')
                    | SFail code => RFail pc code
                    end
                end
            end
            end
        end
    end.

  (* [comment removed for export] *)
  Fixpoint parks_at (pc : Z) (t : rtree) (acc : list sstate) : list sstate :=
    match t with
    | RPark ss => match s_pc ss with PCz p => if Z.eqb p pc then ss :: acc else acc | _ => acc end
    | RBr _ a b => parks_at pc a (parks_at pc b acc)
    | RBind _ a | RJoin _ _ _ a | RCall _ _ _ _ _ a | RCallL _ _ _ _ _ _ a => parks_at pc a acc
    | RCallM _ _ _ _ _ _ a b => parks_at pc a (parks_at pc b acc)
    | RMerge _ _ a b => parks_at pc a (parks_at pc b acc)
    | RLeaf _ | RDead | RFail _ _ => acc
    end.

  (* [comment removed for export] *)
  Fixpoint merge_groups (fuel : nat) (pc : Z) (mps' : list Z) (gs : list (list sstate)) (t : rtree) : rtree :=
    match gs with
    | [] => t
    | g :: gs' =>
        merge_groups fuel pc mps' gs'
          match merge_n C nx0 nl0 g with
          | Some (sm, k) =>
              if forallb (evars_lt nx0) genv then RMerge nx0 k t (lx_go mps' fuel false sm) else RMerge nx0 O t (RFail pc 107)
          | None => RMerge nx0 O t (RFail pc 108)
          end
    end.

  Fixpoint lx_phase (fuel : nat) (mrs : list (Z * Z)) (t : rtree) : rtree :=
    match mrs with
    | [] => t
    | (pc, r) :: mrs' => lx_phase fuel mrs' (merge_groups fuel pc (map fst mrs') (group_states nx0 r (parks_at pc t [])) t)
    end.

  (* [comment removed for export] *)
  Definition mf_bounds (f : mfact) : list pfact :=
    match f with
    | MRw a cs | MRo a cs =>
        [FGe a; FGe (eadd (ELit (two64 - Z.of_N (cells_sizeN cs))) (emulc (-1) a))]
    | MBy a n _ => [FGe a; FGe n; FGe (eadd (ELit two64) (emulc (-1) (eadd a n)))]
    | MStk lo hi => [FGe lo; FGe (eadd (ELit two64) (emulc (-1) hi))]
    | MAobj _ _ | MOpq _ _ _ => []
    | MArr a w _ n _ => [FGe a; FGe n; FGe (eadd (ELit two64) (emulc (-1) (eadd a (emulc (Z.of_N w) n))))]
    | MMunch _ _ _ | MWmono _ _ | MLaw _ _ _ _ | MCli _ _ _ | MCobj _ _ _ => []
    | MHeap _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ | MHpr _ _ _ _ _ => []
    end.

  Definition with_bounds (ss : sstate) : sstate :=
    add_pfs ss (flat_map mf_bounds (s_mf ss)).

  (* [comment removed for export] *)
  Definition frame_sep1 (pf : list pfact) (W : list (expr * expr)) (f : pfact) : list pfact :=
    match f with
    | FOr2 a b c d =>
        flat_map (fun lh : expr * expr => let (l, h) := lh in
                    if (if lin_ge0 pf (esub l b) then lin_ge0 pf (esub c h) else false)
                    then [FSep d (enorm (esub a d)) l (enorm (esub h l))] else []) W
    | FOr3z z a b c d =>
        flat_map (fun lh : expr * expr => let (l, h) := lh in
                    if (if lin_ge0 pf (esub l b) then lin_ge0 pf (esub c h) else false)
                    then [FSep0 z d (enorm (esub a d)) l (enorm (esub h l))] else []) W
    | _ => []
    end.

  Definition with_frame_seps (ss : sstate) : sstate :=
    add_pfs ss (flat_map (frame_sep1 (s_pf ss) (s_W ss)) (s_pf ss)).

  (* [comment removed for export] *)
  Fixpoint alias_of (pf : list pfact) : list (expr * positive) :=
    match pf with
    | [] => []
    | FEq (EZv j) e :: pf' =>
        match e with
        | EZv _ | ELit _ | EUv _ => alias_of pf'
        | _ => (enorm e, j) :: alias_of pf'
        end
    | _ :: pf' => alias_of pf'
    end.

  Definition alias_e (als : list (expr * positive)) (e : expr) : expr :=
    match find (fun p => expr_eqb (fst p) e) als with
    | Some p => eatom (EZv (snd p))
    | None => e
    end.

  Definition alias_r (als : list (expr * positive)) (r : sreg) : sreg :=
    match r with
    | RZ e => match e with
              | ELit _ | EAdd (EMulC 1 (EZv _)) (ELit 0) | EAdd (EMulC 1 (EUv _)) (ELit 0) => r
              | _ => RZ (alias_e als e)
              end
    | RW _ => r
    end.

  Definition als_below (i : positive) (als : list (expr * positive)) : bool :=
    forallb (fun p => evars_lt i (fst p) && Pos.ltb (snd p) i) als.
  Definition als_at (i : positive) (als : list (expr * positive)) : list (expr * positive) :=
    if als_below i als then als else [].

  Fixpoint prune_leaves (pf0 : list pfact) (mf0 : list mfact) (als : list (expr * positive)) (t : rtree) : rtree :=
    match t with
    | RLeaf ss => RLeaf (SSTX (s_pc ss) (map (alias_r als) (s_rs ss))
                              (if s_same ss then List.filter (fun f => negb (mf_mem f mf0)) (s_mf ss) else s_mf ss)
                              (List.filter (fun f => negb (pf_mem f pf0)) (s_pf ss))
                              (map (fun lh => (alias_e als (fst lh), alias_e als (snd lh))) (s_W ss)) (s_nx ss) (s_same ss)
                              (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss))
    | RBr c a b => RBr c (prune_leaves pf0 mf0 als a) (prune_leaves pf0 mf0 als b)
    | RBind i a => RBind i (prune_leaves pf0 mf0 (als_at i als) a)
    | RJoin c nx k a => RJoin c nx k (prune_leaves pf0 mf0 (als_at nx als) a)
    | RCall pc nx k nl kl a => RCall pc nx k nl kl (prune_leaves pf0 mf0 (als_at nx als) a)
    | RCallL pc nx k nl kl nm a => RCallL pc nx k nl kl nm (prune_leaves pf0 mf0 (als_at nx als) a)
    | RCallM pc nx k nl kl nm a b => RCallM pc nx k nl kl nm (prune_leaves pf0 mf0 (als_at nx als) a) (prune_leaves pf0 mf0 (als_at nx als) b)
    | RMerge nx k a b => RMerge nx k (prune_leaves pf0 mf0 als a) (prune_leaves pf0 mf0 (als_at nx als) b)
    | RPark ss => RPark ss
    | RDead => RDead
    | RFail pc code => RFail pc code
    end.
End Run.

(* [comment removed for export] *)
Definition lx_runp (segs : list Segment) (C : lxcfg) (pl : plan) (genv : list expr) (pm : bool) (ss : sstate) : rtree :=
  let ss1 := with_frame_seps (with_bounds (norm_ss ss)) in
  let nx0 := s_nx ss1 in
  let fuel := N.to_nat (p_fuel pl) in
  let mrs := merge_pcs (p_dirs pl) in
  if match c_acc C with Some A => evars_lt nx0 (ac_sb A) | None => true end
  then prune_leaves (s_pf ss1) (if pm then s_mf ss1 else []) (als_at nx0 (alias_of (s_pf ss))) (lx_phase segs C pl genv nx0 (s_nl ss1) fuel mrs (lx_go segs C pl genv nx0 (s_nl ss1) (map fst mrs) fuel true ss1))
  else RFail 0 109.
(* [comment removed for export] *)
Definition lx_run (segs : list Segment) (C : lxcfg) (pl : plan) (genv : list expr) (ss : sstate) : rtree :=
  lx_runp segs C pl genv false ss.

(* [comment removed for export] *)
Fixpoint rt_fails (t : rtree) (acc : list (Z * Z)) : list (Z * Z) :=
  match t with
  | RLeaf _ | RDead | RPark _ => acc
  | RBr _ a b => rt_fails a (rt_fails b acc)
  | RBind _ a => rt_fails a acc
  | RJoin _ _ _ a => rt_fails a acc
  | RCall _ _ _ _ _ a | RCallL _ _ _ _ _ _ a => rt_fails a acc
  | RCallM _ _ _ _ _ _ a b => rt_fails a (rt_fails b acc)
  | RMerge _ _ a b => rt_fails a (rt_fails b acc)
  | RFail pc code => (pc, code) :: acc
  end.

Fixpoint rt_leaf_pcs (t : rtree) (acc : list spc) : list spc :=
  match t with
  | RLeaf ss => s_pc ss :: acc
  | RDead | RFail _ _ | RPark _ => acc
  | RBr _ a b => rt_leaf_pcs a (rt_leaf_pcs b acc)
  | RBind _ a => rt_leaf_pcs a acc
  | RJoin _ _ _ a => rt_leaf_pcs a acc
  | RCall _ _ _ _ _ a | RCallL _ _ _ _ _ _ a => rt_leaf_pcs a acc
  | RCallM _ _ _ _ _ _ a b => rt_leaf_pcs a (rt_leaf_pcs b acc)
  | RMerge _ _ a b => rt_leaf_pcs a (rt_leaf_pcs b acc)
  end.

(* [comment removed for export] *)
Fixpoint rt_parks (t : rtree) (acc : list sstate) : list sstate :=
  match t with
  | RPark ss => ss :: acc
  | RLeaf _ | RDead | RFail _ _ => acc
  | RBr _ a b => rt_parks a (rt_parks b acc)
  | RBind _ a => rt_parks a acc
  | RJoin _ _ _ a => rt_parks a acc
  | RCall _ _ _ _ _ a | RCallL _ _ _ _ _ _ a => rt_parks a acc
  | RCallM _ _ _ _ _ _ a b => rt_parks a (rt_parks b acc)
  | RMerge _ _ a b => rt_parks a (rt_parks b acc)
  end.

Fixpoint rt_size (t : rtree) : nat :=
  match t with
  | RLeaf _ | RDead | RFail _ _ | RPark _ => 1
  | RBr _ a b => S (rt_size a + rt_size b)
  | RBind _ a => S (rt_size a)
  | RJoin _ _ _ a => S (rt_size a)
  | RCall _ _ _ _ _ a | RCallL _ _ _ _ _ _ a => S (rt_size a)
  | RCallM _ _ _ _ _ _ a b => S (rt_size a + rt_size b)
  | RMerge _ _ a b => S (rt_size a + rt_size b)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive elink := ELaw (l : nat) (X : list (expr * expr)) | EMunch (W : list (expr * expr)).

(* [comment removed for export] *)
Definition noheapb (f : mfact) : bool := match f with MHeap _ _ | MHpr _ _ _ _ _ => false | _ => true end.
Definition link_ivls (X : list (expr * expr)) : list (expr * expr) := map (fun lh => (enorm (fst lh), enorm (snd lh))) X.
(* [comment removed for export] *)
Definition link_filter (C : lxcfg) (pf : list pfact) (mf : list mfact) (lk : elink) : list mfact :=
  let mfN := map norm_mf mf in
  let pfN := pf_nodup (flat_map norm_pf pf) ++ flat_map mf_bounds mfN in
  let crs := cranges pfN mfN in
  match lk with
  | ELaw l X => let XN := link_ivls X in
                List.filter (law_survives false C l pfN crs mfN XN (w_all_client pfN crs XN) (all_nonempty pfN XN)) mfN
  | EMunch W => let WN := link_ivls W in
                List.filter (fun f => if noheapb f then mf_survives_call C pfN crs mfN WN (w_all_client pfN crs WN) (all_nonempty pfN WN) f else false) mfN
  end.

(* [comment removed for export] *)
Fixpoint links_filter (C : lxcfg) (pf : list pfact) (ch : list (elink * list mfact)) (acc : list mfact) : list mfact :=
  match ch with
  | [] => acc
  | (lk, mfk) :: ch' => links_filter C pf ch' (link_filter C pf (mfk ++ acc) lk)
  end.

(* [comment removed for export] *)
Definition is_tagb (f : mfact) : bool := match f with MCli _ _ _ | MCobj _ _ _ => true | _ => false end.
(* [comment removed for export] *)
Definition links_entry (C : lxcfg) (pf : list pfact) (ch : list (elink * list mfact)) (mf : list mfact) : list mfact :=
  install_post (List.filter (fun f => negb (is_tagb f)) (links_filter C pf ch (List.filter is_tagb mf))) mf.

(* [comment removed for export] *)
Fixpoint mf_diff (l kept : list mfact) : list mfact :=
  match l with
  | [] => []
  | f :: l' => if existsb (mfact_eqb (norm_mf f)) kept then mf_diff l' kept else f :: mf_diff l' kept
  end.
Fixpoint links_dropped (C : lxcfg) (pf : list pfact) (ch : list (elink * list mfact)) (acc : list mfact) : list mfact :=
  match ch with
  | [] => []
  | (lk, mfk) :: ch' => let inl := mfk ++ acc in let outl := link_filter C pf inl lk in
                        mf_diff inl outl ++ links_dropped C pf ch' outl
  end.
(* [comment removed for export] *)
Fixpoint links_filter2 (C : lxcfg) (pf : list pfact) (ch : list (elink * list mfact)) (acc : list mfact) : list mfact * list mfact :=
  match ch with
  | [] => (acc, [])
  | (lk, mfk) :: ch' => let inl := mfk ++ acc in let outl := link_filter C pf inl lk in
                        let rd := links_filter2 C pf ch' outl in (fst rd, mf_diff inl outl ++ snd rd)
  end.
(* [comment removed for export] *)
Definition links_run (C : lxcfg) (pf : list pfact) (ch : list (elink * list mfact)) (mf : list mfact) : list mfact * (nat * list mfact) :=
  let tags := List.filter is_tagb mf in
  let rd := links_filter2 C pf ch tags in
  let carried := List.filter (fun f => negb (is_tagb f)) (fst rd) in
  (install_post carried mf, (length carried, snd rd)).

End LXH.
