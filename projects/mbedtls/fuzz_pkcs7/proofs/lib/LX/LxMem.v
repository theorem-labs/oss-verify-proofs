(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive cellx : Set :=
| XW (i : positive)                       (* [comment removed for export] *)
| XZ (w : N) (e : expr)                   (* [comment removed for export] *)
| XB (w : N) (k : positive)               (* [comment removed for export] *)
| XWn (w : N) (i : positive)              (* [comment removed for export] *)
| XSl (c : cellx) (off len : N)           (* [comment removed for export] *)
| XRep (w : N) (e : expr).                (* [comment removed for export] *)

Fixpoint cellx_size (c : cellx) : N :=
  match c with XW _ => 8 | XZ w _ => w | XB w _ => w | XWn w _ => w | XSl _ _ l => l | XRep w _ => w end.

Fixpoint cells_sizeN (cs : list cellx) : N :=
  match cs with [] => 0 | c :: cs' => (cellx_size c + cells_sizeN cs')%N end.

Fixpoint cellx_eqb (a b : cellx) : bool :=
  match a, b with
  | XW i, XW j => Pos.eqb i j
  | XZ w e, XZ w' e' => N.eqb w w' && expr_eqb e e'
  | XB w k, XB w' k' => N.eqb w w' && Pos.eqb k k'
  | XWn w i, XWn w' j => N.eqb w w' && Pos.eqb i j
  | XSl c o l, XSl c' o' l' => cellx_eqb c c' && N.eqb o o' && N.eqb l l'
  | XRep w e, XRep w' e' => N.eqb w w' && expr_eqb e e'
  | _, _ => false
  end.

Fixpoint cells_eqb (xs ys : list cellx) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => cellx_eqb x y && cells_eqb xs' ys'
  | _, _ => false
  end.

(* [comment removed for export] *)
Inductive lexpr : Set :=
| LBase (k : positive)
| LUpd (l : lexpr) (i : expr) (w : N) (v : expr).

Fixpoint lexpr_eqb (a b : lexpr) : bool :=
  match a, b with
  | LBase k, LBase k' => Pos.eqb k k'
  | LUpd l i w v, LUpd l' i' w' v' => lexpr_eqb l l' && expr_eqb i i' && N.eqb w w' && expr_eqb v v'
  | _, _ => false
  end.

(* [comment removed for export] *)
Inductive bklist : Set := BL0 | BCons (a n : expr) (bl : bklist)
  (* [comment removed for export] *)
  | BLV (k : nat).
Fixpoint bklist_eqb (x y : bklist) : bool :=
  match x, y with
  | BL0, BL0 => true
  | BCons a n b, BCons a' n' b' => expr_eqb a a' && expr_eqb n n' && bklist_eqb b b'
  | BLV k, BLV k' => Nat.eqb k k'
  | _, _ => false
  end.
(* [comment removed for export] *)
Fixpoint bl_based0 (bl : bklist) : bool :=
  match bl with BL0 => true | BLV _ => false | BCons _ _ bl' => bl_based0 bl' end.
(* [comment removed for export] *)
Fixpoint bl_suffix (s bl : bklist) : bool :=
  if bklist_eqb s bl then true else match bl with BCons _ _ bl' => bl_suffix s bl' | _ => false end.

Inductive mfact : Set :=
| MRw (a : expr) (cs : list cellx)
| MRo (a : expr) (cs : list cellx)
| MBy (a : expr) (n : expr) (k : positive)
| MStk (lo hi : expr)
| MAobj (a n : expr)
| MOpq (k : nat) (ok sh : list (expr * expr))   (* [comment removed for export] *)
| MArr (a : expr) (w : N) (l : lexpr) (n : expr) (wr : bool)
                                                (* [comment removed for export] *)
(* [comment removed for export] *)
| MMunch (W : list (expr * expr)) (i j : nat)    (* [comment removed for export] *)
| MWmono (i j : nat)                             (* [comment removed for export] *)
| MLaw (l : nat) (X : list (expr * expr)) (i j : nat)    (* [comment removed for export] *)
(* [comment removed for export] *)
| MCli (l : nat) (a n : expr)
| MCobj (l : nat) (a n : expr)
(* [comment removed for export] *)
| MHeap (bl : bklist) (ok : list (expr * expr))
| MLawH (l : nat) (bl : bklist) (sp : expr) (X : list (expr * expr)) (i j : nat)
| MCliH (l : nat) (smax a n : expr)
| MApartBl (a n : expr) (bl : bklist)
| MOqH (l : nat) (k : nat)                (* [comment removed for export] *)
(* [comment removed for export] *)
| MHpr (j : nat) (blo bln : bklist) (args : list expr) (ok : list (expr * expr)).

Fixpoint ws_eqb (a b : list (expr * expr)) : bool :=
  match a, b with
  | [], [] => true
  | (l, h) :: a', (l', h') :: b' => expr_eqb l l' && expr_eqb h h' && ws_eqb a' b'
  | _, _ => false
  end.

Definition mfact_eqb (x y : mfact) : bool :=
  match x, y with
  | MRw a cs, MRw b ds => expr_eqb a b && cells_eqb cs ds
  | MRo a cs, MRo b ds => expr_eqb a b && cells_eqb cs ds
  | MBy a n k, MBy b m j => expr_eqb a b && expr_eqb n m && Pos.eqb k j
  | MStk a b, MStk c d => expr_eqb a c && expr_eqb b d
  | MAobj a n, MAobj b m => expr_eqb a b && expr_eqb n m
  | MOpq k ok sh, MOpq k' ok' sh' => Nat.eqb k k' && ws_eqb ok ok' && ws_eqb sh sh'
  | MArr a w l n wr, MArr a' w' l' n' wr' => expr_eqb a a' && N.eqb w w' && lexpr_eqb l l' && expr_eqb n n' && Bool.eqb wr wr'
  | MMunch W i j, MMunch W' i' j' => ws_eqb W W' && Nat.eqb i i' && Nat.eqb j j'
  | MWmono i j, MWmono i' j' => Nat.eqb i i' && Nat.eqb j j'
  | MLaw l X i j, MLaw l' X' i' j' => Nat.eqb l l' && ws_eqb X X' && Nat.eqb i i' && Nat.eqb j j'
  | MCli l a n, MCli l' a' n' => Nat.eqb l l' && expr_eqb a a' && expr_eqb n n'
  | MCobj l a n, MCobj l' a' n' => Nat.eqb l l' && expr_eqb a a' && expr_eqb n n'
  | MHeap bl ok, MHeap bl' ok' => bklist_eqb bl bl' && ws_eqb ok ok'
  | MLawH l bl sp X i j, MLawH l' bl' sp' X' i' j' => Nat.eqb l l' && bklist_eqb bl bl' && expr_eqb sp sp' && ws_eqb X X' && Nat.eqb i i' && Nat.eqb j j'
  | MCliH l s a n, MCliH l' s' a' n' => Nat.eqb l l' && expr_eqb s s' && expr_eqb a a' && expr_eqb n n'
  | MApartBl a n bl, MApartBl a' n' bl' => expr_eqb a a' && expr_eqb n n' && bklist_eqb bl bl'
  | MOqH l k, MOqH l' k' => Nat.eqb l l' && Nat.eqb k k'
  | MHpr j o n xs ok, MHpr j' o' n' xs' ok' => Nat.eqb j j' && bklist_eqb o o' && bklist_eqb n n' && exprs_eqb xs xs' && ws_eqb ok ok'
  | _, _ => false
  end.

Fixpoint mf_mem (f : mfact) (l : list mfact) : bool :=
  match l with [] => false | g :: l' => mfact_eqb f g || mf_mem f l' end.

Definition mf_inter (a b : list mfact) : list mfact := filter (fun f => mf_mem f b) a.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record acfg := ACFG { ac_sb : expr; ac_img_lo : Z; ac_img_hi : Z; ac_got : Z; ac_gsb : Z }.

Record lxcfg := LXC {
  c_acc : option acfg
}.

(* [comment removed for export] *)
Inductive spc : Set := PCz (z : Z) | PCret (r : sreg).

Record sstate := SSTX {
  s_pc : spc;
  s_rs : list sreg;               (* [comment removed for export] *)
  s_mf : list mfact;
  s_pf : list pfact;
  s_W : list (expr * expr);       (* [comment removed for export] *)
  s_nx : positive;               (* [comment removed for export] *)
  s_same : bool;                  (* [comment removed for export] *)
  s_ref : nat;                    (* [comment removed for export] *)
  s_nm : nat;                     (* [comment removed for export] *)
  s_nl : positive;                (* [comment removed for export] *)
  s_bl : bklist                    (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition SST (pc : spc) (rs : list sreg) (mf : list mfact) (pf : list pfact) (W : list (expr * expr)) (nx : positive) (same : bool) : sstate :=
  SSTX pc rs mf pf W nx same 0 1 1 BL0.
Definition SSTN (pc : spc) (rs : list sreg) (mf : list mfact) (pf : list pfact) (W : list (expr * expr)) (nx : positive) (same : bool) (nl : positive) : sstate :=
  SSTX pc rs mf pf W nx same 0 1 nl BL0.

Definition s_pcz (ss : sstate) : option Z :=
  match s_pc ss with PCz z => Some z | _ => None end.

(* [comment removed for export] *)
Fixpoint lget {A} (l : list A) (n : nat) (d : A) : A :=
  match l, n with
  | [], _ => d
  | x :: _, O => x
  | _ :: l', S n' => lget l' n' d
  end.

Fixpoint lset {A} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', S n' => y :: lset l' n' x
  end.

(* [comment removed for export] *)
Definition rd_reg (ss : sstate) (r : Z) : sreg :=
  if Z.eqb r 0 then RZ (ELit 0) else lget (s_rs ss) (Z.to_nat (r - 1)) (RZ (ELit 0)).

Definition rd_expr (ss : sstate) (r : Z) : expr := expr_of_reg (rd_reg ss r).

Definition wr_reg (ss : sstate) (r : Z) (v : sreg) : sstate :=
  if Z.eqb r 0 then ss
  else SSTX (s_pc ss) (lset (s_rs ss) (Z.to_nat (r - 1)) v) (s_mf ss) (s_pf ss) (s_W ss) (s_nx ss) (s_same ss) (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

Definition set_pc (ss : sstate) (p : spc) : sstate :=
  SSTX p (s_rs ss) (s_mf ss) (s_pf ss) (s_W ss) (s_nx ss) (s_same ss) (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

Definition add_pf (ss : sstate) (f : pfact) : sstate :=
  SSTX (s_pc ss) (s_rs ss) (s_mf ss) (pf_add f (s_pf ss)) (s_W ss) (s_nx ss) (s_same ss) (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

Definition add_pfs (ss : sstate) (fs : list pfact) : sstate :=
  fold_left add_pf fs ss.

Definition set_mf (ss : sstate) (mf : list mfact) : sstate :=
  SSTX (s_pc ss) (s_rs ss) mf (s_pf ss) (s_W ss) (s_nx ss) (s_same ss) (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

Definition set_pf (ss : sstate) (pf : list pfact) : sstate :=
  SSTX (s_pc ss) (s_rs ss) (s_mf ss) pf (s_W ss) (s_nx ss) (s_same ss) (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

Definition bump (ss : sstate) : sstate :=
  SSTX (s_pc ss) (s_rs ss) (s_mf ss) (s_pf ss) (s_W ss) (Pos.succ (s_nx ss)) (s_same ss) (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

(* [comment removed for export] *)
Definition set_W (ss : sstate) (W : list (expr * expr)) : sstate :=
  SSTX (s_pc ss) (s_rs ss) (s_mf ss) (s_pf ss) W (s_nx ss) false (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

Definition oracle_of (ss : sstate) : oracle := mk_oracle (s_pf ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint evars_lt (n : positive) (e : expr) : bool :=
  match e with
  | ELit _ | EUv _ => true
  | EZv i => Pos.ltb i n
  | EAdd a b | EOp _ a b => evars_lt n a && evars_lt n b
  | EMulC _ a => evars_lt n a
  end.

Definition rvars_lt (n : positive) (r : sreg) : bool :=
  match r with RW _ => true | RZ e => evars_lt n e end.

Fixpoint cvars_lt (n : positive) (c : cellx) : bool :=
  match c with XZ _ e => evars_lt n e | XSl c _ _ => cvars_lt n c | XRep _ e => evars_lt n e | _ => true end.

Fixpoint lvars_lt (n : positive) (l : lexpr) : bool :=
  match l with LBase _ => true | LUpd l i _ v => lvars_lt n l && evars_lt n i && evars_lt n v end.

Fixpoint blvars_lt (n : positive) (bl : bklist) : bool :=
  match bl with BL0 | BLV _ => true | BCons a m bl' => evars_lt n a && evars_lt n m && blvars_lt n bl' end.
Definition mfvars_lt (n : positive) (f : mfact) : bool :=
  match f with
  | MRw a cs | MRo a cs => evars_lt n a && forallb (cvars_lt n) cs
  | MBy a m _ => evars_lt n a && evars_lt n m
  | MStk a b | MAobj a b => evars_lt n a && evars_lt n b
  | MOpq _ ok sh => forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) (ok ++ sh)
  | MArr a _ l m _ => evars_lt n a && lvars_lt n l && evars_lt n m
  | MMunch W _ _ | MLaw _ W _ _ => forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) W
  | MWmono _ _ => true
  | MCli _ a b | MCobj _ a b => evars_lt n a && evars_lt n b
  | MHeap bl ok => blvars_lt n bl && forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) ok
  | MLawH _ bl sp X _ _ => blvars_lt n bl && evars_lt n sp && forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) X
  | MCliH _ s a b => evars_lt n s && evars_lt n a && evars_lt n b
  | MApartBl a b bl => evars_lt n a && evars_lt n b && blvars_lt n bl
  | MOqH _ _ => true
  | MHpr _ o b xs ok => blvars_lt n o && blvars_lt n b && forallb (evars_lt n) xs && forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) ok
  end.

Definition pfvars_lt (n : positive) (f : pfact) : bool :=
  match f with
  | FGe e => evars_lt n e
  | FSep a b c d => evars_lt n a && evars_lt n b && evars_lt n c && evars_lt n d
  | FSep0 z a b c d => evars_lt n z && evars_lt n a && evars_lt n b && evars_lt n c && evars_lt n d
  | FAl a _ => evars_lt n a
  | FCr a b => evars_lt n a && evars_lt n b
  | FShb v c oa on => Pos.ltb v n && evars_lt n c && evars_lt n oa && evars_lt n on
  | FLe a b | FLt a b | FEq a b => evars_lt n a && evars_lt n b
  | FOr2 a b c d => evars_lt n a && evars_lt n b && evars_lt n c && evars_lt n d
  | FOr3z z a b c d => evars_lt n z && evars_lt n a && evars_lt n b && evars_lt n c && evars_lt n d
  | FProp _ xs => forallb (evars_lt n) xs
  end.

(* [comment removed for export] *)
Fixpoint llvars_lt (b : positive) (l : lexpr) : bool :=
  match l with LBase k => Pos.ltb k b | LUpd l _ _ _ => llvars_lt b l end.
Definition mflvars_lt (b : positive) (f : mfact) : bool :=
  match f with MArr _ _ l _ _ => llvars_lt b l | _ => true end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint blrefs_lt (b : nat) (bl : bklist) : bool :=
  match bl with BL0 => true | BLV k => Nat.ltb k b | BCons _ _ bl' => blrefs_lt b bl' end.
Definition mrefs_lt (b : nat) (f : mfact) : bool :=
  match f with
  | MMunch _ i j | MWmono i j | MLaw _ _ i j => Nat.ltb i b && Nat.ltb j b
  | MLawH _ bl _ _ i j => Nat.ltb i b && Nat.ltb j b && blrefs_lt b bl
  | MHeap bl _ => blrefs_lt b bl
  | MApartBl _ _ bl => blrefs_lt b bl
  | MHpr _ o n _ _ => blrefs_lt b o && blrefs_lt b n
  | _ => true
  end.
(* [comment removed for export] *)
Definition mrefs_ok (ss : sstate) : bool := Nat.eqb (s_ref ss) 0 && forallb (mrefs_lt 1) (s_mf ss).
(* [comment removed for export] *)
Definition lrefs_ok (nl0 : positive) (ss : sstate) : bool := Pos.eqb (s_nl ss) nl0 && forallb (mflvars_lt nl0) (s_mf ss).

Definition pcvars_lt (n : positive) (p : spc) : bool :=
  match p with PCz _ => true | PCret r => rvars_lt n r end.

Definition ss_wf (C : lxcfg) (ss : sstate) : bool :=
  let n := s_nx ss in
  pcvars_lt n (s_pc ss) && forallb (rvars_lt n) (s_rs ss)
  && forallb (mfvars_lt n) (s_mf ss) && forallb (pfvars_lt n) (s_pf ss)
  && forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) (s_W ss)
  && match c_acc C with Some A => evars_lt n (ac_sb A) | None => true end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_shr3 (ts : terms) : option (expr * terms) :=
  match ts with
  | [] => None
  | (1, (EOp OShr x (ELit 3))) :: ts' => Some (x, ts')
  | t :: ts' => match find_shr3 ts' with Some (x, r) => Some (x, t :: r) | None => None end
  end.

(* [comment removed for export] *)
Definition shadow_split (sb : expr) (a : expr) : option (expr * expr) :=
  let '(ts, k) := lin_of a in
  match find_shr3 ts with
  | Some (x, rest) =>
      let r := eadd (of_terms rest k) (emulc (-1) sb) in
      if any_mem (atoms_of_list [sb] []) (atoms_of_list [r] []) then None else Some (x, r)
  | None =>
      (* [comment removed for export] *)
      match is_lit (eadd a (emulc (-1) sb)) with
      | Some kk => Some (ELit (8 * kk), ELit 0)
      | None => None
      end
  end.

Definition sh_c (x r : expr) : expr := eadd x (emulc 8 r).

(* [comment removed for export] *)
Fixpoint cranges (pf : list pfact) (mf : list mfact) : list (expr * expr) :=
  match pf with
  | FCr a n :: pf' => (a, n) :: cranges pf' mf
  | _ :: pf' => cranges pf' mf
  | [] => (fix g (mf : list mfact) : list (expr * expr) :=
             match mf with
             | [] => []
             | MAobj a n :: mf' => (a, n) :: g mf'
             | _ :: mf' => g mf'
             end) mf
  end.

Definition in_some_crange (pf : list pfact) (crs : list (expr * expr)) (a n : expr) : bool :=
  (* [comment removed for export] *)
  if any_iv (fun b k => iv_inside_syn a n b k) crs then true
  else if any_iv (fun b k => dec_inside0 pf a n b k) crs then true
  else if any_iv (fun b k => dec_inside1 pf a n b k) crs then true
  else any_iv (fun b k => dec_insideX pf a n b k) crs.

Inductive acls : Set := AcClient | AcShadow | AcImg.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition acc_client_img (A : acfg) (ss : sstate) (crs : list (expr * expr)) (a : expr) (w : Z) : option acls :=
  if in_some_crange (s_pf ss) crs a (ELit w) then Some AcClient
  else if e_in (oracle_of ss) a (ac_img_lo A) (ac_img_hi A - w) then Some AcImg else None.

Definition acc_class (C : lxcfg) (ss : sstate) (a : expr) (w : Z) : option acls :=
  match c_acc C with
  | None => Some AcClient     (* [comment removed for export] *)
  | Some A =>
      let pf := s_pf ss in
      let crs := cranges pf (s_mf ss) in
      (* [comment removed for export] *)
      match is_lit a with
      | Some z => if Z.leb (ac_img_lo A) z && Z.leb (z + w) (ac_img_hi A) then Some AcImg
                  else if in_some_crange pf crs a (ELit w) then Some AcClient
                  else (* [comment removed for export] *)
                    match shadow_split (ac_sb A) a with
                    | Some (x, kr) =>
                        let c := sh_c x kr in
                        if (if Z.eqb w 1 then in_some_crange pf crs c (ELit 1)
                            else if N.leb 3 (eal (oracle_of ss) x) then in_some_crange pf crs c (ELit (8 * (w - 1) + 1)) else false)
                        then Some AcShadow else None
                    | None => None
                    end
      | None =>
          match shadow_split (ac_sb A) a with
          | Some (x, kr) =>
              let c := sh_c x kr in
              if (if Z.eqb w 1 then in_some_crange pf crs c (ELit 1)
                  else if N.leb 3 (eal (oracle_of ss) x) then in_some_crange pf crs c (ELit (8 * (w - 1) + 1)) else false)
              then Some AcShadow
              else acc_client_img A ss crs a w   (* [comment removed for export] *)
          | None => acc_client_img A ss crs a w
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive lres : Set :=
| LReg (r : sreg)                  (* [comment removed for export] *)
| LFresh (lo hi : Z)              (* [comment removed for export] *)
| LShb (c : expr) (oa on : expr) (* [comment removed for export] *)
| LNone.

(* [comment removed for export] *)
Definition okw (w : N) : bool :=
  match w with 1%N | 2%N | 4%N | 8%N => true | _ => false end.

(* [comment removed for export] *)
Definition zslice (z : Z) (o l : N) : Z := (z mod 2 ^ 64 / 2 ^ (8 * Z.of_N o)) mod 2 ^ (8 * Z.of_N l).

Definition mk_slice2 (b : cellx) (o l : N) : cellx :=
  match b with
  | XZ n (ELit z) => if okw n && okw l then XZ l (ELit (zslice z o l)) else XSl b o l
  | XRep n e => if N.leb (o + l) n then XRep l e else XSl b o l     (* [comment removed for export] *)
  | _ => XSl b o l
  end.

Definition mk_slice (c : cellx) (o l : N) : cellx :=
  if N.eqb o 0 && N.eqb l (cellx_size c) then c else
  match c with
  | XSl c' o' _ => mk_slice2 c' (o' + o) l
  | _ => mk_slice2 c o l
  end.

(* [comment removed for export] *)
Fixpoint cell_lookup (cs : list cellx) (off : Z) (w : N) : option cellx :=
  match cs with
  | [] => None
  | c :: cs' =>
      let n := Z.of_N (cellx_size c) in
      if Z.ltb off n then
        (if Z.eqb off 0 && N.eqb (cellx_size c) w then Some c
         else if Z.leb (off + Z.of_N w) n then Some (mk_slice c (Z.to_N off) w)
         else None (* [comment removed for export] *))
      else cell_lookup cs' (off - n) w
  end.

(* [comment removed for export] *)
Fixpoint cut_cells (cs : list cellx) (p lo hi : Z) : list cellx * list cellx :=
  match cs with
  | [] => ([], [])
  | c :: cs' =>
      let n := Z.of_N (cellx_size c) in
      let '(bef, aft) := cut_cells cs' (p + n) lo hi in
      ((if Z.ltb p lo then (if Z.leb (p + n) lo then c else mk_slice c 0 (Z.to_N (lo - p))) :: bef else bef),
       (if Z.ltb hi (p + n) then (if Z.leb hi p then c else mk_slice c (Z.to_N (hi - p)) (Z.to_N (p + n - hi))) :: aft else aft))
  end.

Definition fresh_range (w : N) (sx : bool) : lres :=
  let bits := 8 * Z.of_N w in
  if sx then LFresh (- 2 ^ (bits - 1)) (2 ^ (bits - 1) - 1) else LFresh 0 (2 ^ bits - 1).

Definition cell_value (O : oracle) (c : cellx) (sx : bool) : lres :=
  match c with
  | XW i => LReg (RW i)
  | XZ 8%N e => LReg (mkreg e)
  | XZ w e => if okw w then
                let bits := 8 * Z.of_N w in
                LReg (RZ (if sx then esx O (elow O e bits) bits else elow O e bits))
              else LNone
  | XB w _ => if okw w then fresh_range w sx else LNone
  | XWn w i => match w with
               | 2%N | 4%N => let bits := 8 * Z.of_N w in
                              LReg (RZ (if sx then esx O (elow O (EUv i) bits) bits else elow O (EUv i) bits))
               | _ => LNone
               end
  | XSl _ _ w => if okw w then fresh_range w sx else LNone
  | XRep w _ => if okw w then fresh_range w sx else LNone     (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Fixpoint terms_shr (O : oracle) (k : Z) (ts : terms) : option terms :=
  match ts with
  | [] => Some []
  | (co, a) :: ts' =>
      match terms_shr O k ts' with
      | None => None
      | Some r =>
          if Z.eqb (co mod 2 ^ k) 0 then Some ((co / 2 ^ k, a) :: r)
          else if N.leb (Z.to_N k) (eal O a) then Some ((co, EOp OShr (eatom a) (ELit k)) :: r)   (* [comment removed for export] *)
          else None
      end
  end.

Fixpoint sum_terms (ts : terms) (c : expr) : expr :=
  match ts with [] => c | (co, a) :: ts' => eadd (emulc co (eatom a)) (sum_terms ts' c) end.

Definition canon_atom (O : oracle) (a : expr) : expr :=
  match a with
  | EOp OShr y (ELit k) =>
      if Z.ltb 0 k then
        let '(ys, c) := lin_of y in
        match ys with
        | [] => eatom a
        | _ => match terms_shr O k ys with
               | Some ys' => sum_terms ys' (ELit (Z.shiftr c k))
               | None => eatom a
               end
        end
      else eatom a
  | _ => eatom a
  end.

Fixpoint canon_terms (O : oracle) (ts : terms) (acc : expr) : expr :=
  match ts with
  | [] => acc
  | (co, a) :: ts' => canon_terms O ts' (eadd (emulc co (canon_atom O a)) acc)
  end.

Definition shr_canon (O : oracle) (e : expr) : expr :=
  let '(ts, c) := lin_of e in canon_terms O ts (ELit c).

(* [comment removed for export] *)
Definition ediff_litO (O : oracle) (a b : expr) : option Z :=
  match ediff_lit a b with
  | Some z => Some z
  | None => ediff_lit (shr_canon O a) (shr_canon O b)
  end.

Fixpoint load_chunks (O : oracle) (mf : list mfact) (a : expr) (w : N) (sx : bool) : option lres :=
  match mf with
  | [] => None
  | f :: mf' =>
      let try_cells (base : expr) (cs : list cellx) :=
          match ediff_litO O a base with
          | Some off =>
              if Z.leb 0 off && Z.leb (off + Z.of_N w) (Z.of_N (cells_sizeN cs)) then
                match cell_lookup cs off w with
                | Some c => Some (cell_value O c sx)
                | None => Some LNone          (* [comment removed for export] *)
                end
              else load_chunks O mf' a w sx
          | None => load_chunks O mf' a w sx
          end in
      match f with
      | MRw base cs | MRo base cs => try_cells base cs
      | _ => load_chunks O mf' a w sx
      end
  end.

(* [comment removed for export] *)
Fixpoint load_other (din : list pfact -> expr -> expr -> expr -> expr -> bool)
         (C : lxcfg) (pf : list pfact) (O : oracle) (mf : list mfact) (all : list mfact)
         (a : expr) (w : N) (sx : bool) : lres :=
  match mf with
  | [] => LNone
  | MBy base n k :: mf' =>
      if (if okw w then din pf a (ELit (Z.of_N w)) base n else false) then fresh_range w sx
      else load_other din C pf O mf' all a w sx
  | MStk lo hi :: mf' =>
      if (if okw w then din pf a (ELit (Z.of_N w)) lo (esub hi lo) else false) then fresh_range w sx
      else load_other din C pf O mf' all a w sx
  | MAobj oa on :: mf' =>
      match c_acc C, w with
      | Some A, 1%N =>
          match shadow_split (ac_sb A) a with
          | Some (x, kr) =>
              let c := sh_c x kr in
              (* [comment removed for export] *)
              if (if N.leb 3 (eal O c) then din pf c (ELit 8) oa on else false) then LReg (RZ (ELit 0))
              else if din pf c (ELit 1) oa on then LShb c oa on
              else load_other din C pf O mf' all a w sx
          | None => load_other din C pf O mf' all a w sx
          end
      | _, _ => load_other din C pf O mf' all a w sx
      end
  | MArr b wd _ n _ :: mf' =>
      (* [comment removed for export] *)
      if (if okw w then din pf a (ELit (Z.of_N w)) b (emulc (Z.of_N wd) n) else false) then fresh_range w sx
      else load_other din C pf O mf' all a w sx
  | _ :: mf' => load_other din C pf O mf' all a w sx
  end.

(* [comment removed for export] *)
Definition sym_load (C : lxcfg) (ss : sstate) (a : expr) (w : N) (sx : bool) : lres :=
  let O := oracle_of ss in
  match load_chunks O (s_mf ss) a w sx with
  | Some r => r
  | None =>
      match load_other dec_inside1 C (s_pf ss) O (s_mf ss) (s_mf ss) a w sx with
      | LNone => load_other dec_insideX C (s_pf ss) O (s_mf ss) (s_mf ss) a w sx
      | r => r
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cell_store (cs : list cellx) (off : Z) (c : cellx) : option (list cellx) :=
  if Z.leb 0 off && Z.leb (off + Z.of_N (cellx_size c)) (Z.of_N (cells_sizeN cs)) then
    let '(bef, aft) := cut_cells cs 0 off (off + Z.of_N (cellx_size c)) in Some (bef ++ c :: aft)
  else None.

Definition store_cell (w : N) (v : sreg) : cellx :=
  match w, v with
  | 8%N, RW i => XW i
  | _, _ => XZ w (expr_of_reg v)
  end.

(* [comment removed for export] *)
Definition is_static (C : lxcfg) (b : expr) : bool :=
  match c_acc C, is_lit b with
  | Some A, Some z => Z.eqb z (ac_got A) || Z.eqb z (ac_gsb A)
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition class_apart (C : lxcfg) (pf : list pfact) (crs : list (expr * expr)) (cl : acls) (b n : expr) : bool :=
  match c_acc C, cl with
  | Some _, AcShadow => in_some_crange pf crs b n
  | Some A, AcClient =>
      match shadow_split (ac_sb A) b with
      | Some (x, kr) => if N.leb 3 (eal (mk_oracle pf) x) then in_some_crange pf crs (sh_c x kr) (emulc 8 n) else false
      | None => false
      end
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition opq_in (test : expr -> expr -> expr -> expr -> bool) (a n : expr) (ivs : list (expr * expr)) : bool :=
  any_iv (fun lo hi => test a n lo (eadd hi (emulc (-1) lo))) ivs.

Definition opq_sh_ok (C : lxcfg) (pf : list pfact) (crs : list (expr * expr)) (a n : expr)
           (test : expr -> expr -> expr -> expr -> bool) (sh : list (expr * expr)) : bool :=
  match c_acc C with
  | Some A =>
      match shadow_split (ac_sb A) a with
      | Some (x, kr) =>
          let c := sh_c x kr in let cn := emulc 8 n in
          if N.leb 3 (eal (mk_oracle pf) x) then (if opq_in test c cn sh then in_some_crange pf crs c cn else false) else false
      | None => false
      end
  | None => false
  end.

Definition opq_iv_ok (C : lxcfg) (pf : list pfact) (crs : list (expr * expr)) (a n : expr) (ok sh : list (expr * expr)) : bool :=
  if opq_in (fun a n b k => iv_inside_syn a n b k) a n ok then true
  else if opq_sh_ok C pf crs a n (fun a n b k => iv_inside_syn a n b k) sh then true
  else if opq_in (dec_inside0 pf) a n ok then true
  else if opq_sh_ok C pf crs a n (dec_inside0 pf) sh then true
  else if opq_in (dec_inside pf) a n ok then true
  else opq_sh_ok C pf crs a n (dec_inside pf) sh.

(* [comment removed for export] *)
Fixpoint bl_covers (pf : list pfact) (bl : bklist) (b n : expr) : bool :=
  match bl with
  | BL0 | BLV _ => false
  | BCons a k bl' => if iv_inside_syn b n a k then true else if dec_inside pf b n a k then true else bl_covers pf bl' b n
  end.
(* [comment removed for export] *)
Fixpoint apart_covers (pf : list pfact) (mf : list mfact) (s : bklist) (b n : expr) : bool :=
  match mf with
  | [] => false
  | MApartBl a k bl' :: mf' =>
      if (if bl_suffix s bl' then (if iv_inside_syn b n a k then true else dec_inside pf b n a k) else false) then true
      else apart_covers pf mf' s b n
  | _ :: mf' => apart_covers pf mf' s b n
  end.
(* [comment removed for export] *)
Definition ivs_cover (pf : list pfact) (b n : expr) (ok : list (expr * expr)) : bool :=
  if opq_in (fun a n b k => iv_inside_syn a n b k) b n ok then true
  else if opq_in (dec_inside0 pf) b n ok then true
  else opq_in (dec_inside pf) b n ok.
(* [comment removed for export] *)
Definition hpr_iv_ok (pf : list pfact) (mf : list mfact) (blo bln : bklist) (ok : list (expr * expr)) (b n : expr) : bool :=
  if ivs_cover pf b n ok then true else if bl_covers pf blo b n then true else apart_covers pf mf bln b n.

(* [comment removed for export] *)
Definition shadow_apart (A : acfg) (pf : list pfact) (a : expr) (w : Z) (oa on : expr) : bool :=
  match shadow_split (ac_sb A) a with
  | Some (x, kr) =>
      if N.leb 3 (eal (mk_oracle pf) x) then
      (let G := sh_c x kr in
       if sep_lookup true pf G (ELit (8 * w)) oa on then true else
       let goals := [emulc (-1) on; sep_l G (ELit (8 * w)) oa; sep_r G oa on] in
       if lin_ge_list pf goals then true else lin_ge_listX pf goals) else false
  | None => false
  end.

Definition mf_survives (C : lxcfg) (pf : list pfact) (crs : list (expr * expr)) (mf : list mfact) (cl : acls) (a : expr) (w : Z) (f : mfact) : bool :=
  match f with
  | MRw b cs => let n := Z.of_N (cells_sizeN cs) in
                (* [comment removed for export] *)
                if (if Z.ltb 0 n then class_apart C pf crs cl b (ELit n) else false) then true else dec_apart pf a (ELit w) b (ELit n)
  | MRo b cs => let n := Z.of_N (cells_sizeN cs) in
                if (match cl with AcImg => false | _ => is_static C b && N.eqb (cells_sizeN cs) 8 end) then true
                else if (if Z.ltb 0 n then class_apart C pf crs cl b (ELit n) else false) then true
                else dec_apart pf a (ELit w) b (ELit n)
  | MBy b n _ => if sep_lookup true pf a (ELit w) b n then true
                 else if class_apart C pf crs cl b n then true
                 else if lin_ge_list pf [emulc (-1) n; sep_l a (ELit w) b; sep_r a b n] then true   (* [comment removed for export] *)
                 else lin_ge_listX pf [emulc (-1) n; sep_l a (ELit w) b; sep_r a b n]
  | MStk lo hi => true    (* [comment removed for export] *)
  | MAobj oa on =>
      (* [comment removed for export] *)
      match c_acc C, cl with
      | Some _, AcClient => true
      | Some A, AcShadow => shadow_apart A pf a w oa on
      | _, _ => false
      end
  | MOpq _ ok sh => opq_iv_ok C pf crs a (ELit w) ok sh
  | MArr b wd _ n _ =>
      let sz := emulc (Z.of_N wd) n in
      if sep_lookup true pf a (ELit w) b sz then true
      else if class_apart C pf crs cl b sz then true
      else if lin_ge_list pf [emulc (-1) n; sep_l a (ELit w) b; sep_r a b sz] then true   (* [comment removed for export] *)
      else lin_ge_listX pf [emulc (-1) n; sep_l a (ELit w) b; sep_r a b sz]
  (* [comment removed for export] *)
  | MHeap bl ok => if opq_iv_ok C pf crs a (ELit w) ok [] then true else bl_covers pf bl a (ELit w)
  | MHpr _ blo bln _ ok => hpr_iv_ok pf mf blo bln ok a (ELit w)
  (* [comment removed for export] *)
  | MMunch _ _ _ | MWmono _ _ | MLaw _ _ _ _ | MCli _ _ _ | MCobj _ _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ => true
  end.

Inductive sres_store : Set :=
| StOk (mf' : list mfact) (W' : list (expr * expr))
| StFail (code : Z).

(* [comment removed for export] *)
Fixpoint w_add (pf : list pfact) (W : list (expr * expr)) (a b : expr) : list (expr * expr) :=
  match W with
  | [] => [(a, b)]
  | (l, h) :: W' =>
      (* [comment removed for export] *)
      if (if dec_le00 pf l a then dec_le00 pf b h else false) then (l, h) :: W'
      else if (if expr_eqb b l then dec_le00 pf l h else false) then (a, h) :: W'
      else if (if expr_eqb h a then dec_le00 pf l h else false) then (l, b) :: W'
      else (l, h) :: w_add pf W' a b
  end.

(* [comment removed for export] *)
Definition cell_expr_of (c : cellx) : option expr :=
  match c with
  | XW i => Some (eatom (EUv i))
  | XZ _ e => Some e
  | _ => None
  end.

(* [comment removed for export] *)
Definition wlog (w : Z) : Z := match w with 2 => 1 | 4 => 2 | 8 => 3 | _ => 0 end.

Fixpoint terms_divc (O : oracle) (w : Z) (ts : terms) : option terms :=
  match ts with
  | [] => Some []
  | (k, a) :: ts' =>
      if Z.eqb (k mod w) 0 then
        match terms_divc O w ts' with Some r => Some ((k / w, a) :: r) | None => None end
      else if Z.ltb 0 (wlog w) && N.leb (Z.to_N (wlog w)) (eal O a) then
        match terms_divc O w ts' with Some r => Some ((k, EOp OShr a (ELit (wlog w))) :: r) | None => None end
      else None
  end.

Definition ediv_exact (O : oracle) (w : N) (d : expr) : option expr :=
  let wz := Z.of_N w in
  if Z.eqb wz 1 then Some d else
  if Z.leb wz 0 then None else
  let '(ts, c) := lin_of d in
  if Z.eqb (c mod wz) 0 then
    match terms_divc O wz ts with Some ts' => Some (of_terms ts' (c / wz)) | None => None end
  else None.

(* [comment removed for export] *)
Definition arr_store (pf : list pfact) (a : expr) (w : N) (c : cellx) (b : expr) (wd : N) (l : lexpr) (n : expr)
  : option mfact :=
  match cell_expr_of c with
  | None => None
  | Some v =>
      if N.eqb wd 1 then
        let i := esub a b in
        if dec_inside pf i (ELit (Z.of_N w)) (ELit 0) n then Some (MArr b wd (LUpd l i w v) n true) else None
      else if N.eqb w wd then
        match ediv_exact (mk_oracle pf) wd (esub a b) with
        | Some i => if dec_inside pf i (ELit 1) (ELit 0) n then Some (MArr b wd (LUpd l i w v) n true) else None
        | None => None
        end
      (* [comment removed for export] *)
      else if N.eqb w 8 && N.eqb wd 4 then
        match ediv_exact (mk_oracle pf) 4 (esub a b) with
        | Some i => if dec_inside pf i (ELit 2) (ELit 0) n
                    then Some (MArr b wd (LUpd (LUpd l i 4 v) (eadd i (ELit 1)) 4 (eshr (mk_oracle pf) v 32)) n true) else None
        | None => None
        end
      else None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_hit (pf : list pfact) (a : expr) (w : N) (c : cellx) (f : mfact) : option (option (list mfact)) :=
  match f with
  | MArr b wd l n true =>
      match arr_store pf a w c b wd l n with
      | Some f' => Some (Some [f'])
      | None => None
      end
  | MRw base cs =>
      match ediff_litO (mk_oracle pf) a base with
      | Some off =>
          if Z.leb 0 off && Z.leb (off + Z.of_N w) (Z.of_N (cells_sizeN cs)) then
            match cell_store cs off c with
            | Some cs' => Some (Some [MRw base cs'])
            | None => Some None
            end
          else None
      | None => None
      end
  | MStk lo hi =>
      (* [comment removed for export] *)
      if dec_inside pf a (ELit (Z.of_N w)) lo (eadd hi (emulc (-1) lo)) then
        Some (Some [MRw a [c]; MStk lo a; MStk (eadd a (ELit (Z.of_N w))) hi])
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint store_target_pass (chunks : bool) (pf : list pfact) (mf : list mfact) (a : expr) (w : N) (c : cellx)
         : option (list mfact * list mfact) :=
  match mf with
  | [] => None
  | f :: mf' =>
      if Bool.eqb chunks (match f with MRw _ _ => true | _ => false end) then
        match store_hit pf a w c f with
        | Some (Some t) => Some (t, mf')
        | Some None => None
        | None => match store_target_pass chunks pf mf' a w c with
                  | Some (t, rest) => Some (t, f :: rest)
                  | None => None
                  end
        end
      else match store_target_pass chunks pf mf' a w c with
           | Some (t, rest) => Some (t, f :: rest)
           | None => None
           end
  end.

Definition store_target (pf : list pfact) (mf : list mfact) (a : expr) (w : N) (c : cellx)
  : option (list mfact * list mfact) :=
  match store_target_pass true pf mf a w c with
  | Some r => Some r
  | None => store_target_pass false pf mf a w c
  end.

(* [comment removed for export] *)
Definition mstk_empty (f : mfact) : bool :=
  match f with MStk a b => expr_eqb a b | _ => false end.

Fixpoint take_rw_at (b : expr) (mf : list mfact) : option (list cellx * list mfact) :=
  match mf with
  | [] => None
  | f :: mf' =>
      match f with
      | MRw b' cs => if expr_eqb b b' then Some (cs, mf')
                     else match take_rw_at b mf' with Some (ds, r) => Some (ds, f :: r) | None => None end
      | _ => match take_rw_at b mf' with Some (ds, r) => Some (ds, f :: r) | None => None end
      end
  end.

(* [comment removed for export] *)
Fixpoint take_rw_ending (a : expr) (mf : list mfact) : option (expr * list cellx * list mfact) :=
  match mf with
  | [] => None
  | f :: mf' =>
      match f with
      | MRw b cs => if expr_eqb (eadd b (ELit (Z.of_N (cells_sizeN cs)))) a then Some (b, cs, mf')
                    else match take_rw_ending a mf' with Some (b', ds, r) => Some (b', ds, f :: r) | None => None end
      | _ => match take_rw_ending a mf' with Some (b', ds, r) => Some (b', ds, f :: r) | None => None end
      end
  end.

Definition coalesce (f : mfact) (rest : list mfact) : list mfact :=
  match f with
  | MRw a cs =>
      let '(a1, cs1, rest1) :=
        match take_rw_at (eadd a (ELit (Z.of_N (cells_sizeN cs)))) rest with
        | Some (ds, r) => (a, cs ++ ds, r)
        | None => (a, cs, rest)
        end in
      match take_rw_ending a1 rest1 with
      | Some (b, ds, r) => MRw b (ds ++ cs1) :: r
      | None => MRw a1 cs1 :: rest1
      end
  | _ => f :: rest
  end.

Definition tidy (mf : list mfact) : list mfact :=
  match filter (fun f => negb (mstk_empty f)) mf with
  | [] => []
  | f :: rest => coalesce f rest
  end.

Definition sym_store (C : lxcfg) (cl : acls) (ss : sstate) (a : expr) (w : N) (v : sreg) : sres_store :=
  let pf := s_pf ss in
  let wz := Z.of_N w in
  let crs := cranges pf (s_mf ss) in
  match store_target pf (s_mf ss) a w (store_cell w v) with
  | None => StFail 21 (* [comment removed for export] *)
  | Some (tgt, rest) => StOk (tidy (tgt ++ filter (mf_survives C pf crs (s_mf ss) cl a wz) rest)) (w_add pf (s_W ss) a (eadd a (ELit wz)))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition oplit (o : opk) (x y : Z) : Z :=
  match o with
  | OAnd => Z.land x y | OOr => Z.lor x y | OXor => Z.lxor x y | OShr => Z.shiftr x y | OMul => x * y
  | OLow => zlow y x | OSx => zswrap y x | OLtu => Z.b2z (Z.ltb x y) | OLts => Z.b2z (Z.ltb x y)
  | ODivU => x / y | ORemU => x mod y | OShl => Z.shiftl x y
  end.

Fixpoint enorm (e : expr) : expr :=
  match e with
  | ELit z => ELit z
  | EZv _ | EUv _ => eatom e
  | EAdd a b => eadd (enorm a) (enorm b)
  | EMulC c a => emulc c (enorm a)
  | EOp o a b => match enorm a, enorm b with
                 | ELit x, ELit y => ELit (oplit o x y)
                 | a', b' => eatom (EOp o a' b')
                 end
  end.

Definition norm_reg (r : sreg) : sreg :=
  match r with RW i => RW i | RZ e => mkreg (enorm e) end.

Definition norm_cell (c : cellx) : cellx :=
  match c with XZ w e => XZ w (enorm e) | XRep w e => XRep w (enorm e) | _ => c end.

Fixpoint norm_lexpr (l : lexpr) : lexpr :=
  match l with LBase k => LBase k | LUpd l i w v => LUpd (norm_lexpr l) (enorm i) w (enorm v) end.

Fixpoint norm_bl (bl : bklist) : bklist :=
  match bl with BL0 => BL0 | BLV k => BLV k | BCons a n bl' => BCons (enorm a) (enorm n) (norm_bl bl') end.
Definition norm_mf (f : mfact) : mfact :=
  match f with
  | MRw a cs => MRw (enorm a) (map norm_cell cs)
  | MRo a cs => MRo (enorm a) (map norm_cell cs)
  | MBy a n k => MBy (enorm a) (enorm n) k
  | MStk lo hi => MStk (enorm lo) (enorm hi)
  | MAobj a n => MAobj (enorm a) (enorm n)
  | MOpq k ok sh => MOpq k (map (fun lh => (enorm (fst lh), enorm (snd lh))) ok) (map (fun lh => (enorm (fst lh), enorm (snd lh))) sh)
  | MArr a w l n wr => MArr (enorm a) w (norm_lexpr l) (enorm n) wr
  | MMunch W i j => MMunch (map (fun lh => (enorm (fst lh), enorm (snd lh))) W) i j
  | MWmono i j => MWmono i j
  | MLaw l X i j => MLaw l (map (fun lh => (enorm (fst lh), enorm (snd lh))) X) i j
  | MCli l a n => MCli l (enorm a) (enorm n)
  | MCobj l a n => MCobj l (enorm a) (enorm n)
  | MHeap bl ok => MHeap (norm_bl bl) (map (fun lh => (enorm (fst lh), enorm (snd lh))) ok)
  | MLawH l bl sp X i j => MLawH l (norm_bl bl) (enorm sp) (map (fun lh => (enorm (fst lh), enorm (snd lh))) X) i j
  | MCliH l s a n => MCliH l (enorm s) (enorm a) (enorm n)
  | MApartBl a n bl => MApartBl (enorm a) (enorm n) (norm_bl bl)
  | MOqH l k => MOqH l k
  | MHpr j o b xs ok => MHpr j (norm_bl o) (norm_bl b) (map enorm xs) (map (fun lh => (enorm (fst lh), enorm (snd lh))) ok)
  end.

Definition norm_pf (f : pfact) : list pfact :=
  match f with
  | FGe e => [FGe (enorm e)]
  | FSep a n b k => [FSep (enorm a) (enorm n) (enorm b) (enorm k)]
  | FSep0 z a n b k => [FSep0 (enorm z) (enorm a) (enorm n) (enorm b) (enorm k)]
  | FAl a k =>
      (* [comment removed for export] *)
      match lin_of (enorm a) with
      | ([(1, b)], c) => if Z.eqb (c mod 2 ^ Z.of_N k) 0 then [FAl b k] else [FAl a k]
      | _ => [FAl a k]
      end
  | FCr a n => [FCr (enorm a) (enorm n)]
  | FShb v c oa on => [FShb v (enorm c) (enorm oa) (enorm on)]
  | FLe a b => [FGe (esub (enorm b) (enorm a))]
  | FLt a b => [FGe (eadd (esub (enorm b) (enorm a)) (ELit (-1)))]
  | FEq a b => [FGe (esub (enorm b) (enorm a)); FGe (esub (enorm a) (enorm b))]
  (* [comment removed for export] *)
  | FOr2 l1 r1 l2 r2 =>
      let a := enorm r2 in let b := enorm r1 in
      [FSep a (esub (enorm l1) a) b (esub (enorm l2) b)]
  | FOr3z z l1 r1 l2 r2 =>
      let a := enorm r2 in let b := enorm r1 in
      [FSep0 (enorm z) a (esub (enorm l1) a) b (esub (enorm l2) b)]
  | FProp j xs => [FProp j (map enorm xs)]
  end.

Definition norm_pc (p : spc) : spc :=
  match p with PCz z => PCz z | PCret r => PCret (norm_reg r) end.

(* [comment removed for export] *)
Definition pf_nodup (l : list pfact) : list pfact := fold_right pf_add [] l.

Definition norm_ss (ss : sstate) : sstate :=
  SSTX (norm_pc (s_pc ss)) (map norm_reg (s_rs ss)) (map norm_mf (s_mf ss)) (pf_nodup (flat_map norm_pf (s_pf ss)))
      (map (fun lh => (enorm (fst lh), enorm (snd lh))) (s_W ss)) (s_nx ss) (s_same ss) (s_ref ss) (s_nm ss) (s_nl ss) (s_bl ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint pv_idx (shift : N) (l : list (N * Z)) (ps : list N) : list N :=
  match l with
  | [] => ps
  | (i, _) :: l' => pv_idx shift l' (if N.leb shift i then (i - shift)%N :: ps else ps)
  end.
Fixpoint cert_used (c : cert) (shift : N) (acc : list N * list N) : list N * list N :=
  let addl := pv_idx shift in
  match c with
  | CFk l => (addl l (fst acc), snd acc)
  | CFkX cuts l =>
      let ps := fold_left (fun ps ct => addl (fst ct) ps) cuts (addl l (fst acc)) in (ps, snd acc)
  | CSp j cl cr => cert_used cl (shift + 1) (cert_used cr (shift + 1) (fst acc, j :: snd acc))
  | CSp0 j c0 cl cr => cert_used c0 (shift + 2) (cert_used cl (shift + 1) (cert_used cr (shift + 1) (fst acc, j :: snd acc)))
  end.

(* [comment removed for export] *)
Definition lin_ge_cert (pf : list pfact) (goals : list expr) : option cert :=
  let pool := base_pool pf goals in
  match fm_search (length goals) pool with
  | Some c => if cert_check pf pool c then Some c else None
  | None =>
      match search_splits true (length goals) split_depth (relevant_seps pf goals) pool with
      | Some c => if cert_check pf pool c then Some c else None
      | None =>
          match search_splits true (length goals) split_depth (relevant_sepsX pf goals pool) pool with
          | Some c => if cert_check pf pool c then Some c else None
          | None => None
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint lia_owners (hyps : list (list pfact)) (h : N) : list pfact * list N :=
  match hyps with
  | [] => ([], [])
  | fs :: hyps' =>
      let nfs := flat_map norm_pf fs in
      let '(pf', own') := lia_owners hyps' (h + 1) in
      (nfs ++ pf', map (fun _ => h) nfs ++ own')
  end.

(* [comment removed for export] *)
Fixpoint fge_positions (pf : list pfact) (i : N) : list N :=
  match pf with
  | [] => []
  | FGe _ :: pf' => i :: fge_positions pf' (i + 1)
  | _ :: pf' => fge_positions pf' (i + 1)
  end.

Fixpoint fal_positions (pf : list pfact) (i : N) : list N :=
  match pf with
  | [] => []
  | FAl _ _ :: pf' => i :: fal_positions pf' (i + 1)
  | _ :: pf' => fal_positions pf' (i + 1)
  end.

Fixpoint mem_N (x : N) (l : list N) : bool :=
  match l with [] => false | y :: l' => N.eqb x y || mem_N x l' end.
Fixpoint nodup_N (l acc : list N) : list N :=
  match l with [] => rev acc | x :: l' => if mem_N x acc then nodup_N l' acc else nodup_N l' (x :: acc) end.

(* [comment removed for export] *)
Definition lx_lia_pick (hyps : list (list pfact)) (goals : list expr) : option (list N) :=
  let '(pf, own) := lia_owners hyps 0 in
  let gs := map enorm goals in
  match all_lits_false gs with
  | Some true => Some []
  | Some false => None
  | None =>
      match lin_ge_cert pf gs with
      | None => None
      | Some c =>
          let '(pidx, fidx) := cert_used c 0 ([], []) in
          let ng := N.of_nat (length gs) in
          let asserted := pf_pool pf in
          let na := N.of_nat (length asserted) in
          let fge := fge_positions pf 0 in
          let nfree := N.of_nat (length (flat_map_free (atoms_of_list (gs ++ asserted) []))
                                 + length (flat_map_goal_free (atoms_of_list gs []))) in
          (* [comment removed for export] *)
          let pfi := flat_map (fun p => if N.ltb p ng then []
                                        else if N.ltb (p - ng) na then [nth_N fge (p - ng) 0%N]
                                        else if N.leb (ng + na + nfree) p then fal_positions pf 0
                                        else []) pidx ++ fidx in
          Some (nodup_N (map (fun i => nth_N own i 0%N) pfi) [])
      end
  end.

End LXH.
