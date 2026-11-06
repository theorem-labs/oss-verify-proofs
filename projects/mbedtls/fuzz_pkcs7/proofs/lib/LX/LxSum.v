(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

(* [comment removed for export] *)
Inductive bleff : Set :=
| BENone                                 (* [comment removed for export] *)
| BECons (ja : positive) (en : expr)     (* [comment removed for export] *)
| BEPop (ja : positive)                  (* [comment removed for export] *)
| BEOpq.                                 (* [comment removed for export] *)
Record heapcall : Set := HCR {
  hc_law : nat;                          (* [comment removed for export] *)
  hc_sp : positive;                      (* [comment removed for export] *)
  hc_hreq : list nat;                    (* [comment removed for export] *)
  hc_obj : option nat;                   (* [comment removed for export] *)
  hc_eff : bleff;                        (* [comment removed for export] *)
  hc_alt : option (list pfact * list mfact * bleff);  (* [comment removed for export] *)
  hc_hpost : list (nat * list expr)      (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition HC (law : nat) (sp : positive) (hreq : list nat) (obj : option nat) (eff : bleff) (alt : option (list pfact * list mfact * bleff)) : heapcall :=
  HCR law sp hreq obj eff alt [].

Record summary : Set := SUMXH {
  su_pc : Z;
  su_acc : bool;                            (* [comment removed for export] *)
  su_np : nat;                              (* [comment removed for export] *)
  su_nr : nat;                              (* [comment removed for export] *)
  su_nb : nat;                              (* [comment removed for export] *)
  su_rbind : list (Z * positive);           (* [comment removed for export] *)
  su_gbind : list (positive * nat);         (* [comment removed for export] *)
  su_sb : option positive;                  (* [comment removed for export] *)
  su_mbind : list mfact;                    (* [comment removed for export] *)
  su_stk : option (positive * positive);    (* [comment removed for export] *)
  su_bbind : list (positive * positive * positive);
                                            (* [comment removed for export] *)
  su_req : list mfact;                      (* [comment removed for export] *)
  su_pre : list pfact;                      (* [comment removed for export] *)
  su_W : list (expr * expr);                (* [comment removed for export] *)
  su_clob : list (Z * positive);            (* [comment removed for export] *)
  su_mpost : list mfact;                    (* [comment removed for export] *)
  su_post : list pfact;                     (* [comment removed for export] *)
  su_oreq : list nat;                       (* [comment removed for export] *)
  su_law : option nat;                      (* [comment removed for export] *)
  su_heap : option heapcall                 (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition SUMXL (pc : Z) (acc : bool) (np nr nb : nat) (rbind : list (Z * positive)) (gbind : list (positive * nat)) (sb : option positive)
           (mbind : list mfact) (stk : option (positive * positive)) (bbind : list (positive * positive * positive))
           (req : list mfact) (pre : list pfact) (W : list (expr * expr)) (clob : list (Z * positive))
           (mpost : list mfact) (post : list pfact) (oreq : list nat) (law : option nat) : summary :=
  SUMXH pc acc np nr nb rbind gbind sb mbind stk bbind req pre W clob mpost post oreq law None.

(* [comment removed for export] *)
Definition SUMX (pc : Z) (acc : bool) (np nr nb : nat) (rbind : list (Z * positive)) (gbind : list (positive * nat)) (sb : option positive)
           (mbind : list mfact) (stk : option (positive * positive)) (bbind : list (positive * positive * positive))
           (req : list mfact) (pre : list pfact) (W : list (expr * expr)) (clob : list (Z * positive))
           (mpost : list mfact) (post : list pfact) (oreq : list nat) : summary :=
  SUMXL pc acc np nr nb rbind gbind sb mbind stk bbind req pre W clob mpost post oreq None.

(* [comment removed for export] *)
Definition SUMG (pc : Z) (acc : bool) (np nr nb : nat) (rbind : list (Z * positive)) (gbind : list (positive * nat)) (sb : option positive)
           (mbind : list mfact) (stk : option (positive * positive)) (bbind : list (positive * positive * positive))
           (req : list mfact) (pre : list pfact) (W : list (expr * expr)) (clob : list (Z * positive))
           (mpost : list mfact) (post : list pfact) : summary :=
  SUMX pc acc np nr nb rbind gbind sb mbind stk bbind req pre W clob mpost post [].

(* [comment removed for export] *)
Definition SUM (pc : Z) (acc : bool) (np nr nb : nat) (rbind : list (Z * positive)) (sb : option positive)
           (mbind : list mfact) (stk : option (positive * positive)) (bbind : list (positive * positive * positive))
           (req : list mfact) (pre : list pfact) (W : list (expr * expr)) (clob : list (Z * positive))
           (mpost : list mfact) (post : list pfact) : summary :=
  SUMX pc acc np nr nb rbind [] sb mbind stk bbind req pre W clob mpost post [].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition subst := list (positive * expr).

Fixpoint sub_get (th : subst) (i : positive) : option expr :=
  match th with [] => None | (j, e) :: th' => if Pos.eqb i j then Some e else sub_get th' i end.

(* [comment removed for export] *)
Fixpoint sxe_raw (th : subst) (e : expr) : expr :=
  match e with
  | ELit z => ELit z
  | EZv i => match sub_get th i with Some e' => e' | None => EZv i end
  | EUv i => EUv i
  | EAdd a b => EAdd (sxe_raw th a) (sxe_raw th b)
  | EMulC c a => EMulC c (sxe_raw th a)
  | EOp o a b => EOp o (sxe_raw th a) (sxe_raw th b)
  end.

Fixpoint renorm (e : expr) : expr :=
  match e with
  | ELit z => ELit z
  | EZv _ | EUv _ => eatom e
  | EAdd a b => eadd (renorm a) (renorm b)
  | EMulC c a => emulc c (renorm a)
  | EOp o a b => match renorm a, renorm b with
                 | ELit x, ELit y => ELit (oplit o x y)
                 | a', b' => eatom (EOp o a' b')
                 end
  end.

Definition sxe (th : subst) (e : expr) : expr := renorm (sxe_raw th e).

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive bval : Set := BVar (k : positive) | BCells (cs : list cellx).
Definition bsubst := list (positive * bval).
Fixpoint bsub_get (tb : bsubst) (k : positive) : option bval :=
  match tb with [] => None | (j, k') :: tb' => if Pos.eqb k j then Some k' else bsub_get tb' k end.
(* [comment removed for export] *)
Definition sxb (tb : bsubst) (k : positive) : positive :=
  match bsub_get tb k with Some (BVar k') => k' | _ => k end.
Definition bvar_bound (tb : bsubst) (k : positive) : bool :=
  match bsub_get tb k with Some (BVar _) => true | _ => false end.

Fixpoint sxc (th : subst) (tb : bsubst) (c : cellx) : cellx :=
  match c with
  | XZ w e => XZ w (sxe th e)
  | XB w k => XB w (sxb tb k)
  | XSl c o l => XSl (sxc th tb c) o l
  | XRep w e => XRep w (sxe th e)
  | _ => c
  end.

Definition sxp (th : subst) (f : pfact) : pfact :=
  match f with
  | FGe e => FGe (sxe th e)
  | FSep a n b k => FSep (sxe th a) (sxe th n) (sxe th b) (sxe th k)
  | FSep0 z a n b k => FSep0 (sxe th z) (sxe th a) (sxe th n) (sxe th b) (sxe th k)
  | FAl a k => FAl (sxe th a) k
  | FCr a n => FCr (sxe th a) (sxe th n)
  | FShb v c oa on => FShb v (sxe th c) (sxe th oa) (sxe th on)
  | FLe a b => FLe (sxe th a) (sxe th b)
  | FLt a b => FLt (sxe th a) (sxe th b)
  | FEq a b => FEq (sxe th a) (sxe th b)
  | FOr2 a b c d => FOr2 (sxe th a) (sxe th b) (sxe th c) (sxe th d)
  | FOr3z z a b c d => FOr3z (sxe th z) (sxe th a) (sxe th b) (sxe th c) (sxe th d)
  | FProp j xs => FProp j (map (sxe th) xs)
  end.

Definition sxw (th : subst) (W : list (expr * expr)) : list (expr * expr) :=
  map (fun lh => (sxe th (fst lh), sxe th (snd lh))) W.

(* [comment removed for export] *)
Definition lsubst := list (positive * lexpr).
Fixpoint lsub_get (tl : lsubst) (j : positive) : option lexpr :=
  match tl with [] => None | (j', l) :: tl' => if Pos.eqb j j' then Some l else lsub_get tl' j end.
Definition lbind (tl : lsubst) (j : positive) (l : lexpr) : option lsubst :=
  match lsub_get tl j with
  | None => Some ((j, l) :: tl)
  | Some l' => if lexpr_eqb l' l then Some tl else None
  end.

Fixpoint sxl (th : subst) (tl : lsubst) (l : lexpr) : lexpr :=
  match l with
  | LBase j => match lsub_get tl j with Some lc => lc | None => LBase j end
  | LUpd l i w v => LUpd (sxl th tl l) (sxe th i) w (sxe th v)
  end.

Fixpoint sxbl (th : subst) (bl : bklist) : bklist :=
  match bl with BL0 => BL0 | BLV k => BLV k | BCons a n bl' => BCons (sxe th a) (sxe th n) (sxbl th bl') end.
Definition sxm (th : subst) (tb : bsubst) (tl : lsubst) (f : mfact) : mfact :=
  match f with
  | MRw a cs => MRw (sxe th a) (map (sxc th tb) cs)
  | MRo a cs => MRo (sxe th a) (map (sxc th tb) cs)
  | MBy a n k => MBy (sxe th a) (sxe th n) (sxb tb k)
  | MStk lo hi => MStk (sxe th lo) (sxe th hi)
  | MAobj a n => MAobj (sxe th a) (sxe th n)
  | MOpq k ok sh => MOpq k (sxw th ok) (sxw th sh)
  | MArr a w l n wr => MArr (sxe th a) w (sxl th tl l) (sxe th n) wr
  (* [comment removed for export] *)
  | MCli l a n => MCli l (sxe th a) (sxe th n)
  | MCobj l a n => MCobj l (sxe th a) (sxe th n)
  | MMunch W i j => MMunch (sxw th W) i j
  | MWmono i j => MWmono i j
  | MLaw l X i j => MLaw l (sxw th X) i j
  (* [comment removed for export] *)
  | MHeap bl ok => MHeap (sxbl th bl) (sxw th ok)
  | MOqH l k => MOqH l k
  | MLawH l bl sp X i j => MLawH l (sxbl th bl) (sxe th sp) (sxw th X) i j
  | MCliH l s a n => MCliH l (sxe th s) (sxe th a) (sxe th n)
  | MApartBl a n bl => MApartBl (sxe th a) (sxe th n) (sxbl th bl)
  (* [comment removed for export] *)
  | MHpr j o b xs ok => MHpr j (sxbl th o) (sxbl th b) (map (sxe th) xs) (sxw th ok)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint eloc (n : positive) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EZv i => Pos.ltb i n
  | EUv _ => false
  | EAdd a b | EOp _ a b => eloc n a && eloc n b
  | EMulC _ a => eloc n a
  end.

(* [comment removed for export] *)
Definition cloc (n : positive) (nb : positive) (blobs : bool) (c : cellx) : bool :=
  match c with
  | XZ w e => okw w && eloc n e
  | XB w k => blobs && Pos.ltb k nb
  | XRep w e => eloc n e
  | _ => false
  end.

Definition mloc (n : positive) (nb : positive) (nl : positive) (blobs : bool) (f : mfact) : bool :=
  match f with
  | MRw a cs | MRo a cs => eloc n a && forallb (cloc n nb blobs) cs
  | MBy a m k => blobs && eloc n a && eloc n m && Pos.ltb k nb
  | MStk a b | MAobj a b => eloc n a && eloc n b
  | MOpq _ _ _ => false     (* [comment removed for export] *)
  | MArr a w (LBase j) m _ => (N.eqb w 4 || N.eqb w 8) && eloc n a && eloc n m && Pos.ltb j nl
                              (* [comment removed for export] *)
  | MArr _ _ _ _ _ => false
  | MCli _ a b | MCobj _ a b => eloc n a && eloc n b     (* [comment removed for export] *)
  | MMunch _ _ _ | MWmono _ _ | MLaw _ _ _ _ => false
  | MHeap _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ => false   (* [comment removed for export] *)
  | MHpr _ _ _ _ _ => false            (* [comment removed for export] *)
  end.

Definition ploc (n : positive) (f : pfact) : bool :=
  match f with
  | FGe e => eloc n e
  | FSep a b c d | FOr2 a b c d => eloc n a && eloc n b && eloc n c && eloc n d
  | FSep0 z a b c d | FOr3z z a b c d => eloc n z && eloc n a && eloc n b && eloc n c && eloc n d
  | FProp _ xs => forallb (eloc n) xs
  | FAl a _ => eloc n a
  | FCr a b | FLe a b | FLt a b | FEq a b => eloc n a && eloc n b
  | FShb _ _ _ _ => false
  end.

(* [comment removed for export] *)
Definition lloc_of (f : mfact) : nat := match f with MArr _ _ (LBase j) _ _ => Pos.to_nat j | _ => O end.
Definition lmax (l : list mfact) : nat := fold_right (fun f acc => Nat.max (lloc_of f) acc) O l.
Definition su_nl (su : summary) : nat := lmax (su_mbind su ++ su_req su).
Definition su_nla (su : summary) : nat := Nat.max (su_nl su) (lmax (su_mpost su)).
Definition su_nrl (su : summary) : nat := su_nla su - su_nl su.
Definition su_nlP (su : summary) : positive := Pos.of_nat (S (su_nl su)).     (* [comment removed for export] *)
Definition su_nlaP (su : summary) : positive := Pos.of_nat (S (su_nla su)).   (* [comment removed for export] *)

Definition su_npP (su : summary) : positive := Pos.of_nat (S (su_np su)).             (* [comment removed for export] *)
Definition su_nallP (su : summary) : positive := Pos.of_nat (S (su_np su + su_nr su)). (* [comment removed for export] *)
Definition su_nbP (su : summary) : positive := Pos.of_nat (S (su_nb su)).

Definition su_wf (su : summary) : bool :=
  let np := su_npP su in let na := su_nallP su in let nb := su_nbP su in
  forallb (fun ri => Pos.ltb (snd ri) np && Z.leb 1 (fst ri) && Z.leb (fst ri) 31) (su_rbind su)
  && forallb (fun gn => Pos.ltb (fst gn) np) (su_gbind su)
  && match su_sb su with Some i => Pos.ltb i np | None => true end
  && forallb (mloc np nb (su_nlP su) true) (su_mbind su)
  && match su_stk su with Some (i, j) => Pos.ltb i np && Pos.ltb j np | None => true end
  && forallb (fun b => match b with (ia, il, kb) => Pos.ltb ia np && Pos.ltb il np && Pos.ltb kb nb end) (su_bbind su)
  && forallb (mloc np nb (su_nlP su) true) (su_req su)
  && forallb (ploc np) (su_pre su)
  && forallb (fun lh => eloc np (fst lh) && eloc np (snd lh)) (su_W su)
  && forallb (fun rj => Pos.leb np (snd rj) && Pos.ltb (snd rj) na && negb (Z.eqb (fst rj) 0)
                       && Z.leb 0 (fst rj) && Z.ltb (fst rj) 32) (su_clob su)
  && forallb (mloc na nb (su_nlaP su) true) (su_mpost su)
  && forallb (ploc na) (su_post su).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bind (th : subst) (i : positive) (e : expr) : option subst :=
  match sub_get th i with
  | None => Some ((i, e) :: th)
  | Some e' => if expr_eqb e' e then Some th else None
  end.

Fixpoint match_regs (ss : sstate) (rb : list (Z * positive)) (th : subst) : option subst :=
  match rb with
  | [] => Some th
  | (r, i) :: rb' => match bind th i (rd_expr ss r) with Some th' => match_regs ss rb' th' | None => None end
  end.

Fixpoint match_globals (genv : list expr) (gb : list (positive * nat)) (th : subst) : option subst :=
  match gb with
  | [] => Some th
  | (i, n) :: gb' =>
      match nth_error genv n with
      | Some g => match bind th i g with Some th' => match_globals genv gb' th' | None => None end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition cell_expr (c : cellx) : option expr :=
  match c with
  | XW i => Some (eatom (EUv i))
  | XZ _ e => Some e
  | XWn 2 i | XWn 4 i => Some (eatom (EUv i))
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint ebound (th : subst) (e : expr) : bool :=
  match e with
  | ELit _ | EUv _ => true
  | EZv i => match sub_get th i with Some _ => true | None => false end
  | EAdd a b | EOp _ a b => ebound th a && ebound th b
  | EMulC _ a => ebound th a
  end.

(* [comment removed for export] *)
Fixpoint enoU (e : expr) : bool :=
  match e with
  | ELit _ | EZv _ => true
  | EUv _ => false
  | EAdd a b | EOp _ a b => enoU a && enoU b
  | EMulC _ a => enoU a
  end.

(* [comment removed for export] *)
Definition pat_local (e : expr) : option positive :=
  match e with
  | EAdd (EMulC 1 (EZv j)) (ELit 0) => Some j
  | EZv j => Some j
  | _ => None
  end.

Fixpoint take_cells (cs : list cellx) (n : Z) : option (list cellx * list cellx) :=
  if Z.eqb n 0 then Some ([], cs) else
  match cs with
  | [] => None
  | c :: cs' =>
      let w := Z.of_N (cellx_size c) in
      if Z.ltb n w then None else
      match take_cells cs' (n - w) with
      | Some (p, r) => Some (c :: p, r)
      | None => None
      end
  end.

(* [comment removed for export] *)
Fixpoint take_cellsx (cs : list cellx) (n : Z) : option (list cellx * list cellx) :=
  if Z.eqb n 0 then Some ([], cs) else
  match cs with
  | [] => None
  | c :: cs' =>
      let w := Z.of_N (cellx_size c) in
      if Z.ltb n w then (if Z.ltb 0 n then Some ([mk_slice c 0 (Z.to_N n)], mk_slice c (Z.to_N n) (Z.to_N (w - n)) :: cs') else None) else
      match take_cellsx cs' (n - w) with
      | Some (p, r) => Some (c :: p, r)
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition xrep_expose (w : N) (c : cellx) (cs' : list cellx) : cellx * list cellx :=
  match c with
  | XRep n e => match is_lit e with
                | Some z => if Z.eqb z 0 && okw w then
                              (if N.ltb w n then (XZ w (ELit 0), XRep (n - w) e :: cs')
                               else if N.eqb w n then (XZ w (ELit 0), cs') else (c, cs'))
                            else (c, cs')
                | None => (c, cs')
                end
  | _ => (c, cs')
  end.

Fixpoint match_cells (pats : list cellx) (cs : list cellx) (th : subst) (tb : bsubst) : option (subst * bsubst) :=
  match pats, cs with
  | [], [] => Some (th, tb)
  | XZ w pe :: pats', c0 :: cs0 =>
      let (c, cs') := xrep_expose w c0 cs0 in
      if N.eqb (cellx_size c) w then
        match cell_expr c with
        | Some e =>
            match pat_local pe with
            | Some j => match bind th j e with Some th' => match_cells pats' cs' th' tb | None => None end
            | None => if ebound th pe && enoU pe && expr_eqb (sxe th pe) e then match_cells pats' cs' th tb else None
            end
        | None => None
        end
      else None
  | XB w kb :: pats', _ =>
      match cs with
      | XB w' k :: cs' =>
          if N.eqb w w' then
            match bsub_get tb kb with
            | None => match_cells pats' cs' th ((kb, BVar k) :: tb)
            | Some (BVar k') => if Pos.eqb k k' then match_cells pats' cs' th tb else None
            | Some _ => None
            end
          else None
      | _ =>
          (* [comment removed for export] *)
          match bsub_get tb kb, take_cellsx cs (Z.of_N w) with
          | None, Some (taken, cs') => match_cells pats' cs' th ((kb, BCells taken) :: tb)
          | _, _ => None
          end
      end
  | _, _ => None
  end.

Fixpoint find_rw (mf : list mfact) (a : expr) : option (list cellx) :=
  match mf with
  | [] => None
  | MRw b cs :: mf' => if expr_eqb a b then Some cs else find_rw mf' a
  | _ :: mf' => find_rw mf' a
  end.

Fixpoint match_chunks (mf : list mfact) (mb : list mfact) (th : subst) (tb : bsubst) : option (subst * bsubst) :=
  match mb with
  | [] => Some (th, tb)
  | MRw a pats :: mb' =>
      if ebound th a then
        match find_rw mf (sxe th a) with
        | Some cs => match match_cells pats cs th tb with Some (th', tb') => match_chunks mf mb' th' tb' | None => None end
        | None => None
        end
      else None
  | MArr _ _ _ _ _ :: mb' => match_chunks mf mb' th tb    (* [comment removed for export] *)
  | _ :: mb' => None
  end.

(* [comment removed for export] *)
Fixpoint find_arr (mf : list mfact) (a : expr) (w : N) (wr : bool) : option (lexpr * expr) :=
  match mf with
  | [] => None
  | MArr b w' l n wr' :: mf' => if expr_eqb a b && N.eqb w w' && (negb wr || wr') then Some (l, n) else find_arr mf' a w wr
  | _ :: mf' => find_arr mf' a w wr
  end.
(* [comment removed for export] *)
Fixpoint lall_bound (tl : lsubst) (n : nat) (i : positive) : bool :=
  match n with O => true | S n' => match lsub_get tl i with Some _ => lall_bound tl n' (Pos.succ i) | None => false end end.

(* [comment removed for export] *)
Fixpoint match_arrs (pf : list pfact) (mf : list mfact) (mb : list mfact) (th : subst) (tl : lsubst) : option (subst * lsubst) :=
  match mb with
  | [] => Some (th, tl)
  | MArr pa w (LBase j) pn wr :: mb' =>
      if ebound th pa && (N.eqb w 4 || N.eqb w 8) then     (* [comment removed for export] *)
        match find_arr mf (sxe th pa) w wr with
        | Some (l, n) =>
            match lbind tl j l with
            | Some tl' =>
                match (match pat_local pn with
                       | Some jn => match bind th jn n with
                                    | Some th' => Some th'
                                    | None => match sub_get th jn with
                                              | Some e => if dec_eq pf e n then Some th else None
                                              | None => None
                                              end
                                    end
                       | None => if ebound th pn && enoU pn && expr_eqb (sxe th pn) n then Some th else None
                       end) with
                | Some th' => match_arrs pf mf mb' th' tl'
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else None
  | MArr _ _ _ _ _ :: _ => None
  | _ :: mb' => match_arrs pf mf mb' th tl
  end.

Fixpoint has_mfact (mf : list mfact) (f : mfact) : bool :=
  match mf with [] => false | g :: mf' => mfact_eqb f g || has_mfact mf' f end.

(* [comment removed for export] *)
Fixpoint zero_cells (cs : list cellx) (off : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S cnt' => match cell_lookup cs off 1 with
              | Some (XZ 1 (ELit 0)) => zero_cells cs (off + 1) cnt'
              | _ => false
              end
  end.

Definition aobj_derivable (C : lxcfg) (pf : list pfact) (crs : list (expr * expr)) (mf : list mfact) (a n : expr) : bool :=
  lexistsb (fun f => match f with
    | MAobj a' n' => if dec_le pf a' a then dec_le pf (eadd a n) (eadd a' n') else false
    | MRw b cs =>
        match c_acc C, is_lit n with
        | Some A, Some nz =>
            match shadow_split (ac_sb A) b with
            | Some (x, kr) =>
                match ediff_lit a (sh_c x kr) with
                | Some d => if Z.leb 0 d && Z.eqb (d mod 8) 0 && Z.ltb 0 nz && Z.eqb (nz mod 8) 0
                               && N.leb 3 (eal (mk_oracle pf) x)
                               && zero_cells cs (d / 8) (Z.to_nat (nz / 8))
                            then in_some_crange pf crs a n else false
                | None => false
                end
            | None => false
            end
        | _, _ => false
        end
    | _ => false end) mf.

Definition req_ok (C : lxcfg) (pf : list pfact) (crs : list (expr * expr)) (mf : list mfact) (g : mfact) : bool :=
  if has_mfact mf g then true else
                   match g with
                   | MAobj a n => aobj_derivable C pf crs mf a n
                   | MArr a w l n wr => match find_arr mf a w wr with
                                        | Some (l', n') => lexpr_eqb l l' && expr_eqb n n'
                                        | None => false end
                   | _ => false end.

(* [comment removed for export] *)
Definition frame_fills (mf0 : list mfact) (h hi : expr) : bool :=
  existsb (fun f => match f with
                    | MRw b cs => expr_eqb b h && expr_eqb (enorm (eadd b (ELit (Z.of_N (cells_sizeN cs))))) (enorm hi)
                    | _ => false
                    end) mf0.
Fixpoint match_stk (mf0 : list mfact) (mf : list mfact) (hi : expr) (i : positive) (th : subst) : option subst :=
  match mf with
  | [] => None
  | MStk lo h :: mf' => if expr_eqb h hi then bind th i lo
                        else if frame_fills mf0 h hi then bind th i lo
                        else match_stk mf0 mf' hi i th
  | _ :: mf' => match_stk mf0 mf' hi i th
  end.

(* [comment removed for export] *)
Definition hyp_cases (f : pfact) : list (list pfact) :=
  match f with
  | FSep a n b k => [[FGe (sep_l a n b)]; [FGe (sep_r a b k)]]
  | FSep0 z a n b k => [[FGe z; FGe (emulc (-1) z)]; [FGe (sep_l a n b)]; [FGe (sep_r a b k)]]
  | _ => []
  end.

Definition goal_case_ok (pf : list pfact) (gc : list expr) : bool := lforallb (lin_ge pf) gc.
(* [comment removed for export] *)
Definition goal_case_ok0 (pf : list pfact) (gc : list expr) : bool := lforallb (lin_ge0 pf) gc.
(* [comment removed for export] *)
Definition goal_case_ok00 (pf : list pfact) (gc : list expr) : bool := lforallb (lin_ge00 pf) gc.
(* [comment removed for export] *)
Definition goal_case_okS (pf : list pfact) (gc : list expr) : bool := lforallb (lin_geS pf) gc.

(* [comment removed for export] *)
Definition goal_atoms1 (pf : list pfact) (gcs : list (list expr)) : list expr :=
  let ga0 := atoms_of_list (concat gcs) [] in
  atoms_of_list (filter (fun e => any_mem (atoms_of_list [e] []) ga0) (pf_pool pf)) ga0.
(* [comment removed for export] *)
Fixpoint ins_ranked (sc : nat) (h : pfact) (l : list (nat * pfact)) : list (nat * pfact) :=
  match l with
  | [] => [(sc, h)]
  | (sc', h') :: l' => if Nat.ltb sc' sc then (sc, h) :: l else (sc', h') :: ins_ranked sc h l'
  end.
Fixpoint rank_hyps (ga : list expr) (pf : list pfact) (acc : list (nat * pfact)) : list (nat * pfact) :=
  match pf with
  | [] => acc
  | h :: pf' => rank_hyps ga pf' (if sep_rel ga h then ins_ranked (hyp_score ga h) h acc else acc)
  end.
Definition rank_hyps2 (ga0 ga : list expr) (pf : list pfact) (acc : list (nat * pfact)) : list (nat * pfact) :=
  (fix go (pf : list pfact) (acc : list (nat * pfact)) : list (nat * pfact) :=
     match pf with
     | [] => acc
     | h :: pf' => go pf' (if sep_rel ga h then ins_ranked (8 * hyp_score ga0 h + hyp_score ga h) h acc else acc)
     end) pf acc.
(* [comment removed for export] *)
Definition rank_hypsA (ga0 ga : list expr) (pf : list pfact) : list (nat * pfact) :=
  (fix go (pf : list pfact) (acc : list (nat * pfact)) : list (nat * pfact) :=
     match pf with
     | [] => acc
     | h :: pf' => go pf' (match hyp_cases h with [] => acc | _ => ins_ranked (8 * hyp_score ga0 h + hyp_score ga h) h acc end)
     end) pf [].
(* [comment removed for export] *)
Fixpoint singletons (gcs : list (list expr)) : option (list expr) :=
  match gcs with
  | [] => Some []
  | [g] :: gcs' => match singletons gcs' with Some gs => Some (g :: gs) | None => None end
  | _ :: _ => None
  end.
Definition gcs_probe (deep : bool) (pf : list pfact) (gcs : list (list expr)) : bool :=
  match singletons gcs with
  | Some gs => lin_ge_fm deep pf gs
  | None => lexistsb (lforallb (fun g => lin_ge_fm deep pf [g])) gcs
  end.
(* [comment removed for export] *)
Definition casewise_gen (all : bool) (gprobe : list pfact -> list (list expr) -> bool) (pf : list pfact) (gcs : list (list expr)) : bool :=
  let ga0 := atoms_of_list (concat gcs) [] in
  let ga := goal_atoms1 pf gcs in
  lexistsb (fun sh => match hyp_cases (snd sh) with
                      | [] => false
                      | hcs => lforallb (fun hc => gprobe (hc ++ pf) gcs) hcs
                      end) (if all then rank_hypsA ga0 ga pf else rank_hyps2 ga0 ga pf []).
Definition casewise := casewise_gen false.
(* [comment removed for export] *)
Definition dec_disj_by (gdir gcase : list pfact -> list expr -> bool) (pf : list pfact) (gcs : list (list expr)) : bool :=
  if lexistsb (gdir pf) gcs then true else casewise (fun pf' gcs' => lexistsb (gcase pf') gcs') pf gcs.
(* [comment removed for export] *)
Definition dec_disj_cheap (pf : list pfact) (gcs : list (list expr)) : bool :=
  if gcs_probe false pf gcs then true else casewise (gcs_probe false) pf gcs.
Definition dec_disj_rest (pf : list pfact) (gcs : list (list expr)) : bool :=
  if gcs_probe true pf gcs then true
  else if dec_disj_by goal_case_okS goal_case_ok pf gcs then true
  else casewise_gen true (gcs_probe true) pf gcs.      (* [comment removed for export] *)
Definition dec_disj (pf : list pfact) (gcs : list (list expr)) : bool :=
  if dec_disj_cheap pf gcs then true else dec_disj_rest pf gcs.

(* [comment removed for export] *)
Definition pf_decide (pf : list pfact) (crs : list (expr * expr)) (O : oracle) (f : pfact) : bool :=
  if pf_mem f pf then true else
  match f with
  | FGe e => lin_ge pf e
  | FLe a b => dec_le pf a b
  | FLt a b => dec_lt pf a b
  | FEq a b => dec_eq pf a b
  | FSep a n b k => dec_disj pf [[sep_l a n b]; [sep_r a b k]]
  | FSep0 z a n b k => dec_disj pf [[emulc (-1) z; z]; [sep_l a n b]; [sep_r a b k]]
  | FOr2 a b c d => dec_disj pf [[eadd b (emulc (-1) a)]; [eadd d (emulc (-1) c)]]
  | FOr3z z a b c d => dec_disj pf [[emulc (-1) z; z]; [eadd b (emulc (-1) a)]; [eadd d (emulc (-1) c)]]
  | FProp _ _ => false       (* [comment removed for export] *)
  | FAl a k => N.leb k (eal O a)
  | FCr a n => in_some_crange pf crs a n
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint mby_facts (mf : list mfact) : list (expr * expr * positive) :=
  match mf with
  | [] => []
  | MBy a n k :: mf' => (a, n, k) :: mby_facts mf'
  | _ :: mf' => mby_facts mf'
  end.

Fixpoint bind_bytes (bb : list (positive * positive * positive)) (cands : list (expr * expr * positive))
         (th : subst) (tb : bsubst) (k : subst -> bool) : option (subst * bsubst) :=
  match bb with
  | [] => if k th then Some (th, tb) else None
  | (ia, il, kb) :: bb' =>
      (fix try (cs : list (expr * expr * positive)) : option (subst * bsubst) :=
         match cs with
         | [] => None
         | (a, n, kc) :: cs' =>
             match bsub_get tb kb with
             | Some _ => None   (* [comment removed for export] *)
             | None =>
                 match bind th ia a with
                 | Some th1 =>
                     match bind th1 il n with
                     | Some th2 =>
                         match bind_bytes bb' cands th2 ((kb, BVar kc) :: tb) k with
                         | Some r => Some r
                         | None => try cs'
                         end
                     | None => try cs'
                     end
                 | None => try cs'
                 end
             end
         end) cands
  end.

(* [comment removed for export] *)
Fixpoint all_bound (th : subst) (n : nat) (i : positive) : bool :=
  match n with
  | O => true
  | S n' => match sub_get th i with Some _ => all_bound th n' (Pos.succ i) | None => false end
  end.

Fixpoint all_bbound (tb : bsubst) (n : nat) (i : positive) : bool :=
  match n with
  | O => true
  | S n' => match bsub_get tb i with Some _ => all_bbound tb n' (Pos.succ i) | None => false end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition overlap0 (shallow : bool) (pf : list pfact) (lo hi b sz : expr) (zero_ok : bool) : bool :=
  let ge := if shallow then lin_ge00 pf else lin_ge0 pf in
  if ge (eadd (eadd b sz) (eadd (emulc (-1) lo) (ELit (-1)))) then
    if ge (eadd hi (eadd (emulc (-1) b) (ELit (-1)))) then
      if zero_ok then ge (eadd sz (ELit (-1))) else true
    else false
  else false.

(* [comment removed for export] *)
Definition dec_apart_rest (pf : list pfact) (a n b k : expr) : bool :=
  if lin_ge_list pf [sep_l a n b; sep_r a b k] then true else lin_ge_listX pf [sep_l a n b; sep_r a b k].
Definition dec_apartS (pf : list pfact) (lo hi b sz : expr) : bool :=
  let n := eadd hi (emulc (-1) lo) in
  if overlap0 true pf lo hi b sz false then false
  else if sep_lookup false pf lo n b sz then true
  else if dec_disj_cheap pf [[sep_l lo n b]; [sep_r lo b sz]] then true
  else if overlap0 false pf lo hi b sz false then false
  else dec_apart_rest pf lo n b sz.
(* [comment removed for export] *)
Definition dec_apart0S (pf : list pfact) (lo hi b sz : expr) : bool :=
  let n := eadd hi (emulc (-1) lo) in
  let gcs := [[sep_l lo n b]; [sep_r lo b sz]; [emulc (-1) sz]] in
  if overlap0 true pf lo hi b sz true then false
  else if sep_lookup false pf lo n b sz then true
  else if dec_disj_cheap pf gcs then true
  else if overlap0 false pf lo hi b sz true then false
  else dec_disj_rest pf gcs.

Fixpoint all_apart (pf : list pfact) (W : list (expr * expr)) (b : expr) (sz : expr) : bool :=
  match W with
  | [] => true
  | (lo, hi) :: W' => if dec_apartS pf lo hi b sz then all_apart pf W' b sz else false
  end.

(* [comment removed for export] *)
Fixpoint all_apart0 (pf : list pfact) (W : list (expr * expr)) (b : expr) (sz : expr) : bool :=
  match W with
  | [] => true
  | (lo, hi) :: W' => if dec_apart0S pf lo hi b sz then all_apart0 pf W' b sz else false
  end.

(* [comment removed for export] *)
Fixpoint all_nonempty (pf : list pfact) (W : list (expr * expr)) : bool :=
  match W with
  | [] => true
  | (lo, hi) :: W' => if dec_lt pf lo hi then all_nonempty pf W' else false
  end.

(* [comment removed for export] *)
Definition mf_survives_call (C : lxcfg) (pf : list pfact) (crs : list (expr * expr)) (mf0 : list mfact) (W : list (expr * expr)) (wclient wne : bool) (f : mfact) : bool :=
  match f with
  | MRw b cs => if all_apart pf W b (ELit (Z.of_N (cells_sizeN cs))) then true
                (* [comment removed for export] *)
                else if wclient && wne && Z.ltb 0 (Z.of_N (cells_sizeN cs)) then class_apart C pf crs AcClient b (ELit (Z.of_N (cells_sizeN cs))) else false
  | MRo b cs => if wclient && wne && is_static C b && N.eqb (cells_sizeN cs) 8 then true else all_apart pf W b (ELit (Z.of_N (cells_sizeN cs)))
  | MBy b n _ => all_apart0 pf W b n
  | MStk lo hi => all_apart pf W lo (eadd hi (emulc (-1) lo))      (* [comment removed for export] *)
  | MAobj _ _ => match c_acc C with Some _ => wclient | None => false end
  | MOpq _ ok sh => lforallb (fun lh => opq_iv_ok C pf crs (fst lh) (eadd (snd lh) (emulc (-1) (fst lh))) ok sh) W
  | MArr b wd _ n _ => all_apart0 pf W b (emulc (Z.of_N wd) n)
  | MHeap _ ok => lforallb (fun lh => opq_iv_ok C pf crs (fst lh) (eadd (snd lh) (emulc (-1) (fst lh))) ok []) W
  | MHpr _ blo bln _ ok => lforallb (fun lh => hpr_iv_ok pf mf0 blo bln ok (fst lh) (eadd (snd lh) (emulc (-1) (fst lh)))) W
  | MMunch _ _ _ | MWmono _ _ | MLaw _ _ _ _ | MCli _ _ _ | MCobj _ _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ => true
  end.

Fixpoint w_all_client (pf : list pfact) (crs : list (expr * expr)) (W : list (expr * expr)) : bool :=
  match W with
  | [] => true
  | (lo, hi) :: W' => if in_some_crange pf crs lo (eadd hi (emulc (-1) lo)) then w_all_client pf crs W' else false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tag_covers (dp obj : bool) (l : nat) (mf : list mfact) (pf : list pfact) (b n : expr) : bool :=
  match mf with
  | [] => false
  (* [comment removed for export] *)
  | MCli l' a k :: mf' => if (if negb obj && Nat.eqb l l' then (if iv_inside_syn b n a k then true else (if dp then dec_inside pf b n a k else dec_inside0 pf b n a k)) else false)
                         then true else tag_covers dp obj l mf' pf b n
  | MCobj l' a k :: mf' => if (if obj && Nat.eqb l l' then (if iv_inside_syn b n a k then true else (if dp then dec_inside pf b n a k else dec_inside0 pf b n a k)) else false)
                          then true else tag_covers dp obj l mf' pf b n
  | _ :: mf' => tag_covers dp obj l mf' pf b n
  end.

(* [comment removed for export] *)
Definition law_survives (dp : bool) (C : lxcfg) (l : nat) (pf : list pfact) (crs : list (expr * expr)) (mf : list mfact) (W : list (expr * expr))
    (wclient wne : bool) (f : mfact) : bool :=
  match f with
  | MRw b cs => let n := ELit (Z.of_N (cells_sizeN cs)) in
                if (if all_apart pf W b n then true else if wclient && wne && Z.ltb 0 (Z.of_N (cells_sizeN cs)) then class_apart C pf crs AcClient b n else false)
                then tag_covers dp false l mf pf b n else false
  | MRo b cs => let n := ELit (Z.of_N (cells_sizeN cs)) in
                         if all_apart pf W b n then tag_covers dp false l mf pf b n else false
  | MBy b n _ => if all_apart0 pf W b n then tag_covers dp false l mf pf b n else false
  | MArr b wd _ n _ => let m := emulc (Z.of_N wd) n in if all_apart0 pf W b m then tag_covers dp false l mf pf b m else false
  | MAobj a n => tag_covers dp true l mf pf a n           (* [comment removed for export] *)
  | MStk lo hi => let n := eadd hi (emulc (-1) lo) in if all_apart pf W lo n then tag_covers dp false l mf pf lo n else false
  | MOpq _ _ _ => false                                 (* [comment removed for export] *)
  | MHeap _ _ => false                                  (* [comment removed for export] *)
  | MHpr _ _ _ _ _ => false                             (* [comment removed for export] *)
  | MMunch _ _ _ | MWmono _ _ | MLaw _ _ _ _ | MCli _ _ _ | MCobj _ _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ => true
  end.

(* [comment removed for export] *)
Fixpoint res_subst (first : positive) (nr : nat) (nx : positive) (th : subst) : subst :=
  match nr with
  | O => th
  | S nr' => res_subst (Pos.succ first) nr' (Pos.succ nx) ((first, eatom (EZv nx)) :: th)
  end.

Fixpoint set_regs (rs : list sreg) (cl : list (Z * expr)) : list sreg :=
  match cl with
  | [] => rs
  | (r, e) :: cl' => set_regs (lset rs (Z.to_nat (r - 1)) (mkreg e)) cl'
  end.

Fixpoint drop_rw_at (mf : list mfact) (a : expr) : list mfact :=
  match mf with
  | [] => []
  | MRw b cs :: mf' => if expr_eqb a b then drop_rw_at mf' a else MRw b cs :: drop_rw_at mf' a
  | f :: mf' => f :: drop_rw_at mf' a
  end.

Fixpoint install_post (mf : list mfact) (ms : list mfact) : list mfact :=
  match ms with
  | [] => mf
  | MRw a cs :: ms' => install_post (MRw a cs :: drop_rw_at mf a) ms'
  | f :: ms' => install_post (f :: mf) ms'
  end.

Fixpoint w_adds (pf : list pfact) (W : list (expr * expr)) (add : list (expr * expr)) : list (expr * expr) :=
  match add with
  | [] => W
  | (lo, hi) :: add' => w_adds pf (if dec_le00 pf lo hi then w_add pf W lo hi else W ++ [(lo, hi)]) add'
  end.

Inductive sumres : Set :=
| SumOk (k kl : nat) (ss' : sstate)     (* [comment removed for export] *)
| SumOkL (k kl : nat) (ss' : sstate)    (* [comment removed for export] *)
| SumOkM (k kl : nat) (ss1 : sstate) (ss2 : option sstate)
                                        (* [comment removed for export] *)
| SumFail (code : Z).

(* [comment removed for export] *)
Fixpoint opq_find (mf : list mfact) (k : nat) : option mfact :=
  match mf with
  | [] => None
  | MOpq k' ok sh :: mf' => if Nat.eqb k k' then Some (MOpq k' ok sh) else opq_find mf' k
  | _ :: mf' => opq_find mf' k
  end.
Definition opq_required (mf : list mfact) (ks : list nat) : option (list mfact) :=
  fold_right (fun k acc => match acc, opq_find mf k with Some l, Some f => Some (f :: l) | _, _ => None end) (Some []) ks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint heap_find (mf : list mfact) : option (bklist * list (expr * expr)) :=
  match mf with
  | [] => None
  | MHeap bl ok :: _ => Some (bl, ok)
  | _ :: mf' => heap_find mf'
  end.

(* [comment removed for export] *)
Fixpoint bl_pop (pf : list pfact) (mf : list mfact) (a : expr) (bl : bklist) : option (expr * bklist) :=
  match bl with
  | BL0 | BLV _ => None
  | BCons b k rest =>
      if expr_eqb a b then Some (k, rest)
      else if (if mf_mem (MApartBl b k rest) mf then dec_lt pf (ELit 0) k else false) then
             match bl_pop pf mf a rest with
             | Some (n, rest') => if dec_lt pf (ELit 0) n then Some (n, BCons b k rest') else None
             | None => None
             end
           else None
  end.

(* [comment removed for export] *)
Fixpoint ws_remove (W : list (expr * expr)) (lo hi : expr) : list (expr * expr) :=
  match W with
  | [] => []
  | (l, h) :: W' => if expr_eqb l lo && expr_eqb h hi then ws_remove W' lo hi else (l, h) :: ws_remove W' lo hi
  end.

(* [comment removed for export] *)
Fixpoint tag_coversH (l : nat) (mf : list mfact) (pf : list pfact) (sp b n : expr) : bool :=
  match mf with
  | [] => false
  | MCliH l' s a k :: mf' => if (if Nat.eqb l l' then (if dec_le pf sp s then (if iv_inside_syn b n a k then true else dec_inside pf b n a k) else false) else false)
                            then true else tag_coversH l mf' pf sp b n
  | _ :: mf' => tag_coversH l mf' pf sp b n
  end.
(* [comment removed for export] *)
Fixpoint oq_taggedH (l k : nat) (mf : list mfact) : bool :=
  match mf with
  | [] => false
  | MOqH l' k' :: mf' => if Nat.eqb l l' && Nat.eqb k k' then true else oq_taggedH l k mf'
  | _ :: mf' => oq_taggedH l k mf'
  end.

(* [comment removed for export] *)
Definition hcovered (l : nat) (pf : list pfact) (mf : list mfact) (bl : bklist) (sp : expr) (b n : expr) : bool :=
  if dec_le pf sp b then true else if bl_covers pf bl b n then true else tag_coversH l mf pf sp b n.

(* [comment removed for export] *)
Definition heap_survives (l : nat) (pf : list pfact) (mf : list mfact) (bl : bklist) (sp : expr) (X : list (expr * expr)) (f : mfact) : bool :=
  match f with
  | MRw b cs | MRo b cs => let n := ELit (Z.of_N (cells_sizeN cs)) in
                         if all_apart pf X b n then hcovered l pf mf bl sp b n else false
  | MBy b n _ => if all_apart pf X b n then hcovered l pf mf bl sp b n else false
  | MArr b wd _ n _ => let m := emulc (Z.of_N wd) n in if all_apart pf X b m then hcovered l pf mf bl sp b m else false
  | MStk _ _ | MAobj _ _ | MHeap _ _ => false         (* [comment removed for export] *)
  | MOpq k _ _ => oq_taggedH l k mf
  | MHpr _ blo bln _ ok => if bl_suffix bln bl then lforallb (fun lh => hpr_iv_ok pf mf blo bln ok (fst lh) (eadd (snd lh) (emulc (-1) (fst lh)))) X else false
  | MMunch _ _ _ | MWmono _ _ | MLaw _ _ _ _ | MCli _ _ _ | MCobj _ _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ => true
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lres_subst (first : positive) (nrl : nat) (nl : positive) (tl : lsubst) : lsubst :=
  match nrl with
  | O => tl
  | S nrl' => lres_subst (Pos.succ first) nrl' (Pos.succ nl) ((first, LBase nl) :: tl)
  end.

Definition sum_post (C : lxcfg) (su : summary) (ss : sstate) (th : subst) (tb : bsubst) (tl : lsubst) (ra : spc) : sstate :=
  let pf := s_pf ss in let mf := s_mf ss in
  let W := sxw th (su_W su) in
  let wcl := w_all_client pf (cranges pf mf) W in let wne := all_nonempty pf W in
  let nx := s_nx ss in
  let th' := res_subst (su_npP su) (su_nr su) nx th in
  let tl' := lres_subst (su_nlP su) (su_nrl su) (s_nl ss) tl in
  let nl' := Pos.add (s_nl ss) (Pos.of_nat (su_nrl su)) in
  let rs := set_regs (s_rs ss) (map (fun rj => (fst rj, sxe th' (EZv (snd rj)))) (su_clob su)) in
  let kept := filter (mf_survives_call C pf (cranges pf mf) mf W wcl wne) mf in
  (* [comment removed for export] *)
  let reest := match opq_required mf (su_oreq su) with Some l => filter (fun f => negb (mf_mem f kept)) l | None => [] end in
  match su_law su with
  | None =>
  let mf' := install_post (kept ++ reest) (map (sxm th' tb tl') (su_mpost su)) in
  let pf' := fold_left (fun l f => pf_add f l) (flat_map (fun f => norm_pf (sxp th' f)) (su_post su)) pf in
  let W' := w_adds pf (s_W ss) W in
  SSTX ra rs mf' pf' W' (Pos.add nx (Pos.of_nat (su_nr su))) false (s_ref ss) (s_nm ss) nl' (s_bl ss)
  | Some l =>
  (* [comment removed for export] *)
  let kc := s_nm ss in let kp := S kc in
  let keptl := filter (law_survives true C l pf (cranges pf mf) mf W wcl wne) mf in
  (* [comment removed for export] *)
  let reestl := match opq_required mf (su_oreq su) with Some l0 => filter (fun f => negb (mf_mem f keptl)) l0 | None => [] end in
  let mf' := install_post (keptl ++ reestl) (map (sxm th' tb tl') (su_mpost su)) in
  let chain := [MMunch (s_W ss) (s_ref ss) kc; MWmono (s_ref ss) kc; MLaw l W kc kp] in
  let pf' := fold_left (fun l f => pf_add f l) (flat_map (fun f => norm_pf (sxp th' f)) (su_post su)) pf in
  SSTX ra rs (chain ++ mf') pf' [] (Pos.add nx (Pos.of_nat (su_nr su))) false kp (S kp) nl' (s_bl ss)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint spine_seps (a n : expr) (bl : bklist) : list pfact :=
  match bl with BL0 | BLV _ => [] | BCons b k bl' => FSep a n b k :: spine_seps a n bl' end.
Fixpoint obj_seps (j : nat) (a n : expr) (pf : list pfact) : list pfact :=
  match pf with
  | [] => []
  | FProp j' [b; k] :: pf' => if Nat.eqb j j' then FSep0 k a n b k :: obj_seps j a n pf' else obj_seps j a n pf'
  | _ :: pf' => obj_seps j a n pf'
  end.
Definition heff_apply (pf : list pfact) (mf : list mfact) (th th' : subst) (obj : option nat) (eff : bleff) (bl : bklist) (kp : nat)
    : option (bklist * bklist * list mfact * list pfact) :=
  match eff with
  | BENone => Some (bl, bl, [], [])
  | BECons ja en => let a := sxe th' (EZv ja) in let n := sxe th' en in
                    Some (BCons a n bl, bl, [MApartBl a n bl],
                          spine_seps a n bl ++ match obj with Some j => obj_seps j a n pf | None => [] end)
  | BEPop ja => match bl_pop pf mf (sxe th (EZv ja)) bl with
                | Some (_, bl') => if bl_based0 bl' then Some (bl', bl', [], []) else None   (* [comment removed for export] *)
                | None => None
                end
  (* [comment removed for export] *)
  | BEOpq => Some (BLV kp, bl, [], [])
  end.

(* [comment removed for export] *)
Definition sum_postH (su : summary) (hc : heapcall) (ss : sstate) (th : subst) (tb : bsubst) (tl : lsubst) (ra : spc)
    (post : list pfact) (mpost : list mfact) (eff : bleff) (hposts : list (nat * list expr)) : option sstate :=
  let pf := s_pf ss in let mf := s_mf ss in
  let X := sxw th (su_W su) in
  let sp := sxe th (EZv (hc_sp hc)) in
  let nx := s_nx ss in
  let th' := res_subst (su_npP su) (su_nr su) nx th in
  let tl' := lres_subst (su_nlP su) (su_nrl su) (s_nl ss) tl in
  let nl' := Pos.add (s_nl ss) (Pos.of_nat (su_nrl su)) in
  let rs := set_regs (s_rs ss) (map (fun rj => (fst rj, sxe th' (EZv (snd rj)))) (su_clob su)) in
  match heap_find mf with
  | None => None
  | Some (bl, ok) =>
  let kc := s_nm ss in let kp := S kc in
  match heff_apply pf mf th th' (hc_obj hc) eff bl kp with
  | None => None
  | Some (blN, blL, extra, pextra) =>
  let l := hc_law hc in
  let kept := filter (heap_survives l pf mf blL sp X) mf in
  let hres := map (fun jx => MHpr (fst jx) bl blN (map (sxe th') (snd jx)) ok) hposts in
  (* [comment removed for export] *)
  let reest := match opq_required mf (su_oreq su) with Some l0 => filter (fun f => negb (mf_mem f kept)) l0 | None => [] end in
  let mf' := install_post (kept ++ MHeap blN ok :: extra ++ hres ++ reest) (map (sxm th' tb tl') mpost) in
  let chain := [MMunch (s_W ss) (s_ref ss) kc; MWmono (s_ref ss) kc; MLawH l blL sp X kc kp] in
  let pf' := fold_left (fun l f => pf_add f l) (flat_map norm_pf pextra ++ flat_map (fun f => norm_pf (sxp th' f)) post) pf in
  Some (SSTX ra rs (chain ++ mf') pf' [] (Pos.add nx (Pos.of_nat (su_nr su))) false kp (S kp) nl' blN)
  end end.

Definition acc_mode (C : lxcfg) : bool := match c_acc C with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition sum_match (C : lxcfg) (genv : list expr) (su : summary) (ss : sstate) : subst * bsubst * lsubst * Z :=
  let pf := s_pf ss in let mf := s_mf ss in let O := oracle_of ss in
  let crs := cranges pf mf in
  match match_regs ss (su_rbind su) [] with
  | None => ([], [], [], 41)
  | Some th0 =>
  match match_globals genv (su_gbind su) th0 with
  | None => ([], [], [], 55)
  | Some th1 =>
  match (match su_sb su, c_acc C with
         | Some i, Some A => bind th1 i (ac_sb A)
         | Some _, None => None
         | None, _ => Some th1
         end) with
  | None => ([], [], [], 47)
  | Some th2 =>
  match match_chunks mf (su_mbind su) th2 [] with
  | None => ([], [], [], 42)
  | Some (th3c, tb3) =>
  match match_arrs pf mf (su_mbind su) th3c [] with
  | None => ([], [], [], 58)
  | Some (th3, tl) =>
  match (match su_stk su with
         | Some (ilo, ihi) => match sub_get th3 ihi with Some h => match_stk mf mf h ilo th3 | None => None end
         | None => Some th3
         end) with
  | None => ([], [], [], 45)
  | Some th4 =>
  let pre_ok (th : subst) :=
      if all_bound th (su_np su) 1%positive
      then lforallb (fun f => pf_decide pf crs O (sxp th f)) (su_pre su) else false in
  match bind_bytes (su_bbind su) (mby_facts mf) th4 tb3 pre_ok with
  | None =>
      (* [comment removed for export] *)
      ([], [], [], Z.max 43
        match bind_bytes (su_bbind su) (mby_facts mf) th4 tb3 (fun _ => true) with
        | None => 43
        | Some (th, _) =>
            if negb (all_bound th (su_np su) 1%positive) then 48 else
            (fix first_bad (l : list pfact) (i : Z) : Z :=
               match l with
               | [] => 43
               | f :: l' => if pf_decide pf crs O (sxp th f) then first_bad l' (i + 1) else 4300 + i
               end) (su_pre su) 1
        end)
  | Some (th, tb) =>
      if negb (all_bbound tb (su_nb su) 1%positive) then ([], [], [], 48)
      else if negb (lforallb (fun f => req_ok C pf crs mf (sxm th tb tl f)) (su_req su)) then ([], [], [], 49)
      else if negb (forallb (fun p => Pos.ltb (fst p) (su_npP su)) th && forallb (fun p => Pos.ltb (fst p) (su_nbP su)) tb
                    && forallb (fun p => Pos.ltb (fst p) (su_nlP su)) tl && lall_bound tl (su_nl su) 1%positive) then ([], [], [], 53)
      else (th, tb, tl, 0)
  end end end end end end end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition carve_chunk (a : expr) (n : Z) (f : mfact) : list mfact :=
  match f with
  | MRw b cs =>
      match ediff_lit a b with
      | Some off =>
          if Z.leb 0 off && Z.ltb 0 n && Z.leb (off + n) (Z.of_N (cells_sizeN cs)) && negb (Z.eqb off 0 && Z.eqb n (Z.of_N (cells_sizeN cs))) then
            match take_cellsx cs off with
            | Some (pre, rest) =>
                match take_cellsx rest n with
                | Some (mid, post) =>
                    (match pre with [] => [] | _ => [MRw b pre] end)
                    ++ MRw a mid :: (match post with [] => [] | _ => [MRw (eadd a (ELit n)) post] end)
                | None => [f]
                end
            | None => [f]
            end
          else [f]
      | None => [f]
      end
  | _ => [f]
  end.

Fixpoint carve_mf (mf : list mfact) (cuts : list (expr * Z)) : list mfact :=
  match cuts with
  | [] => mf
  | (a, n) :: cuts' => carve_mf (flat_map (carve_chunk a n) mf) cuts'
  end.

(* [comment removed for export] *)
Definition su_cuts (C : lxcfg) (genv : list expr) (su : summary) (ss : sstate) : list (expr * Z) :=
  match (match match_regs ss (su_rbind su) [] with Some th0 => match_globals genv (su_gbind su) th0 | None => None end) with
  | None => []
  | Some th1 =>
      let th2 := match su_sb su, c_acc C with
                 | Some i, Some A => match bind th1 i (ac_sb A) with Some th => th | None => th1 end
                 | _, _ => th1
                 end in
      flat_map (fun f => match f with
                         | MRw a pats => if ebound th2 a then [(sxe th2 a, Z.of_N (cells_sizeN pats))] else []
                         | _ => []
                         end) (su_mbind su)
  end.

Definition cell_blob_ok (tb : bsubst) (c : cellx) : bool :=
  match c with XB _ k => bvar_bound tb k | _ => true end.
Definition post_blobs_ok (tb : bsubst) (f : mfact) : bool :=
  match f with MRw _ cs | MRo _ cs => forallb (cell_blob_ok tb) cs | MBy _ _ k => bvar_bound tb k | _ => true end.

(* [comment removed for export] *)
Definition bleff_wf (su : summary) (eff : bleff) : bool :=
  match eff with
  | BENone => true
  | BECons ja en => Pos.ltb ja (su_nallP su) && eloc (su_nallP su) en
  | BEPop ja => Pos.ltb ja (su_npP su)
  | BEOpq => true
  end.
Definition hc_wf (su : summary) (hc : heapcall) (tb : bsubst) : bool :=
  Pos.ltb (hc_sp hc) (su_npP su) && bleff_wf su (hc_eff hc)
  && forallb (fun jx => forallb (eloc (su_nallP su)) (snd jx)) (hc_hpost hc)
  && match hc_alt hc with
     | Some (post2, mpost2, eff2) =>
         forallb (mloc (su_nallP su) (su_nbP su) (su_nlaP su) true) mpost2 && forallb (ploc (su_nallP su)) post2
         && bleff_wf su eff2 && forallb (post_blobs_ok tb) mpost2
     | None => true
     end.

Definition apply_summary0 (C : lxcfg) (genv : list expr) (su : summary) (ss : sstate) : sumres :=
  if negb (su_wf su) then SumFail 50 else
  if negb (Bool.eqb (su_acc su) (acc_mode C)) then SumFail 46 else
  if negb (Nat.eqb (length (s_rs ss)) 31) then SumFail 51 else
  (* [comment removed for export] *)
  if negb (forallb (mflvars_lt (s_nl ss)) (s_mf ss)) then SumFail 60 else
  match s_pc ss with
  | PCret _ => SumFail 40
  | PCz pc =>
      if negb (Z.eqb pc (su_pc su)) then SumFail 40 else
      match (match rd_reg ss 1 with
             | RW j => Some (PCret (RW j))
             | RZ e => match is_lit e with Some ra => Some (PCz (Z.land (zlow 64 ra) (Z.lnot 1))) | None => None end
             end) with
      | None => SumFail 44
      | Some ra =>
          match sum_match C genv su ss with
          | (th, tb, tl, 0) =>
              (* [comment removed for export] *)
              if negb (forallb (post_blobs_ok tb) (su_req su ++ su_mpost su)) then SumFail 55 else
              (* [comment removed for export] *)
              match opq_required (s_mf ss) (su_oreq su) with
              | None => SumFail 56
              | Some _ => match su_heap su, su_law su with
                          | None, None => SumOk (su_nr su) (su_nrl su) (sum_post C su ss th tb tl ra)
                          | None, Some _ =>
                              (* [comment removed for export] *)
                              if Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss)
                              then SumOkL (su_nr su) (su_nrl su) (sum_post C su ss th tb tl ra) else SumFail 57
                          | Some hc, _ =>
                              (* [comment removed for export] *)
                              if Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss) then
                                if negb (hc_wf su hc tb) then SumFail 72 else
                                match sum_postH su hc ss th tb tl ra (su_post su) (su_mpost su) (hc_eff hc) (hc_hpost hc) with
                                | None => SumFail 70
                                | Some ss1 =>
                                    match hc_alt hc with
                                    | None => SumOkM (su_nr su) (su_nrl su) ss1 None
                                    | Some (_, _, BEPop _) => SumFail 73    (* [comment removed for export] *)
                                    | Some (post2, mpost2, eff2) =>
                                        match sum_postH su hc ss th tb tl ra post2 mpost2 eff2 [] with
                                        | None => SumFail 71
                                        | Some ss2 => SumOkM (su_nr su) (su_nrl su) ss1 (Some ss2)
                                        end
                                    end
                                end
                              else SumFail 57
                          end
              end
          | (_, _, _, code) => SumFail code
          end
      end
  end.

(* [comment removed for export] *)
Definition tag_cuts (su : summary) (mf : list mfact) : list (expr * Z) :=
  match su_law su with
  | Some l => flat_map (fun f => match f with MCli l' a (ELit k) => if Nat.eqb l' l then [(a, k)] else [] | _ => [] end) mf
  | None => []
  end.
Definition apply_summary (C : lxcfg) (genv : list expr) (su : summary) (ss : sstate) : sumres :=
  let ss1 := set_mf ss (carve_mf (s_mf ss) (su_cuts C genv su ss ++ tag_cuts su (s_mf ss))) in
  if ss_wf C ss1 && forallb (evars_lt (s_nx ss1)) genv then apply_summary0 C genv su ss1 else SumFail 54.

(* [comment removed for export] *)
Fixpoint sums_at (l : list summary) (pc : Z) : list summary :=
  match l with [] => [] | su :: l' => if Z.eqb (su_pc su) pc then su :: sums_at l' pc else sums_at l' pc end.

Fixpoint apply_sums (C : lxcfg) (genv : list expr) (l : list summary) (ss : sstate) : sumres :=
  match l with
  | [] => SumFail 59
  | [su] => apply_summary C genv su ss
  | su :: l' => match apply_summary C genv su ss with
                | SumOk k kl ss' => SumOk k kl ss'
                | SumOkL k kl ss' => SumOkL k kl ss'
                | SumOkM k kl ss1 ss2 => SumOkM k kl ss1 ss2
                | SumFail _ => apply_sums C genv l' ss
                end
  end.

End LXH.
