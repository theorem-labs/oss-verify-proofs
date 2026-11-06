(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia FMapPositive.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaState LaMem LaStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LAS LAM LAI.
Open Scope Z_scope.

Module LAC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_reg_syms : list (nat * sym) :=
  [(3,4); (4,5); (8,6); (9,7); (18,8); (19,9); (20,10); (21,11); (22,12); (23,13); (24,14); (25,15); (26,16); (27,17)]%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive operand := OReg (r : nat) | OLit (z : Z) | OStk (off w : Z).

Inductive directive :=
| DArr (lo hi : Z)                         (* [comment removed for export] *)
| DFArr (i : nat) (lo hi : Z)              (* [comment removed for export] *)
| DSplit (k : cmpk) (a b : operand)        (* [comment removed for export] *)
| DAssert (k : cmpk) (a b : operand) (fk : farkas).   (* [comment removed for export] *)

Inductive sumkind :=
| SumFail                                   (* [comment removed for export] *)
| SumCBD                                    (* [comment removed for export] *)
| SumMalloc (k : Z)                         (* [comment removed for export] *)
| SumFree5                                  (* [comment removed for export] *)
| SumMemset.                                (* [comment removed for export] *)

Record arrival_hint := AH { ah_src : nat; ah_path : list bool; ah_certs : list (lin * farkas);
                            ah_bind : list (sym * lin) }.   (* [comment removed for export] *)

Record cutpoint := CP {
  cp_pc : Z;
  cp_st : astate;                           (* [comment removed for export] *)
  cp_mu : list lin;
  cp_hints : list arrival_hint;
  cp_cand : list lin                        (* [comment removed for export] *)
}.

Record unitT := Unit {
  un_env   : uenv;
  un_stops : list Z;                        (* [comment removed for export] *)
  un_cuts  : list cutpoint;                 (* [comment removed for export] *)
  un_dirs  : list (Z * directive);
  un_sums  : list (Z * sumkind);
  un_snap  : list (Z * Z);                  (* [comment removed for export] *)
  un_fuel  : nat;                           (* [comment removed for export] *)
  un_forks : nat;                           (* [comment removed for export] *)
  un_total : bool;                          (* [comment removed for export] *)
  un_diag  : bool                           (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition theta := list (sym * lin).
Fixpoint th_get (th : theta) (x : sym) : option lin :=
  match th with [] => None | (y, l) :: r => if Nat.eqb x y then Some l else th_get r x end.
Definition th_fun (th : theta) (x : sym) : option lin := if Nat.ltb x NGLOB then None else th_get th x.
Definition tsub (th : theta) (l : lin) : lin := lsubst (th_fun th) l.

(* [comment removed for export] *)
Fixpoint undetermined (ts : list (sym * Z)) (acc : theta) : list (sym * Z) :=
  match ts with
  | [] => []
  | (x, k) :: r => if (Nat.ltb x NGLOB ||| match th_get acc x with Some _ => true | None => false end)%bool
                   then undetermined r acc else (x, k) :: undetermined r acc
  end.
Definition try_anchor (acc : theta) (t s : aval) : theta :=
  match t, s with
  | LV l, LV sl =>
      match undetermined (lt l) acc with
      | [(u, k)] =>
          if (Z.eqb k 1 ||| Z.eqb k (-1))%bool then
            let rest := lsub l (lscale k (lvar u)) in          (* [comment removed for export] *)
            let v := lscale k (lsub sl (tsub acc rest)) in      (* [comment removed for export] *)
            (u, v) :: acc
          else acc
      | _ => acc
      end
  | _, _ => acc
  end.
Fixpoint anchors_regs (tr sr : list aval) (acc : theta) : theta :=
  match tr, sr with
  | t :: tr', s :: sr' => anchors_regs tr' sr' (try_anchor acc t s)
  | _, _ => acc
  end.
(* [comment removed for export] *)
Fixpoint anchors_cells_ref (tc : list cell) (sc : list cell) (acc : theta) : theta :=
  match tc with
  | [] => acc
  | c :: r =>
      let acc' := match cells_find sc (c_off c) (c_w c) with
                  | Some v' => try_anchor acc (c_val c) v'
                  | None => acc
                  end in
      anchors_cells_ref r sc acc'
  end.
(* [comment removed for export] *)
Definition anchor_wanted (acc : theta) (t : aval) : option (sym * Z * lin) :=
  match t with
  | LV l => match undetermined (lt l) acc with
            | [(u, k)] => if (Z.eqb k 1 ||| Z.eqb k (-1))%bool then Some (u, k, l) else None
            | _ => None
            end
  | _ => None
  end.
Fixpoint anchors_cells (tc : list cell) (sc : list cell) (acc : theta) : theta :=
  match tc with
  | [] => acc
  | c :: r =>
      let acc' := match anchor_wanted acc (c_val c) with
                  | Some (u, k, l) =>
                      match cells_find sc (c_off c) (c_w c) with
                      | Some (LV sl) => (u, lscale k (lsub sl (tsub acc (lsub l (lscale k (lvar u)))))) :: acc
                      | _ => acc
                      end
                  | None => acc
                  end in
      anchors_cells r sc acc'
  end.
Lemma try_anchor_wanted : forall acc t s,
  try_anchor acc t s = match anchor_wanted acc t with
                       | Some (u, k, l) => match s with LV sl => (u, lscale k (lsub sl (tsub acc (lsub l (lscale k (lvar u)))))) :: acc | _ => acc end
                       | None => acc
                       end.
Proof.
  intros acc t s. unfold try_anchor, anchor_wanted.
  destruct t as [|l| |]; try reflexivity.
  destruct (undetermined (lt l) acc) as [|[u k] [|]]; try (destruct s; reflexivity).
  destruct (Z.eqb k 1 ||| Z.eqb k (-1))%bool; destruct s; reflexivity.
Qed.
Lemma anchors_cells_eq : forall tc sc acc, anchors_cells tc sc acc = anchors_cells_ref tc sc acc.
Proof.
  induction tc as [|c r IH]; intros sc acc; [reflexivity|]. cbn [anchors_cells anchors_cells_ref]. cbv zeta.
  rewrite <- IH. f_equal.
  destruct (cells_find sc (c_off c) (c_w c)) as [v'|].
  - rewrite try_anchor_wanted. destruct (anchor_wanted acc (c_val c)) as [[[u k] l]|]; reflexivity.
  - destruct (anchor_wanted acc (c_val c)) as [[[u k] l]|]; reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint anchors_frames (tf sf : list frame) (acc : theta) : theta :=
  match tf, sf with
  | t :: tf', f :: sf' => anchors_frames tf' sf' ((f_sym t, lvar (f_sym f)) :: (f_flag t, lvar (f_flag f)) :: acc)
  | _, _ => acc
  end.
Fixpoint anchors_fcells (tf sf : list frame) (acc : theta) : theta :=
  match tf, sf with
  | t :: tf', f :: sf' => anchors_fcells tf' sf' (anchors_cells (f_cells t) (f_cells f) acc)
  | _, _ => acc
  end.
Definition infer_theta (bind : theta) (T S : astate) : theta :=
  let th0 := anchors_frames (s_frames T) (s_frames S) bind in
  let th1 := anchors_fcells (s_frames T) (s_frames S) (anchors_cells (s_stk T) (s_stk S) (anchors_regs (s_regs T) (s_regs S) th0)) in
  anchors_fcells (s_frames T) (s_frames S) (anchors_cells (s_stk T) (s_stk S) (anchors_regs (s_regs T) (s_regs S) th1)).

(* [comment removed for export] *)
Fixpoint find_cert (cs : list (lin * farkas)) (g : lin) : option farkas :=
  match cs with [] => None | (l, fk) :: r => if leqb l g then Some fk else find_cert r g end.
Definition ent (C : ctx) (certs : list (lin * farkas)) (g : lin) : bool := entails C g (find_cert certs g).
Definition ent_eq (C : ctx) (certs : list (lin * farkas)) (a b : lin) : bool :=
  (leqb a b ||| (ent C certs (lsub a b) &&& ent C certs (lsub b a)))%bool.

Definition match_aval (C : ctx) (certs : list (lin * farkas)) (th : theta) (t s : aval) : bool :=
  match t with
  | Top => true
  | LV l => match s with LV l' => ent_eq C certs (tsub th l) l' | _ => false end
  | CV _ _ _ _ => false
  | XV _ _ => false
  end.
Fixpoint match_regs (C : ctx) certs (th : theta) (tr sr : list aval) : bool :=
  match tr, sr with
  | [], _ => true
  | t :: tr', s :: sr' => (match_aval C certs th t s &&& match_regs C certs th tr' sr')%bool
  | _ :: _, [] => false
  end.
Definition match_cells (C : ctx) certs (th : theta) (tc sc : list cell) : bool :=
  forallb (fun c => match c_val c with
                    | Top => true
                    | v => match cells_find sc (c_off c) (c_w c) with
                           | Some v' => match_aval C certs th v v'
                           | None => false
                           end
                    end) tc.
Definition match_afact (C : ctx) certs (th : theta) (t s : option afact) : bool :=
  match t, s with
  | None, _ => true
  | Some f, Some g => (Z.eqb (af_blo f) (af_blo g) &&& Z.eqb (af_bhi f) (af_bhi g)
                       &&& ent C certs (lsub (af_len g) (tsub th (af_len f)))      (* [comment removed for export] *)
                       &&& (itv_sub (af_first g) (af_first f)                      (* [comment removed for export] *)
                            ||| ent C certs (lneg (tsub th (af_len f)))))%bool          (* [comment removed for export] *)
  | Some _, None => false
  end.
Definition match_arrs (C : ctx) certs (th : theta) (ta sa : list arr) : bool :=
  forallb (fun a => existsb (fun b => (Z.eqb (ar_lo a) (ar_lo b) &&& Z.eqb (ar_hi a) (ar_hi b)
                                       &&& match_afact C certs th (ar_fact a) (ar_fact b))%bool) sa) ta
  &&& forallb (fun b => existsb (fun a => (Z.eqb (ar_lo a) (ar_lo b) &&& Z.eqb (ar_hi a) (ar_hi b))%bool) ta) sa.
Fixpoint zl_eqb (a b : list Z) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (Z.eqb x y &&& zl_eqb a' b')%bool | _, _ => false end.
Fixpoint match_frames (C : ctx) certs (th : theta) (tf sf : list frame) : bool :=
  match tf, sf with
  | [], [] => true
  | t :: tf', f :: sf' => (Z.eqb (f_cls t) (f_cls f) &&& zl_eqb (f_sh t) (f_sh f)
                           &&& ent_eq C certs (tsub th (lvar (f_sym t))) (lvar (f_sym f))
                           &&& ent_eq C certs (tsub th (lvar (f_flag t))) (lvar (f_flag f))
                           &&& match_cells C certs th (f_cells t) (f_cells f) &&& match_arrs C certs th (f_arrs t) (f_arrs f)
                           &&& match_frames C certs th tf' sf')%bool
  | _, _ => false
  end.
Fixpoint bm_eqb (a b : list (Z * Z)) : bool :=
  match a, b with
  | [], [] => true
  | (x, y) :: a', (u, v) :: b' => (Z.eqb x u &&& Z.eqb y v &&& bm_eqb a' b')%bool
  | _, _ => false
  end.
Definition match_facts (C : ctx) certs (th : theta) (T : ctx) : bool :=
  forallb (fun f => ent C certs (tsub th f)) (cfacts T)
  &&& forallb (fun xb : sym * itv =>
                let (x, i) := xb in
                let e := tsub th (lvar x) in
                (match ilo i with Some lo => ent C certs (laddc e (- lo)) | None => true end
                 &&& match ihi i with Some hi => ent C certs (laddc (lneg e) hi) | None => true end)%bool) (cb T).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lex_chk (C : ctx) certs (cur start : list lin) : bool :=
  match cur, start with
  | c :: cr, s :: sr =>
      if ent C certs (laddc (lsub s c) (-1)) then Nat.eqb (length cr) (length sr)   (* [comment removed for export] *)
      else (ent_eq C certs c s &&& lex_chk C certs cr sr)%bool
  | _, _ => false
  end.
Definition mu_lex (C : ctx) certs (cur start : list lin) : bool :=
  match start with
  | [] => match cur with [] => false | _ => true end
  | _ => lex_chk C certs cur start
  end.
Definition mu_ok (C : ctx) certs (cur start : list lin) : bool :=
  (forallb (fun c => ent C certs c) cur &&& mu_lex C certs cur start)%bool.

(* [comment removed for export] *)
Inductive mismatch :=
| MPc | MAnchor | MReg (r : nat) | MCell (off w : Z) | MArrs | MAbs | MFact (f : lin) | MBoundLo (x : sym) | MBoundHi (x : sym)
| MResv | MPcache | MMu | MPay (off : lin) | MFrames.

(* [comment removed for export] *)
Definition pay_justified (C : ctx) certs (sp : list (lin * itv)) (spc : list (lin * Z * sym)) (o : lin) (i : itv) : bool :=
  existsb (fun e : lin * itv => (ent_eq C certs o (fst e) &&& itv_sub (snd e) i)%bool) sp
  ||| existsb (fun e : lin * Z * sym => let '(o', sx, x) := e in
               (Z.eqb sx 0 &&& ent_eq C certs o o'
                &&& match ilo i with Some lo => ent C certs (laddc (lvar x) (- lo)) | None => true end
                &&& match ihi i with Some hi => ent C certs (laddc (lneg (lvar x)) hi) | None => true end)%bool) spc.
Definition pay_report (C : ctx) certs (th : theta) (tp : list (lin * itv)) (S : astate) : list mismatch :=
  concat (map (fun e : lin * itv => if pay_justified C certs (s_pay S) (s_pcache S) (tsub th (fst e)) (snd e) then [] else [MPay (fst e)]) tp).

Fixpoint regs_report (C : ctx) certs (th : theta) (tr sr : list aval) (r : nat) : list mismatch :=
  match tr, sr with
  | [], _ => []
  | t :: tr', s :: sr' => (if match_aval C certs th t s then [] else [MReg r]) ++ regs_report C certs th tr' sr' (S r)
  | _ :: _, [] => [MReg r]
  end.
Definition cells_report (C : ctx) certs (th : theta) (tc sc : list cell) : list mismatch :=
  concat (map (fun c => match c_val c with
                        | Top => []
                        | v => match cells_find sc (c_off c) (c_w c) with
                               | Some v' => if match_aval C certs th v v' then [] else [MCell (c_off c) (c_w c)]
                               | None => [MCell (c_off c) (c_w c)]
                               end
                        end) tc).
Definition facts_report (C : ctx) certs (th : theta) (T : ctx) : list mismatch :=
  concat (map (fun f => if ent C certs (tsub th f) then [] else [MFact f]) (cfacts T))
  ++ concat (map (fun xb : sym * itv =>
                let (x, i) := xb in
                let e := tsub th (lvar x) in
                (match ilo i with Some lo => if ent C certs (laddc e (- lo)) then [] else [MBoundLo x] | None => [] end)
                ++ (match ihi i with Some hi => if ent C certs (laddc (lneg e) hi) then [] else [MBoundHi x] | None => [] end)) (cb T)).

(* [comment removed for export] *)
Fixpoint tsyms_in (ts : list (sym * Z)) (th : theta) : bool :=
  match ts with [] => true | (x, _) :: r => ((Nat.ltb x NGLOB ||| match th_get th x with Some _ => true | None => false end) &&& tsyms_in r th)%bool end.
Definition lin_in (l : lin) (th : theta) : bool := tsyms_in (lt l) th.
Definition aval_in_th (v : aval) (th : theta) : bool :=
  match v with Top => true | LV l => lin_in l th | CV _ _ a b => (lin_in a th &&& lin_in b th)%bool
  | XV a b => (lin_in a th &&& lin_in b th)%bool end.
Definition template_closed (T : astate) (mu : list lin) (th : theta) : bool :=
  (forallb (fun v => aval_in_th v th) (s_regs T)
   &&& forallb (fun f => lin_in f th) (cfacts (s_ctx T))
   &&& forallb (fun xb : sym * itv => (Nat.ltb (fst xb) NGLOB ||| match th_get th (fst xb) with Some _ => true | None => false end)%bool) (cb (s_ctx T))
   &&& forallb (fun c => aval_in_th (c_val c) th) (s_stk T)
   &&& forallb (fun a => match ar_fact a with None => true | Some f => lin_in (af_len f) th end) (s_arrs T)
   &&& forallb (fun e : lin * itv => lin_in (fst e) th) (s_pay T)
   &&& forallb (fun f => match th_get th (f_sym f), th_get th (f_flag f) with Some _, Some _ => true | _, _ => false end
                         &&& forallb (fun c => aval_in_th (c_val c) th) (f_cells f)
                         &&& forallb (fun a => match ar_fact a with None => true | Some af => lin_in (af_len af) th end) (f_arrs f)) (s_frames T)
   &&& forallb (fun m => lin_in m th) mu)%bool.

Definition match_report (total : bool) (S : astate) (cp : cutpoint) (mu_start : list lin) (h : arrival_hint) : list mismatch :=
  let certs := ah_certs h in
  let T := cp_st cp in
  if negb (Z.eqb (s_pc S) (cp_pc cp)) then [MPc] else
  let th := infer_theta (ah_bind h) T S in
  if negb (template_closed T (cp_mu cp) th) then [MAnchor] else
  let C := s_ctx S in
  regs_report C certs th (s_regs T) (s_regs S) 0
  ++ cells_report C certs th (s_stk T) (s_stk S)
  ++ (if match_arrs C certs th (s_arrs T) (s_arrs S) then [] else [MArrs])
  ++ (if match_frames C certs th (s_frames T) (s_frames S) then [] else [MFrames])
  ++ (if bm_eqb (s_abs T) (s_abs S) then [] else [MAbs])
  ++ facts_report C certs th (s_ctx T)
  ++ (if (match s_resv T, s_resv S with None, None => true | Some a, Some b => Z.eqb a b | _, _ => false end) then [] else [MResv])
  ++ (match s_pcache T with [] => [] | _ => [MPcache] end)
  ++ pay_report C certs th (s_pay T) S
  ++ (if total then (if mu_ok C certs (map (tsub th) (cp_mu cp)) mu_start then [] else [MMu]) else []).

Definition match_cut (total : bool) (S : astate) (cp : cutpoint) (mu_start : list lin) (h : arrival_hint) : bool :=
  match match_report total S cp mu_start h with [] => true | _ => false end.

(* [comment removed for export] *)
Definition match_report_fast (total : bool) (S : astate) (cp : cutpoint) (mu_start : list lin) (h : arrival_hint) : list mismatch :=
  let certs := ah_certs h in
  let T := cp_st cp in
  if negb (Z.eqb (s_pc S) (cp_pc cp)) then [MPc] else
  let th := infer_theta (ah_bind h) T S in
  if negb (template_closed T (cp_mu cp) th) then [MAnchor] else
  let C := s_ctx S in
  if negb (match_regs C certs th (s_regs T) (s_regs S)) then [MReg 0] else
  if negb (match_cells C certs th (s_stk T) (s_stk S)) then [MCell 0 0] else
  if negb (match_arrs C certs th (s_arrs T) (s_arrs S)) then [MArrs] else
  if negb (match_frames C certs th (s_frames T) (s_frames S)) then [MFrames] else
  if negb (bm_eqb (s_abs T) (s_abs S)) then [MAbs] else
  if negb (match_facts C certs th (s_ctx T)) then [MFact (lconst 0)] else
  if negb (match s_resv T, s_resv S with None, None => true | Some a, Some b => Z.eqb a b | _, _ => false end) then [MResv] else
  match s_pcache T with
  | _ :: _ => [MPcache]
  | [] =>
      match pay_report C certs th (s_pay T) S with
      | m :: _ => [m]
      | [] => if total then (if mu_ok C certs (map (tsub th) (cp_mu cp)) mu_start then [] else [MMu]) else []
      end
  end.

Lemma forallb_concat_nil : forall {A B} (f : A -> bool) (g : A -> list B) (l : list A),
  (forall x, f x = true -> g x = []) -> forallb f l = true -> concat (map g l) = [].
Proof.
  intros A B f g l Hfg. induction l as [|x r IH]; intros H; [reflexivity|].
  cbn [forallb] in H. cbn [map concat]. destruct (f x) eqn:E; [|discriminate].
  rewrite (Hfg x E). cbn. apply IH. exact H.
Qed.
Lemma match_regs_report : forall C certs th tr sr r, match_regs C certs th tr sr = true -> regs_report C certs th tr sr r = [].
Proof.
  intros C certs th tr. induction tr as [|t tr' IH]; intros sr r H; [reflexivity|].
  destruct sr as [|s sr']; cbn [match_regs] in H; [discriminate|]. cbn [regs_report].
  destruct (match_aval C certs th t s); [|discriminate]. cbn. apply IH. exact H.
Qed.
Lemma match_cells_report : forall C certs th tc sc, match_cells C certs th tc sc = true -> cells_report C certs th tc sc = [].
Proof.
  intros C certs th tc sc H. unfold match_cells in H. unfold cells_report.
  eapply forallb_concat_nil; [|exact H]. intros c Hc. cbv beta in Hc |- *.
  destruct (c_val c); [reflexivity| | |];
    (destruct (cells_find sc (c_off c) (c_w c)); [|discriminate]; rewrite Hc; reflexivity).
Qed.
Lemma match_facts_report : forall C certs th T, match_facts C certs th T = true -> facts_report C certs th T = [].
Proof.
  intros C certs th T H. unfold match_facts in H. unfold facts_report.
  match type of H with (if ?a then ?b else false) = true => destruct a eqn:HA; [|discriminate]; rename H into HB end.
  rewrite (forallb_concat_nil (fun f => ent C certs (tsub th f)) _ (cfacts T)); [| | exact HA].
  2:{ intros f Hf. rewrite Hf. reflexivity. }
  cbn [app].
  apply (forallb_concat_nil (fun xb : sym * itv => let (x, i) := xb in
            (match ilo i with Some lo => ent C certs (laddc (tsub th (lvar x)) (- lo)) | None => true end
             &&& match ihi i with Some hi => ent C certs (laddc (lneg (tsub th (lvar x))) hi) | None => true end)%bool) _ (cb T)); [|exact HB].
  intros [x i] Hxi. cbv beta in Hxi |- *.
  destruct (ilo i) as [lo|]; destruct (ihi i) as [hi|]; cbn [app] in Hxi |- *;
    repeat match goal with |- context [if ?c then [] else _] => destruct c; [|try discriminate] end;
    try reflexivity; try discriminate.
  all: cbv beta iota in Hxi; try discriminate; try reflexivity.
Qed.
Lemma match_report_fast_empty : forall total S cp mu_start h,
  match_report_fast total S cp mu_start h = [] -> match_report total S cp mu_start h = [].
Proof.
  intros total S cp mu_start h H. unfold match_report_fast in H. unfold match_report.
  destruct (negb (Z.eqb (s_pc S) (cp_pc cp))); [discriminate|].
  destruct (negb (template_closed (cp_st cp) (cp_mu cp) (infer_theta (ah_bind h) (cp_st cp) S))); [discriminate|].
  destruct (match_regs _ _ _ _ _) eqn:E1; [|discriminate]. cbn [negb] in H.
  destruct (match_cells _ _ _ _ _) eqn:E2; [|discriminate]. cbn [negb] in H.
  destruct (match_arrs _ _ _ _ _) eqn:E3; [|discriminate]. cbn [negb] in H.
  destruct (match_frames _ _ _ _ _) eqn:E3'; [|discriminate]. cbn [negb] in H.
  destruct (bm_eqb _ _) eqn:E4; [|discriminate]. cbn [negb] in H.
  destruct (match_facts _ _ _ _) eqn:E5; [|discriminate]. cbn [negb] in H.
  match type of H with (if negb ?c then _ else _) = [] => destruct c eqn:E6; [|discriminate]; cbn [negb] in H end.
  rewrite (match_regs_report _ _ _ _ _ 0 E1), (match_cells_report _ _ _ _ _ E2), (match_facts_report _ _ _ _ E5). cbn.
  destruct (s_pcache (cp_st cp)); [|discriminate]. cbn.
  destruct (pay_report _ _ _ _ _); [|discriminate]. cbn. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint cand_refuted (C : ctx) certs (th : theta) (cs : list lin) (k : nat) : list nat :=
  match cs with
  | [] => []
  | l :: r => (if (lin_in l th &&& ent C certs (tsub th l))%bool then [] else [k]) ++ cand_refuted C certs th r (S k)
  end.
Definition cand_report (S : astate) (cp : cutpoint) (h : arrival_hint) : list nat :=
  match cp_cand cp with
  | [] => []
  | cs => let T := cp_st cp in
          let th := infer_theta (ah_bind h) T S in
          cand_refuted (s_ctx S) (ah_certs h) th cs 0
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reg_is_sym (S : astate) (r : nat) (x : sym) : bool :=
  match getreg S r with LV l => leqb l (lvar x) | _ => false end.
Definition reg_is_lit (S : astate) (r : nat) (z : Z) : bool :=
  match getreg S r with LV l => leqb l (lconst (snorm z)) | _ => false end.
Definition exit_ok (U : unitT) (S : astate) : bool :=
  (reg_is_sym S 2 SYM_SP0
   &&& forallb (fun rx : nat * sym => if Nat.eqb (fst rx) 4 then reg_is_lit S 4 (ue_tp (un_env U)) else reg_is_sym S (fst rx) (snd rx)) cs_reg_syms
   &&& match getreg S 10 with LV l => leqb l (lconst 0) | _ => false end
   &&& (bm_eqb (s_abs S) [] ||| bm_eqb (s_abs S) (un_snap U))
   &&& match s_resv S with None => true | _ => false end
   &&& match s_frames S with [] => true | _ => false end)%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eval_operand (S : astate) (o : operand) : option (aval * astate) :=
  match o with
  | OReg r => Some (getreg S r, S)
  | OLit z => Some (alit z, S)
  | OStk off w => None   (* [comment removed for export] *)
  end.

Definition mk_cond (S : astate) (k : cmpk) (a b : operand) : option cond :=
  match eval_operand S a, eval_operand S b with
  | Some (LV x, _), Some (LV y, _) =>
      let C := s_ctx S in
      match k with
      | CK_LTU => if (uexact C x &&& uexact C y)%bool then Some (false, CK_LTU, x, y) else None
      | CK_LT => if (sexact C x &&& sexact C y)%bool then Some (false, CK_LT, x, y) else None
      | CK_EQ => Some (false, CK_EQ, x, y)
      end
  | _, _ => None
  end.

Fixpoint dirs_at (ds : list (Z * directive)) (pc : Z) : list directive :=
  match ds with [] => [] | (p, d) :: r => if Z.eqb p pc then d :: dirs_at r pc else dirs_at r pc end.
Fixpoint sum_at (ss : list (Z * sumkind)) (pc : Z) : option sumkind :=
  match ss with [] => None | (p, s) :: r => if Z.eqb p pc then Some s else sum_at r pc end.
Fixpoint cuts_at (cs : list cutpoint) (pc : Z) (i : nat) : list (nat * cutpoint) :=
  match cs with [] => [] | c :: r => (if Z.eqb (cp_pc c) pc then [(i, c)] else []) ++ cuts_at r pc (S i) end.
Fixpoint path_eqb (a b : list bool) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (Bool.eqb x y &&& path_eqb a' b')%bool
  | _, _ => false
  end.
Fixpoint hint_for (hs : list arrival_hint) (src : nat) (path : list bool) : arrival_hint :=
  match hs with
  | [] => AH src path [] []
  | h :: r => if (Nat.eqb (ah_src h) src &&& path_eqb (ah_path h) path)%bool then h else hint_for r src path
  end.

(* [comment removed for export] *)
Inductive dres := DOk (S : astate) | DFork (c : cond) (S : astate) | DFail (what : Z).

Definition apply_dir (U : uenv) (S : astate) (d : directive) : dres :=
  match d with
  | DArr lo hi =>
      match sp_off S with
      | Some k => match declare_array U S (k + lo) (k + hi) with Some S' => DOk S' | None => DFail 1 end
      | None => DFail 2
      end
  | DFArr i lo hi =>
      match declare_frame_array S i lo hi with Some S' => DOk S' | None => DFail 1 end
  | DSplit k a b =>
      match mk_cond S k a b with Some c => DFork c S | None => DFail 3 end
  | DAssert k a b fk =>
      match mk_cond S k a b with
      | Some (_, CK_EQ, x, y) =>
          let d := lsub x y in
          if (entails (s_ctx S) d (Some fk) &&& entails (s_ctx S) (lneg d) (Some fk))%bool then DOk (learn_eq S d) else DFail 4
      | Some (_, _, x, y) =>
          let g := laddc (lsub y x) (-1) in
          if entails (s_ctx S) g (Some fk) then DOk (learn S g) else DFail 5
      | None => DFail 6
      end
  end.

(* [comment removed for export] *)
Definition keep_regs : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Fixpoint havoc_regs (rs : list aval) (i : nat) : list aval :=
  match rs with
  | [] => []
  | v :: r => (if existsb (Nat.eqb i) keep_regs then v else Top) :: havoc_regs r (S i)
  end.

(* [comment removed for export] *)
Definition sext32_view (C : ctx) (l : lin) : option lin :=
  if sexact32 C l then Some l else None.
(* [comment removed for export] *)
Definition low32s_view (C : ctx) (l : lin) : option lin :=
  if sexact32 C l then Some l
  else if in_range C l two31 two32 then Some (laddc l (- two32))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint sh_zrun (sh : list Z) (g : nat) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => match nth_error sh g with
              | Some s => if Z.eqb s 0 then 8 + sh_zrun sh (S g) fuel' else 0
              | None => 0
              end
  end.
Definition cbd_core (U : uenv) (S : astate) : astate + Z :=
  let C := s_ctx S in
  let fr := ue_cbd_fr U in
  if negb (Z.eqb (s_pc S) (ue_cbd_pc U) &&& Z.leb 0 fr) then inr 11 else
  if existsb (fun f => Z.eqb (f_cls f) 5) (s_frames S) then inr 22 else
  match sp_off S, getreg S 1, getreg S 10, getreg S 11, getreg S 12, getreg S 14 with
  | Some k, LV lra, a0, LV l1, LV l2, LV l4 =>
      if negb (reg_is_lit S 4 (ue_tp U)) then inr 12 else
      match is_const lra, sext32_view C l1, low32s_view C l4 with
      | Some ra, Some len, Some e =>
          if negb (in_window U (k - fr) fr &&& Z.eqb (k mod 16) 0 &&& Z.eqb (ra mod 4) 0 &&& Z.leb 0 ra &&& Z.ltb ra two64) then inr 14 else
          (* [comment removed for export] *)
          let okbuf :=
            match classify (s_frames S) a0 with
            | Some (AFrm i off) =>
                match nth_frame (s_frames S) i with
                | Some f =>
                    match arr_find (f_arrs f) C (lconst off) 1 with
                    | Some a => match ar_fact a with
                                | Some af => if (Z.eqb (af_blo af) 48 &&& Z.eqb (af_bhi af) 57 &&& Z.leb 0 off &&& Z.eqb (off mod 8) 0
                                                 &&& entails C (lsub (laddc (af_len af) (ar_lo a)) (laddc len off)) None)%bool
                                             then Some (f, off) else None
                                | None => None end
                    | None => None end
                | None => None end
            | _ => None
            end in
          match okbuf with
          | None => inr 15
          | Some (f, off) =>
          let oklen := (entails C (laddc len (-1)) None &&& entails C (laddc (lneg len) 780) None)%bool in
          let okexp := (sexact32 C l2 &&& entails C (laddc (ladd len l2) 323) None &&& entails C (laddc (lneg (ladd len l2)) 309) None)%bool in
          let oke := (entails C (laddc e 2047) None &&& entails C (laddc (lneg e) 2047) None)%bool in
          (* [comment removed for export] *)
          let acc := sh_zrun (f_sh f) (Z.to_nat (off / 8)) (Z.to_nat (f_shn f)) in
          let oksh := entails C (laddc (lneg len) acc) None in
          (* [comment removed for export] *)
          let nostraddle := (forallb (fun c => Z.leb (c_off c + c_w c) k ||| Z.leb k (c_off c)) (s_stk S)
                             &&& forallb (fun a => Z.leb (ar_hi a) k ||| Z.leb k (ar_lo a)) (s_arrs S))%bool in
          if negb oklen then inr 16 else if negb okexp then inr 17 else if negb oke then inr 18 else if negb oksh then inr 21
          else if negb nostraddle then inr 19 else
          match s_resv S with
          | Some _ => inr 20
          | None =>
            let S1 := drop_below S k in
            let S2 := set_regs S1 (havoc_regs (s_regs S1) 0) in
            let (r, S3) := fresh_val S2 (Itv (Some (-1)) (Some 1)) in
            inl (set_pc (setreg (setreg S3 4 (alit (ue_tp U))) 10 r) ra)
          end end
      | _, _, _ => inr 13
      end
  | _, _, _, _, _, _ => inr 12
  end.
Definition apply_cbd (U : uenv) (S : astate) : option astate :=
  match cbd_core U S with inl S' => Some S' | inr _ => None end.
Definition cbd_diag (U : uenv) (S : astate) : Z :=
  match cbd_core U S with inl _ => 1 | inr c => c end.

(* [comment removed for export] *)
Fixpoint mallocs_at (ms : list (Z * Z)) (pc : Z) : option Z :=
  match ms with [] => None | (p, k) :: r => if Z.eqb p pc then Some k else mallocs_at r pc end.
Definition zeros (n : nat) : list Z := repeat 0 n.
Definition malloc_core (U : uenv) (S : astate) (k : Z) : astate + Z :=
  let C := s_ctx S in
  let mfr := ue_malloc_fr U in
  if negb ((Z.eqb k 1 ||| Z.eqb k 4 ||| Z.eqb k 5) &&& Z.leb 0 mfr)%bool then inr 31 else
  if negb (match mallocs_at (ue_malloc U) (s_pc S) with Some k' => Z.eqb k' k | None => false end) then inr 31 else
  match sp_off S, getreg S 1 with
  | Some ksp, LV lra =>
      match is_const lra with
      | None => inr 32
      | Some ra =>
          if negb (Z.eqb (ra mod 4) 0 &&& Z.leb 0 ra &&& Z.ltb ra two64) then inr 32 else
          if negb (in_window U (ksp - mfr) mfr &&& Z.eqb (ksp mod 16) 0) then inr 33 else
          if negb (reg_is_lit S 4 (ue_tp U)) then inr 34 else
          if negb (Nat.leb (length (s_frames S)) 2) then inr 35 else
          (* [comment removed for export] *)
          if negb (forallb (fun c => Z.leb (c_off c + c_w c) ksp ||| Z.leb ksp (c_off c)) (s_stk S)
                   &&& forallb (fun a => Z.leb (ar_hi a) ksp ||| Z.leb ksp (ar_lo a)) (s_arrs S))%bool then inr 33 else
          match s_resv S with
          | Some _ => inr 36
          | None =>
            let S1 := drop_below S ksp in
            let S2 := set_regs S1 (havoc_regs (s_regs S1) 0) in
            (* [comment removed for export] *)
            let (g, S3) := fresh S2 (Itv (Some 0x19a00) (Some 0x1fffffffffe)) in           (* [comment removed for export] *)
            let (q, S4) := fresh S3 (Itv (Some 0x669000) (Some 0x7fffffffffff)) in         (* [comment removed for export] *)
            let sz := 2 ^ (6 + k) in
            let fr := Frame g k [Cell (sz - 8) 8 (LV (lvar q))] [] (zeros (Z.to_nat (2 ^ (3 + k)))) q in
            let S5 := set_frames S4 (s_frames S4 ++ [fr]) in
            inl (set_pc (setreg (setreg S5 4 (alit (ue_tp U))) 10 (LV (lscale 64 (lvar g)))) ra)
          end
      end
  | _, _ => inr 33
  end.
Definition apply_malloc (U : uenv) (S : astate) (k : Z) : option astate :=
  match malloc_core U S k with inl S' => Some S' | inr _ => None end.

(* [comment removed for export] *)
Fixpoint bm_fill (bm : list (Z * Z)) (a : Z) (n : nat) (c : Z) : list (Z * Z) :=
  match n with O => bm | S n' => bm_fill (bm_set bm a c) (a + 1) n' c end.
Definition havoc_a1_a6 (rs : list aval) : list aval :=
  list_set (list_set (list_set (list_set (list_set (list_set rs 11 Top) 12 Top) 13 Top) 14 Top) 15 Top) 16 Top.
Definition memset_core (U : uenv) (S : astate) : astate + Z :=
  let C := s_ctx S in
  if negb (Z.eqb (s_pc S) (ue_memset U)) then inr 41 else
  match getreg S 1 with
  | LV lra =>
    match is_const lra with
    | None => inr 41
    | Some ra =>
      if negb (Z.eqb (ra mod 4) 0 &&& Z.leb 0 ra &&& Z.ltb ra two64) then inr 41 else
      match aval_litC C (getreg S 12) with
      | None => inr 42
      | Some n =>
        if negb (Z.leb 0 n &&& Z.leb n 4096) then inr 42 else
        match getreg S 11 with
        | LV l1 =>
          (* [comment removed for export] *)
          match and_lowlit C l1 8 with
          | None => inr 43
          | Some c =>
            match s_resv S with Some _ => inr 45 | None =>
            let a0 := getreg S 10 in
            let res :=
              match classify (s_frames S) a0 with
              | Some (AShFrm i t) =>
                  match nth_frame (s_frames S) i, is_const t with
                  | Some f, Some tc =>
                      if (Z.leb 0 tc &&& Z.leb (tc + n) (f_shn f))%bool then
                        Some (set_frames S (upd_frame (s_frames S) i
                               (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_fill (f_sh f) (Z.to_nat tc) (Z.to_nat n) c) (f_flag f))))
                      else None
                  | _, _ => None
                  end
              | Some (AFrm i off) =>
                  match nth_frame (s_frames S) i with
                  | Some f => match memset_space 0 (f_size f) (f_cells f) (f_arrs f) off n c with
                              | Some (cs, ars) => Some (set_frames S (upd_frame (s_frames S) i (frame_set_space f cs ars)))
                              | None => None end
                  | None => None
                  end
              | Some (AStk off) =>
                  match memset_space (- ue_fr U) 0 (s_stk S) (s_arrs S) off n c with
                  | Some (cs, ars) => Some (set_arrs (set_stk S cs) ars)
                  | None => None
                  end
              | Some (AAbs a) =>
                  if (in_ranges a n (ue_rw U) &&& ro_clear U a n &&& Z.ltb 0 n)%bool then Some (set_pay (set_pcache (set_abs S (bm_fill (s_abs S) a (Z.to_nat n) c)) []) [])
                  else None
              | _ => None
              end in
            match res with
            | None => inr 44
            | Some S1 => inl (set_pc (set_regs S1 (havoc_a1_a6 (s_regs S1))) ra)
            end end
          end
        | _ => inr 43
        end
      end
    end
  | _ => inr 41
  end.
Definition apply_memset (U : uenv) (S : astate) : option astate :=
  match memset_core U S with inl S' => Some S' | inr _ => None end.
Definition sum_diag (U : uenv) (S : astate) (sk : sumkind) : Z :=
  match sk with
  | SumCBD => cbd_diag U S
  | SumMalloc k => match malloc_core U S k with inl _ => 1 | inr c => c end
  | SumMemset => match memset_core U S with inl _ => 1 | inr c => c end
  | _ => 0
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive leaf :=
| LArrive (cut : Z) (src : nat) (path : list bool) (ok : bool) (reports : list (nat * list mismatch))
          (cands : list (nat * list nat))   (* [comment removed for export] *)
          (S : astate)
| LExit (path : list bool) (ok : bool) (S : astate)
| LFail (pc : Z) (path : list bool) (r : reason) (S : astate)
| LInfeasible (path : list bool).
(* [comment removed for export] *)

Definition leaf_ok (l : leaf) : bool :=
  match l with
  | LArrive _ _ _ ok _ _ _ => ok
  | LExit _ ok _ => ok
  | LFail _ _ _ _ => false
  | LInfeasible _ => true
  end.

Fixpoint apply_dirs (U : uenv) (S : astate) (ds : list directive) : dres :=
  match ds with
  | [] => DOk S
  | d :: r => match apply_dir U S d with
              | DOk S' => if wf_state S' then apply_dirs U S' r else DFail 9
              | other => other      (* [comment removed for export] *)
              end
  end.

(* [comment removed for export] *)
Definition degrade_reg (st : astate) (r : nat) : astate :=
  match getreg st r with
  | CV _ _ _ _ | XV _ _ => let (v, st1) := degrade st (getreg st r) in setreg st1 r v
  | _ => st
  end.
Fixpoint degrade_regs_ref (st : astate) (rs : list nat) : option astate :=
  match rs with
  | [] => Some st
  | r :: rs' => let st1 := degrade_reg st r in if wf_state st1 then degrade_regs_ref st1 rs' else None
  end.
(* [comment removed for export] *)
Fixpoint degrade_regs_go (st : astate) (rs : list nat) : option astate :=
  match rs with
  | [] => Some st
  | r :: rs' =>
      match getreg st r with
      | CV _ _ _ _ | XV _ _ => let st1 := degrade_reg st r in if wf_state st1 then degrade_regs_go st1 rs' else None
      | _ => degrade_regs_go st rs'
      end
  end.
Definition degrade_regs (st : astate) (rs : list nat) : option astate :=
  if wf_state st then degrade_regs_go st rs else degrade_regs_ref st rs.
Lemma degrade_regs_go_eq : forall rs st, wf_state st = true -> degrade_regs_go st rs = degrade_regs_ref st rs.
Proof.
  induction rs as [|r rs IH]; intros st Hwf; [reflexivity|]. cbn [degrade_regs_go degrade_regs_ref]. cbv zeta.
  destruct (getreg st r) eqn:Hg;
    first [ destruct (wf_state (degrade_reg st r)) eqn:Hw; [apply IH; exact Hw | reflexivity]
          | assert (E : degrade_reg st r = st) by (unfold degrade_reg; rewrite Hg; reflexivity);
            rewrite E, Hwf; apply IH; exact Hwf ].
Qed.
Lemma degrade_regs_eq : forall st rs, degrade_regs st rs = degrade_regs_ref st rs.
Proof. intros st rs. unfold degrade_regs. destruct (wf_state st) eqn:Hwf; [apply degrade_regs_go_eq; exact Hwf | reflexivity]. Qed.
Definition all_xregs : list nat := seq 1 31.

Section Explore.
  Variable Un : unitT.
  Let U := un_env Un.
  Variable start_idx : nat.
  Variable start : cutpoint.

  (* [comment removed for export] *)
  Fixpoint explore (fuel : nat) (forks : nat) (st : astate) (steps : nat) (path : list bool) (acc : list leaf) : list leaf :=
    match fuel with
    | O => LFail (s_pc st) (rev path) R_FUEL (set_depth st steps) :: acc
    | Datatypes.S fuel' =>
      if negb (wf_state st) then LFail (s_pc st) (rev path) R_UNSUPPORTED (set_depth st steps) :: acc else
      (* [comment removed for export] *)
      if ctx_contra (s_ctx st) None then LInfeasible (rev path) :: acc else
      let pc := s_pc st in
      (* [comment removed for export] *)
      let nsteps := fun S' : astate => if Z.eqb (s_pc S') pc then steps else Datatypes.S steps in
      (* [comment removed for export] *)
      match (match steps with O => None | _ => if existsb (Z.eqb pc) (un_stops Un) then Some (cuts_at (un_cuts Un) pc 0) else None end) with
      | Some cps =>
          match degrade_regs st all_xregs with
          | None => LFail pc (rev path) R_UNSUPPORTED (set_depth st steps) :: acc
          | Some st' =>
          let mrep := if un_diag Un then match_report else match_report_fast in
          let reps := map (fun icp : nat * cutpoint =>
                             let (i, cp) := icp in
                             (i, mrep (un_total Un) st' cp (cp_mu start) (hint_for (cp_hints cp) start_idx (rev path)))) cps in
          let ok := existsb (fun ir : nat * list mismatch => match snd ir with [] => true | _ => false end) reps in
          let cands := map (fun icp : nat * cutpoint =>
                             let (i, cp) := icp in (i, cand_report st' cp (hint_for (cp_hints cp) start_idx (rev path)))) cps in
          LArrive pc start_idx (rev path) ok reps cands (set_depth st' steps) :: acc
          end
      | None =>
        match sum_at (un_sums Un) pc with
        | Some SumFail => LFail pc (rev path) (R_SUMMARY 0) st :: acc
        | Some SumFree5 => LFail pc (rev path) (R_SUMMARY 3) st :: acc      (* [comment removed for export] *)
        | Some sk =>
            match (match sk with SumCBD => apply_cbd U st | SumMalloc k => apply_malloc U st k | SumMemset => apply_memset U st
                   | _ => None end) with
            | Some S' => if wf_state S' then explore fuel' forks S' (Datatypes.S steps) path acc
                         else LFail pc (rev path) (R_SUMMARY 2) st :: acc
            | None => LFail pc (rev path) (R_SUMMARY (sum_diag U st sk)) st :: acc
            end
        | None =>
          match (match dirs_at (un_dirs Un) pc with
                 | [] => DOk st
                 | ds => match apply_dirs U st ds with
                         | DOk S1 => if wf_state S1 then DOk S1 else DFail 9
                         | other => other
                         end
                 end) with
          | DFail w => LFail pc (rev path) (R_CUT pc w) st :: acc
          | DFork c S0 =>
              match forks with
              | O => LFail pc (rev path) R_FORKS (set_depth st steps) :: acc
              | Datatypes.S forks' =>
                  let St := learn_cond S0 c true in
                  let Sf := learn_cond S0 c false in
                  if negb (wf_state St &&& wf_state Sf) then LFail pc (rev path) (R_CUT pc 8) st :: acc else
                  (* [comment removed for export] *)
                  let arm := fun (b : bool) (Sx : astate) (acc0 : list leaf) =>
                     match step U Sx with
                     | SNext S' => explore fuel' forks' S' (Datatypes.S steps) (b :: path) acc0
                     | SFork S1 S2 =>
                         match forks' with
                         | O => LFail pc (rev (b :: path)) R_FORKS (set_depth Sx steps) :: acc0
                         | Datatypes.S forks'' =>
                             let acc2 := explore fuel' forks'' S1 (nsteps S1) (true :: b :: path) acc0 in
                             explore fuel' forks'' S2 (nsteps S2) (false :: b :: path) acc2
                         end
                     | SExit S' => LExit (rev (b :: path)) (exit_ok Un S') S' :: acc0
                     | SFail p r => LFail p (rev (b :: path)) r Sx :: acc0
                     end in
                  arm false Sf (arm true St acc)
              end
          | DOk S1 =>
            match step U S1 with
            | SNext S' => explore fuel' forks S' (Datatypes.S steps) path acc
            | SFork St Sf =>
                match forks with
                | O => LFail pc (rev path) R_FORKS (set_depth S1 steps) :: acc
                | Datatypes.S forks' =>
                    let acc1 := explore fuel' forks' St (nsteps St) (true :: path) acc in
                    explore fuel' forks' Sf (nsteps Sf) (false :: path) acc1
                end
            | SExit S' => LExit (rev path) (exit_ok Un S') (set_depth S' steps) :: acc
            | SFail p r => LFail p (rev path) r (set_depth S1 steps) :: acc
            end
          end
        end
      end
    end.
End Explore.

(* [comment removed for export] *)
Definition norm_st (st : astate) : astate := set_ctx st (ctx_norm (s_ctx st)).
Definition run_cut (Un : unitT) (i : nat) (cp : cutpoint) : list leaf :=
  explore Un i cp (un_fuel Un) (un_forks Un) (norm_st (set_pc (cp_st cp) (cp_pc cp))) 0 [] [].

Fixpoint run_cuts (Un : unitT) (i : nat) (cps : list cutpoint) : list (nat * list leaf) :=
  match cps with [] => [] | cp :: r => (i, run_cut Un i cp) :: run_cuts Un (S i) r end.
Definition run_unit (Un : unitT) : list (nat * list leaf) := run_cuts Un 0 (un_cuts Un).
(* [comment removed for export] *)
Fixpoint run_some_ref (Un : unitT) (i : nat) (cps : list cutpoint) (which : list nat) : list (nat * list leaf) :=
  match cps with [] => [] | cp :: r => (if existsb (Nat.eqb i) which then [(i, run_cut Un i cp)] else []) ++ run_some_ref Un (S i) r which end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icache := PositiveMap.t (instr * Z).
Definition ic_step (U : uenv) (c : icache) (st0 : astate) : sres * icache :=
  let st := gc_facts st0 in
  let pc := s_pc st in
  match pc with
  | Zpos p =>
      match PositiveMap.find p c with
      | Some (i, isz) => (exec_instr U st i isz, c)
      | None =>
          match fetch U pc with
          | None => (SFail pc R_FETCH, c)
          | Some w =>
              if is_ecall w then (SFail pc R_ECALL, c) else
              match decode_any w with
              | Some (i, isz) => (exec_instr U st i isz, PositiveMap.add p (i, isz) c)
              | None => (SFail pc R_DECODE, c)
              end
          end
      end
  | _ => (step U st0, c)
  end.
Definition ic_ok (U : uenv) (c : icache) : Prop :=
  forall p i isz, PositiveMap.find p c = Some (i, isz) ->
    exists w, fetch U (Zpos p) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, isz).
Lemma ic_ok_empty : forall U, ic_ok U (PositiveMap.empty _).
Proof. intros U p i isz H. rewrite PositiveMap.gempty in H. discriminate H. Qed.
Lemma ic_step_ok : forall U c st0, ic_ok U c -> fst (ic_step U c st0) = step U st0 /\ ic_ok U (snd (ic_step U c st0)).
Proof.
  intros U c st0 HC. unfold ic_step, step. cbv zeta.
  destruct (s_pc (gc_facts st0)) as [|p|p] eqn:EP; try (cbn [fst snd]; split; [reflexivity | exact HC]).
  destruct (PositiveMap.find p c) as [[i isz]|] eqn:EF.
  - destruct (HC p i isz EF) as (w & F1 & F2 & F3). rewrite F1, F2, F3. cbn [fst snd]. split; [reflexivity | exact HC].
  - destruct (fetch U (Z.pos p)) as [w|] eqn:F1; [|cbn [fst snd]; split; [reflexivity | exact HC]].
    destruct (is_ecall w) eqn:F2; [cbn [fst snd]; split; [reflexivity | exact HC]|].
    destruct (decode_any w) as [[i isz]|] eqn:F3; [|cbn [fst snd]; split; [reflexivity | exact HC]].
    cbn [fst snd]. split; [reflexivity|].
    intros q i' isz' H. destruct (Pos.eq_dec q p) as [->|N].
    + rewrite PositiveMap.gss in H. injection H as <- <-. exists w. auto.
    + rewrite PositiveMap.gso in H by exact N. exact (HC q i' isz' H).
Qed.
Section ExploreIC.
  Variable Un : unitT.
  Let U := un_env Un.
  Variable start_idx : nat.
  Variable start : cutpoint.
  Fixpoint ic_explore (fuel : nat) (forks : nat) (st : astate) (steps : nat) (path : list bool) (acc : list leaf) (c : icache) : list leaf * icache :=
    match fuel with
    | O => (LFail (s_pc st) (rev path) R_FUEL (set_depth st steps) :: acc, c)
    | Datatypes.S fuel' =>
      if negb (wf_state st) then (LFail (s_pc st) (rev path) R_UNSUPPORTED (set_depth st steps) :: acc, c) else
      if ctx_contra (s_ctx st) None then (LInfeasible (rev path) :: acc, c) else
      let pc := s_pc st in
      let nsteps := fun S' : astate => if Z.eqb (s_pc S') pc then steps else Datatypes.S steps in
      match (match steps with O => None | _ => if existsb (Z.eqb pc) (un_stops Un) then Some (cuts_at (un_cuts Un) pc 0) else None end) with
      | Some cps =>
          match degrade_regs st all_xregs with
          | None => (LFail pc (rev path) R_UNSUPPORTED (set_depth st steps) :: acc, c)
          | Some st' =>
          let mrep := if un_diag Un then match_report else match_report_fast in
          let reps := map (fun icp : nat * cutpoint =>
                             let (i, cp) := icp in
                             (i, mrep (un_total Un) st' cp (cp_mu start) (hint_for (cp_hints cp) start_idx (rev path)))) cps in
          let ok := existsb (fun ir : nat * list mismatch => match snd ir with [] => true | _ => false end) reps in
          let cands := map (fun icp : nat * cutpoint =>
                             let (i, cp) := icp in (i, cand_report st' cp (hint_for (cp_hints cp) start_idx (rev path)))) cps in
          (LArrive pc start_idx (rev path) ok reps cands (set_depth st' steps) :: acc, c)
          end
      | None =>
        match sum_at (un_sums Un) pc with
        | Some SumFail => (LFail pc (rev path) (R_SUMMARY 0) st :: acc, c)
        | Some SumFree5 => (LFail pc (rev path) (R_SUMMARY 3) st :: acc, c)
        | Some sk =>
            match (match sk with SumCBD => apply_cbd U st | SumMalloc k => apply_malloc U st k | SumMemset => apply_memset U st
                   | _ => None end) with
            | Some S' => if wf_state S' then ic_explore fuel' forks S' (Datatypes.S steps) path acc c
                         else (LFail pc (rev path) (R_SUMMARY 2) st :: acc, c)
            | None => (LFail pc (rev path) (R_SUMMARY (sum_diag U st sk)) st :: acc, c)
            end
        | None =>
          match (match dirs_at (un_dirs Un) pc with
                 | [] => DOk st
                 | ds => match apply_dirs U st ds with
                         | DOk S1 => if wf_state S1 then DOk S1 else DFail 9
                         | other => other
                         end
                 end) with
          | DFail w => (LFail pc (rev path) (R_CUT pc w) st :: acc, c)
          | DFork cnd S0 =>
              match forks with
              | O => (LFail pc (rev path) R_FORKS (set_depth st steps) :: acc, c)
              | Datatypes.S forks' =>
                  let St := learn_cond S0 cnd true in
                  let Sf := learn_cond S0 cnd false in
                  if negb (wf_state St &&& wf_state Sf) then (LFail pc (rev path) (R_CUT pc 8) st :: acc, c) else
                  let arm := fun (b : bool) (Sx : astate) (ac : list leaf * icache) =>
                     let (acc0, c0) := ac in
                     match ic_step U c0 Sx with
                     | (SNext S', c1) => ic_explore fuel' forks' S' (Datatypes.S steps) (b :: path) acc0 c1
                     | (SFork S1 S2, c1) =>
                         match forks' with
                         | O => (LFail pc (rev (b :: path)) R_FORKS (set_depth Sx steps) :: acc0, c1)
                         | Datatypes.S forks'' =>
                             let (acc2, c2) := ic_explore fuel' forks'' S1 (nsteps S1) (true :: b :: path) acc0 c1 in
                             ic_explore fuel' forks'' S2 (nsteps S2) (false :: b :: path) acc2 c2
                         end
                     | (SExit S', c1) => (LExit (rev (b :: path)) (exit_ok Un S') S' :: acc0, c1)
                     | (SFail p r, c1) => (LFail p (rev (b :: path)) r Sx :: acc0, c1)
                     end in
                  arm false Sf (arm true St (acc, c))
              end
          | DOk S1 =>
            match ic_step U c S1 with
            | (SNext S', c1) => ic_explore fuel' forks S' (Datatypes.S steps) path acc c1
            | (SFork St Sf, c1) =>
                match forks with
                | O => (LFail pc (rev path) R_FORKS (set_depth S1 steps) :: acc, c1)
                | Datatypes.S forks' =>
                    let (acc1, c2) := ic_explore fuel' forks' St (nsteps St) (true :: path) acc c1 in
                    ic_explore fuel' forks' Sf (nsteps Sf) (false :: path) acc1 c2
                end
            | (SExit S', c1) => (LExit (rev path) (exit_ok Un S') (set_depth S' steps) :: acc, c1)
            | (SFail p r, c1) => (LFail p (rev path) r (set_depth S1 steps) :: acc, c1)
            end
          end
        end
      end
    end.

  Lemma ic_explore_ok : forall fuel forks st steps path acc c, ic_ok U c ->
    fst (ic_explore fuel forks st steps path acc c) = explore Un start_idx start fuel forks st steps path acc
    /\ ic_ok U (snd (ic_explore fuel forks st steps path acc c)).
  Proof.
    induction fuel as [|fuel' IH]; intros forks st steps path acc c HC; [cbn [ic_explore explore fst snd]; split; [reflexivity | exact HC]|].
    cbn [ic_explore explore]. cbv zeta.
    destruct (negb (wf_state st)); [cbn [fst snd]; split; [reflexivity | exact HC]|].
    destruct (ctx_contra (s_ctx st) None); [cbn [fst snd]; split; [reflexivity | exact HC]|].
    (* [comment removed for export] *)
    assert (ARM : forall (gE : astate -> astate) (sF : astate) (fk : nat) (pth : list bool) (Sx : astate) (acc0 : list leaf) (c0 : icache), ic_ok U c0 ->
              fst (match ic_step U c0 Sx with
                   | (SNext S', c1) => ic_explore fuel' fk S' (Datatypes.S steps) pth acc0 c1
                   | (SFork S1 S2, c1) =>
                       match fk with
                       | O => (LFail (s_pc st) (rev pth) R_FORKS (set_depth Sx steps) :: acc0, c1)
                       | Datatypes.S forks'' =>
                           let (acc2, c2) := ic_explore fuel' forks'' S1 (if Z.eqb (s_pc S1) (s_pc st) then steps else Datatypes.S steps) (true :: pth) acc0 c1 in
                           ic_explore fuel' forks'' S2 (if Z.eqb (s_pc S2) (s_pc st) then steps else Datatypes.S steps) (false :: pth) acc2 c2
                       end
                   | (SExit S', c1) => (LExit (rev pth) (exit_ok Un S') (gE S') :: acc0, c1)
                   | (SFail p r, c1) => (LFail p (rev pth) r sF :: acc0, c1)
                   end)
              = match step U Sx with
                | SNext S' => explore Un start_idx start fuel' fk S' (Datatypes.S steps) pth acc0
                | SFork S1 S2 =>
                    match fk with
                    | O => LFail (s_pc st) (rev pth) R_FORKS (set_depth Sx steps) :: acc0
                    | Datatypes.S forks'' =>
                        explore Un start_idx start fuel' forks'' S2 (if Z.eqb (s_pc S2) (s_pc st) then steps else Datatypes.S steps) (false :: pth)
                          (explore Un start_idx start fuel' forks'' S1 (if Z.eqb (s_pc S1) (s_pc st) then steps else Datatypes.S steps) (true :: pth) acc0)
                    end
                | SExit S' => LExit (rev pth) (exit_ok Un S') (gE S') :: acc0
                | SFail p r => LFail p (rev pth) r sF :: acc0
                end
              /\ ic_ok U (snd (match ic_step U c0 Sx with
                   | (SNext S', c1) => ic_explore fuel' fk S' (Datatypes.S steps) pth acc0 c1
                   | (SFork S1 S2, c1) =>
                       match fk with
                       | O => (LFail (s_pc st) (rev pth) R_FORKS (set_depth Sx steps) :: acc0, c1)
                       | Datatypes.S forks'' =>
                           let (acc2, c2) := ic_explore fuel' forks'' S1 (if Z.eqb (s_pc S1) (s_pc st) then steps else Datatypes.S steps) (true :: pth) acc0 c1 in
                           ic_explore fuel' forks'' S2 (if Z.eqb (s_pc S2) (s_pc st) then steps else Datatypes.S steps) (false :: pth) acc2 c2
                       end
                   | (SExit S', c1) => (LExit (rev pth) (exit_ok Un S') (gE S') :: acc0, c1)
                   | (SFail p r, c1) => (LFail p (rev pth) r sF :: acc0, c1)
                   end))).
    { intros gE sF fk pth Sx acc0 c0 H0.
      destruct (ic_step_ok U c0 Sx H0) as [E1 E2]. destruct (ic_step U c0 Sx) as [r c1]. cbn [fst snd] in E1, E2. subst r.
      destruct (step U Sx) as [S'|S1 S2|S'|p r].
      - apply IH. exact E2.
      - destruct fk as [|forks'']; [cbn [fst snd]; split; [reflexivity | exact E2]|].
        destruct (IH forks'' S1 (if Z.eqb (s_pc S1) (s_pc st) then steps else Datatypes.S steps) (true :: pth) acc0 c1 E2) as [I1 I2].
        destruct (ic_explore fuel' forks'' S1 (if Z.eqb (s_pc S1) (s_pc st) then steps else Datatypes.S steps) (true :: pth) acc0 c1) as [acc2 c2].
        cbn [fst snd] in I1, I2. subst acc2. apply IH. exact I2.
      - cbn [fst snd]. split; [reflexivity | exact E2].
      - cbn [fst snd]. split; [reflexivity | exact E2]. }
    unfold U in *.
    destruct (match steps with O => None | _ => if existsb (Z.eqb (s_pc st)) (un_stops Un) then Some (cuts_at (un_cuts Un) (s_pc st) 0) else None end) as [cps|].
    { destruct (degrade_regs st all_xregs); cbn [fst snd]; (split; [reflexivity | exact HC]). }
    destruct (sum_at (un_sums Un) (s_pc st)) as [sk|].
    { destruct sk; try (cbn [fst snd]; split; [reflexivity | exact HC]);
        match goal with |- context [match ?o with Some _ => _ | None => _ end] => destruct o as [S'|] end;
        try (cbn [fst snd]; split; [reflexivity | exact HC]);
        (destruct (wf_state S'); [apply IH; exact HC | cbn [fst snd]; split; [reflexivity | exact HC]]). }
    match goal with |- context [match ?d with DOk _ => _ | DFork _ _ => _ | DFail _ => _ end] => destruct d as [S1|cnd S0|w] end.
    - (* [comment removed for export] *)
      exact (ARM (fun S' => set_depth S' steps) (set_depth S1 steps) forks path S1 acc c HC).
    - (* [comment removed for export] *)
      destruct forks as [|forks']; [cbn [fst snd]; split; [reflexivity | exact HC]|].
      destruct (negb (wf_state (learn_cond S0 cnd true) &&& wf_state (learn_cond S0 cnd false))); [cbn [fst snd]; split; [reflexivity | exact HC]|].
      destruct (ARM (fun S' => S') (learn_cond S0 cnd true) forks' (true :: path) (learn_cond S0 cnd true) acc c HC) as [A1 A2].
      match goal with |- context [let (acc0, c0) := ?X in _] => destruct X as [accA cA] end.
      cbn [fst snd] in A1, A2. rewrite <- A1.
      exact (ARM (fun S' => S') (learn_cond S0 cnd false) forks' (false :: path) (learn_cond S0 cnd false) accA cA A2).
    - cbn [fst snd]. split; [reflexivity | exact HC].
  Qed.
End ExploreIC.
Definition ic_run_cut (Un : unitT) (i : nat) (cp : cutpoint) (c : icache) : list leaf * icache :=
  ic_explore Un i cp (un_fuel Un) (un_forks Un) (norm_st (set_pc (cp_st cp) (cp_pc cp))) 0 [] [] c.
Fixpoint ic_run_some (Un : unitT) (i : nat) (cps : list cutpoint) (which : list nat) (c : icache) : list (nat * list leaf) * icache :=
  match cps with
  | [] => ([], c)
  | cp :: r =>
      if existsb (Nat.eqb i) which then
        let (l, c1) := ic_run_cut Un i cp c in
        let (rest, c2) := ic_run_some Un (S i) r which c1 in ((i, l) :: rest, c2)
      else ic_run_some Un (S i) r which c
  end.

Lemma ic_run_cut_ok : forall Un i cp c, ic_ok (un_env Un) c -> fst (ic_run_cut Un i cp c) = run_cut Un i cp /\ ic_ok (un_env Un) (snd (ic_run_cut Un i cp c)).
Proof. intros. unfold ic_run_cut, run_cut. apply ic_explore_ok. assumption. Qed.
Lemma ic_run_some_ok : forall Un cps i which c, ic_ok (un_env Un) c ->
  fst (ic_run_some Un i cps which c) = run_some_ref Un i cps which /\ ic_ok (un_env Un) (snd (ic_run_some Un i cps which c)).
Proof.
  intros Un cps. induction cps as [|cp r IH]; intros i which c HC; [cbn [ic_run_some run_some_ref fst snd]; split; [reflexivity | exact HC]|].
  cbn [ic_run_some run_some_ref]. destruct (existsb (Nat.eqb i) which).
  - destruct (ic_run_cut_ok Un i cp c HC) as [E1 E2]. destruct (ic_run_cut Un i cp c) as [l c1]. cbn [fst snd] in E1, E2. subst l.
    destruct (IH (S i) which c1 E2) as [I1 I2]. destruct (ic_run_some Un (S i) r which c1) as [rest c2]. cbn [fst snd] in *. subst rest.
    split; [reflexivity | exact I2].
  - cbn [app]. apply IH. exact HC.
Qed.

Definition run_some (Un : unitT) (i : nat) (cps : list cutpoint) (which : list nat) : list (nat * list leaf) :=
  fst (ic_run_some Un i cps which (PositiveMap.empty _)).
Lemma run_some_eq : forall Un i cps which, run_some Un i cps which = run_some_ref Un i cps which.
Proof. intros. unfold run_some. apply ic_run_some_ok. apply ic_ok_empty. Qed.

(* [comment removed for export] *)
Definition template_okb (U : uenv) (cp : cutpoint) : bool :=
  let T := cp_st cp in
  forallb (fun c => in_window U (c_off c) (c_w c)) (s_stk T)
  &&& forallb (fun a => in_window U (ar_lo a) (ar_hi a - ar_lo a) &&& Z.leb (ar_lo a) (ar_hi a)) (s_arrs T)
  &&& forallb (fun f => forallb (fun c => in_win 0 (f_size f) (c_off c) (c_w c)) (f_cells f)
                        &&& forallb (fun a => in_win 0 (f_size f) (ar_lo a) (ar_hi a - ar_lo a) &&& Z.leb (ar_lo a) (ar_hi a)) (f_arrs f)) (s_frames T)
  &&& match s_pcache T with [] => true | _ => false end
  &&& match s_resv T with None => true | _ => false end
  &&& forallb (fun m => lin_below m (s_next T)) (cp_mu cp)
  &&& wf_state (set_pc T (cp_pc cp)).

Definition check_unit (Un : unitT) : bool :=
  tables_validb (un_env Un)
  &&& forallb (template_okb (un_env Un)) (un_cuts Un)
  &&& forallb (fun il : nat * list leaf => forallb leaf_ok (snd il)) (run_unit Un).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition entry_regs (tp : Z) : list aval :=
  [Top; LV (lvar SYM_RA); LV (lvar SYM_SP0); LV (lvar 4); alit tp; Top; Top; Top;
   LV (lvar 6); LV (lvar 7); LV (lvar SYM_DATA); LV (lvar SYM_N); Top; Top; Top; Top;
   Top; Top; LV (lvar 8); LV (lvar 9); LV (lvar 10); LV (lvar 11); LV (lvar 12); LV (lvar 13);
   LV (lvar 14); LV (lvar 15); LV (lvar 16); LV (lvar 17); Top; Top; Top; Top]%nat.

(* [comment removed for export] *)
Definition entry_ctx (nmax sp32 : Z) : ctx :=
  Ctx [laddc (lneg (ladd (lvar SYM_DATA) (lvar SYM_N))) (2 ^ 62 - 4097);         (* [comment removed for export] *)
       laddc (lsub (lvar SYM_SP0) (lscale 32 (lvar SYM_S32))) (- sp32);         (* [comment removed for export] *)
       laddc (lsub (lscale 32 (lvar SYM_S32)) (lvar SYM_SP0)) sp32;             (* [comment removed for export] *)
       lsub (lvar SYM_DATA) (lscale 16 (lvar SYM_D16));                        (* [comment removed for export] *)
       lsub (lscale 16 (lvar SYM_D16)) (lvar SYM_DATA)]                         (* [comment removed for export] *)
      [(SYM_N, Itv (Some 0) (Some (nmax - 1))); (SYM_DATA, Itv (Some 4096) (Some (2 ^ 62 - 4097)));
       (SYM_SP0, Itv (Some 0x10007fff9000) (Some (2 ^ 47))); (SYM_RA, Itv (Some 0) (Some (2 ^ 64 - 1)));
       (SYM_S32, Itv (Some 0x8003fffc80) (Some (2 ^ 42))); (SYM_D16, Itv (Some 256) (Some (2 ^ 58 - 257)));
       (SYM_R32, Itv (Some sp32) (Some sp32))].

Definition entry_state (pc : Z) (nmax sp32 tp : Z) (abs0 : list (Z * Z)) : astate :=
  AS pc (entry_regs tp) (entry_ctx nmax sp32) NGLOB [] [] abs0 [] None 0 [] [].

Definition entry_cut (pc nmax sp32 tp : Z) (abs0 : list (Z * Z)) : cutpoint :=
  CP pc (entry_state pc nmax sp32 tp abs0) [] [] [].

End LAC.
