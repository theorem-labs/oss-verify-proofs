(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SLin.

Definition zlin : Type := (Z * list (Z * expr))%type.

(* [comment removed for export] *)
Fixpoint zins (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb k 0 then [] else [(k, a)]
  | (k', a') :: r => if expr_eqb a a' then (if Z.eqb (k + k') 0 then r else (k + k', a') :: r) else (k', a') :: zins k a r
  end.

Definition zadd_ts (ts us : list (Z * expr)) : list (Z * expr) := fold_right (fun t acc => zins (fst t) (snd t) acc) us ts.
Definition zscale_ts (m : Z) (ts : list (Z * expr)) : list (Z * expr) := map (fun t => (m * fst t, snd t)) ts.

(* [comment removed for export] *)
Definition zsub_lower (R : zlin) (m : Z) (F : lin) (l : Z) : zlin :=
  (fst R - m * fst F + m * l, zadd_ts (zscale_ts (- m) (snd F)) (snd R)).
Definition zsub_upper (R : zlin) (m : Z) (F : lin) (h : Z) : zlin :=
  (fst R + m * fst F - m * h, zadd_ts (zscale_ts m (snd F)) (snd R)).

Record fterm : Type := FT { ft_e : expr; ft_lo : Z; ft_hi : Z; ft_lower : bool; ft_mul : Z }.

(* [comment removed for export] *)
Fixpoint lex {A : Type} (f : A -> bool) (l : list A) : bool := match l with [] => false | x :: r => if f x then true else lex f r end.
Fixpoint lall {A : Type} (f : A -> bool) (l : list A) : bool := match l with [] => true | x :: r => if f x then lall f r else false end.
Lemma lex_eq : forall A (f : A -> bool) l, lex f l = existsb f l.
Proof. intros A f l. induction l as [|x r IH]; [reflexivity|]. cbn [lex existsb]. rewrite IH. destruct (f x); reflexivity. Qed.
Lemma lall_eq : forall A (f : A -> bool) l, lall f l = forallb f l.
Proof. intros A f l. induction l as [|x r IH]; [reflexivity|]. cbn [lall forallb]. rewrite IH. destruct (f x); reflexivity. Qed.
Lemma lex_exists : forall A (f : A -> bool) l, lex f l = true -> exists x, In x l /\ f x = true.
Proof. intros A f l H. rewrite lex_eq in H. apply existsb_exists in H. exact H. Qed.
Lemma lall_forall : forall A (f : A -> bool) l, lall f l = true -> forall x, In x l -> f x = true.
Proof. intros A f l H. rewrite lall_eq in H. apply forallb_forall. exact H. Qed.

Definition kin (K : kentry) (kn : list kentry) : bool := lex (APC.kentry_eqb K) kn.

Lemma kentry_eqb_eq : forall x y, APC.kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [APC.kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.

(* [comment removed for export] *)
Definition srl_fact_ok (e : expr) (lo hi : Z) : bool :=
  match e with
  | EAlu ALU_SUB r (EMd M_MUL (ELit m) (EAlu ALU_SRL r' (ELit s))) =>
      if expr_eqb r r' then if Z.leb 1 s then if Z.leb s 63 then if Z.eqb m (2 ^ s) then
        if Z.eqb lo 0 then Z.eqb hi (2 ^ s - 1) else false else false else false else false else false
  | _ => false
  end.

Definition fstep (kn : list kentry) (R : zlin) (t : fterm) : option zlin :=
  if ((if kin (KRange (ft_e t) (ft_lo t) (ft_hi t)) kn then true else srl_fact_ok (ft_e t) (ft_lo t) (ft_hi t))
      && fact_nowrap kn (ft_e t) (ft_hi t) && Z.ltb 0 (ft_mul t))%bool then
    Some (if ft_lower t then zsub_lower R (ft_mul t) (lin_of (ft_e t)) (ft_lo t)
          else zsub_upper R (ft_mul t) (lin_of (ft_e t)) (ft_hi t))
  else None.

Fixpoint fapply (kn : list kentry) (R : zlin) (hs : list fterm) : option zlin :=
  match hs with
  | [] => Some R
  | t :: r => match fstep kn R t with Some R' => fapply kn R' r | None => None end
  end.

(* [comment removed for export] *)
Definition arng (kn : list kentry) (a : expr) : option (Z * Z) :=
  match erange kn a with
  | Some (lo, hi) => Some (Z.max 0 lo, Z.min (2^64 - 1) hi)
  | None => Some (0, 2^64 - 1)
  end.

Definition zlow (kn : list kentry) (R : zlin) : option Z :=
  match lin_range (arng kn) (fst R) (snd R) with Some (lo, _) => Some lo | None => None end.

(* [comment removed for export] *)
Definition gcd_ts (ts : list (Z * expr)) : Z := fold_right (fun t acc => Z.gcd (fst t) acc) 0 ts.
Definition rnd_ok (R : zlin) (lo : Z) : bool :=
  let g := gcd_ts (snd R) in
  if Z.leb g 1 then Z.leb 0 lo else Z.leb 0 (fst R + g * (- ((fst R - lo) / g))).

Definition fcheck (kn : list kentry) (R : zlin) (hs : list fterm) : bool :=
  match fapply kn R hs with
  | Some R' => match zlow kn R' with Some lo => rnd_ok R lo | None => false end
  | None => false
  end.

(* [comment removed for export] *)
Definition krange_farkas (kn : list kentry) (e : expr) (lo hi : Z) (hl hu : list fterm) : bool :=
  let L := lin_of e in
  (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2^64)
   && fcheck kn (fst L - lo, snd L) hl
   && fcheck kn (hi - fst L, zscale_ts (-1) (snd L)) hu)%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint esz_ok (b : nat) (e : expr) : option nat :=
  match b with
  | O => None
  | S b' => match e with
            | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => match esz_ok b' x with Some r => esz_ok r y | None => None end
            | EExt _ _ _ x => esz_ok b' x
            | _ => Some b'
            end
  end.
Definition small_e (e : expr) : bool := match esz_ok 64 e with Some _ => true | None => false end.
Definition cands (kn : list kentry) : list (zlin * fterm) :=
  flat_map (fun K => match K with
    | KRange e l h =>
        if (if small_e e then fact_nowrap kn e h else false) then
          let L := lin_of e in
          [((fst L - l, snd L), FT e l h true 1); ((h - fst L, zscale_ts (-1) (snd L)), FT e l h false 1)]
        else []
    | _ => []
    end) kn.

Fixpoint zcoef (a : expr) (ts : list (Z * expr)) : Z :=
  match ts with [] => 0 | (k, a') :: r => if expr_eqb a a' then k else zcoef a r end.

Definition contrib (kn : list kentry) (t : Z * expr) : Z :=
  match arng kn (snd t) with Some (lo, hi) => if Z.leb 0 (fst t) then fst t * lo else fst t * hi | None => 0 end.

(* [comment removed for export] *)
Fixpoint ins_by (kn : list kentry) (t : Z * expr) (l : list (Z * expr)) : list (Z * expr) :=
  match l with [] => [t] | u :: r => if Z.leb (contrib kn t) (contrib kn u) then t :: l else u :: ins_by kn t r end.
Definition bad_atoms (kn : list kentry) (ts : list (Z * expr)) : list (Z * expr) :=
  fold_right (fun t acc => if Z.ltb (contrib kn t) 0 then ins_by kn t acc else acc) [] ts.

(* [comment removed for export] *)
Definition elim (R G : zlin) (k g : Z) : option (Z * zlin) :=
  if Z.eqb g 0 then None else
  let m := k / g in
  if (Z.ltb 0 m && Z.eqb (k mod g) 0)%bool then Some (m, (fst R - m * fst G, zadd_ts (zscale_ts (- m) (snd G)) (snd R))) else None.

(* [comment removed for export] *)
Fixpoint fsearchR (R0 : zlin) (depth : nat) (budget : nat) (kn : list kentry) (cs : list (zlin * fterm)) (R : zlin) : option (list fterm) * nat :=
  match budget with
  | O => (None, O)
  | S b =>
    if (match zlow kn R with Some lo => rnd_ok R0 lo | None => false end) then (Some [], b) else
    match depth with
    | O => (None, b)
    | S d =>
      let fix try_atoms (ats : list (Z * expr)) (b : nat) : option (list fterm) * nat :=
        match ats with
        | [] => (None, b)
        | (k, a) :: ats' =>
          let fix try_cands (l : list (zlin * fterm)) (b : nat) : option (list fterm) * nat :=
            match l with
            | [] => (None, b)
            | (G, t) :: l' =>
              match elim R G k (zcoef a (snd G)) with
              | Some (m, R') =>
                  match fsearchR R0 d b kn cs R' with
                  | (Some hs, b') => (Some (FT (ft_e t) (ft_lo t) (ft_hi t) (ft_lower t) m :: hs), b')
                  | (None, b') => try_cands l' b'
                  end
              | None => try_cands l' b
              end
            end in
          match try_cands cs b with
          | (Some hs, b') => (Some hs, b')
          | (None, b') => try_atoms ats' b'
          end
        end in
      try_atoms (bad_atoms kn (snd R)) b
    end
  end.
Definition fsearch (depth budget : nat) (kn : list kentry) (cs : list (zlin * fterm)) (R : zlin) : option (list fterm) * nat :=
  fsearchR R depth budget kn cs R.


(* [comment removed for export] *)
Fixpoint root_try (kn : list kentry) (cs all : list (zlin * fterm)) (R : zlin) : option (list fterm) :=
  match cs with
  | [] => None
  | (G, t) :: cs' =>
      let fix atoms (l : list (Z * expr)) : option (list fterm) :=
        match l with
        | [] => None
        | (k, a) :: l' =>
            match elim R G k (zcoef a (snd G)) with
            | Some (m, R') => match fst (fsearchR R 1 40 kn all R') with
                              | Some hs => Some (FT (ft_e t) (ft_lo t) (ft_hi t) (ft_lower t) m :: hs)
                              | None => atoms l'
                              end
            | None => atoms l'
            end
        end in
      match atoms (snd R) with Some hs => Some hs | None => root_try kn cs' all R end
  end.

Definition fauto0D (d : nat) (bud : nat) (kn : list kentry) (cs : list (zlin * fterm)) (R : zlin) : bool :=
  match fst (fsearch d bud kn cs R) with
  | Some hs => fcheck kn R hs
  | None => match root_try kn cs cs R with Some hs => fcheck kn R hs | None => false end
  end.
Definition fauto0 (kn : list kentry) (cs : list (zlin * fterm)) (R : zlin) : bool := fauto0D 3 400 kn cs R.

(* [comment removed for export] *)
Definition srl_e (a : expr) : option (expr * Z) :=
  match a with
  | EAlu ALU_SRL r (ELit s) =>
      if Z.leb 1 s then if Z.leb s 63 then Some (EAlu ALU_SUB r (EMd M_MUL (ELit (2 ^ s)) a), s) else None else None
  | _ => None
  end.
Definition srl_cands (kn : list kentry) (ts : list (Z * expr)) : list (zlin * fterm) :=
  flat_map (fun t => match srl_e (snd t) with
    | Some (e, s) =>
        if fact_nowrap kn e (2 ^ s - 1) then
          let L := lin_of e in
          [((fst L - 0, snd L), FT e 0 (2 ^ s - 1) true 1); ((2 ^ s - 1 - fst L, zscale_ts (-1) (snd L)), FT e 0 (2 ^ s - 1) false 1)]
        else []
    | None => []
    end) ts.
Fixpoint srl_shift (ts : list (Z * expr)) : option Z :=
  match ts with [] => None | (_, a) :: r => match srl_e a with Some (_, s) => Some s | None => srl_shift r end end.

(* [comment removed for export] *)
Definition sc_of (ts : list (Z * expr)) (G : zlin) : list Z :=
  flat_map (fun t => let k := zcoef (snd t) ts in
                     if Z.eqb k 0 then [] else if Z.eqb (fst t) 0 then [] else
                     if Z.eqb (k mod fst t) 0 then [] else [Z.abs (fst t) / Z.gcd (fst t) k]) (snd G).
Fixpoint uniq2 (acc : list Z) (l : list Z) : list Z :=
  match l with
  | [] => acc
  | c :: r => if Nat.leb 2 (length acc) then acc
              else if Z.leb c 1 then uniq2 acc r
              else if lex (Z.eqb c) acc then uniq2 acc r else uniq2 (acc ++ [c]) r
  end.
Definition scales (cs : list (zlin * fterm)) (ts : list (Z * expr)) : list Z := uniq2 [] (flat_map (fun p => sc_of ts (fst p)) cs).
(* [comment removed for export] *)
Definition fauto0S (kn : list kentry) (cs : list (zlin * fterm)) (R : zlin) : bool :=
  if fauto0D 4 800 kn cs R then true else fauto0D 3 1500 kn cs R.
Fixpoint try_scales (kn : list kentry) (cs : list (zlin * fterm)) (R : zlin) (l : list Z) : bool :=
  match l with
  | [] => false
  | c :: r => if Z.ltb 0 c then (if fauto0S kn cs (c * fst R, zscale_ts c (snd R)) then true else try_scales kn cs R r)
              else try_scales kn cs R r
  end.

Definition fauto (kn : list kentry) (R : zlin) : bool :=
  if fauto0 kn (cands kn) R then true else
  let cs := srl_cands kn (snd R) ++ cands kn in
  if (match srl_shift (snd R) with Some _ => fauto0 kn cs R | None => false end) then true
  else try_scales kn cs R (scales cs (snd R)).

(* [comment removed for export] *)
Definition zval_a (kn : list kentry) (e : expr) : bool :=
  let L := lin_of e in if fauto kn L then fauto kn ((2^64 - 1 - fst L)%Z, zscale_ts (-1) (snd L)) else false.

Definition zsub (A B : zlin) : zlin := (fst A - fst B, zadd_ts (snd A) (zscale_ts (-1) (snd B))).
Definition zplus (A B : zlin) : zlin := (fst A + fst B, zadd_ts (snd A) (snd B)).
Definition zk (k : Z) : zlin := (k, []).

Definition xinside_f (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if zval_a kn b1 then if zval_a kn b2 then if zval_a kn n1 then if zval_a kn n2 then
    let L1 := lin_of b1 in let L2 := lin_of b2 in let N1 := lin_of n1 in let N2 := lin_of n2 in
    if fauto kn (zsub (zplus L1 (zk k1)) (zplus L2 (zk k2))) then
      fauto kn (zsub (zplus (zplus L2 (zk k2)) N2) (zplus (zplus L1 (zk k1)) N1))
    else false
  else false else false else false else false.

Definition xinside2 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if xinside kn b1 k1 n1 b2 k2 n2 then true
  else if shares_var b1 b2 then xinside_f kn b1 k1 n1 b2 k2 n2 else false.

Definition apart_f (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if zval_a kn b1 then if zval_a kn b2 then if zval_a kn n1 then if zval_a kn n2 then
    let L1 := lin_of b1 in let L2 := lin_of b2 in let N1 := lin_of n1 in let N2 := lin_of n2 in
    if fauto kn (zsub (zplus L2 (zk k2)) (zplus (zplus L1 (zk k1)) N1)) then true
    else fauto kn (zsub (zplus L1 (zk k1)) (zplus (zplus L2 (zk k2)) N2))
  else false else false else false else false.

Definition apart2 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if ranges_apart_x kn b1 k1 n1 b2 k2 n2 then true
  else if shares_var b1 b2 then apart_f kn b1 k1 n1 b2 k2 n2 else false.

(* [comment removed for export] *)
Definition ex2 {A : Type} (f g : A -> bool) (l : list A) : bool := if lex f l then true else lex g l.

Lemma ex2_eq : forall (A : Type) (f g : A -> bool) l, (forall x, f x = true -> g x = true) -> ex2 f g l = existsb g l.
Proof.
  intros A f g l H. unfold ex2. rewrite !lex_eq. destruct (existsb f l) eqn:E; [|reflexivity].
  apply existsb_exists in E as (x & Hx & Hf). symmetry. apply existsb_exists. exists x. split; [exact Hx | exact (H x Hf)].
Qed.

Definition krange_auto (kn : list kentry) (e : expr) (lo hi : Z) : bool :=
  let L := lin_of e in
  (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2^64)
   && fauto kn (fst L - lo, snd L)
   && fauto kn (hi - fst L, zscale_ts (-1) (snd L)))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable segs : list Segment.
Variable E : env.
Variable M : word -> option byte.

Definition zden (R : zlin) : Z := fst R + tden E (snd R).

Lemma zins_den : forall k a ts, tden E (zins k a ts) = k * uE E a + tden E ts.
Proof.
  intros k a ts. induction ts as [|[k' a'] r IH]; cbn [zins tden].
  - destruct (Z.eqb k 0) eqn:Hk; cbn [tden]; [apply Z.eqb_eq in Hk; subst; lia | lia].
  - destruct (expr_eqb a a') eqn:He.
    + apply expr_eqb_eq in He. subst a'. destruct (Z.eqb (k + k') 0) eqn:Hz; cbn [tden]; [apply Z.eqb_eq in Hz; nia | lia].
    + cbn [tden]. rewrite IH. lia.
Qed.

Lemma zadd_den : forall ts us, tden E (zadd_ts ts us) = tden E ts + tden E us.
Proof.
  intros ts us. induction ts as [|[k a] r IH]; cbn [zadd_ts fold_right tden]; [lia|].
  fold (zadd_ts r us). rewrite zins_den, IH. cbn [fst snd]. lia.
Qed.

Lemma zscale_den : forall m ts, tden E (zscale_ts m ts) = m * tden E ts.
Proof. intros m ts. induction ts as [|[k a] r IH]; cbn [zscale_ts map tden]; [lia|]. fold (zscale_ts m r). rewrite IH. cbn [fst snd]. lia. Qed.

Lemma kin_ok : forall kn K, know_ok segs E M kn -> kin K kn = true -> kentry_ok segs E M K.
Proof.
  intros kn K HK H. apply lex_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
  exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

Lemma srl_fact_ok_sound : forall e lo hi, srl_fact_ok e lo hi = true -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros e lo hi H. unfold srl_fact_ok in H.
  destruct e as [| |op r b| | | | |]; try discriminate. destruct op; try discriminate.
  destruct b as [| | | |mo x y| | |]; try discriminate. destruct mo; try discriminate.
  destruct x as [m| | | | | | |]; try discriminate. destruct y as [| |op2 r' z| | | | |]; try discriminate.
  destruct op2; try discriminate. destruct z as [sh| | | | | | |]; try discriminate.
  destruct (expr_eqb r r') eqn:Hr; [|discriminate]. apply expr_eqb_eq in Hr. subst r'.
  destruct (Z.leb 1 sh) eqn:H1; [|discriminate]. destruct (Z.leb sh 63) eqn:H2; [|discriminate].
  destruct (Z.eqb m (2 ^ sh)) eqn:H3; [|discriminate]. destruct (Z.eqb lo 0) eqn:H4; [|discriminate].
  apply Z.leb_le in H1, H2. apply Z.eqb_eq in H3, H4, H. subst m lo hi.
  cbn [edenot]. rewrite u_sub64, u_mul64, u_srl64, !u_lit64a.
  rewrite (Z.mod_small sh (2 ^ 64)) by lia. rewrite (Z.mod_small sh 64) by lia.
  assert (Hp : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp64 : 2 ^ sh <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small (2 ^ sh) (2 ^ 64)) by lia.
  set (u := bv_unsigned (edenot E r)). pose proof (u64_range (edenot E r)) as Ru. fold u in Ru.
  pose proof (Z.div_mod u (2 ^ sh) ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound u (2 ^ sh) Hp) as Mb.
  assert (Hq : 0 <= 2 ^ sh * (u / 2 ^ sh) <= u) by (split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]).
  rewrite (Z.mod_small (2 ^ sh * (u / 2 ^ sh)) (2 ^ 64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma fstep_sound : forall kn R t R', know_ok segs E M kn -> fstep kn R t = Some R' -> zden R' <= zden R.
Proof.
  intros kn R [e l h lw m] R' HK H. unfold fstep in H. cbn [ft_e ft_lo ft_hi ft_lower ft_mul] in H.
  destruct ((if kin (KRange e l h) kn then true else srl_fact_ok e l h) && fact_nowrap kn e h && Z.ltb 0 m)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hm]. apply andb_prop in Hc as [Hk Hnw]. apply Z.ltb_lt in Hm.
  assert (HKr : l <= bv_unsigned (edenot E e) <= h).
  { destruct (kin (KRange e l h) kn) eqn:Hk1.
    - pose proof (kin_ok kn _ HK Hk1) as HK2. cbn [kentry_ok] in HK2. exact HK2.
    - exact (srl_fact_ok_sound e l h Hk). }
  pose proof (fact_nowrap_sound segs E M kn e l h HK Hnw HKr) as Hv.
  injection H as <-. unfold zden.
  destruct lw; unfold zsub_lower, zsub_upper; cbn [fst snd]; rewrite zadd_den, zscale_den; nia.
Qed.

Lemma fapply_sound : forall kn hs R R', know_ok segs E M kn -> fapply kn R hs = Some R' -> zden R' <= zden R.
Proof.
  intros kn hs. induction hs as [|t r IH]; intros R R' HK H; cbn [fapply] in H; [injection H as <-; lia|].
  destruct (fstep kn R t) as [R1|] eqn:Hs; [|discriminate].
  pose proof (fstep_sound kn R t R1 HK Hs). pose proof (IH R1 R' HK H). lia.
Qed.

Lemma arng_sound : forall kn a lo hi, know_ok segs E M kn -> arng kn a = Some (lo, hi) -> lo <= bv_unsigned (edenot E a) <= hi.
Proof.
  intros kn a lo hi HK H. pose proof (bv_unsigned_in_range 64 (edenot E a)) as R. unfold bv_modulus in R. cbn in R.
  unfold arng in H. destruct (erange kn a) as [[l h]|] eqn:Er.
  - injection H as <- <-. pose proof (erange_sound segs E M kn a l h HK Er). lia.
  - injection H as <- <-. lia.
Qed.

Lemma gcd_ts_div : forall ts, (gcd_ts ts | tden E ts).
Proof.
  induction ts as [|[k a] r IH]; cbn [gcd_ts fold_right tden fst]; [apply Z.divide_0_r|].
  fold (gcd_ts r). apply Z.divide_add_r.
  - apply Z.divide_mul_l. apply Z.gcd_divide_l.
  - eapply Z.divide_trans; [apply Z.gcd_divide_r | exact IH].
Qed.

Lemma rnd_ok_sound : forall R lo, rnd_ok R lo = true -> lo <= zden R -> 0 <= zden R.
Proof.
  intros [c ts] lo H Hlo. unfold rnd_ok in H. cbn [fst snd] in *. unfold zden in *. cbn [fst snd] in *.
  destruct (Z.leb (gcd_ts ts) 1) eqn:Hg; [apply Z.leb_le in H; lia|]. apply Z.leb_gt in Hg. apply Z.leb_le in H.
  destruct (gcd_ts_div ts) as [y Hy]. set (g := gcd_ts ts) in *.
  (* [comment removed for export] *)
  assert (Hy2 : - ((c - lo) / g) <= y).
  { assert (g * y >= lo - c) by nia.
    assert ((c - lo) / g >= - y); [|lia]. apply Z.le_ge. apply Z.div_le_lower_bound; lia. }
  nia.
Qed.

Theorem fcheck_sound : forall kn R hs, know_ok segs E M kn -> fcheck kn R hs = true -> 0 <= zden R.
Proof.
  intros kn R hs HK H. unfold fcheck in H.
  destruct (fapply kn R hs) as [R'|] eqn:Ha; [|discriminate].
  destruct (zlow kn R') as [lo|] eqn:Hl; [|discriminate].
  unfold zlow in Hl. destruct (lin_range (arng kn) (fst R') (snd R')) as [[lo' hi']|] eqn:Hr; [|discriminate].
  injection Hl as ->.
  pose proof (lin_range_sound E (arng kn) (fun a lo hi Ha => arng_sound kn a lo hi HK Ha) _ _ _ _ Hr) as B.
  pose proof (fapply_sound kn hs R R' HK Ha) as D.
  apply (rnd_ok_sound R lo H). unfold zden in *. lia.
Qed.

Theorem krange_farkas_sound : forall kn e lo hi hl hu, know_ok segs E M kn ->
  krange_farkas kn e lo hi hl hu = true -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros kn e lo hi hl hu HK H. unfold krange_farkas in H.
  apply andb_prop in H as [H Hu]. apply andb_prop in H as [H Hl]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
  pose proof (fcheck_sound kn _ hl HK Hl) as A. pose proof (fcheck_sound kn _ hu HK Hu) as B.
  unfold zden in A, B. cbn [fst snd] in A, B. rewrite zscale_den in B.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as R. unfold bv_modulus in R. cbn in R.
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma fauto0D_sound : forall d bud kn cs R, know_ok segs E M kn -> fauto0D d bud kn cs R = true -> 0 <= zden R.
Proof.
  intros d bud kn cs R HK H. unfold fauto0D in H. destruct (fst (fsearch d bud kn cs R)) as [hs|].
  - exact (fcheck_sound kn R hs HK H).
  - destruct (root_try kn cs cs R) as [hs|]; [|discriminate]. exact (fcheck_sound kn R hs HK H).
Qed.
Lemma fauto0_sound : forall kn cs R, know_ok segs E M kn -> fauto0 kn cs R = true -> 0 <= zden R.
Proof. intros kn cs R HK H. exact (fauto0D_sound 3 400 kn cs R HK H). Qed.

Lemma try_scales_sound : forall kn cs R l, know_ok segs E M kn -> try_scales kn cs R l = true -> 0 <= zden R.
Proof.
  intros kn cs R l HK. induction l as [|c r IH]; intros H; cbn [try_scales] in H; [discriminate|].
  destruct (Z.ltb 0 c) eqn:Hc; [|exact (IH H)]. apply Z.ltb_lt in Hc.
  destruct (fauto0S kn cs (c * fst R, zscale_ts c (snd R))) eqn:H1; [|exact (IH H)].
  assert (B : 0 <= zden (c * fst R, zscale_ts c (snd R))).
  { unfold fauto0S in H1. destruct (fauto0D 4 800 kn cs _) eqn:H2; [exact (fauto0D_sound 4 800 kn _ _ HK H2)|].
    exact (fauto0D_sound 3 1500 kn _ _ HK H1). }
  unfold zden in B |- *. cbn [fst snd] in B. rewrite zscale_den in B. nia.
Qed.

Theorem fauto_sound : forall kn R, know_ok segs E M kn -> fauto kn R = true -> 0 <= zden R.
Proof.
  intros kn R HK H. unfold fauto in H.
  destruct (fauto0 kn (cands kn) R) eqn:H0; [exact (fauto0_sound kn _ R HK H0)|]. cbv zeta in H.
  destruct (match srl_shift (snd R) with Some _ => fauto0 kn (srl_cands kn (snd R) ++ cands kn) R | None => false end) eqn:H1.
  - destruct (srl_shift (snd R)); [exact (fauto0_sound kn _ R HK H1) | discriminate].
  - exact (try_scales_sound kn _ R _ HK H).
Qed.

Theorem krange_auto_sound : forall kn e lo hi, know_ok segs E M kn ->
  krange_auto kn e lo hi = true -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros kn e lo hi HK H. unfold krange_auto in H.
  apply andb_prop in H as [H Hu]. apply andb_prop in H as [H Hl]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
  pose proof (fauto_sound kn _ HK Hl) as A. pose proof (fauto_sound kn _ HK Hu) as B.
  unfold zden in A, B. cbn [fst snd] in A, B. rewrite zscale_den in B.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as R. unfold bv_modulus in R. cbn in R.
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma zval_a_ok : forall kn e, know_ok segs E M kn -> zval_a kn e = true ->
  bv_unsigned (edenot E e) = fst (lin_of e) + tden E (snd (lin_of e)).
Proof.
  intros kn e HK H. unfold zval_a in H. destruct (fauto kn (lin_of e)) eqn:H1; [|discriminate].
  pose proof (fauto_sound kn _ HK H1) as A. pose proof (fauto_sound kn _ HK H) as B.
  unfold zden in A, B. cbn [fst snd] in A, B. rewrite zscale_den in B.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as R. unfold bv_modulus in R. cbn in R.
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma zsub_den : forall A B, zden (zsub A B) = zden A - zden B.
Proof. intros [a ts] [b us]. unfold zden, zsub. cbn [fst snd]. rewrite zadd_den, zscale_den. lia. Qed.
Lemma zplus_den : forall A B, zden (zplus A B) = zden A + zden B.
Proof. intros [a ts] [b us]. unfold zden, zplus. cbn [fst snd]. rewrite zadd_den. lia. Qed.
Lemma zk_den : forall k, zden (zk k) = k.
Proof. intros k. unfold zden, zk. cbn [fst snd tden]. lia. Qed.

Lemma xinside_f_sound : forall kn b1 k1 n1 b2 k2 n2, know_ok segs E M kn -> xinside_f kn b1 k1 n1 b2 k2 n2 = true ->
  estart E (SA b2 k2) <= estart E (SA b1 k1) /\ estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2.
Proof.
  intros kn b1 k1 n1 b2 k2 n2 HK H. unfold xinside_f in H. cbv zeta in H.
  destruct (zval_a kn b1) eqn:V1; [|discriminate]. destruct (zval_a kn b2) eqn:V2; [|discriminate].
  destruct (zval_a kn n1) eqn:V3; [|discriminate]. destruct (zval_a kn n2) eqn:V4; [|discriminate].
  destruct (fauto kn (zsub (zplus (lin_of b1) (zk k1)) (zplus (lin_of b2) (zk k2)))) eqn:F1; [|discriminate].
  pose proof (fauto_sound kn _ HK F1) as A. pose proof (fauto_sound kn _ HK H) as B.
  repeat rewrite ?zsub_den, ?zplus_den, ?zk_den in A. repeat rewrite ?zsub_den, ?zplus_den, ?zk_den in B. unfold zden in A, B.
  pose proof (zval_a_ok kn b1 HK V1). pose proof (zval_a_ok kn b2 HK V2). pose proof (zval_a_ok kn n1 HK V3). pose proof (zval_a_ok kn n2 HK V4).
  cbn [zk fst snd tden] in A, B. unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma xinside_2 : forall kn b1 k1 n1 b2 k2 n2, xinside kn b1 k1 n1 b2 k2 n2 = true -> xinside2 kn b1 k1 n1 b2 k2 n2 = true.
Proof. intros kn b1 k1 n1 b2 k2 n2 H. unfold xinside2. rewrite H. reflexivity. Qed.

Lemma xinside2_sound : forall kn b1 k1 n1 b2 k2 n2, know_ok segs E M kn -> xinside2 kn b1 k1 n1 b2 k2 n2 = true ->
  estart E (SA b2 k2) <= estart E (SA b1 k1) /\ estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2.
Proof.
  intros kn b1 k1 n1 b2 k2 n2 HK H. unfold xinside2 in H.
  destruct (xinside kn b1 k1 n1 b2 k2 n2) eqn:X; [exact (xinside_sound segs E M kn _ _ _ _ _ _ HK X)|].
  destruct (shares_var b1 b2); [exact (xinside_f_sound kn _ _ _ _ _ _ HK H) | discriminate].
Qed.

Lemma apart_f_sound : forall kn b1 k1 n1 b2 k2 n2, know_ok segs E M kn -> apart_f kn b1 k1 n1 b2 k2 n2 = true ->
  estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) \/ estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1).
Proof.
  intros kn b1 k1 n1 b2 k2 n2 HK H. unfold apart_f in H. cbv zeta in H.
  destruct (zval_a kn b1) eqn:V1; [|discriminate]. destruct (zval_a kn b2) eqn:V2; [|discriminate].
  destruct (zval_a kn n1) eqn:V3; [|discriminate]. destruct (zval_a kn n2) eqn:V4; [|discriminate].
  pose proof (zval_a_ok kn b1 HK V1). pose proof (zval_a_ok kn b2 HK V2). pose proof (zval_a_ok kn n1 HK V3). pose proof (zval_a_ok kn n2 HK V4).
  unfold estart, elenZ. cbn [a_base a_off].
  destruct (fauto kn (zsub (zplus (lin_of b2) (zk k2)) (zplus (zplus (lin_of b1) (zk k1)) (lin_of n1)))) eqn:F1.
  - pose proof (fauto_sound kn _ HK F1) as A. repeat rewrite ?zsub_den, ?zplus_den, ?zk_den in A. unfold zden in A. cbn [zk fst snd tden] in A. left. lia.
  - pose proof (fauto_sound kn _ HK H) as B. repeat rewrite ?zsub_den, ?zplus_den, ?zk_den in B. unfold zden in B. cbn [zk fst snd tden] in B. right. lia.
Qed.

Lemma apart2_sound : forall kn b1 k1 n1 b2 k2 n2, know_ok segs E M kn -> apart2 kn b1 k1 n1 b2 k2 n2 = true ->
  estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) \/ estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1).
Proof.
  intros kn b1 k1 n1 b2 k2 n2 HK H. unfold apart2 in H.
  destruct (ranges_apart_x kn b1 k1 n1 b2 k2 n2) eqn:X; [exact (ranges_apart_x_sound segs E M kn _ _ _ _ _ _ HK X)|].
  destruct (shares_var b1 b2); [exact (apart_f_sound kn _ _ _ _ _ _ HK H) | discriminate].
Qed.

End Sound.
End SLin.
