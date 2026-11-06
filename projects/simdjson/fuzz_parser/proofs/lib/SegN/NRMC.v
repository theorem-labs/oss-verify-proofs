(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec SeqExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG NRMG SLOWV NRMV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Module NRC.
Local Notation u := bv_unsigned.

Section C.
Variable segs : list Segment.

Definition kimp (kn : list kentry) (K : kentry) : bool := ST.kimplied segs kn K.
Definition MX : Z := 18446744073709551615.

(* [comment removed for export] *)
Fixpoint pkn (kn : list kentry) (p : list sidecond) : list kentry :=
  match p with
  | [] => kn
  | SCBr t c a b :: r => match SL.learn kn c t a b with Some l => pkn (l ++ kn) r | None => pkn kn r end
  | _ :: r => pkn kn r
  end.

(* [comment removed for export] *)
Definition same_loc (b1 : expr) (k1 : Z) (b2 : expr) (k2 : Z) : bool :=
  match lin_of (EAlu ALU_SUB b1 b2) with
  | (c, []) => Z.eqb (c mod 2 ^ 64) ((k2 - k1) mod 2 ^ 64)
  | _ => false
  end.

(* [comment removed for export] *)
Definition tb (x n : expr) : expr := EAlu ALU_ADD x (EMd M_MUL (ELit 8) n).

(* [comment removed for export] *)
Definition ldiff (b1 : expr) (k1 : Z) (b2 : expr) (k2 : Z) : expr := EAlu ALU_SUB (EAlu ALU_ADD b1 (ELit k1)) (EAlu ALU_ADD b2 (ELit k2)).
Definition loc_eq (kn : list kentry) (b1 : expr) (k1 : Z) (b2 : expr) (k2 : Z) : bool :=
  (same_loc b1 k1 b2 k2 || kimp kn (KRange (ldiff b1 k1 b2 k2) 0 0))%bool.

(* [comment removed for export] *)
Inductive wsrc : Type :=
| WSt (v : expr)           (* [comment removed for export] *)
| W44 (vl vh : expr)       (* [comment removed for export] *)
| WBase.                   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint walk (kn : list kentry) (lg : list sentry) (b : expr) (k : Z) : option (list (list kentry * wsrc)) :=
  match lg with
  | [] => Some [(kn, WBase)]
  | SE (SA sb sk) w v :: r =>
      if ranges_apart_x kn sb sk (elen w) b k (ELit 8) then walk kn r b k
      else if (Nat.eqb w 8 && loc_eq kn sb sk b k)%bool then Some [(kn, WSt v)]
      else if (Nat.eqb w 4 && loc_eq kn sb sk b (k + 4))%bool then
        match r with
        | SE (SA sb' sk') 4 v' :: _ => if loc_eq kn sb' sk' b k then Some [(kn, W44 v' v)] else None
        | _ => None
        end
      else if Nat.eqb w 8 then
        let d := EAlu ALU_SUB (EAlu ALU_ADD b (ELit k)) (EAlu ALU_ADD sb (ELit sk)) in
        if (kimp kn (KAlign d 8) && kimp kn (KRange d 0 (2 ^ 40)))%bool then
          match walk (KRange d 8 (2 ^ 40) :: kn) r b k with
          | Some cs => Some ((KRange d 0 0 :: kn, WSt v) :: cs)
          | None => None
          end
        else None
      else None
  end.

(* [comment removed for export] *)
Fixpoint rd8 (p : list sidecond) (r : nat) : list (expr * Z) :=
  match p with
  | [] => []
  | SCReadBase (SA ab ak) 8 false (EVar r') :: q => if Nat.eqb r r' then (ab, ak) :: rd8 q r else rd8 q r
  | _ :: q => rd8 q r
  end.
Fixpoint rd4 (p : list sidecond) (r : nat) : list (expr * Z) :=
  match p with
  | [] => []
  | SCReadBase (SA ab ak) 4 _ (EVar r') :: q => if Nat.eqb r r' then (ab, ak) :: rd4 q r else rd4 q r
  | _ :: q => rd4 q r
  end.

(* [comment removed for export] *)
Definition atom_nz (kn : list kentry) (b : expr) (k : Z) (g : ST.gatom) : bool :=
  match ST.g_id g, ST.g_args g with
  | 7%nat, [x; n] => (loc_eq kn (tb x n) (-8) b k && kimp kn (KRange n 1 62))%bool
  | 8%nat, [x; n] => (loc_eq kn (tb x n) (-8) b k && kimp kn (KRange n 1 61))%bool
  | 9%nat, [x; n; cy] => (loc_eq kn (tb x n) (-8) b k && kimp kn (KRange n 1 61) && kimp kn (KRange cy 0 0))%bool
  | 10%nat, [a] => loc_eq kn a (-8) b k
  | _, _ => false
  end.
(* [comment removed for export] *)
Fixpoint rd_any (p : list sidecond) : list (expr * Z * nat) :=
  match p with
  | [] => []
  | SCReadBase (SA ab ak) 8 false (EVar r) :: q => (ab, ak, r) :: rd_any q
  | _ :: q => rd_any q
  end.
Definition base_nz (kn : list kentry) (src : list ST.gatom) (p : list sidecond) (b : expr) (k : Z) : bool :=
  (existsb (atom_nz kn b k) src
   || existsb (fun t => match t with (ab, ak, r) => (loc_eq kn ab ak b k && kimp kn (KRange (EVar r) 1 MX))%bool end) (rd_any p))%bool.
Definition rd_nz (kn : list kentry) (src : list ST.gatom) (p : list sidecond) (r : nat) : bool :=
  existsb (fun l => base_nz kn src p (fst l) (snd l)) (rd8 p r).

(* [comment removed for export] *)
Definition is_var (e : expr) : option nat := match e with EVar r => Some r | _ => None end.
Definition has_sc (p : list sidecond) (s : sidecond) : bool := existsb (SG.sc_eqb s) p.
Definition rvar_nz (kn : list kentry) (src : list ST.gatom) (p : list sidecond) (e : expr) : bool :=
  match e with EVar r => rd_nz kn src p r | _ => false end.
Definition addnc (kn : list kentry) (src : list ST.gatom) (p : list sidecond) (v : expr) : bool :=
  match v with
  | EAlu ALU_ADD x y =>
      let ok r := (has_sc p (SCBr true BC_GEU v r) || has_sc p (SCBr false BC_LTU v r))%bool in
      ((rvar_nz kn src p x && ok x) || (rvar_nz kn src p y && ok y))%bool
  | _ => false
  end.
Definition shlnz (kn : list kentry) (src : list ST.gatom) (p : list sidecond) (v : expr) : bool :=
  match v with
  | EAlu ALU_OR (EAlu ALU_SLL x s) (EAlu ALU_SRL q (EAlu ALU_SUB (ELit 64) s')) =>
      (expr_eqb s s' && rvar_nz kn src p x && kimp kn (KRange s 1 63)
       && has_sc p (SCBr true BC_EQ (EAlu ALU_SRL x (EAlu ALU_SUB (ELit 64) s)) (ELit 0)))%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition mul_ok (kn : list kentry) (src : list ST.gatom) (pth : list sidecond) (p q : expr) : bool :=
  ((rvar_nz kn src pth p && kimp kn (KRange q 1 MX)) || (rvar_nz kn src pth q && kimp kn (KRange p 1 MX)))%bool.
Definition cy_pat (v p q cy : expr) : bool :=
  match cy with
  | EAlu ALU_ADD (EAlu ALU_SLTU v' (EMd M_MUL p2 q2)) (EMd M_MULHU p3 q3) =>
      (expr_eqb v v' && expr_eqb p p2 && expr_eqb q q2 && ((expr_eqb p p3 && expr_eqb q q3) || (expr_eqb p q3 && expr_eqb q p3)))%bool
  | _ => false
  end.
Definition cy0 (pth : list sidecond) (v p q : expr) : bool :=
  existsb (fun s => match s with
                    | SCBr true BC_EQ cy (ELit 0) => cy_pat v p q cy
                    | SCBr false BC_NE cy (ELit 0) => cy_pat v p q cy
                    | _ => false
                    end) pth.
Definition smul0 (kn : list kentry) (src : list ST.gatom) (pth : list sidecond) (v : expr) : bool :=
  match v with
  | EAlu ALU_ADD c0 (EMd M_MUL p q) => (mul_ok kn src pth p q && cy0 pth v p q)%bool
  | _ => false
  end.
Definition val_nz (kn : list kentry) (src : list ST.gatom) (p : list sidecond) (v : expr) : bool :=
  (kimp kn (KRange v 1 MX) || rvar_nz kn src p v || addnc kn src p v || shlnz kn src p v || smul0 kn src p v)%bool.

(* [comment removed for export] *)
Definition w44_nz (kn : list kentry) (src : list ST.gatom) (p : list sidecond) (vl vh : expr) : bool :=
  match vl, vh with
  | EVar r1, EVar r2 =>
      existsb (fun l1 => existsb (fun l2 => (loc_eq kn (fst l2) (snd l2) (fst l1) (snd l1 + 4) && existsb (atom_nz kn (fst l1) (snd l1)) src)%bool)
                                 (rd4 p r2)) (rd4 p r1)
  | _, _ => false
  end.

Definition src_nz (kn : list kentry) (c : SG.vc) (b : expr) (k : Z) (s : wsrc) : bool :=
  match s with
  | WSt v => val_nz kn (SG.vc_src c) (SG.vc_path c) v
  | W44 vl vh => w44_nz kn (SG.vc_src c) (SG.vc_path c) vl vh
  | WBase => base_nz kn (SG.vc_src c) (SG.vc_path c) b k
  end.
Definition word_nz (kn : list kentry) (c : SG.vc) (b : expr) (k : Z) : bool :=
  match walk kn (SG.vc_log c) b k with
  | Some cs => forallb (fun cp => src_nz (fst cp) c b k (snd cp)) cs
  | None => false
  end.

(* [comment removed for export] *)
Definition smul_pat (kn : list kentry) (c : SG.vc) (v cy : expr) : bool :=
  match v with
  | EAlu ALU_ADD c0 (EMd M_MUL p q) => (cy_pat v p q cy && mul_ok kn (SG.vc_src c) (SG.vc_path c) p q)%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition word_nz_cy (kn : list kentry) (c : SG.vc) (b : expr) (k : Z) (cy : expr) : bool :=
  match walk kn (SG.vc_log c) b k with
  | Some cs => forallb (fun cp => (src_nz (fst cp) c b k (snd cp)
                                  || match snd cp with WSt v => smul_pat (fst cp) c v cy | _ => false end)%bool) cs
  | None => false
  end.

(* [comment removed for export] *)
Definition tbnd_ok (kn : list kentry) (x n : expr) : bool :=
  match erange kn x, erange kn n with
  | Some (lx, hx), Some (ln, hn) => (Z.leb 8 (lx + 8 * ln) && Z.ltb (hx + 8 * hn) (2 ^ 64))%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition tgt_ok (kn : list kentry) (c : SG.vc) (g : ST.gatom) : bool :=
  match ST.g_id g, ST.g_args g with
  | 7%nat, [x; n] => (tbnd_ok kn x n && (kimp kn (KRange n 0 0) || word_nz (kn ++ [KRange n 1 MX]) c (tb x n) (-8)))%bool
  | 8%nat, [x; n] => (tbnd_ok kn x n && (kimp kn (KRange n 62 MX) || kimp kn (KRange n 0 0)
                      || word_nz (kn ++ [KRange n 1 61]) c (tb x n) (-8)))%bool
  | 9%nat, [x; n; cy] => (tbnd_ok kn x n && (kimp kn (KRange n 62 MX) || kimp kn (KRange cy 1 MX) || kimp kn (KRange n 0 0)
                          || word_nz (kn ++ [KRange n 1 61; KRange cy 0 0]) c (tb x n) (-8)
                          || word_nz_cy (kn ++ [KRange n 1 61]) c (tb x n) (-8) cy))%bool
  | 10%nat, [a] => (kimp kn (KRange a 8 MX) && word_nz kn c a (-8))%bool
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition fact_ok (kn : list kentry) (c : SG.vc) (K : kentry) : bool :=
  match K with
  | KRange e lo hi => (kimp kn K || match e with
                                   | EVar r => (Z.leb lo 1 && Z.leb MX hi && rd_nz kn (SG.vc_src c) (SG.vc_path c) r)%bool
                                   | _ => false
                                   end)%bool
  | KAlign _ _ => kimp kn K
  | _ => false
  end.

(* [comment removed for export] *)
Definition psubst (kn : list kentry) (l : lin) : lin :=
  fold_right (fun t acc => match erange kn (snd t) with
                           | Some (lo, hi) => if Z.eqb lo hi then (fst acc + fst t * lo, snd acc) else (fst acc, t :: snd acc)
                           | None => (fst acc, t :: snd acc)
                           end) (fst l, []) (snd l).
Definition pair_contra (kn : list kentry) (K1 K2 : kentry) : bool :=
  match K1, K2 with
  | KRange e1 l1 h1, KRange e2 l2 h2 =>
      if (fact_nowrap kn e1 h1 && fact_nowrap kn e2 h2)%bool then
        let L1 := psubst kn (lin_of e1) in let L2 := psubst kn (lin_of e2) in
        match ladd L1 L2 with
        | (c, []) => Z.ltb ((h1 + h2 - c) / 2 ^ 64) ((l1 + l2 - c + 2 ^ 64 - 1) / 2 ^ 64)   (* [comment removed for export] *)
        | _ => false
        end
      else false
  | _, _ => false
  end.
Definition infeasible (kn : list kentry) : bool := existsb (fun K1 => existsb (pair_contra kn K1) kn) kn.

(* [comment removed for export] *)
Definition nrc_ok (c : SG.vc) : bool :=
  let kn0 := pkn (SG.vc_kn c) (SG.vc_path c) in
  match SL.al_tight kn0 kn0 with
  | None => true                                                   (* [comment removed for export] *)
  | Some l =>
      let kn := l ++ kn0 in
      (infeasible kn || (forallb (tgt_ok kn c) (SG.vc_tgt c) && forallb (fact_ok kn c) (SG.vc_facts c)))%bool
  end.

End C.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable segs : list Segment.
Variable E : env.
Variable m : word -> option byte.

Lemma pkn_ok : forall p kn, know_ok segs E m kn -> scs_denot segs m E p -> know_ok segs E m (pkn kn p).
Proof.
  induction p as [|s r IH]; intros kn HK HP; cbn [pkn]; [exact HK|].
  unfold scs_denot in HP. apply Forall_cons_iff in HP as [H1 HR].
  destruct s as [t c a b| | | | | |]; try exact (IH kn HK HR).
  destruct (SL.learn kn c t a b) as [l|] eqn:HL; [|exact (IH kn HK HR)].
  apply IH; [|exact HR]. unfold know_ok. apply Forall_app. split; [|exact HK].
  cbn [sc_denot] in H1. exact (SL.learn_sound segs E m kn c t a b l HK H1 HL).
Qed.

Lemma same_loc_ok : forall b1 k1 b2 k2, same_loc b1 k1 b2 k2 = true ->
  (u (edenot E b1) + k1) mod 2 ^ 64 = (u (edenot E b2) + k2) mod 2 ^ 64.
Proof.
  intros b1 k1 b2 k2 H. unfold same_loc in H.
  pose proof (lin_of_sound E (EAlu ALU_SUB b1 b2)) as [q Hq].
  destruct (lin_of (EAlu ALU_SUB b1 b2)) as [c ts] eqn:HL. destruct ts; [|discriminate].
  apply Z.eqb_eq in H. unfold lden, uE in Hq. cbn [fst snd tden] in Hq. cbn [edenot] in Hq. rewrite u_sub64 in Hq.
  assert (Hc : c mod 2 ^ 64 = (u (edenot E b1) - u (edenot E b2)) mod 2 ^ 64).
  { replace c with (c + 0) by ring. rewrite Hq. rewrite Z_mod_plus_full, Z.mod_mod by lia. reflexivity. }
  rewrite H in Hc.
  replace (u (edenot E b1) + k1) with ((u (edenot E b1) - u (edenot E b2)) + (u (edenot E b2) + k1)) by ring.
  rewrite Zplus_mod, <- Hc, <- Zplus_mod. f_equal. ring.
Qed.

Lemma loc_eq_ok : forall kn b1 k1 b2 k2, know_ok segs E m kn -> loc_eq segs kn b1 k1 b2 k2 = true ->
  (u (edenot E b1) + k1) mod 2 ^ 64 = (u (edenot E b2) + k2) mod 2 ^ 64.
Proof.
  intros kn b1 k1 b2 k2 HK H. unfold loc_eq in H. apply orb_prop in H as [H|H]; [exact (same_loc_ok _ _ _ _ H)|].
  pose proof (ST.kimplied_ok segs E m kn _ HK H) as K. cbn [kentry_ok] in K. unfold ldiff in K. cbn [edenot] in K.
  rewrite u_sub64, !u_add64, !Z_to_bv_unsigned in K. unfold bv_wrap in K. change (bv_modulus 64) with (2 ^ 64) in K.
  rewrite !Zplus_mod_idemp_r in K.
  assert (Z0 : ((u (edenot E b1) + k1) mod 2 ^ 64 - (u (edenot E b2) + k2) mod 2 ^ 64) mod 2 ^ 64 = 0) by lia.
  apply Z.mod_divide in Z0; [|lia]. destruct Z0 as [q Hq].
  pose proof (Z.mod_pos_bound (u (edenot E b1) + k1) (2 ^ 64) ltac:(lia)).
  pose proof (Z.mod_pos_bound (u (edenot E b2) + k2) (2 ^ 64) ltac:(lia)).
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma estart_u : forall a w, flat E a w -> u (adenot E a) = estart E a.
Proof. intros a w H. exact (flat_u E a w H). Qed.

(* [comment removed for export] *)
Definition src_ok (M' : word -> option byte) (a : Z) (s : wsrc) : Prop :=
  match s with
  | WSt v => NRV.wat segs M' a (u (edenot E v))
  | W44 vl vh => NRV.wat segs M' a (u (edenot E vl) mod 2 ^ 32 + 2 ^ 32 * (u (edenot E vh) mod 2 ^ 32))
  | WBase => forall W, NRV.wat segs m a W -> NRV.wat segs M' a W
  end.

Lemma src_ok_miss : forall lg a s b k w v, flat E (SA b k) (Z.of_nat w) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (a + 8 <= estart E (SA b k) \/ estart E (SA b k) + Z.of_nat w <= a) ->
  src_ok (mem_denot E m lg) a s -> src_ok (mem_denot E m (SE (SA b k) w v :: lg)) a s.
Proof.
  intros lg a s b k w v Hf H0 H8 Hap H. pose proof (estart_u _ _ Hf) as Hu.
  assert (Hs : u (adenot E (SA b k)) + Z.of_nat w <= 2 ^ 64) by (destruct Hf as (? & ? & ? & ?); lia).
  destruct s as [v'|vl vh|]; cbn [src_ok] in *.
  - apply NRV.wat_miss; [lia | lia | exact Hs | rewrite Hu; exact Hap | exact H].
  - apply NRV.wat_miss; [lia | lia | exact Hs | rewrite Hu; exact Hap | exact H].
  - intros W HW. apply NRV.wat_miss; [lia | lia | exact Hs | rewrite Hu; exact Hap | exact (H W HW)].
Qed.

Lemma elenZ_elen : forall w, (w <= 8)%nat -> elenZ E (elen w) = Z.of_nat w.
Proof.
  intros w Hw. unfold elenZ, elen. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. lia.
Qed.

Lemma u_adenot_mod : forall b k, u (adenot E (SA b k)) = (u (edenot E b) + k) mod 2 ^ 64.
Proof. intros b k. unfold adenot. cbn [a_base a_off]. unfold v_addi. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma u_rng : forall w : word, 0 <= u w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R. Qed.

Lemma walk_ok : forall lg kn b k cs, know_ok segs E m kn -> log_flat E lg -> walk segs kn lg b k = Some cs ->
  0 <= estart E (SA b k) -> estart E (SA b k) + 8 <= 2 ^ 64 ->
  Exists (fun cp => know_ok segs E m (fst cp) /\ src_ok (mem_denot E m lg) (estart E (SA b k)) (snd cp)) cs.
Proof.
  induction lg as [|[[sb sk] w v] r IH]; intros kn b k cs HK HL HW A0 A8.
  - cbn [walk] in HW. injection HW as <-. apply Exists_cons_hd. cbn [fst snd src_ok mem_denot]. split; [exact HK|]. intros W H. exact H.
  - set (a := estart E (SA b k)) in *.
    cbn [log_flat] in HL. destruct HL as (Hw8 & Hf & HL).
    pose proof (estart_u _ _ Hf) as Hsu.
    assert (Ha : a = (u (edenot E b) + k) mod 2 ^ 64) by (unfold a, estart in *; cbn [a_base a_off] in *; rewrite Z.mod_small; lia).
    cbn [walk] in HW.
    destruct (ranges_apart_x kn sb sk (elen w) b k (ELit 8)) eqn:Hap.
    { pose proof (ranges_apart_x_sound segs E m kn sb sk (elen w) b k (ELit 8) HK Hap) as AP.
      rewrite elenZ_elen in AP by exact Hw8.
      assert (E8 : elenZ E (ELit 8) = 8) by reflexivity. rewrite E8 in AP. fold a in AP.
      pose proof (IH kn b k cs HK HL HW A0 A8) as IH'. eapply Exists_impl; [|exact IH'].
      intros [kn' s'] [H1 H2]. split; [exact H1|]. cbn [snd] in *. apply src_ok_miss; [exact Hf | exact A0 | exact A8 | | exact H2].
      destruct AP as [AP|AP]; [right | left]; lia. }
    destruct (Nat.eqb w 8 && loc_eq segs kn sb sk b k)%bool eqn:H8.
    { apply andb_prop in H8 as [Hw Hs]. apply Nat.eqb_eq in Hw. subst w. injection HW as <-. apply Exists_cons_hd.
      cbn [fst snd src_ok]. split; [exact HK|]. apply NRV.wat_hit; [|lia].
      rewrite u_adenot_mod, (loc_eq_ok _ _ _ _ _ HK Hs). exact Ha. }
    destruct (Nat.eqb w 4 && loc_eq segs kn sb sk b (k + 4))%bool eqn:H4.
    { apply andb_prop in H4 as [Hw Hs]. apply Nat.eqb_eq in Hw. subst w.
      destruct r as [|[[sb' sk'] w' v'] r']; [discriminate|]. destruct w' as [|[|[|[|[|w']]]]]; try discriminate.
      destruct (loc_eq segs kn sb' sk' b k) eqn:Hs'; [|discriminate]. injection HW as <-. apply Exists_cons_hd.
      cbn [fst snd src_ok]. split; [exact HK|].
      destruct HL as (_ & Hf' & _). pose proof (estart_u _ _ Hf') as Hsu'.
      assert (U1 : u (adenot E (SA sb sk)) = a + 4).
      { rewrite u_adenot_mod, (loc_eq_ok _ _ _ _ _ HK Hs). unfold a, estart. cbn [a_base a_off]. rewrite Z.mod_small; [lia|].
        unfold a, estart in A8, A0. cbn [a_base a_off] in A8, A0. pose proof (u_rng (edenot E b)). lia. }
      assert (U0 : u (adenot E (SA sb' sk')) = a) by (rewrite u_adenot_mod, (loc_eq_ok _ _ _ _ _ HK Hs'); symmetry; exact Ha).
      apply NRV.wat_44; [exact A0 | exact A8 | |].
      + apply NRV.w4at_miss; [lia | lia | destruct Hf as (? & ? & ? & ?); lia | left; lia |].
        apply NRV.w4at_hit; [symmetry; exact U0 | lia].
      + apply NRV.w4at_hit; [symmetry; exact U1 | lia]. }
    destruct (Nat.eqb w 8) eqn:Hw; [|discriminate]. apply Nat.eqb_eq in Hw. subst w.
    set (d := EAlu ALU_SUB (EAlu ALU_ADD b (ELit k)) (EAlu ALU_ADD sb (ELit sk))) in *.
    destruct (kimp segs kn (KAlign d 8) && kimp segs kn (KRange d 0 (2 ^ 40)))%bool eqn:Hk; [|discriminate].
    apply andb_prop in Hk as [Hk1 Hk2].
    pose proof (ST.kimplied_ok segs E m kn _ HK Hk1) as K1. pose proof (ST.kimplied_ok segs E m kn _ HK Hk2) as K2.
    cbn [kentry_ok] in K1, K2.
    destruct (walk segs (KRange d 8 (2 ^ 40) :: kn) r b k) as [cs'|] eqn:HW'; [|discriminate]. injection HW as <-.
    assert (Ud : u (edenot E d) = (a - u (adenot E (SA sb sk))) mod 2 ^ 64).
    { unfold d. cbn [edenot]. rewrite u_sub64, !u_add64, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite !Zplus_mod_idemp_r. rewrite <- Ha, <- u_adenot_mod. reflexivity. }
    pose proof (u_rng (adenot E (SA sb sk))) as Rs.
    destruct (Z.eq_dec (u (edenot E d)) 0) as [D0|D0].
    + apply Exists_cons_hd. cbn [fst snd src_ok]. split.
      * unfold know_ok. constructor; [cbn [kentry_ok]; lia | exact HK].
      * apply NRV.wat_hit; [|lia]. rewrite Ud in D0. apply Z.mod_divide in D0; [|lia]. destruct D0 as [q Hq].
        assert (q = 0) by nia. subst q. lia.
    + apply Exists_cons_tl.
      assert (D8 : 8 <= u (edenot E d)).
      { destruct K1 as [_ K1]. apply Z.mod_divide in K1; [|lia]. destruct K1 as [q Hq]. lia. }
      assert (HK' : know_ok segs E m (KRange d 8 (2 ^ 40) :: kn)) by (unfold know_ok; constructor; [cbn [kentry_ok]; lia | exact HK]).
      pose proof (IH _ b k cs' HK' HL HW' A0 A8) as IH'. eapply Exists_impl; [|exact IH'].
      intros [kn' s'] [H1 H2]. split; [exact H1|]. cbn [snd] in *. apply src_ok_miss; [exact Hf | exact A0 | exact A8 | | exact H2].
      rewrite Hsu in Rs. rewrite Hsu in Ud. change (Z.of_nat 8) with 8.
      destruct (Z.le_gt_cases (estart E (SA sb sk)) a) as [L|G].
      * right. rewrite Z.mod_small in Ud by lia. lia.
      * left. rewrite <- (Z_mod_plus_full _ 1) in Ud. rewrite Z.mod_small in Ud by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition loc (b : expr) (k : Z) : Z := (u (edenot E b) + k) mod 2 ^ 64.
Local Notation GP := (SNU.snu_gp segs).

Lemma loc_rng : forall b k, 0 <= loc b k < 2 ^ 64.
Proof. intros b k. unfold loc. apply Z.mod_pos_bound. lia. Qed.

Lemma u_tb : forall x n, u (edenot E x) + 8 * u (edenot E n) < 2 ^ 64 ->
  u (edenot E (tb x n)) = u (edenot E x) + 8 * u (edenot E n).
Proof.
  intros x n H. unfold tb. cbn [edenot]. rewrite u_add64, u_mul64, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (8 mod 2 ^ 64) with 8.
  pose proof (u_rng (edenot E x)). pose proof (u_rng (edenot E n)).
  rewrite (Z.mod_small (8 * _)) by lia. apply Z.mod_small. lia.
Qed.

Lemma loc_tb : forall x n, 8 <= u (edenot E x) + 8 * u (edenot E n) < 2 ^ 64 ->
  loc (tb x n) (-8) = u (edenot E x) + 8 * u (edenot E n) - 8.
Proof. intros x n H. unfold loc. rewrite u_tb by lia. apply Z.mod_small. lia. Qed.

Lemma wat_loc : forall M a b k W, NRV.wat segs M a W -> a = loc b k -> NRV.wat segs M (loc b k) W.
Proof. intros M a b k W H ->. exact H. Qed.

Lemma atom_nz_ok : forall kn b k g, know_ok segs E m kn -> GP (ST.g_id g) (map (edenot E) (ST.g_args g)) m ->
  atom_nz segs kn b k g = true -> exists w, NRV.wat segs m (loc b k) w /\ w <> 0 /\ loc b k + 8 <= 2 ^ 64.
Proof.
  intros kn b k [id args] HK HG H. cbn [ST.g_id ST.g_args atom_nz] in *. unfold atom_nz in H. cbn [ST.g_id ST.g_args] in H.
  do 7 (destruct id as [|id]; [discriminate|]).
  destruct id as [|id].
  { (* [comment removed for export] *) destruct args as [|x [|n [|? ?]]]; try discriminate. apply andb_prop in H as [H1 H2].
    pose proof (loc_eq_ok _ _ _ _ _ HK H1) as L. pose proof (ST.kimplied_ok segs E m kn _ HK H2) as K. cbn [kentry_ok] in K.
    cbn [map SNU.snu_gp] in HG. destruct HG as [Hb [Hz|Ht]]; [lia|]. unfold SNU.tbnd in Hb.
    destruct (NRV.topnz_wat segs m _ _ Ht) as (w & Hw & Hn). exists w. split; [|split; [exact Hn|]].
    - apply (wat_loc _ _ _ _ _ Hw). fold (loc (tb x n) (-8)) in L. rewrite <- (loc_tb x n Hb). exact L.
    - fold (loc b k) in L. fold (loc (tb x n) (-8)) in L. rewrite <- L, loc_tb by exact Hb. lia. }
  destruct id as [|id].
  { (* [comment removed for export] *) destruct args as [|x [|n [|? ?]]]; try discriminate. apply andb_prop in H as [H1 H2].
    pose proof (loc_eq_ok _ _ _ _ _ HK H1) as L. pose proof (ST.kimplied_ok segs E m kn _ HK H2) as K. cbn [kentry_ok] in K.
    cbn [map SNU.snu_gp] in HG. destruct HG as [Hb [Hz|[Hz|Ht]]]; [lia|lia|]. unfold SNU.tbnd in Hb.
    destruct (NRV.topnz_wat segs m _ _ Ht) as (w & Hw & Hn). exists w. split; [|split; [exact Hn|]].
    - apply (wat_loc _ _ _ _ _ Hw). fold (loc (tb x n) (-8)) in L. rewrite <- (loc_tb x n Hb). exact L.
    - fold (loc b k) in L. fold (loc (tb x n) (-8)) in L. rewrite <- L, loc_tb by exact Hb. lia. }
  destruct id as [|id].
  { (* [comment removed for export] *) destruct args as [|x [|n [|cy [|? ?]]]]; try discriminate. apply andb_prop in H as [H12 H3].
    apply andb_prop in H12 as [H1 H2].
    pose proof (loc_eq_ok _ _ _ _ _ HK H1) as L. pose proof (ST.kimplied_ok segs E m kn _ HK H2) as K. cbn [kentry_ok] in K.
    pose proof (ST.kimplied_ok segs E m kn _ HK H3) as K3. cbn [kentry_ok] in K3.
    cbn [map SNU.snu_gp] in HG. destruct HG as [Hb [Hz|[Hz|[Hz|Ht]]]]; [lia|lia|lia|]. unfold SNU.tbnd in Hb.
    destruct (NRV.topnz_wat segs m _ _ Ht) as (w & Hw & Hn). exists w. split; [|split; [exact Hn|]].
    - apply (wat_loc _ _ _ _ _ Hw). fold (loc (tb x n) (-8)) in L. rewrite <- (loc_tb x n Hb). exact L.
    - fold (loc b k) in L. fold (loc (tb x n) (-8)) in L. rewrite <- L, loc_tb by exact Hb. lia. }
  destruct id as [|id]; [|discriminate].
  { (* [comment removed for export] *) destruct args as [|a [|? ?]]; try discriminate.
    pose proof (loc_eq_ok _ _ _ _ _ HK H) as L. cbn [map SNU.snu_gp] in HG.
    destruct (NRV.topw_wat segs m _ HG) as (H8 & w & Hw & Hn). exists w.
    pose proof (u_rng (edenot E a)).
    assert (La : loc a (-8) = u (edenot E a) - 8) by (unfold loc; apply Z.mod_small; lia).
    split; [|split; [exact Hn|]].
    - apply (wat_loc _ _ _ _ _ Hw). fold (loc a (-8)) in L. rewrite <- La. exact L.
    - fold (loc b k) in L. fold (loc a (-8)) in L. rewrite <- L, La. lia. }
Qed.

Lemma in_rd_any : forall p ab ak r, In (ab, ak, r) (rd_any p) -> In (SCReadBase (SA ab ak) 8 false (EVar r)) p.
Proof.
  induction p as [|sc q IH]; intros ab ak r H; [destruct H|]. cbn [rd_any] in H.
  destruct sc as [| | | | |[b0 k0] w sx e|]; try (right; exact (IH _ _ _ H)).
  destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try (right; exact (IH _ _ _ H)).
  destruct sx; [right; exact (IH _ _ _ H)|]. destruct e; try (right; exact (IH _ _ _ H)).
  destruct H as [H|H]; [injection H as <- <- <-; left; reflexivity | right; exact (IH _ _ _ H)].
Qed.
Lemma in_rd8 : forall p r ab ak, In (ab, ak) (rd8 p r) -> In (SCReadBase (SA ab ak) 8 false (EVar r)) p.
Proof.
  induction p as [|sc q IH]; intros r ab ak H; [destruct H|]. cbn [rd8] in H.
  destruct sc as [| | | | |[b0 k0] w sx e|]; try (right; exact (IH _ _ _ H)).
  destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try (right; exact (IH _ _ _ H)).
  destruct sx; [right; exact (IH _ _ _ H)|]. destruct e; try (right; exact (IH _ _ _ H)).
  destruct (Nat.eqb r n) eqn:Hr; [|right; exact (IH _ _ _ H)]. apply Nat.eqb_eq in Hr. subst n.
  destruct H as [H|H]; [injection H as <- <-; left; reflexivity | right; exact (IH _ _ _ H)].
Qed.
Lemma in_rd4 : forall p r ab ak, In (ab, ak) (rd4 p r) -> exists sx, In (SCReadBase (SA ab ak) 4 sx (EVar r)) p.
Proof.
  induction p as [|sc q IH]; intros r ab ak H; [destruct H|]. cbn [rd4] in H.
  destruct sc as [| | | | |[b0 k0] w sx e|]; try (destruct (IH _ _ _ H) as [sx' H']; exists sx'; right; exact H').
  destruct w as [|[|[|[|[|w]]]]]; try (destruct (IH _ _ _ H) as [sx' H']; exists sx'; right; exact H').
  destruct e; try (destruct (IH _ _ _ H) as [sx' H']; exists sx'; right; exact H').
  destruct (Nat.eqb r n) eqn:Hr; [|destruct (IH _ _ _ H) as [sx' H']; exists sx'; right; exact H']. apply Nat.eqb_eq in Hr. subst n.
  destruct H as [H|H]; [injection H as <- <-; exists sx; left; reflexivity | destruct (IH _ _ _ H) as [sx' H']; exists sx'; right; exact H'].
Qed.

Lemma in_path : forall p s, scs_denot segs m E p -> In s p -> sc_denot segs m E s.
Proof. intros p s HP Hin. exact (proj1 (Forall_forall _ _) HP s Hin). Qed.

Lemma rr8_loc : forall p ab ak r, scs_denot segs m E p -> In (SCReadBase (SA ab ak) 8 false (EVar r)) p ->
  NRV.wat segs m (loc ab ak) (u (ev E r)).
Proof.
  intros p ab ak r HP Hin. pose proof (NRV.rr8 segs m E ab ak r (in_path p _ HP Hin)) as H.
  rewrite u_adenot_mod in H. exact H.
Qed.

Lemma base_nz_ok : forall kn src p b k, know_ok segs E m kn -> SG.gholds GP E m src -> scs_denot segs m E p ->
  base_nz segs kn src p b k = true -> exists w, NRV.wat segs m (loc b k) w /\ w <> 0.
Proof.
  intros kn src p b k HK HS HP H. unfold base_nz in H. apply orb_prop in H as [H|H].
  - apply existsb_exists in H as (g & Hin & Hg). pose proof (proj1 (Forall_forall _ _) HS g Hin) as Hgp.
    destruct (atom_nz_ok kn b k g HK Hgp Hg) as (w & Hw & Hn & _). exists w. split; [exact Hw | exact Hn].
  - apply existsb_exists in H as ([[ab ak] r] & Hin & Hg). apply andb_prop in Hg as [H1 H2].
    pose proof (loc_eq_ok _ _ _ _ _ HK H1) as L. pose proof (ST.kimplied_ok segs E m kn _ HK H2) as K. cbn [kentry_ok edenot] in K.
    exists (u (ev E r)). split; [|lia]. fold (loc ab ak) in L. fold (loc b k) in L. rewrite <- L.
    exact (rr8_loc p ab ak r HP (in_rd_any p ab ak r Hin)).
Qed.

Lemma rd_nz_ok : forall kn src p r, know_ok segs E m kn -> SG.gholds GP E m src -> scs_denot segs m E p ->
  rd_nz segs kn src p r = true -> u (ev E r) <> 0.
Proof.
  intros kn src p r HK HS HP H. unfold rd_nz in H. apply existsb_exists in H as ([ab ak] & Hin & Hb). cbn [fst snd] in Hb.
  destruct (base_nz_ok kn src p ab ak HK HS HP Hb) as (w & Hw & Hn).
  pose proof (rr8_loc p ab ak r HP (in_rd8 p r ab ak Hin)) as Hr.
  rewrite (NRV.wat_fun segs m _ _ _ Hr Hw). exact Hn.
Qed.

Lemma rvar_nz_ok : forall kn src p e, know_ok segs E m kn -> SG.gholds GP E m src -> scs_denot segs m E p ->
  rvar_nz segs kn src p e = true -> u (edenot E e) <> 0.
Proof.
  intros kn src p e HK HS HP H. destruct e; try discriminate. cbn [rvar_nz] in H. cbn [edenot]. exact (rd_nz_ok kn src p n HK HS HP H).
Qed.

Lemma has_sc_ok : forall p s, scs_denot segs m E p -> has_sc p s = true -> sc_denot segs m E s.
Proof.
  intros p s HP H. unfold has_sc in H. apply existsb_exists in H as (s' & Hin & Heq). apply SG.sc_eqb_eq in Heq. subst s'.
  exact (in_path p s HP Hin).
Qed.

Lemma br_geu : forall a b, sc_denot segs m E (SCBr true BC_GEU a b) -> u (edenot E b) <= u (edenot E a).
Proof. intros a b H. pose proof (SNV.scbr_u segs m E true BC_GEU a b H) as Q. exact Q. Qed.
Lemma br_ltu_f : forall a b, sc_denot segs m E (SCBr false BC_LTU a b) -> u (edenot E b) <= u (edenot E a).
Proof. intros a b H. pose proof (SNV.scbr_u segs m E false BC_LTU a b H) as Q. exact Q. Qed.
Lemma br_eq : forall a b, sc_denot segs m E (SCBr true BC_EQ a b) -> u (edenot E a) = u (edenot E b).
Proof. intros a b H. pose proof (SNV.scbr_u segs m E true BC_EQ a b H) as Q. exact Q. Qed.
Lemma br_ne_f : forall a b, sc_denot segs m E (SCBr false BC_NE a b) -> u (edenot E a) = u (edenot E b).
Proof. intros a b H. pose proof (SNV.scbr_u segs m E false BC_NE a b H) as Q. exact Q. Qed.

(* [comment removed for export] *)
Lemma smul_vals : forall c0 p q cy, cy_pat (EAlu ALU_ADD c0 (EMd M_MUL p q)) p q cy = true ->
  u (edenot E p) <> 0 -> u (edenot E q) <> 0 ->
  u (edenot E (EAlu ALU_ADD c0 (EMd M_MUL p q))) <> 0 \/ u (edenot E cy) <> 0.
Proof.
  intros c0 p q cy H Hp Hq. unfold cy_pat in H.
  destruct cy as [| |op1 a1 b1| | | | |]; try discriminate. destruct op1; try discriminate.
  destruct a1 as [| |op2 v' m2| | | | |]; try discriminate. destruct op2; try discriminate.
  destruct m2 as [| | | |op3 p2 q2| | |]; try discriminate. destruct op3; try discriminate.
  destruct b1 as [| | | |op4 p3 q3| | |]; try discriminate. destruct op4; try discriminate.
  apply andb_prop in H as [H HO]. apply andb_prop in H as [H Hq2]. apply andb_prop in H as [Hv Hp2].
  apply expr_eqb_eq in Hv. apply expr_eqb_eq in Hp2. apply expr_eqb_eq in Hq2. subst v' p2 q2.
  set (X := u (edenot E p)). set (Y := u (edenot E q)). set (C := u (edenot E c0)).
  assert (Hv : u (edenot E (EAlu ALU_ADD c0 (EMd M_MUL p q))) = (C + (X * Y) mod 2 ^ 64) mod 2 ^ 64).
  { cbn [edenot]. rewrite u_add64, u_mul64. reflexivity. }
  pose proof (u_rng (edenot E p)) as Rp. pose proof (u_rng (edenot E q)) as Rq. pose proof (u_rng (edenot E c0)) as Rc.
  pose proof (NRV.smul_nz X Y C Rp Rq Rc Hp Hq) as S.
  rewrite Hv. destruct S as [S|S]; [left; exact S|right].
  assert (Hm : u (edenot E p3) * u (edenot E q3) = X * Y).
  { apply orb_prop in HO as [HO|HO]; apply andb_prop in HO as [H1 H2]; apply expr_eqb_eq in H1; apply expr_eqb_eq in H2;
      subst p3 q3; [reflexivity | apply Z.mul_comm]. }
  cbn [edenot]. rewrite u_add64, u_sltu64, u_mulhu64, Hm.
  replace (u (alu64 ALU_ADD (edenot E c0) (mul_div M_MUL (edenot E p) (edenot E q)))) with ((C + (X * Y) mod 2 ^ 64) mod 2 ^ 64)
    by (rewrite <- Hv; reflexivity).
  rewrite u_mul64. fold X Y. exact S.
Qed.

Lemma val_nz_ok : forall kn src p v, know_ok segs E m kn -> SG.gholds GP E m src -> scs_denot segs m E p ->
  val_nz segs kn src p v = true -> u (edenot E v) <> 0.
Proof.
  intros kn src p v HK HS HP H. unfold val_nz in H.
  apply orb_prop in H as [H|H5]; [apply orb_prop in H as [H|H4]; [apply orb_prop in H as [H|H3]; [apply orb_prop in H as [H1|H2]|]|]|].
  - pose proof (ST.kimplied_ok segs E m kn _ HK H1) as K. cbn [kentry_ok] in K. lia.
  - exact (rvar_nz_ok kn src p v HK HS HP H2).
  - (* [comment removed for export] *) destruct v as [| |op x y| | | | |]; try discriminate. destruct op; try discriminate. cbn [addnc] in H3.
    assert (G : forall r, rvar_nz segs kn src p r = true ->
                (has_sc p (SCBr true BC_GEU (EAlu ALU_ADD x y) r) || has_sc p (SCBr false BC_LTU (EAlu ALU_ADD x y) r))%bool = true ->
                u (edenot E (EAlu ALU_ADD x y)) <> 0).
    { intros r Hr Ho. pose proof (rvar_nz_ok kn src p r HK HS HP Hr) as Nr. pose proof (u_rng (edenot E r)).
      apply orb_prop in Ho as [Ho|Ho].
      - pose proof (br_geu _ _ (has_sc_ok p _ HP Ho)). lia.
      - pose proof (br_ltu_f _ _ (has_sc_ok p _ HP Ho)). lia. }
    apply orb_prop in H3 as [H3|H3]; apply andb_prop in H3 as [Hr Ho]; exact (G _ Hr Ho).
  - (* [comment removed for export] *) destruct v as [| |op a b| | | | |]; try discriminate. destruct op; try discriminate.
    destruct a as [| |op1 x sh| | | | |]; try discriminate. destruct op1; try discriminate.
    destruct b as [| |op2 q d| | | | |]; try discriminate. destruct op2; try discriminate.
    destruct d as [| |op3 l64 sh'| | | | |]; try discriminate. destruct op3; try discriminate.
    destruct l64 as [z| | | | | | |]; try discriminate. destruct z as [|[z|z|]|z]; try discriminate.
    do 6 (destruct z as [z|z|]; try discriminate). cbn [shlnz] in H4.
    repeat match type of H4 with (_ && _)%bool = true => apply andb_prop in H4 as [H4 ?] end.
    apply expr_eqb_eq in H4. subst sh'.
    match goal with Hr : rvar_nz _ _ _ _ x = true |- _ => pose proof (rvar_nz_ok kn src p x HK HS HP Hr) as Nx end.
    match goal with Hk : kimp _ _ (KRange sh 1 63) = true |- _ => pose proof (ST.kimplied_ok segs E m kn _ HK Hk) as Ks end.
    cbn [kentry_ok] in Ks.
    match goal with Hh : has_sc _ _ = true |- _ => pose proof (br_eq _ _ (has_sc_ok p _ HP Hh)) as Z0 end.
    assert (Hd : u (alu64 ALU_SUB (Z_to_bv 64 64) (edenot E sh)) mod 64 = 64 - u (edenot E sh)).
    { rewrite u_sub64, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      change (64 mod 2 ^ 64) with 64. rewrite (Z.mod_small (64 - _)) by lia. apply Z.mod_small. lia. }
    cbn [edenot] in Z0 |- *. rewrite u_srl64, Hd in Z0. change (u (Z_to_bv 64 0)) with 0 in Z0.
    unfold alu64 at 1, alu at 1. rewrite bv_or_unsigned. fold (alu64 ALU_SLL (edenot E x) (edenot E sh)).
    fold (alu64 ALU_SRL (edenot E q) (alu64 ALU_SUB (Z_to_bv 64 64) (edenot E sh))).
    rewrite u_sll64, u_srl64, Hd.
    rewrite (Z.mod_small (u (edenot E sh)) 64) by lia.
    apply (NRV.shl_top_nz _ _ _ _ (u_rng _)); [apply (u_rng (edenot E q)) | lia | reflexivity | exact Nx | exact Z0].
  - (* [comment removed for export] *) destruct v as [| |op c0 mq| | | | |]; try discriminate. destruct op; try discriminate.
    destruct mq as [| | | |op1 p0 q0| | |]; try discriminate. destruct op1; try discriminate. cbn [smul0] in H5.
    apply andb_prop in H5 as [Hm Hc]. unfold mul_ok in Hm.
    assert (NZ : u (edenot E p0) <> 0 /\ u (edenot E q0) <> 0).
    { apply orb_prop in Hm as [Hm|Hm]; apply andb_prop in Hm as [Hr Hk]; pose proof (ST.kimplied_ok segs E m kn _ HK Hk) as K;
        cbn [kentry_ok] in K; pose proof (rvar_nz_ok kn src p _ HK HS HP Hr); split; lia. }
    unfold cy0 in Hc. apply existsb_exists in Hc as (sc & Hin & Hs).
    destruct sc as [t c a b| | | | | |]; try discriminate.
    destruct t, c; try discriminate; destruct b as [z| | | | | | |]; try discriminate; destruct z; try discriminate.
    + pose proof (br_eq _ _ (in_path p _ HP Hin)) as E0. change (u (edenot E (ELit 0))) with 0 in E0.
      destruct (smul_vals c0 p0 q0 a Hs (proj1 NZ) (proj2 NZ)) as [S|S]; [exact S | exfalso; exact (S E0)].
    + pose proof (br_ne_f _ _ (in_path p _ HP Hin)) as E0. change (u (edenot E (ELit 0))) with 0 in E0.
      destruct (smul_vals c0 p0 q0 a Hs (proj1 NZ) (proj2 NZ)) as [S|S]; [exact S | exfalso; exact (S E0)].
Qed.

Lemma rr4_loc : forall p ab ak sx r, scs_denot segs m E p -> In (SCReadBase (SA ab ak) 4 sx (EVar r)) p ->
  NRV.w4at segs m (loc ab ak) (u (ev E r) mod 2 ^ 32).
Proof.
  intros p ab ak sx r HP Hin. pose proof (NRV.rr4 segs m E ab ak sx r (in_path p _ HP Hin)) as H.
  rewrite u_adenot_mod in H. exact H.
Qed.

Lemma w44_nz_ok : forall kn src p vl vh, know_ok segs E m kn -> SG.gholds GP E m src -> scs_denot segs m E p ->
  w44_nz segs kn src p vl vh = true -> u (edenot E vl) mod 2 ^ 32 + 2 ^ 32 * (u (edenot E vh) mod 2 ^ 32) <> 0.
Proof.
  intros kn src p vl vh HK HS HP H. destruct vl as [|r1| | | | | |]; try discriminate. destruct vh as [|r2| | | | | |]; try discriminate.
  cbn [w44_nz] in H. apply existsb_exists in H as ([b1 k1] & Hin1 & H). apply existsb_exists in H as ([b2 k2] & Hin2 & H).
  cbn [fst snd] in H. apply andb_prop in H as [Hl Ha]. apply existsb_exists in Ha as (g & Hg & Ha).
  destruct (atom_nz_ok kn b1 k1 g HK (proj1 (Forall_forall _ _) HS g Hg) Ha) as (w & Hw & Hn & H8).
  pose proof (loc_eq_ok _ _ _ _ _ HK Hl) as L. fold (loc b2 k2) in L.
  destruct (in_rd4 p r1 b1 k1 Hin1) as [sx1 I1]. destruct (in_rd4 p r2 b2 k2 Hin2) as [sx2 I2].
  pose proof (rr4_loc p b1 k1 sx1 r1 HP I1) as W1. pose proof (rr4_loc p b2 k2 sx2 r2 HP I2) as W2.
  assert (L4 : loc b2 k2 = loc b1 k1 + 4).
  { rewrite L. unfold loc. replace (u (edenot E b1) + (k1 + 4)) with ((u (edenot E b1) + k1) + 4) by ring.
    rewrite <- Zplus_mod_idemp_l. fold (loc b1 k1). apply Z.mod_small. pose proof (loc_rng b1 k1). lia. }
  rewrite L4 in W2. pose proof (loc_rng b1 k1).
  pose proof (NRV.wat_44 segs m (loc b1 k1) _ _ ltac:(lia) H8 W1 W2) as W.
  cbn [edenot]. rewrite (NRV.wat_fun segs m _ _ _ W Hw). exact Hn.
Qed.

Lemma estart_loc : forall b k, 0 <= estart E (SA b k) -> estart E (SA b k) < 2 ^ 64 -> loc b k = estart E (SA b k).
Proof. intros b k H0 H1. unfold loc, estart. cbn [a_base a_off]. apply Z.mod_small. unfold estart in *. cbn in *. lia. Qed.

Lemma src_nz_ok : forall kn c b k s, know_ok segs E m kn -> SG.gholds GP E m (SG.vc_src c) -> scs_denot segs m E (SG.vc_path c) ->
  0 <= estart E (SA b k) -> estart E (SA b k) + 8 <= 2 ^ 64 ->
  src_ok (mem_denot E m (SG.vc_log c)) (estart E (SA b k)) s -> src_nz segs kn c b k s = true ->
  exists W, NRV.wat segs (mem_denot E m (SG.vc_log c)) (estart E (SA b k)) W /\ W <> 0.
Proof.
  intros kn c b k s HK HS HP A0 A8 Hs H. destruct s as [v|vl vh|]; cbn [src_nz src_ok] in *.
  - exists (u (edenot E v)). split; [exact Hs | exact (val_nz_ok kn _ _ v HK HS HP H)].
  - eexists. split; [exact Hs | exact (w44_nz_ok kn _ _ vl vh HK HS HP H)].
  - destruct (base_nz_ok kn _ _ b k HK HS HP H) as (w & Hw & Hn). exists w. split; [|exact Hn].
    apply Hs. rewrite <- estart_loc by lia. exact Hw.
Qed.

Lemma word_nz_ok : forall kn c b k, know_ok segs E m kn -> SG.gholds GP E m (SG.vc_src c) -> scs_denot segs m E (SG.vc_path c) ->
  log_flat E (SG.vc_log c) -> 0 <= estart E (SA b k) -> estart E (SA b k) + 8 <= 2 ^ 64 ->
  word_nz segs kn c b k = true -> exists W, NRV.wat segs (mem_denot E m (SG.vc_log c)) (estart E (SA b k)) W /\ W <> 0.
Proof.
  intros kn c b k HK HS HP HL A0 A8 H. unfold word_nz in H.
  destruct (walk segs kn (SG.vc_log c) b k) as [cs|] eqn:HW; [|discriminate].
  pose proof (walk_ok _ kn b k cs HK HL HW A0 A8) as EX. apply Exists_exists in EX as ([kn' s] & Hin & Hk & Hs).
  cbn [fst snd] in *. apply (src_nz_ok kn' c b k s Hk HS HP A0 A8 Hs).
  exact (proj1 (forallb_forall _ _) H _ Hin).
Qed.

Lemma smul_pat_ok : forall kn c v cy, know_ok segs E m kn -> SG.gholds GP E m (SG.vc_src c) -> scs_denot segs m E (SG.vc_path c) ->
  smul_pat segs kn c v cy = true -> u (edenot E v) <> 0 \/ u (edenot E cy) <> 0.
Proof.
  intros kn c v cy HK HS HP H. destruct v as [| |op c0 mq| | | | |]; try discriminate. destruct op; try discriminate.
  destruct mq as [| | | |op1 p0 q0| | |]; try discriminate. destruct op1; try discriminate. cbn [smul_pat] in H.
  apply andb_prop in H as [Hc Hm]. unfold mul_ok in Hm.
  assert (NZ : u (edenot E p0) <> 0 /\ u (edenot E q0) <> 0).
  { apply orb_prop in Hm as [Hm|Hm]; apply andb_prop in Hm as [Hr Hk]; pose proof (ST.kimplied_ok segs E m kn _ HK Hk) as K;
      cbn [kentry_ok] in K; pose proof (rvar_nz_ok kn _ _ _ HK HS HP Hr); split; lia. }
  exact (smul_vals c0 p0 q0 cy Hc (proj1 NZ) (proj2 NZ)).
Qed.

Lemma word_nz_cy_ok : forall kn c b k cy, know_ok segs E m kn -> SG.gholds GP E m (SG.vc_src c) ->
  scs_denot segs m E (SG.vc_path c) -> log_flat E (SG.vc_log c) -> 0 <= estart E (SA b k) -> estart E (SA b k) + 8 <= 2 ^ 64 ->
  word_nz_cy segs kn c b k cy = true ->
  (exists W, NRV.wat segs (mem_denot E m (SG.vc_log c)) (estart E (SA b k)) W /\ W <> 0) \/ u (edenot E cy) <> 0.
Proof.
  intros kn c b k cy HK HS HP HL A0 A8 H. unfold word_nz_cy in H.
  destruct (walk segs kn (SG.vc_log c) b k) as [cs|] eqn:HW; [|discriminate].
  pose proof (walk_ok _ kn b k cs HK HL HW A0 A8) as EX. apply Exists_exists in EX as ([kn' s] & Hin & Hk & Hs).
  cbn [fst snd] in *. pose proof (proj1 (forallb_forall _ _) H _ Hin) as Hc. cbn [fst snd] in Hc.
  apply orb_prop in Hc as [Hc|Hc]; [left; exact (src_nz_ok kn' c b k s Hk HS HP A0 A8 Hs Hc)|].
  destruct s as [v| |]; try discriminate. cbn [src_ok] in Hs.
  destruct (smul_pat_ok kn' c v cy Hk HS HP Hc) as [N|N]; [left; exists (u (edenot E v)); split; [exact Hs | exact N] | right; exact N].
Qed.

Lemma know_app1 : forall kn K, know_ok segs E m kn -> kentry_ok segs E m K -> know_ok segs E m (kn ++ [K]).
Proof. intros kn K HK H. unfold know_ok. apply Forall_app. split; [exact HK | constructor; [exact H | constructor]]. Qed.
Lemma know_app2 : forall kn K1 K2, know_ok segs E m kn -> kentry_ok segs E m K1 -> kentry_ok segs E m K2 ->
  know_ok segs E m (kn ++ [K1; K2]).
Proof. intros kn K1 K2 HK H1 H2. unfold know_ok. apply Forall_app. split; [exact HK | repeat constructor; assumption]. Qed.

Lemma tbnd_ok_ok : forall kn x n, know_ok segs E m kn -> tbnd_ok kn x n = true ->
  8 <= u (edenot E x) + 8 * u (edenot E n) < 2 ^ 64.
Proof.
  intros kn x n HK H. unfold tbnd_ok in H.
  destruct (erange kn x) as [[lx hx]|] eqn:Ex; [|discriminate]. destruct (erange kn n) as [[ln hn]|] eqn:En; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (erange_sound segs E m kn x lx hx HK Ex). pose proof (erange_sound segs E m kn n ln hn HK En). lia.
Qed.

Lemma estart_tb : forall x n, 8 <= u (edenot E x) + 8 * u (edenot E n) < 2 ^ 64 ->
  estart E (SA (tb x n) (-8)) = u (edenot E x) + 8 * u (edenot E n) - 8.
Proof. intros x n H. unfold estart. cbn [a_base a_off]. rewrite u_tb by lia. lia. Qed.

Lemma tgt_ok_ok : forall kn c g, know_ok segs E m kn -> SG.gholds GP E m (SG.vc_src c) -> scs_denot segs m E (SG.vc_path c) ->
  log_flat E (SG.vc_log c) -> tgt_ok segs kn c g = true ->
  GP (ST.g_id g) (map (edenot E) (ST.g_args g)) (mem_denot E m (SG.vc_log c)).
Proof.
  intros kn c [id args] HK HS HP HL H. unfold tgt_ok in H. cbn [ST.g_id ST.g_args] in *.
  set (M' := mem_denot E m (SG.vc_log c)).
  assert (TOP : forall x n kn', know_ok segs E m kn' -> 8 <= u (edenot E x) + 8 * u (edenot E n) < 2 ^ 64 ->
                word_nz segs kn' c (tb x n) (-8) = true -> SNU.topnz segs M' (edenot E x) (edenot E n)).
  { intros x n kn' HK' Hb Hw. destruct (word_nz_ok kn' c (tb x n) (-8) HK' HS HP HL ltac:(rewrite estart_tb by lia; lia)
                                        ltac:(rewrite estart_tb by lia; lia) Hw) as (W & HW & HN).
    rewrite estart_tb in HW by lia. exact (NRV.wat_topnz segs M' _ _ W HW HN). }
  do 7 (destruct id as [|id]; [discriminate|]).
  destruct id as [|id].
  { destruct args as [|x [|n [|? ?]]]; try discriminate. apply andb_prop in H as [Hb H]. pose proof (tbnd_ok_ok kn x n HK Hb) as B.
    cbn [map SNU.snu_gp]. split; [exact B|]. apply orb_prop in H as [H|H].
    - left. pose proof (ST.kimplied_ok segs E m kn _ HK H) as K. cbn [kentry_ok] in K. lia.
    - destruct (Z.eq_dec (u (edenot E n)) 0) as [Z0|Z0]; [left; exact Z0|right].
      apply (TOP x n (kn ++ [KRange n 1 MX])); [apply know_app1; [exact HK | cbn [kentry_ok]; pose proof (u_rng (edenot E n)); unfold MX; lia] | exact B | exact H]. }
  destruct id as [|id].
  { destruct args as [|x [|n [|? ?]]]; try discriminate. apply andb_prop in H as [Hb H]. pose proof (tbnd_ok_ok kn x n HK Hb) as B.
    cbn [map SNU.snu_gp]. split; [exact B|]. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    - left. pose proof (ST.kimplied_ok segs E m kn _ HK H) as K. cbn [kentry_ok] in K. lia.
    - right; left. pose proof (ST.kimplied_ok segs E m kn _ HK H) as K. cbn [kentry_ok] in K. lia.
    - destruct (Z_lt_le_dec 61 (u (edenot E n))) as [G|G]; [left; lia|].
      destruct (Z.eq_dec (u (edenot E n)) 0) as [Z0|Z0]; [right; left; exact Z0|right; right].
      apply (TOP x n (kn ++ [KRange n 1 61])); [apply know_app1; [exact HK | cbn [kentry_ok]; pose proof (u_rng (edenot E n)); lia] | exact B | exact H]. }
  destruct id as [|id].
  { destruct args as [|x [|n [|cy [|? ?]]]]; try discriminate. apply andb_prop in H as [Hb H]. pose proof (tbnd_ok_ok kn x n HK Hb) as B.
    cbn [map SNU.snu_gp]. split; [exact B|].
    apply orb_prop in H as [H|H5]; [apply orb_prop in H as [H|H4]; [apply orb_prop in H as [H|H3]; [apply orb_prop in H as [H1|H2]|]|]|].
    - left. pose proof (ST.kimplied_ok segs E m kn _ HK H1) as K. cbn [kentry_ok] in K. lia.
    - right; left. pose proof (ST.kimplied_ok segs E m kn _ HK H2) as K. cbn [kentry_ok] in K. lia.
    - right; right; left. pose proof (ST.kimplied_ok segs E m kn _ HK H3) as K. cbn [kentry_ok] in K. lia.
    - destruct (Z_lt_le_dec 61 (u (edenot E n))) as [G|G]; [left; lia|].
      destruct (Z.eq_dec (u (edenot E cy)) 0) as [C0|C0]; [|right; left; exact C0].
      destruct (Z.eq_dec (u (edenot E n)) 0) as [Z0|Z0]; [right; right; left; exact Z0|right; right; right].
      apply (TOP x n (kn ++ [KRange n 1 61; KRange cy 0 0])); [|exact B | exact H4].
      apply know_app2; [exact HK | cbn [kentry_ok]; pose proof (u_rng (edenot E n)); lia | cbn [kentry_ok]; lia].
    - destruct (Z_lt_le_dec 61 (u (edenot E n))) as [G|G]; [left; lia|].
      destruct (Z.eq_dec (u (edenot E n)) 0) as [Z0|Z0]; [right; right; left; exact Z0|].
      assert (HK' : know_ok segs E m (kn ++ [KRange n 1 61])) by
        (apply know_app1; [exact HK | cbn [kentry_ok]; pose proof (u_rng (edenot E n)); lia]).
      destruct (word_nz_cy_ok _ c (tb x n) (-8) cy HK' HS HP HL ltac:(rewrite estart_tb by lia; lia)
                  ltac:(rewrite estart_tb by lia; lia) H5) as [(W & HW & HN)|C].
      + right; right; right. rewrite estart_tb in HW by lia. exact (NRV.wat_topnz segs M' _ _ W HW HN).
      + right; left. exact C. }
  destruct id as [|id]; [|discriminate].
  { destruct args as [|a [|? ?]]; try discriminate. apply andb_prop in H as [Ha H].
    pose proof (ST.kimplied_ok segs E m kn _ HK Ha) as K. cbn [kentry_ok] in K. pose proof (u_rng (edenot E a)).
    assert (Es : estart E (SA a (-8)) = u (edenot E a) - 8) by (unfold estart; cbn [a_base a_off]; lia).
    destruct (word_nz_ok kn c a (-8) HK HS HP HL ltac:(rewrite Es; lia) ltac:(rewrite Es; lia) H) as (W & HW & HN).
    rewrite Es in HW. cbn [map SNU.snu_gp]. exact (NRV.wat_topw segs M' (edenot E a) W ltac:(lia) HW HN). }
Qed.

Lemma fact_ok_ok : forall kn c K M', know_ok segs E m kn -> SG.gholds GP E m (SG.vc_src c) -> scs_denot segs m E (SG.vc_path c) ->
  fact_ok segs kn c K = true -> kentry_ok segs E M' K.
Proof.
  intros kn c K M' HK HS HP H. unfold fact_ok in H. destruct K as [ | | | | |e lo hi| | | | ]; try discriminate.
  - pose proof (ST.kimplied_ok segs E m kn _ HK H) as K. cbn [kentry_ok] in *. exact K.
  - apply orb_prop in H as [H|H].
    + pose proof (ST.kimplied_ok segs E m kn _ HK H) as K. cbn [kentry_ok] in *. exact K.
    + destruct e; try discriminate. apply andb_prop in H as [H Hr]. apply andb_prop in H as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof (rd_nz_ok kn _ _ n HK HS HP Hr) as N.
      cbn [kentry_ok edenot]. pose proof (u_rng (ev E n)). unfold MX in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma psubst_ok : forall kn c ts, know_ok segs E m kn -> lden E (psubst kn (c, ts)) = c + tden E ts.
Proof.
  intros kn c ts HK. unfold psubst. cbn [fst snd]. induction ts as [|[k a] r IH]; cbn [fold_right tden]; [unfold lden; cbn; lia|].
  destruct (fold_right _ (c, []) r) as [c' ts'] eqn:HF. unfold lden in IH |- *. cbn [fst snd] in *.
  destruct (erange kn a) as [[lo hi]|] eqn:Er.
  - pose proof (erange_sound segs E m kn a lo hi HK Er) as R.
    destruct (Z.eqb lo hi) eqn:Eq; cbn [fst snd tden]; unfold uE in *.
    + apply Z.eqb_eq in Eq. subst hi. assert (u (edenot E a) = lo) by lia. lia.
    + lia.
  - cbn [fst snd tden]. unfold uE in *. lia.
Qed.

Lemma pair_contra_ok : forall kn K1 K2, know_ok segs E m kn -> kentry_ok segs E m K1 -> kentry_ok segs E m K2 ->
  pair_contra kn K1 K2 = true -> False.
Proof.
  intros kn K1 K2 HK H1 H2 H. unfold pair_contra in H.
  destruct K1 as [ | | | | |e1 l1 h1| | | | ]; try discriminate. destruct K2 as [ | | | | |e2 l2 h2| | | | ]; try discriminate.
  destruct (fact_nowrap kn e1 h1 && fact_nowrap kn e2 h2)%bool eqn:Hn; [|discriminate]. apply andb_prop in Hn as [N1 N2].
  cbn [kentry_ok] in H1, H2.
  pose proof (fact_nowrap_sound segs E m kn e1 l1 h1 HK N1 H1) as U1. pose proof (fact_nowrap_sound segs E m kn e2 l2 h2 HK N2 H2) as U2.
  destruct (lin_of e1) as [c1 t1] eqn:L1. destruct (lin_of e2) as [c2 t2] eqn:L2. cbn [fst snd] in U1, U2.
  pose proof (psubst_ok kn c1 t1 HK) as P1. pose proof (psubst_ok kn c2 t2 HK) as P2.
  pose proof (ladd_sound E (psubst kn (c1, t1)) (psubst kn (c2, t2))) as [q Hq].
  destruct (ladd (psubst kn (c1, t1)) (psubst kn (c2, t2))) as [c ts] eqn:HA. destruct ts; [|discriminate].
  unfold lden in Hq. cbn [fst snd tden] in Hq. apply Z.ltb_lt in H.
  unfold lden in P1, P2. rewrite P1, P2 in Hq.
  assert (S1 : l1 + l2 <= c + 0 - q * 2 ^ 64 <= h1 + h2) by lia.
  assert (T1 : - q <= (h1 + h2 - c) / 2 ^ 64) by (apply Z.div_le_lower_bound; lia).
  assert (T2 : (l1 + l2 - c + 2 ^ 64 - 1) / 2 ^ 64 <= - q) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma infeasible_ok : forall kn, know_ok segs E m kn -> infeasible kn = true -> False.
Proof.
  intros kn HK H. unfold infeasible in H. apply existsb_exists in H as (K1 & I1 & H). apply existsb_exists in H as (K2 & I2 & H).
  exact (pair_contra_ok kn K1 K2 HK (proj1 (Forall_forall _ _) HK _ I1) (proj1 (Forall_forall _ _) HK _ I2) H).
Qed.

End S.

(* [comment removed for export] *)
Theorem nrc_ok_sound : forall segs c, nrc_ok segs c = true -> SG.vc_holds segs (SNU.snu_gp segs) c.
Proof.
  intros segs c H E m HK HP HL HS. unfold nrc_ok in H.
  pose proof (pkn_ok segs E m (SG.vc_path c) (SG.vc_kn c) HK HP) as K0.
  set (kn0 := pkn (SG.vc_kn c) (SG.vc_path c)) in *.
  destruct (SL.al_tight kn0 kn0) as [l|] eqn:HT.
  - destruct (SL.al_tight_ok segs E m kn0 kn0 K0 K0) as [A1 _]. pose proof (A1 l HT) as Kl.
    assert (K : know_ok segs E m (l ++ kn0)) by (unfold know_ok; apply Forall_app; split; assumption).
    apply orb_prop in H as [H|H]; [exfalso; exact (infeasible_ok segs E m _ K H)|].
    apply andb_prop in H as [Ht Hf]. split.
    + unfold SG.gholds. apply Forall_forall. intros g Hg.
      exact (tgt_ok_ok segs E m _ c g K HS HP HL (proj1 (forallb_forall _ _) Ht g Hg)).
    + unfold know_ok. apply Forall_forall. intros K' HK'.
      exact (fact_ok_ok segs E m _ c K' _ K HS HP (proj1 (forallb_forall _ _) Hf K' HK')).
  - destruct (SL.al_tight_ok segs E m kn0 kn0 K0 K0) as [_ A2]. exfalso. exact (A2 HT).
Qed.
End NRC.
