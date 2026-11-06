(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3 AxSymExec3B AxSymExec3C.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AX2L.
Import AX2. Import AX2B. Import AX2C.

(* [comment removed for export] *)
Fixpoint log_lookupPG (tst : sidetest) (bc : bctx) (osp : option sprep) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      let zw := zofn w in
      match rel_lit rb rk zn kb kk zw with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupPG tst bc osp rest rb rk n zn sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let sp := match osp with Some sp => sp | None => fst (mk_sprep3G tst bc rb rk (ELit zn)) end in
          if (if (if Z.ltb zn two64 then Z.ltb zw two64 else false)
              then ranges_apart_pB bc sp rb rk (ELit zn) kb kk (ELit zw)
              else ranges_apartB bc rb rk zn kb kk zw)
          then log_lookupPG tst bc (Some sp) rest rb rk n zn sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupPG tst bc (Some sp) rest rb rk n zn sx (tl hints)
                   (SCDisj (SA rb rk) (ELit zn) (SA kb kk) (ELit zw) :: acc)
          end
      end
  end.
Lemma log_lookupPG_B : forall bc log rb rk n zn sx hints acc osp,
  log_lookupPG (side_testB bc) bc osp log rb rk n zn sx hints acc = log_lookupPZ bc osp log rb rk n zn sx hints acc.
Proof.
  intros bc log rb rk n zn sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc osp; [reflexivity|].
  cbn [log_lookupPG log_lookupPZ]. cbv zeta. rewrite mk_sprep3G_B, mk_sprep3B_fst.
  destruct (rel_lit rb rk zn kb kk (zofn w)); try reflexivity; [apply IH|].
  destruct (if (if Z.ltb zn two64 then Z.ltb (zofn w) two64 else false) then _ else _); [apply IH|].
  destruct hints as [|[|] hs]; [apply IH | apply IH | reflexivity].
Qed.

(* [comment removed for export] *)
Definition num_apart (r1 r2 : option (Z * Z)) (k1 m1 k2 m2 : Z) : bool :=
  match r1, r2 with
  | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
  | _, _ => false
  end.
Definition rest_apart (bc : bctx) (sp : sprep) (b1 : expr) (k1 m1 : Z) (b2 : expr) (k2 m2 : Z) : bool :=
  if in_sidesB bc (sp_D sp) b2 k2 m2 then true else lin_apartB bc b1 k1 m1 b2 k2 m2.
Lemma ranges_apart_pB_split : forall bc sp b1 k1 z1 b2 k2 z2,
  ranges_apart_pB bc sp b1 k1 (ELit z1) b2 k2 (ELit z2)
  = if num_apart (sp_rng sp) (base_rangeB bc b2) k1 (zlit64 z1) k2 (zlit64 z2) then true
    else rest_apart bc sp b1 k1 (zlit64 z1) b2 k2 (zlit64 z2).
Proof.
  intros. unfold ranges_apart_pB, num_apart, rest_apart. cbv zeta.
  destruct (sp_rng sp) as [[lo1 hi1]|]; [|reflexivity]. destruct (base_rangeB bc b2) as [[lo2 hi2]|]; reflexivity.
Qed.
Lemma mk_sprep3G_rng : forall tst bc b1 k1 n1, sp_rng (fst (mk_sprep3G tst bc b1 k1 n1)) = base_rangeB bc b1.
Proof. intros. unfold mk_sprep3G. destruct (disj_sides3G tst (bc_fk bc) b1 k1 n1 []) as [[[d dx] mo] mk]. reflexivity. Qed.

Fixpoint log_lookupPL (tst : sidetest) (bc : bctx) (orng : option (option (Z * Z))) (osp : option sprep) (log : list sentry)
         (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      let zw := zofn w in
      match rel_lit rb rk zn kb kk zw with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupPL tst bc orng osp rest rb rk n zn sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if (if Z.ltb zn two64 then Z.ltb zw two64 else false) then
            let rng := match orng with Some r => r | None => base_rangeB bc rb end in
            if num_apart rng (base_rangeB bc kb) rk (zlit64 zn) kk (zlit64 zw)
            then log_lookupPL tst bc (Some rng) osp rest rb rk n zn sx hints acc
            else
              let sp := match osp with Some sp => sp | None => fst (mk_sprep3G tst bc rb rk (ELit zn)) end in
              if rest_apart bc sp rb rk (zlit64 zn) kb kk (zlit64 zw)
              then log_lookupPL tst bc (Some rng) (Some sp) rest rb rk n zn sx hints acc
              else
              match hints with
              | false :: _ => LStuck
              | _ => log_lookupPL tst bc (Some rng) (Some sp) rest rb rk n zn sx (tl hints)
                       (SCDisj (SA rb rk) (ELit zn) (SA kb kk) (ELit zw) :: acc)
              end
          else
            if ranges_apartB bc rb rk zn kb kk zw
            then log_lookupPL tst bc orng osp rest rb rk n zn sx hints acc
            else
            match hints with
            | false :: _ => LStuck
            | _ => log_lookupPL tst bc orng osp rest rb rk n zn sx (tl hints)
                     (SCDisj (SA rb rk) (ELit zn) (SA kb kk) (ELit zw) :: acc)
            end
      end
  end.
(* [comment removed for export] *)
Lemma log_lookupPG_osp : forall tst bc log rb rk n zn sx hints acc,
  log_lookupPG tst bc (Some (fst (mk_sprep3G tst bc rb rk (ELit zn)))) log rb rk n zn sx hints acc
  = log_lookupPG tst bc None log rb rk n zn sx hints acc.
Proof.
  intros tst bc log rb rk n zn sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc; [reflexivity|].
  cbn [log_lookupPG]. cbv zeta. destruct (rel_lit rb rk zn kb kk (zofn w)); try reflexivity. apply IH.
Qed.
Lemma log_lookupPL_eq : forall tst bc log rb rk n zn sx hints acc orng osp,
  (orng = None \/ orng = Some (base_rangeB bc rb)) ->
  (osp = None \/ osp = Some (fst (mk_sprep3G tst bc rb rk (ELit zn)))) ->
  log_lookupPL tst bc orng osp log rb rk n zn sx hints acc = log_lookupPG tst bc None log rb rk n zn sx hints acc.
Proof.
  intros tst bc log rb rk n zn sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc orng osp HR HS; [reflexivity|].
  cbn [log_lookupPL log_lookupPG]. cbv zeta.
  destruct (rel_lit rb rk zn kb kk (zofn w)); try reflexivity; [apply IH; assumption|].
  assert (ER : match orng with Some r => r | None => base_rangeB bc rb end = base_rangeB bc rb) by (destruct HR as [->| ->]; reflexivity).
  assert (ES : match osp with Some sp => sp | None => fst (mk_sprep3G tst bc rb rk (ELit zn)) end = fst (mk_sprep3G tst bc rb rk (ELit zn)))
    by (destruct HS as [->| ->]; reflexivity).
  destruct (if Z.ltb zn two64 then Z.ltb (zofn w) two64 else false).
  - rewrite ER, ES, ranges_apart_pB_split, mk_sprep3G_rng.
    destruct (num_apart (base_rangeB bc rb) (base_rangeB bc kb) rk (zlit64 zn) kk (zlit64 (zofn w))).
    + rewrite log_lookupPG_osp. apply IH; [right; reflexivity | exact HS].
    + destruct (rest_apart bc (fst (mk_sprep3G tst bc rb rk (ELit zn))) rb rk (zlit64 zn) kb kk (zlit64 (zofn w))).
      * rewrite log_lookupPG_osp. apply IH; right; reflexivity.
      * destruct hints as [|[|] hs]; try reflexivity; rewrite log_lookupPG_osp; apply IH; right; reflexivity.
  - destruct (ranges_apartB bc rb rk zn kb kk (zofn w)).
    + rewrite log_lookupPG_osp. apply IH; assumption.
    + destruct hints as [|[|] hs]; try reflexivity; rewrite log_lookupPG_osp; apply IH; assumption.
Qed.

(* [comment removed for export] *)
Definition ekey (e : sentry) : option positive := match e with SE (SA _ kk) w _ => fgkey kk w end.
Definition ebase (e : sentry) : expr := match e with SE a _ _ => a_base a end.
Definition other_key (ok : option positive) (g : positive) : bool :=
  match ok with Some g' => negb (Pos.eqb g' g) | None => false end.
(* [comment removed for export] *)
Definition dropf (b : expr) (g : positive) (e : sentry) : bool :=
  if other_key (ekey e) g then expr_eqb (ebase e) b else false.
Definition keepf (b : expr) (g : positive) (e : sentry) : bool := negb (dropf b g e).

Lemma fgkey_pos : forall k w g, fgkey k w = Some g -> (0 < Z.of_nat w)%Z.
Proof. intros k w g H. destruct w; [discriminate | lia]. Qed.
Lemma fgkey_sub : forall k w g i, fgkey k w = Some g -> (0 <= i < Z.of_nat w)%Z -> fgkey (k + i) 1 = Some g.
Proof.
  intros k w g i H Hi. unfold fgkey in *. destruct w as [|w0]; [discriminate|]. cbv zeta in *. rewrite zofn_eq in *.
  destruct (Z.eqb_spec (Z.shiftr k FGS) (Z.shiftr (k + Z.of_nat (S w0) - 1) FGS)) as [E|]; [|discriminate]. injection H as <-.
  change (Z.of_nat 1) with 1%Z. replace (k + i + 1 - 1)%Z with (k + i)%Z by lia. rewrite Z.eqb_refl. f_equal. f_equal.
  rewrite !Z.shiftr_div_pow2 in * by (unfold FGS; lia).
  pose proof (Z.div_le_mono k (k + i) (2 ^ FGS) ltac:(unfold FGS; lia) ltac:(lia)).
  pose proof (Z.div_le_mono (k + i) (k + Z.of_nat (S w0) - 1) (2 ^ FGS) ltac:(unfold FGS; lia) ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma rel_lit_drop : forall rb rk n g kb kk w g',
  fgkey rk n = Some g -> fgkey kk w = Some g' -> g' <> g -> expr_eqb kb rb = true ->
  rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) = RDisjoint.
Proof.
  intros rb rk n g kb kk w g' Hr Hk NE EB. apply p_expr_eqb_eq in EB. subst kb.
  pose proof (fgkey_apart kk w rk n g' g Hk Hr NE) as KP. rewrite kword_keepF_eq in KP.
  pose proof (fgkey_pos _ _ _ Hr). pose proof (fgkey_pos _ _ _ Hk).
  rewrite rel_lit_ref_eq. unfold rel_lit_ref. rewrite p_expr_eqb_refl.
  apply orb_true_iff in KP. rewrite !Z.leb_le in KP.
  destruct (Z.leb_spec kk rk); destruct (Z.leb_spec (rk + Z.of_nat n) (kk + Z.of_nat w)); cbn [andb];
    destruct (Z.leb_spec (rk + Z.of_nat n) kk); destruct (Z.leb_spec (kk + Z.of_nat w) rk); cbn [orb]; try reflexivity; lia.
Qed.

Lemma keepf_cons : forall b g e l, keepf b g e = true -> List.filter (keepf b g) (e :: l) = e :: List.filter (keepf b g) l.
Proof.
  intros b g e l H. change (List.filter (keepf b g) (e :: l)) with (if keepf b g e then e :: List.filter (keepf b g) l else List.filter (keepf b g) l).
  rewrite H. reflexivity.
Qed.
Lemma dropf_cons : forall b g e l, keepf b g e = false -> List.filter (keepf b g) (e :: l) = List.filter (keepf b g) l.
Proof.
  intros b g e l H. change (List.filter (keepf b g) (e :: l)) with (if keepf b g e then e :: List.filter (keepf b g) l else List.filter (keepf b g) l).
  rewrite H. reflexivity.
Qed.
Lemma dropf_inv : forall b g kb kk w v, keepf b g (SE (SA kb kk) w v) = false ->
  exists g', fgkey kk w = Some g' /\ g' <> g /\ expr_eqb kb b = true.
Proof.
  intros b g kb kk w v H. unfold keepf, dropf in H. apply negb_false_iff in H. cbn [ekey ebase a_base] in H.
  destruct (fgkey kk w) as [g'|]; cbn [other_key] in H; [|discriminate].
  destruct (Pos.eqb_spec g' g) as [|NE]; cbn [negb] in H; [discriminate|]. exists g'. auto.
Qed.

Lemma log_byte_lit_keep : forall b g rk', fgkey rk' 1 = Some g ->
  forall l, log_byte_lit (List.filter (keepf b g) l) b rk' = log_byte_lit l b rk'.
Proof.
  intros b g rk' Hk l. induction l as [|[[kb kk] w v] rest IH]; [reflexivity|].
  destruct (keepf b g (SE (SA kb kk) w v)) eqn:KF.
  - rewrite (keepf_cons _ _ _ _ KF). cbn [log_byte_lit]. destruct (rel_lit b rk' 1 kb kk (Z.of_nat w)); try reflexivity. exact IH.
  - rewrite (dropf_cons _ _ _ _ KF). destruct (dropf_inv _ _ _ _ _ _ KF) as (g' & K1 & NE & EB).
    cbn [log_byte_lit]. change 1%Z with (Z.of_nat 1). rewrite (rel_lit_drop b rk' 1 g kb kk w g' Hk K1 NE EB). exact IH.
Qed.
Lemma log_bytes_lit_keep : forall b g l n rk',
  (forall j, (0 <= j < Z.of_nat n)%Z -> fgkey (rk' + j) 1 = Some g) ->
  log_bytes_lit (List.filter (keepf b g) l) b rk' n = log_bytes_lit l b rk' n.
Proof.
  intros b g l n. induction n as [|n' IH]; intros rk' H; [reflexivity|].
  cbn [log_bytes_lit]. rewrite (log_byte_lit_keep b g rk').
  2:{ specialize (H 0%Z ltac:(lia)). rewrite Z.add_0_r in H. exact H. }
  rewrite IH; [reflexivity|]. intros j Hj. replace (rk' + 1 + j)%Z with (rk' + (1 + j))%Z by lia. apply H. lia.
Qed.
(* [comment removed for export] *)
Lemma log_lookupPG_keep : forall tst bc rb rk n g sx, fgkey rk n = Some g ->
  forall l osp hints acc,
  log_lookupPG tst bc osp (List.filter (keepf rb g) l) rb rk n (Z.of_nat n) sx hints acc
  = log_lookupPG tst bc osp l rb rk n (Z.of_nat n) sx hints acc.
Proof.
  intros tst bc rb rk n g sx Hk l. induction l as [|[[kb kk] w v] rest IH]; intros osp hints acc; [reflexivity|].
  destruct (keepf rb g (SE (SA kb kk) w v)) eqn:KF.
  - rewrite (keepf_cons _ _ _ _ KF). cbn [log_lookupPG]. cbv zeta.
    destruct (rel_lit rb rk (Z.of_nat n) kb kk (zofn w)); try reflexivity; [apply IH | |].
    + rewrite <- (keepf_cons _ _ _ _ KF). rewrite (log_bytes_lit_keep rb g (SE (SA kb kk) w v :: rest) n rk); [reflexivity|].
      intros j Hj. exact (fgkey_sub rk n g j Hk Hj).
    + destruct (if (if Z.ltb (Z.of_nat n) two64 then Z.ltb (zofn w) two64 else false) then _ else _); [apply IH|].
      destruct hints as [|[|] hs]; [apply IH | apply IH | reflexivity].
  - rewrite (dropf_cons _ _ _ _ KF). destruct (dropf_inv _ _ _ _ _ _ KF) as (g' & K1 & NE & EB).
    cbn [log_lookupPG]. cbv zeta. rewrite zofn_eq, (rel_lit_drop rb rk n g kb kk w g' Hk K1 NE EB). apply IH.
Qed.

(* [comment removed for export] *)
Definition klog : Type := list (sentry * option positive).
Definition subs : Type := list (expr * ptree (list sentry)).
Record lidx : Type := LX { lx_n : positive; lx_kl : klog; lx_sub : subs }.
Definition lx_empty : lidx := LX xH [] [].

Fixpoint mk_sub (b : expr) (g : positive) (kl : klog) : list sentry :=
  match kl with
  | [] => []
  | (e, ok) :: r => if (if other_key ok g then expr_eqb (ebase e) b else false) then mk_sub b g r else e :: mk_sub b g r
  end.
Definition KLOK (kl : klog) (log : list sentry) : Prop := map fst kl = log /\ Forall (fun p => snd p = ekey (fst p)) kl.
Lemma mk_sub_filter : forall b g kl log, KLOK kl log -> mk_sub b g kl = List.filter (keepf b g) log.
Proof.
  intros b g kl. induction kl as [|[e ok] r IH]; intros log [HM HF]; cbn [map fst] in HM; subst log; [reflexivity|].
  inversion HF as [|? ? HK HR]; subst. cbn [fst snd] in HK. subst ok. cbn [mk_sub map fst List.filter]. unfold keepf at 1, dropf.
  rewrite (IH (map fst r) (conj eq_refl HR)).
  destruct (if other_key (ekey e) g then expr_eqb (ebase e) b else false); reflexivity.
Qed.

Fixpoint sub_find (l : subs) (b : expr) : option (ptree (list sentry)) :=
  match l with
  | [] => None
  | (b', t) :: r => if expr_eqb b b' then Some t else sub_find r b
  end.
Fixpoint sub_set (l : subs) (b : expr) (t : ptree (list sentry)) : subs :=
  match l with
  | [] => [(b, t)]
  | (b', t') :: r => if expr_eqb b b' then (b', t) :: r else (b', t') :: sub_set r b t
  end.
Definition TOK (b : expr) (t : ptree (list sentry)) (log : list sentry) : Prop :=
  forall g sl, pt_get t g = Some sl -> sl = List.filter (keepf b g) log.
Definition SUBOK (l : subs) (log : list sentry) : Prop := Forall (fun p => TOK (fst p) (snd p) log) l.
Lemma sub_find_ok : forall l log b t, SUBOK l log -> sub_find l b = Some t -> TOK b t log.
Proof.
  induction l as [|[b' t'] r IH]; intros log b t H F; cbn [sub_find] in F; [discriminate|].
  inversion H as [|? ? H1 H2]; subst. destruct (expr_eqb b b') eqn:E.
  - injection F as <-. apply p_expr_eqb_eq in E. subst b'. exact H1.
  - exact (IH log b t H2 F).
Qed.
Lemma sub_set_ok : forall l log b t, SUBOK l log -> TOK b t log -> SUBOK (sub_set l b t) log.
Proof.
  induction l as [|[b' t'] r IH]; intros log b t H HT; cbn [sub_set].
  - constructor; [exact HT | constructor].
  - inversion H as [|? ? H1 H2]; subst. destruct (expr_eqb b b') eqn:E.
    + apply p_expr_eqb_eq in E. subst b'. constructor; [exact HT | exact H2].
    + constructor; [exact H1 | exact (IH log b t H2 HT)].
Qed.
Lemma TOK_leaf : forall b log, TOK b PTLeaf log.
Proof. intros b log g sl H. rewrite pt_get_leaf in H. discriminate. Qed.

(* [comment removed for export] *)
Definition tree_add (e : sentry) (k : option positive) (b : expr) (t : ptree (list sentry)) : ptree (list sentry) :=
  if expr_eqb (ebase e) b then
    match k with
    | Some g1 => match pt_get t g1 with Some sl => pt_set g1 (e :: sl) t | None => t end
    | None => pt_map (cons e) t
    end
  else pt_map (cons e) t.
Definition sub_add (e : sentry) (k : option positive) (l : subs) : subs := map (fun p => (fst p, tree_add e k (fst p) (snd p))) l.
Definition lx_add (lx : lidx) (e : sentry) : lidx :=
  let k := ekey e in LX (Pos.succ (lx_n lx)) ((e, k) :: lx_kl lx) (sub_add e k (lx_sub lx)).

Lemma tree_add_ok : forall e b t log, TOK b t log -> TOK b (tree_add e (ekey e) b t) (e :: log).
Proof.
  intros e b t log H g sl G. unfold tree_add in G.
  assert (KEEP : forall sl0, pt_get t g = Some sl0 -> keepf b g e = true -> e :: sl0 = List.filter (keepf b g) (e :: log)).
  { intros sl0 G0 KF. rewrite (keepf_cons _ _ _ _ KF), <- (H g sl0 G0). reflexivity. }
  destruct (expr_eqb (ebase e) b) eqn:EB.
  - destruct (ekey e) as [g1|] eqn:EK.
    + destruct (pt_get t g1) as [sl1|] eqn:G1.
      * destruct (Pos.eq_dec g g1) as [->|NE].
        -- rewrite pt_gss in G. injection G as <-. apply (KEEP sl1 G1).
           unfold keepf, dropf. rewrite EK. cbn [other_key]. rewrite Pos.eqb_refl. reflexivity.
        -- rewrite pt_gso in G by exact NE. rewrite (H g sl G). symmetry. apply dropf_cons.
           unfold keepf, dropf. rewrite EK, EB. cbn [other_key]. destruct (Pos.eqb_spec g1 g); [congruence | reflexivity].
      * destruct (Pos.eq_dec g g1) as [->|NE]; [congruence|].
        rewrite (H g sl G). symmetry. apply dropf_cons.
        unfold keepf, dropf. rewrite EK, EB. cbn [other_key]. destruct (Pos.eqb_spec g1 g); [congruence | reflexivity].
    + rewrite pt_get_map in G. destruct (pt_get t g) as [sl0|] eqn:G0; [|discriminate]. cbn in G. injection G as <-.
      apply (KEEP sl0 eq_refl). unfold keepf, dropf. rewrite EK. reflexivity.
  - rewrite pt_get_map in G. destruct (pt_get t g) as [sl0|] eqn:G0; [|discriminate]. cbn in G. injection G as <-.
    apply (KEEP sl0 eq_refl). unfold keepf, dropf. rewrite EB. destruct (other_key (ekey e) g); reflexivity.
Qed.

Definition LXOK (lx : lidx) (log : list sentry) : Prop := KLOK (lx_kl lx) log /\ SUBOK (lx_sub lx) log.
Lemma LXOK_empty : LXOK lx_empty [].
Proof. split; [split; [reflexivity | constructor] | constructor]. Qed.
Lemma lx_add_ok : forall lx log e, LXOK lx log -> LXOK (lx_add lx e) (e :: log).
Proof.
  intros lx log e [[HM HF] HS]. unfold lx_add. cbv zeta. split; cbn [lx_kl lx_sub].
  - split; [cbn [map fst]; rewrite HM; reflexivity | constructor; [reflexivity | exact HF]].
  - unfold SUBOK, sub_add. apply Forall_forall. intros p Hp. apply in_map_iff in Hp. destruct Hp as ([b t] & <- & Hin).
    cbn [fst snd]. apply tree_add_ok. exact (proj1 (Forall_forall _ _) HS (b, t) Hin).
Qed.

(* [comment removed for export] *)
Definition LX_MIN : positive := 12%positive.
Definition lookupL (tst : sidetest) (bc : bctx) (lx : lidx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
           (hints : list bool) (acc : list sidecond) : lres * lidx :=
  if Pos.ltb (lx_n lx) LX_MIN then (log_lookupPL tst bc None None log rb rk n (Z.of_nat n) sx hints acc, lx) else
  match fgkey rk n with
  | None => (log_lookupPL tst bc None None log rb rk n (Z.of_nat n) sx hints acc, lx)
  | Some g =>
      let t := match sub_find (lx_sub lx) rb with Some t => t | None => PTLeaf end in
      match pt_get t g with
      | Some sl => (log_lookupPL tst bc None None sl rb rk n (Z.of_nat n) sx hints acc, lx)
      | None => let sl := mk_sub rb g (lx_kl lx) in
                (log_lookupPL tst bc None None sl rb rk n (Z.of_nat n) sx hints acc,
                 LX (lx_n lx) (lx_kl lx) (sub_set (lx_sub lx) rb (pt_set g sl t)))
      end
  end.
Lemma lookupL_spec : forall tst bc lx log rb rk n sx hints acc, LXOK lx log ->
  fst (lookupL tst bc lx log rb rk n sx hints acc) = log_lookupPG tst bc None log rb rk n (Z.of_nat n) sx hints acc
  /\ LXOK (snd (lookupL tst bc lx log rb rk n sx hints acc)) log.
Proof.
  intros tst bc lx log rb rk n sx hints acc HL. pose proof HL as [HK HS]. unfold lookupL.
  assert (PL : forall l, log_lookupPL tst bc None None l rb rk n (Z.of_nat n) sx hints acc
                         = log_lookupPG tst bc None l rb rk n (Z.of_nat n) sx hints acc)
    by (intros l; apply log_lookupPL_eq; left; reflexivity).
  destruct (Pos.ltb (lx_n lx) LX_MIN); [split; [apply PL | exact HL]|].
  destruct (fgkey rk n) as [g|] eqn:FK; [|split; [apply PL | exact HL]]. cbv zeta.
  assert (HT : TOK rb (match sub_find (lx_sub lx) rb with Some t => t | None => PTLeaf end) log).
  { destruct (sub_find (lx_sub lx) rb) as [t|] eqn:SF; [exact (sub_find_ok _ _ _ _ HS SF) | apply TOK_leaf]. }
  set (t := match sub_find (lx_sub lx) rb with Some t => t | None => PTLeaf end) in *.
  destruct (pt_get t g) as [sl|] eqn:G; cbn [fst snd]; rewrite PL.
  - split; [|exact HL]. rewrite (HT g sl G). apply log_lookupPG_keep. exact FK.
  - rewrite (mk_sub_filter rb g _ log HK). split; [apply log_lookupPG_keep; exact FK|].
    split; [exact HK|]. cbn [lx_sub]. apply sub_set_ok; [exact HS|].
    intros g0 sl0 G0. destruct (Pos.eq_dec g0 g) as [->|NE].
    + rewrite pt_gss in G0. injection G0 as <-. reflexivity.
    + rewrite pt_gso in G0 by exact NE. exact (HT g0 sl0 G0).
Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Definition rres : Type := option (expr * list sidecond * scripts * nat).
(* [comment removed for export] *)
Definition sym_read_k (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts) (a : saddr) (n : nat) (sx' : bool) (r : lres) : rres :=
  match r with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Lemma sym_readBI_k : forall ss bc kx scr a n sx',
  sym_readBI segs ss bc kx scr a n sx'
  = sym_read_k ss bc kx scr a n sx' (log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []).
Proof. reflexivity. Qed.
Definition sym_readLI (tst : sidetest) (ss : sym_state) (bc : bctx) (kx : kix) (lx : lidx) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool) : rres * lidx :=
  let '(r, lx') := lookupL tst bc lx (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] in
  (sym_read_k ss bc kx scr a n sx' r, lx').

(* [comment removed for export] *)
Definition log_head_add (lx : lidx) (r : stepres) : lidx :=
  match r with
  | SOk ss' _ _ => match s_log ss' with e :: _ => lx_add lx e | [] => lx end
  | SStop => lx
  end.
Definition sym_stepLI (tst : sidetest) (bc : bctx) (kx : kix) (i : instr) (ss : sym_state) (scr : scripts) (lx : lidx) : stepres * lidx :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      let '(r, lx') := sym_readLI tst ss bc kx lx scr a n sx' in
      (match r with
       | None => SStop
       | Some (v, scs, scr', nx') =>
           SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                    (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
       end, lx')
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        let '(r, lx') := sym_readLI tst ss bc kx lx scr a n (amo_sx wd) in
        (match r with
         | None => SStop
         | Some (v, scs, scr', nx') =>
             SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                      (s_log ss) (s_know ss) nx' (Some a)) scs scr'
         end, lx')
      else (SStop, lx)
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => (SStop, lx)
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => (SStop, lx)
            | Some r' =>
                let '(r, lx') := sym_readLI tst ss bc kx lx scr a n (amo_sx wd) in
                match r with
                | None => (SStop, lx')
                | Some (vold, scs, scr', nx') =>
                    let en := SE a n (amo_newvalB bc wd aop vold (g rs2)) in
                    (SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                              (en :: s_log ss) (s_know ss) nx' r')
                         (scs ++ storeok_scB bc a n) scr', lx_add lx' en)
                end
            end
          else (SStop, lx)
      end
  | Store _ _ _ _ | Sc _ _ _ _ _ _ => let r := sym_stepBI bc kx segs i ss scr in (r, log_head_add lx r)
  | _ => (sym_stepBI bc kx segs i ss scr, lx)
  end.

Lemma sym_readLI_spec : forall bc kx ss lx scr a n sx',
  LXOK lx (s_log ss) ->
  fst (sym_readLI (side_testB bc) ss bc kx lx scr a n sx') = sym_readBI segs ss bc kx scr a n sx'
  /\ LXOK (snd (sym_readLI (side_testB bc) ss bc kx lx scr a n sx')) (s_log ss).
Proof.
  intros bc kx ss lx scr a n sx' HL. unfold sym_readLI.
  destruct (lookupL_spec (side_testB bc) bc lx (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] HL) as [E1 E2].
  destruct (lookupL (side_testB bc) bc lx (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) as [r lx'].
  cbn [fst snd] in *. split; [|exact E2]. rewrite sym_readBI_k. subst r. rewrite log_lookupPG_B. reflexivity.
Qed.

(* [comment removed for export] *)
Definition LSTEP (lx : lidx) (ss : sym_state) (p : stepres * lidx) : Prop :=
  match fst p with SOk ss' _ _ => LXOK (snd p) (s_log ss') | SStop => True end.
Lemma sym_stepLI_spec : forall bc kx i ss scr lx,
  LXOK lx (s_log ss) ->
  fst (sym_stepLI (side_testB bc) bc kx i ss scr lx) = sym_stepBI bc kx segs i ss scr
  /\ LSTEP lx ss (sym_stepLI (side_testB bc) bc kx i ss scr lx).
Proof.
  intros bc kx i ss scr lx HL. unfold LSTEP.
  destruct i; cbn [sym_stepLI]; cbv zeta;
    try (split; [reflexivity|]; cbn [fst snd]; unfold sym_stepBI; cbv zeta;
         repeat match goal with
                | |- match (match ?x with _ => _ end) with _ => _ end => destruct x
                | |- match (if ?x then _ else _) with _ => _ end => destruct x
                end; cbn [s_log sset sjump log_head_add]; try exact I; try exact HL; try (apply lx_add_ok; exact HL); fail).
  - (* [comment removed for export] *)
    match goal with |- context [sym_readLI _ ss bc kx lx scr ?a ?n ?s] =>
      destruct (sym_readLI_spec bc kx ss lx scr a n s HL) as [E1 E2]; destruct (sym_readLI (side_testB bc) ss bc kx lx scr a n s) as [r lx'] end.
    cbn [fst snd] in *. unfold sym_stepBI. cbv zeta. rewrite <- E1. split; [reflexivity|].
    destruct r as [[[[v scs] scr'] nx']|]; [exact E2 | exact I].
  - (* [comment removed for export] *)
    unfold sym_stepBI. cbv zeta. match goal with |- context [amo_alignedbB bc ?e ?w] => destruct (amo_alignedbB bc e w) end; [|split; [reflexivity | exact I]].
    match goal with |- context [sym_readLI _ ss bc kx lx scr ?a ?n ?s] =>
      destruct (sym_readLI_spec bc kx ss lx scr a n s HL) as [E1 E2]; destruct (sym_readLI (side_testB bc) ss bc kx lx scr a n s) as [r lx'] end.
    cbn [fst snd] in *. rewrite <- E1. split; [reflexivity|].
    destruct r as [[[[v scs] scr'] nx']|]; [exact E2 | exact I].
  - (* [comment removed for export] *)
    unfold sym_stepBI. cbv zeta. match goal with |- context [amo_aluop ?o] => destruct (amo_aluop o) end; [|split; [reflexivity | exact I]].
    match goal with |- context [amo_alignedbB bc ?e ?w] => destruct (amo_alignedbB bc e w) end; [|split; [reflexivity | exact I]].
    match goal with |- context [resv_inval ?x ?y] => destruct (resv_inval x y) end; [|split; [reflexivity | exact I]].
    match goal with |- context [sym_readLI _ ss bc kx lx scr ?a ?n ?s] =>
      destruct (sym_readLI_spec bc kx ss lx scr a n s HL) as [E1 E2]; destruct (sym_readLI (side_testB bc) ss bc kx lx scr a n s) as [r lx'] end.
    cbn [fst snd] in *. rewrite <- E1.
    destruct r as [[[[v scs] scr'] nx']|]; (split; [reflexivity|]); cbn [fst snd s_log]; [apply lx_add_ok; exact E2 | exact I].
Qed.

Definition sym_stepXLI (tst : sidetest) (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) (lx : lidx)
  : stepres * lidx :=
  let '(r, lx') := sym_stepLI tst bc kx i ss scr lx in
  (match r with
   | SOk ss' scs scr' =>
       if Nat.leb (s_next ss) (s_next ss')
       then SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
       else SStop
   | SStop => SStop
   end, lx').
Lemma cap_rd_log : forall K i ss, s_log (cap_rd K i ss) = s_log ss.
Proof.
  intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i); [|reflexivity].
  destruct (bv_eqb _ _); [reflexivity|]. destruct (esize_le _ _); reflexivity.
Qed.
Lemma sym_stepXLI_spec : forall bc kx K i ss scr lx,
  LXOK lx (s_log ss) ->
  fst (sym_stepXLI (side_testB bc) bc kx K i ss scr lx) = sym_stepXBI segs bc kx K i ss scr
  /\ LSTEP lx ss (sym_stepXLI (side_testB bc) bc kx K i ss scr lx).
Proof.
  intros bc kx K i ss scr lx HL. unfold sym_stepXLI, sym_stepXBI, LSTEP.
  destruct (sym_stepLI_spec bc kx i ss scr lx HL) as [E1 E2]. unfold LSTEP in E2.
  destruct (sym_stepLI (side_testB bc) bc kx i ss scr lx) as [r lx']. cbn [fst snd] in *. subst r.
  split; [reflexivity|]. destruct (sym_stepBI bc kx segs i ss scr) as [ss' scs scr'|]; [|exact I].
  destruct (Nat.leb (s_next ss) (s_next ss')); [|exact I]. rewrite cap_rd_log. exact E2.
Qed.

Fixpoint sym_execTXLI_go (tst : sidetest) (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
         (ss : sym_state) (ck : sym_state) (lx : lidx) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXLI tst bc kx K i ss scr_nil lx with
          | (SOk ss' [] _, lx') => sym_execTXLI_go tst bc kx t K f false stops ss' (if s_clean ss' then ss' else ck) lx'
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
(* [comment removed for export] *)
Definition sym_execTXLI (tst : sidetest) (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
           (ss : sym_state) : sym_state :=
  sym_execTXLI_go tst bc kx t K fuel first stops (clr ss) (clr ss) lx_empty.

Lemma sym_execTXLI_go_eq : forall bc kx t K fuel first stops ss ck lx,
  LXOK lx (s_log ss) ->
  sym_execTXLI_go (side_testB bc) bc kx t K fuel first stops ss ck lx = sym_execTXBI_go segs bc kx t K fuel first stops ss ck.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck lx HL; [reflexivity|].
  cbn [sym_execTXLI_go sym_execTXBI_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  destruct (sym_stepXLI_spec bc kx K i ss scr_nil lx HL) as [E1 E2]. unfold LSTEP in E2.
  destruct (sym_stepXLI (side_testB bc) bc kx K i ss scr_nil lx) as [r lx']. cbn [fst snd] in *. subst r.
  destruct (sym_stepXBI segs bc kx K i ss scr_nil) as [ss' scs scr'|]; [|reflexivity].
  destruct scs; [|reflexivity]. apply IH. exact E2.
Qed.
Theorem sym_execTXLI_eq : forall bc kx t K fuel first stops ss,
  s_log ss = [] ->
  sym_execTXLI (side_testB bc) bc kx t K fuel first stops ss = sym_execTXBI segs bc kx t K fuel first stops ss.
Proof.
  intros bc kx t K fuel first stops ss H. unfold sym_execTXLI, sym_execTXBI. apply sym_execTXLI_go_eq.
  destruct ss; cbn [clr s_log] in *. subst. exact LXOK_empty.
Qed.
(* [comment removed for export] *)
Theorem sym_execTXLI_pt : forall (tst : sidetest) bc kx t K fuel first stops ss,
  (forall b1 k1 n1 c m, tst b1 k1 n1 c m = side_testB bc b1 k1 n1 c m) ->
  s_log ss = [] ->
  sym_execTXLI tst bc kx t K fuel first stops ss = sym_execTXBI segs bc kx t K fuel first stops ss.
Proof.
  intros tst bc kx t K fuel first stops ss H HL.
  assert (E : tst = side_testB bc) by (repeat (apply functional_extensionality; intros ?); apply H).
  rewrite E. apply sym_execTXLI_eq. exact HL.
Qed.

End WithSegs.
End AX2L.
