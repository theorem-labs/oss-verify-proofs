(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3 AxSymExec3B.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AX2C.
Import AX2. Import AX2B.

(* [comment removed for export] *)
Definition smemo : Type := list (saddr * expr * (bool * bool)).
Fixpoint disj_sides3B (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (memo : smemo)
  : list (saddr * expr) * list (saddr * expr) * smemo * list bool :=
  match kn with
  | [] => ([], [], memo, [])
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, rx, memo1, mk) := disj_sides3B bc rest b1 k1 n1 memo in
      let '(t2, memo2) := side_memo2B bc b1 k1 n1 memo1 c2 m2 in
      let '(t1, memo3) := side_memo2B bc b1 k1 n1 memo2 c1 m1 in
      let r1 := if fst t2 then (c1, m1) :: r else r in
      let rx1 := if snd t2 then (c1, m1) :: rx else rx in
      (if fst t1 then (c2, m2) :: r1 else r1, if snd t1 then (c2, m2) :: rx1 else rx1, memo3,
       fst t1 :: snd t1 :: fst t2 :: snd t2 :: mk)
  | _ :: rest => disj_sides3B bc rest b1 k1 n1 memo
  end.
(* [comment removed for export] *)
Fixpoint selD (kn : list kentry) (mk : list bool) : list (saddr * expr) * list (saddr * expr) :=
  match kn with
  | [] => ([], [])
  | KDisj c1 m1 c2 m2 :: rest =>
      match mk with
      | f1 :: x1 :: f2 :: x2 :: mk' =>
          let '(r, rx) := selD rest mk' in
          let r1 := if f2 then (c1, m1) :: r else r in
          let rx1 := if x2 then (c1, m1) :: rx else rx in
          (if f1 then (c2, m2) :: r1 else r1, if x1 then (c2, m2) :: rx1 else rx1)
      | _ => ([], [])
      end
  | _ :: rest => selD rest mk
  end.
Definition mk_sprep3B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep * list bool :=
  let '(d, dx, _, mk) := disj_sides3B bc (bc_fk bc) b1 k1 n1 [] in
  (SPrep (base_rangeB bc b1) (xhiB bc n1) d dx, mk).

(* [comment removed for export] *)
Fixpoint mask_eqb (x y : list bool) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => if Bool.eqb a b then mask_eqb x' y' else false
  | _, _ => false
  end.
Definition dtab : Type := (list (list bool * positive) * positive)%type.
Definition dt_empty : dtab := ([], xH).
Fixpoint dt_find (l : list (list bool * positive)) (mk : list bool) : option positive :=
  match l with
  | [] => None
  | (mk', id) :: rest => if mask_eqb mk mk' then Some id else dt_find rest mk
  end.
Definition dt_intern (t : dtab) (mk : list bool) : positive * dtab :=
  match dt_find (fst t) mk with
  | Some id => (id, t)
  | None => (snd t, ((mk, snd t) :: fst t, Pos.succ (snd t)))
  end.

(* [comment removed for export] *)
Definition stxd : Type := (stx * positive)%type.
Fixpoint mk_stxsM (bc : bctx) (log : list sentry) (t : ntab) (dt : dtab) : list stxd * ntab * dtab :=   (* [comment removed for export] *)
  match log with
  | [] => ([], t, dt)
  | SE a w v :: older =>
      let '(sxs, t1, dt1) := mk_stxsM bc older t dt in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let '(sp, mk) := mk_sprep3B bc (a_base a) (a_off a) (elen w) in
      let '(did, dt2) := dt_intern dt1 mk in
      (sxs ++ [(STX a w v sp bid (bi_br bi), did)], t2, dt2)
  end.

(* [comment removed for export] *)
Definition memo_get (mo : ptree bool) (did : positive) (f : unit -> bool) : bool * ptree bool :=
  match pt_get mo did with
  | Some r => (r, mo)
  | None => let r := f tt in (r, pt_set did r mo)
  end.
Definition ranges_apart_pcMB (bc : bctx) (sp : sprep) (did : positive) (mo : ptree bool) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool * ptree bool :=
  match n1 with
  | ELit z1 =>
      match n2 with
      | ELit z2 =>
          let m1 := zlit64 z1 in let m2 := zlit64 z2 in
          if (match sp_rng sp, br2 with
              | Some (lo1, hi1), Some (lo2, hi2) =>
                  if Z.leb (hi1 + k1 + m1) (lo2 + k2) then true else Z.leb (hi2 + k2 + m2) (lo1 + k1)
              | _, _ => false
              end) then (true, mo)
          else let '(r, mo') := memo_get mo did (fun _ => in_sidesB bc (sp_D sp) b2 k2 m2) in
               if r then (true, mo') else (lin_apartB bc b1 k1 m1 b2 k2 m2, mo')
      | _ =>
          if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
              | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
                  if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
                  else if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
                  else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
              | _, _, _, _ => false
              end) then (true, mo)
          else let '(r, mo') := memo_get mo did (fun _ => in_sides_xB bc (sp_Dx sp) b2 k2 n2) in
               if r then (true, mo')
               else if negb (shares_var b1 b2) then (false, mo')
               else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then (true, mo')
               else (lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)], mo')
      end
  | _ => (ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2, mo)
  end.

(* [comment removed for export] *)
Definition prune1pcKM (bc : bctx) (sp : sprep) (did : positive) (mo : ptree bool) (wa : saddr) (w : nat) (wv : expr) (K : kentry)
  (same : bool) (br2 : option (Z * Z)) : pk_res * ptree bool :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      (match len with
       | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
       | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
       end, mo)
    else let '(ap, mo') := ranges_apart_pcMB bc sp did mo wb k (elen w) br2 kb kk len in
         if ap then (PKeep, mo')
         else match kcutB bc mk wb k (elen w) kb kk len with
              | [] => (PRepl [], mo')
              | cut => (PRepl cut, mo')
              end in
  match K with
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (prune1pcK bc sp wa w wv K same br2, mo)
      else let '(ap, mo') := ranges_apart_pcMB bc sp did mo wb k (elen w) br2 kb kk (elen w') in
           if ap then (PKeep, mo')
           else if (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) then (PKeep, mo')
           else (PRepl [], mo')
  | KBlob (SA kb kk) len bk =>
      if same then (prune1pcK bc sp wa w wv K same br2, mo)
      else let '(ap, mo') := ranges_apart_pcMB bc sp did mo wb k (elen w) br2 kb kk len in
           (if ap then PKeep else PRepl [], mo')
  | _ => (prune1pcK bc sp wa w wv K same br2, mo)
  end.

(* [comment removed for export] *)
Fixpoint chainK2M (bc : bctx) (sxs : list stxd) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (mo : ptree bool) : list kentry :=
  match sxs with
  | [] => [K]
  | (sx, did) :: rest =>
      match prune1pcKM bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | (PKeep, mo') => chainK2M bc rest K okb same_of br2 mo'
      | (PRepl l, _) =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 PTLeaf
                                                else chain_slow bc (map fst rest) [K']
                                  | None => chain_slow bc (map fst rest) [K']
                                  end) l
          | None => chain_slow bc (map fst rest) l
          end
      end
  end.

Fixpoint mk_flM (g : gval) (sxs : list stxd) : list (stxd * list stxd) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict (fst sx) g then mk_flM g rest else (sx, rest) :: mk_flM g rest
  end.
Definition gflM : Type := (gval * list (stxd * list stxd))%type.
Definition mk_glM (bnds : gtab) (sxs : list stxd) : ptree gflM := pt_map (fun g => (g, mk_flM g sxs)) bnds.

Fixpoint chainKFM (bc : bctx) (fl : list (stxd * list stxd)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (mo : ptree bool) : list kentry :=
  match fl with
  | [] => [K]
  | ((sx, did), rest) :: fl' =>
      match prune1pcKM bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | (PKeep, mo') => chainKFM bc fl' K okb same_of br2 mo'
      | (PRepl l, _) =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 PTLeaf
                                                else chain_slow bc (map fst rest) [K']
                                  | None => chain_slow bc (map fst rest) [K']
                                  end) l
          | None => chain_slow bc (map fst rest) l
          end
      end
  end.

(* [comment removed for export] *)
Definition inertb (K : kentry) : bool :=
  match K with KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => true | _ => false end.
Lemma chainK2M_inert : forall bc sxs K okb same_of br2 mo, inertb K = true -> chainK2M bc sxs K okb same_of br2 mo = [K].
Proof.
  intros bc sxs K okb same_of br2 mo H. revert mo. induction sxs as [|[sx did] rest IH]; intros mo; [reflexivity|].
  cbn [chainK2M]. destruct K; try discriminate H; cbn [prune1pcKM prune1pcK]; apply IH.
Qed.
Fixpoint entriesGM (bc : bctx) (sxs : list stxd) (gl : ptree gflM) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKFM bc fl K okb same_of br2 PTLeaf else chainK2M bc sxs K okb same_of br2 PTLeaf
           | None => chainK2M bc sxs K okb same_of br2 PTLeaf
           end
       | None => if inertb K then [K]   (* [comment removed for export] *)
                 else chainK2M bc sxs K None (fun _ => false) None PTLeaf
       end) ++ entriesGM bc sxs gl rest irest
  | _, _ => []
  end.

Fixpoint stores_partM (bc : bctx) (sxs : list stxd) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | (sx, _) :: newer => stores_partM bc newer ++ chainK2M bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) PTLeaf
  end.

Definition carryGM (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0, _) := mk_stxsM bc log nt_empty dt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM bc sxs (mk_glM (gs_bnds gs) sxs) kn infos.

Definition carryKM (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGM bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.

(* [comment removed for export] *)
Lemma disj_sides3B_fst : forall bc kn b1 k1 n1 memo,
  disj_sides2B bc kn b1 k1 n1 memo = fst (disj_sides3B bc kn b1 k1 n1 memo).
Proof.
  intros bc kn b1 k1 n1. induction kn as [|K rest IH]; intros memo; [reflexivity|].
  destruct K as [| | | | | | | c1 m1 c2 m2 | | |]; cbn [disj_sides2B disj_sides3B]; try apply IH.
  rewrite IH. destruct (disj_sides3B bc rest b1 k1 n1 memo) as [[[r rx] memo1] mk]. cbn [fst].
  destruct (side_memo2B bc b1 k1 n1 memo1 c2 m2) as [t2 memo2].
  destruct (side_memo2B bc b1 k1 n1 memo2 c1 m1) as [t1 memo3]. reflexivity.
Qed.
Lemma disj_sides3B_sel : forall bc kn b1 k1 n1 memo,
  selD kn (snd (disj_sides3B bc kn b1 k1 n1 memo))
  = (fst (fst (fst (disj_sides3B bc kn b1 k1 n1 memo))), snd (fst (fst (disj_sides3B bc kn b1 k1 n1 memo)))).
Proof.
  intros bc kn b1 k1 n1. induction kn as [|K rest IH]; intros memo; [reflexivity|].
  destruct K as [| | | | | | | c1 m1 c2 m2 | | |]; cbn [selD disj_sides3B]; try apply IH.
  specialize (IH memo). destruct (disj_sides3B bc rest b1 k1 n1 memo) as [[[r rx] memo1] mk]. cbn [fst snd] in IH.
  destruct (side_memo2B bc b1 k1 n1 memo1 c2 m2) as [t2 memo2].
  destruct (side_memo2B bc b1 k1 n1 memo2 c1 m1) as [t1 memo3]. cbn [fst snd selD]. rewrite IH. reflexivity.
Qed.
Lemma mk_sprep3B_fst : forall bc b1 k1 n1, fst (mk_sprep3B bc b1 k1 n1) = mk_sprepB bc b1 k1 n1.
Proof.
  intros. unfold mk_sprep3B, mk_sprepB. rewrite disj_sides3B_fst.
  destruct (disj_sides3B bc (bc_fk bc) b1 k1 n1 []) as [[[d dx] mo] mk]. reflexivity.
Qed.
Lemma mk_sprep3B_sel : forall bc b1 k1 n1,
  selD (bc_fk bc) (snd (mk_sprep3B bc b1 k1 n1)) = (sp_D (fst (mk_sprep3B bc b1 k1 n1)), sp_Dx (fst (mk_sprep3B bc b1 k1 n1))).
Proof.
  intros. unfold mk_sprep3B. pose proof (disj_sides3B_sel bc (bc_fk bc) b1 k1 n1 []) as H.
  destruct (disj_sides3B bc (bc_fk bc) b1 k1 n1 []) as [[[d dx] mo] mk]. exact H.
Qed.

Lemma mask_eqb_eq : forall x y, mask_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; destruct y as [|b y]; cbn; intros H; try discriminate; [reflexivity|].
  destruct (Bool.eqb a b) eqn:E; [|discriminate]. apply Bool.eqb_prop in E. subst b. f_equal. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Definition DTI (t : dtab) : Prop :=
  (forall mk id, In (mk, id) (fst t) -> Pos.lt id (snd t))
  /\ (forall mk1 mk2 id, In (mk1, id) (fst t) -> In (mk2, id) (fst t) -> mk1 = mk2).
Lemma DTI_empty : DTI dt_empty.
Proof. split; cbn; intros; contradiction. Qed.
Lemma dt_find_In : forall l mk id, dt_find l mk = Some id -> In (mk, id) l.
Proof.
  induction l as [|[mk' id'] rest IH]; cbn; intros mk id H; [discriminate|].
  destruct (mask_eqb mk mk') eqn:E.
  - injection H as <-. apply mask_eqb_eq in E. subst mk'. left. reflexivity.
  - right. apply IH. exact H.
Qed.
Lemma dt_intern_ok : forall t mk id t',
  DTI t -> dt_intern t mk = (id, t') ->
  DTI t' /\ In (mk, id) (fst t') /\ (forall p, In p (fst t) -> In p (fst t')).
Proof.
  intros [l nx] mk id t' [H1 H2] H. unfold dt_intern in H. cbn [fst snd] in *.
  destruct (dt_find l mk) as [id0|] eqn:F.
  - injection H as <- <-. split; [split; assumption|]. split; [apply dt_find_In; exact F | intros; assumption].
  - injection H as <- <-. unfold DTI. cbn [fst snd]. split; [split|].
    + intros mk0 id0 [E|HIn]; [injection E as _ <-; lia | specialize (H1 _ _ HIn); lia].
    + intros mk1 mk2 id0 [E1|I1] [E2|I2].
      * congruence.
      * injection E1 as _ <-. specialize (H1 _ _ I2). lia.
      * injection E2 as _ <-. specialize (H1 _ _ I1). lia.
      * exact (H2 _ _ _ I1 I2).
    + split; [left; reflexivity | intros p Hp; right; exact Hp].
Qed.

(* [comment removed for export] *)
Definition SXD (bc : bctx) (dt : dtab) (sd : stxd) : Prop :=
  exists mk, In (mk, snd sd) (fst dt) /\ selD (bc_fk bc) mk = (sp_D (sx_sp (fst sd)), sp_Dx (sx_sp (fst sd))).
Lemma SXD_mono : forall bc dt dt' sd, (forall p, In p (fst dt) -> In p (fst dt')) -> SXD bc dt sd -> SXD bc dt' sd.
Proof. intros bc dt dt' sd Hm (mk & HI & HS). exists mk. split; [apply Hm; exact HI | exact HS]. Qed.

Lemma mk_stxsM_ok : forall bc log t dt sxs t' dt',
  DTI dt -> mk_stxsM bc log t dt = (sxs, t', dt') ->
  mk_stxs bc log t = (map fst sxs, t') /\ DTI dt' /\ (forall p, In p (fst dt) -> In p (fst dt')) /\ Forall (SXD bc dt') sxs.
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t dt sxs t' dt' HD H.
  - cbn in H. injection H as <- <- <-. cbn. repeat split; [exact (proj1 HD) | exact (proj2 HD) | intros; assumption | constructor].
  - cbn [mk_stxsM] in H. destruct (mk_stxsM bc older t dt) as [[sxs1 t1] dt1] eqn:E.
    destruct (IH _ _ _ _ _ HD E) as (IH1 & IH2 & IH3 & IH4).
    cbn [mk_stxs]. rewrite IH1.
    destruct (intern bc t1 (a_base a)) as [[bid bi] t2].
    pose proof (mk_sprep3B_fst bc (a_base a) (a_off a) (elen w)) as Hf.
    pose proof (mk_sprep3B_sel bc (a_base a) (a_off a) (elen w)) as Hs.
    destruct (mk_sprep3B bc (a_base a) (a_off a) (elen w)) as [sp mk]. cbn [fst snd] in Hf, Hs.
    destruct (dt_intern dt1 mk) as [did dt2] eqn:EI.
    destruct (dt_intern_ok _ _ _ _ IH2 EI) as (D1 & D2 & D3).
    injection H as <- <- <-. rewrite map_app. cbn [map fst]. rewrite <- Hf.
    split; [reflexivity|]. split; [exact D1|]. split; [intros p Hp; apply D3; apply IH3; exact Hp|].
    apply Forall_app. split.
    + apply Forall_impl with (P := SXD bc dt1); [intros sd; apply SXD_mono; exact D3 | exact IH4].
    + constructor; [|constructor]. exists mk. cbn [fst snd sx_sp]. split; [exact D2 | exact Hs].
Qed.

(* [comment removed for export] *)
Definition DOK (SXS : list stxd) : Prop :=
  forall sx1 sx2 d, In (sx1, d) SXS -> In (sx2, d) SXS ->
    sp_D (sx_sp sx1) = sp_D (sx_sp sx2) /\ sp_Dx (sx_sp sx1) = sp_Dx (sx_sp sx2).
Lemma DOK_of_SXD : forall bc dt SXS, DTI dt -> Forall (SXD bc dt) SXS -> DOK SXS.
Proof.
  intros bc dt SXS [_ HU] HF sx1 sx2 d I1 I2.
  destruct (proj1 (Forall_forall _ _) HF _ I1) as (mk1 & A1 & B1).
  destruct (proj1 (Forall_forall _ _) HF _ I2) as (mk2 & A2 & B2).
  cbn [fst snd] in *. rewrite (HU _ _ _ A1 A2) in B1. rewrite B1 in B2. injection B2 as -> ->. split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition vd (bc : bctx) (sp : sprep) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n2 with
  | ELit z2 => in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2)
  | _ => in_sides_xB bc (sp_Dx sp) b2 k2 n2
  end.
Definition MOK (bc : bctx) (SXS : list stxd) (b2 : expr) (k2 : Z) (n2 : expr) (mo : ptree bool) : Prop :=
  forall sx did r, In (sx, did) SXS -> pt_get mo did = Some r -> r = vd bc (sx_sp sx) b2 k2 n2.
Lemma MOK_leaf : forall bc SXS b2 k2 n2, MOK bc SXS b2 k2 n2 PTLeaf.
Proof. intros bc SXS b2 k2 n2 sx did r _ H. rewrite pt_get_leaf in H. discriminate. Qed.

Lemma memo_get_ok : forall bc SXS b2 k2 n2 mo sx did f,
  DOK SXS -> In (sx, did) SXS -> MOK bc SXS b2 k2 n2 mo -> f tt = vd bc (sx_sp sx) b2 k2 n2 ->
  fst (memo_get mo did f) = vd bc (sx_sp sx) b2 k2 n2 /\ MOK bc SXS b2 k2 n2 (snd (memo_get mo did f)).
Proof.
  intros bc SXS b2 k2 n2 mo sx did f HD HI HM Hf. unfold memo_get.
  destruct (pt_get mo did) as [r|] eqn:G; cbn [fst snd].
  - split; [exact (HM _ _ _ HI G) | exact HM].
  - split; [exact Hf|]. intros sx' did' r' HI' G'.
    destruct (Pos.eq_dec did' did) as [->|NE].
    + rewrite pt_gss in G'. injection G' as <-. rewrite Hf. unfold vd.
      destruct (HD _ _ _ HI HI') as [E1 E2]. rewrite E1, E2. reflexivity.
    + rewrite pt_gso in G' by exact NE. exact (HM _ _ _ HI' G').
Qed.

Lemma ranges_apart_pcMB_ok : forall bc SXS sx did mo b1 k1 n1 br2 b2 k2 n2,
  DOK SXS -> In (sx, did) SXS -> MOK bc SXS b2 k2 n2 mo ->
  fst (ranges_apart_pcMB bc (sx_sp sx) did mo b1 k1 n1 br2 b2 k2 n2) = ranges_apart_pcB bc (sx_sp sx) b1 k1 n1 br2 b2 k2 n2
  /\ MOK bc SXS b2 k2 n2 (snd (ranges_apart_pcMB bc (sx_sp sx) did mo b1 k1 n1 br2 b2 k2 n2)).
Proof.
  intros bc SXS sx did mo b1 k1 n1 br2 b2 k2 n2 HD HI HM.
  unfold ranges_apart_pcMB, ranges_apart_pcB.
  destruct n1 as [z1| | | | | | |]; try (split; [reflexivity | exact HM]).
  destruct n2 as [z2| | | | | | |];
    [ match goal with |- context [if ?c then (true, ?m) else _] =>
        replace c with (match sp_rng (sx_sp sx), br2 with
                        | Some (lo1, hi1), Some (lo2, hi2) =>
                            (Z.leb (hi1 + k1 + zlit64 z1) (lo2 + k2) || Z.leb (hi2 + k2 + zlit64 z2) (lo1 + k1))%bool
                        | _, _ => false end)
          by (destruct (sp_rng (sx_sp sx)) as [[? ?]|]; destruct br2 as [[? ?]|]; reflexivity) end;
      match goal with |- context [if ?c then (true, ?m) else _] => destruct c end; [split; [reflexivity | exact HM]|];
      destruct (memo_get_ok bc SXS b2 k2 (ELit z2) mo sx did (fun _ => in_sidesB bc (sp_D (sx_sp sx)) b2 k2 (zlit64 z2)) HD HI HM eq_refl) as [E M];
      destruct (memo_get mo did _) as [r mo']; cbn [fst snd] in E, M; unfold vd in E; rewrite <- E;
      destruct r; split; try reflexivity; exact M
    | .. ].
  all: match goal with |- context [if ?c then (true, ?m) else _] => destruct c end; [split; [reflexivity | exact HM]|];
    match goal with |- context [memo_get ?m ?d ?f] =>
      destruct (memo_get_ok bc SXS b2 k2 _ m sx d f HD HI HM eq_refl) as [E M]; destruct (memo_get m d f) as [r mo'] end;
    cbn [fst snd] in E, M; unfold vd in E; rewrite <- E;
    destruct r; [split; [reflexivity | exact M]|];
    destruct (negb (shares_var b1 b2)); [split; [reflexivity | exact M]|];
    match goal with |- context [if ?c then (true, ?m) else _] => destruct c end; split; try reflexivity; exact M.
Qed.

(* [comment removed for export] *)
Definition erange_of (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KWord (SA kb kk) w' _ => Some (kb, kk, elen w')
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ => Some (kb, kk, len)
  | _ => None
  end.
Definition MOKK (bc : bctx) (SXS : list stxd) (K : kentry) (mo : ptree bool) : Prop :=
  match erange_of K with Some (b2, k2, n2) => MOK bc SXS b2 k2 n2 mo | None => True end.
Lemma MOKK_leaf : forall bc SXS K, MOKK bc SXS K PTLeaf.
Proof. intros. unfold MOKK. destruct (erange_of K) as [[[? ?] ?]|]; [apply MOK_leaf | exact I]. Qed.

Lemma prune1pcKM_ok : forall bc SXS sx did mo wa w wv K same br2,
  DOK SXS -> In (sx, did) SXS -> MOKK bc SXS K mo ->
  fst (prune1pcKM bc (sx_sp sx) did mo wa w wv K same br2) = prune1pcK bc (sx_sp sx) wa w wv K same br2
  /\ MOKK bc SXS K (snd (prune1pcKM bc (sx_sp sx) did mo wa w wv K same br2)).
Proof.
  intros bc SXS sx did mo wa w wv K same br2 HD HI HM.
  assert (ZF : forall (mkf : saddr -> expr -> kentry) kb kk len, MOK bc SXS kb kk len mo ->
    let r := (if same then
                (match len with
                 | ELit l0 => PRepl (ktrim mkf kb kk l0 (a_off wa) w)
                 | _ => if Z.leb (a_off wa + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mkf (a_base wa) (a_off wa) (elen w) kb kk len)
                 end, mo)
              else let '(ap, mo') := ranges_apart_pcMB bc (sx_sp sx) did mo (a_base wa) (a_off wa) (elen w) br2 kb kk len in
                   if ap then (PKeep, mo')
                   else match kcutB bc mkf (a_base wa) (a_off wa) (elen w) kb kk len with
                        | [] => (PRepl [], mo')
                        | cut => (PRepl cut, mo')
                        end) in
    fst r = (if same then
               match len with
               | ELit l0 => PRepl (ktrim mkf kb kk l0 (a_off wa) w)
               | _ => if Z.leb (a_off wa + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mkf (a_base wa) (a_off wa) (elen w) kb kk len)
               end
             else if ranges_apart_pcB bc (sx_sp sx) (a_base wa) (a_off wa) (elen w) br2 kb kk len then PKeep
             else match kcutB bc mkf (a_base wa) (a_off wa) (elen w) kb kk len with
                  | [] => if ranges_apart_pcB bc (sx_sp sx) (a_base wa) (a_off wa) (elen w) br2 kb kk len then PKeep else PRepl []
                  | cut => PRepl cut
                  end)
    /\ MOK bc SXS kb kk len (snd r)).
  { intros mkf kb kk len HM0. cbv zeta. destruct same; [split; [reflexivity | exact HM0]|].
    destruct (ranges_apart_pcMB_ok bc SXS sx did mo (a_base wa) (a_off wa) (elen w) br2 kb kk len HD HI HM0) as [E M].
    destruct (ranges_apart_pcMB bc (sx_sp sx) did mo (a_base wa) (a_off wa) (elen w) br2 kb kk len) as [ap mo'].
    cbn [fst snd] in E, M. rewrite <- E. destruct ap; [split; [reflexivity | exact M]|].
    destruct (kcutB bc mkf (a_base wa) (a_off wa) (elen w) kb kk len); split; try reflexivity; exact M. }
  unfold MOKK in *.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len|kid kargs];
    cbn [erange_of] in HM |- *; unfold prune1pcKM, prune1pcK; cbn [a_base a_off];
    try (split; [reflexivity | exact HM]); try (exact (ZF _ kb kk len HM)).
  - (* [comment removed for export] *)
    destruct same; [split; [reflexivity | exact HM]|].
    destruct (ranges_apart_pcMB_ok bc SXS sx did mo (a_base wa) (a_off wa) (elen w) br2 kb kk (elen w') HD HI HM) as [E M].
    destruct (ranges_apart_pcMB bc (sx_sp sx) did mo (a_base wa) (a_off wa) (elen w) br2 kb kk (elen w')) as [ap mo'].
    cbn [fst snd] in E, M. rewrite <- E. destruct ap; [split; [reflexivity | exact M]|].
    destruct (Nat.eqb w 1); destruct (Nat.eqb w' 1); cbn [andb]; try (split; [reflexivity | exact M]).
    destruct (expr_eqb wv v); split; try reflexivity; exact M.
  - (* [comment removed for export] *)
    destruct same; [split; [reflexivity | exact HM]|].
    destruct (ranges_apart_pcMB_ok bc SXS sx did mo (a_base wa) (a_off wa) (elen w) br2 kb kk len HD HI HM) as [E M].
    destruct (ranges_apart_pcMB bc (sx_sp sx) did mo (a_base wa) (a_off wa) (elen w) br2 kb kk len) as [ap mo'].
    cbn [fst snd] in E, M. rewrite <- E. destruct ap; split; try reflexivity; exact M.
Qed.

Lemma chainK2M_eq : forall bc SXS, DOK SXS -> forall sxs K okb same_of br2 mo,
  incl sxs SXS -> MOKK bc SXS K mo ->
  chainK2M bc sxs K okb same_of br2 mo = chainK2 bc (map fst sxs) K okb same_of br2.
Proof.
  intros bc SXS HD sxs. induction sxs as [|[sx did] rest IH]; intros K okb same_of br2 mo Hi HM; [reflexivity|].
  cbn [chainK2M chainK2 map fst].
  assert (HI : In (sx, did) SXS) by (apply Hi; left; reflexivity).
  assert (Hr : incl rest SXS) by (intros x Hx; apply Hi; right; exact Hx).
  destruct (prune1pcKM_ok bc SXS sx did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 HD HI HM) as [E M].
  destruct (prune1pcKM bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) as [pr mo'].
  cbn [fst snd] in E, M. rewrite <- E. destruct pr as [|l]; [apply IH; assumption|].
  destruct okb as [kb|]; [|reflexivity].
  apply flat_map_ext. intros K'. destruct (kbase K') as [kb'|]; [|reflexivity].
  destruct (expr_eqb kb' kb); [|reflexivity]. apply IH; [exact Hr | apply MOKK_leaf].
Qed.

Definition flproj (p : stxd * list stxd) : stx * list stx := (fst (fst p), map fst (snd p)).
Lemma mk_flM_proj : forall g sxs, map flproj (mk_flM g sxs) = mk_fl g (map fst sxs).
Proof.
  intros g sxs. induction sxs as [|sd rest IH]; [reflexivity|]. cbn [mk_flM mk_fl map].
  destruct (verdict (fst sd) g); [exact IH|]. cbn [map]. rewrite IH. reflexivity.
Qed.
Lemma mk_flM_in : forall g sxs p, In p (mk_flM g sxs) -> In (fst p) sxs /\ incl (snd p) sxs.
Proof.
  intros g sxs. induction sxs as [|sd rest IH]; intros p Hp; [contradiction|]. cbn [mk_flM] in Hp.
  destruct (verdict (fst sd) g).
  - destruct (IH _ Hp) as [A B]. split; [right; exact A | intros x Hx; right; apply B; exact Hx].
  - destruct Hp as [<-|Hp]; [split; [left; reflexivity | intros x Hx; right; exact Hx]|].
    destruct (IH _ Hp) as [A B]. split; [right; exact A | intros x Hx; right; apply B; exact Hx].
Qed.

Lemma chainKFM_eq : forall bc SXS, DOK SXS -> forall fl K okb same_of br2 mo,
  (forall p, In p fl -> In (fst p) SXS /\ incl (snd p) SXS) -> MOKK bc SXS K mo ->
  chainKFM bc fl K okb same_of br2 mo = chainKF bc (map flproj fl) K okb same_of br2.
Proof.
  intros bc SXS HD fl. induction fl as [|[[sx did] rest] fl' IH]; intros K okb same_of br2 mo Hf HM; [reflexivity|].
  cbn [chainKFM chainKF map flproj fst snd].
  destruct (Hf _ (or_introl eq_refl)) as [HI Hr]. cbn [fst snd] in HI, Hr.
  destruct (prune1pcKM_ok bc SXS sx did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 HD HI HM) as [E M].
  destruct (prune1pcKM bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) as [pr mo'].
  cbn [fst snd] in E, M. rewrite <- E. destruct pr as [|l].
  - apply IH; [intros p Hp; apply Hf; right; exact Hp | exact M].
  - destruct okb as [kb|]; [|reflexivity].
    apply flat_map_ext. intros K'. destruct (kbase K') as [kb'|]; [|reflexivity].
    destruct (expr_eqb kb' kb); [|reflexivity]. apply (chainK2M_eq bc SXS HD); [exact Hr | apply MOKK_leaf].
Qed.

Lemma entriesGM_eq : forall bc sxs, DOK sxs -> forall bnds kn infos,
  entriesGM bc sxs (mk_glM bnds sxs) kn infos = entriesG bc (map fst sxs) (mk_gl bnds (map fst sxs)) kn infos.
Proof.
  intros bc sxs HD bnds kn. induction kn as [|K rest IH]; intros infos; [reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|]. cbn [entriesGM entriesG]. rewrite IH. f_equal.
  destruct oi as [ei|].
  2:{ destruct (inertb K) eqn:HI; [|apply (chainK2M_eq bc sxs HD); [apply incl_refl | apply MOKK_leaf]].
      rewrite <- (chainK2M_inert bc sxs K None (fun _ => false) None PTLeaf HI).
      apply (chainK2M_eq bc sxs HD); [apply incl_refl | apply MOKK_leaf]. }
  unfold mk_glM, mk_gl. rewrite !pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply (chainK2M_eq bc sxs HD); [apply incl_refl | apply MOKK_leaf]].
  destruct (inb g ei); [|apply (chainK2M_eq bc sxs HD); [apply incl_refl | apply MOKK_leaf]].
  rewrite <- mk_flM_proj. apply (chainKFM_eq bc sxs HD); [apply mk_flM_in | apply MOKK_leaf].
Qed.

Lemma stores_partM_eq : forall bc SXS, DOK SXS -> forall sxs, incl sxs SXS ->
  stores_partM bc sxs = stores_part bc (map fst sxs).
Proof.
  intros bc SXS HD sxs. induction sxs as [|[sx did] newer IH]; intros Hi; [reflexivity|].
  cbn [stores_partM stores_part map fst].
  assert (Hn : incl newer SXS) by (intros x Hx; apply Hi; right; exact Hx).
  rewrite (IH Hn). f_equal. apply (chainK2M_eq bc SXS HD); [exact Hn | apply MOKK_leaf].
Qed.

Lemma carryGM_eq : forall bc log kn, carryGM bc log kn = carryG bc log kn.
Proof.
  intros bc log kn. unfold carryGM, carryG.
  destruct (mk_stxsM bc log nt_empty dt_empty) as [[sxs t0] dt] eqn:E.
  destruct (mk_stxsM_ok _ _ _ _ _ _ _ DTI_empty E) as (E1 & D1 & _ & F1).
  rewrite E1.
  destruct (scan_entries bc kn t0 gst_empty) as [[infos t1] gs].
  pose proof (DOK_of_SXD bc dt sxs D1 F1) as HD.
  rewrite (stores_partM_eq bc sxs HD sxs (incl_refl _)), (entriesGM_eq bc sxs HD). reflexivity.
Qed.

Lemma carryKM_eq : forall bc log kn hints, carryKM bc log kn hints = carryK bc log kn hints.
Proof.
  intros bc log kn hints. unfold carryKM, carryK. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [rewrite carryGM_eq|]; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition quick_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  if xt_nowrapB bc pos then if xt_nowrapB bc neg then
    match lin_range (erangeV bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) with
    | Some (lo, _) => Z.leb 0 lo
    | None => false
    end
  else false else false.
Lemma quick_ge0B_ge0 : forall bc pos neg, quick_ge0B bc pos neg = true -> lin_ge0B bc pos neg = true.
Proof.
  intros bc pos neg H. unfold quick_ge0B in H. unfold lin_ge0B.
  destruct (xt_nowrapB bc pos); [|discriminate]. destruct (xt_nowrapB bc neg); [|discriminate]. cbv zeta.
  unfold lin_testB at 1.
  destruct (lin_range (erangeV bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))) as [[lo hi]|]; [|discriminate].
  rewrite H. reflexivity.
Qed.
Definition side_aboveB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (c : saddr) (m : expr) : bool :=
  quick_ge0B bc [(b1, k1); (n1, 0%Z)] [(a_base c, a_off c); (m, 1%Z)].
Definition side_testS (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (c : saddr) (m : expr) : bool * bool :=
  if side_aboveB bc b1 k1 n1 c m then (false, false) else side_testB bc b1 k1 n1 c m.

Definition sidetest : Type := expr -> Z -> expr -> saddr -> expr -> bool * bool.
Definition side_memo2G (tst : sidetest) (b1 : expr) (k1 : Z) (n1 : expr) (memo : smemo) (c : saddr) (m : expr) : (bool * bool) * smemo :=
  if side_cheap b1 c then ((false, false), memo)
  else match side_find2B c m memo with
       | Some r => (r, memo)
       | None => let r := tst b1 k1 n1 c m in (r, (c, m, r) :: memo)
       end.
Fixpoint disj_sides3G (tst : sidetest) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (memo : smemo)
  : list (saddr * expr) * list (saddr * expr) * smemo * list bool :=
  match kn with
  | [] => ([], [], memo, [])
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, rx, memo1, mk) := disj_sides3G tst rest b1 k1 n1 memo in
      let '(t2, memo2) := side_memo2G tst b1 k1 n1 memo1 c2 m2 in
      let '(t1, memo3) := side_memo2G tst b1 k1 n1 memo2 c1 m1 in
      let r1 := if fst t2 then (c1, m1) :: r else r in
      let rx1 := if snd t2 then (c1, m1) :: rx else rx in
      (if fst t1 then (c2, m2) :: r1 else r1, if snd t1 then (c2, m2) :: rx1 else rx1, memo3,
       fst t1 :: snd t1 :: fst t2 :: snd t2 :: mk)
  | _ :: rest => disj_sides3G tst rest b1 k1 n1 memo
  end.
Definition mk_sprep3G (tst : sidetest) (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep * list bool :=
  let '(d, dx, _, mk) := disj_sides3G tst (bc_fk bc) b1 k1 n1 [] in
  (SPrep (base_rangeB bc b1) (xhiB bc n1) d dx, mk).
Fixpoint mk_stxsG (tst : sidetest) (bc : bctx) (log : list sentry) (t : ntab) (dt : dtab) : list stxd * ntab * dtab :=
  match log with
  | [] => ([], t, dt)
  | SE a w v :: older =>
      let '(sxs, t1, dt1) := mk_stxsG tst bc older t dt in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let '(sp, mk) := mk_sprep3G tst bc (a_base a) (a_off a) (elen w) in
      let '(did, dt2) := dt_intern dt1 mk in
      (sxs ++ [(STX a w v sp bid (bi_br bi), did)], t2, dt2)
  end.
Definition carryGG (tst : sidetest) (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0, _) := mk_stxsG tst bc log nt_empty dt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM bc sxs (mk_glM (gs_bnds gs) sxs) kn infos.

Lemma side_memo2G_B : forall bc, side_memo2G (side_testB bc) = side_memo2B bc.
Proof. intros. repeat (apply functional_extensionality; intros ?). reflexivity. Qed.
Lemma disj_sides3G_B : forall bc kn b1 k1 n1 memo, disj_sides3G (side_testB bc) kn b1 k1 n1 memo = disj_sides3B bc kn b1 k1 n1 memo.
Proof.
  intros bc kn b1 k1 n1 memo. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [disj_sides3G disj_sides3B]; try exact IH. rewrite IH, side_memo2G_B. reflexivity.
Qed.
Lemma mk_sprep3G_B : forall bc b1 k1 n1, mk_sprep3G (side_testB bc) bc b1 k1 n1 = mk_sprep3B bc b1 k1 n1.
Proof. intros. unfold mk_sprep3G, mk_sprep3B. rewrite disj_sides3G_B. reflexivity. Qed.
Lemma mk_stxsG_B : forall bc log t dt, mk_stxsG (side_testB bc) bc log t dt = mk_stxsM bc log t dt.
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t dt; [reflexivity|].
  cbn [mk_stxsG mk_stxsM]. rewrite IH. destruct (mk_stxsM bc older t dt) as [[sxs t1] dt1].
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2]. rewrite mk_sprep3G_B. reflexivity.
Qed.
Lemma carryGG_B : forall bc log kn, carryGG (side_testB bc) bc log kn = carryGM bc log kn.
Proof. intros. unfold carryGG, carryGM. rewrite mk_stxsG_B. reflexivity. Qed.
Lemma carryGG_ext : forall (t1 t2 : sidetest) bc log kn,
  (forall b1 k1 n1 c m, t1 b1 k1 n1 c m = t2 b1 k1 n1 c m) -> carryGG t1 bc log kn = carryGG t2 bc log kn.
Proof.
  intros t1 t2 bc log kn H. assert (E : t1 = t2) by (repeat (apply functional_extensionality; intros ?); apply H). rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Definition carryKS (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _ :: _, [] => (carryGG (side_testS bc) bc log kn, [], [])
  | _ :: _, _ :: _ => carryKM bc log kn hints
  end.
(* [comment removed for export] *)
Lemma carryKS_pt : forall bc log kn hints,
  (forall b1 k1 n1 c m, side_testS bc b1 k1 n1 c m = side_testB bc b1 k1 n1 c m) ->
  carryKS bc log kn hints = carryKM bc log kn hints.
Proof.
  intros bc log kn hints H. unfold carryKS, carryKM. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|reflexivity].
  rewrite (carryGG_ext (side_testS bc) (side_testB bc) bc (s :: older) kn H), carryGG_B. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FGS : Z := 6.
Definition fgenc (a : Z) : positive := Z.to_pos (if Z.leb 0 a then 2 * a + 1 else - (2 * a))%Z.
Definition fgkey (k : Z) (w : nat) : option positive :=
  match w with
  | O => None
  | S _ => let a := Z.shiftr k FGS in
           if Z.eqb a (Z.shiftr (k + zofn w - 1) FGS) then Some (fgenc a) else None
  end.
Lemma fgenc_inj : forall a b, fgenc a = fgenc b -> a = b.
Proof.
  intros a b H. unfold fgenc in H.
  destruct (Z.leb_spec 0 a); destruct (Z.leb_spec 0 b); apply Z2Pos.inj in H; lia.
Qed.
Lemma fgkey_apart : forall kk w' k w g1 g2,
  fgkey kk w' = Some g1 -> fgkey k w = Some g2 -> g1 <> g2 -> kword_keepF kk w' k w = true.
Proof.
  intros kk w' k w g1 g2 H1 H2 NE. rewrite kword_keepF_eq. unfold fgkey in H1, H2.
  destruct w' as [|w'0]; [discriminate|]. destruct w as [|w0]; [discriminate|]. cbv zeta in H1, H2. rewrite !zofn_eq in H1, H2.
  destruct (Z.eqb_spec (Z.shiftr kk FGS) (Z.shiftr (kk + Z.of_nat (S w'0) - 1) FGS)) as [E1|]; [|discriminate]. injection H1 as <-.
  destruct (Z.eqb_spec (Z.shiftr k FGS) (Z.shiftr (k + Z.of_nat (S w0) - 1) FGS)) as [E2|]; [|discriminate]. injection H2 as <-.
  assert (NA : Z.shiftr kk FGS <> Z.shiftr k FGS) by (intros E; apply NE; rewrite E; reflexivity).
  rewrite !Z.shiftr_div_pow2 in E1, E2, NA by (unfold FGS; lia). change (2 ^ FGS)%Z with 64%Z in E1, E2, NA.
  destruct (Z.leb_spec (kk + Z.of_nat (S w'0)) k) as [|L1]; [reflexivity|].
  destruct (Z.leb_spec (k + Z.of_nat (S w0)) kk) as [|L2]; [reflexivity|]. exfalso.
  destruct (Z.le_gt_cases kk k) as [LE|GT].
  - (* [comment removed for export] *)
    pose proof (Z.div_le_mono kk k 64 ltac:(lia) LE). pose proof (Z.div_le_mono k (kk + Z.of_nat (S w'0) - 1) 64 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono k kk 64 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono kk (k + Z.of_nat (S w0) - 1) 64 ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition ranges_apart_pcMF (bc : bctx) (sp : sprep) (did : positive) (mo : ptree bool) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool * ptree bool :=
  match n1 with
  | ELit _ => match pt_get mo did with
              | Some true => (true, mo)
              | _ => ranges_apart_pcMB bc sp did mo b1 k1 n1 br2 b2 k2 n2
              end
  | _ => ranges_apart_pcMB bc sp did mo b1 k1 n1 br2 b2 k2 n2
  end.
Lemma ranges_apart_pcMF_eq : forall bc sp did mo b1 k1 n1 br2 b2 k2 n2,
  ranges_apart_pcMF bc sp did mo b1 k1 n1 br2 b2 k2 n2 = ranges_apart_pcMB bc sp did mo b1 k1 n1 br2 b2 k2 n2.
Proof.
  intros. unfold ranges_apart_pcMF. destruct n1; try reflexivity.
  destruct (pt_get mo did) as [[|]|] eqn:E; try reflexivity.
  unfold ranges_apart_pcMB, memo_get. rewrite E. destruct n2;
    match goal with |- _ = (if ?c then _ else _) => destruct c; reflexivity end.
Qed.
(* [comment removed for export] *)
Definition raptest : Type := bctx -> sprep -> positive -> ptree bool -> expr -> Z -> expr -> option (Z * Z) -> expr -> Z -> expr -> bool * ptree bool.
Definition prune1pcKG (ra : raptest) (bc : bctx) (sp : sprep) (did : positive) (mo : ptree bool) (wa : saddr) (w : nat) (wv : expr) (K : kentry)
  (same : bool) (br2 : option (Z * Z)) : pk_res * ptree bool :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      (match len with
       | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
       | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
       end, mo)
    else let '(ap, mo') := ra bc sp did mo wb k (elen w) br2 kb kk len in
         if ap then (PKeep, mo')
         else match kcutB bc mk wb k (elen w) kb kk len with
              | [] => (PRepl [], mo')
              | cut => (PRepl cut, mo')
              end in
  match K with
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (prune1pcK bc sp wa w wv K same br2, mo)
      else let '(ap, mo') := ra bc sp did mo wb k (elen w) br2 kb kk (elen w') in
           if ap then (PKeep, mo')
           else if (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) then (PKeep, mo')
           else (PRepl [], mo')
  | KBlob (SA kb kk) len bk =>
      if same then (prune1pcK bc sp wa w wv K same br2, mo)
      else let '(ap, mo') := ra bc sp did mo wb k (elen w) br2 kb kk len in
           (if ap then PKeep else PRepl [], mo')
  | _ => (prune1pcK bc sp wa w wv K same br2, mo)
  end.
Lemma prune1pcKG_B : forall bc sp did mo wa w wv K same br2,
  prune1pcKG ranges_apart_pcMB bc sp did mo wa w wv K same br2 = prune1pcKM bc sp did mo wa w wv K same br2.
Proof. reflexivity. Qed.
Definition prune1pcKF : bctx -> sprep -> positive -> ptree bool -> saddr -> nat -> expr -> kentry -> bool -> option (Z * Z) -> pk_res * ptree bool :=
  prune1pcKG ranges_apart_pcMF.
Lemma prune1pcKF_eq : forall bc sp did mo wa w wv K same br2,
  prune1pcKF bc sp did mo wa w wv K same br2 = prune1pcKM bc sp did mo wa w wv K same br2.
Proof.
  intros. unfold prune1pcKF. rewrite <- prune1pcKG_B. f_equal.
  repeat (apply functional_extensionality; intros ?). apply ranges_apart_pcMF_eq.
Qed.

(* [comment removed for export] *)
Definition prepf : Type := expr -> Z -> expr -> sprep * list bool.
Fixpoint mk_stxsA (prep : prepf) (bc : bctx) (rlog : list sentry) (t : ntab) (dt : dtab) (acc : list stxd) : list stxd * ntab * dtab :=
  match rlog with   (* [comment removed for export] *)
  | [] => (rev_append acc [], t, dt)
  | SE a w v :: newer =>
      let '(r, t2) := intern bc t (a_base a) in
      let '(bid, bi) := r in
      let '(sp, mk) := prep (a_base a) (a_off a) (elen w) in
      let '(did, dt2) := dt_intern dt mk in
      mk_stxsA prep bc newer t2 dt2 ((STX a w v sp bid (bi_br bi), did) :: acc)
  end.
Definition mk_stxsL (prep : prepf) (bc : bctx) (log : list sentry) (t : ntab) (dt : dtab) : list stxd * ntab * dtab :=
  mk_stxsA prep bc (rev_append log []) t dt [].
Lemma mk_stxsG_snoc : forall tst bc l a w v t dt,
  mk_stxsG tst bc (l ++ [SE a w v]) t dt =
  let '(r, t2) := intern bc t (a_base a) in
  let '(bid, bi) := r in
  let '(sp, mk) := mk_sprep3G tst bc (a_base a) (a_off a) (elen w) in
  let '(did, dt2) := dt_intern dt mk in
  let '(sxs, t', dt') := mk_stxsG tst bc l t2 dt2 in
  ((STX a w v sp bid (bi_br bi), did) :: sxs, t', dt').
Proof.
  intros tst bc l a w v. induction l as [|[a' w' v'] l IH]; intros t dt.
  - cbn [app mk_stxsG]. destruct (intern bc t (a_base a)) as [[bid bi] t2].
    destruct (mk_sprep3G tst bc (a_base a) (a_off a) (elen w)) as [sp mk]. destruct (dt_intern dt mk) as [did dt2]. reflexivity.
  - cbn [app mk_stxsG]. rewrite IH. destruct (intern bc t (a_base a)) as [[bid bi] t2].
    destruct (mk_sprep3G tst bc (a_base a) (a_off a) (elen w)) as [sp mk]. destruct (dt_intern dt mk) as [did dt2].
    destruct (mk_stxsG tst bc l t2 dt2) as [[sxs t'] dt'].
    destruct (intern bc t' (a_base a')) as [[bid' bi'] t2'].
    destruct (mk_sprep3G tst bc (a_base a') (a_off a') (elen w')) as [sp' mk']. destruct (dt_intern dt' mk') as [did' dt2']. reflexivity.
Qed.
Lemma mk_stxsA_eq : forall tst bc rlog t dt acc,
  mk_stxsA (mk_sprep3G tst bc) bc rlog t dt acc = let '(sxs, t', dt') := mk_stxsG tst bc (rev rlog) t dt in (rev acc ++ sxs, t', dt').
Proof.
  intros tst bc rlog. induction rlog as [|[a w v] newer IH]; intros t dt acc.
  - cbn [mk_stxsA rev mk_stxsG]. rewrite rev_append_rev. reflexivity.
  - cbn [mk_stxsA rev]. rewrite mk_stxsG_snoc. destruct (intern bc t (a_base a)) as [[bid bi] t2].
    destruct (mk_sprep3G tst bc (a_base a) (a_off a) (elen w)) as [sp mk]. destruct (dt_intern dt mk) as [did dt2].
    rewrite IH. destruct (mk_stxsG tst bc (rev newer) t2 dt2) as [[sxs t'] dt']. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma mk_stxsL_eq : forall tst bc log t dt, mk_stxsL (mk_sprep3G tst bc) bc log t dt = mk_stxsG tst bc log t dt.
Proof.
  intros. unfold mk_stxsL. rewrite mk_stxsA_eq, rev_append_rev, app_nil_r, rev_involutive.
  destruct (mk_stxsG tst bc log t dt) as [[sxs t'] dt']. reflexivity.
Qed.


Definition kstx : Type := (stxd * option positive)%type.
Definition skey (sd : stxd) : option positive := fgkey (a_off (sx_a (fst sd))) (sx_w (fst sd)).
Definition kkey (K : kentry) : option positive := match K with KWord (SA _ kk) w' _ => fgkey kk w' | _ => None end.
Definition skipS (ok : option positive) (same : bool) (sk : option positive) : bool :=
  if same then match ok with
               | Some g1 => match sk with Some g2 => negb (Pos.eqb g1 g2) | None => false end
               | None => false
               end
  else false.
Definition KOK (ks : kstx) : Prop := snd ks = skey (fst ks).
Definition OKK (ok : option positive) (K : kentry) : Prop := match ok with Some g => kkey K = Some g | None => True end.
Lemma OKK_kkey : forall K, OKK (kkey K) K.
Proof. intros K. unfold OKK. destruct (kkey K); [reflexivity | exact I]. Qed.

Lemma skip_keep : forall bc sp did mo wa w wv K br2 g1 g2,
  kkey K = Some g1 -> fgkey (a_off wa) w = Some g2 -> g1 <> g2 ->
  prune1pcKM bc sp did mo wa w wv K true br2 = (PKeep, mo).
Proof.
  intros bc sp did mo wa w wv K br2 g1 g2 HK HS NE.
  destruct K as [[kb kk] w' v| | | | | | | | | |]; cbn [kkey] in HK; try discriminate.
  unfold prune1pcKM, prune1pcK. rewrite (fgkey_apart _ _ _ _ _ _ HK HS NE). reflexivity.
Qed.

Definition sx1 (p : kstx) : stx := fst (fst p).
Fixpoint chainK2S (bc : bctx) (ksxs : list kstx) (K : kentry) (ok : option positive) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (mo : ptree bool) : list kentry :=
  match ksxs with
  | [] => [K]
  | ((sx, did), sk) :: rest =>
      let same := same_of (sx_bid sx) in
      if skipS ok same sk then chainK2S bc rest K ok okb same_of br2 mo
      else
      match prune1pcKF bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K same br2 with
      | (PKeep, mo') => chainK2S bc rest K ok okb same_of br2 mo'
      | (PRepl l, _) =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2S bc rest K' (kkey K') okb same_of br2 PTLeaf
                                                else chain_slow bc (map sx1 rest) [K']
                                  | None => chain_slow bc (map sx1 rest) [K']
                                  end) l
          | None => chain_slow bc (map sx1 rest) l
          end
      end
  end.
Lemma map_sx1 : forall l : list kstx, map sx1 l = map fst (map fst l).
Proof. intros l. rewrite map_map. reflexivity. Qed.
Lemma chainK2S_eq : forall bc ksxs K ok okb same_of br2 mo,
  Forall KOK ksxs -> OKK ok K ->
  chainK2S bc ksxs K ok okb same_of br2 mo = chainK2M bc (map fst ksxs) K okb same_of br2 mo.
Proof.
  intros bc ksxs. induction ksxs as [|[[sx did] sk] rest IH]; intros K ok okb same_of br2 mo HF HO; [reflexivity|].
  inversion HF as [|? ? HK HR]; subst. cbn [chainK2S chainK2M map fst]. cbv zeta. rewrite prune1pcKF_eq.
  destruct (skipS ok (same_of (sx_bid sx)) sk) eqn:SK.
  - unfold skipS in SK. destruct (same_of (sx_bid sx)) eqn:SM; [|discriminate].
    destruct ok as [g1|]; [|discriminate]. destruct sk as [g2|]; [|discriminate].
    apply negb_true_iff in SK. apply Pos.eqb_neq in SK. unfold KOK, skey in HK. cbn [fst snd] in HK. cbn [OKK] in HO.
    rewrite (skip_keep bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K br2 g1 g2 HO (eq_sym HK) SK).
    apply IH; [exact HR | exact HO].
  - destruct (prune1pcKM bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) as [[|l] mo'];
      [apply IH; assumption|].
    rewrite map_sx1. destruct okb as [kb|]; [|reflexivity].
    apply flat_map_ext. intros K'. destruct (kbase K') as [kb'|]; [|reflexivity].
    destruct (expr_eqb kb' kb); [|reflexivity]. apply IH; [exact HR | apply OKK_kkey].
Qed.

Fixpoint mk_flS (g : gval) (ksxs : list kstx) : list (kstx * list kstx) :=
  match ksxs with
  | [] => []
  | ks :: rest => if verdict (sx1 ks) g then mk_flS g rest else (ks, rest) :: mk_flS g rest
  end.
Definition flprojS (p : kstx * list kstx) : stxd * list stxd := (fst (fst p), map fst (snd p)).
Lemma mk_flS_proj : forall g ksxs, map flprojS (mk_flS g ksxs) = mk_flM g (map fst ksxs).
Proof.
  intros g ksxs. induction ksxs as [|ks rest IH]; [reflexivity|]. cbn [mk_flS mk_flM map]. unfold sx1.
  destruct (verdict (fst (fst ks)) g); [exact IH|]. cbn [map]. rewrite IH. reflexivity.
Qed.
Lemma mk_flS_ok : forall g ksxs, Forall KOK ksxs -> Forall (fun p => KOK (fst p) /\ Forall KOK (snd p)) (mk_flS g ksxs).
Proof.
  intros g ksxs. induction ksxs as [|ks rest IH]; intros HF; [constructor|]. inversion HF as [|? ? HK HR]; subst.
  cbn [mk_flS]. destruct (verdict (sx1 ks) g); [apply IH; exact HR|]. constructor; [split; assumption | apply IH; exact HR].
Qed.
Fixpoint chainKFS (bc : bctx) (fl : list (kstx * list kstx)) (K : kentry) (ok : option positive) (okb : option expr)
         (same_of : positive -> bool) (br2 : option (Z * Z)) (mo : ptree bool) : list kentry :=
  match fl with
  | [] => [K]
  | (((sx, did), sk), rest) :: fl' =>
      let same := same_of (sx_bid sx) in
      if skipS ok same sk then chainKFS bc fl' K ok okb same_of br2 mo
      else
      match prune1pcKF bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K same br2 with
      | (PKeep, mo') => chainKFS bc fl' K ok okb same_of br2 mo'
      | (PRepl l, _) =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2S bc rest K' (kkey K') okb same_of br2 PTLeaf
                                                else chain_slow bc (map sx1 rest) [K']
                                  | None => chain_slow bc (map sx1 rest) [K']
                                  end) l
          | None => chain_slow bc (map sx1 rest) l
          end
      end
  end.
Lemma chainKFS_eq : forall bc fl K ok okb same_of br2 mo,
  Forall (fun p => KOK (fst p) /\ Forall KOK (snd p)) fl -> OKK ok K ->
  chainKFS bc fl K ok okb same_of br2 mo = chainKFM bc (map flprojS fl) K okb same_of br2 mo.
Proof.
  intros bc fl. induction fl as [|[[[sx did] sk] rest] fl' IH]; intros K ok okb same_of br2 mo HF HO; [reflexivity|].
  inversion HF as [|? ? [HK HRr] HR]; subst. cbn [fst snd] in HK, HRr.
  cbn [chainKFS chainKFM map flprojS fst snd]. cbv zeta. rewrite prune1pcKF_eq.
  destruct (skipS ok (same_of (sx_bid sx)) sk) eqn:SK.
  - unfold skipS in SK. destruct (same_of (sx_bid sx)) eqn:SM; [|discriminate].
    destruct ok as [g1|]; [|discriminate]. destruct sk as [g2|]; [|discriminate].
    apply negb_true_iff in SK. apply Pos.eqb_neq in SK. unfold KOK, skey in HK. cbn [fst snd] in HK. cbn [OKK] in HO.
    rewrite (skip_keep bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K br2 g1 g2 HO (eq_sym HK) SK).
    apply IH; [exact HR | exact HO].
  - destruct (prune1pcKM bc (sx_sp sx) did mo (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) as [[|l] mo'];
      [apply IH; assumption|].
    rewrite map_sx1. destruct okb as [kb|]; [|reflexivity].
    apply flat_map_ext. intros K'. destruct (kbase K') as [kb'|]; [|reflexivity].
    destruct (expr_eqb kb' kb); [|reflexivity]. apply chainK2S_eq; [exact HRr | apply OKK_kkey].
Qed.

Definition gflS : Type := (gval * list (kstx * list kstx))%type.
Definition mk_glS (bnds : gtab) (ksxs : list kstx) : ptree gflS := pt_map (fun g => (g, mk_flS g ksxs)) bnds.
Fixpoint entriesGS (bc : bctx) (ksxs : list kstx) (gl : ptree gflS) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKFS bc fl K (kkey K) okb same_of br2 PTLeaf
                             else chainK2S bc ksxs K (kkey K) okb same_of br2 PTLeaf
           | None => chainK2S bc ksxs K (kkey K) okb same_of br2 PTLeaf
           end
       | None => if inertb K then [K] else chainK2S bc ksxs K None None (fun _ => false) None PTLeaf
       end) ++ entriesGS bc ksxs gl rest irest
  | _, _ => []
  end.
Lemma entriesGS_eq : forall bc ksxs, Forall KOK ksxs -> forall bnds kn infos,
  entriesGS bc ksxs (mk_glS bnds ksxs) kn infos = entriesGM bc (map fst ksxs) (mk_glM bnds (map fst ksxs)) kn infos.
Proof.
  intros bc ksxs HF bnds kn. induction kn as [|K rest IH]; intros infos; [reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|]. cbn [entriesGS entriesGM]. rewrite IH. f_equal.
  destruct oi as [ei|].
  2:{ destruct (inertb K); [reflexivity|]. apply chainK2S_eq; [exact HF | exact I]. }
  unfold mk_glS, mk_glM. rewrite !pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply chainK2S_eq; [exact HF | apply OKK_kkey]].
  destruct (inb g ei); [|apply chainK2S_eq; [exact HF | apply OKK_kkey]].
  rewrite <- mk_flS_proj. apply chainKFS_eq; [apply mk_flS_ok; exact HF | apply OKK_kkey].
Qed.

Fixpoint stores_partS (bc : bctx) (ksxs : list kstx) : list kentry :=   (* [comment removed for export] *)
  match ksxs with
  | [] => []
  | ((sx, _), sk) :: newer =>
      stores_partS bc newer ++ chainK2S bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) sk (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) PTLeaf
  end.
Lemma stores_partS_eq : forall bc ksxs, Forall KOK ksxs -> stores_partS bc ksxs = stores_partM bc (map fst ksxs).
Proof.
  intros bc ksxs. induction ksxs as [|[[sx did] sk] newer IH]; intros HF; [reflexivity|].
  inversion HF as [|? ? HK HR]; subst. cbn [stores_partS stores_partM map fst]. rewrite (IH HR). f_equal.
  apply chainK2S_eq; [exact HR|]. unfold KOK, skey in HK. cbn [fst snd] in HK. subst sk.
  unfold OKK. destruct (fgkey (a_off (sx_a sx)) (sx_w sx)) as [g|] eqn:E; [|exact I].
  destruct (sx_a sx) as [b k]. exact E.
Qed.

Definition carryGS (prep : prepf) (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0, _) := mk_stxsL prep bc log nt_empty dt_empty in
  let ksxs := map (fun sd => (sd, skey sd)) sxs in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partS bc ksxs ++ entriesGS bc ksxs (mk_glS (gs_bnds gs) ksxs) kn infos.
Lemma carryGS_eq : forall tst bc log kn, carryGS (mk_sprep3G tst bc) bc log kn = carryGG tst bc log kn.
Proof.
  intros tst bc log kn. unfold carryGS, carryGG. rewrite mk_stxsL_eq.
  destruct (mk_stxsG tst bc log nt_empty dt_empty) as [[sxs t0] dt]. cbv zeta.
  destruct (scan_entries bc kn t0 gst_empty) as [[infos t1] gs].
  assert (HF : Forall KOK (map (fun sd : stxd => (sd, skey sd)) sxs)).
  { apply Forall_forall. intros p Hp. apply in_map_iff in Hp. destruct Hp as (sd & <- & _). reflexivity. }
  assert (HM : map fst (map (fun sd : stxd => (sd, skey sd)) sxs) = sxs) by (rewrite map_map; apply map_id).
  rewrite (stores_partS_eq bc _ HF), (entriesGS_eq bc _ HF), HM. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lin_range_shift : forall rng d ts c,
  lin_range rng (c + d) ts = match lin_range rng c ts with Some (lo, hi) => Some (lo + d, hi + d)%Z | None => None end.
Proof.
  intros rng d ts. induction ts as [|[k a] rest IH]; intros c; [reflexivity|].
  cbn [lin_range]. rewrite IH. destruct (rng a) as [[al ah]|]; [|reflexivity].
  destruct (lin_range rng c rest) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb 0 k); f_equal; f_equal; lia.
Qed.
Definition quickR (bc : bctx) (pos neg : xterms) : option Z :=
  if xt_nowrapB bc pos then if xt_nowrapB bc neg then
    match lin_range (erangeV bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) with
    | Some (lo, _) => Some lo
    | None => None
    end
  else None else None.
Lemma quick_ge0B_R : forall bc pos neg,
  quick_ge0B bc pos neg = match quickR bc pos neg with Some lo => Z.leb 0 lo | None => false end.
Proof.
  intros. unfold quick_ge0B, quickR. destruct (xt_nowrapB bc pos); [|reflexivity]. destruct (xt_nowrapB bc neg); [|reflexivity].
  destruct (lin_range (erangeV bc) (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg))) as [[lo hi]|]; reflexivity.
Qed.
Lemma quickR_shift_pos : forall bc b1 k1 r neg,
  quickR bc ((b1, k1) :: r) neg = match quickR bc ((b1, 0%Z) :: r) neg with Some lo => Some (lo + k1)%Z | None => None end.
Proof.
  intros. unfold quickR. cbn [xt_nowrapB xt_lin xt_const].
  destruct (lin_nowrapRB bc b1 && xt_nowrapB bc r)%bool; [|reflexivity]. destruct (xt_nowrapB bc neg); [|reflexivity].
  replace (fst (lin_of b1) + k1 + xt_const r - xt_const neg)%Z with (fst (lin_of b1) + 0 + xt_const r - xt_const neg + k1)%Z by lia.
  rewrite lin_range_shift.
  destruct (lin_range (erangeV bc) (fst (lin_of b1) + 0 + xt_const r - xt_const neg)
              (lsub_e (fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xt_lin r) (snd (lin_of b1))) (xt_lin neg))) as [[lo hi]|]; reflexivity.
Qed.
Lemma quickR_shift_neg : forall bc pos b1 k1 r,
  quickR bc pos ((b1, k1) :: r) = match quickR bc pos ((b1, 0%Z) :: r) with Some lo => Some (lo - k1)%Z | None => None end.
Proof.
  intros. unfold quickR. cbn [xt_nowrapB xt_lin xt_const].
  destruct (xt_nowrapB bc pos); [|reflexivity]. destruct (lin_nowrapRB bc b1 && xt_nowrapB bc r)%bool; [|reflexivity].
  replace (xt_const pos - (fst (lin_of b1) + k1 + xt_const r))%Z with (xt_const pos - (fst (lin_of b1) + 0 + xt_const r) + - k1)%Z by lia.
  rewrite lin_range_shift.
  destruct (lin_range (erangeV bc) (xt_const pos - (fst (lin_of b1) + 0 + xt_const r))
              (lsub_e (xt_lin pos) (fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xt_lin r) (snd (lin_of b1))))) as [[lo hi]|];
    [f_equal; lia | reflexivity].
Qed.
(* [comment removed for export] *)
Lemma side_testB_T : forall bc b1 k1 z1 c m,
  shares_var b1 (a_base c) = true -> (Z.leb 0 z1 && Z.ltb z1 two64)%bool = true ->
  quick_ge0B bc [(b1, k1)] [(a_base c, a_off c)] = true ->
  quick_ge0B bc [(a_base c, a_off c); (m, 0%Z)] [(b1, k1); (ELit z1, 0%Z)] = true ->
  side_testB bc b1 k1 (ELit z1) c m = (true, true).
Proof.
  intros bc b1 k1 z1 c m SV RG QA QB. unfold side_testB, sub_itv_xB, xinsideB. rewrite SV. unfold xinside0B.
  rewrite (quick_ge0B_ge0 _ _ _ QA), (quick_ge0B_ge0 _ _ _ QB). cbv zeta. rewrite RG.
  destruct (if (expr_eqb b1 (a_base c) && Z.leb (a_off c) k1)%bool then _ else false); reflexivity.
Qed.

Definition bounds : Type := (option Z * option (Z * Z))%type.
Definition IN_MAX : Z := 1048576%Z.
Definition mk_bounds (bc : bctx) (b1 : expr) (z1 : Z) (c : saddr) (m : expr) : bounds :=
  let ab := quickR bc [(b1, 0%Z); (ELit z1, 0%Z)] [(a_base c, a_off c); (m, 1%Z)] in
  (ab,
   if (match ab with Some lo0 => Z.ltb lo0 IN_MAX | None => true end) then
     if shares_var b1 (a_base c) then
       if (Z.leb 0 z1 && Z.ltb z1 two64)%bool then
         match quickR bc [(b1, 0%Z)] [(a_base c, a_off c)] with
         | Some la => match quickR bc [(a_base c, a_off c); (m, 0%Z)] [(b1, 0%Z); (ELit z1, 0%Z)] with
                      | Some lb => Some (la, lb)
                      | None => None
                      end
         | None => None
         end
       else None
     else None
   else None).
Definition BNDOK (bc : bctx) (b1 : expr) (z1 : Z) (c : saddr) (m : expr) (bd : bounds) : Prop :=
  fst bd = quickR bc [(b1, 0%Z); (ELit z1, 0%Z)] [(a_base c, a_off c); (m, 1%Z)] /\
  (forall la lb, snd bd = Some (la, lb) ->
     shares_var b1 (a_base c) = true /\ (Z.leb 0 z1 && Z.ltb z1 two64)%bool = true /\
     quickR bc [(b1, 0%Z)] [(a_base c, a_off c)] = Some la /\
     quickR bc [(a_base c, a_off c); (m, 0%Z)] [(b1, 0%Z); (ELit z1, 0%Z)] = Some lb).
Lemma mk_bounds_ok : forall bc b1 z1 c m, BNDOK bc b1 z1 c m (mk_bounds bc b1 z1 c m).
Proof.
  intros. unfold BNDOK, mk_bounds. cbv zeta. cbn [fst snd]. split; [reflexivity|]. intros la lb H.
  destruct (match quickR bc [(b1, 0%Z); (ELit z1, 0%Z)] [(a_base c, a_off c); (m, 1%Z)] with Some lo0 => Z.ltb lo0 IN_MAX | None => true end);
    [|discriminate].
  destruct (shares_var b1 (a_base c)); [|discriminate]. destruct (Z.leb 0 z1 && Z.ltb z1 two64)%bool; [|discriminate].
  destruct (quickR bc [(b1, 0%Z)] [(a_base c, a_off c)]) as [la'|]; [|discriminate].
  destruct (quickR bc [(a_base c, a_off c); (m, 0%Z)] [(b1, 0%Z); (ELit z1, 0%Z)]) as [lb'|]; [|discriminate].
  injection H as <- <-. auto.
Qed.
Definition side_testP (bc : bctx) (b1 : expr) (k1 : Z) (z1 : Z) (c : saddr) (m : expr) (bd : bounds) : bool * bool :=
  if (match fst bd with Some lo0 => Z.leb 0 (lo0 + k1) | None => false end) then (false, false)
  else if (match snd bd with Some (la, lb) => if Z.leb 0 (la + k1) then Z.leb 0 (lb - k1) else false | None => false end) then (true, true)
  else side_testB bc b1 k1 (ELit z1) c m.
Lemma side_testP_eq : forall bc b1 k1 z1 c m bd, BNDOK bc b1 z1 c m bd ->
  side_testP bc b1 k1 z1 c m bd = side_testS bc b1 k1 (ELit z1) c m.
Proof.
  intros bc b1 k1 z1 c m bd [HA HI]. unfold side_testP, side_testS, side_aboveB.
  rewrite quick_ge0B_R, quickR_shift_pos, <- HA.
  destruct (fst bd) as [lo0|].
  - destruct (Z.leb 0 (lo0 + k1)); [reflexivity|].
    destruct (snd bd) as [[la lb]|] eqn:SB; [|reflexivity]. destruct (HI la lb eq_refl) as (SV & RG & QA & QB).
    destruct (Z.leb 0 (la + k1)) eqn:E1; [|reflexivity]. destruct (Z.leb 0 (lb - k1)) eqn:E2; [|reflexivity].
    symmetry. apply side_testB_T; [exact SV | exact RG | |].
    + rewrite quick_ge0B_R, quickR_shift_pos, QA. exact E1.
    + rewrite quick_ge0B_R, quickR_shift_neg, QB. exact E2.
  - destruct (snd bd) as [[la lb]|] eqn:SB; [|reflexivity]. destruct (HI la lb eq_refl) as (SV & RG & QA & QB).
    destruct (Z.leb 0 (la + k1)) eqn:E1; [|reflexivity]. destruct (Z.leb 0 (lb - k1)) eqn:E2; [|reflexivity].
    symmetry. apply side_testB_T; [exact SV | exact RG | |].
    + rewrite quick_ge0B_R, quickR_shift_pos, QA. exact E1.
    + rewrite quick_ge0B_R, quickR_shift_neg, QB. exact E2.
Qed.

(* [comment removed for export] *)
Definition sident : Type := (saddr * expr * (positive * bounds))%type.
Definition key_eqb (c : saddr) (m : expr) (c' : saddr) (m' : expr) : bool := if saddr_eqb c c' then expr_eqb m m' else false.
Lemma key_eqb_eq : forall c m c' m', key_eqb c m c' m' = true -> c = c' /\ m = m'.
Proof.
  intros c m c' m' H. unfold key_eqb in H. destruct (saddr_eqb c c') eqn:E; [|discriminate].
  split; [exact (p_saddr_eqb_eq _ _ E) | exact (p_expr_eqb_eq _ _ H)].
Qed.
Lemma key_eqb_refl : forall c m, key_eqb c m c m = true.
Proof. intros [b k] m. unfold key_eqb, saddr_eqb. cbn [a_off a_base]. rewrite Z.eqb_refl, !p_expr_eqb_refl. reflexivity. Qed.
Lemma key_eqb_andb : forall c m c' m', (saddr_eqb c c' && expr_eqb m m')%bool = key_eqb c m c' m'.
Proof. intros. unfold key_eqb. destruct (saddr_eqb c c'); reflexivity. Qed.
Fixpoint ids_find (c : saddr) (m : expr) (l : list sident) : option (positive * bounds) :=
  match l with
  | [] => None
  | (c', m', x) :: rest => if key_eqb c m c' m' then Some x else ids_find c m rest
  end.

Definition pside : Type := (saddr * expr * option (positive * bounds))%type.
Definition pplan : Type := list (pside * pside).
Definition pstate : Type := (list sident * positive)%type.
Definition mk_pside (bc : bctx) (b1 : expr) (z1 : Z) (c : saddr) (m : expr) (st : pstate) : pside * pstate :=
  if side_cheap b1 c then ((c, m, None), st)
  else match ids_find c m (fst st) with
       | Some x => ((c, m, Some x), st)
       | None => let x := (snd st, mk_bounds bc b1 z1 c m) in ((c, m, Some x), ((c, m, x) :: fst st, Pos.succ (snd st)))
       end.
Fixpoint mk_plan (bc : bctx) (kn : list kentry) (b1 : expr) (z1 : Z) (st : pstate) : pplan * pstate :=
  match kn with
  | [] => ([], st)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(s2, st1) := mk_pside bc b1 z1 c2 m2 st in
      let '(s1, st2) := mk_pside bc b1 z1 c1 m1 st1 in
      let '(pl, st3) := mk_plan bc rest b1 z1 st2 in
      ((s1, s2) :: pl, st3)
  | _ :: rest => mk_plan bc rest b1 z1 st
  end.

(* [comment removed for export] *)
Definition side_memo2P (tstP : saddr -> expr -> bounds -> bool * bool) (memo : ptree (bool * bool)) (s : pside)
  : (bool * bool) * ptree (bool * bool) :=
  match s with
  | (_, _, None) => ((false, false), memo)
  | (c, m, Some (id, bd)) =>
      match pt_get memo id with
      | Some r => (r, memo)
      | None => let r := tstP c m bd in (r, pt_set id r memo)
      end
  end.
Fixpoint disj_sides3P (tstP : saddr -> expr -> bounds -> bool * bool) (pl : pplan) (memo : ptree (bool * bool))
  : list (saddr * expr) * list (saddr * expr) * ptree (bool * bool) * list bool :=
  match pl with
  | [] => ([], [], memo, [])
  | (s1, s2) :: rest =>
      let '(r, rx, memo1, mk) := disj_sides3P tstP rest memo in
      let '(t2, memo2) := side_memo2P tstP memo1 s2 in
      let '(t1, memo3) := side_memo2P tstP memo2 s1 in
      let c1m1 := fst s1 in let c2m2 := fst s2 in
      let r1 := if fst t2 then c1m1 :: r else r in
      let rx1 := if snd t2 then c1m1 :: rx else rx in
      (if fst t1 then c2m2 :: r1 else r1, if snd t1 then c2m2 :: rx1 else rx1, memo3,
       fst t1 :: snd t1 :: fst t2 :: snd t2 :: mk)
  end.

(* [comment removed for export] *)
Definition IDLT (T : list sident) (nx : positive) : Prop := forall c m id bd, ids_find c m T = Some (id, bd) -> (id < nx)%positive.
Definition IDINJ (T : list sident) : Prop :=
  forall c m c' m' id bd bd', ids_find c m T = Some (id, bd) -> ids_find c' m' T = Some (id, bd') -> c = c' /\ m = m'.
Definition BNDS (bc : bctx) (b1 : expr) (z1 : Z) (T : list sident) : Prop :=
  forall c m id bd, ids_find c m T = Some (id, bd) -> BNDOK bc b1 z1 c m bd.
Definition EXT (T T' : list sident) : Prop := forall c m x, ids_find c m T = Some x -> ids_find c m T' = Some x.
Definition STINV (bc : bctx) (b1 : expr) (z1 : Z) (st : pstate) : Prop :=
  IDLT (fst st) (snd st) /\ IDINJ (fst st) /\ BNDS bc b1 z1 (fst st).
Definition PSOK (b1 : expr) (T : list sident) (c : saddr) (m : expr) (s : pside) : Prop :=
  fst s = (c, m) /\ (if side_cheap b1 c then snd s = None else exists x, snd s = Some x /\ ids_find c m T = Some x).
Lemma EXT_refl : forall T, EXT T T. Proof. intros T c m x H. exact H. Qed.
Lemma EXT_trans : forall T1 T2 T3, EXT T1 T2 -> EXT T2 T3 -> EXT T1 T3. Proof. intros T1 T2 T3 H1 H2 c m x H. auto. Qed.
Lemma PSOK_ext : forall b1 T T' c m s, EXT T T' -> PSOK b1 T c m s -> PSOK b1 T' c m s.
Proof.
  intros b1 T T' c m s HE [H1 H2]. split; [exact H1|]. destruct (side_cheap b1 c); [exact H2|].
  destruct H2 as (x & Hx & HF). exists x. auto.
Qed.
Lemma mk_pside_ok : forall bc b1 z1 c m st s st',
  mk_pside bc b1 z1 c m st = (s, st') -> STINV bc b1 z1 st ->
  STINV bc b1 z1 st' /\ EXT (fst st) (fst st') /\ PSOK b1 (fst st') c m s.
Proof.
  intros bc b1 z1 c m [T nx] s st' H (HL & HI & HB). unfold mk_pside in H. cbn [fst snd] in *.
  destruct (side_cheap b1 c) eqn:SC.
  - injection H as <- <-. split; [split; [|split]; assumption|]. split; [apply EXT_refl|].
    split; [reflexivity|]. rewrite SC. reflexivity.
  - destruct (ids_find c m T) as [x|] eqn:F.
    + injection H as <- <-. split; [split; [|split]; assumption|]. split; [apply EXT_refl|].
      split; [reflexivity|]. rewrite SC. exists x. auto.
    + injection H as <- <-. cbn [fst snd].
      assert (NEW : forall c0 m0, ids_find c0 m0 ((c, m, (nx, mk_bounds bc b1 z1 c m)) :: T)
                                  = if key_eqb c0 m0 c m then Some (nx, mk_bounds bc b1 z1 c m) else ids_find c0 m0 T) by reflexivity.
      assert (OLD : forall c0 m0 x, ids_find c0 m0 T = Some x -> key_eqb c0 m0 c m = false).
      { intros c0 m0 x F0. destruct (key_eqb c0 m0 c m) eqn:E; [|reflexivity].
        destruct (key_eqb_eq _ _ _ _ E) as [-> ->]. congruence. }
      split; [split; [|split]|split].
      * intros c0 m0 id bd F0. rewrite NEW in F0. destruct (key_eqb c0 m0 c m).
        -- injection F0 as <- <-. apply Pos.lt_succ_diag_r.
        -- apply Pos.lt_lt_succ. exact (HL _ _ _ _ F0).
      * intros c0 m0 c0' m0' id bd bd' F0 F0'. rewrite NEW in F0, F0'.
        destruct (key_eqb c0 m0 c m) eqn:E0; destruct (key_eqb c0' m0' c m) eqn:E0'.
        -- destruct (key_eqb_eq _ _ _ _ E0) as [-> ->]. destruct (key_eqb_eq _ _ _ _ E0') as [-> ->]. auto.
        -- injection F0 as <- <-. pose proof (HL _ _ _ _ F0') as LT. exfalso. exact (Pos.lt_irrefl _ LT).
        -- injection F0' as <- <-. pose proof (HL _ _ _ _ F0) as LT. exfalso. exact (Pos.lt_irrefl _ LT).
        -- exact (HI _ _ _ _ _ _ _ F0 F0').
      * intros c0 m0 id bd F0. rewrite NEW in F0. destruct (key_eqb c0 m0 c m) eqn:E0.
        -- injection F0 as <- <-. destruct (key_eqb_eq _ _ _ _ E0) as [-> ->]. apply mk_bounds_ok.
        -- exact (HB _ _ _ _ F0).
      * intros c0 m0 x F0. rewrite NEW, (OLD _ _ _ F0). exact F0.
      * split; [reflexivity|]. rewrite SC. exists (nx, mk_bounds bc b1 z1 c m). split; [reflexivity|].
        rewrite NEW, key_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Definition REL (T : list sident) (mp : ptree (bool * bool)) (mg : smemo) : Prop :=
  forall c m id bd, ids_find c m T = Some (id, bd) -> pt_get mp id = side_find2B c m mg.
Lemma side_step_eq : forall bc b1 k1 z1 T c m s mp mg,
  IDINJ T -> BNDS bc b1 z1 T -> PSOK b1 T c m s -> REL T mp mg ->
  fst (side_memo2P (side_testP bc b1 k1 z1) mp s) = fst (side_memo2G (side_testS bc) b1 k1 (ELit z1) mg c m)
  /\ REL T (snd (side_memo2P (side_testP bc b1 k1 z1) mp s)) (snd (side_memo2G (side_testS bc) b1 k1 (ELit z1) mg c m)).
Proof.
  intros bc b1 k1 z1 T c m [[c' m'] o] mp mg HI HB [H1 H2] HR. cbn [fst snd] in H1, H2. injection H1 as -> ->.
  unfold side_memo2P, side_memo2G. destruct (side_cheap b1 c).
  - subst o. split; [reflexivity | exact HR].
  - destruct H2 as ([id bd] & -> & F). rewrite (HR _ _ _ _ F).
    destruct (side_find2B c m mg) as [r|]; [split; [reflexivity | exact HR]|].
    rewrite (side_testP_eq bc b1 k1 z1 c m bd (HB _ _ _ _ F)). cbn [fst snd]. split; [reflexivity|].
    intros c0 m0 id0 bd0 F0. cbn [side_find2B]. rewrite key_eqb_andb.
    destruct (key_eqb c0 m0 c m) eqn:E.
    + destruct (key_eqb_eq _ _ _ _ E) as [-> ->]. rewrite F in F0. injection F0 as <- <-. apply pt_gss.
    + rewrite pt_gso; [exact (HR _ _ _ _ F0)|]. intros ->.
      destruct (HI _ _ _ _ _ _ _ F0 F) as [-> ->]. rewrite key_eqb_refl in E. discriminate.
Qed.
Lemma mk_plan_ok : forall bc b1 k1 z1 kn st pl st',
  mk_plan bc kn b1 z1 st = (pl, st') -> STINV bc b1 z1 st ->
  STINV bc b1 z1 st' /\ EXT (fst st) (fst st') /\
  (forall T mp mg, EXT (fst st') T -> IDINJ T -> BNDS bc b1 z1 T -> REL T mp mg ->
     let '(d, dx, mg', mk) := disj_sides3G (side_testS bc) kn b1 k1 (ELit z1) mg in
     let '(d', dx', mp', mk') := disj_sides3P (side_testP bc b1 k1 z1) pl mp in
     d' = d /\ dx' = dx /\ mk' = mk /\ REL T mp' mg').
Proof.
  intros bc b1 k1 z1 kn. induction kn as [|K rest IH]; intros st pl st' H HS.
  - injection H as <- <-. split; [exact HS|]. split; [apply EXT_refl|]. intros T mp mg _ _ _ HR. cbn. auto.
  - destruct K as [? ? ?|? ?|? ? ?|? ?|? ?|? ? ?|? ?|c1 m1 c2 m2|? ? ?|? ?|? ?];
      try (cbn [mk_plan] in H; destruct (IH st pl st' H HS) as (A & B & C); split; [exact A|]; split; [exact B|];
           intros T mp mg HE HI HB HR; cbn [disj_sides3G]; exact (C T mp mg HE HI HB HR)).
    cbn [mk_plan] in H.
    destruct (mk_pside bc b1 z1 c2 m2 st) as [s2 st1] eqn:P2. destruct (mk_pside bc b1 z1 c1 m1 st1) as [s1 st2] eqn:P1.
    destruct (mk_plan bc rest b1 z1 st2) as [pl0 st3] eqn:PL. injection H as <- <-.
    destruct (mk_pside_ok _ _ _ _ _ _ _ _ P2 HS) as (S1 & E1 & K2).
    destruct (mk_pside_ok _ _ _ _ _ _ _ _ P1 S1) as (S2 & E2 & K1).
    destruct (IH st2 pl0 st3 PL S2) as (S3 & E3 & C).
    split; [exact S3|]. split; [exact (EXT_trans _ _ _ E1 (EXT_trans _ _ _ E2 E3))|].
    intros T mp mg HE HI HB HR. cbn [disj_sides3G disj_sides3P].
    specialize (C T mp mg HE HI HB HR).
    destruct (disj_sides3G (side_testS bc) rest b1 k1 (ELit z1) mg) as [[[d dx] mg1] mk].
    destruct (disj_sides3P (side_testP bc b1 k1 z1) pl0 mp) as [[[d' dx'] mp1] mk'].
    destruct C as (-> & -> & -> & R1).
    pose proof (PSOK_ext b1 _ T c2 m2 s2 (EXT_trans _ _ _ E2 (EXT_trans _ _ _ E3 HE)) K2) as K2'.
    pose proof (PSOK_ext b1 _ T c1 m1 s1 (EXT_trans _ _ _ E3 HE) K1) as K1'.
    destruct (side_step_eq bc b1 k1 z1 T c2 m2 s2 mp1 mg1 HI HB K2' R1) as [T2 R2].
    destruct (side_memo2P (side_testP bc b1 k1 z1) mp1 s2) as [t2' mp2].
    destruct (side_memo2G (side_testS bc) b1 k1 (ELit z1) mg1 c2 m2) as [t2 mg2]. cbn [fst snd] in T2, R2. subst t2'.
    destruct (side_step_eq bc b1 k1 z1 T c1 m1 s1 mp2 mg2 HI HB K1' R2) as [T1 R3].
    destruct (side_memo2P (side_testP bc b1 k1 z1) mp2 s1) as [t1' mp3].
    destruct (side_memo2G (side_testS bc) b1 k1 (ELit z1) mg2 c1 m1) as [t1 mg3]. cbn [fst snd] in T1, R3. subst t1'.
    cbv zeta. rewrite (proj1 K1'), (proj1 K2'). auto.
Qed.

(* [comment removed for export] *)
Definition pentry : Type := (option (Z * Z) * option Z * pplan)%type.
Definition ptab : Type := list (expr * Z * pentry).
Fixpoint ptab_find (tab : ptab) (b1 : expr) (z1 : Z) : option pentry :=
  match tab with
  | [] => None
  | (b', z', e) :: rest => if (if Z.eqb z1 z' then expr_eqb b1 b' else false) then Some e else ptab_find rest b1 z1
  end.
Definition mk_pentry (bc : bctx) (b1 : expr) (z1 : Z) : pentry :=
  (base_rangeB bc b1, xhiB bc (ELit z1), fst (mk_plan bc (bc_fk bc) b1 z1 ([], xH))).
Fixpoint mk_ptab (bc : bctx) (log : list sentry) (tab : ptab) : ptab :=
  match log with
  | [] => tab
  | SE a w _ :: rest =>
      let z1 := zofn w in
      mk_ptab bc rest (match ptab_find tab (a_base a) z1 with
                       | Some _ => tab
                       | None => (a_base a, z1, mk_pentry bc (a_base a) z1) :: tab
                       end)
  end.
Definition prepP (bc : bctx) (b1 : expr) (k1 : Z) (z1 : Z) (e : pentry) : sprep * list bool :=
  let '(rng, h1, pl) := e in
  let '(d, dx, _, mk) := disj_sides3P (side_testP bc b1 k1 z1) pl PTLeaf in
  (SPrep rng h1 d dx, mk).
Definition prepT (bc : bctx) (tab : ptab) : prepf :=
  fun b1 k1 n1 =>
    match n1 with
    | ELit z1 => match ptab_find tab b1 z1 with
                 | Some e => prepP bc b1 k1 z1 e
                 | None => mk_sprep3G (side_testS bc) bc b1 k1 n1
                 end
    | _ => mk_sprep3G (side_testS bc) bc b1 k1 n1
    end.
Definition PTABOK (bc : bctx) (tab : ptab) : Prop :=
  Forall (fun p => snd p = mk_pentry bc (fst (fst p)) (snd (fst p))) tab.
Lemma ptab_find_ok : forall bc tab b1 z1 e, PTABOK bc tab -> ptab_find tab b1 z1 = Some e -> e = mk_pentry bc b1 z1.
Proof.
  intros bc tab. induction tab as [|[[b' z'] e'] rest IH]; intros b1 z1 e H F; cbn [ptab_find] in F; [discriminate|].
  pose proof (Forall_inv H) as H1. pose proof (Forall_inv_tail H) as H2. cbn [fst snd] in H1.
  destruct (Z.eqb z1 z') eqn:EZ; [destruct (expr_eqb b1 b') eqn:E2|].
  - injection F as <-. apply p_expr_eqb_eq in E2. apply Z.eqb_eq in EZ. subst. reflexivity.
  - exact (IH b1 z1 e H2 F).
  - exact (IH b1 z1 e H2 F).
Qed.
Lemma mk_ptab_ok : forall bc log tab, PTABOK bc tab -> PTABOK bc (mk_ptab bc log tab).
Proof.
  intros bc log. induction log as [|[a w v] rest IH]; intros tab H; [exact H|].
  cbn [mk_ptab]. cbv zeta. apply IH. destruct (ptab_find tab (a_base a) (zofn w)); [exact H|].
  constructor; [reflexivity | exact H].
Qed.
Lemma prepP_eq : forall bc b1 k1 z1,
  prepP bc b1 k1 z1 (mk_pentry bc b1 z1) = mk_sprep3G (side_testS bc) bc b1 k1 (ELit z1).
Proof.
  intros bc b1 k1 z1. unfold prepP, mk_pentry, mk_sprep3G.
  destruct (mk_plan bc (bc_fk bc) b1 z1 ([], xH)) as [pl st'] eqn:PL. cbn [fst].
  assert (S0 : STINV bc b1 z1 ([], xH)).
  { split; [|split]; intros c m; intros; cbn [fst ids_find] in *; discriminate. }
  destruct (mk_plan_ok bc b1 k1 z1 (bc_fk bc) ([], xH) pl st' PL S0) as ((_ & HI & HB) & _ & C).
  specialize (C (fst st') PTLeaf [] (EXT_refl _) HI HB).
  assert (R0 : REL (fst st') PTLeaf []) by (intros c m id bd _; rewrite pt_get_leaf; reflexivity).
  specialize (C R0).
  destruct (disj_sides3G (side_testS bc) (bc_fk bc) b1 k1 (ELit z1) []) as [[[d dx] mg'] mk].
  destruct (disj_sides3P (side_testP bc b1 k1 z1) pl PTLeaf) as [[[d' dx'] mp'] mk'].
  destruct C as (-> & -> & -> & _). reflexivity.
Qed.
Lemma prepT_eq : forall bc tab, PTABOK bc tab -> prepT bc tab = mk_sprep3G (side_testS bc) bc.
Proof.
  intros bc tab HT. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1.
  apply functional_extensionality; intros n1. unfold prepT. destruct n1 as [z1| | | | | | |]; try reflexivity.
  destruct (ptab_find tab b1 z1) as [e|] eqn:F; [|reflexivity].
  rewrite (ptab_find_ok bc tab b1 z1 e HT F). apply prepP_eq.
Qed.

(* [comment removed for export] *)
Definition carryKS2 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _ :: _, [] => (carryGS (prepT bc (mk_ptab bc log [])) bc log kn, [], [])
  | _ :: _, _ :: _ => carryKM bc log kn hints
  end.
Lemma carryKS2_eq : forall bc log kn hints, carryKS2 bc log kn hints = carryKS bc log kn hints.
Proof.
  intros bc log kn hints. unfold carryKS2, carryKS. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|reflexivity].
  rewrite (prepT_eq bc _ (mk_ptab_ok bc (s :: older) [] (Forall_nil _))), carryGS_eq. reflexivity.
Qed.

End AX2C.
