(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec ShapeAlg AgentLib Spec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanNodesCanon AsanNodesRJoin AsanNodesWorld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.


Fixpoint eblob_free (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => eblob_free a && eblob_free b
  | EExt _ _ _ a => eblob_free a
  | EBlob _ _ _ _ => false
  end.
Definition saddr_bf (a : saddr) : bool := eblob_free (a_base a).
Definition kentry_bf (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_bf a && eblob_free v
  | KZero a n => saddr_bf a && eblob_free n
  | KBlob _ _ _ => false
  | KImg _ _ => true
  | KAlign e _ => eblob_free e
  | KRange e _ _ => eblob_free e
  | KWr a n => saddr_bf a && eblob_free n
  | KDisj a1 n1 a2 n2 => saddr_bf a1 && eblob_free n1 && saddr_bf a2 && eblob_free n2
  | KFill a n _ => saddr_bf a && eblob_free n
  | KUnk a n => saddr_bf a && eblob_free n
  end.
Definition pair_bf (p : expr * expr) : bool := eblob_free (fst p) && eblob_free (snd p).
(* [comment removed for export] *)
Definition acs_noblob (cs : acs) : bool :=
  forallb eblob_free (s_regs (a_ss cs))
  && forallb kentry_bf (kn cs)
  && forallb (fun m => eblob_free (am_base m) && eblob_free (am_len m)) (a_maps cs)
  && forallb pair_bf (a_vis cs) && forallb pair_bf (a_ghost cs)
  && eblob_free (a_brk cs)
  && match a_fd cs with FdStd => true | _ => false end.

Definition ev_same (E E' : env) : Prop := forall n, ev E n = ev E' n.

Lemma edenot_evsame : forall E E' e, ev_same E E' -> eblob_free e = true -> edenot E e = edenot E' e.
Proof.
  intros E E' e HS. induction e; cbn [eblob_free edenot]; intros H;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
    try reflexivity; try discriminate;
    repeat match goal with IH : ?b = true -> edenot E ?x = edenot E' ?x, Hb : ?b = true |- _ => rewrite (IH Hb); clear IH end;
    try reflexivity.
  apply HS.
Qed.

Lemma flat_map_ext_in {X Y} : forall (f g : X -> list Y) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  intros f g l. induction l as [|x l IH]; intros H; [reflexivity|]. cbn [flat_map].
  rewrite (H x (or_introl eq_refl)), IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.
Lemma existsb_ext_in {X} : forall (f g : X -> bool) l, (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  intros f g l. induction l as [|x l IH]; intros H; [reflexivity|]. cbn [existsb].
  rewrite (H x (or_introl eq_refl)), IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Section EvSame.
  Variables E E' : env.
  Hypothesis HS : ev_same E E'.

  Lemma uE_evsame : forall e, eblob_free e = true -> uE E' e = uE E e.
  Proof. intros e H. unfold uE. rewrite (edenot_evsame E E' e HS H). reflexivity. Qed.
  Lemma estart_evsame : forall a, saddr_bf a = true -> estart E' a = estart E a.
  Proof. intros [b o] H. unfold estart. cbn [a_base a_off]. rewrite (edenot_evsame E E' b HS H). reflexivity. Qed.
  Lemma adenot_evsame : forall a, saddr_bf a = true -> adenot E' a = adenot E a.
  Proof. intros [b o] H. unfold adenot. cbn [a_base a_off]. rewrite (edenot_evsame E E' b HS H). reflexivity. Qed.
  Lemma elenZ_evsame : forall n, eblob_free n = true -> elenZ E' n = elenZ E n.
  Proof. intros n H. unfold elenZ. rewrite (edenot_evsame E E' n HS H). reflexivity. Qed.
  Lemma flat_evsame : forall a z, saddr_bf a = true -> flat E' a z = flat E a z.
  Proof. intros a z H. unfold flat. rewrite (estart_evsame a H). reflexivity. Qed.

  Lemma kentry_ok_evsame : forall segs M K, kentry_bf K = true -> kentry_ok segs E M K -> kentry_ok segs E' M K.
  Proof.
    intros segs M K Hb HK. destruct K; cbn [kentry_bf] in Hb;
      repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
      cbn [kentry_ok] in *; try discriminate;
      rewrite ?flat_evsame, ?estart_evsame, ?adenot_evsame, ?elenZ_evsame by assumption;
      rewrite <- ?(edenot_evsame E E') by assumption; exact HK.
  Qed.

  Lemma know_ok_evsame : forall segs M k, forallb kentry_bf k = true -> know_ok segs E M k -> know_ok segs E' M k.
  Proof.
    intros segs M k Hb HK. induction HK as [|K r HK Hr IH]; [constructor|].
    cbn [forallb] in Hb. apply andb_prop in Hb as [H1 H2]. constructor; [apply kentry_ok_evsame; assumption | apply IH; exact H2].
  Qed.

  Lemma regs_ok_evsame : forall sr R, forallb eblob_free sr = true -> regs_ok E sr R -> regs_ok E' sr R.
  Proof.
    intros sr R Hb HR r. rewrite (HR r). apply edenot_evsame; [exact HS|].
    unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
    destruct (Nat.lt_ge_cases (ridx r) (length sr)) as [Hl|Hl].
    - exact (proj1 (forallb_forall _ _) Hb _ (nth_In sr (ELit 0) Hl)).
    - rewrite nth_overflow by exact Hl. reflexivity.
  Qed.

  Lemma amap_den_evsame : forall m, (eblob_free (am_base m) && eblob_free (am_len m))%bool = true -> amap_den E' m = amap_den E m.
  Proof.
    intros m H. apply andb_prop in H as [H1 H2]. unfold amap_den.
    rewrite !(edenot_evsame E E') by assumption. reflexivity.
  Qed.
  Lemma maps_den_evsame : forall ms, forallb (fun m => eblob_free (am_base m) && eblob_free (am_len m)) ms = true ->
    map (amap_den E') ms = map (amap_den E) ms.
  Proof.
    intros ms H. apply map_ext_in. intros m Hin. apply amap_den_evsame. exact (proj1 (forallb_forall _ _) H m Hin).
  Qed.

  Lemma maps_match_evsame : forall ms l, forallb (fun m => eblob_free (am_base m) && eblob_free (am_len m)) ms = true ->
    maps_match E ms l -> maps_match E' ms l.
  Proof.
    induction ms as [|m ms IH]; intros l Hb HM; [exact HM|].
    cbn [forallb] in Hb. apply andb_prop in Hb as [Hm Hms]. cbn [maps_match] in HM |- *.
    destruct (is_fog m).
    - destruct HM as [HM | (iv & l' & -> & Hsz & HM)]; [left; apply IH; assumption|].
      right. exists iv, l'. split; [reflexivity|]. split; [|apply IH; assumption].
      pose proof Hm as Hm'. apply andb_prop in Hm' as [_ H2]. rewrite uE_evsame by assumption. exact Hsz.
    - destruct HM as (l' & -> & HM). exists l'. split; [|apply IH; assumption]. rewrite (amap_den_evsame m Hm). reflexivity.
  Qed.
  Lemma in_ghost_evsame : forall cs z, forallb pair_bf (a_ghost cs) = true -> in_ghost E' cs z = in_ghost E cs z.
  Proof.
    intros cs z H. unfold in_ghost. apply existsb_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. unfold pair_bf in Hp. apply andb_prop in Hp as [H1 H2].
    rewrite !uE_evsame by assumption. reflexivity.
  Qed.
  Lemma allow1_evsame : forall A p, pair_bf p = true -> allow1 A E' p = allow1 A E p.
  Proof.
    intros A p H. unfold pair_bf in H. apply andb_prop in H as [H1 H2]. unfold allow1, APS.sh_lo, APS.sh_hi.
    rewrite !uE_evsame by assumption. reflexivity.
  Qed.
  Lemma allowA_evsame : forall A cs, forallb pair_bf (a_vis cs) = true -> forallb pair_bf (a_ghost cs) = true ->
    allowA A E' cs = allowA A E cs.
  Proof.
    intros A cs H1 H2. unfold allowA. apply flat_map_ext_in. intros p Hin. apply allow1_evsame.
    apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) H1 p Hin) | exact (proj1 (forallb_forall _ _) H2 p Hin)].
  Qed.
  Lemma in_vis_evsame : forall cs z, forallb pair_bf (a_vis cs) = true -> in_vis E' cs z = in_vis E cs z.
  Proof.
    intros cs z H. unfold in_vis. apply existsb_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. unfold pair_bf in Hp. apply andb_prop in Hp as [H1 H2].
    rewrite !uE_evsame by assumption. reflexivity.
  Qed.
  Lemma in_sh_evsame : forall A cs z, forallb pair_bf (a_vis cs) = true -> in_sh A E' cs z = in_sh A E cs z.
  Proof.
    intros A cs z H. unfold in_sh. apply existsb_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. unfold pair_bf in Hp. apply andb_prop in Hp as [H1 H2].
    unfold APS.sh_lo, APS.sh_hi. rewrite !uE_evsame by assumption. reflexivity.
  Qed.
End EvSame.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition content_of (argv : list (list byte)) (fs : Fs.Fs) : list byte :=
  match argv with
  | [_; p] => match fs_lookup fs p with Some c => c | None => [] end
  | _ => []
  end.

(* [comment removed for export] *)
Definition reblob (E : env) (argv : list (list byte)) (c : list byte) : env :=
  Env (ev E) (fun k => if Nat.eqb k 1 then nth 0 argv [] else if Nat.eqb k 2 then nth 1 argv []
                      else if Nat.leb 8 k then chunk (k - 8) c else eb E k).

Lemma reblob_evsame : forall E argv c, ev_same E (reblob E argv c).
Proof. intros E argv c n. reflexivity. Qed.

Section Main.
  Variables (segs : list Segment) (A : atable) (ph : PhdrInfo).
  Variables (sp : word) (rdraw : EntryDraw) (* [comment removed for export] *).
  Variables (brk0 : word) (argv envp : list (list byte)).
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable c : list byte.

  (* [comment removed for export] *)
  Definition SINVm (E : env) (M : word -> option byte) : Prop :=
    SINV0 ph sp rdraw brk0 argv envp uid hw E M /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv []
    /\ forall j, eb E (8 + j)%nat = chunk j c.

  Lemma SINVm_SINV0 : forall E M, SINVm E M -> SINV0 ph sp rdraw brk0 argv envp uid hw E M.
  Proof. intros E M [H _]. exact H. Qed.

  Lemma SINVm_frame : forall E M M', (forall a, argH0 ph sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINVm E M -> SINVm E M'.
  Proof. intros E M M' Hf (H0 & H1 & H2 & H3). split; [eapply SINV0_frame; eassumption | auto]. Qed.

  Lemma SINVm_agree : forall E E' M, env_agree NX0 E E' -> SINVm E M -> SINVm E' M.
  Proof.
    intros E E' M Hag (H0 & H1 & H2 & H3). pose proof Hag as [_ Heb]. split; [eapply SINV0_agree; eassumption|].
    rewrite <- Heb. auto.
  Qed.

  Lemma SINVm_reblob : forall E M, SINV0 ph sp rdraw brk0 argv envp uid hw E M -> SINVm (reblob E argv c) M.
  Proof.
    intros E M [Hev HM]. split; [split; [exact Hev | exact HM]|].
    split; [reflexivity|]. split; [reflexivity|]. intros j. cbn [reblob eb].
    destruct (Nat.eqb_spec (8 + j) 1); [lia|]. destruct (Nat.eqb_spec (8 + j) 2); [lia|].
    destruct (Nat.leb_spec 8 (8 + j)); [|lia]. f_equal. lia.
  Qed.

  Lemma hid_reblob : forall E cs model,
    forallb pair_bf (a_vis cs) = true ->
    hid A (argH0 ph sp rdraw argv envp uid hw) (reblob E argv c) cs model = hid A (argH0 ph sp rdraw argv envp uid hw) E cs model.
  Proof.
    intros E cs model Hv. apply functional_extensionality. intros a. unfold hid, vis, APS.in_allow.
    rewrite (in_vis_evsame E (reblob E argv c) (reblob_evsame E argv c) cs _ Hv).
    rewrite (in_sh_evsame E (reblob E argv c) (reblob_evsame E argv c) A cs _ Hv). reflexivity.
  Qed.

  Theorem cs_ok_reblob : forall LIMIT LINV FS0 E cs R FULL model,
    acs_noblob cs = true ->
    cs_ok segs A LIMIT (SINV0 ph sp rdraw brk0 argv envp uid hw) (argH0 ph sp rdraw argv envp uid hw) LINV FS0 E cs R FULL model ->
    cs_ok segs A LIMIT SINVm (argH0 ph sp rdraw argv envp uid hw) LINV FS0 (reblob E argv c) cs R FULL model.
  Proof.
    intros LIMIT LINV FS0 E cs R FULL model Hnb HC.
    unfold acs_noblob in Hnb.
    apply andb_prop in Hnb as [Hnb Hfd]. apply andb_prop in Hnb as [Hnb Hbrk]. apply andb_prop in Hnb as [Hnb Hgh].
    apply andb_prop in Hnb as [Hnb Hvis]. apply andb_prop in Hnb as [Hnb Hmaps]. apply andb_prop in Hnb as [Hregs Hkn].
    pose proof (reblob_evsame E argv c) as HS. set (E' := reblob E argv c) in *.
    destruct HC as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 fholes f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 flinv].
    constructor.
    - eapply regs_ok_evsame; [exact HS | exact Hregs | exact f1].
    - exact f2.
    - unfold Mr. unfold E'. rewrite (hid_reblob E cs model Hvis). eapply know_ok_evsame; [exact HS | exact Hkn | exact f3].
    - exact f4.
    - destruct (a_fd cs); [exact f5 | discriminate | discriminate].
    - exact f6.
    - exact f7.
    - exact f8.
    - exact f9.
    - apply (maps_match_evsame E E' HS _ _ Hmaps). exact f10.
    - (* [comment removed for export] *)
      apply Forall_forall. intros m Hin Hh. pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [Hm1 Hm2].
      unfold APS.uE. rewrite <- !(edenot_evsame E E') by assumption. exact (proj1 (Forall_forall _ _) fholes m Hin Hh).
    - exact f11.
    - exact f12.
    - exact f13.
    - exact f14.
    - (* [comment removed for export] *) rewrite <- (edenot_evsame E E' e_sp0 HS eq_refl). exact f15.
    - exact f16.
    - apply Forall_forall. intros m Hin Hk. rewrite (amap_den_evsame E E' HS m (proj1 (forallb_forall _ _) Hmaps m Hin)).
      exact (proj1 (Forall_forall _ _) f17 m Hin Hk).
    - apply Forall_forall. intros m Hin Hk a. pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [Hm1 Hm2].
      rewrite <- !(edenot_evsame E E') by assumption. exact (proj1 (Forall_forall _ _) f18 m Hin Hk a).
    - exact f19.
    - rewrite <- (edenot_evsame E E') by assumption. exact f20.
    - exact f21.
    - exact f22.
    - rewrite (allowA_evsame E E' HS A cs Hvis Hgh). exact f23.
    - rewrite (allowA_evsame E E' HS A cs Hvis Hgh). exact f24.
    - unfold E'. rewrite (hid_reblob E cs model Hvis). intros a H1 H2 H3 H4 H5. rewrite (in_ghost_evsame E (reblob E argv c) (reblob_evsame E argv c) cs _ Hgh) in H5. exact (f25 a H1 H2 H3 H4 H5).
    - apply SINVm_reblob. exact f26.
    - exact flinv.
  Qed.
End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive qty : Type :=
| QArgc     (* [comment removed for export] *)
| QL0       (* [comment removed for export] *)
| QL1       (* [comment removed for export] *)
| QLook     (* [comment removed for export] *)
| QFlen     (* [comment removed for export] *)
| QCfgLen   (* [comment removed for export] *)
| QCmod     (* [comment removed for export] *)
| QCnt      (* [comment removed for export] *)
| QRoom.    (* [comment removed for export] *)

Definition qidx (q : qty) : nat :=
  match q with QArgc => 0 | QL0 => 1 | QL1 => 2 | QLook => 3 | QFlen => 4 | QCfgLen => 5 | QCmod => 6 | QCnt => 7 | QRoom => 8 end%nat.
Definition qty_eqb (a b : qty) : bool := Nat.eqb (qidx a) (qidx b).
Lemma qty_eqb_eq : forall a b, qty_eqb a b = true <-> a = b.
Proof. intros a b. unfold qty_eqb. rewrite Nat.eqb_eq. destruct a, b; cbn; split; congruence. Qed.

(* [comment removed for export] *)
Definition class : Type := list (qty * Z * Z).

Definition qlook (argv : list (list byte)) (fs : Fs.Fs) : Z :=
  match argv with
  | [_; p] => if (4096 <=? length p)%nat then 1
              else if list_byte_eqb p [] then 2
              else if list_byte_eqb p dot_path then 3
              else match fs_lookup fs p with None => 2 | Some _ => 4 end
  | _ => 0
  end.
(* [comment removed for export] *)
Definition bz (i : nat) (c : list byte) : Z := ION.hbyte i c.
Definition cfglen (c : list byte) : Z := ION.cfglen c.

Definition qval (q : qty) (argv : list (list byte)) (fs : Fs.Fs) : Z :=
  let c := content_of argv fs in
  match q with
  | QArgc => Z.of_nat (length argv)
  | QL0 => Z.of_nat (length (nth 0 argv []))
  | QL1 => Z.of_nat (length (nth 1 argv []))
  | QLook => qlook argv fs
  | QFlen => flen c
  | QCfgLen => cfglen c
  | QCmod => ION.cmod c
  | QCnt => bz 1 c / 128
  | QRoom => ION.room c
  end.

Definition in_class (C : class) (argv : list (list byte)) (fs : Fs.Fs) : bool :=
  forallb (fun t : qty * Z * Z => let '(q, lo, hi) := t in (lo <=? qval q argv fs) && (qval q argv fs <=? hi)) C.

(* [comment removed for export] *)
Definition QMIN : Z := - 2 ^ 16.
Definition QMAX : Z := 2 ^ 27.

(* [comment removed for export] *)
Definition cbounds (C : class) (q : qty) : Z * Z :=
  fold_left (fun acc (t : qty * Z * Z) => let '(q', lo, hi) := t in
               if qty_eqb q q' then (Z.max (fst acc) lo, Z.min (snd acc) hi) else acc) C (QMIN, QMAX).

Lemma in_class_app : forall C1 C2 argv fs, in_class (C1 ++ C2) argv fs = (in_class C1 argv fs && in_class C2 argv fs)%bool.
Proof. intros. unfold in_class. apply forallb_app. Qed.

Lemma cbounds_sound_gen : forall C q argv fs acc,
  in_class C argv fs = true -> fst acc <= qval q argv fs <= snd acc ->
  fst (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo, hi) := t in
         if qty_eqb q q' then (Z.max (fst acc) lo, Z.min (snd acc) hi) else acc) C acc) <= qval q argv fs
  <= snd (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo, hi) := t in
         if qty_eqb q q' then (Z.max (fst acc) lo, Z.min (snd acc) hi) else acc) C acc).
Proof.
  intros C q argv fs. induction C as [|[[q' lo] hi] C IH]; intros acc HC Hacc; [exact Hacc|].
  cbn [fold_left]. unfold in_class in HC. cbn [forallb] in HC. apply andb_prop in HC as [H1 H2].
  apply IH; [exact H2|]. destruct (qty_eqb q q') eqn:Hq; [|exact Hacc].
  apply qty_eqb_eq in Hq. subst q'. apply andb_prop in H1 as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb.
  cbn [fst snd]. lia.
Qed.

Lemma cbounds_sound : forall C q argv fs,
  in_class C argv fs = true -> QMIN <= qval q argv fs <= QMAX ->
  fst (cbounds C q) <= qval q argv fs <= snd (cbounds C q).
Proof. intros C q argv fs HC HB. unfold cbounds. apply cbounds_sound_gen; [exact HC | exact HB]. Qed.

(* [comment removed for export] *)
Inductive ctree : Type :=
| CLeaf (p : plan)
| CSplit (q : qty) (mid : Z) (le gt : ctree).     (* [comment removed for export] *)

Section Tree.
  Variable chk : class -> plan -> cres.
  Variable sok : class -> shape -> bool.

  Fixpoint tree_ok (C : class) (t : ctree) : bool :=
    match t with
    | CLeaf p => match chk C p with COk s => sok C s | CErr _ _ _ => false end
    | CSplit q mid le gt => tree_ok (C ++ [(q, QMIN, mid)]) le && tree_ok (C ++ [(q, mid + 1, QMAX)]) gt
    end.

  Lemma tree_ok_split : forall C q mid le gt,
    tree_ok (C ++ [(q, QMIN, mid)]) le = true -> tree_ok (C ++ [(q, mid + 1, QMAX)]) gt = true ->
    tree_ok C (CSplit q mid le gt) = true.
  Proof. intros C q mid le gt H1 H2. cbn [tree_ok]. rewrite H1, H2. reflexivity. Qed.

  Lemma tree_ok_leaf_ok : forall C p s, chk C p = COk s -> sok C s = true -> tree_ok C (CLeaf p) = true.
  Proof. intros C p s H1 H2. cbn [tree_ok]. rewrite H1. exact H2. Qed.

  (* [comment removed for export] *)
  Lemma tree_ok_leaf : forall t C argv fs,
    tree_ok C t = true -> in_class C argv fs = true -> (forall q, QMIN <= qval q argv fs <= QMAX) ->
    exists C' p s, in_class C' argv fs = true /\ chk C' p = COk s /\ sok C' s = true.
  Proof.
    induction t as [p|q mid le IHle gt IHgt]; intros C argv fs HT HC HB; cbn [tree_ok] in HT.
    - destruct (chk C p) as [s|] eqn:Hc; [|discriminate]. exists C, p, s. auto.
    - apply andb_prop in HT as [H1 H2]. pose proof (HB q) as Hq.
      destruct (Z.leb_spec (qval q argv fs) mid).
      + apply (IHle _ argv fs H1); [|exact HB]. rewrite in_class_app, HC. cbn. apply andb_true_intro; split; [|reflexivity].
        apply andb_true_intro; split; apply Z.leb_le; lia.
      + apply (IHgt _ argv fs H2); [|exact HB]. rewrite in_class_app, HC. cbn. apply andb_true_intro; split; [|reflexivity].
        apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.
End Tree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition clamp (b : Z * Z) (lo hi : Z) : Z * Z := (Z.max (fst b) lo, Z.min (snd b) hi).
(* [comment removed for export] *)
Definition look_of (C : class) : Z := let b := cbounds C QLook in if fst b =? snd b then fst b else (-1).
(* [comment removed for export] *)
Definition look_L1 (v : Z) : Z * Z :=
  if v =? 1 then (4096, 131071) else if v =? 2 then (0, 4095) else if v =? 3 then (1, 1) else if v =? 4 then (1, 4095) else (0, 131071).

Definition facts_of_class (C : class) : list kentry :=
  let look := look_of C in
  let a := clamp (cbounds C QArgc) 1 1024 in
  let a := if ((1 <=? look) && (look <=? 4))%bool then clamp a 2 2 else a in
  let l0 := clamp (cbounds C QL0) 0 131071 in
  let l1 := clamp (clamp (cbounds C QL1) 0 131071) (fst (look_L1 look)) (snd (look_L1 look)) in
  [KRange (EVar V_ARGC) (fst a) (snd a); KRange (EVar V_L0) (fst l0) (snd l0); KRange (EVar V_L1) (fst l1) (snd l1)].

(* [comment removed for export] *)
Definition JB : nat := 8.

(* [comment removed for export] *)
Definition b1s_of (C : class) : option (Z * Z) :=
  let cnt := cbounds C QCnt in
  if 1 <=? fst cnt then Some (2 ^ 63, 2 ^ 64 - 1) else if snd cnt <=? 0 then Some (0, 2 ^ 63 - 1) else None.
(* [comment removed for export] *)

Definition iotab_of (C : class) : ION.iotab :=
  let look := look_of C in
  let f := clamp (cbounds C QFlen) 0 (2 ^ 26) in
  let r := cbounds C QRoom in
  ION.IOT (if look =? 1 then ION.OTooLong else if look =? 2 then ION.ONoEnt else if look =? 3 then ION.ODir
           else if look =? 4 then ION.OFile (fst f) (snd f) else ION.ONone) JB
          (Some (clamp (cbounds C QCfgLen) 0 32767))
          (Some (fst r, Z.min (snd r) (2 ^ 26)))       (* [comment removed for export] *)
          (Some (clamp (cbounds C QCmod) 0 3))
          (b1s_of C).

(* [comment removed for export] *)
Definition H_class_prop (T : ION.iotab) (argv : list (list byte)) (FS0 : Fs.Fs) (SINV : env -> (word -> option byte) -> Prop) : Prop :=
  match ION.io_open T with
  | ION.ONone => True
  | ION.OTooLong => (4096 <= length (nth 1 argv []))%nat
  | ION.ONoEnt => nth 1 argv [] = [] \/ (nth 1 argv [] <> Uapi.dot_path /\ (length (nth 1 argv []) <= 4095)%nat /\ fs_lookup FS0 (nth 1 argv []) = None)
  | ION.ODir => nth 1 argv [] = Uapi.dot_path
  | ION.OFile lo hi => exists c, nth 1 argv [] <> [] /\ nth 1 argv [] <> Uapi.dot_path /\ (length (nth 1 argv []) <= 4095)%nat /\ fs_lookup FS0 (nth 1 argv []) = Some c
                   /\ lo <= flen c <= hi
                   /\ (forall E M, SINV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (ION.io_blob T + j)%nat = chunk j c)
                   /\ ION.hdr_ok T c
  end.

(* [comment removed for export] *)
Section Hooks.
  Variables (segs : list Segment) (A : atable) (nx0 : nat) (RP : RPN.rptab) (T : ION.iotab).
  Definition XNm (id : nat) (args : list expr) (cs : acs) : option acs :=
    if (id <? 10)%nat then AN.xn segs A nx0 id args cs
    else if (id <? 100)%nat then ION.xn segs A T id args cs
    else if (id <? 110)%nat then RPN.xn segs A nx0 RP id args cs
    else if (id =? 113)%nat then CAN.xn A args cs      (* [comment removed for export] *)
    else if (200 <=? id)%nat then
      if (if (id =? 215)%nat then true else (id <=? 205)%nat)
      then XRJ.xn segs A nx0 id args cs                (* [comment removed for export] *)
      else XWD.xn nx0 AsanInit.LIMIT id args cs        (* [comment removed for export] *)
    else None.
  Definition XEm (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := AN.xe segs A nx0 id args cs.
  Definition XBm (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := ION.xb segs nx0 T id args cs.
End Hooks.
(* [comment removed for export] *)
Definition HS_none (h : nat) : option acs := None.
Definition HOLES0 (h : nat) (E : env) (fs : Fs.Fs) : TSet := t_nil.

(* [comment removed for export] *)

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq. split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H as -> ->. auto.
Qed.

Lemma bz_range : forall i c, 0 <= bz i c < 256.
Proof.
  intros i c. unfold bz, ION.hbyte. pose proof (bv_unsigned_in_range _ (nth i c (Z_to_bv 8 0))) as H.
  change (bv_modulus 8) with 256 in H. lia.
Qed.
Lemma cfglen_range : forall c, 0 <= cfglen c < 32768.
Proof. intros c. unfold cfglen, ION.cfglen. apply Z.mod_pos_bound. lia. Qed.
Lemma room_eq : forall c, ION.room c = flen c - 6 - cfglen c.
Proof. intros c. reflexivity. Qed.
Lemma cmod_eq : forall c, ION.cmod c = bz 2 c mod 4.
Proof. intros c. reflexivity. Qed.
Lemma flen_range : forall c, 0 <= flen c <= 2 ^ 26.
Proof. intros c. unfold flen. lia. Qed.

(* [comment removed for export] *)
Lemma qlook_cases : forall argv fs,
  match argv with
  | [_; p] =>
      (qlook argv fs = 1 /\ (4096 <= length p)%nat)
      \/ (qlook argv fs = 2 /\ (length p < 4096)%nat /\ (p = [] \/ (p <> Uapi.dot_path /\ fs_lookup fs p = None)))
      \/ (qlook argv fs = 3 /\ p = Uapi.dot_path)
      \/ (qlook argv fs = 4 /\ p <> [] /\ p <> Uapi.dot_path /\ (length p < 4096)%nat /\ exists c, fs_lookup fs p = Some c /\ content_of argv fs = c)
  | _ => qlook argv fs = 0
  end.
Proof.
  intros argv fs. destruct argv as [|a0 [|p [|x r]]]; try reflexivity.
  unfold qlook, content_of. destruct (Nat.leb_spec 4096 (length p)) as [Hl|Hl]; [left; auto|]. right.
  destruct (list_byte_eqb p []) eqn:He.
  - apply list_byte_eqb_eq in He. left. subst p. cbn [length]. repeat split; [lia | left; reflexivity].
  - assert (Hne : p <> []) by (intros HH; apply (proj2 (list_byte_eqb_eq _ _)) in HH; congruence).
    destruct (list_byte_eqb p dot_path) eqn:Hd.
    + apply list_byte_eqb_eq in Hd. right; left. auto.
    + assert (Hnd : p <> Uapi.dot_path) by (intros HH; apply (proj2 (list_byte_eqb_eq _ _)) in HH; change dot_path with Uapi.dot_path in Hd; congruence).
      destruct (fs_lookup fs p) as [c|] eqn:Hlk.
      * right; right. repeat split; auto. exists c. auto.
      * left. repeat split; auto.
Qed.

Section ClassSound.
  Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (* [comment removed for export] *).
  Variables (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream).
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  Let argc := Z.of_nat (length argv).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).

  Lemma argc_range : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma L0_range' : 0 <= L0 <= 131071.
  Proof. unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. Qed.
  Lemma L1_range' : 0 <= L1 <= 131071.
  Proof. exact (L1_range ph sp rdraw argv envp uid hw Hva). Qed.
  Lemma qlook_range : 0 <= qlook argv fs <= 4.
  Proof.
    pose proof (qlook_cases argv fs) as Q. destruct argv as [|a0 [|p [|x r]]]; try (rewrite Q; lia).
    destruct Q as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; lia.
  Qed.

  Lemma qval_bounds : forall q, QMIN <= qval q argv fs <= QMAX.
  Proof.
    pose proof argc_range. pose proof L0_range'. pose proof L1_range'. pose proof qlook_range.
    pose proof (cfglen_range (content_of argv fs)). pose proof (flen_range (content_of argv fs)).
    pose proof (bz_range 2 (content_of argv fs)). pose proof (bz_range 1 (content_of argv fs)).
    pose proof (Z.mod_pos_bound (bz 2 (content_of argv fs)) 4 ltac:(lia)).
    assert (0 <= bz 1 (content_of argv fs) / 128 <= 1).
    { split; [apply Z.div_pos; lia |]. assert (bz 1 (content_of argv fs) / 128 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (room_eq (content_of argv fs)). pose proof (cmod_eq (content_of argv fs)).
    unfold QMIN, QMAX. intros q; destruct q; cbn [qval]; unfold argc, L0, L1 in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma look_of_sound : forall C, in_class C argv fs = true -> 0 <= look_of C -> look_of C = qlook argv fs.
  Proof.
    intros C HC Hnn. unfold look_of in *.
    pose proof (cbounds_sound C QLook argv fs HC (qval_bounds QLook)) as B. cbn [qval] in B.
    destruct (Z.eqb_spec (fst (cbounds C QLook)) (snd (cbounds C QLook))); lia.
  Qed.

  Lemma look_L1_sound : forall v, (v = qlook argv fs \/ v = -1) -> fst (look_L1 v) <= L1 <= snd (look_L1 v) /\ (1 <= v <= 4 -> argc = 2).
  Proof.
    intros v Hv. pose proof L1_range' as HL1. pose proof (qlook_cases argv fs) as Q. unfold look_L1.
    destruct Hv as [->| ->]; [|cbn; lia].
    destruct argv as [|a0 [|p [|x r]]]; try (rewrite Q; cbn; lia).
    unfold L1, argc in *. cbn [nth length] in *.
    destruct Q as [[-> Hl]|[[-> [Hl _]]|[[-> Hp]|[-> (Hne & _ & Hl & _)]]]]; cbn; try lia.
    - rewrite Hp. cbn. lia.
    - split; [|lia]. destruct p; [congruence|]. cbn [length] in *. clear -Hl. lia.
  Qed.

  Theorem facts_of_class_sound : forall segs C E M,
    in_class C argv fs = true -> (forall n, (n < 8)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) ->
    know_ok segs E M (facts_of_class C).
  Proof.
    intros segs C E M HC Hev.
    pose proof (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & UA & _ & UL0 & _).
    pose proof (uE0_L1 ph sp rdraw brk0 argv envp uid hw Hva) as UL1.
    assert (HV : forall n, (n < 8)%nat -> uE E (EVar n) = uE (E0 ph sp rdraw brk0 argv envp uid hw) (EVar n)).
    { intros n Hn. unfold uE. cbn [edenot]. rewrite (Hev n Hn). reflexivity. }
    pose proof argc_range as HA. pose proof L0_range' as HL0. pose proof L1_range' as HL1.
    pose proof (cbounds_sound C QArgc argv fs HC (qval_bounds QArgc)) as BA.
    pose proof (cbounds_sound C QL0 argv fs HC (qval_bounds QL0)) as B0.
    pose proof (cbounds_sound C QL1 argv fs HC (qval_bounds QL1)) as B1. cbn [qval] in BA, B0, B1.
    assert (HLK : look_of C = qlook argv fs \/ look_of C = -1).
    { unfold look_of. destruct (Z.eqb_spec (fst (cbounds C QLook)) (snd (cbounds C QLook))); [|right; reflexivity].
      left. pose proof (look_of_sound C HC) as X. unfold look_of in X. rewrite (proj2 (Z.eqb_eq _ _) e) in X.
      apply X. pose proof (cbounds_sound C QLook argv fs HC (qval_bounds QLook)) as BL. pose proof qlook_range. cbn [qval] in BL. lia. }
    pose proof (look_L1_sound (look_of C) HLK) as [LL LA].
    unfold facts_of_class, know_ok. unfold uE in UA, UL0, UL1. cbn [edenot] in UA, UL0, UL1.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok edenot];
      rewrite ?(Hev V_ARGC ltac:(cbv; lia)), ?(Hev V_L0 ltac:(cbv; lia)), ?(Hev V_L1 ltac:(cbv; lia)); rewrite ?UA, ?UL0, ?UL1.
    - unfold clamp. cbn [fst snd].
      destruct ((1 <=? look_of C) && (look_of C <=? 4))%bool eqn:Hlk; cbn [fst snd]; unfold argc in *; [|clear -BA HA; lia].
      apply andb_prop in Hlk as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. specialize (LA ltac:(lia)). clear -BA HA LA. lia.
    - unfold clamp. cbn [fst snd]. unfold L0 in *. clear -B0 HL0. lia.
    - unfold clamp. cbn [fst snd]. unfold L1 in *. clear -B1 HL1 LL. lia.
  Qed.

  Theorem in_class_H_class : forall C (SINV : env -> (word -> option byte) -> Prop),
    in_class C argv fs = true ->
    (forall E M, SINV E M -> forall j, eb E (8 + j)%nat = chunk j (content_of argv fs)) ->
    H_class_prop (iotab_of C) argv fs SINV.
  Proof.
    intros C SINV HC Hblob. unfold H_class_prop, iotab_of. cbn [ION.io_open ION.io_blob].
    assert (HLK : look_of C = qlook argv fs \/ look_of C = -1).
    { unfold look_of. destruct (Z.eqb_spec (fst (cbounds C QLook)) (snd (cbounds C QLook))); [|right; reflexivity].
      left. pose proof (look_of_sound C HC) as X. unfold look_of in X. rewrite (proj2 (Z.eqb_eq _ _) e) in X.
      apply X. pose proof (cbounds_sound C QLook argv fs HC (qval_bounds QLook)) as BL. pose proof qlook_range. cbn [qval] in BL. lia. }
    pose proof (qlook_cases argv fs) as Q.
    pose proof (cbounds_sound C QFlen _ fs HC (qval_bounds QFlen)) as BF. cbn [qval] in BF.
    pose proof (cbounds_sound C QCfgLen _ fs HC (qval_bounds QCfgLen)) as BC. cbn [qval] in BC.
    pose proof (cbounds_sound C QCmod _ fs HC (qval_bounds QCmod)) as BM. cbn [qval] in BM.
    pose proof (cbounds_sound C QRoom _ fs HC (qval_bounds QRoom)) as BR. cbn [qval] in BR.
    (* [comment removed for export] *)
    pose proof (cbounds_sound C QCnt _ fs HC (qval_bounds QCnt)) as BN. cbn [qval] in BN.
    assert (HDR : ION.hdr_ok (iotab_of C) (content_of argv fs)).
    { unfold ION.hdr_ok, iotab_of. cbn [ION.io_cfg ION.io_room ION.io_cmod ION.io_b1s].
      pose proof (cfglen_range (content_of argv fs)) as CR. pose proof (flen_range (content_of argv fs)) as FR.
      pose proof (bz_range 2 (content_of argv fs)) as B2. pose proof (Z.mod_pos_bound (bz 2 (content_of argv fs)) 4 ltac:(lia)) as M4.
      pose proof (bz_range 1 (content_of argv fs)) as B1.
      rewrite room_eq in BR. rewrite cmod_eq in BM. unfold cfglen in *.
      split; [|split; [|split]].
      - unfold ION.in_opt, clamp; cbn [fst snd]. lia.
      - rewrite room_eq. unfold cfglen. lia.
      - unfold ION.in_opt, clamp; cbn [fst snd]. rewrite cmod_eq. lia.
      - (* [comment removed for export] *)
        unfold b1s_of, ION.in_opt, ION.b1s. change (ION.hbyte 1 (content_of argv fs)) with (bz 1 (content_of argv fs)).
        set (b := bz 1 (content_of argv fs)) in *.
        assert (SW : bv_swrap 8 b = (if b <? 128 then b else b - 256)).
        { unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
          destruct (Z.ltb_spec b 128); [rewrite Z.mod_small by lia; lia|].
          replace (b + 128) with ((b + 128 - 256) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
        destruct (Z.leb_spec 1 (fst (cbounds C QCnt))) as [X|X].
        + assert (128 <= b) by (apply Z.nlt_ge; intros Hb; pose proof (Z.div_lt_upper_bound b 128 1 ltac:(lia) ltac:(lia)); lia).
          rewrite SW. destruct (Z.ltb_spec b 128); [lia|].
          replace (b - 256) with ((b - 256 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
        + destruct (Z.leb_spec (snd (cbounds C QCnt)) 0) as [Y|Y]; [|exact I].
          assert (b < 128) by (apply Z.nle_gt; intros Hb; apply (Z.div_le_mono _ _ 128) in Hb; [|lia]; rewrite Z.div_same in Hb by lia; lia).
          rewrite SW. destruct (Z.ltb_spec b 128); [|lia]. rewrite Z.mod_small by lia. lia. }
    revert HDR.
    destruct HLK as [HL|HL]; [|rewrite HL; cbn -[ION.hdr_ok content_of]; intros _; exact I].
    rewrite HL. clearbody argc L0 L1. clear Hva Hfit. destruct argv as [|a0 [|p [|x r]]]; try (rewrite Q; cbn -[ION.hdr_ok content_of]; intros _; exact I).
    cbn [nth].
    destruct Q as [[-> Hl]|[[-> (Hl & Hp)]|[[-> ->]|[-> (Hne & Hnd & Hl & c & Hlk & Hc)]]]]; cbn -[ION.hdr_ok content_of clamp cbounds Z.pow Z.min]; intros HDR.
    - exact Hl.
    - destruct Hp as [->|[H1 H2]]; [left; reflexivity | right]. repeat split; [exact H1 | lia | exact H2].
    - reflexivity.
    - exists c. rewrite Hc in BF, HDR. pose proof (flen_range c).
      split; [exact Hne|]. split; [exact Hnd|]. split; [lia|]. split; [exact Hlk|].
      split; [unfold clamp; cbn [fst snd]; lia|]. split; [|exact HDR].
      intros E M HS j _. rewrite <- Hc. exact (Hblob E M HS j).
  Qed.
End ClassSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition root_class (i : nat) : class :=
  match i with
  | 0%nat => [(QLook, 0, 0); (QArgc, 1, 1)]
  | 1%nat => [(QLook, 0, 0); (QArgc, 3, 1024)]
  | 2%nat => [(QLook, 1, 1)]
  | 3%nat => [(QLook, 2, 2)]
  | 4%nat => [(QLook, 3, 3)]
  | 5%nat => [(QLook, 4, 4)]
  | _ => [(QLook, 5, 5)]
  end.

Lemma root_cover : forall argv fs, valid_argv argv -> exists i, (i < 6)%nat /\ in_class (root_class i) argv fs = true.
Proof.
  intros argv fs Hva. pose proof (qlook_cases argv fs) as Q.
  assert (HA : 1 <= Z.of_nat (length argv) <= 1024) by (destruct Hva as [H _]; exact H).
  assert (CASE : forall v, qlook argv fs = v -> 1 <= v <= 4 -> exists i, (i < 6)%nat /\ in_class (root_class i) argv fs = true).
  { intros v Hv Hr.
    assert (E4 : v = 1 \/ v = 2 \/ v = 3 \/ v = 4) by lia.
    destruct E4 as [-> |[-> |[-> | ->]]];
      [exists 2%nat | exists 3%nat | exists 4%nat | exists 5%nat]; (split; [lia|]);
      unfold in_class, root_class; cbn [forallb qval]; rewrite Hv; reflexivity. }
  destruct argv as [|a0 [|p [|x r]]]; cbn [length] in HA; [lia| | |].
  - exists 0%nat. split; [lia|]. unfold in_class, root_class; cbn [forallb qval length]. rewrite Q. reflexivity.
  - destruct Q as [[Hq _]|[[Hq _]|[[Hq _]|[Hq _]]]]; eapply CASE; try exact Hq; lia.
  - exists 1%nat. split; [lia|]. unfold in_class, root_class. cbn [forallb qval length]. rewrite Q.
    apply andb_true_intro; split; [reflexivity|]. apply andb_true_intro; split; [|reflexivity].
    apply andb_true_intro; split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma t_die_nil : forall msg fs, t_die msg fs [].
Proof. intros. unfold t_die, t_emit. left. apply is_prefix_nil. Qed.
Lemma spec_nil : forall argv fs, spec argv fs [].
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|p [|x r]]]; try apply t_die_nil.
  destruct (4096 <=? length p)%nat; [apply t_die_nil|]. destruct (list_byte_eqb p []); [apply t_die_nil|].
  destruct (list_byte_eqb p dot_path); [left; apply t_die_nil|].
  destruct (fs_lookup fs p); [left; apply t_die_nil | apply t_die_nil].
Qed.

(* [comment removed for export] *)
Fixpoint all_holes (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SAlt2 a b | SCase _ _ a b => all_holes a && all_holes b
  | _ => false
  end.
Lemma sd_all_holes : forall HOLES D E fs s T,
  all_holes s = true -> (forall h, HOLES h E fs = T) -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs s T. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; intros Hs HT; cbn [all_holes] in Hs; try discriminate; cbn [sd].
  - apply andb_prop in Hs as [Ha Hb]. intros tr. unfold t_alt2. split; [intros [H|H]; [apply (IHa Ha HT) | apply (IHb Hb HT)]; exact H | intros H; left; apply (IHa Ha HT); exact H].
  - apply andb_prop in Hs as [Ha Hb]. destruct (bv_unsigned (edenot E e) <=? mid); [apply IHa | apply IHb]; assumption.
  - rewrite HT. apply t_eq_refl.
Qed.

(* [comment removed for export] *)
Fixpoint shape_closed (s : shape) : bool :=
  match s with
  | SNil | SExit _ => true
  | SEmitP _ _ s' => shape_closed s'
  | SAlt2 a b | SCase _ _ a b => shape_closed a && shape_closed b
  | SHole _ | SNext => false
  end.
Lemma sd_closed : forall HOLES1 HOLES2 D1 D2 E fs s,
  shape_closed s = true -> sd HOLES1 D1 E fs s = sd HOLES2 D2 E fs s.
Proof.
  intros HOLES1 HOLES2 D1 D2 E fs s. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; intros Hs; cbn [shape_closed] in Hs; try discriminate; cbn [sd]; try reflexivity.
  - rewrite (IH Hs). reflexivity.
  - apply andb_prop in Hs as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
  - apply andb_prop in Hs as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
Qed.

End FPW_1.
