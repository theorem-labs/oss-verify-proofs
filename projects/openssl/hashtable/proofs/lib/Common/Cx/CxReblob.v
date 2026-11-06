(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition JB : nat := 32.
Definition kept (k : nat) : bool := negb (Nat.eqb k 1) && negb (Nat.eqb k 2) && Nat.ltb k JB.

(* [comment removed for export] *)
Fixpoint eblob_free (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => eblob_free a && eblob_free b
  | EExt _ _ _ a => eblob_free a
  | EBlob _ k _ _ => kept k
  end.
Definition saddr_bf (a : saddr) : bool := eblob_free (a_base a).
Definition kentry_bf (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_bf a && eblob_free v
  | KZero a n => saddr_bf a && eblob_free n
  | KBlob a n k => saddr_bf a && eblob_free n && kept k
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

Definition ev_same (E E' : env) : Prop := (forall n, ev E n = ev E' n) /\ (forall k, kept k = true -> eb E k = eb E' k).

Lemma edenot_evsame : forall E E' e, ev_same E E' -> eblob_free e = true -> edenot E e = edenot E' e.
Proof.
  intros E E' e [HS HB]. induction e; cbn [eblob_free edenot]; intros H;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
    try reflexivity; try discriminate;
    repeat match goal with IH : ?b = true -> edenot E ?x = edenot E' ?x, Hb : ?b = true |- _ => rewrite (IH Hb); clear IH end;
    try reflexivity.
  - apply HS.
  - rewrite (HB _ H). reflexivity.
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
      rewrite <- ?(edenot_evsame E E') by assumption;
      rewrite <- ?(proj2 HS) by assumption; exact HK.
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
                      else if Nat.leb JB k then chunk (k - JB) c else eb E k).

Lemma reblob_evsame : forall E argv c, ev_same E (reblob E argv c).
Proof.
  intros E argv c. split; [intros n; reflexivity|]. intros k Hk. unfold kept in Hk. cbn [reblob eb].
  apply andb_prop in Hk as [Hk H3]. apply andb_prop in Hk as [H1 H2].
  destruct (Nat.eqb k 1); [discriminate H1|]. destruct (Nat.eqb k 2); [discriminate H2|].
  apply Nat.ltb_lt in H3. destruct (Nat.leb_spec JB k); [lia | reflexivity].
Qed.

Section Main.
  Variables (segs : list Segment) (A : atable) (ph : PhdrInfo).
  Variables (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)).
  Variables (uid hw : word).
  Variable c : list byte.

  (* [comment removed for export] *)
  Definition SINVm (E : env) (M : word -> option byte) : Prop :=
    SINV0 ph sp rdraw brk0 argv envp uid hw E M /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv []
    /\ forall j, eb E (JB + j)%nat = chunk j c.

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
    unfold JB. destruct (Nat.eqb_spec (32 + j) 1); [lia|]. destruct (Nat.eqb_spec (32 + j) 2); [lia|].
    destruct (Nat.leb_spec 32 (32 + j)); [|lia]. f_equal. lia.
  Qed.

  Lemma hid_reblob : forall E cs model,
    forallb pair_bf (a_vis cs) = true ->
    hid A (argH0 ph sp rdraw argv envp uid hw) (reblob E argv c) cs model = hid A (argH0 ph sp rdraw argv envp uid hw) E cs model.
  Proof.
    intros E cs model Hv. apply functional_extensionality. intros a. unfold hid, vis, APS.in_allow.
    rewrite (in_vis_evsame E (reblob E argv c) (reblob_evsame E argv c) cs _ Hv).
    rewrite (in_sh_evsame E (reblob E argv c) (reblob_evsame E argv c) A cs _ Hv). reflexivity.
  Qed.

  Theorem cs_ok_reblob : forall LIMIT ISP FS0 E cs R FULL model,
    acs_noblob cs = true ->
    cs_ok segs A LIMIT (SINV0 ph sp rdraw brk0 argv envp uid hw) (argH0 ph sp rdraw argv envp uid hw) ISP FS0 E cs R FULL model ->
    cs_ok segs A LIMIT SINVm (argH0 ph sp rdraw argv envp uid hw) ISP FS0 (reblob E argv c) cs R FULL model.
  Proof.
    intros LIMIT ISP FS0 E cs R FULL model Hnb HC.
    unfold acs_noblob in Hnb.
    apply andb_prop in Hnb as [Hnb Hfd]. apply andb_prop in Hnb as [Hnb Hbrk]. apply andb_prop in Hnb as [Hnb Hgh].
    apply andb_prop in Hnb as [Hnb Hvis]. apply andb_prop in Hnb as [Hnb Hmaps]. apply andb_prop in Hnb as [Hregs Hkn].
    pose proof (reblob_evsame E argv c) as HS. set (E' := reblob E argv c) in *.
    destruct HC as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 fholes f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 fisp ftop].
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
      apply Forall_forall. intros m Hin Hk. pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [Hm1 Hm2].
      rewrite !(uE_evsame E E' HS) by assumption. exact (proj1 (Forall_forall _ _) fholes m Hin Hk).
    - exact f11.
    - exact f12.
    - exact f13.
    - exact f14.
    - exact f15.
    - apply Forall_forall. intros m Hin Hk. rewrite (amap_den_evsame E E' HS m (proj1 (forallb_forall _ _) Hmaps m Hin)).
      exact (proj1 (Forall_forall _ _) f16 m Hin Hk).
    - apply Forall_forall. intros m Hin Hk a. pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [Hm1 Hm2].
      rewrite <- !(edenot_evsame E E') by assumption. exact (proj1 (Forall_forall _ _) f17 m Hin Hk a).
    - exact f18.
    - exact f19.
    - rewrite <- (edenot_evsame E E') by assumption. exact f20.
    - exact f21.
    - exact f22.
    - rewrite (allowA_evsame E E' HS A cs Hvis Hgh). exact f23.
    - rewrite (allowA_evsame E E' HS A cs Hvis Hgh). exact f24.
    - unfold E'. rewrite (hid_reblob E cs model Hvis). intros a H1 H2 H3 H4 H5. rewrite (in_ghost_evsame E (reblob E argv c) (reblob_evsame E argv c) cs _ Hgh) in H5. exact (f25 a H1 H2 H3 H4 H5).
    - apply SINVm_reblob. exact f26.
    - (* [comment removed for export] *) destruct fisp as [X1 X2]. split; [exact X1|]. rewrite (uE_evsame E E' HS e_spw eq_refl). exact X2.
    - exact ftop.
  Qed.
End Main.

