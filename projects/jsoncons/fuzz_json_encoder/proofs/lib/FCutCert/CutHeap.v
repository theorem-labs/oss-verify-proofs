(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CH.
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition ksupport (E : env) (K : kentry) (x : Z) : Prop :=
  match K with
  | KWord a w _ => estart E a <= x < estart E a + Z.of_nat w
  | KZero a n | KBlob a n _ | KFill a n _ | KUnk a n | KWr a n => estart E a <= x < estart E a + elenZ E n
  | KImg lo hi => lo <= x < hi
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => False
  end.

Lemma bv_succ_Z : forall a : Z, (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma rdn_ext : forall (M M' : word -> option byte) n a,
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros M M'. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [rdn]. rewrite (H a) by lia. rewrite bv_succ_Z. rewrite (IH (a + 1)); [reflexivity|]. intros i Hi. apply H. lia.
Qed.

Lemma store_ok_ext : forall (M M' : word -> option byte) n a,
  (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None) ->
  store_ok segs M (Z_to_bv 64 a) n = true -> store_ok segs M' (Z_to_bv 64 a) n = true.
Proof.
  intros M M'. induction n as [|n IH]; intros a H Hs; [reflexivity|].
  cbn [store_ok] in *. destruct (wview segs M (Z_to_bv 64 a)) as [b|] eqn:Hv; [|discriminate].
  assert (Hv' : wview segs M' (Z_to_bv 64 a) <> None).
  { unfold wview in *. destruct (M' (Z_to_bv 64 a)) as [b'|] eqn:Hm'; [discriminate|].
    destruct (M (Z_to_bv 64 a)) as [b0|] eqn:Hm.
    - exfalso. apply (H a); [lia | rewrite Hm; discriminate | exact Hm'].
    - rewrite Hv. discriminate. }
  destruct (wview segs M' (Z_to_bv 64 a)) as [b'|]; [|contradiction].
  rewrite bv_succ_Z in *. apply (IH (a + 1)); [|exact Hs]. intros i Hi. apply H. lia.
Qed.

(* [comment removed for export] *)
Definition def_only (K : kentry) : bool := match K with KUnk _ _ | KWr _ _ => true | _ => false end.

Lemma kentry_transport_def : forall E M M' K, def_only K = true ->
  (forall x, ksupport E K x -> M (Z_to_bv 64 x) <> None -> M' (Z_to_bv 64 x) <> None) ->
  kentry_ok segs E M K -> kentry_ok segs E M' K.
Proof.
  intros E M M' K Hd H HK. destruct K as [| | | | | |a n| | |a n]; try discriminate; cbn [kentry_ok ksupport] in *.
  - destruct HK as [Hfl Hw]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    apply (store_ok_ext M M'); [|exact (Hw d m Hd0 Hdm)]. intros i Hi. apply H. lia.
  - destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply H; [lia | exact (Hz i Hi)].
Qed.

Lemma kentry_transport : forall E M M' K,
  (forall x, ksupport E K x -> M' (Z_to_bv 64 x) = M (Z_to_bv 64 x)) ->
  kentry_ok segs E M K -> kentry_ok segs E M' K.
Proof.
  intros E M M' K H HK.
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [kentry_ok ksupport] in *; try exact HK.
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hr). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hr. pose proof (flat_u E a _ Hfl) as Hu.
    assert (Ha : adenot E a = Z_to_bv 64 (estart E a)).
    { apply bv_eq. rewrite Hu. rewrite Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Z.mod_small.
      destruct Hfl as (F1 & F2 & _). change (bv_modulus 64) with (2 ^ 64). lia. }
    rewrite Ha. apply rdn_ext. intros i Hi. apply H. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite H by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) destruct HK as (Hfl & Hl & Hz). split; [exact Hfl|]. split; [exact Hl|]. intros i Hi. rewrite H by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) destruct HK as (H1 & H2 & Hz). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite H by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) apply (kentry_transport_def E M M' (KWr a n) eq_refl); [|exact HK].
    intros x Hx Hd. cbn [ksupport] in Hx. rewrite (H x Hx). exact Hd.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite H by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite H by lia. exact (Hz i Hi).
Qed.

(* [comment removed for export] *)
Lemma know_transport : forall E M M' kn,
  (forall K, In K kn ->
      (forall x, ksupport E K x -> M' (Z_to_bv 64 x) = M (Z_to_bv 64 x))
      \/ (def_only K = true /\ forall x, ksupport E K x -> M (Z_to_bv 64 x) <> None -> M' (Z_to_bv 64 x) <> None)) ->
  know_ok segs E M kn -> know_ok segs E M' kn.
Proof.
  intros E M M' kn H HK. unfold know_ok in *. rewrite Forall_forall in *. intros K HIn.
  destruct (H K HIn) as [Heq | [Hd Hdef]].
  - exact (kentry_transport E M M' K Heq (HK K HIn)).
  - exact (kentry_transport_def E M M' K Hd Hdef (HK K HIn)).
Qed.

(* [comment removed for export] *)
Lemma know_ok_agree : forall b E E' M kn, env_agree b E E' -> APC.kn_vars_lt b kn = true -> know_ok segs E M kn -> know_ok segs E' M kn.
Proof. intros b E E' M kn Hag Hv HK. exact (APS.know_ok_agree' segs b E E' M kn Hag Hv HK). Qed.

(* [comment removed for export] *)
Lemma nth_vars_lt : forall b sr i, APC.sr_vars_lt b sr = true -> APC.expr_vars_lt b (nth i sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|e t IH]; intros i H; [destruct i; reflexivity|].
  cbn [APC.sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct i; [exact He | apply IH; exact Ht].
Qed.
Lemma fresh_regs_ok : forall rs E sr (R : bvmap 5 word) nx,
  (forall r : reg, ~ In (ridx r) rs -> getr R r = edenot E (sr_get sr r)) ->
  APC.sr_vars_lt nx sr = true -> Forall (fun r => (0 < r < 32)%nat) rs ->
  regs_ok (APS.ext_list E nx (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)) (APC.sr_fresh sr rs nx) R.
Proof.
  induction rs as [|r0 rest IH]; intros E sr R nx H Hsr Hrs; cbn [APC.sr_fresh map APS.ext_list].
  - intros r. apply H. intros [].
  - apply Forall_cons_iff in Hrs as [Hr0 Hrest].
    apply IH; [| |exact Hrest].
    + intros r Hnin. unfold sr_get. destruct (bv_eqb r 0) eqn:Er0.
      * assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0).
        cbn [edenot]. apply getr_zero.
      * rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r) r0) as [<-|Hne].
        -- cbn [edenot]. rewrite APS.ext1_at. rewrite CC.reg_of_ridx. reflexivity.
        -- assert (Hn : ~ In (ridx r) (r0 :: rest)) by (intros [X|X]; [apply Hne; symmetry; exact X | exact (Hnin X)]).
           rewrite (H r Hn). unfold sr_get. rewrite Er0.
           apply (SR.edenot_agree_AP nx); [apply APS.ext1_agree | apply nth_vars_lt; exact Hsr].
    + apply APS.sr_vars_lt_upd; [eapply APS.sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.

End WithSegs.

(* [comment removed for export] *)
Section Heap.
Variable L : heap_layout.
Definition client_ok (LB : list (Z * Z)) (sp : Z) (x : Z) : Prop :=
  0 <= x < 2 ^ 64 /\ client_addr L LB sp (hl_stack L) x /\ ~ in_errno L x.
Definition entry_survives (LB : list (Z * Z)) (sp : Z) (E : env) (K : kentry) : Prop :=
  (forall x, ksupport E K x -> client_ok LB sp x)
  \/ (def_only K = true /\ forall x, ksupport E K x -> client_ok LB sp x \/ (0 <= x < 2 ^ 64 /\ sp - hl_stack L <= x < sp)).

Lemma heap_pres_know : forall LB sp E M M' kn,
  heap_pres_core L LB sp M M' ->
  (forall K, In K kn -> entry_survives LB sp E K) ->
  know_ok (hl_segs L) E M kn -> know_ok (hl_segs L) E M' kn.
Proof.
  intros LB sp E M M' kn [Hc Hs] H HK. apply (know_transport (hl_segs L) E M M' kn); [|exact HK].
  intros K HIn. destruct (H K HIn) as [Hcl | [Hd Hds]].
  - left. intros x Hx. destruct (Hcl x Hx) as (Hr & Hca & Hne). exact (Hc x Hr Hca Hne).
  - right. split; [exact Hd|]. intros x Hx Hdef. destruct (Hds x Hx) as [(Hr & Hca & Hne) | (Hr & Hsc)].
    + rewrite (Hc x Hr Hca Hne). exact Hdef.
    + exact (Hs x Hsc).
Qed.

(* [comment removed for export] *)
Lemma fresh_block_unk : forall E M' (a : saddr) (n : expr) A nz,
  estart E a = A -> elenZ E n = nz -> block_range L A nz -> HeapIface.defined M' A nz -> 2 ^ 47 <= 2 ^ 64 -> hl_sptop L <= 2 ^ 47 ->
  kentry_ok (hl_segs L) E M' (KUnk a n).
Proof.
  intros E M' a n A nz Ha Hn (B1 & B2 & B3 & B4 & B5) Hdef _ Htop. cbn [kentry_ok]. rewrite Ha, Hn. split.
  - unfold flat. rewrite Ha. lia.
  - intros i Hi. apply Hdef. exact Hi.
Qed.
Lemma fresh_block_wr : forall E M' (a : saddr) (n : expr),
  kentry_ok (hl_segs L) E M' (KUnk a n) -> kentry_ok (hl_segs L) E M' (KWr a n).
Proof.
  intros E M' a n HU. cbn [kentry_ok]. split; [exact (proj1 HU)|].
  intros d m Hd Hm. exact (kunk_store_ok (hl_segs L) E M' a n d m HU Hd Hm).
Qed.
End Heap.

(* [comment removed for export] *)
Record hdecl : Type := HD {
  hd_scr : Z;                      (* [comment removed for export] *)
  hd_hstk : Z;                     (* [comment removed for export] *)
  hd_crs : list SGP.region;        (* [comment removed for export] *)
  hd_wrs : list SGP.region;        (* [comment removed for export] *)
  hd_img : list (Z * Z)            (* [comment removed for export] *)
}.
Definition blocks : Type := list (expr * expr).       (* [comment removed for export] *)
Definition stack_reg (d : hdecl) : SGP.region := (EVar 2, - hd_scr d, ELit (hd_scr d)).
Definition blk_regs (BL : blocks) : list SGP.region := map (fun b : expr * expr => (fst b, 0, snd b)) BL.
(* [comment removed for export] *)
Definition foot_regs (d : hdecl) (BL : blocks) : list SGP.region := stack_reg d :: hd_wrs d ++ blk_regs BL.
(* [comment removed for export] *)
Definition keep_regs (d : hdecl) (c : Z) (BL : blocks) : list SGP.region :=
  (EVar 2, c, ELit (- c)) :: (EVar 2, - hd_scr d, ELit (hd_scr d + c - hd_hstk d)) :: hd_crs d ++ hd_wrs d ++ blk_regs BL.
Definition entry_reg (K : kentry) : option SGP.region :=
  match K with
  | KWord (SA b k) w _ => Some (b, k, ELit (Z.of_nat w))
  | KZero (SA b k) n | KBlob (SA b k) n _ | KFill (SA b k) n _ | KUnk (SA b k) n | KWr (SA b k) n => Some (b, k, n)
  | _ => None
  end.
(* [comment removed for export] *)
Definition within (kn : list kentry) (REGS : list SGP.region) (b : expr) (k : Z) (n : expr) : bool :=
  if SGP.withinE kn REGS b k n then true
  else existsb (fun r : SGP.region => let '(rb, rlo, rlen) := r in CX.xinside2 kn b k n rb rlo rlen) REGS.
Definition survive_chk (d : hdecl) (kn : list kentry) (c : Z) (BL : blocks) (K : kentry) : bool :=
  match K with
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => existsb (fun r : Z * Z => (Z.leb (fst r) lo && Z.leb hi (snd r))%bool) (hd_img d)
  | _ => match entry_reg K with
         | Some (b, k, n) => if within kn (keep_regs d c BL) b k n then true
                             else if def_only K then within kn [stack_reg d] b k n else false
         | None => false
         end
  end.
(* [comment removed for export] *)
Fixpoint remove_first (p : expr) (BL : blocks) : blocks :=
  match BL with [] => [] | b :: r => if expr_eqb (fst b) p then r else b :: remove_first p r end.
End CH.
