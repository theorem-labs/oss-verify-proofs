(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Lib.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable G : gtable.

#[local] Notation owned := (GPS.owned SWIN PERMc SPTOPc).
#[local] Notation owned3 := (AzKnowLib.owned3 PERMc SPTOPc).
#[local] Notation shz := (AzKnowLib.shz G).

(* [comment removed for export] *)
Lemma floor_win_sound : forall E M k fl top bud tb tk fwb fwo fwl,
  know_ok SEGS E M k -> top_ok k fl top bud = true -> split_lit top = (tb, tk) ->
  GPS.floor_sem E fl top bud -> floor_win fl top bud = (SA fwb fwo, fwl) ->
  CEIL_run <= uE E fwb + fwo /\ fwl = ELit (bud + WSTK).
Proof. pose proof sfloor_ge as SFG_.
  intros E M k fl top bud tb tk fwb fwo fwl HK Htok Hsp Hfl Hfw.
  destruct (top_ok_sound SEGS E M k fl top bud tb tk HK Htok Hsp) as (TOPEQ & Hb & TOPR & TOPN).
  destruct fl as [f|]; cbn [floor_win GPS.floor_sem] in Hfw, Hfl.
  - injection Hfw as <- <- <-. split; [unfold uE in *; lia | reflexivity].
  - rewrite Hsp in Hfw. injection Hfw as <- <- <-. rewrite TOPEQ in Hfl. split; [unfold uE in *; lia | reflexivity].
Qed.
Lemma floor_win_vars : forall v ms top bud fwb fwo fwl,
  AP.maps_vars_lt v ms = true -> AP.expr_vars_lt v top = true ->
  floor_win (acs_floor ms) top bud = (SA fwb fwo, fwl) -> AP.expr_vars_lt v fwb = true.
Proof.
  intros v ms top bud fwb fwo fwl Hms Htop Hfw. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_win] in Hfw.
  - destruct (split_lit top) as [tb tk] eqn:Hsp. injection Hfw as <- <- <-. eapply GCL.split_lit_vars; [exact Hsp | exact Htop].
  - injection Hfw as <- <- <-. cbn [AP.maps_vars_lt forallb am_base am_len] in Hms.
    apply andb_prop in Hms as [Hms _]. apply andb_prop in Hms as [Hf _]. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma kentry_range_foot : forall E M K b off len,
  kentry_ok SEGS E M K -> kentry_range K = Some (b, off, len) ->
  kfoot E K = Some (estart E (SA b off), uE E len).
Proof.
  intros E M K b off len HK HR.
  destruct K as [[b' o'] w vv|[b' o'] nn|[b' o'] nn kb|ilo ihi|e m|e rlo rhi|[b' o'] nn|a1 n1 a2 n2|[b' o'] nn fc|[b' o'] nn|[b' o'] nn|fv flo fd];
    cbn [kentry_range] in HR; try discriminate; injection HR as <- <- <-; cbn [kfoot]; try reflexivity.
  cbn [kentry_ok] in HK. destruct HK as (Hw & _ & _). unfold uE. cbn [edenot]. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kdisj_of_facts_ok : forall E M M0 k (p n : expr) (pw : word) ks acc,
  know_ok SEGS E M0 k -> edenot E p = pw ->
  (forall K b off len, In K ks -> kentry_range K = Some (b, off, len) -> 1 <= uE E len ->
      bv_unsigned pw + uE E n <= uE E b + off \/ uE E b + off + uE E len <= bv_unsigned pw) ->
  know_ok SEGS E M acc ->
  know_ok SEGS E M (kdisj_of_facts k p n ks acc).
Proof.
  intros E M M0 k p n pw ks. induction ks as [|K r IH]; intros acc HK Hp Hsep Hacc; [exact Hacc|].
  cbn [kdisj_of_facts].
  assert (REST : forall acc', know_ok SEGS E M acc' -> know_ok SEGS E M (kdisj_of_facts k p n r acc')).
  { intros acc' Hacc'. apply IH; [exact HK | exact Hp | | exact Hacc'].
    intros K' b off len HK' HR Hl. apply (Hsep K' b off len); [right; exact HK' | exact HR | exact Hl]. }
  destruct (kdisj_of_fact k p n K) as [D|] eqn:HD; [|apply REST; exact Hacc].
  destruct (existsb (kentry_eqb D) acc); [apply REST; exact Hacc|].
  apply REST. constructor; [|exact Hacc].
  unfold kdisj_of_fact in HD. destruct (kentry_range K) as [[[b off] len]|] eqn:HR; [|discriminate].
  assert (GEN : forall l, xlo k len = Some l -> 1 <= l -> D = KDisj (SA p 0) n (SA b off) len -> kentry_ok SEGS E M D).
  { intros l Hxl Hl1 ->. pose proof (xlo_sound SEGS E M0 k len l HK Hxl) as Hlen.
    cbn [kentry_ok]. rewrite !estart_SA. cbn [edenot a_base a_off]. rewrite Hp. unfold elenZ.
    destruct (Hsep K b off len (or_introl eq_refl) HR ltac:(unfold uE; lia)) as [H|H]; unfold uE in *; lia. }
  destruct b as [bz| | | | | | |]; try discriminate HD;
    (destruct (xlo k len) as [l|] eqn:Hxl; [|discriminate HD]); (destruct (Z.leb 1 l) eqn:Hl1; [|discriminate HD]);
    injection HD as <-; apply Z.leb_le in Hl1; exact (GEN l eq_refl Hl1 eq_refl).
Qed.

(* [comment removed for export] *)
Definition kept_loc (Lc : list (Z * Z)) (z : Z) : Prop :=
  in_blocks Lc z \/ in_wins PERMc z \/ (CEIL_run <= z < SPTOPc) \/ SPTOPc <= z \/ (g_ro_lo G <= z < g_img_hi G).

Lemma owned3_kept_loc : forall Lc (x : word), owned3 Lc x -> kept_loc Lc (bv_unsigned x).
Proof. intros Lc x [H|[H|H]]; unfold kept_loc; [tauto | tauto | pose proof sfloor_ge; right; right; left; lia]. Qed.

(* [comment removed for export] *)
Lemma keep_owned_loc : forall stk E M k live perm objs fl top bud sp spb spk v K z rb ro rl,
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc ->
  split_lit sp = (spb, spk) -> GPS.floor_sem E fl top bud ->
  In K (keep_owned G stk k (live ++ perm) objs fl top bud sp v) -> kentry_range K = Some (rb, ro, rl) -> in_kfoot E K z ->
  kept_loc (blocks_den E live) z \/ shz E objs (uE E sp) z.
Proof.
  intros stk E M k live perm objs fl top bud sp spb spk v K z rb ro rl HK Hflat Hperm Htop Hsp Hceil Hin HKR Hz.
  (* [comment removed for export] *)
  assert (HKc : know_ok SEGS E M (kn_cutout (kn_cutout k spb (spk - stk) (ELit stk)) (ELit 0) (g_errno G) (ELit 4))).   (* [comment removed for export] *)
  { eapply know_ok_cutout; [eapply know_ok_cutout; [exact HK|]; intros; reflexivity|]. intros; reflexivity. }
  assert (HKK : kentry_ok SEGS E M K).
  { rewrite keep_owned_eq in Hin. unfold keep_owned_ref in Hin. rewrite Hsp in Hin.
    repeat (apply in_app_iff in Hin as [Hin'|Hin]; [apply filter_In in Hin' as [Hin' _]; first [exact (proj1 (Forall_forall _ _) HK K Hin') | exact (proj1 (Forall_forall _ _) HKc K Hin')] |]).
    apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) HK K Hin). }
  (* [comment removed for export] *)
  assert (FP : estart E (SA rb ro) <= z < estart E (SA rb ro) + elenZ E rl /\ 0 <= estart E (SA rb ro) /\ estart E (SA rb ro) + elenZ E rl <= 2 ^ 64).
  { unfold in_kfoot, kfoot in Hz.
    destruct K as [[b' o'] w vv|[b' o'] nn|[b' o'] nn kb|ilo ihi|e m|e rlo rhi|[b' o'] nn|a1 n1 a2 n2|[b' o'] nn fc|[b' o'] nn|[b' o'] nn|fv flo fd];
      cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-; cbn [kentry_ok] in HKK.
    - destruct HKK as (Hw8 & (F1 & F2 & F3 & F4) & _). unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. lia.
    - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia.
    - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia.
    - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia.
    - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia.
    - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia. }
  destruct FP as (Hzr & E1 & E2).
  assert (Hx : estart E (SA rb ro) <= bv_unsigned (Z_to_bv 64 z) < estart E (SA rb ro) + elenZ E rl) by (rewrite u64_lit by lia; lia).
  (* [comment removed for export] *)
  assert (HKm : match K with KWord _ _ _ | KZero _ _ | KFill _ _ _ | KBlob _ _ _ | KWr _ _ | KUnk _ _ => true | _ => false end = true).
  { destruct K; try reflexivity; cbn [kentry_range] in HKR; discriminate. }
  (* [comment removed for export] *)
  assert (OWN : owned_x k (live ++ perm) fl top bud rb ro rl = true -> kept_loc (blocks_den E live) z \/ shz E objs (uE E sp) z).
  { intros Hown. left.
    pose proof (owned_x_sound3 SEGS PERMc SPTOPc E M k live perm fl top bud rb ro rl (Z_to_bv 64 z) HK Hflat Hperm Htop Hceil Hown Hx) as OW.
    apply owned3_kept_loc in OW. rewrite u64_lit in OW by lia. exact OW. }
  assert (ABV : above_x k top sp rb ro rl = true -> kept_loc (blocks_den E live) z \/ shz E objs (uE E sp) z).
  { intros Habv. left.
    pose proof (above_x_sound SEGS SPTOPc E M k top sp rb ro rl (Z_to_bv 64 z) HK Habv Htop Hx) as [AB _].
    rewrite u64_lit in AB by lia. unfold kept_loc. right; right; right; left. exact AB. }
  assert (IMG : img_lit_x G k rb ro rl = true -> kept_loc (blocks_den E live) z \/ shz E objs (uE E sp) z).
  { intros Himg. left.
    pose proof (img_lit_x_sound SEGS G E M k rb ro rl (Z_to_bv 64 z) HK Himg E1 ltac:(lia) Hx) as [IM _].
    rewrite u64_lit in IM by lia. unfold kept_loc. right; right; right; right. exact IM. }
  rewrite keep_owned_eq in Hin. unfold keep_owned_ref in Hin. rewrite Hsp in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]].
  - (* [comment removed for export] *)
    apply filter_In in Hin as [_ Hkeep]. apply andb_prop in Hkeep as [_ Hkeep]. unfold keep_sticky in Hkeep.
    destruct K as [[b' o'] w vv|[b' o'] nn|[b' o'] nn kb|ilo ihi|e m|e rlo rhi|[b' o'] nn|a1 n1 a2 n2|[b' o'] nn fc|[b' o'] nn|[b' o'] nn|fv flo fd];
      try discriminate Hkeep; try discriminate HKm; cbn [kentry_range] in HKR; try discriminate HKR; injection HKR as -> -> ->;
      (apply orb_prop in Hkeep as [Ho|Ha]; [exact (OWN Ho) | exact (ABV Ha)]).
  - (* [comment removed for export] *)
    apply filter_In in Hin as [_ Hkeep]. apply andb_prop in Hkeep as [_ Hkeep]. unfold keep_content in Hkeep.
    assert (KK : ((owned_x k (live ++ perm) fl top bud rb ro rl && ranges_apart_x k rb ro rl spb (spk - stk) (ELit stk) && errno_apart_x G k rb ro rl)
                  || above_x k top sp rb ro rl || img_lit_x G k rb ro rl)%bool = true).   (* [comment removed for export] *)
    { destruct K; try discriminate HKm; rewrite ?HKR, ?Hsp in Hkeep; first [exact Hkeep | discriminate Hkeep]. }
    apply orb_prop in KK as [KK|Hi]; [|exact (IMG Hi)]. apply orb_prop in KK as [KK|Ha]; [|exact (ABV Ha)].
    apply andb_prop in KK as [KK _]. apply andb_prop in KK as [Ho _]. exact (OWN Ho).
  - (* [comment removed for export] *)
    apply filter_In in Hin as [_ Hkeep]. apply andb_prop in Hkeep as [_ Hkeep]. right.
    pose proof (keep_shadow_foot SEGS G E M k objs fl top bud sp K (Z_to_bv 64 z) HK HKK Hkeep Hceil) as SH.
    rewrite u64_lit in SH by lia. apply SH. exact Hz.
  - (* [comment removed for export] *)
    apply filter_In in Hin as [_ Hkeep]. apply andb_prop in Hkeep as [_ Hkeep]. unfold keep_kfpc in Hkeep.
    destruct K; try discriminate Hkeep. discriminate HKm.
Qed.

(* [comment removed for export] *)
Lemma block_not_kept_loc : forall Lc (p n : Z) z,
  ablk_ok G p n -> g_img_lo G <= g_ro_lo G -> CEIL_run <= SPTOPc ->
  (forall b m, In (b, m) Lc -> p + n <= b \/ b + m <= p) ->
  (forall lo hi, In (lo, hi) PERMc -> lo < hi -> p + n <= lo \/ hi <= p) ->
  p <= z < p + n -> ~ kept_loc Lc z.
Proof.
  intros Lc p n z (K1 & K2 & K3 & K4) Gimg Htop Hdisj Hperm Hz [Hb|[Hp|[Hst|[Hab|Him]]]].
  - destruct Hb as (b & m & Hin & Hbz). destruct (Hdisj b m Hin); lia.
  - destruct Hp as (lo & hi & Hin & Hlh). destruct (Hperm lo hi Hin ltac:(lia)); lia.
  - lia.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_band : forall E objs top z,
  (forall b m, In (b, m) (blocks_den E objs) -> 0 <= b /\ b + m <= two47) ->
  0 <= g_ro_lo G -> g_img_hi G <= two47 ->
  shz E objs top z -> SHMAPLO <= z < KHI.
Proof.
  intros E objs top z Hobjs Gro Gimg [Hl|[Hs|Hi]].
  - destruct Hl as (b & m & Hin & Hsh). specialize (Hobjs b m Hin). unfold in_shadow in Hsh.
    unfold SHMAPLO, KHI, two47, SB in *. cbn in *. lia.
  - unfold in_sshadow in Hs. pose proof ceil_pos. unfold SHMAPLO, KHI, HEAPLO, SB in *. cbn in *. lia.
  - unfold in_ishadow in Hi. unfold SHMAPLO, KHI, two47, SB in *. cbn in *. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma block_not_shz : forall E objs top (p n : Z) z,
  ablk_ok G p n ->
  (forall b m, In (b, m) (blocks_den E objs) -> 0 <= b /\ b + m <= two47) ->
  0 <= g_ro_lo G -> g_img_hi G <= two47 ->
  p <= z < p + n -> ~ shz E objs top z.
Proof.
  intros E objs top p n z (K1 & K2 & K3 & K4) Hobjs Gro Gimg Hz Hs.
  pose proof (shz_band E objs top z Hobjs Gro Gimg Hs). unfold SHMAPLO, KHI in *. lia.
Qed.
End Lib.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Blkfact.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).
Variable VSH : list (Z * Z).
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable KCAP : Z.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Variable RZ : GPS.rz_t.
Variable G : gtable.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
#[local] Notation kept_loc := (kept_loc PERMc SPTOPc G).
#[local] Notation shz := (AzKnowLib.shz G).

(* [comment removed for export] *)
Hypothesis AINV_zone : forall Lc Lf B C K M mdl b m, AINV Lc Lf B C K M mdl -> In (b, m) (Lc ++ Lf) -> ablk_ok G b m.
Hypothesis AINV_disj : forall Lc Lf B C K M mdl L1 L2 b m b' m',
  AINV Lc Lf B C K M mdl -> Lc = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2 ++ Lf) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINV_perm : forall Lc Lf B C K M mdl b m lo hi,
  AINV Lc Lf B C K M mdl -> In (b, m) Lc -> 1 <= m -> In (lo, hi) PERMc -> lo < hi -> b + m <= lo \/ hi <= b.
Hypothesis AINV_top : forall Lc Lf B C K M mdl, AINV Lc Lf B C K M mdl -> CEIL_run <= SPTOPc.
Hypothesis PERM_bnd : forall Lc Lf B C K M mdl z, AINV Lc Lf B C K M mdl -> in_wins PERMc z -> z < two47.
Hypothesis G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.

Theorem node_blkfact_sound : forall args, node1_stmt always (node_blkfact G args).
Proof.
  intros args. apply (AzNodesArith.add_facts_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
  intros cs cs' E fx R M model HC Hn. unfold node_blkfact in Hn.
  destruct args as [|b [|]]; try discriminate.
  destruct (remove_block b (a_vis cs)) as [[n live']|] eqn:Hrb; [|discriminate]. cbv zeta in Hn.
  destruct (xlo (kn cs) n) as [nlo|] eqn:Hnlo; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlf]. apply andb_prop in Hc as [Hc Hbf]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hn1 Htok]. apply Z.leb_le in Hn1.
  pose proof (co_know HC) as HK. set (MR := GPS.Mr SHC VSH E cs model M) in HK. unfold live_flat in Hlf.
  destruct (remove_block_split _ _ _ _ Hrb) as (L1 & L2 & HL & HL').
  destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htop.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct (floor_win (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)) as [[fwb fwo] fwl] eqn:Hfw.
  destruct (floor_win_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk fwb fwo fwl HK Htok Htop (co_floor HC) Hfw) as [FWlo ->].
  destruct (top_ok_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk HK Htok Htop) as (TOPEQ & _ & TOPR & _).
  pose proof (xlo_sound SEGS E MR (kn cs) n nlo HK Hnlo) as Nlo.
  assert (Hinv : In (b, n) (a_vis cs)) by (rewrite HL; apply in_app_iff; right; left; reflexivity).
  assert (Hin : In (uE E b, uE E n) (blocks_den E (a_vis cs))).
  { unfold blocks_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hinv]. }
  pose proof (AINV_zone _ _ _ _ _ _ _ _ _ (co_ainv HC) ltac:(apply in_app_iff; left; exact Hin)) as Hblk. pose proof Hblk as (K1 & K2 & K3 & K4).
  pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. pose proof GlzConst.ceil_lo as CL.
  pose proof (AINV_top _ _ _ _ _ _ _ (co_ainv HC)) as TOPC.
  pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn.
  assert (Hsum : bv_unsigned (edenot E (eadd b n)) = uE E b + uE E n).
  { unfold eadd. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. unfold uE in *. apply u64_lit. lia. }
  (* [comment removed for export] *)
  assert (Hsub : forall x, In x live' -> In x (a_vis cs)).
  { intros x Hx. rewrite HL, HL' in *. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  assert (Hdisj : forall b' m', In (b', m') (blocks_den E (live' ++ a_fake cs)) -> uE E b + uE E n <= b' \/ b' + m' <= uE E b).
  { intros b' m' Hin'. eapply (AINV_disj _ _ _ _ _ _ _ (blocks_den E L1) (blocks_den E L2)); [exact (co_ainv HC) | | ].
    - rewrite HL. unfold blocks_den. rewrite map_app. cbn [map fst snd]. reflexivity.
    - rewrite HL', !blocks_den_app in Hin'. first [rewrite <- app_assoc in Hin' | rewrite app_assoc in Hin']. exact Hin'. }
  assert (Hperm : forall lo hi, In (lo, hi) PERMc -> lo < hi -> uE E b + uE E n <= lo \/ hi <= uE E b).
  { intros lo hi Hpin Hlh. eapply AINV_perm; [exact (co_ainv HC) | exact Hin | unfold uE in *; lia | exact Hpin | exact Hlh]. }
  assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((live' ++ a_fake cs) ++ a_ghost cs) = true).
  { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) Hlf x).
    rewrite <- app_assoc in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact (Hsub x Hx) | right; exact Hx]. }
  (* [comment removed for export] *)
  assert (Hgh : forall b' m', In (b', m') (blocks_den E (ghosts_ne (kn cs) (a_ghost cs))) ->
                 In (b', b' + m') PERMc /\ 1 <= m').
  { intros b' m' Hin'. unfold blocks_den in Hin'. apply in_map_iff in Hin' as [[gb gl] [Hgeq Hing]]. cbn [fst snd] in Hgeq. injection Hgeq as <- <-.
    unfold ghosts_ne in Hing. apply filter_In in Hing as [Hing Hgl]. cbn [snd] in Hgl.
    destruct (xlo (kn cs) gl) as [l|] eqn:Hxl; [|discriminate]. apply Z.leb_le in Hgl.
    pose proof (xlo_sound SEGS E MR (kn cs) gl l HK Hxl) as Hl. split; [| unfold uE in *; lia].
    rewrite <- (co_perm HC). unfold wins_den. apply in_map_iff. exists (gb, gl). split; [reflexivity | exact Hing]. }
  assert (Hobjs : forall b' m', In (b', m') (blocks_den E ((live' ++ a_fake cs) ++ ghosts_ne (kn cs) (a_ghost cs))) -> 0 <= b' /\ b' + m' <= two47).
  { intros b' m' Hin'. rewrite blocks_den_app in Hin'. apply in_app_iff in Hin' as [Hin'|Hin'].
    - assert (Hin2 : In (b', m') (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs))).
      { rewrite blocks_den_app in Hin'. apply in_app_iff in Hin' as [X|X]; apply in_app_iff; [left | right; exact X].
        unfold blocks_den in X |- *. apply in_map_iff in X as [x [Hx1 Hx2]]. apply in_map_iff. exists x. split; [exact Hx1 | exact (Hsub x Hx2)]. }
      pose proof (AINV_zone _ _ _ _ _ _ _ _ _ (co_ainv HC) Hin2) as (Z1 & Z2 & _). unfold GlzConst.PTRLO in Z1. unfold two47 in *. lia.
    - destruct (Hgh b' m' Hin') as [Hpin Hm1].
      pose proof (PERM_bnd _ _ _ _ _ _ _ (b' + m' - 1) (co_ainv HC) ltac:(exists b', (b' + m'); split; [exact Hpin | lia])) as PB.
      unfold blocks_den in Hin'. apply in_map_iff in Hin' as [[gb gl] [Hgeq _]]. cbn [fst snd] in Hgeq. injection Hgeq as <- <-.
      pose proof (u64_range (edenot E gb)). unfold two47 in *. unfold uE in *. lia. }
  eexists. split; [reflexivity|].
  unfold know_ok. apply Forall_app. split; [|apply Forall_app; split].
  - (* [comment removed for export] *)
    unfold block_place. rewrite Hfw.
    repeat apply Forall_cons; [| | | | | apply Forall_nil]; cbn [kentry_ok].
    + cbv delta [GlzConst.PTRLO GlzConst.PTRHI AzPlanCore.APC.PTRHI] in *. unfold uE in *. lia.
    + rewrite Hsum. cbv delta [GlzConst.PTRLO GlzConst.PTRHI AzPlanCore.APC.PTRHI] in *. unfold uE in *. lia.
    + rewrite !estart_SA. cbn [a_base a_off]. unfold elenZ. left. unfold uE in *. lia.
    + rewrite !estart_SA. cbn [edenot a_base a_off]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E) by lia. unfold elenZ. unfold uE in *. lia.
    + rewrite !estart_SA. cbn [edenot a_base a_off]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E) by (unfold SHMAPLEN, SHMAPLO, KHI; lia).
      unfold elenZ, SHMAPLEN, SHMAPLO, KHI in *. unfold uE in *. lia.
  - (* [comment removed for export] *)
    eapply (disj_facts_ok SEGS E MR MR (kn cs) b n _ (edenot E b)); [exact HK | | reflexivity |].
    + apply forallb_forall. intros x Hx. apply in_app_iff in Hx as [Hx|Hx].
      * exact (proj1 (forallb_forall _ _) Hflat' x ltac:(apply in_app_iff; left; exact Hx)).
      * unfold ghosts_ne in Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (forallb_forall _ _) Hflat' x ltac:(apply in_app_iff; right; exact Hx)).
    + rewrite blocks_den_app. intros b' m' Hin'. apply in_app_iff in Hin' as [Hin'|Hin']; [exact (Hdisj b' m' Hin')|].
      destruct (Hgh b' m' Hin') as [Hpin Hm1].
      destruct (Hperm b' (b' + m') Hpin ltac:(lia)) as [X|X]; unfold uE in *; lia.
  - (* [comment removed for export] *)
    rewrite kdisj_of_factsH_nil.   (* [comment removed for export] *)
    eapply (kdisj_of_facts_ok SEGS E MR MR (kn cs)); [exact HK | reflexivity | | constructor].
    intros K b0 off len HKin HKR Hl.
    assert (HKok : kentry_ok SEGS E MR K).
    { assert (HKc : know_ok SEGS E MR (kn_cutout (kn_cutout (kn cs) spb (spk - 0) (ELit 0)) (ELit 0) (g_errno G) (ELit 4))).   (* [comment removed for export] *)
      { eapply know_ok_cutout; [eapply know_ok_cutout; [exact HK|]; intros; reflexivity|]. intros; reflexivity. }
      rewrite keep_owned_eq in HKin. unfold keep_owned_ref in HKin. rewrite Hsp in HKin.
      repeat (apply in_app_iff in HKin as [HKin'|HKin]; [apply filter_In in HKin' as [HKin' _]; first [exact (proj1 (Forall_forall _ _) HK K HKin') | exact (proj1 (Forall_forall _ _) HKc K HKin')] |]).
      apply filter_In in HKin as [HKin _]. exact (proj1 (Forall_forall _ _) HK K HKin). }
    pose proof (kentry_range_foot SEGS E MR K b0 off len HKok HKR) as HF.
    destruct (Z_lt_ge_dec (uE E b + uE E n) (uE E b0 + off + 1)) as [|Hge1]; [left; unfold uE in *; lia|].
    destruct (Z_lt_ge_dec (uE E b0 + off + uE E len) (uE E b + 1)) as [|Hge2]; [right; unfold uE in *; lia|].
    exfalso. set (z := Z.max (uE E b) (uE E b0 + off)).
    assert (Hz1 : uE E b <= z < uE E b + uE E n) by (unfold z; unfold uE in *; lia).
    assert (Hz2 : uE E b0 + off <= z < uE E b0 + off + uE E len) by (unfold z; unfold uE in *; lia).
    pose proof (keep_owned_loc SEGS PERMc SPTOPc G 0 E MR (kn cs) (live' ++ a_fake cs) (a_ghost cs) ((live' ++ a_fake cs) ++ ghosts_ne (kn cs) (a_ghost cs))
                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk (nxt cs) K z b0 off len
                  HK Hflat' (co_perm HC) (co_top HC) Hsp (co_floor HC) HKin HKR ltac:(unfold in_kfoot; rewrite HF, estart_SA; unfold uE in *; lia)) as LOC.
    destruct LOC as [LOC|SH].
    + refine (block_not_kept_loc PERMc SPTOPc G (blocks_den E (live' ++ a_fake cs)) (uE E b) (uE E n) z Hblk ltac:(lia) TOPC Hdisj Hperm Hz1 LOC).
    + refine (block_not_shz G E _ _ (uE E b) (uE E n) z Hblk Hobjs ltac:(lia) ltac:(pose proof GlzConst.ceil_hi; unfold GlzConst.PTRHI, two47 in *; lia) Hz1 SH).
Qed.

Corollary node_blkfact_obl : AzContracts.OBL_blkfact SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. exact node_blkfact_sound. Qed.
End Blkfact.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Alloc.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).
Variable VSH : list (Z * Z).
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
(* [comment removed for export] *)
Variable AINVN : Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable KCAP : Z.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable G : gtable.
Variable bcap ccap : Z.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.

(* [comment removed for export] *)
Definition ifacts (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) : Prop :=
  (forall Lc Lf B C K M mdl, X Lc Lf B C K M mdl ->
     Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                       /\ (u (fst iv) + u (snd iv) <= img_lo A \/ img_hi A <= u (fst iv))) (m_vm_lazy mdl))
  /\ (forall Lc Lf B C K M mdl b n (a : word), X Lc Lf B C K M mdl -> In (b, n) (Lc ++ Lf) -> b <= u a < b + n -> lz mdl a = false)
  /\ (forall Lc Lf B C K M mdl (a : word), X Lc Lf B C K M mdl -> in_wins PERMc (u a) -> lz mdl a = false)
  /\ (forall Lc Lf B C K M mdl, X Lc Lf B C K M mdl -> CEIL_run <= SPTOPc)
  /\ (forall Lc Lf B C K M mdl z, X Lc Lf B C K M mdl -> in_pshadow PERMc z -> in_shv VSH z = true \/ in_shc SHC z = true)
  /\ (forall Lc Lf B C K M mdl z, X Lc Lf B C K M mdl -> in_wins PERMc z -> z < two47)
  /\ (forall Lc Lf B C K M mdl b m, X Lc Lf B C K M mdl -> In (b, m) (Lc ++ Lf) -> ablk_ok G b m).   (* [comment removed for export] *)
Hypothesis AINV_if : ifacts AINV.
Hypothesis AINVN_if : forall n, ifacts (AINVN n).
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SHC_stack : forall z, in_sshadow z -> in_shc SHC z = true.
Hypothesis SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G.
Hypothesis G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.   (* [comment removed for export] *)
Hypothesis GKCAP_le : GKCAP <= KCAP.
Hypothesis FPC_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo.

#[local] Notation cs_okX X := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH X KCAP FTOPc FXOK UINV).
#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
#[local] Notation node1_stmtN := (GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
#[local] Notation Mr := (GPS.Mr SHC VSH).
#[local] Notation hid := (GPS.hid SHC VSH).
#[local] Notation kept_loc := (kept_loc PERMc SPTOPc G).
#[local] Notation shz := (AzKnowLib.shz G).
#[local] Notation nmalloc_pre X := (AzNSpec.nmalloc_pre SEGS SPTOPc G X FXOK FPC bcap ccap).
#[local] Notation nmalloc_post_ok X := (AzNSpec.nmalloc_post_ok SEGS SWIN PERMc G X FXOK).
#[local] Notation nmalloc_post_null X := (AzNSpec.nmalloc_post_null SEGS SWIN PERMc G X FXOK).

(* [comment removed for export] *)
Section IF.
Variable X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HX : ifacts X.
Lemma if_facts : forall Lc Lf B C K M mdl, X Lc Lf B C K M mdl ->
     Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                       /\ (u (fst iv) + u (snd iv) <= img_lo A \/ img_hi A <= u (fst iv))) (m_vm_lazy mdl).
Proof. exact (proj1 HX). Qed.
Lemma if_nolazy : forall Lc Lf B C K M mdl b n (a : word), X Lc Lf B C K M mdl -> In (b, n) (Lc ++ Lf) -> b <= u a < b + n -> lz mdl a = false.
Proof. exact (proj1 (proj2 HX)). Qed.
Lemma if_perm_nolazy : forall Lc Lf B C K M mdl (a : word), X Lc Lf B C K M mdl -> in_wins PERMc (u a) -> lz mdl a = false.
Proof. exact (proj1 (proj2 (proj2 HX))). Qed.




(* [comment removed for export] *)
Lemma hid_app_falseX : forall E cs mdl B C K M (a : word),
  X (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  in_blocks (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)) (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a \/ in_wins SWIN (u a)
  \/ (g_img_lo G <= u a < g_img_hi G) ->
  hid E cs mdl a = false.
Proof. exact (hid_app_false A SWIN PERMc SHC VSH X G if_facts A_img_hi A_img_lo if_nolazy if_perm_nolazy SWIN_img). Qed.
Lemma Mr_appX : forall E cs mdl B C K M (a : word),
  X (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) B C K M mdl ->
  in_blocks (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs)) (u a) \/ in_wins PERMc (u a) \/ CEIL_run <= u a \/ in_wins SWIN (u a)
  \/ (g_img_lo G <= u a < g_img_hi G) ->
  Mr E cs mdl M a = M a.
Proof. exact (Mr_app A SWIN PERMc SHC VSH X G if_facts A_img_hi A_img_lo if_nolazy if_perm_nolazy SWIN_img). Qed.
End IF.

(* [comment removed for export] *)
Ltac errno_herr X HX HApre HApost Herrk :=
  let a := fresh "a" in let Hew := fresh "Hew" in let HM := fresh "HMRa" in let Hai := fresh "Hai" in
  intros a Hew HM;
  assert (Hai : g_img_lo G <= bv_unsigned a < g_img_hi G) by (unfold errw in Hew; pose proof G_errno_img; lia);
  lazymatch goal with |- ?f a <> None => first [subst f | idtac] end;
  lazymatch type of HM with ?g a <> None => first [subst g | idtac] end;
  unfold GPS.Mr in HM |- *;
  rewrite (mrestrict_visible _ _ _ (hid_app_falseX X HX _ _ _ _ _ _ _ a HApost (or_intror (or_intror (or_intror (or_intror Hai))))));
  rewrite (mrestrict_visible _ _ _ (hid_app_falseX X HX _ _ _ _ _ _ _ a HApre (or_intror (or_intror (or_intror (or_intror Hai)))))) in HM;
  exact (Herrk a Hew HM).

(* [comment removed for export] *)
Ltac node_alloc_gates Hn Hco cs cs' :=
  unfold node_alloc in Hn;
  rewrite Hco in Hn; cbv zeta in Hn;
  lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hfpc; [discriminate|] end;
  destruct (xlo (kn cs) (reg cs 10)) as [nlo|] eqn:Hnlo; [|discriminate];
  destruct (xhi (kn cs) (reg cs 10)) as [nhi|] eqn:Hnhi; [|discriminate];
  destruct (cost_hi (kn cs) (a_vis cs)) as [ch|] eqn:Hch; [|discriminate];
  destruct (xhi (kn cs) (a_meter cs)) as [mh|] eqn:Hmh; [|discriminate];
  lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate];
  apply andb_prop in Hc as [Hc Hnv]; apply andb_prop in Hc as [Hc HKc]; apply andb_prop in Hc as [Hc HC'];
  apply andb_prop in Hc as [Hc HB']; apply andb_prop in Hc as [Hn1 HnN];
  apply Z.leb_le in Hn1; apply Z.leb_le in HnN; apply Z.leb_le in HB'; apply Z.leb_le in HC'; apply Z.leb_le in HKc;
  apply some_inj in Hn; subst cs' end.   (* [comment removed for export] *)

Ltac node_alloc_nb_gates Hn Hco cs cs' :=
  unfold node_alloc_nb in Hn;
  rewrite Hco in Hn; cbv zeta in Hn;
  lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hfpc; [discriminate|] end;
  cbn [negb] in Hn;
  lazymatch type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hgate; cbn [negb] in Hn; [|discriminate];
  apply andb_prop in Hgate as [Hgate Hnvlt]; apply andb_prop in Hgate as [Hgate Hmt]; apply andb_prop in Hgate as [Hvis Hr10];
  apply expr_eqb_eq in Hr10; apply expr_eqb_eq in Hmt; apply (proj1 (Nat.ltb_lt _ _)) in Hnvlt;
  destruct (xlo (kn cs) (reg cs 10)) as [nlo|] eqn:Hnlo; [|discriminate];
  destruct (xhi (kn cs) (reg cs 10)) as [nhi0|] eqn:Hnhi; [|discriminate];
  lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate];
  apply andb_prop in Hc as [Hn1 HnN]; apply Z.leb_le in Hn1; apply Z.leb_le in HnN;
  apply some_inj in Hn; subst cs' end end.

(* [comment removed for export] *)
Ltac node_alloc_core_prologue HC Hco Hnlo Hstk stk entry cs ret nlo E fx R M model :=
  pose proof (call_ok_stk_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV G stk entry cs ret E fx R M model Hstk HC Hco) as CO;
  cbv zeta in CO;
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp;
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hsphi & Hstkw & Hflat);
  unfold node_alloc_core in *;
  pose proof (co_regs HC) as HR; pose proof (co_know HC) as HK;
  set (MR := GPS.Mr SHC VSH E cs model M) in HK;
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle);
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]; pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb;
  pose proof (xlo_sound SEGS E MR (kn cs) (reg cs 10) nlo HK Hnlo) as Nlo;
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10;
  pose proof (reg_sound E cs R 8 HR ltac:(lia)) as R8;
  set (n := uE E (reg cs 10)) in *;
  set (Lc := blocks_den E (a_vis cs)); set (Lf := blocks_den E (a_fake cs)).

(* [comment removed for export] *)
Definition NBF (nv mv : nat) : Prop :=
  forall E, UINV E -> mcost (uE E (EVar nv)) <= bcap /\ MCNT <= ccap /\ uE E (EVar mv) + kcost (uE E (EVar nv)) <= GKCAP.

Lemma vis_nil : forall (l : list (expr * expr)), match l with [] => true | _ => false end = true -> l = [].
Proof. intros [|x l] H; [reflexivity | discriminate H]. Qed.

(* [comment removed for export] *)
Lemma node_alloc_core_pre_sound : forall stk (fpcreq : bool) entry cs ret nlo nhi mh E fx R M model,
  0 < stk < 2 ^ 40 ->
  cs_ok E cs fx R M model -> call_ok_stk nx0 G stk entry cs = Some ret ->
  (fpcreq && negb (fpc_x SEGS (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 8) (reg cs 2)))%bool = false ->
  xlo (kn cs) (reg cs 10) = Some nlo -> 1 <= nlo -> uE E (reg cs 10) <= nhi -> nhi <= NMAX ->
  bcost E (a_vis cs) + mcost nhi <= bcap -> Z.of_nat (length (a_vis cs)) + MCNT <= ccap ->
  uE E (a_meter cs) <= mh -> mh + kcost nhi <= GKCAP ->
  pc cs = entry
  /\ nmalloc_pre AINV fpcreq fx R M model (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs))
                 (uE E (a_meter cs)) ret (uE E (reg cs 10)) (uE E (reg cs 2)) stk.
Proof. pose proof G_img_hull as GIH_. pose proof G_img_ceil as GIC_. pose proof G_errno_img as GEI_.   (* [comment removed for export] *)
  intros stk fpcreq entry cs ret nlo nhi mh E fx R M model Hstk HC Hco Hfpc Hnlo Hn1 Nhi HnN HB' HC' Nmh HKc.
  node_alloc_core_prologue HC Hco Hnlo Hstk stk entry cs ret nlo E fx R M model.
  split; [exact Hpc|]. unfold AzNSpec.nmalloc_pre.
  split; [exact (co_halt HC)|]. split; [exact (co_fx HC)|]. split; [exact (co_ainv HC)|].
  split.
  { unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
    split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|].
    intros a Ha. apply Hstkw. exact Ha. }
  split; [unfold n, uE; rewrite <- R10; reflexivity|]. split; [unfold n, uE in *; lia|].
  split.
  { (* [comment removed for export] *)
    intros Hreq. rewrite Hreq in Hfpc. cbn [andb] in Hfpc. apply negb_false_iff in Hfpc.
    change (Z.of_nat 8) with 8 in R8. rewrite R8.
    apply FPC_kfpc. eapply fpc_Mr_full. exact (fpc_x_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 8) (reg cs 2) HK (co_floor HC) Hfpc). }
  split; [unfold mcost in *; enough (X : n <= nhi) by lia; exact Nhi|].
  split; [unfold bcount in *; lia|].
  unfold kcost in *. enough (X : n <= nhi /\ uE E (a_meter cs) <= mh) by lia. split; [exact Nhi | exact Nmh].
Qed.

(* [comment removed for export] *)
Lemma node_alloc_pre_sound : forall stk fpcreq entry cs cs' ret E fx R M model,
  0 < stk < 2 ^ 40 ->
  cs_ok E cs fx R M model -> call_ok_stk nx0 G stk entry cs = Some ret -> node_alloc SEGS nx0 G bcap ccap stk fpcreq entry cs = Some cs' ->
  pc cs = entry
  /\ nmalloc_pre AINV fpcreq fx R M model (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs))
                 (uE E (a_meter cs)) ret (uE E (reg cs 10)) (uE E (reg cs 2)) stk.
Proof.
  intros stk fpcreq entry cs cs' ret E fx R M model Hstk HC Hco Hn.
  node_alloc_gates Hn Hco cs cs'.
  pose proof (co_know HC) as HK.
  destruct (cost_hi_sound SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) (a_vis cs) ch HK Hch) as [Hcost _].
  apply (node_alloc_core_pre_sound stk fpcreq entry cs ret nlo nhi mh E fx R M model Hstk HC Hco Hfpc Hnlo Hn1).
  - exact (xhi_sound SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) (reg cs 10) nhi HK Hnhi).
  - exact HnN.
  - lia.
  - exact HC'.
  - exact (xhi_sound SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) (a_meter cs) mh HK Hmh).
  - exact HKc.
Qed.

(* [comment removed for export] *)
Lemma node_alloc_nb_pre_sound : forall nv mv stk entry cs cs' ret E fx R M model,
  NBF nv mv -> 0 < stk < 2 ^ 40 ->
  cs_ok E cs fx R M model -> call_ok_stk nx0 G stk entry cs = Some ret -> node_alloc_nb SEGS nx0 G stk entry nv mv cs = Some cs' ->
  pc cs = entry
  /\ nmalloc_pre AINV true fx R M model (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs))
                 (uE E (a_meter cs)) ret (uE E (reg cs 10)) (uE E (reg cs 2)) stk.
Proof.
  intros nv mv stk entry cs cs' ret E fx R M model HNB Hstk HC Hco Hn.
  node_alloc_nb_gates Hn Hco cs cs'.
  pose proof (co_know HC) as HK.
  destruct (HNB E (co_uinv HC)) as (NB1 & NB2 & NB3). rewrite <- Hr10 in NB1, NB3. rewrite <- Hmt in NB3.
  apply vis_nil in Hvis.
  pose proof (xhi_sound SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) (reg cs 10) nhi0 HK Hnhi) as Nhi0.
  apply (node_alloc_core_pre_sound stk true entry cs ret nlo (uE E (reg cs 10)) (uE E (a_meter cs)) E fx R M model Hstk HC Hco Hfpc Hnlo Hn1).
  - lia.
  - unfold uE in *. lia.
  - rewrite Hvis. cbn [bcost]. lia.
  - rewrite Hvis. cbn [length Z.of_nat]. lia.
  - lia.
  - exact NB3.
Qed.

Lemma G_ro_lo_img : g_img_lo G <= g_ro_lo G. Proof. pose proof G_img_hull. lia. Qed.


Lemma call_ok_stk_top_ok : forall stk entry cs ret,
  call_ok_stk nx0 G stk entry cs = Some ret -> top_ok (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) = true.
Proof.
  intros stk entry cs ret H. unfold call_ok_stk in H.
  destruct (negb (Z.eqb (pc cs) entry)); [discriminate|].
  destruct (ret_lit cs) as [ret'|]; [|discriminate]. destruct (reg_lit cs 4) as [tp|]; [|discriminate].
  cbv zeta in H. destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hfl].
  exact (in_floor_top_ok _ _ _ _ _ _ _ Hfl).
Qed.

(* [comment removed for export] *)
Lemma node_alloc_core_ok_sound : forall stk entry cs ret nlo nhi mh E fx R M model fx' R' M' mdl' (p : word),
  0 < stk < 2 ^ 40 ->
  cs_ok E cs fx R M model -> call_ok_stk nx0 G stk entry cs = Some ret ->
  xlo (kn cs) (reg cs 10) = Some nlo -> 1 <= nlo -> uE E (reg cs 10) <= nhi -> nhi <= NMAX ->
  uE E (a_meter cs) <= mh -> mh + kcost nhi <= GKCAP -> expr_vars_lt (nxt cs) (reg cs 10) = true ->
  nmalloc_post_ok AINV R M model (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs))
                  (uE E (reg cs 10)) (uE E (reg cs 2)) stk fx' R' M' mdl' p ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' (node_alloc_core G stk ret nlo cs) fx' R' M' mdl'
             /\ pc (node_alloc_core G stk ret nlo cs) = ret /\ m_fs mdl' = m_fs model.
Proof. pose proof sfloor_ge as SFG_.
  intros stk entry cs ret nlo nhi mh E fx R M model fx' R' M' mdl' p Hstk HC Hco Hnlo Hn1 Nhi HnN Nmh HKc Hnv.
  pose proof (call_ok_stk_top_ok _ _ _ _ Hco) as Htok.
  node_alloc_core_prologue HC Hco Hnlo Hstk stk entry cs ret nlo E fx R M model.
  intros (HFX' & Hkept & Ha0 & Hpal & Hblk & Hal2k & Hdisj & Hpdisj & Hdef & Hshk & Hshw & Hfr & Herrk & Hscr & HAINV' & (Hh' & Hfs' & Hfds')).
  pose proof AINV_if as IFA. destruct AINV_if as (AINV_facts & AINV_nolazy & AINV_perm_nolazy & AINV_top & PERM_vsh & PERM_bnd & AINV_zone).
  set (v := nxt cs) in *.
  set (E1 := ext1 E v p).
  set (E' := ext_call E1 (S v) R').
  assert (Hag1 : env_agree v E E1) by apply ext1_agree.
  assert (Hag2 : env_agree (S v) E1 E') by apply ext_call_agree.
  assert (Hag : env_agree v E E') by (eapply env_agree_trans; [exact Hag1 | eapply env_agree_le; [exact Hag2 | lia]]).
  assert (Hpv : edenot E' (EVar v) = p).
  { cbn [edenot]. rewrite <- (proj1 Hag2 v ltac:(lia)). unfold E1. apply ext1_at. }
  assert (Hne : edenot E' (reg cs 10) = edenot E (reg cs 10)) by (symmetry; eapply edenot_agree'; [exact Hag | exact Hnv]).
  assert (Hnr : 0 <= n) by (unfold n, uE; pose proof (u64_range (edenot E (reg cs 10))); lia).
  assert (HKE' : know_ok SEGS E' MR (kn cs)) by (eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK]).
  assert (HLc : blocks_den E' (a_vis cs) = Lc) by (unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
  assert (HLf : blocks_den E' (a_fake cs) = Lf) by (unfold Lf; eapply blocks_den_agree; [exact Hag | exact Ffk]).
  pose proof Hblk as (K1 & K2 & K3 & K4). pose proof (u64_range p) as Hpr.
  pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. pose proof GlzConst.ceil_lo as CL. unfold GlzConst.PTRLO in K1.
  match goal with |- exists _, _ /\ GPS.cs_ok _ _ _ _ _ _ _ _ _ _ _ _ ?c _ _ _ _ /\ _ => set (cs' := c) in * end.
  (* [comment removed for export] *)
  assert (HMT : uE E' (eadd (a_meter cs) (ELit EVT)) = uE E (a_meter cs) + kcost n).   (* [comment removed for export] *)
  { assert (EMT : uE E' (a_meter cs) = uE E (a_meter cs)) by (eapply uE_agree; [exact Hag | exact Fmt]).
    assert (ELT : uE E' (ELit EVT) = EVT) by (apply uE_lit; unfold EVT; lia).
    assert (BND : uE E (a_meter cs) + EVT < 2 ^ 64).
    { clear - Nmh HKc Nhi Hnr GKCAP_le. unfold kcost, EVT, GKCAP in *. unfold n, uE in *. lia. }
    rewrite uE_eadd_nowrap by (rewrite EMT, ELT; exact BND). rewrite EMT, ELT. unfold kcost. lia. }
  assert (HA' : AINV (blocks_den E' (a_vis cs')) (blocks_den E' (a_fake cs')) (bcost E' (a_vis cs')) (bcount (a_vis cs'))
                     (uE E' (a_meter cs')) M' mdl').
  { unfold cs'. cbn [a_vis a_fake a_meter]. rewrite blocks_den_cons. cbn [fst snd bcost]. rewrite HLc, HLf, HMT.
    unfold uE at 1 2 3. rewrite Hpv, Hne. fold (uE E (reg cs 10)). fold n.
    rewrite (bcost_agree v E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    replace (n + MBLK + bcost E (a_vis cs)) with (bcost E (a_vis cs) + mcost n) by (unfold mcost, AzIface.MBLK, GPS.MBLK; lia).
    replace (bcount ((EVar v, reg cs 10) :: a_vis cs)) with (bcount (a_vis cs) + MCNT) by (unfold bcount, MCNT; cbn [length]; lia).
    exact HAINV'. }
  set (MR' := Mr E' cs' mdl' M').
  (* [comment removed for export] *)
  assert (INB : forall z, u p <= z < u p + n -> in_blocks (blocks_den E' (a_vis cs') ++ blocks_den E' (a_fake cs')) z).
  { intros z Hz. unfold cs'. cbn [a_vis a_fake]. rewrite blocks_den_cons. cbn [fst snd app].
    exists (uE E' (EVar v)), (uE E' (reg cs 10)). split; [left; reflexivity|]. unfold uE. rewrite Hpv, Hne. fold (uE E (reg cs 10)). fold n. lia. }
  assert (VB : forall a : word, u p <= u a < u p + n -> MR' a = M' a).
  { intros a Ha. unfold MR'. eapply (Mr_appX AINV IFA); [exact HA'|]. left. exact (INB (u a) Ha). }
  assert (VS : forall a : word, in_shadow SB (u p) n (u a) -> MR' a = M' a).
  { intros a Ha. unfold MR'. apply (Mr_shadow SHC VSH G SHC_stack SHC_image). left. unfold cs'. cbn [a_vis a_fake]. cbn [app]. rewrite blocks_den_cons. cbn [fst snd].
    exists (uE E' (EVar v)), (uE E' (reg cs 10)). split; [left; reflexivity|]. unfold uE. rewrite Hpv, Hne. exact Ha. }
  (* [comment removed for export] *)
  destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htop.
  destruct (floor_win (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)) as [[fwb fwo] fwl] eqn:Hfw.
  destruct (floor_win_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk fwb fwo fwl HK Htok Htop (co_floor HC) Hfw) as [FWlo ->].
  assert (Hfwb : edenot E' fwb = edenot E fwb).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. exact (floor_win_vars v (a_maps cs) (a_brk cs) (a_ylo cs) fwb fwo _ Fmaps Fbrk Hfw). }
  (* [comment removed for export] *)
  assert (Hobjs : forall b' m', In (b', m') (blocks_den E (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))) -> 0 <= b' /\ b' + m' <= two47).
  { intros b' m' Hin'.
    destruct (objs_ghost_ext SEGS PERMc E MR cs (a_vis cs) (a_fake cs) (fun x => In x (Lc ++ Lf)) HK (co_perm HC)
                ltac:(intros x Hx; unfold Lc, Lf; rewrite <- blocks_den_app; exact Hx) (b', m') Hin') as [HL|[HP Hm]].
    - pose proof (AINV_zone _ _ _ _ _ _ _ _ _ (co_ainv HC) HL) as (Z1 & Z2 & _). unfold GlzConst.PTRLO in Z1. unfold two47 in *. lia.
    - cbn [fst snd] in HP, Hm. pose proof (PERM_bnd _ _ _ _ _ _ _ (b' + m' - 1) (co_ainv HC) ltac:(exists b', (b' + m'); split; [exact HP | lia])) as PB.
      unfold blocks_den in Hin'. apply in_map_iff in Hin' as [[gb gl] [Hgeq _]]. cbn [fst snd] in Hgeq. injection Hgeq as <- <-.
      pose proof (u64_range (edenot E gb)). unfold two47 in *. unfold uE in *. lia. }
  assert (Hpermd : forall lo hi, In (lo, hi) PERMc -> lo < hi -> u p + n <= lo \/ hi <= u p).
  { intros lo hi Hpin Hlh. destruct (Z_lt_le_dec lo (u p + n)) as [L1|L1]; [|left; lia]. destruct (Z_lt_le_dec (u p) hi) as [L2|L2]; [|right; lia].
    exfalso. apply (Hpdisj (Z.max lo (u p))); [exists lo, hi; split; [exact Hpin | lia] | clear - L1 L2 Hlh Hn1 Nlo; unfold n, uE in *; lia]. }
  assert (HdisjC : forall b m, In (b, m) (blocks_den E (a_vis cs ++ a_fake cs)) -> u p + n <= b \/ b + m <= u p).
  { intros b m Hin. apply Hdisj. unfold Lc, Lf. rewrite <- blocks_den_app. exact Hin. }
  exists E'. split; [|split; [|split; [reflexivity | exact Hfs']]].
  + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
  + constructor; try (unfold cs'; cbn [a_ss s_regs s_log s_know kn a_vis a_fake a_fbud a_meter a_ghost a_brk a_fd a_totsz a_eager a_maps a_ylo]).
    * (* [comment removed for export] *)
      unfold ret_regs.
      pose proof (regs_after_call E1 (s_regs (a_ss cs)) R R' (S v) (Some (EVar v))) as RA. cbn iota in RA. apply RA.
      -- eapply regs_ok_agree'; [exact Hag1 | exact Fsr | exact HR].
      -- eapply sr_vars_lt_mono; [exact Fsr | lia].
      -- apply kept_ok_of_callee_saved. exact Hkept.
      -- split; [cbn; apply Nat.leb_refl|]. cbn [edenot]. unfold E1. rewrite ext1_at. exact Ha0.
    * reflexivity.
    * (* [comment removed for export] *)
      fold cs'. fold MR'.
      assert (Hsum : edenot E' (eadd (EVar v) (reg cs 10)) = Z_to_bv 64 (u p + n)).
      { unfold eadd. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. cbn [edenot] in Hpv. rewrite Hpv, Hne. unfold v_add, n, uE. reflexivity. }
      assert (Hes : estart E' (SA (EVar v) 0) = u p) by (rewrite estart_SA, Hpv; lia).
      assert (Hel : elenZ E' (reg cs 10) = n) by (unfold elenZ, n, uE; rewrite Hne; reflexivity).
      unfold know_ok. apply Forall_app. split; [apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]|].
      -- (* [comment removed for export] *)
        destruct (Z.ltb 64512 nlo) eqn:Hbig; [|apply Forall_nil].
        apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. rewrite Hpv. split; [lia|].
        apply Z.ltb_lt in Hbig. specialize (Hal2k ltac:(clear - Hbig Nlo; unfold n, uE in *; lia)).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        clear - Hal2k Hpr. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      -- (* [comment removed for export] *)
        unfold block_rng. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [kentry_ok].
        ++ rewrite Hpv. unfold PTRLO, PTRHI, GlzConst.PTRLO, GlzConst.PTRHI in *. unfold n, uE in *. lia.
        ++ rewrite Hsum. unfold PTRLO, PTRHI, GlzConst.PTRLO, GlzConst.PTRHI in *. rewrite u64_lit by (unfold n, uE in *; lia). unfold n, uE in *; lia.
        ++ rewrite Hpv. split; [lia | exact Hpal].
      -- (* [comment removed for export] *)
        repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [kentry_ok].
        ++ rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|].
           intros d m Hd Hdm. apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
           intros x Hx. rewrite u64_lit in Hx by lia.
           unfold MR', GPS.Mr. rewrite (wview_mrestrict_eq SEGS).
           { eapply (store_ok_all SEGS M' 1 x); [change (Z.of_nat 1) with 1; pose proof (u64_range x); lia | exact (proj2 (Hdef x ltac:(lia))) | change (Z.of_nat 1) with 1; lia]. }
           eapply (hid_app_falseX AINV IFA); [exact HA'|]. left. exact (INB (u x) ltac:(lia)).
        ++ rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|].
           intros i Hi. rewrite (VB (Z_to_bv 64 (u p + i))) by (rewrite u64_lit by lia; lia).
           apply (Hdef (Z_to_bv 64 (u p + i))). rewrite u64_lit by lia. lia.
        ++ (* [comment removed for export] *)
           rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|]. split; [unfold two47 in *; lia|].
           intros z Hz.
           Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
           assert (SHV : MR' (Z_to_bv 64 (SB + z / 8)) = M' (Z_to_bv 64 (SB + z / 8))).
           { apply VS. rewrite u64_lit by (unfold SB in *; lia). unfold in_shadow, SB. lia. }
           rewrite SHV.
           exact (Hshk z Hz).
           Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      -- (* [comment removed for export] *)
        unfold block_sep. rewrite Hfw, ?kdisj_of_factsH_nil. apply Forall_app. split; [|apply Forall_app; split].
        ++ repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [kentry_ok]; rewrite Hes, Hel, estart_SA.
           ** cbn [a_base a_off]. rewrite Hfwb. left. unfold uE in *. lia.
           ** cbn [edenot a_base a_off]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E') by lia. lia.
           ** cbn [edenot a_base a_off]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E') by (unfold SHMAPLEN, SHMAPLO, KHI; lia).
              unfold SHMAPLEN, SHMAPLO, KHI in *. lia.
        ++ (* [comment removed for export] *)
          eapply (disj_facts_ok SEGS E' MR' MR (kn cs)); [exact HKE' | | exact Hpv |].
          ** rewrite !forallb_app in Hflat |- *. apply andb_prop in Hflat as [F1 F23]. apply andb_prop in F23 as [F2 F3].
             rewrite F1, F2. cbn [andb]. unfold ghosts_ne. apply forallb_forall. intros x Hx. apply filter_In in Hx as [Hx _].
             exact (proj1 (forallb_forall _ _) F3 x Hx).
          ** rewrite !blocks_den_app, HLc, HLf. intros b m Hin. unfold uE. rewrite Hne. fold (uE E (reg cs 10)). fold n.
             apply in_app_iff in Hin as [Hin|Hin]; [exact (Hdisj b m Hin)|].
             rewrite (blocks_den_agree v E E' (ghosts_ne (kn cs) (a_ghost cs)) Hag ltac:(unfold ghosts_ne; apply pairs_vars_lt_filter; exact (pairs_vars_lt_app_r _ _ _ Fallow))) in Hin.
             destruct (ghosts_ne_in SEGS PERMc E MR (kn cs) (a_ghost cs) b m HK (co_perm HC) Hin) as [Hw Hm].
             exact (Hpermd b (b + m) Hw ltac:(lia)).
        ++ (* [comment removed for export] *)
          eapply (kdisj_of_facts_ok SEGS E' MR' MR (kn cs)); [exact HKE' | exact Hpv | | constructor].
          intros K b off len HKin HKR Hl.
          assert (HKv : kentry_vars_lt v K = true).
          { pose proof (keep_owned_vars G stk (kn cs) (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs)) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v) as KV.
            rewrite kn_vars_lt_forallb in KV. exact (proj1 (forallb_forall _ _) KV K HKin). }
          assert (Hbe : uE E' b = uE E b /\ uE E' len = uE E len).
          { unfold uE. split; f_equal; symmetry; (eapply edenot_agree'; [exact Hag|]);
            destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?|[? ?] ?|? ? ?]; cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-;
              cbn [kentry_vars_lt saddr_vars_lt a_base expr_vars_lt] in HKv; repeat (apply andb_prop in HKv as [HKv ?]); first [reflexivity | exact HKv | assumption]. }
          destruct Hbe as [Hbe Hle]. rewrite Hbe, Hle in *. assert (Hn' : uE E' (reg cs 10) = n) by (unfold uE, n; rewrite Hne; reflexivity). rewrite Hn'.
          destruct (Z_lt_ge_dec (u p + n) (uE E b + off + 1)) as [|Hge1]; [left; lia|].
          destruct (Z_lt_ge_dec (uE E b + off + uE E len) (u p + 1)) as [|Hge2]; [right; lia|].
          exfalso. set (z := Z.max (u p) (uE E b + off)).
          assert (Hz1 : u p <= z < u p + n) by (unfold z; unfold n, uE in *; lia).
          assert (Hz2 : uE E b + off <= z < uE E b + off + uE E len) by (unfold z; unfold uE in *; lia).
          assert (HKok : kentry_ok SEGS E MR K).
          { assert (HKcut : know_ok SEGS E MR (kn_cutout (kn_cutout (kn cs) spb (spk - stk) (ELit stk)) (ELit 0) (g_errno G) (ELit 4))).   (* [comment removed for export] *)
            { eapply know_ok_cutout; [eapply know_ok_cutout; [exact HK|]; intros; reflexivity|]. intros; reflexivity. }
            pose proof HKin as HKin2. rewrite keep_owned_eq in HKin2. unfold keep_owned_ref in HKin2. rewrite Hsp in HKin2.
            repeat (apply in_app_iff in HKin2 as [HKin'|HKin2]; [apply filter_In in HKin' as [HKin' _]; first [exact (proj1 (Forall_forall _ _) HK K HKin') | exact (proj1 (Forall_forall _ _) HKcut K HKin')] |]).
            apply filter_In in HKin2 as [HKin2 _]. exact (proj1 (Forall_forall _ _) HK K HKin2). }
          pose proof (kentry_range_foot SEGS E MR K b off len HKok HKR) as HF.
          assert (Hflat2 : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) = true).
          { first [rewrite <- app_assoc | rewrite app_assoc]; exact Hflat. }
          assert (HKin3 : In K (keep_owned G stk (kn cs) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
          { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
          destruct (keep_owned_loc SEGS PERMc SPTOPc G stk E MR (kn cs) (a_vis cs ++ a_fake cs) (a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                      (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K z b off len
                      HK Hflat2 (co_perm HC) (co_top HC) Hsp (co_floor HC) HKin3 HKR ltac:(unfold in_kfoot; rewrite HF, estart_SA; unfold uE in *; lia)) as [LOC|SH].
          ** exact (block_not_kept_loc PERMc SPTOPc G (blocks_den E (a_vis cs ++ a_fake cs)) (u p) n z Hblk G_ro_lo_img (AINV_top _ _ _ _ _ _ _ (co_ainv HC)) HdisjC Hpermd Hz1 LOC).
          ** exact (block_not_shz G E _ _ (u p) n z Hblk Hobjs ltac:(pose proof G_img_hull; lia) ltac:(unfold two47 in *; lia) Hz1 SH).
      -- (* [comment removed for export] *)
        apply (know_ok_agree' SEGS v E E'); [exact Hag | apply keep_owned_vars |].
        unfold know_ok. apply Forall_forall. intros K HKin.
        assert (Hflat2 : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) = true).
        { first [rewrite <- app_assoc | rewrite app_assoc]; exact Hflat. }
        assert (HKin3 : In K (keep_owned G stk (kn cs) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                                (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
        { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
        eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G stk E MR MR' (kn cs) (a_vis cs ++ a_fake cs) (a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K
                  ltac:(lia) HK Hflat2 (co_perm HC) (co_top HC) Hsp); [| exact (co_floor HC) | | | | | exact HKin3].   (* [comment removed for export] *)
        ++ pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
        ++ intros a Ha. unfold MR', MR.
           assert (LP : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs))).
           { intros x Hx. rewrite blocks_den_app in Hx. exact Hx. }
           assert (LQ : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E' (a_vis cs') ++ blocks_den E' (a_fake cs'))).
           { intros x Hx. unfold cs'. cbn [a_vis a_fake]. rewrite blocks_den_cons, HLc, HLf. cbn [app]. right.
             rewrite blocks_den_app in Hx. exact Hx. }
           assert (LNK : forall x : word, in_blocks (blocks_den E (a_vis cs ++ a_fake cs)) (u x) -> in_blocks Lc (u x) \/ in_blocks Lf (u x)).
           { intros x Hb. rewrite blocks_den_app in Hb. apply in_blocks_app2 in Hb. exact Hb. }
           exact (Mr_kept_app A SWIN PERMc SPTOPc SHC VSH AINV G AINV_facts A_img_hi A_img_lo AINV_nolazy AINV_perm_nolazy AINV_top SWIN_img G_ro_lo_img
                    E E' cs cs' model mdl' M M' _ _ _ _ _ _ (a_vis cs ++ a_fake cs) (reg cs 2) stk (co_ainv HC) HA' LP LQ (GPS.sfloor_stk _ _ Hsplo) ltac:(lia) Lc Lf Hfr LNK a Ha).
        ++ intros a Ha. unfold MR'.
           assert (HH : hid E' cs' mdl' a = false).
           { eapply (hid_app_falseX AINV IFA); [exact HA'|]. right; right; left. unfold uE in *. lia. }
           unfold GPS.Mr at 1. rewrite (mrestrict_visible _ _ _ HH). rewrite store_ok1_Mr by exact HH. apply Hscr. unfold scratch, uE in *. lia.
        ++ (* [comment removed for export] *) errno_herr AINV IFA (co_ainv HC) HA' Herrk.
        ++ intros a Ha. unfold MR', MR.
           assert (OP : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E (a_vis cs ++ a_fake cs))) by (intros x Hx; exact Hx).
           assert (OQ : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E' (a_vis cs' ++ a_fake cs'))).
           { intros x Hx. unfold cs'. cbn [a_vis a_fake]. cbn [app]. rewrite blocks_den_cons. right.
             rewrite blocks_den_app in Hx |- *. rewrite HLc, HLf. exact Hx. }
           assert (ONK : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (Lc ++ Lf)).
           { intros x Hx. unfold Lc, Lf. rewrite <- blocks_den_app. exact Hx. }
           exact (Mr_kept_shadow SWIN PERMc SPTOPc SHC VSH AINV G AINV_top SHC_stack SHC_image PERM_vsh E E' cs cs' model mdl' M M' _ _ _
                    (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs)) (reg cs 2) stk (co_ainv HC)
                    (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OP) (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OQ)
                    Lc Lf Hfr (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) ONK) a Ha).
    * exact Hh'.
    * rewrite Hfs'. exact (co_fs HC).
    * eapply fds_ok_model; [exact Hfds' | exact Hfs' |]. eapply APS.fds_ok_agree; [exact Hag | exact Ffd | exact (co_fds HC)].
    * fold cs'. exact HA'.
    * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
    * exact HFX'.
    * rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
    * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
    * rewrite HMT. clear - Nmh HKc Nhi GKCAP_le Hnr. unfold kcost in *. unfold n, uE in *. lia.
    * rewrite (uE_agree v E E' (a_fbud cs) Hag Ffb). exact (co_fbud HC).
    * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
Qed.

(* [comment removed for export] *)
Lemma node_alloc_ok_sound : forall stk fpcreq entry cs cs' ret E fx R M model fx' R' M' mdl' (p : word),
  0 < stk < 2 ^ 40 ->
  cs_ok E cs fx R M model -> call_ok_stk nx0 G stk entry cs = Some ret -> node_alloc SEGS nx0 G bcap ccap stk fpcreq entry cs = Some cs' ->
  nmalloc_post_ok AINV R M model (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs))
                  (uE E (reg cs 10)) (uE E (reg cs 2)) stk fx' R' M' mdl' p ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx' R' M' mdl' /\ pc cs' = ret /\ m_fs mdl' = m_fs model.
Proof.
  intros stk fpcreq entry cs cs' ret E fx R M model fx' R' M' mdl' p Hstk HC Hco Hn.
  node_alloc_gates Hn Hco cs cs'.
  pose proof (co_know HC) as HK.
  apply (node_alloc_core_ok_sound stk entry cs ret nlo nhi mh E fx R M model fx' R' M' mdl' p Hstk HC Hco Hnlo Hn1).
  - exact (xhi_sound SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) (reg cs 10) nhi HK Hnhi).
  - exact HnN.
  - exact (xhi_sound SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) (a_meter cs) mh HK Hmh).
  - exact HKc.
  - exact Hnv.
Qed.

(* [comment removed for export] *)
Lemma node_alloc_nb_ok_sound : forall nv mv stk entry cs cs' ret E fx R M model fx' R' M' mdl' (p : word),
  NBF nv mv -> 0 < stk < 2 ^ 40 ->
  cs_ok E cs fx R M model -> call_ok_stk nx0 G stk entry cs = Some ret -> node_alloc_nb SEGS nx0 G stk entry nv mv cs = Some cs' ->
  nmalloc_post_ok AINV R M model (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs))
                  (uE E (reg cs 10)) (uE E (reg cs 2)) stk fx' R' M' mdl' p ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx' R' M' mdl' /\ pc cs' = ret /\ m_fs mdl' = m_fs model.
Proof.
  intros nv mv stk entry cs cs' ret E fx R M model fx' R' M' mdl' p HNB Hstk HC Hco Hn.
  node_alloc_nb_gates Hn Hco cs cs'.
  pose proof (co_know HC) as HK.
  destruct (HNB E (co_uinv HC)) as (NB1 & NB2 & NB3).
  pose proof (xhi_sound SEGS E (GPS.Mr SHC VSH E cs model M) (kn cs) (reg cs 10) nhi0 HK Hnhi) as Nhi0.
  apply (node_alloc_core_ok_sound stk entry cs ret nlo (uE E (reg cs 10)) (uE E (a_meter cs)) E fx R M model fx' R' M' mdl' p Hstk HC Hco Hnlo Hn1).
  - lia.
  - unfold uE in *. lia.
  - lia.
  - rewrite Hr10, Hmt. exact NB3.
  - rewrite Hr10. cbn [expr_vars_lt]. apply (proj2 (Nat.ltb_lt _ _)). exact Hnvlt.
Qed.


(* [comment removed for export] *)
#[local] Notation MSPEC2 FRESH := (malloc_nspec2 SEGS SWIN PERMc SPTOPc G AINV AINVN FXOK RZ FPC bcap ccap FRESH).
#[local] Notation ASPEC1 := (alloc1_nspec SEGS SWIN PERMc SPTOPc FTOPc G AINV FXOK RZ FPC bcap ccap).


(* [comment removed for export] *)
#[local] Notation MSPEC1 FRESH := (malloc_nspec1 SEGS SWIN PERMc SPTOPc G AINV FXOK RZ FPC bcap ccap FRESH).
Theorem node_malloc1_glue : forall (FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop)
    args cs csa csb E fx R M model Tb,
  MSPEC1 FRESH MSTK_A (g_malloc_thunk G) -> MSPEC1 FRESH MSTK_A (g_malloc G) ->
  cs_ok E cs fx R M model ->
  node_malloc2 SEGS nx0 G bcap ccap args cs = Some (csa, csb) ->
  FRESH (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) M model (uE E (reg cs 10)) ->
  Tb [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfgF SEGS fx' R' (pc csb) M' model') Tb) ->
  RZ (cfgF SEGS fx R (pc cs) M model) Tb.
Proof.
  intros FRESH args cs csa csb E fx R M model Tb MT MI HC Hn HF HTb Hkb.
  unfold node_malloc2 in Hn.
  destruct (fresh_chk args cs) eqn:Hfc; [|discriminate].
  destruct (call_ok_stk nx0 G MSTK_A (malloc_entry G cs) cs) as [ret|] eqn:Hco; [|discriminate].
  destruct (xhi (kn cs) (a_meter cs)) as [mh|] eqn:Hmh; [|discriminate].
  destruct (node_alloc SEGS nx0 G bcap ccap MSTK_A true (malloc_entry G cs) cs) as [ok|] eqn:Hna; [|discriminate].
  destruct (Z.leb (mh + EVT) GKCAP) eqn:Hcap; [|discriminate].
  injection Hn as <- <-.
  assert (Hstk : 0 < MSTK_A < 2 ^ 40) by (unfold MSTK_A; lia).
  destruct (node_alloc_pre_sound MSTK_A true (malloc_entry G cs) cs ok ret E fx R M model Hstk HC Hco Hna) as [Hpc PRE].
  assert (MS : MSPEC1 FRESH MSTK_A (malloc_entry G cs)).
  { unfold malloc_entry in *. destruct (Z.eqb (pc cs) (g_malloc_thunk G)); [exact MT | exact MI]. }
  unfold cfgF. rewrite Hpc.
  apply (MS fx R M model _ _ _ _ _ ret _ _ Tb PRE HF HTb).
  intros fx' R' M' mdl' p POST.
  destruct (node_alloc_ok_sound MSTK_A true (malloc_entry G cs) cs ok ret E fx R M model fx' R' M' mdl' p Hstk HC Hco Hna POST) as (E' & Hag & HC' & Hpc' & Hfs').
  rewrite <- Hpc'. exact (Hkb E' fx' R' M' mdl' Hag HC' Hfs').
Qed.

(* [comment removed for export] *)
#[local] Notation MSPEC := (malloc_nspec SEGS SWIN PERMc SPTOPc G AINV AINVN FXOK RZ FPC bcap ccap).


(* [comment removed for export] *)
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis G_opnew_kn_wf : opnew_kn_wf G = true.

Lemma opnew_kn_sound : forall E cs fx R M model,
  cs_ok E cs fx R M model -> opnew_kn_ok G (kn cs) = true -> forall E0, Forall (fun K => kentry_ok SEGS E0 M K) (g_opnew_kn G).
Proof.
  intros E cs fx R M model HC H E0. unfold opnew_kn_ok in H. apply Forall_forall. intros K HinK.
  pose proof (proj1 (forallb_forall _ _) H K HinK) as HK. pose proof (proj1 (forallb_forall _ _) G_opnew_kn_wf K HinK) as GK. cbv beta in GK.
  pose proof G_img_hull as GH. pose proof G_img_ceil as GC. pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH.
  assert (VISI : forall z, g_img_lo G <= z < g_img_hi G -> forall HZ : 0 <= z < 2 ^ 64, Mr E cs model M (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
  { intros z Hz HZ. unfold GPS.Mr. apply mrestrict_visible. eapply (hid_app_falseX AINV AINV_if); [exact (co_ainv HC)|].
    right; right; right; right. rewrite u64_lit by exact HZ. exact Hz. }
  assert (VISS : forall z, in_ishadow G z -> forall HZ : 0 <= z < 2 ^ 64, Mr E cs model M (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
  { intros z Hz HZ. unfold GPS.Mr. apply mrestrict_visible. apply (hid_shadow_false SHC VSH G SHC_stack SHC_image). right; right.
    rewrite (u64_lit z) by exact HZ. exact Hz. }
  destruct K as [[kb ko] w vv|[kb ko] zn|[kb ko] zn kb2|ilo ihi|e m|e rlo rhi|[kb ko] zn|a1 n1 a2 n2|[kb ko] zn fc|[kb ko] zn|[kb ko] zn|fv flo fd];
    try discriminate GK.
  - (* [comment removed for export] *)
    destruct kb as [z| | | | | | |]; try discriminate GK. destruct z; try discriminate GK. destruct vv as [vz| | | | | | |]; try discriminate GK.
    apply andb_prop in GK as [GK Gw]. apply andb_prop in GK as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2. apply Nat.leb_le in Gw.
    apply existsb_exists in HK as [K' [HK' HE']]. apply kentry_eqb_eq in HE'. subst K'.
    pose proof (proj1 (Forall_forall _ _) (co_know HC) _ HK') as F. cbn [kentry_ok] in F |- *. destruct F as (Fw & Fl & Frd).
    assert (Fl0 : flat E0 (SA (ELit 0) ko) (Z.of_nat w)) by (unfold flat in Fl |- *; rewrite estart_lit0 in Fl |- *; exact Fl).
    split; [exact Fw|]. split; [exact Fl0|].
    assert (Hadr : forall EE, flat EE (SA (ELit 0) ko) (Z.of_nat w) -> adenot EE (SA (ELit 0) ko) = Z_to_bv 64 ko).
    { intros EE FlE. rewrite <- (Z_to_bv_bv_unsigned 64 (adenot EE (SA (ELit 0) ko))), (flat_u EE _ _ FlE), estart_lit0. reflexivity. }
    rewrite (Hadr E0 Fl0). rewrite (Hadr E Fl) in Frd. cbn [edenot] in Frd |- *.
    rewrite <- (rdn_mrestrict_eq SEGS (hid E cs model) w M (Z_to_bv 64 ko)); [unfold GPS.Mr in Frd; exact Frd|].
    intros k Hk. eapply (hid_app_falseX AINV AINV_if); [exact (co_ainv HC)|]. right; right; right; right.
    unfold woff. rewrite u64_lit by (rewrite u64_lit by lia; lia). rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *)
    destruct kb as [z| | | | | | |]; try discriminate GK. destruct z; try discriminate GK. destruct zn as [n| | | | | | |]; try discriminate GK.
    apply andb_prop in GK as [GK G3]. apply andb_prop in GK as [G1 G2]. apply Z.ltb_lt in G1. apply Z.leb_le in G2. apply Z.leb_le in G3.
    apply existsb_exists in HK as [K' [HK' HE']]. apply kentry_eqb_eq in HE'. subst K'.
    pose proof (proj1 (Forall_forall _ _) (co_know HC) _ HK') as F. cbn [kentry_ok] in F |- *. destruct F as [Fl Fz].
    unfold elenZ in Fz |- *. cbn [edenot] in Fz |- *. unfold flat in Fl |- *. rewrite estart_lit0 in Fl, Fz |- *.
    pose proof G_ro_lo_img as GR.
    assert (D1 : g_img_lo G / 8 <= g_ro_lo G / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : g_img_hi G / 8 <= (g_img_hi G + 7) / 8) by (apply Z.div_le_mono; lia).
    assert (D3 : (g_img_hi G + 7) / 8 <= g_img_hi G) by (apply Z.div_le_upper_bound; lia).
    assert (D0 : 0 <= g_ro_lo G / 8) by (apply Z.div_pos; lia).
    split; [exact Fl|]. intros i Hi. rewrite (u_small n) in Hi by (unfold SB in *; lia). rewrite <- (Fz i ltac:(rewrite (u_small n) by (unfold SB in *; lia); exact Hi)).
    symmetry. apply VISS; [unfold in_ishadow; lia | unfold SB in *; lia].
  - (* [comment removed for export] *)
    apply andb_prop in GK as [GK G3]. apply andb_prop in GK as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2. apply Z.leb_le in G3.
    apply existsb_exists in HK as [K' [HK' HX']]. destruct K' as [| | |lo' hi'| | | | | | | |]; try discriminate HX'.
    apply andb_prop in HX' as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    pose proof (proj1 (Forall_forall _ _) (co_know HC) _ HK') as F. cbn [kentry_ok] in F |- *. destruct F as (F1 & F2 & F3).
    split; [lia|]. split; [lia|]. intros i Hi. rewrite <- (VISI i ltac:(lia) ltac:(lia)). apply F3. lia.
Qed.

Theorem node_opnew_sound :
  ASPEC1 (nopnew_x SEGS G) MSTK_N (g_opnew G) -> node1_stmtN always (node_opnew SEGS nx0 G bcap ccap).
Proof.
  intros MS cs cs' E fx R M model T HT0 HC _ Hn Hk. unfold node_opnew in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hgate; [|discriminate] end.
  apply andb_prop in Hgate as [Hgate Hfd]. apply andb_prop in Hgate as [Hkn Hfb].
  pose proof G_newh_img as GNI_.   (* [comment removed for export] *)
  destruct (xlo (kn cs) (a_fbud cs)) as [fb|] eqn:Hfbl; [|discriminate Hfb]. apply Z.leb_le in Hfb.
  (* [comment removed for export] *)
  assert (HFDS : m_fds model = APS.fds_std).
  { pose proof (co_fds HC) as X. destruct (a_fd cs); cbn in Hfd; try discriminate Hfd. exact X. }
  pose proof Hn as Hn0. unfold node_alloc in Hn0.
  destruct (call_ok_stk nx0 G MSTK_N (g_opnew G) cs) as [ret|] eqn:Hco; [|discriminate]. clear Hn0.
  assert (Hstk : 0 < MSTK_N < 2 ^ 40) by (unfold MSTK_N; lia).
  destruct (node_alloc_pre_sound MSTK_N false (g_opnew G) cs cs' ret E fx R M model Hstk HC Hco Hn) as [Hpc PRE].
  unfold cfgF. rewrite Hpc.
  (* [comment removed for export] *)
  pose proof (xlo_sound SEGS E (Mr E cs model M) (kn cs) (a_fbud cs) fb (co_know HC) Hfbl) as FB. pose proof (co_fbud HC) as CF.
  assert (HLF : Z.of_nat (length (blocks_den E (a_fake cs))) + 1 <= FTOPc) by (unfold blocks_den; rewrite length_map; unfold uE in *; lia).
  apply (MS fx R M model _ _ _ _ _ ret _ _ T PRE (opnew_kn_sound E cs fx R M model HC Hkn) HFDS HLF HT0).
  intros fx' R' M' mdl' p POST.
  destruct (node_alloc_ok_sound MSTK_N false (g_opnew G) cs cs' ret E fx R M model fx' R' M' mdl' p Hstk HC Hco Hn POST) as (E' & Hag & HC' & Hpc' & Hfs').
  rewrite <- Hpc'. exact (Hk E' fx' R' M' mdl' Hag HC' Hfs').
Qed.

Corollary node_opnew_obl :
  ASPEC1 (nopnew_x SEGS G) MSTK_N (g_opnew G) -> AzContracts.OBL_opnew SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G bcap ccap.
Proof. exact node_opnew_sound. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation FSPEC := (free_nspec SEGS SWIN PERMc SPTOPc G AINV FXOK RZ FPC).

Theorem node_release_sound : forall stk entry,
  0 < stk < 2 ^ 40 ->
  FSPEC stk entry ->
  node1_stmt always (node_release SEGS nx0 G stk entry).
Proof. pose proof sfloor_ge as SFG_.
  intros stk entry Hstk FS cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_release in Hn.
  destruct (call_ok_stk nx0 G stk entry cs) as [ret|] eqn:Hco; [|discriminate].
  pose proof (call_ok_stk_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV G stk entry cs ret E fx R M model Hstk HC Hco) as CO.
  cbv zeta in Hn. cbv zeta in CO.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hsphi & Hstkw & Hflat).
  destruct (fpc_x SEGS (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 8) (reg cs 2)) eqn:Hfpc; [|discriminate]. cbn [negb] in Hn.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := Mr E cs model M) in HK.
  pose proof AINV_if as IFA. destruct AINV_if as (AINV_facts & AINV_nolazy & AINV_perm_nolazy & AINV_top & PERM_vsh & PERM_bnd & AINV_zone).
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]. pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb.
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10. change (Z.of_nat 10) with 10 in R10.
  pose proof (reg_sound E cs R 8 HR ltac:(lia)) as R8. change (Z.of_nat 8) with 8 in R8.
  set (v := nxt cs) in *.
  (* [comment removed for export] *)
  assert (SHAPE : exists live' mt' K',
    cs' = ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) v None)
                      (keep_owned G stk (kn cs) (live' ++ a_fake cs ++ a_ghost cs) (live' ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v) (v + NCS)%nat)
              (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) live' (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) mt' (a_fake cs) (a_fbud cs)
    /\ ((getr R (Z_to_bv 5 10) = Z_to_bv 64 0 /\ live' = a_vis cs /\ mt' = a_meter cs /\ K' = uE E (a_meter cs))
        \/ exists m L1 L2 mh, a_vis cs = L1 ++ (reg cs 10, m) :: L2 /\ live' = L1 ++ L2 /\ mt' = eadd (a_meter cs) (ELit KFREE)
                               /\ xhi (kn cs) (a_meter cs) = Some mh /\ mh + KFREE <= GKCAP /\ K' = uE E (a_meter cs) + KFREE)).
  { destruct (reg cs 10) as [z|x|sh e1 e2|op e1 e2|op e1 e2|w e1|c e1 e2|e1] eqn:Hp10.
    1: destruct (Z.eq_dec z 0) as [->|Hz].
    1: { apply some_inj in Hn. exists (a_vis cs), (a_meter cs), (uE E (a_meter cs)). split; [rewrite <- Hn; destruct cs; reflexivity|].
         left. split; [rewrite R10; reflexivity | repeat split; reflexivity]. }
    1: destruct z; [lia| |].
    all: destruct (remove_block _ (a_vis cs)) as [[m live']|] eqn:Hrb; try discriminate;
         destruct (xhi (kn cs) (a_meter cs)) as [mh|] eqn:Hmh; try discriminate;
         match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hkc; [|discriminate] end; cbn [negb] in Hn;
         apply Z.leb_le in Hkc;
         apply some_inj in Hn; exists live', (eadd (a_meter cs) (ELit KFREE)), (uE E (a_meter cs) + KFREE); split; [rewrite <- Hn; reflexivity|]; right;
         destruct (remove_block_split _ _ _ _ Hrb) as (L1 & L2 & HL & HL'); exists m, L1, L2, mh; repeat split; assumption. }
  clear Hn. destruct SHAPE as (live' & mt' & K' & -> & CASES).
  set (Lc := blocks_den E (a_vis cs)). set (Lc' := blocks_den E live'). set (Lf := blocks_den E (a_fake cs)).
  assert (Hsub : forall x, In x live' -> In x (a_vis cs)).
  { destruct CASES as [(_ & -> & _)|(m & L1 & L2 & mh & HL & -> & _)]; intros x Hx; [exact Hx|].
    rewrite HL. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
  assert (Hflat' : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((live' ++ a_fake cs) ++ a_ghost cs) = true).
  { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) Hflat x).
    apply in_app_iff in Hx as [Hx|Hx]; [apply in_app_iff in Hx as [Hx|Hx]|]; apply in_app_iff;
      [left; exact (Hsub x Hx) | right; apply in_app_iff; left; exact Hx | right; apply in_app_iff; right; exact Hx]. }
  assert (Hvars' : pairs_vars_lt v live' = true).
  { unfold pairs_vars_lt. apply forallb_forall. intros x Hx.
    exact (proj1 (forallb_forall _ _) (pairs_vars_lt_app_l _ _ _ Fallow) x (Hsub x Hx)). }
  unfold cfgF. rewrite Hpc.
  apply (FS fx R M model Lc Lc' Lf (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) (bcost E live') (bcount live') K'
           ret (uE E (reg cs 2)) (getr R (Z_to_bv 5 10)) T (co_halt HC) (co_fx HC) (co_ainv HC)).
  - unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
    split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|]. intros a Ha. apply Hstkw. exact Ha.
  - reflexivity.
  - rewrite R8. apply FPC_kfpc. eapply fpc_Mr_full. exact (fpc_x_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 8) (reg cs 2) HK (co_floor HC) Hfpc).
  - destruct CASES as [(H0 & -> & _ & ->)|(m & L1 & L2 & mh & HL & -> & _ & Hmh & Hkc & ->)].
    + left. split; [exact H0 | repeat split; reflexivity].
    + right. exists (uE E m), (blocks_den E L1), (blocks_den E L2).
      unfold Lc, Lc'. rewrite HL, !blocks_den_app, !bcost_app, !bcount_app. cbn [blocks_den map fst snd app bcost bcount length]. rewrite R10.
      pose proof (bcost_nonneg E L1). pose proof (bcost_nonneg E L2). pose proof (u64_range (edenot E m)).
      pose proof (xhi_sound SEGS E MR (kn cs) (a_meter cs) mh HK Hmh) as Nmh.
      unfold mcost, MCNT, uE, AzIface.MBLK, GPS.MBLK, KFREE, EVT, GKCAP in *.
      split; [reflexivity|]. split; [reflexivity|]. unfold bcount in *. cbn [length] in *. repeat split; lia.
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' HFX' Hkept Hfr Herrk Hscr HAINV' (Hh' & Hfs' & Hfds').
    set (E' := ext_call E v R').
    assert (Hag : env_agree v E E') by apply ext_call_agree.
    assert (HLc : blocks_den E' (a_vis cs) = Lc) by (unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
    assert (HLc' : blocks_den E' live' = Lc') by (unfold Lc'; eapply blocks_den_agree; [exact Hag | exact Hvars']).
    assert (HLf : blocks_den E' (a_fake cs) = Lf) by (unfold Lf; eapply blocks_den_agree; [exact Hag | exact Ffk]).
    match type of Hk with context [GPS.cs_ok _ _ _ _ _ _ _ _ _ _ _ _ ?c _ _ _ _] => set (cs' := c) in * end.
    assert (HMT : uE E' mt' = K').
    { destruct CASES as [(_ & _ & -> & ->)|(m & L1 & L2 & mh & _ & _ & -> & Hmh & Hkc & ->)].
      - eapply uE_agree; [exact Hag | exact Fmt].
      - pose proof (xhi_sound SEGS E MR (kn cs) (a_meter cs) mh HK Hmh) as Nmh.
        assert (EMT : uE E' (a_meter cs) = uE E (a_meter cs)) by (eapply uE_agree; [exact Hag | exact Fmt]).
        assert (ELT : uE E' (ELit KFREE) = KFREE) by (apply uE_lit; unfold KFREE, EVT; lia).
        rewrite uE_eadd_nowrap by (rewrite EMT, ELT; unfold uE, KFREE, EVT, GKCAP in *; lia). rewrite EMT, ELT. reflexivity. }
    assert (HA' : AINV (blocks_den E' (a_vis cs')) (blocks_den E' (a_fake cs')) (bcost E' (a_vis cs')) (bcount (a_vis cs'))
                       (uE E' (a_meter cs')) M' mdl').
    { unfold cs'. cbn [a_vis a_fake a_meter]. rewrite HLc', HLf, HMT. rewrite (bcost_agree v E E' live' Hag Hvars'). exact HAINV'. }
    set (MR' := Mr E' cs' mdl' M').
    apply (Hk E' fx' R' M' mdl').
    + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
    + constructor; try (unfold cs'; cbn [a_ss s_regs s_log s_know kn a_vis a_fake a_fbud a_meter a_ghost a_brk a_fd a_totsz a_eager a_maps a_ylo]).
      * unfold ret_regs.
        pose proof (regs_after_call E (s_regs (a_ss cs)) R R' v None) as RA. cbn iota in RA. apply RA.
        -- exact HR.
        -- exact Fsr.
        -- apply kept_ok_of_callee_saved. exact Hkept.
        -- exact I.
      * reflexivity.
      * fold cs'. fold MR'.
        apply (know_ok_agree' SEGS v E E'); [exact Hag | apply keep_owned_vars |].
        unfold know_ok. apply Forall_forall. intros K HKin. unfold cs' in HKin. cbn [kn a_ss s_know mk_ss] in HKin.
        assert (HKin3 : In K (keep_owned G stk (kn cs) ((live' ++ a_fake cs) ++ a_ghost cs) (live' ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                                (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
        { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
        eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G stk E MR MR' (kn cs) (live' ++ a_fake cs) (a_ghost cs) (live' ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K
                  ltac:(lia) HK Hflat' (co_perm HC) (co_top HC) Hsp); [| exact (co_floor HC) | | | | | exact HKin3].   (* [comment removed for export] *)
        -- pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
        -- intros a Ha. unfold MR', MR.
           assert (LP : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs))).
           { intros x Hx. rewrite blocks_den_app in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right; exact Hx].
             unfold blocks_den in Hx |- *. apply in_map_iff in Hx as [y [<- Hy]]. apply in_map_iff. exists y. split; [reflexivity | exact (Hsub y Hy)]. }
           assert (LQ : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x (blocks_den E' (a_vis cs') ++ blocks_den E' (a_fake cs'))).
           { intros x Hx. unfold cs'. cbn [a_vis a_fake]. rewrite HLc', HLf. rewrite blocks_den_app in Hx. exact Hx. }
           assert (LNK : forall x : word, in_blocks (blocks_den E (live' ++ a_fake cs)) (u x) -> in_blocks Lc' (u x) \/ in_blocks Lf (u x)).
           { intros x Hb. rewrite blocks_den_app in Hb. apply in_blocks_app2 in Hb. exact Hb. }
           exact (Mr_kept_app A SWIN PERMc SPTOPc SHC VSH AINV G AINV_facts A_img_hi A_img_lo AINV_nolazy AINV_perm_nolazy AINV_top SWIN_img G_ro_lo_img
                    E E' cs cs' model mdl' M M' _ _ _ _ _ _ (live' ++ a_fake cs) (reg cs 2) stk (co_ainv HC) HA' LP LQ (GPS.sfloor_stk _ _ Hsplo) ltac:(lia) Lc' Lf Hfr LNK a Ha).
        -- intros a Ha. unfold MR'.
           assert (HH : hid E' cs' mdl' a = false).
           { eapply (hid_app_falseX AINV IFA); [exact HA'|]. right; right; left. unfold uE in *. lia. }
           unfold GPS.Mr at 1. rewrite (mrestrict_visible _ _ _ HH). rewrite store_ok1_Mr by exact HH. apply Hscr. unfold scratch, uE in *. lia.
        -- (* [comment removed for export] *) errno_herr AINV IFA (co_ainv HC) HA' Herrk.
        -- intros a Ha. unfold MR', MR.
           assert (OP : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x (blocks_den E (a_vis cs ++ a_fake cs))).
           { intros x Hx. rewrite !blocks_den_app in Hx |- *. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right; exact Hx].
             unfold blocks_den in Hx |- *. apply in_map_iff in Hx as [y [<- Hy]]. apply in_map_iff. exists y. split; [reflexivity | exact (Hsub y Hy)]. }
           assert (OQ : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x (blocks_den E' (a_vis cs' ++ a_fake cs'))).
           { intros x Hx. unfold cs'. cbn [a_vis a_fake]. rewrite blocks_den_app in Hx |- *. rewrite HLc', HLf. exact Hx. }
           assert (ONK : forall x, In x (blocks_den E (live' ++ a_fake cs)) -> In x (Lc' ++ Lf)).
           { intros x Hx. unfold Lc', Lf. rewrite <- blocks_den_app. exact Hx. }
           exact (Mr_kept_shadow SWIN PERMc SPTOPc SHC VSH AINV G AINV_top SHC_stack SHC_image PERM_vsh E E' cs cs' model mdl' M M' _ _ _
                    (live' ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs)) (reg cs 2) stk (co_ainv HC)
                    (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OP) (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OQ)
                    Lc' Lf Hfr (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) ONK) a Ha).
      * exact Hh'.
      * rewrite Hfs'. exact (co_fs HC).
      * eapply fds_ok_model; [exact Hfds' | exact Hfs' |]. eapply APS.fds_ok_agree; [exact Hag | exact Ffd | exact (co_fds HC)].
      * fold cs'. exact HA'.
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
      * exact HFX'.
      * rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      * rewrite HMT. destruct CASES as [(_ & _ & _ & ->)|(m & L1 & L2 & mh & _ & _ & _ & Hmh & Hkc & ->)].
        -- exact (co_kcap HC).
        -- pose proof (xhi_sound SEGS E MR (kn cs) (a_meter cs) mh HK Hmh) as Nmh. unfold uE in *. lia.
      * rewrite (uE_agree v E E' (a_fbud cs) Hag Ffb). exact (co_fbud HC).
      * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + exact Hfs'.
Qed.

Theorem node_free_sound :
  FSPEC MSTK_A (g_free_thunk G) -> FSPEC MSTK_A (g_free G) ->
  AzContracts.OBL_free SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof.
  intros FT FI cs cs' E fx R M model T HC Hpre Hn Hk. unfold node_free in Hn.
  destruct (Z.eqb (pc cs) (g_free_thunk G)).
  - exact (node_release_sound MSTK_A _ ltac:(unfold MSTK_A; lia) FT cs cs' E fx R M model T HC Hpre Hn Hk).
  - exact (node_release_sound MSTK_A _ ltac:(unfold MSTK_A; lia) FI cs cs' E fx R M model T HC Hpre Hn Hk).
Qed.

Theorem node_opdel_sound :
  FSPEC MSTK_A (g_opdel G) -> AzContracts.OBL_opdel SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros F. exact (node_release_sound MSTK_A _ ltac:(unfold MSTK_A; lia) F). Qed.

Theorem node_opdel_sized_sound :
  FSPEC MSTK_A (g_opdel_sized G) -> AzContracts.OBL_opdel_sized SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros F. exact (node_release_sound MSTK_A _ ltac:(unfold MSTK_A; lia) F). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation SMSPEC := (stkmal_nspec SEGS SWIN PERMc SPTOPc FTOPc G AINV FXOK RZ).

(* [comment removed for export] *)
Lemma shfacts : forall f n, 4112 <= f -> f + n <= 2 ^ 47 -> 64 <= n <= 512 -> f mod 8 = 0 -> n mod 8 = 0 ->
  (0 <= SB + f / 8 /\ SB + f / 8 < 2 ^ 64 /\ 0 <= n / 8 /\ SB + f / 8 + n / 8 <= 2 ^ 64)
  /\ SB + f / 8 + n / 8 < 2 ^ 62
  /\ (forall i, 0 <= i < n / 8 -> (0 <= SB + f / 8 + i < 2 ^ 64) /\ (SB + f / 8 <= SB + f / 8 + i < SB + (f + n + 7) / 8))
  /\ (forall z, f <= z < f + n -> (0 <= SB + z / 8 < 2 ^ 64) /\ (SB + f / 8 <= SB + z / 8 < SB + (f + n + 7) / 8)
                                  /\ 0 <= z / 8 - f / 8 < n / 8 /\ SB + z / 8 = SB + f / 8 + (z / 8 - f / 8))
  /\ (forall x, SB + f / 8 <= x < SB + f / 8 + n / 8 -> SB + f / 8 <= x < SB + (f + n + 7) / 8).
Proof.
  intros f n H1 H2 H3 H4 H5. unfold SB.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split; [lia|]. split; [lia|]. split; [intros i Hi; lia|]. split; [intros z Hz; lia|]. intros x Hx; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Theorem node_stkmal_sound : forall k,
  0 <= k <= 3 -> SMSPEC k ->
  node1_stmt always (node_stack_malloc nx0 G [ELit k]).
Proof. pose proof sfloor_ge as SFG_.
  intros k Hk SM cs cs' E fx R M model T HC _ Hn Hk0.
  unfold node_stack_malloc in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hkk; [|discriminate] end. cbn [negb] in Hn.
  cbv zeta in Hn.
  set (n := 64 * 2 ^ k) in *.
  assert (Hn64 : 64 <= n <= 512).
  { unfold n. assert (2 ^ 0 <= 2 ^ k <= 2 ^ 3) by (split; apply Z.pow_le_mono_r; lia). change (2 ^ 0) with 1 in H. change (2 ^ 3) with 8 in H. lia. }
  assert (Hn8 : n mod 8 = 0) by (unfold n; replace (64 * 2 ^ k) with ((8 * 2 ^ k) * 8) by lia; apply Z_mod_mult).
  assert (Hstk : 0 < MSTK_F < 2 ^ 40) by (unfold MSTK_F; lia).
  destruct (call_ok_stk nx0 G MSTK_F (g_stkmal G k) cs) as [ret|] eqn:Hco; [|discriminate].
  pose proof (call_ok_stk_top_ok _ _ _ _ Hco) as Htok.
  pose proof (call_ok_stk_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV G MSTK_F (g_stkmal G k) cs ret E fx R M model Hstk HC Hco) as CO.
  cbv zeta in CO.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  destruct CO as (Hpc & Hfresh & Hlen & R1 & Rr & Re & R4 & R2 & Hspv & Hal & Hsplo & Hsptop & Hsphi & Hstkw & Hflat).
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  apply andb_prop in Hc as [Hc Hfb]. apply andb_prop in Hc as [Ha0 Hcnt].
  destruct (xlo (kn cs) (a_fbud cs)) as [fb|] eqn:Hxfb; [|discriminate]. apply Z.leb_le in Hfb.
  apply some_inj in Hn. subst cs'.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := Mr E cs model M) in HK.
  pose proof AINV_if as IFA. destruct AINV_if as (AINV_facts & AINV_nolazy & AINV_perm_nolazy & AINV_top & PERM_vsh & PERM_bnd & AINV_zone).
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]. pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb.
  pose proof (xlo_sound SEGS E MR (kn cs) (a_fbud cs) fb HK Hxfb) as Nfb.
  set (Lc := blocks_den E (a_vis cs)). set (Lf := blocks_den E (a_fake cs)).
  unfold cfgF. rewrite Hpc.
  apply (SM fx R M model Lc Lf (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) ret (uE E (reg cs 2)) T Hk
           (co_halt HC) (co_fx HC) (co_ainv HC)).
  - unfold ncall_pre. split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [unfold uE; rewrite <- R2; reflexivity|].
    split; [exact Hal|]. split; [exact Hsplo|]. split; [exact Hsptop|]. split; [exact Hsphi|]. split; [exact R4|]. intros a Ha. apply Hstkw. exact Ha.
  - unfold Lf, blocks_den. rewrite length_map. pose proof (co_fbud HC). unfold uE in *. lia.
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' f flag HFX' Hkept Ha0' Hfal Hblk Hdisj Hpdisj Hdef Hlast Hsh0 Hshw Hfr Herrk Hscr HAINV' (Hh' & Hfs' & Hfds').
    set (v := nxt cs) in *.
    set (E1 := ext1 E v f).
    set (E' := ext_call E1 (S v) R').
    assert (Hag1 : env_agree v E E1) by apply ext1_agree.
    assert (Hag2 : env_agree (S v) E1 E') by apply ext_call_agree.
    assert (Hag : env_agree v E E') by (eapply env_agree_trans; [exact Hag1 | eapply env_agree_le; [exact Hag2 | lia]]).
    assert (Hpv : edenot E' (EVar v) = f).
    { cbn [edenot]. rewrite <- (proj1 Hag2 v ltac:(lia)). unfold E1. apply ext1_at. }
    assert (HKE' : know_ok SEGS E' MR (kn cs)) by (eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK]).
    assert (HLc : blocks_den E' (a_vis cs) = Lc) by (unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
    assert (HLf : blocks_den E' (a_fake cs) = Lf) by (unfold Lf; eapply blocks_den_agree; [exact Hag | exact Ffk]).
    pose proof (u64_range f) as Hfr'. pose proof Hblk as (K1 & K2 & K3 & K4).
    pose proof GlzConst.ceil_hi as CH. unfold GlzConst.PTRHI in CH. pose proof GlzConst.ceil_lo as CL. unfold GlzConst.PTRLO in K1.
    assert (Hnlit : uE E' (ELit n) = n) by (apply uE_lit; lia).
    match type of Hk0 with context [GPS.cs_ok _ _ _ _ _ _ _ _ _ _ _ _ ?c _ _ _ _] => set (cs' := c) in * end.
    assert (EFB : uE E' (a_fbud cs) = uE E (a_fbud cs)) by (eapply uE_agree; [exact Hag | exact Ffb]).
    assert (HFB' : uE E' (eaddz (a_fbud cs) (-1)) = uE E (a_fbud cs) - 1).
    { rewrite uE_eaddz by (rewrite EFB; unfold uE in *; pose proof (u64_range (edenot E (a_fbud cs))); lia). rewrite EFB. lia. }
    assert (HA' : AINV (blocks_den E' (a_vis cs')) (blocks_den E' (a_fake cs')) (bcost E' (a_vis cs')) (bcount (a_vis cs'))
                       (uE E' (a_meter cs')) M' mdl').
    { unfold cs'. cbn [a_vis a_fake a_meter]. rewrite blocks_den_cons. cbn [fst snd]. rewrite HLc, HLf.
      rewrite Hnlit. unfold uE at 1. rewrite Hpv.
      rewrite (bcost_agree v E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
      rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact HAINV'. }
    set (MR' := Mr E' cs' mdl' M').
    assert (INB : forall z, u f <= z < u f + n -> in_blocks (blocks_den E' (a_vis cs') ++ blocks_den E' (a_fake cs')) z).
    { intros z Hz. unfold cs'. cbn [a_vis a_fake]. rewrite blocks_den_cons. cbn [fst snd].
      exists (uE E' (EVar v)), (uE E' (ELit n)). split; [apply in_app_iff; right; left; reflexivity|]. rewrite Hnlit. unfold uE. rewrite Hpv. lia. }
    assert (VB : forall a : word, u f <= u a < u f + n -> MR' a = M' a).
    { intros a Ha. unfold MR'. eapply (Mr_appX AINV IFA); [exact HA'|]. left. exact (INB (u a) Ha). }
    assert (INS : forall z, in_shadow SB (u f) n z -> in_lshadow (blocks_den E' (a_vis cs' ++ a_fake cs')) z).
    { intros z Hz. unfold cs'. cbn [a_vis a_fake]. rewrite blocks_den_app, blocks_den_cons. cbn [fst snd].
      exists (uE E' (EVar v)), (uE E' (ELit n)). split; [apply in_app_iff; right; left; reflexivity|]. rewrite Hnlit. unfold uE. rewrite Hpv. exact Hz. }
    assert (VS : forall a : word, in_shadow SB (u f) n (u a) -> MR' a = M' a).
    { intros a Ha. unfold MR'. apply (Mr_shadow SHC VSH G SHC_stack SHC_image). left. exact (INS (u a) Ha). }
    (* [comment removed for export] *)
    destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htop.
    destruct (floor_win (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)) as [[fwb fwo] fwl] eqn:Hfw.
    destruct (floor_win_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) tb tk fwb fwo fwl HK Htok Htop (co_floor HC) Hfw) as [FWlo ->].
    assert (Hfwb : edenot E' fwb = edenot E fwb).
    { symmetry. eapply (edenot_agree' v); [exact Hag|]. exact (floor_win_vars v (a_maps cs) (a_brk cs) (a_ylo cs) fwb fwo _ Fmaps Fbrk Hfw). }
    assert (Hobjs : forall b' m', In (b', m') (blocks_den E (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))) -> 0 <= b' /\ b' + m' <= two47).
    { intros b' m' Hin'.
      destruct (objs_ghost_ext SEGS PERMc E MR cs (a_vis cs) (a_fake cs) (fun x => In x (Lc ++ Lf)) HK (co_perm HC)
                  ltac:(intros x Hx; unfold Lc, Lf; rewrite <- blocks_den_app; exact Hx) (b', m') Hin') as [HL|[HP Hm]].
      - pose proof (AINV_zone _ _ _ _ _ _ _ _ _ (co_ainv HC) HL) as (Z1 & Z2 & _). unfold GlzConst.PTRLO in Z1. unfold two47 in *. lia.
      - cbn [fst snd] in HP, Hm. pose proof (PERM_bnd _ _ _ _ _ _ _ (b' + m' - 1) (co_ainv HC) ltac:(exists b', (b' + m'); split; [exact HP | lia])) as PB.
        unfold blocks_den in Hin'. apply in_map_iff in Hin' as [[gb gl] [Hgeq _]]. cbn [fst snd] in Hgeq. injection Hgeq as <- <-.
        pose proof (u64_range (edenot E gb)). unfold two47 in *. unfold uE in *. lia. }
    assert (Hpermd : forall lo hi, In (lo, hi) PERMc -> lo < hi -> u f + n <= lo \/ hi <= u f).
    { intros lo hi Hpin Hlh. destruct (Z_lt_le_dec lo (u f + n)) as [L1|L1]; [|left; lia]. destruct (Z_lt_le_dec (u f) hi) as [L2|L2]; [|right; lia].
      exfalso. apply (Hpdisj (Z.max lo (u f))); [exists lo, hi; split; [exact Hpin | lia] | lia]. }
    assert (HdisjC : forall b m, In (b, m) (blocks_den E (a_vis cs ++ a_fake cs)) -> u f + n <= b \/ b + m <= u f).
    { intros b m Hin. apply Hdisj. unfold Lc, Lf. rewrite <- blocks_den_app. exact Hin. }
    apply (Hk0 E' fx' R' M' mdl').
    + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
    + constructor; try (unfold cs'; cbn [a_ss s_regs s_log s_know kn a_vis a_fake a_fbud a_meter a_ghost a_brk a_fd a_totsz a_eager a_maps a_ylo]).
      * unfold ret_regs.
        pose proof (regs_after_call E1 (s_regs (a_ss cs)) R R' (S v) (Some (EVar v))) as RA. cbn iota in RA. apply RA.
        -- eapply regs_ok_agree'; [exact Hag1 | exact Fsr | exact HR].
        -- eapply sr_vars_lt_mono; [exact Fsr | lia].
        -- apply kept_ok_of_callee_saved. exact Hkept.
        -- split; [cbn; apply Nat.leb_refl|]. cbn [edenot]. unfold E1. rewrite ext1_at. exact Ha0'.
      * reflexivity.
      * fold cs'. fold MR'.
        assert (Hes : estart E' (SA (EVar v) 0) = u f) by (rewrite estart_SA, Hpv; lia).
        assert (Hel : elenZ E' (ELit n) = n) by (unfold elenZ; fold (uE E' (ELit n)); exact Hnlit).
        assert (Hsum : edenot E' (eadd (EVar v) (ELit n)) = Z_to_bv 64 (u f + n)).
        { unfold eadd. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. cbn [edenot] in Hpv. rewrite Hpv. unfold v_add. rewrite (u64_lit n) by lia. reflexivity. }
        assert (Hesh : estart E' (SA (shb (EVar v)) SB) = SB + u f / 8).
        { rewrite estart_SA. rewrite (srl3_base_denot E' (shb (EVar v)) (EVar v) eq_refl). rewrite Hpv. lia. }
        assert (Hn8b : 0 <= n / 8 < 2 ^ 64) by (clear - Hn64; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
        assert (Hel8 : elenZ E' (ELit (n / 8)) = n / 8) by (unfold elenZ; cbn [edenot]; apply u64_lit; exact Hn8b).
        assert (Hf8 : u f mod 8 = 0).
        { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hfal; [|lia]. eapply Z.divide_trans; [|exact Hfal].
          exists (8 * 2 ^ k). unfold n. lia. }
        pose proof (shfacts (u f) n ltac:(lia) ltac:(unfold two47 in *; lia) Hn64 Hf8 Hn8) as (SF1 & SF5 & SF2 & SF3 & SF4).
        unfold know_ok. apply Forall_app. split; [apply Forall_app; split; [|apply Forall_app; split]|].
        -- (* [comment removed for export] *)
          unfold block_rng. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [kentry_ok].
          ++ rewrite Hpv. unfold PTRLO, PTRHI, GlzConst.PTRLO, GlzConst.PTRHI in *. lia.
          ++ rewrite Hsum. unfold PTRLO, PTRHI, GlzConst.PTRLO, GlzConst.PTRHI in *. rewrite u64_lit by lia. lia.
          ++ rewrite Hpv. split; [lia | exact Hfal].
        -- (* [comment removed for export] *)
          clear K3 K4.   (* [comment removed for export] *)
          repeat apply Forall_cons; [| | | | | | | apply Forall_nil]; cbn [kentry_ok].
          ++ rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|].
             intros d m Hd Hdm. apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
             intros x Hx. rewrite u64_lit in Hx by lia.
             unfold MR', GPS.Mr. rewrite (wview_mrestrict_eq SEGS).
             { eapply (store_ok_all SEGS M' 1 x); [change (Z.of_nat 1) with 1; pose proof (u64_range x); lia | exact (proj2 (Hdef x ltac:(lia))) | change (Z.of_nat 1) with 1; lia]. }
             eapply (hid_app_falseX AINV IFA); [exact HA'|]. left. exact (INB (u x) ltac:(lia)).
          ++ rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|].
             intros i Hi. rewrite (VB (Z_to_bv 64 (u f + i))) by (rewrite u64_lit by lia; lia).
             apply (Hdef (Z_to_bv 64 (u f + i))). rewrite u64_lit by lia. lia.
          ++ (* [comment removed for export] *)
             rewrite Hesh, Hel8. split; [unfold flat; rewrite Hesh; exact SF1|].
             intros i Hi. destruct (SF2 i Hi) as [U1 U2]. rewrite VS by (rewrite u64_lit by exact U1; exact U2).
             apply Hsh0. exact Hi.
          ++ (* [comment removed for export] *)
             rewrite Hesh, Hel8. split; [unfold flat; rewrite Hesh; exact SF1|].
             intros i Hi. destruct (SF2 i Hi) as [U1 U2]. rewrite VS by (rewrite u64_lit by exact U1; exact U2).
             rewrite (Hsh0 i Hi). discriminate.
          ++ (* [comment removed for export] *)
             rewrite Hesh, Hel8. split; [unfold flat; rewrite Hesh; exact SF1|].
             pose proof SF1 as (V1 & V2 & V3 & V4).
             intros d m Hd Hdm. apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
             intros x Hx. rewrite u64_lit in Hx by lia.
             pose proof (SF4 (u x) ltac:(lia)) as W4.
             unfold MR', GPS.Mr. rewrite (wview_mrestrict_eq SEGS).
             { eapply (store_ok_all SEGS M' 1 x); [change (Z.of_nat 1) with 1; pose proof (u64_range x); lia | apply Hshw; exact W4 | change (Z.of_nat 1) with 1; lia]. }
             apply (hid_shadow_false SHC VSH G SHC_stack SHC_image). left. apply INS. exact W4.
          ++ (* [comment removed for export] *)
             rewrite Hes, Hel. split; [unfold flat; rewrite Hes; lia|]. split; [unfold two47 in *; lia|].
             intros z Hz. exists (Z_to_bv 8 0). split; [|left; reflexivity].
             destruct (SF3 z Hz) as (U1 & U2 & U3 & U4).
             rewrite VS by (rewrite u64_lit by exact U1; exact U2).
             rewrite U4. apply Hsh0. exact U3.
          ++ (* [comment removed for export] *)
             rewrite Hesh, Hel8. rewrite estart_SA. cbn [edenot]. rewrite (u64_lit 0) by lia.
             pose proof G_img_hull as (GH0 & GH1 & GH2).
             assert (HelI : elenZ E' (ELit ((g_img_hi G - g_img_lo G) / 8)) = (g_img_hi G - g_img_lo G) / 8).
             { unfold elenZ. cbn [edenot]. apply u64_lit. pose proof G_img_ceil as GC. pose proof GlzConst.ceil_hi as CH0. unfold GlzConst.PTRHI in CH0.
               split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
             rewrite HelI. destruct Hblk as (A1 & A2 & A3 & A4).
             assert (D8 : u f / 8 + n / 8 = (u f + n) / 8) by (clear - Hf8 Hn8 Hn64; Z.div_mod_to_equations; nia).
             assert (IM : g_img_lo G / 8 + (g_img_hi G - g_img_lo G) / 8 <= g_img_hi G / 8) by (clear - GH0 GH1 GH2; Z.div_mod_to_equations; nia).
             destruct A3 as [Hlow|Hhigh].
             ** left. pose proof (Z.div_le_mono (u f + n) (g_img_lo G) 8 ltac:(lia) Hlow). lia.
             ** right. pose proof (Z.div_le_mono (g_img_hi G) (u f) 8 ltac:(lia) Hhigh). lia.
        -- (* [comment removed for export] *)
          unfold block_sep. rewrite Hfw, ?kdisj_of_factsH_nil. apply Forall_app. split; [|apply Forall_app; split].
          ++ repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [kentry_ok]; rewrite Hes, Hel, estart_SA.
             ** cbn [a_base a_off]. rewrite Hfwb. left. unfold uE in *. lia.
             ** cbn [edenot a_base a_off]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E') by lia. lia.
             ** cbn [edenot a_base a_off]. rewrite (u64_lit 0) by lia. rewrite (elenZ_lit E') by (unfold SHMAPLEN, SHMAPLO, KHI; lia).
                unfold SHMAPLEN, SHMAPLO, KHI in *. lia.
          ++ eapply (disj_facts_ok SEGS E' MR' MR (kn cs)); [exact HKE' | | exact Hpv |].
             ** rewrite !forallb_app in Hflat |- *. apply andb_prop in Hflat as [F1 F23]. apply andb_prop in F23 as [F2 F3].
                rewrite F1, F2. cbn [andb]. unfold ghosts_ne. apply forallb_forall. intros x Hx. apply filter_In in Hx as [Hx _].
                exact (proj1 (forallb_forall _ _) F3 x Hx).
             ** rewrite !blocks_den_app, HLc, HLf. intros b m Hin. rewrite Hnlit.
                apply in_app_iff in Hin as [Hin|Hin]; [exact (Hdisj b m Hin)|].
                rewrite (blocks_den_agree v E E' (ghosts_ne (kn cs) (a_ghost cs)) Hag ltac:(unfold ghosts_ne; apply pairs_vars_lt_filter; exact (pairs_vars_lt_app_r _ _ _ Fallow))) in Hin.
                destruct (ghosts_ne_in SEGS PERMc E MR (kn cs) (a_ghost cs) b m HK (co_perm HC) Hin) as [Hw Hm].
                exact (Hpermd b (b + m) Hw ltac:(lia)).
          ++ eapply (kdisj_of_facts_ok SEGS E' MR' MR (kn cs)); [exact HKE' | exact Hpv | | constructor].
             intros K b off len HKin HKR Hl.
             assert (HKv : kentry_vars_lt v K = true).
             { pose proof (keep_owned_vars G MSTK_F (kn cs) (a_vis cs ++ a_fake cs ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs)) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v) as KV.
               rewrite kn_vars_lt_forallb in KV. exact (proj1 (forallb_forall _ _) KV K HKin). }
             assert (Hbe : uE E' b = uE E b /\ uE E' len = uE E len).
             { unfold uE. split; f_equal; symmetry; (eapply edenot_agree'; [exact Hag|]);
               destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?|[? ?] ?|? ? ?]; cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-;
                 cbn [kentry_vars_lt saddr_vars_lt a_base expr_vars_lt] in HKv; repeat (apply andb_prop in HKv as [HKv ?]); first [reflexivity | exact HKv | assumption]. }
             destruct Hbe as [Hbe Hle]. rewrite Hbe, Hle in *. rewrite Hnlit.
             destruct (Z_lt_ge_dec (u f + n) (uE E b + off + 1)) as [|Hge1]; [left; lia|].
             destruct (Z_lt_ge_dec (uE E b + off + uE E len) (u f + 1)) as [|Hge2]; [right; lia|].
             exfalso. set (z := Z.max (u f) (uE E b + off)).
             assert (Hz1 : u f <= z < u f + n) by (unfold z; unfold uE in *; lia).
             assert (Hz2 : uE E b + off <= z < uE E b + off + uE E len) by (unfold z; unfold uE in *; lia).
             assert (HKok : kentry_ok SEGS E MR K).
             { assert (HKcut : know_ok SEGS E MR (kn_cutout (kn_cutout (kn cs) spb (spk - MSTK_F) (ELit MSTK_F)) (ELit 0) (g_errno G) (ELit 4))).   (* [comment removed for export] *)
               { eapply know_ok_cutout; [eapply know_ok_cutout; [exact HK|]; intros; reflexivity|]. intros; reflexivity. }
               pose proof HKin as HKin2. rewrite keep_owned_eq in HKin2. unfold keep_owned_ref in HKin2. rewrite Hsp in HKin2.
               repeat (apply in_app_iff in HKin2 as [HKin'|HKin2]; [apply filter_In in HKin' as [HKin' _]; first [exact (proj1 (Forall_forall _ _) HK K HKin') | exact (proj1 (Forall_forall _ _) HKcut K HKin')] |]).
               apply filter_In in HKin2 as [HKin2 _]. exact (proj1 (Forall_forall _ _) HK K HKin2). }
             pose proof (kentry_range_foot SEGS E MR K b off len HKok HKR) as HF.
             assert (Hflat2 : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) = true).
             { first [rewrite <- app_assoc | rewrite app_assoc]; exact Hflat. }
             assert (HKin3 : In K (keep_owned G MSTK_F (kn cs) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                                     (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
             { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
             destruct (keep_owned_loc SEGS PERMc SPTOPc G MSTK_F E MR (kn cs) (a_vis cs ++ a_fake cs) (a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                         (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K z b off len
                         HK Hflat2 (co_perm HC) (co_top HC) Hsp (co_floor HC) HKin3 HKR ltac:(unfold in_kfoot; rewrite HF, estart_SA; unfold uE in *; lia)) as [LOC|SH].
             ** exact (block_not_kept_loc PERMc SPTOPc G (blocks_den E (a_vis cs ++ a_fake cs)) (u f) n z Hblk G_ro_lo_img (AINV_top _ _ _ _ _ _ _ (co_ainv HC)) HdisjC Hpermd Hz1 LOC).
             ** exact (block_not_shz G E _ _ (u f) n z Hblk Hobjs ltac:(pose proof G_img_hull; lia) ltac:(unfold two47 in *; lia) Hz1 SH).
        -- (* [comment removed for export] *)
          apply (know_ok_agree' SEGS v E E'); [exact Hag | apply keep_owned_vars |].
          unfold know_ok. apply Forall_forall. intros K HKin.
          assert (Hflat2 : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) = true).
          { first [rewrite <- app_assoc | rewrite app_assoc]; exact Hflat. }
          assert (HKin3 : In K (keep_owned G MSTK_F (kn cs) ((a_vis cs ++ a_fake cs) ++ a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
          { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
          eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G MSTK_F E MR MR' (kn cs) (a_vis cs ++ a_fake cs) (a_ghost cs) (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs))
                    (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K
                    ltac:(lia) HK Hflat2 (co_perm HC) (co_top HC) Hsp); [| exact (co_floor HC) | | | | | exact HKin3].   (* [comment removed for export] *)
          ++ pose proof (u64_range (edenot E (reg cs 2))). unfold uE in Hspv. lia.
          ++ intros a Ha. unfold MR', MR.
             assert (LP : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs))).
             { intros x Hx. rewrite blocks_den_app in Hx. exact Hx. }
             assert (LQ : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E' (a_vis cs') ++ blocks_den E' (a_fake cs'))).
             { intros x Hx. unfold cs'. cbn [a_vis a_fake]. rewrite blocks_den_cons, HLc, HLf. cbn [fst snd].
               rewrite blocks_den_app in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
             assert (LNK : forall x : word, in_blocks (blocks_den E (a_vis cs ++ a_fake cs)) (u x) -> in_blocks Lc (u x) \/ in_blocks Lf (u x)).
             { intros x Hb. rewrite blocks_den_app in Hb. apply in_blocks_app2 in Hb. exact Hb. }
             exact (Mr_kept_app A SWIN PERMc SPTOPc SHC VSH AINV G AINV_facts A_img_hi A_img_lo AINV_nolazy AINV_perm_nolazy AINV_top SWIN_img G_ro_lo_img
                      E E' cs cs' model mdl' M M' _ _ _ _ _ _ (a_vis cs ++ a_fake cs) (reg cs 2) MSTK_F (co_ainv HC) HA' LP LQ (GPS.sfloor_stk _ _ Hsplo) ltac:(lia) Lc Lf Hfr LNK a Ha).
          ++ intros a Ha. unfold MR'.
             assert (HH : hid E' cs' mdl' a = false).
             { eapply (hid_app_falseX AINV IFA); [exact HA'|]. right; right; left. unfold uE, MSTK_F in *. lia. }
             unfold GPS.Mr at 1. rewrite (mrestrict_visible _ _ _ HH). rewrite store_ok1_Mr by exact HH. apply Hscr. unfold scratch, uE in *. lia.
          ++ (* [comment removed for export] *) errno_herr AINV IFA (co_ainv HC) HA' Herrk.
          ++ intros a Ha. unfold MR', MR.
             assert (OP : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E (a_vis cs ++ a_fake cs))) by (intros x Hx; exact Hx).
             assert (OQ : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (blocks_den E' (a_vis cs' ++ a_fake cs'))).
             { intros x Hx. unfold cs'. cbn [a_vis a_fake]. rewrite !blocks_den_app, blocks_den_cons in *. rewrite HLc, HLf. cbn [fst snd].
               apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
             assert (ONK : forall x, In x (blocks_den E (a_vis cs ++ a_fake cs)) -> In x (Lc ++ Lf)).
             { intros x Hx. unfold Lc, Lf. rewrite <- blocks_den_app. exact Hx. }
             exact (Mr_kept_shadow SWIN PERMc SPTOPc SHC VSH AINV G AINV_top SHC_stack SHC_image PERM_vsh E E' cs cs' model mdl' M M' _ _ _
                      (a_vis cs ++ a_fake cs ++ ghosts_ne (kn cs) (a_ghost cs)) (reg cs 2) MSTK_F (co_ainv HC)
                      (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OP) (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OQ)
                      Lc Lf Hfr (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) ONK) a Ha).
      * exact Hh'.
      * rewrite Hfs'. exact (co_fs HC).
      * eapply fds_ok_model; [exact Hfds' | exact Hfs' |]. eapply APS.fds_ok_agree; [exact Hag | exact Ffd | exact (co_fds HC)].
      * fold cs'. exact HA'.
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
      * exact HFX'.
      * rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      * rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact (co_kcap HC).
      * rewrite HFB'. cbn [length]. pose proof (co_fbud HC). lia.
      * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + exact Hfs'.
Qed.

Theorem node_stkmal_all_sound :
  (forall k, 0 <= k <= 3 -> SMSPEC k) ->
  AzContracts.OBL_stkmal SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof.
  intros SM args cs cs' E fx R M model T HC Hpre Hn Hk.
  destruct args as [|[k| | | | | | |] [|]]; try discriminate Hn.
  destruct (Z_le_dec 0 k) as [H0|H0]; [destruct (Z_le_dec k 3) as [H3|H3]|].
  - exact (node_stkmal_sound k (conj H0 H3) (SM k (conj H0 H3)) cs cs' E fx R M model T HC Hpre Hn Hk).
  - exfalso. unfold node_stack_malloc in Hn. replace (Z.leb 0 k && Z.leb k 3)%bool with false in Hn; [discriminate|].
    symmetry. apply andb_false_iff. right. apply Z.leb_gt. lia.
  - exfalso. unfold node_stack_malloc in Hn. replace (Z.leb 0 k && Z.leb k 3)%bool with false in Hn; [discriminate|].
    symmetry. apply andb_false_iff. left. apply Z.leb_gt. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis AINV_lazy : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  exists AA, A_wf AA /\ MInv AA mdl
    /\ (forall a : word, in_shc SHC (u a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall a : word, in_shv VSH (u a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall (a : word) b n, In (b, n) (Lc ++ Lf) -> in_shadow SB b n (u a) -> page_allowedb AA (page_base a) = true)
    /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AINV Lc Lf B C K M mdl').
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis FTOP_small : FTOPc <= 2 ^ 62.
Let AINV_factsG : forall Lc Lf B C K M mdl, AINV Lc Lf B C K M mdl ->
     Forall (fun iv => 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL_run
                       /\ (u (fst iv) + u (snd iv) <= img_lo A \/ img_hi A <= u (fst iv))) (m_vm_lazy mdl) := proj1 AINV_if.

Lemma remove_frame_split : forall f fk m fk',
  remove_frame f fk = Some (m, fk') -> exists F1 F2, fk = F1 ++ (f, m) :: F2 /\ fk' = F1 ++ F2.
Proof.
  intros f fk. induction fk as [|[b n] r IH]; intros m fk' H; cbn [remove_frame] in H; [discriminate|].
  destruct (expr_eqb b f) eqn:Heq.
  - injection H as <- <-. apply expr_eqb_eq in Heq. subst b. exists [], r. split; reflexivity.
  - destruct (remove_frame f r) as [[m' r']|] eqn:Hr; [|discriminate]. injection H as <- <-.
    destruct (IH m' r' eq_refl) as (F1 & F2 & -> & ->). exists ((b, n) :: F1), F2. split; reflexivity.
Qed.

Lemma nkept_noscratch : forall Lc Lf P (a : word),
  nkept SWIN PERMc G Lc Lf P a -> nkept SWIN PERMc G Lc Lf noscratch a.
Proof.
  intros Lc Lf P a H. unfold nkept in *. destruct H as [[H1 [_ H3]]|H]; [left; split; [exact H1 | split; [unfold noscratch; tauto | exact H3]] | right; exact H].
Qed.

Theorem node_fakerel_sound : forall IT,
  itab_sound SEGS IT ->
  fakerel_nspec SEGS SWIN PERMc G AINV FXOK RZ ->
  node1_stmt always (node_fake_release SEGS IT nx0 G).
Proof.
  intros IT IT_ok FRS cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_fake_release in Hn.
  destruct (itab_lookup IT (pc cs)) as [i1|] eqn:Hit1; [|discriminate].
  destruct i1 as [| | | | |sz sx rd rs imm| | | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate.
  destruct sz; try discriminate.
  destruct (itab_lookup IT (pc cs + 4)) as [i2|] eqn:Hit2; [|discriminate].
  destruct i2 as [| | | | | |sz1 rs1 rs2 imm2| | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate.
  destruct sz1; try discriminate.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  set (fe := sr_get (s_regs (a_ss cs)) rs) in Hn.
  destruct (remove_frame fe (a_fake cs)) as [[m fk']|] eqn:Hrf; [|discriminate].
  destruct m as [n| | | | | | |]; try discriminate.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end. cbn [negb] in Hn.
  apply some_inj in Hn. subst cs'.
  (* [comment removed for export] *)
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  rename Hc into Hrs1. rename X9 into Hrs2. rename X8 into Himm2. rename X7 into Hrd0. rename X6 into Hw4. rename X5 into Hfresh.
  rename X4 into Hpc0. rename X3 into Hpc8. rename X2 into Hlen. rename X1 into Hlflat. rename X0 into Hspbf. rename X into Hstx.
  apply Z.leb_le in Hpc0. apply Z.ltb_lt in Hpc8. apply Nat.eqb_eq in Hlen. unfold two64 in Hpc8.
  apply negb_true_iff in Hrd0.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs + 4))) as [w4|] eqn:Hf4; [|discriminate].
  assert (Hw4eq : w4 = Z_to_bv 32 (0x23 + u rd * 2 ^ 15)) by (apply bv_eq; unfold bv_eqb in Hw4; apply Z.eqb_eq in Hw4; exact Hw4). subst w4.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  repeat match type of Hc2 with (_ && _)%bool = true => apply andb_prop in Hc2 as [Hc2 ?X] end.
  rename Hc2 into Himm. rename X1 into Hn8. rename X0 into Hn47. rename X into Hrdb.
  apply Z.eqb_eq in Himm. apply Z.leb_le in Hn8. apply Z.ltb_lt in Hn47. unfold two47 in Hn47.
  (* [comment removed for export] *)
  pose proof (IT_ok _ _ Hit1) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz. injection Hen as ->.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (H := GPS.hid SHC VSH E cs model). set (MR := Mr E cs model M) in *.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt]. pose proof (fresh_ok_parts3 nx0 cs Hfresh) as Ffb.
  pose proof (AzKnowLib.stack_x_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) HK (co_floor HC) Hstx) as Hsplo.
  pose proof AINV_if as IFA. destruct AINV_if as (AINV_facts & AINV_nolazy & AINV_perm_nolazy & AINV_top & PERM_vsh & PERM_bnd & AINV_zone).
  (* [comment removed for export] *)
  destruct (remove_frame_split fe (a_fake cs) (ELit n) fk' Hrf) as (G1 & G2 & HFK & ->).
  set (f := uE E fe).
  assert (Hnlit : uE E (ELit n) = n) by (apply uE_lit; lia).
  set (Lc := blocks_den E (a_vis cs)). set (Lf := blocks_den E (a_fake cs)).
  assert (HLf : Lf = blocks_den E G1 ++ (f, n) :: blocks_den E G2).
  { unfold Lf. rewrite HFK, blocks_den_app, blocks_den_cons. cbn [fst snd]. rewrite Hnlit. reflexivity. }
  (* [comment removed for export] *)
  destruct (kn_readable_x_sound2 SEGS E MR (kn cs) fe (n - 8) (ELit 8) HK Hrdb) as (Rlo & Rhi & Rdef).
  rewrite estart_SA in Rlo, Rhi, Rdef. rewrite (AzAPS.APS.elenZ_lit E 8) in Rhi, Rdef by lia. fold (uE E fe) in Rlo, Rhi, Rdef. fold f in Rlo, Rhi, Rdef.
  set (byte_at := fun j : nat => match MR (Z_to_bv 64 (f + (n - 8) + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (HBj : forall j, (j < 8)%nat -> MR (Z_to_bv 64 (f + (n - 8) + Z.of_nat j)) = Some (byte_at j)).
  { intros j Hj. unfold byte_at. destruct (MR (Z_to_bv 64 (f + (n - 8) + Z.of_nat j))) as [b|] eqn:Hb; [reflexivity|].
    exfalso. exact (Rdef (Z.of_nat j) ltac:(lia) Hb). }
  assert (HMBj : forall j, (j < 8)%nat -> M (Z_to_bv 64 (f + (n - 8) + Z.of_nat j)) = Some (byte_at j)).
  { intros j Hj. pose proof (HBj j Hj) as X. unfold MR, GPS.Mr, mrestrict in X. destruct (GPS.hid SHC VSH E cs model _); [discriminate | exact X]. }
  set (bs := map byte_at (seq 0 8)).
  assert (Hbslen : length bs = 8%nat) by (unfold bs; rewrite length_map, length_seq; reflexivity).
  assert (Haddr : v_addi (getr R rs) (bv_signed imm) = Z_to_bv 64 (f + (n - 8))).
  { rewrite (HR rs). fold fe. rewrite Himm. unfold v_addi. unfold f, uE. reflexivity. }
  assert (Hrdn : rdn SEGS MR (v_addi (getr R rs) (bv_signed imm)) 8 = Some bs).
  { rewrite Haddr. unfold bs. apply (rdn_of_nth SEGS MR 8 (Z_to_bv 64 (f + (n - 8))) byte_at).
    - rewrite u64_lit by lia. change (Z.of_nat 8) with 8. lia.
    - intros j Hj. rewrite u64_lit by lia. apply rdn1_overlay. apply HBj. exact Hj. }
  set (flag := bytes_le_to_Z bs).
  pose proof (bytes_le_to_Z_bound bs) as Hflagb. rewrite Hbslen in Hflagb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hflagb. fold flag in Hflagb.
  set (val := load_result SZ8 sx bs).
  assert (Hval : u val = flag).
  { unfold val, load_result, le_bytes_to_word. fold flag. rewrite bv_extract_unsigned, Z.shiftr_0_r. cbn [Z.of_N].
    rewrite u64_lit by lia. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. lia. }
  set (v := nxt cs) in *.
  set (R1 := regupd R rd val).
  (* [comment removed for export] *)
  assert (Hrdne : bv_eqb rd 0 = false) by (destruct (bv_eqb rd 0) eqn:X; [exfalso; unfold bv_eqb in *; rewrite X in Hrd0; discriminate | reflexivity] || exact Hrd0).
  assert (Hstep : RiscvSemantics.step SEGS (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS)))
                  = MachineOk (mkstF fx R1 (Z_to_bv 64 (pc cs + 4)) MR (seg_rom SEGS))).
  { change (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))) with (mkstF fx R (Z_to_bv 64 (pc cs)) MR (seg_rom SEGS)).
    unfold mkstF. rewrite <- !mkstR_None.
    rewrite (stepR_load fx SEGS R _ MR (seg_rom SEGS) None w SZ8 sx rd rs imm bs Hf Hec Hd Hrdn).
    rewrite Hrdne. rewrite v_addi_pc4 by (unfold two64; lia). reflexivity. }
  unfold cfgF.
  eapply (GPS.restricted_run_sound SEGS A PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_lazy AINV_factsG FXOK UINV RZ RZ_silent1 SEGS_in_hull SEGS_wx);
    [exact HC | eapply msteps_one; [reflexivity | exact Hstep] |].
  intros model1 Hsame Hhid Hhalt1 Hfs1 Hfds1 HA1 Hclean.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
  unfold MR, GPS.Mr. fold H. rewrite munrestrict_mrestrict.
  (* [comment removed for export] *)
  apply (FRS (pc cs + 4) (u rd) fx R1 M model1 Lc Lf (blocks_den E G1) (blocks_den E G2) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) f n flag T
           Hhalt1 (co_fx HC) HA1 HLf).
  - (* [comment removed for export] *)
    exists bs. split; [|split; [exact Hbslen | reflexivity]].
    intros i Hi. replace (f + n - 8 + Z.of_nat i) with (f + (n - 8) + Z.of_nat i) by lia. rewrite (HMBj i Hi).
    unfold bs. rewrite (nth_map_seq byte_at 8 i (Z_to_bv 8 0) Hi). reflexivity.
  - exact Hf4.
  - pose proof (u5_range rd). unfold bv_eqb in Hrdne. apply Z.eqb_neq in Hrdne. change (u (0%bv : bv 5)) with 0 in Hrdne. lia.
  - rewrite Z_to_bv_bv_unsigned. unfold R1, getr. rewrite Hrdne. rewrite regupd_same. exact Hval.
  - lia.
  - lia.
  - (* [comment removed for export] *)
    intros M' mdl' Hfr Herrk HAINV' (Hh' & Hfs' & Hfds').
    set (E' := ext1 E v val).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    assert (Hpv : edenot E' (EVar v) = val) by (cbn [edenot]; unfold E'; apply ext1_at).
    assert (HG12 : forall x, In x (G1 ++ G2) -> In x (a_fake cs)).
    { intros x Hx. rewrite HFK. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx | right; right; exact Hx]. }
    assert (Hvars' : pairs_vars_lt v (G1 ++ G2) = true).
    { unfold pairs_vars_lt. apply forallb_forall. intros x Hx. exact (proj1 (forallb_forall _ _) Ffk x (HG12 x Hx)). }
    assert (HLc : blocks_den E' (a_vis cs) = Lc) by (unfold Lc; eapply blocks_den_agree; [exact Hag | exact (pairs_vars_lt_app_l _ _ _ Fallow)]).
    assert (HLf' : blocks_den E' (G1 ++ G2) = blocks_den E G1 ++ blocks_den E G2).
    { rewrite <- blocks_den_app. eapply blocks_den_agree; [exact Hag | exact Hvars']. }
    match type of Hk with context [GPS.cs_ok _ _ _ _ _ _ _ _ _ _ _ _ ?c _ _ _ _] => set (cs' := c) in * end.
    assert (EFB : uE E' (a_fbud cs) = uE E (a_fbud cs)) by (eapply uE_agree; [exact Hag | exact Ffb]).
    assert (HFB' : uE E' (eaddz (a_fbud cs) 1) = uE E (a_fbud cs) + 1).
    { pose proof (co_fbud HC) as CF. pose proof FTOP_small as FS. rewrite uE_eaddz by (rewrite EFB; unfold uE in *; pose proof (u64_range (edenot E (a_fbud cs))); lia). rewrite EFB. lia. }
    assert (HA' : AINV (blocks_den E' (a_vis cs')) (blocks_den E' (a_fake cs')) (bcost E' (a_vis cs')) (bcount (a_vis cs'))
                       (uE E' (a_meter cs')) M' mdl').
    { unfold cs'. cbn [a_vis a_fake a_meter]. rewrite HLc, HLf'.
      rewrite (bcost_agree v E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
      rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact HAINV'. }
    set (MR' := Mr E' cs' mdl' M').
    assert (Hfr0 : forall a : word, nkept SWIN PERMc G Lc (blocks_den E (G1 ++ G2)) (scratch (uE E (reg cs 2)) 0) a -> M' a = M a).
    { intros a Ha. apply Hfr. rewrite <- blocks_den_app. eapply nkept_noscratch. exact Ha. }
    destruct (bflat_x_sound SEGS E MR (kn cs) spb spk (ELit 0) HK Hspbf) as (SB1 & SB2 & SB3). rewrite estart_SA in SB1, SB3.
    replace (pc cs + 4 + 4) with (pc cs'); [| unfold cs'; cbn [pc a_ss mk_ss s_pc]; lia].
    change (RZ (cfgF SEGS fx R1 (pc cs') M' mdl') T).
    apply (Hk E' fx R1 M' mdl').
    + split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
    + constructor; try (unfold cs'; cbn [a_ss s_regs s_log s_know kn a_vis a_fake a_fbud a_meter a_ghost a_brk a_fd a_totsz a_eager a_maps a_ylo]).
      * pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HRE.
        pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd val (EVar v) HRE Hpv) as HR2.
        rewrite Hrdne in HR2. exact HR2.
      * reflexivity.
      * fold cs'. fold MR'.
        apply (know_ok_agree' SEGS v E E'); [exact Hag | apply keep_owned_vars |].
        unfold know_ok. apply Forall_forall. intros K HKin. unfold cs' in HKin. cbn [kn a_ss s_know mk_ss] in HKin.
        assert (Hflat2 : forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) ((a_vis cs ++ (G1 ++ G2)) ++ a_ghost cs) = true).
        { apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) Hlflat x).
          apply in_app_iff in Hx as [Hx|Hx]; [apply in_app_iff in Hx as [Hx|Hx]|]; apply in_app_iff;
            [left; exact Hx | right; apply in_app_iff; left; exact (HG12 x Hx) | right; apply in_app_iff; right; exact Hx]. }
        assert (HKin3 : In K (keep_owned G 0 (kn cs) ((a_vis cs ++ (G1 ++ G2)) ++ a_ghost cs) (a_vis cs ++ (G1 ++ G2) ++ ghosts_ne (kn cs) (a_ghost cs))
                                (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) v)).
        { first [rewrite <- app_assoc | rewrite app_assoc]; exact HKin. }
        eapply (keep_owned_sound SEGS SWIN PERMc SPTOPc G 0 E MR MR' (kn cs) (a_vis cs ++ (G1 ++ G2)) (a_ghost cs) (a_vis cs ++ (G1 ++ G2) ++ ghosts_ne (kn cs) (a_ghost cs))
                  (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) spb spk v K
                  ltac:(lia) HK Hflat2 (co_perm HC) (co_top HC) Hsp); [| exact (co_floor HC) | | | | | exact HKin3].   (* [comment removed for export] *)
        -- pose proof (u64_range (edenot E (reg cs 2))). unfold uE in *. lia.
        -- intros a Ha. unfold MR', MR.
           assert (LP : forall x, In x (blocks_den E (a_vis cs ++ (G1 ++ G2))) -> In x (blocks_den E (a_vis cs) ++ blocks_den E (a_fake cs))).
           { intros x Hx. rewrite blocks_den_app in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx|right].
             unfold blocks_den in Hx |- *. apply in_map_iff in Hx as [y [<- Hy]]. apply in_map_iff. exists y. split; [reflexivity | exact (HG12 y Hy)]. }
           assert (LQ : forall x, In x (blocks_den E (a_vis cs ++ (G1 ++ G2))) -> In x (blocks_den E' (a_vis cs') ++ blocks_den E' (a_fake cs'))).
           { intros x Hx. unfold cs'. cbn [a_vis a_fake]. rewrite HLc, HLf'. rewrite !blocks_den_app in Hx. exact Hx. }
           assert (LNK : forall x : word, in_blocks (blocks_den E (a_vis cs ++ (G1 ++ G2))) (u x) -> in_blocks Lc (u x) \/ in_blocks (blocks_den E (G1 ++ G2)) (u x)).
           { intros x Hb. rewrite blocks_den_app in Hb. apply in_blocks_app2 in Hb. exact Hb. }
           assert (HSP0' : CEIL_run + 0 <= uE E (reg cs 2)) by (unfold uE in *; lia).
           exact (Mr_kept_app A SWIN PERMc SPTOPc SHC VSH AINV G AINV_facts A_img_hi A_img_lo AINV_nolazy AINV_perm_nolazy AINV_top SWIN_img G_ro_lo_img
                    E E' cs cs' model mdl' M M' _ _ _ _ _ _ (a_vis cs ++ (G1 ++ G2)) (reg cs 2) 0 (co_ainv HC) HA' LP LQ HSP0' (Z.le_refl 0) Lc _ Hfr0 LNK a Ha).
        -- intros a Ha. exfalso. unfold uE in *. lia.
        -- (* [comment removed for export] *) errno_herr AINV IFA (co_ainv HC) HA' Herrk.
        -- intros a Ha. unfold MR', MR.
           assert (OP : forall x, In x (blocks_den E (a_vis cs ++ (G1 ++ G2))) -> In x (blocks_den E (a_vis cs ++ a_fake cs))).
           { intros x Hx. rewrite !blocks_den_app in Hx |- *. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx|right].
             unfold blocks_den in Hx |- *. apply in_map_iff in Hx as [y [<- Hy]]. apply in_map_iff. exists y. split; [reflexivity | exact (HG12 y Hy)]. }
           assert (OQ : forall x, In x (blocks_den E (a_vis cs ++ (G1 ++ G2))) -> In x (blocks_den E' (a_vis cs' ++ a_fake cs'))).
           { intros x Hx. unfold cs'. cbn [a_vis a_fake].
             pose proof (pairs_vars_lt_app_l _ _ _ Fallow) as PV1.
             rewrite (blocks_den_agree v E E' (a_vis cs ++ (G1 ++ G2)) Hag); [exact Hx|].
             unfold pairs_vars_lt in *. rewrite forallb_app, PV1, Hvars'. reflexivity. }
           assert (ONK : forall x, In x (blocks_den E (a_vis cs ++ (G1 ++ G2))) -> In x (Lc ++ blocks_den E (G1 ++ G2))).
           { intros x Hx. unfold Lc. rewrite <- blocks_den_app. exact Hx. }
           exact (Mr_kept_shadow SWIN PERMc SPTOPc SHC VSH AINV G AINV_top SHC_stack SHC_image PERM_vsh E E' cs cs' model mdl' M M' _ _ _
                    (a_vis cs ++ (G1 ++ G2) ++ ghosts_ne (kn cs) (a_ghost cs)) (reg cs 2) 0 (co_ainv HC)
                    (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OP) (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) OQ)
                    Lc _ Hfr0 (objs_ghost_ext SEGS PERMc E MR cs _ _ _ HK (co_perm HC) ONK) a Ha).
      * exact Hh'.
      * rewrite Hfs', Hfs1. exact (co_fs HC).
      * eapply fds_ok_model; [rewrite Hfds'; exact Hfds1 | rewrite Hfs'; exact Hfs1 |]. eapply APS.fds_ok_agree; [exact Hag | exact Ffd | exact (co_fds HC)].
      * fold cs'. exact HA'.
      * eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | exact (co_uinv HC)].
      * exact (co_fx HC).
      * rewrite (wins_den_agree v E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
      * rewrite (sptop_den_agree v E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
      * rewrite (uE_agree v E E' (a_meter cs) Hag Fmt). exact (co_kcap HC).
      * rewrite HFB'. pose proof (co_fbud HC) as CF. rewrite HFK in CF. rewrite !length_app in *. cbn [length] in CF. lia.
      * eapply GPS.floor_sem_agree; [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
    + rewrite Hfs', Hfs1. reflexivity.
Qed.

Theorem node_fakerel_obl : forall IT, itab_sound SEGS IT ->
  fakerel_nspec SEGS SWIN PERMc G AINV FXOK RZ -> AzContracts.OBL_fakerel SEGS IT nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ G.
Proof. intros IT IT_ok FRS. exact (node_fakerel_sound IT IT_ok FRS). Qed.


End Alloc.
