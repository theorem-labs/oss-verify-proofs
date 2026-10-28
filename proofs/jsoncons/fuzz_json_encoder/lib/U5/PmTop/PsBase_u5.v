(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSB.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Definition ps_upd (ps : PML.pstate) (st : Z) (mo : bool) (stk : list Z) (w : option (Z * Z)) : PML.pstate :=
  PML.PS st (PML.ps_sst ps) (PML.ps_nst ps) mo (PML.ps_done ps) (PML.ps_level ps) stk (PML.ps_sb ps) (PML.ps_scap ps) (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps) w.
Lemma ps_upd_same : forall ps, ps_upd ps (PML.ps_st ps) (PML.ps_more ps) (PML.ps_stack ps) (PML.ps_win ps) = ps.
Proof. intros []. reflexivity. Qed.
Lemma ps_upd_win : forall ps w, ps_upd ps (PML.ps_st ps) (PML.ps_more ps) (PML.ps_stack ps) w = PML.ps_set_win ps w.
Proof. intros [] w. reflexivity. Qed.

(* [comment removed for export] *)
Lemma parser_at_upd : forall (K : Z -> Prop) (M M' : mem) P ps st' mo' stk' w' sfx,
  PML.parser_at M P ps -> TK.samem K M M' -> mem_grows M M' -> 0 <= P < 2 ^ 60 ->
  (0 <= PML.ps_bptr ps /\ PML.ps_bptr ps + PML.ps_bcap ps < 2 ^ 62 /\ TK2.cov K (PML.ps_bptr ps) (PML.ps_bcap ps)) ->
  (0 <= PML.ps_sb ps /\ PML.ps_sb ps + PML.ps_scap ps < 2 ^ 62 /\ TK2.cov K (PML.ps_sb ps) (PML.ps_scap ps)) ->
  TK2.cov K P 148 (* [comment removed for export] *) ->
  TK2.cov K (P + 209) 2 -> TK2.cov K (P + 212) 44 -> TK2.cov K (P + 264) 8 ->
  match w' with None => PML.u64 M' (P + 192) 0 /\ PML.u64 M' (P + 200) 0 | Some (p, e) => PML.u64 M' (P + 200) p /\ PML.u64 M' (P + 192) e /\ p <= e end ->
  PML.u8 M' (P + 208) st' -> PML.u8 M' (P + 211) (PML.b2z mo') -> PML.u64 M' (P + 256) (PML.ps_sb ps + Z.of_nat (length stk')) -> PML.ps_stack ps = stk' ++ sfx ->
  PML.parser_at M' P (ps_upd ps st' mo' stk' w').
Proof.
  intros K M M' P ps st' mo' stk' w' sfx H AG MG HP (B1 & B2 & B3) (S1 & S2 & S3) C0 C209 C212 C264 HW HST HMO HEND HSTK. unfold PML.parser_at in *.
  destruct H as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  assert (C : forall a n, (P <= a /\ a + n <= P + 148) \/ (P + 209 <= a /\ a + n <= P + 211) \/ (P + 212 <= a /\ a + n <= P + 256) \/ (P + 264 <= a /\ a + n <= P + 272) -> TK2.cov K a n).
  { intros a n [Ha|[Ha|[Ha|Ha]]]; [eapply TK2.cov_sub; [exact C0|lia|lia] | eapply TK2.cov_sub; [exact C209|lia|lia] | eapply TK2.cov_sub; [exact C212|lia|lia] | eapply TK2.cov_sub; [exact C264|lia|lia]]. }
  destruct ps as [st sst nst more done level stack sb scap bcap bptr buf win].
  cbn [ps_upd PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win] in *.
  assert (LEN : Z.of_nat (length stk') <= Z.of_nat (length stack)) by (rewrite HSTK, length_app; lia).
  repeat (split; [first [apply (TK2.u64_x K M M' AG); [lia | apply C; lia | assumption] | apply (TK2.u32_x K M M' AG); [lia | apply C; lia | assumption] | apply (TK2.u8_x K M M' AG); [lia | apply C; lia | assumption]
                        | apply (TK2.lstr_short_x K M M' AG); [lia | apply C; lia | assumption] ]|]).
  split; [exact HW|]. split; [exact HST|].
  split; [apply (TK2.u8_x K M M' AG); [lia | apply C; lia | assumption]|]. split; [apply (TK2.u8_x K M M' AG); [lia | apply C; lia | assumption]|].
  split; [exact HMO|].
  repeat (split; [first [apply (TK2.u32_x K M M' AG); [lia | apply C; lia | assumption] | apply (TK2.u8_x K M M' AG); [lia | apply C; lia | assumption]]|]).
  split; [apply (TK2.str_at_x K M M' AG); [lia | split; [apply C; lia | split; [lia | split; [lia | exact B3]]] | exact Abuf]|].
  split; [exact Abc|].
  split; [apply (TK2.u64_x K M M' AG); [lia | apply C; lia | assumption]|]. split; [exact HEND|]. split; [apply (TK2.u64_x K M M' AG); [lia | apply C; lia | assumption]|].
  split.
  - assert (PRE : L5.bytes_at RSEGS M sb stk').
    { intros i Hi. specialize (Astk i ltac:(rewrite HSTK, length_app; lia)). rewrite HSTK, app_nth1 in Astk by exact Hi. exact Astk. }
    apply (TK.bytes_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply S3; lia | exact PRE].
  - split; [lia|]. exact (L5.defined_grows M M' _ _ MG Adef).
Qed.

(* [comment removed for export] *)
Lemma wf_upd_win : forall ps w, PML.wf_ps ps -> PML.wf_ps (PML.ps_set_win ps w).
Proof. intros [] w H. exact H. Qed.
Lemma wf_more_false : forall ps w, PML.wf_ps ps -> PML.wf_ps (ps_upd ps (PML.ps_st ps) false (PML.ps_stack ps) w).
Proof.
  intros ps w (H1 & H2 & H3 & H4 & C & T & HS & HC & _). unfold PML.wf_ps, ps_upd. cbn.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exists C, T. split; [exact HS|]. split; [exact HC|]. intros X. discriminate X.
Qed.
Lemma pcredit_upd : forall L cr ps st mo stk w kx bx, PML.pcredit_x L cr ps kx bx -> PML.pcredit_x L cr (ps_upd ps st mo stk w) kx bx.
Proof. intros L cr [] st' mo' stk' w' kx bx H. exact H. Qed.
Lemma buf_bound_upd : forall ps st mo stk w B, PML.buf_bound ps B -> PML.winlen (ps_upd ps st mo stk w) <= PML.winlen ps ->
  (mo = false \/ (mo = PML.ps_more ps /\ st = PML.ps_st ps)) -> PML.buf_bound (ps_upd ps st mo stk w) B.
Proof.
  intros ps st mo stk w B [H1 H2] HW HM. split; [|exact H2]. unfold PML.buf_need in *. destruct ps as [st0 sst nst more done level stack sb scap bcap bptr buf win].
  cbn [ps_upd PML.ps_more PML.ps_st PML.ps_sst PML.ps_buf] in *.
  assert (N0 : 0 <= (if (more && (st0 =? PML.ST_STRING))%bool then PML.esc_need sst else 0)).
  { destruct (more && (st0 =? PML.ST_STRING))%bool; [|lia]. unfold PML.esc_need. destruct (Z.to_nat sst) as [|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]; cbn; try lia. destruct n; cbn; lia. }
  destruct HM as [->|[-> ->]]; [cbn [andb]; lia | lia].
Qed.
Lemma win_ok_sub : forall (M : mem) LBo ps st mo stk p e q, PML.ps_win ps = Some (p, e) -> p <= q <= e -> PML.win_ok M LBo ps -> PML.win_ok M LBo (ps_upd ps st mo stk (Some (q, e))).
Proof.
  intros M LBo ps st mo stk p e q HW Hq H. unfold PML.win_ok in *. rewrite HW in H. destruct ps. cbn [ps_upd PML.ps_win] in *.
  destruct H as (ch & Hin & H1 & H2 & Hd). exists ch. split; [exact Hin|]. split; [lia|]. split; [exact H2|]. intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply Hd. lia.
Qed.
Lemma ws_upd : forall ps w, PML.ws_ok ps -> PML.ws_ok (ps_upd ps (PML.ps_st ps) (PML.ps_more ps) (PML.ps_stack ps) w).
Proof. intros [] w H. exact H. Qed.

(* [comment removed for export] *)
Lemma buf_bound_upd2 : forall ps st mo stk w B, PML.buf_bound ps B -> PML.winlen (ps_upd ps st mo stk w) <= PML.winlen ps -> st <> PML.ST_STRING -> PML.buf_bound (ps_upd ps st mo stk w) B.
Proof.
  intros ps st mo stk w B [H1 H2] HW HS. split; [|exact H2]. unfold PML.buf_need in *. destruct ps as [st0 sst nst more done level stack sb scap bcap bptr buf win].
  cbn [ps_upd PML.ps_more PML.ps_st PML.ps_sst PML.ps_buf] in *.
  assert (N0 : 0 <= (if (more && (st0 =? PML.ST_STRING))%bool then PML.esc_need sst else 0)).
  { destruct (more && (st0 =? PML.ST_STRING))%bool; [|lia]. unfold PML.esc_need. destruct (Z.to_nat sst) as [|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]; cbn; try lia. destruct n; cbn; lia. }
  assert (E : (st =? PML.ST_STRING) = false) by (apply Z.eqb_neq; exact HS). rewrite E, andb_false_r. lia.
Qed.

(* [comment removed for export] *)
Lemma pop_cr : forall ps, PML.wf_ps ps -> PML.ws_ok ps -> PML.ps_st ps = PML.ST_CR ->
  exists rest x, PML.ps_stack ps = rest ++ [x] /\ 0 <= x < 256 /\ x <> PML.ST_CR /\ x <> PML.ST_STRING /\
    forall w, PML.wf_ps (ps_upd ps x (PML.ps_more ps) rest w) /\ PML.ws_ok (ps_upd ps x (PML.ps_more ps) rest w).
Proof.
  intros ps (H1 & H2 & H3 & H4 & C & T & HS & HC & HM) WS HST. destruct (PML.ps_more ps) eqn:EM.
  - destruct (HM eq_refl) as (M1 & M2 & M3 & M4 & M5 & M6). rewrite HST in M4, M5, M6.
    assert (WSX : forall st stk w, PML.ws_ok (ps_upd ps st true stk w)) by (intros st stk w X; destruct ps; cbn in X; discriminate X).
    destruct M4 as [(_ & NC)|[(_ & X)|[(S & ES & -> & _)|(S & ES & -> & _)]]].
    + exfalso. apply NC. right. reflexivity.
    + unfold PML.ST_CR, PML.ST_STRING in X. discriminate X.
    + exists (PML.ST_ROOT :: C), S. unfold PML.is_expect in ES. cbn [In] in ES. unfold PML.ST_CR, PML.ST_STRING.
      split; [rewrite HS; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. intros w. split; [|apply WSX].
      unfold PML.wf_ps. destruct ps as [st0 sst nst more done level stack sb scap bcap bptr buf win]. cbn [ps_upd PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_level PML.ps_stack PML.ps_scap PML.ps_buf] in *.
      split; [exact H1|]. split; [exact H2|]. split; [rewrite HS in H3; cbn [length] in H3 |- *; rewrite ?length_app in H3; cbn [length] in H3; lia|]. split; [exact H4|].
      exists C, []. split; [rewrite app_nil_r; reflexivity|]. split; [exact HC|]. intros _.
      split; [exact M1|]. split; [exact M2|]. split; [unfold PML.handled; lia|].
      split; [left; split; [reflexivity | unfold PML.comment_or_cr, PML.ST_CR; lia]|].
      split; [intros [X|[]]; apply M5; right; left; exact X | unfold PML.ST_NUMBER; lia].
    + exists (PML.ST_ROOT :: C ++ [S]), PML.ST_SLASH_STAR. unfold PML.ST_SLASH_STAR, PML.ST_CR, PML.ST_STRING.
      split; [rewrite HS; cbn [app]; rewrite <- app_assoc; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. intros w. split; [|apply WSX].
      unfold PML.wf_ps. destruct ps as [st0 sst nst more done level stack sb scap bcap bptr buf win]. cbn [ps_upd PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_level PML.ps_stack PML.ps_scap PML.ps_buf] in *.
      split; [exact H1|]. split; [exact H2|]. split; [rewrite HS in H3; cbn [length] in H3 |- *; rewrite ?length_app in H3 |- *; cbn [length] in H3 |- *; lia|]. split; [exact H4|].
      exists C, [S]. split; [reflexivity|]. split; [exact HC|]. intros _.
      split; [exact M1|]. split; [exact M2|]. split; [unfold PML.handled; lia|].
      split; [right; right; left; exists S; split; [exact ES|]; split; [reflexivity | unfold PML.comment_or_cr; lia]|].
      split; [intros [X|[X|[]]]; [unfold PML.ST_SLASH_STAR, PML.ST_EXPECT_COMMA_OR_END in X; lia | apply M5; right; left; exact X] | unfold PML.ST_NUMBER; lia].
  - destruct (WS EM) as (C' & FC & LC & [(X & _)|(_ & HS')] & LV); [rewrite HST in X; unfold PML.ST_CR, PML.ST_DONE in X; discriminate X|].
    exists (PML.ST_ROOT :: C'), PML.ST_DONE. unfold PML.ST_DONE, PML.ST_CR, PML.ST_STRING.
    split; [rewrite HS'; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. intros w.
    destruct ps as [st0 sst nst more done level stack sb scap bcap bptr buf win]. cbn [ps_upd PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_level PML.ps_stack PML.ps_scap PML.ps_buf] in *. split.
    + unfold PML.wf_ps. cbn [ps_upd PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_level PML.ps_stack PML.ps_scap PML.ps_buf].
      split; [exact H1|]. split; [exact H2|]. split; [cbn [length]; lia|]. split; [exact H4|].
      exists C', []. split; [rewrite app_nil_r; reflexivity|]. split; [exact FC|]. intros X. discriminate X.
    + intros _. cbn [ps_upd PML.ps_st PML.ps_more PML.ps_level PML.ps_stack]. exists C'. split; [exact FC|]. split; [exact LC|]. split; [left; split; reflexivity | exact LV].
Qed.
(* [comment removed for export] *)
Lemma ws_more_true : forall ps, PML.ps_more ps = true -> PML.ws_ok ps.
Proof. intros ps H X. rewrite H in X. discriminate X. Qed.
End PSB.
