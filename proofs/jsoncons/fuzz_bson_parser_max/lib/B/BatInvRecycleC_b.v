(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatSecAllocPost_b BatFxQ_b
     BatRecycle2C_b BatRecycle3L_b BatRecycle4P_b BatRecycle4S_b BatRecycle5A_b BatRecycle5I_b BatRecycle5T_b BatInvRecycleA_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma art_not_out_in : forall W x, ~ art_out W x -> exists p, In p W /\ fst p <= x < fst p + snd p.
Proof.
  induction W as [|p r IH]; intros x N; cbn [art_out] in N; [exfalso; apply N; exact I|].
  destruct (Z_le_dec (fst p) x) as [H1|H1]; [destruct (Z_lt_dec x (fst p + snd p)) as [H2|H2]|].
  - exists p. split; [left; reflexivity|lia].
  - destruct (IH x) as (q & Hq & Rq); [intros O; apply N; split; [lia|exact O]|]. exists q. split; [right; exact Hq|exact Rq].
  - destruct (IH x) as (q & Hq & Rq); [intros O; apply N; split; [lia|exact O]|]. exists q. split; [right; exact Hq|exact Rq].
Qed.

Definition art_rel_shw (spb : Z) (e : art_rel) : Z * Z :=
  match e with
  | REP c w d _ n => (SB + (spb + c * 2 ^ 32 + 16 * w + d + 16) / 8, (n + 7) / 8 * 8 / 8)
  | RES mb ms _ _ _ => (SB + mb / 8, ms / 8)
  | REB _ => (0, 0)
  end.

Lemma art_out_intro : forall W x, (forall p, In p W -> ~ (fst p <= x < fst p + snd p)) -> art_out W x.
Proof. induction W as [|p r IH]; intros x H; cbn [art_out]; [exact I|]. split; [apply H; left; reflexivity|apply IH; intros q Hq; apply H; right; exact Hq]. Qed.

(* [comment removed for export] *)
Lemma art_shw_in_zone : forall spb qs e x, spb = 65536 * qs ->
  match e with
  | REP c w d _ n => 0 <= d /\ d mod 16 = 0 /\ d + 16 + (n + 7) / 8 * 8 <= AsanTab.class_size c /\ AsanTab.class_size c mod 16 = 0 /\ 0 <= n
  | _ => True end ->
  fst (art_rel_shw spb e) <= x < fst (art_rel_shw spb e) + snd (art_rel_shw spb e) ->
  SB + fst (art_rel_zone spb e) / 8 <= x < SB + (fst (art_rel_zone spb e) + snd (art_rel_zone spb e)) / 8.
Proof.
  intros spb qs e x Espb GE Hx. destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_shw art_rel_zone fst snd] in *.
  - destruct GE as (Hd & Hd16 & Hdsz & Hsz16 & Hn).
    pose proof (Z.div_mod d 16 ltac:(lia)) as Dd. rewrite Hd16 in Dd. pose proof (Z.div_mod (AsanTab.class_size c) 16 ltac:(lia)) as Ds. rewrite Hsz16 in Ds.
    set (r := (n + 7) / 8) in *.
    assert (E1 : (spb + c * 2 ^ 32 + 16 * w + d + 16) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (d / 16) + 2).
    { rewrite Espb. replace (65536 * qs + c * 2 ^ 32 + 16 * w + d + 16) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (d / 16) + 2) * 8) by lia. apply Z_div_mult. lia. }
    assert (E2 : (spb + c * 2 ^ 32 + 16 * w) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w).
    { rewrite Espb. replace (65536 * qs + c * 2 ^ 32 + 16 * w) with ((8192 * qs + c * 2 ^ 29 + 2 * w) * 8) by lia. apply Z_div_mult. lia. }
    assert (E3 : (spb + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (AsanTab.class_size c / 16)).
    { rewrite Espb. replace (65536 * qs + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * (AsanTab.class_size c / 16)) * 8) by lia. apply Z_div_mult. lia. }
    assert (E4 : r * 8 / 8 = r) by (apply Z_div_mult; lia).
    rewrite E1, E4 in Hx. rewrite E2, E3. assert (0 <= r) by (apply Z.div_pos; lia). lia.
  - assert (mb / 8 + ms / 8 <= (mb + ms) / 8).
    { pose proof (Z.div_mod mb 8 ltac:(lia)). pose proof (Z.mod_pos_bound mb 8 ltac:(lia)). pose proof (Z.div_mod ms 8 ltac:(lia)). pose proof (Z.mod_pos_bound ms 8 ltac:(lia)).
      apply Z.div_le_lower_bound; lia. }
    lia.
  - lia.
Qed.

Section Where.
Variables (t spb ris parr : Z).

Definition art_fp_where (sp1 : Z) (bl : list (Z * Z)) (es : list art_rel) (x : Z) : Prop :=
  (sp1 - 320 <= x < sp1) \/ (0x13c618 + 56 <= x < 0x13c8a8) \/ (t + 208 <= x < t + 2904) \/ (ris <= x < ris + 4096)
  \/ (exists c, 1 <= c <= 30 /\ spb + c * 2 ^ 32 + 3758096384 <= x < spb + c * 2 ^ 32 + 2 ^ 32)
  \/ (exists e, In e es /\ (fst (art_rel_zone spb e) <= x < fst (art_rel_zone spb e) + snd (art_rel_zone spb e)
                            \/ fst (art_rel_shw spb e) <= x < fst (art_rel_shw spb e) + snd (art_rel_shw spb e)))
  \/ (parr <= x < parr + 2 ^ 23) \/ (exists b, In b bl /\ fst b + 24 <= x < fst b + 32).

#[using="Type"] Lemma art_fp_where_mono : forall sp1 bl bl' es es' x, (forall b, In b bl -> In b bl') -> (forall e, In e es -> In e es') -> art_fp_where sp1 bl es x -> art_fp_where sp1 bl' es' x.
Proof.
  intros sp1 bl bl' es es' x Hb He [H|[H|[H|[H|[H|[(e & Hin & H)|[H|(b & Hin & H)]]]]]]]; unfold art_fp_where; auto 10.
  - do 5 right. left. exists e. split; [apply He; exact Hin|exact H].
  - do 7 right. exists b. split; [apply Hb; exact Hin|exact H].
Qed.

#[using="Type"] Lemma art_lcd_fp_where : forall sp1 c nf x p, 1 <= c <= 30 -> 0 <= nf -> 4 * nf + 32 <= 2 ^ 29 -> In p (art_lcd_fp sp1 (t + 208) spb ris c nf) -> fst p <= x < fst p + snd p ->
  (sp1 - 320 <= x < sp1) \/ (t + 208 <= x < t + 2904) \/ (ris <= x < ris + 4096) \/ (spb + c * 2 ^ 32 + 3758096384 <= x < spb + c * 2 ^ 32 + 2 ^ 32).
Proof.
  intros sp1 c nf x p Hc Hnf Hb Hin Hx. unfold art_lcd_fp in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hx; lia.
Qed.

#[using="Type"] Lemma art_rel_fp_where : forall sp1 G e x p, art_rel_pre G e ->
  (forall c, 1 <= c <= 30 -> 4 * Z.of_nat (length (cl_free (rg_cls G c))) + 32 <= 2 ^ 29) -> Z.of_nat (length (rg_bl G)) <= 2 ^ 20 ->
  In p (art_rel_fp t spb ris parr sp1 G e) -> fst p <= x < fst p + snd p -> art_fp_where sp1 (rg_bl G) [e] x.
Proof.
  intros sp1 G e x p PRE NF LEN Hin Hx. unfold art_fp_where.
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_fp art_rel_pre] in *.
  - destruct PRE as (Hc & (Hw0 & _) & _ & Hd & Hd16 & Hdsz & _ & Hn).
    assert (Hr0 : 0 <= (n + 7) / 8 * 8) by (assert (0 <= (n + 7) / 8) by (apply Z.div_pos; lia); lia).
    unfold art_cbr_prim_fp in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hx.
      * left. lia.
      * do 5 right. left. exists (REP c w d b1 n). split; [left; reflexivity|]. left. cbn [art_rel_zone fst snd]. lia.
      * do 5 right. left. exists (REP c w d b1 n). split; [left; reflexivity|]. left. cbn [art_rel_zone fst snd]. lia.
      * do 5 right. left. exists (REP c w d b1 n). split; [left; reflexivity|]. right. cbn [art_rel_shw fst snd]. exact Hx.
      * right; right; left. lia.
    + destruct (art_lcd_fp_where sp1 c (Z.of_nat (length (cl_free (rg_cls G c)))) x p Hc ltac:(lia) (NF c Hc) Hin Hx) as [H|[H|[H|H]]]; [left; exact H|right; right; left; exact H|right; right; right; left; exact H|].
      do 4 right. left. exists c. split; [exact Hc|exact H].
  - destruct PRE as (Hbl & Lo & Hi & _).
    assert (NEl : rg_bl G <> []) by (intros E; rewrite E in Hbl; destruct Hbl).
    assert (Hlast : In (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) (rg_bl G)) by (apply nth_In; destruct (rg_bl G); [contradiction|cbn [length]; lia]).
    assert (Hidx : (art_bl_idx mb (rg_bl G) < length (rg_bl G))%nat).
    { clear - Hbl. induction (rg_bl G) as [|b r IH]; [destruct Hbl|]. cbn [art_bl_idx length]. destruct (Z.eqb_spec (fst b) mb) as [E|NE]; [lia|].
      destruct Hbl as [Eb|Hb]; [exfalso; apply NE; rewrite Eb; reflexivity|]. specialize (IH Hb). lia. }
    unfold art_cbr_sec_fp, art_secd_fp in Hin. cbn [In app] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Hx.
    + left. lia.
    + right; right; left. lia.
    + left. lia.
    + right; left. lia.
    + right; left. lia.
    + do 6 right. left. lia.
    + do 7 right. exists (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)). split; [exact Hlast|lia].
    + right; right; left. lia.
    + do 5 right. left. exists (RES mb ms m b1 n). split; [left; reflexivity|]. right. cbn [art_rel_shw fst snd]. exact Hx.
    + do 5 right. left. exists (RES mb ms m b1 n). split; [left; reflexivity|]. left. cbn [art_rel_zone fst snd]. exact Hx.
  - destruct (art_lcd_fp_where sp1 24 (Z.of_nat (length (cl_free (rg_cls G 24)))) x p ltac:(lia) ltac:(lia) (NF 24 ltac:(lia)) Hin Hx) as [H|[H|[H|H]]]; [left; exact H|right; right; left; exact H|right; right; right; left; exact H|].
    do 4 right. left. exists 24. split; [lia|exact H].
Qed.

#[using="Type"] Lemma art_rels_fp_where : forall sp1 bl0 es G x p, art_rels_pre G es -> art_rg_ok G ->
  (forall c, 1 <= c <= 30 -> Z.of_nat (length (cl_cache (rg_cls G c))) + Z.of_nat (length (cl_free (rg_cls G c))) + Z.of_nat (length es) <= 2 ^ 26) ->
  Z.of_nat (length (rg_bl G)) <= 2 ^ 20 -> (forall b, In b (rg_bl G) -> In b bl0) ->
  In p (art_rels_fp t spb ris parr sp1 G es) -> fst p <= x < fst p + snd p -> art_fp_where sp1 bl0 es x.
Proof.
  intros sp1 bl0 es. induction es as [|e r IH]; intros G x p PRE OK CNT LEN SUB Hin Hx; cbn [art_rels_fp] in Hin; [destruct Hin|].
  destruct PRE as (Pe & Pr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply (art_fp_where_mono sp1 (rg_bl G) bl0 [e] (e :: r) x SUB); [intros e' [<-|[]]; left; reflexivity|].
    apply (art_rel_fp_where sp1 G e x p Pe); [|exact LEN|exact Hin|exact Hx].
    intros c Hc. specialize (CNT c Hc). cbn [length] in CNT. lia.
  - apply (art_fp_where_mono sp1 bl0 bl0 r (e :: r) x (fun b H => H)); [intros e' He'; right; exact He'|].
    apply (IH (art_rel_step e G) x p Pr (art_rg_ok_step e G OK Pe)); [| | |exact Hin|exact Hx].
    + intros c Hc. specialize (CNT c Hc). cbn [length] in CNT. destruct OK as (CK & _).
      destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls art_rel_pre] in *.
      * destruct Pe as (Hc0 & _). destruct (Z.eq_dec c c0) as [->|NE]; [rewrite art_cls_upd_same|rewrite art_cls_upd_other by exact NE; lia].
        pose proof (art_cls_dealloc_total c0 w0 (rg_cls G c0) (CK c0 Hc0) ltac:(lia)). lia.
      * lia.
      * destruct (Z.eq_dec c 24) as [->|NE]; [rewrite art_cls_upd_same|rewrite art_cls_upd_other by exact NE; lia].
        pose proof (art_cls_dealloc_total 24 wb0 (rg_cls G 24) (CK 24 ltac:(lia)) ltac:(lia)). lia.
    + destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_bl]; try exact LEN. rewrite art_swap_remove_length. lia.
    + intros b Hb. apply SUB. destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_bl] in Hb; try exact Hb. exact (art_swap_remove_in _ _ _ _ _ Hb).
Qed.
End Where.

Lemma art_in_not_out : forall W p z, In p W -> fst p <= z < fst p + snd p -> ~ art_out W z.
Proof. induction W as [|q r IH]; intros p z Hp Hz O; [destruct Hp|]. cbn [art_out] in O. destruct O as (O1 & O2). destruct Hp as [->|Hp]; [exact (O1 Hz)|exact (IH p z Hp Hz O2)]. Qed.

Lemma art_rels_fp_sec_in : forall t spb ris parr sp1 es G mb ms m b1 n, In (RES mb ms m b1 n) es ->
  In (mb, ms) (art_rels_fp t spb ris parr sp1 G es) /\ In (SB + mb / 8, ms / 8) (art_rels_fp t spb ris parr sp1 G es).
Proof.
  intros t spb ris parr sp1 es. induction es as [|e r IH]; intros G mb ms m b1 n Hin; [destruct Hin|]. cbn [art_rels_fp].
  destruct Hin as [->|Hin]; [|destruct (IH (art_rel_step e G) mb ms m b1 n Hin) as (X1 & X2); split; apply in_or_app; right; assumption].
  cbn [art_rel_fp]. unfold art_cbr_sec_fp, art_secd_fp. split; apply in_or_app; left; cbn [In app]; tauto.
Qed.
