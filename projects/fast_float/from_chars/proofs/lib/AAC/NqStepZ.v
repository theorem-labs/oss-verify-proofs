(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcPri AcPriSepOk AcNPop AcPriStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition BQ (pz : list Z) : Z := z_sb pz + 103079215104 + 8192 * z_qj pz.

Definition qz_room (pz : list Z) (sz : Z) : list Z := set_nth 67 (z_qb pz + sz) (set_nth 66 (z_qn pz + 1) pz).

Section QRoomZ.
Variable pz : list Z.
Variable sz : Z.
Hypothesis Hlen : List.length pz = PRI_LEN.

#[using="Hlen"] Lemma zn_qroom : forall k, zn (qz_room pz sz) k = if Nat.eqb k 67 then z_qb pz + sz else if Nat.eqb k 66 then z_qn pz + 1 else zn pz k.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros k. unfold zn, qz_room.
  rewrite nth_set_nth by (rewrite set_nth_length, Hlen; unfold PRI_LEN; lia).
  destruct (Nat.eqb k 67); [reflexivity|].
  rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qroom_len : List.length (qz_room pz sz) = PRI_LEN.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold qz_room. rewrite !set_nth_length. exact Hlen. Qed.
#[using="Hlen"] Lemma qroom_sb : z_sb (qz_room pz sz) = z_sb pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_sb. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_sh : z_sh (qz_room pz sz) = z_sh pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_sh. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_ca : z_ca (qz_room pz sz) = z_ca pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_ca. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_pg : z_pg (qz_room pz sz) = z_pg pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_pg. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_tg : z_tg (qz_room pz sz) = z_tg pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_tg. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_qj : z_qj (qz_room pz sz) = z_qj pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qj. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_qn : z_qn (qz_room pz sz) = z_qn pz + 1. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qn. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_qb : z_qb (qz_room pz sz) = z_qb pz + sz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qb. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_gn : z_gn (qz_room pz sz) = z_gn pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gn. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_gl : z_gl (qz_room pz sz) = z_gl pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gl. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_gb : z_gb (qz_room pz sz) = z_gb pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gb. rewrite zn_qroom. reflexivity. Qed.
#[using="Hlen"] Lemma qroom_j : forall c, 1 <= c <= 30 -> z_j (qz_room pz sz) c = z_j pz c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros c Hc. pose proof (cidx_rng c Hc) as Hi. unfold z_j. rewrite zn_qroom.
  replace (Nat.eqb (5 + 2 * cidx c) 67) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c) 66) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qroom_z : forall c, 1 <= c <= 30 -> z_z (qz_room pz sz) c = z_z pz c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros c Hc. pose proof (cidx_rng c Hc) as Hi. unfold z_z. rewrite zn_qroom.
  replace (Nat.eqb (6 + 2 * cidx c) 67) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c) 66) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qroom_foot : forall x, pri_foot_z (qz_room pz sz) x <-> pri_foot_z pz x.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros x. unfold pri_foot_z. rewrite qroom_ca, qroom_sb, qroom_sh.
  split; (intros [H|[H|[H|(c & Hc & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H | right; right; right; exists c; split; [exact Hc|]]).
  - rewrite (qroom_z c (in_cls_rng c Hc)) in H. exact H.
  - rewrite (qroom_z c (in_cls_rng c Hc)). exact H.
Qed.
End QRoomZ.

(* [comment removed for export] *)
Lemma q_seps : forall pz m0, INV_Az pz m0 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) ->
  (z_ca pz + 2592 <= z_pg pz \/ z_pg pz + 137439023104 <= z_ca pz - 128) /\
  (2199291686912 + 2147450880 <= z_sh pz /\ z_sh pz + 17179869184 <= z_pg pz) /\
  (z_ca pz + 2592 <= z_sh pz \/ z_sh pz + 17179869184 <= z_ca pz - 128) /\
  (4096 <= z_ca pz - 208 /\ z_ca pz + 3888 <= 2^47 /\ z_pg pz <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= z_pg pz + 137439023104 /\
   z_pg pz + 137439023104 <= 2^47 /\ 17594333495296 <= z_pg pz).
Proof.
  intros pz m0 HI Hdisj. pose proof (az_geo pz m0 HI) as G. destruct HI as [_ _ _ _ _ Htg _ _ _ _ _ _]. unfold PG_SIZE in Hdisj.
  assert (S1 : 2199291686912 + 2147450880 <= z_sh pz /\ z_sh pz + 17179869184 <= z_pg pz) by (clear - G; lia).
  split; [clear - Hdisj Htg; lia|]. split; [exact S1|]. split; [clear - G S1 Htg; lia | clear - G; lia].
Qed.

(* [comment removed for export] *)
Lemma INV_Az_qroom : forall pz m0 m0' sz, INV_Az pz m0 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) ->
  1 <= z_qn pz ->
  q_inv m0' (z_ca pz - 128) (z_sb pz) (z_qj pz) (z_qn pz + 1) (z_qb pz + sz) ->
  (forall x, z_ca pz - 104 <= x < z_ca pz - 96 -> wview SEGS m0' (wa x) <> None) ->
  (forall x, pri_foot_z pz x -> ~ (z_ca pz - 104 <= x < z_ca pz - 96) -> ~ (BQ pz + 8 <= x < BQ pz + 8192) -> m0' (wa x) = m0 (wa x)) ->
  INV_Az (qz_room pz sz) m0'.
Proof.
  intros pz m0 m0' sz HI Hdisj Hqn1 HQ HW HF. destruct (q_seps pz m0 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof HI as HI0. destruct HI0 as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  destruct Hq as [Hq0 Hqj]. specialize (Hqj Hqn1).
  assert (Hqj0 : 0 <= z_qj pz < 32).
  { destruct Hq0 as (_ & _ & [(Q0 & _)|(_ & Q2 & _)]); [clear - Q0 Hqn1; lia | exact Q2]. }
  destruct (cls_jb pz m0 HI 24 in_cls_24) as (J24 & J24b & _ & _).
  assert (Z24 : z_z pz 24 = 262144 /\ 1 <= z_j pz 24).
  { destruct (Hcls 24 in_cls_24) as [(J0 & _)|(J1 & Z1 & _)]; [clear - J0 Hqj Hqj0; lia | split; [exact Z1 | exact J1]]. }
  unfold BQ in HF.
  constructor; rewrite ?(qroom_sb pz sz Hlen), ?(qroom_sh pz sz Hlen), ?(qroom_ca pz sz Hlen), ?(qroom_pg pz sz Hlen), ?(qroom_tg pz sz Hlen),
    ?(qroom_qj pz sz Hlen), ?(qroom_qn pz sz Hlen), ?(qroom_qb pz sz Hlen), ?(qroom_gn pz sz Hlen), ?(qroom_gl pz sz Hlen), ?(qroom_gb pz sz Hlen); try assumption.
  - exact (qroom_len pz sz Hlen).
  - (* [comment removed for export] *)
    apply (STATS_frame m0); [clear - B0; lia | clear - B0; lia | | exact Hst].
    intros x Hx. apply HF; [left; clear - Hx; lia | clear - Hx; lia | clear - Hx Hqj0 T1 B0; lia].
  - (* [comment removed for export] *)
    apply wr_bytes; [clear - B0; lia | clear - B0; lia |]. intros x Hx.
    destruct (Z_lt_le_dec x (z_ca pz - 104)) as [L1|L1]; [|destruct (Z_lt_le_dec x (z_ca pz - 96)) as [L2|L2]].
    + rewrite (wview_same m0 m0'); [exact (wr_byte m0 (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) Hwc ltac:(clear - Hx; lia))|].
      apply HF; [left; clear - Hx; lia | clear - L1; lia | clear - Hx Hqj0 T1 B0; lia].
    + apply HW. clear - L1 L2. lia.
    + rewrite (wview_same m0 m0'); [exact (wr_byte m0 (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) Hwc ltac:(clear - Hx; lia))|].
      apply HF; [left; clear - Hx; lia | clear - L2; lia | clear - Hx Hqj0 T1 B0; lia].
  - (* [comment removed for export] *)
    split; [exact HQ|]. intros _. rewrite (qroom_j pz sz Hlen 24 ltac:(lia)). exact Hqj.
  - (* [comment removed for export] *)
    destruct Hgq as [Hg Hgl]. split; [|intros Hgn; rewrite (qroom_j pz sz Hlen 24 ltac:(lia)); exact (Hgl Hgn)].
    apply (gq_inv_o_frame m0 m0' (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) ltac:(clear - B0; lia) ltac:(clear - B0; lia)); [|exact Hg].
    intros x [Hx|(Hg1 & Hx)].
    + apply HF; [right; right; left; exact Hx | clear - Hx Hca; lia | clear - Hx Hqj0 B0; lia].
    + assert (Gl : 0 <= z_gl pz < 32) by (destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | exact G1]).
      apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite (proj1 Z24); clear - Hx Gl; lia | clear - Hx Gl T1 B0; lia |].
      (* [comment removed for export] *)
      clear - Hx Gl Hqj0. lia.
  - (* [comment removed for export] *)
    intros c Hc. pose proof (in_cls_rng c Hc) as Hcr. rewrite (qroom_j pz sz Hlen c Hcr), (qroom_z pz sz Hlen c Hcr).
    destruct (cls_jb pz m0 HI c Hc) as (K0 & K1 & K2 & Kz).
    destruct (cls_tbl c Hc) as (Hsz & Hs8 & Hs8r & Hnw & Hnm & Hmc).
    assert (Kz' : 0 <= z_z pz c <= 262144) by (clear - Kz; lia).
    destruct (Z.eq_dec c 24) as [->|Hne].
    + (* [comment removed for export] *)
      destruct (Hcls 24 in_cls_24) as [(J0 & _)|(J1 & Z1 & Jb & HIo & HPo)]; [clear - J0 Z24; lia|]. right.
      split; [exact J1|]. split; [exact Z1|]. split; [exact Jb|]. split.
      * apply (INV_Co_frame m0); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | | exact HIo].
        intros x Hx. unfold foot_Co in Hx. change (sz_tbl 24) with 8192 in Hx. change (262144 / 8192) with 32 in Hx.
        destruct Hx as [Hx|[Hx|Hx]].
        -- apply HF; [left; clear - Hx; lia | clear - Hx; lia | clear - Hx Hqj0 T1 B0; lia].
        -- apply HF; [right; left; clear - Hx; lia | clear - Hx T1 B0; lia | clear - Hx Hqj0; lia].
        -- apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; right; left; rewrite Z1; clear - Hx; lia | clear - Hx T1 B0; lia | clear - Hx Hqj0; lia].
      * apply (POP_C_frame m0); [| change (sz_tbl 24 / 8) with 1024; clear - J1; lia | exact HPo]. intros x Hx. unfold RBX, SHX in Hx. change (sz_tbl 24) with 8192 in Hx. change (8192 / 8) with 1024 in Hx.
        destruct Hx as [Hx|Hx].
        -- apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z1; clear - Hx J1; lia | clear - Hx T1 B0 J1; lia | clear - Hx Hqj Hqj0; lia].
        -- apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; right; right; left; clear - Hx J1; lia | clear - Hx S1 S2 J1; lia | clear - Hx S1 B0 J1 Hqj0; lia].
    + apply (cls_inv_frame m0 m0' _ _ _ c _ _ Hc); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - S1; lia | clear - S1 B0; lia | exact K0 | | exact (Hcls c Hc)].
      intros x Hx. unfold cls_foot in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
      * apply HF; [left; clear - Hx Hcr; lia | clear - Hx Hcr; lia | clear - Hx Hqj0 T1 B0 Hcr; lia].
      * apply HF; [right; left; clear - Hx Hcr; lia | clear - Hx T1 B0 Hcr; lia | clear - Hx Hqj0 Hcr; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; left; exact Hx | clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx Kz' Hqj0 Hcr Hne; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; right; left; exact Hx | clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx Kz' Hqj0 Hcr Hne; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; right; right; left; exact Hx | clear - Hx S1 S2 Hcr; lia | clear - Hx S1 B0 Hqj0 Hcr; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; right; right; right; exact Hx | clear - Hx S1 S2 Hcr; lia | clear - Hx S1 B0 Hqj0 Hcr; lia].
Qed.

(* [comment removed for export] *)
Lemma q_inv_frame : forall (m m' : word -> option byte) QC SB qj qn qb, 0 <= QC -> QC + 32 <= 2^63 -> 0 <= SB -> SB + 137438953472 <= 2^63 ->
  (forall x, QC <= x < QC + 32 -> m' (wa x) = m (wa x)) ->
  (1 <= qn -> forall x, SB + 103079215104 + 8192 * qj <= x < SB + 103079215104 + 8192 * qj + 8192 -> m' (wa x) = m (wa x)) ->
  q_inv m QC SB qj qn qb -> q_inv m' QC SB qj qn qb.
Proof.
  intros m m' QC SB qj qn qb H1 H2 H3 H4 HFq HFb (Hqb & Rqb & Hq). split; [exact Hqb|]. split.
  { apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HFq; lia | exact Rqb]. }
  destruct Hq as [(Q0 & Qb0 & R0)|(Q1 & Q2 & R1 & R1b & R2 & R3 & R4 & W1)]; [left | right].
  - split; [exact Q0|]. split; [exact Qb0|]. apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HFq; lia | exact R0].
  - specialize (HFb ltac:(lia)).
    split; [exact Q1|]. split; [exact Q2|]. split; [|split; [|split; [|split; [|split]]]].
    + apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HFq; lia | exact R1].
    + apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HFq; lia | exact R1b].
    + apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HFq; lia | exact R2].
    + apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HFb; lia | exact R3].
    + apply (rd_frame m); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HFb; lia | exact R4].
    + apply (wr_frame m); [lia | lia | intros x Hx; apply HFb; lia | exact W1].
Qed.

(* [comment removed for export] *)
Section QFoot.
Variable pz : list Z.
Variable m0 : word -> option byte.
Hypothesis HI : INV_Az pz m0.
Hypothesis Hdisj : z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz.

(* [comment removed for export] *)
#[using="m0 HI Hdisj"] Lemma cb_fp : forall x, z_ca pz - 128 <= x < z_ca pz + 2592 -> pri_foot_z pz x /\ FPmax pz x /\ ~ alloc_part pz x /\ 0 <= x < 2^47.
Proof. LiaFast.lf_pins (fun (m0 HI Hdisj : LiaFast.U) => LiaFast.u0).
  intros x Hx. pose proof (az_geo pz m0 HI) as G. unfold PG_SIZE in Hdisj.
  split; [left; exact Hx|]. split; [right; left; exact Hx|]. split; [|clear - Hx G; lia].
  intros (c' & Hc' & Ha). pose proof (in_cls_rng c' Hc') as Hcr'. destruct (cls_jb pz m0 HI c' Hc') as (J0 & J1 & J2 & _).
  destruct Ha as [Ha|Ha]; clear - Ha Hx G Hdisj Hcr' J0 J1 J2; lia.
Qed.
(* [comment removed for export] *)
#[using="m0 HI"] Lemma bq_fp : 1 <= z_qn pz -> forall x, BQ pz <= x < BQ pz + 8192 -> pri_foot_z pz x /\ FPmax pz x /\ 0 <= x < 2^47.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  intros Hqn x Hx. pose proof (az_geo pz m0 HI) as G. destruct HI as [_ _ _ _ _ _ _ _ _ Hq _ Hcls]. destruct Hq as [Hq0 Hqj]. specialize (Hqj Hqn).
  assert (Hqj0 : 0 <= z_qj pz < 32) by (destruct Hq0 as (_ & _ & [(Q0 & _)|(_ & Q2 & _)]); [clear - Q0 Hqn; lia | exact Q2]).
  assert (Z24 : z_z pz 24 = 262144) by (destruct (Hcls 24 in_cls_24) as [(J0 & _)|(_ & Z1 & _)]; [clear - J0 Hqj Hqj0; lia | exact Z1]).
  unfold BQ in Hx.
  split; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z24; clear - Hx Hqj0; lia|].
  split; [left; unfold PG_SIZE; clear - Hx Hqj0 G; lia | clear - Hx Hqj0 G; lia].
Qed.
End QFoot.

(* [comment removed for export] *)
Definition qz_new (pz : list Z) (sz : Z) : list Z := set_nth 67 (sz + 8192) (set_nth 66 1 (set_nth 65 (z_j pz 24) (pz_step pz 24))).
(* [comment removed for export] *)
Definition BN (pz : list Z) : Z := z_sb pz + 103079215104 + 8192 * z_j pz 24.

Section QNewZ.
Variable pz : list Z.
Variable sz : Z.
Hypothesis Hlen : List.length pz = PRI_LEN.

#[using="Hlen"] Lemma zn_qnew : forall k, zn (qz_new pz sz) k =
  if Nat.eqb k 67 then sz + 8192 else if Nat.eqb k 66 then 1 else if Nat.eqb k 65 then z_j pz 24 else zn (pz_step pz 24) k.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros k. pose proof (step_len pz 24 Hlen) as Hl. unfold zn, qz_new.
  rewrite nth_set_nth by (rewrite !set_nth_length, Hl; unfold PRI_LEN; lia).
  destruct (Nat.eqb k 67); [reflexivity|].
  rewrite nth_set_nth by (rewrite set_nth_length, Hl; unfold PRI_LEN; lia).
  destruct (Nat.eqb k 66); [reflexivity|].
  rewrite nth_set_nth by (rewrite Hl; unfold PRI_LEN; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qnew_len : List.length (qz_new pz sz) = PRI_LEN.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold qz_new. rewrite !set_nth_length. exact (step_len pz 24 Hlen). Qed.
#[using="Hlen"] Lemma qnew_sb : z_sb (qz_new pz sz) = z_sb pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_sb. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_sb pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_sh : z_sh (qz_new pz sz) = z_sh pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_sh. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_sh pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_ca : z_ca (qz_new pz sz) = z_ca pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_ca. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_ca pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_pg : z_pg (qz_new pz sz) = z_pg pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_pg. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_pg pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_tg : z_tg (qz_new pz sz) = z_tg pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_tg. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_tg pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_qj : z_qj (qz_new pz sz) = z_j pz 24. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qj. rewrite zn_qnew. reflexivity. Qed.
#[using="Hlen"] Lemma qnew_qn : z_qn (qz_new pz sz) = 1. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qn. rewrite zn_qnew. reflexivity. Qed.
#[using="Hlen"] Lemma qnew_qb : z_qb (qz_new pz sz) = sz + 8192. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qb. rewrite zn_qnew. reflexivity. Qed.
#[using="Hlen"] Lemma qnew_gn : z_gn (qz_new pz sz) = z_gn pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gn. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_gn pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_gl : z_gl (qz_new pz sz) = z_gl pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gl. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_gl pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_gb : z_gb (qz_new pz sz) = z_gb pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gb. rewrite zn_qnew. cbn [Nat.eqb]. exact (step_gb pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_j : forall c, 1 <= c <= 30 -> z_j (qz_new pz sz) c = z_j (pz_step pz 24) c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros c Hc. pose proof (cidx_rng c Hc) as Hi. unfold z_j at 1. rewrite zn_qnew.
  replace (Nat.eqb (5 + 2 * cidx c) 67) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c) 66) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c) 65) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qnew_z : forall c, 1 <= c <= 30 -> z_z (qz_new pz sz) c = z_z (pz_step pz 24) c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros c Hc. pose proof (cidx_rng c Hc) as Hi. unfold z_z at 1. rewrite zn_qnew.
  replace (Nat.eqb (6 + 2 * cidx c) 67) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c) 66) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c) 65) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qnew_j24 : z_j (qz_new pz sz) 24 = z_j pz 24 + 1.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). rewrite (qnew_j 24 ltac:(lia)). exact (step_j_same pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_j_other : forall c, 1 <= c <= 30 -> c <> 24 -> z_j (qz_new pz sz) c = z_j pz c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). intros c Hc Hne. rewrite (qnew_j c Hc). exact (step_j_other pz 24 Hlen ltac:(lia) c Hc Hne). Qed.
#[using="Hlen"] Lemma qnew_z24 : z_z (qz_new pz sz) 24 = 262144.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). rewrite (qnew_z 24 ltac:(lia)). exact (step_z_same pz 24 Hlen ltac:(lia)). Qed.
#[using="Hlen"] Lemma qnew_z_other : forall c, 1 <= c <= 30 -> c <> 24 -> z_z (qz_new pz sz) c = z_z pz c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). intros c Hc Hne. rewrite (qnew_z c Hc). exact (step_z_other pz 24 Hlen ltac:(lia) c Hc Hne). Qed.
(* [comment removed for export] *)
#[using="Hlen"] Lemma qnew_foot : z_z pz 24 = 262144 -> forall x, pri_foot_z (qz_new pz sz) x <-> pri_foot_z pz x.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros Z24 x. unfold pri_foot_z. rewrite qnew_ca, qnew_sb, qnew_sh.
  split; (intros [H|[H|[H|(c & Hc & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H | right; right; right; exists c; split; [exact Hc|]]).
  - destruct (Z.eq_dec c 24) as [->|Hne]; [rewrite qnew_z24 in H; rewrite Z24; exact H | rewrite (qnew_z_other c (in_cls_rng c Hc) Hne) in H; exact H].
  - destruct (Z.eq_dec c 24) as [->|Hne]; [rewrite qnew_z24; rewrite Z24 in H; exact H | rewrite (qnew_z_other c (in_cls_rng c Hc) Hne); exact H].
Qed.
End QNewZ.

Lemma INV_Az_qnew : forall pz m0 m0' sz, INV_Az pz m0 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) ->
  z_qn pz = 0 -> 1 <= z_j pz 24 -> z_j pz 24 + 1 + mc_tbl 24 / 2 <= 262144 / sz_tbl 24 ->
  q_inv m0' (z_ca pz - 128) (z_sb pz) (z_j pz 24) 1 (sz + 8192) ->
  INV_Co m0' (z_ca pz) (z_sb pz) 24 (sz_tbl 24) (mc_tbl 24 / 2) (262144 / sz_tbl 24) (z_j pz 24 + 1) ->
  POP_C m0' (z_sb pz) (z_sh pz) 24 (sz_tbl 24) (z_j pz 24 + 1) -> STATS m0' (z_ca pz) ->
  (forall x, z_ca pz - 128 <= x < z_ca pz - 96 -> wview SEGS m0' (wa x) <> None) ->
  (forall x, pri_foot_z pz x -> ~ owned_C (z_ca pz) (z_sb pz) 24 x -> ~ (z_ca pz - 128 <= x < z_ca pz - 96) -> ~ (BN pz <= x < BN pz + 8192) ->
     m0' (wa x) = m0 (wa x)) ->
  INV_Az (qz_new pz sz) m0'.
Proof.
  intros pz m0 m0' sz HI Hdisj Hqn0 Hj1 Hjb HQ HIo HPo HSt HW HF. destruct (q_seps pz m0 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof HI as HI0. destruct HI0 as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  destruct (cls_jb pz m0 HI 24 in_cls_24) as (J24 & J24b & _ & _).
  assert (Z24 : z_z pz 24 = 262144) by (destruct (Hcls 24 in_cls_24) as [(J0 & _)|(_ & Z1 & _)]; [clear - J0 Hj1; lia | exact Z1]).
  assert (Hj32 : z_j pz 24 + 1 <= 32) by (revert Hjb; change (262144 / sz_tbl 24) with 32; change (mc_tbl 24 / 2) with 1; clear; lia).
  unfold BN in HF.
  constructor; rewrite ?(qnew_sb pz sz Hlen), ?(qnew_sh pz sz Hlen), ?(qnew_ca pz sz Hlen), ?(qnew_pg pz sz Hlen), ?(qnew_tg pz sz Hlen),
    ?(qnew_qj pz sz Hlen), ?(qnew_qn pz sz Hlen), ?(qnew_qb pz sz Hlen), ?(qnew_gn pz sz Hlen), ?(qnew_gl pz sz Hlen), ?(qnew_gb pz sz Hlen); try assumption.
  - exact (qnew_len pz sz Hlen).
  - (* [comment removed for export] *)
    apply wr_bytes; [clear - B0; lia | clear - B0; lia |]. intros x Hx.
    destruct (Z_lt_le_dec x (z_ca pz - 96)) as [L0|L0]; [apply HW; clear - Hx L0; lia|].
    destruct (Z_lt_le_dec x (z_ca pz + 80 * 24)) as [L1|L1]; [|destruct (Z_lt_le_dec x (z_ca pz + 80 * 24 + 80)) as [L2|L2];
      [|destruct (Z_lt_le_dec x (z_ca pz + 2560)) as [L3|L3]]].
    + rewrite (wview_same m0 m0'); [exact (wr_byte m0 (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) Hwc ltac:(clear - Hx; lia))|].
      apply HF; [left; clear - Hx; lia | unfold owned_C; clear - Hx L1 T1 B0; lia | clear - L0; lia | clear - Hx T1 B0 J24 Hj32; lia].
    + destruct HIo as [_ _ _ _ _ _ _ _ _ W _]. exact (wr_byte m0' (z_ca pz + 80 * 24) 80 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) W ltac:(clear - L1 L2; lia)).
    + rewrite (wview_same m0 m0'); [exact (wr_byte m0 (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) Hwc ltac:(clear - Hx; lia))|].
      apply HF; [left; clear - Hx; lia | unfold owned_C; clear - Hx L2 L3 T1 B0; lia | clear - L0; lia | clear - Hx T1 B0 J24 Hj32; lia].
    + destruct HSt as (_ & _ & W). exact (wr_byte m0' (z_ca pz + 2560) 32 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) W ltac:(clear - L3 Hx; lia)).
  - (* [comment removed for export] *)
    split; [exact HQ|]. intros _. rewrite (qnew_j24 pz sz Hlen). clear. lia.
  - (* [comment removed for export] *)
    destruct Hgq as [Hg Hgl]. split; [|intros Hgn; rewrite (qnew_j24 pz sz Hlen); specialize (Hgl Hgn); clear - Hgl; lia].
    apply (gq_inv_o_frame m0 m0' (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) ltac:(clear - B0; lia) ltac:(clear - B0; lia)); [|exact Hg].
    intros x [Hx|(Hg1 & Hx)].
    + apply HF; [right; right; left; exact Hx | unfold owned_C; clear - Hx Hca B0; lia | clear - Hx Hca; lia | clear - Hx B0 J24; lia].
    + assert (Gl : 0 <= z_gl pz < 32) by (destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | exact G1]).
      specialize (Hgl Hg1).
      apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z24; clear - Hx Gl; lia | unfold owned_C; clear - Hx Gl T1 B0; lia |
                 clear - Hx Gl T1 B0; lia | clear - Hx Hgl; lia].
  - (* [comment removed for export] *)
    intros c Hc. pose proof (in_cls_rng c Hc) as Hcr.
    destruct (Z.eq_dec c 24) as [->|Hne].
    + rewrite (qnew_j24 pz sz Hlen), (qnew_z24 pz sz Hlen). right.
      split; [clear - J24; lia|]. split; [reflexivity|]. split; [clear - Hjb; lia|]. split; [exact HIo | exact HPo].
    + rewrite (qnew_j_other pz sz Hlen c Hcr Hne), (qnew_z_other pz sz Hlen c Hcr Hne).
      destruct (cls_jb pz m0 HI c Hc) as (K0 & _ & _ & Kz).
      apply (cls_inv_frame m0 m0' _ _ _ c _ _ Hc); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - S1; lia | clear - S1 B0; lia | exact K0 | | exact (Hcls c Hc)].
      intros x Hx. unfold cls_foot in Hx.
      assert (D : c <= 23 \/ 25 <= c) by (clear - Hne; lia).
      assert (Kz' : 0 <= z_z pz c <= 262144) by (clear - Kz; lia).
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
      * apply HF; [left; clear - Hx Hcr; lia | unfold owned_C; clear - Hx D T1 B0 Hcr; lia | clear - Hx Hcr; lia | clear - Hx T1 B0 J24 Hj32 Hcr; lia].
      * apply HF; [right; left; clear - Hx Hcr; lia | unfold owned_C; clear - Hx D T1 B0 Hcr; lia | clear - Hx T1 B0 Hcr; lia | clear - Hx Hj32 J24 Hcr; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; left; exact Hx | unfold owned_C; clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx Kz' D Hj32 J24 Hcr; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; right; left; exact Hx | unfold owned_C; clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx Kz' D Hj32 J24 Hcr; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; right; right; left; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr; lia | clear - Hx S1 S2 Hcr; lia | clear - Hx S1 B0 J24 Hj32 Hcr; lia].
      * apply HF; [right; right; right; exists c; split; [exact Hc|]; right; right; right; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr; lia | clear - Hx S1 S2 Hcr; lia | clear - Hx S1 B0 J24 Hj32 Hcr; lia].
Qed.

(* [comment removed for export] *)
Lemma ext_sem_qnew : forall pz m0 sz, INV_Az pz m0 -> forall b z, ext_sem pz b z -> ext_sem (qz_new pz sz) b z.
Proof.
  intros pz m0 sz HI b z ((c & Hc & H1 & H2 & H3) & _ & HG). pose proof (iz_len _ _ HI) as Hlen. pose proof (in_cls_rng c Hc) as Hcr.
  destruct (cls_jb pz m0 HI c Hc) as (K0 & K1 & _). destruct (cls_jb pz m0 HI 24 in_cls_24) as (J0 & J1 & _).
  destruct (cls_tbl c Hc) as (Hsz & _).
  split; [|split; [|rewrite (qnew_sb pz sz Hlen), (qnew_gn pz sz Hlen), (qnew_gl pz sz Hlen); exact HG]].
  - exists c. split; [exact Hc|]. rewrite (qnew_sb pz sz Hlen). split; [exact H1|]. split; [|exact H3].
    destruct (Z.eq_dec c 24) as [->|Hne]; [rewrite (qnew_j24 pz sz Hlen); clear - H2 Hsz; nia | rewrite (qnew_j_other pz sz Hlen c Hcr Hne); exact H2].
  - intros _. rewrite (qnew_sb pz sz Hlen), (qnew_qj pz sz Hlen).
    destruct (Z.eq_dec c 24) as [->|Hne]; [left; change (sz_tbl 24) with 8192 in H2; clear - H2; lia|].
    assert (D : c <= 23 \/ 25 <= c) by (clear - Hne; lia). change (sz_tbl 24) with 8192 in J1.
    destruct D as [D|D]; [left; clear - H2 K1 D J0; lia | right; clear - H1 D J1; lia].
Qed.

(* [comment removed for export] *)
Definition qz_drain (pz : list Z) : list Z :=
  set_nth 70 (z_gb pz + z_qb pz) (set_nth 69 (z_qj pz) (set_nth 68 (z_gn pz + 1) (set_nth 67 0 (set_nth 66 0 pz)))).
(* [comment removed for export] *)
Definition BG (pz : list Z) : Z := z_sb pz + 103079215104 + 8192 * z_gl pz.

Section QDrainZ.
Variable pz : list Z.
Hypothesis Hlen : List.length pz = PRI_LEN.

#[using="Hlen"] Lemma zn_qdrain : forall k, zn (qz_drain pz) k =
  if Nat.eqb k 70 then z_gb pz + z_qb pz else if Nat.eqb k 69 then z_qj pz else if Nat.eqb k 68 then z_gn pz + 1 else
  if Nat.eqb k 67 then 0 else if Nat.eqb k 66 then 0 else zn pz k.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros k. unfold zn, qz_drain.
  rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; lia). destruct (Nat.eqb k 70); [reflexivity|].
  rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; lia). destruct (Nat.eqb k 69); [reflexivity|].
  rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; lia). destruct (Nat.eqb k 68); [reflexivity|].
  rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; lia). destruct (Nat.eqb k 67); [reflexivity|].
  rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qdrain_len : List.length (qz_drain pz) = PRI_LEN.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold qz_drain. rewrite !set_nth_length. exact Hlen. Qed.
#[using="Hlen"] Lemma qdrain_sb : z_sb (qz_drain pz) = z_sb pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_sb. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_sh : z_sh (qz_drain pz) = z_sh pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_sh. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_ca : z_ca (qz_drain pz) = z_ca pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_ca. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_pg : z_pg (qz_drain pz) = z_pg pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_pg. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_tg : z_tg (qz_drain pz) = z_tg pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_tg. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_qj : z_qj (qz_drain pz) = z_qj pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qj. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_qn : z_qn (qz_drain pz) = 0. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qn. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_qb : z_qb (qz_drain pz) = 0. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_qb. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_gn : z_gn (qz_drain pz) = z_gn pz + 1. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gn. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_gl : z_gl (qz_drain pz) = z_qj pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gl. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_gb : z_gb (qz_drain pz) = z_gb pz + z_qb pz. Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold z_gb. rewrite zn_qdrain. reflexivity. Qed.
#[using="Hlen"] Lemma qdrain_j : forall c, 1 <= c <= 30 -> z_j (qz_drain pz) c = z_j pz c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros c Hc. pose proof (cidx_rng c Hc) as Hi. unfold z_j. rewrite zn_qdrain.
  replace (Nat.eqb (5 + 2 * cidx c) 70) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c) 69) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c) 68) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c) 67) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c) 66) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qdrain_z : forall c, 1 <= c <= 30 -> z_z (qz_drain pz) c = z_z pz c.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros c Hc. pose proof (cidx_rng c Hc) as Hi. unfold z_z. rewrite zn_qdrain.
  replace (Nat.eqb (6 + 2 * cidx c) 70) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c) 69) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c) 68) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c) 67) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c) 66) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma qdrain_foot : forall x, pri_foot_z (qz_drain pz) x <-> pri_foot_z pz x.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0).
  intros x. unfold pri_foot_z. rewrite qdrain_ca, qdrain_sb, qdrain_sh.
  split; (intros [H|[H|[H|(c & Hc & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H | right; right; right; exists c; split; [exact Hc|]]).
  - rewrite (qdrain_z c (in_cls_rng c Hc)) in H. exact H.
  - rewrite (qdrain_z c (in_cls_rng c Hc)). exact H.
Qed.
End QDrainZ.

(* [comment removed for export] *)
Lemma INV_Az_qdrain : forall pz m1 m2, INV_Az pz m1 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) ->
  1 <= z_qn pz ->
  q_inv m2 (z_ca pz - 128) (z_sb pz) (z_qj pz) 0 0 ->
  gq_inv_o m2 (z_sb pz) (z_gn pz + 1) (z_qj pz) (z_gb pz + z_qb pz) ->
  (forall x, z_ca pz - 128 <= x < z_ca pz - 96 -> wview SEGS m2 (wa x) <> None) ->
  (forall x, pri_foot_z pz x -> ~ (z_ca pz - 128 <= x < z_ca pz - 96) -> ~ (924360 <= x < 924400) ->
     ~ (1 <= z_gn pz /\ BG pz <= x < BG pz + 8) -> m2 (wa x) = m1 (wa x)) ->
  INV_Az (qz_drain pz) m2.
Proof.
  intros pz m1 m2 HI Hdisj Hqn1 HQ HGQ HW HF. destruct (q_seps pz m1 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof HI as HI0. destruct HI0 as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  destruct Hq as [Hq0 Hqj]. specialize (Hqj Hqn1). destruct Hgq as [Hg Hgl].
  assert (Hqj0 : 0 <= z_qj pz < 32) by (destruct Hq0 as (_ & _ & [(Q0 & _)|(_ & Q2 & _)]); [clear - Q0 Hqn1; lia | exact Q2]).
  assert (Gl : 1 <= z_gn pz -> 0 <= z_gl pz < 32).
  { intros Hg1. destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | exact G1]. }
  unfold BG in HF.
  constructor; rewrite ?(qdrain_sb pz Hlen), ?(qdrain_sh pz Hlen), ?(qdrain_ca pz Hlen), ?(qdrain_pg pz Hlen), ?(qdrain_tg pz Hlen),
    ?(qdrain_qj pz Hlen), ?(qdrain_qn pz Hlen), ?(qdrain_qb pz Hlen), ?(qdrain_gn pz Hlen), ?(qdrain_gl pz Hlen), ?(qdrain_gb pz Hlen); try assumption.
  - exact (qdrain_len pz Hlen).
  - (* [comment removed for export] *)
    apply (STATS_frame m1); [clear - B0; lia | clear - B0; lia | | exact Hst].
    intros x Hx. apply HF; [left; clear - Hx; lia | clear - Hx; lia | clear - Hx Hca; lia |].
    intros (Hg1 & Hc0). specialize (Gl Hg1). clear - Hx Hc0 Gl T1 B0. lia.
  - (* [comment removed for export] *)
    apply wr_bytes; [clear - B0; lia | clear - B0; lia |]. intros x Hx.
    destruct (Z_lt_le_dec x (z_ca pz - 96)) as [L0|L0]; [apply HW; clear - Hx L0; lia|].
    rewrite (wview_same m1 m2); [exact (wr_byte m1 (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) Hwc ltac:(clear - Hx; lia))|].
    apply HF; [left; clear - Hx; lia | clear - L0; lia | clear - Hx Hca; lia |].
    intros (Hg1 & Hc0). specialize (Gl Hg1). clear - Hx Hc0 Gl T1 B0. lia.
  - (* [comment removed for export] *)
    split; [exact HQ|]. intros Hc0. exfalso. clear - Hc0. lia.
  - (* [comment removed for export] *)
    split; [exact HGQ|]. intros _. rewrite (qdrain_j pz Hlen 24 ltac:(lia)). exact Hqj.
  - (* [comment removed for export] *)
    intros c Hc. pose proof (in_cls_rng c Hc) as Hcr. rewrite (qdrain_j pz Hlen c Hcr), (qdrain_z pz Hlen c Hcr).
    destruct (cls_jb pz m1 HI c Hc) as (K0 & K1 & K2 & Kz).
    assert (Kz' : 0 <= z_z pz c <= 262144) by (clear - Kz; lia).
    assert (HFc : forall x, pri_foot_z pz x -> ~ (z_ca pz - 128 <= x < z_ca pz - 96) -> ~ (924360 <= x < 924400) ->
              (forall g, 0 <= g < 32 -> g < z_j pz 24 -> ~ (z_sb pz + 103079215104 + 8192 * g <= x < z_sb pz + 103079215104 + 8192 * g + 8)) -> m2 (wa x) = m1 (wa x)).
    { intros x F1 N1 N2 N3. apply HF; [exact F1 | exact N1 | exact N2|]. intros (Hg1 & Hc0). exact (N3 (z_gl pz) (Gl Hg1) (Hgl Hg1) Hc0). }
    destruct (Z.eq_dec c 24) as [->|Hne].
    + destruct (Hcls 24 in_cls_24) as [(J0 & _)|(J1 & Z1 & Jb & HIo & HPo)]; [clear - J0 Hqj Hqj0; lia|]. right.
      split; [exact J1|]. split; [exact Z1|]. split; [exact Jb|]. split.
      * apply (INV_Co_frame m1); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | | exact HIo].
        intros x Hx. unfold foot_Co in Hx. change (sz_tbl 24) with 8192 in Hx. change (262144 / 8192) with 32 in Hx.
        destruct Hx as [Hx|[Hx|Hx]].
        -- apply HFc; [left; clear - Hx; lia | clear - Hx; lia | clear - Hx Hca; lia | intros g G0 G1; clear - Hx G0 T1 B0; lia].
        -- apply HFc; [right; left; clear - Hx; lia | clear - Hx T1 B0; lia | clear - Hx B0; lia | intros g G0 G1; clear - Hx G0; lia].
        -- apply HFc; [right; right; right; exists 24; split; [exact in_cls_24|]; right; left; rewrite Z1; clear - Hx; lia | clear - Hx T1 B0; lia | clear - Hx B0; lia |
                        intros g G0 G1; clear - Hx G0; lia].
      * apply (POP_C_frame m1); [| change (sz_tbl 24 / 8) with 1024; clear - J1; lia | exact HPo]. intros x Hx. unfold RBX, SHX in Hx. change (sz_tbl 24) with 8192 in Hx. change (8192 / 8) with 1024 in Hx.
        destruct Hx as [Hx|Hx].
        -- apply HFc; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z1; clear - Hx J1; lia | clear - Hx T1 B0 J1; lia | clear - Hx B0 J1; lia |
                        intros g G0 G1; clear - Hx G1; lia].
        -- apply HFc; [right; right; right; exists 24; split; [exact in_cls_24|]; right; right; left; clear - Hx J1; lia | clear - Hx S1 S2 J1; lia | clear - Hx S1 J1; lia |
                        intros g G0 G1; clear - Hx S1 B0 J1 G0; lia].
    + apply (cls_inv_frame m1 m2 _ _ _ c _ _ Hc); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - S1; lia | clear - S1 B0; lia | exact K0 | | exact (Hcls c Hc)].
      intros x Hx. unfold cls_foot in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
      * apply HFc; [left; clear - Hx Hcr; lia | clear - Hx Hcr; lia | clear - Hx Hca Hcr; lia | intros g G0 G1; clear - Hx G0 T1 B0 Hcr; lia].
      * apply HFc; [right; left; clear - Hx Hcr; lia | clear - Hx T1 B0 Hcr; lia | clear - Hx B0 Hcr; lia | intros g G0 G1; clear - Hx G0 Hcr; lia].
      * apply HFc; [right; right; right; exists c; split; [exact Hc|]; left; exact Hx | clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx B0 Hcr; lia | intros g G0 G1; clear - Hx Kz' G0 Hcr Hne; lia].
      * apply HFc; [right; right; right; exists c; split; [exact Hc|]; right; left; exact Hx | clear - Hx Kz' T1 B0 Hcr; lia | clear - Hx B0 Hcr; lia | intros g G0 G1; clear - Hx Kz' G0 Hcr Hne; lia].
      * apply HFc; [right; right; right; exists c; split; [exact Hc|]; right; right; left; exact Hx | clear - Hx S1 S2 Hcr; lia | clear - Hx S1 Hcr; lia | intros g G0 G1; clear - Hx S1 B0 G0 Hcr; lia].
      * apply HFc; [right; right; right; exists c; split; [exact Hc|]; right; right; right; exact Hx | clear - Hx S1 S2 Hcr; lia | clear - Hx S1 Hcr; lia | intros g G0 G1; clear - Hx S1 B0 G0 Hcr; lia].
Qed.

(* [comment removed for export] *)
Lemma ext_sem_qdrain : forall pz, List.length pz = PRI_LEN -> 1 <= z_qn pz -> forall b z, ext_sem pz b z -> ext_sem (qz_drain pz) b z.
Proof.
  intros pz Hlen Hqn1 b z ((c & Hc & H1 & H2 & H3) & HB & _). split; [|split].
  - exists c. split; [exact Hc|]. rewrite (qdrain_sb pz Hlen), (qdrain_j pz Hlen c (in_cls_rng c Hc)). split; [exact H1|]. split; [exact H2 | exact H3].
  - rewrite (qdrain_qn pz Hlen). intros Hc0. exfalso. clear - Hc0. lia.
  - intros _. rewrite (qdrain_sb pz Hlen), (qdrain_gl pz Hlen). exact (HB Hqn1).
Qed.

(* [comment removed for export] *)
Lemma gq_fp : forall pz m0, INV_Az pz m0 -> forall x, 924360 <= x < 924400 -> pri_foot_z pz x /\ FPmax pz x /\ ~ alloc_part pz x /\ 0 <= x < 2^47.
Proof.
  intros pz m0 HI x Hx. pose proof (az_geo pz m0 HI) as G.
  split; [right; right; left; exact Hx|]. split; [right; right; right; exact Hx|]. split; [|clear - Hx; lia].
  intros (c' & Hc' & Ha). pose proof (in_cls_rng c' Hc') as Hcr'. destruct (cls_jb pz m0 HI c' Hc') as (J0 & J1 & J2 & _).
  destruct Ha as [Ha|Ha]; clear - Ha Hx G Hcr' J0 J1 J2; lia.
Qed.
(* [comment removed for export] *)
Lemma bg_fp : forall pz m0, INV_Az pz m0 -> 1 <= z_gn pz -> forall x, BG pz <= x < BG pz + 8192 -> pri_foot_z pz x /\ FPmax pz x /\ 0 <= x < 2^47.
Proof.
  intros pz m0 HI Hgn x Hx. pose proof (az_geo pz m0 HI) as G. destruct HI as [_ _ _ _ _ _ _ _ _ _ Hgq Hcls]. destruct Hgq as [Hg Hgl]. specialize (Hgl Hgn).
  assert (Gl : 0 <= z_gl pz < 32) by (destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hgn; lia | exact G1]).
  assert (Z24 : z_z pz 24 = 262144) by (destruct (Hcls 24 in_cls_24) as [(J0 & _)|(_ & Z1 & _)]; [clear - J0 Hgl Gl; lia | exact Z1]).
  unfold BG in Hx.
  split; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z24; clear - Hx Gl; lia|].
  split; [left; unfold PG_SIZE; clear - Hx Gl G; lia | clear - Hx Gl G; lia].
Qed.
