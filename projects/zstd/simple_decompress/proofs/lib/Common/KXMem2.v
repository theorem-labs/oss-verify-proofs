(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXMem.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition elit_w (w : nat) : expr := ELit (Z.of_nat w).

Lemma elen_lit_w : forall E w, (w <= 8)%nat -> elenZ E (elit_w w) = Z.of_nat w.
Proof.
  intros E w Hw. unfold elenZ, elit_w. cbn [edenot]. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
Qed.

Definition log_apart_b (kn : list kentry) (log : list sentry) (ca : saddr) (cn : expr) : bool :=
  forallb (fun e => ranges_apart_x kn (a_base (e_addr e)) (a_off (e_addr e)) (elit_w (e_width e)) (a_base ca) (a_off ca) cn) log.

Definition log_inside_b (kn : list kentry) (log : list sentry) (ws : list (saddr * expr)) : bool :=
  forallb (fun e => existsb (fun w : saddr * expr =>
                      xinside kn (a_base (e_addr e)) (a_off (e_addr e)) (elit_w (e_width e)) (a_base (fst w)) (a_off (fst w)) (snd w)) ws) log.

(* [comment removed for export] *)
Fixpoint log_class (kn : list kentry) (ca : saddr) (size : Z) (log : list sentry) : option (list (option Z)) :=
  match log with
  | [] => Some []
  | SE a w v :: rest =>
      match log_class kn ca size rest with
      | None => None
      | Some cl =>
          if (expr_eqb (a_base a) (a_base ca) && Z.leb (a_off ca) (a_off a) && Z.leb (a_off a + Z.of_nat w) (a_off ca + size))%bool
          then Some (Some (a_off a - a_off ca) :: cl)
          else if ranges_apart_x kn (a_base a) (a_off a) (elit_w w) (a_base ca) (a_off ca) (ELit size) then Some (None :: cl)
          else None
      end
  end.

(* [comment removed for export] *)
Fixpoint cells_hits (E : env) (cs : list cell) (log : list sentry) (cl : list (option Z)) : option (list cell) :=
  match log, cl with
  | [], [] => Some cs
  | SE a w v :: rest, c :: cl' =>
      match cells_hits E cs rest cl' with
      | None => None
      | Some cs1 =>
          match c with
          | Some k => cells_store cs1 (Z.to_nat k) (kx_cell w (edenot E v))
          | None => Some cs1
          end
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition log_u8_b (kn : list kentry) (log : list sentry) (ca : saddr) (cn : expr) : bool :=
  forallb (fun e =>
     xinside kn (a_base (e_addr e)) (a_off (e_addr e)) (elit_w (e_width e)) (a_base ca) (a_off ca) cn
     || ranges_apart_x kn (a_base (e_addr e)) (a_off (e_addr e)) (elit_w (e_width e)) (a_base ca) (a_off ca) cn) log.

(* [comment removed for export] *)
Section M2P.
Variable segs : list Segment.
Variable E : env.
Variable m : word -> option byte.

Lemma kx_cells_at_apartP : forall log A cs, log_flat E log -> log_apart E log A (Z.of_nat (cells_size cs)) ->
  cells_at segs m A cs -> cells_at segs (mem_denot E m log) A cs.
Proof.
  intros log A cs Hlf Hap [Hwf H]. split; [exact Hwf|]. apply kx_bytes_at_log; [exact Hlf| |exact H].
  rewrite (cells_bytes_length cs Hwf). exact Hap.
Qed.
Lemma kx_rw_cells_apartP : forall log A cs, log_flat E log -> log_apart E log A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m A cs -> rw_cells segs (mem_denot E m log) A cs.
Proof. intros log A cs Hlf Hap [Hc Hw]. split; [exact (kx_cells_at_apartP log A cs Hlf Hap Hc) | apply kx_wr_at_log; exact Hw]. Qed.
Lemma kx_ro_cells_apartP : forall log A cs, log_flat E log -> log_apart E log A (Z.of_nat (cells_size cs)) ->
  ro_cells segs m A cs -> ro_cells segs (mem_denot E m log) A cs.
Proof. intros log A cs Hlf Hap H. exact (kx_cells_at_apartP log A cs Hlf Hap H). Qed.
Lemma kx_u8arr_apartP : forall log A bs, log_flat E log -> log_apart E log A (Z.of_nat (length bs)) ->
  u8arr segs m A bs -> u8arr segs (mem_denot E m log) A bs.
Proof. intros log A bs Hlf Hap [H Hw]. split; [apply kx_bytes_at_log; assumption | apply kx_wr_at_log; exact Hw]. Qed.

(* [comment removed for export] *)
Fixpoint log_u8P (log : list sentry) (A N : Z) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      ((A <= estart E a /\ estart E a + Z.of_nat w <= A + N) \/ (A + N <= estart E a \/ estart E a + Z.of_nat w <= A))
      /\ log_u8P rest A N
  end.

Lemma kx_u8arr_logP : forall log A bs, log_flat E log -> log_u8P log A (Z.of_nat (length bs)) ->
  u8arr segs m A bs -> exists bs', u8arr segs (mem_denot E m log) A bs' /\ length bs' = length bs.
Proof.
  intros log A bs. induction log as [|[a w v] rest IH]; intros Hlf Hb H.
  - exists bs. split; [exact H | reflexivity].
  - cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & (F1 & F2 & F3 & F4) & Hlf).
    cbn [log_u8P] in Hb. destruct Hb as [Hb1 Hb2].
    destruct (IH Hlf Hb2 H) as (bs1 & H1 & L1).
    rewrite mem_denot_cons. unfold kx_sbytes.
    assert (LB : length (word_to_le_bytes w (edenot E v)) = w) by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
    destruct Hb1 as [[X1 X2]|Ap].
    + destruct (kx_u8arr_store segs _ A bs1 (estart E a) _ H1 ltac:(rewrite LB, L1; lia)) as (bs2 & H2 & L2).
      exists bs2. split; [exact H2 | congruence].
    + exists bs1. split; [|exact L1]. apply u8arr_frame; [exact H1 | lia | rewrite LB; lia | rewrite LB, L1; lia].
Qed.

End M2P.

Section M2.
Variable segs : list Segment.
Variable E : env.
Variable m : word -> option byte.
Variable kn : list kentry.
Hypothesis HK : know_ok segs E m kn.

Lemma sa_eta2 : forall a : saddr, SA (a_base a) (a_off a) = a.
Proof. intros [b k]. reflexivity. Qed.

Lemma log_apart_b_sound : forall log ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  log_apart E log (estart E ca) (elenZ E cn).
Proof.
  intros log ca cn. induction log as [|[a w v] rest IH]; cbn [log_flat log_apart log_apart_b forallb]; intros Hlf Hb; [exact I|].
  destruct Hlf as (Hw8 & _ & Hlf). apply andb_prop in Hb as [Hb1 Hb2]. cbn [e_addr e_width] in Hb1.
  split; [|exact (IH Hlf Hb2)].
  pose proof (ranges_apart_x_sound segs E m kn _ _ _ _ _ _ HK Hb1) as A. rewrite !sa_eta2, (elen_lit_w E w Hw8) in A. lia.
Qed.

(* [comment removed for export] *)
Lemma kx_bytes_at_apart : forall log A bs ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = Z.of_nat (length bs) ->
  bytes_at segs m A bs -> bytes_at segs (mem_denot E m log) A bs.
Proof.
  intros log A bs ca cn Hlf Hb EA EN H. apply kx_bytes_at_log; [exact Hlf| |exact H].
  rewrite <- EA, <- EN. exact (log_apart_b_sound log ca cn Hlf Hb).
Qed.

Lemma kx_cells_at_apart : forall log A cs ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = Z.of_nat (cells_size cs) ->
  cells_at segs m A cs -> cells_at segs (mem_denot E m log) A cs.
Proof.
  intros log A cs ca cn Hlf Hb EA EN [Hwf H]. split; [exact Hwf|].
  apply (kx_bytes_at_apart log A _ ca cn Hlf Hb EA); [|exact H]. rewrite EN, (cells_bytes_length cs Hwf). reflexivity.
Qed.

Lemma kx_rw_cells_apart : forall log A cs ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = Z.of_nat (cells_size cs) ->
  rw_cells segs m A cs -> rw_cells segs (mem_denot E m log) A cs.
Proof.
  intros log A cs ca cn Hlf Hb EA EN [Hc Hw]. split; [exact (kx_cells_at_apart log A cs ca cn Hlf Hb EA EN Hc)|].
  apply kx_wr_at_log. exact Hw.
Qed.

Lemma kx_ro_cells_apart : forall log A cs ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = Z.of_nat (cells_size cs) ->
  ro_cells segs m A cs -> ro_cells segs (mem_denot E m log) A cs.
Proof. intros log A cs ca cn Hlf Hb EA EN H. exact (kx_cells_at_apart log A cs ca cn Hlf Hb EA EN H). Qed.

Lemma kx_u8arr_apart : forall log A bs ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = Z.of_nat (length bs) ->
  u8arr segs m A bs -> u8arr segs (mem_denot E m log) A bs.
Proof.
  intros log A bs ca cn Hlf Hb EA EN [H Hw]. split; [exact (kx_bytes_at_apart log A bs ca cn Hlf Hb EA EN H)|].
  apply kx_wr_at_log. exact Hw.
Qed.

Lemma kx_u32arr_apart : forall log A ws ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = 4 * Z.of_nat (length ws) ->
  u32arr segs m A ws -> u32arr segs (mem_denot E m log) A ws.
Proof.
  intros log A ws ca cn Hlf Hb EA EN [H Hw]. split; [|apply kx_wr_at_log; exact Hw].
  apply (kx_bytes_at_apart log A _ ca cn Hlf Hb EA); [|exact H]. rewrite EN, u32s_length. lia.
Qed.

Lemma kx_u64arr_apart : forall log A ws ca cn, log_flat E log -> log_apart_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = 8 * Z.of_nat (length ws) ->
  u64arr segs m A ws -> u64arr segs (mem_denot E m log) A ws.
Proof.
  intros log A ws ca cn Hlf Hb EA EN [H Hw]. split; [|apply kx_wr_at_log; exact Hw].
  apply (kx_bytes_at_apart log A _ ca cn Hlf Hb EA); [|exact H]. rewrite EN, u64s_length. lia.
Qed.

(* [comment removed for export] *)
Lemma kx_rw_cells_log : forall log cl A cs cs' ca,
  log_flat E log -> estart E ca = A -> Z.of_nat (cells_size cs) < 2^64 ->
  log_class kn ca (Z.of_nat (cells_size cs)) log = Some cl -> cells_hits E cs log cl = Some cs' ->
  rw_cells segs m A cs -> rw_cells segs (mem_denot E m log) A cs' /\ cells_size cs' = cells_size cs.
Proof.
  intros log. induction log as [|[a w v] rest IH]; intros cl A cs cs' ca Hlf EA HSZ Hcl Hh H.
  - cbn [log_class] in Hcl. injection Hcl as <-. cbn [cells_hits] in Hh. injection Hh as <-. split; [exact H | reflexivity].
  - cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & (F1 & F2 & F3 & F4) & Hlf).
    cbn [log_class] in Hcl. destruct (log_class kn ca (Z.of_nat (cells_size cs)) rest) as [cl0|] eqn:Hc0; [|discriminate Hcl].
    destruct (expr_eqb (a_base a) (a_base ca) && Z.leb (a_off ca) (a_off a) && Z.leb (a_off a + Z.of_nat w) (a_off ca + Z.of_nat (cells_size cs)))%bool eqn:Hin.
    + injection Hcl as <-. cbn [cells_hits] in Hh.
      destruct (cells_hits E cs rest cl0) as [cs1|] eqn:Hh1; [|discriminate Hh].
      destruct (IH cl0 A cs cs1 ca Hlf EA HSZ Hc0 Hh1 H) as [H1 Hs1].
      apply andb_prop in Hin as [Hin Hhi]. apply andb_prop in Hin as [Hbase Hlo].
      apply expr_eqb_eq in Hbase. apply Z.leb_le in Hlo, Hhi.
      assert (EQ : estart E a = A + (a_off a - a_off ca)) by (rewrite <- EA; unfold estart; rewrite Hbase; lia).
      rewrite mem_denot_cons. unfold kx_sbytes.
      rewrite EQ, <- kx_cell_bytes.
      pose proof (kx_rw_cells_storeZ segs _ A cs1 (a_off a - a_off ca) _ cs' H1 Hh (kx_cell_wf _ _) ltac:(lia)) as H2.
      split; [exact H2|].
      (* [comment removed for export] *)
      unfold cells_store in Hh. destruct (cb_split_ok cs1 _ _) eqn:Hok; [|discriminate Hh].
      destruct (cell_at _ _) as [c|] eqn:Hc; [|discriminate Hh]. destruct (Nat.eqb (csize c) _) eqn:Hsz; [|discriminate Hh].
      injection Hh as <-. apply Nat.eqb_eq in Hsz.
      pose proof (rw_cells_cb_split segs _ A cs1 _ _ _ H1 Hok eq_refl) as H3.
      destruct (cell_at_split _ _ c (kx_cell w (edenot E v)) Hc) as (pre & post & Ecs & Hpre & ->).
      rewrite <- Hs1, <- (cells_size_cb_split cs1 _ _ (cells_at_wf _ _ _ _ (proj1 H1)) Hok), Ecs, !cells_size_app. cbn [cells_size]. lia.
    + destruct (ranges_apart_x kn (a_base a) (a_off a) (elit_w w) (a_base ca) (a_off ca) (ELit (Z.of_nat (cells_size cs)))) eqn:Hap; [|discriminate Hcl].
      injection Hcl as <-. cbn [cells_hits] in Hh.
      destruct (cells_hits E cs rest cl0) as [cs1|] eqn:Hh1; [|discriminate Hh]. injection Hh as <-.
      destruct (IH cl0 A cs cs1 ca Hlf EA HSZ Hc0 Hh1 H) as [H1 Hs1]. split; [|exact Hs1].
      pose proof (ranges_apart_x_sound segs E m kn _ _ _ _ _ _ HK Hap) as Ap. rewrite !sa_eta2, (elen_lit_w E w Hw8), EA in Ap.
      assert (EL : elenZ E (ELit (Z.of_nat (cells_size cs))) = Z.of_nat (cells_size cs)).
      { unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
        unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia. }
      rewrite EL, <- Hs1 in Ap.
      rewrite mem_denot_cons. unfold kx_sbytes.
      apply rw_cells_frame; [exact H1 | lia | unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; lia
                            | unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; lia].
Qed.

(* [comment removed for export] *)
Lemma kx_u8arr_log : forall log A bs ca cn, log_flat E log -> log_u8_b kn log ca cn = true ->
  estart E ca = A -> elenZ E cn = Z.of_nat (length bs) ->
  u8arr segs m A bs -> exists bs', u8arr segs (mem_denot E m log) A bs' /\ length bs' = length bs.
Proof.
  intros log A bs ca cn. induction log as [|[a w v] rest IH]; intros Hlf Hb EA EN H.
  - exists bs. split; [exact H | reflexivity].
  - cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & (F1 & F2 & F3 & F4) & Hlf).
    cbn [log_u8_b forallb e_addr e_width] in Hb. apply andb_prop in Hb as [Hb1 Hb2].
    destruct (IH Hlf Hb2 EA EN H) as (bs1 & H1 & L1).
    rewrite mem_denot_cons. unfold kx_sbytes.
    assert (LB : length (word_to_le_bytes w (edenot E v)) = w) by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
    apply orb_prop in Hb1 as [Hin|Hap].
    + pose proof (xinside_sound segs E m kn _ _ _ _ _ _ HK Hin) as [X1 X2]. rewrite !sa_eta2, (elen_lit_w E w Hw8), EA, EN in *.
      destruct (kx_u8arr_store segs _ A bs1 (estart E a) _ H1 ltac:(rewrite LB, L1; lia)) as (bs2 & H2 & L2).
      exists bs2. split; [exact H2 | congruence].
    + pose proof (ranges_apart_x_sound segs E m kn _ _ _ _ _ _ HK Hap) as Ap. rewrite !sa_eta2, (elen_lit_w E w Hw8), EA, EN in Ap.
      exists bs1. split; [|exact L1]. apply u8arr_frame; [exact H1 | lia | rewrite LB; lia | rewrite LB, L1; lia].
Qed.

(* [comment removed for export] *)
Definition win_ok (W : list ivl) (w : saddr * expr) : Prop :=
  exists lo hi, In (lo, hi) W /\ estart E (fst w) = lo /\ estart E (fst w) + elenZ E (snd w) = hi.

Lemma inside_In : forall W lo hi a n, In (lo, hi) W -> lo <= a -> a + n <= hi -> inside W a n.
Proof.
  induction W as [|[l h] W IH]; intros lo hi a n Hin H1 H2; [destruct Hin|].
  cbn [inside]. destruct Hin as [Heq|Hin]; [injection Heq as -> ->; left; lia | right; eapply IH; eassumption].
Qed.

Lemma kx_munch_logb : forall log W ws m0, log_flat E log -> Forall (win_ok W) ws -> log_inside_b kn log ws = true ->
  munch W m0 m -> munch W m0 (mem_denot E m log).
Proof.
  intros log W ws m0 Hlf Hws Hb Hm. apply kx_munch_log; [exact Hlf| |exact Hm].
  clear Hm. induction log as [|[a w v] rest IH]; cbn [log_inside]; [exact I|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & _ & Hlf).
  cbn [log_inside_b forallb e_addr e_width] in Hb. apply andb_prop in Hb as [Hb1 Hb2].
  split; [|exact (IH Hlf Hb2)].
  apply existsb_exists in Hb1 as ([wa0 wn] & Hin & Hx). cbn [fst snd] in Hx.
  pose proof (xinside_sound segs E m kn _ _ _ _ _ _ HK Hx) as [X1 X2]. rewrite !sa_eta2, (elen_lit_w E w Hw8) in *.
  rewrite Forall_forall in Hws. destruct (Hws _ Hin) as (lo & hi & HinW & E1 & E2). cbn [fst snd] in E1, E2.
  eapply inside_In; [exact HinW | lia | lia].
Qed.

End M2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint evars_only (j : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => Nat.eqb v j
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_only j a && evars_only j b
  | EExt _ _ _ a => evars_only j a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_only : forall j E E' e, evars_only j e = true -> ev E j = ev E' j -> edenot E e = edenot E' e.
Proof.
  intros j E E' e H Hj. induction e; cbn [evars_only edenot] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity).
  - apply Nat.eqb_eq in H. subst. exact Hj.
  - rewrite (IHe H). reflexivity.
  - discriminate H.
Qed.

Definition kx_cenv (w : word) : env := Env (fun _ => w) nob.
Definition enum_chk (e : expr) (lo : Z) (cnt : nat) (P : Z -> bool) : bool :=
  forallb (fun k => P (bv_unsigned (edenot (kx_cenv (Z_to_bv 64 (lo + Z.of_nat k))) e))) (seq 0 cnt).

Lemma kx_enum_ok : forall E e j lo cnt P, evars_only j e = true -> enum_chk e lo cnt P = true ->
  lo <= bv_unsigned (ev E j) < lo + Z.of_nat cnt -> P (bv_unsigned (edenot E e)) = true.
Proof.
  intros E e j lo cnt P Ho Hc Hr. unfold enum_chk in Hc. rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat (bv_unsigned (ev E j) - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hc by lia. replace (lo + (bv_unsigned (ev E j) - lo)) with (bv_unsigned (ev E j)) in Hc by lia.
  rewrite Z_to_bv_bv_unsigned in Hc.
  rewrite (edenot_only j E (kx_cenv (ev E j)) e Ho eq_refl). exact Hc.
Qed.
