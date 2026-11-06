(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Strings.String Strings.Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ZBridge MState.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodesCfg TrzStdioCfg SpecT.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model RDrv_B RDrv_C RDrv_run RDrv_D RDrv_E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_alt2_cong : forall A A' B B', t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). tauto. Qed.

Lemma t_alt2_idem : forall A B, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

Lemma t_emit_nil_l_eq : forall T, T [] -> t_eq (ShapeAlg.t_emit [] T) T.
Proof. intros T HT. apply t_emit_nil_eq. exact HT. Qed.

Lemma t_exit_nil : forall c fs, t_exit c fs []. Proof. intros. apply ShapeAlg.t_emit_has_nil. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.

Lemma to_bytes_str : forall s, to_bytes (str s) = s2b s.
Proof.
  intros s. unfold to_bytes, str, s2b. rewrite map_map. apply map_ext. intros a.
  unfold nat_of_ascii. rewrite N_nat_Z. reflexivity.
Qed.

Lemma to_bytes_unsigned : forall l : list byte, to_bytes (map bv_unsigned l) = l.
Proof.
  intros l. unfold to_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH, (definitions.Z_to_bv_bv_unsigned 8 b). reflexivity.
Qed.

Lemma Wz_W : forall ch zs, Wz ch zs = W ch (to_bytes zs).
Proof. reflexivity. Qed.

Lemma bv_and_255_small : forall z, 0 <= z < 256 -> bv_and (Z_to_bv 64 z) (Z_to_bv 64 255) = Z_to_bv 64 z.
Proof.
  intros z Hz. apply bv_eq. rewrite bv_and_unsigned. rewrite !unsigned_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fs.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Variable fs : Fs.Fs.

Lemma TEXIT2_init : t_eq (TEXIT2 stdout_init fs) (t_exit (exit_code 2) fs).
Proof.
  unfold TEXIT2, exit_code. cbn [exit_flush_pure stdout_init so_buf zlength length Z.of_nat Z.ltb fst Wz to_bytes map].
  rewrite bv_and_255_small by lia. apply t_emit_nil_l_eq. apply t_exit_nil.
Qed.

Lemma TDIE_die : forall ps msg, to_bytes (concat ps) = msg -> t_eq (TDIE ps stdout_init fs) (t_die msg fs).
Proof.
  intros ps msg E. unfold TDIE, t_die. rewrite Wz_W, E. apply t_eq_emit. apply TEXIT2_init.
Qed.

Lemma concat5 : forall (a b c d e : list Z), concat [a; b; c; d; e] = a ++ b ++ c ++ d ++ e.
Proof. intros. cbn [concat]. rewrite app_nil_r. reflexivity. Qed.
Lemma concat1 : forall (a : list Z), concat [a] = a.
Proof. intros. cbn [concat]. apply app_nil_r. Qed.

Lemma die_usage : forall a0, t_eq (TDIE (pieces_usage (map bv_unsigned a0)) stdout_init fs) (t_die (msg_usage a0) fs).
Proof.
  intros a0. apply TDIE_die. unfold pieces_usage, msg_usage. rewrite concat5. cbn [app].
  rewrite !to_bytes_app, !to_bytes_str, to_bytes_unsigned. reflexivity.
Qed.
Lemma die_cannot_open : forall p, t_eq (TDIE (pieces_cannot_open (map bv_unsigned p)) stdout_init fs) (t_die (msg_cannot_open p) fs).
Proof.
  intros p. apply TDIE_die. unfold pieces_cannot_open, msg_cannot_open. rewrite concat5. cbn [app].
  rewrite !to_bytes_app, !to_bytes_str, to_bytes_unsigned. reflexivity.
Qed.
Lemma die_read_error : forall p, t_eq (TDIE (pieces_read_error (map bv_unsigned p)) stdout_init fs) (t_die (msg_read_error p) fs).
Proof.
  intros p. apply TDIE_die. unfold pieces_read_error, msg_read_error. rewrite concat5. cbn [app].
  rewrite !to_bytes_app, !to_bytes_str, to_bytes_unsigned. reflexivity.
Qed.
Lemma die_short : t_eq (TDIE pieces_short_hdr stdout_init fs) (t_die msg_short fs).
Proof. apply TDIE_die. unfold pieces_short_hdr, msg_short. rewrite concat1, to_bytes_app, to_bytes_str. reflexivity. Qed.
Lemma die_overrun : t_eq (TDIE pieces_cfg_overrun stdout_init fs) (t_die msg_overrun fs).
Proof. apply TDIE_die. unfold pieces_cfg_overrun, msg_overrun. rewrite concat1, to_bytes_app, to_bytes_str. reflexivity. Qed.
Lemma die_refused : t_eq (TDIE pieces_too_big stdout_init fs) (t_die msg_refused fs).
Proof. apply TDIE_die. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma towrite_active : forall so, so_active so = true -> towrite_pure so = so.
Proof. intros so H. unfold towrite_pure. rewrite H. reflexivity. Qed.

Lemma emits_bytes_active : forall n so, so_active so = true ->
  fst (emits n so) ++ so_buf (snd (emits n so)) = so_buf so ++ concat (repeat (concat (pieces_emit_d 0)) n)
  /\ so_active (snd (emits n so)) = true.
Proof.
  induction n as [|n IH]; intros so Ha.
  - cbn [emits fst snd repeat concat]. rewrite app_nil_r. auto.
  - rewrite (proj1 (emits_S n so)), (proj2 (emits_S n so)).
    unfold vprintf_pure. rewrite (towrite_active so Ha).
    destruct (pieces_pure_bytes (pieces_emit_d 0) so Ha) as [E1 A1].
    destruct (IH _ A1) as [E2 A2]. split; [| exact A2].
    rewrite <- app_assoc, E2, app_assoc, E1, <- app_assoc. cbn [repeat concat]. reflexivity.
Qed.

Lemma exit_flush_bytes : forall so, fst (exit_flush_pure so) = so_buf so.
Proof.
  intros so. unfold exit_flush_pure. destruct (Z.ltb_spec 0 (zlength (so_buf so))).
  - rewrite writefn_pure_fst. unfold ioctl_pure. destruct (so_first so); cbn [so_buf]; apply app_nil_r.
  - cbn [fst]. unfold zlength in *. destruct (so_buf so); [reflexivity | cbn [length] in *; lia].
Qed.

Lemma emits_total : forall n,
  fst (emits n stdout_init) ++ fst (exit_flush_pure (snd (emits n stdout_init))) = concat (repeat [48; 10] n).
Proof.
  intros n. rewrite exit_flush_bytes. destruct n as [|n]; [reflexivity|].
  rewrite (proj1 (emits_S n stdout_init)), (proj2 (emits_S n stdout_init)).
  unfold vprintf_pure. set (so1 := towrite_pure stdout_init).
  assert (A1 : so_active so1 = true) by reflexivity.
  destruct (pieces_pure_bytes (pieces_emit_d 0) so1 A1) as [E1 A2].
  destruct (emits_bytes_active n _ A2) as [E2 _].
  rewrite <- app_assoc, E2, app_assoc, E1. reflexivity.
Qed.

Lemma to_bytes_zero_lines : forall n, to_bytes (concat (repeat [48; 10] n)) = zero_lines n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat concat app]. cbn [to_bytes map]. unfold to_bytes in IH. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma TP_eq : forall c n,
  t_eq (ShapeAlg.t_emit (Wz 1 (fst (emits n stdout_init))) (KEXIT fs c 0 (snd (emits n stdout_init))))
       (ShapeAlg.t_emit (W 1 (zero_lines n)) (t_exit (exit_code 0) fs)).
Proof.
  intros c n. unfold KEXIT.
  eapply t_eq_trans; [apply t_eq_sym; apply t_eq_emit_app|].
  rewrite <- Wz_app, emits_total, Wz_W, to_bytes_zero_lines.
  replace (if c then 0 else 0) with 0 by (destruct c; reflexivity). unfold exit_code. rewrite bv_and_255_small by lia. apply t_eq_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma byte_lt256 : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma KDONE_body : forall FILE, (Driver.MAX_INPUT <=? Z.of_nat (length FILE)) = false -> t_eq (KDONE fs FILE) (t_body FILE fs).
Proof.
  intros FILE HM. unfold KDONE, t_body. unfold SpecT.MAX_INPUT. unfold Driver.MAX_INPUT in HM. rewrite HM.
  destruct (Nat.ltb_spec (length FILE) 6) as [LT|GE]; [apply die_short|]. cbv zeta.
  set (b0 := bv_unsigned (nth 0 FILE (Z_to_bv 8 0))). set (b1 := bv_unsigned (nth 1 FILE (Z_to_bv 8 0))). set (b2 := bv_unsigned (nth 2 FILE (Z_to_bv 8 0))).
  pose proof (byte_lt256 (nth 0 FILE (Z_to_bv 8 0))) as R0. pose proof (byte_lt256 (nth 1 FILE (Z_to_bv 8 0))) as R1.
  fold b0 in R0. fold b1 in R1.
  set (cw := b0 + 256 * b1). set (L := cw mod 32768).
  assert (RL : 0 <= L < 32768) by (subst L; apply Z.mod_pos_bound; lia).
  replace (Z.of_nat (length FILE) <? 6 + L) with (length FILE <? 6 + Z.to_nat L)%nat.
  2:{ destruct (Nat.ltb_spec (length FILE) (6 + Z.to_nat L)), (Z.ltb_spec (Z.of_nat (length FILE)) (6 + L)); try reflexivity; exfalso; lia. }
  destruct (Nat.ltb_spec (length FILE) (6 + Z.to_nat L)) as [LT2|GE2]; [apply die_overrun|].
  replace (128 <=? b1) with (32768 <=? cw).
  2:{ destruct (Z.leb_spec 128 b1), (Z.leb_spec 32768 cw); try reflexivity; exfalso; lia. }
  set (c := 32768 <=? cw).
  replace (if L =? 0 then 1%nat else S (Z.to_nat (b2 mod 4))) with (match Z.to_nat L with O => 1%nat | S _ => S (Z.to_nat (b2 mod 4)) end).
  2:{ destruct (Z.eqb_spec L 0) as [E|NE]; [rewrite E; reflexivity|]. destruct (Z.to_nat L) eqn:EL; [exfalso; lia | reflexivity]. }
  apply TP_eq.
Qed.

Lemma TFIN_body : forall FILE, t_eq (TFIN fs FILE (KDONE fs FILE)) (t_body FILE fs).
Proof.
  intros FILE. unfold TFIN. destruct (Driver.MAX_INPUT <=? Z.of_nat (length FILE)) eqn:HM.
  - unfold t_body, SpecT.MAX_INPUT. unfold Driver.MAX_INPUT in HM. rewrite HM. apply die_refused.
  - apply KDONE_body. exact HM.
Qed.

Lemma TFIN_opened : forall FILE, t_eq (TFIN fs FILE (KDONE fs FILE)) (t_opened FILE fs).
Proof. intros FILE. unfold t_opened. apply TFIN_body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; intros [|b q]; cbn [list_byte_eqb]; try (split; [discriminate | discriminate]); [tauto|].
  rewrite andb_true_iff, IH. split.
  - intros [E1 E2]. apply bv_eqb_eq in E1. subst. reflexivity.
  - intros E. inversion E; subst. split; [apply bv_eqb_eq; reflexivity | reflexivity].
Qed.

Lemma eqb_agree : forall (a b : bool) (P : Prop), (a = true <-> P) -> (b = true <-> P) -> a = b.
Proof. intros [] [] P HA HB; try reflexivity; [symmetry; apply HB, HA | apply HA, HB]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem DRV2_spec : forall MO a0 a1, m_fs MO = fs -> path_eqb a1 Namei.dotdot_path = false ->
  t_eq (DRV2 MO fs a1) (spec [a0; a1] fs).
Proof.
  intros MO a0 a1 MOFS NDD. unfold DRV2, spec, open_classify. unfold path_max.
  destruct (4096 <=? length a1)%nat; [apply die_cannot_open|].
  destruct a1 as [|c p] eqn:EA; [cbn [list_byte_eqb]; apply die_cannot_open|]. rewrite <- EA in *.
  replace (list_byte_eqb a1 []) with false by (rewrite EA; reflexivity).
  unfold path_is_dirref. rewrite NDD, Bool.orb_false_r.
  replace (list_byte_eqb a1 SpecT.dot_path) with (path_eqb a1 Uapi.dot_path).
  2:{ apply (eqb_agree _ _ (a1 = SpecT.dot_path)); [apply path_eqb_eq | apply list_byte_eqb_eq]. }
  destruct (path_eqb a1 Uapi.dot_path).
  - unfold KLOOP, t_opened_dir. apply t_alt2_cong; [apply die_cannot_open| apply die_read_error].
  - rewrite MOFS. destruct (fs_lookup fs a1) as [d|] eqn:FL; [| apply die_cannot_open].
    apply t_alt2_cong; [apply die_cannot_open|]. unfold KLOOP. rewrite FL. apply TFIN_opened.
Qed.

Theorem DRV_spec : forall MO argv, m_fs MO = fs -> valid_argv argv -> t_eq (DRV MO fs argv) (spec argv fs).
Proof.
  intros MO argv MOFS (_ & _ & _ & _ & ND). destruct argv as [|a0 [|a1 [|a2 l]]]; unfold DRV; cbn [hd spec]; try apply die_usage.
  apply (DRV2_spec MO a0 a1 MOFS). cbn [tl] in ND. inversion ND as [|? ? [_ X] _]. exact X.
Qed.
End Fs.
