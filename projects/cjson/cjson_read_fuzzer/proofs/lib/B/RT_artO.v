(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section OPEN.
Variables (zf : word -> bool) (lo hi : Z).
Hypothesis ZS : zf_noseg bsegs zf.
Hypothesis LO : AIMG_HI <= lo.

Local Abbreviation om m := (open_mem zf lo hi m).

(* [comment removed for export] *)
Lemma o_cells : forall m a cs, cells_at bsegs m a cs -> cells_at bsegs (om m) a cs.
Proof. intros m a cs [Hwf Hb]. split; [exact Hwf| apply bytes_at_open; [exact ZS| exact Hb]]. Qed.
Lemma o_rw : forall m a cs, rw_cells bsegs m a cs -> rw_cells bsegs (om m) a cs.
Proof. intros m a cs H. apply rw_cells_open; [exact ZS| exact H]. Qed.
Lemma o_vis : forall m l h, vis m l h -> vis (om m) l h.
Proof. intros m l h H. apply stk_open; [exact ZS| exact H]. Qed.
Lemma o_none : forall m a, 0 <= a < AIMG_HI -> m (wa a) = None -> om m (wa a) = None.
Proof.
  intros m a Ha H. unfold open_mem. rewrite H. rewrite wa_unsigned by (unfold AIMG_HI in *; lia).
  destruct (Z.leb_spec0 lo a); [exfalso; lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac xfer H :=
  lazymatch goal with
  | |- _ /\ _ => let H1 := fresh "K" in let H2 := fresh "K" in destruct H as [H1 H2]; split; [xfer H1| xfer H2]
  | |- exists _, _ => let x := fresh "x" in let H1 := fresh "K" in destruct H as [x H1]; exists x; xfer H1
  | |- True => exact I
  | |- cells_at _ _ _ _ => exact (o_cells _ _ _ H)
  | |- rw_cells _ _ _ _ => exact (o_rw _ _ _ H)
  | |- stk _ _ _ _ => exact (o_vis _ _ _ H)
  | |- forall _, _ => let v := fresh "v" in intro v; let H1 := fresh "K" in pose proof (H v) as H1; xfer H1
  | |- _ => exact H
  end.

Variable st : rtstate.
Variable m : word -> option byte.

Lemma O_link : R_link m -> R_link (om m).
Proof.
  intros [H1 H2]. split; [xfer H1|]. intros a Ha. apply o_none; [| exact (H2 a Ha)].
  unfold A_GLOBREC_LO, A_GLOBREC_HI, AIMG_HI in *. lia.
Qed.
Lemma O_consts : R_consts st m -> R_consts st (om m). Proof. intros H. unfold R_consts, R_emb in *. xfer H. Qed.
Lemma O_alloc : R_alloc st m -> R_alloc st (om m). Proof. intros H. unfold R_alloc in *. xfer H. Qed.
Lemma O_rinfo : R_rinfo st m -> R_rinfo st (om m). Proof. intros H. unfold R_rinfo in *. xfer H. Qed.
Lemma O_regions : R_regions st m -> R_regions st (om m). Proof. intros H. unfold R_regions in *. cbv zeta in *. xfer H. Qed.
Lemma O_avail : R_avail st m -> R_avail st (om m). Proof. intros H. unfold R_avail in *. xfer H. Qed.
Lemma O_cache : R_cache st m -> R_cache st (om m). Proof. intros H. unfold R_cache in *. xfer H. Qed.
Lemma O_thread : R_thread st m -> R_thread st (om m). Proof. intros H. unfold R_thread in *. xfer H. Qed.
Lemma O_block : forall md A n, R_block st m md A n -> R_block st (om m) md A n.
Proof.
  intros md A n H. unfold R_block, R_bighdr, R_sechdr, R_secmap, R_bshadow in *.
  destruct md; destruct (bprim n); cbn iota in *; xfer H.
Qed.
Lemma O_live : R_live st m -> R_live st (om m).
Proof. intros H A n Hin. apply O_block. exact (H A n Hin). Qed.
Lemma O_quar : R_quar st m -> R_quar st (om m).
Proof. intros [H1 H2]. split; intros A n Hin; apply O_block; [exact (H1 A n Hin)| exact (H2 A n Hin)]. Qed.
Lemma O_qslots : forall b, R_qslots m b -> R_qslots (om m) b.
Proof. intros b H. unfold R_qslots in *. xfer H. Qed.
Lemma O_qlist : forall q, R_qlist m q -> R_qlist (om m) q.
Proof.
  induction q as [|b q IH]; intros H; [exact I|]. cbn [R_qlist] in *. destruct H as (H1 & H2 & H3).
  split; [exact (o_rw _ _ _ H1)|]. split; [apply O_qslots; exact H2| apply IH; exact H3].
Qed.
Lemma O_batches : R_batches st m -> R_batches st (om m).
Proof.
  intros (H1 & H2 & H3 & H4). unfold R_batches.
  split; [apply O_qlist; exact H1|]. split; [apply O_qlist; exact H2|]. split; [apply O_qlist; exact H3|].
  intros bd Hbd. destruct (H4 bd Hbd) as [[nx K1] K2]. split; [exists nx; exact (o_rw _ _ _ K1)| apply O_qslots; exact K2].
Qed.
Lemma O_ptrarr : R_ptrarr st m -> R_ptrarr st (om m).
Proof. intros H. unfold R_ptrarr, R_secmap in *. xfer H. Qed.
Lemma O_depot : R_depot st m -> R_depot st (om m). Proof. intros H. unfold R_depot in *. xfer H. Qed.
Lemma O_fs : R_fs st m -> R_fs st (om m). Proof. intros H. unfold R_fs in *. xfer H. Qed.
Lemma O_ia : R_ia m -> R_ia (om m). Proof. intros H. unfold R_ia in *. xfer H. Qed.
Lemma O_lowshadow : R_lowshadow m -> R_lowshadow (om m). Proof. intros H. unfold R_lowshadow in *. xfer H. Qed.

Theorem RTREP_open : RTREP st m -> RTREP st (om m).
Proof.
  intros HR. constructor;
  [ apply O_link; exact (rr_link st m HR) | apply O_consts; exact (rr_consts st m HR) | apply O_alloc; exact (rr_alloc st m HR)
  | apply O_rinfo; exact (rr_rinfo st m HR) | apply O_regions; exact (rr_regions st m HR) | apply O_avail; exact (rr_avail st m HR)
  | apply O_cache; exact (rr_cache st m HR) | apply O_thread; exact (rr_thread st m HR) | apply O_live; exact (rr_live st m HR)
  | apply O_quar; exact (rr_quar st m HR) | apply O_batches; exact (rr_batches st m HR) | apply O_ptrarr; exact (rr_ptrarr st m HR)
  | apply O_depot; exact (rr_depot st m HR) | apply O_fs; exact (rr_fs st m HR) | apply O_ia; exact (rr_ia st m HR)
  | apply O_lowshadow; exact (rr_lowshadow st m HR) ].
Qed.
End OPEN.


End CeilWrap.
