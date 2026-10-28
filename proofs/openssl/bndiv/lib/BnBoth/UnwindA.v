(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface D_kit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Class UnwindKit : Type := mkUK {
  uk_ctx : Z -> list Z -> Prop;                 (* [comment removed for export] *)
  uk_call : Z -> Z -> Z -> Prop;                (* [comment removed for export] *)
  uk_tail : Z -> Z -> Prop;                     (* [comment removed for export] *)
  uk_leaf : Z -> Z -> Prop;                     (* [comment removed for export] *)
  uk_leaf_tail : Z -> Prop;                     (* [comment removed for export] *)
  uk_ctx_call : forall f r g ras, uk_call f r g -> uk_ctx f ras -> uk_ctx g (r :: ras);
  uk_ctx_tail : forall f g ras, uk_tail f g -> uk_ctx f ras -> uk_ctx g ras;
  uk_ctx_leaf : forall f r ras, uk_leaf f r -> uk_ctx f ras -> In (r :: ras) SITE_TRACES;
  uk_ctx_leaf_tail : forall f ras, uk_leaf_tail f -> uk_ctx f ras -> In ras SITE_TRACES
}.

Lemma unwind_ch_intro : forall (m : mem) (ra s0 sp : word) ras,
  In (bv_unsigned ra :: ras) SITE_TRACES -> uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> unwind_ch m ra s0 sp.
Proof. intros m ra s0 sp ras H1 H2. exists ras. split; assumption. Qed.

Lemma rw_cells_app_r : forall (m : mem) A pre post, rw_cells bsegs m A (pre ++ post) ->
  rw_cells bsegs m (A + Z.of_nat (cells_size pre)) post.
Proof.
  intros m A pre post ((Hwf & Hb) & Hw). apply cells_wf_app in Hwf as [Wp Wq].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb2]. rewrite (cells_bytes_length pre Wp) in Hb2.
  split; [split; [exact Wq | exact Hb2]|].
  destruct Hw as (W1 & W2 & W3). rewrite cells_size_app, Nat2Z.inj_add in W2, W3.
  split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size pre) + i) with (A + (Z.of_nat (cells_size pre) + i)) by lia.
  apply W3. lia.
Qed.

(* [comment removed for export] *)
Lemma uw_push_frame : forall (m : mem) f' fp N pre ra_e s0_e ras,
  Z.of_nat (cells_size pre) = N - 16 ->
  f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells bsegs m (fp + - N) (pre ++ [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)]) ->
  uw_chain USTACK_TOP m fp s0_e ras -> uw_chain USTACK_TOP m f' fp (ra_e :: ras).
Proof.
  intros m f' fp N pre ra_e s0_e ras HN H1 H2 H3 H4 HC HU. cbn [uw_chain]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  exists s0_e. split; [exact H4|]. split; [| exact HU].
  pose proof (rw_cells_app_r m _ _ _ HC) as X. rewrite HN in X. replace (fp + - N + (N - 16)) with (fp + -16) in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma uw_chain_agree : forall (m m' : mem) ras f fp,
  uw_chain USTACK_TOP m f fp ras -> agree_on (fun a => f <= a < USTACK_TOP) m m' -> uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros m m' ras. induction ras as [|r ras IH]; intros f fp HU AG; cbn [uw_chain] in *; [exact HU|].
  destruct HU as (H1 & H2 & H3 & fp' & Hfp' & HC & HU). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  exists fp'. split; [exact Hfp'|]. split.
  - eapply rw_cells_agree; [exact AG | exact HC |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia.
  - apply (IH fp fp' HU). eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in *. lia.
Qed.

Lemma uw_chain_munch_nw : forall W (m m' : mem) ras f fp,
  uw_chain USTACK_TOP m f fp ras -> munch W m m' -> Forall (fun iv => snd iv <= f) W -> uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros W m m' ras f fp HU MU HW. apply (uw_chain_agree m m' ras f fp HU).
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbv beta in Ha.
  clear - HW Ha. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. cbn [snd] in H1. split; [lia | exact (IH H2)].
Qed.
