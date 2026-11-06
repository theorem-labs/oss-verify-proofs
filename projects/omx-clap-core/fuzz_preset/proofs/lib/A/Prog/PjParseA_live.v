(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_parse_live.v, with only its comments or blank lines changed. *)
(* Theorem Labs, 2026-10: pj_parse's live room at each event of its all-granted reading (image A' port of pj_parse,
   RELOCATED unchanged from a Theorem Labs lane's image-B' batch-kit rebind 5134b312d551 lib/B/Prog/pj_parse_live.v; image-free; lane
   pj_parse, a Theorem Labs lane): from blocks_bytes S + PRH_FnPj.LIVE_pj_parse tl <= LIVE_MAX at cf_head =
   PresetReqAt.HEAD, PRH_Base.prh_live_evs S holds of the heap events of parse_value 0's all-granted trace
   (PRH_Charge.prhPv_gtrace 0 tl, = PRH_FnPj.prhPj_ptrace tl by PjGrammar.jr_run_eq).
   Route: PresetLiveBytes.pkB_nth bounds each event's live bytes plus request by the byte peak pkB; pkB_frame0 splits
   off the entry's live bytes (blocks_bytes_zsum); the reading's own peak pkB [] is at most
   2 * hpeakR + HEAD * (calls + 1) (pjl_pk): before the event after a prefix P the live bytes are held P plus one HEAD
   per live block (PresetLiveBytes.rd_live_bytes), a grow of m to n still holds the old block m + HEAD, and m <= held P
   because every live entry is at least HEAD (pjl_live_head).
   proves no function (kind: pure model lemma). *)
From Stdlib Require Import ZArith NArith List Lia Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetReqAt PresetRoom
  PresetLiveBytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader PRH_Charge PRH_Base PRH_FnPj.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the trace: parse_value 0's all-granted run is the reader run's trace ---- *)

Lemma pjl_gtrace_eq : forall tl,
  PRH_Charge.prhPv_gtrace 0 tl = snd (PjGrammar.jr_run PRH_Reader.prh_jr_strtod tl []).
Proof. intros tl. unfold PRH_Charge.prhPv_gtrace. rewrite PjGrammar.jr_run_eq. reflexivity. Qed.

Lemma pjl_rd_hevs_cons : forall e t,
  PresetReqAt.rd_hevs (e :: t) = PresetReqAt.rd_hev e ++ PresetReqAt.rd_hevs t.
Proof. reflexivity. Qed.

Lemma pjl_rd_hevs_one : forall e, PresetReqAt.rd_hevs [e] = PresetReqAt.rd_hev e.
Proof. intros e. unfold PresetReqAt.rd_hevs. cbn [flat_map]. apply app_nil_r. Qed.

Lemma pjl_okf_prefix : forall P R,
  PresetReqAt.okf [] (PresetReqAt.rd_hevs (P ++ R)) -> PresetReqAt.okf [] (PresetReqAt.rd_hevs P).
Proof.
  intros P R H. rewrite PresetReqAt.rd_hevs_app in H. exact (proj1 (proj1 (PresetReqAt.okf_app _ _ _) H)).
Qed.

(* ---- the held peak: every prefix's held bytes lie under the whole trace's hpeakR ---- *)

Lemma pjl_hpeakR_nn : forall tr, 0 <= PRH_Reader.hpeakR tr.
Proof. intros [|e r]; cbn [PRH_Reader.hpeakR]; lia. Qed.

Lemma pjl_held_hpeakR : forall a b, PjGrammar.held a + PRH_Reader.hpeakR b <= PRH_Reader.hpeakR (a ++ b).
Proof.
  induction a as [|e a IH]; intros b; cbn [app PjGrammar.held PRH_Reader.hpeakR]; [lia|].
  specialize (IH b). lia.
Qed.

Lemma pjl_held_prefix : forall a b, PjGrammar.held a <= PRH_Reader.hpeakR (a ++ b).
Proof. intros a b. pose proof (pjl_held_hpeakR a b). pose proof (pjl_hpeakR_nn b). lia. Qed.

(* ---- every live entry of a reader prefix is at least HEAD ---- *)

Lemma pjl_Forall_rm1 : forall (Q : Z -> Prop) z s, Forall Q s -> Forall Q (PresetReqAt.rm1 z s).
Proof.
  intros Q z s H. induction H as [|y l Hy Hl IH]; cbn [PresetReqAt.rm1]; [constructor|].
  destruct (y =? z); [exact Hl | constructor; [exact Hy | exact IH]].
Qed.

Lemma pjl_live_head : forall P s, Forall (fun z => PresetReqAt.HEAD <= z) s ->
  Forall (fun z => PresetReqAt.HEAD <= z) (PresetReqAt.hlive_from s (PresetReqAt.rd_hevs P)).
Proof.
  induction P as [|e P IH]; intros s Hs; [exact Hs|].
  rewrite pjl_rd_hevs_cons, PresetReqAt.hlive_from_app. apply IH.
  destruct e as [n | [|m] n | n | n];
    cbn [PresetReqAt.rd_hev PresetReqAt.hlive_from fold_left PresetReqAt.hstep].
  - constructor; [cbv beta; lia | exact Hs].
  - constructor; [cbv beta; lia | exact Hs].
  - constructor; [cbv beta; lia | apply pjl_Forall_rm1; exact Hs].
  - exact Hs.
  - apply pjl_Forall_rm1. exact Hs.
Qed.

Lemma pjl_live_head0 : forall P,
  Forall (fun z => PresetReqAt.HEAD <= z) (PresetReqAt.hlive (PresetReqAt.rd_hevs P)).
Proof. intros P. unfold PresetReqAt.hlive. apply pjl_live_head. constructor. Qed.

Lemma pjl_zsum_ge : forall l, Forall (fun z => PresetReqAt.HEAD <= z) l ->
  PresetReqAt.HEAD * Z.of_nat (length l) <= PresetLiveBytes.zsum l.
Proof.
  intros l H. induction H as [|y r Hy Hr IH]; cbv beta in *.
  - rewrite PresetLiveBytes.zsum_nil. cbn [length]. unfold PresetReqAt.HEAD. lia.
  - rewrite PresetLiveBytes.zsum_cons. cbn [length]. clear - Hy IH. unfold PresetReqAt.HEAD in *. lia.
Qed.

(* a live entry z of a list whose entries are all at least HEAD: z - HEAD is at most the list's bytes above its
   heads *)
Lemma pjl_in_live : forall z l, In z l -> Forall (fun x => PresetReqAt.HEAD <= x) l ->
  z + PresetReqAt.HEAD * Z.of_nat (length l) <= PresetLiveBytes.zsum l + PresetReqAt.HEAD.
Proof.
  intros z l Hin Hf. pose proof (PresetReqAt.rm1_in z l Hin) as Hp.
  pose proof (pjl_zsum_ge _ (pjl_Forall_rm1 _ z l Hf)) as K.
  rewrite (PresetLiveBytes.zsum_perm _ _ Hp), (Permutation_length Hp), PresetLiveBytes.zsum_cons.
  cbn [length]. clear - K. unfold PresetReqAt.HEAD in *. lia.
Qed.

(* ---- the live bytes after a prefix P of a closed reader trace P ++ R ---- *)

Lemma pjl_live_le : forall P R, PresetReqAt.okf [] (PresetReqAt.rd_hevs (P ++ R)) ->
  PresetLiveBytes.zsum (PresetReqAt.hlive (PresetReqAt.rd_hevs P)) <=
    PRH_Reader.hpeakR (P ++ R) + PresetReqAt.HEAD * Z.of_nat (PjGrammar.calls (P ++ R)).
Proof.
  intros P R H. destruct (PresetLiveBytes.rd_live_bytes P (pjl_okf_prefix P R H)) as [E1 E2].
  pose proof (pjl_held_prefix P R) as H1. pose proof (PjGrammar.calls_app P R) as H2.
  clear - E1 E2 H1 H2. unfold PresetReqAt.HEAD in *. lia.
Qed.

(* ---- the reading's own byte peak, over every split P ++ R of a closed trace T (pk_rd0's induction) ---- *)

Lemma pjl_pk : forall T R P, PresetReqAt.okf [] (PresetReqAt.rd_hevs T) -> T = P ++ R ->
  PresetLiveBytes.pkB (PresetReqAt.hlive (PresetReqAt.rd_hevs P)) (PresetReqAt.rd_hevs R) <=
  2 * PRH_Reader.hpeakR T + PresetReqAt.HEAD * (Z.of_nat (PjGrammar.calls T) + 1).
Proof.
  intros T R. induction R as [|e R IH]; intros P Hok E.
  - change (PresetLiveBytes.pkB (PresetReqAt.hlive (PresetReqAt.rd_hevs P)) (PresetReqAt.rd_hevs []))
      with (PresetLiveBytes.zsum (PresetReqAt.hlive (PresetReqAt.rd_hevs P))).
    subst T. pose proof (pjl_live_le P [] Hok) as H1. pose proof (pjl_hpeakR_nn (P ++ [])) as H2.
    clear - H1 H2. unfold PresetReqAt.HEAD in *. lia.
  - rewrite pjl_rd_hevs_cons, PresetLiveBytes.pkB_app.
    assert (E' : T = (P ++ [e]) ++ R) by (rewrite E, <- app_assoc; reflexivity).
    pose proof (IH (P ++ [e]) Hok E') as H2.
    assert (Hs : PresetReqAt.hlive_from (PresetReqAt.hlive (PresetReqAt.rd_hevs P)) (PresetReqAt.rd_hev e) =
                 PresetReqAt.hlive (PresetReqAt.rd_hevs (P ++ [e]))).
    { unfold PresetReqAt.hlive. rewrite PresetReqAt.rd_hevs_app, PresetReqAt.hlive_from_app, pjl_rd_hevs_one.
      reflexivity. }
    assert (H1 : PresetLiveBytes.pkB (PresetReqAt.hlive (PresetReqAt.rd_hevs P)) (PresetReqAt.rd_hev e) <=
                 2 * PRH_Reader.hpeakR T + PresetReqAt.HEAD * (Z.of_nat (PjGrammar.calls T) + 1)).
    { assert (okP : PresetReqAt.okf [] (PresetReqAt.rd_hevs P)).
      { apply (pjl_okf_prefix P (e :: R)). rewrite <- E. exact Hok. }
      assert (okPe : PresetReqAt.okf [] (PresetReqAt.rd_hevs (P ++ [e]))).
      { apply (pjl_okf_prefix (P ++ [e]) R). rewrite <- E'. exact Hok. }
      assert (Hit : PresetReqAt.okf (PresetReqAt.hlive (PresetReqAt.rd_hevs P)) (PresetReqAt.rd_hev e)).
      { pose proof okPe as K. rewrite PresetReqAt.rd_hevs_app in K. apply PresetReqAt.okf_app in K as [_ K].
        rewrite pjl_rd_hevs_one in K. exact K. }
      pose proof (pjl_live_le P (e :: R) ltac:(rewrite <- E; exact Hok)) as B0. rewrite <- E in B0.
      pose proof (pjl_live_le (P ++ [e]) R ltac:(rewrite <- E'; exact Hok)) as B1. rewrite <- E' in B1.
      destruct (PresetLiveBytes.rd_live_bytes P okP) as [EL1 EL2].
      pose proof (pjl_live_head0 P) as HF.
      pose proof (pjl_held_prefix P (e :: R)) as Hh0. rewrite <- E in Hh0.
      pose proof (pjl_held_prefix (P ++ [e]) R) as Hh1. rewrite <- E', PjGrammar.held_app in Hh1.
      cbn [PjGrammar.held] in Hh1.
      pose proof (PjGrammar.calls_app (P ++ [e]) R) as Hc. rewrite <- E', PjGrammar.calls_app in Hc.
      cbn [PjGrammar.calls] in Hc.
      pose proof (pjl_hpeakR_nn T) as Hnn.
      destruct e as [n | [|m] n | n | n];
        cbn [PjGrammar.held_ev PjGrammar.is_call] in Hh1, Hc;
        cbn [PresetReqAt.rd_hev PresetReqAt.hlive_from fold_left] in Hs, Hit;
        cbn [PresetReqAt.rd_hev PresetLiveBytes.pkB PresetLiveBytes.ev_req].
      - (* EAlloc n *)
        rewrite Hs. clear - EL1 EL2 Hh1 Hc Hnn B1. unfold PresetReqAt.HEAD in *. lia.
      - (* EGrow 0 n: a malloc *)
        rewrite Hs. clear - EL1 EL2 Hh1 Hc Hnn B1. unfold PresetReqAt.HEAD in *. lia.
      - (* EGrow (S m) n: the old block S m + HEAD is live *)
        cbn [PresetReqAt.okf PresetReqAt.hits] in Hit. destruct Hit as [Hin _].
        pose proof (pjl_in_live _ _ Hin HF) as Hm.
        rewrite Hs. clear - EL1 EL2 Hh0 Hh1 Hc Hnn B1 Hm. unfold PresetReqAt.HEAD in *. lia.
      - (* EFail n: no heap event *)
        clear - B0 Hnn. unfold PresetReqAt.HEAD in *. lia.
      - (* EFree n: asks nothing *)
        rewrite Hs. clear - B0 B1 Hnn. unfold PresetReqAt.HEAD in *. lia. }
    rewrite Hs. clear - H1 H2. lia.
Qed.

(* ---- the per-event live room of pj_parse's all-granted reading ---- *)

Section c.
Context {cp : CfParams}.

Lemma pjl_live_evs : forall (S : astate) (tl : list Z),
  cf_head = PresetReqAt.HEAD ->
  blocks_bytes S + PRH_FnPj.LIVE_pj_parse tl <= LIVE_MAX ->
  PRH_Base.prh_live_evs S (PresetReqAt.rd_hevs (PRH_Charge.prhPv_gtrace 0 tl)).
Proof.
  intros S tl Hh Hb j e Hj. unfold PRH_Base.prh_live_at.
  assert (Hok : PresetReqAt.okf [] (PresetReqAt.rd_hevs (PRH_Charge.prhPv_gtrace 0 tl))).
  { rewrite pjl_gtrace_eq. apply PresetReqAt.rd_okf. }
  pose proof (PresetLiveBytes.pkB_nth _ (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) j e Hj) as H1.
  rewrite (PresetLiveBytes.pkB_frame0 _ (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) Hok) in H1.
  pose proof (pjl_pk (PRH_Charge.prhPv_gtrace 0 tl) (PRH_Charge.prhPv_gtrace 0 tl) [] Hok eq_refl) as H2.
  change (PresetReqAt.hlive (PresetReqAt.rd_hevs [])) with (@nil Z) in H2.
  assert (Hs : PresetLiveBytes.zsum (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) = blocks_bytes S).
  { rewrite PresetLiveBytes.blocks_bytes_zsum. reflexivity. }
  assert (Ee : PRH_Base.prh_ev_req e = PresetLiveBytes.ev_req e) by (destruct e; reflexivity).
  unfold PRH_FnPj.LIVE_pj_parse, PRH_FnPj.prhPj_ptrace in Hb. rewrite <- pjl_gtrace_eq, Hh in Hb.
  rewrite Ee. unfold PresetLiveBytes.zsum in H1, Hs.
  clear - H1 H2 Hs Hb. unfold PresetReqAt.HEAD in *. lia.
Qed.

End c.

Print Assumptions pjl_live_evs.
