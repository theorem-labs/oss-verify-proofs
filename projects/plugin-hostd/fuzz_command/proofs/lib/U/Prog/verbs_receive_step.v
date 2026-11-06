(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v, with its module names changed; 153 of its 188 lines of code are new or changed and 180 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply.
Import ListNotations.
Local Open Scope Z_scope.

Lemma nodup_app_i : forall (l1 l2 : list Z), List.NoDup l1 -> List.NoDup l2 -> (forall a, In a l1 -> ~ In a l2) ->
  List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2 N1 N2 Dj; cbn; [exact N2|].
  inversion N1 as [|y l Hx N1']; subst. constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hx Hin) | exact (Dj x (or_introl eq_refl) Hin)].
  - apply IH; [exact N1' | exact N2 | intros a Ha; apply Dj; right; exact Ha].
Qed.

Section Step.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation L0 := (s_L S).
Local Notation A0 := (s_A S).
Local Notation rg0 := (s_regs S).
Local Notation m0 := (s_mem S).
Local Notation md0 := (s_md S).
Local Notation b0 := (s_b S).
Local Notation O0 := (s_O S).
Local Notation D := (s_D S).
Local Notation lb := (s_lb S).
Local Notation cb := (s_cb S).
Local Notation ps := (s_ps S).
Local Notation nlb := (s_nlb S).
Local Notation ncb := (s_ncb S).
Local Notation spf := (s_spf S).

Lemma ok_surv : forall L1 A1 mem1 L2 A2 mem2 O1 a k,
  RecKindB.others_kept (ms_segs B) L1 A1 mem1 L2 A2 mem2 O1 -> In (a, k) (blocks L1 A1) -> ~ In (a, k) O1 ->
  In (a, k) (blocks L2 A2) /\ forall i, 0 <= i < k -> mbyte (ms_segs B) mem2 (a + i) = mbyte (ms_segs B) mem1 (a + i).
Proof.
  intros L1 A1 mem1 L2 A2 mem2 O1 a k HOK Hin Hno. unfold blocks in Hin.
  apply in_map_iff in Hin as ([p k'] & E & Hp). cbv beta in E; cbn [fst snd] in E. injection E as <- <-.
  destruct (HOK p k' Hp Hno) as (Hp2 & Ea & Hb). split; [|exact Hb].
  apply in_map_iff. exists (p, k'). split; [cbv beta; cbn [fst snd]; rewrite Ea; reflexivity | exact Hp2].
Qed.

Lemma addr_notin : forall L2 A2 mem2 md2 R2 O2 a k, MR L2 A2 mem2 md2 -> g_rec_rep (ms_segs B) L2 A2 mem2 R2 O2 ->
  In (a, k) (blocks L2 A2) -> 1 <= k -> ~ In (a, k) O2 -> ~ In a (map fst O2).
Proof.
  intros L2 A2 mem2 md2 R2 O2 a k HM HR Hin Hk Hno Ha. apply in_map_iff in Ha as ([a' k'] & E & Hin'). cbv beta in E; cbn [fst snd] in E. subst a'.
  destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ HR _ Hin') as [Hb Hk']. cbn [snd] in Hk'.
  pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ HM) as PD.
  assert (E : k' = k) by exact (reply.same_start _ a k' k PD Hb Hin ltac:(lia) ltac:(lia)). subst k'. exact (Hno Hin').
Qed.

Lemma user_apart : forall L1 A1 O1 q n,
  (forall p k, In (p, k) (user_blocks A1) -> ~ In (ptr_addr L1 p, k) O1 -> ptr_addr L1 p + k <= q \/ q + n <= ptr_addr L1 p) ->
  forall pn', In pn' (blocks L1 A1) -> ~ In pn' O1 -> q + n <= fst pn' \/ fst pn' + snd pn' <= q.
Proof.
  intros L1 A1 O1 q n H [a k] Hin Hno. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbv beta in E; cbn [fst snd] in E. injection E as <- <-. cbn [fst snd]. destruct (H p k' Hp Hno); lia.
Qed.

Lemma tail_step_stub : forall rg mem1 md1 L1 A1 R1 O1 k1 X K L2 A2 rg2 mem2 md2 R2 O2 NEW k2,
  vtail B API S L1 A1 mem1 md1 R1 O1 k1 X ->
  spZ rg = spf -> 0 <= K <= 14336 ->
  RecKindB.call_post_rec B MR K L1 A1 rg mem1 md1 RecKindB.rec_area (fun a => In a (map fst O1))
    L2 A2 rg2 mem2 md2 ->
  g_rec_rep (ms_segs B) L2 A2 mem2 R2 O2 -> RecKindB.owns_new L1 A1 O1 O2 ->
  (forall pn, In pn (blocks L2 A2) -> (In pn (blocks L1 A1) /\ ~ In pn O1) \/ In pn O2 \/ In pn NEW) ->
  RecKindB.others_kept (ms_segs B) L1 A1 mem1 L2 A2 mem2 O1 ->
  ro_agree (ms_segs B) mem2 -> st_init_done A2 = true ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_n b0 k2) -> (k2 <= 32)%nat ->
  (forall pn, In pn NEW -> In pn (blocks L2 A2) /\ ~ In (fst pn) (map fst O2) /\ 1 <= snd pn /\
     (forall pn', In pn' (blocks L1 A1) -> ~ In pn' O1 -> fst pn + snd pn <= fst pn' \/ fst pn' + snd pn' <= fst pn)) ->
  List.NoDup (map fst NEW) ->
  vtail B API S L2 A2 mem2 md2 R2 O2 k2 (X ++ NEW) /\
  (forall a k s bs, In (a, k) X -> a <= s -> s + Z.of_nat (length bs) <= a + k ->
     bytes_at rsegs mem1 s bs -> bytes_at rsegs mem2 s bs).
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 X K L2 A2 rg2 mem2 md2 R2 O2 NEW k2 H SPR HK POST HREC OWN BLK OK
    RO2 INIT RLEN RES HKB HNEW NDN.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof POST as (HM2 & _).
  assert (SURV : forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> In pn (blocks L2 A2) /\
            (forall i, 0 <= i < snd pn -> mbyte (ms_segs B) mem2 (fst pn + i) = mbyte (ms_segs B) mem1 (fst pn + i))).
  { intros [a k] Hin Hno. exact (ok_surv L1 A1 mem1 L2 A2 mem2 O1 a k OK Hin Hno). }
  assert (NO2 : forall pn, In pn (blocks L1 A1) -> ~ In pn O1 -> ~ In pn O2).
  { intros pn Hin Hno Ho. destruct (OWN pn Ho) as [H1|H1]; [exact (Hno H1) | exact (H1 Hin)]. }
  pose proof (t_x _ _ _ _ _ _ _ _ _ _ _ H) as HX.
  assert (XNO : forall pn, In pn X -> ~ In pn O1).
  { intros pn Hp Ho. apply (proj2 (HX pn Hp)). apply in_map_iff. exists pn. split; [reflexivity | exact Ho]. }
  split.
  2:{ intros a k s bs Hx H1 H2 Hb. destruct (HX (a, k) Hx) as [Hin _].
      apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi.
      replace (s + i) with (a + (s - a + i)) by ring. rewrite <- SEGS.
      exact (proj2 (SURV (a, k) Hin (XNO (a, k) Hx)) (s - a + i) ltac:(cbn; lia)). }
  constructor.
  - eapply (rel_call B API (vf_ax B API HF) (vf_ctxo B API HF)); [exact (t_rel _ _ _ _ _ _ _ _ _ _ _ H) | exact POST
      | exact RLEN | | | | ].
    + intros a [Ha|Ha]; [left; rewrite SPR in Ha; unfold s_spf, VR_K in *; lia | right; exact Ha].
    + intros a Ha. right. unfold RecKindB.rec_area, vr_writes in *. tauto.
    + intros a Hs Hn. unfold scratch_k in Hs, Hn. rewrite SPR in Hn.
      destruct Hs as [Hs|Hs]; [|exfalso; apply Hn; right; exact Hs].
      split; [unfold VR_K in *; lia|]. unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT, VR_K in *. lia.
    + intros a k i Hin Hx Hi.
      assert (Hno : ~ In (a, k) O0) by (intros Ho; apply Hx; apply in_map_iff; exists (a, k); split; [reflexivity | exact Ho]).
      destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H (a, k) Hin Hno) as [Hin1 Hno1].
      exact (proj2 (SURV (a, k) Hin1 Hno1) i Hi).
  - exact HREC.
  - exact RO2.
  - exact INIT.
  - split; [exact RES | exact HKB].
  - intros pn Hin Hno. destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H pn Hin Hno) as [H1 H2].
    split; [exact (proj1 (SURV pn H1 H2)) | exact (NO2 pn H1 H2)].
  - intros pn Hin. destruct (BLK pn Hin) as [[H1 H2]|[H1|H1]].
    + destruct (t_sub _ _ _ _ _ _ _ _ _ _ _ H pn H1) as [H3|[H3|H3]];
        [left; exact H3 | exfalso; exact (H2 H3) | right; right; apply in_or_app; left; exact H3].
    + right. left. exact H1.
    + right. right. apply in_or_app. right. exact H1.
  - intros pn Hp. apply in_app_or in Hp as [Hp|Hp].
    + destruct (HX pn Hp) as [H1 _]. pose proof (XNO pn Hp) as H3.
      pose proof (proj1 (SURV pn H1 H3)) as H4. split; [exact H4|].
      destruct pn as [a k]. apply (addr_notin L2 A2 mem2 md2 R2 O2 a k HM2 HREC H4);
        [exact (t_xsz _ _ _ _ _ _ _ _ _ _ _ H (a, k) Hp) | exact (NO2 _ H1 H3)].
    + destruct (HNEW pn Hp) as (H1 & H2 & _). split; assumption.
  - intros pn Hp pn' Hin' Hno'. apply in_app_or in Hp as [Hp|Hp];
      [exact (t_xap _ _ _ _ _ _ _ _ _ _ _ H pn Hp pn' Hin' Hno')|].
    destruct (HNEW pn Hp) as (_ & _ & _ & HA). destruct (t_old _ _ _ _ _ _ _ _ _ _ _ H pn' Hin' Hno') as [H1 H2].
    exact (HA pn' H1 H2).
  - rewrite map_app. apply nodup_app_i; [exact (t_xnd _ _ _ _ _ _ _ _ _ _ _ H) | exact NDN|].
    intros a Ha Hb. apply in_map_iff in Ha as (pn1 & E1 & Hp1). apply in_map_iff in Hb as (pn2 & E2 & Hp2).
    destruct (HNEW pn2 Hp2) as (_ & _ & Hs2 & HA). destruct (HX pn1 Hp1) as [H1 _].
    pose proof (t_xsz _ _ _ _ _ _ _ _ _ _ _ H pn1 Hp1) as Hs1.
    destruct (HA pn1 H1 (XNO pn1 Hp1)); lia.
  - intros pn Hp. apply in_app_or in Hp as [Hp|Hp];
      [exact (t_xsz _ _ _ _ _ _ _ _ _ _ _ H pn Hp) | exact (proj1 (proj2 (proj2 (HNEW pn Hp))))].
Qed.

Lemma heap_step_stub : forall rg mem1 md1 L1 A1 R1 O1 k1 xq K L2 A2 rg2 mem2 md2 R2 O2 NEW xq' k2,
  vheap B API S L1 A1 mem1 md1 R1 O1 k1 xq ->
  spZ rg = spf -> 0 <= K <= 14336 ->
  RecKindB.call_post_rec B MR K L1 A1 rg mem1 md1 RecKindB.rec_area (fun a => In a (map fst O1))
    L2 A2 rg2 mem2 md2 ->
  g_rec_rep (ms_segs B) L2 A2 mem2 R2 O2 -> RecKindB.owns_new L1 A1 O1 O2 ->
  (forall pn, In pn (blocks L2 A2) -> (In pn (blocks L1 A1) /\ ~ In pn O1) \/ In pn O2 \/ In pn NEW) ->
  RecKindB.others_kept (ms_segs B) L1 A1 mem1 L2 A2 mem2 O1 ->
  ro_agree (ms_segs B) mem2 -> st_init_done A2 = true ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_n b0 k2) -> (k2 <= 32)%nat ->
  xbl S xq' = xbl S xq ++ NEW ->
  (forall pn, In pn NEW -> In pn (blocks L2 A2) /\ ~ In (fst pn) (map fst O2) /\ 1 <= snd pn /\
     (forall pn', In pn' (blocks L1 A1) -> ~ In pn' O1 -> fst pn + snd pn <= fst pn' \/ fst pn' + snd pn' <= fst pn)) ->
  List.NoDup (map fst NEW) ->
  (match xq' with
   | Some (q, nq, t) => bytes_at rsegs mem2 q (t ++ [Z_to_bv 8 0]) /\ Z.of_nat (length t) + 1 <= nq
   | None => True
   end) ->
  vheap B API S L2 A2 mem2 md2 R2 O2 k2 xq'.
Proof using HF HS.
  intros rg mem1 md1 L1 A1 R1 O1 k1 xq K L2 A2 rg2 mem2 md2 R2 O2 NEW xq' k2 H SPR HK POST HREC OWN BLK OK
    RO2 INIT RLEN RES HKB XQ HNEW NDN HQ.
  destruct (tail_step_stub rg mem1 md1 L1 A1 R1 O1 k1 (xbl S xq) K L2 A2 rg2 mem2 md2 R2 O2 NEW k2
    (h_t _ _ _ _ _ _ _ _ _ _ _ H) SPR HK POST HREC OWN BLK OK RO2 INIT RLEN RES HKB HNEW NDN) as [T KB].
  constructor.
  - rewrite XQ. exact T.
  - apply (KB lb nlb); [left; reflexivity | lia | | exact (h_lb _ _ _ _ _ _ _ _ _ _ _ H)].
    rewrite !length_app, repeat_length. cbn [length]. pose proof (line_le_upto S). unfold s_nlb. lia.
  - eapply Forall2_impl; [|exact (h_tok _ _ _ _ _ _ _ _ _ _ _ H)]. intros p w ((Hb & Hnz) & H1 & H2).
    split; [split; [|exact Hnz]|split; assumption].
    apply (KB cb ncb); [right; left; reflexivity | exact H1 | | exact Hb].
    rewrite length_app. cbn [length]. lia.
  - exact HQ.
Qed.

End Step.
