(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the facts sup_chain's assembly (lib/A/Prog/sup_chain_s8.v) carries from
   one segment of the ASan walk to the next: the member array's bytes and shadow at a later state of the walk,
   the text block's write permission, and the recorder's representation across the loop.  Written after
   lib/A/Prog/sup_chain.v (segment A) and lib/A/Prog/sup_chain_s6.v (the tail segment). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaArt
PaLibF PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c xstrdup_c rec_shape_of_c answer_c sup_chain_c RecBLemmas
sup_chain_s1 sup_chain_s2 sup_chain_s3 sup_chain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis HB : CmdBSyms B.
(* the program's writable statics (the recorder walks' shared form) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.

(* ---------------------------------------------------------------------------------------------------------
   The caller's member array.  sup_chain's statement puts it either in a side-stack frame (chain_words' ids[64],
   `afobj`) or in a live block apart from every block the recorder owns.  The walk reads it in the loop, at a
   state the journal relates to the entry.  Both arms keep their bytes and their shadow: a byte of a frame or of
   a kept block is none of the walk's footprint (g_rec, record.spill and the recorder's blocks: image bytes and
   blocks the call frees), and the journal keeps exactly those.  --------------------------------------------- *)

(* no byte of a live block or of a live frame is a byte of g_rec or record.spill *)
Lemma sc7_client_apart : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md ->
((exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
 (exists cid pos, In (cid, pos) (frames S) /\
    frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid)) ->
~ (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof.
intros ly S W mem md a HAR Hc Hrec.
assert (Himg : in_img SEGS a).
{ apply cmd_prog_img. destruct Hrec as [Ha | Ha]; [apply recb_grec_in | apply recb_spill_in]; exact Ha. }
destruct Hc as [Hb | Hf].
- exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl Hb)) Himg).
- exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_intror (or_introl Hf))) Himg).
Qed.

(* a byte of the member array is none of the walk's footprint *)
Lemma sc7_arr_out_fp : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) pids nids a,
AR SEGS B ly S W mem md ->
(afobj SEGS B ly S W mem pids nids \/
 (in_blockA (ablocks B ly S) pids nids /\
  Forall (fun qk => iv_apart pids nids (fst qk) (snd qk)) O)) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
pids <= a < pids + nids -> 0 <= nids ->
~ inFP (sc_FP O) a.
Proof.
intros ly S W mem md O pids nids a HAR Harr HOin Ha Hn Hfp.
unfold sc_FP in Hfp. destruct Hfp as (r & Hr & Hra).
(* the client side of the array: a live frame, or a live block *)
assert (Hcl : (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
              (exists cid pos, In (cid, pos) (frames S) /\
                 frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid)).
{ destruct Harr as [Hfo | [(pb & nb & Hin & Hlo & Hhi) _]].
  - destruct Hfo as ((cid & pos & Hfin & _ & _ & Hlo & Hhi) & _ & _).
    right. exists cid, pos. split; [exact Hfin | lia].
  - destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnb).
    pose proof (req_size_pos nb ltac:(lia)) as [_ Hrb].
    left. exists pb, nb. split; [exact Hin | lia]. }
destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Hra. exact (sc7_client_apart ly S W mem md a HAR Hcl (or_introl Hra)).
- cbn [fst snd] in Hra. exact (sc7_client_apart ly S W mem md a HAR Hcl (or_intror Hra)).
- (* a block the recorder owns: the array is apart from it (the block arm), or the array is in a frame *)
  destruct (inFP_ablocks_fp_inv O a ltac:(exists r; split; [exact Hr | exact Hra]))
    as (q & nq & Hin & Hra2).
  destruct Harr as [Hfo | [Harr2 HF]].
  + destruct Hfo as ((cid & pos & Hfin & _ & _ & Hlo & Hhi) & _ & _).
    pose proof (sep_block_frame SEGS B LAWS ly S W mem md q nq cid pos HAR (HOin (q, nq) Hin) Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  + (* the array is in a block of its own, which the apartness premise tells from the recorder's; the
       recorder's block's footprint is its rounded size, so the two are told apart by the record's
       separation of blocks, not by the premise alone *)
    destruct Harr2 as (pb & nb & Hinb & Hlob & Hhib).
    pose proof (proj1 (Forall_forall _ _) HF (q, nq) Hin) as Hap. cbn [fst snd] in Hap.
    destruct (al_blocks _ _ LAWS ly S W mem md q nq HAR (HOin (q, nq) Hin))
      as (_ & _ & _ & _ & _ & _ & Hnq).
    destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hinb) as (_ & _ & _ & _ & _ & _ & Hnb).
    pose proof (req_size_pos nq ltac:(lia)) as [_ Hrq].
    pose proof (req_size_pos nb ltac:(lia)) as [_ Hrb].
    unfold iv_apart in Hap.
    assert (Hne : (pb, nb) <> (q, nq)) by (intros Hx; injection Hx as <- <-; lia).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md pb nb q nq HAR Hinb (HOin (q, nq) Hin) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the member array's bytes, at a state the walk's journal relates to the entry *)
Lemma sc7_arr_bytes : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' W' mem' md' k pids nids,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (sc_FP O) ly S W mem md own ly' S' W' mem' md' k ->
(afobj SEGS B ly S W mem pids nids \/
 (in_blockA (ablocks B ly S) pids nids /\
  Forall (fun qk => iv_apart pids nids (fst qk) (snd qk)) O)) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) ->
0 <= nids ->
forall a, pids <= a < pids + nids -> rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k pids nids HAR HJ Harr HOin HKEEP Hn a Ha.
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & F2 & _ & F4 & _).
pose proof (sc7_arr_out_fp ly S W mem md O pids nids a HAR Harr HOin Ha Hn) as Hnf.
destruct Harr as [Hfo | [(pb & nb & Hin & Hlo & Hhi) HF]].
- (* the array is in a live frame: the journal keeps every byte of a frame it does not name *)
  destruct Hfo as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
  apply (F4 cid pos a Hfin); [| exact Hnf].
  left. unfold frame_rng, in_zr. cbn [fst snd]. lia.
- (* the array is in a live block that the call keeps *)
  destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnb).
  pose proof (req_size_pos nb ltac:(lia)) as [_ Hrb].
  assert (HnO : ~ In (pb, nb) O).
  { intros HbO. pose proof (proj1 (Forall_forall _ _) HF (pb, nb) HbO) as Hap. cbn [fst snd] in Hap.
    unfold iv_apart in Hap. lia. }
  replace a with (pb + (a - pb)) by lia.
  apply (F2 pb nb (a - pb) Hin (HKEEP (pb, nb) Hin HnO) ltac:(lia)).
  replace (pb + (a - pb)) with a by lia. exact Hnf.
Qed.

(* the member array's shadow, at the same later state: in the block arm the block itself is still live, so the
   record gives it; in the frame arm the journal keeps the frame's shadow bytes, which it does not name *)
Lemma sc7_arr_shadow : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' W' mem' md' k pids nids,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (sc_FP O) ly S W mem md own ly' S' W' mem' md' k ->
(afobj SEGS B ly S W mem pids nids \/
 (in_blockA (ablocks B ly S) pids nids /\
  Forall (fun qk => iv_apart pids nids (fst qk) (snd qk)) O)) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) ->
0 < nids ->
range_addressable (rdW W' mem') SHADOW_OFF pids nids.
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k pids nids HAR HJ Harr HOin HKEEP Hn.
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & F2 & _ & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Harr as [Hfo | [(pb & nb & Hin & Hlo & Hhi) HF]].
- (* the frame arm: the entry's range_addressable, carried byte by byte *)
  destruct Hfo as (Hfr & Hal & HRA).
  destruct Hfr as (cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi).
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & _).
  intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [| exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  assert (Hxb : frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid) by lia.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  (* the frame starts at a multiple of 32, so the shadow byte of x is the frame's shadow byte number
     (x - frame_addr) / 8 *)
  destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hfin) as (Hfa64 & Hfb64 & Hfb_lo).
  assert (Hm0 : frame_addr ly cid pos mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 64); [exists 8; lia|].
    apply Z.mod_divide; [lia | exact Hfa64]. }
  assert (Hb0 : 8 * (fs_frame_bytes cid / 8) = fs_frame_bytes cid).
  { assert (Hd8 : fs_frame_bytes cid mod 8 = 0)
      by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans 8 64); [exists 8; lia|];
          apply Z.mod_divide; [lia | exact Hfb64]).
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)). lia. }
  assert (Hgen : forall f d, f mod 8 = 0 -> (f + d) / 8 = f / 8 + d / 8).
  { intros f d Hf. replace f with (f / 8 * 8) at 1 by (pose proof (Z.div_mod f 8 ltac:(lia)); lia).
    rewrite (Z.div_add_l (f / 8) 8 d ltac:(lia)). reflexivity. }
  assert (Hxd : x / 8 = frame_addr ly cid pos / 8 + (x - frame_addr ly cid pos) / 8)
    by (rewrite <- (Hgen (frame_addr ly cid pos) (x - frame_addr ly cid pos) Hm0); f_equal; lia).
  assert (Hdiv : 0 <= (x - frame_addr ly cid pos) / 8 < fs_frame_bytes cid / 8).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia | lia]. }
  apply (F4 cid pos (SHADOW_OFF + x / 8) Hfin).
  + right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
  + (* the shadow byte of a frame is none of the walk's footprint: the footprint is image bytes and live
       blocks, both of them application addresses, and a shadow byte is not one *)
    intros Hfp.
    assert (Hsb : kLowMemEnd <= SHADOW_OFF + x / 8 < kHighShadowEnd).
    { pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd in *; lia)) as Hb.
      unfold shadow_addr in Hb. lia. }
    unfold sc_FP in Hfp. destruct Hfp as (r & Hr & Hra).
    destruct Hr as [<- | [<- | Hr]].
    * cbn [fst snd] in Hra. unfold A_G_REC, REC_SIZE, kLowMemEnd in *. lia.
    * cbn [fst snd] in Hra. unfold A_REC_SPILL, SC_SIZE, kLowMemEnd in *. lia.
    * destruct (inFP_ablocks_fp_inv O (SHADOW_OFF + x / 8)
                  ltac:(exists r; split; [exact Hr | exact Hra])) as (q & nq & Hq & Hra2).
      destruct (al_blocks _ _ LAWS ly S W mem md q nq HAR (HOin (q, nq) Hq))
        as (_ & _ & _ & Hiap & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *. lia.
- (* the block arm: the block is still live, so the record gives its shadow *)
  destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnb).
  pose proof (req_size_pos nb ltac:(lia)) as [_ Hrb].
  assert (HnO : ~ In (pb, nb) O).
  { intros HbO. pose proof (proj1 (Forall_forall _ _) HF (pb, nb) HbO) as Hap. cbn [fst snd] in Hap.
    unfold iv_apart in Hap. lia. }
  exact (range_addressable_of_block SEGS B LAWS ly' S' W' mem' md' pb nb pids nids
           HAR' (HKEEP (pb, nb) Hin HnO) ltac:(lia) ltac:(lia)).
Qed.

(* the bytes of g_rec and record.spill *)
Definition sc7_rec (a : Z) : Prop :=
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.

(* the recorder's representation survives any change outside g_rec, record.spill and its own blocks
   (lib/A/Prog/sup_chain_s6.v's sc6_repA_keep, here for the assembly's loop step) *)
Lemma sc7_repA_keep : forall ly1 S1 rd ly2 S2 rd' R O,
rec_repA B ly1 S1 rd R O ->
(forall a, sc7_rec a -> rd' a = rd a) ->
(forall pn, In pn O -> In pn (ablocks B ly2 S2) /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
rec_repA B ly2 S2 rd' R O.
Proof.
intros ly1 S1 rd ly2 S2 rd' R O (Q & HQ & HO) KG KB.
assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly2 S2) /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros pn Hpn; apply KB; apply HO; exact Hpn).
exists Q. split; [|exact HO].
destruct HQ as (H1 & H2 & H3 & HC & HAn & HRe & HSc & HOw).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|split; [|split; [|split]]].
- unfold ag1_calls. split; [exact C1|]. split; [exact C2|]. split.
  + apply (sc3_aval_keep rd); [exact C3|]. intros x Hx. apply KG.
    left. unfold OFF_NCALLS, REC_SIZE in *. lia.
  + split.
    * intros i cc P Ec EP. destruct (C4 i cc P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite EP; discriminate).
      assert (Hi16 : (i < 16)%nat) by lia.
      assert (HPQ : forall pn, In pn P -> In pn (lay_blocks Q)).
      { intros pn Hpn. unfold lay_blocks. apply in_or_app. left. exact (In_concat_nth _ i P pn EP Hpn). }
      apply (sc3_call_keep (ablocks B ly1 S1) _ rd rd' _ cc P Hc).
      -- intros x Hx. apply KG. left. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      -- intros pn Hpn _. exact (proj1 (KQ pn (HPQ pn Hpn))).
      -- intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HPQ pn Hpn)) i' Hi').
    * split.
      -- assert (HSQ : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
         { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
         apply (sc3_call_keep (ablocks B ly1 S1) _ rd rd' _ _ _ C5).
         ++ intros x Hx. apply KG. right. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
         ++ intros pn Hpn _. exact (proj1 (KQ pn (HSQ pn Hpn))).
         ++ intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HSQ pn Hpn)) i' Hi').
      -- exact C6.
- assert (HAQ : forall pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  apply (sc3_answer_keep (ablocks B ly1 S1) _ rd rd' _ _ _ HAn).
  + intros x Hx. apply KG. left. unfold OFF_ANSWER, REC_SIZE in *. lia.
  + intros pn Hpn _. exact (proj1 (KQ pn (HAQ pn Hpn))).
  + intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HAQ pn Hpn)) i' Hi').
- assert (HRQ : forall pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  apply (sc3_reply_keep (ablocks B ly1 S1) _ rd rd' _ _ _ HRe).
  + intros x Hx. apply KG. left. unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
  + intros pn Hpn _. exact (proj1 (KQ pn (HRQ pn Hpn))).
  + intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HRQ pn Hpn)) i' Hi').
- apply (sc3_scalars_keep rd); [exact HSc|]. intros x Hx. apply KG. left.
  unfold OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *. lia.
- exact HOw.
Qed.

(* the three blocks the join-to-loop segment names (the two recorded numbers and the list text) are three
   blocks of their own: the record's live blocks are distinct *)
Lemma sc7_perm_apart : forall ly' S' (W' : world SEGS) mem' md' (x y z : Z * Z) L,
AR SEGS B ly' S' W' mem' md' ->
Permutation (ablocks B ly' S') (x :: y :: L ++ [z]) ->
~ In x L /\ ~ In y L /\ ~ In z L /\ x <> y /\ x <> z /\ y <> z.
Proof.
intros ly' S' W' mem' md' x y z L HAR HP.
pose proof (Permutation_NoDup HP (recb_ablocks_nodup_m B ly' S' W' mem' md' HAR)) as ND.
apply List.NoDup_cons_iff in ND as [Hx ND].
apply List.NoDup_cons_iff in ND as [Hy ND].
assert (Hzl : ~ In z L)
  by (intros Hz; exact (list_nodup_app_disj L [z] z ND Hz (or_introl eq_refl))).
split; [intros H; apply Hx; right; apply in_or_app; left; exact H|].
split; [intros H; apply Hy; apply in_or_app; left; exact H|].
split; [exact Hzl|].
split; [intros <-; apply Hx; left; reflexivity|].
split; [intros <-; apply Hx; right; apply in_or_app; right; left; reflexivity|].
intros <-. apply Hy. apply in_or_app. right. left. reflexivity.
Qed.

End e.
End f.
End d.
