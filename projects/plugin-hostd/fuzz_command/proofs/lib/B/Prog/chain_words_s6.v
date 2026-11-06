(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the last segment of the walk of chain_words (0x8da84) on the ASan+UBSan build
   of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan): cw_S6 of lib/B/Prog/chain_words_d.v, from the join
   after the recorder call (KJ, +0x2fc = 0x8dd80) to the return (+0x498 = 0x8df1c), 60 instructions on the path
   (the real-stack release +0x3a8..+0x454, 44 instructions, is dead). The B twin of lib/A/Prog/chain_words_s6.v
   (a working branch 5e2cdad423e): B's code here is A's from A +0x2b0 shifted by +0x4c.

   What the code does there: the recorder's answer is in s4 already, it poisons the shadow of ids[64] with 0xf8
   (32 byte stores through s2 = the frame's shadow), writes the frame's magic word at frame + 0 (through s6),
   takes the side-stack branch (s3 = the frame <> 0), refills the whole 64-byte shadow of the frame with 0xf5
   through __asan_set_shadow_f5(s2, 64), releases the frame by storing 0 through frame[504] (its flag, loaded
   through s3), restores a0 = s4, sp = s0 - 160 and ra, s0..s11 from their slots, and returns.

   What B changes against A here: the frame is 160 bytes (A 128), so the realigned sp is sp0 - 160 or sp0 - 176;
   the class-3 frame is in s3 and s6 (A: s3 and s8); the text pointer is in s4 at KJ (cw_QJ = cw_Qr 20), and the
   epilogue's `mv a0,s4` makes it a0 (cw_Q = cw_Qr 10); the post is apost_baseF, at the segment's own FP state
   (S6 makes no call that changes it: PaFx.v's apost_baseF_of_base over the apost_base the walk builds).

   The walk: one symbolic run from KJ to the shadow-fill call (PaCallRun.v's SRr_run_pi_AJ_call), the call
   step aj_set_shadow_atS (below), a re-seat of the symbolic state over the call (PaLibH.v's
   jafter_call_keep_hi) that rebuilds the three regions the release reads and writes, one run from the
   return of the fill to the ret under PaLibF.v's aj_flag_store_pi (which turns the flag store into the
   frame's release: own [(3, fpos)] -> [] and S3 -> stack_free_state 3 fpos S3), and CmdPaLib.v's
   paj_ret_at. The post is the entry journal again, with its count raised to EV_CHAIN_WORDS (ajournal_mono_k)
   and the registers of the entry restored from their slots, and cw_Q carried over the release: the release
   writes only the frame's magic word, the frame's shadow and the flag byte, which are apart from g_rec and
   record.spill (image bytes, by PROG_UNOWNED) and from every live block (AR's block laws), so rec_repA and
   astr_atR cross it (rec_repA_agree / astr_atR_agree below); the release keeps the blocks, so
   4096 <= p < 2 ^ 64, the block facts and the live-byte bound carry over unchanged, and the meter crosses
   stack_free_state by MTFL. *)
(* the environment of the two copied blocks below (the imports their sources compiled under) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the recorder representation under a memory that agrees on what it reads: copied verbatim from the walk
   of reply, lib/A/Prog/reply_s1.v:27-171 of a working branch (commit 0fd6ef0ba2f) ---- *)
Lemma aval_mem_agree : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.
Lemma abytes_atR_agree : forall (rd rd' : reader) p l n,
abytes_atR rd p l -> Z.of_nat (length l) <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l n H Hle Hk i Hi. rewrite Hk by lia. exact (H i Hi). Qed.
Lemma astr_atR_agree : forall (rd rd' : reader) p s n,
astr_atR rd p s -> Z.of_nat (length s) + 1 <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s n [Hb Hn0] Hle Hk. split; [|exact Hn0].
apply (abytes_atR_agree rd rd' p _ n Hb); [rewrite length_app; cbn [length]; lia | exact Hk].
Qed.
Lemma acall_at_agree : forall bl bl' rd rd' a c P,
acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < 8 + 8 * Z.of_nat (length P) -> rd' (a + k) = rd (a + k)) ->
(forall pn, In pn P -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & Hfn & Hna & Hnd & Hargs) HB HR HS.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_agree rd rd' _ 4 _ Hfn); intros k Hk; unfold CALL_OFF_FN; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 0 + k) with (a + k) by lia; apply HR; lia|].
split; [apply (aval_mem_agree rd rd' _ 4 _ Hna); intros k Hk; unfold CALL_OFF_NARGS; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 4 + k) with (a + (4 + k)) by lia; apply HR; lia|].
split; [exact Hnd|].
intros k s pn Hs Hpn. destruct (Hargs k s pn Hs Hpn) as (A1 & A2 & A3 & A4 & A5).
assert (Hk : (k < length P)%nat) by (apply nth_error_Some; rewrite Hpn; discriminate).
pose proof (nth_error_In _ _ Hpn) as HinP.
split; [|split; [exact A2|split; [exact (HB pn HinP A3)|split; [exact A4|]]]].
- apply (aval_mem_agree rd rd' _ 8 _ A1). intros kk Hkk. unfold CALL_OFF_ARGS. change (Z.of_nat 8) with 8 in Hkk.
  replace (a + 8 + 8 * Z.of_nat k + kk) with (a + (8 + 8 * Z.of_nat k + kk)) by lia. apply HR. lia.
- apply (astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HS pn HinP).
Qed.
Lemma in_lay_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn Hi Hp. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hi) | exact Hp].
Qed.
Lemma in_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma in_lay_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite H. left. reflexivity. Qed.
Lemma in_lay_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite H. left. reflexivity. Qed.
Lemma arep_at_agree : forall bl bl' rd rd' gr sc R Q,
arep_at bl rd gr sc R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < REC_SIZE -> rd' (gr + k) = rd (gr + k)) ->
(forall k, 0 <= k < SC_SIZE -> rd' (sc + k) = rd (sc + k)) ->
(forall pn, In pn (lay_blocks Q) -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
arep_at bl' rd' gr sc R Q.
Proof.
intros bl bl' rd rd' gr sc R Q (Hg8 & Hs8 & Hap & HC & HA & HR & HSc & HOwn) HB HG HSP HO.
assert (VG : forall off n v, aval_mem rd (gr + off) n v -> 0 <= off -> off + Z.of_nat n <= REC_SIZE -> aval_mem rd' (gr + off) n v).
{ intros off n v H H0 H1. apply (aval_mem_agree rd rd' _ n _ H). intros k Hk.
  replace (gr + off + k) with (gr + (off + k)) by lia. apply HG. lia. }
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|]. split; [apply VG; [exact C3 | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, REC_SIZE; cbn; lia]|].
  split; [|split; [|exact C6]].
  - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [A F]. split; [|exact F].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    pose proof A as (_ & Hn6 & HlP & _).
    apply (acall_at_agree bl bl' rd rd' _ c P A).
    + intros pn Hpn. apply HB. exact (in_lay_calls Q i P pn HP Hpn).
    + intros k Hk. replace (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + k) with (gr + (OFF_CALLS + CALL_SIZE * Z.of_nat i + k)) by lia.
      apply HG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (in_lay_calls Q i P pn HP Hpn).
  - pose proof C5 as (_ & Hn6 & HlP & _). apply (acall_at_agree bl bl' rd rd' _ _ _ C5).
    + intros pn Hpn. apply HB. exact (in_lay_spill Q pn Hpn).
    + intros k Hk. apply HSP. unfold SC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (in_lay_spill Q pn Hpn). }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|] eqn:Ea, (l_answer Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HA as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply VG; [exact A1 | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]|].
    split; [exact A2|]. split; [exact (HB pn (in_lay_answer Q pn Eq) A3)|]. split; [exact A4|]. split; [|exact A6].
    apply (astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HO pn (in_lay_answer Q pn Eq)).
  - apply VG; [exact HA | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|] eqn:Ea, (l_reply Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply VG; [exact A1 | unfold OFF_REPLY; lia | unfold OFF_REPLY, REC_SIZE; cbn; lia]|].
    split; [apply VG; [exact A2 | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, REC_SIZE; cbn; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HB pn (in_lay_reply Q pn Eq) A5)|]. split; [exact A6|]. split; [|exact A8].
    apply (abytes_atR_agree rd rd' _ _ (snd pn) A7); [lia|]. exact (HO pn (in_lay_reply Q pn Eq)).
  - destruct HR as [A1 A2].
    split; apply VG; first [exact A1 | exact A2 | unfold OFF_REPLY, OFF_REPLY_SIZE; lia | unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE; cbn; lia]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & REST).
split; [apply VG; [exact S1 | unfold OFF_REFUSE; lia | unfold OFF_REFUSE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S2 | unfold OFF_CODE; lia | unfold OFF_CODE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S3 | unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S4 | unfold OFF_STATE; lia | unfold OFF_STATE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S5 | unfold OFF_HOST; lia | unfold OFF_HOST, REC_SIZE; cbn; lia] | exact REST].
Qed.
Lemma lay_blocks_in_bl : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HR & _) Hin.
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  destruct HC as (C1 & C2 & _ & C4 & _).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_Some in Hi'; contradiction].
  destruct (C4 i c P Hc Hi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
  exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HC as (_ & _ & _ & _ & (_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
    exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in HA. destruct (l_answer Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R); [exact (proj1 (proj2 (proj2 HA))) | contradiction].
    * unfold areply_at in HR. destruct (l_reply Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R); [exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))) | contradiction].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
Section e.
Variable B : asyms.
Lemma rec_repA_agree : forall ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
(forall k, 0 <= k < REC_SIZE -> rd' (A_G_REC + k) = rd (A_G_REC + k)) ->
(forall k, 0 <= k < SC_SIZE -> rd' (A_REC_SPILL + k) = rd (A_REC_SPILL + k)) ->
(forall pn, In pn O -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S ly' S' rd rd' R O (Q & HA & HOQ) HB HG HS HO. exists Q. split; [|exact HOQ].
apply (arep_at_agree _ _ rd rd' _ _ R Q HA).
- intros pn Hpn Hbl. apply HB; [apply HOQ; exact Hpn | exact Hbl].
- exact HG. - exact HS.
- intros pn Hpn. apply HO. apply HOQ. exact Hpn.
Qed.
Lemma rec_repA_in_blocks : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HA & HOQ) Hpn. apply (lay_blocks_in_bl _ rd _ _ R Q pn HA). apply HOQ. exact Hpn. Qed.
End e.
End f.
End d.

(* ---- the journal step of the shadow-fill entry __asan_set_shadow_f5: copied verbatim from
   lib/A/Prog/PaRt.v:52-244 of a working branch (commit 474a8f474e6, the walk of
   check_words_chain on the same base): ajournal_after_write_stk (YCbq.v's ajournal_after_write with the
   presence premise narrowed to the journal's own stack window, which is all the shadow-fill contract gives)
   and aj_set_shadow_atS (the call step, on the model of PaCall.v's aj_intrin_atS) ---- *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma ajournal_after_write_stk : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal segs B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof using LAWS segs_low.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
(~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))) \/
(inFP FP a /\ in_img segs a) \/
(inFP FP a /\ ly_stk_lo lyc <= a < ly_stk_hi lyc) \/
(inFP FP a /\ exists cid pos, In (cid, pos) (frames Sc) /\
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx];
[left; exact (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs Hnf. rewrite <- (F1 a Ha Hs Hnf). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | [(cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (_ & Hx)];
[exact (Hs Hs') | zlia | zlia | zlia | exact (Hnf Hf') | exact (Hnf Hf') | exact (Hnf Hf') | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx)].
- zlia.
- exact (Hnf Hfp).
-
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
- exact (Hnf Hf').
- exact (Hnf Hf').
- exact (Hnf Hf').
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]]) | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (proj2 Hsp Hf').
- exact (proj2 Hsp Hf').
- exact (proj2 Hsp Hf').
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | [(c' & p' & Hown & Hr') | [(Hf' & _) | [(Hf' & _) | (Hf' & _)]]]]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos segs B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (shadow_mono _ _ Hd). zlia.
* pose proof (shadow_mono _ _ Hd). zlia.
- exact (Hnf Hf').
- exact (Hnf Hf').
- exact (Hnf Hf').
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [exact Hgr|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | [(cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]]) | [(_ & Hi') | [(_ & Hst) | (_ & c2 & p2 & Hin2 & Hr2)]]]]]) | (Hxo & Hx)].
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xi Hi').
- exact (Xs Hst).
- destruct Hr2 as [Hr2 | Hr2]; unfold in_zr, frame_rng in Hr2; cbn [fst snd] in Hr2;
[exact (proj1 (Xf c2 p2 Hin2) Hr2) | exact (proj2 (Xf c2 p2 Hin2) Hr2)].
- exact (Xo Hxo). }
Qed.

(* __asan_set_shadow_XX(q, n): fills [q, q + n) with v. The range lies in the shadow of a frame (cid, pos) the
   walk holds (In (cid, pos) own), which the journal lets it write. *)
Lemma aj_set_shadow_atS : forall pc v, RtShadow.aset_shadow_realizes segs B pc v ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof using LAWS segs_low.
intros pc v AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Hq Hn Hn0 Hlo Hhi Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR HinC) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
eapply SRr_mono; [exact (AS lyc Sc W regsT memT mdc cid pos q n HPRE HinC Hq Hn Hn0 Hlo Hhi)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hfill & Hkeep & Hwin).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_stk STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => q <= a < q + n) Sc own HJ).
- exact Hkeep.
- intros a Ha. eapply (apresent_transfer segs);
[zlia | intros Him; pose proof (segs_low a Him); zlia | apply Hkeep; zlia | apply Hpres; exact Ha].
- exact Hsame.
- intros a Ha. cbv beta in Ha. left. unfold awr_byte. right; right; right; left. unfold in_frames. exists cid, pos.
split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hfill|]. split; [exact Hkeep|].
split; [intros a Ha; apply Hwin; rewrite Hsp'; exact Ha | exact Hsame].
Qed.
End e.
End c.

(* the environment of the walk *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
number_c sup_chain_c sup_resp_c chain_words_c chain_words_d.
Import ListNotations.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The atoms: registers are 0..31, 32..44 the thirteen registers the prologue saved (in the order of
   cw_saved, so atom 32 + j is the word in slot j, at sp0 - 8 - 8 j), and 45 the frame's flag pointer,
   which the release loads from frame + 504 and stores through. *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition cw6_extra (c : cwx) : list word :=
map (fun r => getr (x_regs c) (Z_to_bv 5 r)) cw_saved ++ [w64 (cw_FL c)].

(* the frame (base s6, x22), with the window of the magic word (frame + 0) and the chunk the release reads
   (frame + 504) *)
Definition cw6_frame : YP09.region :=
YP09.mkRegion (Some 22%nat) 0 512 0 8 [YP09.mkChunk 504 (CVal 8 (SOff 45 0))].
(* the frame's shadow, with the window of the 0xf8 fill (shadow + 4 .. shadow + 36) *)
Definition cw6_shadow : YP09.region :=
YP09.mkRegion (Some 18%nat) 0 64 4 36 [].
(* after the fill: the frame is read only, and only its flag word is read *)
Definition cw6_frame_ro : YP09.region :=
YP09.mkRegion (Some 22%nat) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 45 0))].
(* the flag byte, the one byte the release writes *)
Definition cw6_flag : YP09.region := YP09.mkRegion (Some 45%nat) 0 1 0 1 [].
(* the thirteen saved registers in their slots, below s0 = sp0; the release only reads them *)
Definition cw6_stack : YP09.region :=
YP09.mkRegion (Some 8%nat) (-104) 0 0 0
[YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].

(* the frame is not the null pointer, which decides the branch `beqz s3` at 0x8de10 *)
Definition cw6_facts : facts := mkFacts [(22%nat, mkAF 4096 140737488355328 0)] [] [].
Definition ss_cw6 : sstate := mkSS CW_KJ sr_atoms [cw6_frame; cw6_shadow] None cw6_facts.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SHF5 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
Hypothesis PROG_UNOWNED : cw_prog_unownedP B.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PI := PI).

Lemma cw_S6 : cw_S6P B MT.
Proof.
unfold cw_S6P, from_KJ, cw_from.
intros c HPRE ly3 S3 W3 regs3 mem3 md3 HINV.
destruct HINV as (kj & Hkj & HFI & Hs3 & Hs6 & HQ).
destruct HFI as [HJ Hsp Hgp Htp Hs0 Hs1 Hs2 HsSB Hntok Hsaved Hflag].
destruct HPRE as [HAFN HROD HA0 HTOK64 HA1 HTOKOBJ HTOKS HCB HCBO HNTOK HNTOKR HVERB
HREC HREFUSE HCALLS HRO HVOBJS HFRAMES HNEV HLIVE HMETER].
pose proof HAFN as (HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
assert (HstkC : astk_ok CHAIN_WORDS_STK (x_ly c) (cw_sp0 c)) by exact Hstk0.
pose proof HstkC as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the frame (160) and the realignment (16) above ESTACK, the shadow fill's budget *)
assert (HSTK : 4272 <= CHAIN_WORDS_STK) by (vm_compute; discriminate).
(* the frame and its flag, at the layout of the cut *)
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & Hly3 & _ & _ & _ & Hfrs3 & _).
assert (Hfin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EFA : frame_addr ly3 3 (x_fpos c) = cw_F c).
{ unfold cw_F, frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (EFL : flag_addr ly3 3 (x_fpos c) = cw_FL c).
{ unfold cw_FL, flag_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (cw_s1_facts c Hsp0al) as (Hs1al & Hs1cases).
set (F := cw_F c) in *. set (FL := cw_FL c) in *.
set (sp0 := cw_sp0 c) in *. set (s1v := cw_s1 c) in *.
(* the frame's bounds, its bytes and its shadow bytes *)
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 Hfin3) as (HF4096 & HFceil & HFapp).
rewrite EFA in HF4096, HFceil, HFapp. change (fs_frame_bytes 3) with 512 in HF4096, HFceil, HFapp.
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 Hfin3) as HFimg.
rewrite EFA in HFimg. change (fs_frame_bytes 3) with 512 in HFimg.
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 Hfin3) as (_ & _ & HFpres & HFSpres).
rewrite EFA in HFpres, HFSpres. change (fs_frame_bytes 3) with 512 in HFpres, HFSpres.
change (512 / 8) with 64 in HFSpres.
destruct (FFL ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 Hfin3)
  as (HFLpres & HFLown & (HFLapp & HFLnimg) & (HFL4096 & HFLz & HFLceil)).
rewrite EFL in HFLpres, HFLown, HFLapp, HFLnimg, HFL4096, HFLz, HFLceil.
pose proof (zone2_img _ _ HFLz) as HFLimg. pose proof (zone2_band _ _ HFLz) as HFLband.
(* the frame, its shadow and the flag are three apart ranges; the frame is either below the low shadow or
   above the high shadow, and the shadow of any address below the allocator's ceiling is below high memory *)
set (q := SB + F / 8) in *.
assert (HqF : q = shadow_addr F) by (unfold q, shadow_addr, SB, SHADOW_OFF; reflexivity).
assert (Hdiv8 : 140737479966720 / 8 = 17592184995840) by reflexivity.
assert (Hq1 : 2147451392 <= q).
{ pose proof (Z.div_le_mono 4096 F 8 ltac:(lia) ltac:(lia)) as Hd.
  change (4096 / 8) with 512 in Hd. unfold q, SB. lia. }
assert (Hq2 : q + 64 <= 17594332446784).
{ pose proof (Z.div_le_mono F 140737479966720 8 ltac:(lia) ltac:(lia)) as Hd.
  rewrite Hdiv8 in Hd. unfold q, SB. lia. }
assert (HFq : F + 512 <= q \/ q + 64 <= F).
{ destruct HFapp as (_ & [Hlo | (Hhi & _)]);
  [left; unfold kLowShadowBeg in Hlo; lia | right; unfold kHighMemBeg in Hhi; lia]. }
assert (HFLq : FL + 1 <= q \/ q + 64 <= FL).
{ destruct HFLband as [Hlo | Hhi]; [left; lia | right; lia]. }
assert (HFLF : FL + 1 <= F \/ F + 512 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt | Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 512)) as [Hlt2 | Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres FL ltac:(lia)) HFLown). }
(* the atoms of the walk: the registers of the cut, the thirteen saved words, and the flag pointer *)
set (E := Eimg (Ereg regs3 (cw6_extra c))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs3 r).
{ intros m r Hm. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (cw6_extra c) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45.
cbn [Nat.add nth map app cw_saved cw6_extra] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45.
assert (E2 : ew E 2 = w64 s1v) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E8 : ew E 8 = w64 sp0) by (rewrite (EE 8%nat 8%bv eq_refl); exact Hs0).
assert (E18 : ew E 18 = w64 q) by (rewrite (EE 18%nat 18%bv eq_refl); exact Hs2).
assert (E19 : ew E 19 = w64 F) by (rewrite (EE 19%nat 19%bv eq_refl); exact Hs3).
assert (E22 : ew E 22 = w64 F) by (rewrite (EE 22%nat 22%bv eq_refl); exact Hs6).
assert (E22u : bv_unsigned (ew E 22) = F) by (rewrite E22; apply unsigned_lit_small; lia).
assert (E18u : bv_unsigned (ew E 18) = q) by (rewrite E18; apply unsigned_lit_small; lia).
assert (E45u : bv_unsigned (ew E 45) = FL) by (rewrite E45; apply unsigned_lit_small; lia).
assert (E8u : bv_unsigned (ew E 8) = sp0) by (rewrite E8; apply unsigned_lit_small; lia).
(* the seed of the executor at the join *)
assert (HS : st_ok_pi SEGS VAL E ss_cw6
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CW_KJ)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cw6. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold cw6_frame, cw6_shadow. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E22u. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ F 504 8 (SOff 45 0) FL);
        [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
        exact (val_mem_of_rdword SEGS _ _ _ _ Hflag).
    + rewrite E18u. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (q + o) with (shadow_addr F + o) by (rewrite HqF; reflexivity).
      exact (proj1 (HFSpres o ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold cw6_frame, cw6_shadow, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E22u, E18u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold facts_ok, cw6_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E22u, Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; lia. }
(* s3 and s6 hold the same frame pointer: give them one atom, so that the load of the flag word at
   frame + 504 through s3 and the magic store through s6 are one region *)
pose proof (ast_ok_pi_set_reg_fp E _ _ (19%bv : bv 5) (SOff 22 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; cbn [ms_regs restrict mkst]; symmetry; exact Hs3)) as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
let v := eval vm_compute in ssx in change ssx with v in HS end.
unfold cfg_at. change (w64 (BASE + CW_KJ)) with (Z_to_bv 64 (BASE + CW_KJ)).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 22%nat) (b := F).
  - reflexivity.
  - exact E22u.
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right. right. right. left. exists 3, (x_fpos c). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
  - eapply awr_ok_cons_gen with (n := 18%nat) (b := q).
    + reflexivity.
    + exact E18u.
    + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
      right. right. right. left. exists 3, (x_fpos c). split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite EFA, <- HqF. change (fs_frame_bytes 3 / 8) with 64. lia.
    + apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
set (mdv1 := mdx) in *; clearbody mdv1 end.
(* the shadow fill: __asan_set_shadow_f5(s2, 64) over the frame's own 64 shadow bytes *)
pmkst HS.
assert (Hc10 : getr (ms_regs ms) 10 = w64 q) by (prreg HS (10%bv : bv 5) R10; rewrite R10; exact E18).
assert (Hc11 : getr (ms_regs ms) 11 = w64 64) by (prreg HS (11%bv : bv 5) R11; rewrite R11; reflexivity).
assert (Hc3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (prreg HS (3%bv : bv 5) R3; rewrite R3; exact E3).
assert (Hc4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (prreg HS (4%bv : bv 5) R4; rewrite R4; exact E4).
(* the return address of `jal __asan_set_shadow_f5` at +0x398: +0x39c = listing offset 0x78f0 *)
assert (Hc1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 30960))
by (prreg HS (1%bv : bv 5) R1; exact R1).
assert (Hs1rng : 0 <= s1v < 2 ^ 64) by lia.
assert (Hc2 : spZ (ms_regs ms) = sp0 + (s1v - sp0)).
{ prreg HS (2%bv : bv 5) R2. unfold spZ. rewrite R2, E2.
  rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ exact (aj_set_shadow_atS SEGS B LAWS pa_segs_low (SIGMA CS___asan_set_shadow_f5) 0xf5 (SHF5 fx)
W3 (ms_regs ms) (ms_mem ms) CHAIN_WORDS_STK sp0 (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
[(3, x_fpos c)] ly3 S3 mdv1 kj 3 (x_fpos c) q 64 (s1v - sp0) (Z_to_bv 64 (BASE + 30960))
HJ ltac:(left; reflexivity) Hc10 Hc11 ltac:(lia)
ltac:(rewrite EFA, <- HqF; lia)
ltac:(rewrite EFA, <- HqF; change (fs_frame_bytes 3 / 8) with 64; lia)
Hc2 ltac:(destruct Hs1cases as [Hcase | Hcase]; rewrite Hcase;
[replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity)
ltac:(lia) ltac:(unfold ESTACK; lia) Hc3 Hc4 Hc1
ltac:(apply ret_ok_codeptr_v; [lia | reflexivity])). }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfill & Hkeep2 & Hsame2).
(* what the run and the fill left alone: everything but the frame's magic word and the frame's shadow *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (q <= a < q + 64) ->
aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H1 H2. rewrite (Hkeep2 a Ha H2). apply aview_eq_of. apply HFr.
  rewrite unsigned_lit_small by lia. intros (r & Hin & Hrg).
  cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
  [rewrite E22u in Hrg | rewrite E18u in Hrg]; lia. }
(* re-seat the symbolic state after the call: the three regions the release needs are rebuilt below *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W3) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (Ec := havoc E 1024 (map (getr regs2) CLOB)) in *.
assert (HEI2 : img_env VAL A_LIM Ec)
by (unfold Ec; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (AG : forall m, (m < 1024)%nat -> ew Ec m = ew E m)
by (intros m Hm; unfold Ec; apply ew_havoc_old; lia).
assert (E22uc : bv_unsigned (ew Ec 22) = F) by (rewrite (AG 22%nat ltac:(lia)); exact E22u).
assert (E45u2 : bv_unsigned (ew Ec 45) = FL) by (rewrite (AG 45%nat ltac:(lia)); exact E45u).
assert (E8u2 : bv_unsigned (ew Ec 8) = sp0) by (rewrite (AG 8%nat ltac:(lia)); exact E8u).
(* the bytes of the frame above its magic word, and the saved slots, read as they did at the join *)
assert (Hsplo : alloc_ceiling + 4272 <= sp0) by lia.
assert (KEEPF : forall a, F + 8 <= a < F + 512 -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; apply KEEP1; [lia | lia | destruct HFq; lia]).
assert (KEEPS : forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; apply KEEP1; lia).
assert (Hflag2 : rdword (aview SEGS (w_H W3) mem2) (F + 504) = Some FL).
{ rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem2) (F + 504));
  [exact Hflag | intros kk Hkk; apply KEEPF; lia]. }
assert (EAT : forall j, (j < 13)%nat -> ew E (32 + j) = getr (x_regs c) (Z_to_bv 5 (nth j cw_saved 0))).
{ intros j Hj. rewrite (EX j ltac:(lia)). unfold cw6_extra.
  do 13 (destruct j as [|j]; [cbn [map nth app cw_saved]; reflexivity|]).
  cbn in Hj. lia. }
(* the three regions of the release: the saved slots, the frame's flag word, the flag byte *)
pose proof (proj1 HJ2) as HAR2.
destruct (FFL ly3 S3 W3 mem2 md2 3 (x_fpos c) HAR2 Hfin3) as (HFLpres2 & _ & _ & _).
rewrite EFL in HFLpres2.
pose proof (st_ok_pi_add_region Ec _ _ cw6_stack HS eq_refl
ltac:(unfold cw6_stack, region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E8u2; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?nn 0))) =>
let j := eval compute in (nn - 32)%nat in
let r := eval compute in (nth j cw_saved 0) in
apply (chunk_ok_val SEGS Ec _ sp0 off 8 (SOff nn 0) (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r))));
[ let Hj := fresh "Hj" in pose proof (EAT j ltac:(cbv; lia)) as Hj;
  cbn [Nat.add nth cw_saved] in Hj; cbn [sv_denot];
  rewrite (AG nn ltac:(cbv; lia)), Hj, Z.add_0_r; reflexivity
| let Hr := fresh "Hr" in pose proof (bv_unsigned_in_range 64 (getr (x_regs c) (Z_to_bv 5 r))) as Hr;
  change (bv_modulus 64) with (2 ^ 64) in Hr; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
| cbn; lia
| let Hv := fresh "Hv" in pose proof (Hsaved j r ltac:(cbv; reflexivity)) as Hv;
  replace (sp0 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn [Z.of_nat]; lia);
  apply val_mem_of_rdword;
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem2) (sp0 - 8 - 8 * Z.of_nat j));
  [exact Hv | intros kk Hkk; apply KEEPS; cbn [Z.of_nat] in *; lia] ] end)
ltac:(cbn [all_disjoint]; exact I)) as HS2.
clear HS. rename HS2 into HS.
pose proof (st_ok_pi_add_region Ec _ _ cw6_frame_ro HS eq_refl
ltac:(unfold cw6_frame_ro, region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E22uc; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
constructor; [|constructor];
apply (chunk_ok_val SEGS Ec _ F 504 8 (SOff 45 0) FL);
[ cbn [sv_denot]; rewrite (AG 45%nat ltac:(lia)), E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
| apply val_mem_of_rdword; exact Hflag2 ])
ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, cw6_stack, cw6_frame_ro;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E22uc, E8u2;
repeat match goal with |- _ /\ _ => split end; try exact I; lia)) as HS2.
clear HS. rename HS2 into HS.
pose proof (st_ok_pi_add_region Ec _ _ cw6_flag HS eq_refl
ltac:(unfold cw6_flag, region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E45u2; split; [lia|]; split; [lia|]; split; [|constructor];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLpres2)
ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, cw6_stack, cw6_frame_ro, cw6_flag;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E22uc, E8u2, E45u2;
repeat match goal with |- _ /\ _ => split end; try exact I; destruct HFLF; lia)) as HS2.
clear HS. rename HS2 into HS.
(* the release: the store of 0 through frame[504] frees the frame (own [(3, fpos)] -> []) *)
paj_run_flag_sh RUNF HS HJ2.
{ lia. }
{ intros a (r & Hin & Hrg). cbn [In ss_mem] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
  unfold cw6_flag, cw6_frame_ro, cw6_stack in Hrg;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
  [ right; rewrite EFL; rewrite E45u2 in Hrg; lia | exfalso; lia | exfalso; lia ]. }
{ lazymatch goal with |- forall msr, st_ok_pi _ _ _ ?ssx _ -> _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  intros msr Hmsr;
  pose proof (st_ok_pi_region_nth Ec ssx msr 0%nat r0 Hmsr ltac:(vm_compute; reflexivity)) as HR end.
  destruct HR as (_ & _ & _ & HC). inversion HC as [|ch chs Hch Hrest]. subst.
  destruct (Hch 0 ltac:(cbn; lia)) as (bb & Hbb & Hmb).
  cbn [YP09.r_base YP09.c_off YP09.c_val cbyte YP09.c_len base_val] in Hbb, Hmb.
  rewrite EFL. rewrite E45u2 in Hmb.
  replace (FL + 0 + 0) with FL in Hmb by lia. rewrite Hmb. f_equal.
  cbn in Hbb. injection Hbb as <-. reflexivity. }
(* what the release changed: the frame's magic word, the frame's shadow and the flag byte; nothing the recorder
   or the returned text reads *)
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
set (mdv2 := mdx) in *; clearbody mdv2; set (msF := msx) in *; clearbody msF end.
lazymatch goal with H : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ => rename H into HFr4 end.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> FL ->
aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hne. apply aview_eq_of. apply HFr4.
  rewrite unsigned_lit_small by lia. intros (r & Hin & Hrg). cbn [In ss_mem] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
  unfold cw6_flag, cw6_frame_ro, cw6_stack in Hrg;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
  [ rewrite E45u2 in Hrg; lia | lia | lia ]. }
assert (KEEPALL : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (q <= a < q + 64) -> a <> FL ->
aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H1 H2 H3. rewrite (KEEP2 a Ha H3). exact (KEEP1 a Ha H1 H2). }
(* image bytes and live block bytes are apart from the frame, its shadow and the flag *)
assert (SEPI : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ (F <= a < F + 8) /\ ~ (q <= a < q + 64) /\ a <> FL).
{ intros a Hi. pose proof (pa_img_range a Hi) as Hr. unfold off_img in HFimg, HFLimg.
  split; [lia|]. split; [lia|]. split; [lia|]. intros ->. lia. }
assert (SEPB : forall p n a, In (p, n) (ablocks B ly3 S3) -> p <= a < p + req_size n ->
0 <= a < 2 ^ 64 /\ ~ (F <= a < F + 8) /\ ~ (q <= a < q + 64) /\ a <> FL).
{ intros p n a Hin Ha.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 p n HAR3 Hin) as (_ & Hp4096 & Hpceil & Happ & Hpa & _ & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 p n 3 (x_fpos c) HAR3 Hin Hfin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 3) with 512 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros ->. exact (proj2 (Hpa FL Ha) HFLown). }
(* the return: ra, sp and s0..s11 from their slots, a0 = s4 = the recorder's answer; S6 calls nothing that
   changes the FP state, so the post is apost_baseF at the segment's own fx (fx' := fx) *)
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold cw_post. apply apost_baseF_of_base. unfold apost_base.
exists ly3, (stack_free_state 3 (x_fpos c) S3), (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy mdv2) mat' mdv2).
assert (F1 : getr (ms_regs msF) 1 = getr (x_regs c) 1).
{ prreg HS (1%bv : bv 5) R1. rewrite R1. rewrite (AG 32%nat ltac:(lia)), E32. reflexivity. }
split; [rewrite F1, Hra0; reflexivity|].
split.
{ eapply (ajournal_mono_k _ _); [apply (ajournal_materialize _ _ LAWS pa_segs_low); exact HJ2 | lia]. }
split.
{ apply aregs_preserved_eqs.
  - prreg HS (2%bv : bv 5) R. rewrite R, (AG 8%nat ltac:(lia)), E8. unfold sp0, cw_sp0, spZ, w64.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - prreg HS (3%bv : bv 5) R. rewrite R, (AG 3%nat ltac:(lia)), E3. symmetry. exact Hgp0.
  - prreg HS (4%bv : bv 5) R. rewrite R, (AG 4%nat ltac:(lia)), E4. symmetry. exact Htp0.
  - prreg HS (8%bv : bv 5) R. rewrite R, (AG 33%nat ltac:(lia)), E33. reflexivity.
  - prreg HS (9%bv : bv 5) R. rewrite R, (AG 34%nat ltac:(lia)), E34. reflexivity.
  - prreg HS (18%bv : bv 5) R. rewrite R, (AG 35%nat ltac:(lia)), E35. reflexivity.
  - prreg HS (19%bv : bv 5) R. rewrite R, (AG 36%nat ltac:(lia)), E36. reflexivity.
  - prreg HS (20%bv : bv 5) R. rewrite R, (AG 37%nat ltac:(lia)), E37. reflexivity.
  - prreg HS (21%bv : bv 5) R. rewrite R, (AG 38%nat ltac:(lia)), E38. reflexivity.
  - prreg HS (22%bv : bv 5) R. rewrite R, (AG 39%nat ltac:(lia)), E39. reflexivity.
  - prreg HS (23%bv : bv 5) R. rewrite R, (AG 40%nat ltac:(lia)), E40. reflexivity.
  - prreg HS (24%bv : bv 5) R. rewrite R, (AG 41%nat ltac:(lia)), E41. reflexivity.
  - prreg HS (25%bv : bv 5) R. rewrite R, (AG 42%nat ltac:(lia)), E42. reflexivity.
  - prreg HS (26%bv : bv 5) R. rewrite R, (AG 43%nat ltac:(lia)), E43. reflexivity.
  - prreg HS (27%bv : bv 5) R. rewrite R, (AG 44%nat ltac:(lia)), E44. reflexivity. }
(* the recorder's answer crosses the release; the text pointer was in s4 at the join and is in a0 now *)
revert HQ. unfold cw_QJ, cw_Q, cw_Qr. destruct (VerbsRun.chain_run (x_R c) (tl (x_tks c))) as [R' x]. intros HQ.
destruct HQ as (O' & p & n & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
exists O', p, n.
assert (KB : forall b m k, In (b, m) (ablocks B ly3 S3) -> 0 <= k < m ->
aview SEGS (w_H W3) (ms_mem msF) (b + k) = aview SEGS (w_H W3) mem3 (b + k)).
{ intros b m k Hin Hk.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b m HAR3 Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as Hrq.
  destruct (SEPB b m (b + k) Hin ltac:(lia)) as (K1 & K2 & K3 & K4). exact (KEEPALL _ K1 K2 K3 K4). }
assert (KI : forall a, inFP cmd_PG a -> aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. destruct (SEPI a (proj1 (PROG_UNOWNED a Ha))) as (K1 & K2 & K3 & K4).
  exact (KEEPALL _ K1 K2 K3 K4). }
split.
{ apply (rec_repA_agree B ly3 S3 ly3 (stack_free_state 3 (x_fpos c) S3) _ _ R' O' Q1).
  - intros pn _ Hpn. exact Hpn.
  - intros k Hk. apply KI. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; cbn [In]; left; reflexivity|].
    cbn [fst snd]. unfold REC_SIZE in Hk. lia.
  - intros k Hk. apply KI. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; cbn [In]; right; left; reflexivity|].
    cbn [fst snd]. unfold SC_SIZE in Hk. lia.
  - intros [b m] Hpn k Hk. cbn [fst snd] in Hk |- *.
    exact (KB b m k (rec_repA_in_blocks B ly3 S3 _ R' O' (b, m) Q1 Hpn) Hk). }
split.
{ prreg HS (10%bv : bv 5) R. rewrite R, (AG 20%nat ltac:(lia)), (EE 20%nat 20%bv eq_refl). exact Q2. }
split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|].
split; [exact (astr_atR_agree _ _ p x n Q7 (Z.eq_le_incl _ _ (eq_sym Q8)) (fun k Hk => KB p n k Q4 Hk))|].
split; [exact Q8|]. split; [exact Q9|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
split; [exact Q13|].
unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). exact Q14.
Qed.
End e.
End c.
End b.
