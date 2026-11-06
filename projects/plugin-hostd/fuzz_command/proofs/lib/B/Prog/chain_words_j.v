(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the transport of the caller's objects in the walk of chain_words (0x8da84) on
   the ASan+UBSan build of plugin-hostd/fuzz_command (cw_transportP of lib/B/Prog/chain_words_d.v), the B twin of
   lib/A/Prog/chain_words_j.v (A walk a working branch 5e2cdad423e): from the entry facts (cw_pre),
   the frame part of a cut (cw_fi: its journal gives AR at the cut state, the layout and the frames) and its
   untouched part (cw_un: the bytes the caller can see and the block list), every object the callee statements ask
   for at a cut before a call (cw_caller) still holds. Statement pass 5 (a working branch f490061c104) removed
   astack_pres from every statement, so the A file's last block (the stack bytes up to ly_top, through
   astack_pres_journal) is gone with it; the rest is A's, with B's module paths and the statement's fixed
   CMD_RLO / CMD_RHI in place of A's RLO / RHI variables. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00 YG0q.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import chain_words_c chain_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* Copied from lib/A/Prog/reply_s1.v:27-148 of the reply walk (a Theorem Labs lane): the recorder representation
   under a reader that agrees on the bytes it reads. *)
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
(* the shadow byte of an address inside a frame lies in the frame's shadow (frame and size multiples of 8) *)
Lemma cwj_shadow_in : forall F fsb x, F mod 8 = 0 -> fsb mod 8 = 0 -> F <= x < F + fsb ->
  shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + fsb / 8.
Proof. intros F fsb x HF Hf Hx. unfold shadow_addr, shadow_of_addr. lia. Qed.
Lemma cwj_fsb8 : forall cid, 0 <= cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by exact H.
replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. apply Z_mod_mult.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis RO_IMG : cw_ro_imgP.
Hypothesis PROG_UNOWNED : cw_prog_unownedP B.
Hypothesis RO_OF_ROD : cw_ro_of_rodP B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* Copied from lib/A/Prog/reply_s1.v:156-171 of the reply walk (a Theorem Labs lane). *)
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
Lemma cw_transport_ok : cw_transportP B MT.
Proof.
intros c k ly3 S3 W3 regs3 mem3 md3 HP HF HU.
destruct HP as [Hafn Hrod _ _ _ Htokobj Htoks Hcb _ Hntok _ _ Hrec _ _ _ _ _ _ _ _].
destruct HF as [Hj _ _ _ _ _ _ _ _ _ _].
destruct HU as [Uimg Ublk Ufrm Uperm _ _ _ _].
pose proof Hj as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hfa : forall cid pos, frame_addr ly3 cid pos = frame_addr (x_ly c) cid pos)
  by (intros cid pos; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hbl : forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact Uperm | exact Hpn]).
assert (Hcb3 : In (x_cb c, x_ncb c) (ablocks B ly3 S3)) by exact (Hbl _ Hcb).
destruct Htokobj as ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & Htok8 & Hra).
(* the word array lies in a frame of the entry: its bytes and their shadow are the entry's *)
assert (Hrng : forall a, x_tok c <= a < x_tok c + 8 * x_ntok c -> rdW W3 mem3 a = rdW (x_W c) (x_mem c) a).
{ intros a Ha. apply (Ufrm cid pos a Hin). left. unfold frame_rng, in_zr. cbn [fst snd]. lia. }
assert (Hsh : forall x, x_tok c <= x < x_tok c + 8 * x_ntok c ->
  rdW W3 mem3 (shadow_of_addr SHADOW_OFF x) = rdW (x_W c) (x_mem c) (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. apply (Ufrm cid pos _ Hin). right. unfold in_zr. cbn [fst snd].
  apply cwj_shadow_in; [exact Hal | exact (cwj_fsb8 cid Hcid) | lia]. }
(* the read-only bytes the entry's arodata_okP names are image bytes, so the cut keeps them *)
assert (Hrod3 : arodata_okP SEGS RLO RHI B (rdW W3 mem3)).
{ intros a Hro Ho He. rewrite (Uimg a); [exact (Hrod a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RO_IMG a Hr)]. }
(* a byte of the program's statics (g_rec, record.spill, g_quitting) is an unowned image byte: the cut keeps it *)
assert (Hpg : forall a, inFP cmd_PG a -> rdW W3 mem3 a = rdW (x_W c) (x_mem c) a).
{ intros a Ha. destruct (PROG_UNOWNED a Ha) as (I1 & I2 & I3). exact (Uimg a I1 I2 I3). }
destruct Htoks as (T8 & Tlen & Tptr & Tstr).
split.
{ split; [|split; [exact Htok8|]].
  - exists cid, pos. rewrite Hfa. split; [rewrite Hfrs; apply in_or_app; right; exact Hin|].
    split; [exact Hcid|]. split; [exact Hal|]. split; [exact Hlo | exact Hhi].
  - intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [rewrite (Hsh x Hx); exact Hs | exact Hok]. }
split.
{ split; [exact T8|]. split; [exact Tlen|]. split.
  - intros i p Hi. apply (aval_mem_agree _ _ _ 8 _ (Tptr i p Hi)).
    assert (Hil : (i < length (x_ptrs c))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Hrng. rewrite Hntok, <- Tlen. lia.
  - intros i p w Hp Hw. destruct (Tstr i p w Hp Hw) as (S1 & S2 & S3' & S4). split; [|split; [exact S2 | split; [exact S3' | exact S4]]].
    apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) S1); [lia|].
    intros kk Hkk. replace (p + kk) with (x_cb c + (p - x_cb c + kk)) by lia. apply (Ublk _ _ _ Hcb).
    pose proof (req_size_pos (x_ncb c) ltac:(lia)). lia. }
split; [exact Hcb3|].
split.
{ apply (rec_repA_agree (x_ly c) (x_S c) ly3 S3 _ _ (x_R c) (x_O c) Hrec).
  - intros pn _ Hpn. exact (Hbl pn Hpn).
  - intros kk Hkk. apply Hpg. exists (A_G_REC, A_G_REC + 960).
    split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hkk; lia].
  - intros kk Hkk. apply Hpg. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hkk; lia].
  - intros [p n] HpnO kk Hkk. cbn [fst snd] in *. apply (Ublk _ _ _ (rec_repA_in_blocks _ _ _ _ _ _ Hrec HpnO)).
    pose proof (req_size_pos n ltac:(lia)). lia. }
split; [exact Hrod3|].
exact (RO_OF_ROD ly3 S3 W3 mem3 md3 HAR Hrod3).
Qed.
End e.
End f.
End d.
