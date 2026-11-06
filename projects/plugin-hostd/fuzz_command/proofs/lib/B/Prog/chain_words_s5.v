(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S5 of the walk of chain_words (0x8da84) on the ASan+UBSan build of
   plugin-hostd/fuzz_command (interface chain_words_d.v), the B twin of lib/A/Prog/chain_words_s5.v
   (a working branch 5e2cdad423e): the two refusal tails, from KR1 (0x8dd5c: `li a0,-902;
   jal sup_resp; mv s4,a0; j 0x8dd80`) and from KR2 (0x8dd6c: `li a0,-902; jal sup_resp; mv s4,a0; ld s3,16(s1);
   ld s6,8(s1)`) to the join KJ (0x8dd80). sup_resp's post is apost_baseF (it reaches the snprintf wrapper), so the
   call goes through the kit's cl_callS_wideF and srr_after_callF (lib/B/Prog/PaFx.v) and the code after it is a
   lemma of this closed section, applied at the FP state the call returned (PASS4-REFIT.md section A.5).
   The first part holds the helpers segment S4 (chain_words_s4.v) shares: the reader after a run with read-only
   regions, the frame chain at a program call (s0 = the entry sp, the prologue's frame record at sp0 - 8 /
   sp0 - 16, PASS4-REFIT.md section B, class B), the frame part of a cut carried across a program call (with ntok's
   slot s1 + 24 and the spills of F at s1 + 8 / s1 + 16 above the callee's window), the recorder representation
   under an agreeing reader, and the two join tails: from 0x8dd64 (`mv s4,a0; j 0x8dd80`, F still in s3 / s6) and
   from 0x8dd58 or 0x8dd74 (`[j 0x8dd74;] mv s4,a0; ld s3,16(s1); ld s6,8(s1)`, F reloaded from its spills). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaSB PaCall PaCallRun PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import number_c sup_chain_c sup_resp_c chain_words_c chain_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition cw5_pz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
(* the recorder representation reads only g_rec, record.spill and the recorder's own blocks: copied from
   lib/A/Prog/reply_s1.v as the worktree of a working branch held it (aval_mem_agree ..
   rec_repA_in_blocks), names prefixed cw5_ *)
Lemma cw5_aval_mem_agree : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.
Lemma cw5_abytes_atR_agree : forall (rd rd' : reader) p l n,
abytes_atR rd p l -> Z.of_nat (length l) <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l n H Hle Hk i Hi. rewrite Hk by lia. exact (H i Hi). Qed.
Lemma cw5_astr_atR_agree : forall (rd rd' : reader) p s n,
astr_atR rd p s -> Z.of_nat (length s) + 1 <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s n [Hb Hn0] Hle Hk. split; [|exact Hn0].
apply (cw5_abytes_atR_agree rd rd' p _ n Hb); [rewrite length_app; cbn [length]; lia | exact Hk].
Qed.
Lemma cw5_acall_at_agree : forall bl bl' rd rd' a c P,
acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < 8 + 8 * Z.of_nat (length P) -> rd' (a + k) = rd (a + k)) ->
(forall pn, In pn P -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & Hfn & Hna & Hnd & Hargs) HB HR HS.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (cw5_aval_mem_agree rd rd' _ 4 _ Hfn); intros k Hk; unfold CALL_OFF_FN; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 0 + k) with (a + k) by lia; apply HR; lia|].
split; [apply (cw5_aval_mem_agree rd rd' _ 4 _ Hna); intros k Hk; unfold CALL_OFF_NARGS; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 4 + k) with (a + (4 + k)) by lia; apply HR; lia|].
split; [exact Hnd|].
intros k s pn Hs Hpn. destruct (Hargs k s pn Hs Hpn) as (A1 & A2 & A3 & A4 & A5).
assert (Hk : (k < length P)%nat) by (apply nth_error_Some; rewrite Hpn; discriminate).
pose proof (nth_error_In _ _ Hpn) as HinP.
split; [|split; [exact A2|split; [exact (HB pn HinP A3)|split; [exact A4|]]]].
- apply (cw5_aval_mem_agree rd rd' _ 8 _ A1). intros kk Hkk. unfold CALL_OFF_ARGS. change (Z.of_nat 8) with 8 in Hkk.
  replace (a + 8 + 8 * Z.of_nat k + kk) with (a + (8 + 8 * Z.of_nat k + kk)) by lia. apply HR. lia.
- apply (cw5_astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HS pn HinP).
Qed.
Lemma cw5_in_lay_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn Hi Hp. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hi) | exact Hp].
Qed.
Lemma cw5_in_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma cw5_in_lay_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite H. left. reflexivity. Qed.
Lemma cw5_in_lay_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite H. left. reflexivity. Qed.
Lemma cw5_arep_at_agree : forall bl bl' rd rd' gr sc R Q,
arep_at bl rd gr sc R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < REC_SIZE -> rd' (gr + k) = rd (gr + k)) ->
(forall k, 0 <= k < SC_SIZE -> rd' (sc + k) = rd (sc + k)) ->
(forall pn, In pn (lay_blocks Q) -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
arep_at bl' rd' gr sc R Q.
Proof.
intros bl bl' rd rd' gr sc R Q (Hg8 & Hs8 & Hap & HC & HA & HR & HSc & HOwn) HB HG HSP HO.
assert (VG : forall off n v, aval_mem rd (gr + off) n v -> 0 <= off -> off + Z.of_nat n <= REC_SIZE -> aval_mem rd' (gr + off) n v).
{ intros off n v H H0 H1. apply (cw5_aval_mem_agree rd rd' _ n _ H). intros k Hk.
  replace (gr + off + k) with (gr + (off + k)) by lia. apply HG. lia. }
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|]. split; [apply VG; [exact C3 | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, REC_SIZE; cbn; lia]|].
  split; [|split; [|exact C6]].
  - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [A F]. split; [|exact F].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    pose proof A as (_ & Hn6 & HlP & _).
    apply (cw5_acall_at_agree bl bl' rd rd' _ c P A).
    + intros pn Hpn. apply HB. exact (cw5_in_lay_calls Q i P pn HP Hpn).
    + intros k Hk. replace (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + k) with (gr + (OFF_CALLS + CALL_SIZE * Z.of_nat i + k)) by lia.
      apply HG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (cw5_in_lay_calls Q i P pn HP Hpn).
  - pose proof C5 as (_ & Hn6 & HlP & _). apply (cw5_acall_at_agree bl bl' rd rd' _ _ _ C5).
    + intros pn Hpn. apply HB. exact (cw5_in_lay_spill Q pn Hpn).
    + intros k Hk. apply HSP. unfold SC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (cw5_in_lay_spill Q pn Hpn). }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|] eqn:Ea, (l_answer Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HA as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply VG; [exact A1 | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]|].
    split; [exact A2|]. split; [exact (HB pn (cw5_in_lay_answer Q pn Eq) A3)|]. split; [exact A4|]. split; [|exact A6].
    apply (cw5_astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HO pn (cw5_in_lay_answer Q pn Eq)).
  - apply VG; [exact HA | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|] eqn:Ea, (l_reply Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply VG; [exact A1 | unfold OFF_REPLY; lia | unfold OFF_REPLY, REC_SIZE; cbn; lia]|].
    split; [apply VG; [exact A2 | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, REC_SIZE; cbn; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HB pn (cw5_in_lay_reply Q pn Eq) A5)|]. split; [exact A6|]. split; [|exact A8].
    apply (cw5_abytes_atR_agree rd rd' _ _ (snd pn) A7); [lia|]. exact (HO pn (cw5_in_lay_reply Q pn Eq)).
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
Lemma cw5_lay_blocks_in_bl : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
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
Lemma cw5_rdword_agree : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (pose proof (H 0 ltac:(lia)) as H0; rewrite Z.add_0_r in H0; exact H0).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma cw5_pres_get : forall (regs regs' : bvmap 5 word) (r : bv 5) (z : Z),
aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
intros regs regs' r z HP Hz Hr. pose proof (HP z Hz) as H. subst z. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Lemma cw5_z2bv : forall (r : bv 5) z, bv_unsigned r = z -> Z_to_bv 5 z = r.
Proof. intros r z H. subst z. apply Z_to_bv_bv_unsigned. Qed.
Lemma cw5_mod_of_div : forall x d e, 0 < e -> (e | d) -> d <> 0 -> x mod d = 0 -> x mod e = 0.
Proof.
intros x d e He Hed Hd Hx. apply (proj2 (Z.mod_divide x e ltac:(lia))).
apply (Z.divide_trans _ d); [exact Hed | exact (proj1 (Z.mod_divide x d Hd) Hx)].
Qed.
Lemma cw5_mod_sub : forall x y e, e <> 0 -> x mod e = 0 -> y mod e = 0 -> (x - y) mod e = 0.
Proof.
intros x y e He Hx Hy. apply (proj2 (Z.mod_divide _ e He)).
apply Z.divide_sub_r; [exact (proj1 (Z.mod_divide x e He) Hx) | exact (proj1 (Z.mod_divide y e He) Hy)].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the reader after a symbolic run whose regions are all read-only is the reader before it *)
Lemma cw5_rd_frame_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hro HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Ha). pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Lemma cw5_rec_repA_agree : forall ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
(forall k, 0 <= k < REC_SIZE -> rd' (A_G_REC + k) = rd (A_G_REC + k)) ->
(forall k, 0 <= k < SC_SIZE -> rd' (A_REC_SPILL + k) = rd (A_REC_SPILL + k)) ->
(forall pn, In pn O -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S ly' S' rd rd' R O (Q & HA & HOQ) HB HG HS HO. exists Q. split; [|exact HOQ].
apply (cw5_arep_at_agree _ _ rd rd' _ _ R Q HA).
- intros pn Hpn Hbl. apply HB; [apply HOQ; exact Hpn | exact Hbl].
- exact HG. - exact HS.
- intros pn Hpn. apply HO. apply HOQ. exact Hpn.
Qed.
Lemma cw5_rec_repA_in_blocks : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HA & HOQ) Hpn. apply (cw5_lay_blocks_in_bl _ rd _ _ R Q pn HA). apply HOQ. exact Hpn. Qed.
Lemma cw5_rec_repA_same : forall ly S (rd rd' : reader) R O, rec_repA B ly S rd R O -> (forall a, rd' a = rd a) ->
rec_repA B ly S rd' R O.
Proof.
intros ly S rd rd' R O H Hs. apply (cw5_rec_repA_agree ly S ly S rd rd' R O H (fun _ _ Hb => Hb)); intros; apply Hs.
Qed.
(* the stack facts of the entry *)
Lemma cw5_stk : forall c, cw_pre B MT c ->
cw_sp0 c mod 16 = 0 /\ alloc_ceiling + CHAIN_WORDS_STK <= cw_sp0 c /\ cw_sp0 c <= ly_top (x_ly c) /\
ly_top (x_ly c) <= 2 ^ 47 /\ 4096 <= raZ (x_regs c).
Proof.
intros c HP. pose proof (cp_afn _ _ _ HP) as (_ & _ & Hra4 & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold cw_sp0. repeat split; lia.
Qed.
(* the stack the two recorder callees need, below the 160-byte frame and its realignment *)
Lemma cw5_STK : SUP_RESP_STK + 176 <= CHAIN_WORDS_STK /\ SUP_CHAIN_STK + 176 <= CHAIN_WORDS_STK /\
0 <= SUP_RESP_STK /\ 0 <= SUP_CHAIN_STK.
Proof.
assert (H1 : 0 <= SUP_RESP_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (H2 : 0 <= SUP_CHAIN_STK) by (apply Z.leb_le; vm_compute; reflexivity).
unfold CHAIN_WORDS_STK. lia.
Qed.
(* the walk's footprint lies below alloc_ceiling: the recorder statics and the recorder's blocks *)
Lemma cw5_FP_low : forall c, cw_pre B MT c -> forall a, inFP (cw_FP c) a -> a < alloc_ceiling.
Proof.
intros c HP a Ha. pose proof (cp_afn _ _ _ HP) as (HAR & _).
pose proof (cp_rec _ _ _ HP) as HREC.
pose proof asan_consts as (C1 & _).
unfold cw_FP in Ha. apply inFP_app in Ha as [Ha | Ha].
- unfold CHAIN_WORDS_PG in Ha. apply inFP_cons in Ha as [Ha | Ha];
  [|apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]];
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia.
- destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & n & Hpn & Hr).
  pose proof (cw5_rec_repA_in_blocks _ _ _ _ _ _ HREC Hpn) as Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hb) as (_ & _ & Hc & _). lia.
Qed.
(* the frame chain at a program call of the walk: s0 = sp0, and the prologue's frame record (ra at sp0 - 8, the
   caller's s0 at sp0 - 16) on top of the entry's chain (PASS4-REFIT.md section B, class B) *)
Lemma cw5_achain : forall c k ly3 S3 W3 regs3 mem3 md3, cw_pre B MT c ->
cw_fi B c k ly3 S3 W3 regs3 mem3 md3 ->
exists ch1, achain ly3 (rdW W3 mem3) (cw_s1 c) (cw_sp0 c) ch1.
Proof.
intros c k ly3 S3 W3 regs3 mem3 md3 HP HF.
pose proof (cp_afn _ _ _ HP) as (HAR & Hra & Hra4 & _ & _ & Hstk & _ & Hch & _).
destruct (cw5_stk c HP) as (H16 & Hlo & Htop & H47 & _).
destruct (cw_s1_facts c H16) as (H32 & Hs1).
pose proof cw5_STK as HSTK.
pose proof asan_consts as (C1 & _).
destruct HF as [HJ _ _ _ _ _ _ _ _ Hsaved _].
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (Z_lt_le_dec (cw_sp0 c) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
- pose proof (Hsaved 0%nat 1 eq_refl) as Hra8. pose proof (Hsaved 1%nat 8 eq_refl) as Hs16.
  replace (cw_sp0 c - 8 - 8 * Z.of_nat 0) with (cw_sp0 c - 8) in Hra8 by lia.
  replace (cw_sp0 c - 8 - 8 * Z.of_nat 1) with (cw_sp0 c - 16) in Hs16 by lia.
  rewrite (cw5_z2bv 1%bv 1 eq_refl) in Hra8. rewrite (cw5_z2bv 8%bv 8 eq_refl) in Hs16.
  eexists. apply (achain_ly_top (x_ly c) ly3); [exact Etop|].
  apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 mem3) (cw_sp0 c) (s0Z (x_regs c)) (raZ (x_regs c)) (x_ch c) (cw_s1 c)).
  + exact Hch.
  + lia.
  + intros a Ha. apply F9; [lia | lia | intros Hf; pose proof (cw5_FP_low c HP a Hf); lia].
  + exact Hra8.
  + exact Hs16.
  + exact Hra4.
  + lia.
  + exact (cw5_mod_of_div (cw_sp0 c) 16 8 ltac:(lia) ltac:(exists 2; reflexivity) ltac:(lia) H16).
  + lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
(* a word of chain_words' own frame above the callee's stack pointer (ntok at s1 + 24, the spills at s1 + 8 and
   s1 + 16, the saved registers) is kept by a program call whose footprint lies below alloc_ceiling *)
Lemma cw5_kept_call : forall c ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 STK1 sp1 FP1 k1 a,
cw_pre B MT c ->
ajournal SEGS B STK1 sp1 FP1 ly3 S3 W3 mem3 md3 [] ly4 S4 W4 mem4 md4 k1 ->
(forall a, inFP FP1 a -> a < alloc_ceiling) ->
sp1 <= a -> cw_s1 c <= a -> a + 8 <= cw_sp0 c ->
rdword (rdW W4 mem4) a = rdword (rdW W3 mem3) a.
Proof.
intros c ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 STK1 sp1 FP1 k1 a HP HJc HFPlo Hsp1 Hs1a Ha8.
destruct (cw5_stk c HP) as (H16 & Hlo & Htop & H47 & _).
destruct (cw_s1_facts c H16) as (H32 & Hs1r).
pose proof cw5_STK as HSTK. pose proof asan_consts as (C1 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
apply cw5_rdword_agree. intros i Hi.
apply K9; [lia | lia | intros Hf; pose proof (HFPlo _ Hf); lia].
Qed.
(* the frame part of a cut carried across a program call: the call rule's composed journal, the callee-saved
   registers, ntok's slot and the saved slots above the callee's window and the frame's flag word *)
Lemma cw5_fi_call : forall c k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 STK1 sp1 FP1,
cw_pre B MT c -> cw_fi B c k ly3 S3 W3 regs3 mem3 md3 ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [(3, x_fpos c)] ly4 S4 W4 mem4 md4 (k + k1) ->
ajournal SEGS B STK1 sp1 FP1 ly3 S3 W3 mem3 md3 [] ly4 S4 W4 mem4 md4 k1 ->
sp1 <= cw_s1 c ->
(forall a, inFP FP1 a -> a < alloc_ceiling) ->
(forall a, cw_F c + 504 <= a < cw_F c + 512 -> ~ inFP FP1 a) ->
aregs_preserved regs3 regs4 ->
cw_fi B c (k + k1) ly4 S4 W4 regs4 mem4 md4.
Proof.
intros c k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 STK1 sp1 FP1 HP HF HJ HJc Hsp1 HFPlo HFPfl HPR.
destruct (cw5_stk c HP) as (H16 & Hlo & Htop & H47 & _).
destruct (cw_s1_facts c H16) as (H32 & Hs1r).
pose proof cw5_STK as HSTK. pose proof asan_consts as (C1 & _).
destruct HF as [HJ0 Hsp Hgp Htp Hs0 Hs1 Hs2 Hs8 Hntok Hsaved Hflag].
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _ & _ & K12 & _).
pose proof HJ0 as (_ & Hly3 & _ & _ & _ & Hfr3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (CS : forall z, acallee_saved z -> forall r : bv 5, bv_unsigned r = z -> getr regs4 r = getr regs3 r)
  by (intros z Hz r Hr; exact (cw5_pres_get regs3 regs4 r z HPR Hz Hr)).
constructor.
- exact HJ.
- rewrite (CS 2 ltac:(unfold acallee_saved; lia) 2%bv eq_refl). exact Hsp.
- rewrite (CS 3 ltac:(unfold acallee_saved; lia) 3%bv eq_refl). exact Hgp.
- rewrite (CS 4 ltac:(unfold acallee_saved; lia) 4%bv eq_refl). exact Htp.
- rewrite (CS 8 ltac:(unfold acallee_saved; lia) 8%bv eq_refl). exact Hs0.
- rewrite (CS 9 ltac:(unfold acallee_saved; lia) 9%bv eq_refl). exact Hs1.
- rewrite (CS 18 ltac:(unfold acallee_saved; lia) 18%bv eq_refl). exact Hs2.
- rewrite (CS 24 ltac:(unfold acallee_saved; lia) 24%bv eq_refl). exact Hs8.
- rewrite (cw5_kept_call c ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 STK1 sp1 FP1 k1 (cw_s1 c + 24) HP HJc HFPlo)
    by lia. exact Hntok.
- intros j r Hj. rewrite <- (Hsaved j r Hj). apply cw5_rdword_agree. intros i Hi.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some cw_saved j) ltac:(rewrite Hj; discriminate)) as Hl. exact Hl. }
  apply K9; [lia | lia | intros Hf; pose proof (HFPlo _ Hf); lia].
- rewrite <- Hflag. apply cw5_rdword_agree. intros i Hi.
  apply (K12 3 (x_fpos c)).
  + rewrite Hfr3. left. reflexivity.
  + left. unfold in_zr, frame_rng, cw_F, frame_addr in *. cbn [fst snd]. rewrite EF.
    change (fs_frame_bytes 3) with 512. lia.
  + apply HFPfl. lia.
Qed.
(* the spills of F (s1 + 8, s1 + 16) across a program call *)
Lemma cw5_spills_call : forall c ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 STK1 sp1 FP1 k1,
cw_pre B MT c ->
ajournal SEGS B STK1 sp1 FP1 ly3 S3 W3 mem3 md3 [] ly4 S4 W4 mem4 md4 k1 ->
sp1 <= cw_s1 c -> (forall a, inFP FP1 a -> a < alloc_ceiling) ->
cw_spills c W3 mem3 -> cw_spills c W4 mem4.
Proof.
intros c ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 STK1 sp1 FP1 k1 HP HJc Hsp1 HFPlo [H8 H16].
destruct (cw5_stk c HP) as (H16' & _).
destruct (cw_s1_facts c H16') as (_ & Hs1r).
split.
- rewrite (cw5_kept_call c ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 STK1 sp1 FP1 k1 (cw_s1 c + 8) HP HJc HFPlo)
    by lia. exact H8.
- rewrite (cw5_kept_call c ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 STK1 sp1 FP1 k1 (cw_s1 c + 16) HP HJc HFPlo)
    by lia. exact H16.
Qed.
Lemma cw5_un_same : forall c ly3 S3 (W3 : world SEGS) m m', cw_un B MT c ly3 S3 W3 m ->
(forall a, rdW W3 m' a = rdW W3 m a) -> cw_un B MT c ly3 S3 W3 m'.
Proof.
intros c ly3 S3 W3 m m' [U1 U2 U3 U4 U5 U6 U7 U8] Hs. constructor; try assumption.
- intros a H1 H2 H3. rewrite Hs. exact (U1 a H1 H2 H3).
- intros p n i H1 H2. rewrite Hs. exact (U2 p n i H1 H2).
- intros cid pos a H1 H2. rewrite Hs. exact (U3 cid pos a H1 H2).
- intros i Hi. rewrite Hs. exact (U8 i Hi).
Qed.
Lemma cw5_rdword_same : forall (rd rd' : reader) a, (forall x, rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a H. apply cw5_rdword_agree. intros i _. apply H. Qed.
Lemma cw5_spills_same : forall c (W3 : world SEGS) m m', cw_spills c W3 m ->
(forall a, rdW W3 m' a = rdW W3 m a) -> cw_spills c W3 m'.
Proof.
intros c W3 m m' [H8 H16] Hs. split; rewrite (cw5_rdword_same _ _ _ Hs); assumption.
Qed.
(* the return text in a0 at a state is the join's text in s4 after `mv s4,a0` and reads that change nothing *)
Lemma cw5_QJ_of_Q : forall c ly3 S3 (W3 : world SEGS) regs3 mem3 md3 (regs' : bvmap 5 word) mem' md',
cw_Q B MT c ly3 S3 W3 regs3 mem3 md3 -> getr regs' 20 = getr regs3 10 ->
(forall a, rdW W3 mem' a = rdW W3 mem3 a) -> cw_QJ B MT c ly3 S3 W3 regs' mem' md'.
Proof.
intros c ly3 S3 W3 regs3 mem3 md3 regs' mem' md' HQ E20 UQ. unfold cw_QJ, cw_Q, cw_Qr in *.
revert HQ. destruct (VerbsRun.chain_run (x_R c) (tl (x_tks c))) as [R' x]. intros HQ.
destruct HQ as (O' & p & n & HR & H10 & Hp & Hin & HnO & Hold & Hstr & Hn & Hap & Hkeep & Hcls & HOs & Hbb & Hmle).
exists O', p, n.
split; [exact (cw5_rec_repA_same _ _ _ _ _ _ HR UQ)|].
split; [rewrite E20; exact H10|].
split; [exact Hp|]. split; [exact Hin|]. split; [exact HnO|]. split; [exact Hold|].
split; [apply (cw5_astr_atR_agree _ _ _ _ (Z.of_nat (length x) + 1) Hstr); [lia | intros k _; apply UQ]|].
split; [exact Hn|]. split; [exact Hap|]. split; [exact Hkeep|]. split; [exact Hcls|]. split; [exact HOs|].
split; [exact Hbb | exact Hmle].
Qed.
(* the meter of the refusal: xmalloc's one malloc of |resp -902| + 1 = 10 bytes *)
Lemma cw5_xm_resp : ameter_laws MT -> forall R, 0 + XM_SUP_RESP MT (-902) <= XM_CHAIN_WORDS MT R.
Proof.
intros MTL R. unfold XM_SUP_RESP, XM_XMALLOC, LIVE_XMALLOC, XM_CHAIN_WORDS, CHAIN_WORDS_MALLOCS, CHAIN_WORDS_REQ.
assert (HL : Z.max (Z.of_nat (length (resp (-902))) + 1) 1 = 10) by (vm_compute; reflexivity). rewrite HL.
pose proof (mo_malloc_mono MT MTL 10 8194 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL 8194 ltac:(lia)) as M2.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HE : 0 <= EV_CHAIN_WORDS R) by (unfold EV_CHAIN_WORDS, EV_SUP_RESP, EV_XMALLOC; lia).
pose proof (Z.mul_nonneg_nonneg _ _ HE M3). lia.
Qed.
Lemma cw5_live_resp : LIVE_SUP_RESP (-902) = 10.
Proof. vm_compute. reflexivity. Qed.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* the join tail after the KR1 call (0x8dd64): `mv s4,a0; j 0x8dd80`, F still in s3 and s6 *)
Lemma cw5_tail1 : forall c k ly3 S3 W3 regs3 mem3 md3,
cw_pre B MT c -> from_KJ B MT c -> 0 <= k <= EV_CHAIN_WORDS (x_R c) ->
cw_fi B c k ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 19 = w64 (cw_F c) -> getr regs3 22 = w64 (cw_F c) -> cw_Q B MT c ly3 S3 W3 regs3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (BASE + (CW_KR1 + 8)) regs3 mem3 md3) (cw_post B MT c).
Proof.
intros c k ly3 S3 W3 regs3 mem3 md3 HPRE HKJ Hk HFI H19 H22 HQ.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HFI as [HJ Hsp Hgp Htp Hs0 Hs1 Hs2 Hs8 Hntok Hsaved Hflag].
set (E := Eimg (Ereg regs3 [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS (CW_KR1 + 8) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (CW_KR1 + 8))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + (CW_KR1 + 8))) with (Z_to_bv 64 (BASE + (CW_KR1 + 8))).
(* 0x8dd64 .. 0x8dd68: mv s4,a0; j 0x8dd80 *)
paj_run_to_shc RUNTOP HS HJ CW_KJ.
{ apply awr_ok_nil. }
set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdv. clear mat.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
prreg HS (22%bv : bv 5) R22. prreg HS (24%bv : bv 5) R24.
pmkst HS.
assert (UQ : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by exact (cw5_rd_frame_ro E [] (w_H W3) mem3 (ms_mem ms) (Forall_nil _) HFr).
change (Z_to_bv 64 (BASE + 30800)) with (w64 (BASE + CW_KJ)).
apply (HKJ ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv).
unfold INV_KJ. exists k. split; [exact Hk|].
split.
{ constructor.
  - exact HJ.
  - rewrite R2, (EE 2%nat 2%bv eq_refl). exact Hsp.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - rewrite R8, (EE 8%nat 8%bv eq_refl). exact Hs0.
  - rewrite R9, (EE 9%nat 9%bv eq_refl). exact Hs1.
  - rewrite R18, (EE 18%nat 18%bv eq_refl). exact Hs2.
  - rewrite R24, (EE 24%nat 24%bv eq_refl). exact Hs8.
  - rewrite (cw5_rdword_same _ _ _ UQ). exact Hntok.
  - intros j r Hj. rewrite (cw5_rdword_same _ _ _ UQ). exact (Hsaved j r Hj).
  - rewrite (cw5_rdword_same _ _ _ UQ). exact Hflag. }
split; [rewrite R19, (EE 19%nat 19%bv eq_refl); exact H19|].
split; [rewrite R22, (EE 22%nat 22%bv eq_refl); exact H22|].
exact (cw5_QJ_of_Q c ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdv HQ
  ltac:(rewrite R20; exact (EE 10%nat 10%bv eq_refl)) UQ).
Qed.
(* the join tail after the sup_chain call (0x8dd58: `j 0x8dd74`) and after the KR2 call (0x8dd74): `mv s4,a0;
   ld s3,16(s1); ld s6,8(s1)`, F reloaded from its spills *)
Definition cw5_spillR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 32 0))].
Lemma cw5_tail2 : forall c k ly3 S3 W3 regs3 mem3 md3 pc, pc = CW_KD + 0x14 \/ pc = CW_KR2 + 8 ->
cw_pre B MT c -> from_KJ B MT c -> 0 <= k <= EV_CHAIN_WORDS (x_R c) ->
cw_fi B c k ly3 S3 W3 regs3 mem3 md3 -> cw_spills c W3 mem3 -> cw_Q B MT c ly3 S3 W3 regs3 mem3 md3 ->
SRr SEGS W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3) (cw_post B MT c).
Proof.
intros c k ly3 S3 W3 regs3 mem3 md3 pc Hpc HPRE HKJ Hk HFI [HSP8 HSP16] HQ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (cw5_stk c HPRE) as (H16 & Hlo & Htop & H47 & Hra4).
destruct (cw_s1_facts c H16) as (H32 & Hs1r).
pose proof cw5_STK as HSTK.
pose proof HFI as [HJ Hsp Hgp Htp Hs0 Hs1 Hs2 Hs8 Hntok Hsaved Hflag].
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfr3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (EFA : frame_addr ly3 3 (x_fpos c) = cw_F c) by (unfold cw_F, frame_addr; rewrite EF; reflexivity).
assert (Hin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 Hin3) as (Hfa0 & Hfac & _).
rewrite EFA in Hfa0, Hfac. change (fs_frame_bytes 3) with 512 in Hfac.
set (E := Eimg (Ereg regs3 [Z_to_bv 64 (cw_F c)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (cw_F c))
  by (subst E; rewrite ?Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U9 : bv_unsigned (ew E 9) = cw_s1 c)
  by (rewrite (EE 9%nat 9%bv eq_refl), Hs1; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HS : st_ok_pi SEGS VAL E (mkSS pc sr_atoms [cw5_spillR] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + pc)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cw5_spillR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem3) (cw_s1 c) 8 8 (SOff 32 0) (cw_F c)).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * change (Z.of_N 8) with 8. lia.
      * exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ HSP8).
    + apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem3) (cw_s1 c) 16 8 (SOff 32 0) (cw_F c)).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * change (Z.of_N 8) with 8. lia.
      * exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ HSP16).
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + pc)) with (Z_to_bv 64 (BASE + pc)).
destruct Hpc as [-> | ->].
(* 0x8dd58 (j 0x8dd74) or 0x8dd74 .. 0x8dd7c: mv s4,a0; ld s3,16(s1); ld s6,8(s1) *)
all: paj_run_to_shc RUNTOP HS HJ CW_KJ;
  [ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] | ].
all: set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *; clearbody mdv; clear mat.
all: prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4; prreg HS (8%bv : bv 5) R8;
  prreg HS (9%bv : bv 5) R9; prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20;
  prreg HS (22%bv : bv 5) R22; prreg HS (24%bv : bv 5) R24.
all: pmkst HS.
all: assert (UQ : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (refine (cw5_rd_frame_ro E _ (w_H W3) mem3 (ms_mem ms) _ HFr);
      apply Forall_cons; [cbn; lia | apply Forall_nil]).
all: change (Z_to_bv 64 (BASE + 30800)) with (w64 (BASE + CW_KJ)).
all: apply (HKJ ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv).
all: unfold INV_KJ; exists k; split; [exact Hk|].
all: split; [constructor;
  [ exact HJ
  | rewrite R2, (EE 2%nat 2%bv eq_refl); exact Hsp
  | rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp
  | rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp
  | rewrite R8, (EE 8%nat 8%bv eq_refl); exact Hs0
  | rewrite R9, (EE 9%nat 9%bv eq_refl); exact Hs1
  | rewrite R18, (EE 18%nat 18%bv eq_refl); exact Hs2
  | rewrite R24, (EE 24%nat 24%bv eq_refl); exact Hs8
  | rewrite (cw5_rdword_same _ _ _ UQ); exact Hntok
  | intros j r Hj; rewrite (cw5_rdword_same _ _ _ UQ); exact (Hsaved j r Hj)
  | rewrite (cw5_rdword_same _ _ _ UQ); exact Hflag ] |].
all: split; [rewrite R19, ?E32; reflexivity|].
all: split; [rewrite R22, ?E32; reflexivity|].
all: exact (cw5_QJ_of_Q c ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdv HQ
  ltac:(rewrite R20; exact (EE 10%nat 10%bv eq_refl)) UQ).
Qed.
Hypothesis SUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TRANSP : cw_transportP B MT.
(* the call of sup_resp(-902) at a cut before the recorder call (KR1 or KR2, after `li a0,-902`), through
   cl_callS_wideF: it returns at some fx1 with fxrel fx fx1, the frame part of the cut carried across, the spills
   kept, and the refusal text in a0 as the walk's post states it *)
Lemma cw5_call_resp : forall c ly3 S3 W3 (regs : bvmap 5 word) mem md (rk : Z),
cw_pre B MT c -> frm0 fx ->
cw_fi B c 0 ly3 S3 W3 regs mem md -> cw_un B MT c ly3 S3 W3 mem ->
getr regs 10 = w64 (-902) -> getr regs 1 = Z_to_bv 64 (BASE + rk) -> 0 <= rk < 2 ^ 40 -> rk mod 2 = 0 ->
VerbsRun.chain_run (x_R c) (tl (x_tks c)) = sup_resp_m (x_R c) Verbs.err_invalid_operation ->
SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_sup_resp)) mem (seg_rom SEGS)) md)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
  c2 = mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + rk)) mem2 (seg_rom SEGS)) md2 /\
  (cw_fi B c (0 + EV_SUP_RESP) ly2 S2 W2 regs2 mem2 md2 /\ aregs_preserved regs regs2 /\
   (cw_spills c W3 mem -> cw_spills c W2 mem2) /\ cw_Q B MT c ly2 S2 W2 regs2 mem2 md2)).
Proof.
intros c ly3 S3 W3 regs mem md rk HPRE HFRM HFI HUN Q10' Q1 Hrk Hrk2 HRUN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (cw5_stk c HPRE) as (H16 & Hlo & Htop & H47 & Hra4).
destruct (cw_s1_facts c H16) as (H32 & Hs1r).
pose proof cw5_STK as (HSTK1 & HSTK2 & HSTK3 & HSTK4).
pose proof HFI as [HJ Hsp Hgp Htp Hs0 Hs1 Hs2 Hs8 Hntok Hsaved Hflag].
destruct (TRANSP c 0 ly3 S3 W3 regs mem md HPRE HFI HUN) as (_ & _ & _ & HREC & HROD & HRO).
destruct (cw5_achain c 0 ly3 S3 W3 regs mem md HPRE HFI) as [ch1 Hch1].
pose proof HUN as [U1 U2 U3 Uperm Unev Ubb Umeter Uids].
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfr3 & _).
assert (Qsp : spZ regs = cw_sp0 c + (cw_s1 c - cw_sp0 c))
  by (unfold spZ; rewrite Hsp; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hs0c : s0Z regs = cw_sp0 c)
  by (unfold s0Z; rewrite Hs0; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose (KR := fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
  exists q, let n := Z.of_nat (length (resp (-902))) + 1 in
  getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
  Permutation (ablocks B ly' S') ((q, n) :: ablocks B ly3 S3) /\
  Forall (fun qk => iv_apart q n (fst qk) (snd qk)) (ablocks B ly3 S3) /\
  In (q, n) (ablocks B ly' S') /\ astr_atR (rdW W' mem') q (resp (-902)) /\
  (forall R O, rec_repA B ly3 S3 (rdW W3 mem) R O -> rec_repA B ly' S' (rdW W' mem') (fst (sup_resp_m R (-902))) O) /\
  blocks_bytes S' <= blocks_bytes S3 + LIVE_SUP_RESP (-902) /\
  mo_le MT S3 S' (XM_SUP_RESP MT (-902))).
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W3 regs mem (Z_to_bv 64 (BASE + AF_sup_resp)) CHAIN_WORDS_STK (cw_sp0 c)
    (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] ly3 S3 md 0 SUP_RESP_STK [] EV_SUP_RESP
    (cw_s1 c - cw_sp0 c) (Z_to_bv 64 (BASE + rk)) ch1 KR HJ Qsp).
  - exact (cw5_mod_sub (cw_s1 c) (cw_sp0 c) 16 ltac:(lia)
      (cw5_mod_of_div (cw_s1 c) 32 16 ltac:(lia) ltac:(exists 2; reflexivity) ltac:(lia) H32) H16).
  - lia.
  - exact HSTK3.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | exact Hrk2].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Hs0c. replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) by lia. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { apply (SUP_RESP fx ly3 S3 W3 regs mem md ch1 (-902) HPRE1 HFRM).
      - rewrite Hfr3, length_app. cbn [length]. pose proof (cp_frames _ _ _ HPRE). lia.
      - exact HROD.
      - exact HRO.
      - exact Q10'.
      - lia.
      - pose proof (cp_nev _ _ _ HPRE). unfold EV_CHAIN_WORDS in *. lia.
      - pose proof (cp_live _ _ _ HPRE). rewrite cw5_live_resp.
        unfold LIVE_CHAIN_WORDS, CHAIN_WORDS_MALLOCS, CHAIN_WORDS_REQ in *. lia.
      - apply (mo_ok_step MT MTL (x_S c) S3 0 (XM_SUP_RESP MT (-902))); [|exact Umeter].
        exact (mo_ok_le MT MTL _ _ _ (cp_meter _ _ _ HPRE) (cw5_xm_resp MTL (x_R c))). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W4 c4 Hwle4 (fx1 & ly4 & S4 & regs4 & mem4 & md4 & Hfx & -> & HJ4 & HJc4 & HP4 & HK4).
exists fx1, ly4, S4, regs4, mem4, md4. split; [exact Hfx|]. split; [reflexivity|].
unfold KR in HK4. destruct HK4 as (q & Hq10 & Hq4096 & Hperm & Hapart & Hqin & Hstr & Hrec & Hbb4 & Hmle).
split.
{ exact (cw5_fi_call c 0 EV_SUP_RESP ly3 S3 W3 regs mem md ly4 S4 W4 regs4 mem4 md4 SUP_RESP_STK
    (cw_sp0 c + (cw_s1 c - cw_sp0 c)) [] HPRE HFI HJ4 HJc4 ltac:(lia)
    (fun a Ha => False_ind _ (inFP_nil a Ha)) (fun a _ Ha => inFP_nil a Ha) HP4). }
split; [exact HP4|].
split.
{ exact (cw5_spills_call c ly3 S3 W3 mem md ly4 S4 W4 mem4 md4 SUP_RESP_STK (cw_sp0 c + (cw_s1 c - cw_sp0 c)) []
    EV_SUP_RESP HPRE HJc4 ltac:(lia) (fun a Ha => False_ind _ (inFP_nil a Ha))). }
unfold cw_Q, cw_Qr. cbv beta. rewrite HRUN. unfold sup_resp_m. change Verbs.err_invalid_operation with (-902). cbv beta iota.
set (n := Z.of_nat (length (resp (-902))) + 1) in *.
assert (Hn : n = 10) by (subst n; vm_compute; reflexivity).
exists (x_O c), q, n.
assert (HnO : ~ In (q, n) (x_O c)).
{ intros Hin. pose proof (cw5_rec_repA_in_blocks _ _ _ _ _ _ HREC Hin) as Hb.
  pose proof (proj1 (Forall_forall _ _) Hapart _ Hb) as Ha. unfold iv_apart in Ha. cbn [fst snd] in Ha. lia. }
split; [exact (Hrec _ _ HREC)|].
split; [exact Hq10|].
split; [exact Hq4096|].
split; [exact Hqin|].
split; [exact HnO|].
split.
{ intros Hin. exfalso.
  assert (Hpn3 : In (q, n) (ablocks B ly3 S3)) by (eapply Permutation_in; [exact (Permutation_sym Uperm) | exact Hin]).
  pose proof (proj1 (Forall_forall _ _) Hapart _ Hpn3) as Ha. unfold iv_apart in Ha. cbn [fst snd] in Ha. lia. }
split; [exact Hstr|].
split; [lia|].
split.
{ intros pn Hpn _. assert (Hpn3 : In pn (ablocks B ly3 S3)) by (eapply Permutation_in; [exact (Permutation_sym Uperm) | exact Hpn]).
  pose proof (proj1 (Forall_forall _ _) Hapart _ Hpn3) as Ha. unfold iv_apart in *. lia. }
split.
{ intros pn Hpn _. assert (Hpn3 : In pn (ablocks B ly3 S3)) by (eapply Permutation_in; [exact (Permutation_sym Uperm) | exact Hpn]).
  eapply Permutation_in; [exact (Permutation_sym Hperm) | right; exact Hpn3]. }
split.
{ intros pn Hpn. assert (Hpn' : In pn ((q, n) :: ablocks B ly3 S3)) by (eapply Permutation_in; [exact Hperm | exact Hpn]).
  destruct Hpn' as [Heq | Hpn3]; [right; right; symmetry; exact Heq|].
  assert (Hpn0 : In pn (ablocks B (x_ly c) (x_S c))) by (eapply Permutation_in; [exact Uperm | exact Hpn3]).
  destruct (in_dec cw5_pz_eq_dec pn (x_O c)) as [HO | HO]; [right; left; exact HO | left; split; [exact Hpn0 | exact HO]]. }
split; [intros pn Hpn; left; exact Hpn|].
split.
{ rewrite cw5_live_resp in Hbb4. unfold LIVE_CHAIN_WORDS, CHAIN_WORDS_MALLOCS, CHAIN_WORDS_REQ. lia. }
apply (mo_le_mono MT MTL _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ Umeter Hmle)).
exact (cw5_xm_resp MTL (x_R c)).
Qed.
End e.
End f.
End d.
(* the segment, at the FP state of the cut: the call of sup_resp returns at some fx1 (cw5_call_resp), and the join
   tail runs at fx1 (cw5_tail1 / cw5_tail2, lemmas of the closed section above, applied with (fx := fx1)) *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis SUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TRANSP : cw_transportP B MT.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma cw_S5 : cw_S5P B MT.
Proof.
intros c HPRE HFRM HKJ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (cw5_stk B MT c HPRE) as (H16 & Hlo & Htop & H47 & Hra4).
destruct (cw_s1_facts c H16) as (H32 & Hs1r).
assert (Hk : 0 <= 0 + EV_SUP_RESP <= EV_CHAIN_WORDS (x_R c)) by (unfold EV_CHAIN_WORDS, EV_SUP_RESP, EV_XMALLOC; lia).
split.
- (* KR1, 0x8dd5c .. 0x8dd60: a0 = -902, the call of sup_resp; then the tail from 0x8dd64 *)
  intros ly3 S3 W3 regs3 mem3 md3 ((HFI & HUN) & H19 & H22 & HRUN).
  pose proof HFI as [HJ Hsp Hgp Htp Hs0 Hs1 Hs2 Hs8 Hntok Hsaved Hflag].
  set (E := Eimg (Ereg regs3 [])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
    by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS CW_KR1 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CW_KR1)) mem3 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn. tauto.
    - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
  unfold cfg_at. change (w64 (BASE + CW_KR1)) with (Z_to_bv 64 (BASE + CW_KR1)).
  paj_run_shc RUNP RUNC HS HJ.
  { apply awr_ok_nil. }
  set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdv.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
  pmkst HS.
  assert (UQ : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
    by exact (cw5_rd_frame_ro E [] (w_H W3) mem3 (ms_mem ms) (Forall_nil _) HFr).
  assert (HFI1 : cw_fi B c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv).
  { constructor.
    - exact HJ.
    - rewrite Q2, (EE 2%nat 2%bv eq_refl). exact Hsp.
    - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - rewrite Q8, (EE 8%nat 8%bv eq_refl). exact Hs0.
    - rewrite Q9, (EE 9%nat 9%bv eq_refl). exact Hs1.
    - rewrite Q18, (EE 18%nat 18%bv eq_refl). exact Hs2.
    - rewrite Q24, (EE 24%nat 24%bv eq_refl). exact Hs8.
    - rewrite (cw5_rdword_same _ _ _ UQ). exact Hntok.
    - intros j r Hj. rewrite (cw5_rdword_same _ _ _ UQ). exact (Hsaved j r Hj).
    - rewrite (cw5_rdword_same _ _ _ UQ). exact Hflag. }
  pose proof (cw5_un_same B MT c ly3 S3 W3 mem3 (ms_mem ms) HUN UQ) as HUN1.
  assert (Q10' : getr (ms_regs ms) 10 = w64 (-902)) by (rewrite Q10; unfold w64; apply bv_eq; vm_compute; reflexivity).
  rewrite (proj2 (proj2 (cw_sig_of SIGP))).
  eapply srr_after_callF.
  { exact (cw5_call_resp B MT SUP_RESP MTL TRANSP c ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv 30772 HPRE HFRM HFI1 HUN1
      Q10' Q1 ltac:(lia) eq_refl HRUN). }
  intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfx (HFI2 & HPR2 & _ & HQ2).
  assert (H19' : getr regs2 19 = w64 (cw_F c)).
  { rewrite (cw5_pres_get (ms_regs ms) regs2 19%bv 19 HPR2 ltac:(unfold acallee_saved; lia) eq_refl), Q19.
    rewrite (EE 19%nat 19%bv eq_refl). exact H19. }
  assert (H22' : getr regs2 22 = w64 (cw_F c)).
  { rewrite (cw5_pres_get (ms_regs ms) regs2 22%bv 22 HPR2 ltac:(unfold acallee_saved; lia) eq_refl), Q22.
    rewrite (EE 22%nat 22%bv eq_refl). exact H22. }
  exact (cw5_tail1 (fx := fx1) B MT c (0 + EV_SUP_RESP) ly2 S2 W2 regs2 mem2 md2 HPRE (HKJ fx1 Hfx) Hk HFI2
    H19' H22' HQ2).
- (* KR2, 0x8dd6c .. 0x8dd70: a0 = -902, the call of sup_resp; then the tail from 0x8dd74 *)
  intros ly3 S3 W3 regs3 mem3 md3 ((HFI & HUN) & HSP & HRUN).
  pose proof HFI as [HJ Hsp Hgp Htp Hs0 Hs1 Hs2 Hs8 Hntok Hsaved Hflag].
  set (E := Eimg (Ereg regs3 [])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
    by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (mkSS CW_KR2 sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CW_KR2)) mem3 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn. tauto.
    - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
  unfold cfg_at. change (w64 (BASE + CW_KR2)) with (Z_to_bv 64 (BASE + CW_KR2)).
  paj_run_shc RUNP RUNC HS HJ.
  { apply awr_ok_nil. }
  set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdv.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24.
  pmkst HS.
  assert (UQ : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
    by exact (cw5_rd_frame_ro E [] (w_H W3) mem3 (ms_mem ms) (Forall_nil _) HFr).
  assert (HFI1 : cw_fi B c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv).
  { constructor.
    - exact HJ.
    - rewrite Q2, (EE 2%nat 2%bv eq_refl). exact Hsp.
    - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - rewrite Q8, (EE 8%nat 8%bv eq_refl). exact Hs0.
    - rewrite Q9, (EE 9%nat 9%bv eq_refl). exact Hs1.
    - rewrite Q18, (EE 18%nat 18%bv eq_refl). exact Hs2.
    - rewrite Q24, (EE 24%nat 24%bv eq_refl). exact Hs8.
    - rewrite (cw5_rdword_same _ _ _ UQ). exact Hntok.
    - intros j r Hj. rewrite (cw5_rdword_same _ _ _ UQ). exact (Hsaved j r Hj).
    - rewrite (cw5_rdword_same _ _ _ UQ). exact Hflag. }
  pose proof (cw5_un_same B MT c ly3 S3 W3 mem3 (ms_mem ms) HUN UQ) as HUN1.
  pose proof (cw5_spills_same c W3 mem3 (ms_mem ms) HSP UQ) as HSP1.
  assert (Q10' : getr (ms_regs ms) 10 = w64 (-902)) by (rewrite Q10; unfold w64; apply bv_eq; vm_compute; reflexivity).
  rewrite (proj2 (proj2 (cw_sig_of SIGP))).
  eapply srr_after_callF.
  { exact (cw5_call_resp B MT SUP_RESP MTL TRANSP c ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv 30788 HPRE HFRM HFI1 HUN1
      Q10' Q1 ltac:(lia) eq_refl HRUN). }
  intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfx (HFI2 & _ & HSPc & HQ2).
  exact (cw5_tail2 (fx := fx1) B MT c (0 + EV_SUP_RESP) ly2 S2 W2 regs2 mem2 md2 (CW_KR2 + 8) (or_intror eq_refl)
    HPRE (HKJ fx1 Hfx) Hk HFI2 (HSPc HSP1) HQ2).
Qed.
End e2.
End f2.
End d2.
