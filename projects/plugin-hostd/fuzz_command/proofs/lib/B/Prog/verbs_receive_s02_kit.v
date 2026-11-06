(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the kit of segment S02 (DUP, 0x8cf9c-0x8cff8) of the ASan+UBSan (image B) walk
   of verbs_receive on plugin-hostd/fuzz_command: from the state the prologue leaves (vr_b1 of
   lib/B/Prog/verbs_receive_iface.v) the message size is checked, strndup(data, data_size) takes the line, the frame's
   shadow is opened over tok and save, save is cleared and strlen measures the line; the segment ends at vr_b2 (a
   non-empty line) or at vr_b3 (an empty one, which is already trimmed).

   The B twin of lib/A/Prog/verbs_receive_s02_kit.v (a working branch). What differs from A:
   B enters the segment with a0 = msg + 8 (0x8cf88, S01's inline check of msg+8) and loads the data pointer through
   a0 (`ld a0,0(a0)`, 0x8cfb0), so the symbolic state at the entry holds the message struct as two regions: the size
   word through s8 (msg + 16) and the data word through a0 (msg + 8). The GOT words of cmd_got_ok are B's
   (CmdRep.v), read off cmd_ro_ok by the same generic argument as verbs_receive_s30_kit.v's. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PSF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.
Module PVP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_pre.

(* the two pure facts the duplication needs of the model: with a buffer of exactly n bytes the interceptor's
   memchr premise is free, and the prefix it copies is the line before the trim *)
Lemma vr_memchr_full : forall (D : list byte) (n : Z), n = Z.of_nat (length D) -> PSF.memchr_ok 0 0 n D.
Proof.
intros D n ->. unfold PSF.memchr_ok.
destruct (PSF.find_byte 0 (firstn (Z.to_nat (Z.of_nat (length D))) D)) as [j|]; [left; lia | lia].
Qed.

Lemma vr_upto_firstn : forall (D : list byte) (n : Z), n = Z.of_nat (length D) ->
firstn (Z.to_nat (PSF.strnlen_res n D)) D = PV.upto0 D /\ PSF.strnlen_res n D = Z.of_nat (length (PV.upto0 D)).
Proof. intros D n ->. exact (PVP.strnlen_upto D). Qed.

(* an empty prefix is already trimmed *)
Lemma vr_line_nil : forall (D : list byte) (n : Z), n = Z.of_nat (length D) -> PSF.strnlen_res n D = 0 ->
PV.line D = [].
Proof.
intros D n Hn H0. destruct (vr_upto_firstn D n Hn) as [_ Hlen]. rewrite H0 in Hlen.
unfold PV.line, PV.trim. destruct (PV.upto0 D) as [|x l] eqn:E; [reflexivity|]. cbn [length] in Hlen. lia.
Qed.

(* the bytes of the prefix hold no terminator *)
Lemma vr_upto0_no0 : forall D : list byte, ~ In (Z_to_bv 8 0) (PV.upto0 D).
Proof.
intros D. unfold PV.upto0. induction D as [|x D IH]; cbn [PV.upto]; [intros []|].
destruct (bv_unsigned x =? 0) eqn:Ex; [intros []|].
intros [Hx | Hin]; [|exact (IH Hin)].
subst x. vm_compute in Ex. discriminate Ex.
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

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* ----------------------------------------------------------------------------------------------------------
   The Section hypotheses: the record facts of the interface's list that the lemmas below read *)
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ----------------------------------------------------------------------------------------------------------
   The journal reads memory only through [aview] and asks for presence only inside the caller's stack window, so
   a memory with the same view that is present over that window carries the same journal. *)
Lemma aj_view_eq : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc',
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc' a) ->
AR SEGS B lyc Sc Wc memc' mdc ->
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc'
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & _ & Hstatic & F5 & HQT) HV HP HAR'.
split; [exact HAR'|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [intros a H1 H2 H3; rewrite HV; exact (F1 a H1 H2 H3)|].
split; [intros p n i H1 H2 H3 H4; rewrite HV; exact (F2 p n i H1 H2 H3 H4)|].
split; [intros a H1 H2 H3 H4; rewrite HV; exact (F3 a H1 H2 H3 H4)|].
split; [intros c p a H1 H2 H3; rewrite HV; exact (F4 c p a H1 H2 H3)|].
split; [exact Hgone|]. split; [exact HP|]. split; [exact Hstatic|].
split; [intros a H1 H2; rewrite HV; exact (F5 a H1 H2) | exact HQT].
Qed.

(* ----------------------------------------------------------------------------------------------------------
   The step through a shadow-fill entry: the entry writes only the shadow of a frame this call owns, so the
   journal of the walk goes on through it with the same event count (cgif's aj_intrin_atS has this shape for the
   entries that write memory; RtShadow's contract is not in journal form).

   The entry's contract gives the bytes it set and the bytes it kept, as views, and presence only over the
   scratch window, so the journal is first built over the memory [memT] patched with what the entry wrote (which
   does keep presence everywhere) and then moved to the entry's own memory, whose view is the same. *)
Definition patch_mem (H : word -> bool) (memT mem2 : word -> option byte) (q n : Z) : word -> option byte :=
fun x => if H x then mem2 x
         else if ((q <=? bv_unsigned x) && (bv_unsigned x <? q + n))%bool then mem2 x
         else match mem2 x with Some b => Some b | None => memT x end.

Lemma patch_view : forall (W : world SEGS) memT mem2 q n,
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
forall a, aview SEGS (w_H W) (patch_mem (w_H W) memT mem2 q n) a = aview SEGS (w_H W) mem2 a.
Proof.
intros W memT mem2 q n Hkeep a.
set (x := Z_to_bv 64 a). set (u := bv_unsigned x).
assert (Hu : 0 <= u < 2 ^ 64) by (subst u; pose proof (bv_unsigned_in_range 64 x) as R;
  change (bv_modulus 64) with (2 ^ 64) in R; lia).
assert (Hxu : Z_to_bv 64 u = x) by (subst u; apply Z_to_bv_bv_unsigned).
unfold aview, mbyte, mrestrict, patch_mem. fold x. fold u.
destruct (w_H W x) eqn:EH; [reflexivity|].
destruct ((q <=? u) && (u <? q + n))%bool eqn:Eb; [reflexivity|].
assert (Hout : ~ (q <= u < q + n)).
{ intros [A1 A2]. apply Bool.andb_false_iff in Eb as [E|E];
  [apply Z.leb_nle in E | apply Z.ltb_nlt in E]; lia. }
destruct (mem2 x) as [b|] eqn:Em; [reflexivity|].
destruct (memT x) as [b'|] eqn:EmT; [|reflexivity].
pose proof (Hkeep u Hu Hout) as HK. unfold aview, mbyte, mrestrict in HK. rewrite Hxu, EH, Em, EmT in HK.
destruct (seg_rom SEGS x) as [br|] eqn:Er; cbn [option_map] in HK |- *; congruence.
Qed.

Lemma aj_set_shadow_at : forall v pcx, RtShadow.aset_shadow_realizes SEGS B pcx v -> 0 <= v < 256 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
In (cid, pos) own -> 0 <= cid ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q ->
q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pcx) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros v pcx SH Hv W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hsp Hal Hneg Hbud Hra Hrok Hgp Htp Hown Hcid H10 H11 Hn Hlo Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
(* the shadow of a frame lies in the shadow band, below the allocation ceiling and so below the stack *)
assert (Hfr64 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by (unfold kHighMemEnd; zlia).
assert (Hfs64 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by (unfold kHighMemEnd; zlia).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) Hfr64) as Hsb.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) Hfs64) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hse.
unfold kLowMemEnd, kHighShadowEnd in Hsb, Hsb2.
assert (Hqlo : 0x7fff8000 <= q) by zlia.
assert (Hqhi : q + n <= 0x10007fff8000) by zlia.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg Hbud);
  [rewrite Hra; exact Hrok | exact Hgp | exact Htp]. }
eapply SRr_mono; [exact (SH lyc Sc W regsT memT mdc cid pos q n HPRE Hin H10 H11 Hn Hlo Hhi)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & Hset & Hkeep & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
(* every byte the entry wrote lies in the shadow band, where no segment of the image backs it *)
assert (Hshq : forall a, q <= a < q + n -> ~ in_img SEGS a /\ 0 <= a < 2 ^ 64).
{ intros a Ha. split; [intros Hi; pose proof (pa_img_range a Hi); lia | lia]. }
assert (Hmem2 : forall a, q <= a < q + n -> exists b, mem2 (Z_to_bv 64 a) = Some b).
{ intros a Ha. pose proof (Hset (a - q) ltac:(lia)) as Hs. replace (q + (a - q)) with a in Hs by lia.
  destruct (Hshq a Ha) as [Hni Hb64].
  unfold aview, mbyte, mrestrict in Hs.
  destruct (w_H W (Z_to_bv 64 a)) eqn:EH;
    [rewrite (seg_rom_none SEGS a Hb64 Hni) in Hs; cbn in Hs; discriminate Hs|].
  destruct (mem2 (Z_to_bv 64 a)) as [b|] eqn:Em; [exists b; reflexivity|].
  rewrite (seg_rom_none SEGS a Hb64 Hni) in Hs. cbn in Hs. discriminate Hs. }
set (memP := patch_mem (w_H W) memT mem2 q n).
assert (HVP : forall a, aview SEGS (w_H W) memP a = aview SEGS (w_H W) mem2 a)
  by (subst memP; apply (patch_view W memT mem2 q n Hkeep)).
assert (HJP : ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memP md2 k).
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k memP md2
    (fun a => q <= a < q + n) Sc own HJ).
  - intros a Ha Hna. rewrite HVP. apply Hkeep; [exact Ha | exact Hna].
  - intros a Hap. destruct Hap as [HH [b Hb]].
    destruct ((q <=? bv_unsigned (Z_to_bv 64 a)) && (bv_unsigned (Z_to_bv 64 a) <? q + n))%bool eqn:Eb.
    + pose proof Eb as Eb'. apply Bool.andb_true_iff in Eb' as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      destruct (Hmem2 (bv_unsigned (Z_to_bv 64 a)) ltac:(lia)) as [b2 Hb2].
      rewrite Z_to_bv_bv_unsigned in Hb2.
      split; [exact HH|]. exists b2. subst memP. unfold patch_mem. rewrite HH, Eb. exact Hb2.
    + split; [exact HH|]. subst memP. unfold patch_mem. rewrite HH, Eb.
      destruct (mem2 (Z_to_bv 64 a)) as [b2|]; [exists b2; reflexivity | exists b; exact Hb].
  - exact Hsame.
  - intros a Ha. left. right; right; right; left. exists cid, pos. split; [exact Hown|]. right.
    unfold in_zr. cbn [fst snd]. lia.
  - eapply (al_frame SEGS B LAWS lyc Sc W mem2 md2 memP md2);
    [ exact HAR2
    | intros a _ _; rewrite HVP; reflexivity
    | intros a Hv2; rewrite HVP; exact Hv2
    | reflexivity | reflexivity | reflexivity
    | intros a _ Hh; subst memP; unfold patch_mem; rewrite Hh; reflexivity ].
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split.
{ eapply (aj_view_eq STK sp0 FP ly S W0 mem md own lyc Sc W memP md2 k mem2 HJP).
  - intros a. symmetry. exact (HVP a).
  - intros a Ha.
    pose proof HJP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresP & _).
    destruct (HpresP a Ha) as [HH [b Hb]]. split; [exact HH|].
    subst memP. unfold patch_mem in Hb. rewrite HH in Hb.
    destruct ((q <=? bv_unsigned (Z_to_bv 64 a)) && (bv_unsigned (Z_to_bv 64 a) <? q + n))%bool eqn:Eb;
      [exists b; exact Hb|].
    destruct (mem2 (Z_to_bv 64 a)) as [b2|] eqn:Em; [exists b2; reflexivity|].
    (* the stack window is above the allocation ceiling, so the entry's own window keeps it present *)
    exfalso. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
    destruct (HpresJ a Ha) as [HH0 [b0 Hb0]].
    pose proof (Hkeep a) as HK.
    pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
    assert (Hb64 : 0 <= a < 2 ^ 64) by zlia.
    assert (Hout : ~ (q <= a < q + n)) by zlia.
    specialize (HK Hb64 Hout). unfold aview, mbyte, mrestrict in HK.
    rewrite HH0, Hb0, Em in HK. cbn [option_map] in HK.
    destruct (seg_rom SEGS (Z_to_bv 64 a)) as [br|] eqn:Er; cbn [option_map] in HK; [|discriminate HK].
    pose proof (seg_rom_in_img SEGS a Hb64 ltac:(rewrite Er; discriminate)) as Hi.
    pose proof (pa_img_range a Hi). zlia.
  - exact HAR2. }
split; [exact HP2|]. split; [exact Hset | exact Hkeep].
Qed.

(* ----------------------------------------------------------------------------------------------------------
   The footprint of this call holds no byte of the shadow band: its program statics are three low objects of the
   image and its blocks are application memory. *)
Lemma vr_fp_not_shadow : forall e lyc Sc (Wc : world SEGS) memc mdc a,
AR SEGS B lyc Sc Wc memc mdc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc)) ->
kLowMemEnd <= a < kHighMemBeg -> ~ inFP (vr_fp e) a.
Proof.
intros e lyc Sc Wc memc mdc a HAR HO Ha (r & Hin & Hr).
unfold vr_fp, VERBS_RECEIVE_PG in Hin. apply in_app_or in Hin as [Hin | Hin].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE, kLowMemEnd, kHighMemBeg in *.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
- apply in_map_iff in Hin as ([p m] & <- & Hpm). cbn [fst snd] in Hr.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p m HAR (HO _ Hpm)) as (_ & _ & _ & [Hh1 Hh2] & _).
  unfold in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. zlia.
Qed.

(* nothing of this call's footprint lies at or above the allocation ceiling *)
Lemma vr_fp_below : forall e ly S (Wc : world SEGS) memc mdc a,
AR SEGS B ly S Wc memc mdc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
alloc_ceiling <= a -> ~ inFP (vr_fp e) a.
Proof.
intros e ly S Wc memc mdc a HAR HO Ha (r & Hin & Hr).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
unfold vr_fp, VERBS_RECEIVE_PG in Hin. apply in_app_or in Hin as [Hin | Hin].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in *.
  cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
- apply in_map_iff in Hin as ([p m] & <- & Hpm). cbn [fst snd] in Hr.
  destruct (al_blocks _ _ LAWS ly S Wc memc mdc p m HAR (HO _ Hpm)) as (_ & _ & Hc & _). lia.
Qed.

(* the read-only bytes of the statement's range lie in the image, so a call keeps them *)
Lemma vr_roP_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)].
Qed.

(* the four GOT words the recorder reads are read-only bytes of the image (B's CmdRep.v cmd_got_ok, CmdRo.v) *)
Lemma s2_aval_of_bytes : forall (rd : reader) a (l : list byte) v,
abytes_atR rd a l -> length l = 8%nat -> (forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) ->
aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hk8. rewrite (H k ltac:(lia)). rewrite Hk by exact Hk8. reflexivity. Qed.
Lemma s2_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. decompose [and] Hb. clear Hb.
unfold cmd_got_ok. split; [|split; [|split]];
(eapply s2_aval_of_bytes; [eassumption | reflexivity |];
 intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
Qed.

(* the environment of the walk at any state of the journal whose read-only bytes are kept *)
Lemma s2_env_of_aro : forall lyc Sc (W2 : world SEGS) mem2 mdc,
AR SEGS B lyc Sc W2 mem2 mdc -> arodata_okP SEGS RLO RHI B (rdW W2 mem2) -> vr_env B W2 mem2.
Proof.
intros lyc Sc W2 mem2 mdc HAR2 HROD2.
pose proof (ROA lyc Sc W2 mem2 mdc HAR2 HROD2) as HRO2.
destruct (RECC lyc Sc W2 mem2 mdc HAR2) as (Hf & Hg & [ev He]).
split; [exact HROD2|]. split; [exact (s2_got_of_ro _ HRO2)|]. split; [exact HRO2|].
split; [exact Hg|]. split; [exact Hf | exists ev; exact He].
Qed.

(* the shadow cells of an application range lie in the shadow band *)
Lemma vr_shadow_band : forall x n, 0 <= x -> 0 <= n -> x + n <= alloc_ceiling ->
kLowMemEnd <= shadow_addr x /\ shadow_addr (x + n) < kHighMemBeg.
Proof.
intros x n Hx Hn Hxn. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H2 : (x + n) / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; [lia | zlia]).
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg. zlia.
Qed.

(* a 16-aligned value is 8-aligned *)
Lemma vr_al8_of_al16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
destruct H as [c Hc]. exists (2 * c). lia.
Qed.

(* a 64-aligned value is 8-aligned *)
Lemma vr_al8_of_al64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
destruct H as [c Hc]. exists (8 * c). lia.
Qed.

(* a register of a boundary's list *)
Lemma s2_rv_get : forall (regs : bvmap 5 word) l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.

(* no byte of a live frame is in this call's footprint: the program statics it writes are image bytes, which a
   frame never meets, and its blocks are apart from every frame *)
Lemma vr_fp_not_frame : forall e ly S (Wc : world SEGS) memc mdc cid pos' a,
AR SEGS B ly S Wc memc mdc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
In (cid, pos') (frames S) ->
frame_addr ly cid pos' <= a < frame_addr ly cid pos' + fs_frame_bytes cid ->
~ inFP (vr_fp e) a.
Proof.
intros e ly S Wc memc mdc cid pos' a HAR HO Hin Ha (r & Hr & Hrr).
pose proof (frm_off_imgP B ly S Wc memc mdc cid pos' HAR Hin) as Hoff. unfold off_img in Hoff.
unfold vr_fp, VERBS_RECEIVE_PG in Hr. apply in_app_or in Hr as [Hr | Hr].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in *.
  cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrr; zlia.
- apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Hrr.
  pose proof (sep_block_frame SEGS B LAWS ly S Wc memc mdc p m cid pos' HAR (HO _ Hpm) Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
Qed.

(* the message object of the caller's frame, and the shadow bytes of it, are kept by the journal of the walk *)
Lemma vr_caller_kept : forall e own lyc Sc (Wc : world SEGS) memc mdc kk a,
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  own lyc Sc Wc memc mdc kk ->
AR SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) ->
afobj SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_msg e) 24 ->
(forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e))) ->
(e_msg e <= a < e_msg e + 24 \/ (exists i, 0 <= i < 3 /\ a = shadow_addr (e_msg e) + i)) ->
rdW Wc memc a = rdW (e_W e) (e_mem e) a.
Proof.
intros e own lyc Sc Wc memc mdc kk a HJ HAR0 ((cid & pos' & Hin & Hcid & Hal & Hlo & Hhi) & Hmod & _) HO Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof (shadow_mono (frame_addr (e_ly e) cid pos') (e_msg e) Hlo) as M1.
pose proof (shadow_range_end (frame_addr (e_ly e) cid pos') (fs_frame_bytes cid) Hfb) as M2.
pose proof (shadow_mono (e_msg e + 24) (frame_addr (e_ly e) cid pos' + fs_frame_bytes cid) Hhi) as M3.
destruct (frames_bounds SEGS B LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' HAR0 Hin) as (Hf0 & Hfc & Hfapp).
apply F4 with (cid := cid) (pos := pos'); [exact Hin | |].
- destruct Ha as [Ha | (i & Hi & ->)].
  + left. unfold in_zr, frame_rng. cbn [fst snd]. zlia.
  + right. unfold in_zr. cbn [fst snd].
    destruct (frame_al64 SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' HAR0 Hin)
      as (Ha64 & Hb64 & Hge64).
    pose proof (vr_al8_of_al64 _ Ha64) as Hf8. pose proof (vr_al8_of_al64 _ Hb64) as Hs8.
    pose proof (Z.div_mod (e_msg e) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (e_msg e) 8 ltac:(lia)) as P1.
    pose proof (Z.div_mod (frame_addr (e_ly e) cid pos') 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (frame_addr (e_ly e) cid pos') 8 ltac:(lia)) as P2.
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as P3.
    unfold shadow_addr, SHADOW_OFF in *. zlia.
- destruct Ha as [Ha | (i & Hi & ->)].
  + exact (vr_fp_not_frame e (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) cid pos' a HAR0 HO Hin ltac:(zlia)).
  + destruct (vr_shadow_band (e_msg e) 24 ltac:(zlia) ltac:(lia) ltac:(zlia)) as [Hb1 Hb2].
    apply (vr_fp_not_shadow e (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) _ HAR0 HO).
    pose proof (shadow_mono (e_msg e) (e_msg e + 24) ltac:(lia)) as Hmo.
    pose proof (Z.div_mod (e_msg e) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (e_msg e) 8 ltac:(lia)) as P1.
    pose proof (Z.div_mod (e_msg e + 24) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (e_msg e + 24) 8 ltac:(lia)) as P2.
    unfold shadow_addr, SHADOW_OFF in *. zlia.
Qed.

(* the boundary states say aval_mem; the regions and the chain read through val_mem *)
Lemma VAMg : forall (Wx : world SEGS) memx a n v, aval_mem (rdW Wx memx) a n v ->
val_mem SEGS (mrestrict (w_H Wx) memx) a n v.
Proof.
intros Wx memx a n v Hv kx Hkx. pose proof (Hv kx Hkx) as Hb.
destruct (aview_byte SEGS (w_H Wx) memx _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

(* the unwinder's chain at a call inside this frame: the prologue saved ra at sp0-8 and the caller's s0 at
   sp0-16, so either the chain of the caller extends by this frame, or this frame is at the top of the stack
   window and the chain is empty. *)
Lemma s2_chain_at : forall e own lyc Sc (Wc : world SEGS) memc mdc kk (regsx : bvmap 5 word),
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  own lyc Sc Wc memc mdc kk ->
afn_pre SEGS B VERBS_RECEIVE_STK (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) ->
vr_saved e Wc memc ->
(forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e))) ->
spZ regsx = vr_s1 e -> s0Z regsx = vr_sp0 e -> 4096 <= raZ regsx ->
exists ch', chain_pre lyc (rdW Wc memc) regsx ch'.
Proof.
intros e own lyc Sc Wc memc mdc kk regsx HJ HPRE0 HSAV HOincl Hsp Hs0 Hra.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstat & _).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof Hstat as (Hal16 & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (HAS : ASTACK = 16384) by reflexivity.
assert (HSTKge : 208 + ASTACK <= VERBS_RECEIVE_STK).
{ unfold VERBS_RECEIVE_STK. pose proof (Z.le_max_r VR_CALLEE_STK (Z.max ASTACK (4 * ESTACK))) as Hm1.
  pose proof (Z.le_max_l ASTACK (4 * ESTACK)) as Hm2. lia. }
assert (Hs1 : vr_sp0 e - 224 <= vr_s1 e <= vr_sp0 e - 192).
{ unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hmb.
  remember ((vr_sp0 e - 192) mod 32) as r32 eqn:Hr32. clear Hr32. lia. }
assert (Hcei : alloc_ceiling <= vr_s1 e) by lia.
(* the bytes above sp0 are the caller's and the journal keeps them *)
assert (HK : forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW Wc memc a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. apply F1; [zlia | zlia|].
  exact (vr_fp_below e (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) a HAR0 HOincl ltac:(lia)). }
destruct (Z_lt_le_dec (vr_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- (* the chain of the caller, with this frame on top *)
  assert (HR1 : rdword (rdW Wc memc) (vr_sp0 e - 8) = Some (bv_unsigned (getr (e_regs e) (Z_to_bv 5 1)))).
  { apply (rdword_of_val_mem SEGS (w_H Wc) memc); [|pose proof (bv_unsigned_in_range 64 (getr (e_regs e) (Z_to_bv 5 1)));
      change (bv_modulus 64) with (2 ^ 64) in *; lia].
    apply VAMg. replace (vr_sp0 e - 8) with (vr_sp0 e - 8 - 8 * Z.of_nat 0) by lia.
    exact (HSAV 0%nat 1 eq_refl). }
  assert (HR2 : rdword (rdW Wc memc) (vr_sp0 e - 16) = Some (s0Z (e_regs e))).
  { apply (rdword_of_val_mem SEGS (w_H Wc) memc); [|unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 8));
      change (bv_modulus 64) with (2 ^ 64) in *; lia].
    apply VAMg. replace (vr_sp0 e - 16) with (vr_sp0 e - 8 - 8 * Z.of_nat 1) by lia.
    exact (HSAV 1%nat 8 eq_refl). }
  exists ((vr_sp0 e, bv_unsigned (getr (e_regs e) (Z_to_bv 5 1)), s0Z (e_regs e)) :: e_ch e).
  apply (achain_chain_pre lyc (rdW Wc memc) (vr_s1 e) (vr_sp0 e) _ regsx).
  + apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
    apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW Wc memc) (vr_sp0 e) (s0Z (e_regs e))
      (bv_unsigned (getr (e_regs e) (Z_to_bv 5 1))) (e_ch e) (vr_s1 e) Hch0);
      [zlia | exact HK | exact HR1 | exact HR2 | unfold raZ in Hra40; exact Hra40 | lia
       | exact (vr_al8_of_al16 _ Hal16) | lia | lia].
  + lia.
  + exact Hs0.
  + exact Hra.
- (* the frame is at the top of the window: the unwinder stops at once *)
  exists []. apply (achain_chain_pre lyc (rdW Wc memc) (vr_s1 e) (vr_sp0 e) [] regsx); [|lia|exact Hs0|exact Hra].
  left. split; [right; left; rewrite Etop; exact Hge | reflexivity].
Qed.

(* the symbolic state at the entry of the segment (0x8cf9c): B enters with a0 = msg + 8 and s8 = msg. The check
   at 0x8cf9c-0x8cfac reads the shadow of msg+16 through s8; the size word is loaded through a1 = s8 + 16 and the
   data word through a0 (0x8cfb0), so the message struct is two regions, msg+16 based on s8 and msg+8 based on a0 *)
Definition vr_msg16_region : YP09.region :=
YP09.mkRegion (Some 24%nat) 16 24 24 24 [YP09.mkChunk 16 (CVal 8 (SOff 33 0))].
Definition vr_msg8_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 8 8 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition vr_s02_ss : sstate :=
mkSS (AF_verbs_receive + 0x150) sr_atoms [vr_msg16_region; vr_msg8_region] None
  (mkFacts [(19%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, HPTR 3)] [] []).
Definition vr_Bx : sv := SOff 19 0.
Definition vr_SH : list shent := [mkSHE 24 0 24].
Definition vr_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* ----------------------------------------------------------------------------------------------------------
   The symbolic state of the walk at the entry of the segment (0x8cf9c), seeded from vr_b1 the way cgif's AChc.v
   seeds a boundary: the registers as atoms, the message struct of the caller's frame as the two regions, and the
   shadow entry that removes the inline check of msg+16. *)
Lemma vr_s02_seed_ok : forall e (W : world SEGS) pos F lyc Sc regsc memc mdc k nm,
vr_ent B MT e ->
vr_core B MT e pos F [] vr_sh1 (vr_sl1 F) (vr_rl1 e F) (e_R e) (e_O e) (e_q0 e) k 0 nm 0
  lyc Sc W regsc memc mdc ->
exists E,
img_env VAL A_LIM E /\
st_ok_pi SEGS VAL E vr_s02_ss
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + (AF_verbs_receive + 0x150))) memc (seg_rom SEGS))) /\
sh_ok SEGS vr_Bx vr_SH E (mrestrict (w_H W) memc) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r) /\
ew E 32 = w64 (e_data e) /\ ew E 33 = w64 (e_n e).
Proof.
intros e W pos F lyc Sc regsc memc mdc k nm HENT HCORE0.
pose proof HENT as (HPRE0 & HROD0 & Hr10 & HOBJ & Hfd & Hdata & Hnv & Hnb & HlenD & Hinblk & HnotO & HbytesD & Hmsg64
  & HREC0 & Hcalls & Hans & Hrep & Hnrep & Hdecl & HPERM0 & Hq0 & HGOT0 & HRO0 & HROIN & HVOBJ & Herrno & Hflag
  & HguardE & Hfrlen & Hevb & Hlive & HMOK & HFRM0).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
cbv beta delta [vr_core] in HCORE0.
destruct HCORE0 as (HJ & Hkk & HMET & Hnmm & HFRM & HRV & HSAV & HSPL & HENV & HREC & HnOc & HPERM & HQV).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
assert (HOincl : forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn)).
(* the message object is where the caller's frame has it, and the journal keeps it *)
pose proof HOBJ as ((cidm & posm & Hinm & Hcidm & Halm & Hlom & Hhim) & Hmod8 & HRA0).
assert (HMSG : forall a, e_msg e <= a < e_msg e + 24 \/ (exists i, 0 <= i < 3 /\ a = shadow_addr (e_msg e) + i) ->
  rdW W memc a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. exact (vr_caller_kept e [(4, pos)] lyc Sc W memc mdc k a HJ HAR0 HOBJ HOincl Ha). }
assert (HRA : range_addressable (rdW W memc) SHADOW_OFF (e_msg e) 24).
{ intros x Hx. destruct (HRA0 x Hx) as (c & Hc & Hor). exists c. split; [|exact Hor].
  replace x with (e_msg e + (x - e_msg e)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (e_msg e) (x - e_msg e) Hmod8).
  rewrite HMSG.
  - rewrite <- (shadow_of_addr_aligned_off SHADOW_OFF (e_msg e) (x - e_msg e) Hmod8).
    replace (e_msg e + (x - e_msg e)) with x by lia. exact Hc.
  - right. exists ((x - e_msg e) / 8). split; [|unfold shadow_addr, shadow_of_addr; reflexivity].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
(* the registers of the boundary *)
assert (R10 : getr regsc (Z_to_bv 5 10) = w64 (e_msg e + 8)) by (apply (s2_rv_get regsc _ 10 _ HRV); cbn; tauto).
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 SHADOW_OFF) by (apply (s2_rv_get regsc _ 19 _ HRV); cbn; tauto).
assert (R24 : getr regsc (Z_to_bv 5 24) = w64 (e_msg e)) by (apply (s2_rv_get regsc _ 24 _ HRV); cbn; tauto).
(* the bounds of the message object and of the data block *)
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidm posm HAR0 Hinm) as (Hfm0 & Hfmc & Hfmapp).
pose proof (fs_frame_bytes_nonneg cidm) as Hfmb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_data e) (Z.max (e_n e) 1) HAR0 Hinblk) as (_ & Hd4096 & Hdceil & _).
pose proof (req_size_pos (Z.max (e_n e) 1) ltac:(lia)) as [Hrq1 Hrq2].
(* the environment of the symbolic state: the registers, then data and n *)
remember (Eimg (Ereg regsc [w64 (e_data e); w64 (e_n e)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j [w64 (e_data e); w64 (e_n e)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. cbn [Nat.add nth] in E32, E33.
assert (E10 : ew E 10 = w64 (e_msg e + 8)) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E19 : ew E 19 = w64 SHADOW_OFF) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E24 : ew E 24 = w64 (e_msg e)) by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl); exact R24).
assert (HROK : regs_ok E sr_atoms regsc) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
(* the message object's two words, at the current memory *)
assert (Hdata1 : aval_mem (rdW W memc) (e_msg e + 8) 8 (e_data e)).
{ intros kx Hkx. rewrite HMSG by (left; lia). exact (Hdata kx Hkx). }
assert (Hn1 : aval_mem (rdW W memc) (e_msg e + 16) 8 (e_n e)).
{ intros kx Hkx. rewrite HMSG by (left; lia). exact (Hnv kx Hkx). }
assert (HS : st_ok_pi SEGS VAL E vr_s02_ss
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + (AF_verbs_receive + 0x150))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold vr_s02_ss. apply pa_entry_st_ok_full.
  - exact HROK.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, vr_msg16_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E24. unfold w64. rewrite unsigned_lit_small by zlia.
      split; [zlia|]. split; [zlia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (e_msg e) 16 8 (SOff 33 0) (e_n e));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | zlia | cbn; zlia | exact (VAMg _ _ _ _ _ Hn1)].
    + unfold region_ok, vr_msg8_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E10. unfold w64. rewrite unsigned_lit_small by zlia.
      split; [zlia|]. split; [zlia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (e_msg e + 8) 0 8 (SOff 32 0) (e_data e));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | zlia | cbn; zlia | rewrite Z.add_0_r; exact (VAMg _ _ _ _ _ Hdata1)].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, vr_msg16_region, vr_msg8_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E24, E10. unfold w64. rewrite !unsigned_lit_small by zlia. lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite E19, E24. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; zlia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite Z.mod_1_r.
    split; [split; [lia | split; [reflexivity | lia]]|]. split; [|exact I].
    split; [zlia|]. split; [exact Hmod8 | lia]. }
assert (SHOK : sh_ok SEGS vr_Bx vr_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, vr_SH. apply Forall_cons; [|apply Forall_nil]. split.
  - unfold U, vr_Bx. cbn [sv_denot she_m she_lo she_hi]. rewrite E19, E24, !Z.add_0_r. unfold w64.
    rewrite !Z_to_bv_bv_unsigned, !unsigned_lit_small by (unfold SHADOW_OFF; zlia).
    replace (e_msg e + 0) with (e_msg e) by lia. replace (24 - 0) with 24 by lia. exact HRA.
  - intros a Ha Hband. unfold U, vr_Bx in *. cbn [sv_denot she_m she_lo she_hi] in *.
    rewrite E19, E24, !Z.add_0_r in *. unfold w64 in *.
    rewrite !Z_to_bv_bv_unsigned, !unsigned_lit_small in * by (unfold SHADOW_OFF; zlia).
    unfold SHADOW_OFF in Hband. zlia. }
exists E. split; [exact HEI|]. split; [exact HS|]. split; [exact SHOK|].
split; [exact EE|]. split; [exact E32 | exact E33].
Qed.

End e.
End f.
End d.
