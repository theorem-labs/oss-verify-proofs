(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the image-free part of libreac/fuzz_pcap's pcap_source_next kit (lib/A/Prog/PcapSourceNextKit.v, from proofs/cgif/cgif_file_fuzzer at origin/ossv/recipes c8557374ad2e and a Theorem Labs lane's libreac/fuzz_grant lib/A/Prog), shared by the walks of both images (lib/A, the ASan build; lib/B, the asan-ubsan build): it names no image, no listing and no image-specific kit file, and it Requires only lib/Reusable and the image-free lib/A/Prog files PaTable, PaSym, PaStep, PaRun, PaShadow, PaJournal, YC81 and YC4b. ajournal_sub_own and cl_callS_ownG are cgif lib/YC85.v's ajournal_sub_tok and cl_callS with one more case in the side condition, `awr_byte STK sp0 FP bl0 blc lyc own a` (a byte the caller's own journal may write: its stack window or one of the frames `own` it took), because the donor lemma admits only the caller's footprint and blocks allocated since the caller's start, and the header fread of pcap_source_next writes F + 32, inside the class-0 side-stack frame this call took; cl_callS_ownG is stated over any image (segs, segs_low) and each image's kit states cl_callS_own from it; acall_keptO and the region_kept_*_ajO lemmas are lib/Reusable/YCbq.v's acall_kept and lib/A/Prog/PcapFrame.v's region_kept lemmas without the image clause, because a callee whose footprint carries the sink token keeps no image byte by its journal alone (YCbq.v fp_spares); the tactics and the other lemmas are the generic parts of cgif lib/A/ACjr.v, ACj1.v and ACja.v as a Theorem Labs lane states them (fuzz_grant GrantACjr.v, ACj1.v, GrantACja.v) that name no image object: the walk's own side-stack frame, its shadow, the realigned stack and the stack keep cgif's atoms 516, 529, 60 and 2, awrFL_at takes them as arguments, and the stack regions are placed by the atom's value (awr_ok_cons_stack_at), so a caller-journal walk is covered; the tactics that name an image's objects, kit lemmas or records (img_factsF, keptFL, aconstsF, reseat, ...) are in each image's PcapSourceNextKit.v; module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal YC81 YC4b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================================================================================== *)
(* 1. Composition of a callee whose footprint reaches this call's own frame or stack window.       *)
(* ============================================================================================== *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* A byte of one of the frames `own` a journal took: the frame is live in the journal's end state, it
   lies in the application range, and the byte is in the frame or in the frame's shadow. *)
Lemma in_frames_own_at : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
in_frames lyc own a ->
exists cid pos o1 o2, own = o1 ++ (cid, pos) :: o2 /\ In (cid, pos) (frames Sc) /\
4096 <= frame_addr lyc cid pos /\ frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling /\
in_app (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
((frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid) \/
 (kLowMemEnd <= a < kHighShadowEnd /\
  shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8)).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a HJ (cid & pos & Hin & Hr).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfapp).
apply in_split in Hin as (o1 & o2 & Eo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
exists cid, pos, o1, o2. split; [exact Eo|]. split; [exact HinC|]. split; [exact Hf0|]. split; [exact Hfc|].
split; [exact Hfapp|].
unfold in_zr in Hr; cbn [fst snd] in Hr. destruct Hr as [Hr | Hr]; [left; exact Hr | right].
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hs1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hs2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hs3.
split; [zlia | exact Hr].
Qed.

(* A byte the caller's journal may write, split by where it lies. *)
Lemma awr_fp_cases : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
inFP FP a \/ awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/ in_frames lyc own a \/
(alloc_ceiling <= a /\ sp0 - STK <= a < sp0).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a HJ [Hf | [Hw | [(Hf & _) | [Ht | Hof]]]].
- left. exact Hf.
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
  right. right. right. split; [lia | exact Hw].
- left. exact Hf.
- right. left. exact Ht.
- right. right. left. exact Hof.
Qed.

(* No byte of a live block is a byte of the frames `own` or of the stack window. *)
Lemma block_not_own : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k p n i,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
~ in_frames lyc own (p + i) /\ ~ (alloc_ceiling <= p + i).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k p n i HJ Hb Hi.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hb) as (_ & _ & Hceilb & [Hh1 Hh2] & _).
split; [|lia].
intros Hof.
destruct (in_frames_own_at STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (p + i) HJ Hof)
  as (cid & pos & o1 & o2 & _ & HinC & Hf0 & Hfc & Hfapp & Hr).
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc p n cid pos HAR Hb HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct Hr as [Hr | (Hs & _)]; zlia.
Qed.

(* cgif YC85.ajournal_sub_tok, with the callee's footprint allowed to reach every byte the caller's
   own journal may write (awr_byte): its stack window and the frames `own` it took, as well as its
   footprint and the blocks allocated since its start. The proof is the donor's, with the two new
   cases closed by block_not_own (blocks), frames_bounds / sep_frames_pos (the caller's older
   frames) and the window's floor alloc_ceiling. *)
Lemma ajournal_sub_own : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal segs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> inFP FP a \/ awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
ajournal segs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1 HJ HJ1 Hlo Hhi HF0.
assert (HF : forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
  in_frames lyc own a \/ (alloc_ceiling <= a /\ sp0 - STK <= a < sp0))
  by (intros a Ha; exact (awr_fp_cases STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a HJ (HF0 a Ha))).
clear HF0.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof HJ1 as (HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as [(r' & Hr' & H0') | [(b & n & Hin & _ & Hb) | [Hof | (Hw & _)]]].
- exists r'. split; [exact Hr' | exact H0'].
- exfalso. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). zlia.
- exfalso. destruct (in_frames_own_at STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k 0 HJ Hof)
    as (cid & pos & o1 & o2 & _ & _ & Hf0 & _ & _ & [Hr0 | (Hr0 & _)]); zlia.
- exfalso. zlia. }
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{ intros p n i H1 H2 Hi Hnf.
  assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
  { destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
    exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
  rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
  destruct (block_not_own STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k p n i HJ Hc2 Hi) as (Hno & Hnw).
  intros Hf1. destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hr) | [Hof | (Hw & _)]]];
  [exact (Hnf Hf) | | exact (Hno Hof) | exact (Hnw Hw)].
  assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{ intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). apply (G3 a Hi Hns He). intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- Efr in Hr.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
  apply (G4 cid pos a HinC); [unfold frame_rng, in_zr; cbn [fst snd]; exact Hr|].
  intros Hf1. destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hrb) | [Hof | (Hw & _)]]]; [exact (Hnf Hf) | | | destruct Hr as [Hr|Hr]; zlia].
  - destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
    pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    destruct Hr as [Hr|Hr]; zlia.
  - destruct (in_frames_own_at STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k a HJ Hof)
      as (c' & p' & o1 & o2 & Eo & HinC' & Hf0' & Hfc' & Hfh' & Hr').
    apply in_split in Hin as (g1 & g2 & Eg).
    assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
    { eapply (sep_frames_pos segs B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
      rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
    pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
    pose proof (fs_frame_bytes_nonneg c') as Hnn'.
    destruct Hr' as [Hr' | (Hlo1' & Hr')]; destruct Hr as [Hr | Hr]; [zlia | zlia | zlia |].
    destruct Hd as [Hd | Hd]; pose proof (shadow_mono _ _ Hd); zlia. }
split.
{ intros p n i H1 H2 Hi.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
  assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
  destruct (block_not_own STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k p n i HJ Hc Hi) as (Hno & Hnw).
  destruct (HF _ Hf1) as [Hf | [(b & m & Hbin & Hb0 & Hr) | [Hof | (Hw & _)]]];
  [exact Hf | | exfalso; exact (Hno Hof) | exfalso; exact (Hnw Hw)].
  assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{ intros a Ha.
  destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; zlia|]].
  - eapply (apresent_transfer segs); [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha].
  - eapply (apresent_transfer segs); [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha]. }
split; [exact Hstatic|]. split; [|exact HQT2].
{ intros a HXa He. rewrite <- (F5 a HXa He).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.
End e.

(* Small facts a call site states its side condition with. *)
Lemma in_frames_head : forall ly cid pos own a,
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> in_frames ly ((cid, pos) :: own) a.
Proof. intros ly cid pos own a Ha. exists cid, pos. split; [left; reflexivity | left; exact Ha]. Qed.
Lemma in_frames_head_shadow : forall ly cid pos own a,
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
in_frames ly ((cid, pos) :: own) a.
Proof. intros ly cid pos own a Ha. exists cid, pos. split; [left; reflexivity | right; exact Ha]. Qed.
Lemma in_tmp_block_mono : forall bl0 blc blc' a,
(forall x, In x blc -> In x blc') -> in_tmp_block bl0 blc a -> in_tmp_block bl0 blc' a.
Proof. intros bl0 blc blc' a Hi (b & n & Hb & Hn & Hr). exists b, n. split; [exact (Hi _ Hb) | split; [exact Hn | exact Hr]]. Qed.
Lemma frame_addr_layout_le : forall n ly ly', layout_le n ly ly' -> forall c p, frame_addr ly' c p = frame_addr ly c p.
Proof. intros n ly ly' Hly c p. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.
Lemma in_frames_mono : forall ly ly' own own' a,
(forall x, In x own -> In x own') -> (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
in_frames ly own a -> in_frames ly' own' a.
Proof.
intros ly ly' own own' a Ho Hf (c & p & Hin & Hr). exists c, p. split; [exact (Ho _ Hin)|]. rewrite !Hf. exact Hr.
Qed.
Lemma awr_byte_weaken : forall STK sp0 FP bl0 blc blc' ly ly' own own' a,
(forall x, In x blc -> In x blc') -> (forall x, In x own -> In x own') ->
(forall c p, frame_addr ly' c p = frame_addr ly c p) ->
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a Hb Ho Hf [Hs | [(Hfp & b & n & Hin & Hr) | [Ht | Hof]]].
- left. exact Hs.
- right. left. split; [exact Hfp|]. exists b, n. split; [exact (Hb _ Hin) | exact Hr].
- right. right. left. exact (in_tmp_block_mono bl0 blc blc' a Hb Ht).
- right. right. right. exact (in_frames_mono ly ly' own own' a Ho Hf Hof).
Qed.
Lemma awr_byte_own_head : forall STK sp0 FP bl0 blc ly cid pos own a,
frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
awr_byte STK sp0 FP bl0 blc ly ((cid, pos) :: own) a.
Proof. intros STK sp0 FP bl0 blc ly cid pos own a Ha. right. right. right. exact (in_frames_head ly cid pos own a Ha). Qed.
Lemma awr_byte_own_head_shadow : forall STK sp0 FP bl0 blc ly cid pos own a,
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
awr_byte STK sp0 FP bl0 blc ly ((cid, pos) :: own) a.
Proof. intros STK sp0 FP bl0 blc ly cid pos own a Ha. right. right. right. exact (in_frames_head_shadow ly cid pos own a Ha). Qed.
Lemma awr_byte_of_tmp : forall STK sp0 FP bl0 blc ly own a,
in_tmp_block bl0 blc a -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof. intros STK sp0 FP bl0 blc ly own a Ht. right. right. left. exact Ht. Qed.
Lemma awr_byte_of_window : forall STK sp0 FP bl0 blc ly own a,
sp0 - STK <= a < sp0 -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof. intros STK sp0 FP bl0 blc ly own a Hw. left. exact Hw. Qed.

(* ============================================================================================== *)
(* 2. What a call keeps when its footprint carries the sink token: acall_kept without the image    *)
(*    clause, and the region_kept lemmas over it.                                                  *)
(* ============================================================================================== *)

Section k.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Definition acall_keptO (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
(W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).
Lemma acall_keptO_of_kept : forall lyc Sc W memc W2 mem2 slo shi E,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> acall_keptO lyc Sc W memc W2 mem2 slo shi E.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E (K1 & K2 & _ & K4 & K5 & K6).
exact (conj K1 (conj K2 (conj K4 (conj K5 K6)))).
Qed.
Lemma acall_keptO_mono_E : forall lyc Sc W memc W2 mem2 slo shi (E E' : Z -> Prop),
acall_keptO lyc Sc W memc W2 mem2 slo shi E -> (forall a, E a -> E' a) ->
acall_keptO lyc Sc W memc W2 mem2 slo shi E'.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E E' (K1 & K2 & K4 & K5 & K6) HEE.
split; [exact K1|]. split; [intros b m i Hb Hi Hn; apply (K2 b m i Hb Hi); intros He; exact (Hn (HEE _ He))|].
split; [intros cid pos a Hin Hr Hn; apply (K4 cid pos a Hin Hr); intros He; exact (Hn (HEE _ He))|].
exact (conj K5 K6).
Qed.
(* YCbq.acall_kept_of_journal without its `~ sink_open_fp FP1` premise. *)
Lemma acall_keptO_of_journal : forall stk sp1 FP1 nf lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 (E : Z -> Prop),
ajournal segs B stk sp1 FP1 lyc Sc W memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
acall_keptO lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof.
intros stk sp1 FP1 nf lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 E
(HAR2 & Hly2 & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 & HQT) HFE Hlive.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact G1|]. split.
{ intros b m i Hb Hi HnE. apply (G2 b m i Hb (Hlive b m i Hb Hi HnE) Hi). intros Hf. exact (HnE (HFE _ Hf)). }
split.
{ intros cid pos a Hin Hr HnE. apply (G4 cid pos a); [exact Hin | exact Hr | intros Hf; exact (HnE (HFE _ Hf))]. }
split; [|exact Hpres].
intros a Ha Hs Hp. eapply (apresent_transfer segs);
[zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; [exact Ha | exact Hs] | exact Hp].
Qed.
Lemma region_kept_stack_ajO : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S W0 mem md own ly2 S2 md2 k,
acall_keptO lyc Sc W memc W2 mem2 slo shi Er ->
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S W0 mem md own ly2 S2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply K1; zlia.
- intros _. apply (apresent_writable segs). apply Hpres. zlia.
Qed.
Lemma region_kept_block_ajO : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b m,
acall_keptO lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) ->
0 <= lo -> hi <= req_size m -> whi <= wlo ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b m (_ & K2 & _) Hn Hin Hlo Hhi Hro HnE.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview segs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
Qed.
Lemma region_kept_frame_ajO : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b cid pos,
acall_keptO lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid -> whi <= wlo ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b cid pos (_ & _ & K4 & _) Hn Hin Hlo Hhi Hro HnE.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview segs). apply (K4 cid pos a Hin); [|apply HnE; exact Ha].
left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
Lemma region_kept_ownframe_ajO : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b cid pos,
acall_keptO lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
((frame_addr lyc cid pos <= b + lo /\ b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
(shadow_addr (frame_addr lyc cid pos) <= b + lo /\ b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8)) ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b cid pos (_ & _ & K4 & _) Hn Hin Hrng HnE Hpres.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply (K4 cid pos a Hin); [|apply HnE; exact Ha].
  destruct Hrng as [[H1 H2] | [H1 H2]]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; lia.
- intros _. apply (apresent_writable segs). apply Hpres. exact Ha.
Qed.
Lemma region_kept_block_ajw2O : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b m ly2 S2 md2,
acall_keptO lyc Sc W memc W2 mem2 slo shi Er -> AR segs B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi Hwlo Hwhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable segs). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
End k.

(* ============================================================================================== *)
(* 3. The call-site wrapper (cgif YC85.cl_callS with the side condition of ajournal_sub_own), over  *)
(*    any image; each image's PcapSourceNextKit.v states cl_callS_own from it.                     *)
(* ============================================================================================== *)

Section j.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma cl_callS_ownG : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre segs B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> inFP FP a \/ awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal segs B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_own segs B LAWS segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End j.


(* Generic lemmas of cgif ACjr / ACj1, for any image: both lib/A and lib/B use them. *)
Section m.
Context {segs : list Segment}.
Lemma slot_of_region : forall E m spe cs lo hi wlo whi od e v,
region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem segs m (spe + od) 8 v.
Proof.
intros E m spe cs lo hi wlo whi od e v (_ & _ & _ & Hcs) H2 Hc He Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite H2 in Hck.
change 8%nat with (N.to_nat 8). exact (val_of_chunk_ok segs E m spe od 8%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma aview_wrap : forall H (m : word -> option byte) a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aview_kept_nil : forall E H (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview segs H m' a = aview segs H m a.
Proof.
intros E H m m' HF a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E [] H m m' 0 HF ltac:(lia)); [| apply Z.mod_pos_bound; lia].
intros x Hx (r & Hin & _). exact Hin.
Qed.
Lemma regions_kept_all : forall E H (m m2 : word -> option byte) rs,
(forall a, aview segs H m2 a = aview segs H m a) -> (forall a, apresent H m a -> apresent H m2 a) ->
Forall (region_kept segs E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 rs Hav Hpr. apply Forall_forall. intros r _. split; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav.
- apply writable_kept. apply Hpr.
Qed.
Lemma aview_kept_out : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' HF a Ha Hno. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hno.
Qed.
Lemma denot_add_atoms : forall E n1 n2 a b, ew E n1 = Z_to_bv 64 a -> ew E n2 = Z_to_bv 64 b ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (a + b).
Proof.
intros E n1 n2 a b H1 H2 Ha Hb Hab. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 a H1), (U_atom E n2 b H2) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma regions_kept_out2 : forall E H (m m2 : word -> option byte) lo hi lo2 hi2 rs,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (lo2 <= a < hi2) -> aview segs H m2 a = aview segs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
Forall (fun r => 0 <= base_val E (YP09.r_base r) + YP09.r_lo r /\ base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo \/ hi <= base_val E (YP09.r_base r) + YP09.r_lo r) /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo2 \/ hi2 <= base_val E (YP09.r_base r) + YP09.r_lo r)) rs ->
Forall (region_kept segs E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 lo hi lo2 hi2 rs Hav Hpr Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (H1 & H2 & H3 & H4). split; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav; lia.
- apply writable_kept. apply Hpr.
Qed.
Lemma denot_mul_hw : forall E nh nw h w, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w ->
0 <= h < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> sv_denot E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (h * w).
Proof.
intros E nh nw h w Hh Hw Rh Rw. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 32 - 1) * (2 ^ 32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nh h Hh) by lia. rewrite (U_atom E nw w Hw) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
End m.
End c.

(* A stack region placed by the value of its base atom (awr_ok_cons_stack_off with d = v - sp0): the
   atom may be the call's entry sp (a journal that starts at this call) or not (a caller journal). *)
Lemma awr_ok_cons_stack_at : forall E r rs STK sp0 FP bl0 blc ly own n v,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = v -> sp0 - STK <= v + YP09.r_wlo r -> v + YP09.r_whi r <= sp0 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n v Hb Hv Hlo Hhi H.
eapply (awr_ok_cons_stack_off E r rs STK sp0 FP bl0 blc ly own n (v - sp0)); [exact Hb | lia | lia | lia | exact H].
Qed.

(* ============================================================================================== *)
(* 4. Tactics: cgif ACjr / ACj1 / ACja, generic part (a Theorem Labs lane's GrantACjr.v, ACj1.v, GrantACja.v). *)
(* ============================================================================================== *)

Ltac getB := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end.
Ltac getLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac getML := lazymatch goal with M : model_laws _ |- _ => M end.
Ltac getAM := lazymatch goal with A : amalloc_realizes _ _ |- _ => A end.
Ltac getAF := lazymatch goal with A : afree_realizes _ _ |- _ => A end.
Ltac getENV := lazymatch goal with H : api_env _ _ |- _ => H end.
Ltac kept_intrin Hfr Hpres2 AG Usp :=
eapply region_kept_aview; [cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | intros a Ha; apply Hfr; unfold ESTACK; lia | exact Hpres2].
Ltac reshok_bx HS bx :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) | st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx))  end.
Ltac reshok HS := reshok_bx HS 32%nat.
Ltac norm_ss HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS | st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS  end.
Ltac eatom AG Efact := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; exact Efact.
Ltac rnLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac rnB := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end.
Ltac rnFFL := lazymatch goal with H : frame_flag_lawP _ _ |- _ => H end.
Ltac rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "rnHEI: no img_env fact for" E end.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia | |- _ < _ <= _ => lia end
| idtac ].
Ltac idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac obl_blk HJx HEn HEbx Hin :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex n p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | let v := eval vm_compute in (req_size sz) in change (req_size sz) with v; lia ] end end end.
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox := unfold boxed in *.
Ltac ra_join_val HS N i R En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end | st_ok _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end  end.
Ltac rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)  end.
Ltac upd_aboveW HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
Lemma land_mod256 : forall x m, 0 <= m < 256 -> Z.land (x mod 256) m = Z.land x m.
Proof.
intros x m Hm. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.
Lemma U_and_zext8 : forall E a m, 0 <= m < 256 -> U E (SAlu ALU_AND (SExt false 8 a) (SLit m)) = Z.land (U E a) m.
Proof.
intros E a m Hm. rewrite U_and_lit by lia. rewrite U_zext. change (2 ^ Z.of_N 8) with 256. apply land_mod256. exact Hm.
Qed.
Ltac fsb_lits := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac zconst_lits := repeat match goal with
| |- context [?s] => is_const s; lazymatch type of s with Z =>
let v := eval vm_compute in s in
lazymatch v with Zpos _ => change s with v | Zneg _ => change s with v | Z0 => change s with v end end
end.

(* A stack region (the entry stack, atom 2, or the realigned stack, atom 60 by default): placed by its
   atom's value, which evalE computes; the bounds are closed numerically first, then from the context
   (a caller-journal walk, whose journal starts at the caller's sp0, needs the context). *)
Ltac awr_stack_at n AG :=
eapply (awr_ok_cons_stack_at _ _ _ _ _ _ _ _ _ _ n);
[ reflexivity | evalE AG
| first [ solve [clear; cbn [YP09.r_wlo YP09.r_whi]; unfold ASTACK, ESTACK; zconst_lits; lia]
        | solve [cbn [YP09.r_wlo YP09.r_whi]; unfold ASTACK, ESTACK; zconst_lits; lia] ]
| first [ solve [clear; cbn [YP09.r_wlo YP09.r_whi]; unfold ASTACK, ESTACK; zconst_lits; lia]
        | solve [cbn [YP09.r_wlo YP09.r_whi]; unfold ASTACK, ESTACK; zconst_lits; lia] ]
| ].
(* awr_ok of a region list: read-only regions; the walk's own head regions (hd); the own side-stack
   frame (atom aF) and its shadow (atom aS) as `in_frames` of the journal's head frame (c, fpos), with
   F the frame address (a `set` name) and EFA the layout's frame equation; the stack (atom 2) and the
   realigned stack (atom aR). *)
Ltac awrF_rec_at aF aS aR hd AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| hd
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some aS) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aS); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; fsb_lits; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some aF) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ aF); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; fsb_lits; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ => awr_stack_at 2%nat AG
| |- awr_ok _ (YP09.mkRegion (Some aR) _ _ _ _ _ :: _) _ _ _ _ _ _ _ => awr_stack_at aR AG
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "awrFL: no rule for the head region" ];
awrF_rec_at aF aS aR hd AG fpos F EFA
end.
Ltac awrFL_at aF aS aR hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
awrF_rec_at aF aS aR hd AG fpos F EFA.
Ltac awrF_rec_with hd AG fpos F EFA := awrF_rec_at 516%nat 529%nat 60%nat hd AG fpos F EFA.
Ltac awrF_rec AG fpos F EFA := awrF_rec_with ltac:(idtac; fail) AG fpos F EFA.
Ltac awrFL_with hd AG fpos F EFA := awrFL_at 516%nat 529%nat 60%nat hd AG fpos F EFA.
Ltac awrFL AG fpos F EFA := awrFL_with ltac:(idtac; fail) AG fpos F EFA.
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Ltac rqs_goal := repeat (match goal with |- context [req_size ?n] =>
let v := eval vm_compute in (req_size n) in
lazymatch v with Zpos _ => change (req_size n) with v | Z0 => change (req_size n) with v end end).
Ltac rewrite_frame_addr := repeat match goal with H : forall c p, frame_addr ?l3 c p = frame_addr ?l c p |- context [frame_addr ?l3 _ _] => rewrite H end;
repeat match goal with F := frame_addr _ _ _ |- _ => fold F end.

(* The kept fact of a call, as acall_keptO (acall_kept converts). *)
Ltac kexact HK := first [ exact HK | exact (acall_keptO_of_kept _ _ _ _ _ _ _ _ _ _ _ HK) ].
Ltac upd_aboveW_init HFr AG HUP :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of Wx with world ?sg =>
lazymatch goal with Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview sg (w_H Wx) (ms_mem msX) a = aview sg (w_H Wx) m0 a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| ] end end end.
Lemma chunk_ok_redenote : forall segs E m base off w e e',
sv_denot E e' = sv_denot E e -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)) -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e')).
Proof. intros segs E m base off w e e' He H i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cbyte] in *. rewrite He. exact (H i Hi). Qed.
Ltac idx_of_off cs off :=
lazymatch cs with
| YP09.mkChunk off _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_off tl off in constr:(S i)
end.
Ltac hc_bool H tac :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_and_lit in H by lia; tac H; rewrite ?U_lit in H by lia;
try (apply (proj1 (negb_true_iff _)) in H); try (apply (proj1 (negb_false_iff _)) in H).
Ltac hc_prop H :=
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H
| apply (proj1 (Z.ltb_lt _ _)) in H | apply (proj1 (Z.ltb_ge _ _)) in H | idtac ].
Ltac oblG HJx E10n E32n Hing := obl_blk HJx E10n E32n Hing.
Lemma land_m4 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 4) = 4 * (x / 4).
Proof.
intros x Hx. assert (E1 : 2 ^ 64 - 4 = Z.ldiff (Z.ones 64) (Z.ones 2)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land. rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia.
Qed.
Lemma land_m2 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 2) = 2 * (x / 2).
Proof.
intros x Hx. assert (E1 : 2 ^ 64 - 2 = Z.ldiff (Z.ones 64) (Z.ones 1)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land. rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. lia.
Qed.
Lemma U_and_m4 : forall E a, U E (SAlu ALU_AND a (SLit (-4))) = 4 * (U E a / 4).
Proof. intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-4)) with (2 ^ 64 - 4). pose proof (U_range E a). rewrite land_m4 by (rewrite <- M64_val; lia). apply zcanon_id. rewrite M64_val in *. pose proof (Z.mul_div_le (U E a) 4 ltac:(lia)). split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]. Qed.
Lemma U_and_m2 : forall E a, U E (SAlu ALU_AND a (SLit (-2))) = 2 * (U E a / 2).
Proof. intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-2)) with (2 ^ 64 - 2). pose proof (U_range E a). rewrite land_m2 by (rewrite <- M64_val; lia). apply zcanon_id. rewrite M64_val in *. pose proof (Z.mul_div_le (U E a) 2 ltac:(lia)). split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | lia]. Qed.
Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma zcanon_01 : forall b : bool, zcanon (if b then 1 else 0) = (if b then 1 else 0).
Proof. intros b. apply zcanon_id. rewrite M64_val. destruct b; lia. Qed.
Lemma clr2_rng : forall x, 0 <= x -> 0 <= 2 * (x / 2) <= x.
Proof. intros x Hx. pose proof (Z.mul_div_le x 2 ltac:(lia)). pose proof (Z.div_pos x 2 Hx ltac:(lia)). lia. Qed.
Lemma clr4_rng : forall x, 0 <= x -> 0 <= 4 * (x / 4) <= x.
Proof. intros x Hx. pose proof (Z.mul_div_le x 4 ltac:(lia)). pose proof (Z.div_pos x 4 Hx ltac:(lia)). lia. Qed.
Lemma clr42 : forall x, 0 <= x -> 2 * (4 * (x / 4) / 2) = 4 * (x / 4).
Proof. intros x Hx. replace (4 * (x / 4)) with ((2 * (x / 4)) * 2) by lia. rewrite Z.div_mul by lia. lia. Qed.


(* ============================================================================================== *)
(* 5. The image-free tactics on small goals.                                                       *)
(* ============================================================================================== *)

Section t.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma kit_check_lits : fs_frame_bytes 0 / 8 = 8 /\ fs_frame_bytes 0 = 64.
Proof. split; fsb_lits; reflexivity. Qed.
Lemma kit_check_awr : forall (E E0 : env) STK sp0 FP bl0 blc (ly ly0 : alayout) own fp,
(forall n, (n < 33)%nat -> ew E n = ew E0 n) ->
bv_unsigned (ew E0 2) = sp0 -> 0 <= sp0 < 2 ^ 64 -> 64 <= STK ->
(forall c p, frame_addr ly c p = frame_addr ly0 c p) ->
ew E 516%nat = Z_to_bv 64 (frame_addr ly0 0 fp) -> 0 <= frame_addr ly0 0 fp < 2 ^ 63 ->
ew E 529%nat = Z_to_bv 64 (0x7fff8000 + frame_addr ly0 0 fp / 8) -> 0 <= 0x7fff8000 + frame_addr ly0 0 fp / 8 < 2 ^ 63 ->
awr_ok E [YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 []; YP09.mkRegion (Some 516%nat) 0 64 0 24 [];
          YP09.mkRegion (Some 529%nat) 0 8 0 8 []]
  STK sp0 FP bl0 blc ly ((0, fp) :: own).
Proof.
intros E E0 STK sp0 FP bl0 blc ly ly0 own fp AG Usp Hsp HSTK EFA E516 HF E529 HS.
set (F := frame_addr ly0 0 fp) in *.
awrFL AG fp F EFA.
Qed.
(* A caller journal: the journal's sp0 is the caller's, the entry sp (atom 2) and the realigned sp
   (atom 60) lie below it. *)
Lemma kit_check_awr_caller : forall (E E0 : env) STK sp0 sp sp1 FP bl0 blc ly own,
(forall n, (n < 33)%nat -> ew E n = ew E0 n) ->
bv_unsigned (ew E0 2) = sp -> 0 <= sp < 2 ^ 64 -> sp0 - STK <= sp - 8448 -> sp <= sp0 ->
ew E 60%nat = Z_to_bv 64 sp1 -> sp - 256 <= sp1 <= sp - 224 -> 0 <= sp1 ->
awr_ok E [YP09.mkRegion (Some 2%nat) (-224) 0 (-224) 0 []; YP09.mkRegion (Some 60%nat) 0 120 0 120 []]
  STK sp0 FP bl0 blc ly own.
Proof.
intros E E0 STK sp0 sp sp1 FP bl0 blc ly own AG Usp Hsp Hlo Hhi E60 Hsp1 Hsp1'.
awrFL AG 0 0 I.
Qed.
(* upd_aboveW_init reads the image from the world's type. *)
Lemma kit_check_upd : forall segs (W : world segs) (E0 E : env) (m0 : word -> option byte) (ms : machine_state) (regs : bvmap 5 word),
(forall n, (n < 33)%nat -> ew E n = ew E0 n) ->
frame_of E [] (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem ms)) ->
bv_unsigned (ew E0 2) = spZ regs -> 0 <= spZ regs ->
forall a, spZ regs <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) m0 a.
Proof. intros segs W E0 E m0 ms regs AG HFr Usp Hsp. upd_aboveW_init HFr AG HUP. exact HUP. Qed.
End t.
