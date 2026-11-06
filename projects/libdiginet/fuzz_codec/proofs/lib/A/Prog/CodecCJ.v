(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/A/Prog/IdentCJ.v
   (origin/ossv/recipes 4b6f0df50aa7) for libdiginet/fuzz_codec's ASan builds: the listing layer (PAImg) is
   dropped, so the segment list is a Section variable and the lemmas that used the listing's `pa_segs_low`
   take it as the hypothesis `segs_low`; every definition and every proof is otherwise the donor's text. *)
(* A callee whose writes may land in a frame of its caller (or of its caller's caller) states its contract in
   the caller-journal form: the premise is the caller's journal, the right to write each byte is the caller's
   premise (twr_ok), and the post extends the same journal and says what the call kept (tcj_kept).
   ajournal_sub_awr composes a callee's own journal (its afn_pre-form walk) into the caller's. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section e.
Variable B : asyms.
(* What a call keeps: everything but its own stack window [sp - STK, sp) and the bytes E it may write. *)
Definition tcj_kept (STK : Z) (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
(W2 : world segs) (mem2 : word -> option byte) (sp : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ E a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, sp - STK <= a < sp -> apresent (w_H W2) mem2 a).
(* The caller's right to let the call write [q, q + n): a byte the caller's own journal may change, present,
   not the memory-checking runtime's own, and not in the stack the runtime uses below sp. *)
Definition twr_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world segs) (memc : word -> option byte)
(sp q n : Z) : Prop :=
forall a, q <= a < q + n ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
apresent (w_H W) memc a /\ ~ aowned B lyc Sc a /\ ~ (sp - ESTACK <= a < sp).
(* A range the call reads. *)
Definition tsrc_ok (W : world segs) (memc : word -> option byte) (sp q n : Z) : Prop :=
(forall a, q <= a < q + n -> aview segs (w_H W) memc a <> None /\ ~ (sp - ESTACK <= a < sp)) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n /\
shadow_hull_vis (aview segs (w_H W) memc) q n /\ amem_range q n /\ 0 <= q /\ q + n <= 2 ^ 63.
(* Where the bytes [q, q + n) lie: each in a heap block or in a side-stack frame of the state. *)
Definition tdst_ok (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
forall a, q <= a < q + n ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ in_zr a (frame_rng lyc (cid, pos))).
End e.
Section g.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* A call's own journal with write range [q, q + n) gives what the call kept. *)
Lemma tcj_kept_of_ajournal : forall STK1 sp1 q n lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1,
ajournal segs B STK1 sp1 [(q, q + n)] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> 0 < q ->
tcj_kept B STK1 lyc Sc W memc W2 mem2 sp1 (fun a => q <= a < q + n).
Proof.
intros STK1 sp1 q n lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT) Hperm Hq.
assert (HFP : forall a, inFP [(q, q + n)] a -> q <= a < q + n).
{ intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. exact Hr. }
assert (HNS : ~ YI16.sink_open_fp [(q, q + n)]).
{ intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
split; [intros a Ha Hw _; apply F1; [exact Ha | exact Hw]|].
split.
{ intros b m i Hin Hi HE. apply (F2 b m i); [exact Hin | exact (Permutation_in _ (Permutation_sym Hperm) Hin) | exact Hi |].
  intros Hf. exact (HE (HFP _ Hf)). }
split; [intros a Hi Hns He; apply F3; [exact Hi | exact Hns | exact He | apply fp_spares_closed; exact HNS]|].
split.
{ intros cid pos a Hin Hr HE. apply (F4 cid pos a); [exact Hin | exact Hr |]. intros Hf. exact (HE (HFP _ Hf)). }
split; [|exact Hpres].
intros a Ha Hw Hp. pose proof asan_consts as (C1 & _).
eapply apresent_transfer; [lia | intros Him; pose proof (segs_low a Him); unfold kLowMemEnd in *; lia | apply F1; [exact Ha | exact Hw] | exact Hp].
Qed.
End g.
End c.
Lemma shadow_disj_of_disj : forall F1 L1 F2 L2 a, F1 mod 8 = 0 -> F2 mod 8 = 0 -> 0 <= L1 -> 0 <= L2 ->
(F1 + L1 <= F2 \/ F2 + L2 <= F1) ->
shadow_addr F1 <= a < shadow_addr F1 + L1 / 8 -> shadow_addr F2 <= a < shadow_addr F2 + L2 / 8 -> False.
Proof.
intros F1 L1 F2 L2 a H1 H2 HL1 HL2 Hd Ha Hb. unfold shadow_addr in *.
pose proof (Z.div_mod F1 8 ltac:(lia)) as D1. pose proof (Z.div_mod F2 8 ltac:(lia)) as D2.
pose proof (Z.div_mod L1 8 ltac:(lia)) as D3. pose proof (Z.div_mod L2 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound L1 8 ltac:(lia)). pose proof (Z.mod_pos_bound L2 8 ltac:(lia)).
rewrite H1 in D1. rewrite H2 in D2. lia.
Qed.
Lemma mod32_mod8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (32 * (x / 32)) with ((4 * (x / 32)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Section f.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* Where a byte of a side-stack frame or of its shadow lies. *)
Lemma frame_zone : forall ly S W mem md cid pos a, AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
a < alloc_ceiling /\
((frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid)) \/
 kLowMemEnd <= a < kHighShadowEnd).
Proof.
intros ly S W mem md cid pos a HAR Hin Hr.
destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)) as S1.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)) as S2.
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as S3.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr|Hr]; [split; [zlia | left; split; [zlia | exact Hfh]] | split; [zlia | right; zlia]].
Qed.
(* A heap-block byte is in no frame's zone. *)
Lemma block_not_frame_zone : forall ly S W mem md p n i cid pos,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) -> 0 <= i < req_size n ->
(in_zr (p + i) (frame_rng ly (cid, pos)) \/ in_zr (p + i) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) -> False.
Proof.
intros ly S W mem md p n i cid pos HAR Hb Hin Hi Hr.
destruct (al_blocks segs B LAWS ly S W mem md p n HAR Hb) as (_ & Hp4096 & Hpceil & Hpapp & _).
pose proof (sep_block_frame segs B LAWS ly S W mem md p n cid pos HAR Hb Hin) as Hd.
destruct (frame_zone ly S W mem md cid pos (p + i) HAR Hin Hr) as (_ & [(Hr1 & _) | Hr2]).
- unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- zlia.
Qed.
(* Two different frames of a state share no byte of their zones. *)
Lemma frames_zone_disj : forall ly S W mem md f g l1 l2 l3 a,
AR segs B ly S W mem md -> frames S = l1 ++ f :: l2 ++ g :: l3 ->
(in_zr a (frame_rng ly f) \/ in_zr a (shadow_addr (frame_addr ly (fst f) (snd f)), fs_frame_bytes (fst f) / 8)) ->
(in_zr a (frame_rng ly g) \/ in_zr a (shadow_addr (frame_addr ly (fst g) (snd g)), fs_frame_bytes (fst g) / 8)) -> False.
Proof.
intros ly S W mem md [cf pf] [cg pg] l1 l2 l3 a HAR E Hf Hg. cbn [fst snd] in Hf, Hg.
assert (Hinf : In (cf, pf) (frames S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
assert (Hing : In (cg, pg) (frames S)) by (rewrite E; apply in_or_app; right; right; apply in_or_app; right; left; reflexivity).
pose proof (sep_frames_pos segs B LAWS ly S W mem md (cf, pf) (cg, pg) l1 l2 l3 HAR E) as Hd.
destruct (al_frames _ _ LAWS ly S W mem md cf pf HAR Hinf) as (Af & _).
destruct (al_frames _ _ LAWS ly S W mem md cg pg HAR Hing) as (Ag & _).
apply mod32_mod8 in Af. apply mod32_mod8 in Ag.
destruct (frames_bounds segs B LAWS ly S W mem md cf pf HAR Hinf) as (Bf0 & Bfc & Bfa).
destruct (frames_bounds segs B LAWS ly S W mem md cg pg HAR Hing) as (Bg0 & Bgc & Bga).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cf) as Nf. pose proof (fs_frame_bytes_nonneg cg) as Ng.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cf pf) ltac:(zlia)) as Sf1.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cf pf + fs_frame_bytes cf) ltac:(zlia)) as Sf2.
pose proof (shadow_range_end (frame_addr ly cf pf) (fs_frame_bytes cf) Nf) as Sf3.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cg pg) ltac:(zlia)) as Sg1.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cg pg + fs_frame_bytes cg) ltac:(zlia)) as Sg2.
pose proof (shadow_range_end (frame_addr ly cg pg) (fs_frame_bytes cg) Ng) as Sg3.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
unfold frame_rng, in_zr in Hf, Hg. cbn [fst snd] in Hf, Hg.
destruct Hf as [Hf|Hf]; destruct Hg as [Hg|Hg]; try zlia.
exact (shadow_disj_of_disj (frame_addr ly cf pf) (fs_frame_bytes cf) (frame_addr ly cg pg) (fs_frame_bytes cg) a
Af Ag Nf Ng Hd Hf Hg).
Qed.
(* lib/Reusable/YCbq.v ajournal_sub, with the caller's write right in place of "in the caller's FP and in a
   heap block of the call state, or in a block allocated since the caller's start": a callee may also write
   the caller's stack window and the frames the caller allocated (own). *)
Lemma ajournal_sub_awr : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal segs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
ajournal segs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT)
(HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2) Hlo Hhi HF.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Efr : forall cid pos, frame_addr lyc cid pos = frame_addr ly cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
(* a byte of a frame the caller allocated lies in that frame's zone in the call state *)
assert (HOWN : forall a, in_frames lyc own a -> exists cid pos, In (cid, pos) (frames Sc) /\ In (cid, pos) own /\
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))).
{ intros a (cid & pos & Hin & Hr). exists cid, pos. split; [rewrite Hfrs; apply in_or_app; left; exact Hin|]. split; [exact Hin|].
  unfold frame_rng. cbn [fst snd]. exact Hr. }
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as [Hw | [((r' & Hr' & H0') & _) | [(b & n & Hin & _ & Hb) | Hfr]]].
  - exfalso. zlia.
  - exists r'. split; [exact Hr' | exact H0'].
  - exfalso. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). zlia.
  - exfalso. destruct (HOWN 0 Hfr) as (cid & pos & HinC & _ & Hr0).
    destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & _ & _).
    destruct (frame_zone lyc Sc Wc memc mdc cid pos 0 HAR HinC Hr0) as (_ & [(Hz & _) | Hz]); zlia. }
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|].
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{   intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{   intros p n i H1 H2 Hi Hnf.
assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
intros Hf1.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hc2) as (_ & Hp4096 & Hpceil & _).
destruct (HF _ Hf1) as [Hw | [[Hf _] | [(b & m & Hbin & Hb0 & Hr) | Hfr]]].
- zlia.
- exact (Hnf Hf).
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- destruct (HOWN _ Hfr) as (cid & pos & HinC & _ & Hr0).
exact (block_not_frame_zone lyc Sc Wc memc mdc p n i cid pos HAR Hc2 HinC Hi Hr0). }
split.
{   intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). apply (G3 a Hi Hns He). intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{   intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
assert (Hr' : in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
{ unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr. }
apply (G4 cid pos a HinC); [exact Hr'|].
intros Hf1. destruct (HF _ Hf1) as [Hw | [[Hf _] | [(b & m & Hbin & Hb0 & Hrb) | Hfr]]].
- destruct (frame_zone lyc Sc Wc memc mdc cid pos a HAR HinC Hr') as (Hz & _). zlia.
- exact (Hnf Hf).
- apply (block_not_frame_zone lyc Sc Wc memc mdc b m (a - b) cid pos HAR Hbin HinC); [zlia|].
replace (b + (a - b)) with a by lia. exact Hr'.
- destruct (HOWN _ Hfr) as (cid' & pos' & _ & Hin' & Hr0).
apply in_split in Hin' as (o1 & o2 & Eo). apply in_split in Hin as (s1 & s2 & Es).
apply (frames_zone_disj lyc Sc Wc memc mdc (cid', pos') (cid, pos) o1 (o2 ++ s1) s2 a HAR).
+ rewrite Hfrs, Eo, Es. repeat rewrite <- app_assoc. cbn [app]. repeat rewrite <- app_assoc. reflexivity.
+ cbn [fst snd]. exact Hr0.
+ cbn [fst snd]. exact Hr'. }
split.
{   intros p n i H1 H2 Hi.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hc) as (_ & Hp4096 & Hpceil & _).
destruct (HF _ Hf1) as [Hw | [[Hf _] | [(b & m & Hbin & Hb0 & Hr) | Hfr]]].
- exfalso. zlia.
- exact Hf.
- assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. exfalso. zlia.
- exfalso. destruct (HOWN _ Hfr) as (cid & pos & HinC & _ & Hr0).
exact (block_not_frame_zone lyc Sc Wc memc mdc p n i cid pos HAR Hc HinC Hi Hr0). }
split.
{   intros a Ha.
destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; zlia|]].
- eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha].
- eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha]. }
split; [exact Hstatic|]. split; [|exact HQT2].
{   intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.
(* The bytes a call writes into a block or a live frame lie in application memory, below the allocator
   ceiling and off the image: the contracts' amem_range and the `off the stack window` disjunct follow. *)
Lemma cj_dst_byte : forall lyc Sc W memc mdc q n x, AR segs B lyc Sc W memc mdc -> tdst_ok B lyc Sc q n ->
q <= x < q + n ->
4096 <= x < alloc_ceiling /\ (x + 1 <= kLowShadowBeg \/ kHighMemBeg <= x).
Proof.
intros lyc Sc W memc mdc q n x HAR Hd Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Hd x Hx) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HAR Hin) as (_ & H4096 & Hceil & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
- destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H4096 & Hceil & Happ).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End f.
End b.
