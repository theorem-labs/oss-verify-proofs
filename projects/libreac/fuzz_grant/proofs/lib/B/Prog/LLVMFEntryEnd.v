(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryEndFree), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryLeave), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v, proofs/cgif/cgif_file_fuzzer/lib/YCbo.v, proofs/cgif/cgif_file_fuzzer/lib/YCbq.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryEndFree.v and lib/A/Prog/GrantEntryLeave.v. *)
(* Ported from a working branch 552860c6366 (lib/A/Prog/GrantEntryEndFree.v, ge_end_free) and a working branch 7c8c67da870 (lib/A/Prog/GrantEntryLeave.v, ge_leave); neither image-A file carries licence lines. *)
(* The end of the walk of fuzz_grant's entry function LLVMFuzzerTestOneInput on image B
   (fuzz_grant.asan-ubsan, 0x80a3c): the phase END (0x81da4 .. 0x81e94, from the cut
   `GI_freeT` to the cut `GI_leave`) and the phase LEAVE (0x80cd8 .. 0x80d94, from the cut
   `GI_leave` to the `ret`).

   END: 0x81da4 puts the head-amp table (s4) into a0 and 0x81da8 calls the wrapper for
   free through its trampoline; the call is taken by its contract (`afree04_rule`), and
   it returns to 0x81dac, the third free site of `GE_FSITES` (0x1370). Then `li a0,-8`
   and 55 one-byte stores through s3 (the frame's shadow base) mark the frame's objects
   unusable again (0xf8 in the frame's shadow bytes 4 .. 89), the two loads at 0x81e8c
   and 0x81e90 put the frame back into s5 (spill slot 8) and a6 (spill slot 72), and
   `j 0x80cd8` at 0x81e94 goes to the release block. After the free the phase seats a
   symbolic state whose shadow region carries no chunk: the stores only need the write
   window [0, 104) of the frame's shadow, and the cut `GI_leave` asks only that some
   shadow list holds (`ge_land_ex`). No slot of this stretch branches.

   LEAVE: image B puts the release block BEFORE the body, so two slots reach it: the
   `beq a3,zero,0x80d00` at 0x80cd4 not taken (the early return of an input of 2^26
   bytes or more) and the `j 0x80cd8` at 0x81e94. 0x80cd8 writes the end magic 0x45e0360e
   at F+0 through a6 and gives the frame back: the frame came from the side stack for
   frames, so the code fills the slot's 128 shadow bytes with 0xf5 through
   __asan_set_shadow_f5 (a0 = s3, a1 = 128, 0x80cf0) and stores 0 into the flag byte the
   slot's last word points at (F+1016, through s5, 0x80cf4 / 0x80cf8). The other arm,
   `beq s5,zero,0x80d48` at 0x80ce4 taken and __asan_set_shadow_00 over 104 bytes at
   0x80d50, is the one a frame on the machine stack would take; it is refuted: s5 holds
   the frame of the side stack, which is live (`frames S3 = [(GE_CID, fp)]`), so it is
   at least 4096 (the fact `HPTR 5` on atom 21) and the branch falls through. No
   contract of __asan_set_shadow_00 is used. Then it reads ra and s0..s11 back from the
   machine frame, puts sp back and returns 0 (0x80d54 .. 0x80d94). This is the phase
   that proves the entry function's post-condition. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0p YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC1i YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantACjr ACj1 GrantACja ACbf.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import SetShadowDef.
(* The contract's constants that LLVMFEntryDefs.v's GE_STK, GE_EV and GE_FSITES name;
   Required, not imported, and named in full. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantBContracts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma regs_ok_havoc_hi : forall E k ws regs,
(32 <= k)%nat -> regs_ok E sr_atoms regs -> regs_ok (havoc E k ws) sr_atoms regs.
Proof.
intros E k ws regs Hk H. apply (regs_ok_agree 32 E);
[ apply (env_agree_havoc_ge 32 k E E ws Hk (env_agree_refl 32 E)) | vm_compute; reflexivity | exact H ].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Ltac bvne := let Hq := fresh "Hq" in
  intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate.

Lemma gef_reg_other : forall (regs : bvmap 5 word) (rd : bv 5) (v : word) (r : bv 5),
  r <> rd -> getr (regupd regs rd v) r = getr regs r.
Proof. intros regs rd v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact Hr. Qed.

Lemma gef_reg_same : forall (regs : bvmap 5 word) (rd : bv 5) (v : word),
  bv_eqb rd 0 = false -> getr (regupd regs rd v) rd = v.
Proof. intros regs rd v H. unfold getr. rewrite H. apply regupd_same. Qed.

Lemma gef_rdword_keep : forall (rd rd' : reader) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
  intros rd rd' a v K Hr.
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

(* ---- a journal across a write that keeps only the caller's window present ----
   `ajournal_after_write` (lib/Reusable/YCbq.v:517) asks that every byte present before
   the write is present after it. The memory-checking runtime's shadow-fill entry
   promises that only for the bytes of its own window, so this phase takes the same
   lemma with the weaker hypothesis; the proof is YCbq's, with the one step that uses
   it (the journal's "the caller's window is present") restricted to that window. *)
Section gen.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Lemma ajournal_after_write_stk :
forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal segs B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
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
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx];
  [left; exact (awr_byte_cases segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]) | (_ & Hx)]; [exact (Hs Hs') | zlia | zlia | zlia | zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx)].
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
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (blk_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(pose proof (YCbq.fs_frame_bytes_nonneg cid); zlia)) as Hsb1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(pose proof (YCbq.fs_frame_bytes_nonneg cid); zlia)) as Hsb2.
pose proof (YCbq.shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (YCbq.fs_frame_bytes_nonneg cid)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
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
pose proof (YCbq.shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (YCbq.fs_frame_bytes_nonneg c')) as Hse'.
pose proof (YCbq.fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (YCbq.shadow_mono _ _ Hd). zlia.
* pose proof (YCbq.shadow_mono _ _ Hd). zlia.
-
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [intros a Ha; apply (Hgr a Ha); apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]) | (Hxo & Hx)].
- apply Xs. rewrite Eslo, Eshi. zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xo Hxo). }
Qed.

(* The shadow-fill entry of the memory-checking runtime, in the journal form: it fills
   `n` shadow bytes of a frame this call owns and keeps everything else. *)
Lemma aj_set_shadow_at : forall pc v, aset_shadow_realizes segs B pc v ->
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
(forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
  try eassumption. rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2 & Hkeep2).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds segs B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(pose proof (YCbq.fs_frame_bytes_nonneg cid); zlia)) as Hsb1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(pose proof (YCbq.fs_frame_bytes_nonneg cid); zlia)) as Hsb2.
pose proof (YCbq.shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (YCbq.fs_frame_bytes_nonneg cid)) as Hse.
assert (Hoff : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
{ intros a Ha Hni Hp. destruct (Z_le_gt_dec q a) as [Hqa|Hqa]; [destruct (Z_lt_ge_dec a (q + n)) as [Han|Han]|].
- specialize (Heff (a - q) ltac:(zlia)). replace (q + (a - q)) with a in Heff by zlia.
destruct Hp as [Hh _]. split; [exact Hh|]. unfold aview, mbyte, mrestrict in Heff. rewrite Hh in Heff.
destruct (mem2 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso.
rewrite (seg_rom_none segs a Ha Hni) in Heff. discriminate.
- eapply (apresent_transfer segs); [exact Ha | exact Hni | apply Hfr; [exact Ha | zlia] | exact Hp].
- eapply (apresent_transfer segs); [exact Ha | exact Hni | apply Hfr; [exact Ha | zlia] | exact Hp]. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write_stk STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => q <= a < q + n) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha Hna).
- intros a Ha Hp. apply Hoff; [zlia | intros Hi; pose proof (segs_low a Hi); zlia | exact Hp].
- exact Hsame.
- intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|]. right.
  unfold in_zr. cbn [fst snd]. zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr | exact Hoff].
Qed.
End gen.

Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* A word of a region, from the word the phase's invariant gives. *)
Lemma gl_chunk : forall (E : env) (H : word -> bool) (mem : word -> option byte) n sp off v,
bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
rdword (aview SEGS H mem) (sp + off) = Some v ->
YP09.chunk_ok SEGS E (mrestrict H mem) sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E H mem n sp off v Hn Hv Hr.
apply (chunk_ok_val SEGS E (mrestrict H mem) sp off 8 (SOff n 0) v).
- cbn [sv_denot]. rewrite Z.add_0_r, Hn. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn; lia.
- exact (val_mem_of_rdword SEGS _ _ _ _ Hr).
Qed.

(* A region a call keeps: its bytes are the same and its window stays writable. *)
Lemma gl_kept : forall (E : env) (H : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict H m2) a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply Hw. exact Ha.
Qed.

(* An array of bytes is kept by a change of memory that keeps each of its bytes. *)
Lemma gef_garr8 : forall (H H' : word -> bool) (m m' : word -> option byte) p (l : list Z),
  (forall j, (j < length l)%nat -> aview SEGS H' m' (p + Z.of_nat j) = aview SEGS H m (p + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) p l -> garr8 SEGS (mrestrict H' m') p l.
Proof.
  intros H H' m m' p l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k Hkk. assert (k = 0)%nat by lia. subst k.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (mbyte_of_aview SEGS H H' m m' (p + Z.of_nat j) (HK j Hj)).
  exact Hv0.
Qed.

(* The registers of the state after the free: the five the body keeps (the realigned
   stack pointer in sp and s1, the caller's sp in s0, gp and tp), the frame's shadow
   base in s3 (image B; image A keeps it in s6), and one fresh atom N + i for every
   other register. *)
Definition gef_sr (N : nat) : list sv :=
  [SLit 0; SOff (N + 1) 0; SOff GA_SP1 0; SOff 3%nat 0; SOff 4%nat 0;
   SOff (N + 5) 0; SOff (N + 6) 0; SOff (N + 7) 0; SOff GA_SP 0; SOff GA_SP1 0;
   SOff (N + 10) 0; SOff (N + 11) 0; SOff (N + 12) 0; SOff (N + 13) 0; SOff (N + 14) 0;
   SOff (N + 15) 0; SOff (N + 16) 0; SOff (N + 17) 0; SOff (N + 18) 0; SOff GA_FSH 0;
   SOff (N + 20) 0; SOff (N + 21) 0; SOff (N + 22) 0; SOff (N + 23) 0; SOff (N + 24) 0;
   SOff (N + 25) 0; SOff (N + 26) 0; SOff (N + 27) 0; SOff (N + 28) 0; SOff (N + 29) 0;
   SOff (N + 30) 0; SOff (N + 31) 0].

Ltac gef_case Hat Ha2 Ha8 Ha9 Ha3 Ha4 Ha19 i :=
  lazymatch goal with |- getr ?rg ?rr = sv_denot ?Ex (sr_get ?srl ?rr2) =>
    let v := eval vm_compute in (sr_get srl rr2) in change (sr_get srl rr2) with v;
    first [ rewrite getr_zero; cbn [sv_denot]; reflexivity
          | rewrite ge_sv_SOff0; symmetry;
            first [ exact Ha2 | exact Ha8 | exact Ha9 | exact Ha3 | exact Ha4 | exact Ha19
                  | exact (Hat i rr ltac:(lia) ltac:(vm_compute; reflexivity)) ]
          | match goal with |- ?g => idtac "RO:" g end; fail ]
  end.

Lemma gef_regs_ok : forall (E : env) (N : nat) (regs : bvmap 5 word),
(forall (i : nat) (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r -> ew E (N + i)%nat = getr regs r) ->
ew E GA_SP1 = getr regs 2 -> ew E GA_SP = getr regs 8 -> ew E GA_SP1 = getr regs 9 ->
ew E 3%nat = getr regs 3 -> ew E 4%nat = getr regs 4 -> ew E GA_FSH = getr regs 19 ->
regs_ok E (gef_sr N) regs.
Proof.
intros E N regs Hat H2 H8 H9 H3 H4 H19.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 0%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 1%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 2%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 3%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 4%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 5%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 6%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 7%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 8%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 9%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 10%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 11%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 12%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 13%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 14%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 15%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 16%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 17%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 18%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 19%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 20%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 21%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 22%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 23%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 24%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 25%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 26%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 27%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 28%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 29%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 30%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H19 31%nat|].
destruct Hr.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASETF : aset_shadow_realizes SEGS B (SIGMA GS___asan_set_shadow_f5) 0xf5.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* The table is not a block of the caller: the blocks are disjoint position by position
   (AR_blocks_law), and the table's range is not empty. *)
Lemma gef_blk1_fresh : forall cx ly3 S3 W3 mem3 md3 t,
AR SEGS B ly3 S3 W3 mem3 md3 -> gblk1 B cx ly3 S3 t ->
~ In (t, 460) (ablocks B (c_ly cx) (c_S cx)).
Proof.
intros cx ly3 S3 W3 mem3 md3 t HAR Hg Hc.
apply in_split in Hc as (l1 & l2 & E1).
pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (t, 460) (t, 460) l1 l2 [] HAR) as Hd.
unfold gblk1 in Hg. rewrite Hg, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (Hr : req_size 460 = 460) by reflexivity. rewrite Hr in Hd. lia.
Qed.

(* Taking a block that is not in C out of C ++ [x] leaves C. *)
Lemma gef_remove_last_fresh : forall (C l1 l2 : list (Z * Z)) x,
~ In x C -> C ++ [x] = l1 ++ x :: l2 -> l1 ++ l2 = C.
Proof.
intros C l1 l2 x Hx E.
induction l2 as [|y l2' _] using rev_ind.
- rewrite app_nil_r. symmetry. exact (proj1 (app_inj_tail C l1 x x E)).
- exfalso.
  rewrite app_comm_cons, app_assoc in E.
  apply app_inj_tail in E as (E & ->).
  apply Hx. rewrite E. apply in_or_app. right. left. reflexivity.
Qed.

(* `ge_body` holds of a later machine state that keeps the bytes the body's facts read:
   the saved registers, the frame's shadow bytes, the frame's flag word and the input. *)
Lemma gef_body_keep : forall cx fp pc0 pc W ms W' ms' sh,
  ge_body cx fp pc0 W ms sh ->
  (forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) \/
             gSH cx fp <= a < gSH cx fp + Z.of_nat (length sh) \/
             gF cx fp + 1016 <= a < gF cx fp + 1024 \/
             c_p cx <= a < c_p cx + c_n cx ->
     aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_pc_val ms' = w64 (BASE + pc) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx ms' ->
  ge_body cx fp pc W' ms' sh.
Proof.
  intros cx fp pc0 pc W ms W' ms' sh HB HK Hpc Hrv Hsv Hrom Hfr Hfc Hrg.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & (Hra & Hs12) & Hsh & Hfl & Hlen & Hg).
  split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hfc|]. split; [exact Hrg|].
  split; [split|].
  { apply (gef_rdword_keep (aview SEGS (w_H W) (ms_mem ms))); [|exact Hra].
    intros i Hi. apply HK. left. lia. }
  { intros j Hj. apply (gef_rdword_keep (aview SEGS (w_H W) (ms_mem ms))); [|exact (Hs12 j Hj)].
    intros i Hi. apply HK. left. lia. }
  split.
  { intros i Hi. rewrite HK by (right; left; lia). exact (Hsh i Hi). }
  split.
  { apply (gef_rdword_keep (aview SEGS (w_H W) (ms_mem ms))); [|exact Hfl].
    intros i Hi. apply HK. right. right. left. lia. }
  split; [exact Hlen|].
  intros j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k0 Hk0. assert (k0 = 0)%nat by lia. subst k0.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
  rewrite length_map in Hj. unfold c_n in HK.
  assert (Hx : aview SEGS (w_H W') (ms_mem ms') (c_p cx + Z.of_nat j) =
               aview SEGS (w_H W) (ms_mem ms) (c_p cx + Z.of_nat j))
    by (apply HK; right; right; right; lia).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') (ms_mem ms) (ms_mem ms') _ Hx).
  exact Hv0.
Qed.

(* The right to write the windows of this phase's regions: the spill slots on the
   machine stack, the frame, and the first 104 shadow bytes of the frame. *)
Lemma gef_awr : forall cx fp E sh scs fcs ly S lyc Sc,
  ew E GA_SP1 = Z_to_bv 64 (c_sp1 cx) -> ew E GA_F = Z_to_bv 64 (gF cx fp) ->
  ew E GA_FSH = Z_to_bv 64 (gSH cx fp) ->
  0 <= c_sp1 cx < 2 ^ 64 ->
  spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288 ->
  0 <= gF cx fp < 2 ^ 64 -> frame_addr lyc GE_CID fp = gF cx fp ->
  0 <= gSH cx fp < 2 ^ 64 -> gSH cx fp = shadow_addr (gF cx fp) ->
  awr_ok E (ge_regions cx fp sh scs fcs 0 104 []) GE_STK (spZ (c_regs cx)) []
    (ablocks B ly S) (ablocks B lyc Sc) lyc [(GE_CID, fp)].
Proof.
  intros cx fp E sh scs fcs ly S lyc Sc E60 E516 E529 Hsp1r Hsp1 HFr HFa HSr ESH.
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  unfold ge_regions, ge_regions0, ge_obj_regions. cbn [app].
  apply awr_ok_cons_ro; [unfold ge_saved_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ GA_SP1 (c_sp1 cx - spZ (c_regs cx)));
    [ unfold ge_spill_region; reflexivity
    | rewrite E60; rewrite unsigned_lit_small by lia; lia
    | unfold ge_spill_region; cbn [YP09.r_wlo]; unfold GE_STK, GrantBContracts.STK_LLVMFuzzerTestOneInput; lia
    | unfold ge_spill_region; cbn [YP09.r_whi]; lia
    | ].
  apply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ GA_F (gF cx fp));
    [ unfold ge_frame_region, fframe_region; reflexivity
    | rewrite E516; apply unsigned_lit_small; lia
    | unfold ge_frame_region, fframe_region; cbn [YP09.r_wlo YP09.r_whi];
      intros a Ha; right; right; right; exists GE_CID, fp;
      split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
      rewrite HFa; rewrite Hfb in Ha |- *; lia
    | ].
  apply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ GA_FSH (gSH cx fp));
    [ unfold ge_shadow_region, fshadow_region; reflexivity
    | rewrite E529; apply unsigned_lit_small; lia
    | unfold ge_shadow_region, fshadow_region; cbn [YP09.r_wlo YP09.r_whi];
      intros a Ha; right; right; right; exists GE_CID, fp;
      split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
      rewrite HFa, Hfb; change (1024 / 8) with 128; rewrite <- ESH; lia
    | ].
  apply awr_ok_cons_ro; [unfold got_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold uar_got_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold uar_cell_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
Qed.

(* 0x80cd8 .. 0x80d94: the frame is given back and the function returns 0. *)
Theorem ge_leave : ge_from B MT (ge_post B MT) (GI_leave B MT).
Proof.
intros cx fp k acc ly3 S3 W3 ms3 md3 HBASE HJ3 Hfrs3 HMLE HINV.
pose proof HBASE as (HPRE & Hp10 & Hp11 & Hpn & HPLc & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & Usp & E32c & HMOK & HTR & HNEED).
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & HpresW & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (PBASE : 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64 /\ BASE mod 4 = 0) by exact pa_B_ok.
assert (PBLO : 0x10000 <= BASE) by (pose proof pa_base_lo as X; rewrite IMG_LO_B_val in X; exact X).
assert (Hwx : wx_segs_nowrap SEGS) by exact pa_wx.
assert (Hsegs : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd) by exact pa_segs_low.
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HINV as ((shx & HBODY) & Hk & Hacc & Eab3 & R16 & R21 & R19).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HSHD & HFLW & Hlensh & HPLm).
pose proof HREGS as (Rsp & Rs0 & Rs1 & Rgp3 & Rtp3).
pose proof HSAVED as (Hra_sv & Hsv).
assert (Hfin3 : In (GE_CID, fp) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
pose proof (proj1 HJ3) as HAR3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _).
assert (EFL3 : forall c q, flag_addr ly3 c q = flag_addr (c_ly cx) c q)
  by (intros c q; unfold flag_addr; pose proof (EFA3 c q) as X; unfold frame_addr in X; lia).
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR3 Hfin3) as (HFalign & HFapp & HFpres3 & HFSpres3).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ GE_CID fp HAR3 Hfin3) as (HF4096 & HFceil & HFinapp).
destruct (frame_al64 SEGS B _ _ _ _ _ GE_CID fp HAR3 Hfin3) as (HF64 & _ & _).
destruct (FFL _ _ _ _ _ GE_CID fp HAR3 Hfin3) as (HFLpres & HFLown & HFLrng).
rewrite ?EFA3 in HFalign, HFapp, HFpres3, HFSpres3, HF4096, HFceil, HFinapp, HF64.
rewrite ?EFL3 in HFLpres, HFLown, HFLrng.
assert (EgF : frame_addr (c_ly cx) GE_CID fp = gF cx fp) by reflexivity.
assert (EgFL : flag_addr (c_ly cx) GE_CID fp = gFL cx fp) by reflexivity.
rewrite ?EgF in HFalign, HFapp, HFpres3, HFSpres3, HF4096, HFceil, HFinapp, HF64.
rewrite ?EgFL in HFLpres, HFLown, HFLrng.
change (fs_frame_bytes GE_CID) with 1024 in *.
set (F := gF cx fp) in *.
set (FL := gFL cx fp) in *.
set (SHA := gSH cx fp) in *.
assert (ESHA : SHA = shadow_addr F) by reflexivity.
assert (EFAly3 : frame_addr ly3 GE_CID fp = F) by (rewrite EFA3, EgF; reflexivity).
assert (EFLly3 : flag_addr ly3 GE_CID fp = FL) by (rewrite EFL3, EgFL; reflexivity).
assert (Hrng : forall r : bv 5, 0 <= bv_unsigned (getr (c_regs cx) r) < 2 ^ 64)
  by (intros r; pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) r)) as Q;
      change (bv_modulus 64) with (2 ^ 64) in Q; exact Q).
assert (HF32 : F mod 32 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D. replace (64 * (F / 64)) with (2 * (F / 64) * 32) by lia. apply Z_mod_mult. }
destruct (sp1_facts (spZ (c_regs cx) + -288) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1 : spZ (c_regs cx) - 304 <= c_sp1 cx <= spZ (c_regs cx) - 288) by (clear - Hsp1r; lia).
clear Hsp1r.
destruct (YCbq.shadow_addr_bounds F ltac:(clear - HF4096 HFceil C1 C4; lia)) as (Hsb1 & Hsb2).
assert (HSHAhi : SHA + 128 < alloc_ceiling) by (rewrite ESHA; clear - Hsb2 C1 C2; lia).
assert (HSHA64 : 0 <= SHA /\ SHA + 128 <= 2 ^ 64)
  by (rewrite ESHA; clear - Hsb1 Hsb2 C2 C5; lia).
assert (HdFS : SHA + 128 <= F \/ F + 1024 <= SHA).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as Mq.
  assert (Hq0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  rewrite ESHA. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. unfold SB.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFinapp.
  destruct HFinapp as (_ & [Hlow | [Hhi1 Hhi2]]); [right; lia | left; lia]. }
assert (HdFFL : FL + 1 <= F \/ F + 1024 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 1024)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres3 FL ltac:(lia)) HFLown). }
assert (Ems3 : ms3 = mkst (ms_regs ms3) (w64 (BASE + GP_leave)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity. }
remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 SB])) as EB eqn:HEB.
remember (havoc (havoc EB 528 [Z_to_bv 64 FL]) 540
  [getr (c_regs cx) 1;
   getr (c_regs cx) 8; getr (c_regs cx) 9;
   getr (c_regs cx) 18; getr (c_regs cx) 19;
   getr (c_regs cx) 20; getr (c_regs cx) 21;
   getr (c_regs cx) 22; getr (c_regs cx) 23;
   getr (c_regs cx) 24; getr (c_regs cx) 25;
   getr (c_regs cx) 26; getr (c_regs cx) 27]) as E eqn:HE.
assert (EWlow : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn Hr. rewrite HE. rewrite !ew_havoc_old by lia. rewrite HEB. apply ew_Eimg_Ereg_nat. exact Hr. }
assert (E2 : ew E 2 = Z_to_bv 64 (c_sp1 cx))
  by (rewrite (EWlow 2%nat (2%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rsp).
assert (E3 : ew E 3 = getr (c_regs cx) 3)
  by (rewrite (EWlow 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rgp3).
assert (E4 : ew E 4 = getr (c_regs cx) 4)
  by (rewrite (EWlow 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rtp3).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx)))
  by (rewrite (EWlow 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rs0).
assert (E16 : ew E 16 = Z_to_bv 64 F)
  by (rewrite (EWlow 16%nat (16%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R16).
assert (E19 : ew E 19 = Z_to_bv 64 SHA)
  by (rewrite (EWlow 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 F)
  by (rewrite (EWlow 21%nat (21%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ rewrite HE. rewrite !ew_havoc_old by lia. rewrite HEB. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra (ms_regs ms3) [Z_to_bv 64 SB] 0). }
assert (E528 : ew E 528 = Z_to_bv 64 FL).
{ rewrite HE. rewrite ew_havoc_old by lia.
  exact (ew_havoc_new EB 528 [Z_to_bv 64 FL] 0 (Z_to_bv 64 0) ltac:(cbn; lia)). }
assert (E540 : ew E 540 = getr (c_regs cx) 1)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E541 : ew E 541 = getr (c_regs cx) 8)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E542 : ew E 542 = getr (c_regs cx) 9)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E543 : ew E 543 = getr (c_regs cx) 18)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E544 : ew E 544 = getr (c_regs cx) 19)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E545 : ew E 545 = getr (c_regs cx) 20)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E546 : ew E 546 = getr (c_regs cx) 21)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E547 : ew E 547 = getr (c_regs cx) 22)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E548 : ew E 548 = getr (c_regs cx) 23)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E549 : ew E 549 = getr (c_regs cx) 24)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E550 : ew E 550 = getr (c_regs cx) 25)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E551 : ew E 551 = getr (c_regs cx) 26)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E552 : ew E 552 = getr (c_regs cx) 27)
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (HRO : regs_ok E sr_atoms (ms_regs ms3)).
{ rewrite HE. apply regs_ok_havoc_hi; [lia|]. apply regs_ok_havoc_hi; [lia|].
  rewrite HEB. apply regs_ok_Eimg_Ereg. }
assert (HEI : img_env VAL A_LIM E).
{ rewrite HE. apply img_env_havoc_hi; [|unfold A_LIM; lia].
  apply img_env_havoc_hi; [|unfold A_LIM; lia]. rewrite HEB. apply Eimg_env. }
assert (HS : st_ok_pi SEGS VAL E
  (mkSS GP_leave sr_atoms
     [ YP09.mkRegion (Some 21%nat) 0 1024 0 8 [YP09.mkChunk 1016 (CVal 8 (SOff 528 0))];
       YP09.mkRegion (Some 8%nat) (-104) 0 0 0
         [YP09.mkChunk (-104) (CVal 8 (SOff 552 0));
          YP09.mkChunk (-96) (CVal 8 (SOff 551 0));
          YP09.mkChunk (-88) (CVal 8 (SOff 550 0));
          YP09.mkChunk (-80) (CVal 8 (SOff 549 0));
          YP09.mkChunk (-72) (CVal 8 (SOff 548 0));
          YP09.mkChunk (-64) (CVal 8 (SOff 547 0));
          YP09.mkChunk (-56) (CVal 8 (SOff 546 0));
          YP09.mkChunk (-48) (CVal 8 (SOff 545 0));
          YP09.mkChunk (-40) (CVal 8 (SOff 544 0));
          YP09.mkChunk (-32) (CVal 8 (SOff 543 0));
          YP09.mkChunk (-24) (CVal 8 (SOff 542 0));
          YP09.mkChunk (-16) (CVal 8 (SOff 541 0));
          YP09.mkChunk (-8) (CVal 8 (SOff 540 0))] ]
     None (mkFacts [(21%nat, HPTR 5); (32%nat, mkAF SB SB 0); (528%nat, HPTR 0)] [] []))
  (restrict (w_H W3) ms3)).
{ rewrite Ems3. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E21, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres3 (F + o) ltac:(lia))).
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ F 1016 8 (SOff 528 0) FL).
        -- cbn [sv_denot]. rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS _ _ _ _ HFLW).
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E8, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      repeat (apply Forall_cons;
        [ first
          [ apply (gl_chunk E (w_H W3) (ms_mem ms3) 552%nat (spZ (c_regs cx)) (-104) (bv_unsigned (getr (c_regs cx) 27)));
            [rewrite E552; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -104) with (spZ (c_regs cx) - 16 - 8 * 11) by lia; exact (Hsv 11 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 551%nat (spZ (c_regs cx)) (-96) (bv_unsigned (getr (c_regs cx) 26)));
            [rewrite E551; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -96) with (spZ (c_regs cx) - 16 - 8 * 10) by lia; exact (Hsv 10 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 550%nat (spZ (c_regs cx)) (-88) (bv_unsigned (getr (c_regs cx) 25)));
            [rewrite E550; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -88) with (spZ (c_regs cx) - 16 - 8 * 9) by lia; exact (Hsv 9 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 549%nat (spZ (c_regs cx)) (-80) (bv_unsigned (getr (c_regs cx) 24)));
            [rewrite E549; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -80) with (spZ (c_regs cx) - 16 - 8 * 8) by lia; exact (Hsv 8 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 548%nat (spZ (c_regs cx)) (-72) (bv_unsigned (getr (c_regs cx) 23)));
            [rewrite E548; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -72) with (spZ (c_regs cx) - 16 - 8 * 7) by lia; exact (Hsv 7 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 547%nat (spZ (c_regs cx)) (-64) (bv_unsigned (getr (c_regs cx) 22)));
            [rewrite E547; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -64) with (spZ (c_regs cx) - 16 - 8 * 6) by lia; exact (Hsv 6 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 546%nat (spZ (c_regs cx)) (-56) (bv_unsigned (getr (c_regs cx) 21)));
            [rewrite E546; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -56) with (spZ (c_regs cx) - 16 - 8 * 5) by lia; exact (Hsv 5 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 545%nat (spZ (c_regs cx)) (-48) (bv_unsigned (getr (c_regs cx) 20)));
            [rewrite E545; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -48) with (spZ (c_regs cx) - 16 - 8 * 4) by lia; exact (Hsv 4 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 544%nat (spZ (c_regs cx)) (-40) (bv_unsigned (getr (c_regs cx) 19)));
            [rewrite E544; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -40) with (spZ (c_regs cx) - 16 - 8 * 3) by lia; exact (Hsv 3 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 543%nat (spZ (c_regs cx)) (-32) (bv_unsigned (getr (c_regs cx) 18)));
            [rewrite E543; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -32) with (spZ (c_regs cx) - 16 - 8 * 2) by lia; exact (Hsv 2 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 542%nat (spZ (c_regs cx)) (-24) (bv_unsigned (getr (c_regs cx) 9)));
            [rewrite E542; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -24) with (spZ (c_regs cx) - 16 - 8 * 1) by lia; exact (Hsv 1 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 541%nat (spZ (c_regs cx)) (-16) (bv_unsigned (getr (c_regs cx) 8)));
            [rewrite E541; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia; exact (Hsv 0 ltac:(lia))]
          | apply (gl_chunk E (w_H W3) (ms_mem ms3) 540%nat (spZ (c_regs cx)) (-8) (raZ (c_regs cx)));
            [rewrite E540; reflexivity | apply Hrng
            | replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia; exact Hra_sv] ] | ]);
      apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E21, E8, !unsigned_lit_small by lia.
    split; [split; [left; lia | exact I] | split; [exact I | exact I]].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias].
    split; [|split; [exact I | exact I]].
    cbn [atoms_ok]. split; [|split; [|split; [|exact I]]].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E21, unsigned_lit_small by lia. change (2 ^ 5) with 32.
      split; [lia|]. split; [exact HF32 | lia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, unsigned_lit_small by (unfold SB; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E528, unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (16%bv : bv 5) (SOff 21 0) HS
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E21, unsigned_lit_small by lia;
          rewrite Z.add_0_r; symmetry; exact R16)) as HS2 end.
clear HS. rename HS2 into HS. norm_ss HS.
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ3 SHOK Bspan.
2: {
prreg HS (1%bv : bv 5) Rra1. prreg HS (2%bv : bv 5) Rsp2. prreg HS (3%bv : bv 5) Rgp2.
prreg HS (4%bv : bv 5) Rtp2. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
  eapply (aj_set_shadow_at SEGS B LAWS pa_segs_low (SIGMA GS___asan_set_shadow_f5) 245 ASETF
    W3 (ms_regs msX) (ms_mem msX) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 mdX k GE_CID fp SHA 128 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 0x2b8)) HJ3) end.
  - left; reflexivity.
  - rewrite Ra0, E19. reflexivity.
  - rewrite Ra1. reflexivity.
  - lia.
  - rewrite EFAly3, ESHA. lia.
  - rewrite EFAly3, ESHA. change (fs_frame_bytes GE_CID / 8) with 128. lia.
  - unfold spZ at 1. rewrite Rsp2, E2, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Hsp1al16, Hal16. reflexivity.
  - lia.
  - unfold ESTACK, GE_STK, GrantBContracts.STK_LLVMFuzzerTestOneInput. lia.
  - rewrite Rgp2, E3. exact Hgp.
  - rewrite Rtp2, E4. exact Htp.
  - exact Rra1.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hf5 & Hkeep4 & Hpres4).
pose proof (proj1 HJ4) as HAR4.
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR4 Hfin3) as (_ & _ & HFpres4 & _).
rewrite ?EFA3, ?EgF in HFpres4. change (fs_frame_bytes GE_CID) with 1024 in HFpres4.
destruct (FFL _ _ _ _ _ GE_CID fp HAR4 Hfin3) as (HFLpres4 & _ & _).
rewrite ?EFL3, ?EgFL in HFLpres4.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reseat HS HJ4 HP4 [0%nat; 1%nat] AG
  ltac:(idtac;
    lazymatch goal with
    | |- region_kept _ _ _ _ (YP09.mkRegion (Some 21%nat) _ _ _ _ _) =>
      eapply (gl_kept E (w_H W3) _ _ 21%nat F);
      [ first [rewrite E21; apply unsigned_lit_small; lia | idtac "B1"; fail]
      | first [intros a Ha; apply Hkeep4; [lia | clear - Ha HdFS; lia] | idtac "B2"; fail]
      | first [intros a Ha; apply (apresent_writable SEGS); apply (proj1 (HFpres4 a ltac:(lia)))
             | idtac "B3"; fail] ]
    | |- region_kept _ _ _ _ (YP09.mkRegion (Some 8%nat) _ _ _ _ _) =>
      eapply (gl_kept E (w_H W3) _ _ 8%nat (spZ (c_regs cx)));
      [ first [rewrite E8; apply unsigned_lit_small; lia | idtac "C1"; fail]
      | first [intros a Ha; apply Hkeep4; [lia | clear - Ha HSHAhi Hceil Hslo FFS; lia] | idtac "C2"; fail]
      | first [intros a Ha; exfalso; lia | idtac "C3"; fail] ]
    | |- ?g => idtac "KEPT-OTHER:" g; fail
    end).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
    ltac:(unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E528, unsigned_lit_small by lia;
          split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; replace (FL + o) with FL by lia;
          apply (apresent_writable SEGS); exact HFLpres4)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite (AG 21%nat), (AG 8%nat) by lia;
          rewrite E528, E21, E8, !unsigned_lit_small by lia;
          split; [clear - HdFFL; lia | split; [clear - HFLrng Hceil Hslo FFS; lia | exact I]])) as HS2 end.
clear HS. rename HS2 into HS. norm_ss HS.
paj_run_flag_sh RUNF HS HJ4.
- unfold GE_CID; lia.
- intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | Hin]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + rewrite E528, unsigned_lit_small in Ha by lia.
    right. rewrite EFLly3. lia.
  + rewrite (AG 21%nat) in Ha by lia. rewrite E21, unsigned_lit_small in Ha by lia.
    left. right. right. right. exists GE_CID, fp. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFAly3. change (fs_frame_bytes GE_CID) with 1024. lia.
  + exfalso. rewrite (AG 8%nat) in Ha by lia. rewrite E8, unsigned_lit_small in Ha by lia. lia.
  + destruct Hin.
- flag0 E528 EFLly3.
- prreg HS (1%bv : bv 5) Rra_f. prreg HS (10%bv : bv 5) Ra0_f.
  lazymatch goal with |- SRr _ ?Wx _ _ =>
    eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
  intros mat'. unfold ge_post.
  lazymatch goal with |- exists _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
    exists ly3, (stack_free_state GE_CID fp S3), rg, mm, mdx, k end.
  split.
  { rewrite Rra_f. rewrite E540.
    replace (v_jalr (getr (c_regs cx) 1) 0) with (getr (c_regs cx) 1) by (symmetry; exact Hra1).
    reflexivity. }
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ4|].
  split; [unfold GE_EV, GrantBContracts.EV_LIB_B; lia|].
  split.
  { apply aregs_preserved_eqs.
    - prreg HS (2%bv : bv 5) Q2. rewrite Q2, (AG 8%nat) by lia. rewrite E8.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - prreg HS (3%bv : bv 5) Q3. rewrite Q3, (AG 3%nat) by lia. rewrite E3. reflexivity.
    - prreg HS (4%bv : bv 5) Q4. rewrite Q4, (AG 4%nat) by lia. rewrite E4. reflexivity.
    - prreg HS (8%bv : bv 5) Q8. rewrite Q8. exact E541.
    - prreg HS (9%bv : bv 5) Q9. rewrite Q9. exact E542.
    - prreg HS (18%bv : bv 5) Q18. rewrite Q18. exact E543.
    - prreg HS (19%bv : bv 5) Q19. rewrite Q19. exact E544.
    - prreg HS (20%bv : bv 5) Q20. rewrite Q20. exact E545.
    - prreg HS (21%bv : bv 5) Q21. rewrite Q21. exact E546.
    - prreg HS (22%bv : bv 5) Q22. rewrite Q22. exact E547.
    - prreg HS (23%bv : bv 5) Q23. rewrite Q23. exact E548.
    - prreg HS (24%bv : bv 5) Q24. rewrite Q24. exact E549.
    - prreg HS (25%bv : bv 5) Q25. rewrite Q25. exact E550.
    - prreg HS (26%bv : bv 5) Q26. rewrite Q26. exact E551.
    - prreg HS (27%bv : bv 5) Q27. rewrite Q27. exact E552. }
  split; [rewrite Ra0_f; reflexivity|].
  split.
  { unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly3 S3).
    rewrite Eab3. apply Permutation_refl. }
  split.
  { unfold stack_free_state. apply (mo_le_set_fs_r MT MTF).
    apply (mo_le_mono MT MTL _ _ _ _ HMLE). lia. }
  intros i Hi.
  destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; lia|].
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FF2 & _).
  apply (FF2 (c_p cx) (c_n cx) i Hpin).
  + unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly3 S3).
    rewrite Eab3. exact Hpin.
  + unfold req_size. destruct (Z.eqb_spec (c_n cx) 0) as [Heq0|Hne0]; [exfalso; lia | exact Hi].
  + intros (r & Hin & _). destruct Hin. }
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 21%nat F).
- reflexivity.
- rewrite E21. apply unsigned_lit_small. lia.
- cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
  exists GE_CID, fp. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EFAly3. change (fs_frame_bytes GE_CID) with 1024. lia.
- apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
Qed.

(* 0x81da4 .. 0x81e94: the table is freed and the frame's objects are marked unusable
   again; the walk lands in the cut `GI_leave` at 0x80cd8. *)
Theorem ge_end_free : forall POST, ge_from B MT POST (GI_leave B MT) -> ge_from B MT POST (GI_freeT B MT).
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HBASE HJ3 Hfrs3 HMLE HINV.
pose proof HBASE as (HPRE & Hp10 & Hp11 & Hpn & HPLc & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & Usp & E32c & HMOK & HTR & HNEED).
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & HpresW & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (PBASE : 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64 /\ BASE mod 4 = 0) by exact pa_B_ok.
assert (PBLO : 0x10000 <= BASE) by (pose proof pa_base_lo as X; rewrite IMG_LO_B_val in X; exact X).
assert (Hsegs : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd) by exact pa_segs_low.
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HINV as (t & HBODY & Hk & Hacc & Hblk1 & Hn26 & R20 & R19 & HSL8 & HSL72).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HSHD & HFLW & Hlensh & HPLm).
pose proof HREGS as (Rsp & Rs0 & Rs1 & Rgp3 & Rtp3).
assert (Hfin3 : In (GE_CID, fp) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
pose proof (proj1 HJ3) as HAR3.
assert (HFF : 4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\
              in_app (gF cx fp) 1024 /\
              (gF cx fp + 1024 <= IMG_LO_B \/ IMG_TOP_B <= gF cx fp) /\
              gSH cx fp = SHADOW_OFF + gF cx fp / 8)
  by (eapply ge_F_facts; eassumption).
pose proof HFF as (HF4096 & HFceil & HFinapp & HFimg & HSHeq).
assert (HSPF : spZ (c_regs cx) mod 16 = 0 /\
               alloc_ceiling + 32768 <= spZ (c_regs cx) /\
               spZ (c_regs cx) <= 2 ^ 47 /\
               spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288)
  by (eapply ge_sp_facts; eassumption).
pose proof HSPF as (Hspal & Hsplo & Hsphi & Hsp1b).
assert (EFAly3 : frame_addr ly3 GE_CID fp = gF cx fp)
  by (eapply ge_frame_addr_eq; eassumption).
assert (HFbv : 0 <= gF cx fp < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (HSHbv : 0 <= gSH cx fp /\ gSH cx fp + 128 <= 2 ^ 64)
  by (eapply ge_sh_range; eassumption).
(* ---- the table: a block of its own, apart from the caller's blocks, the frame and
   the frame's shadow ---- *)
assert (ERQT : req_size 460 = 460) by reflexivity.
assert (FB : fs_frame_bytes GE_CID = 1024) by reflexivity.
assert (Hnotin : ~ In (t, 460) (ablocks B (c_ly cx) (c_S cx)))
  by exact (gef_blk1_fresh cx ly3 S3 W3 (ms_mem ms3) md3 t HAR3 Hblk1).
assert (Hint : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in Hblk1; rewrite Hblk1; apply in_or_app; right; left; reflexivity).
destruct (al_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 t 460 HAR3 Hint)
  as (Ht16 & Ht4096 & Htceil & Htapp & _).
rewrite ERQT in Htceil, Htapp.
assert (DFt : gF cx fp + 1024 <= t \/ t + 460 <= gF cx fp).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 t 460 GE_CID fp HAR3 Hint Hfin3) as D.
  rewrite EFAly3, FB, ERQT in D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (ESH : gSH cx fp = shadow_addr (gF cx fp)) by (rewrite HSHeq; reflexivity).
pose proof (YCbq.shadow_addr_bounds (gF cx fp) ltac:(lia)) as (Hsb1 & _).
pose proof (YCbq.shadow_addr_bounds (gF cx fp + 1024) ltac:(lia)) as (_ & Hsb2).
pose proof (YCbq.shadow_range_end (gF cx fp) 1024 ltac:(lia)) as Hsre.
change (1024 / 8) with 128 in Hsre.
assert (DSHt : gSH cx fp + 128 <= t \/ t + 460 <= gSH cx fp).
{ rewrite ESH. destruct Htapp as (_ & [Hlo | (Hhi & _)]).
  - right. unfold kLowShadowBeg in Hlo. lia.
  - left. lia. }
assert (Dpt : c_n cx = 0 \/ c_p cx + c_n cx <= t \/ t + 460 <= c_p cx).
{ destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [left; exact Hn0 | right].
  apply in_split in Hin0. destruct Hin0 as (m1 & m2 & Em).
  assert (Heq : ablocks B ly3 S3 = m1 ++ (c_p cx, c_n cx) :: m2 ++ (t, 460) :: []).
  { unfold gblk1 in Hblk1. rewrite Hblk1, Em, <- app_assoc. reflexivity. }
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx, c_n cx) (t, 460)
    m1 m2 [] HAR3 Heq) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite ERQT in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq). lia. }
(* ---- the mv at 0x81da4 ---- *)
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_freeT)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity. }
assert (Hslot0 : plookup (pl_tpi (L := grant_listing)) GP_freeT = Some (PW 656659))
  by (vm_compute; reflexivity).
rewrite <- (pl_tpi_eq (L := grant_listing)) in Hslot0.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA grant_listing pa_cert _ _ Hslot0) as HCK0.
destruct HCK0 as (Hck0 & _ & _).
cbv beta iota zeta delta [pi_slot_check] in Hck0.
destruct (clookup pa_tbl (VAL A_TEXT + GP_freeT)) as [w0|] eqn:Hfw0; [|discriminate Hck0].
apply Z.eqb_eq in Hck0. subst w0.
destruct (decode_any (Z_to_bv 32 656659)) as [[i0 isz0]|] eqn:Hdec0.
2: { exfalso. vm_compute in Hdec0. discriminate. }
assert (Ei0 : i0 = OpImm ALU_ADD (Z_to_bv 5 10) (Z_to_bv 5 20) (Z_to_bv 12 0) /\ isz0 = 4%Z).
{ pose proof Hdec0 as H'. vm_compute in H'. injection H' as Ei Es. subst i0 isz0.
  split; [|reflexivity]. f_equal; apply bv_eq; vm_compute; reflexivity. }
destruct Ei0 as [-> ->].
assert (HSTEP0 : RiscvSemantics.step SEGS (restrict (w_H W3) ms3) =
  MachineOk (mkst (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
                  (Z_to_bv 64 (BASE + (GP_freeT + 4))) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
{ rewrite Ems3 at 1. rewrite restrict_mkst_fx.
  rewrite (step_addi_at SEGS (ms_regs ms3) (Z_to_bv 64 (BASE + GP_freeT)) (mrestrict (w_H W3) (ms_mem ms3))
    (seg_rom SEGS) (Z_to_bv 32 656659) (Z_to_bv 5 10) (Z_to_bv 5 20) (Z_to_bv 12 0)
    (getr (ms_regs ms3) (Z_to_bv 5 20)) (pa_fetch_ok _ _ Hfw0)
    (not_ecall_of_decode _ _ _ Hdec0 ltac:(discriminate)) Hdec0 ltac:(vm_compute; reflexivity)).
  2: { unfold v_addi. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite Z.add_0_r.
       apply Z_to_bv_bv_unsigned. }
  assert (Epc : v_addi (Z_to_bv 64 (BASE + GP_freeT)) 4 = Z_to_bv 64 (BASE + (GP_freeT + 4))).
  { unfold v_addi. rewrite unsigned_lit_small by (unfold GP_freeT; lia). f_equal. lia. }
  rewrite Epc. reflexivity. }
eapply (SRr_step SEGS pa_wx W3 ms3 _ md3); [exact Hsvc | exact HSTEP0 |].
intros model1 Hsame1.
rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb md3 model1 Hsame1).
(* ---- the jal at 0x81da8 ---- *)
assert (Hslot1 : plookup (pl_tpi (L := grant_listing)) (GP_freeT + 4)
  = Some (PCall GS___interceptor_trampoline_free (1%bv : Prelude.reg))) by (vm_compute; reflexivity).
rewrite <- (pl_tpi_eq (L := grant_listing)) in Hslot1.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA grant_listing pa_cert _ _ Hslot1) as HCK.
destruct HCK as (Hck & _ & _).
cbv beta iota zeta delta [pi_slot_check] in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (GP_freeT + 4))) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck. destruct Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck. destruct Hck as (Hck1 & Ht).
apply andb_prop in Hck1. destruct Hck1 as (Hrd & _).
apply reg_eqb_eq in Hrd. apply Z.eqb_eq in Ht. rewrite <- Hrd in Hdec.
assert (HSTEP1 : RiscvSemantics.step SEGS (restrict (w_H W3)
    (mkst (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
          (Z_to_bv 64 (BASE + (GP_freeT + 4))) (ms_mem ms3) (seg_rom SEGS))) =
  MachineOk (mkst (regupd (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
                     (1%bv : Prelude.reg) (Z_to_bv 64 (BASE + (GP_freeT + 8))))
                  (Z_to_bv 64 (pc_wrap_free (as_code B)))
                  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
{ rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS _ (Z_to_bv 64 (BASE + (GP_freeT + 4)))
    (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS) (Z_to_bv 32 wz) (1%bv : Prelude.reg) _
    (pa_fetch_ok _ _ Hfw) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  destruct (bv_eqb (1%bv : Prelude.reg) 0) eqn:Hx0; [vm_compute in Hx0; discriminate|].
  f_equal. f_equal.
  - f_equal. unfold v_addi. rewrite unsigned_lit_small by (unfold GP_freeT; lia).
    f_equal. unfold GP_freeT. lia.
  - unfold btgt, v_addi. rewrite unsigned_lit_small by (unfold GP_freeT; lia).
    rewrite <- (pal_free B TL), <- Ht. symmetry. apply lit_canon. }
eapply (SRr_step SEGS pa_wx W3 _ _ _); [reflexivity | exact HSTEP1 |].
intros model2 Hsame2.
rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb _ model2 Hsame2).
set (R2 := regupd (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
                  (1%bv : Prelude.reg) (Z_to_bv 64 (BASE + (GP_freeT + 8)))).
assert (RUPD : forall r : bv 5, r <> (1%bv : bv 5) -> r <> Z_to_bv 5 10 ->
  getr R2 r = getr (ms_regs ms3) r).
{ intros r H1 H10. unfold R2. rewrite gef_reg_other by exact H1.
  rewrite gef_reg_other by exact H10. reflexivity. }
assert (RRA : getr R2 (1%bv : bv 5) = Z_to_bv 64 (BASE + (GP_freeT + 8)))
  by (unfold R2; apply gef_reg_same; vm_compute; reflexivity).
assert (RA0 : getr R2 (Z_to_bv 5 10) = w64 t).
{ unfold R2. rewrite gef_reg_other by bvne.
  rewrite gef_reg_same by (vm_compute; reflexivity). exact R20. }
assert (RSP1 : spZ R2 = c_sp1 cx).
{ unfold spZ. rewrite (RUPD (2%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rsp. unfold w64.
  apply unsigned_lit_small. lia. }
assert (HJ2 : ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
   [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3)
   (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) (m_vm_materialized model1) md3))
      (m_vm_materialized model2) (with_vm_backing (m_vm_lazy md3) (m_vm_materialized model1) md3)) k).
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ3. }
assert (Hsp132 : c_sp1 cx mod 32 = 0).
{ rewrite Esp1. first [apply Z_mod_mult | rewrite Z.mul_comm; apply Z_mod_mult]. }
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ pose proof (proj1 (Z.mod_divide _ 32 ltac:(lia)) Hsp132) as (q & Hq).
  pose proof (proj1 (Z.mod_divide _ 16 ltac:(lia)) Hspal) as (r & Hr).
  rewrite Hq, Hr. replace (q * 32 - r * 16) with ((2 * q - r) * 16) by lia. apply Z_mod_mult. }
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
{ pose proof HJ3 as (_ & Hly3 & _).
  apply (achain_ly_top (c_ly cx) ly3);
    [destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et|].
  pose proof HSAVED as (Hra_sv & Hsv).
  eapply ge_achain.
  all: first
    [ exact HBASE
    | intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 a Ha)
    | exact Hra_sv
    | replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia; exact (Hsv 0 ltac:(lia))
    | lia
    | eassumption ]. }
(* ---- the call of the wrapper for free: its contract asks that the table is a live
   block (`Hint`), that the call site is one the call trace allows (the third site of
   `GE_FSITES`), and that the table is not one of the caller's blocks (`Hnotin`); its
   own error path (an invalid or double free) is therefore not reached ---- *)
eapply SRr_bind.
{ eapply (AFREE4 W3 R2 (ms_mem ms3) GE_STK (spZ (c_regs cx)) (@nil (Z * Z))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k t 460
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + (GP_freeT + 8))) (gch cx) HJ2 Hint).
  - exact RA0.
  - rewrite RSP1. lia.
  - exact Ho16.
  - lia.
  - assert (Has : ASTACK = 16384) by reflexivity. rewrite Has, FFS. lia.
  - rewrite (RUPD (3%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rgp3. exact Hgp.
  - rewrite (RUPD (4%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rtp3. exact Htp.
  - exact RRA.
  - apply ret_ok_codeptr_v; [unfold GP_freeT; lia | reflexivity].
  - pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & Hk0 & _). unfold GE_EV, GrantBContracts.EV_LIB_B in Hev. lia.
  - apply (achain_chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx) (spZ (c_regs cx))
      (gch cx) _ HCH).
    + rewrite RSP1. lia.
    + unfold s0Z. rewrite (RUPD (8%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rs0. unfold w64.
      apply unsigned_lit_small. lia.
    + unfold raZ. rewrite RRA, unsigned_lit_small by (unfold GP_freeT; lia). unfold GP_freeT. lia.
  - apply HTR. right. split; [reflexivity|].
    unfold raZ. rewrite RRA, unsigned_lit_small by (unfold GP_freeT; lia).
    replace (BASE + (GP_freeT + 8) - BASE) with (GP_freeT + 8) by lia.
    unfold GE_FSITES, GrantBContracts.TB_LLVMF_FSITES, GP_freeT. cbn [In]. right. right. left. reflexivity.
  - intros Hcon i Hi. exfalso. exact (Hnotin Hcon).
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL HMOK HMLE).
    + apply (mo_free_nonneg MT MTL).
    + unfold GE_NEED in HNEED. lia. }
cbv beta. intros W4 c4 Hwle4 Hpost.
destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hsplit & Hfrs4 & HK4 & MLE4).
(* ---- the blocks after the free: the caller's ---- *)
destruct Hsplit as (l1 & l2 & Eb3 & Eb4).
assert (Eab4 : ablocks B ly4 S4 = ablocks B (c_ly cx) (c_S cx)).
{ rewrite Eb4. apply (gef_remove_last_fresh _ _ _ (t, 460) Hnotin).
  unfold gblk1 in Hblk1. rewrite <- Hblk1. exact Eb3. }
assert (HFR4 : frames S4 = [(GE_CID, fp)]) by (rewrite Hfrs4; exact Hfrs3).
(* ---- the bytes the call kept ---- *)
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK4 by lia.
destruct HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KEEP : forall a : Z,
  c_sp1 cx <= a < 2 ^ 64 \/ c_p cx <= a < c_p cx + c_n cx \/
  gF cx fp <= a < gF cx fp + 1024 \/ gSH cx fp <= a < gSH cx fp + 128 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - apply K1; lia.
  - destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [exfalso; lia|].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (unfold gblk1 in Hblk1; rewrite Hblk1; apply in_or_app; left; exact Hin0).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq).
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin3); [lia|]. rewrite ERQT. lia.
  - apply (K4 GE_CID fp a Hfin3).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFAly3, FB. lia.
    + rewrite ERQT. lia.
  - apply (K4 GE_CID fp a Hfin3).
    + right. unfold in_zr. cbn [fst snd]. rewrite EFAly3, FB.
      change (1024 / 8) with 128. rewrite <- ESH. lia.
    + rewrite ERQT. lia. }
(* ---- the registers the call kept ---- *)
assert (QP : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP4 r Hr). apply RUPD.
  - intros Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite Z_to_bv_unsigned in Hq. unfold bv_wrap in Hq.
    change (bv_modulus 5) with 32 in Hq.
    rewrite Z.mod_small in Hq by (unfold acallee_saved in Hr; lia).
    vm_compute in Hq. unfold acallee_saved in Hr. lia.
  - intros Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite !Z_to_bv_unsigned in Hq. unfold bv_wrap in Hq.
    change (bv_modulus 5) with 32 in Hq.
    rewrite !Z.mod_small in Hq by (unfold acallee_saved in Hr; lia).
    unfold acallee_saved in Hr. lia. }
set (ms4 := mkst regs4 (Z_to_bv 64 (BASE + (GP_freeT + 8))) mem4 (seg_rom SEGS)).
assert (HJ4s : ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
   [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 (k + 1)) by exact HJ4.
assert (HGR4 : gregs cx ms4).
{ unfold gregs. cbn [ms4 ms_regs mkst].
  split; [etransitivity; [exact (QP 2 ltac:(unfold acallee_saved; lia)) | exact Rsp]|].
  split; [etransitivity; [exact (QP 8 ltac:(unfold acallee_saved; lia)) | exact Rs0]|].
  split; [etransitivity; [exact (QP 9 ltac:(unfold acallee_saved; lia)) | exact Rs1]|].
  split; [etransitivity; [exact (QP 3 ltac:(unfold acallee_saved; lia)) | exact Rgp3]|].
  etransitivity; [exact (QP 4 ltac:(unfold acallee_saved; lia)) | exact Rtp3]. }
assert (HBODY4 : ge_body cx fp (GP_freeT + 8) W4 ms4 GSH_sched).
{ apply (gef_body_keep cx fp GP_freeT (GP_freeT + 8) W3 ms3 W4 ms4 GSH_sched HBODY).
  - intros a Ha. cbn [ms4 ms_mem mkst]. apply KEEP.
    rewrite Hlensh in Ha. unfold GE_NSH in Ha.
    destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    + left. lia.
    + right. right. right. lia.
    + right. right. left. lia.
    + right. left. exact Ha.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact HGR4. }
pose proof HBODY4 as (_ & _ & _ & _ & _ & _ & _ & HSV4 & _ & HFLW4 & _ & _).
assert (HSL4 : forall off, off = 8 \/ off = 72 -> gslot cx W4 ms4 off (gF cx fp)).
{ intros off Hoff. unfold gslot. cbn [ms4 ms_mem mkst].
  apply (gef_rdword_keep (aview SEGS (w_H W3) (ms_mem ms3))).
  - intros i Hi. apply KEEP. left. lia.
  - destruct Hoff as [-> | ->]; [exact HSL8 | exact HSL72]. }
(* ---- the environment after the call ---- *)
remember (havoc (havoc (havoc (havoc (Eimg (c_E0 cx)) GA_SP1 [w64 (c_sp1 cx)])
                              GA_F [w64 (gF cx fp)])
                       GA_FL [w64 (gFL cx fp); w64 (gSH cx fp)])
                530 [getr regs4 0; getr regs4 1; getr regs4 2; getr regs4 3; getr regs4 4;
                     getr regs4 5; getr regs4 6; getr regs4 7; getr regs4 8; getr regs4 9;
                     getr regs4 10; getr regs4 11; getr regs4 12; getr regs4 13; getr regs4 14;
                     getr regs4 15; getr regs4 16; getr regs4 17; getr regs4 18; getr regs4 19;
                     getr regs4 20; getr regs4 21; getr regs4 22; getr regs4 23; getr regs4 24;
                     getr regs4 25; getr regs4 26; getr regs4 27; getr regs4 28; getr regs4 29;
                     getr regs4 30; getr regs4 31]) as E eqn:HE.
assert (EWk : forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n).
{ intros n Hn. rewrite HE. rewrite !ew_havoc_old by (unfold GA_SP1, GA_F, GA_FL; lia).
  apply Eimg_low. unfold A_TEXT. lia. }
assert (E60 : ew E GA_SP1 = w64 (c_sp1 cx))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E516 : ew E GA_F = w64 (gF cx fp))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E528 : ew E GA_FL = w64 (gFL cx fp))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E529 : ew E GA_FSH = w64 (gSH cx fp))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (EAT : forall (i : nat) (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  ew E (530 + i)%nat = getr regs4 r).
{ intros i r Hi Hr.
  assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
               i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/
               i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/
               i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31)%nat)
    by lia.
  repeat (destruct Hc as [-> | Hc];
    [ rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub Nat.add];
      first [ f_equal; apply bv_eq; rewrite <- Hr; vm_compute; reflexivity
            | match goal with |- ?g => idtac "EAT-CASE:" g end; fail ] | ]).
  subst i; rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub Nat.add];
  f_equal; apply bv_eq; rewrite <- Hr; vm_compute; reflexivity. }
assert (HEge : ge_E cx fp E).
{ split; [exact EWk|].
  split; [rewrite (EWk GA_SB ltac:(unfold GA_SB; lia)); exact E32c|].
  split; [exact E60|]. split; [exact E516|]. split; [exact E528 | exact E529]. }
assert (HEI : img_env VAL A_LIM E).
{ rewrite HE. apply img_env_havoc_hi; [|unfold A_LIM; lia].
  apply img_env_havoc_hi; [|unfold A_LIM, GA_FL; lia].
  apply img_env_havoc_hi; [|unfold A_LIM, GA_F; lia].
  apply img_env_havoc; [|unfold GA_SP1, A_TEXT; cbn [length]; lia].
  apply Eimg_env. }
pose proof HGR4 as (G2 & G8 & G9 & G3 & G4).
assert (G19 : getr regs4 (Z_to_bv 5 19) = w64 (gSH cx fp))
  by (etransitivity; [exact (QP 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (HRO : regs_ok E (gef_sr 530) (ms_regs ms4)).
{ apply gef_regs_ok.
  - exact EAT.
  - rewrite E60. symmetry. exact G2.
  - rewrite (EWk GA_SP ltac:(unfold GA_SP; lia)), (EE GA_SP (2%bv : bv 5) ltac:(vm_compute; reflexivity)).
    cbn [ms4 ms_regs mkst] in G8 |- *. rewrite G8.
    unfold w64, spZ. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite E60. symmetry. exact G9.
  - rewrite (EWk 3%nat ltac:(lia)), (EE 3%nat (3%bv : bv 5) ltac:(vm_compute; reflexivity)).
    symmetry. exact G3.
  - rewrite (EWk 4%nat ltac:(lia)), (EE 4%nat (4%bv : bv 5) ltac:(vm_compute; reflexivity)).
    symmetry. exact G4.
  - rewrite E529. symmetry. exact G19. }
(* ---- the seat at 0x81dac: the shadow region keeps its window [0, 104) and no chunk;
   the spill slots 8 and 72 hold the frame's address as the atom GA_F ---- *)
assert (HCS : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W4) (ms_mem ms4)) (c_sp1 cx))
   [YP09.mkChunk 8 (CVal 8 (SOff GA_F 0)); YP09.mkChunk 72 (CVal 8 (SOff GA_F 0))]).
{ assert (UF : bv_unsigned (ew E GA_F) = gF cx fp)
    by (rewrite E516; unfold w64; apply unsigned_lit_small; lia).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (gl_chunk E (w_H W4) (ms_mem ms4) GA_F (c_sp1 cx) 8 (gF cx fp) UF HFbv).
    exact (HSL4 8 (or_introl eq_refl)).
  - apply (gl_chunk E (w_H W4) (ms_mem ms4) GA_F (c_sp1 cx) 72 (gF cx fp) UF HFbv).
    exact (HSL4 72 (or_intror eq_refl)). }
assert (HSH0 : gshadow cx fp W4 ms4 []) by (intros i Hi; cbn [length] in Hi; lia).
assert (HS : st_ok_pi SEGS VAL E
  (ge_ss cx fp (GP_freeT + 8) (gef_sr 530) []
     [YP09.mkChunk 8 (CVal 8 (SOff GA_F 0)); YP09.mkChunk 72 (CVal 8 (SOff GA_F 0))] [] 0 104 []
     (mkFacts [] [] []))
  (restrict (w_H W4) ms4)).
{ change (restrict (w_H W4) ms4) with
    (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + (GP_freeT + 8))) (mrestrict (w_H W4) (ms_mem ms4)) (seg_rom SEGS)).
  unfold ge_ss, ge_regions.
  apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute; reflexivity.
  - apply Forall_app. split; [|apply Forall_nil].
    unfold ge_regions0.
    apply Forall_cons; [eapply ge_region_saved with (W3 := W4) (ms3 := ms4); eassumption|].
    apply Forall_cons; [eapply ge_region_spill with (W3 := W4) (ms3 := ms4); eassumption|].
    apply Forall_cons; [eapply ge_region_frame with (W3 := W4) (ms3 := ms4);
                        first [eassumption | apply Forall_nil]|].
    apply Forall_cons; [eapply ge_region_shadow with (W3 := W4) (ms3 := ms4);
                        first [eassumption | lia]|].
    eapply ge_region_objs with (W3 := W4) (ms3 := ms4); eassumption.
  - apply ge_pwd_app.
    + eapply ge_disj with (W3 := W4) (ms3 := ms4); eassumption.
    + exact I.
    + unfold ge_regions0, ge_obj_regions. repeat (apply Forall_cons; [exact I|]). apply Forall_nil.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [exact I | split; [exact I | exact I]]. }
(* ---- 0x81dac .. 0x81e94: `li a0,-8`, the 55 stores of 0xf8 through s3 into the frame's
   shadow bytes 4 .. 89, the loads of s5 and a6 from the spill slots 8 and 72, and the
   `j 0x80cd8` to the release block ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
  let r := eval vm_compute in (sym_run_toN_pi (pl_tpi (L := grant_listing)) 64%N GP_leave ssx) in
  lazymatch r with
  | (?ss', ?st) =>
    assert (Hrun : sym_run_toN_pi (pl_tpi (L := grant_listing)) 64%N GP_leave ssx = (ss', st))
      by (vm_compute; reflexivity);
    eapply (RUNTOP W4 64%N GP_leave Ev ssx ss' st ms4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ4s);
    [ clear Hrun | clear Hrun HS HJ4s; intros ms5 mat5 HS HJ5 HF5 HFr5 HG5 ]
  end
end.
{ apply (gef_awr cx fp E _ _ _ _ _ _ _ E60 E516 E529); try lia.
  all: first [ exact ESH | eapply ge_frame_addr_eq; eassumption ]. }
(* ---- the cut at 0x80cd8 ---- *)
prreg HS (16%bv : bv 5) Q16. prreg HS (21%bv : bv 5) Q21. prreg HS (19%bv : bv 5) Q19.
lazymatch type of HS with
| st_ok_pi ?sg ?vl ?Ex (mkSST ?pc ?sr _ (_ :: YP09.mkRegion _ _ _ _ _ ?scs :: _
                                         :: YP09.mkRegion _ _ _ ?wlo ?whi ?cs :: _) None ?G) ?msx =>
  change (st_ok_pi sg vl Ex (ge_ss_c cx fp pc sr scs [] wlo whi cs [] G) msx) in HS
| _ => fail "ge_end_free: the state at 0x80cd8 has an unexpected shape"
end.
assert (HIN5 : garr8 SEGS (mrestrict (w_H W4) (ms_mem ms5)) (c_p cx)
                 (map (fun b : byte => bv_unsigned b) (c_pl cx))).
{ apply (gef_garr8 (w_H (c_W cx)) (w_H W4) (c_mem cx) (ms_mem ms5)); [|exact HPLc].
  intros j Hj. rewrite length_map in Hj.
  destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [unfold c_n in Hn0; lia|].
  pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FF2 & _).
  apply (FF2 (c_p cx) (c_n cx) (Z.of_nat j) Hin0).
  - rewrite Eab4. exact Hin0.
  - unfold req_size. destruct (Z.eqb_spec (c_n cx) 0) as [Heq0|Hne0]; [exfalso; lia|].
    unfold c_n. lia.
  - intros (r & Hin & _). destruct Hin. }
destruct (ge_land_ex B MT LAWS cx fp W4 ms5 ly4 S4 _ (k + 1) HBASE HJ5 HFR4 E _ _ _ _ _ _ _ _ _ HEge HS
            eq_refl eq_refl eq_refl eq_refl eq_refl HIN5) as (sh5 & HBODY5).
apply (HNEXT cx fp (k + 1) (acc + mo_free MT) ly4 S4 W4 ms5 _ HBASE HJ5 HFR4
         (mle_station MT (c_S cx) S3 S4 acc (mo_free MT) MTL HMLE MLE4)).
unfold GI_leave.
split; [exists sh5; exact HBODY5|].
split; [lia|]. split; [unfold GE_NEED; lia|]. split; [exact Eab4|].
split; [etransitivity; [exact Q16 | exact E516]|].
split; [etransitivity; [exact Q21 | exact E516] | etransitivity; [exact Q19 | exact E529]].
Qed.

(* The whole end: the END phase lands in `GI_leave`, from which `ge_leave` reaches the
   entry function's post-condition. *)
Theorem ge_end : ge_from B MT (ge_post B MT) (GI_freeT B MT).
Proof. exact (ge_end_free (ge_post B MT) ge_leave). Qed.

End c.
End b.
End a.
