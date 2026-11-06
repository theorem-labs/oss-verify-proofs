(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryLeave), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v, proofs/cgif/cgif_file_fuzzer/lib/YCbo.v, proofs/cgif/cgif_file_fuzzer/lib/YCbq.v. *)
(* The last slots of the walk of fuzz_grant's entry function LLVMFuzzerTestOneInput on
   the ASan build: 0x818b8 .. 0x8192c, from the cut `GI_leave` to the `ret`.

   0x818b8 writes the end magic 0x45e0360e at F+0 and gives the frame back: the frame
   came from the side stack for frames, so the code fills the slot's 128 shadow bytes
   with 0xf5 through __asan_set_shadow_f5 and stores 0 into the flag byte the slot's last
   word points at (F+1016); the other arm, __asan_set_shadow_00 over 104 bytes, is the
   one a frame on the machine stack would take and is not reached (the `beqz s3` at
   0x818c4 falls through: s3 holds the frame). Then it reads ra and s0..s11 back from
   the machine frame, puts sp back and returns 0. This is the phase that proves the
   entry function's post-condition. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaRun PaShadow PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantACjr ACj1 GrantACja ACbf.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
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
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
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
Hypothesis ASETF : aset_shadow_realizes SEGS B (SIGMA GS___asan_set_shadow_f5) 0xf5.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.

Theorem ge_leave : ge_from B MT (ge_post B MT) (GI_leave B MT).
Proof.
intros cx fp k acc ly3 S3 W3 ms3 md3 HBASE HJ3 Hfrs3 HMLE HINV.
pose proof HBASE as (HPRE & Hp10 & Hp11 & Hpn & HPLc & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & Usp & E32c & HMOK & HTR & HNEED).
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & HpresW & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (PBASE : 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64 /\ BASE mod 4 = 0) by exact pa_B_ok.
assert (PBLO : 0x10000 <= BASE) by apply pa_base_lo.
assert (Hwx : wx_segs_nowrap SEGS) by exact pa_wx.
assert (Hsegs : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd) by exact pa_segs_low.
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HINV as ((shx & HBODY) & Hk & Hacc & Eab3 & R19 & R21 & R22).
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
assert (E19 : ew E 19 = Z_to_bv 64 F)
  by (rewrite (EWlow 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 F)
  by (rewrite (EWlow 21%nat (21%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 SHA)
  by (rewrite (EWlow 22%nat (22%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R22).
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
     [ YP09.mkRegion (Some 19%nat) 0 1024 0 8 [YP09.mkChunk 1016 (CVal 8 (SOff 528 0))];
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
     None (mkFacts [(19%nat, HPTR 5); (32%nat, mkAF SB SB 0); (528%nat, HPTR 0)] [] []))
  (restrict (w_H W3) ms3)).
{ rewrite Ems3. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E19, unsigned_lit_small by lia.
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
    rewrite E19, E8, !unsigned_lit_small by lia.
    split; [split; [left; lia | exact I] | split; [exact I | exact I]].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias].
    split; [|split; [exact I | exact I]].
    cbn [atoms_ok]. split; [|split; [|split; [|exact I]]].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E19, unsigned_lit_small by lia. change (2 ^ 5) with 32.
      split; [lia|]. split; [exact HF32 | lia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, unsigned_lit_small by (unfold SB; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E528, unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia]. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (21%bv : bv 5) (SOff 19 0) HS
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E19, unsigned_lit_small by lia;
          rewrite Z.add_0_r; symmetry; exact R21)) as HS2 end.
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
    (Z_to_bv 64 (BASE + 0x1224)) HJ3) end.
  - left; reflexivity.
  - rewrite Ra0, E22. reflexivity.
  - rewrite Ra1. reflexivity.
  - lia.
  - rewrite EFAly3, ESHA. lia.
  - rewrite EFAly3, ESHA. change (fs_frame_bytes GE_CID / 8) with 128. lia.
  - unfold spZ at 1. rewrite Rsp2, E2, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, <- Zminus_mod_idemp_r, Hsp1al16, Hal16. reflexivity.
  - lia.
  - unfold ESTACK, GE_STK. lia.
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
    | |- region_kept _ _ _ _ (YP09.mkRegion (Some 19%nat) _ _ _ _ _) =>
      eapply (gl_kept E (w_H W3) _ _ 19%nat F);
      [ first [rewrite E19; apply unsigned_lit_small; lia | idtac "B1"; fail]
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
          rewrite (AG 19%nat), (AG 8%nat) by lia;
          rewrite E528, E19, E8, !unsigned_lit_small by lia;
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
  + rewrite (AG 19%nat) in Ha by lia. rewrite E19, unsigned_lit_small in Ha by lia.
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
  split; [unfold GE_EV; lia|].
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
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat F).
- reflexivity.
- rewrite E19. apply unsigned_lit_small. lia.
- cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
  exists GE_CID, fp. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EFAly3. change (fs_frame_bytes GE_CID) with 1024. lia.
- apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
Qed.
End c.
End b.
End a.
