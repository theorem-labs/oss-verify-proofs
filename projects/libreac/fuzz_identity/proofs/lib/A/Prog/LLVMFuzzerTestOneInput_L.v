(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Segment L of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x82090..0x82178, listing offsets
   0x1984..0x1a6c, 58 slots): the three frees of the output buffers (dp, tk, then nm from mf+184), the
   use-after-scope poisoning of the frame's shadow (0x820a8..0x820f4), the frame release (the magic word at
   SF+0 0x82108, __asan_set_shadow_f5 over the frame's 128 shadow bytes 0x82118, the flag byte through the word
   at SF+1016 0x8211c..0x82120), the epilogue and the return with a0 = 0. The machine-stack fallback release
   (0x82128..0x82130, __asan_set_shadow_00) is not reached: s4 = SF >= 4096 decides 0x8210c beqz s4.
   Statement: seg_L of LLVMFuzzerTestOneInput_inv.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YG0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Imported walk files switch lia's division handling off; this file's arithmetic needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk's symbolic state at 0x82090 (listing offset 0x1984) ---------------------------------------
   Atoms: 0..31 the registers there (2 = sp = mf, 8 = s0 = sp0, 9 = s1 = mf, 19 = s3 = shadow_addr SF,
   21 = s5 = tk, 22 = s6 = dp), 32 = SF, 33 = the frame's flag address, 34 = nm, 35..47 = the entry's ra, s0,
   s1, s2 .. s11 (the words the epilogue reloads). Regions: the machine-frame slots mf+24, mf+80, mf+184 (on s1),
   the thirteen saved words below sp0 (on s0), the side-stack frame (its word 0 writable, the flag word at
   1016) and its 128 shadow bytes (writable for the poisoning stores). *)
Definition L_PC0 : Z := 0x1984.
Definition L_rmf : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 34 0))].
Definition L_rsv : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0
  [YP09.mkChunk (-104) (CVal 8 (SOff 47 0)); YP09.mkChunk (-96) (CVal 8 (SOff 46 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 45 0)); YP09.mkChunk (-80) (CVal 8 (SOff 44 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 43 0)); YP09.mkChunk (-64) (CVal 8 (SOff 42 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 41 0)); YP09.mkChunk (-48) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 39 0)); YP09.mkChunk (-32) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 37 0)); YP09.mkChunk (-16) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 35 0))].
Definition L_rfr : YP09.region := YP09.mkRegion (Some 32%nat) 0 1024 0 8 [YP09.mkChunk 1016 (CVal 8 (SOff 33 0))].
Definition L_rsh : YP09.region := YP09.mkRegion (Some 19%nat) 0 128 0 128 [].
(* the flag byte, added after the frees, before the release *)
Definition L_rfl : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition L_mem0 : smem := [L_rmf; L_rsv; L_rfr; L_rsh].
Definition L_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
   (32%nat, HPTR 6); (33%nat, HPTR 0)].
Definition L_ss0 : sstate := mkSS L_PC0 sr_atoms L_mem0 None (mkFacts L_atoms [] []).
Definition L_extra (SF FL nm : Z) (er : bvmap 5 word) : list word :=
  [Z_to_bv 64 SF; Z_to_bv 64 FL; Z_to_bv 64 nm; getr er 1; getr er 8; getr er 9;
   getr er 18; getr er 19; getr er 20; getr er 21; getr er 22; getr er 23; getr er 24; getr er 25; getr er 26;
   getr er 27].
(* The three free sites' return addresses (0x82094, 0x8209c, 0x820a4 + 4), the set_shadow_f5 call's
   (0x82118 + 4), as listing offsets. *)
Definition L_RA1 : Z := 0x198c.
Definition L_RA2 : Z := 0x1994.
Definition L_RA3 : Z := 0x199c.
Definition L_RA4 : Z := 0x1a10.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* ---- a journal step for a callee that writes some of its caller's own bytes and keeps only the stack
   window present (the set_shadow entries' contract states presence of its own window only). The proof is
   YCbq.v ajournal_after_write's, with the presence premise narrowed to the journal's window: that is the
   only place the original uses it. *)
Section w.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation ajournal := (ajournal segs B).
Local Notation sep_blocks := (YCbq.sep_blocks segs B LAWS).
Local Notation sep_block_frame := (YCbq.sep_block_frame segs B LAWS).
Local Notation blk_img := (YCbq.blk_img segs B LAWS).
Local Notation frm_img := (YCbq.frm_img segs B LAWS).
Local Notation frames_bounds := (YCbq.frames_bounds segs B LAWS).
Local Notation sep_frames_pos := (YCbq.sep_frames_pos segs B LAWS).
Local Notation awr_byte_cases := (YCbq.awr_byte_cases segs B LAWS).
Local Notation shadow_addr_bounds := YCbq.shadow_addr_bounds.
Local Notation shadow_range_end := YCbq.shadow_range_end.
Local Notation shadow_mono := YCbq.shadow_mono.
Lemma L_after_write_win : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img segs a)) ->
AR segs B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
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
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (awr_byte_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
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
pose proof (sep_blocks lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
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
- exact (blk_img _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (fs_frame_bytes_nonneg cid) as Hfbn.
assert (Hfa1 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
assert (Hfa2 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) Hfa1) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) Hfa2) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfbn) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (sep_block_frame lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [zlia | zlia].
+ destruct Hr as [Hr | Hr]; [zlia |].
destruct Hd as [Hd | Hd].
* pose proof (shadow_mono _ _ Hd). zlia.
* pose proof (shadow_mono _ _ Hd). zlia.
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
pose proof (YG0p.AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
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

(* __asan_set_shadow_XX over a range of one of the caller's own side-stack frames' shadow, in journal form
   (cgif_rgb_fuzzer lib/YC05.v:206 aj_set_shadow_at, over this unit's journal). *)
Lemma L_set_shadow_at : forall pc v, aset_shadow_realizes segs B pc v ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ AR segs B lyc Sc W mem2 md2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; try eassumption. rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfbn.
assert (Hfa1 : 0 <= frame_addr lyc cid pos < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
assert (Hfa2 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid < kHighMemEnd) by (clear - Hf0 Hfc Hfbn C1 C4; unfold kHighMemEnd in *; lia).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) Hfa1) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) Hfa2) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (L_after_write_win STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => q <= a < q + n) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha Hna).
- intros a Ha Hp. eapply (apresent_transfer segs); [zlia | intros Hi; pose proof (segs_low a Hi); zlia | apply Hfr; zlia | exact Hp].
- exact Hsame.
- intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact HAR2|]. split; [exact Heff | exact Hfr].
Qed.
End w.

(* region_kept from the region's bytes being unchanged and its window present after a call *)
Lemma L_kept_view : forall segs E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H m m2 n b lo hi wlo whi cs Hn Hk Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hk. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.

(* A block of the run's own list is not one of the entry's blocks: the allocator's blocks are pairwise apart. *)
Lemma L_fresh : forall segs B (LAWS : AR_laws segs B) ly S W mem md (x : Z * Z) l0 E0,
AR segs B ly S W mem md -> Permutation (ablocks B ly S) (l0 ++ E0) -> In x l0 -> 0 <= snd x -> ~ In x E0.
Proof.
intros segs B LAWS ly S W mem md x l0 E0 HAR HP Hx Hn HxE.
assert (Hz : ~ zdisjoint (block_rng x) (block_rng x)).
{ destruct x as [p m]. unfold zdisjoint, block_rng. cbn [fst snd] in *. pose proof (req_size_pos m Hn). lia. }
apply in_split in Hx as (h1 & h2 & ->). apply in_split in HxE as (e1 & e2 & ->).
assert (Hin : In x (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
apply in_split in Hin as (a1 & a2 & Ea). rewrite Ea in HP.
replace ((h1 ++ x :: h2) ++ e1 ++ x :: e2) with (h1 ++ x :: (h2 ++ e1 ++ x :: e2)) in HP by (rewrite <- app_assoc; reflexivity).
pose proof (Permutation_app_inv a1 a2 h1 (h2 ++ e1 ++ x :: e2) x HP) as HP2.
assert (Hin2 : In x (a1 ++ a2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP2|]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
apply in_app_or in Hin2 as [Hin2 | Hin2]; apply in_split in Hin2 as (b1 & b2 & ->).
- apply Hz. apply (sep_blocks_pos segs B LAWS ly S W mem md x x b1 b2 a2 HAR). rewrite Ea. rewrite <- app_assoc. reflexivity.
- apply Hz. apply (sep_blocks_pos segs B LAWS ly S W mem md x x a1 b1 b2 HAR). exact Ea.
Qed.

(* The call chain at a call the entry makes from its own frame: s0 = sp0 holds the entry's saved ra and s0, and
   above them is the entry's own chain (its pre-condition's achain), which the journal keeps. The chain is
   empty or the one record of the entry's own frame. *)
Lemma L_chain : forall ly (rd rdE : reader) (regsT : bvmap 5 word) sp0 mf ra s0e lyE,
spZ regsT = mf -> s0Z regsT = sp0 -> 4096 <= raZ regsT ->
alloc_ceiling <= mf -> mf + 16 <= sp0 -> sp0 mod 16 = 0 ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some s0e -> 4096 <= ra ->
achain lyE rdE sp0 s0e [] -> ly_top lyE = ly_top ly -> ly_top ly <= 2 ^ 47 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rdE a) ->
exists ch, chain_pre ly rd regsT ch /\ (ch = [] \/ exists fp v, ch = [(fp, ra, v)]).
Proof.
intros ly rd rdE regsT sp0 mf ra s0e lyE Hsp Hs0 Hra4 Hce Hmf Hal Hrd1 Hrd2 Hra Hach Etop Htop47 Hab.
unfold chain_pre.
destruct (frame0_ok ly regsT) eqn:Ef0.
2: { exists []. split; [split; [exact Hra4 | reflexivity] | left; reflexivity]. }
destruct (bad_next (spZ regsT) (ly_top ly) (s0Z regsT)) eqn:Ebn.
{ exists []. split; [split; [exact Hra4 | reflexivity] | left; reflexivity]. }
exists [(sp0, ra, s0e)]. split; [| right; exists sp0, s0e; reflexivity].
split; [exact Hra4|]. rewrite Hsp, Hs0. split; [lia|].
cbn [fpchain]. split; [reflexivity|].
split; [pose proof (Z.div_mod sp0 16 ltac:(lia)) as D; rewrite Hal, Z.add_0_r in D; rewrite D;
replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by lia; apply Z_mod_mult|].
split; [exact Hrd1|]. split; [exact Hrd2|]. split; [exact Hra|].
destruct (bad_next sp0 (ly_top ly) s0e) eqn:Ebn2; [reflexivity|].
unfold bad_next in Ebn2. apply Bool.orb_false_iff in Ebn2 as [Ebn2 E3]. apply Bool.orb_false_iff in Ebn2 as [E1 E2].
apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply Bool.negb_false_iff in E3. apply Z.eqb_eq in E3.
unfold achain in Hach. destruct Hach as [(Hbad & _) | (Hlo & Hhi & Hal8 & Hfp & _)].
- exfalso. rewrite Etop in Hbad. lia.
- cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hrr). exists r. split; [|exact Hrr].
rewrite <- Hr. apply rdword_ext. intros kk Hkk. apply Hab. rewrite Etop in Hhi. clear - Hlo Hhi Hkk Htop47. lia.
Qed.

Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation EPRE g := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS g).
#[local] Notation MEV := (mo_malloc MT 256 + mo_free MT).
(* What the walk needs of the contract's constants (LLVMFuzzerTestOneInput.v:82-83, :176). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HXN : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XN_LIB n.
(* the image, the allocator, the side stack *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
(* the runtime entries this segment calls *)
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IS___asan_set_shadow_f5) 0xf5.
(* the call traces of the entry's allocator calls: the contract's HUMF (LLVMFuzzerTestOneInput.v), with its text
   (its contexts hold both the depth-2 trace through the entry's frame record and the depth-1 one). *)
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX (PI := PI) RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* identity's relocated ACfh / YE01 lemmas, with the statements LLVMFuzzerTestOneInput.v takes them *)
Hypothesis AJ_FP_NIL : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis ASINK_NONE_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
asink_none SEGS KS (rd W mem) md -> asink_none SEGS KS (rd W' mem') md'.
Hypothesis AMETA_INV_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ameta_inv SEGS KS ly (rd W mem) M -> ameta_inv SEGS KS ly' (rd W' mem') M.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).

Definition L_E (regs2 : bvmap 5 word) (SF FL nm : Z) (er : bvmap 5 word) : env :=
  Eimg (Ereg regs2 (L_extra SF FL nm er)).

(* The frame and flag facts at a boundary of the entry's journal. *)
Lemma L_ffacts : forall g pos lyc Sc W mem md k,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k ->
frames Sc = [(4, pos)] ->
frame_addr lyc 4 pos = SFa g pos /\ flag_addr lyc 4 pos = flag_addr (e_ly g) 4 pos /\
(forall a, SFa g pos <= a < SFa g pos + 1024 -> apresent (w_H W) mem a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr (SFa g pos) + i)) /\
4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
apresent (w_H W) mem (flag_addr (e_ly g) 4 pos) /\ aowned B lyc Sc (flag_addr (e_ly g) 4 pos) /\
4096 <= flag_addr (e_ly g) 4 pos < alloc_ceiling /\
(forall a, SFa g pos <= a < SFa g pos + 1024 -> ~ aowned B lyc Sc a).
Proof.
intros g pos lyc Sc W mem md k HJ Hfrs.
pose proof HJ as (HAR & Hly & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr lyc 4 pos = SFa g pos)
by (unfold SFa, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (EFL : flag_addr lyc 4 pos = flag_addr (e_ly g) 4 pos)
by (unfold flag_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 4 pos HAR Hin) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin) as (_ & _ & HFpres & HFSpres).
destruct (FFL _ _ _ _ _ 4 pos HAR Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLceil)).
rewrite EFA in HF4096, HFceil, HFapp, HF64, HFpres, HFSpres. rewrite EFL in HFLp, HFLo, HFL4096, HFLceil.
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
split; [exact EFA|]. split; [exact EFL|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros i Hi; exact (proj1 (HFSpres i Hi))|].
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFapp|]. split; [exact HF64|].
split; [exact HFLp|]. split; [exact HFLo|]. split; [lia|].
intros a Ha. exact (proj2 (HFpres a Ha)).
Qed.

(* The symbolic state at 0x82090 holds. *)
Lemma L_entry : forall (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (er : bvmap 5 word) sp0 mf SF FL nm,
getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf -> getr regs2 8 = w64 sp0 -> getr regs2 19 = w64 (shadow_addr SF) ->
alloc_ceiling <= mf -> sp0 - 336 <= mf <= sp0 - 320 -> mf mod 32 = 0 -> sp0 mod 16 = 0 -> sp0 <= 2 ^ 47 ->
4096 <= SF -> SF + 1024 <= alloc_ceiling -> SF mod 64 = 0 -> in_app SF 1024 ->
4096 <= FL < alloc_ceiling -> 0 <= nm < 2 ^ 64 ->
(forall a, SF <= a < SF + 1024 -> apresent (w_H W2) mem2 a) ->
(forall i, 0 <= i < 128 -> apresent (w_H W2) mem2 (shadow_addr SF + i)) ->
val_mem SEGS (rd W2 mem2) (mf + 24) 8 SF ->
val_mem SEGS (rd W2 mem2) (mf + 80) 8 SF ->
val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm ->
val_mem SEGS (rd W2 mem2) (SF + 1016) 8 FL ->
val_mem SEGS (rd W2 mem2) (sp0 - 8) 8 (bv_unsigned (getr er 1)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 16) 8 (bv_unsigned (getr er 8)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 24) 8 (bv_unsigned (getr er 9)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 32) 8 (bv_unsigned (getr er 18)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 40) 8 (bv_unsigned (getr er 19)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 48) 8 (bv_unsigned (getr er 20)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 56) 8 (bv_unsigned (getr er 21)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 64) 8 (bv_unsigned (getr er 22)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 72) 8 (bv_unsigned (getr er 23)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 80) 8 (bv_unsigned (getr er 24)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 88) 8 (bv_unsigned (getr er 25)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 96) 8 (bv_unsigned (getr er 26)) ->
val_mem SEGS (rd W2 mem2) (sp0 - 104) 8 (bv_unsigned (getr er 27)) ->
st_ok_pi SEGS VAL (L_E regs2 SF FL nm er) L_ss0 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + L_PC0)) mem2 (seg_rom SEGS))).
Proof.
intros W2 regs2 mem2 er sp0 mf SF FL nm R2 R9 R8 R19 Hce Hmf Hmf32 Hsp16 Hsp47 HF4096 HFce HF64 HFapp HFL Hnm
HFp HFSp V24 V80 V184 Vfl V1 V8 V9 V18 V19 V20 V21 V22 V23 V24' V25 V26 V27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := L_E regs2 SF FL nm er).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (L_extra SF FL nm er)) n)
by (intros n Hn; subst E; unfold L_E; apply Eimg_low; exact Hn).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn Hr; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j (L_extra SF FL nm er) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (U2 : bv_unsigned (ew E 2) = mf)
by (rewrite (ER 2%nat 2%bv ltac:(lia) eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = mf)
by (rewrite (ER 9%nat 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = sp0)
by (rewrite (ER 8%nat 8%bv ltac:(lia) eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (HSA : shadow_addr SF = SHADOW_OFF + SF / 8) by reflexivity.
assert (U19 : bv_unsigned (ew E 19) = shadow_addr SF)
by (rewrite (ER 19%nat 19%bv ltac:(lia) eq_refl), R19; unfold w64; apply unsigned_lit_small;
    rewrite HSA; unfold SHADOW_OFF; pose proof (Z.div_le_mono SF (2 ^ 47) 8 ltac:(lia) ltac:(lia)); lia).
assert (E32 : ew E 32 = Z_to_bv 64 SF) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 nm) by exact (EX 2%nat ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = SF) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
assert (VB : forall n v, bv_unsigned (ew E n) = v -> base_val E (Some n) = v) by (intros n v Hv; exact Hv).
assert (CK : forall base off (j : nat) (w : word), (j < 16)%nat -> nth j (L_extra SF FL nm er) (Z_to_bv 64 0) = w ->
  val_mem SEGS (rd W2 mem2) (base + off) 8 (bv_unsigned w) ->
  YP09.chunk_ok SEGS E (rd W2 mem2) base (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros base off j w Hj Hw Hv. apply (chunk_ok_val SEGS E _ base off 8 (SOff (32 + j) 0) (bv_unsigned w)).
  - cbn [sv_denot]. rewrite (EX j Hj), Hw, Z.add_0_r. rewrite ?Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hr.
  - cbn. lia.
  - exact Hv. }
unfold L_ss0. apply pa_entry_st_ok_full.
- subst E. unfold L_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold L_mem0, L_rmf, L_rsv, L_rfr, L_rsh.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat mf U9). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (CK mf 24 0%nat (Z_to_bv 64 SF) ltac:(lia) eq_refl). rewrite unsigned_lit_small by lia. exact V24.
    * apply (CK mf 80 0%nat (Z_to_bv 64 SF) ltac:(lia) eq_refl). rewrite unsigned_lit_small by lia. exact V80.
    * apply (CK mf 184 2%nat (Z_to_bv 64 nm) ltac:(lia) eq_refl). rewrite unsigned_lit_small by lia. exact V184.
  + rewrite (VB 8%nat sp0 U8). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (CK sp0 (-104) 15%nat (getr er 27) ltac:(lia) eq_refl). replace (sp0 + -104) with (sp0 - 104) by lia. exact V27.
    * apply (CK sp0 (-96) 14%nat (getr er 26) ltac:(lia) eq_refl). replace (sp0 + -96) with (sp0 - 96) by lia. exact V26.
    * apply (CK sp0 (-88) 13%nat (getr er 25) ltac:(lia) eq_refl). replace (sp0 + -88) with (sp0 - 88) by lia. exact V25.
    * apply (CK sp0 (-80) 12%nat (getr er 24) ltac:(lia) eq_refl). replace (sp0 + -80) with (sp0 - 80) by lia. exact V24'.
    * apply (CK sp0 (-72) 11%nat (getr er 23) ltac:(lia) eq_refl). replace (sp0 + -72) with (sp0 - 72) by lia. exact V23.
    * apply (CK sp0 (-64) 10%nat (getr er 22) ltac:(lia) eq_refl). replace (sp0 + -64) with (sp0 - 64) by lia. exact V22.
    * apply (CK sp0 (-56) 9%nat (getr er 21) ltac:(lia) eq_refl). replace (sp0 + -56) with (sp0 - 56) by lia. exact V21.
    * apply (CK sp0 (-48) 8%nat (getr er 20) ltac:(lia) eq_refl). replace (sp0 + -48) with (sp0 - 48) by lia. exact V20.
    * apply (CK sp0 (-40) 7%nat (getr er 19) ltac:(lia) eq_refl). replace (sp0 + -40) with (sp0 - 40) by lia. exact V19.
    * apply (CK sp0 (-32) 6%nat (getr er 18) ltac:(lia) eq_refl). replace (sp0 + -32) with (sp0 - 32) by lia. exact V18.
    * apply (CK sp0 (-24) 5%nat (getr er 9) ltac:(lia) eq_refl). replace (sp0 + -24) with (sp0 - 24) by lia. exact V9.
    * apply (CK sp0 (-16) 4%nat (getr er 8) ltac:(lia) eq_refl). replace (sp0 + -16) with (sp0 - 16) by lia. exact V8.
    * apply (CK sp0 (-8) 3%nat (getr er 1) ltac:(lia) eq_refl). replace (sp0 + -8) with (sp0 - 8) by lia. exact V1.
  + rewrite (VB 32%nat SF U32). split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HFp; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (CK SF 1016 1%nat (Z_to_bv 64 FL) ltac:(lia) eq_refl). rewrite unsigned_lit_small by lia. exact Vfl.
  + rewrite (VB 19%nat (shadow_addr SF) U19).
    assert (HSr : 0 <= shadow_addr SF /\ shadow_addr SF + 128 <= 2 ^ 64)
    by (rewrite HSA; unfold SHADOW_OFF; pose proof (Z.div_le_mono SF (2 ^ 47) 8 ltac:(lia) ltac:(lia));
        pose proof (Z.div_pos SF 8 ltac:(lia) ltac:(lia)); lia).
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HFSp; lia | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold L_mem0, L_rmf, L_rsv, L_rfr, L_rsh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat mf U9), (VB 8%nat sp0 U8), (VB 32%nat SF U32), (VB 19%nat (shadow_addr SF) U19).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite HSA. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  pose proof (Z.div_le_mono SF (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod SF 8 ltac:(lia)). pose proof (Z.mod_pos_bound SF 8 ltac:(lia)).
  revert Hce Hmf Hsp47 HF4096 HFce HFapp C1 C3 H H0 H1. clear. intros.
  repeat split; lia.
- split; [|split; exact I].
  unfold L_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U8, U32, U33.
  try change (2 ^ 5) with 32. try change (2 ^ 4) with 16. try change (2 ^ 6) with 64. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  revert Hce Hmf Hmf32 Hsp16 Hsp47 HF4096 HFce HF64 HFL C1. clear. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* One free of an output buffer from the entry's frame: afree04_rule with the chain, the trace and the meter
   derived from the entry's pre-condition and the journal. *)
Lemma L_free_at : forall g pos mf W (regsT : bvmap 5 word) memT mdc lyc Sc k pa n hs0 hs1 retk
(Q : world SEGS -> config -> Prop),
EPRE g ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k ->
frames Sc = [(4, pos)] ->
Permutation (ablocks B lyc Sc) (hs0 ++ (pa, n) :: hs1 ++ ablocks B (e_ly g) (e_S g)) -> 0 <= n ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
val_mem SEGS (rd W memT) (e_sp0 g - 8) 8 RA_LLVMF ->
val_mem SEGS (rd W memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
getr regsT 10 = w64 pa -> getr regsT 2 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = Z_to_bv 64 (BASE + retk) -> In retk [0x198c; 0x1994; 0x199c] -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
0 <= k -> k + 1 <= EV_LLVMF ->
mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
(forall W3 ly3 S3 regs3 mem3 md3, wle W W3 ->
 ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 W3 mem3 md3 (k + 1) ->
 aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
 Permutation (ablocks B ly3 S3) (hs0 ++ hs1 ++ ablocks B (e_ly g) (e_S g)) ->
 acall_kept SEGS B lyc Sc W memT W3 mem3 (mf - ASTACK) mf (fun a => pa <= a < pa + req_size n) ->
 mo_le MT (e_S g) S3 ((k + 1) * MEV) -> mo_ok MT S3 ((EV_LLVMF - (k + 1)) * MEV) ->
 SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k pa n hs0 hs1 retk Q HPRE HJ Hfrs HPerm Hn Hmf Hmf32 Vra Vs0
Ha0 Rsp Rs0 Rgp Rtp Rra Hras Hretk Hreven Hk0 Hk1 HMLE HMOK Hk.
pose proof HPRE as (HAFN & Hra & _ & _ & _ & _ & _ & _ & Hnev0 & _).
destruct HAFN as (HAR0 & Hret0 & Hra40 & _ & _ & _ & _ & Hach & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (Hsp16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & HtopS).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
unfold e_sp0 in *.
set (sp0 := spZ (e_regs g)) in *.
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hceil Hslo HSTKv H47 C1 Hshi; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (Hs0t : s0Z regsT = sp0) by (unfold s0Z; rewrite Rs0; unfold w64, sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
assert (HRA : RA_LLVMF = raZ (e_regs g)) by (symmetry; exact Hra).
assert (HRAr : 0 <= RA_LLVMF < 2 ^ 64) by (rewrite HRA; unfold raZ; apply (bv_unsigned_in_range 64)).
assert (Hs0r : 0 <= s0Z (e_regs g) < 2 ^ 64) by (unfold s0Z; apply (bv_unsigned_in_range 64)).
destruct (L_chain lyc (aview SEGS (w_H W) memT) (aview SEGS (w_H (e_W g)) (e_mem g)) regsT sp0 mf RA_LLVMF
  (s0Z (e_regs g)) (e_ly g) Hspt Hs0t ltac:(rewrite Hrat; clear - HBLO Hretk; lia)
  ltac:(clear - Hmf Hceil Hslo HSTKv; lia) ltac:(clear - Hmf; lia) Hsp16
  (rdword_of_val_mem SEGS (w_H W) memT _ _ Vra HRAr) (rdword_of_val_mem SEGS (w_H W) memT _ _ Vs0 Hs0r)
  ltac:(rewrite HRA; exact Hra40) Hach
  ltac:(destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); symmetry; exact Etop)
  ltac:(destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); rewrite Etop; clear - HtopS H47; lia)
  (aview_above_of_journal B LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k HJ))
  as (ch & Hch & Hsh).
assert (Hin : In (pa, n) (ablocks B lyc Sc))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | apply in_or_app; right; left; reflexivity]).
assert (Hnin : ~ In (pa, n) (ablocks B (e_ly g) (e_S g))).
{ intros Hin0. refine (L_fresh SEGS B LAWS lyc Sc W memT mdc (pa, n) (hs0 ++ [(pa, n)]) (hs1 ++ ablocks B (e_ly g) (e_S g)) HAR _ _ Hn _).
  - rewrite <- app_assoc. exact HPerm.
  - apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. exact Hin0. }
assert (Hmfree : 0 <= mo_free MT) by exact (mo_free_nonneg MT MTL).
assert (Hmmal : 0 <= mo_malloc MT 256) by exact (mo_malloc_nonneg MT MTL 256 ltac:(lia)).
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W regsT memT LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g)
    (e_mem g) (e_md g) [(4, pos)] lyc Sc mdc k pa n (mf - sp0) (Z_to_bv 64 (BASE + retk)) ch HJ Hin).
  - exact Ha0.
  - rewrite Hspt. ring.
  - pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - sp0) with ((2 * (mf / 32) - sp0 / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
  - clear - Hmf; lia.
  - unfold ASTACK. clear - Hmf HSTKv; lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - clear - Hnev Hnev0 Hk1 HEV; unfold EV_LLVMF in *; lia.
  - exact Hch.
  - destruct Hsh as [-> | (fp & v & ->)].
    + eapply llvmf_univ_call0; [exact HUMF|]. rewrite Hrat. unfold LLVMF_FREE_CTX, LLVMF_FREE_RAS.
      apply in_or_app. right. apply (in_map (fun o => [BASE + o])). clear - Hras. cbn [In] in *. tauto.
    + eapply llvmf_univ_call; [exact HUMF|]. rewrite Hrat. unfold LLVMF_FREE_CTX, LLVMF_FREE_RAS.
      apply in_or_app. left. apply (in_map (fun o => [BASE + o; RA_LLVMF])). clear - Hras. cbn [In] in *. tauto.
  - intros Hin0. exfalso. exact (Hnin Hin0).
  - apply (mo_ok_le MT MTL Sc (mo_free MT) ((EV_LLVMF - k) * MEV) HMOK).
    assert (X : (EV_LLVMF - k) * MEV = MEV + (EV_LLVMF - (k + 1)) * MEV) by ring.
    assert (Y : 0 <= (EV_LLVMF - (k + 1)) * MEV) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite X. clear - Y Hmmal. lia. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & E1 & E2) & Hfr3 & HK3 & HMLE3 & _).
apply (Hk W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3).
- rewrite Hfr3. exact Hfrs.
- rewrite E2. apply (Permutation_app_inv l1 l2 hs0 (hs1 ++ ablocks B (e_ly g) (e_S g)) (pa, n)). rewrite <- E1. exact HPerm.
- replace (sp0 + (mf - sp0) - ASTACK) with (mf - ASTACK) in HK3 by ring.
  replace (sp0 + (mf - sp0)) with mf in HK3 by ring. exact HK3.
- apply (mo_le_mono MT MTL _ _ (k * MEV + mo_free MT)); [exact (mo_le_trans MT MTL _ _ _ _ _ HMLE HMLE3)|].
  assert (X : (k + 1) * MEV = k * MEV + MEV) by ring. rewrite X. clear - Hmmal. lia.
- assert (X : (EV_LLVMF - k) * MEV = mo_free MT + ((EV_LLVMF - k) * MEV - mo_free MT)) by ring.
  rewrite X in HMOK.
  pose proof (mo_ok_step MT MTL Sc S3 (mo_free MT) ((EV_LLVMF - k) * MEV - mo_free MT) HMOK HMLE3) as HM3.
  apply (mo_ok_le MT MTL S3 _ _ HM3).
  assert (X2 : (EV_LLVMF - k) * MEV = MEV + (EV_LLVMF - (k + 1)) * MEV) by ring.
  rewrite X2. clear - Hmmal. lia.
Qed.

(* The contract's post-condition at the return, from the journal of the whole run. *)
Lemma L_fin : forall g (W : world SEGS) lyF SF' (regsF : bvmap 5 word) memF mdF kF,
EPRE g ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [] lyF SF' W memF mdF kF ->
kF <= EV_LLVMF ->
Permutation (ablocks B lyF SF') (ablocks B (e_ly g) (e_S g)) ->
mo_le MT (e_S g) SF' (kF * MEV) ->
aregs_preserved (e_regs g) regsF -> getr regsF 10 = w64 0 ->
tLLVMFuzzerTestOneInput_post B MT XN_LIB LLVMF_STK EV_LIB asink_syms_T KS asink_none ameta_inv
(e_regs g) (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) (e_M g) (LL 0 (m_fs (e_md g)) [])
lyF SF' W regsF memF mdF kF.
Proof.
intros g W lyF SF' regsF memF mdF kF HPRE HJ HkF HPerm HMLE HP Ha0.
pose proof HPRE as (_ & _ & _ & _ & Hplace & _ & _ & _ & _ & _ & _ & Hsink0 & _ & Hsorted & Hmeta0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & Hk0 & _ & F2 & _).
assert (Hmfree : 0 <= mo_free MT) by exact (mo_free_nonneg MT MTL).
assert (Hmmal : 0 <= mo_malloc MT 256) by exact (mo_malloc_nonneg MT MTL 256 ltac:(lia)).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Efd & Efs).
unfold tLLVMFuzzerTestOneInput_post.
split; [apply AJ_FP_NIL; exact HJ|].
split; [clear - HkF HEV; lia|].
split; [exact HP|]. split; [exact Ha0|]. split; [exact HPerm|].
split; [intros fd; rewrite Efd; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
split; [exact (ASINK_NONE_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ sink_closed_nil Hsink0)|].
split; [exact (AMETA_INV_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hmeta0)|].
split.
{ apply (mo_le_mono MT MTL _ _ _ _ HMLE). pose proof (HXN (e_n g)) as HX.
  assert (Y : kF * MEV <= EV_LLVMF * MEV) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
intros i Hi. destruct Hplace as [[Hn0 _] | [_ Hin]]; [lia|].
apply (F2 (e_p g) (e_n g) i Hin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hin].
- pose proof (req_size_pos (e_n g) ltac:(lia)). lia.
- intros (r & Hr & _). exact Hr.
Qed.

(* ---- the lemmas the walk's steps share ---------------------------------------------------------------- *)
Lemma L_shb : forall SF, 4096 <= SF -> SF + 1024 <= alloc_ceiling ->
2147450880 <= shadow_addr SF /\ shadow_addr SF + 128 <= 17594332446720.
Proof.
intros SF H1 H2. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_le_mono SF (140737479966720 - 1024) 8 ltac:(lia) ltac:(lia)) as H.
pose proof (Z.div_pos SF 8 ltac:(lia) ltac:(lia)) as H0.
change ((140737479966720 - 1024) / 8) with 17592184995712 in H. lia.
Qed.

(* The writable windows of the walk's regions are the frame's word 0 and its shadow: the frame is the run's own. *)
Lemma L_awr : forall (E : env) rs STK sp0 FP bl0 blc lyc pos SF,
frame_addr lyc 4 pos = SF -> bv_unsigned (ew E 32) = SF -> bv_unsigned (ew E 19) = shadow_addr SF ->
(forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
  (YP09.r_base r = Some 32%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 1024) \/
  (YP09.r_base r = Some 19%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 128)) ->
awr_ok E rs STK sp0 FP bl0 blc lyc [(4, pos)].
Proof.
intros E rs STK sp0 FP bl0 blc lyc pos SF EFA U32 U19 Hrs a (r & Hr & Ha).
destruct (Hrs r Hr) as [Hw | [(Hb & H1 & H2) | (Hb & H1 & H2)]].
- exfalso. lia.
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite U32 in Ha.
  right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 4) with 1024. lia.
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite U19 in Ha.
  right. right. right. exists 4, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 4 / 8) with 128. lia.
Qed.

(* The same at the release: the frame's word 0 or the flag byte. *)
Lemma L_awrF : forall (E : env) rs STK sp0 FP bl0 blc lyc pos SF FLv,
frame_addr lyc 4 pos = SF -> flag_addr lyc 4 pos = FLv -> bv_unsigned (ew E 32) = SF -> bv_unsigned (ew E 33) = FLv ->
(forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
  (YP09.r_base r = Some 32%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 1024) \/
  (YP09.r_base r = Some 33%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 1)) ->
forall a, in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc lyc [(4, pos)] a \/ a = flag_addr lyc 4 pos.
Proof.
intros E rs STK sp0 FP bl0 blc lyc pos SF FLv EFA EFL U32 U33 Hrs a (r & Hr & Ha).
destruct (Hrs r Hr) as [Hw | [(Hb & H1 & H2) | (Hb & H1 & H2)]].
- exfalso. lia.
- left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite U32 in Ha.
  right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 4) with 1024. lia.
- right. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite U33 in Ha. rewrite EFL. lia.
Qed.

(* The entry's saved ra and s0, read off the saved-words region at a call. *)
Lemma L_sv : forall (E : env) ss ms (er : bvmap 5 word) sp0,
st_ok SEGS E ss ms -> nth_error (ss_mem ss) 1 = Some L_rsv ->
bv_unsigned (ew E 8) = sp0 -> ew E 35 = getr er 1 -> ew E 36 = getr er 8 ->
val_mem SEGS (ms_mem ms) (sp0 - 8) 8 (bv_unsigned (getr er 1)) /\
val_mem SEGS (ms_mem ms) (sp0 - 16) 8 (bv_unsigned (getr er 8)).
Proof.
intros E ss ms er sp0 HS Hn U8 E35 E36.
pose proof (st_ok_region_nth E ss ms 1 L_rsv HS Hn) as HR. unfold L_rsv in HR.
split.
- pose proof (field_of_region E (ms_mem ms) 8 sp0 _ (-104) 0 0 0 (-8) 8%N (SOff 35 0) (bv_unsigned (getr er 1)) HR U8
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r; rewrite ?Z_to_bv_bv_unsigned; reflexivity)
    ltac:(pose proof (bv_unsigned_in_range 64 (getr er 1)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr)
    ltac:(cbn; lia)) as V.
  replace (sp0 + -8) with (sp0 - 8) in V by lia. exact V.
- pose proof (field_of_region E (ms_mem ms) 8 sp0 _ (-104) 0 0 0 (-16) 8%N (SOff 36 0) (bv_unsigned (getr er 8)) HR U8
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r; rewrite ?Z_to_bv_bv_unsigned; reflexivity)
    ltac:(pose proof (bv_unsigned_in_range 64 (getr er 8)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr)
    ltac:(cbn; lia)) as V.
  replace (sp0 + -16) with (sp0 - 16) in V by lia. exact V.
Qed.

(* After a free: the machine-frame slots and the saved words are above the callee's window, the frame and its
   shadow are the run's own and apart from the freed block. *)
Lemma L_kept_free : forall (E : env) (W W3 : world SEGS) memT mem3 lyc Sc mdc ly3 S3 md3 k k3 g pos mf pa n
cs1 cs2 cs3 cs4,
bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 8) = e_sp0 g -> bv_unsigned (ew E 32) = SFa g pos ->
bv_unsigned (ew E 19) = shadow_addr (SFa g pos) ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k ->
frames Sc = [(4, pos)] -> In (pa, n) (ablocks B lyc Sc) ->
acall_kept SEGS B lyc Sc W memT W3 mem3 (mf - ASTACK) mf (fun a => pa <= a < pa + req_size n) ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 W3 mem3 md3 k3 ->
frames S3 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
Forall (region_kept SEGS E (mrestrict (w_H W) memT) (mrestrict (w_H W3) mem3))
 [YP09.mkRegion (Some 9%nat) 0 192 0 0 cs1; YP09.mkRegion (Some 8%nat) (-104) 0 0 0 cs2;
  YP09.mkRegion (Some 32%nat) 0 1024 0 8 cs3; YP09.mkRegion (Some 19%nat) 0 128 0 128 cs4].
Proof.
intros E W W3 memT mem3 lyc Sc mdc ly3 S3 md3 k k3 g pos mf pa n cs1 cs2 cs3 cs4 U9 U8 U32 U19 HJ Hfrs Hin HK HJ3
Hfrs3 Hmf.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (_ & _ & Hceil & Hslo & _).
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
destruct (L_ffacts g pos lyc Sc W memT mdc k HJ Hfrs) as (EFA & _ & _ & _ & HF4096 & HFce & _ & _).
destruct (L_ffacts g pos ly3 S3 W3 mem3 md3 k3 HJ3 Hfrs3) as (_ & _ & HFp3 & HFSp3 & _).
assert (Hin2 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memT mdc pa n 4 pos HAR Hin Hin2) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 4) with 1024 in Hd.
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc pa n HAR Hin) as (_ & _ & _ & Happ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
destruct (L_shb (SFa g pos) HF4096 HFce) as (HS1 & HS2).
repeat apply Forall_cons; try apply Forall_nil.
- eapply region_kept_stack_aj; [exact HK | exact HJ3 | exact U9 | lia | lia | lia | lia | lia].
- eapply region_kept_stack_aj; [exact HK | exact HJ3 | exact U8 | lia | lia | lia | lia | lia].
- eapply region_kept_ownframe_aj; [exact HK | exact U32 | exact Hin2 | | | ].
  + left. rewrite EFA. change (fs_frame_bytes 4) with 1024. lia.
  + intros a Ha Hn. lia.
  + intros a Ha. apply HFp3. lia.
- eapply region_kept_ownframe_aj; [exact HK | exact U19 | exact Hin2 | | | ].
  + right. rewrite EFA. change (fs_frame_bytes 4 / 8) with 128. lia.
  + intros a Ha Hn. lia.
  + intros a Ha. replace a with (shadow_addr (SFa g pos) + (a - shadow_addr (SFa g pos))) by lia. apply HFSp3. lia.
Qed.

(* After __asan_set_shadow_f5 over the frame's shadow: the kept regions are outside the shadow it wrote. *)
Lemma L_kept_ss : forall (E : env) (W : world SEGS) memT mem2 lyc Sc mdc md2 k g pos mf cs1 cs2 cs3,
bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 8) = e_sp0 g -> bv_unsigned (ew E 32) = SFa g pos ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem2 md2 k ->
frames Sc = [(4, pos)] ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
Forall (region_kept SEGS E (mrestrict (w_H W) memT) (mrestrict (w_H W) mem2))
 [YP09.mkRegion (Some 9%nat) 0 192 0 0 cs1; YP09.mkRegion (Some 8%nat) (-104) 0 0 0 cs2;
  YP09.mkRegion (Some 32%nat) 0 1024 0 8 cs3].
Proof.
intros E W memT mem2 lyc Sc mdc md2 k g pos mf cs1 cs2 cs3 U9 U8 U32 HJ HJ2 Hfrs Hfr Hmf.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
destruct (L_ffacts g pos lyc Sc W mem2 md2 k HJ2 Hfrs) as (_ & _ & HFp2 & _ & HF4096 & HFce & HFapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct (L_shb (SFa g pos) HF4096 HFce) as (HS1 & HS2).
pose proof asan_consts as (C1 & _).
repeat apply Forall_cons; try apply Forall_nil.
- apply (L_kept_view SEGS E (w_H W) memT mem2 9 mf 0 192 0 0 cs1 U9).
  + intros a Ha. apply Hfr; lia.
  + intros a Ha. lia.
- apply (L_kept_view SEGS E (w_H W) memT mem2 8 (e_sp0 g) (-104) 0 0 0 cs2 U8).
  + intros a Ha. apply Hfr; lia.
  + intros a Ha. lia.
- apply (L_kept_view SEGS E (w_H W) memT mem2 32 (SFa g pos) 0 1024 0 8 cs3 U32).
  + intros a Ha. apply Hfr; lia.
  + intros a Ha. apply HFp2. lia.
Qed.

(* The flag byte as a region, added after the frees: it is present, and it is the allocator's, so apart from the
   frame (whose bytes are not the allocator's) and from the machine stack. *)
Lemma L_add_flag : forall (E : env) ss (W : world SEGS) (regs6 : bvmap 5 word) pc mem6 g pos mf lyc Sc md6 k
cs1 cs2 cs3,
st_ok_pi SEGS VAL E ss (restrict (w_H W) (mkst regs6 pc mem6 (seg_rom SEGS))) ->
ss_mem ss = [YP09.mkRegion (Some 9%nat) 0 192 0 0 cs1; YP09.mkRegion (Some 8%nat) (-104) 0 0 0 cs2;
  YP09.mkRegion (Some 32%nat) 0 1024 0 8 cs3] ->
bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 8) = e_sp0 g -> bv_unsigned (ew E 32) = SFa g pos ->
bv_unsigned (ew E 33) = flag_addr (e_ly g) 4 pos ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem6 md6 k ->
frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (L_rfl :: ss_mem ss) (ss_resv ss) (ss_facts ss))
  (restrict (w_H W) (mkst regs6 pc mem6 (seg_rom SEGS))).
Proof.
intros E ss W regs6 pc mem6 g pos mf lyc Sc md6 k cs1 cs2 cs3 HS Hm U9 U8 U32 U33 HJ Hfrs Hmf.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
destruct (L_ffacts g pos lyc Sc W mem6 md6 k HJ Hfrs) as (_ & _ & _ & _ & HF4096 & HFce & _ & _ & HFLp & HFLo & HFL & HnoF).
apply st_ok_pi_add_region; [exact HS | reflexivity | |].
- unfold region_ok, L_rfl. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U33. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. cbn [ms_mem restrict mkst]. apply (apresent_writable SEGS).
  replace (flag_addr (e_ly g) 4 pos + o) with (flag_addr (e_ly g) 4 pos) by lia. exact HFLp.
- rewrite Hm. apply all_disjoint_of_extents. unfold L_rfl, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U8, U32, U33.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  split; [lia|]. split; [lia|]. split; [|exact I].
  destruct (Z_lt_ge_dec (flag_addr (e_ly g) 4 pos) (SFa g pos)); [left; lia|].
  destruct (Z_lt_ge_dec (flag_addr (e_ly g) 4 pos) (SFa g pos + 1024)); [|right; lia].
  exfalso. apply (HnoF (flag_addr (e_ly g) 4 pos)); [lia | exact HFLo].
Qed.

(* After the release's run, the flag byte holds 0: it is the region the store wrote. *)
Lemma L_flag0 : forall (E : env) ss' FLv cs,
nth_error (ss_mem ss') 0 = Some (YP09.mkRegion (Some 33%nat) 0 1 0 1 cs) ->
In (YP09.mkChunk 0 (CVal 1 (SLit 0))) cs -> bv_unsigned (ew E 33) = FLv ->
forall msr, st_ok_pi SEGS VAL E ss' msr -> mbyte SEGS (ms_mem msr) FLv = Some (Z_to_bv 8 0).
Proof.
intros E ss' FLv cs Hn Hc U33 msr HSr.
pose proof (st_ok_pi_region_nth E ss' msr 0 _ HSr Hn) as HR.
pose proof (field_of_region E (ms_mem msr) 33 FLv cs 0 1 0 1 0 1%N (SLit 0) 0 HR U33 Hc eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as V.
specialize (V 0%nat ltac:(lia)). cbn [Z.of_nat] in V. rewrite !Z.add_0_r in V. rewrite V. reflexivity.
Qed.

(* The walk's tactics: the writable windows of a run are the run's own frame (Lawr), and the image is unchanged
   for a havocked environment (Lenvh). *)
Local Ltac Lawr EFAx :=
  eapply (L_awr _ _ _ _ _ _ _ _ _ _ EFAx);
  [ rewrite ?ew_havoc_old by (clear; lia); assumption
  | rewrite ?ew_havoc_old by (clear; lia); assumption
  | let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; vm_compute in Hr;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
      first [ left; lia | right; left; repeat split; first [reflexivity | lia]
            | right; right; repeat split; first [reflexivity | lia] ] |]);
    contradiction ].
Local Ltac Lenvh :=
  lazymatch goal with HSx : st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ |- _ =>
    let H := fresh "HEI" in
    assert (H : img_env VAL A_LIM (havoc Eo kk ws)) by (apply img_env_havoc; [assumption | apply Nat.leb_le; reflexivity]) end.

Theorem seg_L_holds : seg_L B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold seg_L, inv_K_end, acut.
intros g pos mf nm tk dp W2 c2 HK.
destruct HK as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & HMLE & HMOK & HC & HP).
destruct HP as ((HPerm & HFh) & H22 & H21 & Vnm).
unfold ecommon in HC.
destruct HC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & R19 & V80 & _ & _ & Vra & Vs0 & Vs1 & Vs2 & Vs3 & Vs4 &
  Vs5 & Vs6 & Vs7 & Vs8 & Vs9 & Vs10 & Vs11 & V24 & Vfl & HPRE & _ & _ & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
destruct HPRE' as (HAFN & Hra & _).
destruct HAFN as (_ & Hret0 & _ & Hgp0 & Htp0 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (Hsp16 & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (L_ffacts g pos ly2 S2 W2 mem2 md2 _ HJ Hfrs)
  as (EFA2 & EFL2 & HFp2 & HFSp2 & HF4096 & HFce & HFapp & HF64 & _ & _ & HFL & _).
assert (Vra' : val_mem SEGS (rd W2 mem2) (e_sp0 g - 8) 8 (bv_unsigned (getr (e_regs g) 1))).
{ change (bv_unsigned (getr (e_regs g) 1)) with (raZ (e_regs g)). rewrite Hra. exact Vra. }
change (s0Z (e_regs g)) with (bv_unsigned (getr (e_regs g) 8)) in Vs0.
assert (Hmfc : alloc_ceiling <= mf) by (clear - Hmf Hceil Hslo HSTKv; lia).
assert (Hsp47 : e_sp0 g <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (Hnmr : 0 <= nm < 2 ^ 64).
{ assert (Hin : In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | cbn [app In]; left; reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin) as (_ & H4096 & Hce & _).
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(lia)) as Hrq. clear - H4096 Hce Hrq C1. lia. }
pose proof (L_entry W2 regs2 mem2 (e_regs g) (e_sp0 g) mf (SFa g pos) (flag_addr (e_ly g) 4 pos) nm R2 R9 R8 R19
  Hmfc Hmf Hmf32 Hsp16 Hsp47 HF4096 HFce HF64 HFapp HFL Hnmr HFp2 HFSp2 V24 V80 Vnm Vfl Vra' Vs0
  Vs1 Vs2 Vs3 Vs4 Vs5 Vs6 Vs7 Vs8 Vs9 Vs10 Vs11) as HS.
remember (L_E regs2 (SFa g pos) (flag_addr (e_ly g) 4 pos) nm (e_regs g)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold L_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (L_extra (SFa g pos) (flag_addr (e_ly g) 4 pos) nm (e_regs g))) n)
  by (intros n Hn; rewrite HE; unfold L_E; apply Eimg_low; exact Hn).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j (L_extra (SFa g pos) (flag_addr (e_ly g) 4 pos) nm (e_regs g)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE EL.
assert (E2 : ew E 2 = w64 mf) by (rewrite (ER 2%nat 2%bv ltac:(lia) eq_refl); exact R2).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (ER 3%nat 3%bv ltac:(lia) eq_refl); exact R3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (ER 4%nat 4%bv ltac:(lia) eq_refl); exact R4).
assert (E8 : ew E 8 = w64 (e_sp0 g)) by (rewrite (ER 8%nat 8%bv ltac:(lia) eq_refl); exact R8).
assert (E9 : ew E 9 = w64 mf) by (rewrite (ER 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
assert (E19 : ew E 19 = w64 (shadow_addr (SFa g pos))) by (rewrite (ER 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
assert (E21 : ew E 21 = w64 tk) by (rewrite (ER 21%nat 21%bv ltac:(lia) eq_refl); exact H21).
assert (E22 : ew E 22 = w64 dp) by (rewrite (ER 22%nat 22%bv ltac:(lia) eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (flag_addr (e_ly g) 4 pos)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = w64 nm) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr (e_regs g) 1) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = getr (e_regs g) 8) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = getr (e_regs g) 9) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = getr (e_regs g) 18) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = getr (e_regs g) 19) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = getr (e_regs g) 20) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = getr (e_regs g) 21) by exact (EX 9%nat ltac:(lia)).
assert (E42 : ew E 42 = getr (e_regs g) 22) by exact (EX 10%nat ltac:(lia)).
assert (E43 : ew E 43 = getr (e_regs g) 23) by exact (EX 11%nat ltac:(lia)).
assert (E44 : ew E 44 = getr (e_regs g) 24) by exact (EX 12%nat ltac:(lia)).
assert (E45 : ew E 45 = getr (e_regs g) 25) by exact (EX 13%nat ltac:(lia)).
assert (E46 : ew E 46 = getr (e_regs g) 26) by exact (EX 14%nat ltac:(lia)).
assert (E47 : ew E 47 = getr (e_regs g) 27) by exact (EX 15%nat ltac:(lia)).
clear ER EX.
assert (U8 : bv_unsigned (ew E 8) = e_sp0 g) by (rewrite E8; unfold w64; apply unsigned_lit_small; clear - Hsp47 Hmf Hmfc C1; lia).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; unfold w64; apply unsigned_lit_small; clear - Hsp47 Hmf Hmfc C1; lia).
assert (U32 : bv_unsigned (ew E 32) = SFa g pos) by (rewrite E32; apply unsigned_lit_small; clear - HF4096 HFce C1; lia).
assert (U33 : bv_unsigned (ew E 33) = flag_addr (e_ly g) 4 pos) by (rewrite E33; apply unsigned_lit_small; clear - HFL C1; lia).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr (SFa g pos)).
{ rewrite E19; unfold w64; apply unsigned_lit_small. destruct (L_shb (SFa g pos) HF4096 HFce). clear - H H0. lia. }
assert (Hk1 : 0 <= 4 * Z.of_nat (m_nrec g) + 7 /\ 4 * Z.of_nat (m_nrec g) + 7 + 3 <= EV_LLVMF)
  by (clear - Hk; unfold EV_LLVMF in *; lia).
clear Vra Vra' Vs0 Vs1 Vs2 Vs3 Vs4 Vs5 Vs6 Vs7 Vs8 Vs9 Vs10 Vs11 V24 V80 Vnm Vfl HFp2 HFSp2 R2 R3 R4 R8 R9 R19 H21 H22.
unfold cfg_at. change (w64 (BASE + 0x1984)) with (Z_to_bv 64 (BASE + L_PC0)).
(* 1. 0x82090 mv a0,s6; free(dp) *)
paj_run_shc RUNP RUNC HS HJ.
{ Lawr EFA2. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
destruct (L_sv E _ _ (e_regs g) (e_sp0 g) HS eq_refl U8 E35 E36) as (Vra1 & Vs01).
cbn [ms_mem restrict] in Vra1, Vs01. unfold raZ in Hra. rewrite Hra in Vra1.
change (bv_unsigned (getr (e_regs g) 8)) with (s0Z (e_regs g)) in Vs01.
assert (Hin1 : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | cbn [app In]; right; right; left; reflexivity]).
pmkst HS. ppcs.
eapply (L_free_at g pos mf W2 _ _ _ ly2 S2 _ dp _ [_; _] [] L_RA1 _ HPRE HJ Hfrs HPerm).
1: (clear; lia). 1: exact Hmf. 1: exact Hmf32. 1: exact Vra1. 1: exact Vs01.
1: rewrite Ra0; exact E22. 1: rewrite Rsp; exact E2. 1: rewrite Rs0; exact E8.
1: rewrite Rgp; exact E3. 1: rewrite Rtp; exact E4. 1: exact Rra.
1: (unfold L_RA1; cbn [In]; left; reflexivity).
1: (unfold L_RA1; clear; lia). 1: reflexivity. 1: (clear - Hk1; lia). 1: (clear - Hk1; lia). 1: exact HMLE. 1: exact HMOK.
intros W3 ly3 S3 regs3 mem3 md3 Hwle3 HJ3 HP3 Hfrs3 HPerm3 HK3 HMLE3 HMOK3.
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3]%nat HS2.
lazymatch type of HS2 with ?Qk -> _ => assert (HQ : Qk) end.
{ cbn [ms_mem restrict]. eapply L_kept_free; [exact U9 | exact U8 | exact U32 | exact U19 | exact HJ | exact Hfrs
  | exact Hin1 | exact HK3 | exact HJ3 | exact Hfrs3 | exact Hmf]. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS Ra0 Rra Rsp Rgp Rtp Rs0. rename HS2 into HS.
Lenvh.
destruct (L_ffacts g pos ly3 S3 W3 mem3 md3 _ HJ3 Hfrs3) as (EFA3 & _).
(* 2. 0x82098 mv a0,s5; free(tk) *)
paj_run_shc RUNP RUNC HS HJ3.
{ Lawr EFA3. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
destruct (L_sv _ _ _ (e_regs g) (e_sp0 g) HS eq_refl
  ltac:(rewrite ?ew_havoc_old by (clear; lia); exact U8) ltac:(rewrite ?ew_havoc_old by (clear; lia); exact E35)
  ltac:(rewrite ?ew_havoc_old by (clear; lia); exact E36)) as (Vra2 & Vs02).
cbn [ms_mem restrict] in Vra2, Vs02. rewrite Hra in Vra2.
change (bv_unsigned (getr (e_regs g) 8)) with (s0Z (e_regs g)) in Vs02.
assert (Hin3 : In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | cbn [app In]; right; left; reflexivity]).
pmkst HS. ppcs.
eapply (L_free_at g pos mf W3 _ _ _ ly3 S3 _ tk _ [_] [] L_RA2 _ HPRE HJ3 Hfrs3 HPerm3).
1: (clear; lia). 1: exact Hmf. 1: exact Hmf32. 1: exact Vra2. 1: exact Vs02.
1: rewrite Ra0; exact E21. 1: rewrite Rsp; exact E2. 1: rewrite Rs0; exact E8.
1: rewrite Rgp; exact E3. 1: rewrite Rtp; exact E4. 1: exact Rra.
1: (unfold L_RA2; cbn [In]; right; left; reflexivity).
1: (unfold L_RA2; clear; lia). 1: reflexivity. 1: (clear - Hk1; lia). 1: (clear - Hk1; lia). 1: exact HMLE3. 1: exact HMOK3.
intros W4 ly4 S4 regs4 mem4 md4 Hwle4 HJ4 HP4 Hfrs4 HPerm4 HK4 HMLE4 HMOK4.
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3]%nat HS2.
lazymatch type of HS2 with ?Qk -> _ => assert (HQ : Qk) end.
{ cbn [ms_mem restrict]. eapply L_kept_free;
  [ rewrite ?ew_havoc_old by (clear; lia); exact U9 | rewrite ?ew_havoc_old by (clear; lia); exact U8
  | rewrite ?ew_havoc_old by (clear; lia); exact U32 | rewrite ?ew_havoc_old by (clear; lia); exact U19
  | exact HJ3 | exact Hfrs3 | exact Hin3 | exact HK4 | exact HJ4 | exact Hfrs4 | exact Hmf ]. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS Ra0 Rra Rsp Rgp Rtp Rs0. rename HS2 into HS.
Lenvh.
destruct (L_ffacts g pos ly4 S4 W4 mem4 md4 _ HJ4 Hfrs4) as (EFA4 & _).
(* 3. 0x820a0 ld a0,184(s1); free(nm) *)
paj_run_shc RUNP RUNC HS HJ4.
{ Lawr EFA4. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
destruct (L_sv _ _ _ (e_regs g) (e_sp0 g) HS eq_refl
  ltac:(rewrite ?ew_havoc_old by (clear; lia); exact U8) ltac:(rewrite ?ew_havoc_old by (clear; lia); exact E35)
  ltac:(rewrite ?ew_havoc_old by (clear; lia); exact E36)) as (Vra3 & Vs03).
cbn [ms_mem restrict] in Vra3, Vs03. rewrite Hra in Vra3.
change (bv_unsigned (getr (e_regs g) 8)) with (s0Z (e_regs g)) in Vs03.
assert (Hin4 : In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly4 S4))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | cbn [app In]; left; reflexivity]).
pmkst HS. ppcs.
eapply (L_free_at g pos mf W4 _ _ _ ly4 S4 _ nm _ [] [] L_RA3 _ HPRE HJ4 Hfrs4 HPerm4).
1: (clear; lia). 1: exact Hmf. 1: exact Hmf32. 1: exact Vra3. 1: exact Vs03.
1: rewrite Ra0; exact E34. 1: rewrite Rsp; exact E2. 1: rewrite Rs0; exact E8.
1: rewrite Rgp; exact E3. 1: rewrite Rtp; exact E4. 1: exact Rra.
1: (unfold L_RA3; cbn [In]; right; right; left; reflexivity).
1: (unfold L_RA3; clear; lia). 1: reflexivity. 1: (clear - Hk1; lia). 1: (clear - Hk1; lia). 1: exact HMLE4. 1: exact HMOK4.
intros W5 ly5 S5 regs5 mem5 md5 Hwle5 HJ5 HP5 Hfrs5 HPerm5 HK5 HMLE5 HMOK5.
jafter_call_keep_pi HS 80%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0; 1; 2; 3]%nat HS2.
lazymatch type of HS2 with ?Qk -> _ => assert (HQ : Qk) end.
{ cbn [ms_mem restrict]. eapply L_kept_free;
  [ rewrite ?ew_havoc_old by (clear; lia); exact U9 | rewrite ?ew_havoc_old by (clear; lia); exact U8
  | rewrite ?ew_havoc_old by (clear; lia); exact U32 | rewrite ?ew_havoc_old by (clear; lia); exact U19
  | exact HJ4 | exact Hfrs4 | exact Hin4 | exact HK5 | exact HJ5 | exact Hfrs5 | exact Hmf ]. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS Ra0 Rra Rsp Rgp Rtp Rs0. rename HS2 into HS.
Lenvh.
destruct (L_ffacts g pos ly5 S5 W5 mem5 md5 _ HJ5 Hfrs5) as (EFA5 & EFL5 & _).
(* 4. 0x820a8..0x82114: the poisoning stores, the frame's magic word, s4 = SF (beqz decided), the arguments of
   __asan_set_shadow_f5 *)
paj_run_shc RUNP RUNC HS HJ5.
{ Lawr EFA5. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
eapply SRr_bind.
{ eapply (L_set_shadow_at SEGS B LAWS pa_segs_low (SIGMA IS___asan_set_shadow_f5) 0xf5 ASSF5 W5 _ _
    LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly5 S5 _ _ 4 pos
    (shadow_addr (SFa g pos)) 128 (mf - e_sp0 g) (Z_to_bv 64 (BASE + L_RA4)) HJ5).
  - left. reflexivity.
  - rewrite Ra0. exact E19.
  - rewrite Ra1. reflexivity.
  - clear. lia.
  - rewrite EFA5. clear. lia.
  - rewrite EFA5. change (fs_frame_bytes 4 / 8) with 128. clear. lia.
  - unfold spZ. rewrite Rsp, E2. unfold w64. rewrite unsigned_lit_small by (clear - Hsp47 Hmf Hmfc C1; lia). ring.
  - pose proof (Z.div_mod mf 32 ltac:(clear; lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(clear; lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
  - clear - Hmf. lia.
  - unfold ESTACK. clear - Hmf HSTKv. lia.
  - rewrite Rgp. exact E3.
  - rewrite Rtp. exact E4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [unfold L_RA4; lia | reflexivity]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & HAR6 & Hset & Hfr6).
jafter_call_keep_pi HS 96%nat regs6 (mrestrict (w_H W5) mem6) HP6 [0; 1; 2]%nat HS2.
lazymatch type of HS2 with ?Qk -> _ => assert (HQ : Qk) end.
{ cbn [ms_mem restrict]. eapply L_kept_ss;
  [ rewrite ?ew_havoc_old by (clear; lia); exact U9 | rewrite ?ew_havoc_old by (clear; lia); exact U8
  | rewrite ?ew_havoc_old by (clear; lia); exact U32 | exact HJ5 | exact HJ6 | exact Hfrs5 | exact Hfr6 | exact Hmf ]. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS Ra0 Ra1 Rra Rsp Rgp Rtp. rename HS2 into HS.
Lenvh.
pose proof (L_add_flag _ _ W5 regs6 _ mem6 g pos mf ly5 S5 md6 _ _ _ _ HS eq_refl
  ltac:(rewrite ?ew_havoc_old by (clear; lia); exact U9) ltac:(rewrite ?ew_havoc_old by (clear; lia); exact U8)
  ltac:(rewrite ?ew_havoc_old by (clear; lia); exact U32) ltac:(rewrite ?ew_havoc_old by (clear; lia); exact U33)
  HJ6 Hfrs5 Hmf) as HS3.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* 5. 0x8211c..0x82174: the flag byte cleared (the frame's release), a0 = 0, the epilogue, ret *)
paj_run_flag_sh RUNF HS HJ6.
{ clear. lia. }
{ eapply (L_awrF _ _ _ _ _ _ _ _ _ _ _ EFA5 EFL5);
  [ rewrite ?ew_havoc_old by (clear; lia); assumption
  | rewrite ?ew_havoc_old by (clear; lia); assumption
  | let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; vm_compute in Hr;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
      first [ left; lia | right; left; repeat split; first [reflexivity | lia]
            | right; right; repeat split; first [reflexivity | lia] ] |]);
    contradiction ]. }
{ rewrite EFL5. eapply L_flag0; [reflexivity | cbn [In]; left; reflexivity |].
  rewrite ?ew_havoc_old by (clear; lia). exact U33. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msF) |- _ =>
  prreg HSx (1%bv : bv 5) F1; prreg HSx (2%bv : bv 5) F2; prreg HSx (3%bv : bv 5) F3; prreg HSx (4%bv : bv 5) F4;
  prreg HSx (8%bv : bv 5) F8; prreg HSx (9%bv : bv 5) F9; prreg HSx (10%bv : bv 5) F10;
  prreg HSx (18%bv : bv 5) F18; prreg HSx (19%bv : bv 5) F19; prreg HSx (20%bv : bv 5) F20;
  prreg HSx (21%bv : bv 5) F21; prreg HSx (22%bv : bv 5) F22; prreg HSx (23%bv : bv 5) F23;
  prreg HSx (24%bv : bv 5) F24; prreg HSx (25%bv : bv 5) F25; prreg HSx (26%bv : bv 5) F26;
  prreg HSx (27%bv : bv 5) F27;
  eapply (RET W5 _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity))
end.
intros mat'.
unfold inv_ret. cbv beta.
lazymatch goal with
| HJx : ajournal _ _ _ _ _ _ _ _ _ _ [] _ _ _ ?memF _ _ |- context [mkCfg (mkst ?rgF ?pcF _ _) ?mdG] =>
  assert (Hpc : pcF = w64 RA_LLVMF);
  [ rewrite F1, E35; unfold YK0s.ret_ok in Hret0; rewrite Hret0; unfold w64; rewrite <- Hra; try unfold raZ;
    rewrite Z_to_bv_bv_unsigned; reflexivity |];
  exists ly5, (stack_free_state 4 pos S5), rgF, memF, mdG, (4 * Z.of_nat (m_nrec g) + 7 + 1 + 1 + 1);
  split; [unfold cfg_at; rewrite Hpc; reflexivity|];
  apply L_fin; [exact HPRE | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJx | clear - Hk1; lia | | | | ]
end.
- unfold ablocks in *. rewrite blocks_stack_free_state. exact HPerm5.
- unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). exact HMLE5.
- apply aregs_preserved_eqs.
  + rewrite F2, E8. unfold w64, e_sp0, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite F3, E3. symmetry. exact Hgp0.
  + rewrite F4, E4. symmetry. exact Htp0.
  + rewrite F8. exact E36.
  + rewrite F9. exact E37.
  + rewrite F18. exact E38.
  + rewrite F19. exact E39.
  + rewrite F20. exact E40.
  + rewrite F21. exact E41.
  + rewrite F22. exact E42.
  + rewrite F23. exact E43.
  + rewrite F24. exact E44.
  + rewrite F25. exact E45.
  + rewrite F26. exact E46.
  + rewrite F27. exact E47.
- rewrite F10. reflexivity.
Qed.

End c.
End b.
End a.
