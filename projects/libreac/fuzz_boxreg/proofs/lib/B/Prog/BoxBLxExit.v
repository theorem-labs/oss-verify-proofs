(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 447 of its 579 lines of code are new or changed and 2830 lines of the source are left out. *)
(* The exit phase of the B walk of LLVMFuzzerTestOneInput (fuzz_boxreg.asan-ubsan), from the cut LI_X at 0x80e54
   (BoxBLxDefs.v): free (r) at 0x80e58 (afree04_rule through YC85.v afree04_sub: (r, 288) is the registry block that
   lblk adds to the caller's blocks, not one of the caller's, so the rule's footprint premise is vacuous); the frame's
   retired magic at F (0x80e6c), `beqz a4` not taken (F >= 4096), __asan_set_shadow_f5 (s6 = lSH, 64) at 0x80e80 over
   the frame's 64 shadow bytes; the flag store `sb zero, 0(a0)` at 0x80e88 with a0 = the slot's flag address from
   F + 0x1f8, which releases the frame (BoxBFrame.v aj_flag_store_pi); a0 = 0, the epilogue (ra, s0 .. s11 from the
   machine frame, sp = s0) and `ret`. The post is BoxBLxDefs.v lx_post. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The shadow-token run's parameters (BoxBReacBoxregInit.v CBR / BspanR): the shadow base is atom LA_SB. *)
Definition XBx : sv := SOff 32 0.
Definition XSB : Z := 0x7fff8000.
Definition XBspan : Z * Z := (XSB, XSB + 2 ^ 44 - 1).
(* The flag cell, added before the flag store (frame_flag_lawP: present, allocator-owned, below the stack). *)
Definition XFLAG : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

Lemma lx_layout_addrs : forall n ly ly' cid pos, layout_le n ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos /\
  ly_top ly' = ly_top ly.
Proof.
  intros n ly ly' cid pos Hle.
  pose proof Hle as (_ & _ & _ & _ & _ & HF & _ & _ & Htop & _).
  unfold frame_addr, flag_addr. rewrite HF, Htop. auto.
Qed.

Lemma lx_achain_ly : forall ly ly' rd sp v ch, ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch Ht H. unfold achain in *. rewrite Ht. exact H. Qed.

Lemma lx_perm_drop : forall (L0 l1 l2 : list (Z * Z)) x, L0 ++ [x] = l1 ++ x :: l2 -> Permutation (l1 ++ l2) L0.
Proof.
  intros L0 l1 l2 x E. apply (Permutation_cons_inv (a := x)).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- E.
  apply Permutation_sym. apply Permutation_cons_append.
Qed.

Section w.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* lib/Reusable/YCbq.v ajournal_after_write (Anthropic's copyright line, Apache-2.0 OR MIT; its proof copied, the
   section lemmas it calls qualified) with its presence premise only off the image (the set_shadow contract keeps the
   view, so presence transfers only where no read-only byte can stand in for a missing one): the premise is used
   only on the stack window, which lies above the image. *)
Lemma lx_after_write_win : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
(aowned B lyc Sc a /\ app_addr a /\ ~ in_img SEGS a)) ->
AR SEGS B lyc S' Wc memc' mdc' ->
ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc -> frames S' = own2 ++ frames S ->
qtight S' ->
ajournal SEGS B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
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
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img SEGS a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx]; [left; exact (YCbq.awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply YCbq.aos_step_same_io; [exact Hio | apply YCbq.same_io_materialized, Hsame]|].
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
pose proof (YCbq.sep_blocks SEGS B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (YCbq.sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
- zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(zlia)) Hxo). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (pa_segs_low a Hi) as Hal'.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- zlia.
- exact (YCbq.blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (YCbq.frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (YCbq.frames_bounds SEGS B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh). pose proof (fs_frame_bytes_nonneg cid) as Hnn0.
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(pose proof (fs_frame_bytes_nonneg cid); zlia)) as Hsb2.
pose proof (YCbq.shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
apply Heqw; [zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- zlia.
- destruct Hr as [Hr | Hr]; [|zlia].
pose proof (YCbq.sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (YCbq.sep_frames_pos SEGS B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (YCbq.frames_bounds SEGS B LAWS lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (YCbq.shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
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
split; [intros a Ha; apply Hgr; [zlia | intros Him; pose proof (pa_segs_low a Him); zlia | apply Hpres, Ha]|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (YG0p.AR_extra_law_ok SEGS B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
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

(* cgif_rgb_fuzzer YC05.v aj_set_shadow_at (a working branch): the shadow-fill entry over a frame the caller owns,
   composed with the caller's journal. The entry writes only the n shadow bytes at q (inside the frame's shadow),
   so the journal stays (lx_after_write_win), its state and its count unchanged. *)
Lemma lx_set_shadow_at : forall pc v, aset_shadow_realizes SEGS B pc v ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (cid, pos) own ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
  shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
  intros pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
    HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
  assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
  { eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
    rewrite Hra. exact Hraw. }
  assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  eapply SRr_mono; [exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2)|].
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (YCbq.frames_bounds SEGS B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
  pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
  pose proof (YCbq.shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  assert (Hni : forall a, q <= a < q + n -> ~ in_img SEGS a).
  { intros a Ha Hi. pose proof (pa_segs_low a Hi). zlia. }
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split.
  { eapply (lx_after_write_win STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
             (fun a => q <= a < q + n) Sc own HJ).
    - intros a Ha Hna. apply (Hfr a Ha Hna).
    - intros a Ha Hni' Hp.
      destruct (Z_le_gt_dec q a) as [Hqa|Hqa]; [destruct (Z_lt_ge_dec a (q + n)) as [Han|Han]|].
      + specialize (Heff (a - q) ltac:(lia)). replace (q + (a - q)) with a in Heff by lia.
        destruct Hp as [Hh _]. split; [exact Hh|]. unfold aview, mbyte, mrestrict in Heff. rewrite Hh in Heff.
        destruct (mem2 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso.
        rewrite (seg_rom_none SEGS a Ha Hni') in Heff. discriminate.
      + eapply (apresent_transfer SEGS); [exact Ha | exact Hni' | apply Hfr; [exact Ha | lia] | exact Hp].
      + eapply (apresent_transfer SEGS); [exact Ha | exact Hni' | apply Hfr; [exact Ha | lia] | exact Hp].
    - exact Hsame.
    - intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|].
      right. unfold in_zr. cbn [fst snd]. lia.
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP | exact Hfr].
Qed.

(* The registry block is not one of the caller's: the cut's blocks are the caller's with (r, 288) added once
   (AR's separation of distinct positions). *)
Lemma lx_r_fresh : forall (cx : lxcx) ly3 S3 W3 mem3 md3 r,
  AR SEGS B ly3 S3 W3 mem3 md3 -> lblk B cx ly3 S3 r -> ~ In (r, LX_REG) (ablocks B (lc_ly cx) (lc_S cx)).
Proof.
  intros cx ly3 S3 W3 mem3 md3 r HAR Hb Hin. apply in_split in Hin as (l1 & l2 & E1).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (r, LX_REG) (r, LX_REG) l1 l2 [] HAR) as Hd.
  unfold lblk in Hb. rewrite Hb, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size LX_REG) with 288 in Hd. lia.
Qed.

End w.

Section x.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

(* The exit's symbolic state at LP_X: the seat with the spill slots 0x10 / 0x18 (both F), the whole frame writable
   (fwlo = 0, fwhi = 512: 0x80e6c stores the retired magic at F) with no chunk but the flag word, the frame's shadow
   as the cut has it (read-only), no extra region, and LX_AF's facts. *)
Definition XSL : list (Z * sv) := [(0x10, SOff LA_F 0); (0x18, SOff LA_F 0)].
Definition xs_ss : sstate :=
  lx_ss LP_X (lx_sr LX_OV) LSH_entry (lx_slot_chunks XSL) [] 0 512 0 0 [] (mkFacts LX_AF [] []).


Lemma lx_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
  destruct Ha as [x ->]. destruct Hb as [y ->]. apply Z.mod_divide; [lia|]. exists (2 * x - y). lia.
Qed.

Lemma lx_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros a Ha. apply Z.mod_divide in Ha; [|lia]. destruct Ha as [x ->].
  apply Z.mod_divide; [lia|]. exists (2 * x). lia.
Qed.

(* A word a region's 8-byte chunk fixes, read back through any symbolic state over the restricted memory. *)
Lemma xs_word : forall E ss (H : word -> bool) ms i nb b lo hi wlo whi cs off e v,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
  bv_unsigned (ew E nb) = b -> In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> rdword (aview SEGS H (ms_mem ms)) (b + off) = Some v.
Proof.
  intros E ss H ms i nb b lo hi wlo whi cs off e v HS Hi Hb Hc He Hv.
  apply (rdword_of_val_mem SEGS H (ms_mem ms)); [|exact Hv].
  pose proof (st_ok_region_nth E ss (restrict H ms) i _ HS Hi) as HR.
  exact (field_of_region E _ nb b cs lo hi wlo whi off 8%N e v HR Hb Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Ltac xs_ew := rewrite ?ew_havoc_old by lia.
Ltac xs_ewH H := rewrite ?ew_havoc_old in H by lia.

(* The write windows of the exit's state: the spill slots (in the stack window below sp0), the frame (owned). *)
Ltac xs_awr cx fp EFA UB2 UB46 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) _ _ _ _ _ _ _ _ 2%nat (lsp1 cx - lsp0 cx));
    [reflexivity | xs_ew; rewrite UB2; lia | cbn; lia | cbn; lia |]
  | eapply (awr_ok_cons_gen _ (YP09.mkRegion (Some 46%nat) _ _ _ _ _) _ _ _ _ _ _ _ _ 46%nat (lF cx fp));
    [reflexivity | xs_ew; exact UB46
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists LX_CID, fp; split; [left; reflexivity|];
      left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes LX_CID) with 512; lia
    |] ].

Definition XSH : list shent := [mkSHE LA_F 512 0].

(* The frame's write window is the only one the shadow span cannot be told apart from by the facts: its reversed
   shadow entry (BoxBLxSeat.v lx_shent_rev) covers it. *)
Lemma xs_shok : forall (cx : lxcx) fp E m, ew E LA_SB = w64 SHADOW_OFF -> ew E LA_F = w64 (lF cx fp) ->
  in_app (lF cx fp) 512 -> 0 <= lF cx fp < 2 ^ 64 -> sh_ok SEGS XBx XSH E m.
Proof.
  intros cx fp E m H32 H46 Hia Hr. unfold sh_ok, XSH. apply Forall_cons; [|apply Forall_nil].
  eapply lx_shent_rev; [| | exact Hia | lia].
  - apply (U_atom E 32 SHADOW_OFF H32). unfold SHADOW_OFF. lia.
  - apply (U_atom E 46 (lF cx fp) H46). exact Hr.
Qed.

Lemma lx_exit_walk : forall (cx : lxcx) fp k acc ly3 S3 W3 ms3 md3 r E,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  k <= 129 -> acc <= LX_A1 MT + 64 * LX_AI MT -> lblk B cx ly3 S3 r ->
  img_env VAL A_LIM E -> lx_E cx fp E -> ew E 20 = w64 r ->
  st_ok_pi SEGS VAL E xs_ss (restrict (w_H W3) ms3) ->
  SRr SEGS W3 (mkCfg ms3 md3) (lx_post B MT cx).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 r E HB HJ HFR MLE Hk Hacc Hblk HEI HE E20 HS.
  pose proof (lh_laws _ _ HY) as LAWS. pose proof (lh_tl _ _ HY) as TL.
  pose proof (lh_mtl _ _ HY) as MTL. pose proof (lh_mtfl _ _ HY) as MTFL.
  pose proof (lh_ml _ _ HY) as ML. pose proof (lh_asf _ _ HY) as ASF. pose proof (lh_ffl _ _ HY) as FFL.
  pose proof (lh_free _ _ HY) as AFREE. pose proof (lh_setsh_f5 _ _ HY) as ASETSH.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
  pose proof HB as (HPRE & _ & _ & Hpn & _ & Hfr0 & Hev & Hlive & _ & MOK & HNEED & HTR).
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HFal & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFA3.
  pose proof (lx_flag_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFL3.
  assert (Hfin3 : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof HJ as (HAR3 & Hly3 & _).
  pose proof (lx_layout_addrs _ _ _ LX_CID fp Hly3) as (_ & _ & ETOP3).
  pose proof (pa_B_ok (L := boxb_listing)) as (HB0 & HB1 & HB4).
  pose proof (pa_base_lo (L := boxb_listing)) as HBlo.
  assert (Hrin3 : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite Hblk; apply in_or_app; right; left; reflexivity).
  pose proof (lx_r_fresh B LAWS cx ly3 S3 W3 (ms_mem ms3) md3 r HAR3 Hblk) as Hrnot.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin3) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ r LX_REG LX_CID fp HAR3 Hrin3 Hfin3) as HdRF.
  unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (req_size LX_REG) with 288 in HdRF.
  rewrite EFA3 in HdRF. change (fs_frame_bytes LX_CID) with 512 in HdRF.
  assert (WS : LX_STK = 32768) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (SHOK : sh_ok SEGS XBx XSH E (mrestrict (w_H W3) (ms_mem ms3))) by (apply (xs_shok cx fp); [exact E32 | exact E46 | exact HFapp | lia]).
  pose (RUN := paj_run B LAWS).
  assert (ESP0 : lsp0 cx = spZ (lc_regs cx)) by reflexivity.
  assert (E2' : ew E 2 = w64 (lsp1 cx)) by exact E2.
  assert (E8' : ew E 8 = w64 (lsp0 cx)) by exact E8.
  assert (E22' : ew E 22 = w64 (lSH cx fp)) by exact E22.
  assert (E32' : ew E 32 = w64 SHADOW_OFF) by exact E32.
  assert (E46' : ew E 46 = w64 (lF cx fp)) by exact E46.
  assert (E47' : ew E 47 = w64 (lFL cx fp)) by exact E47.
  assert (E33 : ew E 33 = getr (lc_regs cx) 1) by exact (ESAV 0%nat ltac:(lia)).
  assert (E34 : ew E 34 = getr (lc_regs cx) 8) by exact (ESAV 1%nat ltac:(lia)).
  assert (E35 : ew E 35 = getr (lc_regs cx) 9) by exact (ESAV 2%nat ltac:(lia)).
  assert (E36 : ew E 36 = getr (lc_regs cx) 18) by exact (ESAV 3%nat ltac:(lia)).
  assert (E37 : ew E 37 = getr (lc_regs cx) 19) by exact (ESAV 4%nat ltac:(lia)).
  assert (E38 : ew E 38 = getr (lc_regs cx) 20) by exact (ESAV 5%nat ltac:(lia)).
  assert (E39 : ew E 39 = getr (lc_regs cx) 21) by exact (ESAV 6%nat ltac:(lia)).
  assert (E40 : ew E 40 = getr (lc_regs cx) 22) by exact (ESAV 7%nat ltac:(lia)).
  assert (E41 : ew E 41 = getr (lc_regs cx) 23) by exact (ESAV 8%nat ltac:(lia)).
  assert (E42 : ew E 42 = getr (lc_regs cx) 24) by exact (ESAV 9%nat ltac:(lia)).
  assert (E43 : ew E 43 = getr (lc_regs cx) 25) by exact (ESAV 10%nat ltac:(lia)).
  assert (E44 : ew E 44 = getr (lc_regs cx) 26) by exact (ESAV 11%nat ltac:(lia)).
  assert (E45 : ew E 45 = getr (lc_regs cx) 27) by exact (ESAV 12%nat ltac:(lia)).
  assert (UB2 : bv_unsigned (ew E 2) = lsp0 cx + (lsp1 cx - lsp0 cx))
    by (rewrite E2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (UB8 : bv_unsigned (ew E 8) = lsp0 cx) by (rewrite E8'; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (UB46 : bv_unsigned (ew E 46) = lF cx fp) by (rewrite E46'; unfold w64; rewrite unsigned_lit_small by lia; lia).
  (* 0x80e54 mv a0, s4; 0x80e58 jal free *)
  paj_run_tok RUN HS HJ SHOK XBspan; [xs_awr cx fp EFA3 UB2 UB46 |].
  pmkst HS. rewrite (pal_free B TL).
  prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
  assert (Qsp : spZ (ms_regs ms) = lsp1 cx) by (unfold spZ; rewrite Rsp, E2'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  assert (QRA8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (lsp0 cx - 8) = Some (raZ (lc_regs cx))).
  { replace (lsp0 cx - 8) with (lsp0 cx + -8) by lia.
    eapply (xs_word E _ (w_H W3) ms 0 8%nat); [exact HS | reflexivity | exact UB8 | cbn; tauto | | apply u64_range].
    rewrite lx_sv_SOff0, E33. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (QS016 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (lsp0 cx - 16) = Some (s0Z (lc_regs cx))).
  { replace (lsp0 cx - 16) with (lsp0 cx + -16) by lia.
    eapply (xs_word E _ (w_H W3) ms 0 8%nat); [exact HS | reflexivity | exact UB8 | cbn; tauto | | apply u64_range].
    rewrite lx_sv_SOff0, E34. unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
  eapply SRr_bind.
  { eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE W3 (ms_regs ms) (ms_mem ms) LX_STK (lsp0 cx) []
      (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k r LX_REG
      (lsp1 cx - lsp0 cx) (Z_to_bv 64 (BASE + 3760)) (lch cx) HJ).
    - exact Hrin3.
    - rewrite Ra0. exact E20.
    - rewrite Qsp. lia.
    - exact (lx_mod16 _ _ Hsp1al Hsp0al).
    - lia.
    - rewrite Has, WS. lia.
    - rewrite Rgp, E3. exact Hgp.
    - rewrite Rtp, E4. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _). unfold LX_EV in Hev. lia.
    - apply (achain_chain_pre ly3 _ (lsp1 cx) (lsp0 cx)).
      + apply (lx_achain_ly (lc_ly cx)); [exact ETOP3|].
        apply (lx_achain cx _ (lsp1 cx)); [exact Hch | lia | lia | rewrite ESP0; exact (lx_mod8 _ Hal16) | exact Hra4
          | intros a Ha; eapply aview_above_of_journal; [exact HJ | exact Ha] | exact QRA8 | exact QS016 | lia].
      + rewrite Qsp. lia.
      + unfold s0Z. rewrite Rs0, E8'. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + unfold raZ. rewrite Rra, unsigned_lit_small by lia. lia.
    - apply HTR. right. split; [reflexivity|]. unfold raZ. rewrite Rra, unsigned_lit_small by lia.
      replace (BASE + 3760 - BASE) with 3760 by lia. unfold LX_FSITES. right; right; left; reflexivity.
    - intros Hin. exfalso. exact (Hrnot Hin).
    - apply (mok_station MT (lc_S cx) S3 (lc_T cx) acc (mo_free MT) MTL MOK MLE (mo_free_nonneg MT MTL)).
      unfold LX_NEED in HNEED. lia. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl1 & Ebl2) & Hfrs2 & HK2 & MLE2 & HJsub).
  pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  rewrite HFR in Hfrs2.
  assert (Hfin2 : In (LX_CID, fp) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof (lx_layout_addrs _ _ _ LX_CID fp Hly2) as (EFA2 & EFL2 & ETOP2).
  change (frame_addr (lc_ly cx) LX_CID fp) with (lF cx fp) in EFA2.
  change (flag_addr (lc_ly cx) LX_CID fp) with (lFL cx fp) in EFL2.
  destruct (al_frames _ _ LAWS _ _ _ _ _ LX_CID fp HAR2 Hfin2) as (_ & _ & HFp2 & _).
  rewrite EFA2 in HFp2. change (fs_frame_bytes LX_CID) with 512 in HFp2.
  (* back at 0x80e5c: the saved words and the spill slots are above the wrapper's stack, the frame is the
     caller's (acall_kept) *)
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0;1;2]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
    - rewrite UB8 in Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK2); lia.
    - rewrite UB8 in Ha. exfalso. lia.
    - rewrite UB2 in Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK2); lia.
    - intros _. rewrite UB2 in Ha. apply (apresent_writable SEGS). apply Hpres2. lia.
    - rewrite UB46 in Ha. apply (mbyte_of_aview SEGS).
      apply (proj1 (proj2 (proj2 (proj2 HK2))) LX_CID fp a Hfin3).
      + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes LX_CID) with 512. lia.
      + change (req_size LX_REG) with 288. lia.
    - intros _. rewrite UB46 in Ha. apply (apresent_writable SEGS). apply (proj1 (HFp2 a ltac:(lia))). }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS SHOK Ra0 Rra Rsp Rgp Rtp Rs0 QRA8 QS016 HJ HF HFr HG.
  rename HS2 into HS.
  assert (HEI2 : img_env VAL A_LIM (havoc E 512 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
  assert (SHOK : sh_ok SEGS XBx XSH (havoc E 512 (map (getr regs2) CLOB)) (mrestrict (w_H W2) mem2)).
  { apply (xs_shok cx fp); [xs_ew; exact E32 | xs_ew; exact E46 | exact HFapp | lia]. }
  (* 0x80e5c .. 0x80e80: a4 = a5 = F, the retired magic at F, `beqz a4` (F >= 4096), a1 = 64, a0 = s6, s2 = a4;
     jal __asan_set_shadow_f5 *)
  paj_run_tok RUN HS HJ2 SHOK XBspan; [xs_awr cx fp EFA2 UB2 UB46 |].
  pmkst HS.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (QSH : lSH cx fp = 2147450880 + lF cx fp / 8) by (rewrite HSHeq; reflexivity).
  eapply SRr_bind.
  { eapply (lx_set_shadow_at B LAWS _ _ ASETSH W2 (ms_regs ms0) (ms_mem ms0) LX_STK (lsp0 cx) []
      (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly2 S2 _ (k + 1) LX_CID fp
      (lSH cx fp) 64 (lsp1 cx - lsp0 cx) (Z_to_bv 64 (BASE + 3800)) HJ2).
    - left. reflexivity.
    - rewrite Ra0. exact E22'.
    - rewrite Ra1. reflexivity.
    - lia.
    - rewrite EFA2. unfold lSH. lia.
    - rewrite EFA2. change (fs_frame_bytes LX_CID / 8) with 64. unfold lSH. lia.
    - unfold spZ. rewrite Rsp, E2'. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - exact (lx_mod16 _ _ Hsp1al Hsp0al).
    - lia.
    - rewrite Hes, WS. lia.
    - rewrite Rgp, E3. exact Hgp.
    - rewrite Rtp, E4. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity]. }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hkeep4).
  pose proof HJ4 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ LX_CID fp HAR4 Hfin2) as (_ & _ & HFp4 & _).
  rewrite EFA2 in HFp4. change (fs_frame_bytes LX_CID) with 512 in HFp4.
  (* back at 0x80e84: the entry wrote only the frame's 64 shadow bytes *)
  jafter_call_keep_hi HS 528%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0;1;2]%nat HS4.
  match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; xs_ew; intros a Ha.
    - rewrite UB8 in Ha. apply (mbyte_of_aview SEGS). apply Hkeep4; lia.
    - rewrite UB8 in Ha. exfalso. lia.
    - rewrite UB2 in Ha. apply (mbyte_of_aview SEGS). apply Hkeep4; lia.
    - intros _. rewrite UB2 in Ha. apply (apresent_writable SEGS). apply Hpres4. lia.
    - rewrite UB46 in Ha. apply (mbyte_of_aview SEGS). apply Hkeep4; [lia|].
      intros Hq. rewrite QSH in Hq.
      exact (fshadow_not_app (lF cx fp) 64 (lF cx fp) 512 a HF0 ltac:(lia) HFapp Hq ltac:(lia)).
    - intros _. rewrite UB46 in Ha. apply (apresent_writable SEGS). apply (proj1 (HFp4 a ltac:(lia))). }
  rewrite <- restrict_mkst_fx in HS4.
  clear HS.
  rename HS4 into HS.
  pose proof (FFL ly2 S2 W2 mem4 md4 LX_CID fp HAR4 Hfin2) as (Hflp & Hflo & (Hfla & Hfli) & (Hfl4096 & Hflz & Hflc)).
  rewrite EFL2 in Hflp, Hflo, Hfla, Hfli, Hfl4096, Hflz, Hflc.
  assert (Hfl_frame : lFL cx fp + 1 <= lF cx fp \/ lF cx fp + 512 <= lFL cx fp).
  { destruct (Z_lt_ge_dec (lFL cx fp) (lF cx fp)) as [H1|H1]; [left; lia|].
    destruct (Z_lt_ge_dec (lFL cx fp) (lF cx fp + 512)) as [H2|H2]; [|right; lia].
    exfalso. exact (proj2 (HFp4 (lFL cx fp) ltac:(lia)) Hflo). }
  (* the flag cell as a one-byte writable region *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    assert (HRF : region_ok SEGS Ex (ms_mem msx) XFLAG);
    [ unfold XFLAG, region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      xs_ew; rewrite E47'; unfold w64; rewrite unsigned_lit_small by lia;
      split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); replace (lFL cx fp + o) with (lFL cx fp) by lia; exact Hflp
    | pose proof (st_ok_pi_add_region Ex ssx msx XFLAG HS eq_refl HRF) as HS5 ]
  end.
  match type of HS5 with ?tq -> _ => assert (HDJ : tq); [|specialize (HS5 HDJ); clear HDJ] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, XFLAG. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. xs_ew.
    rewrite E47', UB8, UB2, UB46. unfold w64. rewrite unsigned_lit_small by lia.
    repeat split; lia. }
  clear HS. rename HS5 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HEI4 : img_env VAL A_LIM Ex)
      by (apply img_env_havoc_hi; [apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia] | unfold A_LIM; lia]) end.
  pose (RUNF := aj_flag_store_pi B LAWS ML ASF FFL).
  (* 0x80e84 ld a0, 0x1f8(s2); sb zero, 0(a0) (the frame's release); j; a0 = 0; the epilogue; stop at ret *)
  paj_run_flag_sh RUNF HS HJ4.
  { unfold LX_CID. lia. }
  { intros a (rg & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; xs_ewH Hr;
        first [ rewrite E47' in Hr; unfold w64 in Hr; rewrite unsigned_lit_small in Hr by lia; right; rewrite EFL2; lia
              | rewrite UB8 in Hr; exfalso; lia
              | rewrite UB2 in Hr; left; left; lia
              | rewrite UB46 in Hr; left; right; right; right; exists LX_CID, fp; split; [left; reflexivity|];
                left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA2; change (fs_frame_bytes LX_CID) with 512; lia ]
      | ]).
    destruct Hin. }
  { intros msr HSr. rewrite EFL2.
    lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
      pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR end.
    lazymatch type of HR with region_ok _ ?Ex _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
      pose proof (field_of_region Ex (ms_mem msr) n (lFL cx fp) cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
        ltac:(xs_ew; rewrite E47'; unfold w64; apply unsigned_lit_small; lia)
        ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
    pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0. }
  (* 0x80fa0 ret: back at the caller's return address *)
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
  assert (VRA : v_jalr (getr (ms_regs ms1) 1) 0 = getr (lc_regs cx) 1) by (rewrite R1, E33; exact Hra).
  eapply (paj_ret_at (PL := PL_boxb) (PI := PI) W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. rewrite VRA.
  assert (HPERM : Permutation (ablocks B ly2 (stack_free_state LX_CID fp S2)) (ablocks B (lc_ly cx) (lc_S cx))).
  { unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly2 S2). rewrite Ebl2.
    apply (lx_perm_drop (ablocks B (lc_ly cx) (lc_S cx)) l1 l2 (r, LX_REG)). rewrite <- Ebl1.
    unfold lblk in Hblk. symmetry. exact Hblk. }
  pose proof (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ4) as HJF.
  unfold lx_post. do 6 eexists.
  split; [reflexivity|].
  split; [exact HJF|].
  split; [unfold LX_EV; lia|].
  split.
  { apply aregs_preserved_eqs;
    lazymatch goal with |- getr _ ?rr = getr _ _ =>
      let R := fresh "R" in prreg HS rr R; rewrite R; clear R end;
    first [ exact E3 | exact E4 | exact E34 | exact E35 | exact E36 | exact E37 | exact E38 | exact E39
          | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45
          | rewrite E8'; unfold w64, lsp0, spZ; apply Z_to_bv_bv_unsigned ]. }
  split; [exact R10|].
  split; [exact HPERM|].
  split.
  { unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL).
    apply (mo_le_mono MT MTL _ _ (acc + mo_free MT)); [exact (mle_station MT _ _ _ acc (mo_free MT) MTL MLE MLE2)|].
    unfold LX_NEED in HNEED. lia. }
  intros i Hi.
  pose proof HJF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  destruct Hpn as [Hn0 | (Hn & Hin0)]; [lia|].
  pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq].
  apply (F2 (lc_p cx) (lc_n cx) i Hin0); [exact (Permutation_in _ (Permutation_sym HPERM) Hin0) | lia | apply lx_inFP_nil].
Qed.

(* The exit phase: from the cut LI_X, seated by BoxBLxSeat.v lx_seat on the cut's own facts. *)
Theorem lx_exit : lx_from B MT (lx_post B MT) (LI_X B MT).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR MLE (r & HBD & Hk & Hacc & Hblk & H20).
  pose proof (lh_laws _ _ HY) as LAWS.
  pose proof HBD as (_ & _ & _ & _ & _ & _ & Hlregs & _ & _ & _ & Hs10 & Hs18 & _ & _).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & _).
  pose proof asan_consts as (C1 & _).
  set (E := lx_env cx fp (ms_regs ms3) []).
  pose proof (lx_env_E cx fp ms3 [] Hlregs) as HE.
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & E46 & _).
  apply (lx_exit_walk cx fp k acc ly3 S3 W3 ms3 md3 r E HB HJ HFR MLE Hk Hacc Hblk
           (lx_env_img cx fp (ms_regs ms3) []) HE).
  - unfold E. rewrite (lx_env_reg cx fp (ms_regs ms3) [] 20 (20%bv : bv 5) eq_refl). exact H20.
  - unfold xs_ss.
    apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E LP_X (lx_sr LX_OV) LSH_entry XSL [] 0 512 0 0 []
             (mkFacts LX_AF [] [])).
    + exact HE.
    + exact HBD.
    + apply lx_regs_ok; [apply lx_regs_ok_atoms | exact (lx_ov_ok cx fp ms3 [] Hlregs)].
    + unfold lx_slots, XSL. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd];
        (apply (lx_slot_atom cx W3 ms3 E _ LA_F (lF cx fp) 0); [rewrite Z.add_0_r; assumption | exact E46 | lia | lia]).
    + apply Forall_nil.
    + lia.
    + lia.
    + lia.
    + lia.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + exact I.
    + apply Forall_forall. intros rg _. exact I.
    + split; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) | split; exact I].
Qed.

End x.
End a.
