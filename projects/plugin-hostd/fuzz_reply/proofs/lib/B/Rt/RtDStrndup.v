(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the parts the walk of plugin-hostd/fuzz_command's strdup entry needs that no file of this tree holds: the code table of the entry (the shape of lib/A/AE34.v), the two phase lemmas (the shape of lib/A/AE2y.v icpt_phase), and one lemma that carries an [amreal] post through a later run. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDStrdupD.v, with its module paths and module names changed; 402 of its 436 lines of code are new or changed and 53 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0j YFfk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YO0d.
(* YO0d has its own spZ, raZ, ablocks and layout_le; the contracts use YG0d's *)
Import YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require Import RtDStrndupCfRt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require Import RtDStrndupP RtDStrndupA RtDStrndupF RtDStrndupR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* fuzz_command's top (cmd_strndup, astrndup_realizes over cgif's
   AR) restated over the cf allocator invariant of fuzz_reply (Reusable/YG0dcf.v): the contract is
   astrndup_realizes_cf (the trace adup_trace_cf, the malloc tree malloc_cf, the leaf strndup_leaf_cf), the malloc body
   is amalloc_body_realizes_cf, the laws are AR_laws_cf, the model facts are YG0ucf's model_laws_cf_ok. The source
   buffer that the walk reads is built here from the contract's first_byte (sbuf below); the source's shadow comes
   from the live block past its hidden head (AR_shadow_law_cf at the state after the allocation); the range check is
   the Section hypothesis RIPZ in Section g and RtDStrndupZ.reply_region_zero_stk_cf at TfibB.
   The strndup interceptor of plugin-hostd/fuzz_reply's ASan+UBSan image fuzz_reply.asan-ubsan (this harness's
   lib/A/Rt/RtDStrndup.v moved by the A-to-B address map; trampoline 0x421ec, malloc body
   0x5401c, return of the body 0x42810), composed from:
     RtDStrndupA.v snd_pre      the trampoline to the call of the malloc body (internal_strnlen included)
     amalloc_body_realizes_cf   the malloc body (Section hypothesis AMB, at TfibB AMALLOC_BODY), whose trace is the
                                contract's adup_trace_cf (RtDStrndupA.v snd_trace_eq)
     RtDStrndupR.v snd_post     the malloc body's return to the entry's own return *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* an [amreal] post followed by a run of the real machine *)
Lemma amreal_then_SRr {R} : forall (t : itree astate R) (W : world tfibsegs) c
(P Q : R -> world tfibsegs -> config -> Prop),
amreal tfibsegs t W c P -> (forall r W' c', P r W' c' -> SRr tfibsegs W' c' (Q r)) ->
amreal tfibsegs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HK; cbn [amreal] in *.
- eapply SRr_bind; [exact H|]. intros W' c' _ HP. exact (HK r W' c' HP).
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [apply Hc, Hi | exact HK]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact HK].
- exact H.
- exact I.
Qed.
End a.

(* the cf allocator invariant: imported after Section a, as in RtDStrndupR.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG07cf YG08cf YG0ucf YGcfTok YGcfXs.
(* the LPS modules shadow some list names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.

(* The source buffer the walk reads, from the contract's first_byte: the k bytes before the NUL, then (when the NUL is
   inside the count) 8 zero bytes, which cover the NUL and the alignment slack memchr_ok asks. *)
Section bf.
Definition sbuf (f : Z -> option Z) (x n k : Z) : list byte :=
map (fun i => Z_to_bv 8 (match f (x + Z.of_nat i) with Some b => b | None => 0 end)) (seq 0 (Z.to_nat k)) ++
(if k <? n then repeat (Z_to_bv 8 0) 8 else []).

Lemma u8_small : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 8 b) = b.
Proof. intros b Hb. rewrite Z_to_bv_unsigned. change (bv_wrap 8 b) with (b mod 256). apply Z.mod_small. exact Hb. Qed.

Lemma sbuf_facts : forall (f : Z -> option Z) x n k, 0 <= k <= n ->
(forall i, 0 <= i < k -> exists b, f (x + i) = Some b /\ b <> 0 /\ 0 <= b < 256) ->
(k < n -> f (x + k) = Some 0) ->
PStrFun.strnlen_res n (sbuf f x n k) = k /\ PStrFun.memchr_ok x 0 n (sbuf f x n k) /\
k <= Z.of_nat (length (sbuf f x n k)) /\
(forall j, (j < length (sbuf f x n k))%nat -> (j <= Z.to_nat k)%nat ->
Z.of_nat j < Z.min n (k + 1) /\ f (x + Z.of_nat j) = Some (bv_unsigned (nth j (sbuf f x n k) NUL))).
Proof.
intros f x n k Hk Hb Hz.
set (g := fun i : nat => Z_to_bv 8 (match f (x + Z.of_nat i) with Some b => b | None => 0 end)).
set (l := map g (seq 0 (Z.to_nat k))).
assert (Ll : length l = Z.to_nat k) by (unfold l; rewrite length_map, length_seq; reflexivity).
assert (Gl : forall j, (j < Z.to_nat k)%nat -> f (x + Z.of_nat j) = Some (bv_unsigned (g j)) /\ bv_unsigned (g j) <> 0).
{ intros j Hj. destruct (Hb (Z.of_nat j) ltac:(lia)) as (b & Eb & Hb0 & Hbr).
  unfold g. cbn beta. rewrite Eb. cbn beta iota. rewrite u8_small by exact Hbr. split; [reflexivity | exact Hb0]. }
assert (Nl : forall j d, (j < Z.to_nat k)%nat -> nth j l d = g j).
{ intros j d Hj. unfold l.
  assert (E : nth j (map g (seq 0 (Z.to_nat k))) d = nth j (map g (seq 0 (Z.to_nat k))) (g 0%nat))
  by (apply nth_indep; rewrite length_map, length_seq; exact Hj).
  rewrite E, map_nth, seq_nth by exact Hj. reflexivity. }
assert (Inl : forall b, In b l -> bv_unsigned b <> 0).
{ intros b Hin. unfold l in Hin. apply in_map_iff in Hin as (i & <- & Hi). apply in_seq in Hi.
  exact (proj2 (Gl i ltac:(lia))). }
change (sbuf f x n k) with (l ++ (if k <? n then repeat (Z_to_bv 8 0) 8 else [])).
destruct (Z.ltb_spec k n) as [Hlt|Hge]; cbn beta iota.
- (* the NUL at index k *)
  assert (FB : PStrFun.find_byte 0 (firstn (Z.to_nat n) (l ++ repeat (Z_to_bv 8 0) 8)) = Some (length l)).
  { rewrite firstn_app. rewrite firstn_all2 by lia.
    replace (Z.to_nat n - length l)%nat with (S (Z.to_nat n - length l - 1)) by lia.
    cbn [firstn repeat]. apply PStrFun.find_byte_hit; [exact Inl | reflexivity]. }
  split; [unfold PStrFun.strnlen_res; rewrite FB; cbn beta iota; lia|].
  split.
  { unfold PStrFun.memchr_ok. rewrite FB. cbn beta iota. right. rewrite length_app. cbn [length repeat].
    pose proof (Z.mod_pos_bound (- (x + Z.of_nat (length l) + 1)) 8 ltac:(lia)). lia. }
  split; [rewrite length_app; lia|].
  intros j Hj Hjk. rewrite length_app in Hj.
  destruct (Nat.lt_ge_cases j (Z.to_nat k)) as [Hjl|Hjg].
  + rewrite app_nth1 by lia. rewrite (Nl j NUL Hjl). destruct (Gl j Hjl) as [E _]. split; [lia | exact E].
  + assert (Ej : j = Z.to_nat k) by lia. subst j. rewrite app_nth2 by lia. rewrite Ll, Nat.sub_diag. cbn [repeat nth].
    split; [lia|]. rewrite Z2Nat.id by lia. rewrite (Hz Hlt). reflexivity.
- (* no NUL inside the count: k = n *)
  assert (FB : PStrFun.find_byte 0 (firstn (Z.to_nat n) (l ++ [])) = None).
  { rewrite app_nil_r. rewrite firstn_all2 by lia. apply PStrFun.find_byte_notin. exact Inl. }
  split; [unfold PStrFun.strnlen_res; rewrite FB; cbn beta iota; lia|].
  split; [unfold PStrFun.memchr_ok; rewrite FB; cbn beta iota; rewrite length_app; cbn [length]; lia|].
  split; [rewrite length_app; lia|].
  intros j Hj Hjk. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite app_nth1 by lia. rewrite (Nl j NUL ltac:(lia)). destruct (Gl j ltac:(lia)) as [E _]. split; [lia | exact E].
Qed.
End bf.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis LAWS : AR_laws_cf tfibsegs B.
Hypothesis TB : TfibSyms B.
(* part 3c: the unit's row relro_seg_t, which snd_pre reads to carry arodata_ok_cf to the body's call (RtDStrndupA.v) *)
Hypothesis RS : relro_seg_t tfibsegs.
(* the GOT slot of the shadow-offset cell and the cell at fuzz_reply.asan-ubsan's addresses, as RtDStrndupR.v's TL
   (at TfibB, lib/B/YD2l.v's two fields) *)
Hypothesis TL : as_got_shadow B = 0x9df50 /\ as_shadow_cell B = 0xa6638.
(* the ASan range check at 0x559b4 returning 0 (RtDStrndupCfRt.v); RtDStrndupZ.v reply_region_zero_stk_cf proves it *)
Hypothesis RIPZ : aregion_zero_stk_cf tfibsegs B PC_region_is_poisoned.
(* the malloc interceptor's body entered by a call, with the unwinder pc of the malloc path (Reusable/YG0dcf.v) *)
Hypothesis AMB : amalloc_body_realizes_cf tfibsegs B (pc_malloc_ra0 (as_code B)).

(* ly_img covers the image [0x10000, 0x5fc000) (the ledger's alc_img at its first and its fourth segment) *)
Lemma img_cover_cf : forall ly S Hp (W : world tfibsegs) mem md, ARcf tfibsegs B ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S Hp W mem md (M & L & _). split.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.

(* a byte of a live block is off the image, so it is neither errno nor the out-of-memory byte *)
Lemma blk_off_img : forall ly S Hp (W : world tfibsegs) mem md q m a, ARcf tfibsegs B ly S Hp W mem md ->
In (q, m) (ablocks B ly S) -> q <= a < q + req_size m -> a < 0x10000 \/ 0x5fc000 <= a.
Proof.
intros ly S Hp W mem md q m a HAR Hin Ha.
destruct (alc_client_img _ _ LAWS ly S Hp W mem md a HAR ltac:(left; exists q, m; split; [exact Hin | exact Ha]))
as [Hz _].
pose proof (img_cover_cf ly S Hp W mem md HAR) as [C1 C2]. unfold in_zr in Hz. lia.
Qed.

(* the errbuf extents lie below the allocator's ceiling *)
Lemma xs_below : forall ly S a, xs_placed_cf ly S -> Exists (in_zr a) (xs_cf ly S) -> 4096 <= a < ASAN_CEIL.
Proof.
intros ly S a HP Hx. destruct (YGcfXs.cfx_pick ly S a HP Hx) as (e & Hae & Happ & Hce & _).
unfold in_zr, in_app, ASAN_CEIL in *. lia.
Qed.

Lemma hd_skip_nonneg : forall Hp p, 0 <= hd_skip Hp p.
Proof. intros Hp p. unfold hd_skip. destruct (existsb (Z.eqb p) Hp); [exact cf_head_nonneg | lia]. Qed.

Theorem strndup_cf_at : astrndup_realizes_cf tfibsegs B SN_ENTRY SN_MID.
Proof.
intros ly S Hp W regs mem md x n k ch HPRE Hbot2 G10 G11 Hn Hx Hk Hk1 Hlive Hfb Hsrc Hra0 Hblk Htr.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Hbot & Htop & HpresA & Hgp & Htp & Hch & Hqm & Hsec & Herb & Hbud & Hbat).
pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as Lceil.
pose proof (proj1 ASAN_CEIL_range) as CR1.
unfold ASAN_CEIL in Lceil, CR1.
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ASTACK in Hslo, HpresA.
assert (Hsp : 2 ^ 44 <= spZ regs <= 2 ^ 47) by lia.
pose proof YG08cf.cf_malloc_max_bound as MMB.
(* the old block, before the allocation *)
destruct Hblk as (p0 & m0 & Hin0 & Hp0x & HxLp).
pose proof (hd_skip_nonneg Hp p0) as Hhd.
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p0 m0 HAR Hin0) as (Pal0 & P40 & Pce0 & Papp0 & Pby0 & _ & Pm0).
pose proof (req_size_bounds m0 ltac:(lia)) as RQ0.
pose proof (req_size_bounds (k + 1) ltac:(lia)) as RQk.
assert (Hheap : p0 + req_size m0 <= ly_stk_lo ly) by lia.
assert (Hx63 : 0 < x < 2 ^ 63) by lia.
(* the source buffer *)
assert (FB1 : forall i, 0 <= i < k -> exists b, aview tfibsegs (w_H W) mem (x + i) = Some b /\ b <> 0 /\ 0 <= b < 256).
{ intros i Hi. destruct Hfb as (_ & Hb & _). destruct (Hb i Hi) as (b & Eb & Hb0).
  destruct (YE2y.aview_byte_ex _ _ _ _ Eb) as (_ & _ & _ & Hr). exists b. split; [exact Eb|]. split; [exact Hb0 | exact Hr]. }
assert (FB2 : k < n -> aview tfibsegs (w_H W) mem (x + k) = Some 0) by (destruct Hfb as (_ & _ & Hz); exact Hz).
pose proof (sbuf_facts (aview tfibsegs (w_H W) mem) x n k Hk FB1 FB2) as (KS & Hok & Klen & Hrd).
set (buf := sbuf (aview tfibsegs (w_H W) mem) x n k) in *.
assert (HSRC : forall j, (j < length buf)%nat -> (j <= Z.to_nat (PStrFun.strnlen_res n buf))%nat ->
aview tfibsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j buf NUL)) /\
~ (spZ regs - SN_WIN <= x + Z.of_nat j < spZ regs)).
{ intros j Hj Hjk. rewrite KS in Hjk. destruct (Hrd j Hj Hjk) as (Hlt & Hv). split; [exact Hv|].
  destruct (Hsrc (x + Z.of_nat j) ltac:(lia)) as [_ Hns]. unfold ESTACK in Hns. unfold SN_WIN. lia. }
(* the trampoline to the malloc body *)
apply (amreal_SRr_pre tfibsegs _ W (cfg_at tfibsegs SN_ENTRY regs mem md) _ _
(snd_pre B LAWS TB RS ly S Hp W regs mem md x n buf ch HPRE Hbot2 G10 G11 Hn Hx63 Hok HSRC)).
intros W' c' _ (-> & regs_c & mem_c & md_c & -> & HPW & C10 & C1 & C2 & C8 & C9 & C18 & C20 & C21 & CK & Hsbm & MEQ & PRES
& SAVED & MN1).
rewrite KS in C10, C18, C21.
assert (Hspc : spZ regs_c = spZ regs - STRNDUP_FRAME_CF)
by (unfold spZ at 1; rewrite C2; unfold w64; apply unsigned_lit_small; unfold SN_FRAME, STRNDUP_FRAME_CF; lia).
assert (Hrac : raZ regs_c = SN_MID) by (unfold raZ; rewrite C1; reflexivity).
pose proof HPW as (HARc & _ & _ & _ & Hbotc & _).
pose proof (snd_trace_eq ly regs regs_c ch (pc_malloc_ra0 (as_code B)) SN_MID Hbotc Hspc Hrac ltac:(unfold SN_MID; lia))
as ETR.
pose proof (AMB ly S Hp W regs_c mem_c md_c (k + 1) (snd_ch ly regs ch) HPW C10 ltac:(lia) Hlive
ltac:(rewrite ETR; exact Htr)) as HM.
rewrite ETR in HM.
assert (EPC : pc_malloc (as_code B) = SN_BODY) by (rewrite (ts_code B TB); reflexivity).
rewrite EPC in HM.
(* the model step: the allocation keeps the old blocks *)
pose proof (YG0ucf.model_laws_cf_ok _ (ts_universe B TB)) as ML.
pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as HWF.
pose proof (YG0ucf.mlr_malloc_cf _ ML S (k + 1) (adup_trace_cf ly (pc_malloc_ra0 (as_code B)) SN_MID regs ch) HWF
ltac:(lia) Hlive Htr Hsec Herb (proj1 Hbat)) as HTOK.
assert (HPP : forall tr' r, apath (malloc_cf (k + 1) (adup_trace_cf ly (pc_malloc_ra0 (as_code B)) SN_MID regs ch) S) tr' r ->
gflag tr' = true -> exists ns, YG07cf.malloc_post_cf (as_universe B) S (k + 1) ns r).
{ intros tr' r Hp' _. exact (YGcfTok.atok_cf_apath _ _ _ tr' r HTOK Hp'). }
pose proof (amreal_apostg tfibsegs _ _ W _ _ HPP HM) as HM2.
apply (amreal_then_SRr _ W _ _ _ HM2).
intros [pr S2] W2 c2 [(ns & HMP) HLEAF].
cbn [YG07cf.malloc_post_cf] in HMP. destruct HMP as (HWF2 & _ & _ & _ & Hbl & _).
destruct HLEAF as (ly' & regs' & mem' & md' & -> & HPOST & R10 & HQT2 & HNULL & HXS & HERRK & HRAW).
pose proof HPOST as (HAR2 & Hlyle & Hwle2 & PRc & Hio & Hfr & Hpr2).
cbn [fst snd] in *.
destruct (alc_layout _ _ LAWS ly S Hp W mem_c md_c ly' HARc Hlyle) as (Eab & _ & Eown).
pose proof Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the blocks after the allocation *)
assert (EB2 : (pr = PNull /\ ablocks B ly' S2 = ablocks B ly S) \/
(pr <> PNull /\ ablocks B ly' S2 = ablocks B ly S ++ [(sptr_addr B ly' pr, k + 1)])).
{ unfold ablocks in *. destruct pr; cbn beta iota in Hbl;
  [left; split; [reflexivity | rewrite Hbl; exact Eab]
  | (right; split; [discriminate | destruct Hbl as [Hbl _]; rewrite Hbl, map_app, Eab; reflexivity]) ..]. }
assert (Hp0 : pr = PNull -> sptr_addr B ly' pr = 0) by (intros E; rewrite E; reflexivity).
set (p := sptr_addr B ly' pr) in *.
assert (Hin2 : In (p0, m0) (ablocks B ly' S2))
by (destruct EB2 as [[_ E]|[_ E]]; rewrite E; [exact Hin0 | apply in_or_app; left; exact Hin0]).
destruct (alc_blocks _ _ LAWS ly' S2 Hp W2 mem' md' p0 m0 HAR2 Hin2) as (_ & _ & _ & _ & Pby2 & PW2 & _).
destruct (alc_shadow _ _ LAWS ly' S2 Hp W2 mem' md' p0 m0 HAR2 Hin2) as (Hbs2 & Hhull2).
(* the new block *)
assert (NB : pr <> PNull -> 4096 <= p /\ p + req_size (k + 1) <= ly_stk_lo ly /\
(p + req_size (k + 1) <= p0 \/ p0 + req_size m0 <= p) /\
(forall a, p <= a < p + req_size (k + 1) -> apresent (w_H W2) mem' a /\ ~ aowned B ly' S2 a) /\
(forall a, p <= a < p + req_size (k + 1) -> a < 0x10000 \/ 0x5fc000 <= a)).
{ intros Hnn. destruct EB2 as [[Epr _]|[_ E]]; [exfalso; exact (Hnn Epr)|].
  assert (HinN : In (p, k + 1) (ablocks B ly' S2)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  destruct (alc_blocks _ _ LAWS ly' S2 Hp W2 mem' md' p (k + 1) HAR2 HinN) as (_ & P4 & Pce & _ & Pby & _ & _).
  assert (Hdj : zdisjoint (p0, req_size m0) (p, req_size (k + 1))).
  { rewrite E in PW2. rewrite map_app in PW2. apply (in_split_pairwise _ _ _ _ PW2).
    - apply (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin0).
    - left. reflexivity. }
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  split; [exact P4|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply Pby; lia|].
  intros a Ha. exact (blk_off_img ly' S2 Hp W2 mem' md' p (k + 1) a HAR2 HinN Ha). }
assert (Hpn : p <> 0 -> pr <> PNull) by (intros H0 H1; apply H0, Hp0, H1).
(* the errbuf extents: off every live block, below the ceiling *)
pose proof (amc_xs_placed _ _ _ _ _ (proj1 HAR)) as XS1.
assert (XSN : forall a, p0 <= a < p0 + req_size m0 -> ~ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' S2)).
{ intros a Ha Hx'. apply Exists_app in Hx' as [Hx'|Hx'].
  - exact (YGcfXs.block_not_xs_cf tfibsegs B ly S Hp W mem md p0 m0 a HAR XS1 Hin0 Ha Hx').
  - exact (YGcfXs.block_not_xs_cf tfibsegs B ly' S2 Hp W2 mem' md' p0 m0 a HAR2 HXS Hin2 Ha Hx'). }
assert (XSB : forall a, Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' S2) -> 4096 <= a < ASAN_CEIL).
{ intros a Hx'. apply Exists_app in Hx' as [Hx'|Hx']; [exact (xs_below ly S a XS1 Hx') | exact (xs_below ly' S2 a HXS Hx')]. }
unfold ASAN_CEIL in XSB.
(* the bytes of the old block survive the allocation *)
assert (SRC : forall a, p0 <= a < p0 + req_size m0 -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. pose proof (blk_off_img ly S Hp W mem md p0 m0 a HAR Hin0 Ha) as Hoi.
  rewrite Hfr.
  - apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. unfold SN_WIN. lia.
  - lia.
  - exact (proj2 (Pby0 a Ha)).
  - exact (proj2 (Pby2 a Ha)).
  - intros [Hs|He]; [rewrite Hspc in Hs; unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF in Hs; lia|].
    rewrite (ts_errno B TB) in He. unfold TFIB_ERRNO in He. lia.
  - intros [[Hnn Hin]|Hxs]; [destruct (NB Hnn) as (_ & _ & D & _); lia | exact (XSN a Ha Hxs)]. }
assert (SRCx : forall a, x <= a < x + Z.min n (k + 1) -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; apply SRC; lia).
(* the registers at 0x42810 *)
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs_c r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply PRc. exact Hr. }
(* the saved words *)
assert (SV : forall j rz off, nth_error SAVEDA j = Some (rz, off) ->
word_mem tfibsegs (mrestrict (w_H W2) mem') (spZ regs + off) (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. apply (proj1 (val_mem_word_mem tfibsegs _ _ _)).
  assert (Hoff : -80 <= off <= -8)
  by (do 10 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
  apply (YE2y.val_mem_kept (w_H W) (w_H W2) mem_c mem' (spZ regs + off) 8 _); [|exact (SAVED j rz off Hj)].
  intros q Hq. rewrite Hfr; [reflexivity | lia | | | |].
  - intros Ho. exact (alc_stack _ _ LAWS ly S Hp W mem_c md_c (spZ regs + off + q) HARc ltac:(lia) Ho).
  - intros Ho. apply (alc_stack _ _ LAWS ly' S2 Hp W2 mem' md' (spZ regs + off + q) HAR2); [rewrite Eslo, Eshi; lia | exact Ho].
  - intros [Hs|He]; [rewrite Hspc in Hs; unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF in Hs; lia|].
    rewrite (ts_errno B TB) in He. unfold TFIB_ERRNO in He. lia.
  - intros [[Hnn Hin]|Hxs]; [destruct (NB Hnn) as (_ & D & _); lia | apply XSB in Hxs; lia]. }
(* the walk from the malloc body's return *)
rewrite Hrac. unfold SN_MID.
eapply SRr_mono.
{ apply (snd_post B LAWS TB TL RIPZ ly' S2 Hp W2 regs' mem' md' x n k p (spZ regs) buf (raZ regs)
  (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
  (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23))
  (bv_unsigned (getr regs 24)) HAR2).
  - exact Hsp.
  - exact Hal16.
  - rewrite Eslo. lia.
  - rewrite Eshi. lia.
  - intros a Ha. apply Hpr2. rewrite Hspc. unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF. lia.
  - exact R10.
  - rewrite PR by acs. exact C9.
  - rewrite PR by acs. exact C20.
  - rewrite PR by acs. exact C21.
  - rewrite PR by acs. exact C8.
  - rewrite PR by acs. exact C18.
  - rewrite PR by acs. exact C2.
  - pose proof (SV 0%nat 1 (-8) eq_refl) as V. replace (spZ regs + -8) with (spZ regs - 8) in V by lia. exact V.
  - pose proof (SV 1%nat 8 (-16) eq_refl) as V. replace (spZ regs + -16) with (spZ regs - 16) in V by lia. exact V.
  - pose proof (SV 2%nat 9 (-24) eq_refl) as V. replace (spZ regs + -24) with (spZ regs - 24) in V by lia. exact V.
  - pose proof (SV 3%nat 18 (-32) eq_refl) as V. replace (spZ regs + -32) with (spZ regs - 32) in V by lia. exact V.
  - pose proof (SV 4%nat 19 (-40) eq_refl) as V. replace (spZ regs + -40) with (spZ regs - 40) in V by lia. exact V.
  - pose proof (SV 5%nat 20 (-48) eq_refl) as V. replace (spZ regs + -48) with (spZ regs - 48) in V by lia. exact V.
  - pose proof (SV 6%nat 21 (-56) eq_refl) as V. replace (spZ regs + -56) with (spZ regs - 56) in V by lia. exact V.
  - pose proof (SV 7%nat 22 (-64) eq_refl) as V. replace (spZ regs + -64) with (spZ regs - 64) in V by lia. exact V.
  - pose proof (SV 8%nat 23 (-72) eq_refl) as V. replace (spZ regs + -72) with (spZ regs - 72) in V by lia. exact V.
  - pose proof (SV 9%nat 24 (-80) eq_refl) as V. replace (spZ regs + -80) with (spZ regs - 80) in V by lia. exact V.
  - unfold raZ. rewrite Z_to_bv_bv_unsigned. exact Hra.
  - lia.
  - unfold RtDStrndupP.mm. lia.
  - lia.
  - lia.
  - lia.
  - exact Klen.
  - destruct (Z.eq_dec p 0) as [E|E]; [lia|]. destruct (NB (Hpn E)) as (P4 & P5 & _). lia.
  - unfold RtDStrndupP.mm. intros a Ha. rewrite SRCx by lia. destruct (Hsrc a ltac:(lia)) as [Hv _]. exact Hv.
  - unfold RtDStrndupP.mm. exact (ra_of_block _ _ _ x (Z.min n (k + 1)) Hbs2 ltac:(lia) Hp0x ltac:(lia)).
  - unfold RtDStrndupP.mm. intros Hm0. exact (hull_sub _ p0 (req_size m0) x (Z.min n (k + 1)) ltac:(lia) ltac:(lia) Hm0 ltac:(lia) Hhull2).
  - unfold RtDStrndupP.mm. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Papp0.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - intros j Hj. rewrite SRCx by lia. destruct (Hrd j ltac:(lia) ltac:(lia)) as [_ Hv]. exact Hv.
  - intros Hpz. destruct (NB (Hpn Hpz)) as (P4 & P5 & P6 & P7 & _). split; [lia|]. split; [lia|]. split; [lia|].
    intros a Ha. apply P7. lia. }
cbv beta. intros W3 c3 _ (-> & regs'' & mem'' & md'' & -> & HAR3 & Hio3 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21
& E22 & E23 & E24 & EK & Hfr3 & Hpr3 & Hby & HRAW3 & HMN3).
exists ly', regs'', mem'', md''.
cbn [fst snd]. fold p.
split; [reflexivity|].
split.
{ split; [exact HAR3|]. split; [exact Hlyle|]. split; [exact Hwle2|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
    r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E2. unfold spZ. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EK 3%bv) by (left; reflexivity).
      rewrite PR by acs. apply CK. cbn. tauto.
    - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EK 4%bv) by (right; left; reflexivity).
      rewrite PR by acs. apply CK. cbn. tauto.
    - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E8. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E9. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E18. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E19. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E20. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E21. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E22. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E23. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite E24. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite (EK 25%bv) by (right; right; left; reflexivity). rewrite PR by acs. apply CK. cbn. tauto.
    - replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite (EK 26%bv) by (right; right; right; left; reflexivity). rewrite PR by acs. apply CK. cbn. tauto.
    - replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite (EK 27%bv) by (right; right; right; right; reflexivity). rewrite PR by acs. apply CK. cbn. tauto. }
  split; [exact (same_io_tr md md_c md'' (same_io_sbm _ _ Hsbm) (same_io_tr md_c md' md'' Hio Hio3))|].
  split.
  { (* the frame: R's window and the new block, the body's window, errno and E, A's window *)
    intros a Ha Hown Hown2 Hscr HE.
    unfold ascratch, ASTACK in Hscr.
    rewrite Hfr3.
    - rewrite Hfr.
      + apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. unfold SN_WIN. lia.
      + exact Ha.
      + exact Hown.
      + exact Hown2.
      + unfold ascratch. rewrite Hspc. unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF. lia.
      + exact HE.
    - exact Ha.
    - lia.
    - intros [Hpz Hin]. apply HE. left. split; [exact (Hpn Hpz) | lia]. }
  intros a Ha. unfold ASTACK in Ha. apply Hpr3.
  destruct (Z_lt_le_dec a (spZ regs - 16368)) as [L1|L1].
  - apply apresent_of_aview_hi; [unfold YF0x.TFIB_IMG_END; lia|].
    rewrite Hfr; [| lia | | | | ].
    + rewrite (aview_same (w_H W) mem mem_c) by (apply MEQ; rewrite unsigned_lit_small by lia; unfold SN_WIN; lia).
      apply YE2y.aview_some_of_apresent. apply HpresA. lia.
    + intros Ho. exact (alc_stack _ _ LAWS ly S Hp W mem_c md_c a HARc ltac:(lia) Ho).
    + intros Ho. apply (alc_stack _ _ LAWS ly' S2 Hp W2 mem' md' a HAR2); [rewrite Eslo, Eshi; lia | exact Ho].
    + intros [Hs|He]; [rewrite Hspc in Hs; unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF in Hs; lia|].
      rewrite (ts_errno B TB) in He. unfold TFIB_ERRNO in He. lia.
    + intros [[Hnn Hin]|Hxs]; [destruct (NB Hnn) as (_ & D & _); lia | apply XSB in Hxs; lia].
  - destruct (Z_lt_le_dec a (spZ regs - 2160)) as [L2|L2].
    + apply Hpr2. rewrite Hspc. unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF. lia.
    + apply apresent_of_aview_hi; [unfold YF0x.TFIB_IMG_END; lia|].
      rewrite Hfr; [| lia | | | | ].
      * apply YE2y.aview_some_of_apresent. apply PRES. unfold SN_WIN. lia.
      * intros Ho. exact (alc_stack _ _ LAWS ly S Hp W mem_c md_c a HARc ltac:(lia) Ho).
      * intros Ho. apply (alc_stack _ _ LAWS ly' S2 Hp W2 mem' md' a HAR2); [rewrite Eslo, Eshi; lia | exact Ho].
      * intros [Hs|He]; [rewrite Hspc in Hs; unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF in Hs; lia|].
        rewrite (ts_errno B TB) in He. unfold TFIB_ERRNO in He. lia.
      * intros [[Hnn Hin]|Hxs]; [destruct (NB Hnn) as (_ & D & _); lia | apply XSB in Hxs; lia]. }
split; [exact E10|].
split; [exact HQT2|].
split.
{ (* the copy and the NUL *)
  intros Hnn. destruct (NB Hnn) as (P4 & _).
  assert (Hpz : p <> 0) by lia. pose proof (Hby Hpz) as AB. unfold abytes_at in AB.
  split.
  - intros i Hi.
    assert (Hi' : (Z.to_nat i < length buf)%nat) by lia.
    destruct (Hrd (Z.to_nat i) Hi' ltac:(lia)) as [_ Hv]. rewrite Z2Nat.id in Hv by lia. rewrite Hv.
    pose proof (AB (Z.to_nat i) ltac:(rewrite length_app, length_firstn; cbn [length]; lia)) as Hw.
    rewrite Z2Nat.id in Hw by lia. rewrite Hw.
    rewrite app_nth1 by (rewrite length_firstn; lia).
    rewrite RtDStrndupP.nth_firstn_lt by lia.
    assert (ND : nth (Z.to_nat i) buf (Z_to_bv 8 0) = nth (Z.to_nat i) buf NUL) by (apply nth_indep; lia).
    rewrite ND. reflexivity.
  - pose proof (AB (Z.to_nat k) ltac:(rewrite length_app, length_firstn; cbn [length]; lia)) as Hw.
    rewrite Z2Nat.id in Hw by lia. rewrite Hw.
    rewrite app_nth2 by (rewrite length_firstn; lia).
    rewrite length_firstn. replace (Z.to_nat k - Nat.min (Z.to_nat k) (length buf))%nat with 0%nat by lia.
    reflexivity. }
split.
{ (* PNull: errno and the out-of-memory byte, kept from the body's leaf (p = 0, R writes its window only) *)
  intros Hnul. destruct (HNULL Hnul) as (Er & Eo). pose proof (Hp0 Hnul) as Hpz.
  unfold rd32 in Er |- *. rewrite (ts_errno B TB) in Er |- *. rewrite (ts_oom B TB) in Eo |- *.
  unfold TFIB_ERRNO, TFIB_OOM in Er, Eo |- *. split.
  - intros q Hq. rewrite Hfr3; [exact (Er q Hq) | lia | lia | intros [Hz _]; exact (Hz Hpz)].
  - rewrite Hfr3; [exact Eo | lia | lia | intros [Hz _]; exact (Hz Hpz)]. }
split; [exact HXS|].
split.
{ (* errno kept on success, on the raw memory *)
  intros Hnn i Hi.
  assert (Ue : bv_unsigned (w64 (as_errno B + i)) = TFIB_ERRNO + i)
  by (rewrite (ts_errno B TB); unfold w64; apply unsigned_lit_small; unfold TFIB_ERRNO; lia).
  rewrite HRAW3.
  - rewrite (HERRK Hnn i Hi). apply MEQ. rewrite Ue. unfold TFIB_ERRNO, SN_WIN. lia.
  - rewrite Ue. unfold TFIB_ERRNO. lia.
  - rewrite Ue. intros [_ Hin]. destruct (NB Hnn) as (_ & _ & _ & _ & Hoff).
    specialize (Hoff (TFIB_ERRNO + i) ltac:(lia)). unfold TFIB_ERRNO in Hoff. lia. }
(* the raw frame *)
intros w Hown Hown2 Hscr HE.
unfold ascratch, ASTACK in Hscr.
rewrite HRAW3.
- rewrite HRAW; [| exact Hown | exact Hown2 | | exact HE].
  + apply MEQ. unfold SN_WIN. lia.
  + unfold ascratch. rewrite Hspc. unfold MALLOC_IN_STK_CF, STRNDUP_FRAME_CF. lia.
- lia.
- intros [Hpz Hin]. apply HE. left. split; [exact (Hpn Hpz) | lia].
Qed.
End g.

(* The instance at fuzz_reply's image B (fuzz_reply.asan-ubsan). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require RtDStrndupZ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
(* the strndup pc of the listing (`@pa_sigma _ fr_prog_listing PB_fr WS_strndup`, lib/B/W_img.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_kit W_listing W_img.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Lemma strndup_pc_B : @pa_sigma _ fr_prog_listing PB_fr WS_strndup = SN_ENTRY.
Proof. vm_compute. reflexivity. Qed.

Hypothesis AMALLOC_BODY : amalloc_body_realizes_cf tfibsegs TfibB (pc_malloc_ra0 (as_code TfibB)).
(* part 3c: the image row behind arodata_ok_cf's carry; ReplyRelroGeoB.relro_seg_reply_B proves it at CfImg_B *)
Hypothesis RELRO_SEG : relro_seg_t tfibsegs.

Theorem reply_astrndup_cf_B : astrndup_realizes_cf tfibsegs TfibB (@pa_sigma _ fr_prog_listing PB_fr WS_strndup) 0x42810.
Proof.
rewrite strndup_pc_B.
exact (strndup_cf_at TfibB (YG0lawscf.AR_laws_ok_cf tfibsegs TfibB) TfibB_syms RELRO_SEG (conj eq_refl eq_refl)
(RtDStrndupZ.reply_region_zero_stk_cf TfibB (YG0lawscf.AR_laws_ok_cf tfibsegs TfibB) TfibB_syms) AMALLOC_BODY).
Qed.
End top.

Print Assumptions reply_astrndup_cf_B.
About reply_astrndup_cf_B.
