(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan, m_file at 0x85ebc): the premise bundle of m_file's snprintf call
   at 0x86014, snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf"), for the segment
   S_MF_ENTRY (lib/A/Prog/m_file_s_entry.v). Proves no function: invariant lemmas over any state whose AR holds.

   The callee contract is lib/A/Rt/RtPFCmd.v `asnprintf_sh pc gotw guard` = cmd_asnprintf_realizes FR_cmd CMD_SNP_K
   ... (:310-343, :355-356), its family FR_cmd (:90-95), over the vocabulary of lib/A/Rt/RtPFShared.v:38-101. These
   lemmas turn the reader-level facts of lib/A/Prog/SegABase.v (sa_str, sa_addr, sa_heap, sa_fframe, sa_img, sa_lit,
   sa_disj) into that contract's premises, so the walk supplies only reader-level facts:
   - mf_str_end_span: RtPFShared.str_end's slack is seg_spec.cstr_span (the read span SegABase keeps apart);
   - mf_label_arg: the %s argument (pf_arg_asan at APtr, and FR_cmd's cmd_args_slack / cmd_args_amem bands);
   - mf_fmt_lit: the format literal "%s" (fmt_at);
   - mf_dest_heap: the destination, a range of one live heap block (dest_ok, amem_range, off the image);
   - mf_heap_addr: a heap range's shadow facts (sa_addr) at ANY state whose AR holds.
   Image bounds come from AR alone (ALedger.al_img and layout_ok.lo_img: an image byte lies in [0x10000, kImgEnd)).
   mf_dest_heap takes ONE premise beyond the bundle's draft: the image cover of the layout, the type of the
   listing's PAImg field pa_img_cover (lib/A/Prog/SegPa.v:52; image A's value SegImg.seg_img_cover). Without it
   no fact of a generic segs keeps a heap block out of [0x10000 + |ly_img|, kImgEnd); the walk has it for SEGS.
   APtr is RtPFPf's constructor (RtPFShared Requires RtPFPf without re-exporting it), so it is written RtPFPf.APtr. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFPf RtPFShared.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- arithmetic of the read span ---- *)
(* 1: the slack of a C string is exactly seg_spec.cstr_span *)
Lemma mf_str_end_span : forall a s, RtPFShared.str_end a s - a = seg_spec.cstr_span a s.
Proof.
intros a s. unfold RtPFShared.str_end, seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as R1.
pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as R2.
pose proof (Z.div_mod (a + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as D2.
lia.
Qed.
Lemma mfk_span_bounds : forall a s,
  Z.of_nat (length s) + 1 <= seg_spec.cstr_span a s <= Z.of_nat (length s) + 8.
Proof.
intros a s. unfold seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
Qed.
(* the string's slack ends at or below any 8-aligned bound above its NUL *)
Lemma mfk_str_end_le : forall a s A, a + Z.of_nat (length s) < A -> A mod 8 = 0 -> RtPFShared.str_end a s <= A.
Proof.
intros a s A H HA. unfold RtPFShared.str_end.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.div_mod (a + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.div_mod A 8 ltac:(lia)). lia.
Qed.
(* the ASan reader gives a byte *)
Lemma mfk_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v Hv. unfold aview in Hv.
lazymatch type of Hv with option_map _ ?o = Some _ => destruct o as [b|] end; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range _ b) as R.
unfold bv_modulus in R. assert (E : 2 ^ Z.of_N 8 = 256) by reflexivity. rewrite E in R. lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Lemma mfk_ceil8 : alloc_ceiling mod 8 = 0.
Proof.
pose proof ASAN_CEIL_range as [_ H]. unfold ASAN_CEIL in H.
destruct (proj1 (Z.mod_divide alloc_ceiling 4096 ltac:(lia)) H) as [k Hk]. rewrite Hk.
replace (k * 4096) with ((k * 512) * 8) by lia. apply Z_mod_mult.
Qed.
(* an image byte lies in [0x10000, kImgEnd): ALedger's al_img puts every segment inside ly_img, and layout_ok's
   lo_img puts ly_img at kImgLo, below kImgEnd *)
Lemma mfk_img_bound : forall ly S (W : world segs) mem md x,
  AR segs B ly S W mem md -> in_img segs x -> 0x10000 <= x < kImgEnd.
Proof.
intros ly S W mem md x (M & L & _) (sg & Hsg & H1 & H2).
pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img _ (am_layout _ _ _ _ M)) as (J0 & J1 & J2 & J3).
rewrite J0 in I1, I2. unfold kImgLo, kImgEnd in *. lia.
Qed.
(* an object in one of the three places ends below alloc_ceiling, and 7 bytes past its end are in application
   memory *)
Lemma mfk_loc_facts : forall ly S (W : world segs) mem md q n,
  AR segs B ly S W mem md -> 0 < n ->
  (sa_heap B ly S q n \/ sa_fframe ly S q n \/ sa_img segs B q n) ->
  q + n <= alloc_ceiling /\ amem_range q (n + 7).
Proof.
intros ly S W mem md q n HAR Hn Hloc.
pose proof ASAN_CEIL_range as [[C1 C2] C3].
destruct Hloc as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hcid & H1 & H2) | Himg]].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hc & Happ & _).
  assert (Hr : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
  split; [lia|]. destruct Happ as [_ [Hl | [Hh1 Hh2]]]; [left; lia | right; lia].
- destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (F0 & Fc & Fapp).
  unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
  split; [lia|]. destruct Fapp as [_ [Hl | [Hh1 Hh2]]]; [left; lia | right; lia].
- pose proof (mfk_img_bound ly S W mem md q HAR (proj1 (Himg q ltac:(lia)))) as [I1 _].
  pose proof (mfk_img_bound ly S W mem md (q + n - 1) HAR (proj1 (Himg (q + n - 1) ltac:(lia)))) as [_ I2].
  unfold amem_range, kImgEnd, kLowMemEnd, ASAN_CEIL in *. split; [lia | left; lia].
Qed.

(* 2: the %s argument *)
Lemma mf_label_arg : forall ly S (W : world segs) mem md (lptr d : Z) (ltext : list Z) (K sp w : Z),
  AR segs B ly S W mem md -> 0 < lptr ->
  sa_str (aview segs (w_H W) mem) lptr ltext ->
  sa_addr (aview segs (w_H W) mem) lptr (Z.of_nat (length ltext) + 1) ->
  Z.of_nat (length ltext) <= 65535 ->
  (sa_heap B ly S lptr (Z.of_nat (length ltext) + 1) \/ sa_fframe ly S lptr (Z.of_nat (length ltext) + 1) \/
   sa_img segs B lptr (Z.of_nat (length ltext) + 1)) ->
  sa_disj lptr (seg_spec.cstr_span lptr ltext) d w ->
  0 <= w -> 0 <= K -> alloc_ceiling <= sp - K -> sp <= 2 ^ 47 ->
  RtPFShared.pf_arg_asan (aview segs (w_H W) mem) (RtPFShared.snp_out K sp d w) lptr (RtPFPf.APtr ltext)
  /\ amem_range lptr (seg_spec.cstr_span lptr ltext)
  /\ amem_range lptr (Z.of_nat (length ltext) + 8).
Proof.
intros ly S W mem md lptr d ltext K sp w HAR Hp [[Hz Hn0] Ht] (A0 & A1 & A2 & A3 & A4) Hlen Hloc Hdj Hw HK Hc Hsp.
destruct (mfk_loc_facts ly S W mem md lptr (Z.of_nat (length ltext) + 1) HAR ltac:(lia) Hloc) as [Lc Lm].
pose proof (mf_str_end_span lptr ltext) as Esp.
pose proof (mfk_span_bounds lptr ltext) as Sb.
assert (Hlt : lptr + Z.of_nat (length ltext) < alloc_ceiling) by lia.
pose proof (mfk_str_end_le lptr ltext alloc_ceiling Hlt mfk_ceil8) as Se.
assert (E31 : 2 ^ 31 = 2147483648) by reflexivity.
split; [|split].
- unfold RtPFShared.pf_arg_asan. cbv beta iota.
  split.
  { apply Forall_forall. intros c Hc'.
    destruct (List.In_nth ltext c 0 Hc') as (i & Hi & Hnth).
    pose proof (Hz i ltac:(rewrite length_app; cbn [length]; lia)) as Hzi.
    rewrite List.app_nth1 in Hzi by lia. rewrite Hnth in Hzi.
    pose proof (mfk_aview_byte segs (w_H W) mem _ _ Hzi) as Rb.
    assert (c <> 0) by (intros ->; exact (Hn0 Hc')). cbv beta. lia. }
  split; [exact Hp|]. split; [lia|]. split.
  { intros i Hi. pose proof (Hz (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hzi.
    rewrite Z2Nat.id in Hzi by lia. exact Hzi. }
  split; [exact Ht|]. split.
  { unfold RtPFShared.snp_out. constructor; [|constructor; [|constructor]]; unfold zdisjoint; cbn [fst snd].
    - left. lia.
    - unfold sa_disj in Hdj. lia. }
  split; [exact A2|]. split; [exact A3|]. apply A4. lia.
- unfold amem_range in *. lia.
- unfold amem_range in *. lia.
Qed.

(* 3: the format literal "%s" *)
Lemma mf_fmt_lit : forall ly S (W : world segs) mem md (f d : Z) (fm : list Z) (K sp w : Z),
  AR segs B ly S W mem md -> sa_lit segs B (aview segs (w_H W) mem) f fm ->
  0 <= w -> 0 <= K -> alloc_ceiling <= sp - K -> sp <= 2 ^ 47 ->
  (d + w <= 0x10000 \/ kImgEnd <= d) ->
  RtPFShared.fmt_at (aview segs (w_H W) mem) (RtPFShared.snp_out K sp d w) f fm.
Proof.
intros ly S W mem md f d fm K sp w HAR (Hf & [[Hz _] _] & Hpin & _ & Himg) Hw HK Hc Hsp Hd.
destruct (Hpin ly S W mem md HAR) as (A0 & A1 & A2 & A3 & A4).
pose proof ASAN_CEIL_range as [[C1 C2] C3].
pose proof (mfk_img_bound ly S W mem md f HAR (proj1 (Himg f ltac:(lia)))) as [I1 _].
pose proof (mfk_img_bound ly S W mem md (f + Z.of_nat (length fm)) HAR
  (proj1 (Himg (f + Z.of_nat (length fm)) ltac:(lia)))) as [_ I2].
unfold RtPFShared.fmt_at. split; [exact Hf|]. split.
{ intros i Hi. pose proof (Hz (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hzi.
  rewrite Z2Nat.id in Hzi by lia. exact Hzi. }
split.
{ unfold RtPFShared.snp_out. constructor; [|constructor; [|constructor]]; unfold zdisjoint; cbn [fst snd];
  unfold ASAN_CEIL, kImgEnd in *; lia. }
split; [exact A2|]. split; [exact A3|]. apply A4. lia.
Qed.

(* 4: the destination, a range of one live heap block. The first premise is the image cover of the layout, the type
   of the listing's PAImg field pa_img_cover (SegPa.v:52): with it the block, a client range, misses
   [0x10000, kImgEnd) (al_client_img) *)
Lemma mf_dest_heap : forall ly S (W : world segs) (regs : bvmap 5 word) mem md (d w : Z),
  (forall ly' S' md', ALedger segs ly' S' md' ->
    fst (ly_img ly') <= 0x10000 /\ kImgEnd <= fst (ly_img ly') + snd (ly_img ly')) ->
  AR segs B ly S W mem md -> sa_heap B ly S d w -> 0 <= w ->
  alloc_ceiling <= spZ regs - ESTACK ->
  dest_ok segs B ly S W regs mem d w /\ amem_range d w /\ (d + w <= 0x10000 \/ kImgEnd <= d).
Proof.
intros ly S W regs mem md d w IMGC HAR (b & m & Hin & H1 & H2) Hw Hsp.
pose proof ASAN_CEIL_range as [[C1 C2] C3].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hc & Happ & Hpres & _).
assert (Hr : 1 <= req_size m /\ m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [|split].
- intros a Ha. destruct (Hpres a ltac:(lia)) as [Hpr Ho].
  split; [exact (apresent_writable segs _ _ _ Hpr)|]. split; [exact Ho|]. lia.
- unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
  destruct Happ as [_ [Hl | [Hh1 Hh2]]]; [left; lia | right; lia].
- pose proof HAR as (M & L & _). destruct (IMGC ly S md L) as [G1 G2].
  destruct (Z.le_gt_cases (b + req_size m) 0x10000) as [Hlo|Hlo]; [left; lia|].
  destruct (Z.le_gt_cases kImgEnd b) as [Hhi|Hhi]; [right; lia|]. exfalso.
  assert (Ha : b <= Z.max b 0x10000 < b + req_size m) by lia.
  destruct (al_client_img _ _ LAWS ly S W mem md (Z.max b 0x10000) HAR
    (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha))))) as [Hni _].
  apply Hni. unfold in_zr, kImgEnd in *. lia.
Qed.

(* 5: a heap range's shadow facts at ANY state whose AR holds *)
Lemma mf_heap_addr : forall ly S (W : world segs) mem md (q n : Z),
  AR segs B ly S W mem md -> sa_heap B ly S q n -> 0 <= n -> sa_addr (aview segs (w_H W) mem) q n.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & H1 & H2) Hn.
pose proof ASAN_CEIL_range as [[C1 C2] C3].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hc & Happ & _).
assert (Hr : 1 <= req_size m /\ m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (E63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
unfold sa_addr. split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split.
{ unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
  destruct Happ as [_ [Hl | [Hh1 Hh2]]]; [left; lia | right; lia]. }
split.
{ exact (range_addressable_of_block segs B LAWS ly S W mem md b m q n HAR Hin H1 ltac:(lia)). }
intros Hpos. destruct (al_shadow _ _ LAWS ly S W mem md b m HAR Hin) as [_ Hh].
unfold shadow_hull_vis in Hh |- *. intros s Hs. apply Hh. unfold shadow_addr in *.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (Z.div_le_mono b q 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (q + n - 1) (b + req_size m - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (R8 (SHADOW_OFF + b / 8) (SHADOW_OFF + q / 8) ltac:(lia)) as M1.
pose proof (R8 (SHADOW_OFF + (q + n - 1) / 8) (SHADOW_OFF + (b + req_size m - 1) / 8) ltac:(lia)) as M2.
lia.
Qed.
End s.

About mf_str_end_span.
About mf_label_arg.
About mf_fmt_lit.
About mf_dest_heap.
About mf_heap_addr.
Print Assumptions mf_str_end_span.
Print Assumptions mf_label_arg.
Print Assumptions mf_fmt_lit.
Print Assumptions mf_dest_heap.
Print Assumptions mf_heap_addr.
