(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (from fuzz_grant's lib/A/Prog/CtrlParseMid.v, a working branch 603e40683a4; the same code at other addresses): the walk takes fuzz_disco's context, whose contract names no caller frame for f and o, and carries pz_kept in place of acall_kept. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin, for fuzz_disco.asan-ubsan (lib_both3_0_listing, entry 0x874a4): the run steps are fuzz_grant image B's (a working branch edc3e948664, lib/B/Prog/CtrlParseMid.v; the same code, Y pc = image B pc + 0x4d30), stated on the fuzz_disco context of lib/A/Prog/CtrlParseMid.v (a working branch f0661c67ffd) over lib/Y/Prog/CtrlParseCut.v; the runtime entry is AS___asan_memset; the image objects are Y's (objects 0, 1, 12 and the side-stack flag cell as_uar_cell B, atom 34); awrFL_with is lib/Y/Prog/CtrlParseAwr.v's. *)
(* reac_ctrl_parse, the walk from cut A (0x87518, the side-stack frame seated) to cut M (0x875e4): the
   frame's header and shadow, then the memset of the out struct (the call at 0x875e0). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YCkd YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParse CtrlParseLib KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
(* The windows of a run lie in the stack below the entry sp, the out struct or the own frame. *)
Local Ltac mid_win :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; pz_bases; intro Ha; cbv beta;
unfold pz_nf, SHADOW_OFF, SB in *; lia |]); destruct Hin.
(* Speed (measured, a Theorem Labs lane, 2026-10-29): lia's Zify pass turns every x mod y and x / y of the context into
   equations with `set ... in *` over the WHOLE walk context (the symbolic state, the journals, pz_kept), so each
   lia of a run's side goal cost up to 140 s. mid_thin clears every hypothesis that is not plain Z arithmetic
   before lia; a goal that needs one of the cleared facts gets it from the branch that applies it first. *)
Local Ltac mid_arith T :=
lazymatch T with
| @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
| ~ ?A => mid_arith A | ?A /\ ?B => mid_arith A; mid_arith B | ?A \/ ?B => mid_arith A; mid_arith B
| boxed ?A => mid_arith A | off_img _ _ => idtac | in_app _ _ => idtac
| _ => fail end.
Local Ltac mid_thin := repeat match goal with H : ?T |- _ =>
lazymatch type of T with Prop => idtac end; tryif mid_arith T then fail else clear H end.
Local Ltac mid_tlia := mid_thin; lia.
(* The presence of a window byte at the memory of the journal HJx: the own frame, its shadow, or the
   journal's stack window. *)
Local Ltac mid_pres HJx :=
first [ mid_tlia
| lazymatch goal with HFp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 128 -> _ |- _ => apply (HFp _ _ (proj1 HJx)); mid_tlia end
| lazymatch goal with HFSp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 16 -> _ |- _ => apply (HFSp _ _ (proj1 HJx)); mid_tlia end
| let HP := fresh "HP" in pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _); apply HP; mid_tlia ].
(* lia over the walk's context: the disjunctive facts are boxed (lia would split on every one of them); a goal
   that needs one of them gets it destructed, one at a time. The context is thinned once, before the branches. *)
Local Ltac mid_lia :=
mid_thin;
first [ lia
| match goal with H : boxed (_ \/ _) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X; lia end
| match goal with H : boxed (_ /\ (_ \/ _)) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X as [? [?|?]]; lia end
| match goal with H : boxed (off_img _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, off_img in X; destruct X; lia end
| match goal with H : boxed (in_app _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, in_app in X; destruct X as [? [?|?]]; lia end
| unbox; lia ].
(* A range none of whose bytes is the own frame lies below or above it. *)
Lemma mid_sep : forall F FL p n, 0 < n -> (forall a, p <= a < p + n -> ~ pz_nf F FL a) -> p + n <= F \/ F + 128 <= p.
Proof.
intros F FL p n Hn H. destruct (Z_le_gt_dec (p + n) F) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (F + 128) p) as [H2|H2]; [right; exact H2|].
exfalso. apply (H (Z.max p F)); [lia|]. left. lia.
Qed.
(* The shadow hull of a range is the union of the hulls of its bytes. *)
Lemma mid_hull_bytes : forall (rd : reader) p n, 0 <= p -> 0 < n ->
(forall x, p <= x < p + n -> shadow_hull_vis rd x 1) -> shadow_hull_vis rd p n.
Proof.
intros rd p n Hp Hn H s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
set (x := Z.max p (64 * (s / 8) - 8 * 2147450880)).
assert (Hx : p <= x < p + n) by (unfold x; lia).
apply (H x Hx s). unfold x, shadow_addr, SHADOW_OFF. lia.
Qed.
Section m.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* The shadow byte of a byte of a caller frame is no byte of the out struct (an application range). *)
Lemma mid_frame_sh : forall lyc Sc W memc mdc cid pos o x,
AR SEGS B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) -> ~ (o <= shadow_addr x < o + 36).
Proof.
intros lyc Sc W memc mdc cid pos o x HAR Hin Hx Hoap.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4 & Gce & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* Where each byte of the out struct lies: a caller block or a caller frame (the machine stack is above
   the allocation ceiling, and the shadow of a caller frame holds no application byte). *)
Lemma mid_out_loc : forall STK sp0 FP ly S lyc Sc own W memc mdc o x,
AR SEGS B lyc Sc W memc mdc ->
(forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) ->
alloc_ceiling <= sp0 - STK -> o + 36 <= alloc_ceiling ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) -> o <= x < o + 36 ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid).
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hown Hstk Hoce Hoap Hx Hw.
destruct Hw as [Hs|[(_ & b & m & Hb & Hr)|[(b & m & Hb & _ & Hr)|(cid & pos & Hin & [Hr|Hr])]]].
- lia.
- left. exists b, m. split; [exact Hb | lia].
- left. exists b, m. split; [exact Hb | lia].
- right. exists cid, pos. split; [exact (Hown cid pos Hin)|]. unfold in_zr in Hr. cbn [fst snd] in Hr. lia.
- exfalso. destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR (Hown cid pos Hin)) as (G4 & Gce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
unfold in_zr in Hr. cbn [fst snd] in Hr.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* The out struct stays addressable and its shadow hull readable: a byte in a caller block has them from
   the state, a byte in a caller frame keeps its shadow byte (pz_kept) and has its hull from the state. *)
Lemma mid_out_shadow : forall STK sp0 FP ly S lyc Sc own W memc mdc S2 mem2 md2 slo shi o,
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W mem2 md2 ->
(forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) ->
(forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) -> ablocks B lyc S2 = ablocks B lyc Sc ->
alloc_ceiling <= sp0 - STK -> o + 36 <= alloc_ceiling -> 4096 <= o ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
pz_kept B lyc Sc W memc mem2 slo shi o ->
(forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 36 ->
range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF o 36 /\ shadow_hull_vis (aview SEGS (w_H W) mem2) o 36.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc S2 mem2 md2 slo shi o HAR HAR2 Hown HfinS2 Eab Hstk Hoce Ho4 Hoap KP HOW HRo.
assert (L : forall x, o <= x < o + 36 ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid))
by (intros x Hx; exact (mid_out_loc STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hown Hstk Hoce Hoap Hx (HOW x Hx))).
split.
- intros x Hx. destruct (L x Hx) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
+ rewrite <- Eab in Hb. exact (range_addressable_of_block SEGS B LAWS lyc S2 W mem2 md2 b m x 1 HAR2 Hb ltac:(lia) ltac:(lia) x ltac:(lia)).
+ refine (pz_kept_ra B LAWS lyc Sc W memc mdc mem2 slo shi o cid pos x 1 HAR KP Hin ltac:(lia) ltac:(lia) _ _ x ltac:(lia)).
* intros y Hy. exact (mid_frame_sh lyc Sc W memc mdc cid pos o y HAR Hin ltac:(lia) Hoap).
* intros y Hy. apply HRo. lia.
- apply mid_hull_bytes; [lia | lia |]. intros x Hx. destruct (L x Hx) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
+ rewrite <- Eab in Hb. exact (shadow_hull_vis_of_block SEGS B LAWS lyc S2 W mem2 md2 b m x 1 HAR2 Hb ltac:(lia) ltac:(lia) ltac:(lia)).
+ exact (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W mem2 md2 cid pos x 1 HAR2 (HfinS2 _ _ Hin) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
(* The frame f stays addressable: in a caller frame it keeps its shadow bytes (pz_kept), in a caller block
   or on the machine stack (zero shadow) it has them from the state. *)
Lemma mid_f_ra : forall lyc Sc W memc mdc S2 mem2 md2 slo shi o f,
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W mem2 md2 -> ablocks B lyc S2 = ablocks B lyc Sc ->
pz_kept B lyc Sc W memc mem2 slo shi o -> pz_loc B lyc Sc f 50 ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF f 50 ->
range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF f 50.
Proof.
intros lyc Sc W memc mdc S2 mem2 md2 slo shi o f HAR HAR2 Eab KP Hloc Hoap HRf.
destruct Hloc as [(cid & pos & Hin & Hlo & Hhi)|[(b & m & Hb & Hlo & Hhi)|(Hlo & Hhi)]].
- apply (pz_kept_ra B LAWS lyc Sc W memc mdc mem2 slo shi o cid pos f 50 HAR KP Hin Hlo Hhi); [|exact HRf].
intros y Hy. exact (mid_frame_sh lyc Sc W memc mdc cid pos o y HAR Hin ltac:(lia) Hoap).
- rewrite <- Eab in Hb. exact (range_addressable_of_block SEGS B LAWS lyc S2 W mem2 md2 b m f 50 HAR2 Hb Hlo Hhi).
- pose proof (al_zshadow _ _ LAWS lyc S2 W mem2 md2 (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR2 (or_introl eq_refl)) as Hz.
cbn [fst snd] in Hz.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR2))) as (_ & _ & _ & _ & T5 & T6 & _). unfold page_aligned in T5, T6.
apply (range_addressable_sub _ SHADOW_OFF (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) f 50); [| lia | lia].
apply zero_shadow_range; [lia | lia | exact Hz].
Qed.
End m.
(* The shadow entries of the two objects, from their shadow bytes at the current memory (the frame f may
   lie on the machine stack, above the allocation ceiling). *)
Lemma mid_shok : forall E H mem f o,
ew E 10 = Z_to_bv 64 f -> ew E 12 = Z_to_bv 64 o -> ew E 32 = Z_to_bv 64 SB ->
0 < f -> f + 50 <= 2 ^ 47 -> (f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f) ->
0 < o -> o + 36 <= 2 ^ 47 -> (o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
range_addressable (aview SEGS H mem) SHADOW_OFF f 50 -> range_addressable (aview SEGS H mem) SHADOW_OFF o 36 ->
sh_ok SEGS PZx PZ_SH E (mrestrict H mem).
Proof.
intros E H mem f o E10 E12 E32 Hf0 Hf47 Hfsh Ho0 Ho47 Hosh HRf HRo.
unfold sh_ok, PZ_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS H mem E PZx 10 f 50 f 0 50 HRf).
+ unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- apply (shent_ok_of_range SEGS H mem E PZx 12 o 36 o 0 36 HRo).
+ unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma pz_segB : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutM_case B c True -> pz_cutA_spec B c.
Proof.
intros B G RT c Hok HM Hbig E ms md Hcur HS.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_open_f Hbig. pz_std.
lazymatch type of AGX with forall n0, _ -> ew _ n0 = ew ?E0 n0 =>
assert (AG : forall n0, (n0 < 33)%nat -> ew E n0 = ew E0 n0) by (intros; apply AGX; lia) end.
assert (HFp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, F <= a < F + 128 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & Hp & _).
rewrite <- EF in Hp. change (fs_frame_bytes 1) with 128 in Hp. exact (proj1 (Hp a Ha)). }
assert (HFSp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & _ & Hp).
rewrite <- EF in Hp. unfold shadow_addr in Hp. change (fs_frame_bytes 1 / 8) with 16 in Hp.
replace a with (SHADOW_OFF + F / 8 + (a - (SB + F / 8))) by (unfold SHADOW_OFF, SB; lia).
assert (Hi : 0 <= a - (SB + F / 8) < 16).
{ unfold SB in *. idtac. lia. }
apply (proj1 (Hp (a - (SB + F / 8)) Hi)). }
(* The out struct is present at every memory of the journal: each of its bytes is one the caller may write. *)
assert (HOp : forall m md', ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 W m md' k ->
forall a, o <= a < o + 36 -> apresent (w_H W) m a).
{ intros m md' HJx a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((1, fpos) :: own) a)
by (rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a Ha))).
exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJx Hw)). }
(* Where o lies relative to the own frame and the stack window: below the allocation ceiling, where the
   caller may write, so apart from the own frame. *)
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
assert (Hstk : alloc_ceiling <= sp0 - STK) by (clear - Hceil Hslo; lia).
assert (Hslo2 : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by (clear - Hstk Hwin; lia).
assert (Hshi2 : sp <= 2 ^ 64) by (clear - Hsp0 Hshi H47; lia).
repeat match goal with H : _ \/ _ |- _ => box H | H : off_img _ _ |- _ => box H | H : in_app _ _ |- _ => box H end.
assert (HsepO : o + 36 <= F \/ F + 128 <= o).
{ apply (mid_sep F FL o 36 ltac:(lia)). intros a Ha.
exact (pz_awr_nf B STK sp0 FP ly S lyc Sc own W memc mdc a F FL HAR Hownf N1 N3 N4 Hstk (proj1 (HOW a Ha))). }
(* 1. The frame's header (0x41b58ab3, its description, the function), its shadow (f1 f1 f1 f1, 00 x 4, 04,
   f3 f3 f3, f3 x 4), the frame address at sp1 + 24, to the memset of the out struct. *)
pose proof (SRr_run_pi_AJ_call (fx := fq) B LAWS) as RUNC.
lazymatch type of RUNC with forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
lazymatch r with (?ss', PRS_call ?sym) =>
assert (Hrun : sym_runN_pi tpi FUEL ssx = (ss', PRS_call sym)) by (vm_compute; reflexivity);
eapply (RUNC Wx FUEL Ex ssx ss' sym msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ2);
[ clear Hrun | clear Hrun HS HJ2; intros ms1 mat1 HS HJ2 HF HFr HG ] end end end.
{ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by mid_win;
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mB (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HARc Hfrs2 Eab EF EFL FFL Hslo2 Hshi2 Hoimg
ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]) KP
(kept_of_frame _ _ _ _ _ _ HFr Hw) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw HF HFr HG; rename KP' into KP.
destruct (mid_out_shadow B LAWS STK sp0 FP ly S lyc Sc own W memc mdc S2 _ _ (sp - REAC_CTRL_PARSE_STK) sp o
HAR (proj1 HJ2) Hownf HfinS2 Eab Hstk Howin Ho4096 Hosh KP (fun a Ha => proj1 (HOW a Ha)) HRo) as [HRo1 HHo1].
(* 2. memset(out, 0, 36). *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite AGX, E12 in Ra0 by lia. rewrite AGX, E33 in R2 by lia.
rewrite AGX, (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite AGX, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS___asan_memset) (AMEMSET fq) W rT mT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 dT k o 0 36 (sp1 - sp0) _ HJ2) end.
- rewrite Ra0. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- lia. - rewrite Hes; lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a ltac:(lia))) | mid_lia].
- exact Hoam.
- exact HRo1.
- intros _. exact HHo1.
- exact I. }
cbv beta. clear R1 R2 R3 R4 Ra0 Ra1 Ra2.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
lazymatch type of KP with pz_kept _ _ _ _ _ ?mA _ _ _ =>
pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mem3 (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL
(fun a => (sp1 - ESTACK <= a < sp1) \/ (o <= a < o + 36)) HAR HARc Hfrs2 Eab EF EFL FFL Hslo2 Hshi2 Hoimg
ltac:(intros a [Ha|Ha]; [left; rewrite Hes in Ha; lia | right; left; exact Ha]) KP
ltac:(intros a Ha Hna; apply Hfr3; [exact Ha | intros Hx; apply Hna; right; exact Hx | intros Hx; apply Hna; left; lia])
Hpres3) as KP' end.
clear KP HRo1 HHo1; rename KP' into KP.
jafter_call_keep_hi HS 544%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [| specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
(eapply pz_region_kept; [pz_bases; reflexivity
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr3; unfold ESTACK, off_img, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; mid_lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; mid_pres HJ3 ]). }
rewrite <- restrict_mkst_fx in HS3. clear HS; rename HS3 into HS.
pz_rebase HS AGX.
(* 3. The out struct is zero (memset); the frame and its shadow become read-only for the shadow-checked part. *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]));
[| assert (RDJ : all_disjoint Ev (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) (ss_mem ssx))] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
pz_bases. split; [lia|]. split; [lia|]. split.
- intros o0 Ho0. apply (apresent_writable SEGS). apply (HOp _ _ HJ3). lia.
- apply Forall_cons; [|apply Forall_nil]. apply pz_chunk_zero. intros i Hi.
replace (o + 0 + i) with (o + i) by lia. rewrite (Heff3 i Hi). reflexivity. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
pz_bases.
revert Hslo Hshi H47 Hceil Hwin Hstk0 WS C1 Hsp1r Hob0 Hob1 Hob12 Hobu Hf0 Hf47 Ho4096 Ho47 HF4096 HFceil HFapp HFimg
HsepO Hfsh Hosh Hfwin Howin Hfoimg Hoimg Hsp0 HF8lo HF8hi Hdfo.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB. clear. intros. repeat split; mid_lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 12%nat) 0 36 0 36 [YP09.mkChunk 0 (CZero 36)]) HS eq_refl ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o0 Ho0; lia))) as HS' end.
clear HS; rename HS' into HS. pz_norm HS.
(* 4. Cut M. *)
ra_join HS ss_cutM 560%nat pz_deadM ltac:(idtac).
pz_rebase HS AGX.
pose proof (mid_f_ra B LAWS lyc Sc W memc mdc S2 _ _ (sp - REAC_CTRL_PARSE_STK) sp o f HAR (proj1 HJ3) Eab KP Hfloc Hosh HRf) as HRf3.
destruct (mid_out_shadow B LAWS STK sp0 FP ly S lyc Sc own W memc mdc S2 _ _ (sp - REAC_CTRL_PARSE_STK) sp o
HAR (proj1 HJ3) Hownf HfinS2 Eab Hstk Howin Ho4096 Hosh KP (fun a Ha => proj1 (HOW a Ha)) HRo) as [HRo3 _].
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
assert (SHOK : sh_ok SEGS PZx PZ_SH Ev (mrestrict (w_H W) (ms_mem msv)));
[ apply (mid_shok Ev _ _ f o); [rewrite AGX by lia; exact E10 | rewrite AGX by lia; exact E12 | rewrite AGX by lia; exact E32
| lia | exact Hf47 | exact Hfsh | lia | exact Ho47 | exact Hosh | exact HRf3 | exact HRo3 ]
| apply (HM Hbig Ev msv md3); [ | exact HS | exact SHOK | exact I ] ] end.
cbn [pz_cur pz_E0 cx_fq cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc
cx_mdc cx_k cx_regs cx_ch cx_f cx_n cx_o cx_fr cx_S2 cx_fpos ms_mem].
split; [assumption|]. split; [exact AGX|]. split; [exact RF|]. split; [exact E528|]. split; [exact E529|].
split; [exact HJ3 | exact KP].
Qed.
End d.
End b.
