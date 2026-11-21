(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YCe5.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YCe5.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG08_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Export YM04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac appn := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, kImgLo in *.
Ltac zlia := appn; lia.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section j.
Variable segs : list Segment.
Lemma apresent_grows : forall H m m' a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|]. exfalso.
apply (Hg (Z_to_bv 64 a)); unfold mrestrict; rewrite Hh; [rewrite Hb; discriminate | exact E'].
Qed.
End j.
Definition frame_rng (ly : alayout) (f : Z * Z) : Z * Z := (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f)).
Section t.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation code := (as_code B).
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
Definition achain (ly : alayout) (rd : reader) (sp v : Z) (ch : list (Z * Z * Z)) : Prop :=
((v < alloc_ceiling \/ ly_top ly - 16 <= v \/ v mod 8 <> 0) /\ ch = [])
\/ (sp + 16 <= v /\ v < ly_top ly - 16 /\ v mod 8 = 0 /\ fpchain (rdword rd) v (ly_top ly) ch /\
Forall (fun r => sp + 16 <= fst (fst r)) ch).
Lemma rdword_ext : forall (rd rd' : reader) a,
(forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a Hk. unfold rdword.
replace (rd' a) with (rd a) by (rewrite <- (Z.add_0_r a); symmetry; apply Hk; zlia).
rewrite !Hk by zlia. reflexivity.
Qed.
Definition astk_ok (STK : Z) (ly : alayout) (sp0 : Z) : Prop :=
sp0 mod 16 = 0 /\ 0 <= STK /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= sp0 /\ sp0 <= ly_stk_hi ly /\
ly_stk_hi ly <= 2 ^ 47 /\ ly_bot ly + STK < sp0 + ASTACK /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly.
Definition afn_pre (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
AR segs B ly S W mem md /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
astk_ok STK ly (spZ regs) /\
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) /\
achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch /\
qtight S                                               .
Definition ajournal (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
AR segs B ly' S' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ wle W W' /\ same_io md md' /\
frames S' = own ++ frames S /\
st_nev S' <= st_nev S + k /\ 0 <= k /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
astk_ok STK ly sp0 /\
qtight S'                                              .
Lemma asan_consts : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ kHighShadowEnd = 0x10007fff8000 /\ kHighMemBeg = 0x10007fff8000 /\
kHighMemEnd = 0x800000000000 /\ kLowMemEnd = 0x7fff8000.
Proof. split; [exact (proj1 alloc_ceiling_val)|]. repeat split; reflexivity. Qed.
Lemma shadow_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; zlia. Qed.
Lemma find_segment_none : forall a, ~ in_img segs a -> find_segment segs a 1 = None.
Proof.
intros a Hn. induction segs as [|sg rest IH] in Hn |- *; [reflexivity|]. cbn.
destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
- exfalso. apply Hn. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
exists sg. split; [left; reflexivity | zlia].
- apply IH. intros (sg' & Hin & Hr). apply Hn. exists sg'. split; [right; exact Hin | exact Hr].
Qed.
Lemma seg_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> seg_rom segs (Z_to_bv 64 a) = None.
Proof.
intros a Ha Hn. unfold seg_rom, memory_read. cbn [Z.of_N].
rewrite unsigned_lit_small by zlia. rewrite (find_segment_none a Hn). reflexivity.
Qed.
Lemma mbyte_of_aview : forall H H' (m m' : word -> option byte) a,
aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma apresent_transfer : forall H H' (m m' : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ in_img segs a ->
aview segs H' m' a = aview segs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Ha Hn E [Hh [b Hb]]. apply mbyte_of_aview in E. unfold apresent. unfold mbyte, mrestrict in E.
rewrite Hh, Hb in E. rewrite (seg_rom_none a Ha Hn) in E.
destruct (H' (Z_to_bv 64 a)); [discriminate|]. split; [reflexivity|].
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | discriminate].
Qed.
Lemma apresent_writable : forall H (m : word -> option byte) a,
apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
End t.
Definition off_img (a n : Z) : Prop := a + n <= 0x10000 \/ 0x5fa000 <= a.
Definition zone2 (a n : Z) : Prop := off_img a n /\ (a + n <= 2147446784 \/ 17594333495296 <= a).
Definition frame_flag_lawP (segs : list Segment) (B : asyms) : Prop :=
forall ly S (W : world segs) mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
(app_addr (flag_addr ly cid pos) /\ ~ in_img segs (flag_addr ly cid pos)) /\
(4096 <= flag_addr ly cid pos /\ zone2 (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling).
Definition stack_malloc_progressP (B : asyms) : Prop :=
forall s cid, Wf (as_universe B) s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s').
Definition api_env (segs : list Segment) (B : asyms) : Prop :=
(0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd) /\
(forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a) /\
(In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B)).
Section a0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Let UNIV0 : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\ In [pc_free_ra0 (as_code B)] (as_universe B) := proj2 (proj2 errno_low).
Let ERRIMG : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a := proj1 (proj2 errno_low).
Hypothesis ML : model_laws (as_universe B).
Local Notation code := (as_code B).
Local Notation afn_pre := (afn_pre segs B).
Local Notation ajournal := (ajournal segs B).
Let regime_ok_small' : forall s, st_nev s < EV_MAX -> regime_ok s := fun s H => or_introl H.
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
End a0.
Section d0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Local Notation ajournal := (ajournal segs B).
End d0.
Section e0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ML : model_laws (as_universe B).
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis ASF : astack_free_law segs B.
Hypothesis frame_flag_law : frame_flag_lawP segs B.
Local Notation ajournal := (ajournal segs B).
End e0.
Section f0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma aview_byte : forall H mem a v,
aview segs H mem a = Some v -> exists b : byte, mbyte segs (mrestrict H mem) a = Some b /\ v = bv_unsigned b /\ 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. exists b. split; [reflexivity|]. split; [reflexivity|].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H0. cbn in H0. zlia.
Qed.
Lemma val_mem_of_rdword : forall H mem a v,
rdword (aview segs H mem) a = Some v -> val_mem segs (mrestrict H mem) a 8 v.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte in E0 as (c0 & M0 & -> & R0). apply aview_byte in E1 as (c1 & M1 & -> & R1).
apply aview_byte in E2 as (c2 & M2 & -> & R2). apply aview_byte in E3 as (c3 & M3 & -> & R3).
apply aview_byte in E4 as (c4 & M4 & -> & R4). apply aview_byte in E5 as (c5 & M5 & -> & R5).
apply aview_byte in E6 as (c6 & M6 & -> & R6). apply aview_byte in E7 as (c7 & M7 & -> & R7).
rewrite ?Z.add_0_r in M0.
set (v := bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
assert (Hv : 0 <= v < 2 ^ 64) by (subst v; zlia).
assert (BY : forall (k : nat) (c : byte) (lo : Z) (hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YO0f.le_byte v 8 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; zlia).
rewrite Z.shiftr_div_pow2 by zlia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; zlia | zlia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; zlia | zlia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |zlia];
[ change (a + Z.of_nat 0) with (a + 0); rewrite Z.add_0_r
| change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 | change (Z.of_nat 4) with 4
| change (Z.of_nat 5) with 5 | change (Z.of_nat 6) with 6 | change (Z.of_nat 7) with 7 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat c0 0 (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))); cbn; subst v; zlia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat c1 (bv_unsigned c0) (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))))); cbn; subst v; zlia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat c2 (bv_unsigned c0 + 256 * bv_unsigned c1) (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))); cbn; subst v; zlia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat c3 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * bv_unsigned c2))
(bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))); cbn; subst v; zlia.
- rewrite M4. f_equal. symmetry. apply (BY 4%nat c4 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * bv_unsigned c3)))
(bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))); cbn; subst v; zlia.
- rewrite M5. f_equal. symmetry. apply (BY 5%nat c5 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * bv_unsigned c4))))
(bv_unsigned c6 + 256 * bv_unsigned c7)); cbn; subst v; zlia.
- rewrite M6. f_equal. symmetry. apply (BY 6%nat c6 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * bv_unsigned c5)))))
(bv_unsigned c7)); cbn; subst v; zlia.
- rewrite M7. f_equal. symmetry. apply (BY 7%nat c7 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * bv_unsigned c6))))))
0); cbn; subst v; zlia.
Qed.
Lemma val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat k)); [apply Hv, Hkn|]. apply Hk. zlia.
Qed.
Local Notation ajournal := (ajournal segs B).
End f0.
End e.
