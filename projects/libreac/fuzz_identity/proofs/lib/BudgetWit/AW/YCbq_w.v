(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_identity's own (Reusable/YImgTop.v IMG_LO, IMG_TOP = 0x5fa000). *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YCbq.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed proc_but_pins). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0p_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Export YM04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac appn := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, kImgLo in *.
Ltac zlia := appn; lia.
Definition proc_but_pins (md md' : Model) : Prop :=
m_proc md' = mkProcState (procst_halted (m_proc md)) (procst_tid (m_proc md)) (procst_creds (m_proc md)) (procst_setsid_succeeded (m_proc md))
(procst_sigmask (m_proc md)) (procst_children (m_proc md)) (procst_utsname (m_proc md)) (procst_sigaltstack_installed (m_proc md))
(procst_killed (m_proc md)) (procst_sigabrt_pending (m_proc md)) (procst_abort_terminal (m_proc md)) (m_statpins md')
(procst_sigpipe_pending (m_proc md)) (procst_channel_reader (m_proc md))
(procst_sigpipe_action (m_proc md)) (procst_sigpipe_terminal (m_proc md)).
Definition aos_step (FP : list (Z * Z)) (md md' : Model) : Prop :=
m_io md' = m_io md /\ m_pipes md' = m_pipes md /\
YI16.fds_rel (m_fds md) (m_fds md') /\ YI16.fs_rel (m_fs md) (m_fs md') /\
(Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted (m_fs md') = true) /\
proc_but_pins md md' /\
(~ YI16.sink_open_fp FP -> m_fd md' = m_fd md /\ m_fsys md' = m_fsys md /\ m_proc md' = m_proc md).
Section e.
Context {SK : YI16.sink_head}.
Definition AOFL_HEAD : Z := YI16.sk_ofl_head.
Definition fp_spares (FP : list (Z * Z)) (a : Z) : Prop := YI16.sink_open_fp FP -> ~ (AOFL_HEAD <= a < AOFL_HEAD + 8).
End e.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section t.
Variable segs : list Segment.
End t.
Definition frame_rng (ly : alayout) (f : Z * Z) : Z * Z := (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f)).
Section a0.
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
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ wle W W' /\ aos_step FP md md' /\
frames S' = own ++ frames S /\
st_nev S' <= st_nev S + k /\ 0 <= k /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
astk_ok STK ly sp0 /\
(forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
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
Lemma apresent_writable : forall H (m : word -> option byte) a,
apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
End a0.
Definition off_img (a n : Z) : Prop := a + n <= IMG_LO \/ IMG_TOP <= a.
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
Section d0.
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
End d0.
Section e0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Local Notation ajournal := (ajournal segs B).
End e0.
Section f0.
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
End f0.
Section g0.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat k)); [apply Hv, Hkn|]. apply Hk. zlia.
Qed.
Local Notation ajournal := (ajournal segs B).
End g0.
End j.
