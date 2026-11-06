(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3501 of its 3539 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_ctrl_parseF.v, with its module paths, module names, addresses and numbers changed; 5648 of its 6995 lines of code are new or changed and 2192 lines of the source are left out. *)
(* The footprint twin of reac_ctrl_parse_x_holds (reac_ctrl_parse.v, not in this delivery), asan build (A): the same run as an ExecF.evtF
   under a footprint RNG (reac_ctrl_parse_contract_x_F of reac_ctrl_parse_c.v: the EXACT metadata of the window), by
   the script of lib/A/Prog/reac_ctrl_parse.v over StepF's step. Main theorem: reac_ctrl_parse_x_F_holds.
   Provenance. This file is the image-A footprint run that a Theorem Labs lane wrote in fuzz_grant
     git show 92c918924f0:proofs/libreac/fuzz_grant/lib/A/Prog/reac_ctrl_parseF.v   (rc=0 there)
   moved back to this unit by alreloc.py of record (a working branch f7ad5277b9f) with --src libreac/fuzz_grant
   --ref 92c918924f0 --unit libreac/fuzz_ctrl --build asan: 126 pcs of reac_ctrl_parse, each by +0x14b0
   (0x82000 -> 0x834b0 = REAC_CTRL_PARSE, reac_ctrl_parse+off on both sides), __asan_memset 0x51c98 -> 0x524c4,
   .str.4 135200 -> 135648 (= REAC_CTRL_PARSE_BC 0x211e0), the image bound 0x5ea000 -> 0x5ee000 (= IMG_LEN of
   reac_ctrl_parse_c.v); the side-stack offsets 1085440 / 2134016 kept by 23 identity --resolve lines (25 numerals), 1048576 and
   131072 kept (SIZES_KEEP); 0 UNMAPPED. Every moved pc was checked back against fuzz_ctrl.debug's symbol table and
   against this unit's lib/A/Prog/reac_ctrl_parse.v. The fuzz_grant file is itself the port of this unit's image-A
   proof lib/A/Prog/reac_ctrl_parse.v (a working branch 3848e05c646, here by path), in the manner of
   lib/B/Prog/reac_ctrl_parseF.v.
   Changes to the moved text (none moves an address):
   - the callees are this unit's image-A footprint forms: the bcmp wrapper's is its owner's published
     bcmp_wrap_contract_F (lib/A/Prog/bcmp_wrap_c.v); __asan_memset and __asan_memcpy are a Theorem Labs lane's shared texts
     asan_memset_contract_F / asan_memcpy_contract_F (lib/A/Prog/asan_memset_cF.v / asan_memcpy_cF.v of
     a working branch 78b8d116a58, with IMG_LO / IMG_HI of lib/A/Prog/ImgBounds.v and sh_word_rng of
     lib/A/Prog/rng_asan.v; imported before reac_ctrl_parse_c.v, whose sh_lo / sh_len the statement uses);
     __asan_stack_malloc_1 is a Theorem Labs lane's asan_stack_malloc_1_contract_F (lib/A/Prog/asan_stack_malloc_cF.v), the
     NARROW form (a Theorem Labs lane's asan_stack_malloc_contract_F_narrow, a working branch 062bf770c5b
     fuzz_knock lib/A/Prog/asan_stack_malloc_F.v:694-721) with image A's constants; kind_of_link1 by kind_of_link1F.v
     (proved, used). Each call site discharges its callee's premises in that callee's order: the buffers' 8-aligned
     shadow word covers from the quantified covers (shkov), the runtime words [RT_LO, RT_HI) inside the image;
   - the statement has no premise on the whole side stack [FS, FS + FS_SIZE): the narrow __asan_stack_malloc_1 asks
     for the side stack's header [FS, fs_frame FS 0 0) and the class-1 frame area (rcpF_frame_area) instead;
   - this unit's sh_lo / sh_len (reac_ctrl_parse_c.v) are the plain aligned covers: rcpF_cov / rcpF_kov are
     lib/B/Prog/reac_ctrl_parseF.v's, and fuzz_grant's rcpF_kov_sh is replaced by rcpF_kov8 (the bcmp wrapper's
     8 * (y / 8) cover form);
   - the free-frame side-stack lemmas are this unit's RcAsanFP.v / RcAsanFPLib.v (fuzz_grant's RcAsanFPX.v /
     RcAsanFPLibX.v: fpx_outside_In -> outside_In).
   The window's metadata: the run reads and writes the metadata of its real-stack frame [A - 128, A) only
   (A = (S - 128) / 32 * 32, S - 160 < A <= S - 128), so the aligned cover SKW is [S - 288, S - 128) only
   (rcpF_win_kov), as on image B.
   rule 24 (proof-index lookup 2026-10-28, briefs/lookup-parsexf.txt): the 12 released files named
   reac_ctrl_parse are plain / UBSAN builds of other units (no asan runtime, no footprint form); none is portable.
   Donor header follows. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcLib RcParse RcParseLib RcAsan RcAsanLib RcBoxLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c memcmp_c bcmp_wrap_c kind_of_link1_c kind_of_link1F
  asan_memset_cF asan_memcpy_cF reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_cF.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.
(* Route (C): the shadow region form and the callees' `_on` / `_F_on` statement leaves. Required here, after StepF (so
   StepF's step stays the one in scope) and BEFORE this file's Local store hooks, so those hooks stay the ones in force
   below whatever these modules load. __asan_stack_malloc_1's `_F_on` form is a Theorem Labs lane's asan_stack_malloc_cF_on.v
   (never restated here). Some of these leaves open bv_scope; this file's arithmetic is Z's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c_on asan_stack_malloc_cF_on
  asan_memset_c_on asan_memcpy_c_on asan_memset_cF_on asan_memcpy_cF_on bcmp_wrap_c_on sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.ShadowRwOnK.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The footprint forms of the four callees this proof assumes (the Section hypotheses SMAL, HMSET, HMCPY, HBCMPW
   below). __asan_memset and __asan_memcpy: a Theorem Labs lane's shared asan_memset_contract_F / asan_memcpy_contract_F
   (asan_memset_cF.v / asan_memcpy_cF.v, imported above), whose asan_memset_contract_of_F / asan_memcpy_contract_of_F
   give the old contracts back at RNG_all; each call site discharges their footprint premises in their order:
   rng_bytes, the image [IMG_LO, IMG_HI), the helper's window, the buffers, and the 8-aligned shadow word span
   (sh_word_rng of rng_asan.v) of each buffer and of the helper's window. __asan_stack_malloc_1: a Theorem Labs lane's
   asan_stack_malloc_1_contract_F (asan_stack_malloc_cF.v, imported above), see below. The fifth
   callee, kind_of_link1, is proved in footprint form in this unit (kind_of_link1F.v). *)

(* The bcmp wrapper: its owner's published footprint form, bcmp_wrap_contract_F of lib/A/Prog/bcmp_wrap_c.v (imported
   above), and its bcmp_wrap_contract_of_F there.  The premises of bcmp_wrap_contract are unchanged, then: the
   footprint is decided byte by byte, the image, the stack window [sp - BCMP_WRAP_K, sp), the N bytes at each of the
   two buffers and the 8-ALIGNED shadow word cover of each, written 8 * (y / 8). *)

(* __asan_stack_malloc_1 in footprint form: a Theorem Labs lane's asan_stack_malloc_1_contract_F of
   lib/A/Prog/asan_stack_malloc_cF.v 9fb4a9d0c85 (the blob this tree had at release c5e779efe8c) (a working branch af764b88895, imported above), the
   text of record of fs_shadow_area / asan_stack_malloc_contract_F (a Theorem Labs lane 12:16Z), not a local copy.  It is the NARROW
   text, asan_stack_malloc_contract_F_narrow at lines 694-721 of
     git show 062bf770c5b:proofs/libreac/fuzz_knock/lib/A/Prog/asan_stack_malloc_F.v
   (the canonical wide text of 31a0b55aa13 fuzz_scene asan_stack_malloc_cF.v with its one side-stack premise
   rng RNG FS FS_SIZE replaced by two pieces) with image A's names.
   The premises of asan_stack_malloc_contract are unchanged, then one rng premise per region the call reads or writes:
   the image [IMG_LO, IMG_HI); the stack window [S0 - K, S0); the five runtime pointer cells read through DT, TS, C, T
   and DB; the side stack's header [FS, fs_frame FS 0 0) (hint words, the words at FS + 88 and FS + 96, flag bytes of
   every class); the class-c frame area [fs_frame FS c 0, fs_frame FS c 0 + 2^20); the shadow of that frame area
   (fs_M c frames of fs_B c bytes, so fs_shadow_area c shadow bytes from its shadow_addr); the thread-pointer cells
   [TP - 88, TP - 80) and [TP - 8, TP + 16).  The form speaks only of the classes 0..10 (its first premise).  It is the
   Section hypothesis SMAL below. *)

(* The old contract at class 1 is the footprint form at RNG_all: the bounds of every rng premise come from the
   premises the old contract already carries (the window, fs_place for the side stack's header, its class-1 frame area
   and that area's shadow, the bytes_at of asan_tls_cells for the thread cells), so the _F form asks for nothing new. *)
Lemma asan_stack_malloc_1_contract_of_F :
  asan_stack_malloc_1_contract_F -> asan_stack_malloc_1_contract.
Proof.
  unfold asan_stack_malloc_1_contract_F, asan_stack_malloc_contract_F,
    asan_stack_malloc_1_contract, asan_stack_malloc_contract. cbv zeta.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo FS h DT TS C T DB k flags HL HL8 HC HSW MI HT H7 HTP HP H88 H96 HH HFl HFln HFb ST HLK HFS HAPP HDJ.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5. unfold ASAN_STACK_MALLOC_K in HFS.
  pose proof HT as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
                    & A18 & A19).
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  apply (evtF_evt rsegs RNG_all).
  apply (HF (proj1 (Nat.leb_le 1 10) eq_refl) RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS h DT TS C T DB k flags); try assumption.
  - (* image *) apply rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* stack window *) apply rng_all; unfold ASAN_STACK_MALLOC_K; lia.
  - (* DT + 8 *) destruct A4 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* TS + 8 k *) destruct A9 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* C + 152 *) destruct A10 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* T + 48 *) destruct A11 as (tb & te & (Ha & Hb & _)).
    rewrite length_app, !length_le8 in Hb. apply rng_all; lia.
  - (* DB + 24 *) destruct A19 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* side-stack header *) apply rng_all; rewrite ?E0; lia.
  - (* class-1 frame area *) apply rng_all; rewrite ?E1; lia.
  - (* shadow of the class-1 frame area *)
    change (fs_shadow_area 1) with 131072. rewrite E1. unfold shadow_addr, ASAN_K.
    pose proof (Z.div_mod (FS + 1085440) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (FS + 1085440) 8 ltac:(lia)) as M.
    apply rng_all; lia.
  - (* TS cell at TP - 88 *) destruct A8 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* DT, side-stack and DB cells at TP - 8 .. TP + 16 *)
    destruct A3 as (Ha & _). destruct A17 as (_ & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
Qed.



(* reac_ctrl_parse, image A (asan, entry 0x83578): reac_ctrl_parse_holds (the contract of
   lib/A/Prog/reac_ctrl_parse_c.v) from the contracts of __asan_stack_malloc_1, __asan_memset, __asan_memcpy, the
   bcmp wrapper and kind_of_link1. The plain proof (lib/Prog/reac_ctrl_parse.v) with this build's ASan frame: the
   class-1 frame request, the 128-byte frame words and their shadow, the shadow check before each instrumented load
   and store (each passes from the addressable-range premises, so the errpath_* report is not reached), and the
   runtime state (asan_cells, shadow_rw, the window addressable, fp, tls) carried across the calls. *)

(* Every byte readable in m is readable in m'. *)
Definition rd_mono (m m' : word -> option byte) : Prop :=
  forall x : word, (exists b, mrd rsegs m x = Some b) -> exists b, mrd rsegs m' x = Some b.

Lemma rd_mono_refl : forall m, rd_mono m m.
Proof. intros m x H. exact H. Qed.

Lemma rd_mono_trans : forall m1 m2 m3, rd_mono m1 m2 -> rd_mono m2 m3 -> rd_mono m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.

Lemma wtm_cases : forall bs m (a x : word), write_to_mem m a bs x = m x \/ exists v, write_to_mem m a bs x = Some v.
Proof.
  induction bs as [|b bs IH]; intros m a x; cbn [write_to_mem]; [left; reflexivity|].
  destruct (IH (fun y => if bv_eqb y a then Some b else m y) (a + 1)%bv x) as [E|E]; [|right; exact E].
  rewrite E. destruct (bv_eqb x a); [right; eexists; reflexivity | left; reflexivity].
Qed.

Lemma rd_mono_write : forall m0 m a bs, rd_mono m0 m -> rd_mono m0 (write_to_mem m a bs).
Proof.
  intros m0 m a bs H x Hx. destruct (H x Hx) as [v Hv]. unfold mrd in *.
  destruct (wtm_cases bs m a x) as [E|[w E]]; rewrite E; [exists v; exact Hv | exists w; reflexivity].
Qed.

Lemma rd_mono_munch : forall W m m', munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> exists b, mrd rsegs m' x = Some b) -> rd_mono m m'.
Proof.
  intros W m m' Hm H x Hx. destruct (rc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - unfold mrd in *. rewrite (Hm x Ho). exact Hx.
  - exact (H x Ho).
Qed.

Lemma stk_mono : forall m m' lo hi, stk rsegs m lo hi -> wmono rsegs m m' -> rd_mono m m' -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hw Hr. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma stk_sub : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  stk rsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' H Hlo Hhi Hle.
  destruct (stk_split rsegs m lo hi' hi H ltac:(lia)) as [H1 _].
  destruct (stk_split rsegs m lo lo' hi' H1 ltac:(lia)) as [_ H2]. exact H2.
Qed.

(* Route (C) (a Theorem Labs lane 09:20Z, form lib/A/ShadowRwOn.v): shadow_rw_mono for any shadow region P; the `_on` form carries
   the proof and shadow_rw_mono is its corollary. *)
Lemma shadow_rw_mono_on : forall (P : Z -> Prop) m m', shadow_rw_on P m -> wmono rsegs m m' -> rd_mono m m' ->
  shadow_rw_on P m'.
Proof.
  intros P m m' H Hw Hr a Hp Ha. destruct (H a Hp Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma shadow_rw_mono : forall m m', shadow_rw m -> wmono rsegs m m' -> rd_mono m m' -> shadow_rw m'.
Proof.
  intros m m' H Hw Hr.
  exact (shadow_rw_of_on_all m' (shadow_rw_mono_on _ m m' (shadow_rw_on_of_shadow_rw _ m H) Hw Hr)).
Qed.

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H Ha Hn; [exact I|].
  destruct H as [H1 H2]. split; [lia | eapply IH; eauto].
Qed.

Lemma asan_cells_kept : forall W ma mb, asan_cells ma -> munch W ma mb ->
  disjoint_from W RT_LO (RT_HI - RT_LO) -> asan_cells mb.
Proof.
  intros W ma mb AC MU D. unfold asan_cells, RT_LO, RT_HI in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply bytes_at_transport; [eassumption | exact MU |]);
    (eapply disjoint_from_sub; [exact D | |]); rewrite ?length_le8, ?length_le4; cbn [length];
    unfold CELL_K, UAR, INITED, REPLACE, CANPOISON, HIEND, MIDBEG, MIDEND, REAL_MEMCPY, REAL_MEMSET,
      GOT_CELL_K, GOT_UAR, GOT_REPLACE, GOT_HIEND, GOT_MIDBEG, GOT_MIDEND, GOT_REAL_MEMSET; lia.
Qed.

Lemma fs_place_mono : forall m m' FS, fs_place m FS -> wmono rsegs m m' -> rd_mono m m' -> fs_place m' FS.
Proof.
  intros m m' FS (P1 & P2 & P3 & P4 & P5) Hw Hr. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|]. exact (stk_mono m m' _ _ P5 Hw Hr).
Qed.

Lemma wv_store_ok : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2^64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

Lemma stk_wv : forall m lo hi a, stk rsegs m lo hi -> lo <= a < hi -> wview rsegs m (wa a) <> None.
Proof. intros m lo hi a (_ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

Lemma bytes_keep : forall m m' A bs, bytes_at rsegs m A bs ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) -> bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & H) Hk. split; [lia|]. split; [lia|]. intros i Hi. rewrite Hk by lia. apply H, Hi.
Qed.

Lemma addr_keep : forall m m' p n, addressable m p n ->
  (forall i, 0 <= i < n -> mrd rsegs m' (wa (shadow_addr (p + i))) = mrd rsegs m (wa (shadow_addr (p + i)))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & He & HA) Hk. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. rewrite Hk by exact Hi.
  split; [exact Hb | exact Hok].
Qed.

Lemma app_not_shadow : forall x y, app_mem x -> in_shadow y -> x <> y.
Proof.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia.
Qed.

Lemma sh_range : forall L H x, L mod 8 = 0 -> H mod 8 = 0 ->
  (shadow_addr L <= shadow_addr x < shadow_addr H <-> L <= x < H).
Proof. intros L H x HL HH. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma sh_range8 : forall fr x, fr mod 8 = 0 ->
  (shadow_addr fr <= shadow_addr x < shadow_addr fr + 8 <-> fr <= x < fr + 64).
Proof. intros fr x Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma sh_add8 : forall fr i, fr mod 8 = 0 -> shadow_addr (fr + 8 * i) = shadow_addr fr + i.
Proof. intros fr i Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia.
  rewrite Z.mod_small by lia. rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_nonneg' : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma bytes_le_to_Z_cons' : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg' bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z' : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons'.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg' bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma rd8_le8 : forall m a, 0 <= a -> a + 8 <= 2^64 ->
  (forall i, 0 <= i < 8 -> exists b, mrd rsegs m (wa (a + i)) = Some b) -> exists w, bytes_at rsegs m a (le8 w).
Proof.
  intros m a Ha Hl H.
  destruct (H 0 ltac:(lia)) as [b0 E0]. destruct (H 1 ltac:(lia)) as [b1 E1].
  destruct (H 2 ltac:(lia)) as [b2 E2]. destruct (H 3 ltac:(lia)) as [b3 E3].
  destruct (H 4 ltac:(lia)) as [b4 E4]. destruct (H 5 ltac:(lia)) as [b5 E5].
  destruct (H 6 ltac:(lia)) as [b6 E6]. destruct (H 7 ltac:(lia)) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (EL : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite <- store_bytes_8. cbn [width_bytes]. rewrite unsigned_lit_wrap.
    rewrite Z_to_le_bytes_mod by (cbn; lia).
    exact (Z_to_le_bytes_to_Z' [b0; b1; b2; b3; b4; b5; b6; b7]). }
  rewrite EL. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error]; simpl Z.of_nat;
    [rewrite Z.add_0_r in E0; replace (a + Z.of_nat 0) with a by lia; exact E0
    | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
Qed.

Lemma rd_of_bytes : forall m A bs, bytes_at rsegs m A bs ->
  forall y, A <= y < A + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa y) = Some b.
Proof.
  intros m A bs (Ha & Hl & H) y Hy. pose proof (H (Z.to_nat (y - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (y - A))) with y in E by lia.
  destruct (nth_error bs (Z.to_nat (y - A))) as [v|] eqn:En; [exists v; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma rd_of_stk : forall m lo hi, stk rsegs m lo hi -> forall y, lo <= y < hi -> exists b, mrd rsegs m (wa y) = Some b.
Proof. intros m lo hi (_ & _ & H) y Hy. exact (proj2 (H y Hy)). Qed.

Lemma not_outside_in : forall W x, ~ outside W x -> exists r, In r W /\ fst r <= x < snd r.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z.le_gt_cases lo x); destruct (Z.lt_ge_cases x hi).
  - exists (lo, hi). split; [left; reflexivity | cbn; lia].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
Qed.

Lemma rd_mono_list : forall W m m', munch W m m' ->
  Forall (fun r => forall y, fst r <= y < snd r -> exists b, mrd rsegs m' (wa y) = Some b) W -> rd_mono m m'.
Proof.
  intros W m m' Hm HF. apply (rd_mono_munch W m m' Hm). intros x Hx.
  destruct (not_outside_in W _ Hx) as (r & Hr & Hin). rewrite Forall_forall in HF.
  pose proof (HF r Hr (bv_unsigned x) Hin) as R. unfold wa in R. rewrite Z_to_bv_lit_self in R. exact R.
Qed.


Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [lib.Lib.Frame.inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* A one-byte store of a zero-extended frame byte writes [b], not le1 (zxb b): fold it before the cells are
   updated (as lib/Prog/reac_ctrl_parse.v does). *)
Lemma rcp_sx32 : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold sx32. rewrite unsigned_lit by lia. rewrite rc_swrap_small by lia. reflexivity. Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The shadow covers, carried through the proof as quantified facts.  Z.div is opaque to lia, and a GROUND rng
   premise whose bounds hold a division makes every later lia pay for that division's Euclidean equations, so the
   consequences of the statement's 8-aligned shadow word covers are drawn once here, each in a context with no other
   division, and used through shcov (the shadow byte of one checked byte), shblk (the i-th shadow byte of an
   8-aligned block) and shkov (the aligned cover a callee's _F contract names). *)
Definition shcov (RG : ExecF.footprint) (p n : Z) : Prop :=
  forall x, p <= x < p + n -> ExecF.rng RG (x / 8 + ASAN_K) 1.
Definition shblk (RG : ExecF.footprint) (p k : Z) : Prop :=
  forall i, 0 <= i <= k -> ExecF.rng RG (p / 8 + ASAN_K + i) 1.
Definition shkov (RG : ExecF.footprint) (p n : Z) : Prop :=
  forall a b, p <= a -> a <= b -> b < p + n ->
    ExecF.rng RG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).

Lemma shcov_sub : forall RG p n p' n', shcov RG p n -> p <= p' -> p' + n' <= p + n -> shcov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma shkov_sub : forall RG p n p' n', shkov RG p n -> p <= p' -> p' + n' <= p + n -> shkov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 a b H3 H4 H5. apply H; lia. Qed.

Lemma rcpF_floor8 : forall y, y / 8 * 8 <= y <= y / 8 * 8 + 7.
Proof. intros y. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. Qed.

(* The statement's aligned shadow word cover of [p, p + n) gives the shadow byte of each of its bytes. *)
Lemma rcpF_cov : forall RG p n,
  ExecF.rng RG (sh_lo p) (sh_len p n) -> shcov RG p n.
Proof.
  intros RG p n H x Hx. unfold sh_len, sh_lo in H.
  eapply ExecF.rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p x 8 ltac:(lia) ltac:(lia)). pose proof (rcpF_floor8 (p / 8 + ASAN_K)). lia.
  - pose proof (Z.div_le_mono x (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (rcpF_floor8 ((p + n - 1) / 8 + ASAN_K)). lia.
Qed.

(* and the aligned cover of each of its sub-ranges. *)
Lemma rcpF_kov : forall RG p n,
  ExecF.rng RG (sh_lo p) (sh_len p n) -> shkov RG p n.
Proof.
  intros RG p n H a b H1 H2 H3. unfold sh_len, sh_lo in H.
  eapply ExecF.rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p a 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p / 8 + ASAN_K) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono b (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p + n - 1) / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma rcpF_div8 : forall z, (8 * z) / 8 = z.
Proof. intros z. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

(* The class-1 frames' shadow comes as the BYTE-exact span [shadow_addr F0, shadow_addr F1) of fp_w.  Both ends are
   the shadow byte of a 64-aligned address, so that span is a whole number of aligned shadow words and it gives the
   same two consequences.  p0 and p1 below are F0 / 64 and F1 / 64. *)
Lemma rcpF_span_cov : forall RG p0 p1,
  ExecF.rng RG (8 * p0 + ASAN_K) (8 * p1 + ASAN_K - (8 * p0 + ASAN_K)) -> shcov RG (64 * p0) (64 * p1 - 64 * p0).
Proof.
  intros RG p0 p1 H x Hx.
  assert (L1 : 8 * p0 <= x / 8).
  { pose proof (Z.div_le_mono (8 * (8 * p0)) x 8 ltac:(lia) ltac:(lia)) as D. rewrite rcpF_div8 in D. lia. }
  assert (L2 : x / 8 <= 8 * p1 - 1).
  { pose proof (Z.div_le_mono x ((8 * p1 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Lemma rcpF_span_kov : forall RG p0 p1,
  ExecF.rng RG (8 * p0 + ASAN_K) (8 * p1 + ASAN_K - (8 * p0 + ASAN_K)) -> shkov RG (64 * p0) (64 * p1 - 64 * p0).
Proof.
  intros RG p0 p1 H a b H1 H2 H3.
  assert (KA : ASAN_K = 8 * 268431360) by reflexivity.
  assert (L1 : 8 * p0 <= a / 8).
  { pose proof (Z.div_le_mono (8 * (8 * p0)) a 8 ltac:(lia) ltac:(lia)) as D. rewrite rcpF_div8 in D. lia. }
  assert (L2 : b / 8 <= 8 * p1 - 1).
  { pose proof (Z.div_le_mono b ((8 * p1 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  assert (M1 : p0 + 268431360 <= (a / 8 + ASAN_K) / 8).
  { pose proof (Z.div_le_mono (8 * (p0 + 268431360)) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite rcpF_div8 in D. lia. }
  assert (M2 : (b / 8 + ASAN_K) / 8 <= p1 + 268431360 - 1).
  { pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p1 + 268431360 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* The EXACT metadata of the window [S - 8800, S) (the statement's window premise) gives the shadow byte of each
   byte of the window, and the aligned cover of each sub-range of [S - 288, S - 128), the span of the real-stack
   frame [A - 128, A) (S - 160 < A <= S - 128): the run's only use of a window cover (rngF_frame_kov). *)
Lemma rcpF_win_cov : forall RG S, S mod 16 = 0 ->
  ExecF.rng RG (shadow_addr (S - 8800)) (shadow_addr S - shadow_addr (S - 8800)) -> shcov RG (S - 8800) 8800.
Proof.
  intros RG S H16 H x Hx. eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr; Z.div_mod_to_equations; lia.
Qed.

Lemma rcpF_win_kov : forall RG S, S mod 16 = 0 ->
  ExecF.rng RG (shadow_addr (S - 8800)) (shadow_addr S - shadow_addr (S - 8800)) -> shkov RG (S - 288) 160.
Proof.
  intros RG S H16 H a b H1 H2 H3.
  eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* The bcmp wrapper's 8-aligned shadow word cover of a non-empty sub-range [a, b] of a range with a quantified aligned
   cover, in that form's 8 * (y / 8) shape: the same aligned shadow words as shkov's. *)
Lemma rcpF_kov8 : forall RG p n a b, shkov RG p n -> p <= a -> a <= b -> b < p + n ->
  ExecF.rng RG (8 * (shadow_addr a / 8)) (8 * (shadow_addr b / 8) + 8 - 8 * (shadow_addr a / 8)).
Proof.
  intros RG p n a b H H1 H2 H3. unfold shadow_addr.
  replace (8 * ((a / 8 + ASAN_K) / 8)) with ((a / 8 + ASAN_K) / 8 * 8) by ring.
  replace (8 * ((b / 8 + ASAN_K) / 8)) with ((b / 8 + ASAN_K) / 8 * 8) by ring.
  apply H; lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* A shadow access: its address holds a division, which StepF's [alia] does not reason about, so it goes through
   StepF's acc_hint hook and closes from one of the quantified covers above. *)
Ltac rcpF_has_div E := lazymatch E with context [Z.div _ _] => idtac end.

Ltac rcpF_rng1 :=
  lazymatch goal with
  | |- ExecF.rng ?RG ?E 1 =>
      first
        [ (* the i-th shadow byte of the 8-aligned block at p *)
          match goal with H : shblk RG _ _ |- _ => apply H; lia end
        | (* the shadow byte of X, a byte of a shcov range *)
          lazymatch E with ?X / 8 + ASAN_K =>
            match goal with H : shcov RG _ _ |- _ => apply (H X); lia end end
        | (* the same two, with the address written another way *)
          match goal with H : shblk RG ?p _ |- _ =>
            replace E with (p / 8 + ASAN_K + (E - (p / 8 + ASAN_K))) by lia;
            apply H; unfold ASAN_K in *; lia end
        | lazymatch E with ?X / 8 + ?c =>
            replace E with (X / 8 + ASAN_K) by (unfold ASAN_K in *; lia);
            match goal with H : shcov RG _ _ |- _ => apply (H X); lia end end ]
  end.

(* The hook also puts two access shapes into the one StepF's literal branch matches: an address written
   [wa E] (a pointer the run loaded from a GOT word) becomes [Z_to_bv 64 E], and a closed address written with
   named constants (GOT_UAR, CELL_K, ...) becomes its literal value. *)
Ltac acc_hintF :=
  lazymatch goal with
  | |- acc_in ?RG (wa ?E, ?nn) => change (acc_in RG (Z_to_bv 64 E, nn)); solve_acc1
  | |- acc_in ?RG (Z_to_bv 64 ?E, ?nn) =>
      tryif rcpF_has_div E then
        (let nz := eval cbv in (Z.of_nat nn) in
         refine (rng_acc_litZ' RG E nz E nn nz _ (@eq_refl Z nz) (@eq_refl bool true)
                   (conj (Z.le_refl E) (Z.le_refl (E + nz))));
         rcpF_rng1)
      else
        (tryif is_closed_lits E then fail else
           (let E' := eval vm_compute in E in
            is_Zlit E'; change (acc_in RG (Z_to_bv 64 E', nn)); solve_acc1))
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.

(* The store hook of this file: the plain proof's mem_after_store_opt (reac_ctrl_parse.v: rc_le1_zxb first, then Tac.v's
   fix_lit_store) on evtF goals. It folds Z_to_le_bytes of a literal into le8 / le4 / le2 / le1 as Tac's
   fix_lit_store does, and it does not run StepF's norm_lit_store_bytes, whose le1 (Z_to_bv 64 z) -> [Z_to_bv 8 z]
   folding would leave nothing for the script's own `rewrite rc_le1_lit` (sstep). As lib/B/Prog/reac_ctrl_parseF.v. *)
Ltac rcpF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac rcpF_store_opt :=
  try rewrite rc_le1_zxb;
  try rcpF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= rcpF_store_opt.

Lemma bytes_ro : forall m A c, bytes_at rsegs m A (cbytes c) -> cell_wf c -> ro_cells rsegs m A [c].
Proof. intros m A c H Hw. split; [split; [exact Hw | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H]. Qed.
Lemma bytes_ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. exact (bytes_ro m A (C8 v) H I). Qed.
Lemma bytes_ro4 : forall m A v, bytes_at rsegs m A (le4 v) -> ro_cells rsegs m A [C4 v].
Proof. intros m A v H. exact (bytes_ro m A (C4 v) H I). Qed.

(* ----- generic shadow helpers (as in reac_ctrl_classify_box_frame.v) ----- *)

Lemma acl_app_in : forall m p nn i, addressable m p nn -> 0 <= i < nn -> app_mem (p + i).
Proof. intros m p nn i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma acl_app_not_shadow : forall x, app_mem x -> in_shadow x -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia. Qed.

Lemma acl_addr_sub : forall m p nn p' n', addressable m p nn -> p <= p' -> 0 <= n' -> p' + n' <= p + nn ->
  addressable m p' n'.
Proof.
  intros m p nn p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma acl_addr_join : forall m p nn n', addressable m p nn -> addressable m (p + nn) n' -> 0 <= n' ->
  addressable m p (nn + n').
Proof.
  intros m p nn n' (H0 & Hn & He & HA) (H0' & Hn' & He' & HA') Hn''.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i nn) as [L|L]; [apply HA; lia|].
  replace (p + i) with (p + nn + (i - nn)) by lia. apply HA'. lia.
Qed.

Lemma acl_addr_munch : forall W m m' p nn, addressable m p nn -> munch W m m' ->
  (forall i, 0 <= i < nn -> outside W (shadow_addr (p + i))) -> addressable m' p nn.
Proof.
  intros W m m' p nn (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

Lemma acl_rw : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hwm Ho. split; [split; [exact Hwf|]|].
  - eapply fl_bytes; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Ho.
  - eapply wr_at_transport; eassumption.
Qed.

Lemma acl_shadow : forall mc p nn j w X, addressable mc p nn -> 0 <= j -> 1 <= w -> j + w <= nn ->
  X mod 8 + w <= 8 -> X = p + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc p nn j w X HA Hj Hw Hjw Hm ->.
  pose proof (rt_shadow_rd mc p nn [] HA (fun _ _ => I)) as HSR.
  pose proof (rt_addressable mc p nn HA) as HAD.
  destruct (asan_shadow_read rsegs mc ASAN_K p nn [] j HSR ltac:(lia)) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [|apply rc_byte_signed].
  exact (asan_check_lt rsegs mc ASAN_K p nn j w k HAD Hj Hw Hjw Hm BK).
Qed.

Lemma acl_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.

Lemma acl_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma acl_out_app_inv : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
Qed.

Lemma acl_sh_out : forall x a b, app_mem x -> 0 <= a -> b <= APPMEM_END -> ~ (shadow_addr a <= x < shadow_addr b).
Proof.
  intros x a b Hx Ha Hb. unfold shadow_addr.
  pose proof (Z.div_pos a 8 Ha ltac:(lia)) as H1.
  pose proof (Z.div_le_mono b APPMEM_END 8 ltac:(lia) Hb) as H2.
  replace (APPMEM_END / 8) with 0x100000000000 in H2 by reflexivity.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma acl_win_sh : forall x lo hi, lo mod 8 = 0 -> ~ (lo <= x < hi) ->
  ~ (shadow_addr lo <= shadow_addr x < shadow_addr hi).
Proof.
  intros x lo hi Hm Hx [H1 H2]. destruct (Z_lt_le_dec x lo) as [L|L].
  - pose proof (acl_sh_lt x lo Hm L). lia.
  - pose proof (acl_sh_ge x hi ltac:(lia)). lia.
Qed.

Lemma acl_frame_mod8 : forall FS, FS mod 4096 = 0 -> fs_frame FS 1 0 mod 8 = 0.
Proof.
  intros FS H. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

Lemma acl_S_mod8 : forall S j, S mod 16 = 0 -> j mod 8 = 0 -> (S - j) mod 8 = 0.
Proof. intros S j H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma acl_mod_al : forall x j w, x mod 4 = 0 -> 0 <= j -> j mod 4 + w <= 4 -> (x + j) mod 8 + w <= 8.
Proof. intros x j w H Hj Hw. Z.div_mod_to_equations. lia. Qed.

Lemma acl_mod_al0 : forall x, x mod 4 = 0 -> x mod 8 + 4 <= 8.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma acl_bytes_rd : forall mc A bs x, bytes_at rsegs mc A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs mc (wa x) = Some b.
Proof.
  intros mc A bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E.
  - exists b. rewrite <- E, <- H by lia. f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

Ltac steps_to P :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
  | _ => step; steps_to P
  end.

(* ----- shadow-check tactics (as in reac_ctrl_classify_box_frame.v / declaration_of.v) ----- *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

(* A shadow check of the access of w bytes at X (RX : 0 <= X < 2^64): SH gives the shadow byte k, its read at
   X / 8 + ASAN_K and the check fact (k = 0, or X mod 8 + (w - 1) < k); `pre` steps to the shadow address,
   then the load of k and `bnez` go on when k = 0; else the slow path `andi r, X, 7` (and `addi r, r, w - 1` by
   `extra`) and `blt r, k` go on as the check passes. The register r is generalized at the join, and the call of
   __asan_report_* is not reached. *)
Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm (if _ then _ else ?B) ?fcc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs rgq Q (MS (bvmap_set r rr R) Fm B fcc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac pre_no X RX := idtac.
Ltac no_extra X := idtac.
Ltac add1 X :=
  step; let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
  rewrite ?(unsigned_lit (X mod 8)) by (clear -MB; lia); clear MB.
Ltac add3 X :=
  step; let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
  rewrite ?(unsigned_lit (X mod 8)) by (clear -MB; lia); clear MB.

(* The 16 shadow bytes of the frame [shadow_addr fra, + 16) are in the shadow region: the frame is low or high
   application memory, so its shadow is in the low or high shadow. *)
Lemma frame_shadow_in : forall fra i,
  0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
  2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
  0 <= i < 16 -> in_shadow (fra / 8 + ASAN_K + i).
Proof.
  intros fra i H0 HFRA SHlo SHhi Hi.
  unfold in_shadow, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
  destruct HFRA as [L|H]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

(* Route (C): the frame's 16 shadow bytes, the only shadow bytes shadow16_stk takes from its shadow premise. *)
Definition shadow16_stk_shadow_R (fra a : Z) : Prop := fra / 8 + ASAN_K <= a < fra / 8 + ASAN_K + 16.

(* shadow_rw_on of the frame's 16 shadow bytes gives a writable+readable stk over them. *)
Lemma shadow16_stk_on : forall mc fra,
  shadow_rw_on (shadow16_stk_shadow_R fra) mc -> 0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
  2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
  stk rsegs mc (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16).
Proof.
  intros mc fra SR H0 HFRA SHlo SHhi. split; [lia|]. split; [lia|].
  intros a Ha. apply (SR a); [unfold shadow16_stk_shadow_R; lia|].
  replace a with (fra / 8 + ASAN_K + (a - (fra / 8 + ASAN_K))) by lia.
  apply frame_shadow_in; [exact H0 | exact HFRA | exact SHlo | exact SHhi | lia].
Qed.

(* shadow_rw gives a writable+readable stk over the frame's 16-byte shadow region. *)
Lemma shadow16_stk : forall mc fra,
  shadow_rw mc -> 0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
  2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
  stk rsegs mc (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16).
Proof. intros mc fra SR. exact (shadow16_stk_on mc fra (shadow_rw_on_of_shadow_rw _ mc SR)). Qed.

(* The box of the class-1 frame lives at fra + 32; its 36 bytes are addressable from the shadow bytes the frame
   poisoning wrote: granules 4..7 (fra + 32 .. fra + 64) are zero, granule 8 (fra + 64 .. fra + 72) is 4, so the
   first 4 bytes of it are addressable. *)
Lemma frame_shadow_addr : forall mc fra,
  0 <= fra -> fra mod 8 = 0 -> fra + 68 <= APPMEM_END ->
  (forall i, 0 <= i < 36 -> app_mem (fra + 32 + i)) ->
  (forall g, 4 <= g <= 7 -> exists b, mrd rsegs mc (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0) ->
  (exists b, mrd rsegs mc (wa (fra / 8 + ASAN_K + 8)) = Some b /\ bv_signed b = 4) ->
  addressable mc (fra + 32) 36.
Proof.
  intros mc fra Hfra0 Hmod Hend Hap Hz H8.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
  intros i Hi. unfold addr_byte. split; [apply Hap; exact Hi|].
  assert (ESH : shadow_addr (fra + 32 + i) = fra / 8 + ASAN_K + (32 + i) / 8).
  { unfold shadow_addr.
    replace (fra + 32 + i) with ((32 + i) + fra / 8 * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  destruct (Z_lt_le_dec i 32) as [L|L].
  - assert (Hg : 4 <= (32 + i) / 8 <= 7) by (Z.div_mod_to_equations; lia).
    destruct (Hz ((32 + i) / 8) Hg) as (b & Hb & Hs).
    exists b. rewrite ESH. split; [exact Hb|]. unfold shadow_ok. left. exact Hs.
  - assert (Eg : (32 + i) / 8 = 8) by (Z.div_mod_to_equations; lia).
    destruct H8 as (b & Hb & Hs). exists b. rewrite ESH, Eg. split; [exact Hb|].
    unfold shadow_ok. right. split; [|lia].
    assert (Em : (fra + 32 + i) mod 8 = i - 32)
      by (replace (fra + 32 + i) with ((32 + i) + fra / 8 * 8) by (Z.div_mod_to_equations; lia);
          rewrite Z.mod_add by lia; Z.div_mod_to_equations; lia).
    rewrite Em, Hs. lia.
Qed.

(* After the release un-poisons the whole frame to shadow 0, its 128 bytes are addressable. *)
Lemma frame_all_addr : forall mc fra,
  0 <= fra -> fra mod 8 = 0 -> fra + 128 <= APPMEM_END ->
  (forall i, 0 <= i < 128 -> app_mem (fra + i)) ->
  (forall g, 0 <= g <= 15 -> exists b, mrd rsegs mc (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0) ->
  addressable mc fra 128.
Proof.
  intros mc fra Hf0 Hmod Hend Hap Hz.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
  intros i Hi. unfold addr_byte. split; [apply Hap; exact Hi|].
  assert (ESH : shadow_addr (fra + i) = fra / 8 + ASAN_K + i / 8).
  { unfold shadow_addr. replace (fra + i) with (i + fra / 8 * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  assert (Hg : 0 <= i / 8 <= 15) by (Z.div_mod_to_equations; lia).
  destruct (Hz (i / 8) Hg) as (b & Hb & Hs).
  exists b. rewrite ESH. split; [exact Hb|]. unfold shadow_ok. left. exact Hs.
Qed.

(* The tls premise at the frame release: the run wrote only W, fp_w cs FS and Y (the thread cells are apart from the
   last two), so the thread cells and the pointers read from them are those of m (as in fl_fp_ret). *)
Lemma acl_tls_ret : forall cs m m' TP FS lo hi W D Y Wm,
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y)) ->
  munch Wm m m' -> sub_fp Wm (W ++ fp_w cs FS ++ Y) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y).
Proof.
  intros cs m0 m' TP FS lo hi W D Y Wm (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Htls Hm Hs DT TS C T DB k HT.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a b x (Htls _ _ _ _ _ _ HT0) Hin Hx). }
  destruct (fl_tls_same m0 m' Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact (Htls _ _ _ _ _ _ HT0).
Qed.

(* Route (C): the one shadow byte sh_store_ok takes from its shadow premise. *)
Definition sh_store_ok_shadow_R (a x : Z) : Prop := x = a.

(* A shadow byte is writable: shadow_rw_on of that byte gives its wview. *)
Lemma sh_store_ok_on : forall mc a, shadow_rw_on (sh_store_ok_shadow_R a) mc -> in_shadow a -> 0 <= a ->
  a + 1 <= 2^64 -> store_ok rsegs mc (wa a) 1 = true.
Proof.
  intros mc a SR Hin Ha Hb.
  eapply wv_store_ok with (m := mc) (n := 1%nat);
    [ intros i Hi; replace (a + i) with a by lia; exact (proj1 (SR a eq_refl Hin))
    | apply wmono_refl | lia | lia ].
Qed.

(* A shadow byte is writable: shadow_rw gives its wview. *)
Lemma sh_store_ok : forall mc a, shadow_rw mc -> in_shadow a -> 0 <= a -> a + 1 <= 2^64 ->
  store_ok rsegs mc (wa a) 1 = true.
Proof. intros mc a SR. exact (sh_store_ok_on mc a (shadow_rw_on_of_shadow_rw _ mc SR)). Qed.

(* A byte array kept by a run that wrote byte k of it (read back as b) and nothing else in its range. *)
Lemma bytes_at_munch_upd : forall W m1 m2 A bs (k : nat) b,
  bytes_at rsegs m1 A bs -> munch W m1 m2 -> (k < length bs)%nat ->
  bytes_at rsegs m2 (A + Z.of_nat k) [b] ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> x <> A + Z.of_nat k -> outside W x) ->
  bytes_at rsegs m2 A (upd_bytes bs k [b]).
Proof.
  intros W m1 m2 A bs k b (Ha & Hl & H) MU Hk (_ & _ & Hb) HO.
  split; [exact Ha|]. split; [rewrite upd_bytes_length by (cbn [length]; lia); exact Hl|].
  intros i Hi. rewrite upd_bytes_length in Hi by (cbn [length]; lia).
  rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
  destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + 1)); cbn [andb].
  - replace i with k by lia. rewrite Nat.sub_diag.
    pose proof (Hb 0%nat ltac:(cbn; lia)) as E. cbn [Z.of_nat] in E. rewrite Z.add_0_r in E. exact E.
  - unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [exact (H i Hi)|].
    rewrite wa_unsigned by lia. apply HO; lia.
  - unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [exact (H i Hi)|].
    rewrite wa_unsigned by lia. apply HO; lia.
  - unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [exact (H i Hi)|].
    rewrite wa_unsigned by lia. apply HO; lia.
Qed.

(* The bytes of an updated 0/1 byte array stay 0/1 when the new bytes are 0/1. *)
Lemma upd_bytes_01 : forall bs (k : nat) b, Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) bs ->
  (b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) (upd_bytes bs k [b]).
Proof.
  intros bs k b HF Hb. unfold upd_bytes. apply Forall_app. split; [|apply Forall_app; split].
  - pose proof HF as HFa. rewrite <- (firstn_skipn k bs) in HFa. apply Forall_app in HFa. exact (proj1 HFa).
  - constructor; [exact Hb | constructor].
  - pose proof HF as HFb. rewrite <- (firstn_skipn (k + length [b])%nat bs) in HFb.
    apply Forall_app in HFb. exact (proj2 HFb).
Qed.

Lemma len_le_M : forall (fl : list byte), (length fl <= Z.to_nat (fs_M 1))%nat -> Z.of_nat (length fl) <= fs_M 1.
Proof.
  intros fl H. apply Nat2Z.inj_le in H. rewrite Z2Nat.id in H by (unfold fs_M; apply Z.pow_nonneg; lia). exact H.
Qed.

(* A byte apart from a run's writes keeps its value. *)
Lemma munch_mrd_out : forall W m1 m2 x, munch W m1 m2 -> 0 <= x < 2^64 -> outside W x ->
  mrd rsegs m2 (wa x) = mrd rsegs m1 (wa x).
Proof.
  intros W m1 m2 x MU Hx Hout. unfold mrd. rewrite (MU (wa x)); [reflexivity|].
  rewrite wa_unsigned by lia. exact Hout.
Qed.

(* ----- the free-frame side-stack premise (fpx, fp_wx of RcAsanFP.v) ----- *)

Lemma fpx_fp_nil : forall cs m TP FS lo hi W D X, fpx cs m TP FS lo hi W D X -> fp cs m TP FS lo hi W [].
Proof.
  intros cs m TP FS lo hi W D X (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & _).
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|].
  split; [exact H96|]. split; [exact HCL|]. split; [exact HFS|]. split; [exact HA|]. split; [exact HWd|].
  apply Forall_nil.
Qed.

Lemma fpx_dj : forall cs m TP FS lo hi W D X, fpx cs m TP FS lo hi W D X -> fp_dj D (fp_wx cs FS X).
Proof.
  intros cs m TP FS lo hi W D X (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD). exact HD.
Qed.

Lemma fpx_of_fp_nil : forall cs m TP FS lo hi W D X,
  fp cs m TP FS lo hi W [] -> fp_dj D (fp_wx cs FS X) -> fpx cs m TP FS lo hi W D X.
Proof.
  intros cs m TP FS lo hi W D X (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & _) HD.
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|].
  split; [exact H96|]. split; [exact HCL|]. split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HD].
Qed.

(* A point of [lo, hi) in none of the holes is inside one of the pieces that cut_ivls keeps. *)
Lemma cut_ivls0_cover : forall holes lo hi x, lo <= x < hi ->
  Forall (fun h => ~ (fst h <= x < snd h)) holes ->
  exists r, In r (cut_ivls0 lo hi holes) /\ fst r <= x < snd r.
Proof.
  induction holes as [|[a b] hs IH]; intros lo hi x Hx Hh; cbn [cut_ivls0].
  - exists (lo, hi). split; [left; reflexivity | cbn [fst snd]; lia].
  - apply Forall_cons_iff in Hh as [Hab Hhs]. cbn [fst snd] in Hab.
    destruct (Z_lt_le_dec x a) as [L|L].
    + exists (lo, Z.min a hi). split; [left; reflexivity | cbn [fst snd]; lia].
    + destruct (IH (Z.max b lo) hi x ltac:(lia) Hhs) as (r & Hr & Hrx).
      exists r. split; [right; exact Hr | exact Hrx].
Qed.

Lemma cut_ivls_cover : forall holes lo hi x, lo <= x < hi ->
  Forall (fun h => ~ (fst h <= x < snd h)) holes ->
  exists r, In r (cut_ivls lo hi holes) /\ fst r <= x < snd r.
Proof.
  intros holes lo hi x Hx Hh. destruct (cut_ivls0_cover holes lo hi x Hx Hh) as (r & Hr & Hrx).
  exists r. split; [|exact Hrx]. unfold cut_ivls, nonempty. apply filter_In. split; [exact Hr|].
  apply Z.ltb_lt. lia.
Qed.

Lemma fs_frame1 : forall FS j, fs_frame FS 1 j = FS + 1085440 + j * 128.
Proof.
  intros FS j. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. lia.
Qed.

Lemma sh_frame1 : forall FS j, shadow_addr (fs_frame FS 1 j) = shadow_addr (fs_frame FS 1 0) + 16 * j.
Proof. intros FS j. rewrite !fs_frame1. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma fs_flag1 : forall FS i, fs_flag FS 1 i = FS + 20480 + i.
Proof. intros FS i. unfold fs_flag. cbn [Z.of_nat Pos.of_succ_nat]. lia. Qed.

(* The class-1 hint word and flag array are ranges of fp_wx [1] FS X, whatever X is. *)
Lemma fp_wx_hint_flag_in : forall FS X,
  In (fs_hint FS 1, fs_hint FS 1 + 8) (fp_wx [1%nat] FS X) /\
  In (fs_flag FS 1 0, fs_flag FS 1 0 + fs_M 1) (fp_wx [1%nat] FS X).
Proof.
  intros FS X. destruct X as [|p X'].
  - change (fp_wx [1%nat] FS []) with (fp_w1 FS 1 ++ []). rewrite app_nil_r. unfold fp_w1.
    split; [left; reflexivity | right; left; reflexivity].
  - change (fp_wx [1%nat] FS (p :: X')) with (fp_wx1 FS (p :: X') 1 ++ []). rewrite app_nil_r.
    unfold fp_wx1. cbv zeta.
    split; apply in_or_app; left; [left; reflexivity | right; left; reflexivity].
Qed.

(* A byte outside fp_wx [1] FS X is outside the class-1 hint word and flag array. *)
Lemma wx_out_hint_flag : forall FS X x, outside (fp_wx [1%nat] FS X) x ->
  ~ (fs_hint FS 1 <= x < fs_hint FS 1 + 8) /\ ~ (fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1).
Proof.
  intros FS X x Hout. destruct (fp_wx_hint_flag_in FS X) as (Hh & Hf).
  exact (conj (outside_In _ x _ Hout Hh) (outside_In _ x _ Hout Hf)).
Qed.

(* A frame named by the class-1 filter of fp_wx1 is a frame of X. *)
Lemma wx_filter_in : forall (l : list (nat * Z)) ci,
  In ci (filter (fun ci => Nat.eqb (fst ci) 1) l) -> In ci l.
Proof.
  induction l as [|a l IH]; intros ci H; [exact H|].
  cbn in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    first [ destruct H as [H|H]; [left; exact H | right; exact (IH ci H)] | right; exact (IH ci H) ].
Qed.

(* A byte of a class-1 frame j that X does not name is inside fp_wx [1] FS X (the frame is not a hole). *)
Lemma fp_wx_frame_in : forall FS X j x, 0 <= j < fs_M 1 -> Forall (fun ci => snd ci <> j) X ->
  fs_frame FS 1 j <= x < fs_frame FS 1 (j + 1) -> ~ outside (fp_wx [1%nat] FS X) x.
Proof.
  intros FS X j x Hj HX Hx Hout.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  rewrite !fs_frame1 in Hx.
  destruct X as [|p X'].
  - apply (outside_In _ x (fs_frame FS 1 0, fs_frame FS 1 (fs_M 1)) Hout).
    + change (fp_wx [1%nat] FS []) with (fp_w1 FS 1 ++ []). rewrite app_nil_r. unfold fp_w1.
      right; right; left; reflexivity.
    + cbn [fst snd]. rewrite !fs_frame1. lia.
  - assert (Hcut : exists r, In r (cut_ivls (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1))
                    (map (fun j0 => (fs_frame FS 1 j0, fs_frame FS 1 (j0 + 1)))
                       (map snd (filter (fun ci => Nat.eqb (fst ci) 1) (p :: X'))))) /\ fst r <= x < snd r).
    { apply cut_ivls_cover; [rewrite !fs_frame1; lia|].
      apply Forall_forall. intros h Hh. apply in_map_iff in Hh as (j0 & <- & Hj0).
      apply in_map_iff in Hj0 as (ci & <- & Hci). apply wx_filter_in in Hci.
      rewrite Forall_forall in HX. pose proof (HX ci Hci) as Hne. cbn [fst snd]. rewrite !fs_frame1. lia. }
    destruct Hcut as (r & Hr & Hrx).
    apply (outside_In _ x r Hout); [|exact Hrx].
    change (fp_wx [1%nat] FS (p :: X')) with (fp_wx1 FS (p :: X') 1 ++ []). rewrite app_nil_r.
    unfold fp_wx1. cbv zeta. apply in_or_app. right. apply in_or_app. left. exact Hr.
Qed.

(* A shadow byte of a class-1 frame j that X does not name is inside fp_wx [1] FS X. *)
Lemma fp_wx_frame_sh_in : forall FS X j x, 0 <= j < fs_M 1 -> Forall (fun ci => snd ci <> j) X ->
  shadow_addr (fs_frame FS 1 j) <= x < shadow_addr (fs_frame FS 1 (j + 1)) -> ~ outside (fp_wx [1%nat] FS X) x.
Proof.
  intros FS X j x Hj HX Hx Hout.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  rewrite (sh_frame1 FS j), (sh_frame1 FS (j + 1)) in Hx.
  destruct X as [|p X'].
  - apply (outside_In _ x (shadow_addr (fs_frame FS 1 0), shadow_addr (fs_frame FS 1 (fs_M 1))) Hout).
    + change (fp_wx [1%nat] FS []) with (fp_w1 FS 1 ++ []). rewrite app_nil_r. unfold fp_w1.
      right; right; right; left; reflexivity.
    + cbn [fst snd]. rewrite (sh_frame1 FS (fs_M 1)). lia.
  - assert (Hcut : exists r, In r (cut_ivls (shadow_addr (fs_frame FS 1 0)) (shadow_addr (fs_frame FS 1 (fs_M 1)))
                    (map (fun j0 => (shadow_addr (fs_frame FS 1 j0), shadow_addr (fs_frame FS 1 (j0 + 1))))
                       (map snd (filter (fun ci => Nat.eqb (fst ci) 1) (p :: X'))))) /\ fst r <= x < snd r).
    { apply cut_ivls_cover; [rewrite (sh_frame1 FS (fs_M 1)); lia|].
      apply Forall_forall. intros h Hh. apply in_map_iff in Hh as (j0 & <- & Hj0).
      apply in_map_iff in Hj0 as (ci & <- & Hci). apply wx_filter_in in Hci.
      rewrite Forall_forall in HX. pose proof (HX ci Hci) as Hne. cbn [fst snd].
      rewrite (sh_frame1 FS (snd ci)), (sh_frame1 FS (snd ci + 1)). lia. }
    destruct Hcut as (r & Hr & Hrx).
    apply (outside_In _ x r Hout); [|exact Hrx].
    change (fp_wx [1%nat] FS (p :: X')) with (fp_wx1 FS (p :: X') 1 ++ []). rewrite app_nil_r.
    unfold fp_wx1. cbv zeta. apply in_or_app. right. apply in_or_app. right. exact Hr.
Qed.

(* ================= the prologue, the class-1 frame request and poisoning ================= *)

(* The narrow __asan_stack_malloc_1 form's premises on the five runtime pointer cells and the two thread-pointer
   cells, from the statement's one rng fact per cell of fp_tls. *)
Lemma rcpF_tls_rng : forall RG TP DT TS C T DB k,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_tls TP DT TS C T DB k) ->
  rng RG (bv_unsigned DT + 8) 8 /\ rng RG (bv_unsigned TS + 8 * k) 8 /\ rng RG (bv_unsigned C + 152) 8 /\
  rng RG (bv_unsigned T + 48) 16 /\ rng RG (bv_unsigned DB + 24) 8 /\ rng RG (TP - 88) 8 /\ rng RG (TP - 8) 24.
Proof.
  intros RG TP DT TS C T DB k H. unfold fp_tls in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R3 H]. apply Forall_cons_iff in H as [R4 H].
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R7 H]. apply Forall_cons_iff in H as [R8 H].
  apply Forall_cons_iff in H as [R9 H]. apply Forall_cons_iff in H as [R10 H].
  do 5 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [R16 _].
  cbn [fst snd] in R3, R4, R7, R8, R9, R10, R16.
  split; [eapply rng_sub; [exact R4 | lia | lia]|].
  split; [eapply rng_sub; [exact R8 | lia | lia]|].
  split; [eapply rng_sub; [exact R9 | lia | lia]|].
  split; [eapply rng_sub; [exact R10 | lia | lia]|].
  split; [eapply rng_sub; [exact R16 | lia | lia]|].
  split; [eapply rng_sub; [exact R7 | lia | lia]|].
  eapply rng_sub; [exact R3 | lia | lia].
Qed.

(* The narrow form's premise on the shadow of the class-1 frame area, from the statement's rng fact on the frames'
   byte-exact shadow span in fp_w [1%nat] FS: the frames span 2^20 bytes, so their shadow is fs_shadow_area 1 bytes. *)
Lemma rcpF_frame_sh : forall RG FS,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
  rng RG (shadow_addr (fs_frame FS 1 0)) (fs_shadow_area 1).
Proof.
  intros RG FS H. unfold fp_w, fp_w1 in H. cbn [flat_map app] in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [H _].
  cbn [fst snd] in H.
  replace (fs_shadow_area 1) with (shadow_addr (fs_frame FS 1 (fs_M 1)) - shadow_addr (fs_frame FS 1 0));
    [exact H|].
  rewrite (fs_frame1 FS (fs_M 1)), (fs_frame1 FS 0). change (fs_M 1) with 8192.
  change (fs_shadow_area 1) with 131072. unfold shadow_addr.
  replace (FS + 1085440 + 0 * 128) with (FS + 1085440) by lia.
  replace (FS + 1085440 + 8192 * 128) with (FS + 1085440 + 131072 * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* The narrow form's premise on the class-1 frame area, from the statement's rng fact on the frames' span in
   fp_w [1%nat] FS: fs_M 1 = 8192 frames of fs_B 1 = 128 bytes, 2^20 bytes from fs_frame FS 1 0. *)
Lemma rcpF_frame_area : forall RG FS,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
  rng RG (fs_frame FS 1 0) (2 ^ 20).
Proof.
  intros RG FS H. unfold fp_w, fp_w1 in H. cbn [flat_map app] in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [H _].
  cbn [fst snd] in H.
  replace (2 ^ 20) with (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0); [exact H|].
  rewrite (fs_frame1 FS (fs_M 1)), (fs_frame1 FS 0). change (fs_M 1) with 8192. lia.
Qed.

(* ================= the prologue, the class-1 frame request and poisoning ================= *)
Section SetupF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte) (RNG : ExecF.footprint).
  (* the callees, in their image-A footprint forms (above: __asan_memset / __asan_memcpy a Theorem Labs lane's shared texts;
     kind_of_link1's from kind_of_link1_c.v) *)
  Hypothesis SMAL : asan_stack_malloc_1_contract_F.
  Hypothesis HMSET : asan_memset_contract_F.
  Hypothesis HMCPY : asan_memcpy_contract_F.
  Hypothesis HBCMPW : bcmp_wrap_contract_F.
  Hypothesis HKOL : kind_of_link1_contract_F.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rn : 0 <= n < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis RS : 8800 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - 8800) S.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f).
  Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i.
  Hypothesis HOK : o <> 0 ->
    o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
    (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o).
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8800.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - 8800) 8800.
  Hypothesis AF0 : 50 <= n -> addressable m f 50.
  Hypothesis AO0 : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
  (* The free frames X (class-1 frames in use by the caller, flag 1 at m, index below fs_M 1) and the side-stack
     premise in the free-frame form (fpx: the data ranges are apart from fp_wx [1] FS X, which leaves out X's frames
     and their shadow). *)
  Variable X : list (nat * Z).
  Hypothesis XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X.
  Hypothesis XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X.
  Hypothesis FP0 : fpx [1%nat] m (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X.
  Hypothesis TLS0 : reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - 8800) S.

  (* ---- The footprint premises of the run.  The shadow covers are QUANTIFIED (shcov / shblk / shkov): a ground
     rng premise whose bounds hold a division would make every later lia pay for that division's Euclidean
     equations.  The ranges without a division stay ground, since StepF's solve_acc1 matches them in the
     context. SKW covers [S - 288, S - 128) only: the span of the real-stack frame [A - 128, A), its one use. ---- *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8800) 8800.
  Hypothesis SCW : shcov RNG (S - 8800) 8800.
  Hypothesis SKW : shkov RNG (S - 288) 160.
  Hypothesis RINF : 50 <= n -> rng RNG f 50.
  Hypothesis SCF : 50 <= n -> shcov RNG f 50.
  Hypothesis SKF : 50 <= n -> shkov RNG f 50.
  Hypothesis ROUT : o <> 0 -> rng RNG o 36.
  Hypothesis SCO : o <> 0 -> shcov RNG o 36.
  Hypothesis SKO : o <> 0 -> shkov RNG o 36.
  Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFSS : rng RNG FS (fs_frame FS 0 0 - FS).
  Hypothesis RFLG : rng RNG (fs_flag FS 1 0) (fs_M 1).
  Hypothesis RFRM : rng RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis RFW1 : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS).
  Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).
  Local Ltac pf_h H := let T := type of H in change (id T) in H. Local Ltac pf_uh H := lazymatch type of H with id ?T => change T in H end. Local Ltac pf_hide := try pf_h HF; try pf_h HOK; try pf_h AO0; try pf_h AF0; try pf_h RINF; try pf_h SCF; try pf_h SKF; try pf_h ROUT; try pf_h SCO; try pf_h SKO.
  (* the aligned sp (s1 after andi) *)
  Definition A : Z := (S - 128) / 32 * 32.

  Lemma HA1 : A mod 32 = 0 /\ S - 160 < A <= S - 128.
  Proof. unfold A. Z.div_mod_to_equations. lia. Qed.

  Lemma STW0 : forall a, S - 8800 <= a < S -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (stk_wv m _ _ _ ST0 Ha). Qed.

  (* The 12 saved registers, lowest address (S-96, s10) first. *)
  Definition SAVES : list cell :=
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* the writes of the run outside o: the window, the class-1 hint word, flag j, the frame and its shadow *)
  Definition Wf (fr j nn : Z) : list ivl :=
    [(S - 8800, S); (fs_hint FS 1, fs_hint FS 1 + 8); (fs_flag FS 1 j, fs_flag FS 1 j + nn);
     (fr, fr + 128); (shadow_addr fr, shadow_addr fr + 16)].

  (* The frame: real (fv = 0, fr = A - 128, sp = A - 128) or fake (fv = fr the side frame j, sp = A, the flag-byte
     address w120 at fr + 120, and frame j's flag byte 0 at m: __asan_stack_malloc_1 took a free frame, so the
     exit's clear of that flag gives back m's flag array). *)
  Definition FK (fr fv spc j nn : Z) (w120 : word) : Prop :=
    (fv = 0 /\ fr = A - 128 /\ spc = A - 128 /\ j = 0 /\ nn = 0) \/
    (0 <= j < fs_M 1 /\ fr = fs_frame FS 1 j /\ fv = fr /\ spc = A /\ w120 = Z_to_bv 64 (fs_flag FS 1 j) /\ nn = 1 /\
     bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0]).

  (* The class-1 flag bytes (each 0 or 1) and, for a side-stack frame (nn = 1), its flag-address word at fr + 120:
     what __asan_stack_malloc_1 left, and what the release at 0x83920 reads. *)
  Definition FLG (fr nn : Z) (w120 : word) (mc : word -> option byte) : Prop :=
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') /\
    (nn = 1 -> bytes_at rsegs mc (fr + 120) (le8 w120)).

  (* The output box: the frame's redzone fr + 32 when o = 0, else o. *)
  Definition OB (fr ob : Z) : Prop := (o = 0 /\ ob = fr + 32) \/ (o <> 0 /\ ob = o).

  Lemma app_range : forall Y nn, 0 < nn -> (forall i, 0 <= i < nn -> app_mem (Y + i)) ->
    Y + nn <= 2147450880 \/ 17594333495296 <= Y.
  Proof.
    intros Y nn Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (nn - 1) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
    destruct (Z.le_gt_cases (Y + nn) 2147450880) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases 17594333495296 Y) as [G|G]; [right; exact G|].
    exfalso. pose proof (H (2147450880 - Y) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. lia.
  Qed.

  (* What every frame gives: alignment, place, writable and AppMem bytes, writable shadow bytes. *)
  Lemma fk_facts : forall fr fv spc j nn w120, FK fr fv spc j nn w120 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 128 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 128 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 128 -> app_mem (fr + i)) /\
    (fr + 128 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 16 -> wview rsegs m (wa (fr / 8 + ASAN_K + i)) <> None) /\
    2147450880 <= fr / 8 + ASAN_K /\ fr / 8 + ASAN_K + 16 <= 17594333495296.
  Proof using tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd HOK AC0 AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros fr0 fv spc j nn w120 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & HAPP & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : fr0 mod 8 = 0 /\ FS + 36864 <= fr0 /\ fr0 + 128 <= A /\ (spc = A \/ spc = fr0) /\
                (forall i, 0 <= i < 128 -> wview rsegs m (wa (fr0 + i)) <> None) /\
                (forall i, 0 <= i < 128 -> app_mem (fr0 + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En & _)]; subst fr0.
      - split; [unfold A; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. unfold app_mem. right. lia.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ (14 - 1)) with 8192 in Hj. change (2 ^ 1) with 2 in *. change (2 ^ 20) with 1048576 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range fr0 128 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 16 -> fr0 / 8 + ASAN_K + i = shadow_addr (fr0 + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. rewrite B8 by exact Hi. apply (proj1 (SR0 _ (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  (* ---- The footprint of the frame __asan_stack_malloc_1 gave: its 128 bytes and its 16 shadow bytes are in RNG
     whether it is the real-stack frame (inside the window) or a side frame (inside the class-1 frames). ---- *)
  Lemma rngF_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> rng RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply rng_sub; [exact RWIN | lia | lia].
    - eapply rng_sub; [exact RFRM | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  Lemma rngF_frame_cov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shcov RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply shcov_sub; [exact SCW | lia | lia].
    - eapply shcov_sub; [exact SCFR | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  Lemma rngF_frame_kov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shkov RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply shkov_sub; [exact SKW | lia | lia].
    - eapply shkov_sub; [exact SKFR | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  (* The 8-aligned shadow word span of a sub-range [a, b] of the window that keeps 64 bytes from each end of it: inside
     the window's shadow, so in RNG byte by byte (SCW) and so as one range (RBY). The shared __asan_memset /
     __asan_memcpy contracts take it for the shadow of the helper's own window [sp - K, sp). *)
  Lemma rngF_win_sh8 : forall a b, S - 8736 <= a -> a <= b -> b < S - 64 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Proof.
    intros a b Ha Hab Hb.
    assert (HH : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    split; [unfold ASAN_K; Z.div_mod_to_equations; lia|].
    split; [unfold ASAN_K; Z.div_mod_to_equations; lia|].
    intros b' jn Hb' Hj.
    apply RBY; [unfold ASAN_K in *; Z.div_mod_to_equations; lia | unfold ASAN_K in *; Z.div_mod_to_equations; lia |].
    intros k Hk.
    assert (Hx : S - 8800 <= 8 * (b' + Z.of_nat k - ASAN_K) < S - 8800 + 8800)
      by (unfold ASAN_K in *; Z.div_mod_to_equations; lia).
    pose proof (SCW _ Hx) as H1. rewrite rcpF_div8 in H1.
    replace (b' + Z.of_nat k - ASAN_K + ASAN_K) with (b' + Z.of_nat k) in H1 by lia.
    destruct H1 as (_ & _ & H1). apply H1; lia.
  Qed.

  (* The 16 shadow bytes of the frame, at the addresses the run forms: fra / 8 + ASAN_K + i. *)
  Lemma rngF_frame_blk : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shblk RNG fra 15.
  Proof.
    intros fra fv spc j nn w120 HK.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & _).
    pose proof (rngF_frame_cov fra fv spc j nn w120 HK) as HC.
    intros i Hi. pose proof (sh_add8 fra i FR8) as Hs. unfold shadow_addr in Hs.
    replace (fra / 8 + ASAN_K + i) with ((fra + 8 * i) / 8 + ASAN_K) by lia.
    apply HC. lia.
  Qed.

  (* ---- The footprint of the output box ob: the caller's buffer at o, or the frame's redzone at fra + 32. ---- *)
  Lemma rngF_ob : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob -> rng RNG ob 36.
  Proof.
    intros fra fv spc j nn w120 ob HK HO. destruct HO as [(Ho & Eob)|(Ho & Eob)]; subst ob.
    - eapply rng_sub; [exact (rngF_frame fra fv spc j nn w120 HK) | lia | lia].
    - exact (ROUT Ho).
  Qed.

  Lemma rngF_ob_cov : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob -> shcov RNG ob 36.
  Proof.
    intros fra fv spc j nn w120 ob HK HO. destruct HO as [(Ho & Eob)|(Ho & Eob)]; subst ob.
    - eapply shcov_sub; [exact (rngF_frame_cov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SCO Ho).
  Qed.

  Lemma rngF_ob_kov : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob -> shkov RNG ob 36.
  Proof.
    intros fra fv spc j nn w120 ob HK HO. destruct HO as [(Ho & Eob)|(Ho & Eob)]; subst ob.
    - eapply shkov_sub; [exact (rngF_frame_kov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SKO Ho).
  Qed.

  (* Every flag byte X names is a byte of the class-1 flag array. *)
  Lemma x_flag_in : forall ci, In ci X ->
    fs_flag FS (fst ci) (snd ci) = fs_flag FS 1 (snd ci) /\
    fs_flag FS 1 0 <= fs_flag FS 1 (snd ci) /\ fs_flag FS 1 (snd ci) + 1 <= fs_flag FS 1 0 + fs_M 1.
  Proof.
    intros ci Hin.
    destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (Hc & _).
    pose proof (proj1 (Forall_forall _ _) XB0 ci Hin) as Hb.
    rewrite Hc. split; [reflexivity|].
    assert (EM : fs_M 1 = 8192) by reflexivity.
    rewrite !fs_flag1, EM. rewrite EM in Hb. clear -Hb. lia.
  Qed.

  (* A frame index whose flag byte is 0 at m is not an index of X: X's flags are 1 at m. *)
  Lemma x_ne_j : forall j, bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0] -> Forall (fun ci => snd ci <> j) X.
  Proof.
    intros j (_ & _ & H0). eapply Forall_impl; [|exact XF0].
    intros [c i] (Hc & (_ & _ & H1)) E. cbn [fst snd] in Hc, E, H1. subst c i.
    pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0. pose proof (H1 0%nat ltac:(cbn [length]; lia)) as A1.
    cbn [nth_error] in A0, A1. rewrite A0 in A1. injection A1 as A1.
    vm_compute in A1. discriminate.
  Qed.

  (* A data range of the caller (D: f's 50 bytes, o's record) is apart from a class-1 frame j whose flag is 0 at m:
     j is not in X, so the frame is inside fpx's footprint fp_wx [1] FS X, which D is apart from. *)
  Lemma D_apart_frame : forall a b j, In (a, b) (reac_ctrl_parse_D f n o) -> a < b ->
    0 <= j < fs_M 1 -> bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0] ->
    b <= fs_frame FS 1 j \/ fs_frame FS 1 j + 128 <= a.
  Proof.
    intros a b j Hin Hab Hj Hfl0.
    pose proof (fpx_dj _ _ _ _ _ _ _ _ _ FP0) as HDd.
    assert (E1 : fs_frame FS 1 (j + 1) = fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
    destruct (Z_le_gt_dec b (fs_frame FS 1 j)) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (fs_frame FS 1 j + 128) a) as [R|R]; [right; exact R|].
    exfalso. apply (fp_wx_frame_in FS X j (Z.max a (fs_frame FS 1 j)) Hj (x_ne_j j Hfl0)); [lia|].
    apply (fl_dj_out_r _ _ a b (Z.max a (fs_frame FS 1 j)) HDd Hin). lia.
  Qed.

  (* fp's last premise, in the free-frame form: a data range of the contract is apart from every range of
     fp_wx [1] FS X (the hint word and the flag array are two of them, fp_wx_hint_flag_in). *)
  Lemma dj_pair : forall a b c d, In (a, b) (reac_ctrl_parse_D f n o) -> In (c, d) (fp_wx [1%nat] FS X) ->
    b <= c \/ d <= a.
  Proof.
    intros a b c d H1 H2.
    pose proof (fpx_dj _ _ _ _ _ _ _ _ _ FP0) as HDd.
    unfold fp_dj in HDd. rewrite Forall_forall in HDd.
    pose proof (HDd _ H1) as H'. cbn [fst snd] in H'. rewrite Forall_forall in H'.
    pose proof (H' _ H2) as H''. cbn [fst snd] in H''. unfold RcLay.ly_dj in H''. exact H''.
  Qed.

  Definition BI (W : list ivl) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 96) SAVES.

  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (fr fv spc j nn : Z) (w120 : word) (mc : word -> option byte)
           (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      FK fr fv spc j nn w120 -> BI (Wf fr j nn) mc -> FLG fr nn w120 mc -> addressable mc (fr + 32) 36 ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                         (Z_to_bv 64 n) (Z_to_bv 64 (fr / 8 + ASAN_K)) (Z_to_bv 64 fr) (wa ASAN_K)
                         (Z_to_bv 64 (fr + 32)) s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8369c) fc None mc (seg_rom rsegs)).

  Ltac wst a nn tac :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; tac | eassumption | lia | lia ])
    end.

  Ltac wstb a nn base fact :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                  match goal with |- wview _ _ (wa ?X) <> None => replace X with (base + (X - base)) by lia end;
                  apply fact; lia
                | eassumption | lia | lia ])
    end.

  (* A tracked poison store of one shadow byte at base + off (= base + Z.of_nat nn): the stored byte joins the
     frame-shadow cells so that the box's addressability can be read back. *)
  Ltac sstep base off nn fact :=
    wstb (base + off) 1%nat base fact; step;
    replace (base + off) with (base + Z.of_nat nn) by lia;
    rewrite rc_le1_lit; mem_after_store.

  (* 0x8361c .. 0x8369c: the stack slot, the 3 frame words and the 16 shadow bytes of the frame. *)
  Lemma fwords : forall fra fv spc j nn w120 mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 : word) Q,
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> KB Q ->
    evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                       (Z_to_bv 64 n) x23 (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8361c) fc None mc (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 RWIN SCW RFRM SCFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd HOK AC0 AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 TLS0 RBY RIMG SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 Q HK HB HFL K.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSpos & _ & _ & Pfsapp & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (HHMl : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold Wf, shadow_addr in MU.
    (* the writes of this block, for carrying FLG from mc *)
    pose proof (munch_refl [(A + 24, A + 32); (fra, fra + 24); (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16)] mc) as MUf.
    wst (A + 24) 8%nat ltac:(apply STW0; lia). step. store_done.
    steps_to 0x83644.
    wstb fra 8%nat fra FW. step. store_done.
    wstb (fra + 8) 8%nat fra FW. step. store_done.
    wstb (fra + 16) 8%nat fra FW. step. store_done.
    step. step.
    rewrite (unsigned_lit fra) by lia. rewrite rc_shr3.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
      pose proof (shadow_rw_mono m mcur SR0 WM RM) as SRmc;
      pose proof (shadow16_stk mcur fra SRmc ltac:(lia) FRA ltac:(lia) ltac:(lia)) as STsh
    end.
    pose proof (stk_carve rsegs m1 (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(lia))
      as [STsh' [junkS SHC]].
    replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
    sstep (fra / 8 + ASAN_K) 0 0%nat SW.
    sstep (fra / 8 + ASAN_K) 1 1%nat SW.
    sstep (fra / 8 + ASAN_K) 2 2%nat SW.
    sstep (fra / 8 + ASAN_K) 3 3%nat SW.
    step.
    sstep (fra / 8 + ASAN_K) 12 12%nat SW.
    sstep (fra / 8 + ASAN_K) 13 13%nat SW.
    sstep (fra / 8 + ASAN_K) 14 14%nat SW.
    sstep (fra / 8 + ASAN_K) 15 15%nat SW.
    sstep (fra / 8 + ASAN_K) 8 8%nat SW.
    sstep (fra / 8 + ASAN_K) 9 9%nat SW.
    sstep (fra / 8 + ASAN_K) 10 10%nat SW.
    sstep (fra / 8 + ASAN_K) 11 11%nat SW.
    sstep (fra / 8 + ASAN_K) 4 4%nat SW.
    sstep (fra / 8 + ASAN_K) 5 5%nat SW.
    sstep (fra / 8 + ASAN_K) 6 6%nat SW.
    sstep (fra / 8 + ASAN_K) 7 7%nat SW.
    destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) => assert (FLf : FLG fra nn w120 mf) end.
    { destruct HFL as [(flg & Hfl & Hfln & HflF) Hw].
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      split.
      - exists flg. split; [|split; [exact Hfln | exact HflF]].
        eapply fl_bytes; [exact Hfl | exact MUf |].
        intros x Hx. rewrite Hfln, EFL0 in Hx. change (fs_M 1) with 8192 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; unfold FS_SIZE; clear -Hx HFSpos; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx HAlo HFSb RS; lia.
        + clear -Hx FRlo; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
      - intros En. eapply fl_bytes; [exact (Hw En) | exact MUf |].
        intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
        assert (Hxa : app_mem x) by (replace x with (fra + (x - fra)) by lia; apply FAP; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx FRhi; lia.
        + clear -Hx; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
    eapply K.
    - exact HK.
    - unfold BI, Wf, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI SV)))).
    - exact FLf.
    - apply frame_shadow_addr.
      + lia.
      + exact FR8.
      + unfold APPMEM_END in *; lia.
      + intros i Hi. replace (fra + 32 + i) with (fra + (32 + i)) by lia. apply FAP; lia.
      + intros g Hg. destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 0). split; [|reflexivity].
        assert (Hc : g = 4 \/ g = 5 \/ g = 6 \/ g = 7) by lia.
        destruct Hc as [H|[H|[H|H]]]; rewrite H;
          [ replace (fra / 8 + ASAN_K + 4) with (fra / 8 + ASAN_K + Z.of_nat 4) by lia;
            rewrite (Hr 4%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 5) with (fra / 8 + ASAN_K + Z.of_nat 5) by lia;
            rewrite (Hr 5%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 6) with (fra / 8 + ASAN_K + Z.of_nat 6) by lia;
            rewrite (Hr 6%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 7) with (fra / 8 + ASAN_K + Z.of_nat 7) by lia;
            rewrite (Hr 7%nat ltac:(cbn [length]; lia)) ]; reflexivity.
      + destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 4). split; [|reflexivity].
        replace (fra / 8 + ASAN_K + 8) with (fra / 8 + ASAN_K + Z.of_nat 8) by lia.
        rewrite (Hr 8%nat ltac:(cbn [length]; lia)). reflexivity.
  Qed.

  (* 0x83578 .. 0x8361c: the prologue, the class-1 frame request __asan_stack_malloc_1(128) and the choice of a
     side-stack frame or the real-stack fallback with its page probe. *)
  Lemma entry : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> KB Q ->
    evtF rsegs RNG Q (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m0 (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG SMAL Rf Rn Ro RS S16 ST0 MI0 Lfr AC0 SR0 HHM HAE X FP0 RIMG RWIN SCW RFSS RFRM SCFR RFW1 RTLS. clear HMSET HMCPY HBCMPW HKOL HF Hrd HOK AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 TLS0 RBY SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG SKFR. pf_hide.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    unfold REAC_CTRL_PARSE.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPm. unfold reac_ctrl_parse_W in FPm.
    assert (MU : munch [(S - 8800, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (S - 96) _ ST0c ltac:(lia)) as [STw STs].
    pose proof (stk_split rsegs m0 _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
    clear ST0c.
    carve_frame 96%nat STs.
    carve_frame 32%nat STz.
    step.
    steps_to 0x835b4.
    step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; unfold A; f_equal; f_equal; lia).
    rewrite EA.
    steps_to 0x835e0.
    step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (fl_fp [1%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0.
    destruct HCL0 as [(_ & h & flags & HH & HFl & HFln & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STw2 STz ltac:(lia)) as STzc.
    destruct (stk_split rsegs m1 _ A _ STzc ltac:(lia)) as [STA _].
    (* the thread cells' pointers at m1 are those at m (the prologue wrote only the window), so the statement's rng
       facts on the cells of fp_tls (RTLS, at m) name the cells the frame routine reads *)
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd0 & _).
    pose proof (fl_cols (reac_ctrl_parse_W o S) [(S - 8800, S)] _ HWd0
                  ltac:(unfold sub_fp, reac_ctrl_parse_W; intros xq Hxq; cbn [outside] in Hxq |- *;
                        split; [exact (proj1 Hxq) | exact I])) as HCOLa.
    assert (HCOL0 : Forall (fun d => forall x, fst d <= x < snd d -> outside [(S - 8800, S)] x)
                      (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0))
      by (rewrite Forall_forall in HCOLa |- *; intros dq Hdq; apply HCOLa, in_or_app; left; exact Hdq).
    destruct (fl_tls_same m m1 [(S - 8800, S)] (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k
                HT0 HT MU HCOL0) as (EDT & ETS & EC & ET & EDB & Ekq).
    subst DT0 TS0 C0 T0 DB0 k0.
    pose proof SMAL as HM. unfold asan_stack_malloc_1_contract_F, asan_stack_malloc_contract_F in HM. cbv zeta in HM.
    specialize (HM (proj1 (Nat.leb_le 1 10) eq_refl)).
    eapply evtF_cut.
    { destruct (rcpF_tls_rng RNG _ DT TS C T DB k (RTLS DT TS C T DB k HT0))
        as (RTdt & RTts & RTc & RTt & RTdb & RTp88 & RTp8).
      eapply HM with (lo := S - 8800) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (shadow_rw_mono m m1 SR0 WM RM).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HFl.
      - exact HFln.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : RcLay.ly_dj _ _ lo hi |- _ => unfold RcLay.ly_dj in Hd; lia end end.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* the callee's window [A - K, A) inside this function's window *)
        eapply rng_sub; [exact RWIN | lia | lia].
      - (* the runtime pointer cell at DT + 8 *) exact RTdt.
      - (* the runtime pointer cell at TS + 8 k *) exact RTts.
      - (* the runtime pointer cell at C + 152 *) exact RTc.
      - (* the runtime pointer cells at T + 48 *) exact RTt.
      - (* the runtime pointer cell at DB + 24 *) exact RTdb.
      - (* the side stack's header *) exact RFSS.
      - (* the class-1 frame area, from the frames' range in fp_w [1%nat] FS *) exact (rcpF_frame_area RNG FS RFW1).
      - (* the shadow of the class-1 frame area *) exact (rcpF_frame_sh RNG FS RFW1).
      - (* the thread-pointer cell at TP - 88 *) exact RTp88.
      - (* the thread-pointer cells at TP - 8 .. TP + 16 *) exact RTp8. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x835ec)) with (Z_to_bv 64 0x835ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2.
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 128, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf (A - 128) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (FL2 : FLG (A - 128) 0 (Z_to_bv 64 0) m2).
      { split; [|intros HC; discriminate HC].
        exists flags. split; [|split; [exact HFln | exact HFb]].
        eapply fl_bytes; [exact HFl | exact MU2 |].
        intros x Hx. rewrite HFln in Hx. change (fs_M 1) with 8192 in Hx. rewrite EFL0 in Hx.
        cbn [outside]. split; [|split; [|exact I]]; clear -Hx HFS' HAlo HAhi RS P1; lia. }
      pose proof (munch_refl [(A - 4096, A - 4088)] m2) as MUp.
      clear MU MU2 WM WM2 RM RM2 FR STA STw STs STz STw2 STzc MI.
      unfold Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 128)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step.
      assert (HSp : store_ok rsegs m2 (wa (A - 4096)) 8 = true)
        by (eapply wv_store_ok with (m := m2);
              [ intros i Hi; apply (stk_wv m2 (S - 8800) A); [exact ST2 | lia] | apply wmono_refl | lia | lia ]).
      rewrite (unsigned_lit A) by lia.
      step. store_done.
      step.
      rewrite (rc_lts_signed (A - 128) (A - 4096)) by lia.
      replace (A - 128 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (FL3 : FLG (A - 128) 0 (Z_to_bv 64 0) mf) end.
      { destruct FL2 as [(flg & Hfl & Hfln & HflF) _]. split; [|intros HC; discriminate HC].
        exists flg. split; [|split; [exact Hfln | exact HflF]].
        eapply fl_bytes; [exact Hfl | exact MUp |].
        intros x Hx. rewrite Hfln, EFL0 in Hx. change (fs_M 1) with 8192 in Hx.
        cbn [outside]. split; [clear -Hx HFS' HAlo HAhi RS P1; lia | exact I]. }
      eapply (fwords (A - 128) 0 (A - 128) 0 0 (Z_to_bv 64 0)); [left; repeat split; lia | | exact FL3 | exact K].
      refine (conj _ (conj WM3 (conj RM3 (conj MI2 FR2)))). unfold Wf, shadow_addr. exact MU3.
    - (* the side-stack frame fs_frame FS 1 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A) in FRM by lia.
      replace (fs_B 1) with 128 in FRM by reflexivity.
      change (bv_unsigned (Z_to_bv 64 128)) with 128 in FRM.
      replace (fs_shadow_n 1 128) with 16 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFLg & H24 & H120 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 1) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 1) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 1 jj) as fra eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hjj.
      assert (SHb : shadow_addr fra + 16 <= S - 8800)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (EFl : fs_flag FS 1 jj = FS + 20480 + jj)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      pose proof HFS' as HFSw.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFLg). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H120). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf fra jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi RS; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi RS; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
        ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES]; rewrite EFl;
              clear -HFS' FShi Hjj SHb HAlo HAhi RS; lia)) as FR2.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      (* flag jj was 0 at m1 (the frame __asan_stack_malloc_1 took was free), and the prologue wrote only the window *)
      assert (HFj0 : bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0]).
      { pose proof HFl as (Ba & Bl & BH).
        assert (HJ : (Z.to_nat jj < length flags)%nat) by (rewrite EM1 in HFln; lia).
        pose proof (BH (Z.to_nat jj) HJ) as E1. rewrite Hnth in E1. rewrite Z2Nat.id in E1 by lia.
        replace (fs_flag FS 1 0 + jj) with (fs_flag FS 1 jj) in E1 by (unfold fs_flag; lia).
        split; [rewrite EFl; lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat]; rewrite EFl; lia|].
        intros i0 Hi0. cbn [length] in Hi0. destruct i0 as [|i0]; [|lia].
        cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. rewrite <- E1.
        unfold mrd. rewrite (MU (wa (fs_flag FS 1 jj))); [reflexivity|].
        rewrite wa_unsigned by (rewrite EFl; lia). cbn [outside]. rewrite EFl. split; [lia | exact I]. }
      assert (HKs : FK fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj))).
      { right. split; [rewrite EM1; exact Hjj|]. split; [exact Efr|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact HFj0]. }
      destruct (fk_facts fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) HKs)
        as (FR8s & FRlos & FRhis & _ & _ & FAPs & FRAs & _ & SH1s & SH2s).
      assert (FL2 : FLG fra 1 (Z_to_bv 64 (fs_flag FS 1 jj)) m2).
      { split.
        - exists (upd_bytes flags (Z.to_nat jj) [Z_to_bv 8 1]). split; [|split].
          + eapply (bytes_at_munch_upd _ m1 m2 (fs_flag FS 1 0) flags (Z.to_nat jj) (Z_to_bv 8 1)).
            * exact HFl.
            * exact MU2.
            * clear -HFln Hjj; change (fs_M 1) with 8192 in HFln; lia.
            * replace (fs_flag FS 1 0 + Z.of_nat (Z.to_nat jj)) with (fs_flag FS 1 jj)
                by (rewrite EFl, EFL0; clear -Hjj; lia).
              exact HFLg.
            * intros x Hx Hne. rewrite HFln in Hx. change (fs_M 1) with 8192 in Hx. rewrite EFL0 in Hx.
              rewrite EFL0 in Hne.
              assert (Hxa : app_mem x) by (apply P4; clear -Hx P1 HFS'; unfold FS_SIZE; lia).
              cbn [outside]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
              -- clear -Hx P1; lia.
              -- rewrite EFl. clear -Hx Hne Hjj; lia.
              -- clear -Hx FRlos; lia.
              -- clear -Hx FRlos; lia.
              -- intros [HL HR]. apply (acl_app_not_shadow x Hxa). unfold shadow_addr in HL, HR.
                 replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
                 apply frame_shadow_in;
                   [clear -FRlos P1; lia | exact FRAs | clear -SH1s; lia | clear -SH2s; lia | lia].
              -- clear -Hx HFS' HAlo HAhi RS P1; lia.
          + rewrite upd_bytes_length by (cbn [length]; clear -HFln Hjj;
              change (fs_M 1) with 8192 in HFln; lia).
            exact HFln.
          + apply upd_bytes_01; [exact HFb | right; reflexivity].
        - intros _. replace (fra + 120) with (fra + 128 - 8) by lia. exact H120. }
      clear MU MU2 WM WM2 RM RM2 FR STA STw STs STz STw2 STzc MI.
      step. step. step. step.
      rewrite (rc_neq0_64 fra) by lia. cbn [negb]. cbv iota.
      eapply (fwords fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)));
        [exact HKs | | exact FL2 | exact K].
      refine (conj _ (conj WM3 (conj RM3 (conj MI2 FR2)))). unfold Wf, shadow_addr. exact MU3.
  Qed.

  (* ================= the body (0x8369c .. 0x83a10) ================= *)

  (* The runtime state carried across the body's calls (asan_memset, asan_memcpy, bcmp_wrap, kind_of_link1). *)
  Definition aJ (mc : word -> option byte) : Prop :=
    asan_cells mc /\ shadow_rw mc /\ addressable mc (S - 8800) 8800 /\
    fpx [1%nat] mc (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    reac_ctrl_parse_tls mc (bv_unsigned tp) FS (S - 8800) S.

  (* The cells the bcmp wrapper reads. *)
  Definition aCL (mc : word -> option byte) : Prop :=
    bytes_at rsegs mc REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mc REAL_MEMCMP (le8 (wa MEMCMP)) /\
    bytes_at rsegs mc GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mc (CF + 254) [Z_to_bv 8 1] /\
    bytes_at rsegs mc (CF + 255) [Z_to_bv 8 1].

  (* The contract's post (reac_ctrl_parse_contract_x of reac_ctrl_parse_c.v, with K = 8800 and sp = S). *)
  Definition Qp : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 8800) S /\
      (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
      asan_cells m' /\ shadow_rw m' /\ addressable m' (S - 8800) 8800 /\
      fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
      Forall (fun ci => bytes_at rsegs m' (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
      (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat ->
         bytes_at rsegs m (fs_flag FS 1%nat 0) fl -> bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
      reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.

  (* 0x839d8 .. 0x83a10: sp = s0 - 128, the saved registers restored from [S - 96, S), the frame popped, ret. The
     class-1 flag array reads back as at m (rcp_flag_kept of the post), so X's flag bytes, which are in it, are still
     1. *)
  Lemma L_restore : forall (m' : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (spc : Z),
    rw_cells rsegs m' (S - 96) SAVES ->
    munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 8800) S ->
    (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) -> aJ m' ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x839d8) fc None m' (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro Lfr X XF0 XB0 RWIN. clear SMAL HMSET HMCPY HBCMPW HKOL RS S16 ST0 MI0 HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 FP0 TLS0 RBY RIMG SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros m' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 spc
      FR MU WM MI ST HBox HaJ HFK.
    unfold SAVES in FR.
    replace (S - 96) with (S + -96) in FR by lia.
    do 14 step. step.
    apply evtF_done. unfold Qp. destruct HaJ as (AC & SW & AW & FP & TL).
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HBox|]. split; [exact AC|]. split; [exact SW|]. split; [exact AW|].
    split; [exact FP|]. split; [|split; [|exact TL]].
    - apply Forall_forall. intros ci Hin. destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (_ & Hb).
      destruct (x_flag_in ci Hin) as (E & L1 & L2).
      apply (bytes_keep m m' _ _ Hb). intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
      rewrite E in Hx. apply HFK. clear -Hx L1 L2. lia.
    - intros fl Hl Hb. apply (bytes_keep m m' _ _ Hb). intros x Hx. apply HFK.
      pose proof (len_le_M fl Hl) as Hl'. clear -Hx Hl'. lia.
  Qed.

  (* The full body footprint stays apart from the runtime's cells [RT_LO, RT_HI): the window and the side stack are
     above them, o is apart (AO0 via the CF cells), and every shadow byte is apart from application memory. *)
  Lemma aout_rt : forall Wm x,
    sub_fp Wm (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]) ->
    RT_LO <= x < RT_HI -> outside Wm x.
  Proof.
    intros Wm x Hs Hx.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & _) & _ & _ & _ & HFSb & _ & _ & _).
    unfold HIGHMEM_BEG, APPMEM_END in HHM'. unfold RT_LO, RT_HI in Hx. unfold ASAN_GT in P3.
    unfold FS_SIZE in HFSb.
    assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
    assert (EFR0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    apply Hs. apply fl_out_app.
    - unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K. cbn [outside]. split; [lia|].
      destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      destruct (AO0 Eo) as (_ & _ & DRT). unfold GOT_CF, CF in DRT. split; [lia | exact I].
    - assert (F0 : 0 <= fs_frame FS 1 0) by (rewrite EFR0; lia).
      assert (FM : fs_frame FS 1 (fs_M 1) <= APPMEM_END) by (rewrite EFM; clear -HFSb HAE; lia).
      assert (W0 : 0 <= S - 8800) by lia.
      apply fl_out_app.
      + unfold fp_w, fp_w1; cbn [flat_map app outside].
        split; [unfold fs_hint; cbn [Z.of_nat]; lia|].
        split; [unfold fs_flag, fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
        split; [rewrite EFR0; lia|].
        split; [exact (acl_sh_out x (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hap F0 FM)|].
        exact I.
      + cbn [outside]. split; [|exact I].
        exact (acl_sh_out x (S - 8800) S Hap W0 HAE).
  Qed.

  (* The post's asan runtime state (asan_cells, shadow_rw, fpx, tls) once the run wrote only within the window+o
     (fp's W), the class-1 side-stack bytes (fp_w [1] FS) and the window's shadow, with the hint and flag bytes read
     back as 0/1 at m'. fp (with no data ranges) is rebuilt by fl_fp_free and the data ranges' fp_wx-disjointness
     is FP0's; the tls premise by acl_tls_ret. *)
  Lemma aJ_free : forall Wm m',
    munch Wm m m' -> wmono rsegs m m' -> rd_mono m m' ->
    sub_fp Wm (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]) ->
    (forall x, FS + 80 <= x < FS + 104 -> outside Wm x) ->
    (forall x, FS <= x < FS + FS_SIZE -> outside Wm x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
    (exists h', bytes_at rsegs m' (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs m' (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    asan_cells m' /\ shadow_rw m' /\
    fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.
  Proof.
    intros Wm m' MU WM RM Hs O88 HRD Hint Hflags.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPn.
    split; [|split; [|split]].
    - apply (fl_asan_cells Wm m m' AC0 MU). intros x Hx. exact (aout_rt Wm x Hs Hx).
    - exact (shadow_rw_mono m m' SR0 WM RM).
    - apply fpx_of_fp_nil; [|exact (fpx_dj _ _ _ _ _ _ _ _ _ FP0)].
      eapply (fl_fp_free [1%nat] m m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S)
               [] Wm FPn TLS0 MU WM Hs O88 HRD).
      intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[]]. split; [exact Hint | exact Hflags].
    - exact (acl_tls_ret [1%nat] m m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S)
               [] [(shadow_addr (S - 8800), shadow_addr S)] Wm FPn TLS0 MU Hs).
  Qed.

  (* The body/exit footprint: the Qp footprint (the class-1 side stack less X's frames and their shadow, fp_wx) plus
     the frame and its shadow (written explicitly by the un-poison), weakened to the Qp footprint in each exit branch. *)
  Definition Wex (fra : Z) : list ivl :=
    (shadow_addr fra, shadow_addr fra + 16) :: (fra, fra + 128) ::
    reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X.

  (* The same with the whole class-1 side stack (fp_w), which aJ_free's footprint names. *)
  Definition Wexw (fra : Z) : list ivl :=
    (shadow_addr fra, shadow_addr fra + 16) :: (fra, fra + 128) ::
    reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS.

  Lemma Wex_sub_w : forall fra, sub_fp (Wex fra) (Wexw fra).
  Proof.
    intros fra x Hx. unfold Wexw in Hx. unfold Wex. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    apply acl_out_app_inv in H3 as [H3 H4]. apply fl_out_app; [exact H3 | exact (fp_wx_sub_w _ _ _ _ H4)].
  Qed.

  (* A high-shadow address y is not inside a short application-memory range [a, b). *)
  Lemma sh_hi_small_out : forall y a b,
    HIGHSHADOW_BEG <= y < HIGHMEM_BEG -> app_mem a -> a <= b -> b <= a + 2000000000 -> ~ (a <= y < b).
  Proof.
    intros y a b Hy Ha Hab Hb [H1 H2].
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, HIGHSHADOW_BEG, APPMEM_END in *. destruct Ha; lia.
  Qed.

  (* The shadow of a window byte z, apart from the released frame [fra, fra+128), is outside the exit footprint Wex. *)
  Lemma wex_sh_out : forall fra z,
    0 <= fra -> fra mod 8 = 0 -> app_mem fra -> fra + 128 <= APPMEM_END ->
    S - 8800 <= z < S -> (z < fra \/ fra + 128 <= z) ->
    outside (Wex fra) (shadow_addr z).
  Proof.
    intros fra z Hf0 Hfm Hfap Hfe Hz Hnf. apply Wex_sub_w.
    pose proof HHM as HHM0. pose proof HAE as HAE0. unfold HIGHMEM_BEG, APPMEM_END in HHM0, HAE0.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & _) & _ & _ & _ & HFSb & _ & _ & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    assert (Hzsh : HIGHSHADOW_BEG <= shadow_addr z < HIGHMEM_BEG).
    { unfold shadow_addr, ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
    assert (Esh16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (rewrite <- (sh_add8 fra 16 Hfm); f_equal; lia).
    assert (EFR0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Hwinapp : app_mem (S - 8800)) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia).
    assert (Hhintapp : app_mem (fs_hint FS 1)) by (apply Pfsapp; unfold fs_hint, FS_SIZE; cbn [Z.of_nat]; lia).
    assert (Hflagapp : app_mem (fs_flag FS 1 0))
      by (apply Pfsapp; unfold fs_flag, fs_M, FS_SIZE; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (Hfr0app : app_mem (fs_frame FS 1 0)) by (apply Pfsapp; rewrite EFR0; unfold FS_SIZE; lia).
    assert (Hfrge : shadow_addr (fs_frame FS 1 (fs_M 1)) <= shadow_addr z)
      by (apply acl_sh_ge; rewrite EFM; lia).
    unfold Wexw, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K, fp_w, fp_w1.
    destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [app flat_map outside fst snd].
    - split; [rewrite Esh16; exact (acl_win_sh z fra (fra + 128) Hfm ltac:(destruct Hnf; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) fra (fra + 128) Hzsh Hfap ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (S - 8800) S Hzsh Hwinapp ltac:(lia) ltac:(lia))|].
      split; [unfold fs_hint; cbn [Z.of_nat];
              exact (sh_hi_small_out (shadow_addr z) (FS + 8) (FS + 8 + 8) Hzsh
                       ltac:(unfold fs_hint in Hhintapp; cbn [Z.of_nat] in Hhintapp; exact Hhintapp)
                       ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1) Hzsh Hflagapp
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia)
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hzsh Hfr0app
                       ltac:(rewrite EFR0, EFM; lia) ltac:(rewrite EFR0, EFM; lia))|].
      split; [lia | exact I].
    - destruct (AO0 Eo) as (AOa & AOb & AOc).
      pose proof (acl_app_in m o 36 0 AOa ltac:(lia)) as AOo. rewrite Z.add_0_r in AOo.
      split; [rewrite Esh16; exact (acl_win_sh z fra (fra + 128) Hfm ltac:(destruct Hnf; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) fra (fra + 128) Hzsh Hfap ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) o (o + 36) Hzsh AOo ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (S - 8800) S Hzsh Hwinapp ltac:(lia) ltac:(lia))|].
      split; [unfold fs_hint; cbn [Z.of_nat];
              exact (sh_hi_small_out (shadow_addr z) (FS + 8) (FS + 8 + 8) Hzsh
                       ltac:(unfold fs_hint in Hhintapp; cbn [Z.of_nat] in Hhintapp; exact Hhintapp)
                       ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1) Hzsh Hflagapp
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia)
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hzsh Hfr0app
                       ltac:(rewrite EFR0, EFM; lia) ltac:(rewrite EFR0, EFM; lia))|].
      split; [lia | exact I].
  Qed.

  (* The post asan state at the exit memory m' (asan_cells, shadow_rw, fpx, tls), packaging aJ_free for a frame fra
     whose release wrote only Wex (inside Wexw, the footprint aJ_free names). *)
  Lemma Wex_free : forall fra fv spc j nn w120 (m' : word -> option byte),
    FK fra fv spc j nn w120 ->
    munch (Wex fra) m m' -> wmono rsegs m m' -> rd_mono m m' ->
    (exists h', bytes_at rsegs m' (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs m' (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    asan_cells m' /\ shadow_rw m' /\
    fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.
  Proof using tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AO0 X FP0 TLS0. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd AW0 AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 m' HK MU0 WM RM Hint Hflags.
    pose proof (munch_weaken _ _ _ _ (Wex_sub_w fra) MU0) as MU. clear MU0.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM0. pose proof HAE as HAE0. unfold HIGHMEM_BEG, APPMEM_END in HHM0, HAE0.
    pose proof FP0 as (DT & TS & C & T & DB & k & HT & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (EFR0c0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Esh16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (rewrite <- (sh_add8 fra 16 FR8); f_equal; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
    (* sub_fp: Wexw fra refines the Qp footprint. *)
    assert (Hsub : sub_fp (Wexw fra)
                     (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)])).
    { intros x Hxt.
      apply acl_out_app_inv in Hxt as [HxW Hxr]. apply acl_out_app_inv in Hxr as [Hxfpw Hxwin].
      unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K in HxW. cbn [outside] in HxW. destruct HxW as [HxWin HxWo].
      cbn [outside] in Hxwin. destruct Hxwin as [Hxws _].
      unfold Wexw. apply (fl_out_app [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)]
                           (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS)).
      - cbn [outside]. split; [|split; [|exact I]].
        + (* ~ (shadow_addr fra, shadow_addr fra + 16) *)
          rewrite Esh16.
          destruct HK as [(_ & Efra & _) | (Hj & Efra & _)].
          * subst fra. intros [HL HR]. apply Hxws. split.
            -- pose proof (acl_sh_ge (A - 128) (S - 8800) ltac:(lia)) as Hge. lia.
            -- pose proof (acl_sh_ge S (A - 128 + 128) ltac:(lia)) as Hge. lia.
          * pose proof Hxfpw as Hf. unfold fp_w, fp_w1 in Hf. cbn [flat_map app outside fst snd] in Hf.
            destruct Hf as (_ & _ & _ & Hfsh & _). subst fra. intros [HL HR]. apply Hfsh. split.
            -- pose proof (acl_sh_ge (fs_frame FS 1 j) (fs_frame FS 1 0)
                             ltac:(rewrite EFR1, EFRj; lia)) as Hge. lia.
            -- pose proof (acl_sh_ge (fs_frame FS 1 (fs_M 1)) (fs_frame FS 1 j + 128)
                             ltac:(rewrite EFRj, EFM; lia)) as Hge. lia.
        + (* ~ (fra, fra + 128) *)
          destruct HK as [(_ & Efra & _) | (Hj & Efra & _)].
          * subst fra. intros [HL HR]. apply HxWin. split; lia.
          * pose proof Hxfpw as Hf. unfold fp_w, fp_w1 in Hf. cbn [flat_map app outside fst snd] in Hf.
            destruct Hf as (_ & _ & Hfrm & _). subst fra. intros [HL HR]. apply Hfrm.
            rewrite EFRj in HL, HR. rewrite EFR1, EFM. split; lia.
      - apply fl_out_app; [|exact Hxfpw].
        unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. apply fl_out_app; [exact HxWo|].
        cbn [outside]. split; [exact HxWin | exact I]. }
    (* O88: the asan header words FS+80..FS+104 are outside Wexw. *)
    assert (O88 : forall x, FS + 80 <= x < FS + 104 -> outside (Wexw fra) x).
    { intros x Hx. apply Hsub.
      assert (Hxapp : app_mem x) by (apply Pfsapp; unfold FS_SIZE; lia).
      apply fl_out_app; [|apply fl_out_app].
      - exact (fl_dj_out (reac_ctrl_parse_W o S) _ FS (fs_frame FS 0 0) x HWd
                 ltac:(apply in_or_app; right; left; reflexivity) ltac:(rewrite EFR0c0; lia)).
      - unfold fp_w, fp_w1. cbn [flat_map app outside fst snd].
        split; [unfold fs_hint; cbn [Z.of_nat]; lia|].
        split; [unfold fs_flag, fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
        split; [rewrite EFR1; lia|].
        split; [exact (acl_sh_out x (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hxapp
                         ltac:(rewrite EFR1; lia) ltac:(rewrite EFM; lia)) | exact I].
      - cbn [outside]. split; [|exact I].
        exact (acl_sh_out x (S - 8800) S Hxapp ltac:(lia) ltac:(lia)). }
    (* HRD: the side stack stays readable at m'. *)
    assert (HRD : forall x, FS <= x < FS + FS_SIZE -> outside (Wexw fra) x \/ exists b, mrd rsegs m' (wa x) = Some b).
    { intros x Hx. right. apply RM. exact (rd_of_stk m FS (FS + FS_SIZE) Pfsstk x Hx). }
    apply (aJ_free (Wexw fra) m'); [exact MU | exact WM | exact RM | exact Hsub | exact O88 | exact HRD | exact Hint | exact Hflags].
  Qed.

  (* Wex fra refines the Qp footprint in reac_ctrl_parse_fp order (for L_restore's munch): a side frame j and its
     shadow are inside fp_wx [1] FS X, as j is not an index of X (its flag was 0 at m, FK). *)
  Lemma Wex_subfp : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wex fra) (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]).
  Proof using tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X XF0 FP0. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd HOK AC0 AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XB0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (Pfs0 & Pfs1 & _) & _).
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
    assert (Esh16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (rewrite <- (sh_add8 fra 16 FR8); f_equal; lia).
    intros x Hxt.
    apply acl_out_app_inv in Hxt as [Hxfp Hxr]. apply acl_out_app_inv in Hxr as [Hxfpw Hxwin].
    pose proof Hxfp as Hxfp0. unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in Hxfp0.
    apply acl_out_app_inv in Hxfp0 as [HxWo HxW2]. cbn [outside] in HxW2. destruct HxW2 as [HxWin _].
    cbn [outside] in Hxwin. destruct Hxwin as [Hxws _].
    unfold Wex. apply (fl_out_app [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)]
                         (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X)).
    - cbn [outside]. split; [|split; [|exact I]].
      + rewrite Esh16. destruct HK as [(_ & Efra & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)].
        * subst fra. intros [HL HR]. apply Hxws. split.
          -- pose proof (acl_sh_ge (A - 128) (S - 8800) ltac:(lia)) as Hge. lia.
          -- pose proof (acl_sh_ge S (A - 128 + 128) ltac:(lia)) as Hge. lia.
        * intros [HL HR]. apply (fp_wx_frame_sh_in FS X j x Hj (x_ne_j j Hfl0)); [|exact Hxfpw].
          rewrite Efra in HL, HR.
          replace (fs_frame FS 1 (j + 1)) with (fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
          split; [exact HL | exact HR].
      + destruct HK as [(_ & Efra & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)].
        * subst fra. intros [HL HR]. apply HxWin. split; lia.
        * intros [HL HR]. apply (fp_wx_frame_in FS X j x Hj (x_ne_j j Hfl0)); [|exact Hxfpw].
          rewrite Efra in HL, HR.
          replace (fs_frame FS 1 (j + 1)) with (fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
          split; [exact HL | exact HR].
    - apply fl_out_app; [|exact Hxfpw].
      unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. apply fl_out_app; [exact HxWo|].
      cbn [outside]. split; [exact HxWin | exact I].
  Qed.

  (* The body's full write footprint Wf is inside the exit footprint Wex (for L_exit's munch). *)
  Lemma subWf_Wex : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wf fra j nn) (Wex fra).
  Proof.
    intros fra fv spc j nn w120 HK.
    assert (Hjb : 0 <= j < 8192 /\ nn <= 1).
    { destruct HK as [(_ & _ & _ & Ej & En) | (Hjb & _ & _ & _ & _ & En & _)];
        [split; lia | change (fs_M 1) with 8192 in Hjb; split; lia]. }
    assert (EFL : fs_flag FS 1 j = fs_flag FS 1 0 + j)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    intros x Hx. unfold Wex in Hx. cbn [outside] in Hx.
    destruct Hx as (Hsh & Hfr & Hrest).
    apply acl_out_app_inv in Hrest as [Hfp Hfpw].
    apply acl_out_app_inv in Hfp as [_ Hwin].
    cbn [outside] in Hwin. destruct Hwin as [Hwin _].
    destruct (wx_out_hint_flag FS X x Hfpw) as (Hhint & Hflagarr).
    unfold Wf. cbn [outside].
    split; [exact Hwin|]. split; [exact Hhint|].
    split; [intros [HL HR]; apply Hflagarr; rewrite EFL in HL, HR;
            change (fs_M 1) with 8192; clear -HL HR Hjb; split; lia|].
    split; [exact Hfr|]. split; [exact Hsh | exact I].
  Qed.

  (* An app-memory byte apart from the released frame [fra, fra+128) is outside the small exit footprint. *)
  Lemma Wsmall_outside : forall fra x,
    0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
    2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
    app_mem x -> (x < fra \/ fra + 128 <= x) ->
    outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] x.
  Proof.
    intros fra x Hf0 FRA SH1 SH2 Hxapp Hnf. cbn [outside]. split; [|split; [|exact I]].
    - intros [HL HR]. apply (acl_app_not_shadow x Hxapp).
      replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
      apply frame_shadow_in; [exact Hf0 | exact FRA | exact SH1 | exact SH2 | lia].
    - intros [HL HR]. destruct Hnf; lia.
  Qed.

  (* Everything the body needs about the output box ob (the frame's redzone fra + 32 when o = 0, else o): its
     range and alignment, its distance from the runtime's cells, from the deepest callee window (the bcmp
     wrapper's 4560 bytes), from the saved registers, from the 50 bytes at f, from the frame and from the
     class-1 flag array. *)
  Lemma ob_facts : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob ->
    0 <= ob /\ ob + 36 <= 2 ^ 64 /\ ob mod 4 = 0 /\ app_mem (ob + 36) /\
    (ob + 36 <= RT_LO \/ RT_HI <= ob) /\
    (ob + 36 <= spc - 4560 \/ spc <= ob) /\
    (ob + 36 <= S - 96 \/ S <= ob) /\
    (50 <= n -> ob + 36 <= f \/ f + 50 <= ob) /\
    (ob = fra + 32 \/ ob + 36 <= fra \/ fra + 128 <= ob) /\
    (fs_flag FS 1 0 + fs_M 1 <= ob \/ ob + 36 <= fs_flag FS 1 0) /\
    (ob + 36 <= GOT_CF \/ CF + 256 <= ob).
  Proof.
    intros fra fv spc j nn w120 ob HK HO.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    destruct HO as [(Eo & Eob) | (Eo & Eob)]; subst ob.
    - (* the box is the frame's redzone *)
      assert (Hbox36 : app_mem (fra + 32 + 36))
        by (replace (fra + 32 + 36) with (fra + 68) by lia; apply FAP; lia).
      destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew & Enn & Hfl0)].
      + (* the real-stack frame: fra = A - 128, inside the window *)
        split; [clear -FRlo Pfs0; lia|]. split; [clear -Efra HAhi RS; lia|].
        split; [clear -FR8; Z.div_mod_to_equations; lia|]. split; [exact Hbox36|].
        split; [right; unfold RT_HI; clear -FRlo Pfs0 Pfs2; lia|].
        split; [right; clear -Espc Efra; lia|].
        split; [left; clear -Efra HAhi RS; lia|].
        split; [intros Hn50; destruct (HF Hn50) as (_ & _ & HfS); destruct HfS as [Hc|Hc];
                [right; clear -Hc Efra HAlo HAhi RS; lia | left; clear -Hc Efra HAhi RS; lia]|].
        split; [left; reflexivity|].
        split; [left; rewrite EFL0, EM1; clear -FRlo Pfs0; lia|].
        right. unfold CF. clear -FRlo Pfs0 Pfs2; lia.
      + (* the side-stack frame: fra = fs_frame FS 1 j *)
        rewrite EM1 in Hj.
        assert (EFRj : fra = FS + 1085440 + j * 128)
          by (rewrite Efra; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
        split; [clear -EFRj Hj Pfs0; lia|]. split; [clear -EFRj Hj HFSb RS; lia|].
        split; [clear -FR8; Z.div_mod_to_equations; lia|]. split; [exact Hbox36|].
        split; [right; unfold RT_HI; clear -EFRj Hj Pfs0; lia|].
        split; [left; clear -EFRj Hj HFSb Hspcr RS; lia|].
        split; [left; clear -EFRj Hj HFSb RS; lia|].
        split; [intros Hn50;
                destruct (D_apart_frame f (f + 50) j
                  ltac:(unfold reac_ctrl_parse_D; apply in_or_app; left;
                        rewrite (proj2 (Z.ltb_ge n 50) Hn50); left; reflexivity)
                  ltac:(clear; lia) ltac:(rewrite EM1; exact Hj) Hfl0) as [Hc|Hc];
                rewrite <- Efra in Hc;
                [right; clear -Hc; lia | left; clear -Hc; lia]|].
        split; [left; reflexivity|].
        split; [left; rewrite EFL0, EM1; clear -EFRj Hj Pfs0; lia|].
        right. unfold CF. clear -EFRj Hj Pfs0 Pfs2; lia.
    - (* the box is o *)
      destruct (HOK Eo) as (Ho4 & Ho36 & HOrw & HoS & Hof).
      destruct (AO0 Eo) as (AOa & AOapp & AOcf).
      pose proof AOa as (AO0' & _).
      split; [clear -AO0'; lia|]. split; [clear -Ho36; lia|].
      split; [exact Ho4|]. split; [exact AOapp|].
      split; [destruct AOcf as [Hc|Hc];
              [left; unfold GOT_CF, RT_LO in Hc |- *; clear -Hc; lia
              | right; unfold CF, RT_HI in Hc |- *; clear -Hc; lia]|].
      split; [destruct HoS as [Hc|Hc]; [left | right]; clear -Hc Hspcr RS; lia|].
      split; [destruct HoS as [Hc|Hc]; [left | right]; clear -Hc RS; lia|].
      split; [intros Hn50; destruct (Hof Hn50) as [Hc|Hc]; [left | right]; clear -Hc; lia|].
      split.
      + right.
        destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew & Enn & Hfl0)].
        * destruct HoS as [Hc|Hc]; [left | right]; clear -Hc Efra HAlo HAhi RS; lia.
        * destruct (D_apart_frame o (o + 36) j
            ltac:(unfold reac_ctrl_parse_D; apply in_or_app; right;
                  rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity)
            ltac:(clear; lia) Hj Hfl0) as [Hc|Hc];
            rewrite <- Efra in Hc; [left | right]; clear -Hc; lia.
      + split.
        * pose proof (dj_pair o (o + 36) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1)
            ltac:(unfold reac_ctrl_parse_D; apply in_or_app; right;
                  rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity)
            (proj2 (fp_wx_hint_flag_in FS X))) as Hd.
          destruct Hd as [Hc|Hc]; [right | left]; clear -Hc; lia.
        * exact AOcf.
  Qed.

  (* The body's own writes (the box and the callee windows) are inside the exit footprint. *)
  Lemma ob_wex : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob ->
    sub_fp [(ob, ob + 36); (S - 8800, spc)] (Wex fra).
  Proof.
    intros fra fv spc j nn w120 ob HK HO x Hx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    unfold Wex in Hx. cbn [outside] in Hx. destruct Hx as (Hsh & Hfr & Hrest).
    apply acl_out_app_inv in Hrest as [Hfp Hfpw].
    unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in Hfp.
    apply acl_out_app_inv in Hfp as [Hbox Hwin]. cbn [outside] in Hwin. destruct Hwin as [Hwin _].
    cbn [outside]. split; [|split; [|exact I]].
    - destruct HO as [(Eo & Eob) | (Eo & Eob)]; subst ob.
      + clear -Hfr; lia.
      + rewrite (proj2 (Z.eqb_neq o 0) Eo) in Hbox. cbn [outside] in Hbox. exact (proj1 Hbox).
    - clear -Hwin Hspc; lia.
  Qed.

  (* Wex fra refines the Qp footprint in reac_ctrl_parse_W order (for aout_rt). *)
  Lemma Wex_subW : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wex fra) (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]).
  Proof.
    intros fra fv spc j nn w120 HK x Hx.
    apply (Wex_subfp fra fv spc j nn w120 HK).
    apply acl_out_app_inv in Hx as [HW HY]. apply fl_out_app.
    2:{ apply acl_out_app_inv in HY as [HY1 HY2].
        apply fl_out_app; [exact (fp_wx_sub_w _ _ _ _ HY1) | exact HY2]. }
    unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K in HW. cbn [outside] in HW. destruct HW as [H1 H2].
    unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. apply fl_out_app; [exact H2|].
    cbn [outside]. split; [exact H1 | exact I].
  Qed.

  (* 0x83920 .. 0x83a10: the frame-shadow rewrite (un-poison), the side-frame flag cleared, the registers restored,
     ret. Reaches Qp through L_restore. FKP: the body wrote no byte of the class-1 flag array other than flag j (the
     side frame's, set by __asan_stack_malloc_1 and cleared here back to its 0 at m). *)
  Lemma L_exit : forall fra fv spc j nn w120 mc
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 ->
    munch (Wex fra) m mc ->
    wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw mc -> stk rsegs mc (S - 8800) S ->
    rw_cells rsegs mc (S - 96) SAVES ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (exists h', bytes_at rsegs mc (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    (nn = 1 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + nn) ->
       mrd rsegs mc (wa x) = mrd rsegs m (wa x)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mc (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW RFLG RFRM SCFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31
      HK MU WM RM MI AC SR ST SV HBox Hhint Hflags Hw120 FKP.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Ush : bv_unsigned (Z_to_bv 64 (fra / 8 + ASAN_K)) = fra / 8 + ASAN_K)
      by (apply unsigned_lit; clear -SH1 SH2; lia).
    assert (Ufra : bv_unsigned (Z_to_bv 64 fra) = fra)
      by (apply unsigned_lit; clear -FRlo FRhi HAhi RS Pfs0; lia).
    assert (HHMl : 17594333495296 <= S - 8800)
      by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    (* the munch from m (over Wex, whose fp_wx part has an abstract X) is kept out of the store tracking; the exit's
       own writes are tracked from mc on the tight footprints MUe / MUx, and the two are composed at the end *)
    pose proof (conj MU I) as MUn. clear MU.
    pose proof HK as HKc.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)] mc) as MUe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128);
                            (fs_flag FS 1 j, fs_flag FS 1 j + 1)] mc) as MUx.
    pose proof (wmono_refl rsegs mc) as WMe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 8)] mc) as MUw.
    unfold shadow_addr in MUe, MUx, MUw.
    step.
    wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    step. step.
    wstb fra 8%nat fra FW. step. store_done.
    destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew120 & Enn & Hfl0)].
    - (* real-stack frame: fv = 0 *)
      subst fv. step.
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbv iota.
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (shadow_rw_mono m mcur SR0 WM RM) as SRc;
        pose proof (shadow16_stk mcur fra SRc ltac:(clear -FRlo Pfs0; lia) FRA
                      ltac:(clear -SH1; lia) ltac:(clear -SH2; lia)) as STsh
      end.
      pose proof (stk_carve rsegs _ (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(clear -SH1; lia))
        as [STsh' [junkS SHC]].
      replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
      sstep (fra / 8 + ASAN_K) 4 4%nat SW. sstep (fra / 8 + ASAN_K) 5 5%nat SW.
      sstep (fra / 8 + ASAN_K) 6 6%nat SW. sstep (fra / 8 + ASAN_K) 7 7%nat SW.
      sstep (fra / 8 + ASAN_K) 0 0%nat SW. sstep (fra / 8 + ASAN_K) 1 1%nat SW.
      sstep (fra / 8 + ASAN_K) 2 2%nat SW. sstep (fra / 8 + ASAN_K) 3 3%nat SW.
      sstep (fra / 8 + ASAN_K) 12 12%nat SW. sstep (fra / 8 + ASAN_K) 13 13%nat SW.
      sstep (fra / 8 + ASAN_K) 14 14%nat SW. sstep (fra / 8 + ASAN_K) 15 15%nat SW.
      sstep (fra / 8 + ASAN_K) 8 8%nat SW. sstep (fra / 8 + ASAN_K) 9 9%nat SW.
      sstep (fra / 8 + ASAN_K) 10 10%nat SW. sstep (fra / 8 + ASAN_K) 11 11%nat SW.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      assert (EFL : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      pose proof (FAP 0 ltac:(lia)) as Hfraapp. rewrite Z.add_0_r in Hfraapp.
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi RS HAE; unfold APPMEM_END in *; lia).
      destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
      destruct Hhint as [h' Hh]. destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (MU : munch (Wex fra) m mf)
          by (apply (munch_trans _ m mc mf (proj1 MUn)); eapply munch_weaken; [|exact MUe];
              intros y Hy; unfold Wex, shadow_addr in Hy; cbn [outside] in Hy |- *;
              destruct Hy as (H1 & H2 & _); exact (conj H1 (conj H2 I)))
      end.
      eapply L_restore.
      + exact SV.
      + eapply munch_weaken; [exact (Wex_subfp fra 0 spc j nn w120 HKc) | exact MU].
      + exact WM.
      + exact MI.
      + exact ST.
      + intros Ho. eapply acl_rw; [exact (HBox Ho) | exact MUe | exact WMe |].
        intros y Hy. apply Wsmall_outside; [clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2 | |].
        * destruct (AO0 Ho) as (AOa & _ & _). pose proof (acl_app_in m o 36 (y - o) AOa ltac:(cbn [cells_size csize] in Hy; lia)) as Hya.
          replace (o + (y - o)) with y in Hya by lia. exact Hya.
        * destruct (HOK Ho) as (_ & _ & _ & HowS & _). rewrite Efra.
          cbn [cells_size csize] in Hy. destruct HowS as [Hc|Hc]; [left | right]; clear -Hy Hc HAlo HAhi RS; lia.
      + lazymatch goal with |- aJ ?mf =>
          assert (Hz16 : forall g, 0 <= g <= 15 ->
                    exists b, mrd rsegs mf (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0);
          [ destruct HB16 as (_ & _ & Hr); intros g Hg; exists (Z_to_bv 8 0); split; [|vm_compute; reflexivity];
            pose proof (Hr (Z.to_nat g) ltac:(cbn [length]; lia)) as Hg';
            replace (fra / 8 + ASAN_K + Z.of_nat (Z.to_nat g)) with (fra / 8 + ASAN_K + g) in Hg' by lia;
            rewrite Hg';
            assert (Hc : g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9\/g=10\/g=11\/g=12\/g=13\/g=14\/g=15) by lia;
            repeat (destruct Hc as [Hc|Hc]); subst g; vm_compute; reflexivity
          | ];
          assert (AFR : addressable mf fra 128)
            by (apply frame_all_addr; [clear -FRlo Pfs0; lia | exact FR8 | exact Hfe | exact FAP | exact Hz16]);
          assert (ABLO : addressable mf (S - 8800) (fra - (S - 8800)));
          [ apply (acl_addr_munch (Wex fra) m mf (S - 8800) (fra - (S - 8800)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (S - 8800) (fra - (S - 8800)) AW0);
                [ lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRlo HAlo HAhi RS Efra; rewrite Efra in *; lia | left; clear -Hi; lia ] ]
          | ];
          assert (AABOVE : addressable mf (fra + 128) (S - (fra + 128)));
          [ apply (acl_addr_munch (Wex fra) m mf (fra + 128) (S - (fra + 128)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (fra + 128) (S - (fra + 128)) AW0);
                [ clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRhi HAhi RS Efra; rewrite Efra; lia
                | clear -FRhi HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRhi HAlo HAhi RS Efra; rewrite Efra in *; lia | right; clear -Hi; lia ] ]
          | ];
          assert (AWfinal : addressable mf (S - 8800) 8800);
          [ pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800)) 128 ABLO
                         ltac:(replace (S - 8800 + (fra - (S - 8800))) with fra by (clear; lia); exact AFR)
                         ltac:(lia)) as J1;
            pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800) + 128) (S - (fra + 128)) J1
                         ltac:(replace (S - 8800 + (fra - (S - 8800) + 128)) with (fra + 128) by (clear; lia); exact AABOVE)
                         ltac:(clear -FRhi HAhi RS Efra; rewrite Efra; lia)) as J2;
            exact (acl_addr_sub mf (S - 8800) (fra - (S - 8800) + 128 + (S - (fra + 128))) (S - 8800) 8800 J2
                     ltac:(lia) ltac:(lia) ltac:(clear; lia))
          | ];
          assert (Hfree : asan_cells mf /\ shadow_rw mf /\
                    fpx [1%nat] mf (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                    reac_ctrl_parse_tls mf (bv_unsigned tp) FS (S - 8800) S);
          [ apply (Wex_free fra 0 spc j nn w120 mf HKc MU WM RM);
            [ exists h'; eapply fl_bytes; [exact Hh | exact MUe |];
              intros y Hy; unfold fs_hint in Hy; rewrite length_le8 in Hy; cbn [Z.of_nat] in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ]
            | exists flags'; split; [|split; [exact Hfllen | exact HflF]];
              eapply fl_bytes; [exact Hfl | exact MUe |];
              intros y Hy; rewrite Hfllen, EM1, EFL in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ] ]
          | ];
          destruct Hfree as (Hac & Hsw & Hfp & Htl);
          split; [exact Hac|]; split; [exact Hsw|]; split; [exact AWfinal|]; split; [exact Hfp | exact Htl]
        end.
      + intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL, EM1 in Hx; clear -Hx; lia).
        lazymatch goal with |- mrd rsegs ?mf (wa x) = _ =>
          rewrite (munch_mrd_out _ mc mf x MUe ltac:(clear -Hxr Pfs0 HFSb RS; lia)
                     ltac:(apply Wsmall_outside;
                             [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                             | apply Pfsapp; unfold FS_SIZE; clear -Hxr; lia
                             | left; clear -Hxr FRlo; lia ]))
        end.
        apply FKP; [exact Hx | rewrite Enn; clear; lia].
    - (* side-stack frame: fv = fra <> 0 *)
      subst fv.
      pose proof (Hw120 Enn) as Hw120'.
      step.
      rewrite (rc_neq0_64 fra) by (clear -FRlo FRhi HAhi RS Pfs0; lia). cbn [negb]. cbv iota.
      step.
      wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 0) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 1) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 2) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 3) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 12) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 13) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 14) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 15) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 9) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 10) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 11) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      pose proof (fl_bytes _ mc _ (fra + 120) (le8 w120) Hw120' MUw
        ltac:(intros x Hx; rewrite length_le8 in Hx; cbn [Z.of_nat] in Hx; cbn [outside];
              split; [| split; [| exact I]];
              [ intros [HL HR]; apply (acl_app_not_shadow x);
                [ replace x with (fra + (x - fra)) by lia; apply FAP; lia
                | replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia;
                  apply frame_shadow_in;
                  [ clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia ] ]
              | intros [HL HR]; clear -Hx HL HR; lia ])) as Hw120m.
      pose proof (bytes_ro8 _ (fra + 120) w120 Hw120m) as Hw120c.
      step.
      subst w120.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hj.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
        by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
        by (apply unsigned_lit; exact Rfl).
      assert (SOK : store_ok rsegs m1 (wa (fs_flag FS 1 j)) 1 = true).
      { eapply (wv_store_ok m m1 (fs_flag FS 1 j) 1%nat).
        - intros i Hi. replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (cbn in Hi; lia).
          apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
          rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
        - exact WM.
        - clear -Rfl; lia.
        - clear -Rfl; cbn; lia. }
      assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
      { assert (EMj : fs_M 1 = 8192) by reflexivity.
        eapply rng_sub; [exact RFLG | rewrite !fs_flag1; lia | rewrite !fs_flag1; lia]. }
      step.
      replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
      replace (Z_to_bv 64 (fs_flag FS 1 j)) with (wa (fs_flag FS 1 0 + j))
        by (unfold wa; f_equal; rewrite EFLj, EFL0; lia).
      destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      destruct Hhint as [h' Hh].
      pose proof (FAP 0 ltac:(lia)) as Hfrapp. rewrite Z.add_0_r in Hfrapp.
      assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
      assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
      assert (Hfrw : fra + 128 <= S - 8800)
        by (rewrite Efra, EFRj; clear -Pfs0 HFSb Hj; unfold FS_SIZE in HFSb; lia).
      assert (Hfrge : FS + 1085440 <= fra) by (rewrite Efra, EFRj; clear -Hj; lia).
      assert (Afl : 0 <= fs_flag FS 1 0 + j /\ fs_flag FS 1 0 + j + 1 <= 2 ^ 64)
        by (rewrite EFL0; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -Hfrw HAE; unfold APPMEM_END in *; lia).
      (* the flag array [fs_flag FS 1 0, +fs_M 1) is apart from the frame and its shadow *)
      assert (Hdj : forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + Z.of_nat (length flags') ->
                    outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] x).
      { intros x Hx. rewrite Hfllen, EM1 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; rewrite EFL0 in Hx; unfold FS_SIZE; clear -Hx Pfs0 HFSb; lia).
        cbn [outside]. split; [| split; [| exact I]].
        - intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        - intros [HL HR]. rewrite EFL0 in Hx. clear -Hx HL Hfrge; lia. }
      pose proof (fl_bytes _ mc m1 (fs_flag FS 1 0) flags' Hfl MUe Hdj) as Hflm1.
      pose proof (bytes_at_write_inside rsegs m1 (fs_flag FS 1 0) flags' j [Z_to_bv 8 0] Hflm1
        ltac:(clear -Hj; lia)
        ltac:(cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia)) as Hnfl.
      (* facts about m2 = write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] *)
      pose proof (rw_cells_frame rsegs m1 (S - 96) SAVES (fs_flag FS 1 0 + j) [Z_to_bv 8 0] SV
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(right; cbn [length]; rewrite EFL0; clear -Pfs0 HFSb Hj; lia)) as SV2.
      pose proof (wmono_write rsegs m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WM) as WM2.
      pose proof (mem_inv_store rsegs m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] MI
        ltac:(cbn [length]; replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia);
              exact SOK)) as MI2.
      pose proof (stk_write rsegs m1 (S - 8800) S (fs_flag FS 1 0 + j) [Z_to_bv 8 0] ST
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)) as ST2.
      pose proof (rd_mono_write m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] RM) as RM2.
      pose proof (munch_write _ mc m1 (fs_flag FS 1 0 + j) [Z_to_bv 8 0] MUx
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(cbn [lib.Lib.Frame.inside length]; right; right; left; split; [rewrite EFLj, EFL0; clear -Hj; lia | rewrite EFLj, EFL0; clear -Hj; lia])) as MUx2.
      pose proof (wmono_write rsegs mc m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WMe) as WMe2.
      set (m2 := write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0]) in *.
      assert (MU2 : munch (Wex fra) m m2).
      { apply (munch_trans _ m mc m2 (proj1 MUn)). eapply munch_weaken; [|exact MUx2].
        intros y Hy. unfold Wex, shadow_addr in Hy. cbn [outside] in Hy |- *.
        destruct Hy as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. split; [|exact I].
        apply acl_out_app_inv in H3 as [_ H4]. destruct (wx_out_hint_flag FS X y H4) as (_ & Hfa).
        intros [HL HR]. apply Hfa. rewrite EFLj in HL, HR. rewrite EFL0, EM1. clear -HL HR Hj; lia. }
      step.
      eapply L_restore.
      + exact SV2.
      + eapply munch_weaken; [exact (Wex_subfp fra fra spc j nn (Z_to_bv 64 (fs_flag FS 1 j)) HKc) | exact MU2].
      + exact WM2.
      + exact MI2.
      + exact ST2.
      + intros Ho.
        eapply acl_rw; [exact (HBox Ho) | exact MUx2 | exact WMe2 |].
        intros x Hx. cbn [cells_size csize] in Hx.
        assert (Hxa : app_mem x)
          by (destruct (AO0 Ho) as (AOa & _ & _); pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as H;
              replace (o + (x - o)) with x in H by lia; exact H).
        assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
          by (unfold reac_ctrl_parse_D; apply in_or_app; right;
              rewrite (proj2 (Z.eqb_neq o 0) Ho); left; reflexivity).
        pose proof (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) ltac:(rewrite EM1; exact Hj) Hfl0) as Hofr.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        cbn [outside]. split; [| split; [| split; [| exact I]]].
        * intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        * intros [HL HR]. rewrite Efra in HL, HR. clear -Hx HL HR Hofr; lia.
        * intros [HL HR]. rewrite EFLj in HL, HR. rewrite EFL0, EM1 in Hofl. clear -Hx HL HR Hofl Hj; lia.
      + (* aJ m2 *)
        assert (AWfinal : addressable m2 (S - 8800) 8800).
        { apply (acl_addr_munch (Wex fra) m m2 (S - 8800) 8800 AW0 MU2).
          intros i Hi. apply wex_sh_out;
            [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfrapp | exact Hfe
            | clear -Hi; lia | right; clear -Hi Hfrw; lia ]. }
        assert (Hfree : asan_cells m2 /\ shadow_rw m2 /\
                  fpx [1%nat] m2 (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                  reac_ctrl_parse_tls m2 (bv_unsigned tp) FS (S - 8800) S).
        { apply (Wex_free fra fra spc j nn (Z_to_bv 64 (fs_flag FS 1 j)) m2 HKc MU2 WM2 RM2).
          - exists h'. eapply fl_bytes; [exact Hh | exact MUx2 |].
            intros y Hy. unfold fs_hint in Hy. rewrite length_le8 in Hy. cbn [Z.of_nat] in Hy.
            cbn [outside]. split; [| split; [| split; [| exact I]]].
            + intros [HL HR]. apply (acl_app_not_shadow y).
              * apply Pfsapp. unfold FS_SIZE; clear -Hy Pfs0; lia.
              * replace y with (fra / 8 + ASAN_K + (y - (fra / 8 + ASAN_K))) by lia.
                apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
            + intros [HL HR]. clear -Hy HL HR Hfrge; lia.
            + intros [HL HR]. rewrite EFLj in HL, HR. clear -Hy HL HR Hj; lia.
          - exists (upd_bytes flags' (Z.to_nat j) [Z_to_bv 8 0]). split; [exact Hnfl|]. split.
            + rewrite upd_bytes_length by (cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia). exact Hfllen.
            + unfold upd_bytes. apply Forall_app. split; [| apply Forall_app; split].
              * pose proof HflF as HFa. rewrite <- (firstn_skipn (Z.to_nat j) flags') in HFa.
                apply Forall_app in HFa. exact (proj1 HFa).
              * constructor; [left; reflexivity | constructor].
              * pose proof HflF as HFb.
                rewrite <- (firstn_skipn (Z.to_nat j + length [Z_to_bv 8 0])%nat flags') in HFb.
                apply Forall_app in HFb. exact (proj2 HFb). }
        destruct Hfree as (Hac & Hsw & Hfp & Htl).
        split; [exact Hac|]. split; [exact Hsw|]. split; [exact AWfinal|]. split; [exact Hfp | exact Htl].
      + (* the flag array: flag j is 0 again (as at m, FK), the rest as at mc (FKP) *)
        intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
        destruct (Z.eq_dec x (fs_flag FS 1 0 + j)) as [Exj|Exj].
        * subst x.
          assert (A0 : mrd rsegs m (wa (fs_flag FS 1 0 + j)) = Some (Z_to_bv 8 0)).
          { destruct Hfl0 as (_ & _ & H0). pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0.
            cbn [Z.of_nat nth_error] in A0. rewrite Z.add_0_r in A0.
            replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia). exact A0. }
          rewrite A0. unfold m2, mrd. cbn [write_to_mem].
          first [rewrite bv_eqb_refl | unfold bv_eqb; rewrite Z.eqb_refl]. reflexivity.
        * assert (Hout : outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128);
                                  (fs_flag FS 1 j, fs_flag FS 1 j + 1)] x).
          { pose proof (Hdj x ltac:(rewrite Hfllen; exact Hx)) as (Ho1 & Ho2 & _).
            cbn [outside]. split; [exact Ho1|]. split; [exact Ho2|]. split; [|exact I].
            rewrite EFLj. rewrite EFL0 in Exj. clear -Exj; lia. }
          rewrite (munch_mrd_out _ mc m2 x MUx2 ltac:(clear -Hxr Pfs0 HFSb RS; lia) Hout).
          apply FKP; [exact Hx | rewrite Enn, EFLj; rewrite EFL0 in Exj; clear -Exj; lia].
  Qed.

  (* The body's whole write footprint from m: the frame block's writes and the output box. *)
  Definition Wall (fra j nn ob : Z) : list ivl := Wf fra j nn ++ [(ob, ob + 36)].

  Lemma mu_all : forall fra fv spc j nn w120 ob mc mx, FK fra fv spc j nn w120 -> OB fra ob ->
    munch (Wf fra j nn) m mc -> munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    munch (Wall fra j nn ob) m mx.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MU MUb.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    eapply munch_trans.
    - eapply munch_weaken; [| exact MU]. unfold Wall. intros x Hx. apply acl_out_app_inv in Hx as [H1 _]. exact H1.
    - eapply munch_weaken; [| exact MUb]. unfold Wall. intros x Hx.
      apply acl_out_app_inv in Hx as [H1 H2]. unfold Wf in H1. cbn [outside] in H1, H2.
      destruct H1 as (Hw & _). destruct H2 as (Hb & _).
      cbn [outside]. split; [exact Hb|]. split; [clear -Hw Hspc; lia | exact I].
  Qed.

  (* The 50 bytes at f, when the header is long enough: in application memory, addressable, and apart from every
     range the body writes. *)
  Lemma f_facts : 50 <= n -> forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob ->
    0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= 2147450880 \/ 17594333495296 <= f) /\
    addressable m f 50 /\ disjoint_from (Wall fra j nn ob) f 50.
  Proof.
    intros Hn50 fra fv spc j nn w120 ob HK HO.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (HF Hn50) as (Hf0 & Hf64 & HfS).
    pose proof (AF0 Hn50) as AFm.
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Hjb : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | rewrite EM1 in Hjb; lia]).
    assert (Hin_f : In (f, f + 50) (reac_ctrl_parse_D f n o))
      by (unfold reac_ctrl_parse_D; apply in_or_app; left;
          rewrite (proj2 (Z.ltb_ge n 50) Hn50); left; reflexivity).
    pose proof (dj_pair f (f + 50) (fs_hint FS 1) (fs_hint FS 1 + 8) Hin_f
                  (proj1 (fp_wx_hint_flag_in FS X))) as Hfh.
    pose proof (dj_pair f (f + 50) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1) Hin_f
                  (proj2 (fp_wx_hint_flag_in FS X))) as Hff.
    assert (Happ : f + 50 <= 2147450880 \/ 17594333495296 <= f)
      by (apply (app_range f 50); [lia | intros i Hi; exact (acl_app_in m f 50 i AFm Hi)]).
    assert (Hfr : f + 50 <= fra \/ fra + 128 <= f).
    { destruct HK as [(_ & Efra & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)].
      - destruct HfS as [Hc|Hc]; [left | right]; clear -Hc Efra HAlo HAhi RS; lia.
      - destruct (D_apart_frame f (f + 50) j Hin_f ltac:(clear; lia) Hj Hfl0) as [Hc|Hc];
          rewrite <- Efra in Hc; [left | right]; clear -Hc; lia. }
    split; [exact Hf0|]. split; [exact Hf64|]. split; [exact Happ|]. split; [exact AFm|].
    unfold Wall, Wf. cbn [disjoint_from app fst snd].
    split; [clear -HfS; destruct HfS; lia|].
    split; [clear -Hfh; unfold fs_hint in *; cbn [Z.of_nat] in *; lia|].
    split; [rewrite EFLj; rewrite EFL0, EM1 in Hff; clear -Hff Hjb; lia|].
    split; [clear -Hfr; lia|].
    split; [unfold shadow_addr; clear -Happ SH1 SH2; lia|].
    split; [pose proof (Obf Hn50) as Hc; clear -Hc; lia | exact I].
  Qed.

  (* The runtime's cells and the shadow survive the body's writes (the box and the callee windows). *)
  Lemma body_rt : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> addressable mc ob 36 ->
    asan_cells mc -> shadow_rw mc ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> wmono rsegs mc mx ->
    asan_cells mx /\ shadow_rw mx.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO Aob ACc SRc MUb WMb.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    split.
    - apply (fl_asan_cells _ mc mx ACc MUb).
      intros x Hx. cbn [outside]. split; [|split; [|exact I]].
      + clear -Hx Obrt; unfold RT_LO, RT_HI in *; lia.
      + pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; clear -Hx HH0; unfold RT_LO, RT_HI in *; lia.
    - apply (fl_shadow_rw _ mc mx SRc MUb WMb).
      intros x Hx. cbn [outside]. split; [|split; [|exact I]].
      + intros [HL HR]. apply (acl_app_not_shadow x); [| exact Hx].
        pose proof (acl_app_in mc ob 36 (x - ob) Aob ltac:(lia)) as Ha.
        replace (ob + (x - ob)) with x in Ha by lia. exact Ha.
      + intros [HL HR]. apply (acl_app_not_shadow x); [| exact Hx].
        pose proof (acl_app_in m (S - 8800) 8800 (x - (S - 8800)) AW0 ltac:(clear -HL HR Hspc; lia)) as Ha.
        replace (S - 8800 + (x - (S - 8800))) with x in Ha by lia. exact Ha.
  Qed.

  (* A byte of the class-1 flag array other than flag j is apart from everything the frame block writes. *)
  Lemma flag_out_Wf : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    FS + 20480 <= x < FS + 28672 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + nn) ->
    outside (Wf fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx Hnotj.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & _ & _ & FSp4 & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    assert (Hxapp : app_mem x) by (apply FSp4; clear -Hx HFSb; unfold FS_SIZE; lia).
    assert (Efra0 : 0 <= fra) by (clear -FRlo FSp1; lia).
    assert (Efra128 : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    unfold Wf. cbn [outside].
    split; [clear -Hx HFSb; lia|].
    split; [unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; clear -Hx; lia|].
    split; [exact Hnotj|].
    split; [clear -Hx FRlo; lia|].
    split; [|exact I].
    pose proof (sh_add8 fra 16 FR8) as Esh. replace (fra + 8 * 16) with (fra + 128) in Esh by lia.
    rewrite <- Esh. exact (acl_sh_out x fra (fra + 128) Hxapp Efra0 Efra128).
  Qed.

  (* Every exit of the body reaches 0x83920 in a memory mx that the body produced from mc writing only the box
     and the callee windows, with a0 = the parse's kind and the box holding the parse's bytes: L_exit's
     premises, assembled once. *)
  Lemma L_join : forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> wmono rsegs mc mx ->
    mem_inv rsegs mx -> stk rsegs mx (S - 8800) S ->
    rw_cells rsegs mx ob [CB 36 (snd (ctrlparse n fr))] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mx (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc ob mx x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HK HB HFL HO MUb WMb MIx STx RWx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct HB as (MU & WM & RM & MI & SV).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    (* the box bytes and the window are readable at mx, so every byte readable at mc still is *)
    assert (RMb : rd_mono mc mx).
    { pose proof RWx as RWbk. destruct RWbk as [[_ Hbx] _]. cbn [cells_bytes cbytes] in Hbx.
      rewrite app_nil_r in Hbx.
      apply (rd_mono_list _ mc mx MUb). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbx). rewrite ctrlparse_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STx). clear -Hy Hspcr RS; lia. }
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (MUx : munch (Wex fra) m mx).
    { eapply munch_trans;
        [ eapply munch_weaken; [exact (subWf_Wex fra fv spc j nn w120 HK) | exact MU]
        | eapply munch_weaken; [exact (ob_wex fra fv spc j nn w120 ob HK HO) | exact MUb] ]. }
    assert (WMx : wmono rsegs m mx) by (eapply wmono_trans; [exact WM | exact WMb]).
    assert (RMx : rd_mono m mx) by (eapply rd_mono_trans; [exact RM | exact RMb]).
    assert (STfs : stk rsegs mx FS (FS + FS_SIZE)) by (exact (stk_mono m mx _ _ Pfsstk WMx RMx)).
    eapply L_exit.
    - exact HK.
    - exact MUx.
    - exact WMx.
    - exact RMx.
    - exact MIx.
    - exact (fl_asan_cells (Wex fra) m mx AC0 MUx
               (fun x Hx => aout_rt (Wex fra) x (Wex_subW fra fv spc j nn w120 HK) Hx)).
    - exact (shadow_rw_mono m mx SR0 WMx RMx).
    - exact STx.
    - apply (rw_cells_transport rsegs _ mc mx (S - 96) SAVES SV MUb WMb).
      cbn [disjoint_from cells_size csize SAVES fst snd].
      split; [clear -Obsv RS; lia|]. split; [right; clear -Hspcr; lia | exact I].
    - intros Ho. destruct HO as [(Eo & _) | (_ & Eob)]; [exfalso; exact (Ho Eo) | rewrite <- Eob; exact RWx].
    - destruct (rd8_le8 mx (fs_hint FS 1)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0; lia)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0 HFSb RS; lia)
                 ltac:(intros i Hi; apply (rd_of_stk _ _ _ STfs);
                       unfold fs_hint, FS_SIZE; cbn [Z.of_nat]; clear -Hi Pfs0; lia)) as [hh Hhint].
      exists hh. exact Hhint.
    - destruct HFL as [(flg & Hfl & Hfln & HflF) _].
      exists flg. split; [|split; [exact Hfln | exact HflF]].
      eapply fl_bytes; [exact Hfl | exact MUb |].
      intros x Hx. rewrite Hfln, EM1, EFL0 in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + clear -Hx Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
      + clear -Hx HFSb Pfs0 Hspcr RS; lia.
    - intros Enn. destruct HFL as [_ Hw]. pose proof (Hw Enn) as Hw120.
      assert (Hfrside : fra + 128 <= S - 8800).
      { destruct HK as [(_ & _ & _ & _ & Enn0) | (Hj & Efra & _)]; [clear -Enn Enn0; lia|].
        rewrite EM1 in Hj. rewrite Efra. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. clear -Hj HFSb Pfs0; lia. }
      eapply fl_bytes; [exact Hw120 | exact MUb |].
      intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + destruct Obfr as [Eob | Hout]; [clear -Hx Eob; lia | clear -Hx Hout; lia].
      + clear -Hx Hfrside Hspcr RS; lia.
    - (* the class-1 flag array: the frame block wrote only flag j there, the body none of it *)
      intros x Hx Hnj.
      assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
      assert (Hbd : 0 <= x < 2 ^ 64) by (clear -Hxr Pfs0 HFSb RS; lia).
      rewrite (munch_mrd_out _ mc mx x MUb Hbd).
      + exact (munch_mrd_out _ m mc x MU Hbd (flag_out_Wf fra fv spc j nn w120 x HK Hxr Hnj)).
      + cbn [outside]. split; [|split; [|exact I]].
        * clear -Hxr Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
        * clear -Hxr HFSb Pfs0 Hspcr RS; lia.
  Qed.

  (* ================= the body (0x836a8 .. exits) ================= *)

  (* What the body carries from the box's creation (mc) to the current memory. *)
  Definition BJ (ob spc : Z) (mc mx : word -> option byte) : Prop :=
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx /\ wmono rsegs mc mx /\ mem_inv rsegs mx /\
    stk rsegs mx (S - 8800) S.

  (* A window whose upper part the callee only rewrote where the caller can still read stays a stack window. *)
  Lemma stk_join_call : forall (m1 m2 : word -> option byte) lo mid hi W,
    stk rsegs m1 lo hi -> stk rsegs m2 lo mid -> munch W m1 m2 -> wmono rsegs m1 m2 ->
    (forall x, mid <= x < hi -> outside W x \/ exists b, mrd rsegs m2 (wa x) = Some b) -> lo <= mid <= hi ->
    stk rsegs m2 lo hi.
  Proof.
    intros m1 m2 lo mid hi W (L1 & L2 & H1) (_ & _ & H2) MU WM HO Hm.
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Z_lt_le_dec a mid) as [Hlt|Hge]; [apply H2; lia|].
    destruct (H1 a ltac:(lia)) as (Hv & b & Hb). split; [apply WM; exact Hv|].
    destruct (HO a ltac:(lia)) as [Hout|Hrdx]; [| exact Hrdx].
    exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
    rewrite wa_unsigned by lia. exact Hout.
  Qed.

  (* The body's carried state after a callee that wrote only inside the box and its own stack window. *)
  Lemma bj_call : forall ob spc mc (m1 m2 : word -> option byte) (D N K : Z) bs,
    BJ ob spc mc m1 -> munch [(D, D + N); (spc - K, spc)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
    stk rsegs m2 (S - 8800) spc -> rw_cells rsegs m2 D [CB (Z.to_nat N) bs] -> 0 <= N -> 0 <= K ->
    ob <= D -> D + N <= ob + 36 -> S - 8800 <= spc - K -> spc <= S ->
    BJ ob spc mc m2.
  Proof.
    intros ob spc mc m1 m2 D N K bs (MUb & WMb & MIx & STx) MU2 WM2 MI2 ST2 RW2 HN HK0 H1 H2 H3 H4.
    pose proof RW2 as RW2'. destruct RW2' as [[Hwf Hbt] _]. cbn [cells_wf cell_wf] in Hwf.
    destruct Hwf as [Hlen _]. cbn [cells_bytes cbytes] in Hbt. rewrite app_nil_r in Hbt.
    split; [| split; [| split]].
    - eapply munch_trans; [exact MUb |]. eapply munch_weaken; [| exact MU2].
      intros x Hx. cbn [outside] in *. destruct Hx as (Hb & Hw & _).
      split; [clear -Hb H1 H2; lia | split; [clear -Hw H3 H4; lia | exact I]].
    - eapply wmono_trans; [exact WMb | exact WM2].
    - exact MI2.
    - eapply (stk_join_call m1 m2 (S - 8800) spc S [(D, D + N); (spc - K, spc)] STx ST2 MU2 WM2);
        [ intros x Hx;
          destruct (Z_lt_le_dec x D) as [Hlt|Hge];
          [ left; cbn [outside]; split; [clear -Hlt; lia | split; [clear -Hx; lia | exact I]]
          | destruct (Z_lt_le_dec x (D + N)) as [Hin|Hout];
            [ right; apply (rd_of_bytes _ _ _ Hbt); rewrite Hlen, Z2Nat.id by exact HN; clear -Hge Hin; lia
            | left; cbn [outside]; split; [clear -Hout; lia | split; [clear -Hx; lia | exact I]] ] ]
        | split; [clear -H3 HK0; lia | exact H4] ].
  Qed.

  (* The same, for a callee that wrote only its own stack window. *)
  Lemma bj_call0 : forall ob spc mc (m1 m2 : word -> option byte) (K : Z),
    BJ ob spc mc m1 -> munch [(spc - K, spc)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
    stk rsegs m2 (S - 8800) spc -> 0 <= K -> S - 8800 <= spc - K -> spc <= S ->
    BJ ob spc mc m2.
  Proof.
    intros ob spc mc m1 m2 K (MUb & WMb & MIx & STx) MU2 WM2 MI2 ST2 HK0 H3 H4.
    split; [| split; [| split]].
    - eapply munch_trans; [exact MUb |]. eapply munch_weaken; [| exact MU2].
      intros x Hx. cbn [outside] in *. destruct Hx as (Hb & Hw & _).
      split; [clear -Hw H3 H4; lia | exact I].
    - eapply wmono_trans; [exact WMb | exact WM2].
    - exact MI2.
    - eapply (stk_join_call m1 m2 (S - 8800) spc S [(spc - K, spc)] STx ST2 MU2 WM2);
        [ intros x Hx; left; cbn [outside]; split; [clear -Hx; lia | exact I]
        | split; [clear -H3 HK0; lia | exact H4] ].
  Qed.

  (* The box stays addressable: the body writes no shadow byte. *)
  Lemma ob_mx : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    addressable mc ob 36 -> addressable mx ob 36.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MUb Aob.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    apply (acl_addr_munch [(ob, ob + 36); (S - 8800, spc)] mc mx ob 36 Aob MUb).
    intros i Hi.
    pose proof (acl_app_in mc ob 36 i Aob Hi) as Hoi.
    pose proof (rt_app_shadow (ob + i) Hoi) as Hsh.
    cbn [outside]. split; [| split; [| exact I]].
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (ob + i))); [| exact Hsh].
      pose proof (acl_app_in mc ob 36 (shadow_addr (ob + i) - ob) Aob ltac:(clear -HL HR; lia)) as Ha.
      replace (ob + (shadow_addr (ob + i) - ob)) with (shadow_addr (ob + i)) in Ha by lia. exact Ha.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (ob + i))); [| exact Hsh].
      pose proof (acl_app_in m (S - 8800) 8800 (shadow_addr (ob + i) - (S - 8800)) AW0
                    ltac:(clear -HL HR Hspc; lia)) as Ha.
      replace (S - 8800 + (shadow_addr (ob + i) - (S - 8800))) with (shadow_addr (ob + i)) in Ha by lia.
      exact Ha.
  Qed.

  (* The 50 bytes at f stay addressable through the body's writes. *)
  Lemma af_mx : 50 <= n -> forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> addressable mc ob 36 ->
    munch (Wall fra j nn ob) m mx -> addressable mx f 50.
  Proof.
    intros Hn50 fra fv spc j nn w120 ob mc mx HK HO Aob MUall.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof DFf as DFf'. unfold Wall, Wf in DFf'. cbn [disjoint_from app fst snd] in DFf'.
    destruct DFf' as (Dwin & Dhint & Dflag & Dfr & Dsh & Dbox & _).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    apply (acl_addr_munch (Wall fra j nn ob) m mx f 50 AFm MUall).
    intros i Hi.
    pose proof (acl_app_in m f 50 i AFm Hi) as Hfi.
    pose proof (rt_app_shadow (f + i) Hfi) as Hsh.
    unfold Wall, Wf. cbn [outside app].
    split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      pose proof (acl_app_in m (S - 8800) 8800 (shadow_addr (f + i) - (S - 8800)) AW0
                    ltac:(clear -HL HR; lia)) as Ha.
      replace (S - 8800 + (shadow_addr (f + i) - (S - 8800))) with (shadow_addr (f + i)) in Ha by lia.
      exact Ha.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_hint in HL, HR. cbn [Z.of_nat] in HL, HR. unfold FS_SIZE.
      clear -HL HR Pfs0; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_flag in HL, HR. cbn [Z.of_nat Pos.of_succ_nat] in HL, HR.
      change (2 ^ 15) with 32768 in HL, HR. change (2 ^ (15 - 1)) with 16384 in HL, HR.
      unfold FS_SIZE. clear -HL HR Pfs0 Hjnn; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      replace (shadow_addr (f + i)) with (fra + (shadow_addr (f + i) - fra)) by lia.
      apply FAP; clear -HL HR; lia.
    - intros HC. rewrite E16 in HC.
      exact (acl_win_sh (f + i) fra (fra + 128) FR8 ltac:(clear -Hi Dfr; lia) HC).
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      pose proof (acl_app_in mc ob 36 (shadow_addr (f + i) - ob) Aob ltac:(clear -HL HR; lia)) as Ha.
      replace (ob + (shadow_addr (f + i) - ob)) with (shadow_addr (f + i)) in Ha by lia. exact Ha.
  Qed.

  (* The same facts, stated from the two munches the body actually carries (no Wall hypothesis is kept in the
     context: the store tactics must see only concrete footprints). *)
  Lemma af_mx2 : 50 <= n -> forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wf fra j nn) m mc -> addressable mc ob 36 ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> addressable mx f 50.
  Proof.
    intros Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb.
    exact (af_mx Hn50 fra fv spc j nn w120 ob mc mx HK HO Aob (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
  Qed.

  (* The frame bytes [lo, lo + len), read back in the memory the body reached. *)
  Lemma ro_mx : 50 <= n -> forall fra fv spc j nn w120 ob mc (mx : word -> option byte) (lo len : nat),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wf fra j nn) m mc -> addressable mc ob 36 ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    (forall jx, (jx < len)%nat -> In (lo + jx)%nat (cp_rd n fr)) -> (lo + len <= 50)%nat ->
    ro_cells rsegs mx (f + Z.of_nat lo) (map C1 (map (cp_b fr) (seq lo len))).
  Proof.
    intros Hn50 fra fv spc j nn w120 ob mc mx lo len HK HO MU Aob MUb HIN Hlen.
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    apply (rc_ro_now rsegs (Wall fra j nn ob) m mx f fr lo len (cp_rd n fr) Hrd HIN
             ltac:(rewrite Lfr; lia) ltac:(lia) ltac:(rewrite Lfr; cbn [Z.of_nat]; lia)
             (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
    eapply disjoint_from_sub;
      [ exact DFf | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia ].
  Qed.

  (* The frame bytes [lo, lo + len), read back in the memory the run reached. *)
  Ltac rdb lo len tac :=
    let HIN := fresh "HIN" in
    assert (HIN : forall jx, (jx < len)%nat -> In (lo + jx)%nat (cp_rd n fr)) by tac;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let R := fresh "RO" in
        assert (R : ro_cells rsegs mcur (f + Z.of_nat lo) (map C1 (map (cp_b fr) (seq lo len))))
          by (eapply ro_mx;
              [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact HIN | cbn [Nat.add]; lia ]);
        cbn [map seq] in R;
        let z := eval vm_compute in (Z.of_nat lo) in change (Z.of_nat lo) with z in R;
        rewrite ?Z.add_0_r in R
    end;
    clear HIN.

  (* `mv r,s10; beqz s4; mv r,s4` at a join: r holds the box pointer on both paths, continuing at tgt. *)
  Ltac obsel r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the addressable ranges at the memory the run reached *)
  Ltac refresh :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let A1 := fresh "AFx" in
        assert (A1 : addressable mcur f 50) by (eapply af_mx2; eassumption);
        match goal with
        | HOb : OB _ ?obq |- _ =>
            let A2 := fresh "Aobx" in
            assert (A2 : addressable mcur obq 36) by (eapply ob_mx; eassumption)
        end
    end.

  (* the shadow check of the one-byte load of frame byte i *)
  Ltac chkf i r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let RX := fresh "RX" in let SH := fresh "SH" in
        assert (RX : 0 <= f + i < 2 ^ 64)
          by (match goal with Hb : 0 <= f /\ f + 50 <= 2 ^ 64 |- _ => clear -Hb; lia end);
        pose proof (acl_shadow mcur f 50 i 1 (f + i) ltac:(eassumption) ltac:(clear; lia) ltac:(clear; lia)
                      ltac:(clear; lia)
                      ltac:(let MB := fresh "MB" in
                            pose proof (Z.mod_pos_bound (f + i) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                      ltac:(clear; lia)) as SH;
        chk_core (f + i) RX r SH pre_sr no_extra
    end.

  (* the shadow check of the four-byte access at the box pointer itself (offset 0: the address register holds ob,
     with no added literal) *)
  Ltac chkb0 r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ =>
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            chk_core obq RX r SH pre_sr extra
        end
    end.

  (* the same check where the fast path is the TAKEN branch (`beqz` instead of `bnez`, at 0x83a90) *)
  Ltac chkb0inv r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ =>
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            let kk := fresh "kk" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
            destruct SH as (kk & RK & OK & KR);
            pre_sr obq RX; steps_until_if; clear RK;
            unfold sxb; rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR; lia);
            lazymatch goal with
            | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm (if _ then ?B1 else _) ?fcc ?rv ?mm ?ro) =>
                let G := fresh "G" in
                enough (G : forall rr : word, evtF segs rgq Q (MS (bvmap_set r rr R) Fm B1 fcc rv mm ro));
                [ destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbv iota;
                  [ bjoin G r
                  | step; rewrite ?(unsigned_lit obq) by (clear -RX; lia); rewrite rc_land7; add3 obq;
                    step;
                    let MB := fresh "MB" in pose proof (Z.mod_pos_bound obq 8 eq_refl) as MB;
                    rewrite (rc_lts_signed (obq mod 8 + 3) (bv_signed kk)) by (clear -MB KR; lia);
                    replace (obq mod 8 + 3 <? bv_signed kk) with true
                      by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK];
                          [exfalso; exact (K0 OK) | clear -OK; lia]);
                    clear MB; cbv iota; bjoin G r ]
                | intros ?; simp_regs; clear OK KR ]
            end
        end
    end.

  (* `beqz s4; mv r,s4` (0x83c38): r holds the box pointer on both paths *)
  Ltac obsel2 r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the shadow check of a w-byte access at ob + k *)
  Ltac chkb k w r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ =>
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq + k < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 k w (obq + k) AO ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear; lia)
                          ltac:(apply (acl_mod_al obq k w); [eassumption | clear; lia | clear; lia])
                          ltac:(clear; lia)) as SH;
            chk_core (obq + k) RX r SH pre_sr extra
        end
    end.

  (* The six bytes at .str.4 that the bcmp wrapper compares with stay addressable. *)
  Lemma abc_mx : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> addressable mc ob 36 ->
    munch (Wall fra j nn ob) m mx -> addressable mx REAC_CTRL_PARSE_BC 6.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO Aob MUall.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    apply (acl_addr_munch (Wall fra j nn ob) m mx REAC_CTRL_PARSE_BC 6 ABC MUall).
    intros i Hi.
    pose proof (acl_app_in m REAC_CTRL_PARSE_BC 6 i ABC Hi) as Hbi.
    pose proof (rt_app_shadow (REAC_CTRL_PARSE_BC + i) Hbi) as Hsh.
    unfold Wall, Wf. cbn [outside app].
    split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      pose proof (acl_app_in m (S - 8800) 8800 (shadow_addr (REAC_CTRL_PARSE_BC + i) - (S - 8800)) AW0
                    ltac:(clear -HL HR; lia)) as Ha.
      replace (S - 8800 + (shadow_addr (REAC_CTRL_PARSE_BC + i) - (S - 8800)))
        with (shadow_addr (REAC_CTRL_PARSE_BC + i)) in Ha by lia.
      exact Ha.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_hint in HL, HR. cbn [Z.of_nat] in HL, HR. unfold FS_SIZE.
      clear -HL HR Pfs0; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_flag in HL, HR. cbn [Z.of_nat Pos.of_succ_nat] in HL, HR.
      change (2 ^ 15) with 32768 in HL, HR. change (2 ^ (15 - 1)) with 16384 in HL, HR.
      unfold FS_SIZE. clear -HL HR Pfs0 Hjnn; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      replace (shadow_addr (REAC_CTRL_PARSE_BC + i)) with (fra + (shadow_addr (REAC_CTRL_PARSE_BC + i) - fra))
        by lia.
      apply FAP; clear -HL HR; lia.
    - intros HC. rewrite E16 in HC.
      exact (acl_win_sh (REAC_CTRL_PARSE_BC + i) fra (fra + 128) FR8
               ltac:(unfold REAC_CTRL_PARSE_BC; clear -Hi FRlo Pfs0 Pfs2; lia) HC).
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      pose proof (acl_app_in mc ob 36 (shadow_addr (REAC_CTRL_PARSE_BC + i) - ob) Aob
                    ltac:(clear -HL HR; lia)) as Ha.
      replace (ob + (shadow_addr (REAC_CTRL_PARSE_BC + i) - ob))
        with (shadow_addr (REAC_CTRL_PARSE_BC + i)) in Ha by lia.
      exact Ha.
  Qed.

  (* The cells the bcmp wrapper reads lie below the side stack and apart from the box. *)
  Lemma cl_mx : forall fra fv spc j nn w120 ob (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wall fra j nn ob) m mx -> aCL mx.
  Proof.
    intros fra fv spc j nn w120 ob mx HK HO MUall.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof HHM as HHM0. unfold HIGHMEM_BEG in HHM0.
    assert (DJ : forall a len, 0 <= a -> a + len <= CF + 256 -> GOT_CF <= a -> 0 <= len ->
                 disjoint_from (Wall fra j nn ob) a len).
    { intros a len Ha0 Hae Hag Hl. unfold Wall, Wf. cbn [disjoint_from app fst snd].
      split; [unfold GOT_CF, CF in *; clear -Hae Hag HHM0; lia|].
      split; [unfold fs_hint, GOT_CF, CF in *; cbn [Z.of_nat];
              clear -Hae Hag Pfs2 Pfs0; lia|].
      split; [unfold fs_flag, GOT_CF, CF in *; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384;
              clear -Hae Hag Pfs2 Pfs0 Hjnn; lia|].
      split; [unfold GOT_CF, CF in *; clear -Hae Hag FRlo Pfs2 Pfs0; lia|].
      split; [unfold shadow_addr, ASAN_K, GOT_CF, CF in *; clear -Hae Hag Ha0 FRlo Pfs0; lia|].
      split; [unfold GOT_CF, CF in *; clear -Hae Hag Obcf; lia | exact I]. }
    split; [| split; [| split; [| split]]].
    - apply (bytes_at_transport rsegs _ m mx REAL_BCMP _ HBCMP MUall).
      apply DJ; unfold REAL_BCMP, GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx REAL_MEMCMP _ HMEMCMP MUall).
      apply DJ; unfold REAL_MEMCMP, GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx GOT_CF _ HGCF MUall).
      apply DJ; unfold GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx (CF + 254) _ HCF254 MUall).
      apply DJ; unfold GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx (CF + 255) _ HCF255 MUall).
      apply DJ; unfold GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
  Qed.

  Lemma abc_mx2 : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wf fra j nn) m mc -> addressable mc ob 36 ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    addressable mx REAC_CTRL_PARSE_BC 6.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb.
    exact (abc_mx fra fv spc j nn w120 ob mc mx HK HO Aob (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
  Qed.

  Lemma cl_mx2 : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob ->
    munch (Wf fra j nn) m mc -> munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> aCL mx.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MU MUb.
    exact (cl_mx fra fv spc j nn w120 ob mx HK HO (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
  Qed.

  (* The 24 bytes the body writes at ob + 4 (P1 of lib/Prog/reac_ctrl_parse.v). *)
  Definition P1 : list byte :=
    [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11;
     cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5;
     (if cp_bcast fr then Z_to_bv 8 1 else cp_z); cp_z; cp_z; cp_z;
     cp_b fr 14; cp_b fr 15; cp_b fr 18; cp_b fr 19; cp_b fr 21; cp_b fr 20; cp_b fr 22; cp_z].

  (* 0x83ac8: the kind is stored into the box (its shadow check was done before the jump), then the exit. *)
  Lemma L_kind : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ac8) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG RINF SCF SKF RBC SKBC RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    destruct HBJ as (MUb & WMb & MIx & STx).
    step. step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HKc' end.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca8: the stored kind is checked, read back, and the run exits. *)
  Lemma L_be0 : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [C4 (Z_to_bv 64 k)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca8) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG RINF SCF SKF RBC SKBC RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22
      x26 x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc' HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    destruct HBJ as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (Aobx : addressable mcur ob 36) by (eapply ob_mx; eassumption)
    end.
    chkb0 (Z_to_bv 5 11) add3.
    step. rewrite (rcp_sx32 k) by (clear -Hk; lia).
    step.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca4: the kind is stored into the box, checked, read back, then the exit. *)
  Lemma L_bdc : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca4) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG RINF SCF SKF RBC SKBC RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HK4 end.
    eapply (L_be0 fra fv spc j nn w120 mc ob _ k tg amp);
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj _ (conj _ (conj _ _))); eassumption
      | exact Aob | exact HK4 | eassumption | eassumption | eassumption
      | exact Ek | exact Hk | exact EB ].
  Qed.

  (* the plain proof's condition normaliser and branch splitter (lib/Prog/reac_ctrl_parse.v) *)
  Ltac cond_norm :=
    rewrite ?rc_lor0;
    rewrite ?rc_eqb_zxb by (clear; lia);
    repeat match goal with
    | |- context [bv_unsigned (cp_b fr ?i)] => change (bv_unsigned (cp_b fr i)) with (cp_v fr i)
    end.

  Ltac br :=
    cond_norm;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if negb (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    | |- evtF _ _ _ (MS _ _ (if (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    end.

  (* walk the kind dispatch, stopping at every leaf (each leaf checks the box before it stores the kind) *)
  Ltac drive :=
    repeat (lazymatch goal with
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539276) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539368) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
            end).

  (* the kind and the box bytes of a leaf (kfact / bfact of the plain proof) *)
  Ltac kfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [fst];
    unfold cp_kind, cp_type, cp_amp; zeval; reflexivity.
  Ltac bfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [snd];
    unfold cp_struct, cp_rec, cp_kind, cp_type, cp_amp, P1; zeval; zeval; reflexivity.

  Ltac leafk :=
    eapply L_kind;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].
  Ltac leafb :=
    eapply L_bdc;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].

  (* after the two tag bytes are stored, the box's [ob + 28] cell is a C2: flatten it back to the two
     bytes cp_struct names, so that a leaf below the record can still apply L_kind / L_bdc *)
  Ltac flat_tg :=
    match goal with
    | HOb : OB _ ?obq |- _ =>
        match goal with
        | Hq : rw_cells rsegs _ (obq + 28) [C2 _] |- _ =>
            apply (rc_rw_flat rsegs _ (obq + 28) _ [cp_b fr 35; cp_b fr 34]) in Hq;
            [ cbn [length] in Hq
            | first [ cbn [cells_bytes cbytes]; rewrite rc_le2_pack; reflexivity
                    | cbn [cells_bytes cbytes app]; rewrite rc_le2_pack; reflexivity
                    | vm_compute; reflexivity ] ]
        end
    end.

  Ltac leaves :=
    lazymatch goal with
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafk
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafb
    end.

  (* 0x8370c .. 0x8375c: the two copies into the box, the broadcast comparison and its 4-byte store. *)
  Lemma body_copy : 50 <= n -> cp_hdr n fr = true ->
    forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG Qp
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 ob) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8370c) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL HMSET MI0 RFSS RFW1 RTLS. pf_hide.
    intros Hn50 HE fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pf_h SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    destruct (HF Hn50) as (_ & _ & HfS).
    pose proof (Obf Hn50) as Hobf.
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (Rob10 : 0 <= ob + 10 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rob4 : 0 <= ob + 4 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rf6 : 0 <= f + 6 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    assert (STsp : stk rsegs mx (S - 8800) spc)
      by (apply (stk_sub mx (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    destruct (body_rt fra fv spc j nn w120 ob mc mx HK HO Aob ACc SRc MUb WMb) as (ACx & SRx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc mx HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0.
    cbn [map seq firstn skipn] in BD0. rewrite Z.add_0_r in BD0.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 6 6 RO ltac:(cbn; lia)) as BD1.
    cbn [map seq firstn skipn] in BD1. change (Z.of_nat 6) with 6 in BD1.
    clear RO.
    (* the pieces of the box the body writes *)
    destruct (rc_rw_cut_at rsegs _ ob cp_z 36 4 (ob + 4) RWx ltac:(lia) ltac:(lia)) as [HKc HZ1];
      cbn [Nat.sub] in HZ1.
    destruct (rc_rw_cut_at rsegs _ (ob + 4) cp_z 32 6 (ob + 10) HZ1 ltac:(lia) ltac:(lia)) as [HSRC HZ2];
      cbn [Nat.sub] in HZ2.
    destruct (rc_rw_cut_at rsegs _ (ob + 10) cp_z 26 6 (ob + 16) HZ2 ltac:(lia) ltac:(lia)) as [HDST HZ3];
      cbn [Nat.sub] in HZ3.
    destruct (rc_rw_cut_at rsegs _ (ob + 16) cp_z 20 12 (ob + 28) HZ3 ltac:(lia) ltac:(lia)) as [HMID HZ4];
      cbn [Nat.sub] in HZ4.
    destruct (rc_rw_cut_at rsegs _ (ob + 28) cp_z 8 2 (ob + 30) HZ4 ltac:(lia) ltac:(lia)) as [HTG HAMP];
      cbn [Nat.sub] in HAMP.
    clear HZ1 HZ2 HZ3 HZ4 RWx.
    pose proof HMCPY as HMC. unfold asan_memcpy_contract_F, ASAN_MEMCPY_K in HMC. cbv zeta in HMC.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMC.
    (* 0x8370c: __asan_memcpy(ob + 10, f, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 10) Rob10), ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD0.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HDST.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub mx f 50 f 6 AFx); clear; lia.
      - apply (acl_addr_sub mx ob 36 (ob + 10) 6 Aobx); clear; lia.
      - right. apply (acl_app_in mx f 50 6 AFx); clear; lia.
      - right. replace (ob + 10 + 6) with (ob + 16) by lia. apply (acl_app_in mx ob 36 16 Aobx); clear; lia.
      - right. split; [ apply (acl_app_in mx f 50 7 AFx); clear; lia
                      | replace (ob + 10 + 7) with (ob + 17) by lia;
                        apply (acl_app_in mx ob 36 17 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACx.
      - exact SRx.
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 &
                       Hms & MU1 & WM1 & MI1 & ST1 & RW1 & BS1 & AC1 & SR1).
    subst ms'.
    rewrite (ret_pc_even 538396 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob10), U6, (unsigned_lit spc Rspc) in MU1.
    rewrite (unsigned_lit _ Rob10), U6 in RW1.
    rewrite (unsigned_lit _ Rf) in BS1.
    rewrite (unsigned_lit spc Rspc) in ST1.
    unfold ASAN_MEMCPY_K in MU1. change (Z.to_nat 6) with 6%nat in RW1.
    pose proof (bj_call ob spc mc mx m1 (ob + 10) 6 2224 _ HBJ MU1 WM1 MI1 ST1 RW1
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ1.
    pose proof (rw_cells_transport rsegs _ mx m1 ob [CB 4 (repeat cp_z 4)] HKc MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 4) [CB 6 (repeat cp_z 6)] HSRC MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HSRC1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 16) [CB 12 (repeat cp_z 12)] HMID MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 28) [CB 2 (repeat cp_z 2)] HTG MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP1.
    pose proof (bytes_at_transport rsegs _ mx m1 (f + 6) [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                          cp_b fr 10; cp_b fr 11] BD1 MU1
                  ltac:(cbn [disjoint_from length]; clear -Hobf Hf0 Hf64 HfS Hspcr RS; lia)) as BD1a.
    clear HKc HSRC HMID HTG HAMP BD0 BD1 MU1 WM1 MI1 ST1 HBJ MUb WMb MIx STx STsp ACx SRx Aobx AFx.
    pose proof HBJ1 as HBJ1'. destruct HBJ1' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m1 (S - 8800) spc)
      by (apply (stk_sub m1 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m1 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m1 HK HO MU Aob MUb) as AFx.
    (* 0x8371c: __asan_memcpy(ob + 4, f + 6, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 4) Rob4), ?(unsigned_lit (f + 6) Rf6), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD1a.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HSRC1.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub m1 f 50 (f + 6) 6 AFx); clear; lia.
      - apply (acl_addr_sub m1 ob 36 (ob + 4) 6 Aobx); clear; lia.
      - right. replace (f + 6 + 6) with (f + 12) by lia. apply (acl_app_in m1 f 50 12 AFx); clear; lia.
      - right. replace (ob + 4 + 6) with (ob + 10) by lia. apply (acl_app_in m1 ob 36 10 Aobx); clear; lia.
      - right. split; [ replace (f + 6 + 7) with (f + 13) by lia; apply (acl_app_in m1 f 50 13 AFx); clear; lia
                      | replace (ob + 4 + 7) with (ob + 11) by lia;
                        apply (acl_app_in m1 ob 36 11 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC1.
      - exact SR1.
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 &
                       Hms & MU2 & WM2 & MI2 & ST2 & RW2 & BS2 & AC2 & SR2).
    subst ms'.
    rewrite (ret_pc_even 538412 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob4), U6, (unsigned_lit spc Rspc) in MU2.
    rewrite (unsigned_lit _ Rob4), U6 in RW2.
    rewrite (unsigned_lit _ Rf6) in BS2.
    rewrite (unsigned_lit spc Rspc) in ST2.
    unfold ASAN_MEMCPY_K in MU2. change (Z.to_nat 6) with 6%nat in RW2.
    pose proof (bj_call ob spc mc m1 m2 (ob + 4) 6 2224 _ HBJ1 MU2 WM2 MI2 ST2 RW2
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ2.
    pose proof (rw_cells_transport rsegs _ m1 m2 ob [CB 4 (repeat cp_z 4)] HKc1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1b.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 16) [CB 12 (repeat cp_z 12)] HMID1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 28) [CB 2 (repeat cp_z 2)] HTG1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP2.
    clear HKc1 HSRC1 HMID1 HTG1 HAMP1 RW1 BD1a MU2 WM2 MI2 ST2 HBJ1 MUb WMb MIx STx STsp Aobx AFx
      AC1 SR1.
    pose proof HBJ2 as HBJ2'. destruct HBJ2' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m2 (S - 8800) spc)
      by (apply (stk_sub m2 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m2 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as AFx.
    (* 0x8372c .. 0x8373c: the bcmp wrapper on the 6 bytes at f and the 6 bytes of .str.4 *)
    destruct (cl_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU MUb) as (CLa & CLb & CLc & CLd & CLe).
    pose proof (abc_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as ABCx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0c.
    cbn [map seq firstn skipn] in BD0c. rewrite Z.add_0_r in BD0c.
    clear RO.
    destruct (rc_memcmp_ff (cp_b fr 0) (cp_b fr 1) (cp_b fr 2) (cp_b fr 3) (cp_b fr 4) (cp_b fr 5))
      as (v & Hv & Hvr & Hvb).
    pose proof HBCMPW as HBW. unfold bcmp_wrap_contract_F, BCMP_WRAP_K in HBW. cbv zeta in HBW.
    assert (UBC : bv_unsigned (Z_to_bv 64 135680) = 135680) by reflexivity.
    do 5 step.
    eapply evtF_cut.
    { eapply HBW with (ls := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (rs := repeat (Z_to_bv 8 255) 6) (v := v) (lo := S - 8800);
        rewrite ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc), ?UBC.
      - exact BD0c.
      - apply (rc_ro_in_image rsegs _ _ (repeat (Z_to_bv 8 255) 6)); [exact MIx | vm_compute; reflexivity].
      - exact Hv.
      - exact MIx.
      - clear; lia.
      - apply (acl_addr_sub m2 f 50 f 6 AFx); clear; lia.
      - exact ABCx.
      - right. apply (acl_app_in m2 f 50 6 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - right. apply (acl_app_in m2 f 50 7 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - clear -HfS Hspcr RS; lia.
      - left. pose proof HHM as HH0. unfold HIGHMEM_BEG in HH0. clear -HH0 Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC2.
      - exact SR2.
      - exact CLa.
      - exact CLb.
      - exact CLc.
      - exact CLd.
      - exact CLe.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) exact RIMG.
      - (* the bcmp wrapper's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 6 input bytes *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* their aligned shadow word cover *) right. apply (rcpF_kov8 RNG f 50 _ _ SKINF); clear; lia.
      - (* the 6 bytes at .str.4 *) exact RBC.
      - (* their aligned shadow word cover *)
        right. apply (rcpF_kov8 RNG REAC_CTRL_PARSE_BC 6 _ _ SKBC); unfold REAC_CTRL_PARSE_BC; clear; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 &
                       Hms & MU3 & WM3 & MI3 & ST3 & AC3 & SR3 & BSl & BSr).
    subst ms'.
    rewrite (ret_pc_even 538432 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit spc Rspc) in MU3. rewrite (unsigned_lit spc Rspc) in ST3.
    unfold BCMP_WRAP_K in MU3.
    pose proof (bj_call0 ob spc mc m2 m3 4560 HBJ2 MU3 WM3 MI3 ST3
                  ltac:(clear; lia) ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ3.
    pose proof (rw_cells_transport rsegs _ m2 m3 ob [CB 4 (repeat cp_z 4)] HKc2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 4) [CB 6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                                cp_b fr 10; cp_b fr 11]] RW2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW2b.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1b MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1c.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 16) [CB 12 (repeat cp_z 12)] HMID2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 28) [CB 2 (repeat cp_z 2)] HTG2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP3.
    clear HKc2 RW2 RW1b HMID2 HTG2 HAMP2 BD0c MU3 WM3 MI3 ST3 HBJ2 MUb WMb MIx STx STsp Aobx AFx
      AC2 SR2 BSl BSr ABCx CLa CLb CLc CLd CLe.
    pose proof HBJ3 as HBJ3'. destruct HBJ3' as (MUb & WMb & MIx & STx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m3 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m3 HK HO MU Aob MUb) as AFx.
    (* 0x83740 .. 0x83758: the 4-byte store of the broadcast flag at ob + 16, checked *)
    step.
    assert (RX16 : 0 <= ob + 16 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    pose proof (acl_shadow m3 ob 36 16 4 (ob + 16) Aobx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Obmod; Z.div_mod_to_equations; lia) ltac:(clear; lia)) as SH16.
    chk_core (ob + 16) RX16 (Z_to_bv 5 13) SH16 pre_sr add3.
    step. step.
    (* 0x8375c .. 0x83900: the frame's fields, each load and each store behind its shadow check *)
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    refresh.
    step.                                      (* 0x8375c addi a0,s5,14 *)
    pf_uh SCINF; chkf 14%Z (Z_to_bv 5 12); pf_h SCINF.
    step.                                      (* 0x83770 addi a0,s5,15 *)
    pf_uh SCINF; chkf 15%Z (Z_to_bv 5 13); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538516.               (* 0x83788 .. 0x83794: a1 = ob *)
    step.                                      (* 0x83794 addi a1,a1,20 *)
    chkb 20%Z 2%Z (Z_to_bv 5 14) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,18, sh a2,0(a1) *)
    refresh.
    pf_uh SCINF; chkf 18%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538584.               (* 0x837cc .. 0x837d8 *)
    step.                                      (* 0x837d8 addi a1,a1,22 *)
    chkb 22%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a2,0(a1), addi a0,s5,19 *)
    refresh.
    pf_uh SCINF; chkf 19%Z (Z_to_bv 5 13); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538644.               (* 0x83808 .. 0x83814 *)
    step.                                      (* 0x83814 addi a1,a1,23 *)
    chkb 23%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a3,0(a1), addi a0,s5,20 *)
    refresh.
    pf_uh SCINF; chkf 20%Z (Z_to_bv 5 14); pf_h SCINF.
    step.                                      (* 0x83844 addi a0,s5,21 *)
    pf_uh SCINF; chkf 21%Z (Z_to_bv 5 15); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538728.               (* 0x8385c .. 0x83868 *)
    step.                                      (* 0x83868 addi a1,a1,24 *)
    chkb 24%Z 2%Z (Z_to_bv 5 16) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,22, sh a4,0(a1) *)
    refresh.
    pf_uh SCINF; chkf 22%Z (Z_to_bv 5 14); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538796.               (* 0x838a0 .. 0x838ac *)
    step.                                      (* 0x838ac addi a1,a1,26 *)
    chkb 26%Z 1%Z (Z_to_bv 5 15) no_extra.
    do 2 step.                                 (* sb a0,0(a1), addi a1,s5,16 *)
    refresh.
    pf_uh SCINF; chkf 16%Z (Z_to_bv 5 15); pf_h SCINF.
    step.                                      (* 0x838dc addi a1,s5,17 *)
    pf_uh SCINF; chkf 17%Z (Z_to_bv 5 16); pf_h SCINF.
    do 3 step.                                 (* lbu a1, zext.b, or a5,a4,a1 *)
    (* 0x83900: (fr[16] | fr[17]) = 0 is the filler, kind 1; else the kind dispatch at 0x83a14 *)
    rewrite ?rc_zextb.
    step.
    rewrite rc_lor0.
    change (bv_unsigned (cp_b fr 16)) with (cp_v fr 16).
    change (bv_unsigned (cp_b fr 17)) with (cp_v fr 17).
    match goal with H : rw_cells rsegs _ (ob + 4) [CB 6 _] |- _ => rename H into HSRCf end.
    match goal with H : rw_cells rsegs _ (ob + 10) [CB 6 _] |- _ => rename H into HDSTf end.
    match goal with H : rw_cells rsegs _ (ob + 16) _ |- _ => rename H into HMIDf end.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 10) _ _ HSRCf
                  ltac:(cbn [cells_size csize app]; lia) HDSTf) as J1.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 16) _ _ J1
                  ltac:(cbn [cells_size csize app]; lia) HMIDf) as J2.
    apply (rc_rw_flat rsegs _ (ob + 4) _ P1) in J2.
    2:{ cbn [app cells_bytes cbytes]. rewrite rc_le4_seqz by lia. rewrite !rc_le2_pack. rewrite Hvb.
        cbn [skipn repeat app]. unfold P1. reflexivity. }
    change (length P1) with 24%nat in J2.
    destruct ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)) eqn:T0; cbn [negb]; cbv iota.
    { idtac "F0".
      (* the filler: 0x83904 the 4-byte check at the box, 0x83914 li a0,1, 0x83918 -> 0x83ac8 *)
    rewrite andb_true_iff, !Z.eqb_eq in T0. destruct T0 as [T0a T0b].
    refresh. idtac "F1".
    chkb0 (Z_to_bv 5 11) add3. idtac "F2".
    step. step. idtac "F3".
    assert (EK1 : cp_kind fr = 1)
      by (unfold cp_kind, cp_type; rewrite T0a, T0b; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    assert (ERC : cp_rec fr = false)
      by (unfold cp_rec, cp_type; rewrite T0a; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    match goal with H : rw_cells rsegs _ ob [CB 4 _] |- _ => rename H into HKf end.
    match goal with H : rw_cells rsegs _ (ob + 28) [CB 2 _] |- _ => rename H into HTGf end.
    match goal with H : rw_cells rsegs _ (ob + 30) [CB 6 _] |- _ => rename H into HAMPf end.
    eapply (L_kind fra fv spc j nn w120 mc ob _ 1 (repeat cp_z 2) (repeat cp_z 6));
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj MUb (conj WMb (conj MIx STx)))
      | exact HKf | exact J2 | exact HTGf | exact HAMPf
      | unfold ctrlparse; rewrite HE; cbn [fst]; exact EK1
      | clear; lia
      | unfold ctrlparse; rewrite HE; cbn [snd]; unfold cp_struct; rewrite EK1, ERC;
        cbn [Z.eqb Pos.eqb repeat app]; unfold P1; reflexivity ]. }
    (* 0x83a14 ..: the kind dispatch *)
    pose proof (cp_v_range fr 16) as R16. pose proof (cp_v_range fr 17) as R17.
    pose proof (cp_v_range fr 18) as R18. pose proof (cp_v_range fr 19) as R19.
    pose proof (cp_v_range fr 22) as R22. pose proof (KL1_range (cp_v fr 22)) as KR.
    assert (KL6 : KL1 (cp_v fr 22) <> 6) by (clear -KR; lia).
    (* the dispatch does no more calls: drop the disjunctive premises, they make every store's
       transport (slia) split the context *)
    clear DFf Fapp Obrt Obsp Obsv Obfr Obcf Obf HfS AFm.
    drive.
    all: try leaves.
    (* goal 2: 0x83a8c, kind_of_link1 *)
    2:{ step.
        eapply evtF_cut; [eapply HKOL | intros ? [? ->]].
        rewrite rc_signed_zxb.
        change (bv_unsigned (cp_b fr 22)) with (cp_v fr 22).
        rewrite (ret_pc_even 539280 ltac:(clear; lia) ltac:(clear; lia)).
        refresh.
        chkb0inv (Z_to_bv 5 12).
        leafb. }
    (* goal 1: 0x83ae8, the record: fr[19] = 3, the two tag bytes, then the amp test *)
    step. step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 19) 3) as [E19|E19]; cbn [negb]; cbv iota.
    2:{ drive. all: leaves. }
    assert (HRC : cp_rec fr = true) by (unfold cp_rec, cp_type; zeval; reflexivity).
    rdb 34%nat 2%nat ltac:(intros jx Hjx; apply cp_rd_rec; [exact HE | exact HRC | lia]).
    rdb 32%nat 1%nat ltac:(intros jx Hjx; replace (32 + jx)%nat with 32%nat by lia;
                           apply cp_rd_rec; [exact HE | exact HRC | lia]).
    refresh.
    step. pf_uh SCINF; chkf 34%Z (Z_to_bv 5 12); pf_h SCINF.
    step. pf_uh SCINF; chkf 35%Z (Z_to_bv 5 13); pf_h SCINF.
    obsel (Z_to_bv 5 11) 539432.
    step. chkb 28%Z 2%Z (Z_to_bv 5 14) add1.
    do 4 step.
    refresh.
    pf_uh SCINF; chkf 32%Z (Z_to_bv 5 13); pf_h SCINF.
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 32) 18) as [E32|E32]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    rdb 33%nat 1%nat ltac:(intros jx Hjx; replace (33 + jx)%nat with 33%nat by lia;
                           apply cp_rd_33; [exact HE | exact HRC | exact E32]).
    step. pf_uh SCINF; chkf 33%Z (Z_to_bv 5 13); pf_h SCINF.
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 33) 18) as [E33|E33]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    do 2 step.
    rewrite rc_pack_eqb by (clear; lia).
    change (bv_unsigned (cp_b fr 34)) with (cp_v fr 34).
    change (bv_unsigned (cp_b fr 35)) with (cp_v fr 35).
    destruct (Z.eqb_spec (cp_v fr 34 * 256 + cp_v fr 35) 257) as [EP|EP]; cbn [negb]; cbv iota.
    2:{ flat_tg.
        destruct (Z.eqb_spec (cp_v fr 34) 1) as [E34a|E34a];
          [ assert (E35a : cp_v fr 35 <> 1)
              by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
                  clear -A34 A35 EP E34a; lia)
          | ];
          drive; leaves. }
    assert (E34 : cp_v fr 34 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    assert (E35 : cp_v fr 35 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    refresh. chkb0 (Z_to_bv 5 11) add3.
    do 3 step.
    assert (EK6 : cp_kind fr = 6) by (unfold cp_kind, cp_type, cp_amp; zeval; reflexivity).
    rdb 36%nat 3%nat ltac:(intros jx Hjx; apply cp_rd_amp; [exact HE | exact HRC | exact EK6 | lia]).
    refresh.
    pf_uh SCINF; chkf 36%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel (Z_to_bv 5 11) 539596.
    step. chkb 30%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    pf_uh SCINF; chkf 37%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel (Z_to_bv 5 11) 539656.
    step. chkb 31%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    pf_uh SCINF; chkf 38%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel2 (Z_to_bv 5 26) 539712.
    step. chkb 32%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    flat_tg.
    match goal with
    | HOb : OB ?fraq ?obq |- _ =>
        match goal with Hq : rw_cells rsegs _ (obq + 30) _ |- _ => rename Hq into HAMPr end;
        apply (rc_rw_flat rsegs _ (obq + 30) _
                 ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3)) in HAMPr;
        [ cbn [length app repeat] in HAMPr
        | first [ reflexivity
                | cbn [cells_bytes cbytes app repeat skipn firstn]; reflexivity
                | vm_compute; reflexivity ] ];
        eapply (L_be0 fraq _ _ _ _ _ _ obq _ 6 [cp_b fr 35; cp_b fr 34]
                      ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3))
    end;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | kfact
          | bfact ].
  Qed.


  (* 0x836c0 .. 0x8370c: the two header bytes (12 = 0x88, 13 = 0x19), each behind its shadow check; a byte that
     differs leaves with the kind 0 and the zeroed box. *)
  Lemma body_tail : 50 <= n -> forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG Qp
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836c0) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL HMSET MI0 RFSS RFW1 RTLS. pf_hide.
    intros Hn50 fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof DFf as DFf'. unfold Wall, Wf in DFf'. cbn [disjoint_from app fst snd] in DFf'.
    destruct DFf' as (Dwin & Dhint & Dflag & Dfr & Dsh & Dbox & _).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    (* 0x836c0: byte 12 of the frame, checked *)
    rdb 12%nat 1%nat ltac:(intros jx Hjx; replace (12 + jx)%nat with 12%nat by lia;
                                     apply cp_rd_12; lia).
    step.
    assert (RX12 : 0 <= f + 12 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 12 1 (f + 12) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH12.
    chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 12) 136) by (clear; lia).
    change (bv_unsigned (cp_b fr 12)) with (cp_v fr 12).
    destruct (Z.eqb_spec (cp_v fr 12) 136) as [E12|E12]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E12), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    (* 0x836e0: byte 13 of the frame, checked *)
    rdb 13%nat 1%nat ltac:(intros jx Hjx; replace (13 + jx)%nat with 13%nat by lia;
                                     apply cp_rd_13; lia).
    step.
    assert (RX13 : 0 <= f + 13 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 13 1 (f + 13) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH13.
    chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 13) 25) by (clear; lia).
    change (bv_unsigned (cp_b fr 13)) with (cp_v fr 13).
    destruct (Z.eqb_spec (cp_v fr 13) 25) as [E13|E13]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E13), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    assert (HE : cp_hdr n fr = true) by (apply cp_hdr_spec; repeat split; lia).
    (* 0x83700 .. 0x8370c: s6 = the box pointer, on both paths of `beqz s4` *)
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w : word, w = Z_to_bv 64 ob ->
                      evtF segs rgq Q (MS (bvmap_set (Z_to_bv 5 22) w R) Fm (Z_to_bv 64 0x8370c) fcc rv mm ro));
        [ step; step; rewrite (rc_eqb_lit o 0) by (clear -Ro; lia);
          destruct HO as [(Eo & Eob) | (Eo & Eob)];
          [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
            apply (G (Z_to_bv 64 (fra + 32)) ltac:(rewrite Eob; reflexivity))
          | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
            apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
        | intros w Hw; subst w; simp_regs ]
    end.
    eapply (body_copy Hn50 HE fra fv spc j nn w120 mc ob mx);
      [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc | exact HBJ | exact RWx ].
  Qed.


  (* 0x836a8 .. : __asan_memset(ob, 0, 36) zeroes the output box, then the header test n < 50. ob is the box the
     run chose at 0x8369c/0x836a0 (the frame's redzone when o = 0, else o). *)
  Lemma body_main : forall fra fv spc j nn w120 mc ob jb
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    rw_cells rsegs mc ob [CB 36 jb] -> addressable mc ob 36 -> stk rsegs mc (S - 8800) S ->
    asan_cells mc -> shadow_rw mc ->
    evtF rsegs RNG Qp
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836a8) fc None mc (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL MI0 RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob jb rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO HOrw Aob STw ACc SRc.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (U36 : bv_unsigned (Z_to_bv 64 36) = 36) by reflexivity.
    assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (STsp : stk rsegs mc (S - 8800) spc)
      by (apply (stk_sub mc (S - 8800) S (S - 8800) spc STw); clear -Hspcr RS; lia).
    pose proof HMSET as HM. unfold asan_memset_contract_F, ASAN_MEMSET_K in HM. cbv zeta in HM.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HM.
    (* 0x836a8 li a2,36; 0x836ac mv a0,s3; 0x836b0 li a1,0; 0x836b4 jal -> 0x524c4 *)
    do 4 step.
    eapply evtF_cut.
    { eapply HM with (junk := jb) (lo := S - 8800);
        rewrite ?(unsigned_lit _ Rob), ?(unsigned_lit spc Rspc), ?U36, ?U0.
      - change (Z.to_nat 36) with 36%nat. exact HOrw.
      - clear; lia.
      - exact Aob.
      - right; exact Obapp.
      - right; apply (acl_app_in mc _ 36 7 Aob); clear; lia.
      - exact Obrt.
      - clear -Obsp; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACc.
      - exact SRc.
      - exact MI.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memset's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 36 bytes of the box *) exact RGOB.
      - (* their aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the shadow of __asan_memset's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1m & a2m & a3m & a4m & a5m & a6m & a7m & t3' & t4' & t5' & t6' & m' &
                       Hms & MUm & WMm & MIm & STm & RWm & ACm & SRm).
    subst ms'.
    rewrite (ret_pc_even 538296 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob), U36, (unsigned_lit spc Rspc) in MUm. unfold ASAN_MEMSET_K in MUm.
    rewrite (unsigned_lit _ Rob), U36 in RWm. change (Z.to_nat 36) with 36%nat in RWm.
    rewrite (unsigned_lit spc Rspc) in STm.
    (* the body's running footprint: the box and the callee windows *)
    pose proof RWm as RWbk. destruct RWbk as [[_ Hbox] _]. cbn [cells_bytes cbytes] in Hbox.
    rewrite app_nil_r in Hbox.
    assert (RMc : rd_mono mc m').
    { apply (rd_mono_list _ mc m' MUm). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbox). rewrite repeat_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STm). clear -Hy Hspcr; lia. }
    assert (MUx : munch [(ob, ob + 36); (S - 8800, spc)] mc m').
    { eapply munch_weaken; [| exact MUm].
      intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _).
      split; [exact H1|]. split; [clear -H2 Hspcr; lia | exact I]. }
    assert (STx : stk rsegs m' (S - 8800) S) by (exact (stk_mono mc m' (S - 8800) S STw WMm RMc)).
    (* 0x836b8: li a0,50; 0x836bc: bltu s6,a0 -> n < 50 exits at 0x8391c *)
    step. step. rewrite (rc_ltu_lit n 50) by lia.
    destruct (Z.ltb_spec n 50) as [Hlt|Hge]; cbv iota.
    - (* n < 50: no header, the box stays zero, a0 = 0 *)
      step.
      assert (Hcphdr : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.leb_gt 50 n) Hlt); reflexivity).
      assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
      eapply (L_join fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact MUx | exact WMm | exact MIm | exact STx | ].
      rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWm.
    - (* 50 <= n: the header checks, the copies, the comparison and the kind *)
      eapply (body_tail Hge fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc
        | refine (conj MUx (conj WMm (conj MIm STx))) | ].
      replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with cp_z in RWm
        by (vm_compute; reflexivity).
      exact RWm.
  Qed.

  (* 0x8369c .. 0x836a8: the box pointer s3 = o (or the frame's redzone when o = 0). *)
  Lemma body_holds : KB Qp.
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL MI0 RFSS RFW1 RTLS. pf_hide.
    unfold KB. intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      HK HB HFL HBaddr.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (EMt : fs_M 1 = 8192) by reflexivity.
    assert (Hjb0 : 0 <= j < 8192)
      by (destruct HK as [(_ & _ & _ & Ej & _) | (Hjb & _ & _ & _ & _ & _)];
          [lia | rewrite EMt in Hjb; lia]).
    assert (Hnn1 : nn <= 1)
      by (destruct HK as [(_ & _ & _ & _ & Enn) | (_ & _ & _ & _ & _ & Enn & _)]; lia).
    pose proof (stk_mono m mc (S - 8800) S ST0 WM RM) as STw.
    assert (STfr : stk rsegs mc fra (fra + 128)).
    { destruct HK as [(Efv & Efra & _) | (Hj & Efra & _)].
      - apply (stk_sub mc (S - 8800) S fra (fra + 128) STw);
          [ clear -Efra HAlo HAhi RS; rewrite Efra; lia | clear -Efra HAlo HAhi RS; rewrite Efra; lia | lia ].
      - pose proof (stk_mono m mc FS (FS + FS_SIZE) Pfsstk WM RM) as STfs.
        assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
        rewrite EMt in Hj.
        apply (stk_sub mc FS (FS + FS_SIZE) fra (fra + 128) STfs);
          [ rewrite Efra, EFRj; clear -Pfs0 Hj; lia
          | rewrite Efra, EFRj; unfold FS_SIZE; clear -Pfs0 HFSb Hj; lia | lia ]. }
    assert (ACc : asan_cells mc).
    { apply (asan_cells_kept (Wf fra j nn) m mc AC0 MU).
      unfold Wf, RT_LO, RT_HI, fs_hint, fs_flag, shadow_addr;
        cbn [disjoint_from fst snd Z.of_nat Pos.of_succ_nat].
      try (change (2 ^ 15) with 32768); try (change (2 ^ (15 - 1)) with 16384).
      repeat split; try exact I; left;
        unfold HIGHMEM_BEG, APPMEM_END in *;
        clear -HHM HAE Pfs2 Hjb0 FRlo SH1; lia. }
    pose proof (shadow_rw_mono m mc SR0 WM RM) as SRc.
    (* 0x8369c: mv s3,s10; 0x836a0: beqz s4 -> the box pointer *)
    step.
    step. rewrite (rc_eqb_lit o 0) by lia.
    destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbv iota.
    - (* o = 0: the box is the frame's redzone fra + 32, carved from the frame's stack bytes *)
      assert (STbox : stk rsegs mc (fra + 32) (fra + 68))
        by (apply (stk_sub mc fra (fra + 128) (fra + 32) (fra + 68) STfr); lia).
      destruct (stk_carve rsegs mc (fra + 32) (fra + 68) 36%nat STbox ltac:(lia)) as [_ [jb Hrw]].
      replace (fra + 68 - Z.of_nat 36) with (fra + 32) in Hrw by lia.
      eapply (body_main fra fv spc j nn w120 mc (fra + 32) jb);
        [ exact HK | exact HB | exact HFL | left; split; [exact Eo | reflexivity]
        | exact Hrw | exact HBaddr | exact STw | exact ACc | exact SRc ].
    - (* o <> 0: the box is o, transported from the caller's rw_cells *)
      step.
      destruct (HOK Eo) as (Ho4 & Ho36 & HOrw & HoS & Hof).
      assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
        by (unfold reac_ctrl_parse_D; apply in_or_app; right;
            rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity).
      assert (Hdjo : forall x, o <= x < o + 36 -> outside (Wf fra j nn) x).
      { intros x Hx.
        destruct (AO0 Eo) as (AOa & _ & _).
        assert (Hxapp : app_mem x)
          by (pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as Ha;
              replace (o + (x - o)) with x in Ha by lia; exact Ha).
        pose proof (dj_pair o (o + 36) _ _ HinO (proj1 (fp_wx_hint_flag_in FS X))) as Hoh.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        unfold Wf. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        - clear -Hx HoS; destruct HoS; lia.
        - intros [HL HR]. clear -Hx HL HR Hoh; lia.
        - intros [HL HR]. destruct HK as [(_ & _ & _ & _ & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)].
          + rewrite Enn in HR. clear -HL HR; lia.
          + rewrite Enn in HR.
            assert (EFL : fs_flag FS 1 j = fs_flag FS 1 0 + j) by (rewrite !fs_flag1; lia).
            rewrite EFL in HL, HR. rewrite EMt in Hjb, Hofl. clear -Hx HL HR Hofl Hjb; lia.
        - intros [HL HR]. destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          + rewrite Efr in HL, HR. clear -Hx HoS HL HR HAlo HAhi; destruct HoS; lia.
          + destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hx HL HR Hc; lia.
        - intros [HL HR]. apply (acl_app_not_shadow x Hxapp). unfold shadow_addr in HL, HR.
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
      assert (Hbox : rw_cells rsegs mc o [CB 36 junk])
        by (eapply acl_rw; [exact HOrw | exact MU | exact WM |
              intros x Hx; apply Hdjo; cbn [cells_size csize] in Hx; lia]).
      assert (Aob : addressable mc o 36).
      { destruct (AO0 Eo) as (AOa & _ & _).
        apply (acl_addr_munch (Wf fra j nn) m mc o 36 AOa MU).
        intros i Hi.
        pose proof (acl_app_in m o 36 i AOa Hi) as Hoi.
        pose proof (rt_app_shadow (o + i) Hoi) as Hsh.
        unfold Wf. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *; clear -HL HR HHM HAE; right; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_hint in HL, HR; cbn [Z.of_nat] in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_flag in HL, HR; cbn [Z.of_nat Pos.of_succ_nat] in HL, HR;
            change (2 ^ 15) with 32768 in HL, HR; change (2 ^ (15 - 1)) with 16384 in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0 Hjb0 Hnn1; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          replace (shadow_addr (o + i)) with (fra + (shadow_addr (o + i) - fra)) by lia.
          apply FAP; clear -HL HR; lia.
        + intros HC.
          assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
            by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
          rewrite E16 in HC.
          apply (acl_win_sh (o + i) fra (fra + 128) FR8); [| exact HC].
          intros [HL HR].
          destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          * destruct HoS as [Hc|Hc]; rewrite Efr in HL, HR; clear -Hi Hc HL HR HAlo HAhi; lia.
          * destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hi HL HR Hc; lia. }
      eapply (body_main fra fv spc j nn w120 mc o junk);
        [ exact HK | exact HB | exact HFL | right; split; [exact Eo | reflexivity]
        | exact Hbox | exact Aob | exact STw | exact ACc | exact SRc ].
  Qed.

  (* The whole run: the entry (0x83578 .. 0x8369c), the body, the exit. *)
  Lemma parse_run : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evtF rsegs RNG Qp (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    exact (entry t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Qp m eq_refl body_holds).
  Qed.

End SetupF.

(* The free-frame contract in footprint form (the exact metadata of the window): the Section's run at the
   statement's state. The Section's X premises are the statement's leading Forall split into the flag bytes (XF0)
   and the frame indices (XB0); its shadow premises are the statement's covers, turned here into the quantified
   covers the run uses (the window's from its exact metadata, rcpF_win_cov / rcpF_win_kov). *)
Theorem reac_ctrl_parse_x_F_holds :
  asan_stack_malloc_1_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F -> bcmp_wrap_contract_F ->
  reac_ctrl_parse_contract_x_F.
Proof.
  intros SMAL MSET MCPY BWRP. unfold reac_ctrl_parse_contract_x_F.
  intros RNG X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk HXF Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae
    Haddr Hfa Hoa Hbc Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls
    RBY RIMG0 RWIN RWSHA RINF RFSHA ROUT ROSHA RBC RBCSHA RFSS RW1 RTLS.
  subst a0 a1 a2 sp. unfold REAC_CTRL_PARSE_K in *.
  assert (RS : 8800 <= S < 2^64) by lia.
  assert (XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X)
    by (eapply Forall_impl; [|exact HXF]; intros ci (H1 & _ & H3); exact (conj H1 H3)).
  assert (XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X)
    by (eapply Forall_impl; [|exact HXF]; intros ci (_ & H2 & _); exact H2).
  pose proof kind_of_link1_F_holds as KOL.
  (* the image, as the literal range the step tactics match *)
  assert (RIMG : rng RNG 0x10000 0x5ee000) by (unfold IMG_LO, IMG_HI in RIMG0; exact RIMG0).
  (* the quantified shadow covers of the window (from its exact metadata), of f, of o and of the compare bytes *)
  assert (SCW : shcov RNG (S - 8800) 8800) by exact (rcpF_win_cov RNG S HS16 RWSHA).
  assert (SKW : shkov RNG (S - 288) 160) by exact (rcpF_win_kov RNG S HS16 RWSHA).
  assert (SCF : 50 <= n -> shcov RNG f 50) by (intros H50; apply rcpF_cov; exact (RFSHA H50)).
  assert (SKF : 50 <= n -> shkov RNG f 50) by (intros H50; apply rcpF_kov; exact (RFSHA H50)).
  assert (SCO : o <> 0 -> shcov RNG o 36) by (intros H0; apply rcpF_cov; exact (ROSHA H0)).
  assert (SKO : o <> 0 -> shkov RNG o 36) by (intros H0; apply rcpF_kov; exact (ROSHA H0)).
  assert (SKBC : shkov RNG REAC_CTRL_PARSE_BC 6) by (apply rcpF_kov; exact RBCSHA).
  (* the class-1 side-stack bytes of fp_w, one rng fact per range *)
  pose proof RW1 as RWc. unfold fp_w, fp_w1 in RWc. cbn [flat_map app] in RWc.
  apply Forall_cons_iff in RWc as [_ RWc].
  apply Forall_cons_iff in RWc as [RFLG RWc].
  apply Forall_cons_iff in RWc as [RFRM RWc].
  apply Forall_cons_iff in RWc as [RFRS _].
  cbn [fst snd] in RFLG, RFRM, RFRS.
  replace (fs_flag FS 1 0 + fs_M 1 - fs_flag FS 1 0) with (fs_M 1) in RFLG by lia.
  (* the frames' shadow comes byte-exact; both of its ends are the shadow byte of a 64-aligned address *)
  pose proof Hfp as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSp & HFS4 & _) & _).
  assert (EQ : FS = 4096 * (FS / 4096)) by (pose proof (Z.div_mod FS 4096 ltac:(lia)); lia).
  set (q := FS / 4096) in EQ. clearbody q.
  assert (EF0 : fs_frame FS 1 0 = 64 * (64 * q + 16960)) by (rewrite fs_frame1; lia).
  assert (EF1 : fs_frame FS 1 (fs_M 1) = 64 * (64 * q + 33344))
    by (rewrite fs_frame1; change (fs_M 1) with 8192; lia).
  assert (ES0 : shadow_addr (fs_frame FS 1 0) = 8 * (64 * q + 16960) + ASAN_K).
  { unfold shadow_addr. rewrite EF0.
    replace (64 * (64 * q + 16960)) with (8 * (8 * (64 * q + 16960))) by lia. rewrite rcpF_div8. lia. }
  assert (ES1 : shadow_addr (fs_frame FS 1 (fs_M 1)) = 8 * (64 * q + 33344) + ASAN_K).
  { unfold shadow_addr. rewrite EF1.
    replace (64 * (64 * q + 33344)) with (8 * (8 * (64 * q + 33344))) by lia. rewrite rcpF_div8. lia. }
  rewrite ES0, ES1 in RFRS.
  assert (SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0))
    by (rewrite EF0, EF1; exact (rcpF_span_cov RNG (64 * q + 16960) (64 * q + 33344) RFRS)).
  assert (SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0))
    by (rewrite EF0, EF1; exact (rcpF_span_kov RNG (64 * q + 16960) (64 * q + 33344) RFRS)).
  eapply parse_run; eassumption.
Qed.

(* RECIPE step 1: the old statement, back from the footprint form at ExecF.RNG_all, from the same callee contracts
   (in footprint form) as reac_ctrl_parse_x_holds (reac_ctrl_parse.v, not in this delivery) takes in the same places. *)
Theorem reac_ctrl_parse_x_holds_of_F :
  asan_stack_malloc_1_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F -> bcmp_wrap_contract_F ->
  reac_ctrl_parse_contract_x.
Proof.
  intros SMAL MSET MCPY BWRP.
  exact (reac_ctrl_parse_contract_x_of_F (reac_ctrl_parse_x_F_holds SMAL MSET MCPY BWRP)).
Qed.

(* ==== Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 09:58Z ruling): the footprint
   run of the `_on` contracts. Section SetupF above and the theorems after it stay as they were: they take the callees'
   old footprint contracts, which do not give the `_F_on` ones. Module ParseFOn re-derives Section SetupF, lemma by
   lemma and with the same names, from the callees' `_F_on` contracts (asan_stack_malloc_1_contract_F_on of r2's
   asan_stack_malloc_cF_on.v,
   asan_memset_contract_F_on, asan_memcpy_contract_F_on, bcmp_wrap_contract_F_on; kind_of_link1 has no shadow premise)
   and the narrowed premise SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m (lib/A/Prog/reac_ctrl_parse_c.v),
   with the same changes as Module ParseOn (reac_ctrl_parse.v, not in this delivery): the region lemmas frame_in_R .. srw_bcmp (before
   fk_facts); the frame's shadow bytes from SR0 at a byte of R (fk_facts, fwords, L_exit by srw_frame /
   shadow16_stk_on); each callee's `_on` premise from R (srw_smal, srw_memset, srw_memcpy, srw_bcmp); the shadow facts
   carried between the calls are `shadow_rw_on R` (body_rt by ShadowRwOnK.fl_shadow_rw_on, the callees' posts at
   P := R); the post's `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (Qp, aJ, aJ_free, Wex_free) by
   shadow_rw_mono_on from m. rule 24: proof-index reac_ctrl_parse (2026-10-29 00:3xZ, exit 0): 12 named files +
   8 lemma rows, plain / ubsan builds of fuzz_disco / fuzz_grant / fuzz_scene; checker a Theorem Labs lane: CONFIRM. At ossv/recipes c5e779efe8c (2026-10-31),
   released ASan proofs of reac_ctrl_parse exist in fuzz_grant, fuzz_disco and fuzz_scene. ==== *)
Module ParseFOn.

Section SetupF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte) (RNG : ExecF.footprint).
  (* the callees, in their image-A footprint forms (above: __asan_memset / __asan_memcpy a Theorem Labs lane's shared texts;
     kind_of_link1's from kind_of_link1_c.v) *)
  Hypothesis SMAL : asan_stack_malloc_1_contract_F_on.
  Hypothesis HMSET : asan_memset_contract_F_on.
  Hypothesis HMCPY : asan_memcpy_contract_F_on.
  Hypothesis HBCMPW : bcmp_wrap_contract_F_on.
  Hypothesis HKOL : kind_of_link1_contract_F.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rn : 0 <= n < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis RS : 8800 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - 8800) S.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f).
  Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i.
  Hypothesis HOK : o <> 0 ->
    o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
    (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o).
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8800.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - 8800) 8800.
  Hypothesis AF0 : 50 <= n -> addressable m f 50.
  Hypothesis AO0 : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
  (* The free frames X (class-1 frames in use by the caller, flag 1 at m, index below fs_M 1) and the side-stack
     premise in the free-frame form (fpx: the data ranges are apart from fp_wx [1] FS X, which leaves out X's frames
     and their shadow). *)
  Variable X : list (nat * Z).
  Hypothesis XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X.
  Hypothesis XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X.
  Hypothesis FP0 : fpx [1%nat] m (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X.
  Hypothesis TLS0 : reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - 8800) S.

  (* ---- The footprint premises of the run.  The shadow covers are QUANTIFIED (shcov / shblk / shkov): a ground
     rng premise whose bounds hold a division would make every later lia pay for that division's Euclidean
     equations.  The ranges without a division stay ground, since StepF's solve_acc1 matches them in the
     context. SKW covers [S - 288, S - 128) only: the span of the real-stack frame [A - 128, A), its one use. ---- *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8800) 8800.
  Hypothesis SCW : shcov RNG (S - 8800) 8800.
  Hypothesis SKW : shkov RNG (S - 288) 160.
  Hypothesis RINF : 50 <= n -> rng RNG f 50.
  Hypothesis SCF : 50 <= n -> shcov RNG f 50.
  Hypothesis SKF : 50 <= n -> shkov RNG f 50.
  Hypothesis ROUT : o <> 0 -> rng RNG o 36.
  Hypothesis SCO : o <> 0 -> shcov RNG o 36.
  Hypothesis SKO : o <> 0 -> shkov RNG o 36.
  Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFSS : rng RNG FS (fs_frame FS 0 0 - FS).
  Hypothesis RFLG : rng RNG (fs_flag FS 1 0) (fs_M 1).
  Hypothesis RFRM : rng RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis RFW1 : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS).
  Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).
  Local Ltac pf_h H := let T := type of H in change (id T) in H. Local Ltac pf_uh H := lazymatch type of H with id ?T => change T in H end. Local Ltac pf_hide := try pf_h HF; try pf_h HOK; try pf_h AO0; try pf_h AF0; try pf_h RINF; try pf_h SCF; try pf_h SKF; try pf_h ROUT; try pf_h SCO; try pf_h SKO.
  (* the aligned sp (s1 after andi) *)
  Definition A : Z := (S - 128) / 32 * 32.

  Lemma HA1 : A mod 32 = 0 /\ S - 160 < A <= S - 128.
  Proof. unfold A. Z.div_mod_to_equations. lia. Qed.

  Lemma STW0 : forall a, S - 8800 <= a < S -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (stk_wv m _ _ _ ST0 Ha). Qed.

  (* The 12 saved registers, lowest address (S-96, s10) first. *)
  Definition SAVES : list cell :=
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* the writes of the run outside o: the window, the class-1 hint word, flag j, the frame and its shadow *)
  Definition Wf (fr j nn : Z) : list ivl :=
    [(S - 8800, S); (fs_hint FS 1, fs_hint FS 1 + 8); (fs_flag FS 1 j, fs_flag FS 1 j + nn);
     (fr, fr + 128); (shadow_addr fr, shadow_addr fr + 16)].

  (* The frame: real (fv = 0, fr = A - 128, sp = A - 128) or fake (fv = fr the side frame j, sp = A, the flag-byte
     address w120 at fr + 120, and frame j's flag byte 0 at m: __asan_stack_malloc_1 took a free frame, so the
     exit's clear of that flag gives back m's flag array). *)
  Definition FK (fr fv spc j nn : Z) (w120 : word) : Prop :=
    (fv = 0 /\ fr = A - 128 /\ spc = A - 128 /\ j = 0 /\ nn = 0) \/
    (0 <= j < fs_M 1 /\ fr = fs_frame FS 1 j /\ fv = fr /\ spc = A /\ w120 = Z_to_bv 64 (fs_flag FS 1 j) /\ nn = 1 /\
     bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0]).

  (* The class-1 flag bytes (each 0 or 1) and, for a side-stack frame (nn = 1), its flag-address word at fr + 120:
     what __asan_stack_malloc_1 left, and what the release at 0x83920 reads. *)
  Definition FLG (fr nn : Z) (w120 : word) (mc : word -> option byte) : Prop :=
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') /\
    (nn = 1 -> bytes_at rsegs mc (fr + 120) (le8 w120)).

  (* The output box: the frame's redzone fr + 32 when o = 0, else o. *)
  Definition OB (fr ob : Z) : Prop := (o = 0 /\ ob = fr + 32) \/ (o <> 0 /\ ob = o).

  Lemma app_range : forall Y nn, 0 < nn -> (forall i, 0 <= i < nn -> app_mem (Y + i)) ->
    Y + nn <= 2147450880 \/ 17594333495296 <= Y.
  Proof.
    intros Y nn Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (nn - 1) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
    destruct (Z.le_gt_cases (Y + nn) 2147450880) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases 17594333495296 Y) as [G|G]; [right; exact G|].
    exfalso. pose proof (H (2147450880 - Y) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. lia.
  Qed.

  (* ---- Route (C): the run's region reac_ctrl_parse_shadow_R f n o S FS holds every shadow byte the run stores into
     (the frame's 16 shadow bytes) and every callee's `_on` region at its call. ---- *)

  (* The frame's 16 shadow bytes: the real frame [A - 128, A) is R's first disjunct; a side-stack frame fs_frame FS 1 j
     lies in the class-1 block shadow (asan_stack_malloc_shadow_R FS 1). *)
  Lemma frame_in_R : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    fra / 8 + ASAN_K <= x < fra / 8 + ASAN_K + 16 -> reac_ctrl_parse_shadow_R f n o S FS x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx. unfold reac_ctrl_parse_shadow_R.
    destruct HK as [(_ & Efr & _) | (Hj & Efr & _)]; subst fra.
    - left. unfold A in Hx. unfold shadow_addr. lia.
    - right; left. unfold asan_stack_malloc_shadow_R; cbv beta. unfold shadow_addr.
      assert (EF : forall jj, fs_frame FS 1 jj = FS + 1085440 + jj * 128)
        by (intros jj; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
      assert (EM : fs_M 1 = 8192) by reflexivity.
      rewrite (EF j) in Hx. rewrite (EF 0). rewrite EM in Hj. clear -Hx Hj. unfold ASAN_K in *.
      Z.div_mod_to_equations. lia.
  Qed.

  Lemma srw_frame : forall fra fv spc j nn w120 mc, FK fra fv spc j nn w120 ->
    shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc -> shadow_rw_on (shadow16_stk_shadow_R fra) mc.
  Proof.
    intros fra fv spc j nn w120 mc HK H.
    exact (shadow_rw_on_mono _ _ mc (fun x Hx => frame_in_R fra fv spc j nn w120 x HK Hx) H).
  Qed.

  (* The aligned shadow words of a sub-range are words of the range. *)
  Lemma sh_word_sub : forall p lp q lq x, p <= q -> q + lq <= p + lp -> 0 < lq ->
    sh_word_on q lq x -> sh_word_on p lp x.
  Proof.
    intros p lp q lq x H1 H2 H3 (Hn & Hlo & Hhi).
    unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *.
    split; [lia|]. clear Hn. unfold ASAN_K in *. Z.div_mod_to_equations. lia.
  Qed.

  (* The box's aligned shadow words: o's (R's third disjunct) or, for o = 0, the frame's redzone fra + 32, whose
     words lie in the frame's 16 shadow bytes (fra mod 32 = 0). *)
  Lemma box_in_R : forall fra fv spc j nn w120 ob x, FK fra fv spc j nn w120 -> OB fra ob ->
    sh_word_on ob 36 x -> reac_ctrl_parse_shadow_R f n o S FS x.
  Proof.
    intros fra fv spc j nn w120 ob x HK HO Hx.
    destruct HO as [(Eo & Eob) | (Eo & Eob)]; subst ob.
    - apply (frame_in_R fra fv spc j nn w120 x HK).
      assert (H32 : fra mod 32 = 0).
      { pose proof HA1 as (HA32 & _ & _).
        pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & _) & _).
        destruct HK as [(_ & Efr & _) | (_ & Efr & _)]; rewrite Efr.
        - clear -HA32. Z.div_mod_to_equations. lia.
        - assert (EF : fs_frame FS 1 j = FS + 1085440 + j * 128)
            by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
                change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
          rewrite EF. clear -P2. Z.div_mod_to_equations. lia. }
      destruct Hx as (_ & Hlo & Hhi). unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *.
      clear -H32 Hlo Hhi. unfold ASAN_K in *. Z.div_mod_to_equations. lia.
    - unfold reac_ctrl_parse_shadow_R. right; right; left. split; [exact Eo | exact Hx].
  Qed.

  (* __asan_stack_malloc_1's region (0x835e8): the class-1 block shadow. *)
  Lemma srw_smal : forall mc, shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    shadow_rw_on (asan_stack_malloc_shadow_R FS 1%nat) mc.
  Proof.
    intros mc H. apply (shadow_rw_on_mono (reac_ctrl_parse_shadow_R f n o S FS) _ mc); [|exact H].
    intros x Hx. unfold reac_ctrl_parse_shadow_R. right; left. exact Hx.
  Qed.

  (* __asan_memset(ob, 0, 36)'s region (0x836b4). *)
  Lemma srw_memset : forall fra fv spc j nn w120 ob mc (a0 a2 : word),
    FK fra fv spc j nn w120 -> OB fra ob -> bv_unsigned a0 = ob -> bv_unsigned a2 = 36 ->
    shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc -> shadow_rw_on (asan_memset_shadow_R a0 a2) mc.
  Proof.
    intros fra fv spc j nn w120 ob mc a0 a2 HK HO E0 E2 H.
    apply (shadow_rw_on_mono (reac_ctrl_parse_shadow_R f n o S FS) _ mc); [|exact H].
    intros x Hx. unfold asan_memset_shadow_R in Hx. rewrite E0, E2 in Hx.
    exact (box_in_R fra fv spc j nn w120 ob x HK HO Hx).
  Qed.

  (* __asan_memcpy(ob + d, f + k, 6)'s region (0x83718: d = 10, k = 0; 0x83728: d = 4, k = 6). *)
  Lemma srw_memcpy : forall fra fv spc j nn w120 ob mc (a0 a1 a2 : word) d k,
    FK fra fv spc j nn w120 -> OB fra ob -> 50 <= n ->
    bv_unsigned a0 = ob + d -> bv_unsigned a1 = f + k -> bv_unsigned a2 = 6 ->
    0 <= d -> d + 6 <= 36 -> 0 <= k -> k + 6 <= 50 ->
    shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc -> shadow_rw_on (asan_memcpy_shadow_R a0 a1 a2) mc.
  Proof.
    intros fra fv spc j nn w120 ob mc a0 a1 a2 d k HK HO Hn50 E0 E1 E2 Hd0 Hd1 Hk0 Hk1 H.
    apply (shadow_rw_on_mono (reac_ctrl_parse_shadow_R f n o S FS) _ mc); [|exact H].
    intros x Hx. unfold asan_memcpy_shadow_R in Hx. rewrite E0, E1, E2 in Hx.
    destruct Hx as [Hx|Hx].
    - unfold reac_ctrl_parse_shadow_R. right; right; right; left. split; [exact Hn50|].
      exact (sh_word_sub f 50 (f + k) 6 x ltac:(lia) ltac:(lia) ltac:(lia) Hx).
    - exact (box_in_R fra fv spc j nn w120 ob x HK HO
               (sh_word_sub ob 36 (ob + d) 6 x ltac:(lia) ltac:(lia) ltac:(lia) Hx)).
  Qed.

  (* The bcmp wrapper's region on (f, BC, 6) (0x8373c). *)
  Lemma srw_bcmp : forall mc, 50 <= n -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    shadow_rw_on (bcmp_wrap_shadow_R f REAC_CTRL_PARSE_BC 6) mc.
  Proof.
    intros mc Hn50 H. apply (shadow_rw_on_mono (reac_ctrl_parse_shadow_R f n o S FS) _ mc); [|exact H].
    intros x Hx. unfold bcmp_wrap_shadow_R in Hx. unfold reac_ctrl_parse_shadow_R.
    destruct Hx as [Hx|Hx].
    - right; right; right; left. split; [exact Hn50|].
      exact (sh_word_sub f 50 f 6 x ltac:(lia) ltac:(lia) ltac:(lia) Hx).
    - right; right; right; right. split; [exact Hn50 | exact Hx].
  Qed.

  (* What every frame gives: alignment, place, writable and AppMem bytes, writable shadow bytes. *)
  Lemma fk_facts : forall fr fv spc j nn w120, FK fr fv spc j nn w120 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 128 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 128 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 128 -> app_mem (fr + i)) /\
    (fr + 128 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 16 -> wview rsegs m (wa (fr / 8 + ASAN_K + i)) <> None) /\
    2147450880 <= fr / 8 + ASAN_K /\ fr / 8 + ASAN_K + 16 <= 17594333495296.
  Proof using tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd HOK AC0 AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros fr0 fv spc j nn w120 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & HAPP & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : fr0 mod 8 = 0 /\ FS + 36864 <= fr0 /\ fr0 + 128 <= A /\ (spc = A \/ spc = fr0) /\
                (forall i, 0 <= i < 128 -> wview rsegs m (wa (fr0 + i)) <> None) /\
                (forall i, 0 <= i < 128 -> app_mem (fr0 + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En & _)]; subst fr0.
      - split; [unfold A; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. unfold app_mem. right. lia.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ (14 - 1)) with 8192 in Hj. change (2 ^ 1) with 2 in *. change (2 ^ 20) with 1048576 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range fr0 128 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 16 -> fr0 / 8 + ASAN_K + i = shadow_addr (fr0 + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. pose proof (frame_in_R fr0 fv spc j nn w120 (fr0 / 8 + ASAN_K + i) HK ltac:(lia)) as HinR.
      rewrite B8 in HinR by exact Hi. rewrite B8 by exact Hi.
      apply (proj1 (SR0 _ HinR (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  (* ---- The footprint of the frame __asan_stack_malloc_1 gave: its 128 bytes and its 16 shadow bytes are in RNG
     whether it is the real-stack frame (inside the window) or a side frame (inside the class-1 frames). ---- *)
  Lemma rngF_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> rng RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply rng_sub; [exact RWIN | lia | lia].
    - eapply rng_sub; [exact RFRM | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  Lemma rngF_frame_cov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shcov RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply shcov_sub; [exact SCW | lia | lia].
    - eapply shcov_sub; [exact SCFR | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  Lemma rngF_frame_kov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shkov RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply shkov_sub; [exact SKW | lia | lia].
    - eapply shkov_sub; [exact SKFR | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  (* The 8-aligned shadow word span of a sub-range [a, b] of the window that keeps 64 bytes from each end of it: inside
     the window's shadow, so in RNG byte by byte (SCW) and so as one range (RBY). The shared __asan_memset /
     __asan_memcpy contracts take it for the shadow of the helper's own window [sp - K, sp). *)
  Lemma rngF_win_sh8 : forall a b, S - 8736 <= a -> a <= b -> b < S - 64 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Proof.
    intros a b Ha Hab Hb.
    assert (HH : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    split; [unfold ASAN_K; Z.div_mod_to_equations; lia|].
    split; [unfold ASAN_K; Z.div_mod_to_equations; lia|].
    intros b' jn Hb' Hj.
    apply RBY; [unfold ASAN_K in *; Z.div_mod_to_equations; lia | unfold ASAN_K in *; Z.div_mod_to_equations; lia |].
    intros k Hk.
    assert (Hx : S - 8800 <= 8 * (b' + Z.of_nat k - ASAN_K) < S - 8800 + 8800)
      by (unfold ASAN_K in *; Z.div_mod_to_equations; lia).
    pose proof (SCW _ Hx) as H1. rewrite rcpF_div8 in H1.
    replace (b' + Z.of_nat k - ASAN_K + ASAN_K) with (b' + Z.of_nat k) in H1 by lia.
    destruct H1 as (_ & _ & H1). apply H1; lia.
  Qed.

  (* The 16 shadow bytes of the frame, at the addresses the run forms: fra / 8 + ASAN_K + i. *)
  Lemma rngF_frame_blk : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shblk RNG fra 15.
  Proof.
    intros fra fv spc j nn w120 HK.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & _).
    pose proof (rngF_frame_cov fra fv spc j nn w120 HK) as HC.
    intros i Hi. pose proof (sh_add8 fra i FR8) as Hs. unfold shadow_addr in Hs.
    replace (fra / 8 + ASAN_K + i) with ((fra + 8 * i) / 8 + ASAN_K) by lia.
    apply HC. lia.
  Qed.

  (* ---- The footprint of the output box ob: the caller's buffer at o, or the frame's redzone at fra + 32. ---- *)
  Lemma rngF_ob : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob -> rng RNG ob 36.
  Proof.
    intros fra fv spc j nn w120 ob HK HO. destruct HO as [(Ho & Eob)|(Ho & Eob)]; subst ob.
    - eapply rng_sub; [exact (rngF_frame fra fv spc j nn w120 HK) | lia | lia].
    - exact (ROUT Ho).
  Qed.

  Lemma rngF_ob_cov : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob -> shcov RNG ob 36.
  Proof.
    intros fra fv spc j nn w120 ob HK HO. destruct HO as [(Ho & Eob)|(Ho & Eob)]; subst ob.
    - eapply shcov_sub; [exact (rngF_frame_cov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SCO Ho).
  Qed.

  Lemma rngF_ob_kov : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob -> shkov RNG ob 36.
  Proof.
    intros fra fv spc j nn w120 ob HK HO. destruct HO as [(Ho & Eob)|(Ho & Eob)]; subst ob.
    - eapply shkov_sub; [exact (rngF_frame_kov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SKO Ho).
  Qed.

  (* Every flag byte X names is a byte of the class-1 flag array. *)
  Lemma x_flag_in : forall ci, In ci X ->
    fs_flag FS (fst ci) (snd ci) = fs_flag FS 1 (snd ci) /\
    fs_flag FS 1 0 <= fs_flag FS 1 (snd ci) /\ fs_flag FS 1 (snd ci) + 1 <= fs_flag FS 1 0 + fs_M 1.
  Proof.
    intros ci Hin.
    destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (Hc & _).
    pose proof (proj1 (Forall_forall _ _) XB0 ci Hin) as Hb.
    rewrite Hc. split; [reflexivity|].
    assert (EM : fs_M 1 = 8192) by reflexivity.
    rewrite !fs_flag1, EM. rewrite EM in Hb. clear -Hb. lia.
  Qed.

  (* A frame index whose flag byte is 0 at m is not an index of X: X's flags are 1 at m. *)
  Lemma x_ne_j : forall j, bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0] -> Forall (fun ci => snd ci <> j) X.
  Proof.
    intros j (_ & _ & H0). eapply Forall_impl; [|exact XF0].
    intros [c i] (Hc & (_ & _ & H1)) E. cbn [fst snd] in Hc, E, H1. subst c i.
    pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0. pose proof (H1 0%nat ltac:(cbn [length]; lia)) as A1.
    cbn [nth_error] in A0, A1. rewrite A0 in A1. injection A1 as A1.
    vm_compute in A1. discriminate.
  Qed.

  (* A data range of the caller (D: f's 50 bytes, o's record) is apart from a class-1 frame j whose flag is 0 at m:
     j is not in X, so the frame is inside fpx's footprint fp_wx [1] FS X, which D is apart from. *)
  Lemma D_apart_frame : forall a b j, In (a, b) (reac_ctrl_parse_D f n o) -> a < b ->
    0 <= j < fs_M 1 -> bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0] ->
    b <= fs_frame FS 1 j \/ fs_frame FS 1 j + 128 <= a.
  Proof.
    intros a b j Hin Hab Hj Hfl0.
    pose proof (fpx_dj _ _ _ _ _ _ _ _ _ FP0) as HDd.
    assert (E1 : fs_frame FS 1 (j + 1) = fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
    destruct (Z_le_gt_dec b (fs_frame FS 1 j)) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (fs_frame FS 1 j + 128) a) as [R|R]; [right; exact R|].
    exfalso. apply (fp_wx_frame_in FS X j (Z.max a (fs_frame FS 1 j)) Hj (x_ne_j j Hfl0)); [lia|].
    apply (fl_dj_out_r _ _ a b (Z.max a (fs_frame FS 1 j)) HDd Hin). lia.
  Qed.

  (* fp's last premise, in the free-frame form: a data range of the contract is apart from every range of
     fp_wx [1] FS X (the hint word and the flag array are two of them, fp_wx_hint_flag_in). *)
  Lemma dj_pair : forall a b c d, In (a, b) (reac_ctrl_parse_D f n o) -> In (c, d) (fp_wx [1%nat] FS X) ->
    b <= c \/ d <= a.
  Proof.
    intros a b c d H1 H2.
    pose proof (fpx_dj _ _ _ _ _ _ _ _ _ FP0) as HDd.
    unfold fp_dj in HDd. rewrite Forall_forall in HDd.
    pose proof (HDd _ H1) as H'. cbn [fst snd] in H'. rewrite Forall_forall in H'.
    pose proof (H' _ H2) as H''. cbn [fst snd] in H''. unfold RcLay.ly_dj in H''. exact H''.
  Qed.

  Definition BI (W : list ivl) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 96) SAVES.

  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (fr fv spc j nn : Z) (w120 : word) (mc : word -> option byte)
           (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      FK fr fv spc j nn w120 -> BI (Wf fr j nn) mc -> FLG fr nn w120 mc -> addressable mc (fr + 32) 36 ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                         (Z_to_bv 64 n) (Z_to_bv 64 (fr / 8 + ASAN_K)) (Z_to_bv 64 fr) (wa ASAN_K)
                         (Z_to_bv 64 (fr + 32)) s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8369c) fc None mc (seg_rom rsegs)).

  Ltac wst a nn tac :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; tac | eassumption | lia | lia ])
    end.

  Ltac wstb a nn base fact :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                  match goal with |- wview _ _ (wa ?X) <> None => replace X with (base + (X - base)) by lia end;
                  apply fact; lia
                | eassumption | lia | lia ])
    end.

  (* A tracked poison store of one shadow byte at base + off (= base + Z.of_nat nn): the stored byte joins the
     frame-shadow cells so that the box's addressability can be read back. *)
  Ltac sstep base off nn fact :=
    wstb (base + off) 1%nat base fact; step;
    replace (base + off) with (base + Z.of_nat nn) by lia;
    rewrite rc_le1_lit; mem_after_store.

  (* 0x8361c .. 0x8369c: the stack slot, the 3 frame words and the 16 shadow bytes of the frame. *)
  Lemma fwords : forall fra fv spc j nn w120 mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 : word) Q,
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> KB Q ->
    evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                       (Z_to_bv 64 n) x23 (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8361c) fc None mc (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 RWIN SCW RFRM SCFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd HOK AC0 AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 TLS0 RBY RIMG SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 Q HK HB HFL K.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSpos & _ & _ & Pfsapp & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (HHMl : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold Wf, shadow_addr in MU.
    (* the writes of this block, for carrying FLG from mc *)
    pose proof (munch_refl [(A + 24, A + 32); (fra, fra + 24); (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16)] mc) as MUf.
    wst (A + 24) 8%nat ltac:(apply STW0; lia). step. store_done.
    steps_to 0x83644.
    wstb fra 8%nat fra FW. step. store_done.
    wstb (fra + 8) 8%nat fra FW. step. store_done.
    wstb (fra + 16) 8%nat fra FW. step. store_done.
    step. step.
    rewrite (unsigned_lit fra) by lia. rewrite rc_shr3.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
      pose proof (shadow_rw_mono_on _ m mcur SR0 WM RM) as SRmc;
      pose proof (shadow16_stk_on mcur fra (srw_frame fra fv spc j nn w120 mcur HK SRmc) ltac:(lia) FRA
                    ltac:(lia) ltac:(lia)) as STsh
    end.
    pose proof (stk_carve rsegs m1 (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(lia))
      as [STsh' [junkS SHC]].
    replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
    sstep (fra / 8 + ASAN_K) 0 0%nat SW.
    sstep (fra / 8 + ASAN_K) 1 1%nat SW.
    sstep (fra / 8 + ASAN_K) 2 2%nat SW.
    sstep (fra / 8 + ASAN_K) 3 3%nat SW.
    step.
    sstep (fra / 8 + ASAN_K) 12 12%nat SW.
    sstep (fra / 8 + ASAN_K) 13 13%nat SW.
    sstep (fra / 8 + ASAN_K) 14 14%nat SW.
    sstep (fra / 8 + ASAN_K) 15 15%nat SW.
    sstep (fra / 8 + ASAN_K) 8 8%nat SW.
    sstep (fra / 8 + ASAN_K) 9 9%nat SW.
    sstep (fra / 8 + ASAN_K) 10 10%nat SW.
    sstep (fra / 8 + ASAN_K) 11 11%nat SW.
    sstep (fra / 8 + ASAN_K) 4 4%nat SW.
    sstep (fra / 8 + ASAN_K) 5 5%nat SW.
    sstep (fra / 8 + ASAN_K) 6 6%nat SW.
    sstep (fra / 8 + ASAN_K) 7 7%nat SW.
    destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) => assert (FLf : FLG fra nn w120 mf) end.
    { destruct HFL as [(flg & Hfl & Hfln & HflF) Hw].
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      split.
      - exists flg. split; [|split; [exact Hfln | exact HflF]].
        eapply fl_bytes; [exact Hfl | exact MUf |].
        intros x Hx. rewrite Hfln, EFL0 in Hx. change (fs_M 1) with 8192 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; unfold FS_SIZE; clear -Hx HFSpos; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx HAlo HFSb RS; lia.
        + clear -Hx FRlo; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
      - intros En. eapply fl_bytes; [exact (Hw En) | exact MUf |].
        intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
        assert (Hxa : app_mem x) by (replace x with (fra + (x - fra)) by lia; apply FAP; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx FRhi; lia.
        + clear -Hx; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
    eapply K.
    - exact HK.
    - unfold BI, Wf, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI SV)))).
    - exact FLf.
    - apply frame_shadow_addr.
      + lia.
      + exact FR8.
      + unfold APPMEM_END in *; lia.
      + intros i Hi. replace (fra + 32 + i) with (fra + (32 + i)) by lia. apply FAP; lia.
      + intros g Hg. destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 0). split; [|reflexivity].
        assert (Hc : g = 4 \/ g = 5 \/ g = 6 \/ g = 7) by lia.
        destruct Hc as [H|[H|[H|H]]]; rewrite H;
          [ replace (fra / 8 + ASAN_K + 4) with (fra / 8 + ASAN_K + Z.of_nat 4) by lia;
            rewrite (Hr 4%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 5) with (fra / 8 + ASAN_K + Z.of_nat 5) by lia;
            rewrite (Hr 5%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 6) with (fra / 8 + ASAN_K + Z.of_nat 6) by lia;
            rewrite (Hr 6%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 7) with (fra / 8 + ASAN_K + Z.of_nat 7) by lia;
            rewrite (Hr 7%nat ltac:(cbn [length]; lia)) ]; reflexivity.
      + destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 4). split; [|reflexivity].
        replace (fra / 8 + ASAN_K + 8) with (fra / 8 + ASAN_K + Z.of_nat 8) by lia.
        rewrite (Hr 8%nat ltac:(cbn [length]; lia)). reflexivity.
  Qed.

  (* 0x83578 .. 0x8361c: the prologue, the class-1 frame request __asan_stack_malloc_1(128) and the choice of a
     side-stack frame or the real-stack fallback with its page probe. *)
  Lemma entry : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> KB Q ->
    evtF rsegs RNG Q (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m0 (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG SMAL Rf Rn Ro RS S16 ST0 MI0 Lfr AC0 SR0 HHM HAE X FP0 RIMG RWIN SCW RFSS RFRM SCFR RFW1 RTLS. clear HMSET HMCPY HBCMPW HKOL HF Hrd HOK AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 TLS0 RBY SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG SKFR. pf_hide.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    unfold REAC_CTRL_PARSE.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPm. unfold reac_ctrl_parse_W in FPm.
    assert (MU : munch [(S - 8800, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (S - 96) _ ST0c ltac:(lia)) as [STw STs].
    pose proof (stk_split rsegs m0 _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
    clear ST0c.
    carve_frame 96%nat STs.
    carve_frame 32%nat STz.
    step.
    steps_to 0x835b4.
    step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; unfold A; f_equal; f_equal; lia).
    rewrite EA.
    steps_to 0x835e0.
    step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (fl_fp [1%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0.
    destruct HCL0 as [(_ & h & flags & HH & HFl & HFln & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STw2 STz ltac:(lia)) as STzc.
    destruct (stk_split rsegs m1 _ A _ STzc ltac:(lia)) as [STA _].
    (* the thread cells' pointers at m1 are those at m (the prologue wrote only the window), so the statement's rng
       facts on the cells of fp_tls (RTLS, at m) name the cells the frame routine reads *)
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd0 & _).
    pose proof (fl_cols (reac_ctrl_parse_W o S) [(S - 8800, S)] _ HWd0
                  ltac:(unfold sub_fp, reac_ctrl_parse_W; intros xq Hxq; cbn [outside] in Hxq |- *;
                        split; [exact (proj1 Hxq) | exact I])) as HCOLa.
    assert (HCOL0 : Forall (fun d => forall x, fst d <= x < snd d -> outside [(S - 8800, S)] x)
                      (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0))
      by (rewrite Forall_forall in HCOLa |- *; intros dq Hdq; apply HCOLa, in_or_app; left; exact Hdq).
    destruct (fl_tls_same m m1 [(S - 8800, S)] (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k
                HT0 HT MU HCOL0) as (EDT & ETS & EC & ET & EDB & Ekq).
    subst DT0 TS0 C0 T0 DB0 k0.
    pose proof SMAL as HM.
    unfold asan_stack_malloc_1_contract_F_on, asan_stack_malloc_contract_F_on in HM. cbv zeta in HM.
    specialize (HM (proj1 (Nat.leb_le 1 10) eq_refl)).
    eapply evtF_cut.
    { destruct (rcpF_tls_rng RNG _ DT TS C T DB k (RTLS DT TS C T DB k HT0))
        as (RTdt & RTts & RTc & RTt & RTdb & RTp88 & RTp8).
      eapply HM with (lo := S - 8800) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (srw_smal m1 (shadow_rw_mono_on _ m m1 SR0 WM RM)).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HFl.
      - exact HFln.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : RcLay.ly_dj _ _ lo hi |- _ => unfold RcLay.ly_dj in Hd; lia end end.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* the callee's window [A - K, A) inside this function's window *)
        eapply rng_sub; [exact RWIN | lia | lia].
      - (* the runtime pointer cell at DT + 8 *) exact RTdt.
      - (* the runtime pointer cell at TS + 8 k *) exact RTts.
      - (* the runtime pointer cell at C + 152 *) exact RTc.
      - (* the runtime pointer cells at T + 48 *) exact RTt.
      - (* the runtime pointer cell at DB + 24 *) exact RTdb.
      - (* the side stack's header *) exact RFSS.
      - (* the class-1 frame area, from the frames' range in fp_w [1%nat] FS *) exact (rcpF_frame_area RNG FS RFW1).
      - (* the shadow of the class-1 frame area *) exact (rcpF_frame_sh RNG FS RFW1).
      - (* the thread-pointer cell at TP - 88 *) exact RTp88.
      - (* the thread-pointer cells at TP - 8 .. TP + 16 *) exact RTp8. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x835ec)) with (Z_to_bv 64 0x835ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2.
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 128, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf (A - 128) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (FL2 : FLG (A - 128) 0 (Z_to_bv 64 0) m2).
      { split; [|intros HC; discriminate HC].
        exists flags. split; [|split; [exact HFln | exact HFb]].
        eapply fl_bytes; [exact HFl | exact MU2 |].
        intros x Hx. rewrite HFln in Hx. change (fs_M 1) with 8192 in Hx. rewrite EFL0 in Hx.
        cbn [outside]. split; [|split; [|exact I]]; clear -Hx HFS' HAlo HAhi RS P1; lia. }
      pose proof (munch_refl [(A - 4096, A - 4088)] m2) as MUp.
      clear MU MU2 WM WM2 RM RM2 FR STA STw STs STz STw2 STzc MI.
      unfold Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 128)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step.
      assert (HSp : store_ok rsegs m2 (wa (A - 4096)) 8 = true)
        by (eapply wv_store_ok with (m := m2);
              [ intros i Hi; apply (stk_wv m2 (S - 8800) A); [exact ST2 | lia] | apply wmono_refl | lia | lia ]).
      rewrite (unsigned_lit A) by lia.
      step. store_done.
      step.
      rewrite (rc_lts_signed (A - 128) (A - 4096)) by lia.
      replace (A - 128 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (FL3 : FLG (A - 128) 0 (Z_to_bv 64 0) mf) end.
      { destruct FL2 as [(flg & Hfl & Hfln & HflF) _]. split; [|intros HC; discriminate HC].
        exists flg. split; [|split; [exact Hfln | exact HflF]].
        eapply fl_bytes; [exact Hfl | exact MUp |].
        intros x Hx. rewrite Hfln, EFL0 in Hx. change (fs_M 1) with 8192 in Hx.
        cbn [outside]. split; [clear -Hx HFS' HAlo HAhi RS P1; lia | exact I]. }
      eapply (fwords (A - 128) 0 (A - 128) 0 0 (Z_to_bv 64 0)); [left; repeat split; lia | | exact FL3 | exact K].
      refine (conj _ (conj WM3 (conj RM3 (conj MI2 FR2)))). unfold Wf, shadow_addr. exact MU3.
    - (* the side-stack frame fs_frame FS 1 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A) in FRM by lia.
      replace (fs_B 1) with 128 in FRM by reflexivity.
      change (bv_unsigned (Z_to_bv 64 128)) with 128 in FRM.
      replace (fs_shadow_n 1 128) with 16 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFLg & H24 & H120 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 1) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 1) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 1 jj) as fra eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hjj.
      assert (SHb : shadow_addr fra + 16 <= S - 8800)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (EFl : fs_flag FS 1 jj = FS + 20480 + jj)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      pose proof HFS' as HFSw.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFLg). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H120). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf fra jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi RS; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi RS; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
        ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES]; rewrite EFl;
              clear -HFS' FShi Hjj SHb HAlo HAhi RS; lia)) as FR2.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      (* flag jj was 0 at m1 (the frame __asan_stack_malloc_1 took was free), and the prologue wrote only the window *)
      assert (HFj0 : bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0]).
      { pose proof HFl as (Ba & Bl & BH).
        assert (HJ : (Z.to_nat jj < length flags)%nat) by (rewrite EM1 in HFln; lia).
        pose proof (BH (Z.to_nat jj) HJ) as E1. rewrite Hnth in E1. rewrite Z2Nat.id in E1 by lia.
        replace (fs_flag FS 1 0 + jj) with (fs_flag FS 1 jj) in E1 by (unfold fs_flag; lia).
        split; [rewrite EFl; lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat]; rewrite EFl; lia|].
        intros i0 Hi0. cbn [length] in Hi0. destruct i0 as [|i0]; [|lia].
        cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. rewrite <- E1.
        unfold mrd. rewrite (MU (wa (fs_flag FS 1 jj))); [reflexivity|].
        rewrite wa_unsigned by (rewrite EFl; lia). cbn [outside]. rewrite EFl. split; [lia | exact I]. }
      assert (HKs : FK fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj))).
      { right. split; [rewrite EM1; exact Hjj|]. split; [exact Efr|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact HFj0]. }
      destruct (fk_facts fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) HKs)
        as (FR8s & FRlos & FRhis & _ & _ & FAPs & FRAs & _ & SH1s & SH2s).
      assert (FL2 : FLG fra 1 (Z_to_bv 64 (fs_flag FS 1 jj)) m2).
      { split.
        - exists (upd_bytes flags (Z.to_nat jj) [Z_to_bv 8 1]). split; [|split].
          + eapply (bytes_at_munch_upd _ m1 m2 (fs_flag FS 1 0) flags (Z.to_nat jj) (Z_to_bv 8 1)).
            * exact HFl.
            * exact MU2.
            * clear -HFln Hjj; change (fs_M 1) with 8192 in HFln; lia.
            * replace (fs_flag FS 1 0 + Z.of_nat (Z.to_nat jj)) with (fs_flag FS 1 jj)
                by (rewrite EFl, EFL0; clear -Hjj; lia).
              exact HFLg.
            * intros x Hx Hne. rewrite HFln in Hx. change (fs_M 1) with 8192 in Hx. rewrite EFL0 in Hx.
              rewrite EFL0 in Hne.
              assert (Hxa : app_mem x) by (apply P4; clear -Hx P1 HFS'; unfold FS_SIZE; lia).
              cbn [outside]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
              -- clear -Hx P1; lia.
              -- rewrite EFl. clear -Hx Hne Hjj; lia.
              -- clear -Hx FRlos; lia.
              -- clear -Hx FRlos; lia.
              -- intros [HL HR]. apply (acl_app_not_shadow x Hxa). unfold shadow_addr in HL, HR.
                 replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
                 apply frame_shadow_in;
                   [clear -FRlos P1; lia | exact FRAs | clear -SH1s; lia | clear -SH2s; lia | lia].
              -- clear -Hx HFS' HAlo HAhi RS P1; lia.
          + rewrite upd_bytes_length by (cbn [length]; clear -HFln Hjj;
              change (fs_M 1) with 8192 in HFln; lia).
            exact HFln.
          + apply upd_bytes_01; [exact HFb | right; reflexivity].
        - intros _. replace (fra + 120) with (fra + 128 - 8) by lia. exact H120. }
      clear MU MU2 WM WM2 RM RM2 FR STA STw STs STz STw2 STzc MI.
      step. step. step. step.
      rewrite (rc_neq0_64 fra) by lia. cbn [negb]. cbv iota.
      eapply (fwords fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)));
        [exact HKs | | exact FL2 | exact K].
      refine (conj _ (conj WM3 (conj RM3 (conj MI2 FR2)))). unfold Wf, shadow_addr. exact MU3.
  Qed.

  (* ================= the body (0x8369c .. 0x83a10) ================= *)

  (* The runtime state carried across the body's calls (asan_memset, asan_memcpy, bcmp_wrap, kind_of_link1). *)
  Definition aJ (mc : word -> option byte) : Prop :=
    asan_cells mc /\ (forall P, shadow_rw_on P m -> shadow_rw_on P mc) /\ addressable mc (S - 8800) 8800 /\
    fpx [1%nat] mc (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    reac_ctrl_parse_tls mc (bv_unsigned tp) FS (S - 8800) S.

  (* The cells the bcmp wrapper reads. *)
  Definition aCL (mc : word -> option byte) : Prop :=
    bytes_at rsegs mc REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mc REAL_MEMCMP (le8 (wa MEMCMP)) /\
    bytes_at rsegs mc GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mc (CF + 254) [Z_to_bv 8 1] /\
    bytes_at rsegs mc (CF + 255) [Z_to_bv 8 1].

  (* The contract's post (reac_ctrl_parse_contract_x of reac_ctrl_parse_c.v, with K = 8800 and sp = S). *)
  Definition Qp : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 8800) S /\
      (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
      asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (S - 8800) 8800 /\
      fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
      Forall (fun ci => bytes_at rsegs m' (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
      (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat ->
         bytes_at rsegs m (fs_flag FS 1%nat 0) fl -> bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
      reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.

  (* 0x839d8 .. 0x83a10: sp = s0 - 128, the saved registers restored from [S - 96, S), the frame popped, ret. The
     class-1 flag array reads back as at m (rcp_flag_kept of the post), so X's flag bytes, which are in it, are still
     1. *)
  Lemma L_restore : forall (m' : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (spc : Z),
    rw_cells rsegs m' (S - 96) SAVES ->
    munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 8800) S ->
    (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) -> aJ m' ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x839d8) fc None m' (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro Lfr X XF0 XB0 RWIN. clear SMAL HMSET HMCPY HBCMPW HKOL RS S16 ST0 MI0 HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 FP0 TLS0 RBY RIMG SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros m' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 spc
      FR MU WM MI ST HBox HaJ HFK.
    unfold SAVES in FR.
    replace (S - 96) with (S + -96) in FR by lia.
    do 14 step. step.
    apply evtF_done. unfold Qp. destruct HaJ as (AC & SW & AW & FP & TL).
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HBox|]. split; [exact AC|]. split; [exact SW|]. split; [exact AW|].
    split; [exact FP|]. split; [|split; [|exact TL]].
    - apply Forall_forall. intros ci Hin. destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (_ & Hb).
      destruct (x_flag_in ci Hin) as (E & L1 & L2).
      apply (bytes_keep m m' _ _ Hb). intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
      rewrite E in Hx. apply HFK. clear -Hx L1 L2. lia.
    - intros fl Hl Hb. apply (bytes_keep m m' _ _ Hb). intros x Hx. apply HFK.
      pose proof (len_le_M fl Hl) as Hl'. clear -Hx Hl'. lia.
  Qed.

  (* The full body footprint stays apart from the runtime's cells [RT_LO, RT_HI): the window and the side stack are
     above them, o is apart (AO0 via the CF cells), and every shadow byte is apart from application memory. *)
  Lemma aout_rt : forall Wm x,
    sub_fp Wm (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]) ->
    RT_LO <= x < RT_HI -> outside Wm x.
  Proof.
    intros Wm x Hs Hx.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & _) & _ & _ & _ & HFSb & _ & _ & _).
    unfold HIGHMEM_BEG, APPMEM_END in HHM'. unfold RT_LO, RT_HI in Hx. unfold ASAN_GT in P3.
    unfold FS_SIZE in HFSb.
    assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
    assert (EFR0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    apply Hs. apply fl_out_app.
    - unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K. cbn [outside]. split; [lia|].
      destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      destruct (AO0 Eo) as (_ & _ & DRT). unfold GOT_CF, CF in DRT. split; [lia | exact I].
    - assert (F0 : 0 <= fs_frame FS 1 0) by (rewrite EFR0; lia).
      assert (FM : fs_frame FS 1 (fs_M 1) <= APPMEM_END) by (rewrite EFM; clear -HFSb HAE; lia).
      assert (W0 : 0 <= S - 8800) by lia.
      apply fl_out_app.
      + unfold fp_w, fp_w1; cbn [flat_map app outside].
        split; [unfold fs_hint; cbn [Z.of_nat]; lia|].
        split; [unfold fs_flag, fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
        split; [rewrite EFR0; lia|].
        split; [exact (acl_sh_out x (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hap F0 FM)|].
        exact I.
      + cbn [outside]. split; [|exact I].
        exact (acl_sh_out x (S - 8800) S Hap W0 HAE).
  Qed.

  (* The post's asan runtime state (asan_cells, shadow_rw, fpx, tls) once the run wrote only within the window+o
     (fp's W), the class-1 side-stack bytes (fp_w [1] FS) and the window's shadow, with the hint and flag bytes read
     back as 0/1 at m'. fp (with no data ranges) is rebuilt by fl_fp_free and the data ranges' fp_wx-disjointness
     is FP0's; the tls premise by acl_tls_ret. *)
  Lemma aJ_free : forall Wm m',
    munch Wm m m' -> wmono rsegs m m' -> rd_mono m m' ->
    sub_fp Wm (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]) ->
    (forall x, FS + 80 <= x < FS + 104 -> outside Wm x) ->
    (forall x, FS <= x < FS + FS_SIZE -> outside Wm x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
    (exists h', bytes_at rsegs m' (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs m' (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
    fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.
  Proof.
    intros Wm m' MU WM RM Hs O88 HRD Hint Hflags.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPn.
    split; [|split; [|split]].
    - apply (fl_asan_cells Wm m m' AC0 MU). intros x Hx. exact (aout_rt Wm x Hs Hx).
    - intros P HP. exact (shadow_rw_mono_on P m m' HP WM RM).
    - apply fpx_of_fp_nil; [|exact (fpx_dj _ _ _ _ _ _ _ _ _ FP0)].
      eapply (fl_fp_free [1%nat] m m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S)
               [] Wm FPn TLS0 MU WM Hs O88 HRD).
      intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[]]. split; [exact Hint | exact Hflags].
    - exact (acl_tls_ret [1%nat] m m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S)
               [] [(shadow_addr (S - 8800), shadow_addr S)] Wm FPn TLS0 MU Hs).
  Qed.

  (* The body/exit footprint: the Qp footprint (the class-1 side stack less X's frames and their shadow, fp_wx) plus
     the frame and its shadow (written explicitly by the un-poison), weakened to the Qp footprint in each exit branch. *)
  Definition Wex (fra : Z) : list ivl :=
    (shadow_addr fra, shadow_addr fra + 16) :: (fra, fra + 128) ::
    reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X.

  (* The same with the whole class-1 side stack (fp_w), which aJ_free's footprint names. *)
  Definition Wexw (fra : Z) : list ivl :=
    (shadow_addr fra, shadow_addr fra + 16) :: (fra, fra + 128) ::
    reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS.

  Lemma Wex_sub_w : forall fra, sub_fp (Wex fra) (Wexw fra).
  Proof.
    intros fra x Hx. unfold Wexw in Hx. unfold Wex. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    apply acl_out_app_inv in H3 as [H3 H4]. apply fl_out_app; [exact H3 | exact (fp_wx_sub_w _ _ _ _ H4)].
  Qed.

  (* A high-shadow address y is not inside a short application-memory range [a, b). *)
  Lemma sh_hi_small_out : forall y a b,
    HIGHSHADOW_BEG <= y < HIGHMEM_BEG -> app_mem a -> a <= b -> b <= a + 2000000000 -> ~ (a <= y < b).
  Proof.
    intros y a b Hy Ha Hab Hb [H1 H2].
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, HIGHSHADOW_BEG, APPMEM_END in *. destruct Ha; lia.
  Qed.

  (* The shadow of a window byte z, apart from the released frame [fra, fra+128), is outside the exit footprint Wex. *)
  Lemma wex_sh_out : forall fra z,
    0 <= fra -> fra mod 8 = 0 -> app_mem fra -> fra + 128 <= APPMEM_END ->
    S - 8800 <= z < S -> (z < fra \/ fra + 128 <= z) ->
    outside (Wex fra) (shadow_addr z).
  Proof.
    intros fra z Hf0 Hfm Hfap Hfe Hz Hnf. apply Wex_sub_w.
    pose proof HHM as HHM0. pose proof HAE as HAE0. unfold HIGHMEM_BEG, APPMEM_END in HHM0, HAE0.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & _) & _ & _ & _ & HFSb & _ & _ & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    assert (Hzsh : HIGHSHADOW_BEG <= shadow_addr z < HIGHMEM_BEG).
    { unfold shadow_addr, ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
    assert (Esh16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (rewrite <- (sh_add8 fra 16 Hfm); f_equal; lia).
    assert (EFR0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Hwinapp : app_mem (S - 8800)) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia).
    assert (Hhintapp : app_mem (fs_hint FS 1)) by (apply Pfsapp; unfold fs_hint, FS_SIZE; cbn [Z.of_nat]; lia).
    assert (Hflagapp : app_mem (fs_flag FS 1 0))
      by (apply Pfsapp; unfold fs_flag, fs_M, FS_SIZE; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (Hfr0app : app_mem (fs_frame FS 1 0)) by (apply Pfsapp; rewrite EFR0; unfold FS_SIZE; lia).
    assert (Hfrge : shadow_addr (fs_frame FS 1 (fs_M 1)) <= shadow_addr z)
      by (apply acl_sh_ge; rewrite EFM; lia).
    unfold Wexw, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K, fp_w, fp_w1.
    destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [app flat_map outside fst snd].
    - split; [rewrite Esh16; exact (acl_win_sh z fra (fra + 128) Hfm ltac:(destruct Hnf; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) fra (fra + 128) Hzsh Hfap ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (S - 8800) S Hzsh Hwinapp ltac:(lia) ltac:(lia))|].
      split; [unfold fs_hint; cbn [Z.of_nat];
              exact (sh_hi_small_out (shadow_addr z) (FS + 8) (FS + 8 + 8) Hzsh
                       ltac:(unfold fs_hint in Hhintapp; cbn [Z.of_nat] in Hhintapp; exact Hhintapp)
                       ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1) Hzsh Hflagapp
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia)
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hzsh Hfr0app
                       ltac:(rewrite EFR0, EFM; lia) ltac:(rewrite EFR0, EFM; lia))|].
      split; [lia | exact I].
    - destruct (AO0 Eo) as (AOa & AOb & AOc).
      pose proof (acl_app_in m o 36 0 AOa ltac:(lia)) as AOo. rewrite Z.add_0_r in AOo.
      split; [rewrite Esh16; exact (acl_win_sh z fra (fra + 128) Hfm ltac:(destruct Hnf; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) fra (fra + 128) Hzsh Hfap ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) o (o + 36) Hzsh AOo ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (S - 8800) S Hzsh Hwinapp ltac:(lia) ltac:(lia))|].
      split; [unfold fs_hint; cbn [Z.of_nat];
              exact (sh_hi_small_out (shadow_addr z) (FS + 8) (FS + 8 + 8) Hzsh
                       ltac:(unfold fs_hint in Hhintapp; cbn [Z.of_nat] in Hhintapp; exact Hhintapp)
                       ltac:(lia) ltac:(lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1) Hzsh Hflagapp
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia)
                       ltac:(unfold fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia))|].
      split; [exact (sh_hi_small_out (shadow_addr z) (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hzsh Hfr0app
                       ltac:(rewrite EFR0, EFM; lia) ltac:(rewrite EFR0, EFM; lia))|].
      split; [lia | exact I].
  Qed.

  (* The post asan state at the exit memory m' (asan_cells, shadow_rw, fpx, tls), packaging aJ_free for a frame fra
     whose release wrote only Wex (inside Wexw, the footprint aJ_free names). *)
  Lemma Wex_free : forall fra fv spc j nn w120 (m' : word -> option byte),
    FK fra fv spc j nn w120 ->
    munch (Wex fra) m m' -> wmono rsegs m m' -> rd_mono m m' ->
    (exists h', bytes_at rsegs m' (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs m' (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
    fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.
  Proof using tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AO0 X FP0 TLS0. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd AW0 AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XF0 XB0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 m' HK MU0 WM RM Hint Hflags.
    pose proof (munch_weaken _ _ _ _ (Wex_sub_w fra) MU0) as MU. clear MU0.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM0. pose proof HAE as HAE0. unfold HIGHMEM_BEG, APPMEM_END in HHM0, HAE0.
    pose proof FP0 as (DT & TS & C & T & DB & k & HT & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (EFR0c0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Esh16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (rewrite <- (sh_add8 fra 16 FR8); f_equal; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
    (* sub_fp: Wexw fra refines the Qp footprint. *)
    assert (Hsub : sub_fp (Wexw fra)
                     (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)])).
    { intros x Hxt.
      apply acl_out_app_inv in Hxt as [HxW Hxr]. apply acl_out_app_inv in Hxr as [Hxfpw Hxwin].
      unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K in HxW. cbn [outside] in HxW. destruct HxW as [HxWin HxWo].
      cbn [outside] in Hxwin. destruct Hxwin as [Hxws _].
      unfold Wexw. apply (fl_out_app [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)]
                           (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS)).
      - cbn [outside]. split; [|split; [|exact I]].
        + (* ~ (shadow_addr fra, shadow_addr fra + 16) *)
          rewrite Esh16.
          destruct HK as [(_ & Efra & _) | (Hj & Efra & _)].
          * subst fra. intros [HL HR]. apply Hxws. split.
            -- pose proof (acl_sh_ge (A - 128) (S - 8800) ltac:(lia)) as Hge. lia.
            -- pose proof (acl_sh_ge S (A - 128 + 128) ltac:(lia)) as Hge. lia.
          * pose proof Hxfpw as Hf. unfold fp_w, fp_w1 in Hf. cbn [flat_map app outside fst snd] in Hf.
            destruct Hf as (_ & _ & _ & Hfsh & _). subst fra. intros [HL HR]. apply Hfsh. split.
            -- pose proof (acl_sh_ge (fs_frame FS 1 j) (fs_frame FS 1 0)
                             ltac:(rewrite EFR1, EFRj; lia)) as Hge. lia.
            -- pose proof (acl_sh_ge (fs_frame FS 1 (fs_M 1)) (fs_frame FS 1 j + 128)
                             ltac:(rewrite EFRj, EFM; lia)) as Hge. lia.
        + (* ~ (fra, fra + 128) *)
          destruct HK as [(_ & Efra & _) | (Hj & Efra & _)].
          * subst fra. intros [HL HR]. apply HxWin. split; lia.
          * pose proof Hxfpw as Hf. unfold fp_w, fp_w1 in Hf. cbn [flat_map app outside fst snd] in Hf.
            destruct Hf as (_ & _ & Hfrm & _). subst fra. intros [HL HR]. apply Hfrm.
            rewrite EFRj in HL, HR. rewrite EFR1, EFM. split; lia.
      - apply fl_out_app; [|exact Hxfpw].
        unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. apply fl_out_app; [exact HxWo|].
        cbn [outside]. split; [exact HxWin | exact I]. }
    (* O88: the asan header words FS+80..FS+104 are outside Wexw. *)
    assert (O88 : forall x, FS + 80 <= x < FS + 104 -> outside (Wexw fra) x).
    { intros x Hx. apply Hsub.
      assert (Hxapp : app_mem x) by (apply Pfsapp; unfold FS_SIZE; lia).
      apply fl_out_app; [|apply fl_out_app].
      - exact (fl_dj_out (reac_ctrl_parse_W o S) _ FS (fs_frame FS 0 0) x HWd
                 ltac:(apply in_or_app; right; left; reflexivity) ltac:(rewrite EFR0c0; lia)).
      - unfold fp_w, fp_w1. cbn [flat_map app outside fst snd].
        split; [unfold fs_hint; cbn [Z.of_nat]; lia|].
        split; [unfold fs_flag, fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
        split; [rewrite EFR1; lia|].
        split; [exact (acl_sh_out x (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hxapp
                         ltac:(rewrite EFR1; lia) ltac:(rewrite EFM; lia)) | exact I].
      - cbn [outside]. split; [|exact I].
        exact (acl_sh_out x (S - 8800) S Hxapp ltac:(lia) ltac:(lia)). }
    (* HRD: the side stack stays readable at m'. *)
    assert (HRD : forall x, FS <= x < FS + FS_SIZE -> outside (Wexw fra) x \/ exists b, mrd rsegs m' (wa x) = Some b).
    { intros x Hx. right. apply RM. exact (rd_of_stk m FS (FS + FS_SIZE) Pfsstk x Hx). }
    apply (aJ_free (Wexw fra) m'); [exact MU | exact WM | exact RM | exact Hsub | exact O88 | exact HRD | exact Hint | exact Hflags].
  Qed.

  (* Wex fra refines the Qp footprint in reac_ctrl_parse_fp order (for L_restore's munch): a side frame j and its
     shadow are inside fp_wx [1] FS X, as j is not an index of X (its flag was 0 at m, FK). *)
  Lemma Wex_subfp : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wex fra) (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]).
  Proof using tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X XF0 FP0. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd HOK AC0 AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 XB0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS RFLG RFRM SCFR SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (Pfs0 & Pfs1 & _) & _).
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
    assert (Esh16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (rewrite <- (sh_add8 fra 16 FR8); f_equal; lia).
    intros x Hxt.
    apply acl_out_app_inv in Hxt as [Hxfp Hxr]. apply acl_out_app_inv in Hxr as [Hxfpw Hxwin].
    pose proof Hxfp as Hxfp0. unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in Hxfp0.
    apply acl_out_app_inv in Hxfp0 as [HxWo HxW2]. cbn [outside] in HxW2. destruct HxW2 as [HxWin _].
    cbn [outside] in Hxwin. destruct Hxwin as [Hxws _].
    unfold Wex. apply (fl_out_app [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)]
                         (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X)).
    - cbn [outside]. split; [|split; [|exact I]].
      + rewrite Esh16. destruct HK as [(_ & Efra & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)].
        * subst fra. intros [HL HR]. apply Hxws. split.
          -- pose proof (acl_sh_ge (A - 128) (S - 8800) ltac:(lia)) as Hge. lia.
          -- pose proof (acl_sh_ge S (A - 128 + 128) ltac:(lia)) as Hge. lia.
        * intros [HL HR]. apply (fp_wx_frame_sh_in FS X j x Hj (x_ne_j j Hfl0)); [|exact Hxfpw].
          rewrite Efra in HL, HR.
          replace (fs_frame FS 1 (j + 1)) with (fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
          split; [exact HL | exact HR].
      + destruct HK as [(_ & Efra & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)].
        * subst fra. intros [HL HR]. apply HxWin. split; lia.
        * intros [HL HR]. apply (fp_wx_frame_in FS X j x Hj (x_ne_j j Hfl0)); [|exact Hxfpw].
          rewrite Efra in HL, HR.
          replace (fs_frame FS 1 (j + 1)) with (fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
          split; [exact HL | exact HR].
    - apply fl_out_app; [|exact Hxfpw].
      unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. apply fl_out_app; [exact HxWo|].
      cbn [outside]. split; [exact HxWin | exact I].
  Qed.

  (* The body's full write footprint Wf is inside the exit footprint Wex (for L_exit's munch). *)
  Lemma subWf_Wex : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wf fra j nn) (Wex fra).
  Proof.
    intros fra fv spc j nn w120 HK.
    assert (Hjb : 0 <= j < 8192 /\ nn <= 1).
    { destruct HK as [(_ & _ & _ & Ej & En) | (Hjb & _ & _ & _ & _ & En & _)];
        [split; lia | change (fs_M 1) with 8192 in Hjb; split; lia]. }
    assert (EFL : fs_flag FS 1 j = fs_flag FS 1 0 + j)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    intros x Hx. unfold Wex in Hx. cbn [outside] in Hx.
    destruct Hx as (Hsh & Hfr & Hrest).
    apply acl_out_app_inv in Hrest as [Hfp Hfpw].
    apply acl_out_app_inv in Hfp as [_ Hwin].
    cbn [outside] in Hwin. destruct Hwin as [Hwin _].
    destruct (wx_out_hint_flag FS X x Hfpw) as (Hhint & Hflagarr).
    unfold Wf. cbn [outside].
    split; [exact Hwin|]. split; [exact Hhint|].
    split; [intros [HL HR]; apply Hflagarr; rewrite EFL in HL, HR;
            change (fs_M 1) with 8192; clear -HL HR Hjb; split; lia|].
    split; [exact Hfr|]. split; [exact Hsh | exact I].
  Qed.

  (* An app-memory byte apart from the released frame [fra, fra+128) is outside the small exit footprint. *)
  Lemma Wsmall_outside : forall fra x,
    0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
    2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
    app_mem x -> (x < fra \/ fra + 128 <= x) ->
    outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] x.
  Proof.
    intros fra x Hf0 FRA SH1 SH2 Hxapp Hnf. cbn [outside]. split; [|split; [|exact I]].
    - intros [HL HR]. apply (acl_app_not_shadow x Hxapp).
      replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
      apply frame_shadow_in; [exact Hf0 | exact FRA | exact SH1 | exact SH2 | lia].
    - intros [HL HR]. destruct Hnf; lia.
  Qed.

  (* Everything the body needs about the output box ob (the frame's redzone fra + 32 when o = 0, else o): its
     range and alignment, its distance from the runtime's cells, from the deepest callee window (the bcmp
     wrapper's 4560 bytes), from the saved registers, from the 50 bytes at f, from the frame and from the
     class-1 flag array. *)
  Lemma ob_facts : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob ->
    0 <= ob /\ ob + 36 <= 2 ^ 64 /\ ob mod 4 = 0 /\ app_mem (ob + 36) /\
    (ob + 36 <= RT_LO \/ RT_HI <= ob) /\
    (ob + 36 <= spc - 4560 \/ spc <= ob) /\
    (ob + 36 <= S - 96 \/ S <= ob) /\
    (50 <= n -> ob + 36 <= f \/ f + 50 <= ob) /\
    (ob = fra + 32 \/ ob + 36 <= fra \/ fra + 128 <= ob) /\
    (fs_flag FS 1 0 + fs_M 1 <= ob \/ ob + 36 <= fs_flag FS 1 0) /\
    (ob + 36 <= GOT_CF \/ CF + 256 <= ob).
  Proof.
    intros fra fv spc j nn w120 ob HK HO.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    destruct HO as [(Eo & Eob) | (Eo & Eob)]; subst ob.
    - (* the box is the frame's redzone *)
      assert (Hbox36 : app_mem (fra + 32 + 36))
        by (replace (fra + 32 + 36) with (fra + 68) by lia; apply FAP; lia).
      destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew & Enn & Hfl0)].
      + (* the real-stack frame: fra = A - 128, inside the window *)
        split; [clear -FRlo Pfs0; lia|]. split; [clear -Efra HAhi RS; lia|].
        split; [clear -FR8; Z.div_mod_to_equations; lia|]. split; [exact Hbox36|].
        split; [right; unfold RT_HI; clear -FRlo Pfs0 Pfs2; lia|].
        split; [right; clear -Espc Efra; lia|].
        split; [left; clear -Efra HAhi RS; lia|].
        split; [intros Hn50; destruct (HF Hn50) as (_ & _ & HfS); destruct HfS as [Hc|Hc];
                [right; clear -Hc Efra HAlo HAhi RS; lia | left; clear -Hc Efra HAhi RS; lia]|].
        split; [left; reflexivity|].
        split; [left; rewrite EFL0, EM1; clear -FRlo Pfs0; lia|].
        right. unfold CF. clear -FRlo Pfs0 Pfs2; lia.
      + (* the side-stack frame: fra = fs_frame FS 1 j *)
        rewrite EM1 in Hj.
        assert (EFRj : fra = FS + 1085440 + j * 128)
          by (rewrite Efra; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
        split; [clear -EFRj Hj Pfs0; lia|]. split; [clear -EFRj Hj HFSb RS; lia|].
        split; [clear -FR8; Z.div_mod_to_equations; lia|]. split; [exact Hbox36|].
        split; [right; unfold RT_HI; clear -EFRj Hj Pfs0; lia|].
        split; [left; clear -EFRj Hj HFSb Hspcr RS; lia|].
        split; [left; clear -EFRj Hj HFSb RS; lia|].
        split; [intros Hn50;
                destruct (D_apart_frame f (f + 50) j
                  ltac:(unfold reac_ctrl_parse_D; apply in_or_app; left;
                        rewrite (proj2 (Z.ltb_ge n 50) Hn50); left; reflexivity)
                  ltac:(clear; lia) ltac:(rewrite EM1; exact Hj) Hfl0) as [Hc|Hc];
                rewrite <- Efra in Hc;
                [right; clear -Hc; lia | left; clear -Hc; lia]|].
        split; [left; reflexivity|].
        split; [left; rewrite EFL0, EM1; clear -EFRj Hj Pfs0; lia|].
        right. unfold CF. clear -EFRj Hj Pfs0 Pfs2; lia.
    - (* the box is o *)
      destruct (HOK Eo) as (Ho4 & Ho36 & HOrw & HoS & Hof).
      destruct (AO0 Eo) as (AOa & AOapp & AOcf).
      pose proof AOa as (AO0' & _).
      split; [clear -AO0'; lia|]. split; [clear -Ho36; lia|].
      split; [exact Ho4|]. split; [exact AOapp|].
      split; [destruct AOcf as [Hc|Hc];
              [left; unfold GOT_CF, RT_LO in Hc |- *; clear -Hc; lia
              | right; unfold CF, RT_HI in Hc |- *; clear -Hc; lia]|].
      split; [destruct HoS as [Hc|Hc]; [left | right]; clear -Hc Hspcr RS; lia|].
      split; [destruct HoS as [Hc|Hc]; [left | right]; clear -Hc RS; lia|].
      split; [intros Hn50; destruct (Hof Hn50) as [Hc|Hc]; [left | right]; clear -Hc; lia|].
      split.
      + right.
        destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew & Enn & Hfl0)].
        * destruct HoS as [Hc|Hc]; [left | right]; clear -Hc Efra HAlo HAhi RS; lia.
        * destruct (D_apart_frame o (o + 36) j
            ltac:(unfold reac_ctrl_parse_D; apply in_or_app; right;
                  rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity)
            ltac:(clear; lia) Hj Hfl0) as [Hc|Hc];
            rewrite <- Efra in Hc; [left | right]; clear -Hc; lia.
      + split.
        * pose proof (dj_pair o (o + 36) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1)
            ltac:(unfold reac_ctrl_parse_D; apply in_or_app; right;
                  rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity)
            (proj2 (fp_wx_hint_flag_in FS X))) as Hd.
          destruct Hd as [Hc|Hc]; [right | left]; clear -Hc; lia.
        * exact AOcf.
  Qed.

  (* The body's own writes (the box and the callee windows) are inside the exit footprint. *)
  Lemma ob_wex : forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob ->
    sub_fp [(ob, ob + 36); (S - 8800, spc)] (Wex fra).
  Proof.
    intros fra fv spc j nn w120 ob HK HO x Hx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    unfold Wex in Hx. cbn [outside] in Hx. destruct Hx as (Hsh & Hfr & Hrest).
    apply acl_out_app_inv in Hrest as [Hfp Hfpw].
    unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in Hfp.
    apply acl_out_app_inv in Hfp as [Hbox Hwin]. cbn [outside] in Hwin. destruct Hwin as [Hwin _].
    cbn [outside]. split; [|split; [|exact I]].
    - destruct HO as [(Eo & Eob) | (Eo & Eob)]; subst ob.
      + clear -Hfr; lia.
      + rewrite (proj2 (Z.eqb_neq o 0) Eo) in Hbox. cbn [outside] in Hbox. exact (proj1 Hbox).
    - clear -Hwin Hspc; lia.
  Qed.

  (* Wex fra refines the Qp footprint in reac_ctrl_parse_W order (for aout_rt). *)
  Lemma Wex_subW : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wex fra) (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]).
  Proof.
    intros fra fv spc j nn w120 HK x Hx.
    apply (Wex_subfp fra fv spc j nn w120 HK).
    apply acl_out_app_inv in Hx as [HW HY]. apply fl_out_app.
    2:{ apply acl_out_app_inv in HY as [HY1 HY2].
        apply fl_out_app; [exact (fp_wx_sub_w _ _ _ _ HY1) | exact HY2]. }
    unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K in HW. cbn [outside] in HW. destruct HW as [H1 H2].
    unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. apply fl_out_app; [exact H2|].
    cbn [outside]. split; [exact H1 | exact I].
  Qed.

  (* 0x83920 .. 0x83a10: the frame-shadow rewrite (un-poison), the side-frame flag cleared, the registers restored,
     ret. Reaches Qp through L_restore. FKP: the body wrote no byte of the class-1 flag array other than flag j (the
     side frame's, set by __asan_stack_malloc_1 and cleared here back to its 0 at m). *)
  Lemma L_exit : forall fra fv spc j nn w120 mc
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 ->
    munch (Wex fra) m mc ->
    wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc -> stk rsegs mc (S - 8800) S ->
    rw_cells rsegs mc (S - 96) SAVES ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (exists h', bytes_at rsegs mc (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    (nn = 1 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + nn) ->
       mrd rsegs mc (wa x) = mrd rsegs m (wa x)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mc (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW RFLG RFRM SCFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 HF Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFSS SKFR RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31
      HK MU WM RM MI AC SR ST SV HBox Hhint Hflags Hw120 FKP.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Ush : bv_unsigned (Z_to_bv 64 (fra / 8 + ASAN_K)) = fra / 8 + ASAN_K)
      by (apply unsigned_lit; clear -SH1 SH2; lia).
    assert (Ufra : bv_unsigned (Z_to_bv 64 fra) = fra)
      by (apply unsigned_lit; clear -FRlo FRhi HAhi RS Pfs0; lia).
    assert (HHMl : 17594333495296 <= S - 8800)
      by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    (* the munch from m (over Wex, whose fp_wx part has an abstract X) is kept out of the store tracking; the exit's
       own writes are tracked from mc on the tight footprints MUe / MUx, and the two are composed at the end *)
    pose proof (conj MU I) as MUn. clear MU.
    pose proof HK as HKc.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)] mc) as MUe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128);
                            (fs_flag FS 1 j, fs_flag FS 1 j + 1)] mc) as MUx.
    pose proof (wmono_refl rsegs mc) as WMe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 8)] mc) as MUw.
    unfold shadow_addr in MUe, MUx, MUw.
    step.
    wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    step. step.
    wstb fra 8%nat fra FW. step. store_done.
    destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew120 & Enn & Hfl0)].
    - (* real-stack frame: fv = 0 *)
      subst fv. step.
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbv iota.
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (shadow_rw_mono_on _ m mcur SR0 WM RM) as SRc;
        pose proof (shadow16_stk_on mcur fra (srw_frame fra _ _ _ _ _ mcur HKc SRc) ltac:(clear -FRlo Pfs0; lia) FRA
                      ltac:(clear -SH1; lia) ltac:(clear -SH2; lia)) as STsh
      end.
      pose proof (stk_carve rsegs _ (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(clear -SH1; lia))
        as [STsh' [junkS SHC]].
      replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
      sstep (fra / 8 + ASAN_K) 4 4%nat SW. sstep (fra / 8 + ASAN_K) 5 5%nat SW.
      sstep (fra / 8 + ASAN_K) 6 6%nat SW. sstep (fra / 8 + ASAN_K) 7 7%nat SW.
      sstep (fra / 8 + ASAN_K) 0 0%nat SW. sstep (fra / 8 + ASAN_K) 1 1%nat SW.
      sstep (fra / 8 + ASAN_K) 2 2%nat SW. sstep (fra / 8 + ASAN_K) 3 3%nat SW.
      sstep (fra / 8 + ASAN_K) 12 12%nat SW. sstep (fra / 8 + ASAN_K) 13 13%nat SW.
      sstep (fra / 8 + ASAN_K) 14 14%nat SW. sstep (fra / 8 + ASAN_K) 15 15%nat SW.
      sstep (fra / 8 + ASAN_K) 8 8%nat SW. sstep (fra / 8 + ASAN_K) 9 9%nat SW.
      sstep (fra / 8 + ASAN_K) 10 10%nat SW. sstep (fra / 8 + ASAN_K) 11 11%nat SW.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      assert (EFL : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      pose proof (FAP 0 ltac:(lia)) as Hfraapp. rewrite Z.add_0_r in Hfraapp.
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi RS HAE; unfold APPMEM_END in *; lia).
      destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
      destruct Hhint as [h' Hh]. destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (MU : munch (Wex fra) m mf)
          by (apply (munch_trans _ m mc mf (proj1 MUn)); eapply munch_weaken; [|exact MUe];
              intros y Hy; unfold Wex, shadow_addr in Hy; cbn [outside] in Hy |- *;
              destruct Hy as (H1 & H2 & _); exact (conj H1 (conj H2 I)))
      end.
      eapply L_restore.
      + exact SV.
      + eapply munch_weaken; [exact (Wex_subfp fra 0 spc j nn w120 HKc) | exact MU].
      + exact WM.
      + exact MI.
      + exact ST.
      + intros Ho. eapply acl_rw; [exact (HBox Ho) | exact MUe | exact WMe |].
        intros y Hy. apply Wsmall_outside; [clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2 | |].
        * destruct (AO0 Ho) as (AOa & _ & _). pose proof (acl_app_in m o 36 (y - o) AOa ltac:(cbn [cells_size csize] in Hy; lia)) as Hya.
          replace (o + (y - o)) with y in Hya by lia. exact Hya.
        * destruct (HOK Ho) as (_ & _ & _ & HowS & _). rewrite Efra.
          cbn [cells_size csize] in Hy. destruct HowS as [Hc|Hc]; [left | right]; clear -Hy Hc HAlo HAhi RS; lia.
      + lazymatch goal with |- aJ ?mf =>
          assert (Hz16 : forall g, 0 <= g <= 15 ->
                    exists b, mrd rsegs mf (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0);
          [ destruct HB16 as (_ & _ & Hr); intros g Hg; exists (Z_to_bv 8 0); split; [|vm_compute; reflexivity];
            pose proof (Hr (Z.to_nat g) ltac:(cbn [length]; lia)) as Hg';
            replace (fra / 8 + ASAN_K + Z.of_nat (Z.to_nat g)) with (fra / 8 + ASAN_K + g) in Hg' by lia;
            rewrite Hg';
            assert (Hc : g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9\/g=10\/g=11\/g=12\/g=13\/g=14\/g=15) by lia;
            repeat (destruct Hc as [Hc|Hc]); subst g; vm_compute; reflexivity
          | ];
          assert (AFR : addressable mf fra 128)
            by (apply frame_all_addr; [clear -FRlo Pfs0; lia | exact FR8 | exact Hfe | exact FAP | exact Hz16]);
          assert (ABLO : addressable mf (S - 8800) (fra - (S - 8800)));
          [ apply (acl_addr_munch (Wex fra) m mf (S - 8800) (fra - (S - 8800)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (S - 8800) (fra - (S - 8800)) AW0);
                [ lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRlo HAlo HAhi RS Efra; rewrite Efra in *; lia | left; clear -Hi; lia ] ]
          | ];
          assert (AABOVE : addressable mf (fra + 128) (S - (fra + 128)));
          [ apply (acl_addr_munch (Wex fra) m mf (fra + 128) (S - (fra + 128)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (fra + 128) (S - (fra + 128)) AW0);
                [ clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRhi HAhi RS Efra; rewrite Efra; lia
                | clear -FRhi HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRhi HAlo HAhi RS Efra; rewrite Efra in *; lia | right; clear -Hi; lia ] ]
          | ];
          assert (AWfinal : addressable mf (S - 8800) 8800);
          [ pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800)) 128 ABLO
                         ltac:(replace (S - 8800 + (fra - (S - 8800))) with fra by (clear; lia); exact AFR)
                         ltac:(lia)) as J1;
            pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800) + 128) (S - (fra + 128)) J1
                         ltac:(replace (S - 8800 + (fra - (S - 8800) + 128)) with (fra + 128) by (clear; lia); exact AABOVE)
                         ltac:(clear -FRhi HAhi RS Efra; rewrite Efra; lia)) as J2;
            exact (acl_addr_sub mf (S - 8800) (fra - (S - 8800) + 128 + (S - (fra + 128))) (S - 8800) 8800 J2
                     ltac:(lia) ltac:(lia) ltac:(clear; lia))
          | ];
          assert (Hfree : asan_cells mf /\ (forall P, shadow_rw_on P m -> shadow_rw_on P mf) /\
                    fpx [1%nat] mf (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                    reac_ctrl_parse_tls mf (bv_unsigned tp) FS (S - 8800) S);
          [ apply (Wex_free fra 0 spc j nn w120 mf HKc MU WM RM);
            [ exists h'; eapply fl_bytes; [exact Hh | exact MUe |];
              intros y Hy; unfold fs_hint in Hy; rewrite length_le8 in Hy; cbn [Z.of_nat] in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ]
            | exists flags'; split; [|split; [exact Hfllen | exact HflF]];
              eapply fl_bytes; [exact Hfl | exact MUe |];
              intros y Hy; rewrite Hfllen, EM1, EFL in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ] ]
          | ];
          destruct Hfree as (Hac & Hsw & Hfp & Htl);
          split; [exact Hac|]; split; [exact Hsw|]; split; [exact AWfinal|]; split; [exact Hfp | exact Htl]
        end.
      + intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL, EM1 in Hx; clear -Hx; lia).
        lazymatch goal with |- mrd rsegs ?mf (wa x) = _ =>
          rewrite (munch_mrd_out _ mc mf x MUe ltac:(clear -Hxr Pfs0 HFSb RS; lia)
                     ltac:(apply Wsmall_outside;
                             [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                             | apply Pfsapp; unfold FS_SIZE; clear -Hxr; lia
                             | left; clear -Hxr FRlo; lia ]))
        end.
        apply FKP; [exact Hx | rewrite Enn; clear; lia].
    - (* side-stack frame: fv = fra <> 0 *)
      subst fv.
      pose proof (Hw120 Enn) as Hw120'.
      step.
      rewrite (rc_neq0_64 fra) by (clear -FRlo FRhi HAhi RS Pfs0; lia). cbn [negb]. cbv iota.
      step.
      wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 0) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 1) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 2) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 3) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 12) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 13) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 14) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 15) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 9) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 10) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 11) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      pose proof (fl_bytes _ mc _ (fra + 120) (le8 w120) Hw120' MUw
        ltac:(intros x Hx; rewrite length_le8 in Hx; cbn [Z.of_nat] in Hx; cbn [outside];
              split; [| split; [| exact I]];
              [ intros [HL HR]; apply (acl_app_not_shadow x);
                [ replace x with (fra + (x - fra)) by lia; apply FAP; lia
                | replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia;
                  apply frame_shadow_in;
                  [ clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia ] ]
              | intros [HL HR]; clear -Hx HL HR; lia ])) as Hw120m.
      pose proof (bytes_ro8 _ (fra + 120) w120 Hw120m) as Hw120c.
      step.
      subst w120.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hj.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
        by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
        by (apply unsigned_lit; exact Rfl).
      assert (SOK : store_ok rsegs m1 (wa (fs_flag FS 1 j)) 1 = true).
      { eapply (wv_store_ok m m1 (fs_flag FS 1 j) 1%nat).
        - intros i Hi. replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (cbn in Hi; lia).
          apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
          rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
        - exact WM.
        - clear -Rfl; lia.
        - clear -Rfl; cbn; lia. }
      assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
      { assert (EMj : fs_M 1 = 8192) by reflexivity.
        eapply rng_sub; [exact RFLG | rewrite !fs_flag1; lia | rewrite !fs_flag1; lia]. }
      step.
      replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
      replace (Z_to_bv 64 (fs_flag FS 1 j)) with (wa (fs_flag FS 1 0 + j))
        by (unfold wa; f_equal; rewrite EFLj, EFL0; lia).
      destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      destruct Hhint as [h' Hh].
      pose proof (FAP 0 ltac:(lia)) as Hfrapp. rewrite Z.add_0_r in Hfrapp.
      assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
      assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
      assert (Hfrw : fra + 128 <= S - 8800)
        by (rewrite Efra, EFRj; clear -Pfs0 HFSb Hj; unfold FS_SIZE in HFSb; lia).
      assert (Hfrge : FS + 1085440 <= fra) by (rewrite Efra, EFRj; clear -Hj; lia).
      assert (Afl : 0 <= fs_flag FS 1 0 + j /\ fs_flag FS 1 0 + j + 1 <= 2 ^ 64)
        by (rewrite EFL0; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -Hfrw HAE; unfold APPMEM_END in *; lia).
      (* the flag array [fs_flag FS 1 0, +fs_M 1) is apart from the frame and its shadow *)
      assert (Hdj : forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + Z.of_nat (length flags') ->
                    outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] x).
      { intros x Hx. rewrite Hfllen, EM1 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; rewrite EFL0 in Hx; unfold FS_SIZE; clear -Hx Pfs0 HFSb; lia).
        cbn [outside]. split; [| split; [| exact I]].
        - intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        - intros [HL HR]. rewrite EFL0 in Hx. clear -Hx HL Hfrge; lia. }
      pose proof (fl_bytes _ mc m1 (fs_flag FS 1 0) flags' Hfl MUe Hdj) as Hflm1.
      pose proof (bytes_at_write_inside rsegs m1 (fs_flag FS 1 0) flags' j [Z_to_bv 8 0] Hflm1
        ltac:(clear -Hj; lia)
        ltac:(cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia)) as Hnfl.
      (* facts about m2 = write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] *)
      pose proof (rw_cells_frame rsegs m1 (S - 96) SAVES (fs_flag FS 1 0 + j) [Z_to_bv 8 0] SV
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(right; cbn [length]; rewrite EFL0; clear -Pfs0 HFSb Hj; lia)) as SV2.
      pose proof (wmono_write rsegs m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WM) as WM2.
      pose proof (mem_inv_store rsegs m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] MI
        ltac:(cbn [length]; replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia);
              exact SOK)) as MI2.
      pose proof (stk_write rsegs m1 (S - 8800) S (fs_flag FS 1 0 + j) [Z_to_bv 8 0] ST
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)) as ST2.
      pose proof (rd_mono_write m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] RM) as RM2.
      pose proof (munch_write _ mc m1 (fs_flag FS 1 0 + j) [Z_to_bv 8 0] MUx
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(cbn [lib.Lib.Frame.inside length]; right; right; left; split; [rewrite EFLj, EFL0; clear -Hj; lia | rewrite EFLj, EFL0; clear -Hj; lia])) as MUx2.
      pose proof (wmono_write rsegs mc m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WMe) as WMe2.
      set (m2 := write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0]) in *.
      assert (MU2 : munch (Wex fra) m m2).
      { apply (munch_trans _ m mc m2 (proj1 MUn)). eapply munch_weaken; [|exact MUx2].
        intros y Hy. unfold Wex, shadow_addr in Hy. cbn [outside] in Hy |- *.
        destruct Hy as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. split; [|exact I].
        apply acl_out_app_inv in H3 as [_ H4]. destruct (wx_out_hint_flag FS X y H4) as (_ & Hfa).
        intros [HL HR]. apply Hfa. rewrite EFLj in HL, HR. rewrite EFL0, EM1. clear -HL HR Hj; lia. }
      step.
      eapply L_restore.
      + exact SV2.
      + eapply munch_weaken; [exact (Wex_subfp fra fra spc j nn (Z_to_bv 64 (fs_flag FS 1 j)) HKc) | exact MU2].
      + exact WM2.
      + exact MI2.
      + exact ST2.
      + intros Ho.
        eapply acl_rw; [exact (HBox Ho) | exact MUx2 | exact WMe2 |].
        intros x Hx. cbn [cells_size csize] in Hx.
        assert (Hxa : app_mem x)
          by (destruct (AO0 Ho) as (AOa & _ & _); pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as H;
              replace (o + (x - o)) with x in H by lia; exact H).
        assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
          by (unfold reac_ctrl_parse_D; apply in_or_app; right;
              rewrite (proj2 (Z.eqb_neq o 0) Ho); left; reflexivity).
        pose proof (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) ltac:(rewrite EM1; exact Hj) Hfl0) as Hofr.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        cbn [outside]. split; [| split; [| split; [| exact I]]].
        * intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        * intros [HL HR]. rewrite Efra in HL, HR. clear -Hx HL HR Hofr; lia.
        * intros [HL HR]. rewrite EFLj in HL, HR. rewrite EFL0, EM1 in Hofl. clear -Hx HL HR Hofl Hj; lia.
      + (* aJ m2 *)
        assert (AWfinal : addressable m2 (S - 8800) 8800).
        { apply (acl_addr_munch (Wex fra) m m2 (S - 8800) 8800 AW0 MU2).
          intros i Hi. apply wex_sh_out;
            [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfrapp | exact Hfe
            | clear -Hi; lia | right; clear -Hi Hfrw; lia ]. }
        assert (Hfree : asan_cells m2 /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m2) /\
                  fpx [1%nat] m2 (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                  reac_ctrl_parse_tls m2 (bv_unsigned tp) FS (S - 8800) S).
        { apply (Wex_free fra fra spc j nn (Z_to_bv 64 (fs_flag FS 1 j)) m2 HKc MU2 WM2 RM2).
          - exists h'. eapply fl_bytes; [exact Hh | exact MUx2 |].
            intros y Hy. unfold fs_hint in Hy. rewrite length_le8 in Hy. cbn [Z.of_nat] in Hy.
            cbn [outside]. split; [| split; [| split; [| exact I]]].
            + intros [HL HR]. apply (acl_app_not_shadow y).
              * apply Pfsapp. unfold FS_SIZE; clear -Hy Pfs0; lia.
              * replace y with (fra / 8 + ASAN_K + (y - (fra / 8 + ASAN_K))) by lia.
                apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
            + intros [HL HR]. clear -Hy HL HR Hfrge; lia.
            + intros [HL HR]. rewrite EFLj in HL, HR. clear -Hy HL HR Hj; lia.
          - exists (upd_bytes flags' (Z.to_nat j) [Z_to_bv 8 0]). split; [exact Hnfl|]. split.
            + rewrite upd_bytes_length by (cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia). exact Hfllen.
            + unfold upd_bytes. apply Forall_app. split; [| apply Forall_app; split].
              * pose proof HflF as HFa. rewrite <- (firstn_skipn (Z.to_nat j) flags') in HFa.
                apply Forall_app in HFa. exact (proj1 HFa).
              * constructor; [left; reflexivity | constructor].
              * pose proof HflF as HFb.
                rewrite <- (firstn_skipn (Z.to_nat j + length [Z_to_bv 8 0])%nat flags') in HFb.
                apply Forall_app in HFb. exact (proj2 HFb). }
        destruct Hfree as (Hac & Hsw & Hfp & Htl).
        split; [exact Hac|]. split; [exact Hsw|]. split; [exact AWfinal|]. split; [exact Hfp | exact Htl].
      + (* the flag array: flag j is 0 again (as at m, FK), the rest as at mc (FKP) *)
        intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
        destruct (Z.eq_dec x (fs_flag FS 1 0 + j)) as [Exj|Exj].
        * subst x.
          assert (A0 : mrd rsegs m (wa (fs_flag FS 1 0 + j)) = Some (Z_to_bv 8 0)).
          { destruct Hfl0 as (_ & _ & H0). pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0.
            cbn [Z.of_nat nth_error] in A0. rewrite Z.add_0_r in A0.
            replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia). exact A0. }
          rewrite A0. unfold m2, mrd. cbn [write_to_mem].
          first [rewrite bv_eqb_refl | unfold bv_eqb; rewrite Z.eqb_refl]. reflexivity.
        * assert (Hout : outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128);
                                  (fs_flag FS 1 j, fs_flag FS 1 j + 1)] x).
          { pose proof (Hdj x ltac:(rewrite Hfllen; exact Hx)) as (Ho1 & Ho2 & _).
            cbn [outside]. split; [exact Ho1|]. split; [exact Ho2|]. split; [|exact I].
            rewrite EFLj. rewrite EFL0 in Exj. clear -Exj; lia. }
          rewrite (munch_mrd_out _ mc m2 x MUx2 ltac:(clear -Hxr Pfs0 HFSb RS; lia) Hout).
          apply FKP; [exact Hx | rewrite Enn, EFLj; rewrite EFL0 in Exj; clear -Exj; lia].
  Qed.

  (* The body's whole write footprint from m: the frame block's writes and the output box. *)
  Definition Wall (fra j nn ob : Z) : list ivl := Wf fra j nn ++ [(ob, ob + 36)].

  Lemma mu_all : forall fra fv spc j nn w120 ob mc mx, FK fra fv spc j nn w120 -> OB fra ob ->
    munch (Wf fra j nn) m mc -> munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    munch (Wall fra j nn ob) m mx.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MU MUb.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    eapply munch_trans.
    - eapply munch_weaken; [| exact MU]. unfold Wall. intros x Hx. apply acl_out_app_inv in Hx as [H1 _]. exact H1.
    - eapply munch_weaken; [| exact MUb]. unfold Wall. intros x Hx.
      apply acl_out_app_inv in Hx as [H1 H2]. unfold Wf in H1. cbn [outside] in H1, H2.
      destruct H1 as (Hw & _). destruct H2 as (Hb & _).
      cbn [outside]. split; [exact Hb|]. split; [clear -Hw Hspc; lia | exact I].
  Qed.

  (* The 50 bytes at f, when the header is long enough: in application memory, addressable, and apart from every
     range the body writes. *)
  Lemma f_facts : 50 <= n -> forall fra fv spc j nn w120 ob, FK fra fv spc j nn w120 -> OB fra ob ->
    0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= 2147450880 \/ 17594333495296 <= f) /\
    addressable m f 50 /\ disjoint_from (Wall fra j nn ob) f 50.
  Proof.
    intros Hn50 fra fv spc j nn w120 ob HK HO.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (HF Hn50) as (Hf0 & Hf64 & HfS).
    pose proof (AF0 Hn50) as AFm.
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
      by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    assert (Hjb : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | rewrite EM1 in Hjb; lia]).
    assert (Hin_f : In (f, f + 50) (reac_ctrl_parse_D f n o))
      by (unfold reac_ctrl_parse_D; apply in_or_app; left;
          rewrite (proj2 (Z.ltb_ge n 50) Hn50); left; reflexivity).
    pose proof (dj_pair f (f + 50) (fs_hint FS 1) (fs_hint FS 1 + 8) Hin_f
                  (proj1 (fp_wx_hint_flag_in FS X))) as Hfh.
    pose proof (dj_pair f (f + 50) (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1) Hin_f
                  (proj2 (fp_wx_hint_flag_in FS X))) as Hff.
    assert (Happ : f + 50 <= 2147450880 \/ 17594333495296 <= f)
      by (apply (app_range f 50); [lia | intros i Hi; exact (acl_app_in m f 50 i AFm Hi)]).
    assert (Hfr : f + 50 <= fra \/ fra + 128 <= f).
    { destruct HK as [(_ & Efra & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)].
      - destruct HfS as [Hc|Hc]; [left | right]; clear -Hc Efra HAlo HAhi RS; lia.
      - destruct (D_apart_frame f (f + 50) j Hin_f ltac:(clear; lia) Hj Hfl0) as [Hc|Hc];
          rewrite <- Efra in Hc; [left | right]; clear -Hc; lia. }
    split; [exact Hf0|]. split; [exact Hf64|]. split; [exact Happ|]. split; [exact AFm|].
    unfold Wall, Wf. cbn [disjoint_from app fst snd].
    split; [clear -HfS; destruct HfS; lia|].
    split; [clear -Hfh; unfold fs_hint in *; cbn [Z.of_nat] in *; lia|].
    split; [rewrite EFLj; rewrite EFL0, EM1 in Hff; clear -Hff Hjb; lia|].
    split; [clear -Hfr; lia|].
    split; [unfold shadow_addr; clear -Happ SH1 SH2; lia|].
    split; [pose proof (Obf Hn50) as Hc; clear -Hc; lia | exact I].
  Qed.

  (* The runtime's cells and the shadow survive the body's writes (the box and the callee windows). *)
  Lemma body_rt : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> addressable mc ob 36 ->
    asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> wmono rsegs mc mx ->
    asan_cells mx /\ shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mx.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO Aob ACc SRc MUb WMb.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    split.
    - apply (fl_asan_cells _ mc mx ACc MUb).
      intros x Hx. cbn [outside]. split; [|split; [|exact I]].
      + clear -Hx Obrt; unfold RT_LO, RT_HI in *; lia.
      + pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; clear -Hx HH0; unfold RT_LO, RT_HI in *; lia.
    - apply (lib.A.ShadowRwOnK.fl_shadow_rw_on _ _ mc mx SRc MUb WMb).
      intros x Hx. cbn [outside]. split; [|split; [|exact I]].
      + intros [HL HR]. apply (acl_app_not_shadow x); [| exact Hx].
        pose proof (acl_app_in mc ob 36 (x - ob) Aob ltac:(lia)) as Ha.
        replace (ob + (x - ob)) with x in Ha by lia. exact Ha.
      + intros [HL HR]. apply (acl_app_not_shadow x); [| exact Hx].
        pose proof (acl_app_in m (S - 8800) 8800 (x - (S - 8800)) AW0 ltac:(clear -HL HR Hspc; lia)) as Ha.
        replace (S - 8800 + (x - (S - 8800))) with x in Ha by lia. exact Ha.
  Qed.

  (* A byte of the class-1 flag array other than flag j is apart from everything the frame block writes. *)
  Lemma flag_out_Wf : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    FS + 20480 <= x < FS + 28672 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + nn) ->
    outside (Wf fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx Hnotj.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & _ & _ & FSp4 & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    assert (Hxapp : app_mem x) by (apply FSp4; clear -Hx HFSb; unfold FS_SIZE; lia).
    assert (Efra0 : 0 <= fra) by (clear -FRlo FSp1; lia).
    assert (Efra128 : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    unfold Wf. cbn [outside].
    split; [clear -Hx HFSb; lia|].
    split; [unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; clear -Hx; lia|].
    split; [exact Hnotj|].
    split; [clear -Hx FRlo; lia|].
    split; [|exact I].
    pose proof (sh_add8 fra 16 FR8) as Esh. replace (fra + 8 * 16) with (fra + 128) in Esh by lia.
    rewrite <- Esh. exact (acl_sh_out x fra (fra + 128) Hxapp Efra0 Efra128).
  Qed.

  (* Every exit of the body reaches 0x83920 in a memory mx that the body produced from mc writing only the box
     and the callee windows, with a0 = the parse's kind and the box holding the parse's bytes: L_exit's
     premises, assembled once. *)
  Lemma L_join : forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> wmono rsegs mc mx ->
    mem_inv rsegs mx -> stk rsegs mx (S - 8800) S ->
    rw_cells rsegs mx ob [CB 36 (snd (ctrlparse n fr))] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mx (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc ob mx x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HK HB HFL HO MUb WMb MIx STx RWx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct HB as (MU & WM & RM & MI & SV).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    (* the box bytes and the window are readable at mx, so every byte readable at mc still is *)
    assert (RMb : rd_mono mc mx).
    { pose proof RWx as RWbk. destruct RWbk as [[_ Hbx] _]. cbn [cells_bytes cbytes] in Hbx.
      rewrite app_nil_r in Hbx.
      apply (rd_mono_list _ mc mx MUb). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbx). rewrite ctrlparse_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STx). clear -Hy Hspcr RS; lia. }
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (MUx : munch (Wex fra) m mx).
    { eapply munch_trans;
        [ eapply munch_weaken; [exact (subWf_Wex fra fv spc j nn w120 HK) | exact MU]
        | eapply munch_weaken; [exact (ob_wex fra fv spc j nn w120 ob HK HO) | exact MUb] ]. }
    assert (WMx : wmono rsegs m mx) by (eapply wmono_trans; [exact WM | exact WMb]).
    assert (RMx : rd_mono m mx) by (eapply rd_mono_trans; [exact RM | exact RMb]).
    assert (STfs : stk rsegs mx FS (FS + FS_SIZE)) by (exact (stk_mono m mx _ _ Pfsstk WMx RMx)).
    eapply L_exit.
    - exact HK.
    - exact MUx.
    - exact WMx.
    - exact RMx.
    - exact MIx.
    - exact (fl_asan_cells (Wex fra) m mx AC0 MUx
               (fun x Hx => aout_rt (Wex fra) x (Wex_subW fra fv spc j nn w120 HK) Hx)).
    - exact (shadow_rw_mono_on _ m mx SR0 WMx RMx).
    - exact STx.
    - apply (rw_cells_transport rsegs _ mc mx (S - 96) SAVES SV MUb WMb).
      cbn [disjoint_from cells_size csize SAVES fst snd].
      split; [clear -Obsv RS; lia|]. split; [right; clear -Hspcr; lia | exact I].
    - intros Ho. destruct HO as [(Eo & _) | (_ & Eob)]; [exfalso; exact (Ho Eo) | rewrite <- Eob; exact RWx].
    - destruct (rd8_le8 mx (fs_hint FS 1)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0; lia)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0 HFSb RS; lia)
                 ltac:(intros i Hi; apply (rd_of_stk _ _ _ STfs);
                       unfold fs_hint, FS_SIZE; cbn [Z.of_nat]; clear -Hi Pfs0; lia)) as [hh Hhint].
      exists hh. exact Hhint.
    - destruct HFL as [(flg & Hfl & Hfln & HflF) _].
      exists flg. split; [|split; [exact Hfln | exact HflF]].
      eapply fl_bytes; [exact Hfl | exact MUb |].
      intros x Hx. rewrite Hfln, EM1, EFL0 in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + clear -Hx Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
      + clear -Hx HFSb Pfs0 Hspcr RS; lia.
    - intros Enn. destruct HFL as [_ Hw]. pose proof (Hw Enn) as Hw120.
      assert (Hfrside : fra + 128 <= S - 8800).
      { destruct HK as [(_ & _ & _ & _ & Enn0) | (Hj & Efra & _)]; [clear -Enn Enn0; lia|].
        rewrite EM1 in Hj. rewrite Efra. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. clear -Hj HFSb Pfs0; lia. }
      eapply fl_bytes; [exact Hw120 | exact MUb |].
      intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + destruct Obfr as [Eob | Hout]; [clear -Hx Eob; lia | clear -Hx Hout; lia].
      + clear -Hx Hfrside Hspcr RS; lia.
    - (* the class-1 flag array: the frame block wrote only flag j there, the body none of it *)
      intros x Hx Hnj.
      assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
      assert (Hbd : 0 <= x < 2 ^ 64) by (clear -Hxr Pfs0 HFSb RS; lia).
      rewrite (munch_mrd_out _ mc mx x MUb Hbd).
      + exact (munch_mrd_out _ m mc x MU Hbd (flag_out_Wf fra fv spc j nn w120 x HK Hxr Hnj)).
      + cbn [outside]. split; [|split; [|exact I]].
        * clear -Hxr Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
        * clear -Hxr HFSb Pfs0 Hspcr RS; lia.
  Qed.

  (* ================= the body (0x836a8 .. exits) ================= *)

  (* What the body carries from the box's creation (mc) to the current memory. *)
  Definition BJ (ob spc : Z) (mc mx : word -> option byte) : Prop :=
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx /\ wmono rsegs mc mx /\ mem_inv rsegs mx /\
    stk rsegs mx (S - 8800) S.

  (* A window whose upper part the callee only rewrote where the caller can still read stays a stack window. *)
  Lemma stk_join_call : forall (m1 m2 : word -> option byte) lo mid hi W,
    stk rsegs m1 lo hi -> stk rsegs m2 lo mid -> munch W m1 m2 -> wmono rsegs m1 m2 ->
    (forall x, mid <= x < hi -> outside W x \/ exists b, mrd rsegs m2 (wa x) = Some b) -> lo <= mid <= hi ->
    stk rsegs m2 lo hi.
  Proof.
    intros m1 m2 lo mid hi W (L1 & L2 & H1) (_ & _ & H2) MU WM HO Hm.
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Z_lt_le_dec a mid) as [Hlt|Hge]; [apply H2; lia|].
    destruct (H1 a ltac:(lia)) as (Hv & b & Hb). split; [apply WM; exact Hv|].
    destruct (HO a ltac:(lia)) as [Hout|Hrdx]; [| exact Hrdx].
    exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
    rewrite wa_unsigned by lia. exact Hout.
  Qed.

  (* The body's carried state after a callee that wrote only inside the box and its own stack window. *)
  Lemma bj_call : forall ob spc mc (m1 m2 : word -> option byte) (D N K : Z) bs,
    BJ ob spc mc m1 -> munch [(D, D + N); (spc - K, spc)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
    stk rsegs m2 (S - 8800) spc -> rw_cells rsegs m2 D [CB (Z.to_nat N) bs] -> 0 <= N -> 0 <= K ->
    ob <= D -> D + N <= ob + 36 -> S - 8800 <= spc - K -> spc <= S ->
    BJ ob spc mc m2.
  Proof.
    intros ob spc mc m1 m2 D N K bs (MUb & WMb & MIx & STx) MU2 WM2 MI2 ST2 RW2 HN HK0 H1 H2 H3 H4.
    pose proof RW2 as RW2'. destruct RW2' as [[Hwf Hbt] _]. cbn [cells_wf cell_wf] in Hwf.
    destruct Hwf as [Hlen _]. cbn [cells_bytes cbytes] in Hbt. rewrite app_nil_r in Hbt.
    split; [| split; [| split]].
    - eapply munch_trans; [exact MUb |]. eapply munch_weaken; [| exact MU2].
      intros x Hx. cbn [outside] in *. destruct Hx as (Hb & Hw & _).
      split; [clear -Hb H1 H2; lia | split; [clear -Hw H3 H4; lia | exact I]].
    - eapply wmono_trans; [exact WMb | exact WM2].
    - exact MI2.
    - eapply (stk_join_call m1 m2 (S - 8800) spc S [(D, D + N); (spc - K, spc)] STx ST2 MU2 WM2);
        [ intros x Hx;
          destruct (Z_lt_le_dec x D) as [Hlt|Hge];
          [ left; cbn [outside]; split; [clear -Hlt; lia | split; [clear -Hx; lia | exact I]]
          | destruct (Z_lt_le_dec x (D + N)) as [Hin|Hout];
            [ right; apply (rd_of_bytes _ _ _ Hbt); rewrite Hlen, Z2Nat.id by exact HN; clear -Hge Hin; lia
            | left; cbn [outside]; split; [clear -Hout; lia | split; [clear -Hx; lia | exact I]] ] ]
        | split; [clear -H3 HK0; lia | exact H4] ].
  Qed.

  (* The same, for a callee that wrote only its own stack window. *)
  Lemma bj_call0 : forall ob spc mc (m1 m2 : word -> option byte) (K : Z),
    BJ ob spc mc m1 -> munch [(spc - K, spc)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
    stk rsegs m2 (S - 8800) spc -> 0 <= K -> S - 8800 <= spc - K -> spc <= S ->
    BJ ob spc mc m2.
  Proof.
    intros ob spc mc m1 m2 K (MUb & WMb & MIx & STx) MU2 WM2 MI2 ST2 HK0 H3 H4.
    split; [| split; [| split]].
    - eapply munch_trans; [exact MUb |]. eapply munch_weaken; [| exact MU2].
      intros x Hx. cbn [outside] in *. destruct Hx as (Hb & Hw & _).
      split; [clear -Hw H3 H4; lia | exact I].
    - eapply wmono_trans; [exact WMb | exact WM2].
    - exact MI2.
    - eapply (stk_join_call m1 m2 (S - 8800) spc S [(spc - K, spc)] STx ST2 MU2 WM2);
        [ intros x Hx; left; cbn [outside]; split; [clear -Hx; lia | exact I]
        | split; [clear -H3 HK0; lia | exact H4] ].
  Qed.

  (* The box stays addressable: the body writes no shadow byte. *)
  Lemma ob_mx : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    addressable mc ob 36 -> addressable mx ob 36.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MUb Aob.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (Hspc : spc <= S)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    apply (acl_addr_munch [(ob, ob + 36); (S - 8800, spc)] mc mx ob 36 Aob MUb).
    intros i Hi.
    pose proof (acl_app_in mc ob 36 i Aob Hi) as Hoi.
    pose proof (rt_app_shadow (ob + i) Hoi) as Hsh.
    cbn [outside]. split; [| split; [| exact I]].
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (ob + i))); [| exact Hsh].
      pose proof (acl_app_in mc ob 36 (shadow_addr (ob + i) - ob) Aob ltac:(clear -HL HR; lia)) as Ha.
      replace (ob + (shadow_addr (ob + i) - ob)) with (shadow_addr (ob + i)) in Ha by lia. exact Ha.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (ob + i))); [| exact Hsh].
      pose proof (acl_app_in m (S - 8800) 8800 (shadow_addr (ob + i) - (S - 8800)) AW0
                    ltac:(clear -HL HR Hspc; lia)) as Ha.
      replace (S - 8800 + (shadow_addr (ob + i) - (S - 8800))) with (shadow_addr (ob + i)) in Ha by lia.
      exact Ha.
  Qed.

  (* The 50 bytes at f stay addressable through the body's writes. *)
  Lemma af_mx : 50 <= n -> forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> addressable mc ob 36 ->
    munch (Wall fra j nn ob) m mx -> addressable mx f 50.
  Proof.
    intros Hn50 fra fv spc j nn w120 ob mc mx HK HO Aob MUall.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof DFf as DFf'. unfold Wall, Wf in DFf'. cbn [disjoint_from app fst snd] in DFf'.
    destruct DFf' as (Dwin & Dhint & Dflag & Dfr & Dsh & Dbox & _).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    apply (acl_addr_munch (Wall fra j nn ob) m mx f 50 AFm MUall).
    intros i Hi.
    pose proof (acl_app_in m f 50 i AFm Hi) as Hfi.
    pose proof (rt_app_shadow (f + i) Hfi) as Hsh.
    unfold Wall, Wf. cbn [outside app].
    split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      pose proof (acl_app_in m (S - 8800) 8800 (shadow_addr (f + i) - (S - 8800)) AW0
                    ltac:(clear -HL HR; lia)) as Ha.
      replace (S - 8800 + (shadow_addr (f + i) - (S - 8800))) with (shadow_addr (f + i)) in Ha by lia.
      exact Ha.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_hint in HL, HR. cbn [Z.of_nat] in HL, HR. unfold FS_SIZE.
      clear -HL HR Pfs0; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_flag in HL, HR. cbn [Z.of_nat Pos.of_succ_nat] in HL, HR.
      change (2 ^ 15) with 32768 in HL, HR. change (2 ^ (15 - 1)) with 16384 in HL, HR.
      unfold FS_SIZE. clear -HL HR Pfs0 Hjnn; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      replace (shadow_addr (f + i)) with (fra + (shadow_addr (f + i) - fra)) by lia.
      apply FAP; clear -HL HR; lia.
    - intros HC. rewrite E16 in HC.
      exact (acl_win_sh (f + i) fra (fra + 128) FR8 ltac:(clear -Hi Dfr; lia) HC).
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (f + i))); [|exact Hsh].
      pose proof (acl_app_in mc ob 36 (shadow_addr (f + i) - ob) Aob ltac:(clear -HL HR; lia)) as Ha.
      replace (ob + (shadow_addr (f + i) - ob)) with (shadow_addr (f + i)) in Ha by lia. exact Ha.
  Qed.

  (* The same facts, stated from the two munches the body actually carries (no Wall hypothesis is kept in the
     context: the store tactics must see only concrete footprints). *)
  Lemma af_mx2 : 50 <= n -> forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wf fra j nn) m mc -> addressable mc ob 36 ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> addressable mx f 50.
  Proof.
    intros Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb.
    exact (af_mx Hn50 fra fv spc j nn w120 ob mc mx HK HO Aob (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
  Qed.

  (* The frame bytes [lo, lo + len), read back in the memory the body reached. *)
  Lemma ro_mx : 50 <= n -> forall fra fv spc j nn w120 ob mc (mx : word -> option byte) (lo len : nat),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wf fra j nn) m mc -> addressable mc ob 36 ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    (forall jx, (jx < len)%nat -> In (lo + jx)%nat (cp_rd n fr)) -> (lo + len <= 50)%nat ->
    ro_cells rsegs mx (f + Z.of_nat lo) (map C1 (map (cp_b fr) (seq lo len))).
  Proof.
    intros Hn50 fra fv spc j nn w120 ob mc mx lo len HK HO MU Aob MUb HIN Hlen.
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    apply (rc_ro_now rsegs (Wall fra j nn ob) m mx f fr lo len (cp_rd n fr) Hrd HIN
             ltac:(rewrite Lfr; lia) ltac:(lia) ltac:(rewrite Lfr; cbn [Z.of_nat]; lia)
             (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
    eapply disjoint_from_sub;
      [ exact DFf | cbn [Z.of_nat Pos.of_succ_nat]; lia | cbn [Z.of_nat Pos.of_succ_nat]; lia ].
  Qed.

  (* The frame bytes [lo, lo + len), read back in the memory the run reached. *)
  Ltac rdb lo len tac :=
    let HIN := fresh "HIN" in
    assert (HIN : forall jx, (jx < len)%nat -> In (lo + jx)%nat (cp_rd n fr)) by tac;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let R := fresh "RO" in
        assert (R : ro_cells rsegs mcur (f + Z.of_nat lo) (map C1 (map (cp_b fr) (seq lo len))))
          by (eapply ro_mx;
              [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact HIN | cbn [Nat.add]; lia ]);
        cbn [map seq] in R;
        let z := eval vm_compute in (Z.of_nat lo) in change (Z.of_nat lo) with z in R;
        rewrite ?Z.add_0_r in R
    end;
    clear HIN.

  (* `mv r,s10; beqz s4; mv r,s4` at a join: r holds the box pointer on both paths, continuing at tgt. *)
  Ltac obsel r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the addressable ranges at the memory the run reached *)
  Ltac refresh :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let A1 := fresh "AFx" in
        assert (A1 : addressable mcur f 50) by (eapply af_mx2; eassumption);
        match goal with
        | HOb : OB _ ?obq |- _ =>
            let A2 := fresh "Aobx" in
            assert (A2 : addressable mcur obq 36) by (eapply ob_mx; eassumption)
        end
    end.

  (* the shadow check of the one-byte load of frame byte i *)
  Ltac chkf i r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let RX := fresh "RX" in let SH := fresh "SH" in
        assert (RX : 0 <= f + i < 2 ^ 64)
          by (match goal with Hb : 0 <= f /\ f + 50 <= 2 ^ 64 |- _ => clear -Hb; lia end);
        pose proof (acl_shadow mcur f 50 i 1 (f + i) ltac:(eassumption) ltac:(clear; lia) ltac:(clear; lia)
                      ltac:(clear; lia)
                      ltac:(let MB := fresh "MB" in
                            pose proof (Z.mod_pos_bound (f + i) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                      ltac:(clear; lia)) as SH;
        chk_core (f + i) RX r SH pre_sr no_extra
    end.

  (* the shadow check of the four-byte access at the box pointer itself (offset 0: the address register holds ob,
     with no added literal) *)
  Ltac chkb0 r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ =>
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            chk_core obq RX r SH pre_sr extra
        end
    end.

  (* the same check where the fast path is the TAKEN branch (`beqz` instead of `bnez`, at 0x83a90) *)
  Ltac chkb0inv r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ =>
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            let kk := fresh "kk" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
            destruct SH as (kk & RK & OK & KR);
            pre_sr obq RX; steps_until_if; clear RK;
            unfold sxb; rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR; lia);
            lazymatch goal with
            | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm (if _ then ?B1 else _) ?fcc ?rv ?mm ?ro) =>
                let G := fresh "G" in
                enough (G : forall rr : word, evtF segs rgq Q (MS (bvmap_set r rr R) Fm B1 fcc rv mm ro));
                [ destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbv iota;
                  [ bjoin G r
                  | step; rewrite ?(unsigned_lit obq) by (clear -RX; lia); rewrite rc_land7; add3 obq;
                    step;
                    let MB := fresh "MB" in pose proof (Z.mod_pos_bound obq 8 eq_refl) as MB;
                    rewrite (rc_lts_signed (obq mod 8 + 3) (bv_signed kk)) by (clear -MB KR; lia);
                    replace (obq mod 8 + 3 <? bv_signed kk) with true
                      by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK];
                          [exfalso; exact (K0 OK) | clear -OK; lia]);
                    clear MB; cbv iota; bjoin G r ]
                | intros ?; simp_regs; clear OK KR ]
            end
        end
    end.

  (* `beqz s4; mv r,s4` (0x83c38): r holds the box pointer on both paths *)
  Ltac obsel2 r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the shadow check of a w-byte access at ob + k *)
  Ltac chkb k w r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ =>
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq + k < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 k w (obq + k) AO ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear; lia)
                          ltac:(apply (acl_mod_al obq k w); [eassumption | clear; lia | clear; lia])
                          ltac:(clear; lia)) as SH;
            chk_core (obq + k) RX r SH pre_sr extra
        end
    end.

  (* The six bytes at .str.4 that the bcmp wrapper compares with stay addressable. *)
  Lemma abc_mx : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> addressable mc ob 36 ->
    munch (Wall fra j nn ob) m mx -> addressable mx REAC_CTRL_PARSE_BC 6.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO Aob MUall.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    apply (acl_addr_munch (Wall fra j nn ob) m mx REAC_CTRL_PARSE_BC 6 ABC MUall).
    intros i Hi.
    pose proof (acl_app_in m REAC_CTRL_PARSE_BC 6 i ABC Hi) as Hbi.
    pose proof (rt_app_shadow (REAC_CTRL_PARSE_BC + i) Hbi) as Hsh.
    unfold Wall, Wf. cbn [outside app].
    split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      pose proof (acl_app_in m (S - 8800) 8800 (shadow_addr (REAC_CTRL_PARSE_BC + i) - (S - 8800)) AW0
                    ltac:(clear -HL HR; lia)) as Ha.
      replace (S - 8800 + (shadow_addr (REAC_CTRL_PARSE_BC + i) - (S - 8800)))
        with (shadow_addr (REAC_CTRL_PARSE_BC + i)) in Ha by lia.
      exact Ha.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_hint in HL, HR. cbn [Z.of_nat] in HL, HR. unfold FS_SIZE.
      clear -HL HR Pfs0; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      apply Pfsapp. unfold fs_flag in HL, HR. cbn [Z.of_nat Pos.of_succ_nat] in HL, HR.
      change (2 ^ 15) with 32768 in HL, HR. change (2 ^ (15 - 1)) with 16384 in HL, HR.
      unfold FS_SIZE. clear -HL HR Pfs0 Hjnn; lia.
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      replace (shadow_addr (REAC_CTRL_PARSE_BC + i)) with (fra + (shadow_addr (REAC_CTRL_PARSE_BC + i) - fra))
        by lia.
      apply FAP; clear -HL HR; lia.
    - intros HC. rewrite E16 in HC.
      exact (acl_win_sh (REAC_CTRL_PARSE_BC + i) fra (fra + 128) FR8
               ltac:(unfold REAC_CTRL_PARSE_BC; clear -Hi FRlo Pfs0 Pfs2; lia) HC).
    - intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (REAC_CTRL_PARSE_BC + i))); [|exact Hsh].
      pose proof (acl_app_in mc ob 36 (shadow_addr (REAC_CTRL_PARSE_BC + i) - ob) Aob
                    ltac:(clear -HL HR; lia)) as Ha.
      replace (ob + (shadow_addr (REAC_CTRL_PARSE_BC + i) - ob))
        with (shadow_addr (REAC_CTRL_PARSE_BC + i)) in Ha by lia.
      exact Ha.
  Qed.

  (* The cells the bcmp wrapper reads lie below the side stack and apart from the box. *)
  Lemma cl_mx : forall fra fv spc j nn w120 ob (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wall fra j nn ob) m mx -> aCL mx.
  Proof.
    intros fra fv spc j nn w120 ob mx HK HO MUall.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof HHM as HHM0. unfold HIGHMEM_BEG in HHM0.
    assert (DJ : forall a len, 0 <= a -> a + len <= CF + 256 -> GOT_CF <= a -> 0 <= len ->
                 disjoint_from (Wall fra j nn ob) a len).
    { intros a len Ha0 Hae Hag Hl. unfold Wall, Wf. cbn [disjoint_from app fst snd].
      split; [unfold GOT_CF, CF in *; clear -Hae Hag HHM0; lia|].
      split; [unfold fs_hint, GOT_CF, CF in *; cbn [Z.of_nat];
              clear -Hae Hag Pfs2 Pfs0; lia|].
      split; [unfold fs_flag, GOT_CF, CF in *; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384;
              clear -Hae Hag Pfs2 Pfs0 Hjnn; lia|].
      split; [unfold GOT_CF, CF in *; clear -Hae Hag FRlo Pfs2 Pfs0; lia|].
      split; [unfold shadow_addr, ASAN_K, GOT_CF, CF in *; clear -Hae Hag Ha0 FRlo Pfs0; lia|].
      split; [unfold GOT_CF, CF in *; clear -Hae Hag Obcf; lia | exact I]. }
    split; [| split; [| split; [| split]]].
    - apply (bytes_at_transport rsegs _ m mx REAL_BCMP _ HBCMP MUall).
      apply DJ; unfold REAL_BCMP, GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx REAL_MEMCMP _ HMEMCMP MUall).
      apply DJ; unfold REAL_MEMCMP, GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx GOT_CF _ HGCF MUall).
      apply DJ; unfold GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx (CF + 254) _ HCF254 MUall).
      apply DJ; unfold GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
    - apply (bytes_at_transport rsegs _ m mx (CF + 255) _ HCF255 MUall).
      apply DJ; unfold GOT_CF, CF; rewrite ?length_le8; cbn [Z.of_nat length]; lia.
  Qed.

  Lemma abc_mx2 : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob -> munch (Wf fra j nn) m mc -> addressable mc ob 36 ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx ->
    addressable mx REAC_CTRL_PARSE_BC 6.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb.
    exact (abc_mx fra fv spc j nn w120 ob mc mx HK HO Aob (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
  Qed.

  Lemma cl_mx2 : forall fra fv spc j nn w120 ob mc (mx : word -> option byte),
    FK fra fv spc j nn w120 -> OB fra ob ->
    munch (Wf fra j nn) m mc -> munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> aCL mx.
  Proof.
    intros fra fv spc j nn w120 ob mc mx HK HO MU MUb.
    exact (cl_mx fra fv spc j nn w120 ob mx HK HO (mu_all fra fv spc j nn w120 ob mc mx HK HO MU MUb)).
  Qed.

  (* The 24 bytes the body writes at ob + 4 (P1 of lib/Prog/reac_ctrl_parse.v). *)
  Definition P1 : list byte :=
    [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11;
     cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5;
     (if cp_bcast fr then Z_to_bv 8 1 else cp_z); cp_z; cp_z; cp_z;
     cp_b fr 14; cp_b fr 15; cp_b fr 18; cp_b fr 19; cp_b fr 21; cp_b fr 20; cp_b fr 22; cp_z].

  (* 0x83ac8: the kind is stored into the box (its shadow check was done before the jump), then the exit. *)
  Lemma L_kind : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ac8) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG RINF SCF SKF RBC SKBC RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    destruct HBJ as (MUb & WMb & MIx & STx).
    step. step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HKc' end.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca8: the stored kind is checked, read back, and the run exits. *)
  Lemma L_be0 : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [C4 (Z_to_bv 64 k)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca8) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG RINF SCF SKF RBC SKBC RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22
      x26 x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc' HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    destruct HBJ as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (Aobx : addressable mcur ob 36) by (eapply ob_mx; eassumption)
    end.
    chkb0 (Z_to_bv 5 11) add3.
    step. rewrite (rcp_sx32 k) by (clear -Hk; lia).
    step.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca4: the kind is stored into the box, checked, read back, then the exit. *)
  Lemma L_bdc : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca4) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR. clear SMAL HMSET HMCPY HBCMPW HKOL MI0 Hrd AF0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 RBY RIMG RINF SCF SKF RBC SKBC RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HK4 end.
    eapply (L_be0 fra fv spc j nn w120 mc ob _ k tg amp);
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj _ (conj _ (conj _ _))); eassumption
      | exact Aob | exact HK4 | eassumption | eassumption | eassumption
      | exact Ek | exact Hk | exact EB ].
  Qed.

  (* the plain proof's condition normaliser and branch splitter (lib/Prog/reac_ctrl_parse.v) *)
  Ltac cond_norm :=
    rewrite ?rc_lor0;
    rewrite ?rc_eqb_zxb by (clear; lia);
    repeat match goal with
    | |- context [bv_unsigned (cp_b fr ?i)] => change (bv_unsigned (cp_b fr i)) with (cp_v fr i)
    end.

  Ltac br :=
    cond_norm;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if negb (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    | |- evtF _ _ _ (MS _ _ (if (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    end.

  (* walk the kind dispatch, stopping at every leaf (each leaf checks the box before it stores the kind) *)
  Ltac drive :=
    repeat (lazymatch goal with
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539276) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539368) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => fail
            | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
            end).

  (* the kind and the box bytes of a leaf (kfact / bfact of the plain proof) *)
  Ltac kfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [fst];
    unfold cp_kind, cp_type, cp_amp; zeval; reflexivity.
  Ltac bfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [snd];
    unfold cp_struct, cp_rec, cp_kind, cp_type, cp_amp, P1; zeval; zeval; reflexivity.

  Ltac leafk :=
    eapply L_kind;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].
  Ltac leafb :=
    eapply L_bdc;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].

  (* after the two tag bytes are stored, the box's [ob + 28] cell is a C2: flatten it back to the two
     bytes cp_struct names, so that a leaf below the record can still apply L_kind / L_bdc *)
  Ltac flat_tg :=
    match goal with
    | HOb : OB _ ?obq |- _ =>
        match goal with
        | Hq : rw_cells rsegs _ (obq + 28) [C2 _] |- _ =>
            apply (rc_rw_flat rsegs _ (obq + 28) _ [cp_b fr 35; cp_b fr 34]) in Hq;
            [ cbn [length] in Hq
            | first [ cbn [cells_bytes cbytes]; rewrite rc_le2_pack; reflexivity
                    | cbn [cells_bytes cbytes app]; rewrite rc_le2_pack; reflexivity
                    | vm_compute; reflexivity ] ]
        end
    end.

  Ltac leaves :=
    lazymatch goal with
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafk
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ Qp (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafb
    end.

  (* 0x8370c .. 0x8375c: the two copies into the box, the broadcast comparison and its 4-byte store. *)
  Lemma body_copy : 50 <= n -> cp_hdr n fr = true ->
    forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG Qp
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 ob) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8370c) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL HMSET MI0 RFSS RFW1 RTLS. pf_hide.
    intros Hn50 HE fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pf_h SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    destruct (HF Hn50) as (_ & _ & HfS).
    pose proof (Obf Hn50) as Hobf.
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (Rob10 : 0 <= ob + 10 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rob4 : 0 <= ob + 4 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rf6 : 0 <= f + 6 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    assert (STsp : stk rsegs mx (S - 8800) spc)
      by (apply (stk_sub mx (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    destruct (body_rt fra fv spc j nn w120 ob mc mx HK HO Aob ACc SRc MUb WMb) as (ACx & SRx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc mx HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0.
    cbn [map seq firstn skipn] in BD0. rewrite Z.add_0_r in BD0.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 6 6 RO ltac:(cbn; lia)) as BD1.
    cbn [map seq firstn skipn] in BD1. change (Z.of_nat 6) with 6 in BD1.
    clear RO.
    (* the pieces of the box the body writes *)
    destruct (rc_rw_cut_at rsegs _ ob cp_z 36 4 (ob + 4) RWx ltac:(lia) ltac:(lia)) as [HKc HZ1];
      cbn [Nat.sub] in HZ1.
    destruct (rc_rw_cut_at rsegs _ (ob + 4) cp_z 32 6 (ob + 10) HZ1 ltac:(lia) ltac:(lia)) as [HSRC HZ2];
      cbn [Nat.sub] in HZ2.
    destruct (rc_rw_cut_at rsegs _ (ob + 10) cp_z 26 6 (ob + 16) HZ2 ltac:(lia) ltac:(lia)) as [HDST HZ3];
      cbn [Nat.sub] in HZ3.
    destruct (rc_rw_cut_at rsegs _ (ob + 16) cp_z 20 12 (ob + 28) HZ3 ltac:(lia) ltac:(lia)) as [HMID HZ4];
      cbn [Nat.sub] in HZ4.
    destruct (rc_rw_cut_at rsegs _ (ob + 28) cp_z 8 2 (ob + 30) HZ4 ltac:(lia) ltac:(lia)) as [HTG HAMP];
      cbn [Nat.sub] in HAMP.
    clear HZ1 HZ2 HZ3 HZ4 RWx.
    pose proof HMCPY as HMC. unfold asan_memcpy_contract_F_on, ASAN_MEMCPY_K in HMC. cbv zeta in HMC.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMC.
    (* 0x8370c: __asan_memcpy(ob + 10, f, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 10) Rob10), ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD0.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HDST.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub mx f 50 f 6 AFx); clear; lia.
      - apply (acl_addr_sub mx ob 36 (ob + 10) 6 Aobx); clear; lia.
      - right. apply (acl_app_in mx f 50 6 AFx); clear; lia.
      - right. replace (ob + 10 + 6) with (ob + 16) by lia. apply (acl_app_in mx ob 36 16 Aobx); clear; lia.
      - right. split; [ apply (acl_app_in mx f 50 7 AFx); clear; lia
                      | replace (ob + 10 + 7) with (ob + 17) by lia;
                        apply (acl_app_in mx ob 36 17 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACx.
      - apply (srw_memcpy fra fv spc j nn w120 ob mx _ _ _ 10 0 HK HO Hn50);
          [ rewrite ?(unsigned_lit (ob + 10) Rob10), ?(unsigned_lit f Rf), ?U6; lia .. | exact SRx ].
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 &
                       Hms & MU1 & WM1 & MI1 & ST1 & RW1 & BS1 & AC1 & SR1).
    subst ms'.
    pose proof (SR1 _ SRx) as SR1p.
    rewrite (ret_pc_even 538396 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob10), U6, (unsigned_lit spc Rspc) in MU1.
    rewrite (unsigned_lit _ Rob10), U6 in RW1.
    rewrite (unsigned_lit _ Rf) in BS1.
    rewrite (unsigned_lit spc Rspc) in ST1.
    unfold ASAN_MEMCPY_K in MU1. change (Z.to_nat 6) with 6%nat in RW1.
    pose proof (bj_call ob spc mc mx m1 (ob + 10) 6 2224 _ HBJ MU1 WM1 MI1 ST1 RW1
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ1.
    pose proof (rw_cells_transport rsegs _ mx m1 ob [CB 4 (repeat cp_z 4)] HKc MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 4) [CB 6 (repeat cp_z 6)] HSRC MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HSRC1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 16) [CB 12 (repeat cp_z 12)] HMID MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 28) [CB 2 (repeat cp_z 2)] HTG MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP1.
    pose proof (bytes_at_transport rsegs _ mx m1 (f + 6) [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                          cp_b fr 10; cp_b fr 11] BD1 MU1
                  ltac:(cbn [disjoint_from length]; clear -Hobf Hf0 Hf64 HfS Hspcr RS; lia)) as BD1a.
    clear HKc HSRC HMID HTG HAMP BD0 BD1 MU1 WM1 MI1 ST1 HBJ MUb WMb MIx STx STsp ACx SRx Aobx AFx.
    pose proof HBJ1 as HBJ1'. destruct HBJ1' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m1 (S - 8800) spc)
      by (apply (stk_sub m1 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m1 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m1 HK HO MU Aob MUb) as AFx.
    (* 0x8371c: __asan_memcpy(ob + 4, f + 6, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 4) Rob4), ?(unsigned_lit (f + 6) Rf6), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD1a.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HSRC1.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub m1 f 50 (f + 6) 6 AFx); clear; lia.
      - apply (acl_addr_sub m1 ob 36 (ob + 4) 6 Aobx); clear; lia.
      - right. replace (f + 6 + 6) with (f + 12) by lia. apply (acl_app_in m1 f 50 12 AFx); clear; lia.
      - right. replace (ob + 4 + 6) with (ob + 10) by lia. apply (acl_app_in m1 ob 36 10 Aobx); clear; lia.
      - right. split; [ replace (f + 6 + 7) with (f + 13) by lia; apply (acl_app_in m1 f 50 13 AFx); clear; lia
                      | replace (ob + 4 + 7) with (ob + 11) by lia;
                        apply (acl_app_in m1 ob 36 11 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC1.
      - apply (srw_memcpy fra fv spc j nn w120 ob m1 _ _ _ 4 6 HK HO Hn50);
          [ rewrite ?(unsigned_lit (ob + 4) Rob4), ?(unsigned_lit (f + 6) Rf6), ?U6; lia .. | exact SR1p ].
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 &
                       Hms & MU2 & WM2 & MI2 & ST2 & RW2 & BS2 & AC2 & SR2).
    subst ms'.
    pose proof (SR2 _ SR1p) as SR2p.
    rewrite (ret_pc_even 538412 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob4), U6, (unsigned_lit spc Rspc) in MU2.
    rewrite (unsigned_lit _ Rob4), U6 in RW2.
    rewrite (unsigned_lit _ Rf6) in BS2.
    rewrite (unsigned_lit spc Rspc) in ST2.
    unfold ASAN_MEMCPY_K in MU2. change (Z.to_nat 6) with 6%nat in RW2.
    pose proof (bj_call ob spc mc m1 m2 (ob + 4) 6 2224 _ HBJ1 MU2 WM2 MI2 ST2 RW2
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ2.
    pose proof (rw_cells_transport rsegs _ m1 m2 ob [CB 4 (repeat cp_z 4)] HKc1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1b.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 16) [CB 12 (repeat cp_z 12)] HMID1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 28) [CB 2 (repeat cp_z 2)] HTG1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP2.
    clear HKc1 HSRC1 HMID1 HTG1 HAMP1 RW1 BD1a MU2 WM2 MI2 ST2 HBJ1 MUb WMb MIx STx STsp Aobx AFx
      AC1 SR1 SR1p.
    pose proof HBJ2 as HBJ2'. destruct HBJ2' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m2 (S - 8800) spc)
      by (apply (stk_sub m2 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m2 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as AFx.
    (* 0x8372c .. 0x8373c: the bcmp wrapper on the 6 bytes at f and the 6 bytes of .str.4 *)
    destruct (cl_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU MUb) as (CLa & CLb & CLc & CLd & CLe).
    pose proof (abc_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as ABCx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0c.
    cbn [map seq firstn skipn] in BD0c. rewrite Z.add_0_r in BD0c.
    clear RO.
    destruct (rc_memcmp_ff (cp_b fr 0) (cp_b fr 1) (cp_b fr 2) (cp_b fr 3) (cp_b fr 4) (cp_b fr 5))
      as (v & Hv & Hvr & Hvb).
    pose proof HBCMPW as HBW. unfold bcmp_wrap_contract_F_on, BCMP_WRAP_K in HBW. cbv zeta in HBW.
    assert (UBC : bv_unsigned (Z_to_bv 64 135680) = 135680) by reflexivity.
    do 5 step.
    eapply evtF_cut.
    { eapply HBW with (ls := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (rs := repeat (Z_to_bv 8 255) 6) (v := v) (lo := S - 8800);
        rewrite ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc), ?UBC.
      - exact BD0c.
      - apply (rc_ro_in_image rsegs _ _ (repeat (Z_to_bv 8 255) 6)); [exact MIx | vm_compute; reflexivity].
      - exact Hv.
      - exact MIx.
      - clear; lia.
      - apply (acl_addr_sub m2 f 50 f 6 AFx); clear; lia.
      - exact ABCx.
      - right. apply (acl_app_in m2 f 50 6 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - right. apply (acl_app_in m2 f 50 7 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - clear -HfS Hspcr RS; lia.
      - left. pose proof HHM as HH0. unfold HIGHMEM_BEG in HH0. clear -HH0 Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC2.
      - exact (srw_bcmp m2 Hn50 SR2p).
      - exact CLa.
      - exact CLb.
      - exact CLc.
      - exact CLd.
      - exact CLe.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) exact RIMG.
      - (* the bcmp wrapper's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 6 input bytes *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* their aligned shadow word cover *) right. apply (rcpF_kov8 RNG f 50 _ _ SKINF); clear; lia.
      - (* the 6 bytes at .str.4 *) exact RBC.
      - (* their aligned shadow word cover *)
        right. apply (rcpF_kov8 RNG REAC_CTRL_PARSE_BC 6 _ _ SKBC); unfold REAC_CTRL_PARSE_BC; clear; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 &
                       Hms & MU3 & WM3 & MI3 & ST3 & AC3 & SR3 & BSl & BSr).
    subst ms'.
    rewrite (ret_pc_even 538432 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit spc Rspc) in MU3. rewrite (unsigned_lit spc Rspc) in ST3.
    unfold BCMP_WRAP_K in MU3.
    pose proof (bj_call0 ob spc mc m2 m3 4560 HBJ2 MU3 WM3 MI3 ST3
                  ltac:(clear; lia) ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ3.
    pose proof (rw_cells_transport rsegs _ m2 m3 ob [CB 4 (repeat cp_z 4)] HKc2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 4) [CB 6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                                cp_b fr 10; cp_b fr 11]] RW2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW2b.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1b MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1c.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 16) [CB 12 (repeat cp_z 12)] HMID2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 28) [CB 2 (repeat cp_z 2)] HTG2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP3.
    clear HKc2 RW2 RW1b HMID2 HTG2 HAMP2 BD0c MU3 WM3 MI3 ST3 HBJ2 MUb WMb MIx STx STsp Aobx AFx
      AC2 SR2 SR2p BSl BSr ABCx CLa CLb CLc CLd CLe.
    pose proof HBJ3 as HBJ3'. destruct HBJ3' as (MUb & WMb & MIx & STx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m3 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m3 HK HO MU Aob MUb) as AFx.
    (* 0x83740 .. 0x83758: the 4-byte store of the broadcast flag at ob + 16, checked *)
    step.
    assert (RX16 : 0 <= ob + 16 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    pose proof (acl_shadow m3 ob 36 16 4 (ob + 16) Aobx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Obmod; Z.div_mod_to_equations; lia) ltac:(clear; lia)) as SH16.
    chk_core (ob + 16) RX16 (Z_to_bv 5 13) SH16 pre_sr add3.
    step. step.
    (* 0x8375c .. 0x83900: the frame's fields, each load and each store behind its shadow check *)
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    refresh.
    step.                                      (* 0x8375c addi a0,s5,14 *)
    pf_uh SCINF; chkf 14%Z (Z_to_bv 5 12); pf_h SCINF.
    step.                                      (* 0x83770 addi a0,s5,15 *)
    pf_uh SCINF; chkf 15%Z (Z_to_bv 5 13); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538516.               (* 0x83788 .. 0x83794: a1 = ob *)
    step.                                      (* 0x83794 addi a1,a1,20 *)
    chkb 20%Z 2%Z (Z_to_bv 5 14) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,18, sh a2,0(a1) *)
    refresh.
    pf_uh SCINF; chkf 18%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538584.               (* 0x837cc .. 0x837d8 *)
    step.                                      (* 0x837d8 addi a1,a1,22 *)
    chkb 22%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a2,0(a1), addi a0,s5,19 *)
    refresh.
    pf_uh SCINF; chkf 19%Z (Z_to_bv 5 13); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538644.               (* 0x83808 .. 0x83814 *)
    step.                                      (* 0x83814 addi a1,a1,23 *)
    chkb 23%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a3,0(a1), addi a0,s5,20 *)
    refresh.
    pf_uh SCINF; chkf 20%Z (Z_to_bv 5 14); pf_h SCINF.
    step.                                      (* 0x83844 addi a0,s5,21 *)
    pf_uh SCINF; chkf 21%Z (Z_to_bv 5 15); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538728.               (* 0x8385c .. 0x83868 *)
    step.                                      (* 0x83868 addi a1,a1,24 *)
    chkb 24%Z 2%Z (Z_to_bv 5 16) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,22, sh a4,0(a1) *)
    refresh.
    pf_uh SCINF; chkf 22%Z (Z_to_bv 5 14); pf_h SCINF.
    obsel (Z_to_bv 5 11) 538796.               (* 0x838a0 .. 0x838ac *)
    step.                                      (* 0x838ac addi a1,a1,26 *)
    chkb 26%Z 1%Z (Z_to_bv 5 15) no_extra.
    do 2 step.                                 (* sb a0,0(a1), addi a1,s5,16 *)
    refresh.
    pf_uh SCINF; chkf 16%Z (Z_to_bv 5 15); pf_h SCINF.
    step.                                      (* 0x838dc addi a1,s5,17 *)
    pf_uh SCINF; chkf 17%Z (Z_to_bv 5 16); pf_h SCINF.
    do 3 step.                                 (* lbu a1, zext.b, or a5,a4,a1 *)
    (* 0x83900: (fr[16] | fr[17]) = 0 is the filler, kind 1; else the kind dispatch at 0x83a14 *)
    rewrite ?rc_zextb.
    step.
    rewrite rc_lor0.
    change (bv_unsigned (cp_b fr 16)) with (cp_v fr 16).
    change (bv_unsigned (cp_b fr 17)) with (cp_v fr 17).
    match goal with H : rw_cells rsegs _ (ob + 4) [CB 6 _] |- _ => rename H into HSRCf end.
    match goal with H : rw_cells rsegs _ (ob + 10) [CB 6 _] |- _ => rename H into HDSTf end.
    match goal with H : rw_cells rsegs _ (ob + 16) _ |- _ => rename H into HMIDf end.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 10) _ _ HSRCf
                  ltac:(cbn [cells_size csize app]; lia) HDSTf) as J1.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 16) _ _ J1
                  ltac:(cbn [cells_size csize app]; lia) HMIDf) as J2.
    apply (rc_rw_flat rsegs _ (ob + 4) _ P1) in J2.
    2:{ cbn [app cells_bytes cbytes]. rewrite rc_le4_seqz by lia. rewrite !rc_le2_pack. rewrite Hvb.
        cbn [skipn repeat app]. unfold P1. reflexivity. }
    change (length P1) with 24%nat in J2.
    destruct ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)) eqn:T0; cbn [negb]; cbv iota.
    { idtac "F0".
      (* the filler: 0x83904 the 4-byte check at the box, 0x83914 li a0,1, 0x83918 -> 0x83ac8 *)
    rewrite andb_true_iff, !Z.eqb_eq in T0. destruct T0 as [T0a T0b].
    refresh. idtac "F1".
    chkb0 (Z_to_bv 5 11) add3. idtac "F2".
    step. step. idtac "F3".
    assert (EK1 : cp_kind fr = 1)
      by (unfold cp_kind, cp_type; rewrite T0a, T0b; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    assert (ERC : cp_rec fr = false)
      by (unfold cp_rec, cp_type; rewrite T0a; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    match goal with H : rw_cells rsegs _ ob [CB 4 _] |- _ => rename H into HKf end.
    match goal with H : rw_cells rsegs _ (ob + 28) [CB 2 _] |- _ => rename H into HTGf end.
    match goal with H : rw_cells rsegs _ (ob + 30) [CB 6 _] |- _ => rename H into HAMPf end.
    eapply (L_kind fra fv spc j nn w120 mc ob _ 1 (repeat cp_z 2) (repeat cp_z 6));
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj MUb (conj WMb (conj MIx STx)))
      | exact HKf | exact J2 | exact HTGf | exact HAMPf
      | unfold ctrlparse; rewrite HE; cbn [fst]; exact EK1
      | clear; lia
      | unfold ctrlparse; rewrite HE; cbn [snd]; unfold cp_struct; rewrite EK1, ERC;
        cbn [Z.eqb Pos.eqb repeat app]; unfold P1; reflexivity ]. }
    (* 0x83a14 ..: the kind dispatch *)
    pose proof (cp_v_range fr 16) as R16. pose proof (cp_v_range fr 17) as R17.
    pose proof (cp_v_range fr 18) as R18. pose proof (cp_v_range fr 19) as R19.
    pose proof (cp_v_range fr 22) as R22. pose proof (KL1_range (cp_v fr 22)) as KR.
    assert (KL6 : KL1 (cp_v fr 22) <> 6) by (clear -KR; lia).
    (* the dispatch does no more calls: drop the disjunctive premises, they make every store's
       transport (slia) split the context *)
    clear DFf Fapp Obrt Obsp Obsv Obfr Obcf Obf HfS AFm.
    drive.
    all: try leaves.
    (* goal 2: 0x83a8c, kind_of_link1 *)
    2:{ step.
        eapply evtF_cut; [eapply HKOL | intros ? [? ->]].
        rewrite rc_signed_zxb.
        change (bv_unsigned (cp_b fr 22)) with (cp_v fr 22).
        rewrite (ret_pc_even 539280 ltac:(clear; lia) ltac:(clear; lia)).
        refresh.
        chkb0inv (Z_to_bv 5 12).
        leafb. }
    (* goal 1: 0x83ae8, the record: fr[19] = 3, the two tag bytes, then the amp test *)
    step. step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 19) 3) as [E19|E19]; cbn [negb]; cbv iota.
    2:{ drive. all: leaves. }
    assert (HRC : cp_rec fr = true) by (unfold cp_rec, cp_type; zeval; reflexivity).
    rdb 34%nat 2%nat ltac:(intros jx Hjx; apply cp_rd_rec; [exact HE | exact HRC | lia]).
    rdb 32%nat 1%nat ltac:(intros jx Hjx; replace (32 + jx)%nat with 32%nat by lia;
                           apply cp_rd_rec; [exact HE | exact HRC | lia]).
    refresh.
    step. pf_uh SCINF; chkf 34%Z (Z_to_bv 5 12); pf_h SCINF.
    step. pf_uh SCINF; chkf 35%Z (Z_to_bv 5 13); pf_h SCINF.
    obsel (Z_to_bv 5 11) 539432.
    step. chkb 28%Z 2%Z (Z_to_bv 5 14) add1.
    do 4 step.
    refresh.
    pf_uh SCINF; chkf 32%Z (Z_to_bv 5 13); pf_h SCINF.
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 32) 18) as [E32|E32]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    rdb 33%nat 1%nat ltac:(intros jx Hjx; replace (33 + jx)%nat with 33%nat by lia;
                           apply cp_rd_33; [exact HE | exact HRC | exact E32]).
    step. pf_uh SCINF; chkf 33%Z (Z_to_bv 5 13); pf_h SCINF.
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 33) 18) as [E33|E33]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    do 2 step.
    rewrite rc_pack_eqb by (clear; lia).
    change (bv_unsigned (cp_b fr 34)) with (cp_v fr 34).
    change (bv_unsigned (cp_b fr 35)) with (cp_v fr 35).
    destruct (Z.eqb_spec (cp_v fr 34 * 256 + cp_v fr 35) 257) as [EP|EP]; cbn [negb]; cbv iota.
    2:{ flat_tg.
        destruct (Z.eqb_spec (cp_v fr 34) 1) as [E34a|E34a];
          [ assert (E35a : cp_v fr 35 <> 1)
              by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
                  clear -A34 A35 EP E34a; lia)
          | ];
          drive; leaves. }
    assert (E34 : cp_v fr 34 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    assert (E35 : cp_v fr 35 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    refresh. chkb0 (Z_to_bv 5 11) add3.
    do 3 step.
    assert (EK6 : cp_kind fr = 6) by (unfold cp_kind, cp_type, cp_amp; zeval; reflexivity).
    rdb 36%nat 3%nat ltac:(intros jx Hjx; apply cp_rd_amp; [exact HE | exact HRC | exact EK6 | lia]).
    refresh.
    pf_uh SCINF; chkf 36%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel (Z_to_bv 5 11) 539596.
    step. chkb 30%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    pf_uh SCINF; chkf 37%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel (Z_to_bv 5 11) 539656.
    step. chkb 31%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    pf_uh SCINF; chkf 38%Z (Z_to_bv 5 12); pf_h SCINF.
    obsel2 (Z_to_bv 5 26) 539712.
    step. chkb 32%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    flat_tg.
    match goal with
    | HOb : OB ?fraq ?obq |- _ =>
        match goal with Hq : rw_cells rsegs _ (obq + 30) _ |- _ => rename Hq into HAMPr end;
        apply (rc_rw_flat rsegs _ (obq + 30) _
                 ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3)) in HAMPr;
        [ cbn [length app repeat] in HAMPr
        | first [ reflexivity
                | cbn [cells_bytes cbytes app repeat skipn firstn]; reflexivity
                | vm_compute; reflexivity ] ];
        eapply (L_be0 fraq _ _ _ _ _ _ obq _ 6 [cp_b fr 35; cp_b fr 34]
                      ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3))
    end;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | kfact
          | bfact ].
  Qed.


  (* 0x836c0 .. 0x8370c: the two header bytes (12 = 0x88, 13 = 0x19), each behind its shadow check; a byte that
     differs leaves with the kind 0 and the zeroed box. *)
  Lemma body_tail : 50 <= n -> forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG Qp
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836c0) fc None mx (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL HMSET MI0 RFSS RFW1 RTLS. pf_hide.
    intros Hn50 fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof DFf as DFf'. unfold Wall, Wf in DFf'. cbn [disjoint_from app fst snd] in DFf'.
    destruct DFf' as (Dwin & Dhint & Dflag & Dfr & Dsh & Dbox & _).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    (* 0x836c0: byte 12 of the frame, checked *)
    rdb 12%nat 1%nat ltac:(intros jx Hjx; replace (12 + jx)%nat with 12%nat by lia;
                                     apply cp_rd_12; lia).
    step.
    assert (RX12 : 0 <= f + 12 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 12 1 (f + 12) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH12.
    chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 12) 136) by (clear; lia).
    change (bv_unsigned (cp_b fr 12)) with (cp_v fr 12).
    destruct (Z.eqb_spec (cp_v fr 12) 136) as [E12|E12]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E12), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    (* 0x836e0: byte 13 of the frame, checked *)
    rdb 13%nat 1%nat ltac:(intros jx Hjx; replace (13 + jx)%nat with 13%nat by lia;
                                     apply cp_rd_13; lia).
    step.
    assert (RX13 : 0 <= f + 13 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 13 1 (f + 13) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH13.
    chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 13) 25) by (clear; lia).
    change (bv_unsigned (cp_b fr 13)) with (cp_v fr 13).
    destruct (Z.eqb_spec (cp_v fr 13) 25) as [E13|E13]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E13), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    assert (HE : cp_hdr n fr = true) by (apply cp_hdr_spec; repeat split; lia).
    (* 0x83700 .. 0x8370c: s6 = the box pointer, on both paths of `beqz s4` *)
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w : word, w = Z_to_bv 64 ob ->
                      evtF segs rgq Q (MS (bvmap_set (Z_to_bv 5 22) w R) Fm (Z_to_bv 64 0x8370c) fcc rv mm ro));
        [ step; step; rewrite (rc_eqb_lit o 0) by (clear -Ro; lia);
          destruct HO as [(Eo & Eob) | (Eo & Eob)];
          [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
            apply (G (Z_to_bv 64 (fra + 32)) ltac:(rewrite Eob; reflexivity))
          | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
            apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
        | intros w Hw; subst w; simp_regs ]
    end.
    eapply (body_copy Hn50 HE fra fv spc j nn w120 mc ob mx);
      [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc | exact HBJ | exact RWx ].
  Qed.


  (* 0x836a8 .. : __asan_memset(ob, 0, 36) zeroes the output box, then the header test n < 50. ob is the box the
     run chose at 0x8369c/0x836a0 (the frame's redzone when o = 0, else o). *)
  Lemma body_main : forall fra fv spc j nn w120 mc ob jb
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    rw_cells rsegs mc ob [CB 36 jb] -> addressable mc ob 36 -> stk rsegs mc (S - 8800) S ->
    asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    evtF rsegs RNG Qp
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836a8) fc None mc (seg_rom rsegs)).
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL MI0 RFSS RFW1 RTLS. pf_hide.
    intros fra fv spc j nn w120 mc ob jb rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO HOrw Aob STw ACc SRc.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (U36 : bv_unsigned (Z_to_bv 64 36) = 36) by reflexivity.
    assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (STsp : stk rsegs mc (S - 8800) spc)
      by (apply (stk_sub mc (S - 8800) S (S - 8800) spc STw); clear -Hspcr RS; lia).
    pose proof HMSET as HM. unfold asan_memset_contract_F_on, ASAN_MEMSET_K in HM. cbv zeta in HM.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HM.
    (* 0x836a8 li a2,36; 0x836ac mv a0,s3; 0x836b0 li a1,0; 0x836b4 jal -> 0x524c4 *)
    do 4 step.
    eapply evtF_cut.
    { eapply HM with (junk := jb) (lo := S - 8800);
        rewrite ?(unsigned_lit _ Rob), ?(unsigned_lit spc Rspc), ?U36, ?U0.
      - change (Z.to_nat 36) with 36%nat. exact HOrw.
      - clear; lia.
      - exact Aob.
      - right; exact Obapp.
      - right; apply (acl_app_in mc _ 36 7 Aob); clear; lia.
      - exact Obrt.
      - clear -Obsp; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACc.
      - apply (srw_memset fra fv spc j nn w120 ob mc _ _ HK HO);
          [ rewrite ?(unsigned_lit _ Rob); reflexivity | first [exact U36 | reflexivity] | exact SRc ].
      - exact MI.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memset's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 36 bytes of the box *) exact RGOB.
      - (* their aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the shadow of __asan_memset's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1m & a2m & a3m & a4m & a5m & a6m & a7m & t3' & t4' & t5' & t6' & m' &
                       Hms & MUm & WMm & MIm & STm & RWm & ACm & SRm).
    subst ms'.
    rewrite (ret_pc_even 538296 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob), U36, (unsigned_lit spc Rspc) in MUm. unfold ASAN_MEMSET_K in MUm.
    rewrite (unsigned_lit _ Rob), U36 in RWm. change (Z.to_nat 36) with 36%nat in RWm.
    rewrite (unsigned_lit spc Rspc) in STm.
    (* the body's running footprint: the box and the callee windows *)
    pose proof RWm as RWbk. destruct RWbk as [[_ Hbox] _]. cbn [cells_bytes cbytes] in Hbox.
    rewrite app_nil_r in Hbox.
    assert (RMc : rd_mono mc m').
    { apply (rd_mono_list _ mc m' MUm). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbox). rewrite repeat_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STm). clear -Hy Hspcr; lia. }
    assert (MUx : munch [(ob, ob + 36); (S - 8800, spc)] mc m').
    { eapply munch_weaken; [| exact MUm].
      intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _).
      split; [exact H1|]. split; [clear -H2 Hspcr; lia | exact I]. }
    assert (STx : stk rsegs m' (S - 8800) S) by (exact (stk_mono mc m' (S - 8800) S STw WMm RMc)).
    (* 0x836b8: li a0,50; 0x836bc: bltu s6,a0 -> n < 50 exits at 0x8391c *)
    step. step. rewrite (rc_ltu_lit n 50) by lia.
    destruct (Z.ltb_spec n 50) as [Hlt|Hge]; cbv iota.
    - (* n < 50: no header, the box stays zero, a0 = 0 *)
      step.
      assert (Hcphdr : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.leb_gt 50 n) Hlt); reflexivity).
      assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
      eapply (L_join fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact MUx | exact WMm | exact MIm | exact STx | ].
      rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWm.
    - (* 50 <= n: the header checks, the copies, the comparison and the kind *)
      eapply (body_tail Hge fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc
        | refine (conj MUx (conj WMm (conj MIm STx))) | ].
      replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with cp_z in RWm
        by (vm_compute; reflexivity).
      exact RWm.
  Qed.

  (* 0x8369c .. 0x836a8: the box pointer s3 = o (or the frame's redzone when o = 0). *)
  Lemma body_holds : KB Qp.
  Proof using ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR. clear SMAL MI0 RFSS RFW1 RTLS. pf_hide.
    unfold KB. intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      HK HB HFL HBaddr.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (EMt : fs_M 1 = 8192) by reflexivity.
    assert (Hjb0 : 0 <= j < 8192)
      by (destruct HK as [(_ & _ & _ & Ej & _) | (Hjb & _ & _ & _ & _ & _)];
          [lia | rewrite EMt in Hjb; lia]).
    assert (Hnn1 : nn <= 1)
      by (destruct HK as [(_ & _ & _ & _ & Enn) | (_ & _ & _ & _ & _ & Enn & _)]; lia).
    pose proof (stk_mono m mc (S - 8800) S ST0 WM RM) as STw.
    assert (STfr : stk rsegs mc fra (fra + 128)).
    { destruct HK as [(Efv & Efra & _) | (Hj & Efra & _)].
      - apply (stk_sub mc (S - 8800) S fra (fra + 128) STw);
          [ clear -Efra HAlo HAhi RS; rewrite Efra; lia | clear -Efra HAlo HAhi RS; rewrite Efra; lia | lia ].
      - pose proof (stk_mono m mc FS (FS + FS_SIZE) Pfsstk WM RM) as STfs.
        assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
        rewrite EMt in Hj.
        apply (stk_sub mc FS (FS + FS_SIZE) fra (fra + 128) STfs);
          [ rewrite Efra, EFRj; clear -Pfs0 Hj; lia
          | rewrite Efra, EFRj; unfold FS_SIZE; clear -Pfs0 HFSb Hj; lia | lia ]. }
    assert (ACc : asan_cells mc).
    { apply (asan_cells_kept (Wf fra j nn) m mc AC0 MU).
      unfold Wf, RT_LO, RT_HI, fs_hint, fs_flag, shadow_addr;
        cbn [disjoint_from fst snd Z.of_nat Pos.of_succ_nat].
      try (change (2 ^ 15) with 32768); try (change (2 ^ (15 - 1)) with 16384).
      repeat split; try exact I; left;
        unfold HIGHMEM_BEG, APPMEM_END in *;
        clear -HHM HAE Pfs2 Hjb0 FRlo SH1; lia. }
    pose proof (shadow_rw_mono_on _ m mc SR0 WM RM) as SRc.
    (* 0x8369c: mv s3,s10; 0x836a0: beqz s4 -> the box pointer *)
    step.
    step. rewrite (rc_eqb_lit o 0) by lia.
    destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbv iota.
    - (* o = 0: the box is the frame's redzone fra + 32, carved from the frame's stack bytes *)
      assert (STbox : stk rsegs mc (fra + 32) (fra + 68))
        by (apply (stk_sub mc fra (fra + 128) (fra + 32) (fra + 68) STfr); lia).
      destruct (stk_carve rsegs mc (fra + 32) (fra + 68) 36%nat STbox ltac:(lia)) as [_ [jb Hrw]].
      replace (fra + 68 - Z.of_nat 36) with (fra + 32) in Hrw by lia.
      eapply (body_main fra fv spc j nn w120 mc (fra + 32) jb);
        [ exact HK | exact HB | exact HFL | left; split; [exact Eo | reflexivity]
        | exact Hrw | exact HBaddr | exact STw | exact ACc | exact SRc ].
    - (* o <> 0: the box is o, transported from the caller's rw_cells *)
      step.
      destruct (HOK Eo) as (Ho4 & Ho36 & HOrw & HoS & Hof).
      assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
        by (unfold reac_ctrl_parse_D; apply in_or_app; right;
            rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity).
      assert (Hdjo : forall x, o <= x < o + 36 -> outside (Wf fra j nn) x).
      { intros x Hx.
        destruct (AO0 Eo) as (AOa & _ & _).
        assert (Hxapp : app_mem x)
          by (pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as Ha;
              replace (o + (x - o)) with x in Ha by lia; exact Ha).
        pose proof (dj_pair o (o + 36) _ _ HinO (proj1 (fp_wx_hint_flag_in FS X))) as Hoh.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        unfold Wf. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        - clear -Hx HoS; destruct HoS; lia.
        - intros [HL HR]. clear -Hx HL HR Hoh; lia.
        - intros [HL HR]. destruct HK as [(_ & _ & _ & _ & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)].
          + rewrite Enn in HR. clear -HL HR; lia.
          + rewrite Enn in HR.
            assert (EFL : fs_flag FS 1 j = fs_flag FS 1 0 + j) by (rewrite !fs_flag1; lia).
            rewrite EFL in HL, HR. rewrite EMt in Hjb, Hofl. clear -Hx HL HR Hofl Hjb; lia.
        - intros [HL HR]. destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          + rewrite Efr in HL, HR. clear -Hx HoS HL HR HAlo HAhi; destruct HoS; lia.
          + destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hx HL HR Hc; lia.
        - intros [HL HR]. apply (acl_app_not_shadow x Hxapp). unfold shadow_addr in HL, HR.
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
      assert (Hbox : rw_cells rsegs mc o [CB 36 junk])
        by (eapply acl_rw; [exact HOrw | exact MU | exact WM |
              intros x Hx; apply Hdjo; cbn [cells_size csize] in Hx; lia]).
      assert (Aob : addressable mc o 36).
      { destruct (AO0 Eo) as (AOa & _ & _).
        apply (acl_addr_munch (Wf fra j nn) m mc o 36 AOa MU).
        intros i Hi.
        pose proof (acl_app_in m o 36 i AOa Hi) as Hoi.
        pose proof (rt_app_shadow (o + i) Hoi) as Hsh.
        unfold Wf. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *; clear -HL HR HHM HAE; right; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_hint in HL, HR; cbn [Z.of_nat] in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_flag in HL, HR; cbn [Z.of_nat Pos.of_succ_nat] in HL, HR;
            change (2 ^ 15) with 32768 in HL, HR; change (2 ^ (15 - 1)) with 16384 in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0 Hjb0 Hnn1; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          replace (shadow_addr (o + i)) with (fra + (shadow_addr (o + i) - fra)) by lia.
          apply FAP; clear -HL HR; lia.
        + intros HC.
          assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
            by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
          rewrite E16 in HC.
          apply (acl_win_sh (o + i) fra (fra + 128) FR8); [| exact HC].
          intros [HL HR].
          destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          * destruct HoS as [Hc|Hc]; rewrite Efr in HL, HR; clear -Hi Hc HL HR HAlo HAhi; lia.
          * destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hi HL HR Hc; lia. }
      eapply (body_main fra fv spc j nn w120 mc o junk);
        [ exact HK | exact HB | exact HFL | right; split; [exact Eo | reflexivity]
        | exact Hbox | exact Aob | exact STw | exact ACc | exact SRc ].
  Qed.

  (* The whole run: the entry (0x83578 .. 0x8369c), the body, the exit. *)
  Lemma parse_run : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evtF rsegs RNG Qp (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    exact (entry t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Qp m eq_refl body_holds).
  Qed.

End SetupF.

End ParseFOn.

(* The free-frame `_on` contract in footprint form: Module ParseFOn's run at the statement's state, as
   reac_ctrl_parse_x_F_holds (the same quantified shadow covers of the footprint). *)
Theorem reac_ctrl_parse_x_F_holds_on :
  asan_stack_malloc_1_contract_F_on -> asan_memset_contract_F_on -> asan_memcpy_contract_F_on ->
  bcmp_wrap_contract_F_on -> reac_ctrl_parse_contract_x_F_on.
Proof.
  intros SMAL MSET MCPY BWRP. unfold reac_ctrl_parse_contract_x_F_on.
  intros RNG X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk HXF Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae
    Haddr Hfa Hoa Hbc Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls
    RBY RIMG0 RWIN RWSHA RINF RFSHA ROUT ROSHA RBC RBCSHA RFSS RW1 RTLS.
  subst a0 a1 a2 sp. unfold REAC_CTRL_PARSE_K in *.
  assert (RS : 8800 <= S < 2^64) by lia.
  assert (XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X)
    by (eapply Forall_impl; [|exact HXF]; intros ci (H1 & _ & H3); exact (conj H1 H3)).
  assert (XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X)
    by (eapply Forall_impl; [|exact HXF]; intros ci (_ & H2 & _); exact H2).
  pose proof kind_of_link1_F_holds as KOL.
  (* the image, as the literal range the step tactics match *)
  assert (RIMG : rng RNG 0x10000 0x5ee000) by (unfold IMG_LO, IMG_HI in RIMG0; exact RIMG0).
  (* the quantified shadow covers of the window (from its exact metadata), of f, of o and of the compare bytes *)
  assert (SCW : shcov RNG (S - 8800) 8800) by exact (rcpF_win_cov RNG S HS16 RWSHA).
  assert (SKW : shkov RNG (S - 288) 160) by exact (rcpF_win_kov RNG S HS16 RWSHA).
  assert (SCF : 50 <= n -> shcov RNG f 50) by (intros H50; apply rcpF_cov; exact (RFSHA H50)).
  assert (SKF : 50 <= n -> shkov RNG f 50) by (intros H50; apply rcpF_kov; exact (RFSHA H50)).
  assert (SCO : o <> 0 -> shcov RNG o 36) by (intros H0; apply rcpF_cov; exact (ROSHA H0)).
  assert (SKO : o <> 0 -> shkov RNG o 36) by (intros H0; apply rcpF_kov; exact (ROSHA H0)).
  assert (SKBC : shkov RNG REAC_CTRL_PARSE_BC 6) by (apply rcpF_kov; exact RBCSHA).
  (* the class-1 side-stack bytes of fp_w, one rng fact per range *)
  pose proof RW1 as RWc. unfold fp_w, fp_w1 in RWc. cbn [flat_map app] in RWc.
  apply Forall_cons_iff in RWc as [_ RWc].
  apply Forall_cons_iff in RWc as [RFLG RWc].
  apply Forall_cons_iff in RWc as [RFRM RWc].
  apply Forall_cons_iff in RWc as [RFRS _].
  cbn [fst snd] in RFLG, RFRM, RFRS.
  replace (fs_flag FS 1 0 + fs_M 1 - fs_flag FS 1 0) with (fs_M 1) in RFLG by lia.
  (* the frames' shadow comes byte-exact; both of its ends are the shadow byte of a 64-aligned address *)
  pose proof Hfp as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSp & HFS4 & _) & _).
  assert (EQ : FS = 4096 * (FS / 4096)) by (pose proof (Z.div_mod FS 4096 ltac:(lia)); lia).
  set (q := FS / 4096) in EQ. clearbody q.
  assert (EF0 : fs_frame FS 1 0 = 64 * (64 * q + 16960)) by (rewrite fs_frame1; lia).
  assert (EF1 : fs_frame FS 1 (fs_M 1) = 64 * (64 * q + 33344))
    by (rewrite fs_frame1; change (fs_M 1) with 8192; lia).
  assert (ES0 : shadow_addr (fs_frame FS 1 0) = 8 * (64 * q + 16960) + ASAN_K).
  { unfold shadow_addr. rewrite EF0.
    replace (64 * (64 * q + 16960)) with (8 * (8 * (64 * q + 16960))) by lia. rewrite rcpF_div8. lia. }
  assert (ES1 : shadow_addr (fs_frame FS 1 (fs_M 1)) = 8 * (64 * q + 33344) + ASAN_K).
  { unfold shadow_addr. rewrite EF1.
    replace (64 * (64 * q + 33344)) with (8 * (8 * (64 * q + 33344))) by lia. rewrite rcpF_div8. lia. }
  rewrite ES0, ES1 in RFRS.
  assert (SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0))
    by (rewrite EF0, EF1; exact (rcpF_span_cov RNG (64 * q + 16960) (64 * q + 33344) RFRS)).
  assert (SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0))
    by (rewrite EF0, EF1; exact (rcpF_span_kov RNG (64 * q + 16960) (64 * q + 33344) RFRS)).
  eapply ParseFOn.parse_run; eassumption.
Qed.
