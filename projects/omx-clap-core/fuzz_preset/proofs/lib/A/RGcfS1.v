(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: field round 3 part 3c (YGcfMallocCompose.ikeep_cf no longer keeps the overlay
   normal form): seg_pre_cf's ikeep_cf goal is its two raw-frame conjuncts; MNK stays proved for pa_leaf's post
   (FSRealloc_S1_pa.v), which still states it. *)
(* Modified by Theorem Labs, 2026-10-31: seg_pre_cf / rw_pre_A take the form of the realloc keep record's field rwk_pre
   (YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf): the frame is YGcfMallocComposeKeep.ikeep_mn_cf (ikeep_cf's two
   conjuncts, then the memnorm keep, which is MNK). *)
(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S1.v (hub ddc081c1a03, blob 72c9c802e887) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025; one resolve line, 86568 -> 87896 = 0xac0c0 / 8), then restated at preset's event-free allocator instance (record, the internal file A5.md):
   - the Section premise PRE is acall_pre_cf tfibsegs B ly S Hp W regs mem md ch (YG0dcf.v:48), whose ARcf reads the machine's memory itself, so fs's user-poison layer (FSupoison.unpoison, ARU, appz, vm_lo / vm_T / vm_C) is gone and Up is preset's ghost set Hp;
   - the cell facts come from a Theorem Labs lane's WrapAKit.v (cf_const_lookup / cf_const_lookup_sym / cf_cell_state / cf_unwinding_val, img_cover_of_ledger_cf), p's facts from chunk_facts_cf (YG0scf.v);
   - FINH re-establishes RGcfLaws.ARXqA B Hp (YGcfInstBase.ARXq_cf at image A) at s1 with A/AFf0cfR.v's free_finn_ARcf (AFf0cf's realloc twin), xs_mapped_cf from the rebuilt ARcf's ledger field (YGcfXs.ARcf_xsm), and pa_leaf's relation parameter R := ARXqA.
   The walk (FSRealloc_S1_t.segA) is unchanged. *)
(* fuzz_state image A: realloc segment S1, RGtop's [seg_pre K1_fs] at fs's instance (FSRealloc_inst.FS_seg_pre).
   RtS1, 2026-10-29.

   Rule 24 (VERIFY 02:59Z form; the internal file L12-RtResume.md): proves function __asan::Allocator::Reallocate chain (fs image A:
   __wrap_realloc 0x5373c -> __interceptor_realloc 0x53b38 -> __asan::asan_realloc 0x32f40 -> __asan::Allocator::Reallocate
   0x32fec), segment S1 (reuse search: proof-index by NAME and by EVERY ADDRESS, unpiped, 2026-10-29 03:50-03:56Z,
   outputs in a lane record (a Theorem Labs lane r24/1029/*.txt); named cold branches, 725 refs,
   a lane record (a Theorem Labs lane's internal file cold-search.md)).  Released donor (ported, same machine code modulo pc-relative
   fields): cgif_rgb_fuzzer lib/YF6s.v (FH_ok, FINH, pa_arm; this file's Section f), with YF6t / YF6u / YF6r / YF6q / YF6v /
   YF77 / YF69 as FSRealloc_S1_t / _u / _r / _pa / _tbl / _f.  The released donor YF6t walks this code on the LONG branch:
   the malloc_context_size cell read by GetMallocContextSize 0x5b4c4 (`lw a0, -0x1c4(a0)`) is 0xabbbc = 30, the generated
   start-up certificate's row `z4 (ANum 0xabbbc) 0x1e` (A/AF0m.v), seeded as REG0's `flit4 0xabbbc 30`.
   p's facts (PF) come from the chunk of p instead of cgif_rgb's free walk (YF1p.p_facts); the leaf stops at Allocate's
   entry 0x325b8 (one `jal` after the donor's 0x33054); word_of_bytes is fs's A/AFio.v lemma (copied).
   Every error / CHECK branch of the prefix is decided untaken by the symbolic walk (FSRealloc_S1_t.segA). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AFgi AFex AFfy AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB13 AFfg FSRealloc_S1_tbl FSRealloc_S1_pa FSRealloc_S1_u FSRealloc_S1_r FSRealloc_S1_t.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFl4 WrapAKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFf0cfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1h CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YG08cf AllocG RGtop YGcfRmodel YGcfMallocCompose YGcfReallocCompose YGcfXsMapped.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RGthinK RGthinS RGcfK.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RGcfLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_io. destruct md; cbn; repeat split; reflexivity. Qed.
Lemma mbyte_off_apresent : forall (H : word -> bool) mem a b,
off_img a -> mbyte tfibsegs (mrestrict H mem) a = Some b -> apresent H mem a.
Proof.
intros H mem a b Ha Hb. unfold mbyte, mrestrict in Hb.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- rewrite (seg_rom_none_off a Ha) in Hb. discriminate.
- destruct (mem (Z_to_bv 64 a)) as [b'|] eqn:E; [|rewrite (seg_rom_none_off a Ha) in Hb; discriminate].
split; [exact Hh | exists b'; exact E].
Qed.
Lemma rw_wview : forall m (x : word), 0xa1000 <= bv_unsigned x < 0x600000 -> wview tfibsegs m x <> None.
Proof. intros m x Hx. rewrite <- tsegs_tfasegs. exact (tfib_rw_window m x Hx). Qed.
Lemma memnorm_addr : forall (m m' : word -> option byte),
YAkMemnorm.memnorm tfibsegs m ->
(forall x b, m' x = Some b -> (exists b0, m x = Some b0) \/ wview tfibsegs m x <> None) ->
YAkMemnorm.memnorm tfibsegs m'.
Proof.
intros m m' [Mi Mt] HX.
assert (P : forall x : word, (exists b0, m x = Some b0) \/ wview tfibsegs m x <> None ->
  YAkMemnorm.ro_addr tfibsegs x = false /\ (find_segment tfibsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE)).
{ intros x [[b0 E0]|Wv]; [exact (conj (Mi x b0 E0) (Mt x b0 E0))|].
  unfold wview in Wv. revert Wv. destruct (m x) as [b0|] eqn:E; intros Wv; [exact (conj (Mi x b0 E) (Mt x b0 E))|].
  unfold YAkMemnorm.ro_addr. revert Wv.
  destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|]; intros Wv; [|exfalso; exact (Wv eq_refl)].
  revert Wv. destruct (seg_writable seg); intros Wv; [|exfalso; exact (Wv eq_refl)].
  split; [reflexivity | left; discriminate]. }
split; intros x b E; destruct (P x (HX x b E)) as [P1 P2]; [exact P1 | exact P2].
Qed.
Lemma cf_malloc_max_lt30 : cf_malloc_max < 2 ^ 30.
Proof.
pose proof cf_malloc_max_pos as P. assert (P1 : 0 <= cf_malloc_max - 1) by lia.
pose proof (YG08cf.sec_map_size_ge (cf_malloc_max - 1) P1) as G.
assert (P2 : 0 <= cf_malloc_max - 1 < cf_malloc_max) by lia.
pose proof (cf_sizes_ok (cf_malloc_max - 1) P2) as Sz. pose proof cf_nob_ok as N. lia.
Qed.
Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable Hp : list Z.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (pp : sptr) (nold rn : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly 0x53c74 regs ch.
Let rp : Z := sptr_addr B ly pp.
Let sp0 : Z := bv_unsigned (getr regs 2).
Hypothesis PRE : acall_pre_cf tfibsegs B ly S Hp W regs mem md ch.
Hypothesis HBLK : In (pp, nold) (blocks S).
Hypothesis HA0 : getr regs 10 = w64 rp.
Hypothesis HA1 : getr regs 11 = w64 rn.
Hypothesis Hrn : 1 <= rn < 2 ^ 30.
Hypothesis IA1 : tfib_ialloc_spec.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation ii := (st_internal_inited S).
Lemma M : ARmcf B ly S Hp rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf_cf (as_universe B) S := amc_wf B ly S Hp rd0 M.
Let LO : layout_ok ly := amc_layout B ly S Hp rd0 M.
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
(* the junk words T + 2856 / T + 2864 (the thread stats Reallocate bumps): Section variables of the walk; the glue
   below takes them from junk_T *)
Section j.
Variables (jr1 jr2 : Z).
Hypothesis Hjr1 : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2856) 8 jr1.
Hypothesis Hjr2 : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2864) 8 jr2.
Local Notation E0 := (FSRealloc_S1_u.E0 ly regs ch rp jr1 jr2).
Local Notation IMv := (FSRealloc_S1_u.IMv rp).
Local Notation LENv := (FSRealloc_S1_u.LENv ly regs ch).
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. exact (cf_const_lookup_sym B TB ly S Hp H0 mem M e w e' E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. intros a w x E. exact (cf_const_lookup B TB ly S Hp H0 mem M a w x E). Qed.
Lemma cell_state : forall c e (w : nat) e', In c (acells_cf B ly S) -> c = ACell e w (AV e') -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros c e w e' Hin E. exact (cf_cell_state B ly S Hp H0 mem M c e w e' Hin E). Qed.
Lemma cell_stateZ : forall c e (w : nat) x, In c (acells_cf B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. exact (cell_state c e w (ANum x) Hin E). Qed.
Lemma unwinding_val : val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof. exact (cf_unwinding_val B ly S Hp H0 mem M). Qed.
Lemma ial_vals : val_mem tfibsegs m0 TFIB_IAL_FLAG 1 (if ii then 1 else 0) /\ val_mem tfibsegs m0 (TFIB_IAL_FLAG + 1) 1 0 /\
(if ii then val_mem tfibsegs m0 TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16)
else val_mem tfibsegs m0 TFIB_IAL_W 8 0 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 0) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0)).
Proof.
assert (IN : forall c, In c (ialloc_cells B S) -> In c (acells_cf B ly S)) by (intros c Hc; unfold acells_cf; rewrite !in_app_iff; do 7 right; left; exact Hc).
unfold ialloc_cells in IN. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB) in IN.
splits.
- replace TFIB_IAL_FLAG with (aeval B ly (ANum TFIB_IAL_FLAG)) at 1 by reflexivity. eapply cell_stateZ; [apply IN; left; reflexivity | destruct ii; reflexivity].
- replace (TFIB_IAL_FLAG + 1) with (aeval B ly (ANum (TFIB_IAL_FLAG + 1))) by reflexivity. eapply cell_stateZ; [apply IN; right; left; reflexivity | reflexivity].
- assert (E1 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO)) = TFIB_IAL_W) by (cbn; rewrite (ts_ial_lo _ TB); lia).
assert (E2 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 8)) = TFIB_IAL_W + 8) by (cbn; rewrite (ts_ial_lo _ TB); lia).
assert (E3 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) = TFIB_IAL_W + 16) by (cbn; rewrite (ts_ial_lo _ TB); lia).
destruct ii; split.
+ rewrite <- E1. eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2, <- E3. eapply cell_state; [apply IN; do 3 right; left; reflexivity | reflexivity].
+ rewrite <- E1. eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2. eapply (cell_state _ _ 8 (ANum 0)); [apply IN; do 3 right; left; reflexivity | reflexivity].
- intros a Ha. pose proof (amc_zero B ly S Hp rd0 M) as ZR. unfold ialloc_zero in ZR. rewrite (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB) in ZR.
apply Forall_cons_iff in ZR as [Z1 ZR]. apply Forall_cons_iff in ZR as [Z2 _].
assert (R : rd0 a = Some 0).
{ destruct Ha as [Ha|Ha].
- replace a with (aeval B ly (AIal 0) + (a - TFIB_IAL_LO)) by (cbn; rewrite (ts_ial_lo _ TB); lia). apply Z1. cbn [snd]. lia.
- replace a with (aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) + (a - (TFIB_IAL_W + 16))) by (cbn; rewrite (ts_ial_lo _ TB); lia). apply Z2. cbn [snd]. lia. }
exact (aview_byte _ _ _ _ R).
Qed.
Lemma HSP : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & Hlo & _ & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma IMG : img_cover ly.
Proof. destruct PRE as ((_ & LED & _) & _). exact (img_cover_of_ledger_cf ly S md LED). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) kPtrArrayResv /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) kFakeStackSize /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_stk_lo ly mod 4096 = 0.
Proof. exact (AFf0cfR.HIGH B ly S rd0 Hp M IMG). Qed.
(* the thread stats words Reallocate bumps (T + 2856, T + 2864) hold some word: they are thread junk (ajunk's
   (AT t_stats, t_unwinding - t_stats)), present by ARm's am_junk *)
Lemma word_of_bytes : forall (m : word -> option byte) a,
(forall k, (k < 8)%nat -> exists b, mbyte tfibsegs m (a + Z.of_nat k) = Some b) -> exists w, val_mem tfibsegs m a 8 w.
Proof.
intros m a BY.
destruct (BY 0%nat ltac:(lia)) as [b0 B0]. destruct (BY 1%nat ltac:(lia)) as [b1 B1]. destruct (BY 2%nat ltac:(lia)) as [b2 B2]. destruct (BY 3%nat ltac:(lia)) as [b3 B3].
destruct (BY 4%nat ltac:(lia)) as [b4 B4]. destruct (BY 5%nat ltac:(lia)) as [b5 B5]. destruct (BY 6%nat ltac:(lia)) as [b6 B6]. destruct (BY 7%nat ltac:(lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YO0f.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs m (a + Z.of_nat kk) = Some bk -> YO0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs m (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|lia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | lia].
Qed.
Lemma junk_T : forall a, T + t_stats <= a -> a + 8 <= T + t_unwinding -> exists w, val_mem tfibsegs m0 a 8 w.
Proof.
intros a H1 H2. apply word_of_bytes. intros k Hk.
assert (HIN : In (AT t_stats, t_unwinding - t_stats) (ajunk_cf B ly S)).
{ unfold ajunk_cf. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto. }
destruct (range_vis_mbyte B ly (w_H W) mem (AT t_stats) (t_unwinding - t_stats) (a + Z.of_nat k - aeval B ly (AT t_stats))
  (proj1 (Forall_forall _ _) (amc_junk B ly S Hp _ M) _ HIN) ltac:(cbn [aeval]; lia)) as [b Hb].
exists b. replace (aeval B ly (AT t_stats) + (a + Z.of_nat k - aeval B ly (AT t_stats))) with (a + Z.of_nat k) in Hb by lia.
exact Hb.
Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (FSRealloc_S1_u.E2 ly regs ch rp jr1 jr2). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. reflexivity. Qed.
Lemma EaIM : ew E0 37 = w64 IMv. Proof. reflexivity. Qed.
Lemma PF : 4112 <= rp < 2 ^ 47 /\ rp mod 16 = 0 /\ 0 <= IMv - 0xac0c0 <= 8 * 32767 /\ IMv mod 8 = 0.
Proof.
assert (Hin : In (rp, nold) (ablocks B ly S)).
{ unfold ablocks. apply in_map_iff. exists (pp, nold). split; [reflexivity | exact HBLK]. }
apply In_ablocks in Hin as (k & Hk & _ & Hu & _).
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
assert (E : rp = ck_base B ly k + ck_rz k) by lia.
unfold in_app in G1.
assert (R1 : 4112 <= rp < 2 ^ 47) by lia.
assert (R2 : rp mod 16 = 0).
{ rewrite E. apply Z.mod_divide in G3 as [c Hc]; [|lia]. apply Z.mod_divide in G6 as [c' Hc']; [|lia].
  rewrite Hc, Hc'. apply Z.mod_divide; [lia|]. exists (c + c'). lia. }
assert (D32 : 0 <= rp / 2 ^ 32 <= 32767).
{ split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
unfold FSRealloc_S1_u.IMv.
split; [exact R1|]. split; [exact R2|]. split; [lia|].
apply Z.mod_divide; [lia|]. exists (88088 + rp / 2 ^ 32). lia.
Qed.
Lemma val_mem_mod8 : forall m a x, val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 (x mod 2 ^ 64).
Proof.
intros m a x H k Hk. rewrite (H k Hk). do 2 f_equal. rewrite <- (le_byte_eq x), <- (le_byte_eq (x mod 2 ^ 64)). unfold YG0f.le_byte.
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. reflexivity. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k d))).
Proof.
intros base a w k d x Hk Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m0 o.
Proof. intros a w v o Hv Ho Ha. apply vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply val_mem_vis; [exact Hv | lia]. Qed.
Ltac offw := first [ lia | apply off_img_high; unfold TFIB_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HI)))))); unfold kThreadObjSize, t_qc, t_unwinding, t_stats, t_cache in *; lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) FSRealloc_S1_u.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg in hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, S1, S2, T2, T4, T7.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
destruct PRE as (_ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold FSRealloc_S1_u.REG0, flit1, flit4, flit8, flits8, fatom8. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- ASTACK)); [rewrite E2; reflexivity | unfold ASTACK in *; lia | lia |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, ASTACK in *; lia | apply HPRES; exact Ha]. }
do 11 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; lia | | unfold SHADOW_OFF; cbn; lia | cbn; lia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 13 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; lia | cbn; lia].
replace (0x5ddef0 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TB); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. replace 0x5ff298 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; lia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; lia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP; unfold w64; f_equal; lia | unfold kStackSpan; lia | | unfold kStackSpan; cbn; lia | cbn; lia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; lia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; lia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_unwinding.
pose proof unwinding_val as U. unfold t_unwinding in U.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ U); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact U | cbn; lia | cbn; lia]. }
{   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 2864).
- apply (val_mem_writable _ _ _ _ Hjr1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw.
- apply (val_mem_writable _ _ _ _ Hjr2); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 38%nat 0 (jr1 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by lia; reflexivity
| pose proof (Z.mod_pos_bound jr1 (2 ^ 64)); lia | apply val_mem_mod8; exact Hjr1 | cbn; pose proof (Z.mod_pos_bound jr1 (2 ^ 64)); lia | cbn; lia].
- apply (chunk_atom _ _ 8 39%nat 0 (jr2 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by lia; reflexivity
| pose proof (Z.mod_pos_bound jr2 (2 ^ 64)); lia | apply val_mem_mod8; exact Hjr2 | cbn; pose proof (Z.mod_pos_bound jr2 (2 ^ 64)); lia | cbn; lia]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 FSRealloc_S1_u.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof HSP as [S1 S2].
pose proof (AFf0cfR.SX B ly S rd0 Hp M 2 6 _ _ eq_refl eq_refl ltac:(lia)) as DCT.
pose proof (AFf0cfR.SX B ly S rd0 Hp M 6 8 _ _ eq_refl eq_refl ltac:(lia)) as DCS.
pose proof (AFf0cfR.SX B ly S rd0 Hp M 2 8 _ _ eq_refl eq_refl ltac:(lia)) as DTS.
unfold zdisjoint in DCT, DCS, DTS. cbn [fst snd] in DCT, DCS, DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold FSRealloc_S1_u.REG0, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP.
rewrite E2, EaT, EaC. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, ASTACK in *.
fold sp0. rewrite !unsigned_lit_small by lia.
clear - S1 S2 hT1 hT2 hC1 hC2 hS1 hS2 hSP1 hSP2 hP1 hP2 Usp DCT DCS DTS CR CR0.
unfold TFIB_TP, TFIB_TSD, t_unwinding in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1.
repeat split;
first [ clear DCT DCS DTS hT1 hC1; lia
| clear - hT1 CR0; lia
| clear - hC1 CR0; lia
| clear - hC1 hC2 hT1 hT2 DCT; lia
| clear - hC1 hC2 S1 S2 hS1 hS2 Usp DCS; lia
| clear - hT1 hT2 S1 S2 hS1 hS2 Usp DTS; lia ].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms FSRealloc_S1_u.FFN).
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct PRE as (_ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. pose proof (lo_C_al ly LO) as CAL. unfold page_aligned in TAL, T3.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg, ASTACK in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, S1, S2, T2, T4, T7.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HL : 1 <= LENv <= 30).
{ unfold FSRealloc_S1_u.LENv, FSRealloc_S1_u.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0.
pose proof (unwind_of_chain_length 0x53c74 ((sp0, bv_unsigned (getr regs 1), bv_unsigned (getr regs 8)) :: ch)) as LEN.
destruct (sp0 + 16 <? ly_top ly); cbn [length]; lia. }
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [FSRealloc_S1_u.FFN f_atoms atoms_ok]. unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { pose proof PF as (PF1 & PF2 & _). apply (AF 10%nat rp); [rewrite (FSRealloc_S1_u.E10 ly regs ch rp jr1 jr2); exact HA0| | | |]. all: clear - PF1 PF2; first [lia | change (2 ^ 4) with 16; exact PF2]. }
split. { apply (AF 11%nat rn); [rewrite (FSRealloc_S1_u.E11 ly regs ch rp jr1 jr2); exact HA1| | | |]. all: clear - Hrn; unfold MALLOC_MAX in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 32%nat T); [exact EaT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |]. all: clear - CR0 hC1 hC2 CAL; first [lia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |]. all: clear - CR0 T1 T2 T3 T4 T7 hS1; unfold ly_bot, kStackSpan in *; first [lia | exact T3]. }
split. { apply (AF 36%nat LENv); [exact EaLEN| | | |]. all: clear - CR0 HL; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { pose proof PF as (_ & _ & PF3 & PF4). apply (AF 37%nat IMv); [exact EaIM| | | |]. all: clear - PF3 PF4; first [lia | change (2 ^ 3) with 8; exact PF4]. }
split; [|exact I]. { apply (AF 40%nat SHADOW_OFF); [exact EaSHB| | | |]. all: clear; unfold SHADOW_OFF; first [lia | reflexivity]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 FSRealloc_S1_u.SS0 (restrict (w_H W) (mkst regs (w64 0x5373c) mem (seg_rom tfibsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
rewrite restrict_mkst_fx. unfold FSRealloc_S1_u.SS0, FSRealloc_S1_u.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Theorem FH_ok : FSRealloc_S1_u.free_hyps W ly regs mem ch ii rp rn jr1 jr2.
Proof.
pose proof PRE as PRE'. destruct PRE' as (MM & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT & _). unfold spZ, raZ, s0Z in *. fold sp0 in Hal, Hlo, Hbot, Hhi, HPRES, Hch.
constructor.
- exact LO.
- exact IMG.
- exact HA0.
- exact HA1.
- pose proof PF as (PF1 & PF2 & _). exact (conj PF1 PF2).
- exact Hrn.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- destruct Hch as [R4096 _]. exact R4096.
- splits; lia.
- exact Hal.
- destruct Hch as [_ CH]. unfold frame0_ok, spZ, s0Z in CH. fold sp0 in CH. exact CH.
- exact ial_vals.
- exact IA1.
- exact U1.
- exact SEED_ok.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ FSRealloc_S1_u.WIN ly regs (aeval B ly (c_at c) + i) /\ ~ FSRealloc_S1_u.IZONE (aeval B ly (c_at c) + i) /\
0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (AFfy.Tfib_const_loc ly) c Hc) as K. unfold AFfy.const_loc_ok in K.
pose proof FH_ok as FH.
assert (LOW : forall a, AFfy.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ FSRealloc_S1_u.WIN ly regs (a + i) /\ ~ FSRealloc_S1_u.IZONE (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold AFfy.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/ (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
(SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
clear L. unfold FSRealloc_S1_u.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *.
change (65536 / 8) with 8192 in R. change (0x600000 / 8) with 0xc0000 in R.
split; [|lia]. destruct R as [R|[R|[R|R]]].
1-3: apply (FSRealloc_S1_u.notWIN_img W ly regs mem ch ii rp rn jr1 jr2 FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia.
apply (FSRealloc_S1_u.notWIN_shb W ly regs mem ch ii rp rn jr1 jr2 FH); unfold kLowShadowBeg, kHighMemBeg; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- pose proof (FSRealloc_S1_u.LYB W ly regs mem ch ii rp rn jr1 jr2 FH) as (LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [apply (FSRealloc_S1_u.notWIN_Thead W ly regs mem ch ii rp rn jr1 jr2 FH); lia|].
unfold FSRealloc_S1_u.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- pose proof (FSRealloc_S1_u.LYB W ly regs mem ch ii rp rn jr1 jr2 FH) as (_ & _ & _ & _ & _ & _ & LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [apply (FSRealloc_S1_u.notWIN_C W ly regs mem ch ii rp rn jr1 jr2 FH); lia|].
unfold FSRealloc_S1_u.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof (FSRealloc_S1_u.LYBD W ly regs mem ch ii rp rn jr1 jr2 FH) as (HD1 & HD2 & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HD1, HD2.
split; [apply (FSRealloc_S1_u.notWIN_D W ly regs mem ch ii rp rn jr1 jr2 FH); lia|].
unfold FSRealloc_S1_u.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.
Local Notation ARXs := (fun S' (W' : world tfibsegs) mem' md' => RGcfLaws.ARXqA B Hp (as_inst B) ly S' W' mem' md').
Lemma FINH : forall W' c', FSRealloc_S1_t.at_PA W ly regs mem md ch W' c' -> pa_leaf B ARXs ly S W regs mem md tr (tt, s1) W' c'.
Proof.
intros W' c' HR.
destruct PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT & HSEC & HERR & HBUD & HBR & _).
destruct HR as (-> & regs' & mem' & mat & -> & PAST & PBF & MEQ' & UNW & PRES' & PRST).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'.
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
(* the machine's memory changed only on D: the stack window, T + t_stats .. T + t_unwinding, the internal allocator *)
assert (AGm : forall a, 0 <= a < 2 ^ 64 -> ~ AFf0cfR.D B ly ASTACK sp0 a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha ND. apply (proj1 MEQ' (Z_to_bv 64 a)); rewrite unsigned_lit_small by exact Ha.
- intros [X|[X|X]]; apply ND; [right; left; exact X | left; unfold AFf0cfR.DT; clear - X; unfold t_stats, t_unwinding in *; lia | left; unfold AFf0cfR.DT; clear - X; unfold t_stats, t_unwinding in *; lia].
- intros X. apply ND. right; right. unfold FSRealloc_S1_u.IZONE in X. unfold AFf0cfR.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). exact X. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFf0cfR.D B ly ASTACK sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. exact (AGm a Ha ND). }
assert (VISm : forall a, aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (NIMG : ~ (0x10000 <= a' < 0x600000)).
{ intros X. apply (tfib_rom_all a' X). rewrite Ex. exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
destruct (EM (sp0 - ASTACK) sp0 a') as [C1|C1]. { exact (PRX mem' (PRES' a' C1) E'). }
destruct (EM (T + t_unwinding) (T + t_unwinding + 1) a') as [C2|C2].
{ pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a' in U by lia. rewrite Ex, Hx, E', ROM in U. discriminate. }
destruct (EM (T + 2856) (T + 2872) a') as [C3|C3]. { exact (PRX mem' (PRST a' C3) E'). }
destruct (EM TFIB_IAL_LO TFIB_IAL_HI a') as [C4|C4]; [apply NIMG; unfold TFIB_IAL_LO, TFIB_IAL_HI in C4; lia|].
destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a') as [C5|C5]; [apply NIMG; unfold TFIB_IAL_FLAG in C5; lia|].
rewrite (proj1 MEQ' x) in E'; [congruence | |].
- intros [X|[X|X]]; [apply C1 | apply C2 | apply C3]; exact X.
- unfold FSRealloc_S1_u.IZONE. tauto. }
assert (VIS : forall a, rd a <> None -> rd' a <> None) by exact VISm.
assert (HSKm : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate).
assert (C1 : ~ (sp0 - ASTACK <= a < sp0)) by (intros C1; exact (PRX mem' (PRES' a C1))).
assert (C2 : ~ (T + t_unwinding <= a < T + t_unwinding + 1)).
{ intros C2. pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a in U by lia.
rewrite (seg_rom_none_high a ltac:(clear - Ha; unfold TFIB_IMG_END, kLowShadowBeg, kHighShadowEnd in *; lia)) in U. fold x in U. rewrite Hx in U. discriminate. }
assert (C3 : ~ (T + 2856 <= a < T + 2872)) by (intros C3; exact (PRX mem' (PRST a C3))).
apply (proj1 MEQ' x); rewrite Ux.
- intros [X|[X|X]]; [apply C1 | apply C2 | apply C3]; exact X.
- unfold FSRealloc_S1_u.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia. }
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (val_mem_aview _ _ _ _ _ 0 UNW ltac:(lia)). }
assert (VA : forall a, 0 <= a < SHADOW_OFF -> rd' a = aview tfibsegs (w_H W) mem' a) by (intros a Ha; reflexivity).
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B s1) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ destruct MEQ' as [_ IP]. unfold FSRealloc_S1_u.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. change (st_internal_inited s1) with true. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
split.
- apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. rewrite VA by (unfold TFIB_IAL_FLAG, SHADOW_OFF; lia). apply (val_mem_aview _ _ _ _ _ 0 I1). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. rewrite VA by (unfold TFIB_IAL_FLAG, SHADOW_OFF; lia). apply (val_mem_aview _ _ _ _ _ 0 I2). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
intros kk Hkk. rewrite VA by (unfold TFIB_IAL_W, SHADOW_OFF; lia). exact (val_mem_aview _ _ _ _ _ kk I3 Hkk). }
apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
intros kk Hkk. rewrite VA by (unfold TFIB_IAL_W, SHADOW_OFF; lia). exact (val_mem_aview _ _ _ _ _ kk I4 Hkk). }
- assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> rd' a0 = Some 0).
{ intros a0 Ha0. rewrite VA by (unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_HI, SHADOW_OFF in *; lia). unfold aview. rewrite (I5 a0 Ha0). reflexivity. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TB); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (amc_const B ly S Hp rd M) c Hc)|].
intros i Hi. subst rd rd'. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). apply aview_same.
apply (proj1 MEQ' (Z_to_bv 64 _)); rewrite unsigned_lit_small by exact X3; [exact X1 | exact X2]. }
pose proof (AFf0cfR.free_finn_ARcf B TB ly S Hp W mem md mem' mat ASTACK sp0 HAR IMG ltac:(unfold ASTACK; lia) HSP' AG VIS NEW_unw IAL CONST' HSKm) as HARcf.
assert (ERRK : forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))).
{ intros i Hi. rewrite (ts_errno _ TB). unfold w64. apply AGm; [unfold TFIB_ERRNO; lia|].
  pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _).
  pose proof HSP' as [SPa SPb].
  unfold AFf0cfR.D, AFf0cfR.DT, AFf0cfR.DS, AFf0cfR.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB).
  unfold zone3, zone3cases in hT1.
  unfold TFIB_ERRNO, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, t_stats, t_unwinding, ASTACK in *.
  lia. }
assert (MNK : YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem').
{ intros MN. apply (memnorm_addr mem mem' MN). intros x b E.
  pose proof (u64_range x) as Ux. set (a := bv_unsigned x) in *.
  assert (Ex : Z_to_bv 64 a = x) by (subst a; apply Z_to_bv_bv_unsigned).
  pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & _).
  destruct (EM (sp0 - ASTACK) sp0 a) as [C1|C1].
  { left. assert (Ha : spZ regs - ASTACK <= a < spZ regs) by exact C1. destruct (HPRES a Ha) as [_ Hb]. rewrite Ex in Hb. exact Hb. }
  destruct (EM (T + t_stats) (T + t_unwinding) a) as [C2|C2].
  { left.
    assert (HIN : In (AT t_stats, t_unwinding - t_stats) (ajunk_cf B ly S)).
    { unfold ajunk_cf. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto. }
    destruct (range_vis_mbyte B ly (w_H W) mem (AT t_stats) (t_unwinding - t_stats) (a - aeval B ly (AT t_stats))
      (proj1 (Forall_forall _ _) (amc_junk B ly S Hp _ M) _ HIN) ltac:(cbn [aeval]; lia)) as [b0 Hb0].
    replace (aeval B ly (AT t_stats) + (a - aeval B ly (AT t_stats))) with a in Hb0 by lia.
    destruct (mbyte_off_apresent (w_H W) mem a b0 (zone3_off_img T kThreadObjSize a hT1 ltac:(unfold t_stats, t_unwinding, kThreadObjSize in *; lia)) Hb0) as [_ Hm].
    rewrite Ex in Hm. exact Hm. }
  destruct (EM (T + t_unwinding) (T + t_unwinding + 1) a) as [C3|C3].
  { left. pose proof unwinding_val as U0. pose proof (U0 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U.
    replace (ly_T ly + t_unwinding) with a in U by lia.
    destruct (mbyte_off_apresent (w_H W) mem a _ (zone3_off_img T kThreadObjSize a hT1 ltac:(unfold t_unwinding, kThreadObjSize in *; lia)) U) as [_ Hm].
    rewrite Ex in Hm. exact Hm. }
  destruct (EM TFIB_IAL_LO TFIB_IAL_HI a) as [C4|C4].
  { right. apply rw_wview. fold a. unfold TFIB_IAL_LO, TFIB_IAL_HI in C4. lia. }
  destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a) as [C5|C5].
  { right. apply rw_wview. fold a. unfold TFIB_IAL_FLAG in C5. lia. }
  left. exists b. rewrite <- E. rewrite <- Ex. symmetry. apply AGm; [exact Ux|].
  unfold AFf0cfR.D, AFf0cfR.DT, AFf0cfR.DS, AFf0cfR.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB).
  intros [X|[X|[X|X]]]; [| exact (C1 X) | exact (C4 X) | exact (C5 X)].
  destruct (Z.lt_ge_cases a (T + t_unwinding)); [exact (C2 ltac:(lia)) | exact (C3 ltac:(lia))]. }
split; [reflexivity|]. split; [reflexivity|].
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split; [reflexivity|].
split; [|split; [exact PAST | split; [intros i Hi; exact (PBF i Hi) | split; [|split; [exact (qmeter_cf_tight _ HQT) | exact (conj ERRK MNK)]]]]].
2:{
intros a Ha. apply aview_same. pose proof FH_ok as FH.
pose proof (FSRealloc_S1_u.LYB W ly regs mem ch ii rp rn jr1 jr2 FH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & T3 & T4 & T5).
unfold spZ in Ha. fold sp0 in Ha.
apply (proj1 MEQ' (Z_to_bv 64 a)); rewrite unsigned_lit_small by (clear - Ha Usp T3 T4; unfold kHighMemEnd in *; lia).
- exact (FSRealloc_S1_u.WIN_not_high W ly regs mem ch ii rp rn jr1 jr2 FH a Ha).
- intros Hz. unfold FSRealloc_S1_u.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Hz. clear - Hz Ha HSP' T5. destruct HSP' as [S1 _]. unfold kHighMemBeg, ASTACK in *. lia. }
split; [|split; [apply wle_refl | split; [apply same_io_wvb | split; [|split]]]].
-
cbv beta. apply (RGcfLaws.ARXqA_intro B); [reflexivity | exact HARcf | exact (YGcfXs.ARcf_xsm _ _ _ _ _ _ _ _ HARcf) | exact (qmeter_cf_tight _ HQT)].
- intros a Ha NO NO' NS. apply aview_same. apply AGm; [exact Ha|]. intros HD.
destruct (AFf0cfR.D_owned_cf B TB ly S rd Hp M ASTACK sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch; left; exact O].
- (* the raw frame: AGm off D, and D is owned or realloc's window *)
intros x NO NS. pose proof (u64_range x) as Ux.
replace x with (Z_to_bv 64 (bv_unsigned x)) by apply Z_to_bv_bv_unsigned.
apply AGm; [exact Ux|]. intros HD.
destruct (AFf0cfR.D_owned_cf B TB ly S rd Hp M ASTACK sp0 HSP' IMG (bv_unsigned x) (proj1 Ux) HD) as [O|O];
[exact (NO O) | apply NS; unfold ascratch; left; exact O].
- exact PRES'.
Qed.
Theorem pa_arm :
amreal tfibsegs (free_cf PNull tr S) W (cfg_at tfibsegs 0x5373c regs mem md) (pa_leaf B ARXs ly S W regs mem md tr).
Proof.
assert (SPLIT : amreal tfibsegs (ret tt s1) W (cfg_at tfibsegs 0x5373c regs mem md) (pa_leaf B ARXs ly S W regs mem md tr) ->
amreal tfibsegs (free_cf PNull tr S) W (cfg_at tfibsegs 0x5373c regs mem md) (pa_leaf B ARXs ly S W regs mem md tr)).
{ intros MAIN. unfold free_cf. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
- replace (set_nev (st_nev S + 1) S) with s1; [exact MAIN|]. unfold s1. generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. subst. reflexivity.
- exact MAIN. }
apply SPLIT. clear SPLIT. cbn [ret amreal].
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- exact (FSRealloc_S1_t.segA rp rn jr1 jr2 W ly regs mem md ch ii (m_vm_materialized md) FH_ok).
- intros W' c' _ HR. exact (FINH W' c' HR).
Qed.
End j.
Lemma blk_out : forall i, 0 <= i < req_size nold -> 0 <= rp + i < 2 ^ 64 /\ ~ aowned B ly S (rp + i) /\ ~ ascratch B ASTACK regs (rp + i).
Proof.
intros i Hi.
assert (Hin : In (rp, nold) (ablocks B ly S)) by (unfold ablocks; apply in_map_iff; exists (pp, nold); split; [reflexivity | exact HBLK]).
destruct (AR_blocks_law_ok_cf tfibsegs B ly S Hp W mem md rp nold (proj1 PRE) Hin) as (P16 & P4096 & PC & PA & PP & _).
pose proof Hin as Hin'. apply In_ablocks in Hin' as (k & Hk & _ & Hu & Hr).
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (AFf0cfR.ZCH B ly S rd0 Hp M IMG k Hk) as Z.
pose proof (lo_stk_ceil ly LO) as SC. pose proof HSP as [SP1 SP2].
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
rewrite Hr in G7, G8.
unfold ASAN_CEIL in *.
split; [lia|]. split; [exact (proj2 (PP (rp + i) ltac:(lia)))|].
unfold ascratch. rewrite (ts_errno B TB). unfold zone3, zone3cases, TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASTACK in *.
unfold sp0 in *. unfold spZ. lia.
Qed.
Variable nmax : Z.
Hypothesis HROOM : ly_bot ly + 4096 < spZ regs.
Lemma seg_pre_cf : xs_placed_cf ly S -> 0 <= rn < nmax ->
amreal tfibsegs (free_cf PNull tr S) W (cfg_at tfibsegs 0x5373c regs mem md)
(fun r W1 c1 => exists inst so bp regsA memA mdA,
c1 = cfg_at tfibsegs 0x325b8 regsA memA mdA /\
(YGcfRmodel.rpre_cfr B (snd r) rn -> blocks_bytes (snd r) + rn <= LIVE_MAX -> admits (as_universe B) tr (snd r) ->
 YGcfMallocCompose.malloc_apre_cf tfibsegs B nmax 8 1 1 (fun Hp0 inst0 ly0 S0 W0 mem0 md0 => RGcfLaws.ARXqA B Hp0 inst0 ly0 S0 W0 mem0 md0)
 Hp inst so bp ly (snd r) W1 regsA memA mdA rn tr) /\
wle W W1 /\ same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
YGcfMallocComposeKeep.ikeep_mn_cf tfibsegs B ly S regs W mem W1 memA /\ YGcfMallocCompose.errno_kept_cf B mem memA /\
RGcfK.K1A B ly S Hp W regs mem md pp nold rn ch (snd r) W1 regsA memA mdA).
Proof.
intros HXS0 Hnm.
destruct (junk_T (T + 2856) ltac:(unfold t_stats; lia) ltac:(unfold t_unwinding; lia)) as [jr1 Hjr1].
destruct (junk_T (T + 2864) ltac:(unfold t_stats; lia) ltac:(unfold t_unwinding; lia)) as [jr2 Hjr2].
eapply amreal_mono; [|exact (pa_arm jr1 jr2 Hjr1 Hjr2)].
intros r W1 c1 (Es & EW & regs' & mem' & md' & Ec & (HARU & HWLE & HIO & HFR & HFRw & HPR) & PAST & PBF & _ & _ & ERRK & MNK).
subst W1 c1.
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT & _).
pose proof HSP as [SP1 SP2].
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (SP0 : spZ regs = sp0) by reflexivity.
pose proof HROOM as HB0. rewrite SP0 in Hal, HB0.
assert (HL : (1 <= length tr <= 30)%nat).
{ pose proof (unwind_of_chain_length 0x53c74 ((spZ regs, raZ regs, s0Z regs) :: ch)) as UL.
  unfold tr, call_trace. destruct (frame0_ok ly regs); [exact UL | cbn; lia]. }
destruct PAST as (PLEN & PREG & PFR). rewrite Forall_forall in PREG, PFR.
assert (GL : forall (r0 : bv 5) z, In (r0, SLit z) PAREGS -> getr regs' r0 = Z_to_bv 64 z).
{ intros r0 z Hin. pose proof (PREG (r0, SLit z) Hin) as X. cbn [fst snd sv_denot] in X. exact X. }
assert (GS : forall (r0 : bv 5) (k : nat) (rk : bv 5) d, In (r0, SOff k d) PAREGS -> Z.of_nat k = bv_unsigned rk ->
  getr regs' r0 = Z_to_bv 64 (bv_unsigned (getr regs rk) + d)).
{ intros r0 k rk d Hin Hk. pose proof (PREG (r0, SOff k d) Hin) as X. cbn [fst snd sv_denot] in X. rewrite (ew_Ereg_nat regs [] k rk Hk) in X. exact X. }
assert (GK : forall (r0 : bv 5) (k : nat), In (r0, SOff k 0) PAREGS -> Z.of_nat k = bv_unsigned r0 -> getr regs' r0 = getr regs r0).
{ intros r0 k Hin Hk. rewrite (GS r0 k r0 0 Hin Hk), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (R1 : getr regs' 1 = Z_to_bv 64 0x33058) by (apply GL; unfold PAREGS; cbn [In]; tauto).
assert (R2 : getr regs' 2 = Z_to_bv 64 (sp0 + -2208)) by (apply (GS 2%bv 2%nat 2%bv); [unfold PAREGS; cbn [In]; tauto | reflexivity]).
assert (R3 : getr regs' 3 = getr regs 3) by (apply (GK 3%bv 3%nat); [unfold PAREGS; cbn [In]; tauto | reflexivity]).
assert (R4 : getr regs' 4 = Z_to_bv 64 TFIB_TP) by (apply GL; unfold PAREGS; cbn [In]; tauto).
assert (R8 : getr regs' 8 = Z_to_bv 64 (sp0 + -2136)) by (apply (GS 8%bv 2%nat 2%bv); [unfold PAREGS; cbn [In]; tauto | reflexivity]).
assert (R9 : getr regs' 9 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 0)) by (apply (GS 9%bv 10%nat 10%bv); [unfold PAREGS; cbn [In]; tauto | reflexivity]).
assert (R10 : getr regs' 10 = Z_to_bv 64 TFIB_INST) by (apply GL; unfold PAREGS; cbn [In]; tauto).
assert (R11 : getr regs' 11 = getr regs 11) by (apply (GK 11%bv 11%nat); [unfold PAREGS; cbn [In]; tauto | reflexivity]).
assert (R12 : getr regs' 12 = Z_to_bv 64 8) by (apply GL; unfold PAREGS; cbn [In]; tauto).
assert (R13 : getr regs' 13 = Z_to_bv 64 (sp0 + -2136)) by (apply (GS 13%bv 2%nat 2%bv); [unfold PAREGS; cbn [In]; tauto | reflexivity]).
assert (R14 : getr regs' 14 = Z_to_bv 64 1) by (apply GL; unfold PAREGS; cbn [In]; tauto).
assert (R15 : getr regs' 15 = Z_to_bv 64 1) by (apply GL; unfold PAREGS; cbn [In]; tauto).
assert (R18 : getr regs' 18 = Z_to_bv 64 TFIB_INST) by (apply GL; unfold PAREGS; cbn [In]; tauto).
assert (R19 : getr regs' 19 = Z_to_bv 64 (bv_unsigned (getr regs 11) + 0)) by (apply (GS 19%bv 11%nat 11%bv); [unfold PAREGS; cbn [In]; tauto | reflexivity]).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R9, R19.
assert (RK : forall k, 23 <= k <= 27 -> getr regs' (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
{ intros k Hk. assert (Hc : k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
  destruct Hc as [->|[->|[->|[->| ->]]]].
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). apply (GK _ 23%nat); [unfold PAREGS; cbn [In]; tauto | reflexivity].
  - replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). apply (GK _ 24%nat); [unfold PAREGS; cbn [In]; tauto | reflexivity].
  - replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). apply (GK _ 25%nat); [unfold PAREGS; cbn [In]; tauto | reflexivity].
  - replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). apply (GK _ 26%nat); [unfold PAREGS; cbn [In]; tauto | reflexivity].
  - replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). apply (GK _ 27%nat); [unfold PAREGS; cbn [In]; tauto | reflexivity]. }
assert (SPA : spZ regs' = sp0 - 2208).
{ unfold spZ. rewrite R2. rewrite unsigned_lit_small; [lia|]. unfold ASTACK, kHighMemBeg in *. lia. }
assert (FL : forall o z, In (o, SLit z) PAFRAMES -> val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 + o) 8 (bv_unsigned (Z_to_bv 64 z))).
{ intros o z Hin. exact (PFR (o, SLit z) Hin). }
assert (FK : forall o (k : nat) (rk : bv 5), In (o, SOff k 0) PAFRAMES -> Z.of_nat k = bv_unsigned rk ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 + o) 8 (bv_unsigned (getr regs rk))).
{ intros o k rk Hin Hk. pose proof (PFR (o, SOff k 0) Hin) as X. cbn [fst snd sv_denot] in X.
  rewrite (ew_Ereg_nat regs [] k rk Hk), Z.add_0_r, Z_to_bv_bv_unsigned in X. exact X. }
assert (VSO : val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 + -2136) 8 (sp0 - 2120)).
{ pose proof (PFR (-2136, SOff 2 (-2120)) ltac:(unfold PAFRAMES; cbn [In]; tauto)) as X. cbn [fst snd sv_denot] in X.
  rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl) in X. fold sp0 in X. rewrite unsigned_lit_small in X; [replace (sp0 - 2120) with (sp0 + -2120) by lia; exact X|].
  unfold ASTACK, kHighMemBeg in *. lia. }
assert (VLEN : val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 + -2128) 8 (Z.of_nat (length tr))) by exact PLEN.
exists (as_inst B), (sp0 - 2136), (sp0 - 2120), regs', mem', md'.
split; [reflexivity|].
split.
{ intros HRA HBB HU. unfold YGcfMallocCompose.malloc_apre_cf, AllocG.alloc_pre.
split; [exact HARU|].
split; [exact HRA|].
split; [rewrite R1; apply YK0s.ret_ok_even; reflexivity|].
split; [unfold raZ; rewrite R1, unsigned_lit_small by lia; lia|].
split; [rewrite SPA; replace (sp0 - 2208) with (sp0 + (-138) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [rewrite SPA; unfold AllocG.AFSTACK_G, ASTACK in *; lia|].
split; [rewrite SPA; lia|].
split; [rewrite SPA; lia|].
split; [intros a Ha; apply HPR; rewrite SP0; rewrite SPA in Ha; unfold AllocG.AFSTACK_G, ASTACK in *; lia|].
split; [rewrite R3; exact Hgp|].
split; [rewrite R4, (ts_tp _ TB); reflexivity|].
split; [rewrite R10, (ts_inst _ TB); reflexivity|].
split; [rewrite R11; exact HA1|].
split; [rewrite R12; reflexivity|].
split; [rewrite R13; unfold w64; f_equal; lia|].
split; [rewrite R14; reflexivity|].
split; [rewrite R15; reflexivity|].
split; [rewrite SPA; lia|].
split; [lia|].
split; [replace (sp0 - 2136) with (sp0 + (-267) * 8) by lia; rewrite Z_mod_plus_full; apply (mod0_factor _ 8 2); [lia | exact Hal]|].
split; [rewrite SPA; lia|].
split; [lia|].
split; [replace (sp0 - 2120) with (sp0 + (-265) * 8) by lia; rewrite Z_mod_plus_full; apply (mod0_factor _ 8 2); [lia | exact Hal]|].
split; [exact HL|].
split; [replace (sp0 - 2136) with (sp0 + -2136) by lia; exact VSO|].
split; [replace (sp0 - 2136 + 8) with (sp0 + -2128) by lia; exact VLEN|].
split; [intros i Hi; replace (sp0 - 2120 + 8 * Z.of_nat i) with (spZ regs - 2120 + 8 * Z.of_nat i) by (rewrite SP0; lia); exact (PBF i Hi)|].
split; [exact HU|].
split; [exact Hnm | exact HBB]. }
split; [exact HWLE|].
split; [exact HIO|].
split; [unfold RGtop.rin; rewrite SPA, SP0; unfold AllocG.AFSTACK_G, ASTACK; lia|].
split.
{ split; [|split; [exact HFRw | exact MNK]].
  intros a Ha NO NS. apply (HFR a Ha NO); [rewrite Es; exact NO | exact NS]. }
split; [exact ERRK|].
unfold RGcfK.K1A, RGthinS.K1r.
split; [rewrite SPA, SP0; reflexivity|].
split; [rewrite R1; reflexivity|].
split; [rewrite R8, SP0; unfold w64; f_equal; lia|].
split; [rewrite R13, SP0; unfold w64; f_equal; lia|].
split; [exact R9|].
split; [rewrite R18; reflexivity|].
split; [exact R19|].
split.
{ unfold RGthinS.kregs. intros r0 Hr0. cbn [In] in Hr0.
  destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
  - exact R3.
  - rewrite R4, Htp, (ts_tp _ TB). reflexivity.
  - pose proof (RK 23 ltac:(lia)) as X. replace (Z_to_bv 5 23) with (23%bv : bv 5) in X by (apply bv_eq; reflexivity). exact X.
  - pose proof (RK 24 ltac:(lia)) as X. replace (Z_to_bv 5 24) with (24%bv : bv 5) in X by (apply bv_eq; reflexivity). exact X.
  - pose proof (RK 25 ltac:(lia)) as X. replace (Z_to_bv 5 25) with (25%bv : bv 5) in X by (apply bv_eq; reflexivity). exact X.
  - pose proof (RK 26 ltac:(lia)) as X. replace (Z_to_bv 5 26) with (26%bv : bv 5) in X by (apply bv_eq; reflexivity). exact X.
  - pose proof (RK 27 ltac:(lia)) as X. replace (Z_to_bv 5 27) with (27%bv : bv 5) in X by (apply bv_eq; reflexivity). exact X. }
split.
{ unfold RGthinS.rt_frames. rewrite SP0.
  split; [replace (sp0 - 2152) with (sp0 + -2152) by lia; pose proof (FL (-2152) 0x53ce4 ltac:(unfold PAFRAMES; cbn [In]; tauto)) as X;
    rewrite unsigned_lit_small in X by lia; exact X|].
  split; [replace (sp0 - 8) with (sp0 + -8) by lia; exact (FK (-8) 1%nat 1%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl)|].
  split; [replace (sp0 - 16) with (sp0 + -16) by lia; exact (FK (-16) 8%nat 8%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl)|].
  split; [replace (sp0 - 24) with (sp0 + -24) by lia; exact (FK (-24) 9%nat 9%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl)|].
  split; [replace (sp0 - 32) with (sp0 + -32) by lia; exact (FK (-32) 18%nat 18%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl)|].
  split; [replace (sp0 - 40) with (sp0 + -40) by lia; exact (FK (-40) 19%nat 19%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl)|].
  split; [replace (sp0 - 48) with (sp0 + -48) by lia; exact (FK (-48) 20%nat 20%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl)|].
  split; [replace (sp0 - 56) with (sp0 + -56) by lia; exact (FK (-56) 21%nat 21%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl)|].
  replace (sp0 - 64) with (sp0 + -64) by lia; exact (FK (-64) 22%nat 22%bv ltac:(unfold PAFRAMES; cbn [In]; tauto) eq_refl). }
split.
{ rewrite SP0. replace (sp0 - 2168) with (sp0 + -2168) by lia. pose proof (FL (-2168) 0x32fdc ltac:(unfold PAFRAMES; cbn [In]; tauto)) as X.
  rewrite unsigned_lit_small in X by lia. exact X. }
split; [unfold RGtop.rwin; exact HPR|].
intros i Hi. destruct (blk_out i Hi) as (Hr & NO & NS).
apply (HFR (rp + i) Hr NO); [rewrite Es; exact NO | exact NS].
Qed.
End f.
End b.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_A.
Theorem rw_pre_A : forall (B : asyms), TfibSyms B ->
forall nmax ly S Hp W regs mem md p n_old n ch,
YGcfReallocCompose.rentry_cf tfibsegs B ly S Hp W regs mem md p n_old n ch -> ly_bot ly + 4096 < spZ regs -> xs_placed_cf ly S ->
YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
amreal tfibsegs (free_cf PNull (YGcfReallocCompose.rtr_cf ly regs ch) S) W (cfg_at tfibsegs cf_pc_wrap_realloc regs mem md)
(fun r W1 c1 => exists inst so bp regsA memA mdA,
  c1 = cfg_at tfibsegs cf_pc_allocate regsA memA mdA /\
  (YGcfRmodel.rpre_cfr B (snd r) n -> blocks_bytes (snd r) + n <= LIVE_MAX -> admits (as_universe B) (YGcfReallocCompose.rtr_cf ly regs ch) (snd r) ->
   YGcfMallocCompose.malloc_apre_cf tfibsegs B nmax 8 1 1 (fun Hp0 inst0 ly0 S0 W0 mem0 md0 => RGcfLaws.ARXqA B Hp0 inst0 ly0 S0 W0 mem0 md0)
   Hp inst so bp ly (snd r) W1 regsA memA mdA n (YGcfReallocCompose.rtr_cf ly regs ch)) /\
  wle W W1 /\ same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
  YGcfMallocComposeKeep.ikeep_mn_cf tfibsegs B ly S regs W mem W1 memA /\ YGcfMallocCompose.errno_kept_cf B mem memA /\
  RGcfK.K1A B ly S Hp W regs mem md p n_old n ch (snd r) W1 regsA memA mdA).
Proof.
intros B TB nmax ly S Hp W regs mem md p n_old n ch RE HROOM HXS HRP Hnm.
destruct RE as (PRE & HBLK & HA0 & HNH & HA1 & Hn & Hlive & HU).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (amc_tsd B ly S Hp _ (proj1 (proj1 PRE))); apply (ts_tsd _ TB)).
assert (Hrn : 1 <= n < 2 ^ 30) by (pose proof cf_malloc_max_lt30; lia).
change (@cf_pc_wrap_realloc CfImg_A) with 0x5373c. change (@cf_pc_allocate CfImg_A) with 0x325b8.
unfold YGcfReallocCompose.rtr_cf. change (@cf_pc_realloc_ra0 CfImg_A) with 0x53c74.
eapply (seg_pre_cf B TB Hp ly S W regs mem md p n_old n ch).
all: first [ exact PRE | exact HBLK | exact HA0 | exact HA1 | exact Hrn | exact tfib_ialloc_ok | exact tfib_unwind_ok | exact HTSD
           | exact HROOM | exact HXS | exact Hnm ].
Qed.
End c.
