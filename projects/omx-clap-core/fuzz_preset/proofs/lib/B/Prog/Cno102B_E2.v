(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1165 of its 1242 lines of code are new or changed and 437 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): SEGMENT CB2
   (Copies) of the re-walk of check_no_overread (cno, entry B' 0x819f0 = slot 201), row R7-4 (a Theorem Labs lane's
   CB2, brief, the internal file brief-r74.md; plan, the internal file PLAN-cno-caw-102.md 5.2 row "CB2 Copies |
   0x81b80 -> 0x81bbc").
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (by path, ON THE KIT'S CUT a working branch 7cdbb61b5fa0, at the worktree's base
   0e85941c7687; every path but this file is that head's blob):
     SHARED CONTRACT lib/B/Prog/Cno102B_Base.v 06098b64f859 (cnb_pre CTX0 D, no DW, with the entry room wild_room and
     its two position-free pkR counts; cnb_base .. k wk over the budgeted journal cnb_J D wk, wk = 0 at both cuts here;
     cnb_at_copy with cnb_prog D [], cnb_ex_init with cnb_prog D (cnb_cevs ..) and `own0 <> 0 -> cnb_cdead D`; the
     progress fact cnb_prog, cnb_cevs, cnb_pre_mid with g_own_ran_out through the ledger, cnb_copy, cnb_cblks,
     cnb_S1_bounds, cnb_ck_cno_evs).
     STEP KIT lib/B/Prog/Cno102B_Ro.v c1b5ec3f8fff (on the same head): the hand steps
     cnb_hs_addi / cnb_hs_call and their closed decode checks cnb_is_addi, cnb_base_mat, cnb_entry_facts, cnb_slot_agree,
     cnb_regsat_*, ro_* helpers (ro_from: a conjunct by its type), cnb_stk_val, cnb_off_val, cnb_pc4, cnb_prog_app /
     cnb_prog_eq, the journal's cnb_J_rebase / cnb_J_fixed (cited, never restated).
     The kit text tpadded_specX: lib/A/PRH_FnCheck.v c40cf3fdcd2a :954- (a FIXED-trace text, fpostm), its post-implication
     position form (P0: no event, the position kept; P1: HMal (size + 16)), its OUTCOME clause (:970-978: at a model
     run and position whose next event is the copy's raw malloc, a consumer event, res <> 0), its P1 ceiling
     res + size + 16 <= alloc_ceiling, g_most / g_own_ran_out carried as ledger fields; ck_cno_copies (:264-266);
     PRH_Base.v ef7c8ca98529 (prh_ledger .. ran most own, prh_run_at / prh_run_at_app_iff, prh_cons_from /
     prh_cons_from_sub, src_rd, kept_at, the ledger's named projections).
     LISTING lib/B/Listing_prog.v c97cc46b3e13 (slots 301-316 = offsets 400-460 of cno; PCall AS_padded at 412 / 432
     / 452, checked by the closed lemmas cb2_c4xx below).
     ENGINE: YCbqGcallW.v aj_call_xW / fpostW_x_of_apost, YCbqG.v 219748197d6b ajournal_x / ajournal_x_exec and the
     journal's projections ajx_*, YCbqGwild.v 0c63874858e4 (through the kit's rebase / unbase), YC80x.v SRr_step_inv
     (the two `sd` hand steps carry P through the runner's srr_inv_laws), YK14.v step_sd_at, YK1b.v store_ok_of_all,
     YK0u.v wbytes_inside / wbytes_outside; the cf instance (the walk's allocator relation ARcf with the error-buffer
     extents placed, YGcallcf.v AR_laws_x_xs over a Theorem Labs lane's AR_laws_ok_cf, YG0lawscf.v), its shadow law
     AR_shadow_law_ok_cf (YG0sshcf.v), its zero-shadow law alc_zshadow and symbol facts aso_zshadow; S1Ledger.v
     prh_ledger_kept_aview / prh_ablocks_nonneg_cf. The instance is CnoB102f's (Cno102B_F.v): CfParams_preset,
     prh_room_live_a8, ARcfx.
   THE SEGMENT (DERIVED byte offsets inside check_no_overread):
     400 `li a2, 0x31`  404 `mv a0, s8`  408 `mv a1, s7`  412 `jal padded` -> 416
     416 `mv s9, a0`    420 `li a2, 0x32`  424 `mv a0, s8`  428 `mv a1, s7`  432 `jal padded` -> 436
     436 `sd a0, 0x18(s1)`  440 `mv a0, s8`  444 `mv a1, s7`  448 `li a2, 0`  452 `jal padded` -> 456
     456 `sd a0, 0x10(s1)`  460 CNB_INIT.
   WHAT THE SEGMENT DOES: three padded (data, size, fill) calls through the kit's text; each P1 arm (a fresh RAW block of
   size + 16, not a harness block) extends the progress fact cnb_prog by its event HMal (size + FUZZ_PAD), a P0 arm
   (NULL; g_own_ran_out = 1) by none (cnb_prog_app over padded's post-implication and its block permutation). Between
   the calls the input's src_rd is RE-DERIVED at the call's post state (padded's text gives
   back bytes_at only): its bytes from the text, its shadow facts from the state's own laws through cnb_pre's home
   (prhReader_home): a ledger harness block (AR_shadow_law_ok_cf past the head), a registered read-only global or an
   image string (alc_zshadow, the const-shadow cells alx_const_cells, and the image hull IMG_SHADOW below), or an
   allocator block that is not a harness block (AR_shadow_law_ok_cf at hd_skip = 0). The copies cross the later calls
   by the callee journal's block clause and the same shadow law.
   PADDED'S LIVE COUNTS (tpadded_specX's entry pair `sec_cnt S <= LSEC + DRV /\ ccnt24 S <= L24 + DRV`, :959-960) at each
   call's OWN state S, from no position (the cut binds none): cnb_prog gives rs_live S ~ hlive_from (entry's
   live set) E for the k <= 2 granted copies' events E = HMal^k, E is a prefix of ck_cno_evs .. None None None (its C3,
   cnb_ck_cno_evs), and a count after a prefix is at most the run's peak pkR (cb2_cnt_pkR); cnb_pre's two pkR
   conjuncts bound that peak (cb2_counts). No counts premise and no PresetRoomCounts citation are needed.
   THE WILD BUDGET: the walk's journal is cnb_J D 0 at both cuts (the segment has no wild site). padded is a FIXED-trace
   callee (fpostm), so each call is made on the journal REBASED to the empty budget (the kit's cnb_J_rebase: the entry
   with its depot moved to the call state's) and the return state's journal is UNBASED at the same budget
   (cnb_J_fixed); each `sd` store rebases, runs ajournal_x_exec and unbases the same way (cb2_J_st8).
   THE REFUSED COPY (the cut's `own0 <> 0 -> cnb_cdead D`): g_own_ran_out leaves 0 only at a P0 (NULL) arm. At that
   call's state S the progress fact holds for the granted copies' events E, k <= 2 of them, so the three copies
   ck_cno_copies x are E ++ [HMal (size + 16)] ++ the rest. At a model run and position i at the entry state whose
   next events are the three copies, consumer events (cnb_cdead's premises), the progress fact makes i + k a position
   of S, the run's next event there is the copy's HMal (size + 16) (prh_run_at_app_iff) and its one-event window is a
   consumer one (prh_cons_from_sub), so padded's outcome clause gives res <> 0 against the NULL arm's res = 0
   (cb2_dead). A P1 arm keeps own and the fact; a later P0 arm derives it again.
   THE HULL BUDGET (route (b), the contract's cnb_hrest stages): cnb_at_copy carries hull_budget S (cnb_hev_all x),
   which is the three copies' cnb_hmal x followed by cnb_hrest_copies x (cnb_hrest_cpy1_split / cpy2_split /
   copies_split, reflexivity). cb2_inv carries the budget with 3 - k copies' mallocs still to pay. Each copy pays one
   (the contract's cnb_hpay_copy): padded's premise hull_budget S [HMal (size + 16)] by weakening, and after the call
   padded's post conjunct hull_used S S' [HMal (size + 16)] leaves the budget for the rest (hull_budget_app).
   CNB_INIT gets hull_budget S (cnb_hrest_copies x).
   NAMED ARGUMENT (ONE argument; not a stand-in lemma):
     IMG_SHADOW - the shadow of every byte of the image band [pa_lo, pa_hi) is present at every ARcf state, `ARcf .. ->
       pa_lo <= a < pa_hi -> aview (shadow_addr a) <> None`: the same words as CB0's B' range fact cnb0_img_shadow_vis
       (Cno102B_E0.v :505-507; = YImgShadowCoverCf.img_shadow_vis_cf_at SEGS B pa_lo pa_hi). RE-FIT to the kit Batch 2:
       kept_at bounds a kept global by PA's pa_lo / pa_hi (PRH_Base.v 3004a98fe2d9 :1021, :1044), no longer by
       YImgTop's IMG_LO / IMG_TOP, so the fact is stated over that band. NOT derivable from ARcf; the top supplies it
       (at the instance, YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover). Only the kept_at image cases of the input's
       home read it.
   Numerals: the offsets above (DERIVED); 49 / 50 / 0 (WORD: the fill bytes '1' / '2' / '\0'); 16 / 24 / 48 / 104 / 160
   / 192 / 32 / 8 / 64 (LENGTH: the padded tail, slot offsets, the frame, the saved words, the hull margin); 3 (COUNT:
   the copies); register numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre FCiface YGcallx YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0sshcf YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoomKeep YK0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetRoom PresetRoomPos
  PresetLiveBounds PresetRodata PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_Ro.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which turns zify's division rewriting off globally; this file's arithmetic on the frame
   and slot offsets needs it on (the step kit's reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ==== PURE HELPERS ==== *)
Lemma cb2_li : forall regs i, 0 <= i < 2 ^ 64 -> v_addi (getr regs 0%bv) i = w64 i.
Proof. intros regs i Hi. rewrite ro_getr0. unfold v_addi, w64. rewrite unsigned_lit_small by lia. f_equal; try lia. Qed.
Lemma cb2_mv : forall (x : word), v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* an update of a register the snapshot does not name keeps it *)
Lemma cb2_regsat_upd : forall regs l (r : bv 5) v, cnb_regsat regs l ->
  Forall (fun p : bv 5 * Z => bv_eqb (fst p) r = false) l -> cnb_regsat (regupd regs r v) l.
Proof.
intros regs l r v H HF. apply (cnb_regsat_kept regs _ l H). rewrite Forall_forall in *.
intros p Hp. apply ro_getr_other. exact (HF p Hp).
Qed.

Lemma cb2_ctx_firstn : forall {PI : PrhImg} CTX F x n, prh_ctx CTX F x -> prh_ctx CTX F (firstn n x).
Proof. intros PI CTX F x n (c & j & HR & ->). exists c, (Nat.min n j). split; [exact HR|]. apply firstn_firstn. Qed.

(* cgif YCbq.v:1945 shadow_hull_vis_of_block, for any covering hull (FuzzStrdupB.v sd_hull_sub) *)
Lemma cb2_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* fuzz_grant GrantRo.v:82-100 ro_hull's arithmetic: the hull of a range at least 64 bytes inside a band [lo, hi) is
   the shadow of band bytes (FuzzStrdupB.v sd_hull_img, over any band) *)
Lemma cb2_hull_img : forall lo hi a n s, 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ lo <= 8 * (s - SHADOW_OFF) < hi.
Proof.
intros lo hi a n s Hn Hlo Hhi Hs. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.

Lemma cb2_garr8_prefix : forall segs mem p l1 l2, garr8 segs mem p (l1 ++ l2) -> garr8 segs mem p l1.
Proof. intros segs mem p l1 l2 H j Hj. rewrite <- (app_nth1 l1 l2 0 Hj). apply H. rewrite length_app. lia. Qed.

(* ==== THE 8-BYTE STORE AT THE MEMORY OF A HAND STEP: what `sd` leaves after the runner's unrestrict ==== *)
Section st.
Variable segs : list Segment.
Definition cb2_st8 (H : word -> bool) (mem : word -> option byte) (a v : Z) : word -> option byte :=
  munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))).

Lemma cb2_nth_le : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma cb2_word_le_nth : forall v k, 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  nth k (word_to_le_bytes 8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (le_byte v 8 k).
Proof.
intros v k Hv Hk. unfold word_to_le_bytes. rewrite (unsigned_lit_small v) by lia.
rewrite (cb2_nth_le 8 v k Hk). unfold le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma cb2_st8_hidden : forall H mem a v x, H x = true -> cb2_st8 H mem a v x = mem x.
Proof. intros H mem a v x Hx. unfold cb2_st8, munrestrict. rewrite Hx. reflexivity. Qed.

Lemma cb2_st8_out : forall H mem a v (x : word), 0 <= a -> a + 8 <= 2 ^ 64 -> ~ (a <= bv_unsigned x < a + 8) ->
  mrestrict H (cb2_st8 H mem a v) x = mrestrict H mem x.
Proof.
intros H mem a v x Ha0 Ha8 Hx. unfold cb2_st8, mrestrict, munrestrict.
destruct (H x) eqn:Ex; [reflexivity|]. cbv beta iota.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
rewrite YK0u.wbytes_outside.
- cbv beta. rewrite Ex. reflexivity.
- rewrite Hu, length_N_to_le_bytes. lia.
- rewrite Hu, length_N_to_le_bytes. lia.
Qed.

Lemma cb2_st8_grows : forall H mem a v, mem_grows (mrestrict H mem) (mrestrict H (cb2_st8 H mem a v)).
Proof.
intros H mem a v x Hx. revert Hx. unfold cb2_st8, mrestrict, munrestrict.
destruct (H x) eqn:Ex; cbv beta iota; intros Hx; [exact Hx|].
apply (wbytes_grows _ _ _ x). cbv beta. rewrite Ex. exact Hx.
Qed.

Lemma cb2_st8_apresent : forall H mem a v z, apresent H mem z -> apresent H (cb2_st8 H mem a v) z.
Proof. intros H mem a v z Hp. eapply apresent_grows; [apply cb2_st8_grows | exact Hp]. Qed.

Lemma cb2_st8_val : forall H mem a v, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> H (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
  val_mem segs (mrestrict H (cb2_st8 H mem a v)) a 8 v.
Proof.
intros H mem a v Ha0 Ha8 Hv Hh k Hk.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
assert (Hu' : bv_unsigned (Z_to_bv 64 (a + Z.of_nat k)) = a + Z.of_nat k) by (apply unsigned_lit_small; lia).
unfold mbyte, cb2_st8, mrestrict, munrestrict. rewrite (Hh k Hk). cbv beta iota.
rewrite YK0u.wbytes_inside.
- cbv iota. f_equal. rewrite Hu, Hu'. replace (Z.to_nat (a + Z.of_nat k - a)) with k by lia.
  exact (cb2_word_le_nth v k Hv Hk).
- rewrite Hu, length_N_to_le_bytes. lia.
- rewrite Hu, Hu', length_N_to_le_bytes. lia.
Qed.

(* YCem.v rdword_of_val_mem, restated here (that file is not in this closure) *)
Lemma cb2_rdword_of_val_mem : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Lemma cb2_st8_rdword : forall H mem a v, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> H (Z_to_bv 64 (a + Z.of_nat k)) = false) ->
  rdword (aview segs H (cb2_st8 H mem a v)) a = Some v.
Proof.
intros H mem a v Ha0 Ha8 Hv Hh. apply cb2_rdword_of_val_mem; [|exact Hv].
exact (cb2_st8_val H mem a v Ha0 Ha8 Hv Hh).
Qed.

Lemma cb2_st8_aview : forall H mem a v z, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= z < 2 ^ 64 -> ~ (a <= z < a + 8) ->
  aview segs H (cb2_st8 H mem a v) z = aview segs H mem z.
Proof.
intros H mem a v z Ha0 Ha8 Hz Hout. apply aview_eq_of. apply cb2_st8_out; [exact Ha0 | exact Ha8 |].
rewrite unsigned_lit_small by lia. exact Hout.
Qed.
End st.

(* ==== THE SLOTS OF THE SEGMENT: closed checks on the listing of record (the kit's form: decoded fields compared by
   bv_unsigned, never as bv literals) ==== *)
Definition cb2_is_sd (off : Z) (rs1 rs2 : bv 5) (i : Z) : bool :=
  match cnb_dec off with
  | Some (Store SZ8 rs1' rs2' imm, sz) => (sz =? 4) && bv_eqb rs1' rs1 && bv_eqb rs2' rs2 && (bv_signed imm =? i)
  | _ => false end.
Lemma cb2_c400 : cnb_is_addi 400 12%bv 0%bv 49 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c404 : cnb_is_addi 404 10%bv 24%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c408 : cnb_is_addi 408 11%bv 23%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c412 : plookup B_prog_tpi_cno (CNB_OFF + 412) = Some (PCall AS_padded 1%bv). Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c416 : cnb_is_addi 416 25%bv 10%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c420 : cnb_is_addi 420 12%bv 0%bv 50 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c424 : cnb_is_addi 424 10%bv 24%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c428 : cnb_is_addi 428 11%bv 23%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c432 : plookup B_prog_tpi_cno (CNB_OFF + 432) = Some (PCall AS_padded 1%bv). Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c436 : cb2_is_sd 436 9%bv 10%bv 24 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c440 : cnb_is_addi 440 10%bv 24%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c444 : cnb_is_addi 444 11%bv 23%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c448 : cnb_is_addi 448 12%bv 0%bv 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c452 : plookup B_prog_tpi_cno (CNB_OFF + 452) = Some (PCall AS_padded 1%bv). Proof. vm_compute. reflexivity. Qed.
Lemma cb2_c456 : cb2_is_sd 456 9%bv 10%bv 16 = true. Proof. vm_compute. reflexivity. Qed.
(* padded's three return sites (B' 0x81b90 / 0x81ba4 / 0x81bb8, = PRH_ImgB's pi_call_rets F_check_no_overread F_padded) *)
Definition cb2_rets : list Z := [416; 436; 456].
Lemma cb2_ret_slots : forall ret, In ret cb2_rets ->
  match plookup B_prog_tpi_cno (CNB_OFF + ret) with Some _ => true | None => false end = true.
Proof.
intros ret Hin. cbn [cb2_rets In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  lazymatch goal with |- match plookup B_prog_tpi_cno (CNB_OFF + _) with Some _ => true | None => false end = true =>
    vm_compute; reflexivity end.
Qed.

(* ==== THE IMAGE B' WALK CONTEXT: CnoB102f's instance (preset's CfParams, the room invariant of record, the cf
   allocator relation with the error-buffer extents placed), PrhImg prh_img_B, the contract's listing tables; the
   PAImg instance is a PARAMETER (owner 12:48Z) ==== *)
Section e2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Instance CB2_cp : CfParams := CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Instance CB2_RL : PrhRoomLive := prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Instance CB2_PL : PAListing B_prog_listing := PL_cno_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* the walk's allocator relation, the cf instance (S1KitAlloc's ARxs, YGcallcf.v; Cno102B_F.v:181) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARcfx).
#[local] Notation STK := STK_check_no_overread.
Variable CTX0 : list (list Z).
(* the walk's image facts (the contract's record, closed by computation at the instance once PAImg_prog.v builds) *)
Hypothesis IMG : cnb_img B.
(* the callee text: the kit's padded, at every float state (the cut's float state is the one the earlier callees left) *)
Hypothesis HPAD : forall fz : YK11.FPState, tpadded_specX (fx := fz) B ARcfx SK CTX0.
(* NAMED ARGUMENT IMG_SHADOW (header): CB0's cnb0_img_shadow_vis, the same words, over PA's image band *)
Hypothesis IMG_SHADOW : forall ly S Hp (W : world SEGS) mem md a, ARcf SEGS B ly S Hp W mem md ->
  @pa_lo _ _ PA <= a < @pa_hi _ _ PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.

(* the allocator's laws at ARcf: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
(* the copies' blocks of a prefix of the copies (cnb_cblks for three) *)
Definition cb2_cbl (D : cnb_in) (cs : list Z) : list (Z * Z) := concat (map (cnb_cblk D) cs).
Lemma cb2_cbl_app1 : forall D cs r, cb2_cbl D (cs ++ [r]) = cb2_cbl D cs ++ cnb_cblk D r.
Proof. intros D cs r. unfold cb2_cbl. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.
Lemma cb2_cbl_len : forall D cs, (length (cb2_cbl D cs) <= length cs)%nat.
Proof.
intros D cs. induction cs as [|r cs IH]; [cbn; lia|]. unfold cb2_cbl in *. cbn [map concat length].
rewrite length_app.
assert (Hr : (length (cnb_cblk D r) <= 1)%nat) by (unfold cnb_cblk; destruct (r =? 0); cbn; lia).
lia.
Qed.
Lemma cb2_cbl_3 : forall D r1 r2 r3, cb2_cbl D [r1; r2; r3] = cnb_cblks D r1 r2 r3.
Proof. intros D r1 r2 r3. unfold cb2_cbl, cnb_cblks. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.

(* the callee-saved registers of the cuts (sp, s0, s1, s2-s11) *)
Ltac cb2_bvu := match goal with |- context [bv_unsigned ?r] =>
  let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end.
Lemma cb2_regs_saved : forall D extra, Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) extra ->
  Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) (cnb_core D ++ extra).
Proof.
intros D extra He. apply Forall_app. split; [|exact He]. unfold cnb_core.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; try cb2_bvu; unfold acallee_saved; lia.
Qed.
Lemma cb2_s78_saved : forall v7 v8, Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p)))
  [(23%bv, v7); (24%bv, v8)].
Proof. intros v7 v8. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; try cb2_bvu; unfold acallee_saved; lia. Qed.
Lemma cb2_s9_saved : forall v, Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) [(25%bv, v)].
Proof. intros v. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; try cb2_bvu; unfold acallee_saved; lia. Qed.


(* ---- small facts of the instance ---- *)
Lemma cb2_stk : STK_padded + 192 <= STK /\ 0 <= STK_padded.
Proof. split; lazymatch goal with |- _ <= _ => vm_compute; discriminate end. Qed.

Lemma cb2_live_nonneg : forall x, 0 <= PRH_FnPj.LIVE_pj_parse x.
Proof.
intros x. unfold PRH_FnPj.LIVE_pj_parse. pose proof (@cf_head_nonneg CB2_cp) as Hh.
assert (H1 : 0 <= hpeakR (PRH_FnPj.prhPj_ptrace x)) by (destruct (PRH_FnPj.prhPj_ptrace x); cbn [hpeakR]; lia).
pose proof (Nat2Z.is_nonneg (PjGrammar.calls (PRH_FnPj.prhPj_ptrace x))). nia.
Qed.

Lemma cb2_bb : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof. intros ly S. apply blocks_bytes_bsum. Qed.
Lemma cb2_ablocks_snd : forall ly S, map snd (ablocks B ly S) = map snd (blocks S).
Proof. intros ly S. unfold ablocks. rewrite map_map. apply map_ext. intros b. reflexivity. Qed.

(* THE LIVE COUNTS ALONG THE RUN: a count after a prefix of the events is at most the run's peak pkR *)
Lemma cb2_cnt_pkR : forall f E E2 L,
  (PresetReqAt.cnt f (PresetReqAt.hlive_from L E) <= PresetRun.pkR f L (E ++ E2))%nat.
Proof.
intros f E. induction E as [|e E IH]; intros E2 L.
- rewrite PresetReqAt.hlive_from_nil. cbn [app]. destruct E2 as [|e2 E2]; cbn [PresetRun.pkR]; lia.
- cbn [app PresetRun.pkR]. unfold PresetReqAt.hlive_from in *. cbn [fold_left].
  specialize (IH E2 (PresetReqAt.hstep L e)). lia.
Qed.
Lemma cb2_map_const : forall {A C : Type} (c : C) (l : list A), map (fun _ => c) l = repeat c (length l).
Proof. intros A C c l. induction l as [|a l IH]; [reflexivity|]. cbn [map length repeat]. rewrite IH. reflexivity. Qed.

(* alloc.c's statics are image bytes below the low-memory end (FuzzStrdupB.v sd_pst_low, with #102's two cells) *)
Lemma cb2_pst_low : forall a, Exists (in_zr a) prh_pst -> 0 <= a < kLowMemEnd.
Proof.
intros a Hx. unfold prh_pst in Hx.
cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
  pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B] in Hx.
unfold kLowMemEnd.
repeat (apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [unfold in_zr in Hx; cbn [fst snd] in Hx; lia |]).
apply Exists_nil in Hx; destruct Hx.
Qed.

(* the return sites: code words of the listing below the ceiling (fpre's raZ bound), even, small offsets *)
Lemma cb2_ret_ok : forall ret, In ret cb2_rets ->
  4096 <= cnb_pc ret < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cnb_pc ret)) /\ 0 <= ret < 2 ^ 28.
Proof.
intros ret Hin. pose proof (cnbi_base B IMG) as HB. pose proof cnb_off_val as HO.
pose proof (cb2_ret_slots ret Hin) as Hsl.
assert (Hr : 0 <= ret < 2 ^ 28 /\ (CNB_OFF + ret) mod 2 = 0).
{ cbn [cb2_rets In] in Hin. rewrite HO.
  destruct Hin as [<- | [<- | [<- | []]]]; (split; [lia | reflexivity]). }
destruct Hr as (Hr28 & Hr2).
unfold cnb_pc, w64. replace (BASE + CNB_OFF + ret) with (BASE + (CNB_OFF + ret)) by lia.
split; [split|split].
- rewrite HB. unfold B_prog_base. lia.
- exact (pa_slot_lt_ceil_b (PL := PL_cno_B) (PI := PA) (CNB_OFF + ret) ltac:(lia) Hsl).
- apply ret_ok_codeptr_v; [lia | exact Hr2].
- exact Hr28.
Qed.

(* the return sites are PRH_ImgB's call returns of check_no_overread into padded (computed, no address typed) *)
Lemma cb2_call_rets : forall ret, In ret cb2_rets -> In (cnb_pc ret) (pi_call_rets F_check_no_overread F_padded).
Proof.
intros ret Hin. unfold cnb_pc. rewrite (cnbi_base B IMG).
cbn [cb2_rets In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; vm_compute;
  first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity].
Qed.

(* ---- cno's pre, the facts the copies read (each conjunct picked BY ITS TYPE, the kit's ro_from) ---- *)
Lemma cb2_pre_facts : forall D, cnb_pre (fx := fx) B ARcfx CTX0 D ->
  prh_univ_closure B CTX0 /\ prh_ctx CTX0 F_check_no_overread (raZ (bi_regs D) :: spine (bi_ch D)) /\
  cnb_size D <= 3 * 2 ^ 20 /\ cnb_size D + 16 < cf_malloc_max /\
  blocks_bytes (bi_S D) + LIVE_check_no_overread (bi_x D) <= LIVE_MAX /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None)) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None)) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D H. unfold cnb_pre in H. cbv zeta in H.
split; [ro_from H|]. split; [ro_from H|]. split; [ro_from H|]. split; [ro_from H|]. split; [ro_from H|].
split; ro_from H.
Qed.

(* PADDED'S LIVE COUNTS at a call state S that has made the granted copies' events (k <= 3 of them) since entry:
   cnb_prog's live set, the events a prefix of the text's list (its C3, cnb_ck_cno_evs), and cnb_pre's peak bounds *)
Lemma cb2_counts : forall D S cs, cnb_pre (fx := fx) B ARcfx CTX0 D -> (length (cb2_cbl D cs) <= 3)%nat ->
  cnb_prog D (map (fun _ => PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)) (cb2_cbl D cs)) S ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros D S cs HPRE Hk (HL & _).
destruct (cb2_pre_facts D HPRE) as (_ & _ & _ & _ & _ & HK1 & HK2).
set (m := PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)) in *.
set (k := length (cb2_cbl D cs)) in *.
set (E2 := repeat m (3 - k) ++ cnb_revs3 D None None None ++ cnb_fevs D None None None).
assert (EE : map (fun _ => m) (cb2_cbl D cs) ++ E2 = ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None).
{ rewrite <- (cnb_ck_cno_evs D None None None). unfold E2. rewrite cb2_map_const. fold k.
  rewrite app_assoc, <- repeat_app. replace (k + (3 - k))%nat with 3%nat by lia. reflexivity. }
set (L0 := PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D))) in *.
assert (C : forall f, (PresetReqAt.cnt f (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) <=
  PresetRun.pkR f L0 (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None))%nat).
{ intros f. rewrite (PresetReqAt.cnt_perm f _ _ HL), <- EE. apply cb2_cnt_pkR. }
split.
- pose proof (C YGcfRoomLive.rl_sec_req) as C1.
  unfold YGcfRoomLive.sec_cnt. unfold PresetReqAt.cnt, YGcfRoom.room_of_cf in C1. cbn [PresetRoom.rs_live] in C1. lia.
- pose proof (C (PresetRoom.in_cls YG00.kBatchClass)) as C2.
  unfold YGcfRoomLive.ccnt24, PresetRoom.ccnt. unfold PresetReqAt.cnt, YGcfRoom.room_of_cf in C2.
  cbn [PresetRoom.rs_live] in C2. lia.
Qed.

(* ---- THE FRAME CHAIN at a cno call state, with its spine (the kit's cnb_chain and the context a callee's text
   asks: the entry record's ra on top of the entry's chain, or nothing) ---- *)
Lemma cb2_chain : forall D fxk ly S Hp W regs mem md k wk,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> cnb_base (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k wk ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cnb_S1 D) (cnb_sp0 D) ch1 /\
    (ch1 = [] \/ spine ch1 = raZ (bi_regs D) :: spine (bi_ch D)).
Proof.
intros D fxk ly S Hp W regs mem md k wk HPRE HB.
destruct (cnb_entry_facts B ARcfx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _ & _ & Hra40 & Hch0 & _).
pose proof cnb_stk_val as HSTKv.
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
destruct HB as (_ & _ & (WS & HJ & _) & _ & HSV & _).
pose proof (ajx_ly HJ) as Hly. pose proof (ajx_hi HJ) as F1.
assert (Etop : ly_top ly = ly_top (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
destruct (Z_lt_le_dec (cnb_sp0 D) (ly_top (bi_ly D) - 16)) as [Hlt|Hge].
- exists ((cnb_sp0 D, raZ (bi_regs D), s0Z (bi_regs D)) :: bi_ch D). split; [|right; reflexivity].
  apply (achain_ly_top (bi_ly D) ly); [exact Etop|].
  pose proof (proj1 (Forall_forall _ _) HSV (152, 1%bv) ltac:(ro_in)) as V1.
  pose proof (proj1 (Forall_forall _ _) HSV (144, 8%bv) ltac:(ro_in)) as V8.
  cbn [fst snd] in V1, V8.
  apply (achain_push (bi_ly D) (aview SEGS (w_H (bi_W D)) (bi_mem D)) (aview SEGS (w_H W) mem) (cnb_sp0 D)
    (s0Z (bi_regs D)) (raZ (bi_regs D)) (bi_ch D) (cnb_S1 D) Hch0).
  + lia.
  + intros a Ha. apply F1; lia.
  + replace (cnb_sp0 D - 8) with (cnb_sp0 D - 160 + 152) by lia. exact V1.
  + replace (cnb_sp0 D - 16) with (cnb_sp0 D - 160 + 144) by lia. exact V8.
  + exact Hra40.
  + lia.
  + lia.
  + exact Hlt.
  + lia.
- exists []. split; [|left; reflexivity]. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* ==== WHAT A STATE'S OWN LAWS GIVE: the shadow facts of a text at its home (G3, PRH_FnReader.v :33-43) ==== *)
Lemma cb2_home_shadow : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own p n,
  ARcfx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 < n ->
  PRH_FnReader.prhReader_home B ly S Hp Lam p n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n HAR HL Hn
  [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hnh & Hb & Hm)].
- (* a harness block of the ledger: its user bytes, past the hidden head *)
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) (b, m)
    Hin)
    as (Hm0 & Hab & Hhp & _). cbn [fst snd] in Hm0, Hab, Hhp.
  pose proof (@cf_head_nonneg CB2_cp) as Hh0.
  destruct (AR_shadow_law_ok_cf SEGS B ly S Hp W mem md (b - cf_head) (m + cf_head) (proj1 HAR) Hab) as [Hbs Hhu].
  assert (Hsk : hd_skip Hp (b - cf_head) = cf_head).
  { unfold hd_skip. replace (existsb (Z.eqb (b - cf_head)) Hp) with true; [reflexivity|]. symmetry.
    apply existsb_exists. exists (b - cf_head). split; [exact Hhp | apply Z.eqb_refl]. }
  rewrite Hsk in Hbs. replace (b - cf_head + cf_head) with b in Hbs by lia.
  pose proof (req_size_pos (m + @cf_head CB2_cp) ltac:(lia)) as (_ & Hq).
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (cb2_hull_sub _ (b - cf_head) (req_size (m + cf_head)) p n Hhu); lia.
- (* a registered read-only global: zero shadow (AR_zshadow_law_cf at the symbols' alignment), the image hull *)
  destruct Hzs as (q & m & Hin & Hq & Hqm).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin)
    as (Z1 & Z2 & Z3 & Z4 & Z5).
  cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
  pose proof (alc_zshadow SEGS B LAWS_cf ly S Hp W mem md (q, m) (proj1 HAR)
    ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
  cbn [fst snd] in Hz.
  split.
  + apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF q m p n); [|exact Hq|exact Hqm].
    exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz).
  + intros s0 Hs. destruct (cb2_hull_img _ _ p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (IMG_SHADOW ly S Hp W mem md _ (proj1 HAR) Hr).
- (* an image string under route (a): per granule, zero shadow or a const-shadow cell (alx_const_cells) *)
  split.
  + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzg | (v & Hcell & Hv)]).
    * destruct Hzg as (q & m & Hin & Hq & Hqm).
      pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin)
        as (Z1 & Z2 & Z3 & Z4 & Z5).
      cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
      pose proof (alc_zshadow SEGS B LAWS_cf ly S Hp W mem md (q, m) (proj1 HAR)
        ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
      cbn [fst snd] in Hz.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz x ltac:(lia)).
    * pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARcfx LAWS ly S Hp W mem md HAR) _ (Hcell ly))
        as Hc.
      unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
      specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      assert (Hb : YG0f.le_byte v 1 0 = v).
      { unfold YG0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
        replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
        change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
      exists v. split; [|exact Hv].
      change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite Hc, Hb. reflexivity.
  + intros s0 Hs. destruct (cb2_hull_img _ _ p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (IMG_SHADOW ly S Hp W mem md _ (proj1 HAR) Hr).
- (* an allocator block that is not a harness block: the cf shadow law at hd_skip = 0 *)
  pose proof (proj1 (Forall_forall _ _) (S1Ledger.prh_ablocks_nonneg_cf B ly S Hp W mem md (proj1 HAR)) (b, m) Hin)
    as Hm0. cbn [snd] in Hm0.
  destruct (AR_shadow_law_ok_cf SEGS B ly S Hp W mem md b m (proj1 HAR) Hin) as [Hbs Hhu].
  assert (Hsk : hd_skip Hp b = 0).
  { unfold hd_skip. replace (existsb (Z.eqb b) Hp) with false; [reflexivity|]. symmetry.
    apply not_true_iff_false. intros Hx. apply existsb_exists in Hx as (h & Hh & Eh). apply Z.eqb_eq in Eh.
    subst h. exact (Hnh Hh). }
  rewrite Hsk, Z.add_0_r, Z.sub_0_r in Hbs.
  pose proof (req_size_pos m Hm0) as (_ & Hq).
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (cb2_hull_sub _ b (req_size m) p n Hhu); lia.
Qed.

(* a text the function reads (src_rd) at any state, from its bytes, its state-free bounds (the cut's ceiling on the
   window's own bytes, SRC-CEIL) and its home there *)
Lemma cb2_src_home : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own p x,
  ARcfx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  bytes_at W mem p x -> 4096 <= p -> p + Z.of_nat (length x) <= YM05.alloc_ceiling ->
  amem_range p (Z.of_nat (length x)) ->
  (0 < Z.of_nat (length x) -> PRH_FnReader.prhReader_home B ly S Hp Lam p (Z.of_nat (length x))) ->
  src_rd W mem p x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p x HAR HL Hby H4 Hc Ham HH.
split; [exact Hby|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Ham|].
destruct (Z_lt_le_dec 0 (Z.of_nat (length x))) as [Hn | Hn].
- destruct (cb2_home_shadow ly S Hp W mem md Lam peak cnt fail ran most own p _ HAR HL Hn (HH Hn)) as (Hra & Hhv).
  split; [exact Hra | intros _; exact Hhv].
- split; [apply range_addressable_nil; lia | intros H; lia].
Qed.

(* a home survives a call that keeps every block *)
Lemma cb2_home_lift : forall ly S Hp ly2 S2 Lam p n,
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2)) ->
  PRH_FnReader.prhReader_home B ly S Hp Lam p n -> PRH_FnReader.prhReader_home B ly2 S2 Hp Lam p n.
Proof.
intros ly S Hp ly2 S2 Lam p n Hinc [H | (b & m & Hin & Hnh & Hb & Hm)]; [left; exact H|].
right. exists b, m. split; [exact (Hinc _ Hin)|]. split; [exact Hnh|]. split; lia.
Qed.

(* ==== WHAT A STACK STORE KEEPS: every byte below the ceiling ==== *)
Lemma cb2_st8_low : forall (W : world SEGS) mem a v z, YM05.alloc_ceiling <= a -> a + 8 <= 2 ^ 64 ->
  0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H W) (cb2_st8 (w_H W) mem a v) z = aview SEGS (w_H W) mem z.
Proof.
intros W mem a v z Ha Ha8 Hz. pose proof asan_consts as (C1 & _).
apply cb2_st8_aview; lia.
Qed.

Lemma cb2_bytes_low : forall (W : world SEGS) mem mem' p x,
  (forall z, 0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  0 <= p -> p + Z.of_nat (length x) <= YM05.alloc_ceiling -> bytes_at W mem p x -> bytes_at W mem' p x.
Proof.
intros W mem mem' p x HA Hp Hpx Hby. unfold bytes_at in *.
apply (garr8R_frame SEGS (rdW W mem) (rdW W mem') p x Hby).
intros z Hz. apply (mbyte_of_aview SEGS). apply HA. lia.
Qed.

Lemma cb2_ledger_low : forall ly S Hp (W : world SEGS) mem mem' md Lam peak cnt fail ran most own,
  ARcfx ly S Hp W mem md ->
  (forall z, 0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' md Lam peak cnt fail ran most own HAR HA HL.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
apply (S1Ledger.prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HL).
- intros a Ha. apply HA. pose proof (cb2_pst_low a Ha). lia.
- intros a kk i Hin Hi.
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) (a, kk)
    Hin)
    as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & _).
  change (@cf_head CB2_cp) with 16 in *.
  pose proof (req_size_pos (kk + 16) ltac:(lia)) as (_ & Hq).
  apply HA. lia.
- intros a kk _ H. exact H.
- apply Permutation_refl.
Qed.

(* ==== THE STORE HAND STEP (`sd rs2, imm(rs1)` into the walk's own stack window): P across by srr_inv_laws ==== *)
Lemma cb2_hs_sd0 : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (W : world SEGS) fxk regs mem md Q off off' w rs1 rs2 imm a v,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs1) + bv_signed imm = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  getr regs rs2 = w64 v ->
  (forall j, 0 <= j < 8 -> apresent (w_H W) mem (a + j)) -> P mem ->
  (forall X, P (cb2_st8 (w_H W) mem a v) ->
     SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') regs (cb2_st8 (w_H W) mem a v) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros P PLAW W fxk regs mem md Q off off' w rs1 rs2 imm a v Hpl Hdec Ho -> Ha Ha0 Ha8 Hv Hpres HPm HK.
assert (Eaddr : v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
assert (Hok : RiscvSemantics.store_ok SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 a) 8 = true).
{ apply store_ok_of_all.
  - rewrite unsigned_lit_small by lia. lia.
  - intros x Hx. rewrite unsigned_lit_small in Hx by lia.
    assert (Hp : apresent (w_H W) mem (bv_unsigned x)).
    { replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia. apply Hpres. lia. }
    pose proof (apresent_writable SEGS (w_H W) mem (bv_unsigned x) Hp) as Hw.
    unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
unfold cnb_cfg, cnb_pc, w64. replace (BASE + CNB_OFF + off) with (BASE + (CNB_OFF + off)) by lia.
eapply (SRr_step_inv SEGS pa_wx P PLAW W).
- reflexivity.
- rewrite (@restrict_mkst_fx fxk).
  exact (@step_sd_at fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs1 rs2 imm (Z_to_bv 64 a)
    (Z_to_bv 64 v) (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec
    Eaddr Hv Hok).
- exact HPm.
- intros md' Hs HP'. rewrite (same_but_materialized_wvb md md' Hs).
  specialize (HK (m_vm_materialized md') HP').
  unfold cnb_cfg, cnb_pc, w64 in HK.
  replace (BASE + CNB_OFF + (off + 4)) with (BASE + (CNB_OFF + (off + 4))) in HK by lia.
  rewrite <- (cnb_pc4 off ltac:(lia)) in HK. exact HK.
Qed.

Lemma cb2_hs_sd : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (W : world SEGS) fxk regs mem md Q off off' rs1 rs2 i a v,
  cb2_is_sd off rs1 rs2 i = true -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs1) + i = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  getr regs rs2 = w64 v ->
  (forall j, 0 <= j < 8 -> apresent (w_H W) mem (a + j)) -> P mem ->
  (forall X, P (cb2_st8 (w_H W) mem a v) ->
     SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') regs (cb2_st8 (w_H W) mem a v) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros P PLAW W fxk regs mem md Q off off' rs1 rs2 i a v H.
unfold cb2_is_sd, cnb_dec in H.
destruct (plookup B_prog_tpi_cno (CNB_OFF + off)) as [e|] eqn:Hpl; [|discriminate H].
destruct e; try (cbv beta iota in H; discriminate H).
match type of H with context [decode_any ?x] => destruct (decode_any x) as [[ii sz]|] eqn:Hdec; [|discriminate H] end.
destruct ii; try (cbv beta iota in H; discriminate H).
match goal with Hd : decode_any _ = Some (Store ?z _ _ _, _) |- _ => destruct z; try (cbv beta iota in H; discriminate H) end.
cbv beta iota in H.
repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  | H : bv_eqb _ _ = true |- _ => apply ro_bv_eqb_eq in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end; subst.
intros Ho Eo Ha Ha0 Ha8 Hv Hpres HPm HK.
eapply cb2_hs_sd0; [exact PLAW | exact Hpl | exact Hdec | exact Ho | exact Eo | exact Ha | exact Ha0 | exact Ha8
  | exact Hv | exact Hpres | exact HPm | exact HK].
Qed.

(* the walk's journal after the store (REBASED to the empty budget, ajournal_x_exec, UNBASED at the same budget, the
   kit's cnb_J_rebase / cnb_J_fixed): its bytes are in the walk's own stack window *)
Lemma cb2_J_st8 : forall D wk ly S Hp (W : world SEGS) mem md k a v X,
  cnb_J B ARcfx D wk ly S Hp W mem md k ->
  cnb_sp0 D - STK <= a -> a + 8 <= cnb_sp0 D -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  cnb_J B ARcfx D wk ly S Hp W (cb2_st8 (w_H W) mem a v) (with_vm_backing (m_vm_lazy md) X md) k.
Proof.
intros D wk ly S Hp W mem md k a v X HJ Hlo Hhi Ha0 Ha8.
apply (cnb_J_fixed B ARcfx D wk ly S Hp W mem md k _ _ _ _ _ _ _ HJ).
apply (ajournal_x_exec SEGS B prh_pst ARcfx LAWS pa_segs_low STK (cnb_sp0 D) [] (bi_ly D)
  (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp W mem md k
  (cb2_st8 (w_H W) mem a v) (with_vm_backing (m_vm_lazy md) X md) (fun z => a <= z < a + 8)
  (cnb_J_rebase B ARcfx D wk ly S Hp W mem md k HJ)).
- intros x Hx. cbv beta in Hx. apply cb2_st8_out; [exact Ha0 | exact Ha8 | exact Hx].
- apply cb2_st8_grows.
- intros x Hx. apply cb2_st8_hidden. exact Hx.
- apply same_but_materialized_wvb_any.
- intros z Hz. cbv beta in Hz. left. lia.
Qed.

(* cnb_base after a store into the body's stack below the saved words *)
Lemma cb2_base_st8 : forall D fxk ly S Hp (W : world SEGS) regs mem md k wk a v X,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_base (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k wk ->
  cnb_S1 D <= a -> a + 8 <= cnb_sp0 D - 104 ->
  cnb_base (fx := fx) B ARcfx D fxk ly S Hp W regs (cb2_st8 (w_H W) mem a v) (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros D fxk ly S Hp W regs mem md k wk a v X HPRE (Hz & Hk & HJ & HF & HSV & R3 & R4 & HRO) Ha Ha'.
destruct (cnb_entry_facts B ARcfx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
pose proof cnb_stk_val as HSTKv. pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
assert (Hc : YM05.alloc_ceiling <= a) by lia.
assert (HA : forall z, 0 <= z < 2 ^ 64 -> ~ (a <= z < a + 8) ->
  aview SEGS (w_H W) (cb2_st8 (w_H W) mem a v) z = aview SEGS (w_H W) mem z)
  by (intros z Hz0 Hz1; apply cb2_st8_aview; lia).
pose proof HJ as (WS & HJW & _).
pose proof (ajx_ar HJW) as HAR. pose proof (ajx_ly HJW) as Hly.
split; [exact Hz|]. split; [exact Hk|].
split; [apply cb2_J_st8; [exact HJ | lia | lia | lia | lia]|].
split.
{ destruct HF as (Hfrs & Hnin & Hflag & Hfpres & Hspres).
  assert (Hin3 : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds_x SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
  assert (EF1 : ly_F ly = ly_F (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
  assert (EFa1 : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite EF1; reflexivity).
  rewrite EFa1 in HF4096, HFceil.
  assert (EFB : fs_frame_bytes CNB_CID = 512) by reflexivity. rewrite EFB in HFceil.
  split; [exact Hfrs|]. split; [exact Hnin|]. split.
  - rewrite <- Hflag. rewrite EFB. apply (ro_rdword_kept _ _ 0 YM05.alloc_ceiling); [intros z Hz0; apply HA; lia | lia | lia].
  - split.
    + intros z Hz0. apply cb2_st8_apresent. exact (Hfpres z Hz0).
    + intros z Hz0. apply cb2_st8_apresent. exact (Hspres z Hz0). }
split.
{ unfold cnb_saved in *. apply Forall_forall. intros [o r] Hin.
  pose proof (proj1 (Forall_forall _ _) HSV (o, r) Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 56 <= o <= 152) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
  rewrite <- Hv. apply (ro_rdword_kept _ _ (a + 8) (2 ^ 64)); [intros z Hz0; apply HA; lia | lia | lia]. }
split; [exact R3|]. split; [exact R4|].
intros z Hro Hown Herr. rewrite <- (HRO z Hro Hown Herr).
assert (Himg : in_img SEGS z).
{ destruct Hro as [(sg & Hsg & _ & Hb) | Hrel]; [exists sg; split; [exact Hsg | exact Hb] | exact (pa_relro_img z Hrel)]. }
pose proof (@pa_segs_low _ _ PA z Himg) as Hl.
apply HA; lia.
Qed.

(* ==== THE CALL to padded (return sites 416 / 436 / 452 + 4): a FIXED-trace callee, so the walk's journal is REBASED
   to the empty budget (cnb_J_rebase), aj_call_xW, and UNBASED at the same budget (cnb_J_fixed); the kit's text for any
   float state, fpre's raZ bound from the closed lemma cb2_ret_ok, the callee context by prh_ctx_call at the
   frame-pointer caller, P across by srr_inv_call at the text's memnorm keep ---- *)
(* padded's post body (PRH_FnCheck.v c40cf3fdcd2a :968-1007), verbatim; fz is the call's float state (the text's
   malloc_cf_null_post is read at it, never at the section's entry fx) *)
Definition cb2_padQ (fz : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (mem : word -> option byte) (data : Z) (x : list Z) (fill : Z) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  let size := Z.of_nat (length x) in
  fun ly' S' Hp' W' regs' mem' md' =>
       exists res own', getr regs' 10 = w64 res /\ room_live_cf S' /\ Hp' = Hp /\
       PresetHullBudget.hull_used S S' [PresetReqAt.HMal (size + 16)] /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' /\ bytes_at W' mem' data x /\
       (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 16)] ->
          PRH_Base.prh_cons_from sm x0 os i (length [PresetReqAt.HMal (size + 16)]) ->
          res <> 0 /\
          exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 16)])%nat H0 hist' S') /\
       ((res = 0 /\ own' = 1 /\ ablocks B ly' S' = ablocks B ly S /\
         (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> PRH_Base.prh_run_at sm x0 os i (@nil PresetReqAt.hev) ->
         exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
         rd32 (aview SEGS (w_H W') mem') (as_errno B) 12 /\
         (exists ly1 S0 Hp1 W1 regsc memc mdc Wc cc,
            @YG0dcf.malloc_cf_null_post fz rc ci CB2_cp SEGS B ly1 S0 Hp1 W1 regsc memc mdc (size + 16) (PNull, S') Wc cc))
        \/
        (res <> 0 /\ own' = own /\ 4096 <= res /\ res + size + 16 <= YM05.alloc_ceiling /\
         ~ In res (map fst (ablocks B ly S)) /\
         Permutation (ablocks B ly' S') ((res, size + 16) :: ablocks B ly S) /\
         (forall a k, In (a, k) Lam -> a - cf_head <> res) /\
         bytes_at W' mem' res (x ++ repeat (fill mod 256) 16) /\
         (forall a, res <= a < res + size + 16 -> writable_at SEGS (rdW W' mem') a) /\
         range_addressable (aview SEGS (w_H W') mem') SHADOW_OFF res (size + 16) /\
         shadow_hull_vis (aview SEGS (w_H W') mem') res (size + 16) /\
         (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
         PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (size + 16)] ->
         exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (size + 16)])%nat H0 hist'
           S'))).

Lemma cb2_pad_call : forall (P : (word -> option byte) -> Prop), srr_inv_call SEGS P ->
  forall D fxk ly S Hp (W : world SEGS) regs mem md k wk Lam peak cnt fail ran most own ret fill,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> In ret cb2_rets ->
  cnb_base (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k wk ->
  getr regs 2%bv = w64 (cnb_S1 D) -> getr regs 8%bv = w64 (cnb_sp0 D) -> getr regs 1%bv = w64 (cnb_pc ret) ->
  getr regs 10%bv = w64 (bi_data D) -> getr regs 11%bv = w64 (cnb_size D) -> getr regs 12%bv = w64 fill ->
  0 <= fill < 2 ^ 64 -> room_live_cf S ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (cnb_size D + 16)] ->
  src_rd W mem (bi_data D) (bi_x D) ->
  (0 < cnb_size D -> PRH_FnReader.prhReader_home B ly S Hp Lam (bi_data D) (cnb_size D)) ->
  blocks_bytes S + (cnb_size D + 16) <= LIVE_MAX ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (SIGMA AS_padded) regs mem md)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = @cnb_cfg SEGS fxk (cnb_pc ret) regs2 mem2 md2 /\
       cnb_J B ARcfx D wk ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJ STK_padded (cnb_S1 D) [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regs regs2 /\
       cb2_padQ fxk ly S Hp W mem (bi_data D) (bi_x D)
         fill Lam peak cnt fail ran most own ly2 S2 Hp2 W2 regs2 mem2 md2 /\
       P mem2).
Proof.
intros P PCALL D fxk ly S Hp W regs mem md k wk Lam peak cnt fail ran most own ret fill
  HPRE Hret HB R2 R8 R1 R10 R11 R12 Hfill HRL HSEC HC24 HHB HSRC HHOME HBB HLED HPM.
destruct (cnb_entry_facts B ARcfx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & Hgp0 & Htp0 & _ & _ & _).
pose proof cnb_stk_val as HSTKv. pose proof cb2_stk as (HSTKp & HSTKp0). pose proof asan_consts as (C1 & _).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
destruct (cb2_ret_ok ret Hret) as ((Hr0 & Hrc) & Hrok & Hr28).
destruct (cb2_chain D fxk ly S Hp W regs mem md k wk HPRE HB) as (ch1 & Hch1 & Hsp1).
destruct (cb2_pre_facts D HPRE) as (HUNIV & HCTX0 & Hsz3 & Hcf & _).
pose proof HB as (Hz & Hk & HJ & HF & HSV & R3 & R4 & HROD).
pose proof (cnb_J_rebase B ARcfx D wk ly S Hp W mem md k HJ) as HJr.
pose proof HJ as (WS & HJW & _). pose proof (ajx_ly HJW) as Hly.
assert (Eshi : ly_stk_hi ly = ly_stk_hi (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
assert (Hsp : spZ regs = cnb_S1 D) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = cnb_sp0 D) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
assert (Hraz : raZ regs = cnb_pc ret) by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; lia).
assert (HCTX : prh_ctx CTX0 F_padded (raZ regs :: spine ch1)).
{ pose proof (prh_ctx_call CTX0 F_check_no_overread F_padded _ (cnb_pc ret) HCTX0 (cb2_call_rets ret Hret)) as Hc.
  change (pi_fp F_check_no_overread) with true in Hc. cbv iota in Hc.
  rewrite Hraz. destruct Hsp1 as [-> | ->]; [exact (cb2_ctx_firstn _ _ _ 1 Hc) | exact Hc]. }
pose proof HSRC as (_ & Hd4096 & Hdceil & _).
unfold cnb_cfg, w64.
eapply SRr_bind.
{ apply (@aj_call_xW fxk rc SK SEGS B prh_pst ARcfx cf_head LAWS pa_segs_low W regs mem (SIGMA AS_padded)
    STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly S Hp md k
    STK_padded 0 [] (cnb_S1 D - cnb_sp0 D) (w64 (cnb_pc ret)) ch1
    (fQmn mem (cb2_padQ fxk ly S Hp W mem (bi_data D)
       (bi_x D) fill Lam peak cnt fail ran most own))).
  - exact HJr.
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - exact R1.
  - exact Hrok.
  - unfold w64. rewrite unsigned_lit_small by lia. exact Hr0.
  - replace (cnb_sp0 D + (cnb_S1 D - cnb_sp0 D)) with (cnb_S1 D) by lia. rewrite Hs0. exact Hch1.
  - intros HAFN _.
    assert (HFP : fpre (fx := fxk) B ARcfx STK_padded ly S Hp W regs mem md ch1).
    { split; [exact HAFN|]. split; [exact HROD|].
      split; [rewrite Hsp, Eshi; lia | split; [rewrite Hraz; exact Hrc | exact Hz]]. }
    eapply SRr_mono; [exact (HPAD fxk ly S Hp W regs mem
      md ch1 (bi_data D) (bi_x D) fill Lam peak cnt fail ran most own HFP HRL HUNIV HCTX HSEC HC24 HHB R10 R11 R12 Hfill
      Hsz3 ltac:(lia) ltac:(lia) HSRC HHOME Hcf HBB HLED)|].
    intros W' c' _ HPOST. apply fpostW_x_of_apost. exact HPOST.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & _ & HP2 & (HQ & HMN)).
rewrite !Z.add_0_r in HJ1. replace (cnb_sp0 D + (cnb_S1 D - cnb_sp0 D)) with (cnb_S1 D) in HJ1 by lia.
apply SRr_ret. exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact (cnb_J_fixed B ARcfx D wk ly S Hp W mem md k _ _ _ _ _ _ _ HJ HJ2)|].
split; [exact HJ1|]. split; [exact HP2|]. split; [exact HQ|].
exact (PCALL mem mem2 HMN HPM).
Qed.

(* ---- cnb_base across a callee with FP = [] that may change the state (padded's P1 adds a block): the walk's journal
   at the return state (unbased, cb2_pad_call), the callee journal's frame, stack and image clauses (the kit's
   cnb_call_keep, its cnb_base half, at S2 with frames S2 = frames S); and the bytes of [s1, entry sp) kept ---- *)
Lemma cb2_base_keep : forall D fxk ly S Hp (W : world SEGS) regs mem md k wk STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> cnb_base (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k wk ->
  0 <= STK1 -> STK1 + (cnb_sp0 D - cnb_S1 D) <= STK ->
  cnb_J B ARcfx D wk ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  AJ STK1 (cnb_S1 D) [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  aregs_preserved regs regs2 ->
  cnb_base (fx := fx) B ARcfx D fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) wk /\
  (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
Proof.
intros D fxk ly S Hp W regs mem md k wk STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HB HSTK1 HSTKb HJ2 HJ1 HP.
destruct (cnb_entry_facts B ARcfx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
pose proof cnb_stk_val as HSTKv. pose proof asan_consts as (C1 & _).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
destruct HB as (Hz & Hk & HJ & HF & HSV & R3 & R4 & HROD).
pose proof HJ as (WS & HJW & _). pose proof HJ2 as (WS2 & HJW2 & _).
pose proof (ajx_ar HJW) as HAR. pose proof (ajx_ly HJW) as Hly.
pose proof (ajx_ar HJW2) as HAR2. pose proof (ajx_ly HJW2) as Hly2.
pose proof (ajx_frs HJ1) as Hfrs1. pose proof (ajx_hi HJ1) as G1. pose proof (ajx_blk HJ1) as G2.
pose proof (ajx_img HJ1) as G3. pose proof (ajx_frm HJ1) as G4.
assert (EF1 : ly_F ly = ly_F (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
assert (EF2 : ly_F ly2 = ly_F (bi_ly D)) by (unfold layout_le in Hly2; ro_from Hly2).
assert (EFa1 : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite EF1; reflexivity).
assert (EFa2 : frame_addr ly2 CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite EF2; reflexivity).
assert (EFl : flag_addr ly2 CNB_CID (bi_fpos D) = flag_addr ly CNB_CID (bi_fpos D))
  by (unfold flag_addr; rewrite EF1, EF2; reflexivity).
assert (EFB : fs_frame_bytes CNB_CID = 512) by reflexivity.
destruct HF as (Hfrs & Hnin & Hflag & Hfpres & Hspres).
assert (Hfrs2 : frames S2 = (CNB_CID, bi_fpos D) :: frames (bi_S D)) by (rewrite Hfrs1; exact Hfrs).
assert (Hin3 : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hin3' : In (CNB_CID, bi_fpos D) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp2 W2 mem2 md2 CNB_CID (bi_fpos D) HAR2 Hin3')
  as (_ & _ & Hfb2 & Hsh2).
rewrite EFa2, EFB in Hfb2, Hsh2.
destruct (frames_bounds_x SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
rewrite EFa1 in HF4096, HFceil. rewrite EFB in HFceil.
assert (KF : forall a, cnb_F D <= a < cnb_F D + 512 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CNB_CID (bi_fpos D) a Hin3); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa1, EFB; lia |].
  exact (inFP_nil a). }
assert (KT : forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply G1; lia. }
assert (KI : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Hro Hown Herr. apply G3.
  + destruct Hro as [(sg & Hsg & _ & Hb) | Hrel]; [exists sg; split; [exact Hsg | exact Hb] | exact (pa_relro_img a Hrel)].
  + exact Hown.
  + exact Herr.
  + intros Hpst. exact (cnbi_pst_rw B IMG a Hpst Hro).
  + intros (r & Hr & _). destruct Hr. }
split; [|exact KT].
split; [exact Hz|]. split; [exact Hk|]. split; [exact HJ2|].
split.
{ split; [exact Hfrs2|]. split; [exact Hnin|]. split.
  - rewrite EFl, <- Hflag. apply (ro_rdword_kept _ _ (cnb_F D) (cnb_F D + 512)); [exact KF| rewrite EFB; lia | rewrite EFB; lia].
  - split.
    + intros a Ha. rewrite EFB in Ha. exact (proj1 (Hfb2 a Ha)).
    + intros a Ha. rewrite EFB in Ha. replace a with (shadow_addr (cnb_F D) + (a - shadow_addr (cnb_F D))) by lia.
      apply (proj1 (Hsh2 (a - shadow_addr (cnb_F D)) ltac:(change (512 / 8) with 64 in *; lia))). }
split.
{ unfold cnb_saved in *. apply Forall_forall. intros [o r] Hin.
  pose proof (proj1 (Forall_forall _ _) HSV (o, r) Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 56 <= o <= 152) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
  rewrite <- Hv. apply (ro_rdword_kept _ _ (cnb_S1 D) (cnb_sp0 D)); [exact KT | lia | lia]. }
split; [exact (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) R3)|].
split; [exact (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) R4)|].
intros a Hro Hown Herr. rewrite <- (HROD a Hro Hown Herr). exact (KI a Hro Hown Herr).
Qed.

(* a copy taken earlier survives a later call that keeps its block: its bytes by the callee journal's block clause,
   its shadow by the state's own law (cb2_src_home at the block home) *)
Lemma cb2_copy_keep : forall D ly S Hp (W : world SEGS) mem ly2 S2 (W2 : world SEGS) mem2 md2 Lam peak cnt fail ran most
  own r,
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2)) ->
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
     aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)) ->
  ARcfx ly2 S2 Hp W2 mem2 md2 -> prh_ledger B ly2 S2 Hp W2 mem2 Lam peak cnt fail ran most own ->
  cnb_copy B D ly S Hp W mem r -> cnb_copy B D ly2 S2 Hp W2 mem2 r.
Proof.
intros D ly S Hp W mem ly2 S2 W2 mem2 md2 Lam peak cnt fail ran most own r Hinc KB HAR2 HL2 [Hr0 | (Hin & Hnh & Hsrc)];
  [left; exact Hr0|].
right. pose proof (Hinc _ Hin) as Hin2. split; [exact Hin2|]. split; [exact Hnh|].
destruct Hsrc as (Hby & H4096 & Hceil' & Hamr & _).
pose proof (req_size_pos (cnb_size D + 16) ltac:(unfold cnb_size; lia)) as (_ & Hq).
apply (cb2_src_home ly2 S2 Hp W2 mem2 md2 Lam peak cnt fail ran most own r (bi_x D) HAR2 HL2);
  [| exact H4096 | exact Hceil' | exact Hamr |].
- unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W2 mem2) r (bi_x D) Hby).
  intros z Hz. apply (mbyte_of_aview SEGS). replace z with (r + (z - r)) by lia.
  apply (KB r _ (z - r) Hin Hin2). unfold cnb_size in *. lia.
- intros _. right. exists r, (cnb_size D + 16). split; [exact Hin2|]. split; [exact Hnh|]. unfold cnb_size. lia.
Qed.

(* ==== THE STATE BETWEEN THE CALLS: cs the copies taken so far, own the g_own_ran_out byte (not 0 only after a
   refused copy, which is then dead at a consumer run: cb2_dead); the hull budget with the 3 - length cs copies'
   mallocs still to pay, then the contract's cnb_hrest_copies ==== *)
Definition cb2_inv (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (cs : list Z) (own : Z) : Prop :=
  cnb_base (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D)]) /\
  rdword (aview SEGS (w_H W) mem) (cnb_S1 D + 48) = Some (cnb_F D) /\
  cnb_pre_mid B D ly S Hp W mem own /\ (own = 0 -> Forall (fun r => r <> 0) cs) /\ (own <> 0 -> cnb_cdead D) /\
  cnb_prog D (map (fun _ => PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)) (cb2_cbl D cs)) S /\
  Permutation (ablocks B ly S) (cb2_cbl D cs ++ ablocks B (bi_ly D) (bi_S D)) /\
  Forall (cnb_copy B D ly S Hp W mem) cs /\
  blocks_bytes S + (3 - Z.of_nat (length cs)) * (cnb_size D + 16) + 3 * PRH_FnPj.LIVE_pj_parse (bi_x D) <= LIVE_MAX /\
  PresetHullBudget.hull_budget S (repeat (cnb_hmal (bi_x D)) (3 - length cs)%nat ++ cnb_hrest_copies (bi_x D)).

(* a hand step that writes a0 / a1 / a2 / ra / s9 keeps it *)
Lemma cb2_inv_upd : forall D fxk ly S Hp (W : world SEGS) regs mem md k cs own (r : bv 5) v X,
  In r [1%bv; 10%bv; 11%bv; 12%bv; 25%bv] ->
  cb2_inv D fxk ly S Hp W regs mem md k cs own ->
  cb2_inv D fxk ly S Hp W (regupd regs r v) mem (with_vm_backing (m_vm_lazy md) X md) k cs own.
Proof.
intros D fxk ly S Hp W regs mem md k cs own r v X Hr (HB & HR & HS48 & HM & HO0 & HOD & HRP & HPA & HC & HBB).
assert (E3 : getr (regupd regs r v) 3%bv = getr regs 3%bv)
  by (apply ro_getr_other; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity).
assert (E4 : getr (regupd regs r v) 4%bv = getr regs 4%bv)
  by (apply ro_getr_other; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity).
split; [exact (cnb_base_mat B ARcfx LAWS D fxk ly S Hp W regs _ mem md k 0 X HB E3 E4)|].
split.
{ apply cb2_regsat_upd; [exact HR|]. unfold cnb_core. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [app];
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; reflexivity. }
exact (conj HS48 (conj HM (conj HO0 (conj HOD (conj HRP (conj HPA (conj HC HBB))))))).
Qed.

(* the stores at s1 + 16 / s1 + 24 keep it: below the saved words, above the ceiling *)
Lemma cb2_inv_st8 : forall D fxk ly S Hp (W : world SEGS) regs mem md k cs own o v X,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> (o = 16 \/ o = 24) ->
  cb2_inv D fxk ly S Hp W regs mem md k cs own ->
  cb2_inv D fxk ly S Hp W regs (cb2_st8 (w_H W) mem (cnb_S1 D + o) v) (with_vm_backing (m_vm_lazy md) X md) k cs own.
Proof.
intros D fxk ly S Hp W regs mem md k cs own o v X HPRE Ho (HB & HR & HS48 & HM & HO0 & HOD & HRP & HPA & HC & HBB).
destruct (cnb_entry_facts B ARcfx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
pose proof cnb_stk_val as HSTKv. pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
assert (Hc : YM05.alloc_ceiling <= cnb_S1 D + o) by lia.
assert (HAlow : forall z, 0 <= z < YM05.alloc_ceiling ->
  aview SEGS (w_H W) (cb2_st8 (w_H W) mem (cnb_S1 D + o) v) z = aview SEGS (w_H W) mem z)
  by (intros z Hz; apply cb2_st8_low; [exact Hc | lia | exact Hz]).
pose proof (cb2_base_st8 D fxk ly S Hp W regs mem md k 0 (cnb_S1 D + o) v X HPRE HB ltac:(lia) ltac:(lia)) as HB2.
pose proof HB as (_ & _ & (WS & HJW & _) & _). pose proof (ajx_ar HJW) as HAR.
pose proof HB2 as (_ & _ & (WS2 & HJW2 & _) & _). pose proof (ajx_ar HJW2) as HAR2.
destruct HM as (EHp & HLED & HRL & HSRC & HHOME).
assert (HLED2 : prh_ledger B ly S Hp W (cb2_st8 (w_H W) mem (cnb_S1 D + o) v) (bi_Lam D) (bi_peak D) (bi_cnt D)
  SIZE_MAXZ (bi_ran D) (bi_most D) own) by exact (cb2_ledger_low ly S Hp W mem _ md _ _ _ _ _ _ _ HAR HAlow HLED).
split; [exact HB2|]. split; [exact HR|].
split.
{ rewrite <- HS48. apply (ro_rdword_kept _ _ (cnb_S1 D + o + 8) (2 ^ 64)); [|lia|lia].
  intros z Hz. apply cb2_st8_aview; lia. }
split.
{ split; [exact EHp|]. split; [exact HLED2|]. split; [exact HRL|].
  split; [|exact HHOME].
  destruct HSRC as (Hby & H4 & Hcl & Ham & _).
  apply (cb2_src_home ly S Hp W _ _ (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) own (bi_data D)
    (bi_x D)
    HAR2 HLED2); [|exact H4|exact Hcl|exact Ham|exact HHOME].
  apply (cb2_bytes_low W mem _ _ _ HAlow); [lia | lia | exact Hby]. }
split; [exact HO0|]. split; [exact HOD|]. split; [exact HRP|]. split; [exact HPA|].
split; [|exact HBB].
apply Forall_impl with (P := cnb_copy B D ly S Hp W mem); [|exact HC].
intros r [Hr0 | (Hin & Hnh & Hsrc)]; [left; exact Hr0|]. right. split; [exact Hin|]. split; [exact Hnh|].
destruct Hsrc as (Hby & H4 & Hcl & Ham & _).
apply (cb2_src_home ly S Hp W _ _ (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) own r (bi_x D) HAR2
  HLED2);
  [|exact H4|exact Hcl|exact Ham|].
- apply (cb2_bytes_low W mem _ _ _ HAlow); [lia | lia | exact Hby].
- intros _. right. exists r, (cnb_size D + 16). split; [exact Hin|]. split; [exact Hnh|]. unfold cnb_size. lia.
Qed.

(* ==== THE REFUSED COPY IS DEAD AT A CONSUMER RUN (the cut's `own0 <> 0 -> cnb_cdead D`): at a call state S that has
   made the granted copies' events E since entry (k = length E <= 2 of them), padded's outcome clause there (any run
   position at S whose next event is the copy's HMal (size + 16), a consumer event, has res <> 0) and a NULL return
   (res = 0) refute every model run and position i at the entry state whose next events are the three copies, each a
   consumer event: the copies are E ++ [HMal (size + 16)] ++ the rest, the progress fact makes i + k a position of S,
   the run's next event there is the copy's (prh_run_at_app_iff) and its one-event window a consumer one
   (prh_cons_from_sub) ==== *)
Lemma cb2_dead : forall D S S' cs res, (length (cb2_cbl D cs) <= 2)%nat ->
  cnb_prog D (map (fun _ => PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)) (cb2_cbl D cs)) S ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S ->
     PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (Z.of_nat (length (bi_x D)) + 16)] ->
     PRH_Base.prh_cons_from sm x0 os i (length [PresetReqAt.HMal (Z.of_nat (length (bi_x D)) + 16)]) ->
     res <> 0 /\
     exists hist', PresetRoomPos.iface_room_pos sm x0 os
       (i + length [PresetReqAt.HMal (Z.of_nat (length (bi_x D)) + 16)])%nat H0 hist' S') ->
  res = 0 -> cnb_cdead D.
Proof.
intros D S S' cs res Hk (_ & HP) HOUT Hres sm x0 os i H0 hist Hpos Hrun Hcons.
pose (m := PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)).
assert (EC : ck_cno_copies (bi_x D) =
  map (fun _ => m) (cb2_cbl D cs) ++ [m] ++ repeat m (2 - length (cb2_cbl D cs))).
{ rewrite cb2_map_const. change [m] with (repeat m 1). rewrite <- !repeat_app.
  replace (length (cb2_cbl D cs) + (1 + (2 - length (cb2_cbl D cs))))%nat with 3%nat by lia. reflexivity. }
rewrite EC in Hrun, Hcons. apply prh_run_at_app_iff in Hrun as (R1 & R2).
apply prh_run_at_app_iff in R2 as (R3 & _).
destruct (HP sm x0 os i H0 hist Hpos R1) as (hist1 & Hpos1).
assert (Hc1 : prh_cons_from sm x0 os (i + length (map (fun _ => m) (cb2_cbl D cs))) 1).
{ apply (prh_cons_from_sub sm x0 os i
    (length (map (fun _ => m) (cb2_cbl D cs) ++ [m] ++ repeat m (2 - length (cb2_cbl D cs))))
    (length (map (fun _ => m) (cb2_cbl D cs))) 1); [|exact Hcons].
  rewrite !length_app, repeat_length, length_map. cbn [length]. lia. }
destruct (HOUT sm x0 os (i + length (map (fun _ => m) (cb2_cbl D cs)))%nat H0 hist1 Hpos1 R3 Hc1) as (Hr & _).
exact (Hr Hres).
Qed.

(* ==== ONE COPY: the padded call from its entry to its return site, the state facts carried ==== *)
Lemma cb2_round : forall (P : (word -> option byte) -> Prop), srr_inv_call SEGS P ->
  forall D fxk ly S Hp (W : world SEGS) regs mem md k cs own ret fill,
  cnb_pre (fx := fx) B ARcfx CTX0 D -> In ret cb2_rets ->
  (length cs < 3)%nat ->
  cb2_inv D fxk ly S Hp W regs mem md k cs own ->
  getr regs 1%bv = w64 (cnb_pc ret) -> getr regs 10%bv = w64 (bi_data D) -> getr regs 11%bv = w64 (cnb_size D) ->
  getr regs 12%bv = w64 fill -> 0 <= fill < 2 ^ 64 -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (SIGMA AS_padded) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' k' res own',
       c' = @cnb_cfg SEGS fxk (cnb_pc ret) regs' mem' md' /\
       cb2_inv D fxk ly' S' Hp W' regs' mem' md' k' (cs ++ [res]) own' /\
       aregs_preserved regs regs' /\ getr regs' 10%bv = w64 res /\ 0 <= res < 2 ^ 64 /\
       (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
       P mem').
Proof.
intros P PCALL D fxk ly S Hp W regs mem md k cs own ret fill HPRE Hret Hlen HI R1 R10 R11 R12 Hfill HPM.
destruct HI as (HB & HR & HS48 & HM & HO0 & HOD & HRP & HPA & HC & HBB & HH).
destruct (cnb_entry_facts B ARcfx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
pose proof cnb_stk_val as HSTKv. pose proof cb2_stk as (HSTKp & HSTKp0). pose proof asan_consts as (C1 & _).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
pose proof (cb2_live_nonneg (bi_x D)) as HL0.
pose proof (cb2_cbl_len D cs) as Hcl.
pose proof (Nat2Z.is_nonneg (length (bi_x D))) as Hx0.
pose proof HM as (EHp & HLED & HRL & HSRC & HHOME).
assert (R2 : getr regs 2%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get regs _ _ _ HR); ro_in).
assert (R8 : getr regs 8%bv = w64 (cnb_sp0 D)) by (apply (cnb_regsat_get regs _ _ _ HR); ro_in).
assert (HBB1 : blocks_bytes S + (cnb_size D + 16) <= LIVE_MAX).
{ assert (Hlc : (length cs <= 2)%nat) by lia. unfold cnb_size in *. nia. }
(* padded's live counts at THIS call's state, from the progress fact and cnb_pre's peak bounds *)
assert (HCNT : YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV)
  by (apply (cb2_counts D S cs HPRE); [lia | exact HRP]).
(* THE HULL PAYMENT of this copy (cnb_hpay_copy): padded's premise from the budget's head, and after the call the
   budget for the rest from padded's hull use *)
assert (HHs : PresetHullBudget.hull_budget S
  (cnb_hmal (bi_x D) :: (repeat (cnb_hmal (bi_x D)) (2 - length cs)%nat ++ cnb_hrest_copies (bi_x D)))).
{ assert (E3 : (3 - length cs)%nat = (1 + (2 - length cs))%nat) by lia. rewrite E3 in HH. exact HH. }
destruct (cnb_hpay_copy S (bi_x D) _ HHs) as (HHpad & HHpay).
assert (El : forall r : Z, (3 - length (cs ++ [r]))%nat = (2 - length cs)%nat)
  by (intros r; rewrite length_app; cbn [length]; lia).
eapply SRr_bind.
{ exact (cb2_pad_call P PCALL D fxk ly S Hp W regs mem md k 0 (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D)
    (bi_most D) own ret fill HPRE Hret HB R2 R8 R1 R10 R11 R12 Hfill HRL
    (proj1 HCNT) (proj2 HCNT) HHpad HSRC HHOME HBB1 HLED HPM). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HP2 & HQ & HMN).
unfold cb2_padQ in HQ. cbv zeta in HQ.
destruct HQ as (res & own2 & R10' & HRL2 & EHp2 & HU2 & HLED2 & HDAT2 & HOUT & HARM). subst Hp2.
pose proof (HHpay S2 HU2) as HH2.
assert (HK1 : 0 <= STK_padded) by lia.
assert (HK2 : STK_padded + (cnb_sp0 D - cnb_S1 D) <= STK) by lia.
destruct (cb2_base_keep D fxk ly S Hp W regs mem md k 0 STK_padded ly2 S2 Hp W2 regs2 mem2 md2 k1 HPRE HB
  HK1 HK2 HJ2 HJ1 HP2) as (HB2 & KT).
pose proof HJ2 as (WS2 & HJW2 & _). pose proof (ajx_ar HJW2) as HAR2.
pose proof (ajx_blk HJ1) as G2.
assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i))
  by (intros p n i H1 H2 Hi; exact (G2 p n i H1 H2 Hi (inFP_nil _))).
assert (HR2 : cnb_regsat regs2 (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D)]))
  by exact (cnb_regsat_pres regs regs2 _ HR HP2 (cb2_regs_saved D _ (cb2_s78_saved _ _))).
assert (HS48' : rdword (aview SEGS (w_H W2) mem2) (cnb_S1 D + 48) = Some (cnb_F D))
  by exact (cnb_slot_agree D W mem W2 mem2 48 (cnb_F D) Hal16 ltac:(lia) KT HS48).
assert (Hincl : forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2)).
{ destruct HARM as [(_ & _ & EAB & _) | (_ & _ & _ & _ & _ & HPm & _)].
  - rewrite EAB. tauto.
  - intros b Hb. apply (Permutation_in _ (Permutation_sym HPm)). right. exact Hb. }
assert (HSRC2 : src_rd W2 mem2 (bi_data D) (bi_x D)).
{ destruct HSRC as (_ & H4 & Hcl' & Ham & _).
  apply (cb2_src_home ly2 S2 Hp W2 mem2 md2 (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) own2
    (bi_data D) (bi_x D)
    HAR2 HLED2 HDAT2 H4 Hcl' Ham).
  intros Hn. exact (cb2_home_lift ly S Hp ly2 S2 (bi_Lam D) _ _ Hincl (HHOME Hn)). }
assert (HM2 : cnb_pre_mid B D ly2 S2 Hp W2 mem2 own2).
{ split; [exact EHp|]. split; [exact HLED2|]. split; [exact HRL2|].
  split; [exact HSRC2|]. intros Hn. exact (cb2_home_lift ly S Hp ly2 S2 (bi_Lam D) _ _ Hincl (HHOME Hn)). }
assert (HC2 : Forall (cnb_copy B D ly2 S2 Hp W2 mem2) cs).
{ apply Forall_impl with (P := cnb_copy B D ly S Hp W mem); [|exact HC].
  intros r Hr. exact (cb2_copy_keep D ly S Hp W mem ly2 S2 W2 mem2 md2 (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ
    (bi_ran D) (bi_most D) own2 r Hincl KB HAR2 HLED2 Hr). }
apply SRr_ret.
destruct HARM as [(Er & Eo & EAB & HRP2 & _ & _) | (Hr0 & Eo & Hr4096 & Hrc & _ & HPm & Hrh & Hby & _ & Hra & Hhv & HEV)].
- (* P0: the copy is NULL, g_own_ran_out = 1, the position kept *)
  subst res own2.
  exists ly2, S2, regs2, mem2, md2, (k + k1), 0, 1.
  split; [reflexivity|].
  split.
  { split; [exact HB2|]. split; [exact HR2|]. split; [exact HS48'|]. split; [exact HM2|].
    split; [intros H; discriminate H|].
    split; [intros _; exact (cb2_dead D S S2 cs 0 ltac:(lia) HRP HOUT eq_refl)|].
    rewrite cb2_cbl_app1. assert (E0 : cnb_cblk D 0 = []) by reflexivity. rewrite E0, app_nil_r.
    split.
    { apply (cnb_prog_eq D (map (fun _ => PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)) (cb2_cbl D cs) ++ [])
        _ S2 (app_nil_r _)).
      apply (cnb_prog_app D _ [] S S2 HRP); [|exact HRP2].
      rewrite PresetReqAt.hlive_from_nil. unfold YGcfRoom.room_of_cf. cbn [PresetRoom.rs_live].
      rewrite <- (cb2_ablocks_snd ly2 S2), <- (cb2_ablocks_snd ly S), EAB. apply Permutation_refl. }
    split; [rewrite EAB; exact HPA|].
    split; [apply Forall_app; split; [exact HC2 | constructor; [left; reflexivity | constructor]]|].
    split.
    { rewrite (cb2_bb ly2 S2), EAB, <- (cb2_bb ly S).
      rewrite length_app. cbn [length]. unfold cnb_size in *. nia. }
    (* the hull budget: one copy's malloc paid (HH2) *)
    rewrite El. exact HH2. }
  split; [exact HP2|]. split; [exact R10'|]. split; [lia|]. split; [exact KT|].
  exact HMN.
- (* P1: a fresh RAW block of size + 16 holding x, the position advanced by the run's HMal *)
  subst own2.
  assert (Ec : cnb_cblk D res = [(res, cnb_size D + 16)]).
  { unfold cnb_cblk. rewrite (proj2 (Z.eqb_neq res 0) Hr0). reflexivity. }
  assert (Hin2 : In (res, cnb_size D + 16) (ablocks B ly2 S2)).
  { apply (Permutation_in _ (Permutation_sym HPm)). left. reflexivity. }
  exists ly2, S2, regs2, mem2, md2, (k + k1), res, own.
  split; [reflexivity|].
  split.
  { split; [exact HB2|]. split; [exact HR2|]. split; [exact HS48'|]. split; [exact HM2|].
    split; [intros H0; apply Forall_app; split; [exact (HO0 H0) | constructor; [exact Hr0 | constructor]]|].
    split; [exact HOD|].
    rewrite cb2_cbl_app1, Ec.
    split.
    { rewrite map_app. cbn [map].
      apply (cnb_prog_app D _ [PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)] S S2 HRP); [|exact HEV].
      unfold PresetReqAt.hlive_from. cbn [fold_left PresetReqAt.hstep].
      unfold YGcfRoom.room_of_cf. cbn [PresetRoom.rs_live].
      rewrite <- (cb2_ablocks_snd ly2 S2), <- (cb2_ablocks_snd ly S).
      apply (Permutation_map snd) in HPm. cbn [map snd] in HPm. exact HPm. }
    split.
    { rewrite <- app_assoc. cbn [app].
      eapply Permutation_trans; [exact HPm|].
      eapply Permutation_trans; [apply perm_skip; exact HPA|].
      apply Permutation_middle. }
    split.
    { apply Forall_app. split; [exact HC2|]. constructor; [|constructor]. right.
      split; [exact Hin2|]. split.
      - intros Hh. apply (Permutation_in _ (prh_ledger_heads B ly S Hp W mem _ _ _ _ _ _ _ HLED)) in Hh.
        apply in_map_iff in Hh as ((a & kk) & Ea & Hak). cbn [fst] in Ea. exact (Hrh a kk Hak Ea).
      - destruct (alx_blocks SEGS B ARcfx LAWS ly2 S2 Hp W2 mem2 md2 _ _ HAR2 Hin2) as (_ & _ & _ & Happ & _).
        pose proof (req_size_pos (cnb_size D + 16) ltac:(unfold cnb_size; lia)) as (_ & Hq).
        split; [exact (cb2_garr8_prefix SEGS (rdW W2 mem2) res (bi_x D) _ Hby)|].
        split; [exact Hr4096|].
        split; [unfold cnb_size in *; lia|].
        split.
        { unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
          unfold cnb_size in *. lia. }
        split.
        { apply (range_addressable_sub _ _ res (cnb_size D + 16)); [exact Hra | lia | unfold cnb_size; lia]. }
        intros Hn. apply (ro_hull_mono _ res (cnb_size D + 16)); [unfold cnb_size in *; lia | exact Hhv]. }
    split.
    { rewrite (cb2_bb ly2 S2), (bsum_perm _ _ HPm), bsum_cons, <- (cb2_bb ly S). cbn [fst snd].
      rewrite length_app. cbn [length]. unfold cnb_size in *. nia. }
    (* the hull budget: one copy's malloc paid (HH2) *)
    rewrite El. exact HH2. }
  split; [exact HP2|]. split; [exact R10'|]. split; [lia|]. split; [exact KT|].
  exact HMN.
Qed.

(* ==== THE SEGMENT LEMMA: CB2 Copies, 0x81b80 (CNB_COPY) -> 0x81bbc (CNB_INIT), the contract's FORWARD form ==== *)
Lemma cnb_seg_copies : forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp (W : world SEGS) regs mem md k,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_copy (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc CNB_COPY) regs mem md)
    (fun W' c' => cnb_ex_init (fx := fx) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k HPRE HAT HPM.
destruct (cnb_entry_facts B ARcfx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
pose proof cnb_stk_val as HSTKv. pose proof asan_consts as (C1 & _).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
destruct (cb2_pre_facts D HPRE) as (_ & _ & Hsz3 & Hcf & HLV).
(* the start cut cnb_at_copy, each conjunct picked BY ITS TYPE *)
assert (HI0 : cb2_inv D fxk ly S Hp W regs mem md k [] 0).
{ unfold cnb_at_copy in HAT.
  assert (HB : cnb_base (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k 0) by ro_from HAT.
  assert (HR : cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D)])) by ro_from HAT.
  assert (HS48 : rdword (aview SEGS (w_H W) mem) (cnb_S1 D + 48) = Some (cnb_F D)) by ro_from HAT.
  assert (HM : cnb_pre_mid B D ly S Hp W mem 0) by ro_from HAT.
  assert (HRP : cnb_prog D [] S) by ro_from HAT.
  assert (HAB : ablocks B ly S = ablocks B (bi_ly D) (bi_S D)) by ro_from HAT.
  assert (HBB : blocks_bytes S = blocks_bytes (bi_S D)) by ro_from HAT.
  assert (HH : PresetHullBudget.hull_budget S (cnb_hev_all (bi_x D))) by ro_from HAT.
  split; [exact HB|]. split; [exact HR|]. split; [exact HS48|]. split; [exact HM|].
  split; [intros _; constructor|].
  split; [intros H0; exfalso; apply H0; reflexivity|].
  unfold cb2_cbl. cbn [map concat length app].
  split; [exact HRP|].
  split; [rewrite HAB; apply Permutation_refl|].
  split; [constructor|].
  split; [rewrite HBB; unfold LIVE_check_no_overread in HLV; unfold cnb_size; cbn [Z.of_nat]; lia|].
  (* the hull budget: the three copies' mallocs, then cnb_hrest_copies (the contract's splits) *)
  rewrite cnb_hrest_cpy1_split, cnb_hrest_cpy2_split, cnb_hrest_copies_split in HH. exact HH. }
pose proof HI0 as (_ & HR0 & _).
assert (G23 : getr regs 23%bv = w64 (cnb_size D)) by (apply (cnb_regsat_get regs _ _ _ HR0); ro_in).
assert (G24 : getr regs 24%bv = w64 (bi_data D)) by (apply (cnb_regsat_get regs _ _ _ HR0); ro_in).
(* ---- copy 1: `li a2, '1'; mv a0, s8; mv a1, s7; jal padded` ---- *)
apply (cnb_hs_addi W fxk regs mem md _ 400 404 12%bv 0%bv 49 cb2_c400); [reflexivity | lia | reflexivity |]. intros X1.
apply (cnb_hs_addi W fxk _ mem _ _ 404 408 10%bv 24%bv 0 cb2_c404); [reflexivity | lia | reflexivity |]. intros X2.
apply (cnb_hs_addi W fxk _ mem _ _ 408 412 11%bv 23%bv 0 cb2_c408); [reflexivity | lia | reflexivity |]. intros X3.
apply (cnb_hs_call W fxk _ mem _ _ 412 416 AS_padded cb2_c412); [lia | reflexivity |]. intros X4.
match goal with |- SRr _ _ (@cnb_cfg _ _ _ ?R _ ?M) _ => set (regs4 := R); set (md4 := M) end.
assert (HI4 : cb2_inv D fxk ly S Hp W regs4 mem md4 k [] 0).
{ unfold regs4, md4. apply cb2_inv_upd; [ro_in|]. apply cb2_inv_upd; [ro_in|].
  apply cb2_inv_upd; [ro_in|]. apply cb2_inv_upd; [ro_in|]. exact HI0. }
assert (R4_1 : getr regs4 1%bv = w64 (cnb_pc 416)) by (unfold regs4; ro_getr; reflexivity).
assert (R4_10 : getr regs4 10%bv = w64 (bi_data D)) by (unfold regs4; ro_getr; rewrite cb2_mv; ro_getr; exact G24).
assert (R4_11 : getr regs4 11%bv = w64 (cnb_size D)) by (unfold regs4; ro_getr; rewrite cb2_mv; ro_getr; exact G23).
assert (R4_12 : getr regs4 12%bv = w64 49) by (unfold regs4; ro_getr; apply cb2_li; lia).
assert (Hrt1 : In 416 cb2_rets) by (unfold cb2_rets; ro_in).
assert (Hl1 : (length (@nil Z) < 3)%nat) by (cbn; lia).
assert (Hf1 : 0 <= 49 < 2 ^ 64) by lia.
eapply SRr_bind.
{ exact (cb2_round P PCALL D fxk ly S Hp W regs4 mem md4 k [] 0 416 49 HPRE Hrt1 Hl1 HI4 R4_1 R4_10 R4_11
    R4_12 Hf1 HPM). }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & k5 & r1 & own1 & -> & HI5 & HP5 & R5_10 & Hr1 & KT5 & HPM5).
cbn [app] in HI5.
pose proof HI5 as (_ & HR5 & _).
assert (G5_23 : getr regs5 23%bv = w64 (cnb_size D)) by (apply (cnb_regsat_get regs5 _ _ _ HR5); ro_in).
assert (G5_24 : getr regs5 24%bv = w64 (bi_data D)) by (apply (cnb_regsat_get regs5 _ _ _ HR5); ro_in).
(* ---- `mv s9, a0`; copy 2: `li a2, '2'; mv a0, s8; mv a1, s7; jal padded` ---- *)
apply (cnb_hs_addi W5 fxk regs5 mem5 md5 _ 416 420 25%bv 10%bv 0 cb2_c416); [reflexivity | lia | reflexivity |]. intros X6.
apply (cnb_hs_addi W5 fxk _ mem5 _ _ 420 424 12%bv 0%bv 50 cb2_c420); [reflexivity | lia | reflexivity |]. intros X7.
apply (cnb_hs_addi W5 fxk _ mem5 _ _ 424 428 10%bv 24%bv 0 cb2_c424); [reflexivity | lia | reflexivity |]. intros X8.
apply (cnb_hs_addi W5 fxk _ mem5 _ _ 428 432 11%bv 23%bv 0 cb2_c428); [reflexivity | lia | reflexivity |]. intros X9.
apply (cnb_hs_call W5 fxk _ mem5 _ _ 432 436 AS_padded cb2_c432); [lia | reflexivity |]. intros X10.
match goal with |- SRr _ _ (@cnb_cfg _ _ _ ?R _ ?M) _ => set (regs10 := R); set (md10 := M) end.
assert (HI10 : cb2_inv D fxk ly5 S5 Hp W5 regs10 mem5 md10 k5 [r1] own1).
{ unfold regs10, md10. apply cb2_inv_upd; [ro_in|]. apply cb2_inv_upd; [ro_in|].
  apply cb2_inv_upd; [ro_in|]. apply cb2_inv_upd; [ro_in|]. apply cb2_inv_upd; [ro_in|]. exact HI5. }
assert (Q10 : cnb_regsat regs10 [(25%bv, r1)]).
{ unfold regs10. repeat (apply cb2_regsat_upd; [|repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; reflexivity]).
  unfold cnb_regsat. repeat apply Forall_cons; try apply Forall_nil. cbn [fst snd].
  rewrite ro_getr_same by reflexivity. rewrite cb2_mv.
  exact R5_10. }
assert (R10_1 : getr regs10 1%bv = w64 (cnb_pc 436)) by (unfold regs10; ro_getr; reflexivity).
assert (R10_10 : getr regs10 10%bv = w64 (bi_data D)) by (unfold regs10; ro_getr; rewrite cb2_mv; ro_getr; exact G5_24).
assert (R10_11 : getr regs10 11%bv = w64 (cnb_size D)) by (unfold regs10; ro_getr; rewrite cb2_mv; ro_getr; exact G5_23).
assert (R10_12 : getr regs10 12%bv = w64 50) by (unfold regs10; ro_getr; apply cb2_li; lia).
assert (Hrt2 : In 436 cb2_rets) by (unfold cb2_rets; ro_in).
assert (Hl2 : (length [r1] < 3)%nat) by (cbn; lia).
assert (Hf2 : 0 <= 50 < 2 ^ 64) by lia.
eapply SRr_bind.
{ exact (cb2_round P PCALL D fxk ly5 S5 Hp W5 regs10 mem5 md10 k5 [r1] own1 436 50 HPRE Hrt2 Hl2 HI10 R10_1
    R10_10 R10_11 R10_12 Hf2 HPM5). }
cbv beta. intros W11 c11 _ (ly11 & S11 & regs11 & mem11 & md11 & k11 & r2 & own2 & -> & HI11 & HP11 & R11_10 & Hr2
  & KT11 & HPM11).
cbn [app] in HI11.
pose proof HI11 as (HB11 & HR11 & _).
assert (Q11 : cnb_regsat regs11 [(25%bv, r1)]) by exact (cnb_regsat_pres regs10 regs11 _ Q10 HP11 (cb2_s9_saved r1)).
assert (G11_9 : getr regs11 9%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get regs11 _ _ _ HR11); ro_in).
assert (G11_23 : getr regs11 23%bv = w64 (cnb_size D)) by (apply (cnb_regsat_get regs11 _ _ _ HR11); ro_in).
assert (G11_24 : getr regs11 24%bv = w64 (bi_data D)) by (apply (cnb_regsat_get regs11 _ _ _ HR11); ro_in).
(* ---- `sd a0, 0x18(s1)`: r2 at s1 + 24 ---- *)
assert (HPRES11 : forall j, 0 <= j < 8 -> apresent (w_H W11) mem11 (cnb_S1 D + 24 + j)).
{ pose proof HB11 as (_ & _ & (WS11 & HJW11 & _) & _). pose proof (ajx_pres HJW11) as Hpres.
  intros j Hj. apply Hpres. lia. }
assert (Hpres24 : forall j, (j < 8)%nat -> w_H W11 (Z_to_bv 64 (cnb_S1 D + 24 + Z.of_nat j)) = false)
  by (intros j Hj; exact (proj1 (HPRES11 (Z.of_nat j) ltac:(lia)))).
apply (cb2_hs_sd P PLAW W11 fxk regs11 mem11 md11 _ 436 440 9%bv 10%bv 24 (cnb_S1 D + 24) r2 cb2_c436);
  [lia | reflexivity | rewrite G11_9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
  | exact R11_10 | exact HPRES11 | exact HPM11 |].
intros X12 HPM12.
set (mem12 := cb2_st8 (w_H W11) mem11 (cnb_S1 D + 24) r2).
assert (HI12 : cb2_inv D fxk ly11 S11 Hp W11 regs11 mem12 (with_vm_backing (m_vm_lazy md11) X12 md11) k11 [r1; r2] own2)
  by exact (cb2_inv_st8 D fxk ly11 S11 Hp W11 regs11 mem11 md11 k11 [r1; r2] own2 24 r2 X12 HPRE (or_intror eq_refl) HI11).
assert (SL24 : rdword (aview SEGS (w_H W11) mem12) (cnb_S1 D + 24) = Some r2)
  by (apply cb2_st8_rdword; [lia | lia | exact Hr2 | exact Hpres24]).
(* ---- copy 3: `mv a0, s8; mv a1, s7; li a2, 0; jal padded` ---- *)
apply (cnb_hs_addi W11 fxk regs11 mem12 _ _ 440 444 10%bv 24%bv 0 cb2_c440); [reflexivity | lia | reflexivity |]. intros X13.
apply (cnb_hs_addi W11 fxk _ mem12 _ _ 444 448 11%bv 23%bv 0 cb2_c444); [reflexivity | lia | reflexivity |]. intros X14.
apply (cnb_hs_addi W11 fxk _ mem12 _ _ 448 452 12%bv 0%bv 0 cb2_c448); [reflexivity | lia | reflexivity |]. intros X15.
apply (cnb_hs_call W11 fxk _ mem12 _ _ 452 456 AS_padded cb2_c452); [lia | reflexivity |]. intros X16.
match goal with |- SRr _ _ (@cnb_cfg _ _ _ ?R _ ?M) _ => set (regs16 := R); set (md16 := M) end.
assert (HI16 : cb2_inv D fxk ly11 S11 Hp W11 regs16 mem12 md16 k11 [r1; r2] own2).
{ unfold regs16, md16. apply cb2_inv_upd; [ro_in|]. apply cb2_inv_upd; [ro_in|].
  apply cb2_inv_upd; [ro_in|]. apply cb2_inv_upd; [ro_in|]. exact HI12. }
assert (Q16 : cnb_regsat regs16 [(25%bv, r1)]).
{ unfold regs16. repeat (apply cb2_regsat_upd; [|repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; reflexivity]).
  exact Q11. }
assert (R16_1 : getr regs16 1%bv = w64 (cnb_pc 456)) by (unfold regs16; ro_getr; reflexivity).
assert (R16_10 : getr regs16 10%bv = w64 (bi_data D)) by (unfold regs16; ro_getr; rewrite cb2_mv; exact G11_24).
assert (R16_11 : getr regs16 11%bv = w64 (cnb_size D)) by (unfold regs16; ro_getr; rewrite cb2_mv; ro_getr; exact G11_23).
assert (R16_12 : getr regs16 12%bv = w64 0) by (unfold regs16; ro_getr; apply cb2_li; lia).
assert (Hrt3 : In 456 cb2_rets) by (unfold cb2_rets; ro_in).
assert (Hl3 : (length [r1; r2] < 3)%nat) by (cbn; lia).
assert (Hf3 : 0 <= 0 < 2 ^ 64) by lia.
eapply SRr_bind.
{ exact (cb2_round P PCALL D fxk ly11 S11 Hp W11 regs16 mem12 md16 k11 [r1; r2] own2 456 0 HPRE Hrt3 Hl3 HI16
    R16_1 R16_10 R16_11 R16_12 Hf3 HPM12). }
cbv beta. intros W17 c17 _ (ly17 & S17 & regs17 & mem17 & md17 & k17 & r3 & own3 & -> & HI17 & HP17 & R17_10 & Hr3
  & KT17 & HPM17).
cbn [app] in HI17.
pose proof HI17 as (HB17 & HR17 & _).
assert (Q17 : cnb_regsat regs17 [(25%bv, r1)]) by exact (cnb_regsat_pres regs16 regs17 _ Q16 HP17 (cb2_s9_saved r1)).
assert (G17_9 : getr regs17 9%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get regs17 _ _ _ HR17); ro_in).
assert (SL24' : rdword (aview SEGS (w_H W17) mem17) (cnb_S1 D + 24) = Some r2)
  by exact (cnb_slot_agree D W11 mem12 W17 mem17 24 r2 Hal16 ltac:(lia) KT17 SL24).
(* ---- `sd a0, 0x10(s1)`: r3 at s1 + 16 ---- *)
assert (HPRES17 : forall j, 0 <= j < 8 -> apresent (w_H W17) mem17 (cnb_S1 D + 16 + j)).
{ pose proof HB17 as (_ & _ & (WS17 & HJW17 & _) & _). pose proof (ajx_pres HJW17) as Hpres.
  intros j Hj. apply Hpres. lia. }
assert (Hpres16 : forall j, (j < 8)%nat -> w_H W17 (Z_to_bv 64 (cnb_S1 D + 16 + Z.of_nat j)) = false)
  by (intros j Hj; exact (proj1 (HPRES17 (Z.of_nat j) ltac:(lia)))).
apply (cb2_hs_sd P PLAW W17 fxk regs17 mem17 md17 _ 456 460 9%bv 10%bv 16 (cnb_S1 D + 16) r3 cb2_c456);
  [lia | reflexivity | rewrite G17_9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
  | exact R17_10 | exact HPRES17 | exact HPM17 |].
intros X18 HPM18.
set (mem18 := cb2_st8 (w_H W17) mem17 (cnb_S1 D + 16) r3).
assert (HI18 : cb2_inv D fxk ly17 S17 Hp W17 regs17 mem18 (with_vm_backing (m_vm_lazy md17) X18 md17) k17 [r1; r2; r3]
  own3) by exact (cb2_inv_st8 D fxk ly17 S17 Hp W17 regs17 mem17 md17 k17 [r1; r2; r3] own3 16 r3 X18 HPRE
  (or_introl eq_refl) HI17).
assert (SL16 : rdword (aview SEGS (w_H W17) mem18) (cnb_S1 D + 16) = Some r3)
  by (apply cb2_st8_rdword; [lia | lia | exact Hr3 | exact Hpres16]).
assert (SL24'' : rdword (aview SEGS (w_H W17) mem18) (cnb_S1 D + 24) = Some r2).
{ rewrite <- SL24'. apply (ro_rdword_kept _ _ (cnb_S1 D + 24) (2 ^ 64)); [|lia|lia].
  intros z Hz. apply cb2_st8_aview; lia. }
(* ---- CNB_INIT ---- *)
apply SRr_ret. split; [|exact HPM18].
destruct HI18 as (HB18 & HR18 & HS48 & HM18 & HO0 & HOD & HRP18 & HPA18 & HC18 & HBB18 & HH18).
exists fxk, ly17, S17, Hp, regs17, mem18, (with_vm_backing (m_vm_lazy md17) X18 md17), k17, r1, r2, r3, own3.
split; [reflexivity|].
rewrite cb2_cbl_3 in HRP18, HPA18.
apply Forall_cons_iff in HC18 as (HC1 & HC18). apply Forall_cons_iff in HC18 as (HC2 & HC18).
apply Forall_cons_iff in HC18 as (HC3 & _).
split; [exact HB18|].
split.
{ unfold cnb_regsat in *. replace (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D); (25%bv, r1)]) with
    ((cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D)]) ++ [(25%bv, r1)]) by (rewrite <- app_assoc; reflexivity).
  apply Forall_app. split; [exact HR18 | exact Q17]. }
split; [unfold cnb_slots; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption|].
split; [exact HC1|]. split; [exact HC2|]. split; [exact HC3|].
split.
{ intros H0. pose proof (HO0 H0) as HF0.
  apply Forall_cons_iff in HF0 as (N1 & HF0). apply Forall_cons_iff in HF0 as (N2 & HF0).
  apply Forall_cons_iff in HF0 as (N3 & _). exact (conj N1 (conj N2 N3)). }
(* a refused copy is dead at a consumer run (cb2_dead at its call, carried by cb2_inv) *)
split; [exact HOD|].
split; [exact HM18|]. split; [exact HRP18|]. split; [exact HPA18|].
split; [cbn [length Z.of_nat] in HBB18; lia|].
(* the hull budget: all three copies' mallocs paid, cnb_hrest_copies left *)
cbn [length Nat.sub repeat app] in HH18. exact HH18.
Qed.

End e2.
