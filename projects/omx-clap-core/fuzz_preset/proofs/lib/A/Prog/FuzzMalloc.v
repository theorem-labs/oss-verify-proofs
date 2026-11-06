(* fuzz_preset, S1 ALLOC-HEAP, image A' (asan, #102 pin 1be0f53d; fuzz_malloc at 0x85728, 97 insns, frame 32):
   fuzz_malloc's walk in cgif's per-function form over the second allocator instance ARcf, against the batch-cut text
   tfuzz_malloc_specX (lib/A/PRH_FnAlloc.v:288: the walk-kit text plus THE OUTCOME conjunct, the LIVE premise guarded by
   cnt <> fail, the hull_budget premise :294 and the hull_used conjunct :308; the cut preset-tree-at-2026-10-30T04-57-22Z.tsv
   (sha256 652fe98064b9; internal record) pinned blob 4d8aeba047e5 with PRH_Base.v ef7c8ca98529, without the hull parts), on the whole-program listing
   A_prog_listing (lib/A/Listing_prog.v, #102 pins). Ported from the old-pin walk FuzzMalloc.v.wip (blob ec4c921972f).
   Source: merged alloc.c (#102, blob bd2740a): fuzz_malloc :80-93, failing :40-46, own :48-56, refused :70-78.
   Arms: CHOSEN-FAIL (g_count = g_fail_at: g_fail_at := SIZE_MAX, return 0; prh_alloc_post arm 1); the malloc wrapper's
   NULL (REFUSED, prh_alloc_post arm 2: refused(n), NEW code 0x85824 .. 0x8586c: held = g_live + n (saturating; the
   texts' premises keep it below SIZE_MAX), g_peak := held when g_peak < held (the `sd` at 0x85848), g_ran_out := 1
   when n <= g_most (the `sb` at 0x8586c), return 0: four paths); SUCCESS (prh_alloc_post arm 3: two instrumented
   header-store checks, own's head = the 8 bytes of n, poison of the head, g_live += n, g_peak := max, return
   b + HEAD). TOOBIG and the errpath_store_n paths are excluded by the facts.
   The text's other parts: room_live_cf S' by h-mani-a8's RL_malloc_step (YGcfRoomLive.v) at the named live-set bounds
   (CfRoomLivePreset.preset_rl_sec_ok / preset_rl_b24_ok); QM_cf at the call from room_live_room; the run position in
   the text's POST-IMPLICATION form, at each arm's own event list E: E = [] at every NULL return (CHOSEN-FAIL: S' = S;
   the four REFUSED paths: h-pre-b1's room_pos_keep_alloc_null; i + length [] = i), E = [HMal (n + cf_head)] at the
   grant (room_pos_keep_alloc, the run premise turned into nth_error by PRH_Base.prh_run_at_one); the history is the
   entry's on every arm. THE OUTCOME conjunct (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a consumer
   allocation whose run event is this call's HMal (n + cf_head), with cnt <> fail, the call granted - SUCCESS proves it
   (res = b + 16 <> 0, the position by room_pos_keep_alloc); CHOSEN-FAIL refutes it by cnt = fail; the four REFUSED
   paths refute it by the kit's PRH_Refute.prh_refute_window (P8 at the call's state S, the run's event 0 of
   [HMal (n + cf_head)], and the call's granted path Hpath / Hgf as the machine-level refusal prh_granted_null).
   The LIVE premise (cnt <> fail -> ..) is used only past the CHOSEN-FAIL test, where cnt <> fail holds;
   the m-form post (fpostm) by a Theorem Labs lane's carrier m |-> (memnorm mem -> memnorm m) through the runner
   segments (YC1fPx's paj_run_x_m_inv) and across the two calls by the texts' own keeps (the malloc call by
   YGcallMxmnKeep's aj_malloc_x_ct_m_keep over the keep text YGcfMallocComposeKeep.amalloc_realizes_cf_keep, whose last
   conjunct carries memnorm across the call; the poison by YGcallMxmn's
   aj_poison_x_m); g_most and g_own_ran_out (the ledger's fields most / own since the E sweep: prh_ledger_most /
   prh_ledger_own of PRH_Base's ledger_proj) kept byte by byte (fm_cell: no run segment writes them, the malloc call
   keeps image bytes outside the owned statics and errno, the poison keeps bytes outside the stack window and the
   head's shadow). The ledger is reached through PRH_Base's named projections (ledger_proj) and S1Ledger's lemmas,
   never by a positional destruct of prh_ledger. NAME CLASH: PRH_Base.prh_ledger_own (the projection) and
   S1Ledger.prh_ledger_own (the OWN step of the SUCCESS arm) share a name; S1Ledger is imported last, so the bare name
   is S1Ledger's and the projection is written PRH_Base.prh_ledger_own.
   Numerals (BRIEF-COMMON rule): no typed ADDRESS; every image address is A_prog_val / pa_val / pi_* of the generated files.
   - register numbers 1 2 3 4 8 10 11 and atom indices 32 .. 38 (38: g_most's entry value), 39 (the agreement bound),
     40, 44, 60 (havoc bases), A_OBJ 0 / 7 .. 12 / 14 (14: g_most, read only): WORD (names);
   - 16 = cf_head, 2 ^ 28 + 2 ^ 27 = cf_malloc_max, 16416 = STK_fuzz_malloc: LENGTH, each checked by reflexivity against
     CfParams_preset / PRH_Img; 32 / -32 the frame (`addi sp,sp,-32`): LENGTH; 8, 4, 1 widths and offsets: LENGTH;
   - 2 ^ 46, 2 ^ 47 (sp band), 2 ^ 44 (shadow span), 2 ^ 29 (n's band), 4096 and 2 ^ 47 - 2 ^ 23 (a heap block's band),
     2 ^ 64, 63: DERIVED from asan_consts / the texts' premises / the word size;
   - 0 .. 14 in case splits and bit positions 8 * k: DERIVED.
   PART 3c and THE HULL: the call's QMm_cf is QM_cf from room_live_room with cf_hull_ok from the text's hull budget
   (lib/A/PresetHullPay.v hull_ok_of_budget) and arodata_ok_cf carried from the entry's reader form by the journal
   (YGcallcf.v arodata_ok_cf_of_journal_P at image A's rows, lib/A/CfAroPresetA.v); the hull use of each arm is the
   call's model path (YGcfSecsStep.secs_malloc_step, PresetHullBudget.hull_used_of_call), or none on CHOSEN-FAIL. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YG0sshcf YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallPx YGcfHp YGcallPcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRun PresetReqAt PresetRoomPos
  PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset PRH_Refute.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep YGcfAroBridge
  YGcfMallocComposeKeep YGcallMxmnKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m CfAroPresetA PresetHullPay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Abbreviation PA := (PI_prog_A).
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
#[local] Existing Instance CfParams_preset.

(* ---- the symbolic state at fuzz_malloc's entry (whole-program listing A_prog_listing, slot A_prog_slot
   AS_fuzz_malloc; atoms per a Theorem Labs lane's internal file INTERFACE.md: A_OBJ 0 shadow-base GOT cell, A_OBJ 12 the cell it points
   to, A_OBJ 7 .. 11 g_count, g_fail_at, g_live, g_peak, g_ran_out, A_OBJ 14 g_most (#102; the listing's g_most
   load at 0x85850)) ---- *)
(* the statics fuzz_malloc's walk tracks: the five it writes, and g_most, which it only reads *)
#[local] Abbreviation fm_stj j := ((7 <= j <= 11)%nat \/ j = 14%nat).
(* DERIVED: the slot's byte offset from the listing base *)
Definition FM_PC : Z := 4 * Z.of_nat (A_prog_slot AS_fuzz_malloc).
Definition FM_Bx : sv := SOff 32 0.
Definition FM_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition st_region (j : nat) (w : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some (A_OBJ j)) 0 w 0 w cs.
(* a static the walk reads and never writes: its write window is empty *)
Definition ro_region (j : nat) (w : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some (A_OBJ j)) 0 w 0 0 cs.
Definition fm_regions : smem :=
  [ stack_region 32; got_regionP; bcell_regionP 32;
    st_region 7 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
    st_region 8 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))];
    st_region 9 8 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))];
    st_region 10 8 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))];
    st_region 11 1 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))];
    ro_region 14 8 [YP09.mkChunk 0 (CVal 8 (SOff 38 0))] ].
Definition obj_fact (j : nat) : nat * afact := (A_OBJ j, mkAF (A_prog_val (A_OBJ j)) (A_prog_val (A_OBJ j)) 0).
(* the facts: sp's band, n's range (n + cf_head < cf_malloc_max), the shadow base, the statics' addresses, and the
   generated alias table (h-verbs-1's A_alias_hints: one row per static-store site) *)
Definition fm_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 (2 ^ 29) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           obj_fact 7; obj_fact 8; obj_fact 9; obj_fact 10; obj_fact 11; obj_fact 14] [] A_alias_hints.
Definition ss_fm : sstate := mkSS FM_PC sr_atoms fm_regions None fm_facts.

(* the image numbers a walk compares, computed from the generated instance, never typed *)
Ltac fm_lits0 :=
  repeat match goal with
  | |- context [A_prog_val ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v
  end.
Lemma fm_pst_vals : pi_g_count (PrhImg := prh_img_A) = A_prog_val (A_OBJ 7) /\
  pi_g_fail (PrhImg := prh_img_A) = A_prog_val (A_OBJ 8) /\
  pi_g_live (PrhImg := prh_img_A) = A_prog_val (A_OBJ 9) /\ pi_g_peak (PrhImg := prh_img_A) = A_prog_val (A_OBJ 10) /\
  pi_g_ran_out (PrhImg := prh_img_A) = A_prog_val (A_OBJ 11) /\ pi_g_most (PrhImg := prh_img_A) = A_prog_val (A_OBJ 14).
Proof. vm_compute. repeat split. Qed.
(* the statics' value widths (LENGTH, the generated asan_globals descriptors): size_t 8, g_ran_out 1 *)
Definition fm_w (j : nat) : Z := if (j =? 11)%nat then 1 else 8.
Lemma fm_widths : Z.of_nat (pi_gz_count (PrhImg := prh_img_A)) = fm_w 7 /\ Z.of_nat (pi_gz_fail (PrhImg := prh_img_A)) = fm_w 8 /\
  Z.of_nat (pi_gz_live (PrhImg := prh_img_A)) = fm_w 9 /\ Z.of_nat (pi_gz_peak (PrhImg := prh_img_A)) = fm_w 10 /\
  Z.of_nat (pi_gz_ran_out (PrhImg := prh_img_A)) = fm_w 11 /\ Z.of_nat (pi_gz_most (PrhImg := prh_img_A)) = fm_w 14.
Proof. vm_compute. repeat split. Qed.
(* the statics' bytes are prh_pst's *)
Lemma fm_obj_pst : forall j o, fm_stj j -> 0 <= o < fm_w j ->
  Exists (in_zr (A_prog_val (A_OBJ j) + o)) (prh_pst (PI := prh_img_A)).
Proof.
intros j o Hj Ho. destruct fm_pst_vals as (Pc & Pf & Pl & Pp & Pr & Pm).
destruct fm_widths as (Wc & Wf & Wl & Wp & Wr & Wm).
unfold prh_pst. destruct Hj as [Hj | ->].
- destruct j as [|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]; try lia; unfold fm_w in *; cbn [Nat.eqb] in *.
  + rewrite <- Pc. do 2 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite Wc. lia.
  + rewrite <- Pf. do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite Wf. lia.
  + rewrite <- Pl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite Wl. lia.
  + rewrite <- Pp. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite Wp. lia.
  + rewrite <- Pr. do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite Wr. lia.
- unfold fm_w in *. cbn [Nat.eqb] in *.
  rewrite <- Pm. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite Wm. lia.
Qed.
Lemma fm_obj_writable : forall (m : word -> option byte) j o, fm_stj j -> 0 <= o < fm_w j ->
  writable_at rsegs m (A_prog_val (A_OBJ j) + o).
Proof. intros m j o Hj Ho. apply pst_writable_A. apply fm_obj_pst; [exact Hj | exact Ho]. Qed.

(* THE TWO CELLS fuzz_malloc never writes and the text keeps (prh_most, prh_own): g_most and g_own_ran_out, both PST *)
Definition fm_cell (a : Z) : Prop :=
  pi_g_most (PrhImg := prh_img_A) <= a < pi_g_most (PrhImg := prh_img_A) + Z.of_nat (pi_gz_most (PrhImg := prh_img_A)) \/
  pi_g_own_ran_out (PrhImg := prh_img_A) <= a <
    pi_g_own_ran_out (PrhImg := prh_img_A) + Z.of_nat (pi_gz_own_ran_out (PrhImg := prh_img_A)).
Lemma fm_cell_pst : forall a, fm_cell a -> Exists (in_zr a) (prh_pst (PI := prh_img_A)).
Proof.
intros a [H|H]; unfold prh_pst; [do 5 apply Exists_cons_tl | do 6 apply Exists_cons_tl];
apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia.
Qed.
(* the cells' bounds as numerals, computed from the generated record (never typed) *)
Ltac fm_cell_lit Ha :=
  unfold fm_cell in Ha;
  let g1 := eval vm_compute in (pi_g_most (PrhImg := prh_img_A)) in
  let z1 := eval vm_compute in (Z.of_nat (pi_gz_most (PrhImg := prh_img_A))) in
  let g2 := eval vm_compute in (pi_g_own_ran_out (PrhImg := prh_img_A)) in
  let z2 := eval vm_compute in (Z.of_nat (pi_gz_own_ran_out (PrhImg := prh_img_A))) in
  change (pi_g_most (PrhImg := prh_img_A)) with g1 in Ha;
  change (Z.of_nat (pi_gz_most (PrhImg := prh_img_A))) with z1 in Ha;
  change (pi_g_own_ran_out (PrhImg := prh_img_A)) with g2 in Ha;
  change (Z.of_nat (pi_gz_own_ran_out (PrhImg := prh_img_A))) with z2 in Ha.
(* refused()'s held = g_live + n, saturating (`add`, `sltu`, `neg`, `or`): below 2 ^ 64 the saturation is off *)
Lemma fm_U_sat : forall E a b x y, U E a = x + y -> U E b = x -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  U E (SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU a b)) a) = x + y.
Proof.
intros E a b x y Ha Hb Hx Hy Hl. rewrite !U_SAlu, U_SLit, Ha, Hb. cbn [zalu_raw].
destruct (Z.ltb_spec (x + y) x) as [H|H]; [lia|].
unfold zcanon, M64. change (0 mod 2 ^ 64) with 0. change ((0 - 0) mod 2 ^ 64) with 0. rewrite Z.lor_0_l.
apply Z.mod_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
Context {SK : YI16.sink_head}.
Lemma fm_cell_low : forall a, fm_cell a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. exact (@pa_segs_low _ A_prog_listing PI_prog_A a (pst_in_img_A a (fm_cell_pst a Ha))). Qed.
Ltac fm_lits :=
  repeat match goal with |- context [@pa_val ?r ?L ?P ?j] =>
    let v := eval vm_compute in (@pa_val r L P j) in change (@pa_val r L P j) with v end;
  fm_lits0.
(* atoms 32 .. 38: the shadow base, the five statics' entry values and g_most's (cgif's extra-atom convention) *)
Definition FM_E (regs : bvmap 5 word) (cnt fail live peak ran most : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; live; peak; ran; most])).
Lemma FM_E_img : forall regs c f l p r m j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew (FM_E regs c f l p r m) j) = VAL j.
Proof. intros regs c f l p r m j Hj. unfold FM_E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. Qed.
Lemma FM_E_reg : forall regs c f l p r m n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (FM_E regs c f l p r m) n = getr regs x.
Proof.
intros regs c f l p r m n x Hn. unfold FM_E. pose proof (u5_range x) as Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n x Hn).
Qed.
Lemma FM_E_extra : forall regs c f l p r m,
  ew (FM_E regs c f l p r m) 32 = Z_to_bv 64 SHADOW_OFF /\ ew (FM_E regs c f l p r m) 33 = Z_to_bv 64 c /\
  ew (FM_E regs c f l p r m) 34 = Z_to_bv 64 f /\ ew (FM_E regs c f l p r m) 35 = Z_to_bv 64 l /\
  ew (FM_E regs c f l p r m) 36 = Z_to_bv 64 p /\ ew (FM_E regs c f l p r m) 37 = Z_to_bv 64 r /\
  ew (FM_E regs c f l p r m) 38 = Z_to_bv 64 m.
Proof.
intros regs c f l p r m. unfold FM_E. rewrite !Eimg_low by (unfold A_TEXT; lia). repeat split.
Qed.
(* the ledger's two cells g_own_ran_out (prh_own) and g_most (prh_most) at a later state, from the two cells' views *)
Lemma fm_keeps_post : forall (W W' : world SEGS) mem mem',
  (forall a, fm_cell a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall o, prh_own (PI := prh_img_A) (PA := PA) W mem o -> prh_own (PI := prh_img_A) (PA := PA) W' mem' o) /\
  (forall m, prh_most (PI := prh_img_A) (PA := PA) W mem m -> prh_most (PI := prh_img_A) (PA := PA) W' mem' m).
Proof.
intros W W' mem mem' K. split.
- intros o [V Ho]. split; [|exact Ho]. apply (prh_val_mem_keep (PA := PA) _ _ _ _ _ V).
  intros k Hk. apply (prh_mbyte_of_aview (PA := PA)). apply K. right. lia.
- intros m [V Hm]. split; [|exact Hm]. apply (prh_val_mem_keep (PA := PA) _ _ _ _ _ V).
  intros k Hk. apply (prh_mbyte_of_aview (PA := PA)). apply K. left. lia.
Qed.

Section f.
Variable B : asyms.
(* the allocator relation: h-mani-a8's ARcf with the error-buffer extents placed (S1KitAlloc's YGcallcf.v ARλ') *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane): swap by citation (proved once by the final instance) *)
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.

Lemma fm_entry : forall ly S Hp W regs mem md ch n Lam peak cnt fail ran most own,
  afn_pre_x SEGS B ARcfx (STK_fuzz_malloc (PI := prh_img_A)) ly S Hp W regs mem md ch ->
  getr regs 10 = w64 n -> 0 <= n <= 2 ^ 29 ->
  prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  st_ok_pi SEGS VAL (FM_E regs cnt fail (Ledger.lsum Lam) peak ran most) ss_fm
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + FM_PC)) mem (seg_rom SEGS))) /\
  sh_ok SEGS FM_Bx [] (FM_E regs cnt fail (Ledger.lsum Lam) peak ran most) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch n Lam peak cnt fail ran most own HPRE H10 Hn HL.
pose proof HPRE as ([HAR _] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_fuzz_malloc (PI := prh_img_A) = 16416) by reflexivity.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* the ledger's cells, by PRH_Base's named projections *)
pose proof (prh_ledger_live B ly S Hp W mem Lam peak cnt fail ran most own HL) as Mlive.
pose proof (prh_ledger_peak B ly S Hp W mem Lam peak cnt fail ran most own HL) as Mpeak.
pose proof (prh_ledger_count B ly S Hp W mem Lam peak cnt fail ran most own HL) as Mcnt.
pose proof (prh_ledger_fail B ly S Hp W mem Lam peak cnt fail ran most own HL) as Mfail.
pose proof (prh_ledger_ran B ly S Hp W mem Lam peak cnt fail ran most own HL) as Mran.
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HL) as (Rl & Rp & Rc & Rf & Rr).
destruct (prh_ledger_most B ly S Hp W mem Lam peak cnt fail ran most own HL) as [Mmost Rm].
destruct fm_pst_vals as (Pc & Pf & Pl & Pp & Pr & Pm).
rewrite Pc in Mcnt. rewrite Pf in Mfail. rewrite Pl in Mlive. rewrite Pp in Mpeak. rewrite Pr in Mran.
rewrite Pm in Mmost.
destruct (alc_const _ _ (AR_laws_ok_cf SEGS B) ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
set (E := FM_E regs cnt fail (Ledger.lsum Lam) peak ran most).
destruct (FM_E_extra regs cnt fail (Ledger.lsum Lam) peak ran most) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
fold E in E32, E33, E34, E35, E36, E37, E38.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (FM_E_reg _ _ _ _ _ _ _ 2 2%bv eq_refl); reflexivity).
assert (Un : bv_unsigned (ew E 10) = n)
  by (subst E; rewrite (FM_E_reg _ _ _ _ _ _ _ 10 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j) by (intros j Hj; subst E; apply FM_E_img; exact Hj).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FM_E; apply Eimg_env).
assert (Dv : forall (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v).
{ intros k v Hk Hv. cbn [sv_denot]. rewrite Hk, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j) by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
rewrite restrict_mkst_fx. split.
- unfold ss_fm. apply pa_entry_st_ok_full.
  + subst E. unfold FM_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold fm_regions, stack_region, got_regionP, bcell_regionP, st_region, ro_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok; cbv zeta;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK. lia.
    * pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 12)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * pose proof (pa_val_range (A_OBJ 12)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [apply Dv; [exact E32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * pose proof (pa_val_range (A_OBJ 7)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; apply fm_obj_writable; [lia | unfold fm_w; cbn [Nat.eqb]; lia]|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 33 0) cnt); [apply Dv; [exact E33 | lia] | zside | zside |].
      rewrite Z.add_0_r. exact Mcnt.
    * pose proof (pa_val_range (A_OBJ 8)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; apply fm_obj_writable; [lia | unfold fm_w; cbn [Nat.eqb]; lia]|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 34 0) fail); [apply Dv; [exact E34 | lia] | zside | zside |].
      rewrite Z.add_0_r. exact Mfail.
    * pose proof (pa_val_range (A_OBJ 9)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; apply fm_obj_writable; [lia | unfold fm_w; cbn [Nat.eqb]; lia]|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 35 0) (Ledger.lsum Lam)); [apply Dv; [exact E35 | lia] | zside | zside |].
      rewrite Z.add_0_r. exact Mlive.
    * pose proof (pa_val_range (A_OBJ 10)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; apply fm_obj_writable; [lia | unfold fm_w; cbn [Nat.eqb]; lia]|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 36 0) peak); [apply Dv; [exact E36 | lia] | zside | zside |].
      rewrite Z.add_0_r. exact Mpeak.
    * pose proof (pa_val_range (A_OBJ 11)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; apply fm_obj_writable; [lia | unfold fm_w; cbn [Nat.eqb]; lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 37 0) ran); [apply Dv; [exact E37 | lia] | cbn; lia | lia |].
      rewrite Z.add_0_r. exact Mran.
    * pose proof (pa_val_range (A_OBJ 14)).
      split; [lia|]. split; [fm_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 38 0) most); [apply Dv; [exact E38 | lia] | zside | zside |].
      rewrite Z.add_0_r. exact Mmost.
  + unfold fm_regions, stack_region, got_regionP, bcell_regionP, st_region, ro_region.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia). fm_lits.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + split; [|split; [exact I | apply A_alias_hints_ok; exact HEI]].
    unfold fm_facts, obj_fact. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Un, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia). fm_lits.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- helpers the walk uses at every stop ---- *)
Lemma fm_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma fm_rd32_keep : forall (rd rd' : reader) a v, (forall i, 0 <= i < 4 -> rd' (a + i) = rd (a + i)) -> rd32 rd a v -> rd32 rd' a v.
Proof. intros rd rd' a v Hk H k Hk4. rewrite Hk by lia. exact (H k Hk4). Qed.
(* the n present bytes at p have some values *)
Lemma fm_bytes_present : forall (W : world SEGS) mem p (k : nat),
  (forall a, p <= a < p + Z.of_nat k -> apresent (w_H W) mem a) ->
  exists l, length l = k /\ garr8 SEGS (mrestrict (w_H W) mem) p l.
Proof.
intros W mem p k. revert p. induction k as [|k IH]; intros p Hp.
- exists []. split; [reflexivity | apply garr8_nil].
- destruct (Hp p ltac:(lia)) as [Hh [b Hb]].
  destruct (IH (p + 1) ltac:(intros a Ha; apply Hp; lia)) as (l & Hl & Hg).
  exists (bv_unsigned b :: l). split; [cbn; rewrite Hl; reflexivity|].
  intros j Hj. destruct j as [|j].
  + cbn [nth]. split; [|pose proof (bv_unsigned_in_range _ b) as Hr; unfold bv_modulus in Hr; cbn in Hr; lia].
    intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite !Z.add_0_r.
    pose proof (bv_unsigned_in_range _ b) as Hr. unfold bv_modulus in Hr. cbn in Hr.
    unfold mbyte, mrestrict. rewrite Hh, Hb. f_equal.
    rewrite (YI04.le_byte_small (bv_unsigned b) 1 0) by (cbn; lia).
    change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  + cbn [nth length] in Hj |- *. destruct (Hg j ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
    replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. exact Hv.
Qed.
Lemma fm_region_ok : forall E ss ms r, st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms r HS Hin. destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r Hin).
Qed.
(* the chunk a region of the symbolic state holds at (j, off) gives the bytes there *)
Lemma fm_chunk_at : forall E ss ms (j : nat) off n c,
  st_ok_pi SEGS VAL E ss ms ->
  (exists r, find_region (ss_mem ss) (Some j) off n = Some r /\ find_chunk (r_chunks r) off n = Some c) ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off n c HS (r & Hr & Hc).
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ Hc) as (Hcin & _).
destruct (fm_region_ok E ss ms r HS Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs c Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma fm_kept_gen : forall E (m m' : word -> option byte) k b lo hi wlo whi cs, bv_unsigned (ew E k) = b ->
  (forall a, b + lo <= a < b + hi -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall a, b + wlo <= a < b + whi -> writable_at SEGS m' a) ->
  region_kept SEGS E m m' (YP09.mkRegion (Some k) lo hi wlo whi cs).
Proof.
intros E m m' k b lo hi wlo whi cs Hb Hm Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hb; intros a Ha; [exact (Hm a Ha) | intros _; exact (Hw a Ha)].
Qed.
(* a static region keeps its bytes whenever the statics' bytes are kept *)
Lemma fm_kept_st : forall E (m m' : word -> option byte) j w whi cs, fm_stj j -> img_env VAL A_LIM E ->
  0 <= whi <= w -> w <= fm_w j ->
  (forall a, Exists (in_zr a) (prh_pst (PI := prh_img_A)) -> mbyte SEGS m' a = mbyte SEGS m a) ->
  region_kept SEGS E m m' (YP09.mkRegion (Some (A_OBJ j)) 0 w 0 whi cs).
Proof.
intros E m m' j w whi cs Hj HEI Hw1 Hw2 Hk.
apply (fm_kept_gen E m m' (A_OBJ j) (A_prog_val (A_OBJ j))); [apply HEI; unfold A_OBJ, A_TEXT, A_LIM; destruct Hj; lia | |].
- intros a Ha. apply Hk. replace a with (A_prog_val (A_OBJ j) + (a - A_prog_val (A_OBJ j))) by lia.
  apply fm_obj_pst; [exact Hj | lia].
- intros a Ha. apply pst_writable_A. replace a with (A_prog_val (A_OBJ j) + (a - A_prog_val (A_OBJ j))) by lia.
  apply fm_obj_pst; [exact Hj | lia].
Qed.

(* ---- the final statics, read off the symbolic state ---- *)
Definition fm_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma fm_cv_ok : forall E ss ms j off w c, st_ok_pi SEGS VAL E ss ms -> fm_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold fm_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
exact (fm_chunk_at E ss ms j off w c HS (ex_intro _ r (conj Hr H))).
Qed.
Lemma fm_val_cv : forall E ss ms j off (w : N) e v, st_ok_pi SEGS VAL E ss ms ->
  fm_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) -> U E e = v -> Z.of_N w <= 8 ->
  0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) (bv_unsigned (ew E j) + off) (N.to_nat w) v.
Proof.
intros E ss ms j off w e v HS H HU Hw Hv.
exact (val_of_chunk_ok SEGS E _ _ off w e v (fm_cv_ok E ss ms j off (Z.of_N w) _ HS H) (fm_denot_U E e v HU) Hv Hw).
Qed.
Lemma fm_U_range : forall E e, 0 <= U E e < 2 ^ 64.
Proof. intros E e. unfold U. pose proof (bv_unsigned_in_range _ (sv_denot E e)) as H. exact H. Qed.
(* the five statics' values at a symbolic state, with g_most's and g_own_ran_out's (kept cells, given), as prh_glob *)
Lemma fm_glob_of_ss : forall E ss (Wf : world SEGS) msf el ep ec ef er live peak cnt fail ran most own,
  st_ok_pi SEGS VAL E ss (restrict (w_H Wf) msf) -> img_env VAL A_LIM E ->
  fm_cv (ss_mem ss) (A_OBJ 9) 0 8 = Some (YP09.mkChunk 0 (CVal 8 el)) ->
  fm_cv (ss_mem ss) (A_OBJ 10) 0 8 = Some (YP09.mkChunk 0 (CVal 8 ep)) ->
  fm_cv (ss_mem ss) (A_OBJ 7) 0 8 = Some (YP09.mkChunk 0 (CVal 8 ec)) ->
  fm_cv (ss_mem ss) (A_OBJ 8) 0 8 = Some (YP09.mkChunk 0 (CVal 8 ef)) ->
  fm_cv (ss_mem ss) (A_OBJ 11) 0 1 = Some (YP09.mkChunk 0 (CVal 1 er)) ->
  U E el = live -> U E ep = peak -> U E ec = cnt -> U E ef = fail -> U E er = ran ->
  live <= peak -> (ran = 0 \/ ran = 1) ->
  prh_most (PI := prh_img_A) (PA := PA) Wf (ms_mem msf) most -> prh_own (PI := prh_img_A) (PA := PA) Wf (ms_mem msf) own ->
  prh_glob (PI := prh_img_A) (PA := PA) Wf (ms_mem msf) live peak cnt fail ran most own.
Proof.
intros E ss Wf msf el ep ec ef er live peak cnt fail ran most own HS HEI Cl Cp Cc Cf Cr Ul Up Uc Uf Ur Hlp Hr HMo HOo.
destruct fm_pst_vals as (Pc & Pf & Pl & Pp & Pr & _).
assert (Bj : forall j, (7 <= j <= 11)%nat -> bv_unsigned (ew E (A_OBJ j)) = A_prog_val (A_OBJ j))
  by (intros j Hj; apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (fm_U_range E el) as Rl. pose proof (fm_U_range E ep) as Rp.
pose proof (fm_U_range E ec) as Rc. pose proof (fm_U_range E ef) as Rf.
rewrite Ul in Rl. rewrite Up in Rp. rewrite Uc in Rc. rewrite Uf in Rf.
unfold prh_glob. split; [|split; [|split; [|split; [|split; [|split; [exact HMo|split; [exact HOo|]]]]]]].
- pose proof (fm_val_cv E ss _ (A_OBJ 9) 0 8 el live HS Cl Ul ltac:(lia) ltac:(cbn; lia)) as V.
  rewrite Bj, Z.add_0_r in V by lia. rewrite Pl. exact V.
- pose proof (fm_val_cv E ss _ (A_OBJ 10) 0 8 ep peak HS Cp Up ltac:(lia) ltac:(cbn; lia)) as V.
  rewrite Bj, Z.add_0_r in V by lia. rewrite Pp. exact V.
- pose proof (fm_val_cv E ss _ (A_OBJ 7) 0 8 ec cnt HS Cc Uc ltac:(lia) ltac:(cbn; lia)) as V.
  rewrite Bj, Z.add_0_r in V by lia. rewrite Pc. exact V.
- pose proof (fm_val_cv E ss _ (A_OBJ 8) 0 8 ef fail HS Cf Uf ltac:(lia) ltac:(cbn; lia)) as V.
  rewrite Bj, Z.add_0_r in V by lia. rewrite Pf. exact V.
- pose proof (fm_val_cv E ss _ (A_OBJ 11) 0 1 er ran HS Cr Ur ltac:(lia) ltac:(cbn; destruct Hr; lia)) as V.
  rewrite Bj, Z.add_0_r in V by lia. rewrite Pr. exact V.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Hr].
Qed.
Lemma fm_ag_u : forall E0 E (k : nat), env_agree 39 E0 E -> (k < 39)%nat -> bv_unsigned (ew E k) = bv_unsigned (ew E0 k).
Proof. intros E0 E k [A _] Hk. rewrite (A k Hk). reflexivity. Qed.
Lemma fm_U_off : forall E0 E (k : nat) v c, env_agree 39 E0 E -> (k < 39)%nat -> ew E0 k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff k c) = (v + c) mod 2 ^ 64.
Proof.
intros E0 E k v c [A _] Hk He Hv. rewrite U_SOff, (A k Hk), He, unsigned_lit_small by exact Hv.
unfold zcanon, M64. reflexivity.
Qed.
Lemma fm_U0 : forall E0 E (k : nat) v, env_agree 39 E0 E -> (k < 39)%nat -> ew E0 k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff k 0) = v.
Proof. intros E0 E k v c Hk He Hv. rewrite (fm_U_off E0 E k v 0 c Hk He Hv), Z.add_0_r. apply Z.mod_small. exact Hv. Qed.
(* a byte outside the run's write windows keeps its view (the runner's frame_of) *)
Lemma fm_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma fm_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma fm_U_srl : forall E a s, 0 <= s < 64 -> U E (SAlu ALU_SRL a (SLit s)) = Z.shiftr (U E a) s.
Proof.
intros E a s Hs. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id s) by (unfold M64; lia).
replace (Z.land s 63) with s by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
pose proof (fm_U_range E a) as Ha.
apply zcanon_id. unfold M64. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (U E a)); [apply Z.div_le_upper_bound; nia | lia].
Qed.
(* a byte chunk at a state the runner stopped at a call (plain st_ok) *)
Lemma fm_byte_st : forall E ss ms j off e, st_ok SEGS E ss ms ->
  fm_cv (ss_mem ss) j off 1 = Some (YP09.mkChunk off (CVal 1 e)) ->
  mbyte SEGS (ms_mem ms) (bv_unsigned (ew E j) + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros E ss ms j off e HS H. unfold fm_cv in H.
destruct (find_region (ss_mem ss) (Some j) off 1) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn in Hb1. injection Hb1 as <-.
cbn [YP09.c_off base_val] in Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. unfold YP09.byte_of_word, U. rewrite Z.shiftr_0_r. reflexivity.
Qed.
(* the block head: the 8 `sb` of v's bytes (`srli` by 8k), read off the symbolic state *)
Lemma fm_hdr_of_st : forall E ss (Wf : world SEGS) msf (j : nat) e b v,
  st_ok SEGS E ss (restrict (w_H Wf) msf) -> bv_unsigned (ew E j) = b ->
  fm_cv (ss_mem ss) j 0 1 = Some (YP09.mkChunk 0 (CVal 1 e)) ->
  (forall k, (1 <= k < 8)%nat ->
     fm_cv (ss_mem ss) j (Z.of_nat k) 1 = Some (YP09.mkChunk (Z.of_nat k) (CVal 1 (SAlu ALU_SRL e (SLit (8 * Z.of_nat k)))))) ->
  U E e = v -> val_mem SEGS (mrestrict (w_H Wf) (ms_mem msf)) b 8 v.
Proof.
intros E ss Wf msf j e b v HS Hb C0 Ck Hv.
pose proof (fm_U_range E e) as Rv. rewrite Hv in Rv.
apply (prh_val_mem_hdr8 (PA := PA)); [exact Rv|]. intros k Hk. destruct k as [|k].
- pose proof (fm_byte_st E ss _ j 0 e HS C0) as V. rewrite Hb, Hv in V. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. exact V.
- pose proof (fm_byte_st E ss _ j _ _ HS (Ck (S k) ltac:(lia))) as V. rewrite Hb, fm_U_srl, Hv in V by lia. exact V.
Qed.

#[local] Abbreviation PST := (prh_pst (PI := prh_img_A)).
#[local] Abbreviation AJ := (ajournal_x (SK := SK) SEGS B PST ARcfx).
#[local] Abbreviation LEDGER := (prh_ledger (PI := prh_img_A) (PA := PA) B).
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane): swap by citation (proved once by the final instance) *)
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* callee text: the malloc wrapper (h-mani-a8, YG0dcf.v) *)
(* with the memnorm keep at the leaf (YGcfMallocComposeKeep.v) *)
Hypothesis AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep SEGS B.
(* callee text: __asan_poison_memory_region (h-rw-man-5, YGcfHp.v, relaxed to cf_head <= req_size n) *)
Hypothesis APOISON : apoison_realizes_cf SEGS B.
(* STAND-IN for the unit's TFIB symbol binding of B (image binding, no state; the instance's TfibB_syms): errno's
   place, apart from the read-only ranges of the call memory's arodata_ok_cf (CfAroPresetA.errno_relro_preset_A) *)
Hypothesis TB : AF0m.TfibSyms B.

(* the allocator laws at ARcf: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let APOISONx : apoison_realizes_x SEGS B ARcfx cf_head cf_pc_poison := apoison_realizes_cf_xs SEGS B APOISON.
Let AMALLOCx := YGcallMxmnKeep.amalloc_realizes_x_xs_keep SEGS B AMALLOC.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.
Let XSL := ARx_xs_law_xs SEGS B.
Lemma fm_PST_ok : forall a, Exists (in_zr a) PST -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. intros a Ha. split; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha))]. Qed.
(* alloc.c's statics are no byte the call memory's arodata_ok_cf covers: each such byte is a read-only image byte
   (RELRO, or a report read inside a non-writable segment, CfAroPresetA.ro_reads_nw_preset_A), and no static is one
   (S1ImgA.pst_not_ro_A) *)
Lemma fm_pst_aro : forall a, aro_addr_cf a -> ~ Exists (in_zr a) PST.
Proof.
intros a Ha Hx. apply (pst_not_ro_A a Hx). destruct Ha as [Ha | Ha].
- right. unfold PAImg_prog.A_prog_relro_lo, PAImg_prog.A_prog_relro_hi. cbv [cf_relro_lo cf_relro_hi CfImg_A] in Ha.
  exact Ha.
- left. pose proof CfAroPresetA.ro_reads_nw_preset_A as RONW.
  unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite Forall_forall in RONW.
  apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
  destruct (RONW r Hr) as (_ & sg & Hin & NW & L & R). exists sg. split; [exact Hin|]. split; [exact NW | lia].
Qed.
Let RUNm := paj_run_x_m (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B PST ARcfx LAWS fm_PST_ok.
(* the same runner carrying the memnorm keep from a fixed memory m0 (h-hpreset-7's carrier, YSRrMemnorm.v:40) *)
Let RUNM (m0 : word -> option byte) := paj_run_x_m_inv (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) B
  PST ARcfx LAWS fm_PST_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
Let BR := paj_branch (L := A_prog_listing) (PI := PA).
Let RET := paj_ret_at (L := A_prog_listing) (PL := PL_prog_A) (PI := PA).

(* errno's four bytes (the REFUSED arm keeps the wrapper's errno 12 through refused()) *)
Definition fm_errno (a : Z) : Prop := as_errno B <= a < as_errno B + 4.
(* a set of bytes no run segment writes keeps its view across the segment (the runner's frame_of) *)
Lemma fm_keep_frame : forall (P : Z -> Prop) (Wx : world SEGS) E' rs (m m' : word -> option byte) (W0 : world SEGS) m0,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E' rs a) ->
  (forall a, P a -> aview SEGS (w_H Wx) m a = aview SEGS (w_H W0) m0 a) ->
  forall a, P a -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H W0) m0 a.
Proof.
intros P Wx E' rs m m' W0 m0 HF Hn K a Ha. destruct (Hn a Ha) as [Hr Hw].
rewrite <- (K a Ha). exact (fm_aview_of_frame Wx E' rs m m' a HF Hw Hr).
Qed.

(* the heads of the ledger's blocks survive a journal whose footprint is empty (its block clause) *)
Lemma fm_heads_kept : forall STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k Lam peak cnt fail ran most own,
  AJ STK sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  forall a k0 i, In (a, k0) Lam -> 0 <= i < 8 ->
  mbyte SEGS (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte SEGS (mrestrict (w_H W) mem) (a - cf_head + i).
Proof.
intros STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k Lam peak cnt fail ran most own HJ HL Hbl a k0 i Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k0 most own HL Hin) as (Hk0 & Hab & _).
change (@cf_head CfParams_preset) with 16 in *.
apply (prh_mbyte_of_aview (PA := PA)).
apply (F2 (a - 16) (k0 + 16) i Hab (Hbl _ Hab)); [|apply inFP_nil].
unfold req_size. destruct (Z.eqb_spec (k0 + 16) 0); lia.
Qed.
(* a block's first 8 bytes and a static are apart: the block holds no image byte, the static is one *)
Lemma fm_blk_static_disj : forall (j : nat) b w, fm_stj j -> 0 < w <= fm_w j ->
  (forall a, b <= a < b + 8 -> ~ in_img SEGS a) ->
  b + 8 <= A_prog_val (A_OBJ j) \/ A_prog_val (A_OBJ j) + w <= b.
Proof.
intros j b w Hj Hw Hn.
destruct (Z_le_gt_dec (b + 8) (A_prog_val (A_OBJ j))) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (A_prog_val (A_OBJ j) + w) b) as [H2|H2]; [right; exact H2|]. exfalso.
assert (Hx : exists x, b <= x < b + 8 /\ A_prog_val (A_OBJ j) <= x < A_prog_val (A_OBJ j) + w)
  by (exists (Z.max b (A_prog_val (A_OBJ j))); lia).
destruct Hx as (x & Hx1 & Hx2). apply (Hn x Hx1). apply pst_in_img_A.
replace x with (A_prog_val (A_OBJ j) + (x - A_prog_val (A_OBJ j))) by lia.
apply fm_obj_pst; [exact Hj | lia].
Qed.
(* the success arm's block is new: it was not in the entry's block list (S1Strdup's sd_newblk) *)
Lemma fm_newblk : forall ly S ly' S' Hp' W' m' md' (x : Z * Z), ARcfx ly' S' Hp' W' m' md' -> 0 <= snd x ->
  ablocks B ly' S' = ablocks B ly S ++ [x] -> ~ In x (ablocks B ly S).
Proof.
intros ly S ly' S' Hp' W' m' md' [p m] HAR Hm E Hin. cbn [snd] in Hm.
assert (Hin' : In (p, m) (ablocks B ly' S')) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARcfx LAWS ly' S' Hp' W' m' md' p m HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (YCbq.pairwise_In2 zdisjoint _ (p, req_size m) (p, req_size m)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. pose proof (prh_req_size_pos m Hm). lia.
Qed.
(* the ledger's hidden heads lie outside a fresh block *)
Lemma fm_hp_apart : forall ly S Hp W mem Lam peak cnt fail ran most own ly2 S2 Hp2 W2 mem2 md2 b m,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> ARcfx ly2 S2 Hp2 W2 mem2 md2 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(b, m)] -> 0 <= m ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly2 S2 Hp2 W2 mem2 md2 b m HL HAR Eab Hm h Hh.
pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HL) as HP.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hin). cbn [fst] in Eh. subst h.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & _).
change (@cf_head CfParams_preset) with 16 in *.
assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Hab2 : In (a - 16, k + 16) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; left; exact Hab).
assert (Hne : (a - 16, k + 16) <> (b, m)).
{ intros Eq. rewrite Eq in Hab. exact (fm_newblk ly S ly2 S2 Hp2 W2 mem2 md2 (b, m) HAR Hm Eab Hab). }
pose proof (sep_blocks_x SEGS B ARcfx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR Hab2 Hin2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (prh_req_size_pos (k + 16) ltac:(lia)). lia.
Qed.
(* a covering hull covers a sub-range (S1Strdup's sd_hull_sub, cgif YCbq.v:1945) *)
Lemma fm_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma fm_denot_off : forall E (k : nat) b c, bv_unsigned (ew E k) = b -> 0 <= b + c < 2 ^ 64 ->
  sv_denot E (SOff k c) = Z_to_bv 64 (b + c).
Proof. intros E k b c Hb Hr. apply fm_denot_U. rewrite U_SOff, Hb. apply zcanon_id. unfold M64. lia. Qed.
(* the head poison's two shadow bytes miss the statics, the block's bytes and the stack *)
Lemma fm_not_shadow : forall b len a, in_app b len -> b + len <= alloc_ceiling -> 0 <= len ->
  (a < kLowMemEnd \/ (b <= a < b + len) \/ alloc_ceiling <= a) -> ~ (shadow_addr b <= a < shadow_addr b + 2).
Proof.
intros b len a Happ Hc Hl Ha. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF.
assert (Hb8 : 0 <= b / 8) by (apply Z.div_pos; lia).
assert (Hbc : b / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hc8 : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.mod_pos_bound b 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
rewrite C5 in Ha. lia.
Qed.

(* ---- the walk's tactics ---- *)
Ltac ex_zr := first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl; ex_zr ].
Ltac fm_lits_in H :=
  repeat match type of H with context [@pa_val ?r ?L ?P ?j] =>
    let v := eval vm_compute in (@pa_val r L P j) in change (@pa_val r L P j) with v in H end.
(* a byte of one of alloc.c's statics is PST *)
Ltac fm_wr_st H :=
  lazymatch type of H with context [bv_unsigned (ew ?Ex ?k)] =>
  lazymatch goal with HEIx : img_env _ _ Ex |- _ =>
    rewrite (HEIx k ltac:(unfold A_TEXT, A_LIM; lia)) in H end end;
  fm_lits_in H;
  let p := eval vm_compute in PST in change PST with p;
  ex_zr.
(* the mixed runner's write premise, region by region: the frame, the statics (PST), the new block (blk) *)
Ltac fm_wr AGx Usp HSTK blk :=
  let fmA := fresh "fmA" in let fmR := fresh "fmR" in let fmIn := fresh "fmIn" in let fmHa := fresh "fmHa" in
  intros fmA (fmR & fmIn & fmHa);
  lazymatch type of fmIn with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in fmIn end;
  repeat (destruct fmIn as [fmIn | fmIn];
          [subst fmR; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in fmHa;
           first [ exfalso; lia
                 | left; unfold awr_byte; left; try rewrite (proj1 AGx 2%nat ltac:(lia)) in fmHa; rewrite Usp in fmHa; rewrite HSTK; lia
                 | right; fm_wr_st fmHa
                 | blk fmHa ] |]);
  destruct fmIn.
(* the env of a new state agrees with the entry's on the atoms below 39 *)
Ltac fm_ag AGp :=
  split; [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
           try rewrite <- (proj1 AGp i Hi); rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; reflexivity
         | exact (proj2 AGp) ].
Ltac fm_newenv E0 HS AGp AGn :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?En _ _ => assert (AGn : env_agree 39 E0 En) by fm_ag AGp
  | st_ok _ ?En _ _ => assert (AGn : env_agree 39 E0 En) by fm_ag AGp
  end.
(* ---- the byte keeps across one run segment (fm_keep_frame): an address a with property P lies in no write window
   of the segment. Each window's base is an atom of the run's env: the stack pointer (atom 2, through Usp), a static
   (an image atom, through the entry env's img_env), or the new block (blk). stc closes a static's case from the
   static's numeric window (Hr); a and Ha are the address and its property. ---- *)
Ltac fm_nw_reg a Ha Hr stc blk :=
  first [ lia
        | cbn [ew extK Nat.eqb Nat.ltb Nat.leb Nat.add Nat.sub A_OBJ] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
          rewrite ?ew_havoc_above in Hr by (cbn; lia);
          first [ match goal with Usp : bv_unsigned (ew _ 2) = spZ _ |- _ => rewrite Usp in Hr; lia end
                | lazymatch type of Hr with context [bv_unsigned (ew ?Ex ?k)] =>
                    lazymatch goal with HEIx : img_env _ _ Ex |- _ =>
                      rewrite (HEIx k ltac:(unfold A_TEXT, A_LIM; lia)) in Hr end end;
                  fm_lits_in Hr; stc Hr
                | blk a Ha Hr ] ].
Ltac fm_nw_all a Ha stc blk :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; fm_nw_reg a Ha Hr stc blk |]);
  destruct Hin.
(* K : forall a, P a -> aview (w_H Wx) mA a = aview (w_H W0) m0 a, carried over the run whose frame_of is HFr *)
Ltac fm_keep K P rng nwt :=
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
  lazymatch type of K with forall a, _ -> _ = aview _ (w_H ?W0) ?m0 a =>
    let K' := fresh "K" in
    assert (K' : forall a, P a -> aview SEGS (w_H Wx) mB a = aview SEGS (w_H W0) m0 a);
    [ apply (fm_keep_frame P Wx Ex rsx mA mB W0 m0 HFr); [|exact K];
      let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [rng a Ha | nwt a Ha]
    | clear K; rename K' into K ] end end.
Ltac fm_rng_cell a Ha :=
  let L := fresh "L" in let C := fresh "C" in
  pose proof (fm_cell_low a Ha) as L; pose proof asan_consts as (_ & _ & _ & _ & C); lia.
Ltac fm_nwt_cell blk a Ha :=
  let L := fresh "L" in let C := fresh "C" in
  pose proof (fm_cell_low a Ha) as L; pose proof asan_consts as (_ & _ & _ & _ & C);
  fm_cell_lit Ha; fm_nw_all a Ha ltac:(fun Hr => lia) blk.
Ltac fm_rng_errno a Ha :=
  let L := fresh "L" in let C := fresh "C" in
  pose proof (@pa_segs_low _ A_prog_listing PI_prog_A a (proj1 (proj2 (pal_env B PAL)) a Ha)) as L;
  pose proof asan_consts as (_ & _ & _ & _ & C); unfold fm_errno in Ha; lia.
Ltac fm_nwt_errno blk a Ha :=
  let L := fresh "L" in let C := fresh "C" in let Hnp := fresh "Hnp" in
  pose proof (@pa_segs_low _ A_prog_listing PI_prog_A a (proj1 (proj2 (pal_env B PAL)) a Ha)) as L;
  pose proof asan_consts as (_ & _ & _ & _ & C);
  assert (Hnp : ~ Exists (in_zr a) PST) by (let Hx := fresh in intros Hx; exact (proj2 (pal_pst_ok _ Hx) Ha));
  unfold fm_errno in Ha;
  fm_nw_all a Ha ltac:(fun Hr => exfalso; apply Hnp; let p := eval vm_compute in PST in change PST with p; ex_zr) blk.
(* the cells (KA) and errno (KE) over the last run *)
Ltac fm_ka KA blk := fm_keep KA fm_cell ltac:(fun a Ha => fm_rng_cell a Ha) ltac:(fun a Ha => fm_nwt_cell blk a Ha).
Ltac fm_ke KE blk := fm_keep KE fm_errno ltac:(fun a Ha => fm_rng_errno a Ha) ltac:(fun a Ha => fm_nwt_errno blk a Ha).
Ltac fm_noblk a Ha Hr := fail.
(* an address below the stack that is not PST is in none of the walk's write windows (H: its bound) *)
Ltac fm_nw AGx Usp Hnp :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
           first [ lia
                 | try rewrite (proj1 AGx 2%nat ltac:(lia)) in Hr; rewrite Usp in Hr; lia
                 | apply Hnp; fm_wr_st Hr ] |]);
  destruct Hin.
(* the empty shadow-entry list at a state *)
Ltac fm_shok HS SHOK :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
    assert (SHOK : sh_ok SEGS FM_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (unfold sh_ok; apply Forall_nil) end.
Ltac fm_jk HJ :=
  lazymatch type of HJ with ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?lyf ?Sf ?Hpf ?Wf _ _ ?kf =>
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyf, Sf, Hpf, r, m, d, kf end end.
(* a register's symbolic value, unnormalized *)
Ltac prreg0 HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr end.
(* an equation whose left side is a closed computation *)
Ltac fm_cvt := lazymatch goal with |- ?L = _ => let v := eval vm_compute in L in change L with v end; reflexivity.
Ltac fm_lits0_in H :=
  repeat match type of H with context [A_prog_val ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v in H end.

Theorem fuzz_malloc_holds :
  tfuzz_malloc_specX (fx := fx) (rc := rc) (cp := CfParams_preset) (PI := prh_img_A)
    (RL := prh_room_live_a8 (cp := CfParams_preset)) (L := A_prog_listing) (PA := PI_prog_A) B ARcfx SK.
Proof.
unfold tfuzz_malloc_specX, fpre, fpostm, fQmn, fpost.
intros ly S Hp W regs mem md ch n Lam peak cnt fail ran most own
  [HPRE [HRO [Hstkhi [Hraceil Hfrm0]]]] HRL HUNIV Hsec H24 HHUL H10 Hn0 Hnmax HL Hlive.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (HHD : @cf_head CfParams_preset = 16) by reflexivity.
assert (HMX : @cf_malloc_max CfParams_preset = 2 ^ 28 + 2 ^ 27) by reflexivity.
assert (HSTK : STK_fuzz_malloc (PI := prh_img_A) = 16416) by reflexivity.
rewrite HHD in Hnmax, Hlive. rewrite HMX in Hnmax.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as ([HAR0 HXS0] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HL) as (Rl & Rp & Rc & Rf & Rr).
(* the ledger's g_most and g_own_ran_out cells (PRH_Base's projections; the bare prh_ledger_own is S1Ledger's step) *)
pose proof (prh_ledger_most B ly S Hp W mem Lam peak cnt fail ran most own HL) as HMOST.
pose proof (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt fail ran most own HL) as HOWN.
pose proof HMOST as [_ Rmost].
destruct (fm_entry ly S Hp W regs mem md ch n Lam peak cnt fail ran most own HPRE H10 ltac:(lia) HL) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARcfx (STK_fuzz_malloc (PI := prh_img_A)) []
  ly S Hp W regs mem md ch HPRE) as HJ.
set (xs0 := map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; Ledger.lsum Lam; peak; ran; most]).
remember (FM_E regs cnt fail (Ledger.lsum Lam) peak ran most) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FM_E; apply Eimg_env).
assert (AGe : env_agree 32 (Ereg regs xs0) E)
  by (subst E; unfold FM_E; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (AG0 : env_agree 39 E E) by (split; [intros; reflexivity | reflexivity]).
destruct (FM_E_extra regs cnt fail (Ledger.lsum Lam) peak ran most) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
rewrite <- HE in E32, E33, E34, E35, E36, E37, E38. clear HE.
assert (EL : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. pose proof (u5_range r). rewrite (proj1 AGe k ltac:(lia)). exact (ew_Ereg_nat regs xs0 k r Hk). }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
pose proof (EL 1%nat 1%bv eq_refl) as E1. pose proof (EL 3%nat 3%bv eq_refl) as E3. pose proof (EL 4%nat 4%bv eq_refl) as E4.
pose proof (EL 10%nat 10%bv eq_refl) as E10. rewrite H10 in E10.
unfold cfg_at. change (w64 (SIGMA AS_fuzz_malloc)) with (Z_to_bv 64 (BASE + FM_PC)).
(* the carried facts: memnorm (HPM) and the two cells' views (KA) *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
assert (KA : forall a, fm_cell a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by (intros; reflexivity).
(* ---- g_count += 1; the CHOSEN-FAIL test ---- *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FM_Bspan; [fm_wr AG0 Usp HSTK ltac:(fun H => fail)|].
fm_newenv E HS AG0 AG1.
fm_ka KA fm_noblk.
clear HF HFr HG.
psrr_branch_tok RUNm BR HS SHOK FM_Bspan.
2:{
(* ---- CHOSEN-FAIL (prh_alloc_post arm 1): g_count = g_fail_at: g_fail_at := SIZE_MAX, return 0 ---- *)
rewrite branch_ne_U, (fm_U0 E _ 33 cnt AG1 ltac:(lia) E33 ltac:(lia)), (fm_U0 E _ 34 fail AG1 ltac:(lia) E34 ltac:(lia)) in Hc.
assert (Hcf : cnt = fail) by (destruct (Z.eqb_spec cnt fail); [assumption | discriminate Hc]).
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FM_Bspan; [fm_wr AG1 Usp HSTK ltac:(fun H => fail)|].
fm_newenv E HS AG1 AG2.
fm_ka KA fm_noblk.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base_x.
fm_jk HJ.
split; [cbn [ms_regs]; rewrite R1, E1; rewrite Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARcfx LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs xs0 HS);
  [exact (YP03.env_agree_trans 32 _ _ _ AGe (YP03.env_agree_le 32 39 _ _ ltac:(lia) AG2)) | vm_compute; reflexivity]|].
cbv beta. split; [|exact HPM].
exists 0. split; [rewrite R10; reflexivity|].
split; [exact HRL|].
(* the hull: no allocator call, S' = S *)
split; [exact (PresetHullBudget.hull_used_refl S _)|].
(* E = []: no allocator call, S' = S, the position and its history kept *)
split; [intros _ psm px pos pi pH0 phist Hpos _; exists phist; cbn [length]; rewrite Nat.add_0_r; exact Hpos|].
split; [intros Hne; exfalso; exact (Hne eq_refl)|].
(* THE OUTCOME: refuted, the chosen failure fired (cnt = fail) *)
split; [intros psm px pos pi pH0 phist _ _ _ Hne; exfalso; exact (Hne Hcf)|].
left. split; [exact Hcf|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
apply (prh_ledger_frame B ly S Hp W mem ly S Hp W _ Lam peak cnt fail ran peak _ _ _ _ _ HL).
- eapply (fm_glob_of_ss _ _ W _ (SOff 35 0) (SOff 36 0) (SOff 33 1) (SLit (2 ^ 64 - 1)) (SOff 37 0) _ _ _ _ _ _ _ HS);
  [assumption | fm_cvt | fm_cvt | fm_cvt | fm_cvt | fm_cvt | | | | | | lia | exact Rr
  | exact (proj2 (fm_keeps_post W W mem _ KA) most HMOST) | exact (proj1 (fm_keeps_post W W mem _ KA) own HOWN)].
  + exact (fm_U0 E _ 35 _ AG2 ltac:(lia) E35 ltac:(lia)).
  + exact (fm_U0 E _ 36 _ AG2 ltac:(lia) E36 ltac:(lia)).
  + exact (fm_U_off E _ 33 _ 1 AG2 ltac:(lia) E33 ltac:(lia)).
  + rewrite U_SLit. unfold SIZE_MAXZ, zcanon, M64. reflexivity.
  + exact (fm_U0 E _ 37 _ AG2 ltac:(lia) E37 ltac:(lia)).
- exact (fm_heads_kept _ _ ly S Hp W mem md ly S Hp W _ _ _ Lam peak cnt fail ran most own HJ HL (fun x H => H)).
- intros a k0 _ H. exact H.
- apply Permutation_refl. }
(* ---- g_count <> g_fail_at: n + HEAD is admissible (TOOBIG excluded), the malloc wrapper ---- *)
rewrite branch_ne_U, (fm_U0 E _ 33 cnt AG1 ltac:(lia) E33 ltac:(lia)), (fm_U0 E _ 34 fail AG1 ltac:(lia) E34 ltac:(lia)) in Hc.
assert (Hcf : cnt <> fail) by (intros Heq; rewrite Heq, Z.eqb_refl in Hc; discriminate Hc).
(* the call is made (cnt <> fail): the text's guarded LIVE premise applies from here on *)
specialize (Hlive Hcf).
clear Hc.
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FM_Bspan; [fm_wr AG1 Usp HSTK ltac:(fun H => fail)|].
fm_newenv E HS AG1 AG2.
fm_ka KA fm_noblk.
clear HF HFr HG.
rewrite HSTK in Hslo, Hbot.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
pose proof (alloc_model_laws_x_cf B (universe_ok_of_ARcf SEGS B ly S Hp W mem md HAR0)) as AMX.
(* the call memory QMm_cf at the call: the room from room_live_room, cf_hull_ok from the text's budget
   (PresetHullPay.hull_ok_of_budget), arodata_ok_cf from the entry's reader form through the journal (below) *)
pose proof (QM_cf_of_room SEGS B ly S Hp W mem md HAR0 HQT (YGcfRoomLive.room_live_room S HRL)
  (PresetHullPay.hull_ok_of_budget S _ HHUL)) as HQM0.
assert (Hpr : 0 <= @pi_ret_malloc prh_img_A < 2 ^ 64) by (split; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
let retk := eval vm_compute in (match sr_get (ss_regs ssx) 1 with SOff _ z => z | _ => 0 end) in
assert (Hretk : BASE + retk = @pi_ret_malloc prh_img_A) by (vm_compute; reflexivity);
assert (Hspc : spZ (ms_regs msx) = spZ regs - 32)
  by (unfold spZ at 1; rewrite Rsp2, Usp, unsigned_lit_small by lia; lia);
assert (Hret : raZ (ms_regs msx) = @pi_ret_malloc prh_img_A)
  by (unfold raZ; rewrite Rra, Hretk; apply unsigned_lit_small; exact Hpr);
assert (Hs0 : s0Z (ms_regs msx) = n) by (unfold s0Z; rewrite Rs0, E10; unfold w64; apply unsigned_lit_small; lia);
assert (Ha0 : getr (ms_regs msx) 10 = w64 (n + 16))
  by (rewrite Ra0, E10; unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
assert (Hchp : chain_pre ly (aview SEGS (w_H W) (ms_mem msx)) (ms_regs msx) []);
[ unfold chain_pre; split; [rewrite Hret; apply Z.leb_le; vm_compute; reflexivity|];
  destruct (frame0_ok ly (ms_regs msx)); [|reflexivity];
  replace (bad_next (spZ (ms_regs msx)) (ly_top ly) (s0Z (ms_regs msx))) with true; [reflexivity|];
  symmetry; unfold bad_next; rewrite Hs0, Hspc;
  apply orb_true_intro; left; apply orb_true_intro; left; apply Z.leb_le; lia
| ];
(* the call's trace is the text's prh_trace at the empty chain (prh_malloc_univ), a FIXED trace of the universe; the
   P'' call rule asks `admits`, which YG01.admits_fix gives from ARcf's universe_ok *)
assert (Htr : In (call_trace ly (pc_malloc_ra0 (as_code B)) (ms_regs msx) []) (as_universe B));
[ unfold call_trace; destruct (frame0_ok ly (ms_regs msx)); [|exact (proj1 HUNIV)];
  pose proof (proj2 HUNIV) as HU2; unfold prh_trace in HU2;
  unfold unwind_of_chain; cbn [flat_map app] in HU2 |- *; rewrite Hret; exact HU2
| ];
(* arodata_ok_cf at the call memory: the entry's reader form carried by the journal (arodata_ok_cf_of_journal_P at
   image A's rows; the footprint is empty, so it opens no sink) *)
assert (HQM : QMm_cf SEGS B S (ms_mem msx));
[ destruct HQM0 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6);
  refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 _))))));
  apply (arodata_ok_cf_of_journal_P (SK := SK) SEGS B PST ARcfx (@wle SEGS)
    _ _ [] ly S Hp W mem md _ ly S Hp W (ms_mem msx) _ _ [] HJ
    CfAroPresetA.relro_seg_preset_A (CfAroPresetA.errno_relro_preset_A B TB)
    CfAroPresetA.relro_top_preset_A CfAroPresetA.ro_reads_nw_preset_A fm_pst_aro);
  [ intros (r & Hin & _); destruct Hin | exact HRO ]
| ];
eapply SRr_bind;
[ exact (YGcallMxmnKeep.aj_malloc_x_ct_m_keep (SK := SK) SEGS B PST ARcfx QM_cf (QMm_cf SEGS B) malloc_cf cf_malloc_max
    free_cf (Wf_cf (as_universe B)) xs_cf LAWS Hsegs (pal_env B PAL) OWNLOW WFL AMX (QMQ_cf SEGS B) XSL AMALLOCx W Ex
    ssx msx
    _ _ [] ly S Hp W mem md [] ly S Hp _ _ (n + 16) (-32) (ew Ex 2) (Z_to_bv 64 (BASE + retk)) [] HS
    ltac:(cbn [ss_pc setpc]; exact (pal_malloc B PAL)) ltac:(vm_compute; reflexivity) HJ
    Ha0 ltac:(rewrite HMX; lia) Hlive (st_ok_restrict_reg SEGS (w_H W) Ex ssx msx 2%bv HS) eq_refl
    (eq_trans (fm_ag_u _ _ 2 AG2 ltac:(lia)) Usp) eq_refl ltac:(lia) ltac:(unfold ASTACK; rewrite HSTK; lia)
    ltac:(rewrite Rgp, E3; exact Hgp) ltac:(rewrite Rtp, E4; exact Htp) Rra
    (ret_ok_codeptr_v (PI := PA) retk ltac:(lia) eq_refl) HQM Hchp
    (YG01.admits_fix _ _ _ (universe_ok_of_ARcf SEGS B ly S Hp W mem md HAR0) Htr))
| ]
end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & HPRE2 & Htr2 &
  (p & trc & Hpath & Hgf & Hleaf & Hpn & Hpres_p) & Hres & Hmn2).
(* the post journal carries the call's trace in its wild budget; the trace is a FIXED one, so YCbqG.ajournal_xw_fix1
   drops it and the journal is the walk's ajournal_x again *)
apply (YCbqG.ajournal_xw_fix1 Htr) in HJ2.
(* the room after the call: h-mani-a8's RL_malloc_step at the named live-set bounds *)
pose proof (YGcfRoomLive.RL_malloc_step SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPRE2) (CfRoomLivePreset.preset_rl_sec_ok S Hsec)
  (CfRoomLivePreset.preset_rl_b24_ok S H24) HRL Hpath) as HRL2.
cbn [snd] in HRL2.
(* the memnorm carrier across the call: the keep rule's last conjunct *)
pose proof (fun H => Hmn2 (HPM H)) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _). rewrite HSTK in Hpres2.
pose proof (prh_live_room B ly S Hp W mem Lam peak cnt fail ran n most own HL
  (prh_ablocks_nonneg_cf B ly S Hp W mem md HAR0) Hlive) as [_ Hlr].
pose proof (prh_ledger_sizes B ly S Hp W mem Lam peak cnt fail ran most own HL) as HLs.
pose proof (prh_lsum_nonneg Lam HLs) as Hl0.
destruct Hres as [(Hr0 & Eab2 & Hk2 & Herr & Hoom) | (Hr4096 & Eab2 & Hk2)].
{
(* ---- REFUSED (prh_alloc_post arm 2): the allocator's NULL, then refused(n) (merged alloc.c :70-78; A' 0x85824 ..
   0x8586c): held = g_live + n, g_peak := held if g_peak < held, g_ran_out := 1 if n <= g_most, return 0 ---- *)
subst res. assert (Hp0 : p = PNull) by (apply Hpn; reflexivity). subst p.
unfold acall_kept_x, acall_kept in Hk2. destruct Hk2 as (K1 & _ & K3 & _).
assert (KA2 : forall a, fm_cell a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (fm_cell_pst a Ha) as Hpa. rewrite <- (KA a Ha).
  apply K3; [exact (pst_in_img_A a Hpa) | exact (proj1 (pal_pst_ok a Hpa)) | exact (proj2 (pal_pst_ok a Hpa))]. }
clear KA. rename KA2 into KA.
assert (KE : forall a, fm_errno a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by (intros; reflexivity).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3; 4; 5; 6; 7; 8]%nat HS3.
match type of HS3 with ?T -> _ => assert (HRK3 : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [..|apply Forall_nil].
  - apply (fm_kept_gen _ _ _ 2 (spZ regs)); [exact (eq_trans (fm_ag_u _ _ 2 AG2 ltac:(lia)) Usp) | |].
    + intros a Ha. apply (mbyte_of_aview SEGS). apply K1; [lia | unfold ASTACK; lia].
    + intros a Ha. apply (apresent_writable SEGS). apply Hpres2. lia.
  - apply (fm_kept_st _ _ _ 7 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 8 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 9 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 10 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 11 1 1); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 14 8 0); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))]. }
specialize (HS3 HRK3). clear HRK3. rewrite <- restrict_mkst_fx in HS3.
lazymatch type of HS3 with st_ok_pi _ _ ?Ey _ _ =>
  assert (HEI3 : img_env VAL A_LIM Ey) by (apply img_env_havoc; [assumption | cbv; lia]) end.
fm_newenv E HS3 AG2 AG3.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS3 ltac:(cbn [ms_regs restrict mkst]; rewrite Ha02; reflexivity) eq_refl) as HS4.
clear HS HS3 SHOK. rename HS4 into HS. fm_shok HS SHOK.
(* beqz taken; ld g_live, ld g_peak, held; stop at `bgeu g_peak, held` (0x85844) *)
paj_run_tok_x_inv (RUNM mem) HS HJ2 SHOK HPM FM_Bspan; [fm_wr AG3 Usp HSTK ltac:(fun H => fail)|].
fm_newenv E HS AG3 AG4.
fm_ka KA fm_noblk. fm_ke KE fm_noblk.
clear HF HFr HG.
(* refused()'s held = g_live + n, as the runner holds it (`add a2, a1, s0`, `sltu`, `neg`, `or`): exact below 2 ^ 64 *)
assert (UH : forall Ex, env_agree 39 E Ex ->
  U Ex (SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SOff 35 0)) (SOff 35 0)))
    (SAlu ALU_ADD (SOff 10 0) (SOff 35 0))) = Ledger.lsum Lam + n).
{ intros Ex AGx. apply fm_U_sat; [| exact (fm_U0 E _ 35 _ AGx ltac:(lia) E35 ltac:(lia)) | lia | lia | lia].
  rewrite fm_U_add, (fm_U0 E _ 10 n AGx ltac:(lia) E10 ltac:(lia)), (fm_U0 E _ 35 _ AGx ltac:(lia) E35 ltac:(lia)).
  rewrite Z.mod_small by lia. lia. }
psrr_branch_tok RUNm BR HS SHOK FM_Bspan.
(* path split 1, `bgeu g_peak, held` (0x85844): taken (g_peak >= held, no store) / not taken (the store at 0x85848) *)
all: rewrite branch_geu_U, (fm_U0 E _ 36 peak AG4 ltac:(lia) E36 ltac:(lia)), (UH _ AG4) in Hc.
all: lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc
  | negb _ = false => apply negb_false_iff, Z.ltb_lt in Hc
  end.
all: rename Hc into Hpk.
(* the store or not; ld g_most; stop at `bgeu g_most, n` (0x85854) *)
all: paj_run_tok_x_inv (RUNM mem) HS HJ2 SHOK HPM FM_Bspan; [fm_wr AG4 Usp HSTK ltac:(fun H => fail)|].
all: fm_newenv E HS AG4 AG5.
all: fm_ka KA fm_noblk. all: fm_ke KE fm_noblk.
all: clear HF HFr HG.
all: psrr_branch_tok RUNm BR HS SHOK FM_Bspan.
(* path split 2, `bgeu g_most, n`: taken (n <= g_most: g_ran_out := 1, the sb at 0x8586c) / not taken (kept) *)
all: rewrite branch_geu_U, (fm_U0 E _ 38 most AG5 ltac:(lia) E38 Rmost), (fm_U0 E _ 10 n AG5 ltac:(lia) E10 ltac:(lia)) in Hc.
all: lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc
  | negb _ = false => apply negb_false_iff, Z.ltb_lt in Hc
  end.
all: rename Hc into Hmo.
(* a0 = 0, the epilogue, ret *)
all: paj_run_tok_x_inv (RUNM mem) HS HJ2 SHOK HPM FM_Bspan; [fm_wr AG5 Usp HSTK ltac:(fun H => fail)|].
all: fm_newenv E HS AG5 AG6.
all: fm_ka KA fm_noblk. all: fm_ke KE fm_noblk.
all: clear HF HFr HG.
all: prreg HS (10%bv : bv 5) R10. all: prreg HS (1%bv : bv 5) R1.
all: eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
all: intros mat'. all: unfold apost_base_x.
all: fm_jk HJ2.
all: split; [cbn [ms_regs]; rewrite R1, E1; rewrite Hra; reflexivity|].
all: split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARcfx LAWS Hsegs); exact HJ2|].
all: split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs xs0 HS);
  [exact (YP03.env_agree_trans 32 _ _ _ AGe (YP03.env_agree_le 32 39 _ _ ltac:(lia) AG6)) | vm_compute; reflexivity]|].
all: cbv beta. all: split; [|exact HPM].
all: exists 0. all: split; [rewrite R10; reflexivity|].
all: split; [exact HRL2|].
(* the hull use: the refused call's model path (YGcfSecsStep.secs_malloc_step, PresetHullBudget.hull_used_of_call) *)
all: split; [exact (PresetHullBudget.hull_used_of_call _ S _ S2 (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath))|].
(* a refusal is no run event, E = []: the position and its history stay (h-pre-b1's room_pos_keep_alloc_null) *)
all: split; [intros _ psm px pos pi pH0 phist Hpos _; exists phist; cbn [length]; rewrite Nat.add_0_r;
  exact (PresetRoomPosKeep.room_pos_keep_alloc_null SEGS B _ _ _ _ _ _ _ _ psm px pos pi pH0 phist (n + 16) _ trc S2
    (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPRE2) ltac:(rewrite HMX; lia) Hlive Htr Hpath Hpos)|].
all: split; [intros Hne; exfalso; exact (Hne eq_refl)|].
(* THE OUTCOME: refuted - at a consumer allocation of the run the allocator's NULL on its granted path (Hpath / Hgf,
   the call rule's) is impossible: the kit's PRH_Refute.prh_refute_window at the call's state S (the run's event 0 of
   [HMal (n + cf_head)]) *)
all: split; [intros psm px pos pi pH0 phist Hpos Hrun Hcons _; exfalso;
  apply (PRH_Refute.prh_refute_window (ci := CfImg_A) (cp := CfParams_preset) (as_universe B) psm px pos pi _ 0 _
    pH0 phist S Hrun Hcons eq_refl eq_refl);
  [ rewrite Nat.add_0_r; exact Hpos
  | exact (proj1 (YGcfRoomLive.rl_of_acall_pre_cf SEGS B _ _ _ _ _ _ _ _
      (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPRE2)))
  | left; do 4 eexists; exact (conj Hpath Hgf) ]|].
all: right; left. all: split; [exact Hcf|]. all: split; [reflexivity|]. all: split; [reflexivity|].
all: split; [exact Eab2|].
all: split; [do 5 eexists; exact (malloc_cf_null_post_of_leaf SEGS B ly S Hp W _ _ _ (n + 16) [] _ trc S2 W2 _
  (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPRE2) Hpath Hgf (malloc_leaf_x_xs_cf SEGS B _ _ _ _ _ _ _ _ _ _ _ Hleaf))|].
all: split; [apply (fm_rd32_keep (aview SEGS (w_H W2) mem2)); [intros i Hi; apply KE; unfold fm_errno; lia | exact Herr]|].
(* the ledger (S1Ledger's prh_ledger_frame): Lam and Hp unchanged; g_peak = max (g_peak, min SIZE_MAX (g_live + n)),
   g_count + 1, g_ran_out = if n <=? g_most then 1 else g_ran_out *)
all: apply (prh_ledger_frame B ly S Hp W mem ly2 S2 Hp W2 _ Lam peak cnt fail ran _ _ _ _ _ _ HL);
  [ eapply (fm_glob_of_ss _ _ W2 _ (SOff 35 0) _ (SOff 33 1) (SOff 34 0) _ _ _ _ _ _ _ _ HS);
    [ assumption | fm_cvt | fm_cvt | fm_cvt | fm_cvt | fm_cvt
    | exact (fm_U0 E _ 35 _ AG6 ltac:(lia) E35 ltac:(lia))
    | first [ rewrite (fm_U0 E _ 36 peak AG6 ltac:(lia) E36 ltac:(lia)); unfold SIZE_MAXZ; lia
            | rewrite (UH _ AG6); unfold SIZE_MAXZ; lia ]
    | exact (fm_U_off E _ 33 _ 1 AG6 ltac:(lia) E33 ltac:(lia))
    | exact (fm_U0 E _ 34 _ AG6 ltac:(lia) E34 ltac:(lia))
    | first [ rewrite U_SLit; destruct (Z.leb_spec n most); [reflexivity | lia]
            | rewrite (fm_U0 E _ 37 ran AG6 ltac:(lia) E37 ltac:(lia)); destruct (Z.leb_spec n most); [lia | reflexivity] ]
    | unfold SIZE_MAXZ; lia
    | destruct (Z.leb_spec n most); [right; reflexivity | exact Rr]
    | exact (proj2 (fm_keeps_post W W2 mem _ KA) most HMOST)
    | exact (proj1 (fm_keeps_post W W2 mem _ KA) own HOWN) ]
  | exact (fm_heads_kept _ _ ly S Hp W mem md ly2 S2 Hp W2 _ _ _ Lam peak cnt fail ran most own HJ2 HL
      (fun x H => eq_ind_r (fun l => In x l) H Eab2))
  | intros a k0 _ H; rewrite Eab2; exact H
  | apply Permutation_refl ].
}
(* ---- SUCCESS (prh_alloc_post arm 3): the fresh block b; the two instrumented header stores, own's head and poison,
   the ledger ---- *)
rename res into b.
assert (Hreq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
assert (Hin2 : In (b, n + 16) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARcfx LAWS ly2 S2 Hp W2 mem2 md2 b (n + 16) HAR2 Hin2) as (Hb16 & _ & Hbceil & Hbapp & Hbpres & Hpw2).
rewrite Hreq in Hbceil, Hbapp, Hbpres.
pose proof (fm_newblk ly S ly2 S2 Hp W2 mem2 md2 (b, n + 16) HAR2 ltac:(cbn; lia) Eab2) as Hnew.
pose proof (fm_hp_apart ly S Hp W mem Lam peak cnt fail ran most own ly2 S2 Hp W2 mem2 md2 b (n + 16) HL HAR2 Eab2
  ltac:(lia)) as Hhp.
pose proof (proj1 (prh_ledger_iff B ly S Hp W mem Lam peak cnt fail ran most own) HL) as [_ HLB].
pose proof (prh_fresh_malloc B ly S Hp W mem ly2 S2 Lam b n HLB Hn0 Eab2 Hpw2) as Hfresh.
assert (Hnimg : forall a, b <= a < b + 8 -> ~ in_img SEGS a)
  by (intros a Ha; apply (blk_img_x SEGS B ARcfx LAWS ly2 S2 Hp W2 mem2 md2 b (n + 16) a HAR2 Hin2); rewrite Hreq; lia).
assert (Hpnn : p <> PNull) by (intros Hq; apply Hpn in Hq; lia).
unfold acall_kept_x, acall_kept in Hk2. destruct Hk2 as (K1 & _ & K3 & _).
assert (KA2 : forall a, fm_cell a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (fm_cell_pst a Ha) as Hpa. rewrite <- (KA a Ha).
  apply K3; [exact (pst_in_img_A a Hpa) | exact (proj1 (pal_pst_ok a Hpa)) | exact (proj2 (pal_pst_ok a Hpa))]. }
clear KA. rename KA2 into KA.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3; 4; 5; 6; 7; 8]%nat HS3.
match type of HS3 with ?T -> _ => assert (HRK3 : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [..|apply Forall_nil].
  - apply (fm_kept_gen _ _ _ 2 (spZ regs)); [exact (eq_trans (fm_ag_u _ _ 2 AG2 ltac:(lia)) Usp) | |].
    + intros a Ha. apply (mbyte_of_aview SEGS). apply K1; [lia | unfold ASTACK; lia].
    + intros a Ha. apply (apresent_writable SEGS). apply Hpres2. lia.
  - apply (fm_kept_st _ _ _ 7 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 8 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 9 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 10 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 11 1 1); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))].
  - apply (fm_kept_st _ _ _ 14 8 0); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. apply (mbyte_of_aview SEGS). apply K3; [exact (pst_in_img_A a Ha) | exact (proj1 (pal_pst_ok a Ha)) | exact (proj2 (pal_pst_ok a Ha))]. }
specialize (HS3 HRK3). clear HRK3. rewrite <- restrict_mkst_fx in HS3.
lazymatch type of HS3 with st_ok_pi _ _ ?Ey _ _ =>
  assert (HEI3 : img_env VAL A_LIM Ey) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (Ub : bv_unsigned (ew Ey 44) = b)
    by (change (ew Ey 44) with (getr regs2 10%bv); rewrite Ha02; unfold w64; apply unsigned_lit_small; lia) end.
fm_newenv E HS3 AG2 AG3.
(* the block's address fact, its first 8 bytes as a region, and the shadow entry of its 16 head bytes *)
pose proof (st_ok_pi_add_fact _ _ _ 44 (mkAF 4096 (2 ^ 47 - 2 ^ 23) 4) HS3
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Ub; change (2 ^ 4) with 16;
        split; [lia | split; [exact Hb16 | lia]])) as HS4.
pose proof (fm_blk_static_disj 7 b 8 ltac:(lia) ltac:(cbn; lia) Hnimg) as D7.
pose proof (fm_blk_static_disj 8 b 8 ltac:(lia) ltac:(cbn; lia) Hnimg) as D8.
pose proof (fm_blk_static_disj 9 b 8 ltac:(lia) ltac:(cbn; lia) Hnimg) as D9.
pose proof (fm_blk_static_disj 10 b 8 ltac:(lia) ltac:(cbn; lia) Hnimg) as D10.
pose proof (fm_blk_static_disj 11 b 1 ltac:(lia) ltac:(cbn; lia) Hnimg) as D11.
pose proof (fm_blk_static_disj 14 b 8 ltac:(lia) ltac:(cbn; lia) Hnimg) as D14.
fm_lits0_in D7. fm_lits0_in D8. fm_lits0_in D9. fm_lits0_in D10. fm_lits0_in D11. fm_lits0_in D14.
pose proof (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 44%nat) 0 8 0 8 []) HS4 eq_refl
  ltac:(unfold region_ok; cbv zeta; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite Ub; split; [lia|]; split; [lia|]; split; [|constructor];
        intros o Ho; apply (apresent_writable SEGS); apply Hbpres; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite Ub; try rewrite (proj1 AG3 2%nat ltac:(lia)); rewrite Usp;
        rewrite !HEI3 by (unfold A_TEXT, A_LIM; lia); fm_lits;
        repeat match goal with |- _ /\ _ => split end; try exact I; lia)) as HS5.
lazymatch type of HS5 with st_ok_pi _ _ ?Ey _ (restrict (w_H ?Wx) ?msx) =>
assert (SHOK5 : sh_ok SEGS FM_Bx [mkSHE 44 0 16] Ey (mrestrict (w_H Wx) (ms_mem msx))) end.
{ unfold sh_ok. constructor; [|constructor].
  destruct (alx_shadow SEGS B ARcfx LAWS ly2 S2 Hp W2 mem2 md2 b (n + 16) HAR2 Hin2 Hhp) as [Hbs _].
  rewrite Hreq in Hbs.
  apply (shent_ok_of_range SEGS (w_H W2) mem2 _ FM_Bx 44 b (n + 16) b 0 16).
  - eapply block_shadow_range; [exact Hbs | lia | lia].
  - exact (fm_U0 E _ 32 SHADOW_OFF AG3 ltac:(lia) E32 ltac:(unfold SHADOW_OFF; lia)).
  - rewrite U_SOff, Ub, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF. lia. }
clear HS HS3 HS4 SHOK. rename HS5 into HS.
paj_run_tok_x_inv (RUNM mem) HS HJ2 SHOK5 HPM FM_Bspan;
  [fm_wr AG3 Usp HSTK ltac:(fun H => left; unfold awr_byte; right; right; left; exists b, (n + 16);
     split; [exact Hin2|]; split; [exact Hnew|]; rewrite Hreq; rewrite Ub in H; lia)|].
fm_newenv E HS AG3 AG4.
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (Ub4 : bv_unsigned (ew Ey 44) = b) by (rewrite ?ew_ewset_other by lia; exact Ub) end.
fm_ka KA ltac:(fun a Ha Hr =>
  first [ rewrite Ub in Hr | rewrite Ub4 in Hr
        | rewrite Ha02 in Hr; unfold w64 in Hr; rewrite unsigned_lit_small in Hr by lia | idtac ];
  exact (Hnimg a ltac:(lia) (pst_in_img_A a (fm_cell_pst a Ha)))).
clear HF HFr HG.
(* own's head: the 8 bytes of n at b *)
lazymatch type of HS with st_ok _ ?Ey ?ssy (restrict _ ?msy) =>
  assert (Hhdr4 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msy)) b 8 n)
    by exact (fm_hdr_of_st Ey ssy W2 msy 44 (SOff 10 0) b n HS Ub4 ltac:(fm_cvt)
      ltac:(intros k Hk; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia; fm_cvt)
      (fm_U0 E _ 10 n AG4 ltac:(lia) E10 ltac:(lia))) end.
assert (Hnp_b : forall a, b <= a < b + 8 -> ~ Exists (in_zr a) PST)
  by (intros a Ha Hx; exact (Hnimg a Ha (pst_in_img_A a Hx))).
(* ---- own: __asan_poison_memory_region (b, cf_head), with the memnorm keep (YGcallMxmn's aj_poison_x_m) ---- *)
prreg HS (10%bv : bv 5) Pa0. prreg HS (11%bv : bv 5) Pa1. prreg HS (1%bv : bv 5) Pra.
prreg HS (3%bv : bv 5) Pgp. prreg HS (4%bv : bv 5) Ptp.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
let retk := eval vm_compute in (match sr_get (ss_regs ssx) 1 with SOff _ z => z | _ => 0 end) in
eapply SRr_bind;
[ exact (YGcallMxmn.aj_poison_x_m (SK := SK) SEGS B PST ARcfx cf_head LAWS Hsegs cf_pc_poison APOISONx W2 Ex ssx msx
    _ _ [] ly S Hp W mem md [] ly2 S2 Hp _ _ b (n + 16) (-32) (ew Ex 2) (Z_to_bv 64 (BASE + retk)) HS
    ltac:(cbn [ss_pc setpc]; vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2
    ltac:(rewrite Pa0; exact Ha02) ltac:(rewrite Pa1; reflexivity) eq_refl Hin2 ltac:(rewrite Hreq; cbn; lia)
    (st_ok_restrict_reg SEGS (w_H W2) Ex ssx msx 2%bv HS) eq_refl
    (eq_trans (fm_ag_u _ _ 2 AG4 ltac:(lia)) Usp) eq_refl ltac:(lia) ltac:(unfold ESTACK; rewrite HSTK; lia)
    ltac:(rewrite Pgp, E3; exact Hgp) ltac:(rewrite Ptp, E4; exact Htp) Pra
    (ret_ok_codeptr_v (PI := PA) retk ltac:(lia) eq_refl))
| ] end.
cbv beta. intros W3 c3 Hwle3 (EW3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hsh3 & Hkp3 & Hpr3 & Hmn3). subst W3.
pose proof (fun H => Hmn3 (HPM H)) as HPM3. clear HPM Hmn3. rename HPM3 into HPM.
assert (KA3 : forall a, fm_cell a -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (KA a Ha). pose proof (fm_cell_low a Ha) as Hlow.
  apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)); left; lia]. }
clear KA. rename KA3 into KA.
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _). rewrite HSTK in Hpres3.
destruct (alx_blocks SEGS B ARcfx LAWS ly2 S2 (b :: Hp) W2 mem3 md3 b (n + 16) HAR3 Hin2) as (_ & _ & _ & _ & Hbpres3 & _).
rewrite Hreq in Hbpres3.
jafter_call_keep_pi HS 60%nat regs3 (mrestrict (w_H W2) mem3) HP3 [1; 2; 3; 4; 5; 6; 7]%nat HS6.
match type of HS6 with ?T -> _ => assert (HRK6 : T) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [..|apply Forall_nil].
  - apply (fm_kept_gen _ _ _ 2 (spZ regs)); [exact (eq_trans (fm_ag_u _ _ 2 AG4 ltac:(lia)) Usp) | |].
    + intros a Ha. apply (mbyte_of_aview SEGS). apply Hkp3; [lia | unfold ESTACK; lia |].
      apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)). right; right; lia.
    + intros a Ha. apply (apresent_writable SEGS). apply Hpres3. lia.
  - apply (fm_kept_st _ _ _ 7 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. pose proof (Hsegs a (pst_in_img_A a Ha)) as Hlow. apply (mbyte_of_aview SEGS).
    apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)); left; lia].
  - apply (fm_kept_st _ _ _ 8 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. pose proof (Hsegs a (pst_in_img_A a Ha)) as Hlow. apply (mbyte_of_aview SEGS).
    apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)); left; lia].
  - apply (fm_kept_st _ _ _ 9 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. pose proof (Hsegs a (pst_in_img_A a Ha)) as Hlow. apply (mbyte_of_aview SEGS).
    apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)); left; lia].
  - apply (fm_kept_st _ _ _ 10 8 8); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. pose proof (Hsegs a (pst_in_img_A a Ha)) as Hlow. apply (mbyte_of_aview SEGS).
    apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)); left; lia].
  - apply (fm_kept_st _ _ _ 11 1 1); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. pose proof (Hsegs a (pst_in_img_A a Ha)) as Hlow. apply (mbyte_of_aview SEGS).
    apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)); left; lia].
  - apply (fm_kept_st _ _ _ 14 8 0); [lia | assumption | lia | unfold fm_w; cbn [Nat.eqb]; lia |].
    intros a Ha. pose proof (Hsegs a (pst_in_img_A a Ha)) as Hlow. apply (mbyte_of_aview SEGS).
    apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) a Hbapp Hbceil ltac:(lia)); left; lia]. }
specialize (HS6 HRK6). clear HRK6. rewrite <- restrict_mkst_fx in HS6.
lazymatch type of HS6 with st_ok_pi _ _ ?Ey _ _ =>
  assert (HEI6 : img_env VAL A_LIM Ey) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (Ub6 : bv_unsigned (ew Ey 44) = b) by (rewrite ew_havoc_old by lia; exact Ub4) end.
assert (Hhdr6 : val_mem SEGS (mrestrict (w_H W2) mem3) b 8 n).
{ apply (prh_val_mem_keep (PA := PA) _ _ _ _ _ Hhdr4). intros k Hk. apply (mbyte_of_aview SEGS).
  apply Hkp3; [lia | unfold ESTACK; lia | apply (fm_not_shadow b (n + 16) _ Hbapp Hbceil ltac:(lia)); right; left; lia]. }
fm_newenv E HS6 AG4 AG6.
clear HS SHOK5. rename HS6 into HS. fm_shok HS SHOK.
(* ---- g_live += n; the g_peak test ---- *)
paj_run_tok_x_inv (RUNM mem) HS HJ3 SHOK HPM FM_Bspan; [fm_wr AG6 Usp HSTK ltac:(fun H => fail)|].
fm_newenv E HS AG6 AG7.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msy) =>
  assert (Hhdr7 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msy)) b 8 n) end.
{ apply (prh_val_mem_keep (PA := PA) _ _ _ _ _ Hhdr6). intros k Hk. apply (mbyte_of_aview SEGS).
  apply (fm_aview_of_frame W2 _ _ _ _ _ HFr); [|lia].
  pose proof (Hnp_b (b + Z.of_nat k) ltac:(lia)) as Hnp. fm_nw AG6 Usp Hnp. }
fm_ka KA fm_noblk.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ey _ _ => assert (Ub7 : bv_unsigned (ew Ey 44) = b) by (rewrite ?ew_ewset_other by lia; exact Ub6) end.
psrr_branch_tok RUNm BR HS SHOK FM_Bspan.
all: rewrite branch_geu_U, (fm_U0 E _ 36 peak AG7 ltac:(lia) E36 ltac:(lia)), fm_U_add,
  (fm_U0 E _ 10 n AG7 ltac:(lia) E10 ltac:(lia)), (fm_U0 E _ 35 _ AG7 ltac:(lia) E35 ltac:(lia)), Z.mod_small in Hc by lia.
all: lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff, Z.ltb_ge in Hc
  | negb _ = false => apply negb_false_iff, Z.ltb_lt in Hc
  end.
(* ---- both arms: g_peak := max (g_peak, g_live) (the second arm stores it), return b + HEAD ---- *)
all: paj_run_tok_x_inv (RUNM mem) HS HJ3 SHOK HPM FM_Bspan; [fm_wr AG7 Usp HSTK ltac:(fun H => fail)|].
all: fm_newenv E HS AG7 AG8.
all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msy) =>
  assert (Hhdr8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msy)) b 8 n) by (
    apply (prh_val_mem_keep (PA := PA) _ _ _ _ _ Hhdr7); intros k Hk; apply (mbyte_of_aview SEGS);
    apply (fm_aview_of_frame W2 _ _ _ _ _ HFr); [|lia];
    pose proof (Hnp_b (b + Z.of_nat k) ltac:(lia)) as Hnp; fm_nw AG7 Usp Hnp) end.
all: fm_ka KA fm_noblk.
all: lazymatch type of HS with st_ok_pi _ _ ?Ey _ _ =>
  assert (Ub8 : bv_unsigned (ew Ey 44) = b) by (rewrite ?ew_ewset_other by lia; exact Ub7) end.
all: prreg0 HS (10%bv : bv 5) R10.
all: prreg HS (1%bv : bv 5) R1.
all: eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
all: intros mat'. all: unfold apost_base_x.
all: fm_jk HJ3.
all: split; [cbn [ms_regs]; rewrite R1, E1; rewrite Hra; reflexivity|].
all: split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARcfx LAWS Hsegs); exact HJ3|].
all: split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs xs0 HS);
  [exact (YP03.env_agree_trans 32 _ _ _ AGe (YP03.env_agree_le 32 39 _ _ ltac:(lia) AG8)) | vm_compute; reflexivity]|].
all: cbv beta. all: split; [|exact HPM].
all: exists (b + 16).
all: split; [cbn [ms_regs]; rewrite R10; exact (fm_denot_off _ 44 b 16 Ub8 ltac:(lia))|].
all: split; [exact HRL2|].
(* the hull use: the grant's model path (YGcfSecsStep.secs_malloc_step, PresetHullBudget.hull_used_of_call) *)
all: split; [exact (PresetHullBudget.hull_used_of_call _ S _ S2 (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath))|].
all: split; [intros Hz; exfalso; lia|].
(* the grant, E = [HMal (n + cf_head)]: the position advances by this call's own event (h-pre-b1's
   room_pos_keep_alloc; PRH_Base.prh_run_at_one turns the one-event run premise into nth_error) *)
all: split; [intros _ psm px pos pi pH0 phist Hpos Hrun; exists phist;
  apply (proj1 (PRH_Base.prh_run_at_one psm px pos pi _)) in Hrun; rewrite HHD in Hrun;
  cbn [length]; rewrite Nat.add_1_r;
  exact (PresetRoomPosKeep.room_pos_keep_alloc SEGS B _ _ _ _ _ _ _ _ psm px pos pi pH0 phist (n + 16) _ trc p S2
    (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPRE2) ltac:(rewrite HMX; lia) Hlive Htr Hpath Hpnn Hpos Hrun)|].
(* THE OUTCOME: the call granted, res = b + 16 <> 0, and the position as in the grant arm above *)
all: split; [intros psm px pos pi pH0 phist Hpos Hrun _ _; split; [lia|]; exists phist;
  apply (proj1 (PRH_Base.prh_run_at_one psm px pos pi _)) in Hrun; rewrite HHD in Hrun;
  cbn [length]; rewrite Nat.add_1_r;
  exact (PresetRoomPosKeep.room_pos_keep_alloc SEGS B _ _ _ _ _ _ _ _ psm px pos pi pH0 phist (n + 16) _ trc p S2
    (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPRE2) ltac:(rewrite HMX; lia) Hlive Htr Hpath Hpnn Hpos Hrun)|].
all: right; right.
all: pose proof HJ3 as (HARF & _).
all: destruct (AR_shadow_law_ok_cf SEGS B ly2 S2 (b :: Hp) W2 _ _ b (n + 16) (proj1 HARF) Hin2) as [Hbs Hhu].
all: assert (Hsk : hd_skip (b :: Hp) b = 16) by (unfold hd_skip; cbn [existsb]; rewrite Z.eqb_refl; reflexivity).
all: rewrite Hsk, Hreq in Hbs. all: rewrite Hreq in Hhu.
all: destruct (alx_blocks SEGS B ARcfx LAWS ly2 S2 (b :: Hp) W2 _ _ b (n + 16) HARF Hin2) as (_ & _ & _ & _ & HbpF & _).
all: rewrite Hreq in HbpF.
all: split; [exact Hcf|]. all: split; [rewrite HHD; lia|].
all: split; [rewrite Z.add_mod by lia; rewrite Hb16; reflexivity|].
all: split; [exact Hfresh|].
all: split; [rewrite HHD; f_equal; lia|].
all: split; [rewrite Eab2, HHD; replace (b + 16 - 16) with b by lia; reflexivity|].
all: split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
all: split; [intros Hnpos; apply (fm_hull_sub _ b (n + 16) (b + 16) n Hhu); lia|].
all: split; [destruct (fm_bytes_present W2 _ (b + 16) (Z.to_nat n) ltac:(intros a Ha; apply HbpF; lia)) as (l & Hl & Hg);
  exists l; split; [rewrite Hl; lia | exact Hg]|].
(* S1Ledger.prh_ledger_own's premises: the statics' final values (glob, with g_most / g_own_ran_out kept), live' = lsum + n,
   peak' = max, the old heads kept, the old blocks kept, n's range, the block, its alignment, its head n, its freshness *)
all: apply (S1Ledger.prh_ledger_own B ly S Hp W mem ly2 S2 (b :: Hp) W2 _ Lam peak cnt fail ran _ _ _ _ b n most own HL).
all: try (eapply (fm_glob_of_ss _ _ W2 _ _ _ _ _ _ _ _ _ _ _ _ _ HS);
  [assumption | fm_cvt | fm_cvt | fm_cvt | fm_cvt | fm_cvt | | | | | | lia | exact Rr
  | exact (proj2 (fm_keeps_post W W2 mem _ KA) most HMOST) | exact (proj1 (fm_keeps_post W W2 mem _ KA) own HOWN)]).
all: try (rewrite fm_U_add, (fm_U0 E _ 10 n AG8 ltac:(lia) E10 ltac:(lia)), (fm_U0 E _ 35 _ AG8 ltac:(lia) E35 ltac:(lia)),
  Z.mod_small by lia; lia).
all: try (rewrite (fm_U0 E _ 36 peak AG8 ltac:(lia) E36 ltac:(lia)); lia).
all: try exact (fm_U_off E _ 33 _ 1 AG8 ltac:(lia) E33 ltac:(lia)).
all: try exact (fm_U0 E _ 34 _ AG8 ltac:(lia) E34 ltac:(lia)).
all: try exact (fm_U0 E _ 37 _ AG8 ltac:(lia) E37 ltac:(lia)).
all: try exact (fm_heads_kept _ _ ly S Hp W mem md ly2 S2 (b :: Hp) W2 _ _ _ Lam peak cnt fail ran most own HJ3 HL
      (fun x H => ltac:(rewrite Eab2; apply in_or_app; left; exact H))).
all: try (intros a k0 _ H; rewrite Eab2; apply in_or_app; left; exact H).
all: try exact Hn0.
all: try exact Hin2.
all: try (rewrite HHD, Z.add_mod by lia; rewrite Hb16; reflexivity).
all: try exact Hhdr8.
all: try exact Hfresh.
all: try reflexivity.
Qed.
End f.
End d.
