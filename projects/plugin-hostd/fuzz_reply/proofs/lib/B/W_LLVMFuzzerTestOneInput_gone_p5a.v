(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: p5st carries gn_cst and gn_runc; RIend at that cost bound *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE 5, part a: the table-order loop of fuzz_reply.c:646-653, fuzz_reply.asan-ubsan 0x84b78 (GT0) to
   check_shape_done's call at 0x84c84 (GCSD).  A PORT of image A's phase file lib/A/W_LLVMFuzzerTestOneInput_gone_p5.v
   (a working branch 32b23a20c3e): the model, block, journal-transport, coverage and value lemmas are
   A's text, the cut points, the walks and the transport across a call are rewritten at B's addresses, registers and
   frame, read from B's objdump (of the pinned binary fuzz_reply.asan-ubsan, guided by
   the old-stack B walk a working branch e29b582ba724 lib/B/Prog/SlotPass5.v), over the base
   lib/B/W_LLVMFuzzerTestOneInput_gone_base.v and the transport kit _gone_tk.v (a working branch
   85b530db754).
     for (i = 0; i < g_nsrc; i++) for (k = 0; k < 4; k++)
       if (g_s[k].open && g_s[k].fd == g_src[i].fd) {
         check_no_loss(&g_s[k], &at); check_shape_ends(&g_s[k], prefix, &at); }
   B against A (each read from B's objdump):
   - 0x84b78 `auipc a0,0x554` (0x5d8b78 = g_nsrc - 424) is spilled to F+112 and re-read at the outer latch 0x84c74
     (A keeps HI_G_NSRC in s7 and at F+120); B's i is s7, 56 i is s9 (made at the outer head 0x84b8c), s4 = s5 =
     &g_s[k], s6 = 4 - k, s8 / s10 = the shadow cells of g_s[k].open / .fd (from F+152 / F+120).
   - B's UBSan traps on &g_src[i] (0x84bd0 bltu, 0x84be0 null-consistency, 0x84be4 beqz, 0x84bec align8): the runner
     decides all but 0x84bd0 from the seat's atom facts (W_traps.v's recipe R1 / R2: atom 35 = g_src + 56 i with its two
     aliases); 0x84bd0 is closed with W_traps.v trap_ptr_bltu.
   - The loop's cut points: 0x84b78 GT0 -> 0x84b8c P5OH i -> 0x84bb0 P5IH i k -> (0x84c28 P5T | 0x84c0c P5C) ;
     0x84c0c P5C -> check_no_loss -> 0x84c18 P5M -> check_shape_ends -> 0x84c28 P5T -> (P5IH | 0x84c74 P5OT) ;
     P5OT -> (P5OH | 0x84c84 GCSD).  The two calls are in part b (W_LLVMFuzzerTestOneInput_gone_p5b.v), the two
     inductions and gp5_t0_csd in W_LLVMFuzzerTestOneInput_gone_p5.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ---- the bytes of the relay's table: entry i's 4-byte fd field (W_LLVMFuzzerTestOneInput_drain.v:103-162,
   copied with dr_ -> gp5_ so this phase imports no other phase's file) ---- *)
Lemma gp5_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma gp5_cat_len : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, gp5_eb_len, IH by assumption. lia.
Qed.
Lemma gp5_cat_nth : forall es i k d,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> (k < 56)%nat ->
  nth (56 * i + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth i es gn_e0)) d.
Proof.
  induction es as [|e es IH]; intros i k d HF Hi Hk; cbn [length] in Hi; [lia|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat]. destruct i as [|i].
  - replace (56 * 0 + k)%nat with k by lia. cbn [nth].
    apply app_nth1. rewrite gp5_eb_len by assumption. exact Hk.
  - rewrite app_nth2 by (rewrite gp5_eb_len by assumption; lia).
    rewrite gp5_eb_len by assumption.
    replace (56 * S i + k - 56)%nat with (56 * i + k)%nat by lia.
    cbn [nth]. apply IH; [exact HF | lia | exact Hk].
Qed.
Lemma gp5_nth_le : forall n z k d, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k d Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma gp5_le4 : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YO0f.le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4. rewrite gp5_nth_le by exact Hk.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.
Lemma gp5_le1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Hr. reflexivity.
Qed.
Lemma gp5_nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.
Lemma gp5_le_byte0 : forall n k, YO0f.le_byte 0 n k = 0.
Proof. intros n k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.

Section gp5.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* the cut's Section w context (lib/B/W_LLVMFuzzerTestOneInput_cut.v:392-409, the base's Section g) *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- the base's obligations this part reads (A's p5 set, by the base's B names) ---- *)
Hypothesis HGs : GN_HGs G_fr.
Hypothesis HGcells : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
Hypothesis HZS : GN_HZS B.
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis RIend : GN_RI_end B MT LS RINV.
(* the cut's two segment facts (lib/B/W_LLVMFuzzerTestOneInput_cut.v:412 / :414): G_fr's cells are writable in every
   memory, and errno is writable in every AR state (the callees' OWED conjunct gives errno's view only) *)
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ERRL : errno_law B.
(* errno's place (the base's GN_ERRNO_LOW): the transport kit's amodel lemma reads it across the F+112 spill *)
Hypothesis HERR : GN_ERRNO_LOW B.

(* ================================================================== model helpers *)
Lemma gp5_setn_length : forall k (x : option hsrc) l, length (gn_setn k x l) = length l.
Proof. induction k as [|k IH]; intros x [|y l]; cbn [gn_setn length]; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma gp5_setn_same : forall k (x : option hsrc) l, (k < length l)%nat -> nth k (gn_setn k x l) None = x.
Proof.
  induction k as [|k IH]; intros x [|y l] Hk; cbn [gn_setn length nth] in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.
Lemma gp5_setn_other : forall k j (x : option hsrc) l, j <> k -> nth j (gn_setn k x l) None = nth j l None.
Proof.
  induction k as [|k IH]; intros j x [|y l] Hjk; cbn [gn_setn]; try reflexivity.
  - destruct j as [|j]; [lia | reflexivity].
  - destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma gp5_setn_setn : forall k (x y : option hsrc) l, gn_setn k x (gn_setn k y l) = gn_setn k x l.
Proof. induction k as [|k IH]; intros x y [|z l]; cbn [gn_setn]; try reflexivity. rewrite IH. reflexivity. Qed.
(* the fields gn_run keeps *)
Definition gp5_same (m1 mc : lmod) : Prop :=
  lm_k mc = lm_k m1 /\ lm_G mc = lm_G m1 /\ lm_es mc = lm_es m1 /\ lm_c mc = lm_c m1 /\ lm_O mc = lm_O m1 /\
  lm_mx mc = lm_mx m1 /\ lm_cap mc = lm_cap m1 /\ lm_out mc = lm_out m1 /\ lm_gn mc = lm_gn m1 /\
  lm_nfd mc = lm_nfd m1 /\ length (lm_hs mc) = length (lm_hs m1).
Lemma gp5_run_same : forall P m1 mc A i k, gn_run P m1 mc A i k -> gp5_same m1 mc.
Proof.
  intros P m1 mc A i k H. induction H as [| mc A i k H IH | mc A i k h h' h'' E' H' ds c H IH | mc A i H IH].
  - repeat split; reflexivity.
  - exact IH.
  - destruct IH as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold gp5_same, gn_set. cbn [lm_k lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_hs].
    rewrite gp5_setn_length. repeat split; assumption.
  - exact IH.
Qed.

(* ================================================================== blocks *)
Lemma gp5_blk_FP : forall bs, blk_FP bs = ablocks_fp bs.
Proof. reflexivity. Qed.
(* the slots' blocks, with slot k taken out *)
Lemma gp5_slots_perm : forall hs k h, nth k hs None = Some h ->
  Permutation (concat (map slot_blks hs)) (asrc_blks h ++ concat (map slot_blks (gn_setn k None hs))).
Proof.
  induction hs as [|o hs IH]; intros k h Hk; [destruct k; discriminate Hk|].
  destruct k as [|k]; cbn [nth gn_setn map concat] in *.
  - subst o. cbn [slot_blks]. reflexivity.
  - rewrite (IH k h Hk). rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Definition gp5_mrest (mc : lmod) (k : nat) : list (Z * Z) :=
  (lm_G mc, ATABLE) :: concat (map aentry_blks (lm_es mc)) ++
  concat (map slot_blks (gn_setn k None (lm_hs mc))) ++ aout_blks (lm_cap mc) (lm_out mc).
Lemma gp5_model_perm : forall mc k h, nth k (lm_hs mc) None = Some h ->
  Permutation (model_blks mc) (asrc_blks h ++ gp5_mrest mc k).
Proof.
  intros mc k h Hk. unfold model_blks, gp5_mrest.
  rewrite (gp5_slots_perm (lm_hs mc) k h Hk).
  change ((lm_G mc, ATABLE) :: concat (map aentry_blks (lm_es mc)) ++
    (asrc_blks h ++ concat (map slot_blks (gn_setn k None (lm_hs mc)))) ++ aout_blks (lm_cap mc) (lm_out mc))
    with (((lm_G mc, ATABLE) :: concat (map aentry_blks (lm_es mc))) ++
    (asrc_blks h ++ concat (map slot_blks (gn_setn k None (lm_hs mc)))) ++ aout_blks (lm_cap mc) (lm_out mc)).
  change ((lm_G mc, ATABLE) :: concat (map aentry_blks (lm_es mc)) ++
    concat (map slot_blks (gn_setn k None (lm_hs mc))) ++ aout_blks (lm_cap mc) (lm_out mc))
    with (((lm_G mc, ATABLE) :: concat (map aentry_blks (lm_es mc))) ++
    concat (map slot_blks (gn_setn k None (lm_hs mc))) ++ aout_blks (lm_cap mc) (lm_out mc)).
  rewrite <- app_assoc.
  rewrite (app_assoc ((lm_G mc, ATABLE) :: concat (map aentry_blks (lm_es mc))) (asrc_blks h)).
  rewrite (Permutation_app_comm ((lm_G mc, ATABLE) :: concat (map aentry_blks (lm_es mc))) (asrc_blks h)).
  rewrite <- !app_assoc. reflexivity.
Qed.
Lemma gp5_model_set : forall mc k h', (k < length (lm_hs mc))%nat ->
  Permutation (model_blks (gn_set mc k h')) (asrc_blks h' ++ gp5_mrest mc k).
Proof.
  intros mc k h' Hk.
  assert (E : gp5_mrest mc k = gp5_mrest (gn_set mc k h') k).
  { unfold gp5_mrest, gn_set. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite gp5_setn_setn. reflexivity. }
  rewrite E. apply gp5_model_perm. unfold gn_set. cbn [lm_hs]. apply gp5_setn_same. exact Hk.
Qed.
(* a source's blocks: the two lists check_no_loss rebuilds, then the rest *)
Lemma gp5_asrc_perm : forall h,
  Permutation (asrc_blks h) (alist_blks (hs_expected h) ++ alist_blks (hs_held h) ++
    ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h))).
Proof.
  intros h. unfold asrc_blks.
  transitivity (((hs_partial h, APARTIAL) :: alist_blks (hs_pending h)) ++
    (alist_blks (hs_expected h) ++ alist_blks (hs_held h))); [reflexivity|].
  rewrite (app_assoc (alist_blks (hs_expected h))). apply Permutation_app_comm.
Qed.
Lemma gp5_asrc_exp_held : forall h E' H',
  asrc_blks (set_exp_held h E' H') = (hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks E' ++ alist_blks H'.
Proof. reflexivity. Qed.
Lemma gp5_asrc_held : forall h H',
  asrc_blks (set_held h H') = (hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks (hs_expected h) ++ alist_blks H'.
Proof. reflexivity. Qed.

(* ================================================================== the transport kit *)
Lemma gp5_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> seg_rom segs (Z_to_bv 64 a) = None.
Proof.
  intros a Ha Hni. unfold seg_rom, memory_read.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|reflexivity].
  exfalso. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi).
  rewrite unsigned_lit_small in Hlo, Hhi by lia. apply Hni. exists sg. split; [exact Hin | lia].
Qed.
Lemma gp5_wview_none : forall (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  m (Z_to_bv 64 a) = None -> wview segs m (Z_to_bv 64 a) = None.
Proof.
  intros m a Ha Hni Hm. unfold wview. rewrite Hm.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Ef; [|reflexivity].
  exfalso. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi).
  rewrite unsigned_lit_small in Hlo, Hhi by lia. apply Hni. exists sg. split; [exact Hin | lia].
Qed.
(* off the image a byte is writable exactly when a reader sees it *)
Lemma gp5_akept_noimg : forall (W W' : world segs) mem mem' a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Ha Hni Hv. split; [exact Hv|]. intros Hw. unfold arm, writable_at in *.
  destruct (mrestrict (w_H W') mem' (Z_to_bv 64 a)) as [b'|] eqn:E'.
  - unfold wview. rewrite E'. discriminate.
  - exfalso. destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|] eqn:E.
    + unfold aview, mbyte in Hv. rewrite E, E', (gp5_rom_none a Ha Hni) in Hv. discriminate Hv.
    + exact (Hw (gp5_wview_none _ a Ha Hni E)).
Qed.
(* a byte of G_fr: writable in every memory (glob_wr_law) *)
Lemma gp5_akept_G : forall (W W' : world segs) mem mem' a, inG G_fr a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof. intros W W' mem mem' a Hg Hv. split; [exact Hv|]. intros _. exact (GWL _ _ a Hg). Qed.
(* ---- what a callee's journal keeps (W_gestures_end.v's gse_keep_* kit, for this file) ---- *)
Section jk.
Variables (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z)).
Variables (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model) (own : list (Z * Z)).
Variables (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z).
Hypothesis HGx : gx_ok segs B G.
Hypothesis HJ : ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Lemma gp5_jk_high : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma gp5_jk_xo : forall a, sp0 <= a < sp0 + XO -> ~ inFP OUT a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct HJ as (_ & _ & _ & Hout). exact Hout. Qed.
Lemma gp5_jk_img : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> ~ inG G a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia).
  exact Hg.
Qed.
Lemma gp5_jk_blk : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros p n i H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP B ly' S' W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. red in Hoff. lia.
Qed.
Lemma gp5_jk_frm : forall cid pos a, AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros cid pos a HAR Hin Hr Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Hr Hf).
  pose proof (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof asan_consts as (C1 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (Ha : 0 <= a < 2 ^ 64).
  { unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)).
    assert (frame_addr ly cid pos / 8 <= frame_addr ly cid pos) by (apply Z.div_le_upper_bound; lia).
    assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
    destruct Hr; lia. }
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi' _]. pose proof (pa_img_range _ Hi') as HR.
  destruct Hr as [Hr|Hr].
  - exact (frm_img segs B LAWS ly S W mem md cid pos a HAR Hin Hr Hi').
  - unfold in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma gp5_jk_pres : forall a, sp0 + XO - (STK + XO) <= a < sp0 + XO -> apresent (w_H W') mem' a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & _) & _). intros a Ha.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. exact Ha.
Qed.
Lemma gp5_jk_AR : AR segs B ly' S' W' mem' md'.
Proof. eapply ajournal_gx_AR. exact HJ. Qed.
Lemma gp5_jk_faddr : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
  intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
(* B: the fake frame's flag word names the layout too (the cut's lcut clause, FF + 120) *)
Lemma gp5_jk_flag : forall cid pos, flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
  intros cid pos. unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
End jk.
(* ---- a live block: its bounds (W_LLVMFuzzerTestOneInput_latch.v lt_blk) and the blocks' distinctness
   (W_gesture_end.v ablocks_nodup) ---- *)
Lemma gp5_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma gp5_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma gp5_kp_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.
Lemma gp5_tr_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
Lemma gp5_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
(* ---- every byte a representation reads lies in one of its cells or one of its blocks ---- *)
Section cov.
Variable KEEP : Z -> Prop.
Definition gp5_bkeep (bl : list (Z * Z)) : Prop :=
  forall p n i, In (p, n) bl -> 0 <= i < req_size n -> KEEP (p + i).
Definition gp5_fkeep (fp : list (Z * Z)) : Prop := forall r, In r fp -> forall a, fst r <= a < snd r -> KEEP a.
Lemma gp5_bkeep_sub : forall bl bl', gp5_bkeep bl -> (forall b, In b bl' -> In b bl) -> gp5_bkeep bl'.
Proof. intros bl bl' H Hs p n i Hin Hi. exact (H p n i (Hs _ Hin) Hi). Qed.
Lemma gp5_brng : forall bl p n a, gp5_bkeep bl -> In (p, n) bl -> 0 <= n -> p <= a < p + n -> KEEP a.
Proof.
  intros bl p n a H Hin Hn Ha. pose proof (req_size_pos n Hn) as [_ Hr].
  replace a with (p + (a - p)) by lia. apply (H p n); [exact Hin | lia].
Qed.
Lemma gp5_alist_cov : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> KEEP a) -> gp5_bkeep (alist_blks l) ->
  gp5_fkeep (alist_fp LA l).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL HB r Hr a Ha.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [cbn in Ha; apply HL; lia|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
    destruct Hr as [<- | []]. destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    cbn [gfp fst snd] in Ha. rewrite gp5_bzs_len, length_app, gp5_tr_len in Ha. unfold hl_n in Hj.
    apply (gp5_brng (alist_blks l) (hl_v l) (AREC * hl_cap l)); [exact HB | | unfold AREC; lia | unfold AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. destruct (Z.eqb_spec (hl_cap l) 0); [lia | left; reflexivity].
  - apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha. rewrite gp5_bzs_len, length_app in Ha.
    cbn [length] in Ha.
    apply (gp5_brng (alist_blks l) (fst x) (Z.of_nat (length (snd x)) + 1)); [exact HB | | lia | lia].
    unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx.
Qed.
Lemma gp5_asrc_cov : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> (forall a, HA <= a < HA + ASRC -> KEEP a) -> gp5_bkeep (asrc_blks h) ->
  gp5_fkeep (asrc_fp HA h).
Proof.
  intros ly S W mem HA h HS HL HB.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  - apply HL. cbn in Ha. lia.
  - cbn [gfp fst snd] in Ha. rewrite gp5_bzs_len, Hpj in Ha.
    apply (gp5_brng (asrc_blks h) (hs_partial h) APARTIAL); [exact HB | left; reflexivity | unfold APARTIAL; lia | lia].
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + refine (gp5_alist_cov ly S W mem (HA + 16) _ _ Hpend _ _ r Hr a Ha);
        [intros x Hx; apply HL; unfold ASRC; lia |].
      apply (gp5_bkeep_sub _ _ HB). intros b Hb. right. apply in_or_app. left. exact Hb.
    + refine (gp5_alist_cov ly S W mem (HA + 64) _ _ Hexp _ _ r Hr a Ha);
        [intros x Hx; apply HL; unfold ASRC; lia |].
      apply (gp5_bkeep_sub _ _ HB). intros b Hb. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + refine (gp5_alist_cov ly S W mem (HA + 80) _ _ Hheld _ _ r Hr a Ha);
        [intros x Hx; apply HL; unfold ASRC; lia |].
      apply (gp5_bkeep_sub _ _ HB). intros b Hb. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma gp5_aentry_cov : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> gp5_bkeep (aentry_blks e) -> gp5_fkeep (aentry_fp e).
Proof.
  intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) HB r Hr a Ha.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
    cbn [gfp fst snd] in Ha. rewrite gp5_bzs_len, length_app in Ha.
    apply (gp5_brng (aentry_blks e) (re_buf e) (re_cap e)); [exact HB | | lia | lia].
    unfold aentry_blks. apply in_or_app. left. destruct (Z.eqb_spec (re_cap e) 0); [lia | left; reflexivity].
  - destruct Hr as [<- | Hr].
    + cbn [gfp fst snd] in Ha. rewrite gp5_bzs_len, gp5_kp_len in Ha.
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * rewrite Hks in Ha. cbn [length] in Ha. lia.
      * unfold re_nheld in Hk1.
        apply (gp5_brng (aentry_blks e) (re_hp e) (re_kh e)); [exact HB | | lia | lia].
        unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
        destruct (Z.eqb_spec (re_hp e) 0); [lia | left; reflexivity].
    + apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha. rewrite gp5_bzs_len, length_app in Ha.
      cbn [length] in Ha.
      apply (gp5_brng (aentry_blks e) (gestures_end_b_c.key_addr x)
        (Z.of_nat (length (gestures_end_b_c.key_text x)) + 1)); [exact HB | | lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (gestures_end_b_c.key_addr k, Z.of_nat (length (gestures_end_b_c.key_text k)) + 1))).
      exact Hx.
Qed.
Lemma gp5_arelay_cov : forall RG ly S (W : world segs) mem G es,
  arelay_at B RG ly S W mem G es ->
  (forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 ->
     KEEP a) ->
  gp5_bkeep (arelay_blks G es) -> gp5_fkeep (arelay_fp RG G es).
Proof.
  intros RG ly S W mem G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HC HB r Hr a Ha.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
  - apply HC. lia.
  - apply HC. lia.
  - apply HC. lia.
  - apply (gp5_brng (arelay_blks G es) G ATABLE); [exact HB | left; reflexivity | unfold ATABLE; lia | lia].
  - apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
    rewrite Forall_forall in R10.
    refine (gp5_aentry_cov ly S W mem e (R10 e He) _ r Hr a Ha).
    apply (gp5_bkeep_sub _ _ HB). intros b Hb. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map; exact He | exact Hb].
Qed.
Lemma gp5_aout_cov : forall RG ly S (W : world segs) mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out ->
  (forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> KEEP a) ->
  gp5_bkeep (aout_blks cap out) -> gp5_fkeep (aout_fp B RG cap out).
Proof.
  intros RG ly S W mem c O mx no cap out HO HC HB r Hr a Ha.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp in Hr.
  do 9 (destruct Hr as [<- | Hr];
    [refine (HC _ a _ Ha); unfold aout_fp; cbn [In]; repeat (first [left; reflexivity | right]) |]).
  destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  apply (gp5_brng (aout_blks cap out) out cap); [exact HB | | lia | lia].
  unfold aout_blks. destruct (Z.eqb_spec cap 0); [lia | left; reflexivity].
Qed.
End cov.
(* ---- the ROM's ranges G_fr's cells avoid (W_LLVMFuzzerTestOneInput_G.v rom_apart, copied) ---- *)
Definition gp5_rom_apart (G : list (Z * Z)) : bool :=
  forallb (fun sg => seg_writable sg || forallb (fun r =>
    (fst r + snd r <=? Z.of_N (seg_base sg)) || (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) G) segs.
Lemma gp5_rom_apart_ok : forall G a, gp5_rom_apart G = true -> in_rom segs a -> ~ inG G a.
Proof.
  intros G a H (sg & Hs & Hw & Hr) Ha. unfold gp5_rom_apart in H. rewrite forallb_forall in H.
  specialize (H sg Hs). rewrite Hw in H. cbn [orb] in H. rewrite forallb_forall in H.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr' & Hz). specialize (H r Hr').
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; unfold in_zr in Hz; lia.
Qed.
Lemma gp5_rom_gs : forall a, in_rom segs a -> ~ (rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC).
Proof.
  intros a Hr Ha. apply (gp5_rom_apart_ok [(rg_s fr_RG, 4 * ASRC)] a); [vm_compute; reflexivity | exact Hr |].
  apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
Definition gp5_inromb (a : Z) : bool :=
  existsb (fun sg => (negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                      (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) segs.
Lemma gp5_inromb_ok : forall a, gp5_inromb a = true -> in_rom segs a.
Proof.
  intros a H. unfold gp5_inromb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Lemma gp5_jt_in_rom : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof.
  intros a Ha. apply gp5_inromb_ok.
  assert (K : forallb (fun i => gp5_inromb (fr_jtab + Z.of_nat i)) (seq 0 36) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. replace a with (fr_jtab + Z.of_nat (Z.to_nat (a - fr_jtab))) by lia.
  apply K. apply in_seq. lia.
Qed.
(* ================================================================== across one call
   The callee's journal is at gn_Gs k (slot k's two list headers), footprint blk_FP fpb (blocks of slot k's
   expected and held lists), window [F - STK1, F + 224) with the out cell `at` = [F + 208, F + 216).  Every
   fact of the loop's state outside slot k and `at` survives it; the outer journal absorbs it. *)
Lemma gp5_nodup_app : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1. induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
  inversion Hnd as [|y0 l0 Hni Hnd']; subst. destruct H1 as [<- | H1].
  - apply Hni. apply in_or_app. right. exact H2.
  - exact (IH l2 x Hnd' H1 H2).
Qed.
Definition gp5_SLOT (k : nat) : Z := rg_s fr_RG + ASRC * Z.of_nat k.
Lemma gp5_cell : forall lo n a, In (lo, n) gn_cells -> lo <= a < lo + n -> inG gn_cells a.
Proof. intros lo n a Hin Ha. unfold inG. apply Exists_exists. exists (lo, n). split; [exact Hin | unfold in_zr; cbn; lia]. Qed.
Ltac gp5_num := unfold gp5_SLOT, ASRC, AG_NFD, AG_THREAD_UP, AG_LISTEN, fr_RG, fr_globals_b in *;
  cbn [rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr rg_send_dead rg_gone
       rg_client rg_client_broken rg_lock rg_wake Z.of_nat] in *; lia.
Ltac gp5_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).
Lemma gp5_slot_in_mrest : forall mc k j h b, j <> k -> (j < length (lm_hs mc))%nat ->
  nth j (lm_hs mc) None = Some h -> In b (asrc_blks h) -> In b (gp5_mrest mc k).
Proof.
  intros mc k j h b Hjk Hj Hh Hb. unfold gp5_mrest. right. apply in_or_app. right. apply in_or_app. left.
  apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
  apply in_map. rewrite <- Hh. rewrite <- (gp5_setn_other k j None (lm_hs mc) Hjk).
  apply nth_In. rewrite gp5_setn_length. exact Hj.
Qed.
Lemma gp5_inG_Gs : forall k a, (k < 4)%nat -> inG (gn_Gs k) a -> gp5_SLOT k + 64 <= a < gp5_SLOT k + 96.
Proof.
  intros k a Hk H. unfold gn_Gs in H. apply inG_cons in H as [H|H]; [|exfalso; exact (inG_nil a H)].
  unfold in_zr, gp5_SLOT in *. cbn [fst snd] in H. lia.
Qed.
Lemma gp5_gx_Gs : forall k, (k < 4)%nat -> gx_ok segs B (gn_Gs k).
Proof.
  intros k Hk. apply (gx_ok_sub segs B (gn_Gs k) G_fr); [|exact HG].
  intros a Ha. apply HGs. pose proof (gp5_inG_Gs k a Hk Ha) as R. unfold gp5_SLOT, ASRC in *. lia.
Qed.
(* the auipc value 0x84b78 spills to F+112 (g_nsrc - 424) *)
Definition gp5_HI79 : Z := 0x5d8b78.
Definition gp5_xp (cx : lfcx) (t : Z) (m mc : lmod) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) (k : nat) : Prop :=
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx fake_shadow_open (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 16) (c_p cx + gn_kq cx m) /\ sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m) /\
  sv8 W mem (lf_F cx + 88) t /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79 /\
  (forall j, (j < 4)%nat -> j <> k -> aslot B ly S W mem j (nth j (lm_hs mc) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G mc) (lm_es mc) /\
  aout_at B fr_RG ly S W mem (lm_c mc) (lm_O mc) (lm_mx mc) (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc) /\
  agone_at fr_RG W mem (lm_gn mc) /\ alock_at fr_RG W mem false /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd mc) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd mc <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.


Lemma gp5_xport : forall cx t m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  gst B G_fr fr_FP cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk ->
  awr W mem (lf_F cx + 192) 16 -> gn_prefix_at cx m W mem (frame_addr ly 1 fpos) ->
  sv8 W mem (lf_F cx + 24) HI_G_NOUT -> sv8 W mem (lf_F cx + 112) gp5_HI79 ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some hk ->
  (forall b, In b fpb -> In b (alist_blks (hs_expected hk) ++ alist_blks (hs_held hk))) ->
  ajournal_gx segs B (gn_Gs k) 224 [(lf_F cx + 208, lf_F cx + 216)] STK1 (lf_F cx) (blk_FP fpb)
    ly S W mem md [] ly' S' W' mem' md' kk1 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  (* the callees' OWED conjunct: errno's view; its writability is ERRL's at the callee's AR state *)
  (forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)) ->
  (forall b, In b (ablocks B ly S) -> ~ In b fpb -> In b (ablocks B ly' S')) ->
  gp5_xp cx t m mc fpos ly' S' W' mem' md' (kk + kk1) k.
Proof.
  intros cx t m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1 HB
    ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP) HAW HPF H24 H112 Hk Hhk Hfpb HJc HS0 HS1
    HEv Hsurv.
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_jk_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR'.
  pose proof (gp5_gx_Gs k Hk) as HGk.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HE : forall i, 0 <= i < 4 -> abyte_kept W mem W' mem' (as_errno B + i)).
  { intros i Hi. split; [exact (HEv i Hi)|]. intros _.
    destruct (ERRL ly' S' W' mem' md' HAR') as (_ & Hw). exact (Hw i Hi). }
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (EFF : frame_addr ly' 1 fpos = FF) by exact (gp5_jk_faddr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  assert (EFL : flag_addr ly' 1 fpos = flag_addr ly 1 fpos)
    by exact (gp5_jk_flag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  unfold gp5_xp. rewrite EFF, EFL.
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  (* ---- the blocks: slot k's, the rest of the model's, the input's ---- *)
  destruct HSEP as ((rest0 & HPM) & HSEP2).
  pose proof (gp5_nodup ly S W mem md HAR) as HND.
  pose proof (gp5_model_perm mc k hk Hhk) as HMP.
  assert (HND2 : List.NoDup (input_blks cx ++ (asrc_blks hk ++ gp5_mrest mc k) ++ rest0)).
  { eapply Permutation_NoDup; [|exact HND].
    exact (Permutation_trans HPM (Permutation_app_head _ (Permutation_app_tail _ HMP))). }
  assert (HINab : forall b, In b (input_blks cx ++ (asrc_blks hk ++ gp5_mrest mc k) ++ rest0) -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in b (Permutation_sym (Permutation_trans HPM
      (Permutation_app_head _ (Permutation_app_tail _ HMP))))). exact Hb. }
  assert (F1 : forall b, In b (asrc_blks hk) -> In b (ablocks B ly S)).
  { intros b Hb. apply HINab. apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact Hb. }
  assert (F2 : forall b, In b (gp5_mrest mc k) -> In b (ablocks B ly S) /\ ~ In b (asrc_blks hk)).
  { intros b Hb. split.
    - apply HINab. apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact Hb.
    - intros Hb2. apply List.NoDup_app_remove_l in HND2. apply List.NoDup_app_remove_r in HND2.
      exact (gp5_nodup_app _ _ _ b HND2 Hb2 Hb). }
  assert (F3 : forall b, In b (input_blks cx) -> In b (ablocks B ly S) /\ ~ In b (asrc_blks hk)).
  { intros b Hb. split; [apply HINab; apply in_or_app; left; exact Hb|].
    intros Hb2. apply (gp5_nodup_app _ _ _ b HND2 Hb). apply in_or_app. left. apply in_or_app. left. exact Hb2. }
  assert (Hfpk : forall b, In b fpb -> In b (asrc_blks hk)).
  { intros b Hb. apply (Permutation_in b (Permutation_sym (gp5_asrc_perm hk))). rewrite app_assoc.
    apply in_or_app. left. exact (Hfpb b Hb). }
  assert (Hfp4 : Forall (fun b => 0 < fst b) fpb).
  { apply Forall_forall. intros [p n] Hb. destruct (gp5_blk ly S W mem md p n HAR (F1 _ (Hfpk _ Hb))) as (P1 & _).
    cbn [fst]. lia. }
  assert (Hspare : forall a, fp_spares (blk_FP fpb) a).
  { intros a Ho. exfalso. apply (sink_closed_ablocks_fp fpb Hfp4). rewrite <- gp5_blk_FP. exact Ho. }
  assert (Hinfp : forall a, inFP (blk_FP fpb) a -> exists p n, In (p, n) fpb /\ p <= a < p + req_size n).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    exists p, n. cbn [fst snd] in Hra. split; [exact Hb | exact Hra]. }
  (* ---- the kept bytes ---- *)
  assert (KC : forall a, inG gn_cells a -> ~ (gp5_SLOT k <= a < gp5_SLOT k + ASRC) -> abyte_kept W mem W' mem' a).
  { intros a Ha Hns. pose proof (HGcells a Ha) as HGa. destruct (HG a HGa) as (Him & Hown & _).
    destruct (Z_le_dec (as_errno B) a) as [He1|He1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [He2|He2]|].
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia.
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia. }
  assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (asrc_blks hk) -> 0 <= i < req_size n ->
      abyte_kept W mem W' mem' (p + i)).
  { intros p n i Hin Hnk Hi.
    assert (Hnf : ~ In (p, n) fpb) by (intros Hf; exact (Hnk (Hfpk _ Hf))).
    destruct (gp5_blk ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    apply gp5_akept_noimg; [lia | exact (blk_img segs B LAWS ly S W mem md p n (p + i) HAR Hin ltac:(lia)) |].
    apply (gp5_jk_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc p n i Hin (Hsurv _ Hin Hnf) Hi).
    intros Hf. destruct (Hinfp _ Hf) as (p' & n' & Hb' & Hr').
    assert (Hne : (p, n) <> (p', n')) by (intros E; rewrite E in Hnf; exact (Hnf Hb')).
    pose proof (sep_blocks segs B LAWS ly S W mem md p n p' n' HAR Hin (F1 _ (Hfpk _ Hb')) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KF : forall a, FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hd8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    apply gp5_akept_noimg; [exact Ha64 | |].
    - destruct Ha as [Ha | Ha].
      + exact (frm_img segs B LAWS ly S W mem md 1 fpos a HAR Hfin Ha).
      + intros Hi. pose proof (pa_img_range a Hi). unfold SB in Ha. lia.
    - apply (gp5_jk_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc 1 fpos a HAR Hfin).
      + unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
        change (128 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia.
      + intros Hf. destruct (Hinfp _ Hf) as (p' & n' & Hb' & Hr').
        pose proof (F1 _ (Hfpk _ Hb')) as Hb'2.
        destruct Ha as [Ha | Ha].
        * pose proof (sep_block_frame segs B LAWS ly S W mem md p' n' 1 fpos HAR Hb'2 Hfin) as Hd.
          unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold FF in Hd. lia.
        * destruct (al_blocks _ _ LAWS ly S W mem md p' n' HAR Hb'2) as (_ & _ & _ & Happ & _).
          unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. }
  assert (KH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (F - STK1 <= a < F) -> ~ (F + 208 <= a < F + 216) ->
      abyte_kept W mem W' mem' a).
  { intros a Ha H1 H2. apply gp5_akept_noimg; [lia | intros Hi; pose proof (pa_img_range a Hi); lia |].
    destruct (Z_lt_le_dec a F) as [H0|H0];
      [apply (gp5_jk_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha); lia|].
    destruct (Z_lt_le_dec a (F + 224)) as [H3|H3].
    - apply (gp5_jk_xo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a ltac:(lia)).
      intros Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil a Hf)].
    - apply (gp5_jk_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha). lia. }
  assert (KP : forall a, F - STK1 <= a < F + 224 -> apresent (w_H W') mem' a).
  { intros a Ha. apply (gp5_jk_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a). lia. }
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r)); [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view segs B ly' S' W' mem' md' a HAR' Hp), (rom_pinned_view segs B ly S W mem md a HAR Hp).
      reflexivity.
    - destruct (Z_le_dec (as_errno B) a) as [He1|He1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [He2|He2]|].
      + replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
      + apply (gp5_jk_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
        intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). apply (gp5_rom_gs a Ha). unfold gp5_SLOT, ASRC in *. lia.
      + apply (gp5_jk_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
        intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). apply (gp5_rom_gs a Ha). unfold gp5_SLOT, ASRC in *. lia. }
  assert (KSV : forall a v, F <= a -> a + 8 <= F + 208 \/ F + 216 <= a -> a + 8 <= sp0 -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H1 H2 H3 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. cbn in Hx. apply KH; lia. }
  assert (Hlen : c_n cx = Z.of_nat (length (c_pl cx))).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf in HPRE. tauto. }
  assert (HSEPx : ablocks_sep B fr_FP cx mc ly S) by (split; [exists rest0; exact HPM | exact HSEP2]).
  assert (HMR : forall b, In b (gp5_mrest mc k) -> In b (ablocks B ly' S')).
  { intros b Hb. destruct (F2 b Hb) as [Hab Hnk]. apply Hsurv; [exact Hab | intros Hf; exact (Hnk (Hfpk _ Hf))]. }
  assert (KM : forall p n i, In (p, n) (gp5_mrest mc k) -> 0 <= i < req_size n -> abyte_kept W mem W' mem' (p + i)).
  { intros p n i Hb Hi. destruct (F2 _ Hb) as [Hab Hnk]. exact (KB p n i Hab Hnk Hi). }
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  (* ---- the journal from the entry ---- *)
  split.
  { assert (HJc' : ajournal_gx segs B G_fr 224 [(F + 208, F + 216)] STK1 F (blk_FP fpb) ly S W mem md [] ly' S' W' mem' md' kk1).
    { apply (ajournal_gx_G_mono segs B (gn_Gs k) G_fr); [|exact HJc].
      intros a Ha. apply HGs. pose proof (gp5_inG_Gs k a Hk Ha). unfold gp5_SLOT, ASRC in *. lia. }
    refine (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk
      STK1 F 224 [(F + 208, F + 216)] (blk_FP fpb) [] ly' S' W' mem' md' kk1 HJ HJc' _ _ _ _ HG _).
    - unfold LLVMF_STK in *. lia.
    - lia.
    - lia.
    - intros a Ha. apply inFP_cons in Ha as [Ha|Ha]; [left; unfold LLVMF_STK in *; lia | exfalso; exact (inFP_nil a Ha)].
    - intros a Ha. destruct (Hinfp a Ha) as (p & n & Hb & Hr). pose proof (Hfpk _ Hb) as Hbk.
      assert (Hbm : In (p, n) (model_blks mc)).
      { apply (Permutation_in _ (Permutation_sym HMP)). apply in_or_app. left. exact Hbk. }
      destruct (gn_sep_req B fr_FP cx mc ly S HSEPx (p, n) Hbm) as [Hne | Hfp].
      + right. exists p, n. split; [exact (F1 _ Hbk)|]. split; [exact Hne | exact Hr].
      + left. split; [exact (Hfp a Hr) | exists p, n; split; [exact (F1 _ Hbk) | exact Hr]]. }
  (* ---- the frame and the fake frame ---- *)
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22).
    split.
    { intros o r Hin. assert (Ho : 8 <= o <= 104).
      { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
      apply KSV; [lia | lia | lia | exact (G1 o r Hin)]. }
    split.
    { intros i Hi. destruct (Z_lt_le_dec (F + i) (F + 208)) as [Q1|Q1];
        [|destruct (Z_lt_le_dec (F + i) (F + 216)) as [Q2|Q2]].
      - apply (proj2 (KH (F + i) ltac:(lia) ltac:(lia) ltac:(lia))). exact (G2 i Hi).
      - apply (apresent_writable segs). apply KP. lia.
      - apply (proj2 (KH (F + i) ltac:(lia) ltac:(lia) ltac:(lia))). exact (G2 i Hi). }
    do 14 (split; [apply KSV; [lia | lia | lia | assumption]|]).
    do 3 (split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | assumption]|]).
    split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G20]|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KF; unfold fake_shadow_open in Hx; cbn [length] in Hx; lia
                                        | exact G21]|].
    apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G22]. }
  (* the fake frame's flag word, the cursor slots, t *)
  split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | exact HFL]|].
  split; [apply KSV; [lia | lia | lia | exact H16]|].
  split; [apply KSV; [lia | lia | lia | exact H144]|].
  split; [apply KSV; [lia | lia | lia | exact H88]|].
  (* ---- the input ---- *)
  split.
  { destruct HIN as (I1 & I2). split.
    { destruct I1 as [I1 | (Hn & Hin)]; [left; exact I1 | right; split; [exact Hn|]].
      assert (Hib : In (c_p cx, c_n cx) (input_blks cx)).
      { unfold input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]. }
      destruct (F3 _ Hib) as [_ Hnk]. apply Hsurv; [exact Hin | intros Hf; exact (Hnk (Hfpk _ Hf))]. }
    apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map in Hx. rewrite <- Hlen in Hx.
    destruct I1 as [(Hn0 & Hp) | (Hn & Hin)]; [lia|].
    assert (Hib : In (c_p cx, c_n cx) (input_blks cx)).
    { unfold input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]. }
    destruct (F3 _ Hib) as [_ Hnk]. pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hr].
    replace x with (c_p cx + (x - c_p cx)) by lia. apply (KB _ _ _ Hin Hnk). lia. }
  (* ---- the read-only image and the jump table ---- *)
  split; [intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)|].
  split.
  { intros i Hi. apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact (HJT i Hi)].
    intros j Hj. apply ROMK. apply gp5_jt_in_rom. cbn in Hj. lia. }
  (* ---- reads[], the prefix ---- *)
  split; [intros i Hi; apply (proj2 (KH (F + 192 + i) ltac:(lia) ltac:(lia) ltac:(lia))); exact (HAW i Hi)|].
  split.
  { destruct HPF as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KF (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KF (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KF a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* ---- HI_G_NOUT at F+24, the auipc spill at F+112 ---- *)
  split; [apply KSV; [lia | lia | lia | exact H24]|].
  split; [apply KSV; [lia | lia | lia | exact H112]|].
  (* ---- the model, but slot k ---- *)
  assert (Hjk2 : forall j a, (j < 4)%nat -> j <> k -> gp5_SLOT j <= a < gp5_SLOT j + ASRC ->
      ~ (gp5_SLOT k <= a < gp5_SLOT k + ASRC)).
  { intros j a Hj Hjk Ha Hb. unfold gp5_SLOT, ASRC in *. assert (Z.of_nat j <> Z.of_nat k) by lia. lia. }
  split.
  { intros j Hj Hjk. pose proof (M2 j Hj) as Hs. unfold aslot in *.
    assert (Hjl : (j < length (lm_hs mc))%nat) by (rewrite M1; exact Hj).
    destruct (nth j (lm_hs mc) None) as [h|] eqn:Ej.
    - apply (asrc_at_kept B ly S W mem ly' S' W' mem' (rg_s fr_RG + ASRC * Z.of_nat j) h Hs).
      + apply (gp5_asrc_cov (abyte_kept W mem W' mem') ly S W mem _ h Hs).
        * intros a Ha. apply KC; [apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold ASRC in *; lia]|].
          apply (Hjk2 j a Hj Hjk). unfold gp5_SLOT. lia.
        * intros p n i Hpn Hi. exact (KM p n i (gp5_slot_in_mrest mc k j h _ Hjk Hjl Ej Hpn) Hi).
      + intros b Hb. exact (HMR b (gp5_slot_in_mrest mc k j h _ Hjk Hjl Ej Hb)).
    - destruct Hs as [Q1 Q2].
      assert (KJ : forall x, rg_s fr_RG + ASRC * Z.of_nat j <= x < rg_s fr_RG + ASRC * Z.of_nat j + ASRC ->
          abyte_kept W mem W' mem' x).
      { intros x Hx. apply KC; [apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold ASRC in *; lia]|].
        apply (Hjk2 j x Hj Hjk). unfold gp5_SLOT. lia. }
      split; [apply (akept_garr8 W mem); [|exact Q1] | apply (akept_awr W mem); [|exact Q2]].
      + intros x Hx. rewrite repeat_length in Hx. apply KJ. unfold ASRC in *. lia.
      + exact KJ. }
  (* ---- the relay's table ---- *)
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly' S' W' mem' (lm_G mc) (lm_es mc) M3).
    - apply (gp5_arelay_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ M3).
      + intros a Ha. apply KC.
        * destruct Ha as [Ha | [Ha | Ha]]; refine (gp5_cell _ _ a _ Ha); gp5_inl.
        * clear - Hk Ha. gp5_num.
      + intros p n i Hb Hi. apply (KM p n i); [|exact Hi]. unfold gp5_mrest. unfold arelay_blks in Hb.
        destruct Hb as [E | Hb]; [left; exact E | right; apply in_or_app; left; exact Hb].
    - intros b Hb. apply HMR. unfold gp5_mrest. unfold arelay_blks in Hb.
      destruct Hb as [E | Hb]; [left; exact E | right; apply in_or_app; left; exact Hb]. }
  (* ---- the controller's stream ---- *)
  split.
  { apply (aout_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ _ _ _ _ M4).
    - apply (gp5_aout_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ _ _ _ _ M4).
      + intros r a Hr Ha. unfold aout_fp in Hr. cbn [Z.eqb] in Hr.
        do 8 (destruct Hr as [<- | Hr];
          [cbn [fst snd] in Ha; apply KC; [refine (gp5_cell _ _ a _ Ha); gp5_inl | clear - Hk Ha; gp5_num] |]).
        destruct Hr as [<- | []]. cbn [fst snd] in Ha. replace a with (as_errno B + (a - as_errno B)) by lia.
        apply HE. lia.
      + intros p n i Hb Hi. apply (KM p n i); [|exact Hi]. unfold gp5_mrest. right. apply in_or_app. right.
        apply in_or_app. right. exact Hb.
    - intros b Hb. apply HMR. unfold gp5_mrest. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  (* ---- g_gone, g_lock, g_wake[1], g_nfd, g_thread_up, g_listen ---- *)
  destruct M5 as (M5a & M5b & M5c). destruct M6 as (M6a & M6b & M6c & M6d).
  split.
  { split; [|split; [|exact M5c]].
    - apply (akept_vm W mem); [|exact M5a]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_gone fr_RG) 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_awr W mem); [|exact M5b]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_gone fr_RG) 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { split; [|split; [|split]].
    - apply (akept_vm W mem); [|exact M6a]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_vm W mem); [|exact M6b]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_vm W mem); [|exact M6c]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_awr W mem); [|exact M6d]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_vm W mem); [|exact M7]. intros x Hx. apply KC;
      [apply (gp5_cell (rg_wake fr_RG + 4) 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KC;
      [apply (gp5_cell AG_NFD 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KC;
      [apply (gp5_cell AG_NFD 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KC;
      [apply (gp5_cell AG_THREAD_UP 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KC;
      [apply (gp5_cell AG_LISTEN 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KC;
    [apply (gp5_cell AG_LISTEN 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
Qed.
(* ================================================================== the model after a call on slot k *)
Lemma gp5_perm5 : forall (A : Type) (a b c d e : list A),
  Permutation (a ++ ((b ++ c) ++ d) ++ e) (b ++ (a ++ c ++ d ++ e)).
Proof. intros A a b c d e. rewrite <- !app_assoc. apply Permutation_app_swap_app. Qed.
(* the live blocks, with the blocks a call on slot k replaces split off *)
Lemma gp5_split : forall cx mc k hk ly S (oldb R : list (Z * Z)),
  ablocks_sep B fr_FP cx mc ly S -> nth k (lm_hs mc) None = Some hk ->
  Permutation (asrc_blks hk) (oldb ++ R) ->
  exists rest0, Permutation (ablocks B ly S) (oldb ++ (input_blks cx ++ R ++ gp5_mrest mc k ++ rest0)) /\
    Permutation (ablocks B ly S) (input_blks cx ++ model_blks mc ++ rest0).
Proof.
  intros cx mc k hk ly S oldb R ((rest0 & HPM) & _) Hk HA. exists rest0. split; [|exact HPM].
  eapply Permutation_trans; [exact HPM|].
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact (gp5_model_perm mc k hk Hk)|].
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; apply Permutation_app_tail; exact HA|].
  apply gp5_perm5.
Qed.
Lemma gp5_surv : forall ly S ly' S' (oldb newb X : list (Z * Z)) b,
  Permutation (ablocks B ly S) (oldb ++ X) -> Permutation (ablocks B ly' S') (newb ++ X) ->
  In b (ablocks B ly S) -> ~ In b oldb -> In b (ablocks B ly' S').
Proof.
  intros ly S ly' S' oldb newb X b H1 H2 Hb Hno.
  apply (Permutation_in b (Permutation_sym H2)). apply in_or_app. right.
  pose proof (Permutation_in b H1 Hb) as Hb2. apply in_app_or in Hb2 as [Hb2|Hb2]; [exfalso; exact (Hno Hb2) | exact Hb2].
Qed.
Lemma gp5_sep_step : forall cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' (oldb newb R : list (Z * Z)),
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk ->
  AR segs B ly' S' W' mem' md' ->
  ablocks_sep B fr_FP cx mc ly S ->
  (k < length (lm_hs mc))%nat -> nth k (lm_hs mc) None = Some hk ->
  Permutation (asrc_blks hk) (oldb ++ R) -> Permutation (asrc_blks h') (newb ++ R) ->
  (forall rest, Permutation (ablocks B ly S) (oldb ++ rest) -> Permutation (ablocks B ly' S') (newb ++ rest)) ->
  ablocks_sep B fr_FP cx (gn_set mc k h') ly' S'.
Proof.
  intros cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' oldb newb R HJ HAR' HSEP Hkl Hk HA HA' HPOST.
  destruct (gp5_split cx mc k hk ly S oldb R HSEP Hk HA) as (rest0 & P1 & _).
  pose proof (HPOST _ P1) as P2.
  pose proof (gp5_nodup ly' S' W' mem' md' HAR') as HND'.
  destruct HSEP as (_ & HC2).
  split.
  - exists rest0. eapply Permutation_trans; [exact P2|].
    eapply Permutation_trans; [apply Permutation_sym; apply gp5_perm5|].
    apply Permutation_app_head. apply Permutation_app_tail.
    eapply Permutation_trans; [|apply Permutation_sym; exact (gp5_model_set mc k h' Hkl)].
    apply Permutation_app_tail. apply Permutation_sym. exact HA'.
  - intros b Hb.
    (* B's ablocks_sep states its second clause over the block's request size (the cut, :409-416) *)
    assert (Hold : In b (model_blks mc) ->
      ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
      (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) by exact (HC2 b).
    assert (HinA : forall x, In x (asrc_blks hk) -> In x (model_blks mc)).
    { intros x Hx. apply (Permutation_in x (Permutation_sym (gp5_model_perm mc k hk Hk))). apply in_or_app. left. exact Hx. }
    pose proof (Permutation_in b (gp5_model_set mc k h' Hkl) Hb) as Hb2.
    apply in_app_or in Hb2 as [Hb2 | Hb2].
    + pose proof (Permutation_in b HA' Hb2) as Hb3. apply in_app_or in Hb3 as [Hb3 | Hb3].
      * destruct (List.in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B ly S))
          as [Hin|Hnin].
        { apply Hold. apply HinA. apply (Permutation_in b (Permutation_sym HA)). apply in_or_app. left.
          pose proof (Permutation_in b P1 Hin) as Hb4. apply in_app_or in Hb4 as [Hb4|Hb4]; [exact Hb4|].
          exfalso. apply (gp5_nodup_app _ newb (input_blks cx ++ R ++ gp5_mrest mc k ++ rest0) b);
            [exact (Permutation_NoDup P2 HND') | exact Hb3 | exact Hb4]. }
        destruct (List.in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B (c_ly cx) (c_S cx)))
          as [Hen|Hnen]; [right | left; exact Hnen].
        destruct b as [p n]. cbn [fst snd]. intros a Ha.
        assert (Hb5 : In (p, n) (ablocks B ly' S')).
        { apply (Permutation_in _ (Permutation_sym P2)). apply in_or_app. left. exact Hb3. }
        destruct (gp5_blk ly' S' W' mem' md' p n HAR' Hb5) as (_ & _ & Hn & Hrq).
        destruct HJ as (_ & _ & (memS & HJi & _) & _).
        pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
        replace a with (p + (a - p)) by lia. apply (Hgone p n (a - p) Hen Hnin). lia.
      * apply Hold. apply HinA. apply (Permutation_in b (Permutation_sym HA)). apply in_or_app. right. exact Hb3.
    + apply Hold. apply (Permutation_in b (Permutation_sym (gp5_model_perm mc k hk Hk))). apply in_or_app. right. exact Hb2.
Qed.
(* gp5_sep_step's block relation, kept against the operation's LS state: a call on slot k whose post relates the
   replaced blocks oldb to newb over any rest carries gn_tie from (ly, S) at mc to (ly', S') at gn_set mc k h' *)
Lemma gp5_tie_step : forall cx m ly0 S0 mc k hk h' ly S ly' S' (oldb newb R : list (Z * Z)),
  gn_tie B cx m ly0 S0 mc ly S ->
  (k < length (lm_hs mc))%nat -> nth k (lm_hs mc) None = Some hk ->
  Permutation (asrc_blks hk) (oldb ++ R) -> Permutation (asrc_blks h') (newb ++ R) ->
  (forall rest, Permutation (ablocks B ly S) (oldb ++ rest) -> Permutation (ablocks B ly' S') (newb ++ rest)) ->
  gn_tie B cx m ly0 S0 (gn_set mc k h') ly' S'.
Proof.
  intros cx m ly0 S0 mc k hk h' ly S ly' S' oldb newb R (HT0 & HT) Hkl Hk HA HA' HPOST.
  split; [exact HT0|]. intros rest Hr.
  pose proof (HT rest Hr) as HPM.
  assert (P1 : Permutation (ablocks B ly S) (oldb ++ (input_blks cx ++ R ++ gp5_mrest mc k ++ rest))).
  { eapply Permutation_trans; [exact HPM|].
    eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact (gp5_model_perm mc k hk Hk)|].
    eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; apply Permutation_app_tail; exact HA|].
    apply gp5_perm5. }
  eapply Permutation_trans; [exact (HPOST _ P1)|].
  eapply Permutation_trans; [apply Permutation_sym; apply gp5_perm5|].
  apply Permutation_app_head. apply Permutation_app_tail.
  eapply Permutation_trans; [|apply Permutation_sym; exact (gp5_model_set mc k h' Hkl)].
  apply Permutation_app_tail. apply Permutation_sym. exact HA'.
Qed.
(* the loop's state after a call on slot k that left the source h' there *)
Lemma gp5_rebuild : forall cx t m mc fpos ly S W mem md kk k h',
  gp5_xp cx t m mc fpos ly S W mem md kk k -> (k < 4)%nat -> length (lm_hs mc) = 4%nat ->
  asrc_at B ly S W mem (gp5_SLOT k) h' -> ablocks_sep B fr_FP cx (gn_set mc k h') ly S ->
  gst B G_fr fr_FP cx t (gn_kq cx m) (gn_set mc k h') fake_shadow_open fpos ly S W mem md kk /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79.
Proof.
  intros cx t m mc fpos ly S W mem md kk k h'
    (HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT & HAW & HPF & H24 & H112 & HSL & HREL & HOUT & HGN & HLK &
     HWK & HNF & HNW & HNR & HTU & HLI & HLW)
    Hk Hlen Hsrc Hsep.
  split; [|split; [exact HAW | split; [exact HPF | split; [exact H24 | exact H112]]]].
  split; [repeat (split; [assumption|]); assumption|]. split; [|exact Hsep].
  unfold amodel_at, gn_set. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite gp5_setn_length; exact Hlen|].
  split.
  { intros j Hj. destruct (Nat.eq_dec j k) as [->|Hjk].
    - rewrite gp5_setn_same by lia. exact Hsrc.
    - rewrite gp5_setn_other by exact Hjk. exact (HSL j Hj Hjk). }
  split; [exact HREL|]. split; [exact HOUT|]. split; [exact HGN|]. split; [exact HLK|]. split; [exact HWK|].
  split; [exact HNF|]. split; [exact HNW|]. split; [exact HNR|]. split; [exact HTU|]. split; [exact HLI | exact HLW].
Qed.
(* ================================================================== values the loop reads *)
Lemma gp5_tbl_fd : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat i) 4 (re_fd (nth i es gn_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hfd Hi.
  assert (Hv : 0 <= re_fd (nth i es gn_e0) < 2 ^ 31).
  { rewrite Forall_forall in Hfd. apply Hfd. apply nth_In. exact Hi. }
  pose proof (gp5_cat_len es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + k < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + Z.of_nat k) with (G + Z.of_nat (56 * i + k) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + k) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_fd (nth i es gn_e0)))) (Z_to_bv 8 0))).
  { rewrite gp5_nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite gp5_cat_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, gp5_le1.
  apply bv_eq. rewrite Z_to_bv_unsigned, gp5_le4 by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma gp5_pads : forall ly S (W : world segs) mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  split; rewrite Forall_forall in HE |- *; intros e He;
    destruct (HE e He) as (_ & _ & H3 & H4 & H5 & _); [split; assumption | exact H5].
Qed.
Lemma gp5_zero_vm : forall m a (N : nat) off (n : nat), garr8 segs m a (repeat 0 N) -> 0 <= off ->
  off + Z.of_nat n <= Z.of_nat N -> val_mem segs m (a + off) n 0.
Proof.
  intros m a N off n Hg Ho Hn k Hk.
  assert (Hj : (Z.to_nat off + k < length (repeat 0%Z N))%nat) by (rewrite repeat_length; lia).
  pose proof (garr8_mbyte segs m a _ _ Hg Hj) as E.
  replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia. rewrite E.
  rewrite nth_repeat, gp5_le_byte0. reflexivity.
Qed.
(* slot k's fd and open fields, whether the slot is open or not *)
Definition gp5_fdv (o : option hsrc) : Z := match o with Some h => hs_fd h | None => 0 end.
Definition gp5_opv (o : option hsrc) : Z := match o with Some h => hs_open h | None => 0 end.
Lemma gp5_slot_vals : forall ly S (W : world segs) mem j o, aslot B ly S W mem j o ->
  val_mem segs (arm W mem) (gp5_SLOT j) 4 (gp5_fdv o) /\ val_mem segs (arm W mem) (gp5_SLOT j + 4) 4 (gp5_opv o) /\
  0 <= gp5_fdv o < 2 ^ 31 /\ (gp5_opv o = 0 \/ gp5_opv o = 1) /\ (o = None <-> gp5_opv o = 0).
Proof.
  intros ly S W mem j o Hs. unfold aslot, gp5_SLOT in *. destruct o as [h|]; cbn [gp5_fdv gp5_opv].
  - destruct Hs as (H1 & H2 & _ & _ & _ & _ & _ & Ho & Hf & _).
    split; [exact H1|]. split; [exact H2|]. split; [exact Hf|]. split; [right; exact Ho|].
    split; [discriminate | lia].
  - destruct Hs as [Hg _].
    split; [rewrite <- (Z.add_0_r (rg_s fr_RG + ASRC * Z.of_nat j));
            apply (gp5_zero_vm _ _ (Z.to_nat ASRC)); [exact Hg | lia | unfold ASRC; lia]|].
    split; [apply (gp5_zero_vm _ _ (Z.to_nat ASRC)); [exact Hg | lia | unfold ASRC; lia]|].
    split; [lia|]. split; [left; reflexivity|]. split; reflexivity.
Qed.
(* ================================================================== the loop's cut points
   Every state of the loop carries p5st: the arm's state gst at the current model mc, what relay_instance_gone
   fixed (gdone), the allocator meter from the operation's LS state, the loop's relation gn_run over the model
   (entry i of the table, slot k of g_s, `at` = A), reads[] still writable, `at` = A, the prefix, and (B) the two frame
   slots the loop and the next phase read: HI_G_NOUT at F+24 and the auipc spill 0x5d8b78 at F+112.  KF-COUNT: the
   meter conjunct carries the loop's cost q of its calls so far (gn_runc, at the same i, k as gn_run) and the bound
   gn_cst of cst by relay_instance_gone's cost plus q, which GN_RI_step / GN_RI_end take. *)
Definition p5st (cx : lfcx) (t : Z) (m m1 mc : lmod) (A : Z) (i k : nat) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gst B G_fr fr_FP cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
  gdone RINV cx t m m1 /\
  (exists ly0 S0 cst q, LS cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_runc MT (gn_pre cx m) m1 mc A i k q /\
     gn_cst MT cx m m1 q cst /\ gn_tie B cx m ly0 S0 mc ly S) /\
  gn_run (gn_pre cx m) m1 mc A i k /\
  awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) A /\
  gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79.
(* the inner loop's registers (B, 0x84bb0): s7 = i, s9 = 56 i, s4 = s5 = &g_s[k], s6 = 4 - k, s8 / s10 = the shadow
   cells of g_s[k].open / .fd *)
Definition gp5_SH0 : Z := SB + rg_s fr_RG / 8.
Definition gp5_ih_regs (i k : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 23 = w64 (Z.of_nat i) /\ getr regs 25 = w64 (56 * Z.of_nat i) /\
  getr regs 20 = w64 (gp5_SLOT k) /\ getr regs 21 = w64 (gp5_SLOT k) /\ getr regs 22 = w64 (4 - Z.of_nat k) /\
  getr regs 24 = w64 (gp5_SH0 + 12 * Z.of_nat k) /\ getr regs 26 = w64 (gp5_SH0 + 12 * Z.of_nat k).
Definition AF_gn_call : Z := 0x28c8.   (* 0x84c0c: check_no_loss(&g_s[k], &at) *)
Definition AF_gn_ret1 : Z := 0x28d4.   (* 0x84c18: back from check_no_loss; check_shape_ends(&g_s[k], s3, &at) *)
Definition AF_gn_skip : Z := 0x28e4.   (* 0x84c28: the inner latch *)
(* 0x84b8c *)
Definition P5OH (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t1) regs mem md /\
    p5st cx t m m1 mc A i 0 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ getr regs 23 = w64 (Z.of_nat i).
(* 0x84bb0 *)
Definition P5IH (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t2) regs mem md /\
    p5st cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x84c0c: slot k is open and holds entry i's fd *)
Definition P5C (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h, c = cfg_at segs (fr_B0 + AF_gn_call) regs mem md /\
    p5st cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x84c28: slot k done *)
Definition P5T (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_skip) regs mem md /\
    p5st cx t m m1 mc A i (S k) fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x84c74: entry i done *)
Definition P5OT (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_tn) regs mem md /\
    p5st cx t m m1 mc A i 4 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ getr regs 23 = w64 (Z.of_nat i).

Lemma gp5_st_jour : forall cx t m m1 mc A i k fpos ly S W mem md kk md',
  p5st cx t m m1 mc A i k fpos ly S W mem md kk ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md' kk ->
  p5st cx t m m1 mc A i k fpos ly S W mem md' kk.
Proof.
  intros cx t m m1 mc A i k fpos ly S W mem md kk md' (((_ & R1) & R2 & R3) & R4) HJ.
  split; [|exact R4]. split; [split; [exact HJ | exact R1]|]. split; [exact R2 | exact R3].
Qed.
(* KF-COUNT (A's p5 gp5_st_skip / gp5_st_next): p5st across a skip of slot k and across the latch to entry i + 1 (no
   call: q and cst unchanged) *)
Lemma gp5_st_skip : forall cx t m m1 mc A i k fpos ly S3 W mem md kk,
  p5st cx t m m1 mc A i k fpos ly S3 W mem md kk -> (k < 4)%nat ->
  (nth k (lm_hs mc) None = None \/
   (forall h, nth k (lm_hs mc) None = Some h -> hs_fd h <> re_fd (nth i (lm_es m1) gn_e0))) ->
  p5st cx t m m1 mc A i (S k) fpos ly S3 W mem md kk.
Proof.
  intros cx t m m1 mc A i k fpos ly S3 W mem md kk
    (X1 & X2 & (ly0 & S0 & cst & q & Y1 & Y2 & Y3 & Y4 & Y5) & X4 & X5) Hk Hsk.
  split; [exact X1|]. split; [exact X2|].
  split; [exists ly0, S0, cst, q; split; [exact Y1|]; split; [exact Y2|];
          split; [apply gn_runc_skip; [exact Y3 | exact Hk | exact Hsk]|]; split; [exact Y4 | exact Y5]|].
  split; [|exact X5]. apply gn_run_skip; [exact X4 | exact Hk | exact Hsk].
Qed.
Lemma gp5_st_next : forall cx t m m1 mc A i fpos ly S3 W mem md kk,
  p5st cx t m m1 mc A i 4 fpos ly S3 W mem md kk -> p5st cx t m m1 mc A (S i) 0 fpos ly S3 W mem md kk.
Proof.
  intros cx t m m1 mc A i fpos ly S3 W mem md kk
    (X1 & X2 & (ly0 & S0 & cst & q & Y1 & Y2 & Y3 & Y4 & Y5) & X4 & X5).
  split; [exact X1|]. split; [exact X2|].
  split; [exists ly0, S0, cst, q; split; [exact Y1|]; split; [exact Y2|];
          split; [apply gn_runc_next; exact Y3|]; split; [exact Y4 | exact Y5]|].
  split; [|exact X5]. apply gn_run_next. exact X4.
Qed.

(* ================================================================== the walks' common pieces *)
Lemma gp5_hi : VAL (A_HI 79) = gp5_HI79 /\ VAL (A_HI 70) = HI_G_SRC /\ VAL (A_OBJ 4) = rg_nsrc fr_RG /\
  VAL (A_OBJ 5) = rg_src fr_RG /\ VAL (A_OBJ 19) = rg_s fr_RG.
Proof. vm_compute. repeat split. Qed.
Lemma gp5_SH0_val : gp5_SH0 = SB + (rg_s fr_RG + 4) / 8 /\ gp5_SH0 = SB + rg_s fr_RG / 8 /\ gp5_SH0 = 2148217292.
Proof. unfold gp5_SH0, SB, fr_RG, fr_globals_b. cbn [rg_s]. split; [reflexivity | split; reflexivity]. Qed.
Definition gp5_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gp5_Bx : sv := SOff 27 0.
Lemma gp5_EE : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
  intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma gp5_EX : forall regs extra j, (j < 8)%nat -> ew (Eimg (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma gp5_SLOT_rng : forall k, (k < 4)%nat -> 0x5d8e60 <= gp5_SLOT k <= 0x5d8e60 + 288 /\ gp5_SLOT k mod 32 = 0.
Proof.
  intros k Hk. unfold gp5_SLOT, fr_RG, fr_globals_b, ASRC. cbn [rg_s]. split; [lia|].
  replace (6131296 + 96 * Z.of_nat k) with ((191603 + 3 * Z.of_nat k) * 32) by lia. apply Z_mod_mult.
Qed.
Lemma gp5_sv_U : forall E v z, U E v = z -> 0 <= z < 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H Hz. apply bv_eq. rewrite unsigned_lit_small by exact Hz. exact H. Qed.
(* a run over read-only regions leaves the memory as it was *)
Ltac gp5_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac gp5_awr := repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn in Ha; lia|]); apply awr_ok_x_nil.
(* a register the run pinned to an expression, still that expression at the end *)
Ltac gp5_pin HS r P Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  lazymatch type of P with getr ?R _ = _ =>
    let Hr0 := fresh "Hr0" in
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr0;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr0;
    cbn [ms_regs restrict] in Hr0;
    assert (Hr : getr (ms_regs ms) r = getr R r) by (rewrite Hr0, P; reflexivity); clear Hr0 end end.
(* a register's symbolic value at the end of a run, left unnormalized *)
Ltac gp5_rraw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* the arm's kept registers and the inner loop's, carried by a run that keeps KL and pins 18 / 21 / 24 / 26 *)
Lemma gp5_kregs_tr : forall cx FF (regs rf : bvmap 5 word) (KL : list (bv 5)),
  gn_kregs B cx FF regs -> (forall r, In r [2; 3; 4; 8; 9; 18; 19; 27]%bv -> In r KL) ->
  (forall r, In r KL -> getr rf r = getr regs r) -> gn_kregs B cx FF rf.
Proof.
  intros cx FF regs rf KL (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4) HKL KR.
  assert (K : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 27]%bv -> getr rf r = getr regs r)
    by (intros r Hr; apply KR, HKL, Hr).
  repeat split; rewrite K by (cbv; tauto); assumption.
Qed.
Definition IH_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 22; 23; 25; 27]%bv.
Lemma gp5_regs_tr : forall cx FF i k (regs rf : bvmap 5 word),
  gn_kregs B cx FF regs -> gp5_ih_regs i k regs ->
  (forall r, In r IH_KEPT -> getr rf r = getr regs r) ->
  getr rf 18 = getr regs 18 -> getr rf 21 = getr regs 21 -> getr rf 24 = getr regs 24 -> getr rf 26 = getr regs 26 ->
  gn_kregs B cx FF rf /\ gp5_ih_regs i k rf.
Proof.
  intros cx FF i k regs rf (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4) (R23 & R25 & R20 & R21 & R22 & R24 & R26)
    KR Q18 Q21 Q24 Q26.
  split.
  - repeat split; first [rewrite Q18; assumption | rewrite KR by (cbv; tauto); assumption].
  - repeat split; first [rewrite Q21; assumption | rewrite Q24; assumption | rewrite Q26; assumption
                       | rewrite KR by (cbv; tauto); assumption].
Qed.

(* ================================================================== the inner head 0x84bb0 *)
Definition ih_sr : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff (A_HI 70) 0))
    24 (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3))))
    26 (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))))
    21 (SOff 20 0).
Definition ih_regions : smem :=
  [ YP09.mkRegion (Some 20%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))];
    YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 35%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))] ].
(* W_traps.v's recipe: R1 on the pointer atoms 32 (g_src) and 35 (&g_src[i]), R2's two aliases for 35 = 32 + 25 *)
Definition ih_facts : facts :=
  mkFacts [ (20%nat, mkAF 0x5d8e60 (0x5d8e60 + 288) 5); (25%nat, mkAF 0 840 3); (27%nat, mkAF SB SB 0);
            (32%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 1 0);
            (35%nat, mkAF 4096 140737479966720 3); (36%nat, mkAF 0 (2 ^ 31 - 1) 0) ] []
          [ (SAlu ALU_ADD (SOff 32 0) (SOff 25 0), SOff 35 0); (SAlu ALU_ADD (SOff 25 0) (SOff 32 0), SOff 35 0) ].
Definition ss_ih : sstate := mkSS AF_gn_t2 ih_sr ih_regions None ih_facts.
Definition ih_SH : list shent := [ mkSHE 20 0 16; mkSHE 35 0 8 ].
Definition ih_extra (G fdv opv ea efd : Z) : list word := map (Z_to_bv 64) [G; fdv; opv; ea; efd].

Lemma gp5_ih_entry : forall (W : world segs) ly S mem md regs (i k : nat) G es tail fdv opv,
  AR segs B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> atable_at W mem G es tail ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat -> (length es <= 16)%nat -> (k < 4)%nat ->
  val_mem segs (arm W mem) (rg_src fr_RG) 8 G ->
  val_mem segs (arm W mem) (gp5_SLOT k) 4 fdv -> val_mem segs (arm W mem) (gp5_SLOT k + 4) 4 opv ->
  0 <= fdv < 2 ^ 31 -> (opv = 0 \/ opv = 1) ->
  getr regs 18 = w64 HI_G_SRC -> getr regs 27 = w64 SB -> gp5_ih_regs i k regs ->
  let E := Eimg (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) in
  (st_ok_pi segs VAL E ss_ih (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_t2)) mem (seg_rom segs))) /\
   sh_ok segs gp5_Bx ih_SH E (mrestrict (w_H W) mem)) /\
  (getr regs 18 = sv_denot E (SOff (A_HI 70) 0) /\
   getr regs 24 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3))) /\
   getr regs 26 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))) /\
   getr regs 21 = sv_denot E (SOff 20 0)) /\
  ew E 32 = Z_to_bv 64 G /\ ew E 33 = Z_to_bv 64 fdv /\ ew E 34 = Z_to_bv 64 opv /\
  ew E 35 = Z_to_bv 64 (G + AENT * Z.of_nat i) /\ ew E 36 = Z_to_bv 64 (re_fd (nth i es gn_e0)) /\
  env_agree 32 (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) E /\
  img_env VAL A_LIM E.
Proof.
  intros W ly S mem md regs i k G es tail fdv opv HAR HGin HTAB HPAD HFDS Hi Hl16 Hk M8 Mfd Mop Hfd Hop R18 R27
    (R23 & R25 & R20 & R21 & R22 & R24 & R26) E.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md G ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & HGapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil, HGapp.
  pose proof (blk_off_imgP B ly S W mem md G ATABLE HAR HGin) as Hoff. rewrite RQ in Hoff. red in Hoff.
  pose proof (gp5_SLOT_rng k Hk) as (HS1 & HS2).
  assert (Hefd : 0 <= re_fd (nth i es gn_e0) < 2 ^ 31) by (rewrite Forall_forall in HFDS; apply HFDS, nth_In; exact Hi).
  pose proof (gp5_tbl_fd W mem G es tail i HTAB HPAD HFDS Hi) as Mefd.
  assert (E20 : ew E 20 = Z_to_bv 64 (gp5_SLOT k)) by (unfold E; rewrite (gp5_EE regs _ 20 20%bv eq_refl); exact R20).
  assert (E25 : ew E 25 = Z_to_bv 64 (56 * Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 25 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 27 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 G) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 fdv) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 opv) by (unfold E; exact (gp5_EX regs _ 2 ltac:(lia))).
  assert (E35 : ew E 35 = Z_to_bv 64 (G + AENT * Z.of_nat i)) by (unfold E; exact (gp5_EX regs _ 3 ltac:(lia))).
  assert (E36 : ew E 36 = Z_to_bv 64 (re_fd (nth i es gn_e0))) by (unfold E; exact (gp5_EX regs _ 4 ltac:(lia))).
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (EO5 : ew E (A_OBJ 5) = Z_to_bv 64 (rg_src fr_RG))
    by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        destruct gp5_hi as (_ & _ & _ & H & _); rewrite H; reflexivity).
  assert (U20 : bv_unsigned (ew E 20) = gp5_SLOT k) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (UO5 : bv_unsigned (ew E (A_OBJ 5)) = rg_src fr_RG)
    by (rewrite EO5; apply unsigned_lit_small; unfold fr_RG, fr_globals_b; cbn; lia).
  assert (U35 : bv_unsigned (ew E 35) = G + AENT * Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; unfold AENT; lia).
  assert (USH : forall c, 0 <= c < 8 -> U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 c) (SLit 3))) = gp5_SH0 + 12 * Z.of_nat k).
  { intros c Hc. rewrite !U_SAlu, (U_atom E 27 SB E27) by (unfold SB; lia).
    rewrite (U_atom_off E 20 (gp5_SLOT k) c E20) by lia. rewrite U_lit by lia. cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (Hq : (gp5_SLOT k + c) / 8 = rg_s fr_RG / 8 + 12 * Z.of_nat k).
    { unfold gp5_SLOT, fr_RG, fr_globals_b, ASRC in *. cbn [rg_s] in *.
      replace (6131296 + 96 * Z.of_nat k + c) with (c + (766412 + 12 * Z.of_nat k) * 8) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. change (6131296 / 8) with 766412. lia. }
    rewrite Hq. unfold gp5_SH0, zcanon, M64, SB, fr_RG, fr_globals_b. cbn [rg_s]. change (6131296 / 8) with 766412.
    rewrite (Z.mod_small (766412 + 12 * Z.of_nat k)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (P18 : getr regs 18 = sv_denot E (SOff (A_HI 70) 0)).
  { rewrite R18. apply bv_eq. fold (U E (SOff (A_HI 70) 0)).
    rewrite (U_img_atom E HEI (A_HI 70)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & H & _). rewrite H. unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia. }
  assert (P24 : getr regs 24 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3)))).
  { rewrite R24. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3)))).
    rewrite (USH 4 ltac:(lia)). unfold w64. apply unsigned_lit_small. unfold gp5_SH0, SB, fr_RG, fr_globals_b; cbn; lia. }
  assert (P26 : getr regs 26 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
  { rewrite R26. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
    rewrite (USH 0 ltac:(lia)). unfold w64. apply unsigned_lit_small. unfold gp5_SH0, SB, fr_RG, fr_globals_b; cbn; lia. }
  assert (P21 : getr regs 21 = sv_denot E (SOff 20 0)).
  { rewrite R21. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HAE : env_agree 32 (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  split; [split|split; [exact (conj P18 (conj P24 (conj P26 P21)))|repeat (split; [assumption|]); assumption]].
  - rewrite restrict_mkst_fx. unfold ss_ih. apply pa_entry_st_ok_full.
    + unfold ih_sr.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
        | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |];
        assumption.
    + vm_compute. reflexivity.
    + unfold ih_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        -- apply (chunk_ok_val segs E _ (gp5_SLOT k) 0 4 (SOff 33 0) fdv);
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           rewrite Z.add_0_r. exact Mfd.
        -- apply (chunk_ok_val segs E _ (gp5_SLOT k) 4 4 (SOff 34 0) opv);
             [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
           exact Mop.
      * rewrite UO5. split; [unfold fr_RG, fr_globals_b; cbn; lia|]. split; [unfold fr_RG, fr_globals_b; cbn; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 32 0) G);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
        rewrite Z.add_0_r. exact M8.
      * rewrite U35. split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (G + AENT * Z.of_nat i) 0 4 (SOff 36 0) (re_fd (nth i es gn_e0)));
          [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
        rewrite Z.add_0_r. exact Mefd.
    + apply pairwise_disjoint_of_extents. unfold ih_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, UO5, U35.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold fr_RG, fr_globals_b, AENT in *. cbn [rg_src] in *. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [ih_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E20, E25, E27, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB, AENT; lia).
        change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
        assert (HG8 : (G + AENT * Z.of_nat i) mod 8 = 0).
        { unfold AENT. replace (G + 56 * Z.of_nat i) with (G + (7 * Z.of_nat i) * 8) by lia.
          rewrite Z_mod_plus_full. pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
          rewrite D. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by lia. apply Z_mod_mult. }
        assert (H56 : (56 * Z.of_nat i) mod 8 = 0).
        { replace (56 * Z.of_nat i) with ((7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
        unfold SB, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia;
          destruct Hop as [-> | ->]; lia.
      * cbn [ih_facts f_alias alias_ok].
        assert (UA : U E (SAlu ALU_ADD (SOff 32 0) (SOff 25 0)) = G + AENT * Z.of_nat i /\
                     U E (SAlu ALU_ADD (SOff 25 0) (SOff 32 0)) = G + AENT * Z.of_nat i).
        { rewrite !U_SAlu, (U_atom E 32 G E32), (U_atom E 25 (56 * Z.of_nat i) E25) by lia. cbn [zalu_raw].
          unfold zcanon, M64, AENT. split; rewrite Z.mod_small by lia; lia. }
        destruct UA as (UA1 & UA2).
        assert (U35' : U E (SOff 35 0) = G + AENT * Z.of_nat i) by (apply U_atom; [exact E35 | unfold AENT; lia]).
        split; [|split; [|exact I]]; apply bv_eq; fold (U E (SOff 35 0)).
        -- fold (U E (SAlu ALU_ADD (SOff 32 0) (SOff 25 0))). rewrite UA1, U35'. reflexivity.
        -- fold (U E (SAlu ALU_ADD (SOff 25 0) (SOff 32 0))). rewrite UA2, U35'. reflexivity.
  - assert (HBx : U E gp5_Bx = SHADOW_OFF) by (unfold gp5_Bx; rewrite (U_atom E 27 SB E27) by (unfold SB; lia); reflexivity).
    constructor; [|constructor; [|constructor]].
    + eapply shent_ok_of_range.
      * apply (azs_range_addressable B LAWS ly S W mem md (gp5_SLOT k) 16 HAR).
        destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold gp5_SLOT, ASRC in *.
        exists zr. refine (conj Hzin (conj Hz8 _)). lia.
      * exact HBx.
      * rewrite (U_atom E 20 _ E20) by lia. reflexivity.
      * lia.
      * lia.
      * intros x Hx. unfold SHADOW_OFF in *. lia.
    + eapply shent_ok_of_range.
      * apply (range_addressable_of_block segs B LAWS ly S W mem md G ATABLE (G + AENT * Z.of_nat i) 8 HAR HGin);
          rewrite ?RQ; unfold AENT; lia.
      * exact HBx.
      * rewrite (U_atom E 35 _ E35) by (unfold AENT; lia). reflexivity.
      * lia.
      * lia.
      * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia.
Qed.

(* ================================================================== 0x84bb0 -> 0x84c28 (skip) or 0x84c0c (call) *)
Lemma gp5_ih : forall cx t m m1 i k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5IH cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => P5T cx t m m1 i k W' c' \/ P5C cx t m m1 i k W' c').
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (HGS & HDN & HLS0 & HRUN & HAW & HAT & HPF & H24 & H112).
  pose proof HGS as ((HJ & HFR & _) & HMOD & HSEP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof HMOD as (M1 & M2 & M3 & _).
  pose proof M3 as (R1 & _ & _ & _ & _ & _ & Hl16 & HGin & (tl & HTAB) & _ & _).
  destruct (gp5_pads ly S3 W mem (lm_G mc) (lm_es mc) M3) as (HPAD & HFDS).
  assert (HAR : AR segs B ly S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (Hi' : (i < length (lm_es mc))%nat) by (rewrite Q3; exact Hi).
  pose proof (M2 k Hk) as Hslot.
  destruct (gp5_slot_vals ly S3 W mem k _ Hslot) as (Mfd & Mop & Hfdr & Hopr & Hnone).
  assert (Hopb : 0 <= gp5_opv (nth k (lm_hs mc) None) <= 1) by (destruct Hopr as [Ho | Ho]; rewrite Ho; lia).
  assert (Hefd : 0 <= re_fd (nth i (lm_es mc) gn_e0) < 2 ^ 31).
  { pose proof HFDS as HF2. rewrite Forall_forall in HF2. apply HF2, nth_In. exact Hi'. }
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  destruct (al_blocks _ _ LAWS ly S3 W mem md (lm_G mc) ATABLE HAR HGin) as (_ & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (gp5_ih_entry W ly S3 mem md regs i k (lm_G mc) (lm_es mc) tl _ _ HAR HGin HTAB HPAD HFDS Hi' Hl16 Hk
    R1 Mfd Mop Hfdr Hopr R18 R27 HIR) as ((HS & SHOK) & (P18 & P24 & P26 & P21) & E32 & E33 & E34 & E35 & E36 & HAE & HEI).
  set (E := Eimg (Ereg regs (ih_extra (lm_G mc) (gp5_fdv (nth k (lm_hs mc) None)) (gp5_opv (nth k (lm_hs mc) None))
    (lm_G mc + AENT * Z.of_nat i) (re_fd (nth i (lm_es mc) gn_e0))))) in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t2)) with (Z_to_bv 64 (BASE + AF_gn_t2)).
  (* the shadow check of g_s[k].open, the load of open, to `beqz` *)
  paj_run_tok RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* open = 0: the slot is closed - on to 0x84c28 *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. apply Hnone in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_skip.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
    gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left.
    lazymatch goal with |- P5T _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26)]]].
    apply (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
    apply gp5_st_skip; [exact HST | exact Hk | left; exact Hc].
  - (* open: the shadow check of fd, g_src[i] and its traps, the shadow of g_src[i].fd, the two fds, to `bne` *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    destruct (nth k (lm_hs mc) None) as [h|] eqn:Eh; [|cbn in Hc; lia].
    paj_run_tok RUN HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em2. clear HF HFr HG0.
    (* 0x84bd0 `bltu a0,a1`: &g_src[i] = g_src + 56 i does not wrap (W_traps.v trap_ptr_bltu) *)
    psrr_branch_tok RUN BR HS SHOK gp5_span.
    { exfalso.
      rewrite (trap_ptr_bltu E (SOff 32 0) (SOff 35 0) (lm_G mc) (lm_G mc + AENT * Z.of_nat i)) in Hc0;
        [discriminate Hc0 | apply U_atom; [exact E32 | lia] | apply U_atom; [exact E35 | unfold AENT; lia]
        | unfold AENT; lia]. }
    paj_run_tok RUN HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em3. clear HF HFr HG0.
    psrr_branch_tok RUN BR HS SHOK gp5_span.
    + (* the fds differ: on to 0x84c28 *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc1 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc1. cbn [gp5_fdv] in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_skip.
      { gp5_awr. }
      gp5_meq HF Em4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
      gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
      pmkst HS. rewrite Em4, Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. left.
      lazymatch goal with |- P5T _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
      split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26)]]].
      apply (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_skip; [exact HST | exact Hk|].
      right. intros h' Eh'. rewrite Eh in Eh'. injection Eh' as <-. rewrite <- Q3. exact Hc1.
    + (* the fds are equal: on to the calls at 0x84c0c *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc1 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc1. cbn [gp5_fdv] in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_call.
      { gp5_awr. }
      gp5_meq HF Em4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
      gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
      pmkst HS. rewrite Em4, Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. right.
      lazymatch goal with |- P5C _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A, h. split; [reflexivity|].
      split; [exact (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
      split; [exact Hk|]. split; [exact Hi|]. split; [exact Eh|]. split; [rewrite <- Q3; exact Hc1|].
      exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26).
Qed.

(* ================================================================== 0x84c28 -> 0x84bb0 (k + 1 < 4) or 0x84c74 *)
Definition it_facts : facts := mkFacts [ (22%nat, mkAF 1 4 0); (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_it : sstate := mkSS AF_gn_skip sr_atoms [] None it_facts.
Lemma gp5_it_entry : forall (W : world segs) regs mem (k : nat),
  getr regs 22 = w64 (4 - Z.of_nat k) -> (k < 4)%nat -> getr regs 27 = w64 SB ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) ss_it
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_skip)) mem (seg_rom segs))) /\
  sh_ok segs gp5_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem k R22 Hk R27. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs [])).
  assert (E22 : ew E 22 = Z_to_bv 64 (4 - Z.of_nat k)) by (unfold E; rewrite (gp5_EE regs _ 22 22%bv eq_refl); exact R22).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 27 27%bv eq_refl); exact R27).
  split.
  - unfold ss_it. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [it_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E27, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Definition IT_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 23; 25; 27]%bv.
Lemma gp5_it : forall cx t m m1 i k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5T cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => ((S k < 4)%nat /\ P5IH cx t m m1 i (S k) W' c') \/
                             (S k = 4%nat /\ P5OT cx t m m1 i W' c')).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (((HJ & _) & _) & _).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  destruct (gp5_it_entry W regs mem k R22 Hk R27) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; exact (gp5_EE regs _ n r Hn)).
  pose proof (gp5_SLOT_rng k Hk) as (HS1 & HS2).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + AF_gn_skip)).
  paj_run_tok RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (U22 : U E (SOff 22 (-1)) = 4 - Z.of_nat k - 1) by (apply U_atom_off; [rewrite (EE 22%nat 22%bv eq_refl); exact R22 | lia | lia]).
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* s6 <> 0: the next slot *)
    rewrite branch_ne_U, U22, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_t2.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
    gp5_rraw HS (24%bv : bv 5) N24. gp5_rraw HS (26%bv : bv 5) N26.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [lia|].
    lazymatch goal with |- P5IH _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [exact (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [lia|]. split; [exact Hi|].
    split; [apply (gp5_kregs_tr _ _ _ _ IT_KEPT HR); [intros r Hr; unfold IT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    assert (EV : forall (rr : bv 5) n v c, Z.of_nat n = bv_unsigned rr -> getr regs rr = w64 v -> 0 <= v < 2 ^ 64 ->
        0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c)).
    { intros rr n v c Hn Hr Hv Hvc. apply gp5_sv_U; [|lia]. apply U_atom_off; [rewrite (EE n rr Hn); exact Hr | lia | lia]. }
    unfold gp5_ih_regs. rewrite !KR by (cbv; tauto).
    split; [exact R23|]. split; [exact R25|].
    unfold gp5_SH0, gp5_SLOT, ASRC in *.
    split; [rewrite N20, (EV 20%bv 20%nat _ 96 eq_refl R20) by lia; f_equal; lia|].
    split; [rewrite N21, (EV 21%bv 21%nat _ 96 eq_refl R21) by lia; f_equal; lia|].
    split; [rewrite N22, (EV 22%bv 22%nat _ (-1) eq_refl R22) by lia; f_equal; lia|].
    split; [rewrite N24, (EV 24%bv 24%nat _ 12 eq_refl R24) by (unfold SB, fr_RG, fr_globals_b; cbn; lia); f_equal; lia|].
    rewrite N26, (EV 26%bv 26%nat _ 12 eq_refl R26) by (unfold SB, fr_RG, fr_globals_b; cbn; lia). f_equal. lia.
  - (* s6 = 0: j 0x84c74 *)
    rewrite branch_ne_U, U22, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_tn.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. split; [lia|].
    lazymatch goal with |- P5OT _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    replace 4%nat with (S k) by lia.
    split; [exact (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [exact Hi|].
    split; [apply (gp5_kregs_tr _ _ _ _ IT_KEPT HR); [intros r Hr; unfold IT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite KR by (cbv; tauto). exact R23.
Qed.

(* ================================================================== 0x84b8c -> 0x84bb0: s9 = 56 i, s4 = s5 = &g_s[0],
   s6 = 4, s8 / s10 = the shadow cells of g_s[0].open / .fd from F+152 / F+120 *)
Definition oh_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 120 160 0 0
      [YP09.mkChunk 120 (CVal 8 (SLit gp5_SH0)); YP09.mkChunk 152 (CVal 8 (SLit gp5_SH0))] ].
Definition oh_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (23%nat, mkAF 0 15 0); (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_oh : sstate := mkSS AF_gn_t1 sr_atoms oh_regions None oh_facts.
Lemma gp5_oh_entry : forall (W : world segs) regs mem F (i : nat),
  getr regs 9 = w64 F -> getr regs 23 = w64 (Z.of_nat i) -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F -> F + 160 <= 2 ^ 47 -> F mod 32 = 0 -> (i < 16)%nat ->
  sv8 W mem (F + 120) gp5_SH0 -> sv8 W mem (F + 152) gp5_SH0 ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) ss_oh
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_t1)) mem (seg_rom segs))) /\
  sh_ok segs gp5_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F i R9 R23 R27 HF1 HF2 HF3 Hi M120 M152. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs [])).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (unfold E; rewrite (gp5_EE regs _ 9 9%bv eq_refl); exact R9).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 27 27%bv eq_refl); exact R27).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
  pose proof gp5_SH0_val as (_ & _ & HSH).
  split.
  - unfold ss_oh. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, oh_regions.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val segs E _ F 120 8 (SLit gp5_SH0) gp5_SH0); [reflexivity | rewrite HSH; cbn; lia | zside | exact M120].
      * apply (chunk_ok_val segs E _ F 152 8 (SLit gp5_SH0) gp5_SH0); [reflexivity | rewrite HSH; cbn; lia | zside | exact M152].
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [oh_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E23, E27, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Definition OH_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 23; 27]%bv.
Lemma gp5_oh : forall cx t m m1 i W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5OH cx t m m1 i W c ->
  SRr segs W c (P5IH cx t m m1 i 0).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R23).
  pose proof HST as (((HJ & HFR & _) & HMOD & _) & _ & _ & HRUN & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (_ & _ & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _). pose proof M3 as (_ & _ & _ & _ & _ & _ & Hl16 & _). rewrite Q3 in Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F120 & _ & _ & F152 & _).
  pose proof gp5_SH0_val as (EQ1 & EQ2 & _). pose proof asan_consts as (C1 & _).
  rewrite <- EQ2 in F120. rewrite <- EQ1 in F152.
  destruct (gp5_oh_entry W regs mem (lf_F cx) i R9 R23 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) F120 F152) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t1)) with (Z_to_bv 64 (BASE + AF_gn_t1)).
  paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_t2.
  { gp5_awr. }
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
  gp5_rraw HS (24%bv : bv 5) N24. gp5_rraw HS (25%bv : bv 5) N25. gp5_rraw HS (26%bv : bv 5) N26.
  pmkst HS. rewrite Em in HJ |- *.
  apply SRr_ret.
  lazymatch goal with |- P5IH _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
  exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
  split; [exact (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
  split; [lia|]. split; [exact Hi|].
  split; [apply (gp5_kregs_tr _ _ _ _ OH_KEPT HR); [intros r Hr; unfold OH_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
  assert (ES : sv_denot E (SOff (A_OBJ 19) 0) = w64 (rg_s fr_RG)).
  { cbn [sv_denot]. unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & _ & _ & _ & H). rewrite H, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  unfold gp5_ih_regs, gp5_SLOT. rewrite Nat2Z.inj_0, Z.mul_0_r, !Z.add_0_r.
  split; [rewrite KR by (cbv; tauto); exact R23|].
  split.
  { rewrite N25. apply gp5_sv_U; [|lia]. rewrite U_SMd, (U_atom E 23 (Z.of_nat i) E23), U_lit by lia.
    cbn [zmd_raw]. unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
  split; [rewrite N20; exact ES|]. split; [rewrite N21; exact ES|].
  split; [rewrite N22; reflexivity|].
  pose proof gp5_SH0_val as (_ & _ & HSH). rewrite HSH.
  split; [rewrite N24; reflexivity|]. rewrite N26. reflexivity.
Qed.

(* ================================================================== the loop's end: 0x84c84 *)
Lemma gp5_mk_csd : forall cx t m m1 mc A fpos ly S3 W mem md kk regs c,
  c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md ->
  p5st cx t m m1 mc A (length (lm_es m1)) 0 fpos ly S3 W mem md kk ->
  gn_kregs B cx (frame_addr ly 1 fpos) regs ->
  GCSD B G_fr fr_FP LS RINV cx t m mc W c.
Proof.
  intros cx t m m1 mc A fpos ly S3 W mem md kk regs c ->
    (HGS & (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
            Hmpos & Hmsz & Hc2) &
     (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF & H24 & H112) HR.
  (* g_gone is 0 or 1 (agone_at, W_rep.v:195-196, in amodel_at at mc), and lm_gn mc = lm_gn m1 = lm_gn m *)
  assert (Hgn : lm_gn m = 0 \/ lm_gn m = 1).
  { pose proof HGS as (_ & (_ & _ & _ & _ & (_ & _ & G01) & _) & _).
    pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & _).
    pose proof Hafter as (_ & _ & _ & _ & _ & _ & _ & _ & A9 & _).
    rewrite Q9, A9 in G01. exact G01. }
  destruct (RIend cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A ly S3 cst qc HRI Hop Hkeys Hgn Hcap0 Hent Hsrc HLS Hpairs
    Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie))
    as (HA & HRI' & HLS').
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & _).
  pose proof Hafter as (K1 & _).
  pose proof Hop as (_ & _ & Ht & Hkm).
  exists regs, mem, md, ly, S3, kk, fpos. split; [reflexivity|].
  split; [exact HGS|]. split; [exact HLS'|]. split; [exact HRI'|].
  split; [rewrite Q1; exact K1|].
  split; [unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia|].
  split; [exact Ht|]. split; [rewrite <- HA; exact HAT|]. split; [exact HAW|].
  split; [exact H24 | exact HR].
Qed.

(* ================================================================== 0x84c74 -> 0x84b8c (i + 1 < g_nsrc) or 0x84c84:
   a0 = the spill 0x5d8b78 from F+112, a0 = g_nsrc (lw 424(a0)), s7 = i + 1 *)
Definition ot_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 112 120 0 0 [YP09.mkChunk 112 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 32%nat) 424 428 0 0 [YP09.mkChunk 424 (CVal 4 (SOff 33 0))] ].
Definition ot_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (23%nat, mkAF 0 15 0); (27%nat, mkAF SB SB 0);
            (32%nat, mkAF gp5_HI79 gp5_HI79 0); (33%nat, mkAF 1 16 0) ] [] [].
Definition ss_ot : sstate := mkSS AF_gn_tn sr_atoms ot_regions None ot_facts.
Definition ot_extra (n : Z) : list word := map (Z_to_bv 64) [gp5_HI79; n].
Lemma gp5_nsrc_addr : gp5_HI79 + 424 = rg_nsrc fr_RG.
Proof. vm_compute. reflexivity. Qed.
Lemma gp5_ot_entry : forall (W : world segs) regs mem F (i : nat) n,
  getr regs 9 = w64 F -> getr regs 23 = w64 (Z.of_nat i) -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F -> F + 160 <= 2 ^ 47 -> F mod 32 = 0 -> (i < 16)%nat -> 1 <= n <= 16 ->
  sv8 W mem (F + 112) gp5_HI79 -> val_mem segs (arm W mem) (rg_nsrc fr_RG) 4 n ->
  st_ok_pi segs VAL (Eimg (Ereg regs (ot_extra n))) ss_ot
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_tn)) mem (seg_rom segs))) /\
  sh_ok segs gp5_Bx [] (Eimg (Ereg regs (ot_extra n))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F i n R9 R23 R27 HF1 HF2 HF3 Hi Hn M112 Mn. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (ot_extra n))).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (unfold E; rewrite (gp5_EE regs _ 9 9%bv eq_refl); exact R9).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 27 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 gp5_HI79) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = gp5_HI79) by (rewrite E32; apply unsigned_lit_small; unfold gp5_HI79; lia).
  split.
  - unfold ss_ot. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold ot_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ F 112 8 (SOff 32 0) gp5_HI79);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold gp5_HI79; cbn; lia | zside | exact M112].
      * rewrite U32. split; [unfold gp5_HI79; lia|]. split; [unfold gp5_HI79; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ gp5_HI79 424 4 (SOff 33 0) n);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
        rewrite gp5_nsrc_addr. exact Mn.
    + apply pairwise_disjoint_of_extents. unfold ot_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold gp5_HI79. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [ot_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E23, E27, E32, E33, !unsigned_lit_small by (unfold SB, gp5_HI79; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, gp5_HI79.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Definition OT_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 27]%bv.
Lemma gp5_ot : forall cx t m m1 i W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5OT cx t m m1 i W c ->
  SRr segs W c (fun W' c' => ((S i < length (lm_es m1))%nat /\ P5OH cx t m m1 (S i) W' c') \/
                             (exists mc, GCSD B G_fr fr_FP LS RINV cx t m mc W' c')).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R23).
  pose proof HST as (HGS & _ & _ & HRUN & _ & _ & _ & _ & H112).
  pose proof HGS as ((HJ & HFR & _) & HMOD & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  rewrite Q3 in Mn, Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof asan_consts as (C1 & _).
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_ot_entry W regs mem (lf_F cx) i n R9 R23 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) ltac:(unfold n; lia) H112 Mn) as [HS SHOK].
  set (E := Eimg (Ereg regs (ot_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ot_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_tn)) with (Z_to_bv 64 (BASE + AF_gn_tn)).
  paj_run_tok RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (S23 : bv_signed (sv_denot E (SOff 23 1)) = Z.of_nat i + 1).
  { assert (U23 : U E (SOff 23 1) = Z.of_nat i + 1) by (apply U_atom_off; [exact E23 | lia | lia]).
    unfold U in U23. rewrite bv_signed_small; [exact U23 | rewrite U23; lia]. }
  assert (S33 : bv_signed (sv_denot E (SOff 33 0)) = n).
  { assert (U33 : U E (SOff 33 0) = n) by (apply U_atom; [exact E33 | unfold n; lia]).
    unfold U in U33. rewrite bv_signed_small; [exact U33 | rewrite U33; unfold n; lia]. }
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* i + 1 < g_nsrc: the next entry *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S23, S33 in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split.
    { apply (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next. exact HST. }
    split; [unfold n in Hc; lia|].
    split; [apply (gp5_kregs_tr _ _ _ _ OT_KEPT HR); [intros r Hr; unfold OT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite N23. apply gp5_sv_U; [rewrite Nat2Z.inj_succ; apply U_atom_off; [exact E23 | lia | lia] | lia].
  - (* g_nsrc <= i + 1: the loop is done; 0x84c84 *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S23, S33 in Hc. apply Z.ltb_ge in Hc.
    assert (Hend : S i = length (lm_es m1)) by (unfold n in Hc; lia).
    paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. exists mc.
    eapply (gp5_mk_csd cx t m m1 mc A fpos ly S3 W _ _ kk); [reflexivity | |].
    + rewrite <- Hend. apply (gp5_st_jour _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next. exact HST.
    + apply (gp5_kregs_tr _ _ _ _ OT_KEPT HR); [intros r Hr; unfold OT_KEPT; cbn [In] in Hr |- *; tauto | exact KR].
Qed.

(* ================================================================== 0x84b78: a0 = 0x5d8b78 (auipc), spilled to F+112;
   a0 = g_nsrc (lw 424(a0)); blez -> 0x84c84 (empty table), else s7 = 0 and on to 0x84b8c.  The spill is the one store
   of the phase: every other byte is kept by the runs' frame_of (the frame region's one writable window F+112..F+120). *)
(* a byte present before a run that only grows the memory is present after it (A's p0 gp0_pres_grows) *)
Lemma gp5_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
(* the arm's state across a step that keeps every byte but the spill cell F+112..F+120 (and every writable byte
   writable): A's p0 gp0_close, with B's gcom *)
Lemma gp5_gst_keep : forall cx t kq mc fpos ly S W mem mem' md md' kk,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  gst B G_fr fr_FP cx t kq mc fake_shadow_open fpos ly S W mem md kk ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem' md' kk ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 112 <= a < lf_F cx + 120) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  gst B G_fr fr_FP cx t kq mc fake_shadow_open fpos ly S W mem' md' kk.
Proof.
  intros cx t kq mc fpos ly S W mem mem' md md' kk HB
    ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP) HJ' KEEP WK.
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof gk_ceil_lo as HCL. pose proof asan_consts as (C1 & _). unfold LLVMF_STK in Hsp.
  destruct HERR as (HE0 & HE1).
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (Hd8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, LLVMF_STK in *; lia).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= F + 112 \/ F + 120 <= a) -> sv8 W mem a v ->
      sv8 W mem' a v).
  { intros a v H0 H1 H2 Hv. apply (gk_sv8_kept W W mem mem'); [|exact Hv]. intros x Hx. apply KEEP; lia. }
  assert (Hlen : c_n cx = Z.of_nat (length (c_pl cx))).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf in HPRE. tauto. }
  split; [|split; [apply (gk_amodel_kept B LAWS ly S W mem md W mem' mc HAR HMOD HE0); [unfold GK_CEIL8 in *; lia | exact KL]
                  | exact HSEP]].
  split; [exact HJ'|].
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22).
    split.
    { intros o r Hin. assert (Ho : 8 <= o <= 104).
      { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
      apply KV; [lia | lia | lia | exact (G1 o r Hin)]. }
    split; [intros i Hi; apply WK; exact (G2 i Hi)|].
    do 14 (split; [apply KV; [lia | lia | lia | assumption]|]).
    do 3 (split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | assumption]|]).
    split; [intros i Hi; apply WK; exact (G20 i Hi)|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KL; unfold fake_shadow_open in Hx; cbn [length] in Hx;
                                         unfold GK_CEIL8, SB in *; lia | exact G21]|].
    intros i Hi; apply WK; exact (G22 i Hi). }
  split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | exact HFL]|].
  split; [apply KV; [lia | lia | lia | exact H16]|].
  split; [apply KV; [lia | lia | lia | exact H144]|].
  split; [apply KV; [lia | lia | lia | exact H88]|].
  split; [exact (gk_ainput_kept B LAWS cx ly S W mem md W mem' HAR HIN (eq_sym Hlen) KL)|].
  split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
  exact (gk_jt_kept W W mem mem' HJT KL).
Qed.
Lemma gp5_prefix_keep : forall cx m (W : world segs) mem mem' FF,
  (forall a, FF + 32 <= a < FF + 80 -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  gn_prefix_at cx m W mem FF -> gn_prefix_at cx m W mem' FF.
Proof.
  intros cx m W mem mem' FF K (P1 & P2 & P3 & P4 & P5).
  split; [intros i Hi; rewrite K by lia; exact (P1 i Hi)|].
  split; [rewrite K by lia; exact P2|].
  split; [intros a Ha; rewrite K by lia; exact (P3 a Ha)|].
  split; [exact P4 | exact P5].
Qed.
Definition t0_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 112 120 112 120 [];
    YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))] ].
Definition t0_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 16 0) ] [] [].
Definition ss_t0 : sstate := mkSS AF_gn_t0 sr_atoms t0_regions None t0_facts.
Definition t0_extra (n : Z) : list word := map (Z_to_bv 64) [n].
Lemma gp5_t0_entry : forall (W : world segs) regs mem F n,
  getr regs 9 = w64 F -> getr regs 27 = w64 SB -> 2 ^ 46 <= F -> F + 160 <= 2 ^ 47 -> F mod 32 = 0 ->
  awr W mem F 160 -> 0 <= n <= 16 -> val_mem segs (arm W mem) (rg_nsrc fr_RG) 4 n ->
  st_ok_pi segs VAL (Eimg (Ereg regs (t0_extra n))) ss_t0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_t0)) mem (seg_rom segs))) /\
  sh_ok segs gp5_Bx [] (Eimg (Ereg regs (t0_extra n))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F n R9 R27 HF1 HF2 HF3 HFw Hn Mn. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (t0_extra n))).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (unfold E; rewrite (gp5_EE regs _ 9 9%bv eq_refl); exact R9).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 27 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (EO4 : ew E (A_OBJ 4) = Z_to_bv 64 (rg_nsrc fr_RG))
    by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        destruct gp5_hi as (_ & _ & H & _); rewrite H; reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (UO4 : bv_unsigned (ew E (A_OBJ 4)) = rg_nsrc fr_RG)
    by (rewrite EO4; apply unsigned_lit_small; unfold fr_RG, fr_globals_b; cbn; lia).
  split.
  - unfold ss_t0. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold t0_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor.
      * rewrite UO4. split; [unfold fr_RG, fr_globals_b; cbn; lia|]. split; [unfold fr_RG, fr_globals_b; cbn; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_nsrc fr_RG) 0 4 (SOff 32 0) n);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
        rewrite Z.add_0_r. exact Mn.
    + apply pairwise_disjoint_of_extents. unfold t0_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, UO4.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold fr_RG, fr_globals_b. cbn [rg_nsrc]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [t0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E27, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* the write obligation: the spill cell is inside the function's own stack window *)
Local Ltac gp5_awr_t0 U9 :=
  cbn [ss_mem add_cond ss_t0 t0_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK in *; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the spill cell is outside every region's writable window *)
Local Ltac gp5_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_t0 t0_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.
Definition T0_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 27]%bv.
Lemma gp5_t0 : forall cx t m m1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GT0 B MT G_fr fr_FP LS RINV cx t m m1 W c ->
  SRr segs W c (fun W' c' => ((0 < length (lm_es m1))%nat /\ P5OH cx t m m1 0 W' c') \/
                             (exists mc, GCSD B G_fr fr_FP LS RINV cx t m mc W' c')).
Proof.
  intros cx t m m1 W c HB (regs & mem & md & ly & S3 & kk & fpos & -> & HGS & HDN & HLS0 & HKR & H24 & HAW & HAT & HPF).
  pose proof HGS as ((HJ0 & HFR & _) & HMOD & _).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ0 eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HFR as (_ & HFw & _).
  pose proof asan_consts as (C1 & _). pose proof gk_ceil_lo as HCL. unfold LLVMF_STK in Hsp.
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_t0_entry W regs mem F n R9 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(intros o Ho; apply HFw; lia) ltac:(unfold n; lia) Mn) as (HS & SHOK).
  set (E := Eimg (Ereg regs (t0_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (t0_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (unfold E; rewrite (gp5_EE regs _ 9 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof HJ0 as HJ.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)).
  (* auipc; sd a0,112(s1); lw a0,424(a0), to `blez` *)
  paj_run_tok RUN HS HJ SHOK gp5_span.
  { gp5_awr_t0 U9. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr1 end.
  rename HFr into HFr1. clear HF. rename ms into ms1.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W mem W (ms_mem ms1) a).
  { intros a Ha Hna. split.
    - apply (aview_kept_out _ _ _ _ _ HFr1 a Ha). gp5_nowr U9 Hna.
    - apply (writable_kept (w_H W) mem (ms_mem ms1) a). intros Hp. exact (gp5_pres_grows W _ _ a HGr1 Hp). }
  assert (W1 : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms1)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms1) a); [|exact Hw].
    intros Hp. exact (gp5_pres_grows W _ _ a HGr1 Hp). }
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = n).
  { assert (U32 : U E (SOff 32 0) = n) by (apply U_atom; [exact E32 | unfold n; lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; unfold n; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  (* what both branches build at the end: the loop's state at entry 0, slot 0, `at` = 0 *)
  assert (FIN : forall (ms2 : machine_state) md2,
      ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
        (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S3 W (ms_mem ms2) md2 kk ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W (ms_mem ms1) W (ms_mem ms2) a) ->
      (forall a, writable_at segs (arm W (ms_mem ms1)) a -> writable_at segs (arm W (ms_mem ms2)) a) ->
      sv8 W (ms_mem ms2) (F + 112) gp5_HI79 ->
      p5st cx t m m1 m1 0 0 0 fpos ly S3 W (ms_mem ms2) md2 kk).
  { intros ms2 md2 HJ2 K2 W2 H112.
    assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W mem W (ms_mem ms2) a).
    { intros a Ha Hna. destruct (K1 a Ha Hna) as [V1 X1]. destruct (K2 a Ha Hna) as [V2 X2].
      split; [rewrite V2; exact V1 | intros Hw; exact (X2 (X1 Hw))]. }
    assert (WW : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms2)) a)
      by (intros a Hw; exact (W2 a (W1 a Hw))).
    split; [exact (gp5_gst_keep cx t _ m1 fpos ly S3 W mem (ms_mem ms2) md md2 kk HB HGS HJ2 KK WW)|].
    split; [exact HDN|].
    (* the meter: GT0's at q = 0, where gn_runc starts (gn_runc0) *)
    split; [destruct HLS0 as (lyz & Sz & cz & L1 & L2 & L3 & L4); exists lyz, Sz, cz, 0;
            split; [exact L1|]; split; [exact L2|]; split; [apply gn_runc0|]; split; [exact L3 | exact L4]|].
    split; [apply gn_run0|].
    split; [intros i Hi; apply WW; exact (HAW i Hi)|].
    split; [apply (gk_sv8_kept W W mem (ms_mem ms2)); [intros x Hx; apply KK; lia | exact HAT]|].
    split; [apply (gp5_prefix_keep cx m W mem (ms_mem ms2) FF); [|exact HPF];
            intros a Ha; apply (proj1 (KK a ltac:(lia) ltac:(lia)))|].
    split; [apply (gk_sv8_kept W W mem (ms_mem ms2)); [intros x Hx; apply KK; lia | exact H24] | exact H112]. }
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* g_nsrc <= 0: straight to 0x84c84 *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m1) = 0%nat) by (unfold n in Hc; lia).
    paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr_t0 U9. }
    lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr2 end.
    rename HFr into HFr2. clear HF.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. right. exists m1.
    eapply (gp5_mk_csd cx t m m1 m1 0 fpos ly S3 W _ _ kk); [reflexivity | |].
    + rewrite Hn0. apply FIN; [exact HJ | | |].
      * intros a Ha Hna. split.
        -- apply (aview_kept_out _ _ _ _ _ HFr2 a Ha). gp5_nowr U9 Hna.
        -- apply (writable_kept (w_H W) (ms_mem ms1) _ a). intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      * intros a Hw. apply (writable_kept (w_H W) (ms_mem ms1) _ a); [|exact Hw].
        intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      * unfold sv8, arm.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 112 8%N (SOff (A_HI 79) 0) gp5_HI79 RG0).
        -- exact U9.
        -- left. reflexivity.
        -- apply gp5_sv_U; [|unfold gp5_HI79; lia].
           rewrite (U_img_atom E HEI (A_HI 79)) by (unfold A_HI, A_TEXT, A_LIM; lia). exact (proj1 gp5_hi).
        -- unfold gp5_HI79; zside.
        -- zside.
    + apply (gp5_kregs_tr _ _ _ _ T0_KEPT HKR); [intros r Hr; unfold T0_KEPT; cbn [In] in Hr |- *; tauto | exact KR].
  - (* 0 < g_nsrc: li s7, 0, on to 0x84b8c *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr_t0 U9. }
    lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr2 end.
    rename HFr into HFr2. clear HF.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, m1, 0. split; [reflexivity|].
    split.
    { apply FIN; [exact HJ | | |].
      - intros a Ha Hna. split.
        + apply (aview_kept_out _ _ _ _ _ HFr2 a Ha). gp5_nowr U9 Hna.
        + apply (writable_kept (w_H W) (ms_mem ms1) _ a). intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      - intros a Hw. apply (writable_kept (w_H W) (ms_mem ms1) _ a); [|exact Hw].
        intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      - unfold sv8, arm.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 112 8%N (SOff (A_HI 79) 0) gp5_HI79 RG0).
        + exact U9.
        + left. reflexivity.
        + apply gp5_sv_U; [|unfold gp5_HI79; lia].
          rewrite (U_img_atom E HEI (A_HI 79)) by (unfold A_HI, A_TEXT, A_LIM; lia). exact (proj1 gp5_hi).
        + unfold gp5_HI79; zside.
        + zside. }
    split; [unfold n in Hc; lia|].
    split; [apply (gp5_kregs_tr _ _ _ _ T0_KEPT HKR); [intros r Hr; unfold T0_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite N23. reflexivity.
Qed.

(* the layout's stack bounds along the arm's journal *)
Lemma gp5_ly : forall cx fpos ly3 S3 (W : world segs) mem md k,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  spZ (c_regs cx) <= ly_top ly3 /\ ly_top ly3 <= ly_stk_hi ly3 /\
  ly_stk_lo ly3 + LLVMF_STK <= spZ (c_regs cx) /\ alloc_ceiling <= ly_stk_lo ly3.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil0 & Hslo & Hshi & _ & _ & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & _).
  pose proof HJ0 as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
  rewrite Etop, Elo, Ehi. lia.
Qed.

(* the stack's shadow is zero (W_check_shape_event.v range_addressable_stack, copied) *)
Lemma gp5_ra_stack : forall ly S (W : world segs) mem md a len,
  AR segs B ly S W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
  intros ly S W mem md a len HAR Hlo Hhi Hlen.
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
  pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
  cbn [fst snd] in Hz.
  unfold page_aligned in Hpal, Hpah.
  pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as A. pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as C.
  rewrite Hpal, Z.add_0_r in A. rewrite Hpah, Z.add_0_r in C.
  assert (Hm1 : ly_stk_lo ly mod 8 = 0)
    by (rewrite A; replace (4096 * (ly_stk_lo ly / 4096)) with ((512 * (ly_stk_lo ly / 4096)) * 8) by lia; apply Z_mod_mult).
  assert (Hm2 : (ly_stk_hi ly - ly_stk_lo ly) mod 8 = 0).
  { rewrite A, C. replace (4096 * (ly_stk_hi ly / 4096) - 4096 * (ly_stk_lo ly / 4096))
      with ((512 * (ly_stk_hi ly / 4096) - 512 * (ly_stk_lo ly / 4096)) * 8) by lia. apply Z_mod_mult. }
  eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.

(* the fake frame's prefix area [FF + 32, FF + 80) has zero shadow (gframe's fake_shadow_open) *)
Lemma gp5_ra_fake : forall cx FF (W : world segs) mem a n,
  gframe cx fake_shadow_open FF W mem -> FF mod 8 = 0 -> 0 <= FF ->
  FF + 32 <= a -> a + n <= FF + 80 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros cx FF W mem a n HFR H8 H0 Ha Hn x Hx.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
  set (j := (x - FF) / 8).
  assert (Hj : 4 <= j < 10) by (unfold j; split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  assert (Hx8 : x / 8 = FF / 8 + j).
  { unfold j. pose proof (Z.div_mod FF 8 ltac:(lia)) as D. rewrite H8, Z.add_0_r in D.
    rewrite D at 1. replace (8 * (FF / 8) + (x - 8 * (FF / 8))) with (x) by lia.
    replace x with ((FF / 8) * 8 + (x - FF)) at 1 by lia. rewrite Z.div_add_l by lia. lia. }
  destruct (Hsh (Z.to_nat j) ltac:(cbn; lia)) as [Hv Hr].
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite Hx8.
  replace (SHADOW_OFF + (FF / 8 + j)) with (SB + FF / 8 + Z.of_nat (Z.to_nat j)) by (unfold SB, SHADOW_OFF; lia).
  rewrite (aview_of_val_mem1 segs (w_H W) mem _ _ Hv Hr).
  assert (E : nth (Z.to_nat j) fake_shadow_open 0 = 0).
  { assert (K : forall q, (4 <= q < 10)%nat -> nth q fake_shadow_open 0 = 0)
      by (intros q Hq; do 10 (destruct q as [|q]; [cbn; try lia; reflexivity|]); lia).
    apply K. lia. }
  rewrite E. reflexivity.
Qed.

(* the three literals check_no_loss reads, from the read-only image *)
Definition gp5_romb (a : Z) (l : list Z) : bool :=
  forallb (fun j => gp5_inromb (a + Z.of_nat j) &&
    (match seg_rom segs (Z_to_bv 64 (a + Z.of_nat j)) with
     | Some b => bv_unsigned b =? nth j l 0 | None => false end) && (0 <=? nth j l 0) && (nth j l 0 <? 256))%bool
    (seq 0 (length l)).
Lemma gp5_lit : forall (W : world segs) mem a l, rom_view segs W mem -> gp5_romb a l = true ->
  garr8 segs (arm W mem) a l.
Proof.
  intros W mem a l HRV H j Hj. unfold gp5_romb in H. rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  pose proof (gp5_inromb_ok _ H1) as Hrom. pose proof (HRV _ Hrom) as Hv.
  destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat j))) as [b|] eqn:Eb; [|discriminate H2].
  apply Z.eqb_eq in H2. split; [|lia].
  intros q Hq. replace q with 0%nat by lia. rewrite Z.add_0_r.
  unfold aview in Hv. cbn [option_map] in Hv.
  unfold arm. destruct (mbyte segs (mrestrict (w_H W) mem) (a + Z.of_nat j)) as [b'|] eqn:Eb'; [|discriminate Hv].
  injection Hv as Hv. f_equal. apply bv_eq. rewrite Hv, H2.
  rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity.
Qed.
Lemma gp5_lits : forall (W : world segs) mem, rom_view segs W mem ->
  garr8 segs (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE /\
  garr8 segs (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN /\
  garr8 segs (arm W mem) (VAL A_lit_end) RelayModel.W_END.
Proof.
  intros W mem HRV. split; [|split]; apply gp5_lit; try exact HRV; vm_compute; reflexivity.
Qed.
(* B: check_shape_ends' " end" (.str.4 at A_OBJ 28), as its cshe_spec premise states it *)
Lemma gp5_lit_end5 : forall (W : world segs) mem, rom_view segs W mem ->
  garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5).
Proof. intros W mem HRV. apply gp5_lit; [exact HRV | vm_compute; reflexivity]. Qed.

(* ---- ends_run and the filter: the dropped records and the kept ones are the held list's ---- *)
Lemma gp5_find_text_lt : forall y rs i, CheckRep.find_text y rs = Some i -> (i < length rs)%nat.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i H; cbn [CheckRep.find_text] in H; [discriminate H|].
  destruct (list_eqb (bzs (snd r)) (bzs y)); [injection H as <-; cbn; lia|].
  destruct (CheckRep.find_text y rs) as [i'|] eqn:E; cbn in H; [|discriminate H].
  injection H as <-. specialize (IH i' eq_refl). cbn. lia.
Qed.
Lemma gp5_skipn_nth : forall (A : Type) (l : list A) i d, (i < length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros A l. induction l as [|x l IH]; intros i d Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma gp5_drop_perm : forall (rs : list (Z * list byte)) i, (i < length rs)%nat ->
  Permutation rs (nth i rs (0, []) :: CheckRep.drop_nth i rs).
Proof.
  intros rs i Hi. unfold CheckRep.drop_nth.
  rewrite <- (firstn_skipn i rs) at 1.
  rewrite (gp5_skipn_nth _ rs i (0, [])) by exact Hi.
  apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma gp5_ends_perm : forall P w rs d rs' ds c,
  CheckRep.ends_run P rs d w = Some (rs', ds, c) -> Permutation rs (ds ++ rs').
Proof.
  intros P w. induction w as [|w IH]; intros rs d rs' ds c H; cbn [CheckRep.ends_run] in H.
  - injection H as <- <- <-. reflexivity.
  - destruct (CheckRep.split_nul d) as [[l d']|]; [|discriminate H].
    destruct (_ && _)%bool; [|discriminate H].
    destruct (CheckRep.find_text _ rs) as [i|] eqn:Ef; [|discriminate H].
    destruct (CheckRep.ends_run P (CheckRep.drop_nth i rs) d' w) as [[[rs1 ds1] c1]|] eqn:Er; [|discriminate H].
    injection H as <- <- <-.
    eapply Permutation_trans; [exact (gp5_drop_perm rs i (gp5_find_text_lt _ _ _ Ef))|].
    cbn [app]. apply perm_skip. exact (IH _ _ _ _ _ Er).
Qed.
Lemma gp5_filter_perm : forall (A : Type) (g : A -> bool) (l : list A),
  Permutation l (filter (fun x => g x) l ++ filter (fun x => negb (g x)) l).
Proof.
  intros A g l. induction l as [|x l IH]; [reflexivity|].
  destruct (g x) eqn:E.
  - rewrite (list_basics.list.filter_cons_True (fun x => g x)) by (rewrite E; exact I).
    rewrite (list_basics.list.filter_cons_False (fun x => negb (g x))) by (rewrite E; intros X; exact X).
    cbn [app]. apply perm_skip. exact IH.
  - rewrite (list_basics.list.filter_cons_False (fun x => g x)) by (rewrite E; intros X; exact X).
    rewrite (list_basics.list.filter_cons_True (fun x => negb (g x))) by (rewrite E; exact I).
    eapply Permutation_trans; [apply perm_skip; exact IH|]. apply Permutation_middle.
Qed.
(* ================================================================== the two calls, 0x84c0c -> 0x84c28 *)
Definition ca_facts : facts := mkFacts [ (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_ca (pc : Z) : sstate := mkSS pc sr_atoms [] None ca_facts.
Lemma gp5_ca_entry : forall (W : world segs) regs mem pc,
  getr regs 27 = w64 SB ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) (ss_ca pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs))) /\
  sh_ok segs gp5_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem pc R27. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs [])).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 27 27%bv eq_refl); exact R27).
  split.
  - unfold ss_ca. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [ca_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E27, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* the registers the three instructions before check_no_loss do not write (a0, a1, ra) *)
Definition CA1_KEPT : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* the registers the four instructions before check_shape_ends do not write (a0, a1, a2, ra) *)
Definition CA2_KEPT : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* a concrete register is callee-saved *)
Ltac gp5_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* a callee-saved register across a call *)
Lemma gp5_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma gp5_regs_call : forall cx FF i k (regs r1 r2 : bvmap 5 word) (KL : list (bv 5)),
  gn_kregs B cx FF regs -> gp5_ih_regs i k regs ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> In r KL) ->
  (forall r, In r KL -> getr r1 r = getr regs r) -> aregs_preserved r1 r2 ->
  gn_kregs B cx FF r2 /\ gp5_ih_regs i k r2.
Proof.
  intros cx FF i k regs r1 r2 KL HR HIR HKL KR HP.
  assert (K : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
      getr r2 r = getr regs r).
  { intros r Hr. rewrite (gp5_pres r1 r2 r HP); [apply KR, HKL, Hr|].
    cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [gp5_cs|]). destruct Hr. }
  destruct HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  destruct HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  split; (repeat split); (rewrite K by (cbv; tauto); assumption).
Qed.
(* slot k's blocks are not g_out's block *)
Lemma gp5_lb_fst : forall l x, In x (list_blocks l) -> exists b, In b (alist_blks l) /\ fst b = x.
Proof.
  intros l x H. unfold list_blocks, alist_blks in *. apply in_app_or in H as [H|H].
  - destruct (Z.eqb (hl_cap l) 0); [destruct H|]. destruct H as [<- | []].
    exists (hl_v l, AREC * hl_cap l). split; [apply in_or_app; left; left; reflexivity | reflexivity].
  - apply in_map_iff in H as (r & <- & Hr). exists (fst r, Z.of_nat (length (snd r)) + 1).
    split; [apply in_or_app; right; apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hr | reflexivity].
Qed.
Lemma gp5_hsb_fst : forall h x, In x (hs_blocks h) -> exists b, In b (asrc_blks h) /\ fst b = x.
Proof.
  intros h x H. unfold hs_blocks in H. unfold asrc_blks.
  apply in_app_or in H as [H|H]; [|apply in_app_or in H as [H|H]; [|apply in_app_or in H as [H|H]]].
  - destruct (gp5_lb_fst _ _ H) as (b & Hb & Hf). exists b. split; [right; apply in_or_app; left; exact Hb | exact Hf].
  - destruct H as [<- | []]. exists (hs_partial h, APARTIAL). split; [left; reflexivity | reflexivity].
  - destruct (gp5_lb_fst _ _ H) as (b & Hb & Hf). exists b.
    split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hf].
  - destruct (gp5_lb_fst _ _ H) as (b & Hb & Hf). exists b.
    split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hf].
Qed.
Lemma gp5_out_apart : forall cx mc k h ly S (W : world segs) mem md rest0,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (input_blks cx ++ model_blks mc ++ rest0) ->
  nth k (lm_hs mc) None = Some h -> 0 < lm_cap mc ->
  ~ In (lm_out mc) (hs_blocks h).
Proof.
  intros cx mc k h ly S W mem md rest0 HAR HPM Hk Hc Hin.
  destruct (gp5_hsb_fst h _ Hin) as ([p n] & Hb & Hf). cbn [fst] in Hf. subst p.
  pose proof (gp5_nodup ly S W mem md HAR) as HND.
  pose proof (gp5_model_perm mc k h Hk) as HMP.
  assert (P : Permutation (ablocks B ly S) (input_blks cx ++ (asrc_blks h ++ gp5_mrest mc k) ++ rest0))
    by exact (Permutation_trans HPM (Permutation_app_head _ (Permutation_app_tail _ HMP))).
  assert (HND2 : List.NoDup (input_blks cx ++ (asrc_blks h ++ gp5_mrest mc k) ++ rest0))
    by (eapply Permutation_NoDup; [exact P | exact HND]).
  assert (Ho : In (lm_out mc, lm_cap mc) (gp5_mrest mc k)).
  { unfold gp5_mrest. right. apply in_or_app. right. apply in_or_app. right. unfold aout_blks.
    destruct (Z.eqb_spec (lm_cap mc) 0); [lia | left; reflexivity]. }
  assert (Hne : (lm_out mc, n) <> (lm_out mc, lm_cap mc)).
  { intros E. apply List.NoDup_app_remove_l in HND2. apply List.NoDup_app_remove_r in HND2.
    rewrite E in Hb. exact (gp5_nodup_app _ _ _ _ HND2 Hb Ho). }
  assert (I1 : In (lm_out mc, n) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. right. apply in_or_app. left.
    apply in_or_app. left. exact Hb. }
  assert (I2 : In (lm_out mc, lm_cap mc) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. right. apply in_or_app. left.
    apply in_or_app. right. exact Ho. }
  pose proof (sep_blocks segs B LAWS ly S W mem md _ _ _ _ HAR I1 I2 Hne) as Hd.
  destruct (gp5_blk ly S W mem md _ _ HAR I1) as (_ & _ & Hn1).
  destruct (gp5_blk ly S W mem md _ _ HAR I2) as (_ & _ & Hn2).
  pose proof (req_size_pos n ltac:(lia)) as [Q1 _]. pose proof (req_size_pos (lm_cap mc) ltac:(lia)) as [Q2 _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* check_shape_ends drops some of the held records and keeps the rest *)
Lemma gp5_held_perm : forall (H H2 : hlist) ds,
  hl_v H2 = hl_v H -> hl_cap H2 = hl_cap H -> Permutation (hl_recs H) (ds ++ hl_recs H2) ->
  Permutation (alist_blks H) (cshe_ds_blks ds ++ alist_blks H2).
Proof.
  intros H H2 ds Hv Hc HP. unfold alist_blks, cshe_ds_blks. rewrite Hv, Hc.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_map; exact HP|].
  rewrite map_app. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma gp5_cshe_perm : forall P gone A0 (ob : list byte) (H H2 : hlist) ds c,
  ((gone <> 0 /\ hl_recs H2 = filter (fun r => negb (prefixb P (snd r))) (hl_recs H) /\
    ds = filter (fun r => prefixb P (snd r)) (hl_recs H) /\ c = 0) \/
   (gone = 0 /\ CheckRep.ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H))
      = Some (hl_recs H2, ds, c))) ->
  Permutation (hl_recs H) (ds ++ hl_recs H2).
Proof.
  intros P gone A0 ob H H2 ds c [(_ & E1 & E2 & _) | (_ & E)].
  - rewrite E1, E2. exact (gp5_filter_perm _ (fun r => prefixb P (snd r)) (hl_recs H)).
  - exact (gp5_ends_perm _ _ _ _ _ _ _ E).
Qed.

(* g_out's facts check_no_loss and check_shape_ends read *)
Lemma gp5_aout_pre : forall cx mc k h ly S (W : world segs) mem md rest0,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (input_blks cx ++ model_blks mc ++ rest0) ->
  nth k (lm_hs mc) None = Some h ->
  aout_at B fr_RG ly S W mem (lm_c mc) (lm_O mc) (lm_mx mc) (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc) ->
  ob_at W mem (lm_out mc) (lm_O mc) /\ amem_range (lm_out mc) (Z.of_nat (length (lm_O mc)) + 8) /\
  (lm_O mc = [] \/ exists CO, Z.of_nat (length (lm_O mc)) <= CO /\ In (lm_out mc, CO) (ablocks B ly S) /\
     ~ In (lm_out mc) (hs_blocks h)).
Proof.
  intros cx mc k h ly S W mem md rest0 HAR HPM Hk HO.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hblk as [(Hc0 & Ho0 & Hn0) | (Hcp & Hno & Hin & junk & Hjk & Hg)].
  - assert (E : lm_O mc = []) by (destruct (lm_O mc); [reflexivity | cbn in Hn0; lia]).
    rewrite E, Ho0. split; [intros j Hj; cbn in Hj; lia|]. split; [unfold amem_range; left; cbn; lia|].
    left; reflexivity.
  - split.
    + intros j Hj.
      assert (Hjl : (Z.to_nat j < length (bzs (lm_O mc ++ junk)))%nat)
        by (unfold bzs; rewrite length_map, length_app; lia).
      destruct (Hg _ Hjl) as [Hv Hr]. unfold arm in Hv.
      rewrite (Z2Nat.id j ltac:(lia)) in Hv.
      rewrite (aview_of_val_mem1 segs (w_H W) mem _ _ Hv Hr).
      rewrite gp5_nth_bzs, app_nth1 by lia. reflexivity.
    + destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & P2 & P3 & _).
      unfold req_size in P2, P3. destruct (Z.eqb_spec (lm_cap mc) 0) as [Hc|Hc]; [lia|].
      split.
      * unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
      * right. exists (lm_cap mc). split; [lia|]. split; [exact Hin|].
        exact (gp5_out_apart cx mc k h ly S W mem md rest0 HAR HPM Hk Hcp).
Qed.
(* the held list's blocks lie below alloc_ceiling (heap blocks) *)
Lemma gp5_held_low : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h ->
  (forall a, hl_v (hs_held h) <= a < hl_v (hs_held h) + AREC * hl_cap (hs_held h) -> a < alloc_ceiling) /\
  (forall r, In r (hl_recs (hs_held h)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
     a < alloc_ceiling).
Proof.
  intros ly S W mem md HA h HAR HS.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hheld & _).
  destruct Hheld as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  split.
  - intros a Ha. destruct H6 as [(Hc0 & _) | (Hcp & Hin & _)]; [rewrite Hc0 in Ha; lia|].
    destruct (gp5_blk ly S W mem md _ _ HAR Hin) as (_ & P2 & P3). lia.
  - intros r Hr a Ha. rewrite Forall_forall in H9. destruct (H9 r Hr) as (Hin & _).
    destruct (gp5_blk ly S W mem md _ _ HAR Hin) as (_ & P2 & P3). lia.
Qed.
Lemma gp5_perm_held : forall (x : Z * Z) a b c d e, Permutation c (d ++ e) ->
  Permutation (x :: a ++ b ++ c) (d ++ x :: a ++ b ++ e).
Proof.
  intros x a b c d e H.
  eapply Permutation_trans; [apply perm_skip; apply Permutation_app_head; apply Permutation_app_head; exact H|].
  replace (x :: a ++ b ++ d ++ e) with ((x :: a ++ b) ++ d ++ e) by (cbn; rewrite <- !app_assoc; reflexivity).
  replace (d ++ x :: a ++ b ++ e) with (d ++ (x :: a ++ b) ++ e) by (cbn; rewrite <- !app_assoc; reflexivity).
  apply Permutation_app_swap_app.
Qed.
Lemma gp5_set_set : forall mc k x y, gn_set (gn_set mc k x) k y = gn_set mc k y.
Proof. intros mc k x y. unfold gn_set. cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  rewrite gp5_setn_setn. reflexivity. Qed.

End gp5.
