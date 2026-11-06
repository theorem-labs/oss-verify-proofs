(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths and names changed, the cell rows are this unit's AsanCells rows, and the read-only-image helper is dropped. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths and module names changed; 1109 of its 1232 lines of code are new or changed and 398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_uci's check_value in image A, proving the frozen statement
   lib/A/Prog/check_value_cg.v uci_check_value_cg_holds_stmt, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/
   crtA_walk.v, crtA_w_head.v, crtA_w_tail.v, crtA_encw.v, crtA_w_mid.v and crtA_close.v (origin/ossv/recipes
   88154566652a): footprint runs carried into SRr, an inner journal over the call's stack window, each call cut by its
   callee contract, and the helpers of those files (crtA_run, crtA_ms_shape, crtA_ms_reg, crtT_regs_of, crtA_trace0,
   crtT_chain_nil, crtA_byte_eq, crtT_rw_cells_ext, crtA_rng_vis, crtT_aj_md, crtT_not_old, crtT_perm_rm,
   crtA_addressable, crtA_rng_hull, crtA_vis_hull) restated at this unit's image. *)
(* check_value_cgW: uci_check_value_cg (uci_sigma US_check_value) from the callee contracts the statement names.

   The walk (offsets from the entry; lib/A/Prog/UciCvIface.v names the cut points):
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init): stack window [spZ regs - CV_STK, spZ regs),
        no footprint, no frame of its own;
     2. cv_seg1_F (lib/A/Prog/UciCvSegs.v): the 0x40-byte frame, the shadow offset, a0 = n + (n == 0); the inner
        journal follows the frame write (YCbq.v ajournal_exec);
     3. malloc (YC5d.v amalloc04_rule): the chain is empty, s0 = cur is an int (YG00.v bad_next), the trace is
        uci_cv_ufix's first;
     4. n > 0: cv_seg2p_F, __asan_memcpy(P, r, n) (YCbq.v aj_intrin_at: P is the call's new block, r lies in a block
        of the caller, the two are disjoint), cv_seg3_F, rp_uci_int(P, n, cur) (rp_uci_int_cg.v contract; the
        journal follows by YCbq.v ajournal_after_write over its stack window), then the inlined expected_value
        (UciCvIface.v cv_ev_stmt_F over the reply r, read through the journal's kept caller blocks) and cv_test_F;
        n = 0: cv_seg2z_F, rp_uci_int(P, 0, cur), cv_segz_F, cv_test_F;
        the property test is not taken: rp_uci_int_m = expected_value_m (lib/Spec/UciModel.v uci_value_ok);
     5. free(P) (YC5d.v afree04_rule): empty chain, uci_cv_ufix's second trace;
     6. cv_end_F: a0 := s2, the frame reloaded, `ret` to the caller's ra (YK0s.v ret_ok);
     7. the post: the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciPSyms UciPAddr UciCg check_value_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciCvIface UciCvSegs.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue UciPImg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require rp_uci_int_cg UciCvEvA UciCvEvB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_uci_int_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Img0.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_uci_int_cg.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_uci_int_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers                                                         *)
(* ======================================================================== *)

Lemma cv_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact UciPImg.uci_segs_low. Qed.

Lemma cv_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

(* The allocator's trace at a call (YCbq.v call_trace0) is UciCg.v's uci_utrace of the return address followed by
   the chain's return addresses (crtA_w_head.v crtA_trace0). *)
Lemma cv_trace0 : forall pc0 regs ch, call_trace0 pc0 regs ch = uci_utrace pc0 (raZ regs :: spine ch).
Proof.
  intros pc0 regs ch. unfold call_trace0, unwind_of_chain, uci_utrace.
  assert (E : flat_map (fun ra : Z => if ra =? pc0 then [] else [ra]) (raZ regs :: spine ch) =
              flat_map (fun r : Z * Z * Z => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end)
                ((spZ regs, raZ regs, s0Z regs) :: ch)).
  { cbn [flat_map]. f_equal. unfold spine. induction ch as [|[[fp ra] nfp] ch IH]; [reflexivity|].
    cbn [flat_map map fst snd]. rewrite IH. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* A frame pointer at or below sp, or at or above the stack top, ends the chain (YG00.v bad_next). *)
Lemma cv_chain_nil : forall ly rd (regsT : bvmap 5 word),
  4096 <= raZ regsT -> (s0Z regsT <= spZ regsT \/ ly_top ly - 16 <= s0Z regsT) -> chain_pre ly rd regsT [].
Proof.
  intros ly rd regsT Hra Hs. unfold chain_pre. split; [exact Hra|].
  destruct (frame0_ok ly regsT); [|reflexivity].
  unfold bad_next. destruct Hs as [Hs|Hs].
  - rewrite (proj2 (Z.leb_le _ _) Hs). reflexivity.
  - rewrite (proj2 (Z.leb_le _ _) Hs), Bool.orb_true_r. reflexivity.
Qed.

(* An int held in a word, read back, is at or below an sp above 2^31, or at or above 2^64 - 2^31. *)
Lemma cv_int_word : forall v, INT_MIN <= v <= INT_MAX ->
  (0 <= v /\ v mod 2 ^ 64 = v) \/ (v < 0 /\ v mod 2 ^ 64 = v + 2 ^ 64).
Proof.
  intros v Hv. unfold INT_MIN, INT_MAX in Hv. destruct (Z_le_gt_dec 0 v) as [H|H].
  - left. split; [lia|]. apply Z.mod_small. lia.
  - right. split; [lia|]. rewrite <- (Z.mod_add v 1 (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma cv_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma cv_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells AImg.rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells AImg.rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wl & Hw)] He.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
    assert (Hi' : A <= A + Z.of_nat i < A + Z.of_nat (cells_size cs)) by (rewrite <- L; lia).
    unfold mrd. rewrite (He _ Hi'). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wl|]. intros i Hi.
    unfold wview. rewrite (He (A + i)) by lia. exact (Hw i Hi).
Qed.

(* A range of visible bytes is in the walk's footprint (crtA_w_head.v crtA_rng_vis). *)
Lemma cv_rng_vis : forall (W : world tfibsegs) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) a n.
Proof.
  intros W a n H0 H1 Hv. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj. unfold LCK.RNG_W, LCK.range_avoids. intros kk Hk. unfold LCK.woff.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply cv_u64; lia).
  rewrite Ub. replace (b + Z.of_nat kk) with (a + (b + Z.of_nat kk - a)) by lia. apply Hv. lia.
Qed.

Lemma cv_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (crtA_walk.v crtA_run, with the bridge of
   lib/A/Prog/LeafCgFacts.v): the walk continues from every state the transported run can reach. *)
Lemma cv_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF AImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv AImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cv_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

(* A state register-equivalent to an MS form with the cgif float state is that cgif state (crtA_ms_shape). *)
Lemma cv_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma cv_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

(* The registers of a state register-equivalent to an `mkR` state (crtA_w_tail.v crtT_regs_of). *)
Lemma cv_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 1) = x1 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 2) = x2 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 3) = x3 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 4) = x4 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 8) = x8 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 9) = x9 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 10) = x10 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 11) = x11 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 12) = x12 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 18) = x18 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 19) = x19 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 20) = x20 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 21) = x21 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 22) = x22 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 23) = x23 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 24) = x24 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 25) = x25 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 26) = x26 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 27) = x27.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (cv_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma cv_perm_dup : forall {X : Type} (l rest : list X) (x : X),
  Permutation l (x :: rest) -> In x rest -> exists l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
  intros X l rest x HP Hin.
  assert (Hx : In x l) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  apply in_split in Hx as (a & b & ->).
  assert (HP2 : Permutation rest (a ++ b)) by (eapply Permutation_cons_app_inv; apply Permutation_sym; exact HP).
  pose proof (Permutation_in _ HP2 Hin) as Hin2.
  apply in_app_or in Hin2 as [Ha | Hb].
  - apply in_split in Ha as (c & d & ->). exists c, d, b. rewrite <- app_assoc. reflexivity.
  - apply in_split in Hb as (c & d & ->). exists a, c, d. reflexivity.
Qed.

(* The return addresses of the calls: values, parity, and the trace names of the statement. *)
Lemma cv_ra_malloc : bv_unsigned (Z_to_bv 64 CV_RET_MALLOC) = UCI_CV_RA_MALLOC /\
  bv_unsigned (Z_to_bv 64 CV_RET_MALLOC) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 CV_RET_MALLOC).
Proof. split; [|split]; vm_compute; first [reflexivity | discriminate]. Qed.
Lemma cv_ra_free : bv_unsigned (Z_to_bv 64 CV_RET_FREE) = UCI_CV_RA_FREE /\
  bv_unsigned (Z_to_bv 64 CV_RET_FREE) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 CV_RET_FREE).
Proof. split; [|split]; vm_compute; first [reflexivity | discriminate]. Qed.
Lemma cv_ra_even : forall o, In o [0x5c; 0x6c; 0xb8] ->
  bv_unsigned (Z_to_bv 64 (CV_AT o)) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 (CV_AT o)) /\
  bv_unsigned (Z_to_bv 64 (CV_AT o)) = CV_AT o.
Proof.
  intros o Ho. cbn [In] in Ho.
  destruct Ho as [<- | [<- | [<- | []]]]; (split; [|split]); vm_compute; first [reflexivity | discriminate].
Qed.


(* RNG_W W holds on a range of bytes the world does not hide (crtA_encw.v crtA_rng). *)
Lemma cv_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (cv_u64 b) by lia. apply H. lia.
Qed.

(* ---- aview at this image (crtA_encw.v crtA_aview_vis, crtA_aview_mrd, crtA_aview_some) ---- *)

Lemma cv_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma cv_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd AImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma cv_mrd_of_aview : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> mrd AImg.rsegs mem (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v E. pose proof (cv_aview_vis W mem a v E) as Hv.
  rewrite (cv_aview_mrd W mem a Hv) in E.
  destruct (mrd AImg.rsegs mem (wa a)) as [b|]; cbn in E; [|discriminate].
  injection E as E. subst v. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

Lemma cv_present_vis : forall (W : world tfibsegs) m a, apresent (w_H W) m a -> aview tfibsegs (w_H W) m a <> None.
Proof.
  intros W m a (Hh & b & Hb). rewrite (cv_aview_mrd W m a Hh). unfold mrd, wa. rewrite Hb. discriminate.
Qed.

(* ---- garr8 against aview ---- *)

Lemma cv_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma cv_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (cv_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cv_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (cv_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The reply bytes as numbers (lib/Prog/check_value.v zbytes_rng). *)
Lemma cv_zbytes_rng : forall bs i, 0 <= nthz (PRc.zbytes bs) i < 256.
Proof.
  intros bs i. unfold nthz, PRc.zbytes.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length (map (@bv_unsigned 8) bs))) as [Hl|Hl].
  - pose proof (nth_In (map (@bv_unsigned 8) bs) 0 Hl) as Hin.
    apply in_map_iff in Hin as (x & Ex & _). rewrite <- Ex.
    pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. cbn in R. lia.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

Lemma cv_perm_rm : forall {X : Type} (l1 l2 rest : list X) (x : X),
  Permutation (l1 ++ x :: l2) (x :: rest) -> Permutation (l1 ++ l2) rest.
Proof.
  intros X l1 l2 rest x H. apply Permutation_sym. eapply Permutation_cons_app_inv. apply Permutation_sym. exact H.
Qed.

Lemma cv_rom_img : forall a, in_rom tfibsegs a -> in_img tfibsegs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

(* ---- the runtime cells (crtA_cells.v, at this image's uci_seg_covers) ---- *)

Lemma cv_find_none : forall (l : list Segment) addr n s,
  find_segment l addr n = None -> In s l ->
  Z.of_N (seg_base s) <= addr -> addr + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s) -> False.
Proof.
  induction l as [|s0 l IH]; intros addr n s Hf Hin H1 H2; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s0)) addr && Z.leb (addr + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%Z
    eqn:E; [discriminate|].
  destruct Hin as [<- | Hin].
  - apply andb_false_iff in E as [E | E]; apply Z.leb_gt in E; lia.
  - exact (IH addr n s Hf Hin H1 H2).
Qed.

Lemma cv_covers_visible : forall (hd : word -> bool) a n i,
  H_off_segments tfibsegs hd -> uci_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 ->
  hd (Z_to_bv 64 (a + i)) = false.
Proof.
  intros hd a n i Hoff Hc Hi Ht.
  unfold uci_seg_covers in Hc. apply existsb_exists in Hc as (s & Hs & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  destruct (hd (Z_to_bv 64 (a + i))) eqn:E; [exfalso | reflexivity].
  pose proof (Hoff _ E) as E2.
  rewrite (cv_u64 (a + i)) in E2 by lia.
  exact (cv_find_none tfibsegs (a + i) 1 s E2 Hs ltac:(lia) ltac:(lia)).
Qed.

Lemma cv_covers_lo : forall a n, uci_seg_covers a n = true -> 0 <= a.
Proof.
  intros a n Hc. unfold uci_seg_covers in Hc. apply existsb_exists in Hc as (s & _ & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 _]. apply Z.leb_le in H1.
  pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Lemma cv_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma cv_byte_mod : forall z n k, 0 <= k -> k + 8 <= n ->
  Z.shiftr (z mod 2 ^ n) k mod 256 = Z.shiftr z k mod 256.
Proof.
  intros z n k Hk Hn. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i 8) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma cv_mod_pow2_mod : forall v n m, 0 <= n <= m -> (v mod 2 ^ m) mod 2 ^ n = v mod 2 ^ n.
Proof.
  intros v n m Hnm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i n) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma cv_le_byte : forall (w k : nat) z v, (k < w)%nat ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (Z_to_le_bytes w z) k) = Some (le_byte v w k).
Proof.
  intros w k z v Hk Hm. rewrite cv_nth_le_bytes by exact Hk. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold le_byte. rewrite <- Hm. symmetry. apply cv_byte_mod; lia.
Qed.

Lemma cv_wa_mod : forall v (w : nat), (w <= 8)%nat ->
  bv_unsigned (wa v) mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros v w Hw. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply cv_mod_pow2_mod. change (Z.of_N 64) with 64. lia.
Qed.

Lemma cv_le8_byte : forall v k, (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (le8 (wa v)) k) = Some (le_byte v 8 k).
Proof.
  intros v k Hk. unfold le8, word_to_le_bytes.
  apply cv_le_byte; [exact Hk | apply cv_wa_mod; lia].
Qed.

Lemma cv_opt_byte_eq : forall (x y : option byte) z,
  option_map (fun b : byte => bv_unsigned b) x = Some z ->
  option_map (fun b : byte => bv_unsigned b) y = Some z -> x = y.
Proof.
  intros [x|] [y|] z Hx Hy; cbn in Hx, Hy; try discriminate.
  injection Hx as Hx. injection Hy as Hy. f_equal. apply bv_eq. congruence.
Qed.

Section Cells.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* One constant cell of B at a numeral address in a loaded segment is bytes_at under mrd (crtA_cells.v
   crt_cell_bytes, crt_z8). *)
Lemma cv_cell_bytes : forall ly (hd : word -> bool) mem a v (w : nat) (bs : list byte),
  H_off_segments tfibsegs hd ->
  cell_holds B ly (aview tfibsegs hd mem) (ACell (ANum a) w (AV (ANum v))) ->
  uci_seg_covers a (Z.of_nat w) = true -> a + Z.of_nat w <= 2 ^ 64 ->
  length bs = w ->
  (forall k, (k < w)%nat -> option_map (fun b : byte => bv_unsigned b) (nth_error bs k) = Some (le_byte v w k)) ->
  bytes_at AImg.rsegs mem a bs.
Proof.
  intros ly hd mem a v w bs Hoff Hc Hcov Htop Hlen Henc.
  unfold cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  unfold bytes_at.
  split; [exact (cv_covers_lo a (Z.of_nat w) Hcov)|].
  split; [rewrite Hlen; exact Htop|].
  intros i Hi. rewrite Hlen in Hi.
  assert (Hv : hd (Z_to_bv 64 (a + Z.of_nat i)) = false)
    by (apply (cv_covers_visible hd a (Z.of_nat w) (Z.of_nat i) Hoff Hcov); lia).
  assert (Erd : mrd AImg.rsegs mem (wa (a + Z.of_nat i)) =
                YP09.mbyte tfibsegs (mrestrict hd mem) (a + Z.of_nat i)).
  { unfold mrd, wa, YP09.mbyte, mrestrict. rewrite Hv. reflexivity. }
  rewrite Erd. apply (cv_opt_byte_eq _ _ (le_byte v w i)); [exact (Hc i Hi) | exact (Henc i Hi)].
Qed.

Lemma cv_z8 : forall ly (hd : word -> bool) mem a v,
  H_off_segments tfibsegs hd ->
  Forall (cell_holds B ly (aview tfibsegs hd mem)) (as_const B ly) ->
  In (z8 (ANum a) v) (as_const B ly) -> uci_seg_covers a 8 = true -> a + 8 <= 2 ^ 64 ->
  bytes_at AImg.rsegs mem a (le8 (wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (cv_cell_bytes ly hd mem a v 8 (le8 (wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (length_le8 _) (cv_le8_byte v)).
Qed.

(* The two runtime cells check_value reads (the GOT word of the shadow base, and the shadow base). *)
Lemma cv_cells2 : uci_cells B ->
  forall ly S (W : world tfibsegs) mem md, @AR rc tfibsegs B ly S W mem md ->
  bytes_at AImg.rsegs mem AC.GOT_CELL_K (le8 (wa AC.CELL_K)) /\ bytes_at AImg.rsegs mem AC.CELL_K (le8 (wa AC.ASAN_K)).
Proof.
  intros HC ly S W mem md HAR.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) by (eapply am_const; exact HM).
  destruct (HC ly) as (C1 & C2 & _).
  split.
  - apply (cv_z8 ly _ mem AC.GOT_CELL_K AC.CELL_K (w_Hoff W) HK C2); vm_compute; first [reflexivity | discriminate].
  - apply (cv_z8 ly _ mem AC.CELL_K AC.ASAN_K (w_Hoff W) HK C1); vm_compute; first [reflexivity | discriminate].
Qed.
End Cells.

(* ---- shadow and addressability of a block range (crtA_encw.v crtA_addressable, crtA_rng_hull) ---- *)

Lemma cv_byte_signed : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma cv_addressable {rc : YM05.RunCeil} : forall (W : world tfibsegs) mem p n,
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n -> 0 <= n ->
  4096 <= p /\ (p + n <= kLowShadowBeg \/ kHighMemBeg <= p /\ p + n <= ASAN_CEIL) ->
  AC.addressable mem p n.
Proof.
  intros W mem p n HA Hn Happ. pose proof ASAN_CEIL_range as [CR _].
  split; [lia|]. split; [exact Hn|].
  split; [unfold AC.APPMEM_END, kLowShadowBeg, kHighMemBeg in *; lia|].
  intros i Hi. split.
  - unfold AC.app_mem, AC.LOWMEM_END, AC.HIGHMEM_BEG, AC.APPMEM_END, kLowShadowBeg, kHighMemBeg in *. lia.
  - destruct (HA (p + i) ltac:(lia)) as (s & Hs & Hok).
    pose proof (cv_mrd_of_aview W mem _ s Hs) as Hb.
    exists (Z_to_bv 8 s). split.
    + replace (AC.shadow_addr (p + i)) with (shadow_of_addr SHADOW_OFF (p + i))
        by (unfold AC.shadow_addr, shadow_of_addr, AC.ASAN_K, SHADOW_OFF; lia).
      exact Hb.
    + unfold saddr_ok in Hok. unfold AC.shadow_ok.
      assert (Us : bv_unsigned (Z_to_bv 8 s) = s).
      { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
      rewrite cv_byte_signed by lia. rewrite Us. lia.
Qed.

Lemma cv_shadow_addr_eq : forall a, AC.shadow_addr a = YG0f.shadow_addr a.
Proof. intros a. unfold AC.shadow_addr, YG0f.shadow_addr, AC.ASAN_K, SHADOW_OFF. lia. Qed.

Lemma cv_rng_hull : forall (W : world tfibsegs) mem x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 48 ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x n ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (AC.shadow_addr x / 8 * 8)
    (AC.shadow_addr (x + n - 1) / 8 * 8 + 8 - AC.shadow_addr x / 8 * 8).
Proof.
  intros W mem x n H0 Hn H1 H. rewrite !cv_shadow_addr_eq.
  assert (B1 : 0 <= YG0f.shadow_addr x / 8 * 8) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  assert (B2 : YG0f.shadow_addr x / 8 * 8 <= YG0f.shadow_addr (x + n - 1) / 8 * 8)
    by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
        unfold YG0f.shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (B3 : YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 <= 2 ^ 64) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  apply cv_rng; [exact B1 | lia |]. intros s Hs.
  specialize (H s ltac:(lia)).
  destruct (aview tfibsegs (w_H W) mem s) as [v|] eqn:E; [|exfalso; exact (H eq_refl)].
  exact (cv_aview_vis W mem s v E).
Qed.

(* Present bytes form a stack range (crtA_w_head.v crtA_stk_present). *)
Lemma cv_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk AImg.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* ======================================================================== *)
(* The walk                                                                   *)
(* ======================================================================== *)

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HMPC : pc_wrap_malloc (as_code B) = uci_sigma US___interceptor_trampoline_malloc.
Hypothesis HFPC : pc_wrap_free (as_code B) = uci_sigma US___interceptor_trampoline_free.
Hypothesis HCELLS : uci_cells B.
Hypothesis HOWN : uci_ro_rd_unowned B.
Hypothesis HERR : uci_rom_no_errno B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis UFIX : uci_cv_ufix B.
Hypothesis AMALLOC : forall fx' : YK11.FPState, @amalloc04_rule fx' rc sink segs B MT.
Hypothesis AFREE : forall fx' : YK11.FPState, @afree04_rule fx' rc sink segs B MT.
Hypothesis AMEMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (uci_sigma US___asan_memcpy).
Hypothesis ARUI : forall fx' : YK11.FPState, @PR.uci_rp_uci_int_cg fx' rc B (uci_sigma US_rp_uci_int).
(* The inlined expected_value, lib/A/Prog/UciCvIface.v; proved by lib/A/Prog/UciCvEvA.v and UciCvEvB.v. *)
Hypothesis EV : cv_ev_stmt_F.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* A run that writes no memory: the journal follows its same_but_materialized (crtA_w_tail.v crtT_aj_md). *)
Lemma cv_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS cv_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc'
            (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

(* A block in front of `rest` in a permutation of the live blocks is not also in `rest` (crtT_not_old). *)
Lemma cv_not_old : forall ly S W m md (x : Z * Z) rest,
  AR segs B ly S W m md -> Permutation (ablocks B ly S) (x :: rest) -> 0 < req_size (snd x) -> ~ In x rest.
Proof.
  intros ly S W m md [p n] rest HAR HP Hn Hin. cbn [snd] in Hn.
  destruct (cv_perm_dup _ _ _ HP Hin) as (l1 & l2 & l3 & E).
  pose proof (sep_blocks_pos segs B LAWS ly S W m md (p, n) (p, n) l1 l2 l3 HAR E) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (r n cur T : Z)
  (bs : list byte).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 r.
Hypothesis H11 : YK11.getr regs 11 = w64 n.
Hypothesis H12 : YK11.getr regs 12 = w64 cur.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - CV_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hcur : INT_MIN <= cur <= INT_MAX.
Hypothesis Hn : 0 <= n <= PR.REPLY_MAX.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hblk : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= r /\ r + n <= bA + nA.
Hypothesis Hgarr : garr8 segs (mrestrict (w_H W) memc) r (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hrom : uci_rom_view_rd W memc.
Hypothesis Hnev : st_nev S + k + CV_EV <= EV_MAX.
Hypothesis Hlive : blocks_bytes Sc + CV_LIVE <= LIVE_MAX.
Hypothesis Hmo : mo_ok MT Sc T.
Hypothesis Hcost : uci_cv_cost MT n <= T.

Local Abbreviation POST := (uci_cv_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n cur bs).
(* The inner journal: from the entry state, stack window [spZ regs - CV_STK, spZ regs). *)
Local Abbreviation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CV_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).
Local Abbreviation zs := (PRc.zbytes bs).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

(* The frame the prologue wrote: the caller's s5 .. s0 and ra at [spZ regs - 0x38, spZ regs). *)
Definition cv_frame (m : word -> option byte) : Prop :=
  exists v0, rw_cells AImg.rsegs m (spZ regs - 64)
    (C8 v0 :: cv_fr (GR regs 21) (GR regs 20) (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)).

(* The registers the walk keeps from the prologue on: sp (the frame), gp, tp, s3 = r, s4 = n, s5 = the shadow
   offset, and s6 .. s11 untouched. *)
Definition cv_kept (rg : bvmap 5 word) : Prop :=
  GR rg 2 = w64 (spZ regs - 64) /\ GR rg 3 = GR regs 3 /\ GR rg 4 = GR regs 4 /\
  GR rg 19 = w64 r /\ GR rg 20 = w64 n /\ GR rg 21 = w64 AC.ASAN_K /\
  GR rg 22 = GR regs 22 /\ GR rg 23 = GR regs 23 /\ GR rg 24 = GR regs 24 /\ GR rg 25 = GR regs 25 /\
  GR rg 26 = GR regs 26 /\ GR rg 27 = GR regs 27.

Ltac kp_by HP i K := etransitivity; [apply (HP i); unfold acallee_saved; lia | exact K].

Lemma cv_kept_pres : forall r1 r2, cv_kept r1 -> aregs_preserved r1 r2 -> cv_kept r2.
Proof.
  intros r1 r2 (K2 & K3 & K4 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27) HP.
  unfold cv_kept.
  split; [kp_by HP 2 K2|]. split; [kp_by HP 3 K3|]. split; [kp_by HP 4 K4|]. split; [kp_by HP 19 K19|].
  split; [kp_by HP 20 K20|]. split; [kp_by HP 21 K21|]. split; [kp_by HP 22 K22|]. split; [kp_by HP 23 K23|].
  split; [kp_by HP 24 K24|]. split; [kp_by HP 25 K25|]. split; [kp_by HP 26 K26|]. kp_by HP 27 K27.
Qed.

(* ---- facts of the entry ---- *)

Lemma cv_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cv_JI0 : JI lyc Sc W memc mdc 0.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CV_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CV_STK, CV_FRAME, ASTACK. lia.
  - lia.
Qed.

Lemma cv_sp_rng : YM05.alloc_ceiling + 64 + 16384 <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cv_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  unfold CV_STK, CV_FRAME, ASTACK in Hlo. lia.
Qed.

Lemma cv_ly_top : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> ly_top ly1 <= 2 ^ 47.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & _ & _ & Hshi & H47 & _ & Htop2 & Htop) & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). rewrite Etop. lia.
Qed.

Lemma cv_win : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CV_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma cv_AR : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> AR segs B ly1 S1 W1 m1 md1.
Proof. intros ly1 S1 W1 m1 md1 k1 J. destruct J as (HAR & _). exact HAR. Qed.

Lemma cv_nev : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> k1 <= 1 -> st_nev S1 < EV_MAX.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J Hk.
  destruct J as (_ & _ & _ & _ & _ & _ & Hn1 & _).
  destruct HJ as (_ & _ & _ & _ & _ & _ & Hn0 & _).
  unfold CV_EV in Hnev. lia.
Qed.

Lemma cv_cost : 0 <= mo_malloc MT (Z.max n 1) /\ 0 <= mo_free MT /\ mo_malloc MT (Z.max n 1) + mo_free MT <= T.
Proof.
  pose proof (mo_malloc_nonneg MT MTL (Z.max n 1) ltac:(lia)).
  pose proof (mo_free_nonneg MT MTL).
  unfold uci_cv_cost in Hcost. lia.
Qed.

(* The frame [spZ regs - 64, spZ regs) lies above every callee's window [spZ regs - 64 - X, spZ regs - 64). *)
Lemma cv_frame_kept : forall (W1 W2 : world segs) (m1 m2 : word -> option byte),
  cv_frame m1 ->
  (forall a, spZ regs - CV_STK <= a < spZ regs -> apresent (w_H W1) m1 a) ->
  (forall a, spZ regs - CV_STK <= a < spZ regs -> apresent (w_H W2) m2 a) ->
  (forall a, spZ regs - 64 <= a < spZ regs -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  cv_frame m2.
Proof.
  intros W1 W2 m1 m2 (v0 & F) P1 P2 E. exists v0.
  pose proof cv_sp_rng as [S1 S2].
  apply (cv_rw_cells_ext m1 m2 _ _ F). intros a Ha.
  change (Z.of_nat (cells_size (C8 v0 :: cv_fr (GR regs 21) (GR regs 20) (GR regs 19) (GR regs 18) (GR regs 9)
                                    (GR regs 8) (GR regs 1)))) with 64 in Ha.
  unfold wa. apply (cv_byte_eq (w_H W1) (w_H W2) m1 m2 a); [apply P1 | apply P2 | apply E];
    unfold CV_STK, CV_FRAME, ASTACK in *; lia.
Qed.

(* ======================================================================== *)
(* The walk, backwards from the return                                        *)
(* ======================================================================== *)

(* At CV_RET_FREE: cv_end_F, the return, and the post. *)
Lemma cv_at_retfree : forall ly2 S2 W2 regs2 m2 md2,
  JI ly2 S2 W2 m2 md2 2 -> frames S2 = frames Sc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  mo_le MT Sc S2 (uci_cv_cost MT n) ->
  cv_frame m2 -> cv_kept regs2 ->
  GR regs2 18 = w64 (rp_uci_int_m zs cur) ->
  SRr segs W2 (@cfg_at fx segs CV_RET_FREE regs2 m2 md2) POST.
Proof.
  intros ly2 S2 W2 regs2 m2 md2 J2 Hfr Hperm Hle (v0 & FR) HK H18.
  destruct HK as (K2 & K3 & K4 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof cv_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CV_STK = 64 + 16384) by reflexivity.
  assert (SP2 : bv_unsigned (GR regs2 2) = spZ regs - 64).
  { rewrite K2. unfold w64. apply cv_u64. lia. }
  eapply (@cv_run fx W2 regs2 m2 md2 CV_RET_FREE).
  { unfold LCK.ms_of_regs. eapply cv_end_F.
    - rewrite SP2. exact FR.
    - rewrite SP2. lia.
    - rewrite SP2. apply cv_rng_vis; [lia | lia |]. intros i Hi.
      exact (proj1 (cv_win _ _ _ _ _ _ J2 (spZ regs - 64 + i) ltac:(lia))). }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (cv_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & _ & _ & G18 & G19 & G20 & G21 & G22 & G23 &
    G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1).
  { apply LeafCgFacts.ret_ok_stmt_YK0s. exact Hra. }
  rewrite Hret in EQV.
  rewrite (cv_ms_shape _ _ _ _ EQV).
  pose proof (cv_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 SBM) as J2'.
  apply SRr_ret. unfold uci_cv_post.
  exists ly2, S2, (ms_regs ms'), m2, md'.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS cv_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CV_STK (spZ regs) [] [] ly2 S2 W2 m2 md' 2 HJ J2' Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G2|]. rewrite SP2. replace (spZ regs - 64 + 64) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact G3|]. exact K3.
    - etransitivity; [exact G4|]. exact K4.
    - exact G8.
    - exact G9.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G21.
    - etransitivity; [exact G22|]. exact K22.
    - etransitivity; [exact G23|]. exact K23.
    - etransitivity; [exact G24|]. exact K24.
    - etransitivity; [exact G25|]. exact K25.
    - etransitivity; [exact G26|]. exact K26.
    - etransitivity; [exact G27|]. exact K27. }
  split; [exact Hfr|].
  split; [exact Hperm|].
  split.
  { apply (acall_kept_of_journal segs B cv_segs_low CV_STK (spZ regs) [] [] lyc Sc W memc mdc ly2 S2 W2 m2
             md' 2 (fun _ => False) J2' cv_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    - exact sink_closed_nil. }
  split; [exact Hle|].
  etransitivity; [exact G10|]. exact H18.
Qed.


(* The reply's bytes at a state of the inner journal whose blocks keep the caller's: the journal keeps every byte
   of a caller block that is still live (YCbq.v ajournal, the kept-block clause), and the entry's garr8 gives them. *)
Lemma cv_reply_at : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> 0 < n ->
  (forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1)) ->
  forall i, 0 <= i < n -> aview segs (w_H W1) m1 (r + i) = Some (nthz zs i).
Proof.
  intros ly1 S1 W1 m1 md1 k1 J1 Hn0 Hsub i Hi.
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  replace (r + i) with (bA + (r + i - bA)) by lia.
  rewrite (F2 bA nA (r + i - bA) HbA (Hsub _ _ HbA) ltac:(lia) ltac:(intros (r0 & Hr0 & _); destruct Hr0)).
  replace (bA + (r + i - bA)) with (r + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (cv_garr8_aview (w_H W) memc r _ (Z.to_nat i) Hgarr ltac:(rewrite length_map; lia)).
  reflexivity.
Qed.

(* At the free trampoline: free(P) by afree04_rule, then cv_at_retfree. *)
Lemma cv_at_freecall : forall ly1 S1 W1 regsF m1 md1 P v,
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cv_frame m1 -> cv_kept regsF ->
  GR regsF 1 = Z_to_bv 64 CV_RET_FREE -> GR regsF 10 = w64 P ->
  INT_MIN <= v <= INT_MAX -> GR regsF 8 = Z_to_bv 64 v ->
  GR regsF 18 = w64 (rp_uci_int_m zs cur) ->
  SRr segs W1 (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 CV_FREE) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros ly1 S1 W1 regsF m1 md1 P v J1 Hfr EB Hle HF HK G1 G10 HV G8 G18.
  pose proof (cv_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cv_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof HK as (K2 & K3 & K4 & _).
  assert (Hin : In (P, Z.max n 1) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
  assert (Hnot : ~ In (P, Z.max n 1) (ablocks B lyc Sc)).
  { intros H. apply (cv_not_old ly1 S1 W1 m1 md1 (P, Z.max n 1) (ablocks B lyc Sc) HAR1).
    - rewrite EB. apply Permutation_sym, Permutation_cons_append.
    - cbn [snd]. unfold req_size. destruct (Z.eqb_spec (Z.max n 1) 0); lia.
    - exact H. }
  assert (SPF : spZ regsF = spZ regs + -64).
  { change (spZ regsF) with (bv_unsigned (GR regsF 2)). rewrite K2. unfold w64.
    rewrite cv_u64 by lia. lia. }
  assert (CHAIN : chain_pre ly1 (aview segs (w_H W1) m1) regsF []).
  { apply cv_chain_nil.
    - change (raZ regsF) with (bv_unsigned (GR regsF 1)). rewrite G1. exact (proj2 (proj2 cv_ra_free)).
    - change (s0Z regsF) with (bv_unsigned (GR regsF 8)). rewrite G8, unsigned_lit_wrap.
      pose proof (cv_ly_top _ _ _ _ _ _ J1) as Htop. unfold INT_MIN, INT_MAX in HV.
      destruct (cv_int_word v HV) as [(H0 & E) | (H0 & E)]; rewrite E; [left | right]; lia. }
  assert (TRACE : In (call_trace0 (pc_free_ra0 (as_code B)) regsF []) (as_universe B)).
  { rewrite cv_trace0. cbn [spine map].
    replace (raZ regsF) with UCI_CV_RA_FREE; [exact (proj2 UFIX)|].
    change (raZ regsF) with (bv_unsigned (GR regsF 1)). rewrite G1. symmetry. exact (proj1 cv_ra_free). }
  pose proof cv_cost as (Mc1 & Mc2 & Msum).
  assert (MOK : mo_ok MT S1 (mo_free MT)).
  { apply (mok_station MT Sc S1 T (mo_malloc MT (Z.max n 1)) (mo_free MT) MTL Hmo Hle Mc2). lia. }
  assert (EF : CV_FREE = pc_wrap_free (as_code B)) by (rewrite HFPC; reflexivity).
  rewrite EF.
  eapply SRr_bind.
  - exact (AFREE fx W1 regsF m1 CV_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 md1 1 P (Z.max n 1) (-64)
             (Z_to_bv 64 CV_RET_FREE) [] J1 Hin G10 SPF eq_refl ltac:(lia)
             ltac:(unfold CV_STK, CV_FRAME, ASTACK; lia)
             (eq_trans K3 Hgp) (eq_trans K4 Htp) G1 (YK0s.ret_ok_even _ (proj1 (proj2 cv_ra_free)))
             (cv_nev _ _ _ _ _ _ J1 ltac:(lia)) CHAIN TRACE (fun H => False_ind _ (Hnot H)) MOK).
  - intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & -> & J2 & HRP & HBL & HFR & HKEPT & HML).
    apply (cv_at_retfree ly2 S2 W2 regs2 m2 md2).
    + exact J2.
    + rewrite HFR. exact Hfr.
    + destruct HBL as (l1 & l2 & E1 & E2). rewrite E2. apply (cv_perm_rm l1 l2 _ (P, Z.max n 1)).
      rewrite <- E1, EB. apply Permutation_sym, Permutation_cons_append.
    + unfold uci_cv_cost. exact (mle_station MT Sc S1 S2 _ _ MTL Hle HML).
    + apply (cv_frame_kept W1 W2 m1 m2 HF (cv_win _ _ _ _ _ _ J1) (cv_win _ _ _ _ _ _ J2)).
      intros a Ha. apply (proj1 HKEPT); [unfold CV_STK, CV_FRAME, ASTACK in *; lia | lia].
    + exact (cv_kept_pres _ _ HK HRP).
    + kp_by HRP 18 G18.
Qed.

(* At CV_RET_RUI (n > 0): the inlined expected_value (cv_ev_stmt_F) and the property test (cv_test_F), then
   cv_at_freecall. *)
Lemma cv_at_ruiret_pos : forall ly1 S1 W1 regsR m1 md1 P,
  0 < n ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cv_frame m1 -> cv_kept regsR ->
  GR regsR 8 = w64 cur -> GR regsR 9 = w64 P -> GR regsR 10 = w64 (rp_uci_int_m zs cur) ->
  SRr segs W1 (@cfg_at fx segs CV_RET_RUI regsR m1 md1) POST.
Proof.
  intros ly1 S1 W1 regsR m1 md1 P Hn0 J1 Hfr EB Hle HF HK G8 G9 G10.
  pose proof HK as (K2 & K3 & K4 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof (cv_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HinA : In (bA, nA) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbA).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bA nA HAR1 HinA) as (_ & HA4 & HAc & HAapp & HAb & _ & _).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _]. unfold YG0f.ASAN_CEIL in CR.
  assert (Hsub : forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1))
    by (intros b nb Hb; rewrite EB; apply in_or_app; left; exact Hb).
  pose proof (cv_reply_at _ _ _ _ _ _ J1 Hn0 Hsub) as Hrd.
  set (v := expected_value_m zs cur).
  assert (Hval : rp_uci_int_m zs cur = v) by (apply uci_value_ok).
  assert (Hv : INT_MIN <= v <= INT_MAX) by (rewrite <- Hval; apply rp_uci_int_range; exact Hcur).
  rewrite Hval in G10.
  pose proof EV as EV'. unfold cv_ev_stmt_F in EV'.
  eapply (@cv_run fx W1 regsR m1 md1 CV_RET_RUI).
  { unfold LCK.ms_of_regs. rewrite K19, K20, K21, G10.
    eapply EV' with (r := r) (n := n) (cur := cur) (zs := zs)
      (Q := fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word,
              ms = MS (mkR (Z_to_bv 64 CV_RET_FREE) (GR regsR 2) (GR regsR 3) (GR regsR 4) t0 t1 t2
                         (Z_to_bv 64 v) (GR regsR 9) (GR regsR 9) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v)
                         (Z_to_bv 64 r) (Z_to_bv 64 n) (Z_to_bv 64 AC.ASAN_K) (GR regsR 22) (GR regsR 23)
                         (GR regsR 24) (GR regsR 25) (GR regsR 26) (GR regsR 27) (GR regsR 28) (GR regsR 29)
                         (GR regsR 30) (GR regsR 31))
                      (@fp_regs fx) (Z_to_bv 64 CV_FREE) (@fp_csr fx) None m1 (seg_rom AImg.rsegs)).
    - lia.
    - unfold PR.REPLY_MAX in Hn. lia.
    - unfold PRc.zbytes. rewrite length_map. exact Hlen.
    - apply cv_zbytes_rng.
    - intros i Hi. exact (cv_mrd_of_aview W1 m1 (r + i) _ (Hrd i Hi)).
    - apply (cv_addressable W1 m1 r n).
      + apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA r n HAR1 HinA); lia.
      + lia.
      + unfold in_app in HAapp. split; [lia|]. destruct HAapp as (_ & [HL | [HH1 HH2]]); [left | right]; lia.
    - apply cv_rng; [lia | lia |]. intros b Hb. exact (proj1 (proj1 (HAb b ltac:(lia)))).
    - apply (cv_rng_hull W1 m1 r n); [lia | lia | lia |].
      apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA r n HAR1 HinA); lia.
    - exact Hcur.
    - rewrite G8. unfold w64. apply unsigned_lit_wrap.
    - intros s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' Hs0'.
      eapply ExecF.evtF_mono.
      + eapply cv_test_F; [exact Hv | exact Hs0'].
      + intros ms' ->. do 10 eexists. reflexivity. }
  intros ms' md' (ms0 & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & ->) & EQV) SBM.
  destruct (cv_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
    E24 & E25 & E26 & E27).
  rewrite (cv_ms_shape _ _ _ _ EQV).
  apply (cv_at_freecall ly1 S1 W1 (ms_regs ms') m1 md' P v).
  - exact (cv_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
  - exact Hfr.
  - exact EB.
  - exact Hle.
  - exact HF.
  - unfold cv_kept.
    split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
    split; [exact E19|]. split; [exact E20|]. split; [exact E21|].
    split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|]. split; [rewrite E24; exact K24|].
    split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|]. rewrite E27; exact K27.
  - exact E1.
  - rewrite E10. exact G9.
  - exact Hv.
  - exact E8.
  - rewrite E18, Hval. reflexivity.
Qed.

(* At CV_RET_RUI0 (n = 0): cv_segz_F and cv_test_F (the value is cur), then cv_at_freecall. *)
Lemma cv_at_ruiret_zero : forall ly1 S1 W1 regsZ m1 md1 P,
  n = 0 ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cv_frame m1 -> cv_kept regsZ ->
  GR regsZ 8 = w64 cur -> GR regsZ 9 = w64 P -> GR regsZ 10 = w64 (rp_uci_int_m zs cur) ->
  SRr segs W1 (@cfg_at fx segs CV_RET_RUI0 regsZ m1 md1) POST.
Proof.
  intros ly1 S1 W1 regsZ m1 md1 P Hn0 J1 Hfr EB Hle HF HK G8 G9 G10.
  pose proof HK as (K2 & K3 & K4 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  assert (Hbs : bs = []) by (destruct bs; [reflexivity | cbn [length] in Hlen; lia]).
  assert (Hval : rp_uci_int_m zs cur = cur) by (rewrite Hbs; reflexivity).
  rewrite Hval in G10.
  eapply (@cv_run fx W1 regsZ m1 md1 CV_RET_RUI0).
  { unfold LCK.ms_of_regs. rewrite G10.
    eapply ExecF.evtF_cut; [apply cv_segz_F|].
    intros ms1 ->. eapply cv_test_F; [exact Hcur|].
    rewrite G8. unfold w64. apply unsigned_lit_wrap. }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (cv_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
    E24 & E25 & E26 & E27).
  rewrite (cv_ms_shape _ _ _ _ EQV).
  apply (cv_at_freecall ly1 S1 W1 (ms_regs ms') m1 md' P cur).
  - exact (cv_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
  - exact Hfr.
  - exact EB.
  - exact Hle.
  - exact HF.
  - unfold cv_kept.
    split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
    split; [rewrite E19; exact K19|]. split; [rewrite E20; exact K20|]. split; [rewrite E21; exact K21|].
    split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|]. split; [rewrite E24; exact K24|].
    split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|]. rewrite E27; exact K27.
  - exact E1.
  - rewrite E10. exact G9.
  - exact Hcur.
  - exact E8.
  - rewrite E18, Hval. reflexivity.
Qed.

(* The call of rp_uci_int(P, n, cur) on the copy, from either path: the contract (rp_uci_int_cg.v), the inner journal
   re-established over its stack window (YCbq.v ajournal_after_write), and the walk's continuation. *)
Lemma cv_rui_call : forall ly1 S1 W1 regsC m1 md1 P (rl : Z),
  JI ly1 S1 W1 m1 md1 1 ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  cv_kept regsC -> GR regsC 1 = Z_to_bv 64 rl -> 0 <= rl < 2 ^ 64 -> YK0s.ret_ok (GR regsC 1) ->
  GR regsC 10 = w64 P -> GR regsC 11 = w64 n -> GR regsC 12 = w64 cur ->
  (forall i, 0 <= i < n -> aview segs (w_H W1) m1 (P + i) = Some (nthz zs i)) ->
  (forall regs' m' md',
     JI ly1 S1 W1 m' md' 1 -> aregs_preserved regsC regs' ->
     GR regs' 10 = w64 (rp_uci_int_m zs cur) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 - PR.RUI_STK <= a < spZ regs - 64) ->
        aview segs (w_H W1) m' a = aview segs (w_H W1) m1 a) ->
     SRr segs W1 (@cfg_at fx segs rl regs' m' md') POST) ->
  SRr segs W1 (@cfg_at fx segs CV_RUI regsC m1 md1) POST.
Proof.
  intros ly1 S1 W1 regsC m1 md1 P rl J1 EB HK G1 Hrl Hret G10 G11 G12 HCP KONT.
  pose proof HK as (K2 & K3 & K4 & _).
  pose proof cv_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (cv_AR _ _ _ _ _ _ J1) as HAR1.
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & HP4 & HPc & HPapp & HPb & _ & _).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1) by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  rewrite Hreq in HPc, HPapp, HPb.
  assert (SPC : spZ regsC = spZ regs + -64).
  { change (spZ regsC) with (bv_unsigned (GR regsC 2)). rewrite K2. unfold w64. rewrite cv_u64 by lia. lia. }
  assert (ECP : ecall_pre segs B ly1 S1 W1 regsC m1 md1).
  { apply (ecall_pre_at segs B CV_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 1 regsC (-64) J1 SPC
             eq_refl ltac:(lia) ltac:(unfold ESTACK, CV_STK, CV_FRAME, ASTACK; lia) Hret (eq_trans K3 Hgp)
             (eq_trans K4 Htp)). }
  pose proof J1 as (_ & Hly & _ & _ & _ & Hfrs1 & _ & _ & _ & _ & F3 & _ & _ & _ & (_ & _ & _ & Hslo & _) & _ & HQT1).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
  unfold CV_RUI.
  eapply SRr_bind.
  { apply (ARUI fx ly1 S1 W1 regsC m1 md1 P n cur bs ECP).
    - rewrite Eslo, SPC. unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK, CV_STK, CV_FRAME, ASTACK in *. lia.
    - intros x Hx. apply (cv_win _ _ _ _ _ _ J1). rewrite SPC in Hx.
      unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK, CV_STK, CV_FRAME, ASTACK in *. lia.
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hn.
    - exact Hlen.
    - exact Hcur.
    - lia.
    - lia.
    - apply cv_garr8_of_aview. intros j Hj. rewrite length_map in Hj.
      split.
      + rewrite (HCP (Z.of_nat j) ltac:(lia)). unfold nthz, PRc.zbytes. rewrite Nat2Z.id. reflexivity.
      + pose proof (cv_zbytes_rng bs (Z.of_nat j)) as R. unfold nthz, PRc.zbytes in R. rewrite Nat2Z.id in R.
        exact R.
    - intros x Hx. split.
      + replace x with (P + (x - P)) by lia. rewrite (HCP (x - P) ltac:(lia)). discriminate.
      + rewrite SPC. unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK, CV_STK, CV_FRAME, ASTACK in *. lia.
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP); rewrite ?Hreq; lia.
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
        rewrite ?Hreq; lia.
    - intros Hn0. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
        rewrite ?Hreq; lia.
    - intros a Ha.
      assert (Hin : uci_in_ro_rd a).
      { unfold uci_in_ro_rd, UCI_RO_RD. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
        unfold PR.UCI_MC_LO, PR.UCI_MC_HI in Ha. lia. }
      destruct (uci_ro_rd_scoped B HOWN HERR a Hin) as [N1 N2].
      destruct (uci_ro_rd_rom_clean a Hin) as [HR _].
      rewrite (F3 a (cv_rom_img a HR) N1 N2 (fun Ho => False_ind _ (sink_closed_nil Ho))).
      exact (Hrom a Hin). }
  cbv beta. intros W' c' _ (-> & regs' & m' & md' & -> & HAR' & HPRES & HSBM & HA0 & HVIEW & HAPP).
  assert (J1' : JI ly1 S1 W1 m' md' 1).
  { apply (ajournal_after_write segs B LAWS cv_segs_low CV_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1
             1 m' md' (fun a => spZ regsC - PR.RUI_STK <= a < spZ regsC) S1 [] J1).
    - intros a Ha HnW. exact (HVIEW a Ha HnW).
    - exact HAPP.
    - exact HSBM.
    - intros a Ha. left. left. rewrite SPC in Ha.
      unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK, CV_STK, CV_FRAME, ASTACK in *. lia.
    - exact HAR'.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact Hfrs1.
    - exact HQT1. }
  replace (raZ regsC) with rl.
  2:{ change (raZ regsC) with (bv_unsigned (GR regsC 1)). rewrite G1. symmetry. apply cv_u64. exact Hrl. }
  apply (KONT regs' m' md' J1' HPRES HA0).
  intros a Ha Hw. apply HVIEW; [exact Ha|]. rewrite SPC. replace (spZ regs + -64) with (spZ regs - 64) by lia.
  exact Hw.
Qed.

(* At the __asan_memcpy call (n > 0): aj_intrin_at, cv_seg3_F, then cv_rui_call and cv_at_ruiret_pos. *)
Lemma cv_memcpy_call : forall ly1 S1 W1 regsM m1 md1 P,
  0 < n ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cv_frame m1 -> cv_kept regsM ->
  GR regsM 1 = Z_to_bv 64 CV_RET_MEMCPY -> GR regsM 8 = w64 cur -> GR regsM 9 = w64 P ->
  GR regsM 10 = w64 P -> GR regsM 11 = w64 r -> GR regsM 12 = w64 n ->
  SRr segs W1 (mkCfg (@YK11.mkst fx regsM (Z_to_bv 64 CV_MEMCPY) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros ly1 S1 W1 regsM m1 md1 P Hn0 J1 Hfr EB Hle HF HK G1 G8 G9 G10 G11 G12.
  pose proof HK as (K2 & K3 & K4 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof cv_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (cv_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _]. unfold YG0f.ASAN_CEIL in CR.
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & HP4 & HPc & HPapp & HPb & _ & _).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1) by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  rewrite Hreq in HPc, HPapp, HPb.
  assert (Hnot : ~ In (P, Z.max n 1) (ablocks B lyc Sc)).
  { intros H. apply (cv_not_old ly1 S1 W1 m1 md1 (P, Z.max n 1) (ablocks B lyc Sc) HAR1).
    - rewrite EB. apply Permutation_sym, Permutation_cons_append.
    - cbn [snd]. lia.
    - exact H. }
  destruct (Hblk Hn0) as (bA & nA & HbA & HbA1 & HbA2).
  assert (HinA : In (bA, nA) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbA).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bA nA HAR1 HinA) as (_ & HA4 & HAc & HAapp & HAb & _ & _).
  assert (HreqA : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
  assert (Hne : (bA, nA) <> (P, Z.max n 1)) by (intros E; rewrite E in HbA; exact (Hnot HbA)).
  pose proof (sep_blocks segs B LAWS ly1 S1 W1 m1 md1 _ _ _ _ HAR1 HinA HinP Hne) as DAP.
  rewrite Hreq in DAP. unfold zdisjoint in DAP. cbn [fst snd] in DAP.
  assert (Hsub : forall b nb, In (b, nb) (ablocks B lyc Sc) -> In (b, nb) (ablocks B ly1 S1))
    by (intros b nb Hb; rewrite EB; apply in_or_app; left; exact Hb).
  pose proof (cv_reply_at _ _ _ _ _ _ J1 Hn0 Hsub) as Hrd.
  assert (SPM : spZ regsM = spZ regs + -64).
  { change (spZ regsM) with (bv_unsigned (GR regsM 2)). rewrite K2. unfold w64. rewrite cv_u64 by lia. lia. }
  eapply SRr_bind.
  { apply (aj_intrin_at segs B LAWS cv_segs_low OCpy CV_MEMCPY (AMEMCPY fx) W1 regsM m1 CV_STK (spZ regs) []
             lyc Sc W memc mdc [] ly1 S1 md1 1 P r n (-64) (Z_to_bv 64 CV_RET_MEMCPY) J1 G10 G11 G12).
    - unfold PR.REPLY_MAX in Hn. lia.
    - lia.
    - lia.
    - exact SPM.
    - reflexivity.
    - lia.
    - unfold ESTACK, CV_STK, CV_FRAME, ASTACK. lia.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - exact G1.
    - apply YK0s.ret_ok_even. exact (proj1 (cv_ra_even 0x5c ltac:(cbn; tauto))).
    - intros a Ha. split.
      + right. right. left. exists P, (Z.max n 1). split; [exact HinP|]. split; [exact Hnot|].
        rewrite Hreq. lia.
      + unfold ESTACK, CV_STK, CV_FRAME, ASTACK in *. lia.
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP); rewrite ?Hreq; lia.
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
        rewrite ?Hreq; lia.
    - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
        rewrite ?Hreq; lia.
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - replace a with (r + (a - r)) by lia. rewrite (Hrd (a - r) ltac:(lia)). discriminate.
        - rewrite SPM. unfold ESTACK, CV_STK, CV_FRAME, ASTACK in *. lia. }
      split; [lia|]. split.
      { apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA r n HAR1 HinA); lia. }
      split.
      { apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA r n HAR1 HinA); lia. }
      intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA r n HAR1 HinA); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & J2 & HPRES & HA0 & HCOPY & HVIEW & HAPP).
  assert (HK2 : cv_kept regs2) by exact (cv_kept_pres _ _ HK HPRES).
  assert (HF2 : cv_frame m2).
  { apply (cv_frame_kept W1 W1 m1 m2 HF (cv_win _ _ _ _ _ _ J1) (cv_win _ _ _ _ _ _ J2)).
    intros a Ha. apply HVIEW; [lia | lia |]. unfold ESTACK in *. lia. }
  (* ---- CV_RET_MEMCPY -> rp_uci_int: cv_seg3_F ---- *)
  eapply (@cv_run fx W1 regs2 m2 md2 CV_RET_MEMCPY).
  { unfold LCK.ms_of_regs. apply cv_seg3_F. }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (cv_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 & E23 &
    E24 & E25 & E26 & E27).
  rewrite (cv_ms_shape _ _ _ _ EQV).
  pose proof (cv_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 SBM) as J2'.
  assert (HKs : cv_kept (ms_regs ms')).
  { pose proof HK2 as (L2 & L3 & L4 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27). unfold cv_kept.
    split; [rewrite E2; exact L2|]. split; [rewrite E3; exact L3|]. split; [rewrite E4; exact L4|].
    split; [rewrite E19; exact L19|]. split; [rewrite E20; exact L20|]. split; [rewrite E21; exact L21|].
    split; [rewrite E22; exact L22|]. split; [rewrite E23; exact L23|]. split; [rewrite E24; exact L24|].
    split; [rewrite E25; exact L25|]. split; [rewrite E26; exact L26|]. rewrite E27; exact L27. }
  assert (G8' : GR regs2 8 = w64 cur) by (kp_by HPRES 8 G8).
  assert (G9' : GR regs2 9 = w64 P) by (kp_by HPRES 9 G9).
  assert (G20' : GR regs2 20 = w64 n) by (kp_by HPRES 20 K20).
  pose proof (cv_ra_even 0x6c ltac:(cbn; tauto)) as (RE1 & RE2 & RE3).
  change (mkCfg (YK11.mkst (ms_regs ms') (Z_to_bv 64 CV_RUI) m2 (YK11.seg_rom segs)) md')
    with (@cfg_at fx segs CV_RUI (ms_regs ms') m2 md').
  apply (cv_rui_call ly1 S1 W1 (ms_regs ms') m2 md' P CV_RET_RUI J2' EB HKs E1).
  - unfold CV_RET_RUI. rewrite <- RE3. apply bv_unsigned_in_range.
  - rewrite E1. apply YK0s.ret_ok_even. exact RE1.
  - rewrite E10. exact G9'.
  - rewrite E11. exact G20'.
  - rewrite E12. exact G8'.
  - intros i Hi. rewrite (HCOPY i ltac:(lia)). exact (Hrd i Hi).
  - intros regs' m' md'' J3 HP3 HA3 HV3.
    apply (cv_at_ruiret_pos ly1 S1 W1 regs' m' md'' P Hn0 J3 Hfr EB Hle).
    + apply (cv_frame_kept W1 W1 m2 m' HF2 (cv_win _ _ _ _ _ _ J2) (cv_win _ _ _ _ _ _ J3)).
      intros a Ha. apply HV3; [lia|]. unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK in *. lia.
    + exact (cv_kept_pres _ _ HKs HP3).
    + kp_by HP3 8 (eq_trans E8 G8').
    + kp_by HP3 9 (eq_trans E9 G9').
    + exact HA3.
Qed.

(* At CV_RET_MALLOC: a0 = P; n > 0: cv_seg2p_F and the copy; n = 0: cv_seg2z_F and rp_uci_int(P, 0, cur). *)
Lemma cv_at_retmalloc : forall ly1 S1 W1 regs1 m1 md1 P,
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] -> 4096 <= P ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cv_frame m1 -> cv_kept regs1 -> GR regs1 8 = w64 cur -> GR regs1 10 = w64 P ->
  SRr segs W1 (@cfg_at fx segs CV_RET_MALLOC regs1 m1 md1) POST.
Proof.
  intros ly1 S1 W1 regs1 m1 md1 P J1 Hfr EB HP4 Hle HF HK G8 G10.
  pose proof HK as (K2 & K3 & K4 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof cv_sp_rng as [Hsp1 Hsp2].
  pose proof (cv_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & _ & HPc & _ & HPb & _ & _).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1) by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  rewrite Hreq in HPc, HPb.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  - (* n = 0 *)
    eapply (@cv_run fx W1 regs1 m1 md1 CV_RET_MALLOC).
    { unfold LCK.ms_of_regs. rewrite G10, K20, Hn0. apply cv_seg2z_F. lia. }
    intros ms' md' (ms0 & -> & EQV) SBM.
    destruct (cv_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    rewrite (cv_ms_shape _ _ _ _ EQV).
    pose proof (cv_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM) as J1'.
    assert (HKs : cv_kept (ms_regs ms')).
    { unfold cv_kept.
      split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
      split; [rewrite E19; exact K19|]. split; [rewrite E20, Hn0; reflexivity|].
      split; [rewrite E21; exact K21|].
      split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|]. split; [rewrite E24; exact K24|].
      split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|]. rewrite E27; exact K27. }
    pose proof (cv_ra_even 0xb8 ltac:(cbn; tauto)) as (RE1 & RE2 & RE3).
    change (mkCfg (YK11.mkst (ms_regs ms') (Z_to_bv 64 CV_RUI) m1 (YK11.seg_rom segs)) md')
      with (@cfg_at fx segs CV_RUI (ms_regs ms') m1 md').
    apply (cv_rui_call ly1 S1 W1 (ms_regs ms') m1 md' P CV_RET_RUI0 J1' EB HKs E1).
    + unfold CV_RET_RUI0. rewrite <- RE3. apply bv_unsigned_in_range.
    + rewrite E1. apply YK0s.ret_ok_even. exact RE1.
    + exact E10.
    + rewrite E11, Hn0. reflexivity.
    + rewrite E12. exact G8.
    + intros i Hi. lia.
    + intros regs' m' md'' J3 HP3 HA3 HV3.
      apply (cv_at_ruiret_zero ly1 S1 W1 regs' m' md'' P Hn0 J3 Hfr EB Hle).
      * apply (cv_frame_kept W1 W1 m1 m' HF (cv_win _ _ _ _ _ _ J1) (cv_win _ _ _ _ _ _ J3)).
        intros a Ha. apply HV3; [lia|]. unfold PR.RUI_STK, PR.RUI_FRAME, ESTACK in *. lia.
      * exact (cv_kept_pres _ _ HKs HP3).
      * kp_by HP3 8 (eq_trans E8 G8).
      * kp_by HP3 9 E9.
      * exact HA3.
  - (* n > 0 *)
    assert (Hn1 : 0 < n) by lia.
    eapply (@cv_run fx W1 regs1 m1 md1 CV_RET_MALLOC).
    { unfold LCK.ms_of_regs. rewrite G10, K20. apply cv_seg2p_F; unfold PR.REPLY_MAX in Hn; lia. }
    intros ms' md' (ms0 & -> & EQV) SBM.
    destruct (cv_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    rewrite (cv_ms_shape _ _ _ _ EQV).
    apply (cv_memcpy_call ly1 S1 W1 (ms_regs ms') m1 md' P Hn1).
    + exact (cv_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
    + exact Hfr.
    + exact EB.
    + exact Hle.
    + exact HF.
    + unfold cv_kept.
      split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
      split; [rewrite E19; exact K19|]. split; [rewrite E20; reflexivity|]. split; [rewrite E21; exact K21|].
      split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|]. split; [rewrite E24; exact K24|].
      split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|]. rewrite E27; exact K27.
    + exact E1.
    + rewrite E8. exact G8.
    + exact E9.
    + exact E10.
    + rewrite E11. exact K19.
    + exact E12.
Qed.

(* At CV_ENTRY: the inner journal, cv_seg1_F (the prologue), then malloc(n + (n == 0)). *)
Lemma cv_entry : SRr segs W (@cfg_at fx segs CV_ENTRY regs memc mdc) POST.
Proof.
  pose proof cv_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cv_JI0 as JI0.
  pose proof (cv_win _ _ _ _ _ _ JI0) as Hpres0.
  pose proof cv_cost as (Mc1 & Mc2 & Msum).
  assert (EST : CV_STK = 64 + 16384) by reflexivity.
  destruct (cv_cells2 B HCELLS lyc Sc W memc mdc cv_HARc) as [GCK CK].
  assert (E10 : GR regs 10 = Z_to_bv 64 r) by exact H10.
  assert (E11 : GR regs 11 = Z_to_bv 64 n) by exact H11.
  assert (E12 : GR regs 12 = Z_to_bv 64 cur) by exact H12.
  (* the prologue *)
  eapply (@cv_run fx W regs memc mdc CV_ENTRY).
  { unfold LCK.ms_of_regs. rewrite E10, E11, E12.
    eapply cv_seg1_F with (lo := spZ regs - CV_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (cv_stk_present (w_H W)); [lia | lia | exact Hpres0].
    - lia.
    - exact GCK.
    - exact CK.
    - unfold AC.CELL_K. lia.
    - unfold PR.REPLY_MAX in Hn. lia.
    - apply cv_rng; [lia | lia |]. intros b Hb. exact (proj1 (Hpres0 b ltac:(lia))).
    - apply cv_rng; [unfold AC.GOT_CELL_K; lia | unfold AC.GOT_CELL_K; lia |]. intros b Hb.
      replace b with (AC.GOT_CELL_K + (b - AC.GOT_CELL_K)) by lia.
      apply (cv_covers_visible (w_H W) AC.GOT_CELL_K 8 (b - AC.GOT_CELL_K) (w_Hoff W));
        [vm_compute; reflexivity | lia | unfold AC.GOT_CELL_K; lia].
    - apply cv_rng; [unfold AC.CELL_K; lia | unfold AC.CELL_K; lia |]. intros b Hb.
      replace b with (AC.CELL_K + (b - AC.CELL_K)) by lia.
      apply (cv_covers_visible (w_H W) AC.CELL_K 8 (b - AC.CELL_K) (w_Hoff W));
        [vm_compute; reflexivity | lia | unfold AC.CELL_K; lia]. }
  intros ms' md' (ms0 & (m1 & v0 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR.
  destruct (cv_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite (cv_ms_shape _ _ _ _ EQV).
  (* the inner journal after the frame write *)
  assert (HJ1 : JI lyc Sc W m1 md' 0).
  { apply (ajournal_exec segs B LAWS cv_segs_low CV_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 md'
             (fun a => spZ regs - 64 <= a < spZ regs) JI0).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 64)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hxr : spZ regs - CV_STK <= bv_unsigned x < spZ regs) by lia.
      destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
      assert (Hw : wview AImg.rsegs m1 x <> None).
      { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
      unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (LeafCgGlue.find_segment_out AImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
      intros sg Hin Hr. pose proof (cv_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
      unfold kLowMemEnd in Hlow. lia.
    - intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 64)) as [Hl|Hl];
        [apply (MU x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|apply (MU x); cbn [outside]; split; [lia | exact I]].
      exfalso.
      assert (Hxr : spZ regs - CV_STK <= bv_unsigned x < spZ regs) by lia.
      pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. left. lia. }
  (* the frame and the kept registers *)
  assert (HF1 : cv_frame m1) by (exists v0; exact FR).
  assert (HK1 : cv_kept (ms_regs ms')).
  { unfold cv_kept.
    split; [rewrite E2; reflexivity|]. split; [rewrite E3; reflexivity|]. split; [rewrite E4; reflexivity|].
    split; [rewrite E19; reflexivity|]. split; [rewrite E20; reflexivity|]. split; [rewrite E21; reflexivity|].
    split; [rewrite E22; reflexivity|]. split; [rewrite E23; reflexivity|]. split; [rewrite E24; reflexivity|].
    split; [rewrite E25; reflexivity|]. split; [rewrite E26; reflexivity|]. rewrite E27; reflexivity. }
  (* malloc(n + (n == 0)) *)
  pose proof HK1 as (K2 & K3 & K4 & _).
  assert (SP1 : spZ (ms_regs ms') = spZ regs + -64).
  { change (spZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 2)). rewrite K2. unfold w64.
    rewrite cv_u64 by lia. lia. }
  assert (CHAIN : chain_pre lyc (aview segs (w_H W) m1) (ms_regs ms') []).
  { apply cv_chain_nil.
    - change (raZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 1)). rewrite E1.
      exact (proj2 (proj2 cv_ra_malloc)).
    - change (s0Z (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 8)). rewrite E8, unsigned_lit_wrap.
      pose proof (cv_ly_top _ _ _ _ _ _ HJ1) as Htop. unfold INT_MIN, INT_MAX in Hcur.
      destruct (cv_int_word cur Hcur) as [(H0 & E) | (H0 & E)]; rewrite E; [left | right]; lia. }
  assert (TRACE : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms') []) (as_universe B)).
  { rewrite cv_trace0. cbn [spine map].
    replace (raZ (ms_regs ms')) with UCI_CV_RA_MALLOC; [exact (proj1 UFIX)|].
    change (raZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 1)). rewrite E1.
    symmetry. exact (proj1 cv_ra_malloc). }
  assert (MOK : mo_ok MT Sc (mo_malloc MT (Z.max n 1))) by (apply (mo_ok_le MT MTL Sc _ T Hmo); lia).
  assert (Pnev : st_nev Sc < EV_MAX) by exact (cv_nev _ _ _ _ _ _ HJ1 ltac:(lia)).
  assert (Plive : blocks_bytes Sc + Z.max n 1 <= LIVE_MAX) by (unfold CV_LIVE, PR.REPLY_MAX in Hlive, Hn; lia).
  assert (G10 : GR (ms_regs ms') 10 = w64 (Z.max n 1)) by exact E10'.
  assert (EM : CV_MALLOC = pc_wrap_malloc (as_code B)) by (rewrite HMPC; reflexivity).
  rewrite EM.
  eapply SRr_bind.
  - exact (AMALLOC fx W (ms_regs ms') m1 CV_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc md' 0
             (Z.max n 1) (-64) (Z_to_bv 64 CV_RET_MALLOC) [] HJ1 G10 ltac:(unfold MALLOC_MAX, PR.REPLY_MAX in *; lia)
             Plive SP1 eq_refl ltac:(lia) ltac:(unfold CV_STK, CV_FRAME, ASTACK; lia)
             (eq_trans K3 Hgp) (eq_trans K4 Htp) E1 (YK0s.ret_ok_even _ (proj1 (proj2 cv_ra_malloc)))
             Pnev CHAIN TRACE MOK).
  - intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & P & -> & HJ2 & HP2 & H10' & Hfr2 & HP4 & EB & HKEPT & Hle1).
    apply (cv_at_retmalloc ly2 S2 W2 regs2 m2 md2 P).
    + exact HJ2.
    + exact Hfr2.
    + exact EB.
    + exact HP4.
    + exact Hle1.
    + apply (cv_frame_kept W W2 m1 m2 HF1 (cv_win _ _ _ _ _ _ HJ1) (cv_win _ _ _ _ _ _ HJ2)).
      intros a Ha. apply (proj1 HKEPT); [unfold CV_STK, CV_FRAME, ASTACK in *; lia | lia].
    + exact (cv_kept_pres _ _ HK1 HP2).
    + kp_by HP2 8 E8.
    + exact H10'.
Qed.

End Entry.

Theorem cv_walk : uci_check_value_cg B MT (uci_sigma US_check_value).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r n cur T bs.
  intros HJ Hra Hra4 Hgp Htp H10 H11 H12 Hal Hwlo Hwhi Hcur Hn Hlen Hblk Hgarr Hrom Hnev Hlive Hmo Hcost.
  eapply cv_entry; eassumption.
Qed.
End Walk.

(* The frozen statement: every premise of the walk is a premise of uci_check_value_cg_holds_stmt, and the inlined
   expected_value is lib/A/Prog/UciCvEvA.v cv_ev_of_dgt applied to lib/A/Prog/UciCvEvB.v cv_dgt_holds. *)
Theorem uci_check_value_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  uci_check_value_cg_holds_stmt B MT.
Proof.
  intros HMPC HFPC HCELLS HOWN HERR LAWS MTL UFIX AMALLOC AFREE AMEMCPY ARUI.
  apply cv_walk; try assumption.
  exact (UciCvEvA.cv_ev_of_dgt UciCvEvB.cv_dgt_holds).
Qed.
