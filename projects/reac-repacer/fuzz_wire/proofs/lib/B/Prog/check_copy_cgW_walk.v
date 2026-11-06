(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 653 of its 721 lines of code are new or changed and 396 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_wire's check_width in image A, proving the frozen
   statement lib/A/Prog/check_width_cg.v wire_check_width_holds_stmt. The form is reac-repacer/fuzz_uci's
   lib/A/Prog/check_value_cgW.v (footprint runs carried into SRr, an inner journal over the call's stack window, each
   call cut by its callee's statement) with its segment file lib/A/Prog/UciCvSegs.v, and the leaf call of its
   lib/A/Prog/check_clamp_cgW.v (here through lib/A/Prog/WireCcLeafb.v wcc_leafb_journal, the leaf taken by
   WireCg.v wire_leaf_at). The w_width loop and the frame law are this unit's plain walk lib/Prog/check_width.v
   (width_loop, w_width_frame_law, fc_model_neg), restated over image A's rp_frame_channels_model. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_width_cgW.v, with its module paths, module names and numbers changed; 1585 of its 1769 lines of code are new or changed and 537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_uci's check_value in image A, proving the frozen statement
   lib/A/Prog/check_value_cg.v uci_check_value_cg_holds_stmt, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/
   crtA_walk.v, crtA_w_head.v, crtA_w_tail.v, crtA_encw.v, crtA_w_mid.v and crtA_close.v (commit
   88154566652a): footprint runs carried into SRr, an inner journal over the call's stack window, each call cut by its
   callee contract, and the helpers of those files (crtA_run, crtA_ms_shape, crtA_ms_reg, crtT_regs_of, crtA_trace0,
   crtT_chain_nil, crtA_byte_eq, crtT_rw_cells_ext, crtA_rng_vis, crtT_aj_md, crtT_not_old, crtT_perm_rm,
   crtA_addressable, crtA_rng_hull, crtA_vis_hull) restated at this unit's image. *)
(* check_copy_cgW_walk: the walk of check_copy (fuzz_wire.asan-ubsan 0x80abc = wire_sigma WS_check_copy) from the
   callee contracts its statement names, i.e. lib/B/Prog/check_copy_cg.v wire_check_copy_cg; the image-B twin of
   lib/A/Prog/check_copy_cgW_walk.v (the same lemmas and steps at image B's names and offsets), in the form of
   reac-repacer/fuzz_uci's image-B walk of check_value (lib/B/Prog/check_value_cgW.v): the straight-line segments
   run as footprint runs (lib/Lib/ExecF.v evtF; stated in lib/B/Prog/check_copy_cgW_iface.v, proved in
   lib/B/Prog/check_copy_cgW_segs.v) carried into SRr by the leaf kit's bridge (lib/B/Prog/LeafCgFacts.v
   bridge_evtF_stmt_YA0n), an inner journal over the call's stack window, and each call cut by its callee contract.
   lib/B/Prog/check_copy_cgW.v composes this walk with the segment proofs into the frozen statement.

   The inner journal (YCbq.v ajournal_sub_init) starts at the entry state with the stack window
   [spZ regs - CC_STK, spZ regs) and the footprint [c, c + n) when n > 0 (the bytes rp_copy_untag's memmove writes;
   empty when n = 0, where no byte of c is written and c may be any address). The closing theorem composes it into
   the caller's journal (YCbq.v ajournal_sub), which asks of each footprint byte what the statement's premise
   gives: inFP FP or in_tmp_block.

   The calls, in order, and what cuts each:
     rp_copy_untag (c, n) at +0x3c   its frozen contract (lib/B/Prog/rp_copy_untag_cg.v), carried through the
                                     journal by cc_rcu_call (YCbq.v ajournal_after_write over its stack window and
                                     the bytes [c + 12, c + n - 4) it moves); a0 = copy_untag_result n bs
     malloc (max n 1) at +0x4c       YC5d.v amalloc04_rule: the chain is empty (s0 = got, and 0 <= got <= n <= 1600
                                     is below sp), so the trace is wire_cc_ufix's first; the depot premise is the
                                     statement's st_depot Sc <> []
     __asan_memcpy (u, f, n) +0x68   YCbq.v aj_intrin_at: u is the call's new block, f lies in a block of the
                                     caller, the two are disjoint
     __asan_memcpy (u+12, f+16, n-16) at +0x138 on the tagged path, the same rule
     bcmp (c, u, got) at +0x1d0      YCbq.v aj_bcmp_at; it returns 0, since c holds cu_bytes n bs and u holds the
                                     same bytes (lib/Prog/rp_copy_untag_c.v; cc_ut_cu), so `bnez a0` is not taken
     free (u) at +0x1dc              YC5d.v afree04_rule, wire_cc_ufix's second trace
   The abort (+0x238 / +0x23c) is reached only from branches this walk refutes: the malloc rule never returns NULL,
   `beq s0, a0` holds because got is the want of u's bytes (cc_got_want), and `bnez a0` after the bcmp fails
   because the compared bytes are equal. The eight report calls are not reached: every checked load reads a byte of
   f or of u, each inside a live block whose shadow allows it (range_addressable_of_block); nor is `unimp` at +0x240,
   the target of the ten UBSan checks of f + 12 .. f + 17 and u + 12 .. u + 17 (both lie in application memory, the
   segment proofs refute each). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0d YI00 YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import check_copy_cgW_iface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require
LeafCgKit LeafCgFacts LeafCgGlue WirePImg WireCcLeafb check_copy_cg rp_copy_untag_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_copy_untag_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module WCL := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.WireCcLeafb.
Module AC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
Module BImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Img0.
Module CC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_copy_cg.
Module PRU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_copy_untag_cg.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-free helpers (the uci template's cv_* at this unit's names)          *)
(* ======================================================================== *)

(* A byte outside one range of a frame write (Lib/Frame.v munch). *)
Lemma cc_outside : forall x lo hi, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) ->
  outside [(lo, hi)] (bv_unsigned (Z_to_bv 64 x)).
Proof.
  intros x lo hi Hx Hn. cbn [outside].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hx.
  split; [exact Hn | exact I].
Qed.

Lemma cc_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact WirePImg.wire_segs_low. Qed.

Lemma cc_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

(* The allocator's trace at a call (YCbq.v call_trace0) is WireCg.v's wire_utrace of the return address followed by
   the chain's return addresses. *)
Lemma cc_trace0 : forall pc0 regs ch, call_trace0 pc0 regs ch = wire_utrace pc0 (raZ regs :: spine ch).
Proof.
  intros pc0 regs ch. unfold call_trace0, unwind_of_chain, wire_utrace.
  assert (E : flat_map (fun ra : Z => if ra =? pc0 then [] else [ra]) (raZ regs :: spine ch) =
              flat_map (fun r : Z * Z * Z => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end)
                ((spZ regs, raZ regs, s0Z regs) :: ch)).
  { cbn [flat_map]. f_equal. unfold spine. induction ch as [|[[fp ra] nfp] ch IH]; [reflexivity|].
    cbn [flat_map map fst snd]. rewrite IH. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* A frame pointer at or below sp ends the chain (YG00.v bad_next): at each allocator call of check_copy s0 holds
   got, and 0 <= got <= n <= 1600 is far below the stack. *)
Lemma cc_chain_nil : forall ly rd (regsT : bvmap 5 word),
  4096 <= raZ regsT -> s0Z regsT <= spZ regsT -> chain_pre ly rd regsT [].
Proof.
  intros ly rd regsT Hra Hs. unfold chain_pre. split; [exact Hra|].
  destruct (frame0_ok ly regsT); [|reflexivity].
  unfold bad_next. rewrite (proj2 (Z.leb_le _ _) Hs). reflexivity.
Qed.

Lemma cc_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma cc_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells BImg.rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells BImg.rsegs m' A cs.
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

(* The footprint the call site picks (the kit's RNG_W) avoids the world's hidden bytes by its own definition. *)
Lemma cc_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from the kit's configuration at pc, carried into SRr by the leaf kit's bridge: the walk
   continues from every state the transported run can reach. *)
Lemma cc_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF BImg.rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv BImg.rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cc_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

Lemma cc_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma cc_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

Lemma cc_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
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
  repeat split; (etransitivity; [apply (cc_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma cc_perm_dup : forall {X : Type} (l rest : list X) (x : X),
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

Lemma cc_perm_rm : forall {X : Type} (l1 l2 rest : list X) (x : X),
  Permutation (l1 ++ x :: l2) (x :: rest) -> Permutation (l1 ++ l2) rest.
Proof.
  intros X l1 l2 rest x H. apply Permutation_sym. eapply Permutation_cons_app_inv. apply Permutation_sym. exact H.
Qed.

(* ---- the view against the raw bytes the footprint runs read ---- *)

Lemma cc_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma cc_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd BImg.rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma cc_mrd_of_aview : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> mrd BImg.rsegs mem (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v E. pose proof (cc_aview_vis W mem a v E) as Hv.
  rewrite (cc_aview_mrd W mem a Hv) in E.
  destruct (mrd BImg.rsegs mem (wa a)) as [b|]; cbn in E; [|discriminate].
  injection E as E. subst v. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

Lemma cc_present_vis : forall (W : world tfibsegs) m a, apresent (w_H W) m a -> aview tfibsegs (w_H W) m a <> None.
Proof.
  intros W m a (Hh & b & Hb). rewrite (cc_aview_mrd W m a Hh). unfold mrd, wa. rewrite Hb. discriminate.
Qed.

Lemma cc_le_byte1 : forall v, 0 <= v < 256 -> Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. apply Z.mod_small. lia.
Qed.

Lemma cc_garr8_aview : forall (H : word -> bool) mem a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H mem a l j G Hj. destruct (G j Hj) as [V R]. specialize (V 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  unfold YO0f.le_byte, YG0f.le_byte. rewrite Z_to_bv_unsigned, (cc_le_byte1 _ R).
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cc_garr8_of_aview : forall (H : word -> bool) mem a (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H mem) a l.
Proof.
  intros H mem a l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r.
  unfold aview in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. f_equal. apply bv_eq. unfold YO0f.le_byte, YG0f.le_byte.
  rewrite Z_to_bv_unsigned, (cc_le_byte1 _ R), <- E.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ---- the footprint over visible bytes, and the shadow cover of a range ---- *)

Lemma cc_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hbj. unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros k Hk.
  rewrite (cc_u64 b) by lia. apply H. lia.
Qed.

Lemma cc_shadow_addr_eq : forall a, AC.shadow_addr a = YG0f.shadow_addr a.
Proof. intros a. unfold AC.shadow_addr, YG0f.shadow_addr, AC.ASAN_K, SHADOW_OFF. lia. Qed.

Lemma cc_rng_hull : forall (W : world tfibsegs) mem x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 48 ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x n ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (cc_hull_lo x) (cc_hull_len x n).
Proof.
  intros W mem x n H0 Hn H1 H. unfold cc_hull_lo, cc_hull_len. rewrite !cc_shadow_addr_eq.
  assert (B1 : 0 <= YG0f.shadow_addr x / 8 * 8) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  assert (B2 : YG0f.shadow_addr x / 8 * 8 <= YG0f.shadow_addr (x + n - 1) / 8 * 8)
    by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
        unfold YG0f.shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (B3 : YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8 <= 2 ^ 64) by (unfold YG0f.shadow_addr, SHADOW_OFF; lia).
  apply cc_rng; [exact B1 | lia |]. intros s Hs.
  specialize (H s ltac:(lia)).
  destruct (aview tfibsegs (w_H W) mem s) as [v|] eqn:E; [|exfalso; exact (H eq_refl)].
  exact (cc_aview_vis W mem s v E).
Qed.

Lemma cc_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk BImg.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* ======================================================================== *)
(* The model: the bytes of u and the want test (lib/Prog/rp_copy_untag_c.v)    *)
(* ======================================================================== *)

(* u's bytes after fuzz_dup's copy of the n frame bytes and, on the tagged path, untagged's move of
   [f + 16, f + n) to u + 12 (fuzz_wire.c untagged, inlined); and the length it reports. *)
Definition cc_ut_bytes (n : Z) (bs : list byte) : list byte :=
  if ((18 <=? n) && PRc.cu_tagged bs)%bool then upd_bytes bs 12 (firstn (Z.to_nat (n - 16)) (skipn 16 bs)) else bs.
Definition cc_ut_len (n : Z) (bs : list byte) : Z := if ((18 <=? n) && PRc.cu_tagged bs)%bool then n - 4 else n.

(* check_copy's want (the four byte tests on u and the reported length) is rp_copy_untag's result: the two read the
   same frame, and past n >= 50 the two moves agree. *)
Lemma cc_got_want : forall n bs, 50 <= n ->
  cc_want (PRc.cu_byte (cc_ut_bytes n bs) 12) (PRc.cu_byte (cc_ut_bytes n bs) 13)
          (PRc.cu_byte (cc_ut_bytes n bs) 16) (PRc.cu_byte (cc_ut_bytes n bs) 17) (cc_ut_len n bs)
  = PRc.copy_untag_result n bs.
Proof.
  intros n bs Hn. unfold cc_want, cc_ut_bytes, cc_ut_len, PRc.copy_untag_result, PRc.cu_bytes, PRc.cu_len,
    PRc.cu_moves.
  rewrite (proj2 (Z.ltb_ge n 50)) by lia.
  rewrite (proj2 (Z.leb_le 18 n)), (proj2 (Z.leb_le 50 n)) by lia.
  reflexivity.
Qed.

Lemma cc_got_lo : forall n bs, 0 <= n -> 0 <= PRc.copy_untag_result n bs <= n.
Proof.
  intros n bs Hn. unfold PRc.copy_untag_result, PRc.cu_len, PRc.cu_moves.
  destruct (Z.ltb_spec n 50); [lia|].
  destruct (_ && _ && _ && _)%bool; [|lia]. destruct (_ && _)%bool; lia.
Qed.

(* Past n >= 50 the bytes u holds are the bytes the frame c holds after the call. *)
Lemma cc_ut_cu : forall n bs, 50 <= n -> cc_ut_bytes n bs = PRc.cu_bytes n bs.
Proof.
  intros n bs Hn. unfold cc_ut_bytes, PRc.cu_bytes, PRc.cu_moves.
  rewrite (proj2 (Z.leb_le 18 n)), (proj2 (Z.leb_le 50 n)) by lia. reflexivity.
Qed.

Lemma cc_ut_bytes_len : forall n bs, 0 <= n -> Z.of_nat (length bs) = n ->
  length (cc_ut_bytes n bs) = length bs.
Proof.
  intros n bs H0 HL. unfold cc_ut_bytes. destruct ((18 <=? n) && PRc.cu_tagged bs)%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E _]. apply Z.leb_le in E.
  apply upd_bytes_length. rewrite firstn_length, skipn_length. lia.
Qed.

Lemma cc_cu_bytes_len : forall n bs, 0 <= n -> Z.of_nat (length bs) = n ->
  length (PRc.cu_bytes n bs) = length bs.
Proof.
  intros n bs H0 HL. unfold PRc.cu_bytes. destruct (PRc.cu_moves n bs) eqn:E; [|reflexivity].
  unfold PRc.cu_moves in E. apply andb_prop in E as [E _]. apply Z.leb_le in E.
  apply upd_bytes_length. rewrite firstn_length, skipn_length. lia.
Qed.

Lemma cc_nth_firstn : forall (l : list byte) (k i : nat) d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros k i d Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct k as [|k]; [lia|]. cbn [firstn]. destruct i as [|i]; cbn [nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma cc_nth_skipn : forall (l : list byte) (k i : nat) d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  induction l as [|x l IH]; intros k i d.
  - rewrite skipn_nil. rewrite !nth_overflow by (cbn [length]; lia). reflexivity.
  - destruct k as [|k]; cbn [skipn Nat.add]; [reflexivity|]. apply IH.
Qed.

Lemma cc_nth_upd : forall (l ins : list byte) (k i : nat) d,
  (k + length ins <= length l)%nat -> (i < length l)%nat ->
  nth i (upd_bytes l k ins) d =
  if (Nat.leb k i && Nat.ltb i (k + length ins))%bool then nth (i - k) ins d else nth i l d.
Proof.
  intros l ins k i d Hk Hi. unfold upd_bytes.
  destruct (Nat.leb k i && Nat.ltb i (k + length ins))%bool eqn:Eb.
  - apply andb_prop in Eb as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    rewrite app_nth2 by (rewrite firstn_length; lia).
    rewrite firstn_length, Nat.min_l by lia.
    rewrite app_nth1 by lia. reflexivity.
  - apply andb_false_iff in Eb as [E|E].
    + apply Nat.leb_gt in E. rewrite app_nth1 by (rewrite firstn_length; lia). apply cc_nth_firstn. lia.
    + apply Nat.ltb_ge in E.
      rewrite app_nth2 by (rewrite firstn_length; lia).
      rewrite firstn_length, Nat.min_l by lia.
      rewrite app_nth2 by lia. rewrite cc_nth_skipn. f_equal. lia.
Qed.

Lemma cc_nth_map : forall (l : list byte) j, nth j (map (fun b : byte => bv_unsigned b) l) 0 = PRc.cu_byte l j.
Proof.
  intros l j. unfold PRc.cu_byte.
  change (nth j (map (fun b : byte => bv_unsigned b) l) 0)
    with (nth j (map (fun b : byte => bv_unsigned b) l) ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0))).
  apply map_nth.
Qed.

Lemma cc_byte_rng : forall (l : list byte) j, 0 <= PRc.cu_byte l j < 256.
Proof.
  intros l j. unfold PRc.cu_byte. pose proof (bv_unsigned_in_range 8 (nth j l (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. lia.
Qed.

(* ======================================================================== *)
(* The walk                                                                   *)
(* ======================================================================== *)

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HMPC : pc_wrap_malloc (as_code B) = wire_sigma WS___interceptor_trampoline_malloc.
Hypothesis HFPC : pc_wrap_free (as_code B) = wire_sigma WS___interceptor_trampoline_free.
Hypothesis HCELLS : wire_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis UFIX : CC.wire_cc_ufix B.
Hypothesis AMALLOC : forall fx' : YK11.FPState, @amalloc04_rule fx' rc sink segs B MT.
Hypothesis AFREE : forall fx' : YK11.FPState, @afree04_rule fx' rc sink segs B MT.
Hypothesis AMEMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (wire_sigma WS___asan_memcpy).
Hypothesis ABCMP : forall fx' : YK11.FPState,
  @abcmp_realizes fx' rc segs B (wire_sigma WS___interceptor_trampoline_bcmp).
Hypothesis ARCU : forall fx' : YK11.FPState, @PRU.wire_rp_copy_untag_cg fx' rc B (wire_sigma WS_rp_copy_untag).
(* The footprint runs of the straight-line segments (lib/B/Prog/check_copy_cgW_iface.v). *)
Hypothesis SEG_ENTRY : cc_seg_entry_F.
Hypothesis SEG_M : cc_seg_m_F.
Hypothesis SEG_Z : cc_seg_z_F.
Hypothesis SEG_CP1 : cc_seg_cp1_F.
Hypothesis SEG_SHORT : cc_seg_short_F.
Hypothesis SEG_TAG_YES : cc_seg_tag_yes_F.
Hypothesis SEG_TAG_NO : cc_seg_tag_no_F.
Hypothesis SEG_CP2RET : cc_seg_cp2ret_F.
Hypothesis SEG_WANT_LO : cc_seg_want_lo_F.
Hypothesis SEG_WANT_HI : cc_seg_want_hi_F.
Hypothesis SEG_BCMPRET : cc_seg_bcmpret_F.
Hypothesis SEG_END : cc_seg_end_F.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

(* A run that writes no memory: the journal follows its same_but_materialized. *)
Lemma cc_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS cc_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc'
            (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

(* A block in front of `rest` in a permutation of the live blocks is not also in `rest`. *)
Lemma cc_not_old : forall ly S W m md (x : Z * Z) rest,
  AR segs B ly S W m md -> Permutation (ablocks B ly S) (x :: rest) -> 0 < req_size (snd x) -> ~ In x rest.
Proof.
  intros ly S W m md [p nb] rest HAR HP Hn Hin. cbn [snd] in Hn.
  destruct (cc_perm_dup _ _ _ HP Hin) as (l1 & l2 & l3 & E).
  pose proof (sep_blocks_pos segs B LAWS ly S W m md (p, nb) (p, nb) l1 l2 l3 HAR E) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* A byte of a live block the call did not touch keeps its view (YCbq.v acall_kept, the kept-block clause). *)
Lemma cc_kept_block : forall lyX SX WX mX WY mY slo shi (E : Z -> Prop) b m a,
  @acall_kept rc segs B lyX SX WX mX WY mY slo shi E ->
  In (b, m) (ablocks B lyX SX) -> b <= a < b + req_size m -> ~ E a ->
  aview segs (w_H WY) mY a = aview segs (w_H WX) mX a.
Proof.
  intros lyX SX WX mX WY mY slo shi E b m a (_ & G2 & _) Hin Hr HnE.
  pose proof (G2 b m (a - b) Hin ltac:(lia)
    ltac:(replace (b + (a - b)) with a by lia; exact HnE)) as E2.
  replace (b + (a - b)) with a in E2 by lia. exact E2.
Qed.

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (c f n T : Z)
  (bs : list byte).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 c.
Hypothesis H11 : YK11.getr regs 11 = w64 f.
Hypothesis H12 : YK11.getr regs 12 = w64 n.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - CC.CC_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hn : 0 <= n <= CC.CC_RECV_MAX.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis HblkC : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= c /\ c + n <= bA + nA.
Hypothesis HblkF : 0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA.
Hypothesis Hdj : 0 < n -> c + n <= f \/ f + n <= c.
Hypothesis HFPc : forall x, c <= x < c + n -> inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) x.
Hypothesis HgC : garr8 segs (mrestrict (w_H W) memc) c (map (fun b : byte => bv_unsigned b) bs).
Hypothesis HgF : garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs).
Hypothesis Hdepot : st_depot Sc <> [].
Hypothesis Hnev : st_nev S + k + CC.CC_EV <= EV_MAX.
Hypothesis Hlive : blocks_bytes Sc + CC.CC_LIVE <= LIVE_MAX.
Hypothesis Hmo : mo_ok MT Sc T.
Hypothesis Hcost : CC.wire_check_copy_cost MT n <= T.

Local Abbreviation POST := (@CC.wire_cc_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c n).
(* The bytes rp_copy_untag's memmove writes: the inner journal's footprint. *)
Definition cc_FP1 : list (Z * Z) := if 0 <? n then [(c, c + n)] else [].
Local Abbreviation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA CC.CC_STK (spZ regs) cc_FP1 lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).
Local Abbreviation G := (PRc.copy_untag_result n bs).

(* The frame the prologue wrote: the caller's s5 .. s0 and ra at [spZ regs - 0x38, spZ regs). *)
Definition cc_frame (m : word -> option byte) : Prop :=
  exists v0, rw_cells BImg.rsegs m (spZ regs - 64)
    (C8 v0 :: cc_fr (GR regs 21) (GR regs 20) (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)).

(* The registers the walk keeps from the prologue on: sp (the frame), gp, tp, s1 = c, s3 = n, s4 = f,
   s5 = the shadow base, and s6 .. s11 untouched. *)
Definition cc_kept (rg : bvmap 5 word) : Prop :=
  GR rg 2 = w64 (spZ regs - 64) /\ GR rg 3 = GR regs 3 /\ GR rg 4 = GR regs 4 /\
  GR rg 9 = w64 c /\ GR rg 19 = w64 n /\ GR rg 20 = w64 f /\ GR rg 21 = w64 AC.ASAN_K /\
  GR rg 22 = GR regs 22 /\ GR rg 23 = GR regs 23 /\ GR rg 24 = GR regs 24 /\ GR rg 25 = GR regs 25 /\
  GR rg 26 = GR regs 26 /\ GR rg 27 = GR regs 27.

(* What c holds after the call to rp_copy_untag, and what the fresh block u holds after the copies. *)
Definition cc_c_holds (W1 : world segs) (m1 : word -> option byte) : Prop :=
  forall i, 0 <= i < n -> aview segs (w_H W1) m1 (c + i) = Some (PRc.cu_byte (PRc.cu_bytes n bs) (Z.to_nat i)).
Definition cc_u_holds (W1 : world segs) (m1 : word -> option byte) (P : Z) : Prop :=
  forall i, 0 <= i < n -> aview segs (w_H W1) m1 (P + i) = Some (PRc.cu_byte (cc_ut_bytes n bs) (Z.to_nat i)).
(* The frame f is read, never written: it holds its entry bytes at every state of the walk. *)
Definition cc_f_holds (W1 : world segs) (m1 : word -> option byte) : Prop :=
  forall i, 0 <= i < n -> aview segs (w_H W1) m1 (f + i) = Some (PRc.cu_byte bs (Z.to_nat i)).
(* What the fresh block holds after fuzz_dup's copy, before untagged's move. *)
Definition cc_u0_holds (W1 : world segs) (m1 : word -> option byte) (P : Z) : Prop :=
  forall i, 0 <= i < n -> aview segs (w_H W1) m1 (P + i) = Some (PRc.cu_byte bs (Z.to_nat i)).

(* The byte at index j of the frame u holds after untagged's move. *)
Lemma cc_ut_byte : forall (j : nat), (j < length bs)%nat -> 18 <= n -> PRc.cu_tagged bs = true ->
  PRc.cu_byte (cc_ut_bytes n bs) j =
  if (Nat.leb 12 j && Nat.ltb j (12 + Z.to_nat (n - 16)))%bool
  then PRc.cu_byte bs (j - 12 + 16) else PRc.cu_byte bs j.
Proof.
  intros j Hj H18 Htag. unfold cc_ut_bytes, PRc.cu_byte.
  rewrite (proj2 (Z.leb_le 18 n) H18), Htag. cbn [andb].
  assert (Hins : length (firstn (Z.to_nat (n - 16)) (skipn 16 bs)) = Z.to_nat (n - 16))
    by (rewrite firstn_length, skipn_length; lia).
  rewrite (cc_nth_upd bs _ 12 j (Z_to_bv 8 0) ltac:(rewrite Hins; lia) Hj), Hins.
  destruct (Nat.leb 12 j && Nat.ltb j (12 + Z.to_nat (n - 16)))%bool eqn:Eb; [|reflexivity].
  apply andb_prop in Eb as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
  rewrite cc_nth_firstn by lia. rewrite cc_nth_skipn.
  replace (16 + (j - 12))%nat with (j - 12 + 16)%nat by lia. reflexivity.
Qed.

Ltac kp_by HP i K := etransitivity; [apply (HP i); unfold acallee_saved; lia | exact K].

Lemma cc_kept_pres : forall r1 r2, cc_kept r1 -> aregs_preserved r1 r2 -> cc_kept r2.
Proof.
  intros r1 r2 (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27) HP.
  unfold cc_kept.
  split; [kp_by HP 2 K2|]. split; [kp_by HP 3 K3|]. split; [kp_by HP 4 K4|]. split; [kp_by HP 9 K9|].
  split; [kp_by HP 19 K19|]. split; [kp_by HP 20 K20|]. split; [kp_by HP 21 K21|]. split; [kp_by HP 22 K22|].
  split; [kp_by HP 23 K23|]. split; [kp_by HP 24 K24|]. split; [kp_by HP 25 K25|]. split; [kp_by HP 26 K26|].
  kp_by HP 27 K27.
Qed.

(* ---- facts of the entry ---- *)

Lemma cc_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cc_JI0 : JI lyc Sc W memc mdc 0.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CC.CC_STK (spZ regs) cc_FP1
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CC.CC_STK, CC.CC_FRAME, ASTACK. lia.
  - lia.
Qed.

Lemma cc_sp_rng : YM05.alloc_ceiling + CC.CC_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cc_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc2 & Hlo & Hhi & H47 & _) & _).
  lia.
Qed.

Lemma cc_ly_top : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> ly_top ly1 <= 2 ^ 47.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & _ & _ & Hshi & H47 & _ & Htop2 & Htop) & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). rewrite Etop. lia.
Qed.

Lemma cc_win : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 ->
  forall a, spZ regs - CC.CC_STK <= a < spZ regs -> apresent (w_H W1) m1 a.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma cc_AR : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> AR segs B ly1 S1 W1 m1 md1.
Proof. intros ly1 S1 W1 m1 md1 k1 J. destruct J as (HAR & _). exact HAR. Qed.

Lemma cc_slo : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> ly_stk_lo ly1 = ly_stk_lo lyc.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J. destruct J as (_ & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _). exact Eslo.
Qed.

Lemma cc_stklo : ly_stk_lo lyc + CC.CC_STK <= spZ regs.
Proof.
  pose proof cc_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & _ & Hlo & _) & _). exact Hlo.
Qed.

Lemma cc_nevJ : forall ly1 S1 W1 m1 md1 k1, JI ly1 S1 W1 m1 md1 k1 -> k1 <= 1 -> st_nev S1 < EV_MAX.
Proof.
  intros ly1 S1 W1 m1 md1 k1 J Hk.
  destruct J as (_ & _ & _ & _ & _ & _ & Hn1 & _).
  destruct HJ as (_ & _ & _ & _ & _ & _ & Hn0 & _).
  unfold CC.CC_EV in Hnev. lia.
Qed.

Lemma cc_cost : 0 <= mo_malloc MT (Z.max n 1) /\ 0 <= mo_free MT /\ mo_malloc MT (Z.max n 1) + mo_free MT <= T.
Proof.
  pose proof (mo_malloc_nonneg MT MTL (Z.max n 1) ltac:(lia)).
  pose proof (mo_free_nonneg MT MTL).
  unfold CC.wire_check_copy_cost in Hcost. lia.
Qed.

(* The footprint of the inner journal: the bytes of c the call writes. *)
Lemma cc_FP1_closed : ~ YI16.sink_open_fp cc_FP1.
Proof.
  unfold cc_FP1. destruct (Z.ltb_spec 0 n) as [Hpos|Hz]; [|apply sink_closed_nil].
  apply sink_closed_pos. apply Forall_cons; [|apply Forall_nil]. cbn [fst].
  destruct (HblkC Hpos) as (bA & nA & HbA & H1 & H2).
  pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA cc_HARc HbA) as (_ & H4096 & _).
  lia.
Qed.

Lemma cc_FP1_in : forall a, inFP cc_FP1 a -> c <= a < c + n.
Proof.
  intros a Ha. unfold cc_FP1 in Ha. destruct (Z.ltb_spec 0 n) as [Hpos|Hz].
  - destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
  - destruct Ha as (r & [] & _).
Qed.

Lemma cc_FP1_cover : forall a, 0 < n -> c <= a < c + n -> inFP cc_FP1 a.
Proof.
  intros a Hpos Ha. unfold cc_FP1. rewrite (proj2 (Z.ltb_lt 0 n) Hpos).
  exists (c, c + n). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

(* The frame [spZ regs - 64, spZ regs) lies above every callee's stack window. *)
Lemma cc_frame_kept : forall (W1 W2 : world segs) (m1 m2 : word -> option byte),
  cc_frame m1 ->
  (forall a, spZ regs - CC.CC_STK <= a < spZ regs -> apresent (w_H W1) m1 a) ->
  (forall a, spZ regs - CC.CC_STK <= a < spZ regs -> apresent (w_H W2) m2 a) ->
  (forall a, spZ regs - 64 <= a < spZ regs -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  cc_frame m2.
Proof.
  intros W1 W2 m1 m2 (v0 & F) P1 P2 E. exists v0.
  pose proof cc_sp_rng as [S1 S2].
  apply (cc_rw_cells_ext m1 m2 _ _ F). intros a Ha.
  change (Z.of_nat (cells_size (C8 v0 :: cc_fr (GR regs 21) (GR regs 20) (GR regs 19) (GR regs 18) (GR regs 9)
                                  (GR regs 8) (GR regs 1)))) with 64 in Ha.
  unfold wa. apply (cc_byte_eq (w_H W1) (w_H W2) m1 m2 a); [apply P1 | apply P2 | apply E];
    unfold CC.CC_STK, CC.CC_FRAME, ASTACK in *; lia.
Qed.

(* ---- the return: cc_seg_end_F, then the post ---- *)
Lemma cc_at_retfree : forall ly2 S2 W2 regs2 m2 md2,
  JI ly2 S2 W2 m2 md2 2 -> frames S2 = frames Sc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  mo_le MT Sc S2 (CC.wire_check_copy_cost MT n) ->
  cc_frame m2 -> cc_kept regs2 -> GR regs2 8 = w64 G -> cc_c_holds W2 m2 ->
  SRr segs W2 (@cfg_at fx segs CC_RET_FREE regs2 m2 md2) POST.
Proof.
  intros ly2 S2 W2 regs2 m2 md2 J2 Hfr Hperm Hle (v0 & FR) HK H8 HC.
  destruct HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 64 + 16384) by reflexivity.
  assert (SP2 : bv_unsigned (GR regs2 2) = spZ regs - 64).
  { rewrite K2. unfold w64. apply cc_u64. lia. }
  eapply (@cc_run fx W2 regs2 m2 md2 CC_RET_FREE).
  { unfold LCK.ms_of_regs. eapply SEG_END.
    - rewrite SP2. exact FR.
    - rewrite SP2. lia.
    - rewrite SP2. apply cc_rng; [lia | lia |]. intros i Hi.
      exact (proj1 (cc_win _ _ _ _ _ _ J2 i ltac:(lia))). }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (cc_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & _ & _ & G18 & G19 & G20 & G21 & G22 & G23 &
    G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV.
  rewrite (cc_ms_shape _ _ _ _ EQV).
  pose proof (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 SBM) as J2'.
  apply SRr_ret. unfold CC.wire_cc_post.
  exists ly2, S2, (ms_regs ms'), m2, md', G, (PRc.cu_bytes n bs).
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS cc_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CC.CC_STK (spZ regs) cc_FP1 [] ly2 S2 W2 m2 md' 2 HJ J2' Hwlo Hwhi) as J.
    cbn [app] in J. apply J.
    intros a Ha. pose proof (cc_FP1_in a Ha) as Hr.
    assert (Hpos : 0 < n) by (unfold cc_FP1 in Ha; destruct (Z.ltb_spec 0 n); [lia|];
                              destruct Ha as (r0 & [] & _)).
    destruct (HFPc a Hr) as [Hin | Htmp]; [|right; exact Htmp].
    left. split; [exact Hin|].
    destruct (HblkC Hpos) as (bA & nA & HbA & H1 & H2).
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA cc_HARc HbA) as (_ & _ & Hc2 & _).
    pose proof (req_size_pos nA ltac:(lia)) as Hrq.
    exists bA, nA. split; [exact HbA | lia]. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc2 : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc2 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
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
  { apply (acall_kept_of_journal segs B cc_segs_low CC.CC_STK (spZ regs) cc_FP1 [] lyc Sc W memc mdc ly2 S2 W2 m2
             md' 2 (fun x => c <= x < c + n) J2' cc_HARc).
    - exact cc_FP1_in.
    - intros b m i Hb _ _. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    - exact cc_FP1_closed. }
  split; [exact Hle|].
  split; [etransitivity; [exact G10|]; exact H8|].
  split; [exact (cc_got_lo n bs ltac:(lia))|].
  split; [rewrite (cc_cu_bytes_len n bs ltac:(lia) Hlen); exact Hlen|].
  apply cc_garr8_of_aview. intros j Hj.
  rewrite length_map, (cc_cu_bytes_len n bs ltac:(lia) Hlen) in Hj.
  rewrite cc_nth_map. split; [|apply cc_byte_rng].
  rewrite (HC (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
Qed.

(* ---- the return addresses of the six calls: their values, parity and the trace names of the statement ---- *)
Lemma cc_cut_ok : forall p,
  In p [CC_RET_RCU; CC_RET_MALLOC; CC_RET_CP1; CC_RET_CP2; CC_RET_BCMP; CC_RET_FREE] ->
  bv_unsigned (Z_to_bv 64 p) = p /\ bv_unsigned (Z_to_bv 64 p) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 p).
Proof.
  intros p Hp. cbn [In] in Hp.
  destruct Hp as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    (split; [|split]); vm_compute; first [reflexivity | discriminate].
Qed.

Lemma cc_ra_malloc_eq : CC_RET_MALLOC = CC.WIRE_CC_RA_MALLOC.
Proof. vm_compute. reflexivity. Qed.
Lemma cc_ra_free_eq : CC_RET_FREE = CC.WIRE_CC_RA_FREE.
Proof. vm_compute. reflexivity. Qed.

(* ---- free (u) at +0x1dc (YC5d.v afree04_rule), then the return ---- *)
Lemma cc_at_freecall : forall ly1 S1 W1 regsF m1 md1 P,
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regsF -> cc_c_holds W1 m1 ->
  GR regsF 1 = Z_to_bv 64 CC_RET_FREE -> GR regsF 10 = w64 P -> GR regsF 8 = w64 G ->
  SRr segs W1 (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 CC_FREE) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros ly1 S1 W1 regsF m1 md1 P J1 Hfr EB Hle HF HK HC G1 G10 G8.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & _).
  pose proof (cc_cut_ok CC_RET_FREE ltac:(cbn; tauto)) as (RV & RE & R4).
  assert (HGl : 0 <= G <= n) by (apply cc_got_lo; lia).
  assert (Hin : In (P, Z.max n 1) (ablocks B ly1 S1))
    by (rewrite EB; apply in_or_app; right; left; reflexivity).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  assert (Hnot : ~ In (P, Z.max n 1) (ablocks B lyc Sc)).
  { intros H. apply (cc_not_old ly1 S1 W1 m1 md1 (P, Z.max n 1) (ablocks B lyc Sc) HAR1).
    - rewrite EB. apply Permutation_sym, Permutation_cons_append.
    - cbn [snd]. rewrite Hreq. lia.
    - exact H. }
  assert (SPF : spZ regsF = spZ regs + -64).
  { change (spZ regsF) with (bv_unsigned (GR regsF 2)). rewrite K2. unfold w64. rewrite cc_u64 by lia. lia. }
  assert (CHAIN : chain_pre ly1 (aview segs (w_H W1) m1) regsF []).
  { apply cc_chain_nil.
    - change (raZ regsF) with (bv_unsigned (GR regsF 1)). rewrite G1. exact R4.
    - change (s0Z regsF) with (bv_unsigned (GR regsF 8)). rewrite G8. unfold w64.
      rewrite cc_u64 by lia. rewrite SPF. lia. }
  assert (TRACE : In (call_trace0 (pc_free_ra0 (as_code B)) regsF []) (as_universe B)).
  { rewrite cc_trace0. cbn [spine map].
    replace (raZ regsF) with CC.WIRE_CC_RA_FREE; [exact (proj2 UFIX)|].
    change (raZ regsF) with (bv_unsigned (GR regsF 1)). rewrite G1, RV. symmetry. exact cc_ra_free_eq. }
  pose proof cc_cost as (Mc1 & Mc2 & Msum).
  assert (MOK : mo_ok MT S1 (mo_free MT)).
  { apply (mok_station MT Sc S1 T (mo_malloc MT (Z.max n 1)) (mo_free MT) MTL Hmo Hle Mc2). lia. }
  assert (EF : CC_FREE = pc_wrap_free (as_code B)) by (rewrite HFPC; reflexivity).
  rewrite EF.
  eapply SRr_bind.
  - exact (AFREE fx W1 regsF m1 CC.CC_STK (spZ regs) cc_FP1 lyc Sc W memc mdc [] ly1 S1 md1 1 P (Z.max n 1) (-64)
             (Z_to_bv 64 CC_RET_FREE) [] J1 Hin G10 SPF eq_refl ltac:(lia)
             ltac:(unfold CC.CC_STK, CC.CC_FRAME, ASTACK; lia)
             (eq_trans K3 Hgp) (eq_trans K4 Htp) G1 (YK0s.ret_ok_even _ RE)
             (cc_nevJ _ _ _ _ _ _ J1 ltac:(lia)) CHAIN TRACE (fun H => False_ind _ (Hnot H)) MOK).
  - intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & -> & J2 & HRP & HBL & HFR & HKEPT & HML).
    apply (cc_at_retfree ly2 S2 W2 regs2 m2 md2).
    + exact J2.
    + rewrite HFR. exact Hfr.
    + destruct HBL as (l1 & l2 & E1 & E2). rewrite E2. apply (cc_perm_rm l1 l2 _ (P, Z.max n 1)).
      rewrite <- E1, EB. apply Permutation_sym, Permutation_cons_append.
    + unfold CC.wire_check_copy_cost. exact (mle_station MT Sc S1 S2 _ _ MTL Hle HML).
    + apply (cc_frame_kept W1 W2 m1 m2 HF (cc_win _ _ _ _ _ _ J1) (cc_win _ _ _ _ _ _ J2)).
      intros a Ha. apply (proj1 HKEPT); [unfold CC.CC_STK, CC.CC_FRAME, ASTACK in *; lia | lia].
    + exact (cc_kept_pres _ _ HK HRP).
    + kp_by HRP 8 G8.
    + (* c's bytes: its block is live at the call and is not the block the free released *)
      intros i Hi.
      destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
      assert (HinA : In (bA, nA) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbA).
      destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bA nA HAR1 HinA) as (_ & _ & HAc & _).
      pose proof (req_size_pos nA ltac:(lia)) as HrA.
      assert (Hne : (bA, nA) <> (P, Z.max n 1)) by (intros E; rewrite E in HbA; exact (Hnot HbA)).
      pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 HinA Hin Hne) as HD.
      unfold zdisjoint in HD. cbn [fst snd] in HD. rewrite Hreq in HD.
      rewrite (cc_kept_block ly1 S1 W1 m1 W2 m2 _ _ _ bA nA (c + i) HKEPT HinA ltac:(lia) ltac:(lia)).
      exact (HC i Hi).
Qed.

(* ---- back from the bcmp at +0x1d4 with a0 = 0: `bnez a0` is not taken, a0 := u, free (u) ---- *)
Lemma cc_at_bcmpret : forall ly1 S1 W1 regsB m1 md1 P,
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regsB -> cc_c_holds W1 m1 ->
  GR regsB 8 = w64 G -> GR regsB 10 = w64 0 -> GR regsB 18 = w64 P ->
  SRr segs W1 (@cfg_at fx segs CC_RET_BCMP regsB m1 md1) POST.
Proof.
  intros ly1 S1 W1 regsB m1 md1 P J1 Hfr EB Hle HF HK HC G8 G10 G18.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  eapply (@cc_run fx W1 regsB m1 md1 CC_RET_BCMP).
  { unfold LCK.ms_of_regs. rewrite G10. apply SEG_BCMPRET. }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
    E24 & E25 & E26 & E27).
  rewrite (cc_ms_shape _ _ _ _ EQV).
  apply (cc_at_freecall ly1 S1 W1 (ms_regs ms') m1 md' P).
  - exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
  - exact Hfr.
  - exact EB.
  - exact Hle.
  - exact HF.
  - unfold cc_kept.
    split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
    split; [rewrite E9; exact K9|]. split; [rewrite E19; exact K19|]. split; [rewrite E20; exact K20|].
    split; [rewrite E21; exact K21|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
    split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
    rewrite E27; exact K27.
  - exact HC.
  - exact E1.
  - rewrite E10. exact G18.
  - rewrite E8. exact G8.
Qed.

(* ---- bcmp (c, u, got) at +0x1d0 (YCbq.v aj_bcmp_at): it returns 0, since c and u hold the same bytes ---- *)
Lemma cc_bcmp_call : forall ly1 S1 W1 regsC m1 md1 P,
  0 < G ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regsC -> cc_c_holds W1 m1 -> cc_u_holds W1 m1 P ->
  GR regsC 1 = Z_to_bv 64 CC_RET_BCMP -> GR regsC 8 = w64 G ->
  GR regsC 10 = w64 c -> GR regsC 11 = w64 P -> GR regsC 12 = w64 G -> GR regsC 18 = w64 P ->
  SRr segs W1 (mkCfg (@YK11.mkst fx regsC (Z_to_bv 64 CC_BCMP) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros ly1 S1 W1 regsC m1 md1 P HG J1 Hfr EB Hle HF HK HC HU G1 G8 G10 G11 G12 G18.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & _).
  pose proof (cc_cut_ok CC_RET_BCMP ltac:(cbn; tauto)) as (RV & RE & R4).
  assert (HGl : 0 <= G <= n) by (apply cc_got_lo; lia).
  assert (H50 : 50 <= n).
  { destruct (Z.ltb_spec n 50) as [Hlt|Hge]; [exfalso|exact Hge].
    unfold PRc.copy_untag_result in HG. rewrite (proj2 (Z.ltb_lt n 50) Hlt) in HG. lia. }
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1))
    by (rewrite EB; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & HP4 & HPc & HPapp & HPb & _).
  rewrite Hreq in HPc, HPapp, HPb.
  destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
  assert (HinA : In (bA, nA) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbA).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bA nA HAR1 HinA) as (_ & HA4 & HAc & HAapp & HAb & _).
  pose proof (req_size_pos nA ltac:(lia)) as HrA.
  assert (SPC : spZ regsC = spZ regs + -64).
  { change (spZ regsC) with (bv_unsigned (GR regsC 2)). rewrite K2. unfold w64. rewrite cc_u64 by lia. lia. }
  eapply SRr_bind.
  { apply (aj_bcmp_at segs B LAWS cc_segs_low CC_BCMP (ABCMP fx) W1 regsC m1 CC.CC_STK (spZ regs) cc_FP1 lyc Sc W memc mdc []
             ly1 S1 md1 1 c P G (-64) (Z_to_bv 64 CC_RET_BCMP) J1 G10 G11 G12).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SPC.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - exact G1.
    - apply YK0s.ret_ok_even. exact RE.
    - intros a Ha. split.
      + replace a with (c + (a - c)) by lia. rewrite (HC (a - c) ltac:(lia)). discriminate.
      + rewrite SPC. unfold ESTACK. lia.
    - intros a Ha. split.
      + replace a with (P + (a - P)) by lia. rewrite (HU (a - P) ltac:(lia)). discriminate.
      + rewrite SPC. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA c G HAR1 HinA); lia.
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P G HAR1 HinP);
        rewrite ?Hreq; lia.
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA c G HAR1 HinA); lia.
    - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 bA nA c G HAR1 HinA); lia.
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P G HAR1 HinP);
        rewrite ?Hreq; lia.
    - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P G HAR1 HinP);
        rewrite ?Hreq; lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & v & -> & J2 & HRP & HA0 & HCMP & HVIEW & HAPP).
  assert (Hv0 : v = w64 0).
  { apply HCMP. intros i Hi. rewrite (HC i ltac:(lia)), (HU i ltac:(lia)).
    rewrite (cc_ut_cu n bs H50). reflexivity. }
  change (mkCfg (YK11.mkst regs2 (Z_to_bv 64 CC_RET_BCMP) m2 (YK11.seg_rom segs)) md2)
    with (@cfg_at fx segs CC_RET_BCMP regs2 m2 md2).
  apply (cc_at_bcmpret ly1 S1 W1 regs2 m2 md2 P).
  - exact J2.
  - exact Hfr.
  - exact EB.
  - exact Hle.
  - apply (cc_frame_kept W1 W1 m1 m2 HF (cc_win _ _ _ _ _ _ J1) (cc_win _ _ _ _ _ _ J2)).
    intros a Ha. apply HVIEW; [lia|]. unfold ESTACK. lia.
  - exact (cc_kept_pres _ _ HK HRP).
  - intros i Hi. rewrite HVIEW; [exact (HC i Hi) | lia |]. unfold ESTACK. lia.
  - kp_by HRP 8 G8.
  - rewrite Hv0 in HA0. exact HA0.
  - kp_by HRP 18 G18.
Qed.

(* ---- CC_WANT: the want test on u's bytes; got is that want (cc_got_want), so `beq s0, a0` is taken ---- *)
Lemma cc_at_want : forall ly1 S1 W1 regsW m1 md1 P,
  18 <= n ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regsW -> cc_c_holds W1 m1 -> cc_u_holds W1 m1 P ->
  GR regsW 8 = w64 G -> GR regsW 12 = w64 (cc_ut_len n bs) -> GR regsW 18 = w64 P ->
  SRr segs W1 (@cfg_at fx segs CC_WANT regsW m1 md1) POST.
Proof.
  intros ly1 S1 W1 regsW m1 md1 P H18 J1 Hfr EB Hle HF HK HC HU G8 G12 G18.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1))
    by (rewrite EB; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & HP4 & HPc & HPapp & HPb & _).
  rewrite Hreq in HPc, HPapp, HPb.
  destruct (Z_lt_le_dec n 50) as [Hlt | H50].
  - (* n < 50: the want is 0, and so is got; the compare is skipped and u is freed *)
    assert (HG0 : G = 0)
      by (unfold PRc.copy_untag_result; rewrite (proj2 (Z.ltb_lt n 50) Hlt); reflexivity).
    eapply (@cc_run fx W1 regsW m1 md1 CC_WANT).
    { unfold LCK.ms_of_regs. rewrite G8, HG0, G18, K19. apply SEG_WANT_LO; lia. }
    intros ms' md' (ms0 & -> & EQV) SBM.
    destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
      E24 & E25 & E26 & E27).
    rewrite (cc_ms_shape _ _ _ _ EQV).
    apply (cc_at_freecall ly1 S1 W1 (ms_regs ms') m1 md' P).
    + exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
    + exact Hfr.
    + exact EB.
    + exact Hle.
    + exact HF.
    + unfold cc_kept.
      split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
      split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; exact K20|].
      split; [rewrite E21; exact K21|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
      split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
      rewrite E27; exact K27.
    + exact HC.
    + exact E1.
    + exact E10.
    + rewrite E8, HG0. reflexivity.
  - (* n >= 50: the four checked loads of u, then `beq s0, a0` *)
    assert (HL : 0 <= cc_ut_len n bs < 2 ^ 63)
      by (unfold cc_ut_len; destruct ((18 <=? n) && PRc.cu_tagged bs)%bool; lia).
    assert (HW : cc_want (PRc.cu_byte (cc_ut_bytes n bs) 12) (PRc.cu_byte (cc_ut_bytes n bs) 13)
                   (PRc.cu_byte (cc_ut_bytes n bs) 16) (PRc.cu_byte (cc_ut_bytes n bs) 17) (cc_ut_len n bs) = G)
      by (apply cc_got_want; lia).
    assert (MR : forall j, 0 <= j < n ->
              mrd BImg.rsegs m1 (wa (P + j)) = Some (Z_to_bv 8 (PRc.cu_byte (cc_ut_bytes n bs) (Z.to_nat j))))
      by (intros j Hj; apply (cc_mrd_of_aview W1); exact (HU j Hj)).
    eapply (@cc_run fx W1 regsW m1 md1 CC_WANT).
    { unfold LCK.ms_of_regs. rewrite G8, <- HW, G12, G18, K19, K21.
      eapply SEG_WANT_HI.
      - lia.
      - lia.
      - exact HL.
      - apply (@WCL.wcc_leafb_addressable_block rc B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
          rewrite ?Hreq; lia.
      - apply (@WCL.wcc_leafb_rng_block rc B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
          rewrite ?Hreq; lia.
      - apply (cc_rng_hull W1 m1 P n); [lia | lia | lia |].
        apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
          rewrite ?Hreq; lia.
      - apply cc_byte_rng.
      - apply cc_byte_rng.
      - apply cc_byte_rng.
      - apply cc_byte_rng.
      - pose proof (MR 12 ltac:(lia)) as M12. cbn [Z.to_nat] in M12. exact M12.
      - pose proof (MR 13 ltac:(lia)) as M13. cbn [Z.to_nat] in M13. exact M13.
      - pose proof (MR 16 ltac:(lia)) as M16. cbn [Z.to_nat] in M16. exact M16.
      - pose proof (MR 17 ltac:(lia)) as M17. cbn [Z.to_nat] in M17. exact M17. }
    intros ms' md' (ms0 & (a1' & a2' & a3' & [(HW0 & ->) | (HWp & ->)]) & EQV) SBM.
    + (* the want is 0: no compare, free (u) *)
      destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 &
        E23 & E24 & E25 & E26 & E27).
      rewrite (cc_ms_shape _ _ _ _ EQV).
      apply (cc_at_freecall ly1 S1 W1 (ms_regs ms') m1 md' P).
      * exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
      * exact Hfr.
      * exact EB.
      * exact Hle.
      * exact HF.
      * unfold cc_kept.
        split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
        split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; exact K20|].
        split; [rewrite E21; reflexivity|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
        split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
        rewrite E27; exact K27.
      * exact HC.
      * exact E1.
      * exact E10.
      * rewrite E8, <- HW, HW0. reflexivity.
    + (* the want is positive: bcmp (c, u, got) *)
      destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
        E23 & E24 & E25 & E26 & E27).
      rewrite (cc_ms_shape _ _ _ _ EQV).
      assert (HGL : G = cc_ut_len n bs)
        by (rewrite <- HW; unfold cc_want in HW, HWp |- *;
            destruct ((_ =? 136) && (_ =? 25) && (_ =? 0) && (_ =? 0))%bool; [reflexivity | lia]).
      apply (cc_bcmp_call ly1 S1 W1 (ms_regs ms') m1 md' P).
      * rewrite HW in HWp. exact HWp.
      * exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
      * exact Hfr.
      * exact EB.
      * exact Hle.
      * exact HF.
      * unfold cc_kept.
        split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
        split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; exact K20|].
        split; [rewrite E21; reflexivity|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
        split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
        rewrite E27; exact K27.
      * exact HC.
      * exact HU.
      * exact E1.
      * rewrite E8, HGL. reflexivity.
      * rewrite E10. exact K9.
      * exact E11.
      * rewrite E12, HGL. reflexivity.
      * exact E18.
Qed.

(* ---- __asan_memcpy (u + 12, f + 16, n - 16) at +0x138 (untagged's move), then CC_WANT ---- *)
Lemma cc_cp2_call : forall ly1 S1 W1 regsM m1 md1 P,
  18 <= n -> PRc.cu_tagged bs = true ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regsM -> cc_c_holds W1 m1 -> cc_f_holds W1 m1 -> cc_u0_holds W1 m1 P ->
  GR regsM 1 = Z_to_bv 64 CC_RET_CP2 -> GR regsM 8 = w64 G ->
  GR regsM 10 = w64 (P + 12) -> GR regsM 11 = w64 (f + 16) -> GR regsM 12 = w64 (n - 16) ->
  GR regsM 18 = w64 P ->
  SRr segs W1 (mkCfg (@YK11.mkst fx regsM (Z_to_bv 64 CC_MEMCPY) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros ly1 S1 W1 regsM m1 md1 P H18 Htag J1 Hfr EB Hle HF HK HC HFb HU0 G1 G8 G10 G11 G12 G18.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof (cc_cut_ok CC_RET_CP2 ltac:(cbn; tauto)) as (RV & RE & R4).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1))
    by (rewrite EB; apply in_or_app; right; left; reflexivity).
  assert (Hnot : ~ In (P, Z.max n 1) (ablocks B lyc Sc)).
  { intros H. apply (cc_not_old ly1 S1 W1 m1 md1 (P, Z.max n 1) (ablocks B lyc Sc) HAR1).
    - rewrite EB. apply Permutation_sym, Permutation_cons_append.
    - cbn [snd]. rewrite Hreq. lia.
    - exact H. }
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & HP4 & HPc & HPapp & HPb & _).
  rewrite Hreq in HPc, HPapp, HPb.
  destruct (HblkF ltac:(lia)) as (bF & nF & HbF & Hf1 & Hf2).
  assert (HinF : In (bF, nF) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbF).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bF nF HAR1 HinF) as (_ & HF4 & HFc & HFapp & HFb2 & _).
  pose proof (req_size_pos nF ltac:(lia)) as HrF.
  assert (Hne : (bF, nF) <> (P, Z.max n 1)) by (intros E; rewrite E in HbF; exact (Hnot HbF)).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 HinF HinP Hne) as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD. rewrite Hreq in HD.
  destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
  assert (HinA : In (bA, nA) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbA).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bA nA HAR1 HinA) as (_ & HA4 & HAc & HAapp & HAb & _).
  pose proof (req_size_pos nA ltac:(lia)) as HrA.
  assert (HneA : (bA, nA) <> (P, Z.max n 1)) by (intros E; rewrite E in HbA; exact (Hnot HbA)).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 HinA HinP HneA) as HDA.
  unfold zdisjoint in HDA. cbn [fst snd] in HDA. rewrite Hreq in HDA.
  assert (SPM : spZ regsM = spZ regs + -64).
  { change (spZ regsM) with (bv_unsigned (GR regsM 2)). rewrite K2. unfold w64. rewrite cc_u64 by lia. lia. }
  eapply SRr_bind.
  { apply (aj_intrin_at segs B LAWS cc_segs_low OCpy CC_MEMCPY (AMEMCPY fx) W1 regsM m1 CC.CC_STK (spZ regs)
             cc_FP1 lyc Sc W memc mdc [] ly1 S1 md1 1 (P + 12) (f + 16) (n - 16) (-64)
             (Z_to_bv 64 CC_RET_CP2) J1 G10 G11 G12).
    - lia.
    - lia.
    - lia.
    - exact SPM.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - exact G1.
    - apply YK0s.ret_ok_even. exact RE.
    - intros a Ha. split.
      + right. right. left. exists P, (Z.max n 1).
        split; [exact HinP | split; [exact Hnot | rewrite Hreq; lia]].
      + unfold ESTACK. lia.
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) (P + 12) (n - 16) HAR1 HinP);
        rewrite ?Hreq; lia.
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) (P + 12) (n - 16) HAR1 HinP);
        rewrite ?Hreq; lia.
    - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) (P + 12) (n - 16)
        HAR1 HinP); rewrite ?Hreq; lia.
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - replace a with (f + (a - f)) by lia. rewrite (HFb (a - f) ltac:(lia)). discriminate.
        - rewrite SPM. unfold ESTACK. lia. }
      split; [lia|]. split.
      { apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 bF nF (f + 16) (n - 16) HAR1 HinF); lia. }
      split.
      { apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 bF nF (f + 16) (n - 16) HAR1 HinF); lia. }
      intros _.
      apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 bF nF (f + 16) (n - 16) HAR1 HinF); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & J2 & HRP & HA0 & HCOPY & HVIEW & HAPP).
  (* u now holds the bytes untagged leaves: the moved window, the rest of the copy *)
  assert (HU : cc_u_holds W1 m2 P).
  { intros j Hj. rewrite (cc_ut_byte (Z.to_nat j) ltac:(lia) H18 Htag).
    destruct (Nat.leb 12 (Z.to_nat j) && Nat.ltb (Z.to_nat j) (12 + Z.to_nat (n - 16)))%bool eqn:Eb.
    - apply andb_prop in Eb as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
      replace (P + j) with (P + 12 + (j - 12)) by lia.
      rewrite (HCOPY (j - 12) ltac:(lia)).
      replace (f + 16 + (j - 12)) with (f + (j + 4)) by lia.
      rewrite (HFb (j + 4) ltac:(lia)). f_equal. f_equal. lia.
    - apply andb_false_iff in Eb as [E|E];
        [apply Nat.leb_gt in E | apply Nat.ltb_ge in E];
        (rewrite HVIEW; [exact (HU0 j Hj) | lia | lia | unfold ESTACK; lia]). }
  assert (HC2 : cc_c_holds W1 m2).
  { intros i Hi. rewrite HVIEW; [exact (HC i Hi) | lia | lia | unfold ESTACK; lia]. }
  assert (HF2 : cc_frame m2).
  { apply (cc_frame_kept W1 W1 m1 m2 HF (cc_win _ _ _ _ _ _ J1) (cc_win _ _ _ _ _ _ J2)).
    intros a Ha. apply HVIEW; [lia | lia | unfold ESTACK; lia]. }
  assert (HK2 : cc_kept regs2) by exact (cc_kept_pres _ _ HK HRP).
  pose proof HK2 as (L2 & L3 & L4 & L9 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  (* +0x13c: a2 := n - 4, the length untagged reports *)
  eapply (@cc_run fx W1 regs2 m2 md2 CC_RET_CP2).
  { unfold LCK.ms_of_regs. rewrite L19. apply SEG_CP2RET. lia. }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite (cc_ms_shape _ _ _ _ EQV).
  assert (HUL : cc_ut_len n bs = n - 4)
    by (unfold cc_ut_len; rewrite (proj2 (Z.leb_le 18 n) H18), Htag; reflexivity).
  apply (cc_at_want ly1 S1 W1 (ms_regs ms') m2 md' P).
  - lia.
  - exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 SBM).
  - exact Hfr.
  - exact EB.
  - exact Hle.
  - exact HF2.
  - unfold cc_kept.
    split; [rewrite E2; exact L2|]. split; [rewrite E3; exact L3|]. split; [rewrite E4; exact L4|].
    split; [rewrite E9; exact L9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; exact L20|].
    split; [rewrite E21; exact L21|]. split; [rewrite E22; exact L22|]. split; [rewrite E23; exact L23|].
    split; [rewrite E24; exact L24|]. split; [rewrite E25; exact L25|]. split; [rewrite E26; exact L26|].
    rewrite E27; exact L27.
  - exact HC2.
  - exact HU.
  - rewrite E8. kp_by HRP 8 G8.
  - rewrite E12, HUL. reflexivity.
  - rewrite E18. kp_by HRP 18 G18.
Qed.

(* ---- back from the first copy at +0x6c: n < 18 goes to the free; otherwise the tag test on f ---- *)
Lemma cc_at_cp1ret : forall ly1 S1 W1 regsR m1 md1 P,
  0 < n ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regsR -> cc_c_holds W1 m1 -> cc_f_holds W1 m1 -> cc_u0_holds W1 m1 P ->
  GR regsR 8 = w64 G -> GR regsR 18 = w64 P ->
  SRr segs W1 (@cfg_at fx segs CC_RET_CP1 regsR m1 md1) POST.
Proof.
  intros ly1 S1 W1 regsR m1 md1 P Hpos J1 Hfr EB Hle HF HK HC HFb HU0 G8 G18.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1))
    by (rewrite EB; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & HP4 & HPc & HPapp & HPb & _).
  rewrite Hreq in HPc, HPapp, HPb.
  destruct (Z_lt_le_dec n 18) as [Hlt | H18].
  - (* n < 18: no tag test, got = 0, the compare is skipped and u is freed *)
    assert (HG0 : G = 0)
      by (unfold PRc.copy_untag_result; rewrite (proj2 (Z.ltb_lt n 50) ltac:(lia)); reflexivity).
    eapply (@cc_run fx W1 regsR m1 md1 CC_RET_CP1).
    { unfold LCK.ms_of_regs. rewrite G8, HG0, G18, K19. apply SEG_SHORT; lia. }
    intros ms' md' (ms0 & -> & EQV) SBM.
    destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
      E24 & E25 & E26 & E27).
    rewrite (cc_ms_shape _ _ _ _ EQV).
    apply (cc_at_freecall ly1 S1 W1 (ms_regs ms') m1 md' P).
    + exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
    + exact Hfr.
    + exact EB.
    + exact Hle.
    + exact HF.
    + unfold cc_kept.
      split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
      split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; exact K20|].
      split; [rewrite E21; exact K21|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
      split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
      rewrite E27; exact K27.
    + exact HC.
    + exact E1.
    + exact E10.
    + rewrite E8, HG0. reflexivity.
  - (* n >= 18: the four checked loads of f's bytes 12, 13, 16, 17 *)
    destruct (HblkF ltac:(lia)) as (bF & nF & HbF & Hf1 & Hf2).
    assert (HinF : In (bF, nF) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbF).
    destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bF nF HAR1 HinF) as (_ & HF4 & HFc & HFapp & HFb2 & _).
    pose proof (req_size_pos nF ltac:(lia)) as HrF.
    assert (MRf : forall j, 0 <= j < n ->
              mrd BImg.rsegs m1 (wa (f + j)) = Some (Z_to_bv 8 (PRc.cu_byte bs (Z.to_nat j))))
      by (intros j Hj; apply (cc_mrd_of_aview W1); exact (HFb j Hj)).
    assert (HADDR : AC.addressable m1 f n)
      by (apply (@WCL.wcc_leafb_addressable_block rc B LAWS ly1 S1 W1 m1 md1 bF nF f n HAR1 HinF); lia).
    assert (HRNG : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) f n)
      by (apply (@WCL.wcc_leafb_rng_block rc B LAWS ly1 S1 W1 m1 md1 bF nF f n HAR1 HinF); lia).
    assert (HHULL : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W1) (cc_hull_lo f) (cc_hull_len f n)).
    { apply (cc_rng_hull W1 m1 f n); [lia | lia | lia |].
      apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 bF nF f n HAR1 HinF); lia. }
    destruct (PRc.cu_tagged bs) eqn:Htag.
    + (* tagged: untagged moves [f + 16, f + n) to u + 12 *)
      unfold PRc.cu_tagged in Htag.
      apply andb_prop in Htag as [Htag T17]. apply andb_prop in Htag as [Htag T16].
      apply andb_prop in Htag as [T12 T13].
      apply Z.eqb_eq in T12. apply Z.eqb_eq in T13. apply Z.eqb_eq in T16. apply Z.eqb_eq in T17.
      assert (Htag' : PRc.cu_tagged bs = true)
        by (unfold PRc.cu_tagged; rewrite T12, T13, T16, T17; reflexivity).
      eapply (@cc_run fx W1 regsR m1 md1 CC_RET_CP1).
      { unfold LCK.ms_of_regs. rewrite G18, K19, K20, K21.
        eapply SEG_TAG_YES.
        - lia.
        - lia.
        - lia.
        - exact HADDR.
        - exact HRNG.
        - exact HHULL.
        - pose proof (MRf 12 ltac:(lia)) as M. rewrite M. do 2 f_equal. exact T12.
        - pose proof (MRf 13 ltac:(lia)) as M. rewrite M. do 2 f_equal. exact T13.
        - pose proof (MRf 16 ltac:(lia)) as M. rewrite M. do 2 f_equal. exact T16.
        - pose proof (MRf 17 ltac:(lia)) as M. rewrite M. do 2 f_equal. exact T17. }
      intros ms' md' (ms0 & (a3' & ->) & EQV) SBM.
      destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
        E23 & E24 & E25 & E26 & E27).
      rewrite (cc_ms_shape _ _ _ _ EQV).
      apply (cc_cp2_call ly1 S1 W1 (ms_regs ms') m1 md' P).
      * lia.
      * exact Htag'.
      * exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
      * exact Hfr.
      * exact EB.
      * exact Hle.
      * exact HF.
      * unfold cc_kept.
        split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
        split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; reflexivity|].
        split; [rewrite E21; reflexivity|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
        split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
        rewrite E27; exact K27.
      * exact HC.
      * exact HFb.
      * exact HU0.
      * exact E1.
      * rewrite E8. exact G8.
      * exact E10.
      * exact E11.
      * exact E12.
      * exact E18.
    + (* not tagged: no move, the reported length is n *)
      assert (Hno : ~ (PRc.cu_byte bs 12 = 0x81 /\ PRc.cu_byte bs 13 = 0 /\ PRc.cu_byte bs 16 = 0x88 /\
                       PRc.cu_byte bs 17 = 0x19)).
      { intros (A12 & A13 & A16 & A17). unfold PRc.cu_tagged in Htag.
        rewrite A12, A13, A16, A17 in Htag. cbn in Htag. discriminate. }
      assert (HUL : cc_ut_len n bs = n)
        by (unfold cc_ut_len; rewrite Htag, andb_false_r; reflexivity).
      assert (HUB : cc_ut_bytes n bs = bs)
        by (unfold cc_ut_bytes; rewrite Htag, andb_false_r; reflexivity).
      eapply (@cc_run fx W1 regsR m1 md1 CC_RET_CP1).
      { unfold LCK.ms_of_regs. rewrite G18, K19, K20, K21.
        eapply SEG_TAG_NO.
        - lia.
        - lia.
        - lia.
        - exact HADDR.
        - exact HRNG.
        - exact HHULL.
        - apply cc_byte_rng.
        - apply cc_byte_rng.
        - apply cc_byte_rng.
        - apply cc_byte_rng.
        - pose proof (MRf 12 ltac:(lia)) as M. exact M.
        - pose proof (MRf 13 ltac:(lia)) as M. exact M.
        - pose proof (MRf 16 ltac:(lia)) as M. exact M.
        - pose proof (MRf 17 ltac:(lia)) as M. exact M.
        - exact Hno. }
      intros ms' md' (ms0 & (a0' & a1' & a3' & ->) & EQV) SBM.
      destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
        E23 & E24 & E25 & E26 & E27).
      rewrite (cc_ms_shape _ _ _ _ EQV).
      apply (cc_at_want ly1 S1 W1 (ms_regs ms') m1 md' P).
      * lia.
      * exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
      * exact Hfr.
      * exact EB.
      * exact Hle.
      * exact HF.
      * unfold cc_kept.
        split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
        split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; reflexivity|].
        split; [rewrite E21; reflexivity|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
        split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
        rewrite E27; exact K27.
      * exact HC.
      * intros i Hi. rewrite HUB. exact (HU0 i Hi).
      * rewrite E8. exact G8.
      * rewrite E12, HUL. reflexivity.
      * exact E18.
Qed.

(* ---- __asan_memcpy (u, f, n) at +0x68 (fuzz_dup's copy), then the tag test ---- *)
Lemma cc_cp1_call : forall ly1 S1 W1 regsM m1 md1 P,
  0 < n ->
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regsM -> cc_c_holds W1 m1 -> cc_f_holds W1 m1 ->
  GR regsM 1 = Z_to_bv 64 CC_RET_CP1 -> GR regsM 8 = w64 G ->
  GR regsM 10 = w64 P -> GR regsM 11 = w64 f -> GR regsM 12 = w64 n -> GR regsM 18 = w64 P ->
  SRr segs W1 (mkCfg (@YK11.mkst fx regsM (Z_to_bv 64 CC_MEMCPY) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros ly1 S1 W1 regsM m1 md1 P Hpos J1 Hfr EB Hle HF HK HC HFb G1 G8 G10 G11 G12 G18.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof (cc_cut_ok CC_RET_CP1 ltac:(cbn; tauto)) as (RV & RE & R4).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1))
    by (rewrite EB; apply in_or_app; right; left; reflexivity).
  assert (Hnot : ~ In (P, Z.max n 1) (ablocks B lyc Sc)).
  { intros H. apply (cc_not_old ly1 S1 W1 m1 md1 (P, Z.max n 1) (ablocks B lyc Sc) HAR1).
    - rewrite EB. apply Permutation_sym, Permutation_cons_append.
    - cbn [snd]. rewrite Hreq. lia.
    - exact H. }
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & HP4 & HPc & HPapp & HPb & _).
  rewrite Hreq in HPc, HPapp, HPb.
  destruct (HblkF ltac:(lia)) as (bF & nF & HbF & Hf1 & Hf2).
  assert (HinF : In (bF, nF) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbF).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bF nF HAR1 HinF) as (_ & HF4 & HFc & HFapp & HFb2 & _).
  pose proof (req_size_pos nF ltac:(lia)) as HrF.
  assert (HneF : (bF, nF) <> (P, Z.max n 1)) by (intros E; rewrite E in HbF; exact (Hnot HbF)).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 HinF HinP HneF) as HDF.
  unfold zdisjoint in HDF. cbn [fst snd] in HDF. rewrite Hreq in HDF.
  destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
  assert (HinA : In (bA, nA) (ablocks B ly1 S1)) by (rewrite EB; apply in_or_app; left; exact HbA).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 bA nA HAR1 HinA) as (_ & HA4 & HAc & HAapp & HAb & _).
  pose proof (req_size_pos nA ltac:(lia)) as HrA.
  assert (HneA : (bA, nA) <> (P, Z.max n 1)) by (intros E; rewrite E in HbA; exact (Hnot HbA)).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 HinA HinP HneA) as HDA.
  unfold zdisjoint in HDA. cbn [fst snd] in HDA. rewrite Hreq in HDA.
  assert (SPM : spZ regsM = spZ regs + -64).
  { change (spZ regsM) with (bv_unsigned (GR regsM 2)). rewrite K2. unfold w64. rewrite cc_u64 by lia. lia. }
  eapply SRr_bind.
  { apply (aj_intrin_at segs B LAWS cc_segs_low OCpy CC_MEMCPY (AMEMCPY fx) W1 regsM m1 CC.CC_STK (spZ regs)
             cc_FP1 lyc Sc W memc mdc [] ly1 S1 md1 1 P f n (-64) (Z_to_bv 64 CC_RET_CP1) J1 G10 G11 G12).
    - lia.
    - lia.
    - lia.
    - exact SPM.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - exact G1.
    - apply YK0s.ret_ok_even. exact RE.
    - intros a Ha. split.
      + right. right. left. exists P, (Z.max n 1).
        split; [exact HinP | split; [exact Hnot | rewrite Hreq; lia]].
      + unfold ESTACK. lia.
    - apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP); rewrite ?Hreq; lia.
    - apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
        rewrite ?Hreq; lia.
    - intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) P n HAR1 HinP);
        rewrite ?Hreq; lia.
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - replace a with (f + (a - f)) by lia. rewrite (HFb (a - f) ltac:(lia)). discriminate.
        - rewrite SPM. unfold ESTACK. lia. }
      split; [lia|]. split.
      { apply (amem_range_of_block segs B LAWS ly1 S1 W1 m1 md1 bF nF f n HAR1 HinF); lia. }
      split.
      { apply (range_addressable_of_block segs B LAWS ly1 S1 W1 m1 md1 bF nF f n HAR1 HinF); lia. }
      intros _. apply (shadow_hull_vis_of_block segs B LAWS ly1 S1 W1 m1 md1 bF nF f n HAR1 HinF); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & J2 & HRP & HA0 & HCOPY & HVIEW & HAPP).
  assert (HU0 : cc_u0_holds W1 m2 P)
    by (intros j Hj; rewrite (HCOPY j Hj); exact (HFb j Hj)).
  assert (HC2 : cc_c_holds W1 m2)
    by (intros i Hi; rewrite HVIEW; [exact (HC i Hi) | lia | lia | unfold ESTACK; lia]).
  assert (HF2b : cc_f_holds W1 m2)
    by (intros i Hi; rewrite HVIEW; [exact (HFb i Hi) | lia | lia | unfold ESTACK; lia]).
  assert (HF2 : cc_frame m2).
  { apply (cc_frame_kept W1 W1 m1 m2 HF (cc_win _ _ _ _ _ _ J1) (cc_win _ _ _ _ _ _ J2)).
    intros a Ha. apply HVIEW; [lia | lia | unfold ESTACK; lia]. }
  change (mkCfg (YK11.mkst regs2 (Z_to_bv 64 CC_RET_CP1) m2 (YK11.seg_rom segs)) md2)
    with (@cfg_at fx segs CC_RET_CP1 regs2 m2 md2).
  apply (cc_at_cp1ret ly1 S1 W1 regs2 m2 md2 P).
  - exact Hpos.
  - exact J2.
  - exact Hfr.
  - exact EB.
  - exact Hle.
  - exact HF2.
  - exact (cc_kept_pres _ _ HK HRP).
  - exact HC2.
  - exact HF2b.
  - exact HU0.
  - kp_by HRP 8 G8.
  - kp_by HRP 18 G18.
Qed.

(* ---- back from the malloc at +0x50 with a0 = u: n = 0 skips the copies, otherwise the first copy ---- *)
Lemma cc_at_retmalloc : forall ly1 S1 W1 regs1 m1 md1 P,
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, Z.max n 1)] -> 4096 <= P ->
  mo_le MT Sc S1 (mo_malloc MT (Z.max n 1)) ->
  cc_frame m1 -> cc_kept regs1 -> cc_c_holds W1 m1 -> cc_f_holds W1 m1 ->
  GR regs1 8 = w64 G -> GR regs1 10 = w64 P ->
  SRr segs W1 (@cfg_at fx segs CC_RET_MALLOC regs1 m1 md1) POST.
Proof.
  intros ly1 S1 W1 regs1 m1 md1 P J1 Hfr EB HP4 Hle HF HK HC HFb G8 G10.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  assert (HinP : In (P, Z.max n 1) (ablocks B ly1 S1))
    by (rewrite EB; apply in_or_app; right; left; reflexivity).
  assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 P (Z.max n 1) HAR1 HinP) as (_ & _ & HPc & _).
  rewrite Hreq in HPc.
  destruct (Z.eq_dec n 0) as [Hz | Hpos].
  - (* n = 0: no copy, got = 0, u is freed at once *)
    assert (HG0 : G = 0)
      by (unfold PRc.copy_untag_result; rewrite (proj2 (Z.ltb_lt n 50) ltac:(lia)); reflexivity).
    assert (G8z : GR regs1 8 = Z_to_bv 64 0) by (rewrite G8, HG0; reflexivity).
    assert (K19z : GR regs1 19 = Z_to_bv 64 0) by (rewrite K19, Hz; reflexivity).
    eapply (@cc_run fx W1 regs1 m1 md1 CC_RET_MALLOC).
    { unfold LCK.ms_of_regs. rewrite G8z, G10, K19z. apply SEG_Z. lia. }
    intros ms' md' (ms0 & -> & EQV) SBM.
    destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
      E24 & E25 & E26 & E27).
    rewrite (cc_ms_shape _ _ _ _ EQV).
    apply (cc_at_freecall ly1 S1 W1 (ms_regs ms') m1 md' P).
    + exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
    + exact Hfr.
    + exact EB.
    + exact Hle.
    + exact HF.
    + unfold cc_kept.
      split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
      split; [rewrite E9; exact K9|]. split; [rewrite E19, Hz; reflexivity|].
      split; [rewrite E20; exact K20|]. split; [rewrite E21; exact K21|]. split; [rewrite E22; exact K22|].
      split; [rewrite E23; exact K23|]. split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|].
      split; [rewrite E26; exact K26|]. rewrite E27; exact K27.
    + exact HC.
    + exact E1.
    + exact E10.
    + rewrite E8, HG0. reflexivity.
  - (* n > 0: the copy of the n frame bytes into u *)
    assert (Hn0 : 0 < n) by lia.
    eapply (@cc_run fx W1 regs1 m1 md1 CC_RET_MALLOC).
    { unfold LCK.ms_of_regs. rewrite G10, K19. apply SEG_CP1; lia. }
    intros ms' md' (ms0 & -> & EQV) SBM.
    destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 &
      E23 & E24 & E25 & E26 & E27).
    rewrite (cc_ms_shape _ _ _ _ EQV).
    apply (cc_cp1_call ly1 S1 W1 (ms_regs ms') m1 md' P).
    + exact Hn0.
    + exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
    + exact Hfr.
    + exact EB.
    + exact Hle.
    + exact HF.
    + unfold cc_kept.
      split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
      split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; exact K20|].
      split; [rewrite E21; exact K21|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
      split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
      rewrite E27; exact K27.
    + exact HC.
    + exact HFb.
    + exact E1.
    + rewrite E8. exact G8.
    + exact E10.
    + rewrite E11. exact K20.
    + exact E12.
    + exact E18.
Qed.

(* ---- malloc (max n 1) at +0x4c (YC5d.v amalloc04_rule): it never returns NULL ---- *)
Lemma cc_malloc_call : forall regsM m1 md1,
  JI lyc Sc W m1 md1 0 ->
  cc_frame m1 -> cc_kept regsM -> cc_c_holds W m1 -> cc_f_holds W m1 ->
  GR regsM 1 = Z_to_bv 64 CC_RET_MALLOC -> GR regsM 8 = w64 G -> GR regsM 10 = w64 (Z.max n 1) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsM (Z_to_bv 64 CC_MALLOC) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros regsM m1 md1 J1 HF HK HC HFb G1 G8 G10.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  assert (ELIVE : CC.CC_LIVE = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & _).
  pose proof (cc_cut_ok CC_RET_MALLOC ltac:(cbn; tauto)) as (RV & RE & R4).
  assert (HGl : 0 <= G <= n) by (apply cc_got_lo; lia).
  assert (SPM : spZ regsM = spZ regs + -64).
  { change (spZ regsM) with (bv_unsigned (GR regsM 2)). rewrite K2. unfold w64. rewrite cc_u64 by lia. lia. }
  assert (CHAIN : chain_pre lyc (aview segs (w_H W) m1) regsM []).
  { apply cc_chain_nil.
    - change (raZ regsM) with (bv_unsigned (GR regsM 1)). rewrite G1. exact R4.
    - change (s0Z regsM) with (bv_unsigned (GR regsM 8)). rewrite G8. unfold w64.
      rewrite cc_u64 by lia. rewrite SPM. lia. }
  assert (TRACE : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsM []) (as_universe B)).
  { rewrite cc_trace0. cbn [spine map].
    replace (raZ regsM) with CC.WIRE_CC_RA_MALLOC; [exact (proj1 UFIX)|].
    change (raZ regsM) with (bv_unsigned (GR regsM 1)). rewrite G1, RV. symmetry. exact cc_ra_malloc_eq. }
  pose proof cc_cost as (Mc1 & Mc2 & Msum).
  assert (MOK : mo_ok MT Sc (mo_malloc MT (Z.max n 1))) by (apply (mo_ok_le MT MTL Sc _ T Hmo); lia).
  assert (EM : CC_MALLOC = pc_wrap_malloc (as_code B)) by (rewrite HMPC; reflexivity).
  rewrite EM.
  eapply SRr_bind.
  - exact (AMALLOC fx W regsM m1 CC.CC_STK (spZ regs) cc_FP1 lyc Sc W memc mdc [] lyc Sc md1 0
             (Z.max n 1) (-64) (Z_to_bv 64 CC_RET_MALLOC) [] J1 G10
             ltac:(unfold MALLOC_MAX; lia) ltac:(lia) SPM eq_refl ltac:(lia)
             ltac:(unfold ASTACK; lia) (eq_trans K3 Hgp) (eq_trans K4 Htp) G1 (YK0s.ret_ok_even _ RE)
             (cc_nevJ _ _ _ _ _ _ J1 ltac:(lia)) CHAIN TRACE MOK Hdepot).
  - intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & P & -> & J2 & HRP & HA0 & HFR & HP4 & EB & HKEPT & HML).
    pose proof (cc_AR _ _ _ _ _ _ J2) as HAR2.
    assert (Hreq : req_size (Z.max n 1) = Z.max n 1)
      by (unfold req_size; destruct (Z.eqb_spec (Z.max n 1) 0); lia).
    assert (HinP : In (P, Z.max n 1) (ablocks B ly2 S2))
      by (rewrite EB; apply in_or_app; right; left; reflexivity).
    assert (Hnot : ~ In (P, Z.max n 1) (ablocks B lyc Sc)).
    { intros H. apply (cc_not_old ly2 S2 W2 m2 md2 (P, Z.max n 1) (ablocks B lyc Sc) HAR2).
      - rewrite EB. apply Permutation_sym, Permutation_cons_append.
      - cbn [snd]. rewrite Hreq. lia.
      - exact H. }
    apply (cc_at_retmalloc ly2 S2 W2 regs2 m2 md2 P).
    + exact J2.
    + rewrite HFR. reflexivity.
    + exact EB.
    + exact HP4.
    + exact HML.
    + apply (cc_frame_kept W W2 m1 m2 HF (cc_win _ _ _ _ _ _ J1) (cc_win _ _ _ _ _ _ J2)).
      intros a Ha. apply (proj1 HKEPT); [unfold ASTACK; lia | lia].
    + exact (cc_kept_pres _ _ HK HRP).
    + (* c's bytes: its block is the caller's, and the new block is disjoint from it *)
      intros i Hi.
      destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
      assert (HinA : In (bA, nA) (ablocks B ly2 S2)) by (rewrite EB; apply in_or_app; left; exact HbA).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 m2 md2 bA nA HAR2 HinA) as (_ & _ & HAc & _).
      pose proof (req_size_pos nA ltac:(lia)) as HrA.
      assert (HneA : (bA, nA) <> (P, Z.max n 1)) by (intros E; rewrite E in HbA; exact (Hnot HbA)).
      pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR2 HinA HinP HneA) as HDA.
      unfold zdisjoint in HDA. cbn [fst snd] in HDA. rewrite Hreq in HDA.
      rewrite (cc_kept_block lyc Sc W m1 W2 m2 _ _ _ bA nA (c + i) HKEPT HbA ltac:(lia) ltac:(lia)).
      exact (HC i Hi).
    + (* f's bytes, the same way *)
      intros i Hi.
      destruct (HblkF ltac:(lia)) as (bF & nF & HbF & Hf1 & Hf2).
      assert (HinF : In (bF, nF) (ablocks B ly2 S2)) by (rewrite EB; apply in_or_app; left; exact HbF).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 m2 md2 bF nF HAR2 HinF) as (_ & _ & HFc & _).
      pose proof (req_size_pos nF ltac:(lia)) as HrF.
      assert (HneF : (bF, nF) <> (P, Z.max n 1)) by (intros E; rewrite E in HbF; exact (Hnot HbF)).
      pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR2 HinF HinP HneF) as HDF.
      unfold zdisjoint in HDF. cbn [fst snd] in HDF. rewrite Hreq in HDF.
      rewrite (cc_kept_block lyc Sc W m1 W2 m2 _ _ _ bF nF (f + i) HKEPT HbF ltac:(lia) ltac:(lia)).
      exact (HFb i Hi).
    + kp_by HRP 8 G8.
    + exact HA0.
Qed.

(* ---- back from rp_copy_untag at +0x40: s0 := got, a0 := max n 1, then the malloc ---- *)
Lemma cc_at_retrcu : forall regsR m1 md1,
  JI lyc Sc W m1 md1 0 ->
  cc_frame m1 -> cc_kept regsR -> cc_c_holds W m1 -> cc_f_holds W m1 ->
  GR regsR 10 = w64 G ->
  SRr segs W (@cfg_at fx segs CC_RET_RCU regsR m1 md1) POST.
Proof.
  intros regsR m1 md1 J1 HF HK HC HFb G10.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  eapply (@cc_run fx W regsR m1 md1 CC_RET_RCU).
  { unfold LCK.ms_of_regs. rewrite K19. apply SEG_M. lia. }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
    E24 & E25 & E26 & E27).
  rewrite (cc_ms_shape _ _ _ _ EQV).
  apply (cc_malloc_call (ms_regs ms') m1 md').
  - exact (cc_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM).
  - exact HF.
  - unfold cc_kept.
    split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
    split; [rewrite E9; exact K9|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; exact K20|].
    split; [rewrite E21; exact K21|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
    split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
    rewrite E27; exact K27.
  - exact HC.
  - exact HFb.
  - exact E1.
  - rewrite E8. exact G10.
  - exact E10.
Qed.

(* ---- rp_copy_untag (c, n) at +0x3c: its frozen contract, carried through the inner journal ---- *)
Lemma cc_rcu_call : forall regsT m1 md1,
  JI lyc Sc W m1 md1 0 ->
  cc_frame m1 -> cc_kept regsT ->
  (forall i, 0 <= i < n -> aview segs (w_H W) m1 (c + i) = Some (PRc.cu_byte bs (Z.to_nat i))) ->
  cc_f_holds W m1 ->
  GR regsT 1 = Z_to_bv 64 CC_RET_RCU -> GR regsT 10 = w64 c -> GR regsT 11 = w64 n ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 CC_RCU) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros regsT m1 md1 J1 HF HK HC0 HFb G1 G10 G11.
  pose proof (cc_AR _ _ _ _ _ _ J1) as HAR1.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  assert (ERS : PRU.RCU_STK = 4144) by reflexivity.
  pose proof HK as (K2 & K3 & K4 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof (cc_cut_ok CC_RET_RCU ltac:(cbn; tauto)) as (RV & RE & R4).
  pose proof cc_stklo as HSLO.
  assert (SPT : spZ regsT = spZ regs + -64).
  { change (spZ regsT) with (bv_unsigned (GR regsT 2)). rewrite K2. unfold w64. rewrite cc_u64 by lia. lia. }
  assert (HRET : YK0s.ret_ok (GR regsT 1)) by (rewrite G1; exact (YK0s.ret_ok_even _ RE)).
  assert (HPRE : ecall_pre segs B lyc Sc W regsT m1 md1).
  { apply (ecall_pre_at segs B CC.CC_STK (spZ regs) cc_FP1 lyc Sc W memc mdc [] lyc Sc W m1 md1 0 regsT (-64) J1
             SPT eq_refl ltac:(lia) ltac:(unfold ESTACK; lia)
             HRET (eq_trans K3 Hgp) (eq_trans K4 Htp)). }
  pose proof J1 as (_ & Hly1 & _ & _ & _ & Hfrs1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT1).
  pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
  eapply SRr_bind.
  { apply (ARCU fx lyc Sc W regsT m1 md1 c n bs HPRE).
    - rewrite SPT. lia.
    - intros x Hx. apply (cc_win _ _ _ _ _ _ J1). lia.
    - exact G10.
    - exact G11.
    - unfold PRU.RCU_LEN_MAX. lia.
    - exact Hlen.
    - intros H50.
      destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
      destruct (al_blocks _ _ LAWS lyc Sc W m1 md1 bA nA HAR1 HbA) as (_ & HA4 & HAc & HAapp & HAb & _).
      pose proof (req_size_pos nA ltac:(lia)) as HrA.
      split; [lia|]. split; [lia|]. split.
      { apply cc_garr8_of_aview. intros j Hj. rewrite length_map in Hj.
        rewrite cc_nth_map. split; [|apply cc_byte_rng].
        rewrite (HC0 (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
      split.
      { intros x Hx. split.
        - replace x with (c + (x - c)) by lia. rewrite (HC0 (x - c) ltac:(lia)). discriminate.
        - split; [|split].
          + apply apresent_writable. exact (proj1 (HAb x ltac:(lia))).
          + exact (proj2 (HAb x ltac:(lia))).
          + lia. }
      split; [apply (amem_range_of_block segs B LAWS lyc Sc W m1 md1 bA nA c n HAR1 HbA); lia|].
      split; [apply (range_addressable_of_block segs B LAWS lyc Sc W m1 md1 bA nA c n HAR1 HbA); lia|].
      apply (shadow_hull_vis_of_block segs B LAWS lyc Sc W m1 md1 bA nA c n HAR1 HbA); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & HAR2 & HRP & HSBM & HA0 & HCU & HVIEW & HAPP).
  (* the inner journal follows the call's writes: its stack window and the bytes of c it moves *)
  assert (J2 : JI lyc Sc W m2 md2 0).
  { apply (ajournal_after_write segs B LAWS cc_segs_low CC.CC_STK (spZ regs) cc_FP1 lyc Sc W memc mdc [] lyc Sc W
             m1 md1 0 m2 md2
             (fun a => (PRc.cu_moves n bs = true /\ c + 12 <= a < c + n - 4) \/
                       (spZ regsT - PRU.RCU_STK <= a < spZ regsT)) Sc [] J1).
    - intros a Ha HnW. apply HVIEW; [exact Ha | intros Hm; apply HnW; left; exact Hm
                                    | intros Hs; apply HnW; right; exact Hs].
    - exact HAPP.
    - exact HSBM.
    - intros a [[Hmv Hr] | Hs].
      + assert (H50 : 50 <= n)
          by (unfold PRc.cu_moves in Hmv; apply andb_prop in Hmv as [Hmv _]; apply Z.leb_le in Hmv; lia).
        destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
        destruct (al_blocks _ _ LAWS lyc Sc W m1 md1 bA nA HAR1 HbA) as (_ & _ & HAc & _).
        pose proof (req_size_pos nA ltac:(lia)) as HrA.
        left. right. left. split; [apply cc_FP1_cover; lia|]. exists bA, nA. split; [exact HbA | lia].
      + left. left. rewrite SPT in Hs. lia.
    - exact HAR2.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact Hfrs1.
    - exact HQT1. }
  assert (HC2 : cc_c_holds W m2).
  { intros i Hi. destruct (Z_lt_le_dec n 50) as [Hlt | H50].
    - assert (Hmv : PRc.cu_moves n bs = false)
        by (unfold PRc.cu_moves; rewrite (proj2 (Z.leb_gt 50 n) ltac:(lia)); reflexivity).
      assert (Hcb : PRc.cu_bytes n bs = bs) by (unfold PRc.cu_bytes; rewrite Hmv; reflexivity).
      destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
      destruct (al_blocks _ _ LAWS lyc Sc W m1 md1 bA nA HAR1 HbA) as (_ & HA4 & HAc & _).
      pose proof (req_size_pos nA ltac:(lia)) as HrA.
      rewrite Hcb. rewrite HVIEW; [exact (HC0 i Hi) | lia | intros (Hm & _); rewrite Hmv in Hm; discriminate
                                  | rewrite SPT; lia].
    - exact (HCU H50 i Hi). }
  assert (HF2b : cc_f_holds W m2).
  { intros i Hi.
    destruct (HblkF ltac:(lia)) as (bF & nF & HbF & Hf1 & Hf2).
    destruct (al_blocks _ _ LAWS lyc Sc W m1 md1 bF nF HAR1 HbF) as (_ & HF4 & HFc & _).
    pose proof (req_size_pos nF ltac:(lia)) as HrF.
    rewrite HVIEW; [exact (HFb i Hi) | lia | | rewrite SPT; lia].
    intros (_ & Hr). destruct (Hdj ltac:(lia)); lia. }
  assert (HF2 : cc_frame m2).
  { apply (cc_frame_kept W W m1 m2 HF (cc_win _ _ _ _ _ _ J1) (cc_win _ _ _ _ _ _ J2)).
    intros a Ha. apply HVIEW; [lia | | rewrite SPT; lia].
    intros (_ & Hr).
    destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
    destruct (al_blocks _ _ LAWS lyc Sc W m1 md1 bA nA HAR1 HbA) as (_ & _ & HAc & _).
    pose proof (req_size_pos nA ltac:(lia)) as HrA. lia. }
  replace (raZ regsT) with CC_RET_RCU.
  2:{ change (raZ regsT) with (bv_unsigned (GR regsT 1)). rewrite G1. symmetry. exact RV. }
  apply (cc_at_retrcu regs2 m2 md2).
  - exact J2.
  - exact HF2.
  - exact (cc_kept_pres _ _ HK HRP).
  - exact HC2.
  - exact HF2b.
  - exact HA0.
Qed.

(* ---- the entry: the inner journal, the prologue (cc_seg_entry_F), then rp_copy_untag ---- *)
Lemma cc_entry : SRr segs W (@cfg_at fx segs CC_ENTRY regs memc mdc) POST.
Proof.
  pose proof cc_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof (@YM05.alloc_ceiling_lt rc) as CEILLT.
  assert (EST : CC.CC_STK = 16448) by reflexivity.
  assert (ERM : CC.CC_RECV_MAX = 1600) by reflexivity.
  pose proof cc_JI0 as JI0.
  pose proof (cc_win _ _ _ _ _ _ JI0) as Hpres0.
  destruct (WCL.wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc cc_HARc) as (CK & GCK & _).
  destruct (WCL.wcc_leafb_rng_cells W) as [RGC RCK].
  assert (E10 : GR regs 10 = Z_to_bv 64 c) by exact H10.
  assert (E11 : GR regs 11 = Z_to_bv 64 f) by exact H11.
  assert (E12 : GR regs 12 = Z_to_bv 64 n) by exact H12.
  eapply (@cc_run fx W regs memc mdc CC_ENTRY).
  { unfold LCK.ms_of_regs. rewrite E10, E11, E12.
    eapply SEG_ENTRY with (lo := spZ regs - CC.CC_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (cc_stk_present (w_H W)); [lia | lia | exact Hpres0].
    - lia.
    - exact GCK.
    - exact CK.
    - unfold AC.CELL_K. lia.
    - apply cc_rng; [lia | lia |]. intros b Hb. exact (proj1 (Hpres0 b ltac:(lia))).
    - exact RGC.
    - exact RCK. }
  intros ms' md' (ms0 & (m1 & v0 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR.
  destruct (cc_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & E11' & E12' & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite (cc_ms_shape _ _ _ _ EQV).
  (* the inner journal follows the frame write *)
  assert (HJ1 : JI lyc Sc W m1 md' 0).
  { apply (ajournal_exec segs B LAWS cc_segs_low CC.CC_STK (spZ regs) cc_FP1 lyc Sc W memc mdc [] lyc Sc W memc mdc
             0 m1 md' (fun a => spZ regs - 64 <= a < spZ regs) JI0).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 64)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hxr : spZ regs - CC.CC_STK <= bv_unsigned x < spZ regs) by lia.
      destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
      assert (Hw : wview BImg.rsegs m1 x <> None).
      { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
      unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (LeafCgGlue.find_segment_out BImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
      intros sg Hin Hr. pose proof (cc_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
      unfold kLowMemEnd in Hlow. lia.
    - intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 64)) as [Hl|Hl];
        [apply (MU x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|apply (MU x); cbn [outside]; split; [lia | exact I]].
      exfalso.
      assert (Hxr : spZ regs - CC.CC_STK <= bv_unsigned x < spZ regs) by lia.
      pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. left. lia. }
  assert (HF1 : cc_frame m1) by (exists v0; exact FR).
  assert (HK1 : cc_kept (ms_regs ms')).
  { unfold cc_kept.
    split; [rewrite E2; reflexivity|]. split; [rewrite E3; reflexivity|]. split; [rewrite E4; reflexivity|].
    split; [rewrite E9; reflexivity|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; reflexivity|].
    split; [rewrite E21; reflexivity|]. split; [rewrite E22; reflexivity|]. split; [rewrite E23; reflexivity|].
    split; [rewrite E24; reflexivity|]. split; [rewrite E25; reflexivity|]. split; [rewrite E26; reflexivity|].
    rewrite E27; reflexivity. }
  (* the frames c and f keep their entry bytes: the prologue wrote only the call's own frame *)
  assert (HC1 : forall i, 0 <= i < n -> aview segs (w_H W) m1 (c + i) = Some (PRc.cu_byte bs (Z.to_nat i))).
  { intros i Hi.
    destruct (HblkC ltac:(lia)) as (bA & nA & HbA & Hb1 & Hb2).
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA cc_HARc HbA) as (_ & HA4 & HAc & _).
    destruct (req_size_pos nA ltac:(lia)) as [HrA1 HrA2].
    assert (Hout : mrestrict (w_H W) m1 (Z_to_bv 64 (c + i)) = mrestrict (w_H W) memc (Z_to_bv 64 (c + i))).
    { unfold mrestrict. rewrite (MU (Z_to_bv 64 (c + i))); [reflexivity|].
      assert (Hb64 : 0 <= c + i < 2 ^ 64) by lia.
      assert (Hnf : ~ (spZ regs - 64 <= c + i < spZ regs)) by lia.
      exact (cc_outside (c + i) (spZ regs - 64) (spZ regs) Hb64 Hnf). }
    rewrite (aview_eq_of segs (w_H W) memc m1 (c + i) Hout).
    replace (c + i) with (c + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (cc_garr8_aview (w_H W) memc c _ (Z.to_nat i) HgC ltac:(rewrite length_map; lia)).
    rewrite cc_nth_map. reflexivity. }
  assert (HF1b : cc_f_holds W m1).
  { intros i Hi.
    destruct (HblkF ltac:(lia)) as (bF & nF & HbF & Hf1 & Hf2).
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bF nF cc_HARc HbF) as (_ & HF4 & HFc & _).
    destruct (req_size_pos nF ltac:(lia)) as [HrF1 HrF2].
    assert (Hout : mrestrict (w_H W) m1 (Z_to_bv 64 (f + i)) = mrestrict (w_H W) memc (Z_to_bv 64 (f + i))).
    { unfold mrestrict. rewrite (MU (Z_to_bv 64 (f + i))); [reflexivity|].
      assert (Hb64 : 0 <= f + i < 2 ^ 64) by lia.
      assert (Hnf : ~ (spZ regs - 64 <= f + i < spZ regs)) by lia.
      exact (cc_outside (f + i) (spZ regs - 64) (spZ regs) Hb64 Hnf). }
    rewrite (aview_eq_of segs (w_H W) memc m1 (f + i) Hout).
    replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (cc_garr8_aview (w_H W) memc f _ (Z.to_nat i) HgF ltac:(rewrite length_map; lia)).
    rewrite cc_nth_map. reflexivity. }
  apply (cc_rcu_call (ms_regs ms') m1 md').
  - exact HJ1.
  - exact HF1.
  - exact HK1.
  - exact HC1.
  - exact HF1b.
  - exact E1.
  - exact E10'.
  - exact E11'.
Qed.

End Entry.

(* The contract at WS_check_copy: every premise of the walk is a premise of the frozen statement. *)
Theorem cc_walk : @CC.wire_check_copy_cg fx rc B MT (wire_sigma WS_check_copy).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c f n T bs.
  intros HJ Hra Hra4 Hgp' Htp' H10 H11 H12 Hal Hwlo Hwhi Hn Hlen HblkC HblkF Hdj HFPc HgC HgF Hdepot Hnev
    Hlive Hmo Hcost.
  change (wire_sigma WS_check_copy) with CC_ENTRY.
  eapply cc_entry; eassumption.
Qed.

End Walk.
