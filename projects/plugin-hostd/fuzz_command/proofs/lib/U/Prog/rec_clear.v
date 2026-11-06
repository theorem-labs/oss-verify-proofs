(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 779 of its 856 lines of code are new or changed and 471 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma rc_sx32 : forall v, (0 <= v < 2 ^ 31)%Z -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v H. unfold sx32. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rc_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo n : Z) (an nr rp rs : word),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (0x343e0 <= lo)%Z ->
  rw_cells rsegs m 0x34030 [C4 (Z_to_bv 64 n)] -> (0 <= n <= 16)%Z ->
  rw_cells rsegs m 0x343b8 [C8 an] -> rw_cells rsegs m 0x343c0 [C4 nr] ->
  rw_cells rsegs m 0x343c8 [C8 rp] -> rw_cells rsegs m 0x343d0 [C8 rs] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15ad4) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0) s1
                     (Z_to_bv 64 0x34038) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b08) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 16)%Z [C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x34030 [C4 (Z_to_bv 64 n)] /\ rw_cells rsegs m' 0x343b8 [C8 an]
       /\ rw_cells rsegs m' 0x343c0 [C4 nr] /\ rw_cells rsegs m' 0x343c8 [C8 rp] /\ rw_cells rsegs m' 0x343d0 [C8 rs])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ab4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n an nr rp rs ST LO LO2 NC Hn N2 N3 N4 N5.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  apply evt_done.
  eexists. split.
  { try (rewrite rc_sx32 by lia). reflexivity. }
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma rc_run2 :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 nc an nr rp rs : word),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x34030 [C4 nc] -> rw_cells rsegs m 0x343b8 [C8 an] -> rw_cells rsegs m 0x343c0 [C4 nr] ->
  rw_cells rsegs m 0x343c8 [C8 rp] -> rw_cells rsegs m 0x343d0 [C8 rs] ->
  (0x343e0 + 16 <= bv_unsigned sp0)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15ae0) (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0) s1
                     an a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18ad0) fc None m' (seg_rom rsegs)
       /\ munch [(0x34030, 0x34034)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp0 - 16) [C8 s00; C8 ra0]
       /\ rw_cells rsegs m' 0x34030 [C4 (Z_to_bv 64 0)] /\ rw_cells rsegs m' 0x343b8 [C8 an]
       /\ rw_cells rsegs m' 0x343c0 [C4 nr] /\ rw_cells rsegs m' 0x343c8 [C8 rp] /\ rw_cells rsegs m' 0x343d0 [C8 rs])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ad4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 nc an nr rp rs FR N1 N2 N3 N4 N5 SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x34030, 0x34034)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma rc_run3 :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 nc an nr rp rs : word),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x34030 [C4 nc] -> rw_cells rsegs m 0x343b8 [C8 an] -> rw_cells rsegs m 0x343c0 [C4 nr] ->
  rw_cells rsegs m 0x343c8 [C8 rp] -> rw_cells rsegs m 0x343d0 [C8 rs] ->
  (0x343e0 + 16 <= bv_unsigned sp0)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15aec) (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0) s1
                     rp a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18ad0) fc None m' (seg_rom rsegs)
       /\ munch [(0x343b8, 0x343c0)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp0 - 16) [C8 s00; C8 ra0]
       /\ rw_cells rsegs m' 0x34030 [C4 nc] /\ rw_cells rsegs m' 0x343b8 [C8 (Z_to_bv 64 0)]
       /\ rw_cells rsegs m' 0x343c0 [C4 nr] /\ rw_cells rsegs m' 0x343c8 [C8 rp] /\ rw_cells rsegs m' 0x343d0 [C8 rs])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ae0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 nc an nr rp rs FR N1 N2 N3 N4 N5 SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x343b8, 0x343c0)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma rc_run4 :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 nc an nr rp rs : word),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x34030 [C4 nc] -> rw_cells rsegs m 0x343b8 [C8 an] -> rw_cells rsegs m 0x343c0 [C4 nr] ->
  rw_cells rsegs m 0x343c8 [C8 rp] -> rw_cells rsegs m 0x343d0 [C8 rs] ->
  (0x343e0 + 16 <= bv_unsigned sp0)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(0x343c0, 0x343c4); (0x343c8, 0x343d8)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x34030 [C4 nc] /\ rw_cells rsegs m' 0x343b8 [C8 an]
       /\ rw_cells rsegs m' 0x343c0 [C4 (Z_to_bv 64 0)] /\ rw_cells rsegs m' 0x343c8 [C8 (Z_to_bv 64 0)]
       /\ rw_cells rsegs m' 0x343d0 [C8 (Z_to_bv 64 0)])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15aec) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 nc an nr rp rs FR N1 N2 N3 N4 N5 SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x343c0, 0x343c4); (0x343c8, 0x343d8)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 7 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 16 + 16)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecGlue RecTail RecChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_calls_free_c rec_clear_c.
Local Open Scope Z_scope.

Definition ofst (qo : option (Z * Z)) : Z := match qo with Some pn => fst pn | None => 0 end.

Lemma c4b : forall m a v, rw_cells rsegs m a [C4 v] -> bytes_at rsegs m a (le4 v).
Proof. intros m a v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma c8b : forall m a v, rw_cells rsegs m a [C8 v] -> bytes_at rsegs m a (le8 v).
Proof. intros m a v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rw_cells_same_bytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf' | rewrite Eb; exact Hb]|].
  rewrite Es. exact Hw.
Qed.

Lemma rec_rep_O_in : forall segs gr sc L A mem R O pn, rec_rep segs gr sc L A mem R O -> In pn O -> In pn (blocks L A).
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. exact (rep_at_blocks segs _ _ _ _ _ _ pn HR (proj1 (HO pn) Hin)).
Qed.

Lemma rec_rep_keep : forall segs gr sc L A mem mem' R O,
  rec_rep segs gr sc L A mem R O ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall p k i, In (p, k) O -> 0 <= i < k -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) ->
  rec_rep segs gr sc L A mem' R O.
Proof.
  intros segs gr sc L A mem mem' R O (Q & HR & HO) KG KW KB. exists Q. split; [|exact HO].
  pose proof HR as (_ & _ & _ & _ & HX & _).
  apply (rep_at_set_word segs (blocks L A) mem mem' gr sc R R Q HR eq_refl eq_refl eq_refl eq_refl).
  - intros a Ha. apply KG. unfold REC_SIZE. lia.
  - exact KW.
  - intros [p k] Hpn i Hi. exact (KB p k i (proj2 (HO (p, k)) Hpn) Hi).
  - apply (scalars_keep segs mem mem' gr R HX). intros x Hx. apply KG. unfold REC_SIZE. lia.
Qed.

Lemma bytes_cell4 : forall m a v, GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le4 v) -> rw_cells rsegs m a [C4 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le4 v)) (le4 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le4; lia | exact H].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes]. reflexivity.
  - cbn [cells_size csize]. rewrite length_le4. reflexivity.
Qed.

Lemma cell8 : forall m a v, GLOB_LO <= a -> a + 8 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le8 v) -> rw_cells rsegs m a [C8 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le8 v)) (le8 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le8; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le8. reflexivity.
Qed.

Lemma keep_c4 : forall m m' a v, bytes_at rsegs m a (le4 v) -> GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  (forall i, 0 <= i < 4 -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) -> rw_cells rsegs m' a [C4 v].
Proof.
  intros m m' a v H H1 H2 K. apply bytes_cell4; [lia | lia |].
  apply (bytes_at_keep rsegs m m' a _ H). intros i Hi. rewrite length_le4 in Hi. apply K. lia.
Qed.

Lemma keep_c8 : forall m m' a v, bytes_at rsegs m a (le8 v) -> GLOB_LO <= a -> a + 8 <= GLOB_LO + Z.of_nat GLOB_N ->
  (forall i, 0 <= i < 8 -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) -> rw_cells rsegs m' a [C8 v].
Proof.
  intros m m' a v H H1 H2 K. apply cell8; [lia | lia |].
  apply (bytes_at_keep rsegs m m' a _ H). intros i Hi. rewrite length_le8 in Hi. apply K. lia.
Qed.

Lemma rw_keep : forall (Pa : Z -> Prop) m m' a cs, rw_cells rsegs m a cs ->
  (forall x, Pa x -> mbyte rsegs m' x = mbyte rsegs m x /\ (writable_at rsegs m x -> writable_at rsegs m' x)) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Pa (a + i)) -> rw_cells rsegs m' a cs.
Proof. intros Pa m m' a cs H K D. apply (rw_cells_transfer rsegs m m' a cs H). intros i Hi. exact (K _ (D i Hi)). Qed.

Lemma ans_facts : forall bl m gr t q, answer_at rsegs bl m gr t q ->
  bytes_at rsegs m (gr + OFF_ANSWER) (le8 (Z_to_bv 64 (ofst q))) /\ (forall pn, q = Some pn -> In pn bl /\ 0 < snd pn).
Proof.
  intros bl m gr [x|] [pn|] H; cbv beta iota delta [answer_at] in H; try contradiction.
  - destruct H as (H1 & _ & H3 & H4 & _). split; [exact H1|]. intros pn' Ep. injection Ep as <-. split; [exact H3 | lia].
  - split; [exact H | intros pn Ep; discriminate].
Qed.

Lemma rep_facts : forall bl m gr y q, reply_at rsegs bl m gr y q ->
  bytes_at rsegs m (gr + OFF_REPLY) (le8 (Z_to_bv 64 (ofst q))) /\
  (exists rs, bytes_at rsegs m (gr + OFF_REPLY_SIZE) (le8 rs)) /\
  (forall pn, q = Some pn -> In pn bl /\ 0 < snd pn).
Proof.
  intros bl m gr [x|] [pn|] H; cbv beta iota delta [reply_at] in H; try contradiction.
  - destruct H as (H1 & H2 & _ & Hx & H3 & H4 & _). split; [exact H1|]. split; [eexists; exact H2|].
    intros pn' Ep. injection Ep as <-. split; [exact H3|].
    destruct x as [|c x]; [exfalso; exact (Hx eq_refl)|]. cbn [length] in H4. lia.
  - destruct H as [H1 H2]. split; [exact H1|]. split; [eexists; exact H2 | intros pn Ep; discriminate].
Qed.

Lemma surv : forall (bl bl' F : list (Z * Z)) pn, Permutation bl (bl' ++ F) -> In pn bl -> ~ In pn F -> In pn bl'.
Proof.
  intros bl bl' F pn HP Hin Hn. assert (H2 : In pn (bl' ++ F)) by (eapply Permutation_in; eassumption).
  apply in_app_or in H2 as [H|H]; [exact H | contradiction].
Qed.

Lemma lay_D1 : forall gr sc Q x y, g1_own gr sc Q -> In x (concat (l_calls Q)) ->
  In y (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) -> fst x <> fst y.
Proof. intros gr sc Q x y (ND & _) Hx Hy. exact (nodup_fst_disj _ _ x y ND Hx Hy). Qed.

Lemma lay_D3 : forall gr sc Q x y, g1_own gr sc Q -> In x (l_spill Q) ->
  In y (oblk (l_answer Q) ++ oblk (l_reply Q)) -> fst x <> fst y.
Proof.
  intros gr sc Q x y (ND & _) Hx Hy.
  exact (nodup_fst_disj (l_spill Q) (oblk (l_answer Q) ++ oblk (l_reply Q)) x y
           (nodup_fst_drop_mid [] (concat (l_calls Q)) (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) ND) Hx Hy).
Qed.

Lemma lay_D2 : forall gr sc Q x y, g1_own gr sc Q -> In x (oblk (l_answer Q)) -> In y (oblk (l_reply Q)) -> fst x <> fst y.
Proof.
  intros gr sc Q x y (ND & _) Hx Hy.
  exact (nodup_fst_disj (oblk (l_answer Q)) (oblk (l_reply Q)) x y
           (nodup_fst_drop_mid [] (l_spill Q) (oblk (l_answer Q) ++ oblk (l_reply Q))
           (nodup_fst_drop_mid [] (concat (l_calls Q)) (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) ND)) Hx Hy).
Qed.

Lemma no1 : forall lo hi a, ~ outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi);
    first [lia | exfalso; apply H; cbn; split; [lia | exact I]].
Qed.

Lemma no2 : forall l1 h1 l2 h2 a, ~ outside [(l1, h1); (l2, h2)] a -> l1 <= a < h1 \/ l2 <= a < h2.
Proof.
  intros l1 h1 l2 h2 a H. destruct (Z_le_gt_dec l1 a); destruct (Z_lt_ge_dec a h1);
    destruct (Z_le_gt_dec l2 a); destruct (Z_lt_ge_dec a h2);
    first [lia | exfalso; apply H; cbn; split; [lia | split; [lia | exact I]]].
Qed.

Lemma out1 : forall lo hi a, a < lo \/ hi <= a -> outside [(lo, hi)] a.
Proof. intros lo hi a H. cbn. split; [lia | exact I]. Qed.

Lemma lay_spill_in : forall S pn, In pn (lay_blocks (RLay [] S None None)) <-> In pn S.
Proof. intros S pn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply concat oblk app]. rewrite app_nil_r. tauto. Qed.

Lemma own_spill : forall gr sc Q, g1_own gr sc Q -> g1_own gr sc (RLay [] (l_spill Q) None None).
Proof.
  intros gr sc Q (ND & AP). split.
  - pose proof (nodup_fst_drop_mid [] (concat (l_calls Q)) (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) ND) as N1.
    cbn [app] in N1. rewrite <- (app_nil_r (oblk (l_answer Q) ++ oblk (l_reply Q))) in N1.
    pose proof (nodup_fst_drop_mid (l_spill Q) (oblk (l_answer Q) ++ oblk (l_reply Q)) [] N1) as N2.
    unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply concat oblk app]. exact N2.
  - intros pn Hpn. apply AP. rewrite lay_spill_in in Hpn. unfold lay_blocks.
    apply in_or_app; right; apply in_or_app; left; exact Hpn.
Qed.

Definition krest (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma krest_trans : forall R1 R2 R3, krest R1 R2 -> krest R2 R3 -> krest R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr N2 N8. rewrite (H2 r Hr N2 N8). exact (H1 r Hr N2 N8). Qed.

Lemma krest_pres : forall R R', regs_preserved R R' -> krest R R'.
Proof. intros R R' H r Hr _ _. exact (H r Hr). Qed.

Ltac preg X := match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Ltac krest_tac X :=
  intros rr Hrr Nrr2 Nrr8; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr Nrr2 Nrr8;
  repeat (destruct CC as [CC|CC]; [subst rr; preg X|]); subst rr; preg X.

Section Steps.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis RCFG : rec_calls_free_g_contract B API.
Hypothesis FREE : free_contract B API.
Hypothesis FREE_NULL : free_null_contract B.

Lemma rc_glob_low : forall a, in_globals frame_G a -> 0 <= a < alloc_ceiling.
Proof using SEGS GFACT.
  intros a Ha. pose proof (in_img_low B SEGS a (proj1 (GFACT a Ha))). pose proof alloc_ceiling_val. lia.
Qed.

Lemma fchain_cp : forall S K E L A mem md b F Lc Ac memc mdc Kc r,
  fchain B API S K E L A mem md b F Lc Ac memc mdc -> alloc_ceiling + K <= S -> S < 2 ^ 63 ->
  YK0s.ret_ok (getr r 1) -> spZ r mod 16 = 0 -> 0 <= Kc -> S - K <= spZ r - Kc -> spZ r <= S ->
  getr r 4 = Z_to_bv 64 (ms_tp B) ->
  (st_init_done Ac = false -> auxv_pre B (ly_sec Lc) (spZ r) memc) ->
  call_pre_k B (aa_MR API) Kc Lc Ac r memc mdc.
Proof.
  intros S K E L A mem md b F Lc Ac memc mdc Kc r
    (HMc & HWc & HBc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSCR & _) HK H63 Hra Hal HKc Hlo Hhi Htp Haux.
  split; [exact HMc|]. split; [exact HWc|]. split; [exact HBc|]. split; [exact Hra|]. split; [exact Hal|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSCR; left; lia|].
  split; [exact Htp|].
  split; [intros a Ha; apply HSCR; right; exact Ha|].
  exact Haux.
Qed.

Lemma fchain_call : forall S K E L A mem md b F Lc Ac regs_c memc mdc Kc Ec G L2 A2 regs2 mem2 md2,
  aa_MR API L A mem md -> alloc_ceiling + K <= S -> S < 2 ^ 63 ->
  fchain B API S K E L A mem md b F Lc Ac memc mdc ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c memc mdc Ec L2 A2 regs2 mem2 md2 ->
  (forall a, hi_img B a -> Ec a -> E a /\ ~ (S - K <= a < S)) ->
  Permutation (blocks Lc Ac) (blocks L2 A2 ++ G) ->
  (forall q k, In (q, k) (user_blocks Ac) -> ~ In (ptr_addr Lc q, k) G -> In (q, k) (user_blocks A2)) ->
  (forall x, In x (user_blocks A2) -> In x (user_blocks Ac)) ->
  ro_agree (ms_segs B) mem2 -> guard_kept B memc mem2 ->
  (st_init_done Ac = true -> st_init_done A2 = true) ->
  (length (st_regions Ac) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (rfree_b (rfree_b b F) G) ->
  fchain B API S K E L A mem md b (F ++ G) L2 A2 mem2 md2.
Proof using CTX AX ERRNO_LOW.
  intros S K E L A mem md b F Lc Ac regs_c memc mdc Kc Ec G L2 A2 regs2 mem2 md2 HM0 HK H63
    (HMc & HWc & HBc & HLE & HRG & HINIT & (vm & Hvm) & HSUB & HPTR & HKEEP & HPERM & HBYTES & HFRAME & HSCR & HRO & HGK & HRES)
    Hlo Hhi (HM2 & HW2 & HB2 & HLE2 & HSTAB & _ & (vm2 & Hvm2) & HFR2 & HKB2 & HSCR2)
    HEc HP2 HK2 HS2 HRO2 HGK2 HI2 HRG2 HRES2.
  pose proof alloc_ceiling_val as AC. pose proof (aa_laws API) as LAWS.
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|].
  split; [exact (layout_le_trans A Ac L Lc L2 HLE HLE2 HRG)|].
  split; [lia|]. split; [tauto|].
  split; [exists vm2; rewrite Hvm2, Hvm; apply with_vmmaps_twice'|].
  split; [intros x Hx; apply HSUB; exact (HS2 x Hx)|].
  split.
  { intros q k Hq. pose proof (HS2 (q, k) Hq) as Hc. rewrite (HSTAB q k Hc Hq). exact (HPTR q k Hc). }
  split.
  { intros q k Hq Hnf.
    assert (Hc : In (q, k) (user_blocks Ac)) by (apply HKEEP; [exact Hq | intros H; apply Hnf; apply in_or_app; left; exact H]).
    apply HK2; [exact Hc|]. rewrite (HPTR q k Hc). intros H; apply Hnf; apply in_or_app; right; exact H. }
  split.
  { eapply Permutation_trans; [exact HPERM|]. eapply Permutation_trans; [apply Permutation_app_tail; exact HP2|].
    rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
  split.
  { intros q k i H2 Hi. pose proof (HS2 (q, k) H2) as Hc.
    pose proof (HKB2 q k i Hc H2 Hi) as Eb. rewrite (HPTR q k Hc) in Eb. rewrite Eb. exact (HBYTES q k i Hc Hi). }
  split.
  { intros a Ha Hno Hs He HE. destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    assert (Hnc : ~ owned B Lc Ac a) by exact (own_any B API AX CTX L A mem md Lc Ac memc mdc a HM0 HMc Ha Hno).
    assert (Hn2 : ~ owned B L2 A2 a) by exact (own_any B API AX CTX L A mem md L2 A2 mem2 md2 a HM0 HM2 Ha Hno).
    assert (Hns : ~ scratch_k B Kc regs_c a) by (unfold scratch_k; intros [H|H]; [apply Hs; lia | exact (He H)]).
    assert (Hnf : ~ Ec a) by (intros H; exact (HE (proj1 (HEc a Ha H)))).
    destruct (HFR2 a Ha Hnc Hn2 Hns Hnf) as [F1 F2]. split; [congruence | tauto]. }
  split.
  { intros a Ha.
    destruct (Z_le_gt_dec (spZ regs_c - Kc) a) as [D1|D1];
      [destruct (Z_lt_ge_dec a (spZ regs_c)) as [D2|D2]|].
    - apply HSCR2. left. lia.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : hi_img B a) by (left; lia).
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch_k B Kc regs_c a) by (unfold scratch_k; intros [H|H]; lia).
      assert (Hnf : ~ Ec a) by (intros H; exact (proj2 (HEc a Hh H) Ha)).
      apply (proj2 (HFR2 a Hh Hn1 Hn2 Hns Hnf)). apply HSCR. left. exact Ha.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : hi_img B a) by (left; lia).
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch_k B Kc regs_c a) by (unfold scratch_k; intros [H|H]; lia).
      assert (Hnf : ~ Ec a) by (intros H; exact (proj2 (HEc a Hh H) Ha)).
      apply (proj2 (HFR2 a Hh Hn1 Hn2 Hns Hnf)). apply HSCR. left. exact Ha. }
  split; [exact HRO2|]. split; [intros i Hi; rewrite (HGK2 i Hi); exact (HGK i Hi)|].
  unfold rfree_b. rewrite fold_left_app. exact HRES2.
Qed.

Lemma rc_auxv : forall L A mem md m' W S, aa_MR API L A mem md -> auxv_pre B (ly_sec L) S mem -> munch W mem m' ->
  (forall a, 0 <= a < alloc_ceiling -> outside W a) -> (forall a, S <= a < 2 ^ 64 -> outside W a) ->
  auxv_pre B (ly_sec L) S m'.
Proof.
  intros L A mem md m' W S HM HAX MU HL HS. pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC0.
  destruct HAX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
  exists av, ar.
  assert (LIB : forall k, (k < 8)%nat -> 0 <= ms_libc B + 8 + Z.of_nat k < 2 ^ 64 /\ outside W (ms_libc B + 8 + Z.of_nat k)).
  { intros k Hk. assert (Ho : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
    pose proof (owned_low B _ LAWS L A mem md _ HM Ho). split; [lia | apply HL; lia]. }
  split; [exact (word_mem_munch _ _ _ _ _ _ MU LIB W1)|].
  split; [intros k Hk; apply (word_mem_munch _ _ _ _ _ _ MU); [|exact (W2 k Hk)]; intros k' Hk'; split; [lia | apply HS; lia]|].
  split; [apply (word_mem_munch _ _ _ _ _ _ MU); [|exact W3]; intros k' Hk'; split; [lia | apply HS; lia]|].
  split; [apply (word_mem_munch _ _ _ _ _ _ MU); [|exact W4]; intros k' Hk'; split; [lia | apply HS; lia]|].
  lia.
Qed.

Lemma rc_free : forall S K E L A mem md b F Lc Ac regs_c memc mdc (qo : option (Z * Z)) (P : config -> Prop),
  aa_MR API L A mem md -> alloc_ceiling + K <= S -> S < 2 ^ 63 ->
  fchain B API S K E L A mem md b F Lc Ac memc mdc ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 10 = Z_to_bv 64 (ofst qo) ->
  (forall pn, qo = Some pn -> In pn (blocks Lc Ac)) ->
  (forall Ln An regs_n memn mdn,
     fchain B API S K E L A mem md b (F ++ oblk qo) Ln An memn mdn ->
     regs_preserved regs_c regs_n ->
     (forall a, in_globals frame_G a \/ spZ regs_c <= a < S ->
        mbyte rsegs memn a = mbyte rsegs memc a /\ (writable_at rsegs memc a -> writable_at rsegs memn a)) ->
     SR rsegs (mkCfg (mkst regs_n (getr regs_c 1) memn (seg_rom rsegs)) mdn) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x18ad0) memc (seg_rom rsegs)) mdc) P.
Proof using SEGS FREE_PC ERRNO_LOW GFACT GOWN AX CTX FREE FREE_NULL.
  intros S K E L A mem md b F Lc Ac regs_c memc mdc qo P HM0 HK H63 FC Hra Hal Hlo Hhi Htp H10 HQ KC.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  change ALLOC_STACK with 8192 in Hlo.
  pose proof FC as (HMc & HWc & HBc & _ & _ & _ & _ & _ & HPTR & _ & _ & _ & _ & _ & HRO & _ & HRES).
  destruct (mr_model B _ LAWS _ _ _ _ HMc) as (Hh & Hl & _).
  destruct qo as [[q k]|].
  - change (ofst (Some (q, k))) with q in H10.
    pose proof (HQ (q, k) eq_refl) as HQk.
    destruct (proj1 (YI04.blocks_In Lc Ac q k) HQk) as (p & EP & Hp).
    assert (INIT : st_init_done Ac = true) by exact (YI04.init_done_of_block Ac (p, k) HWc Hp).
    assert (CP : call_pre B (aa_MR API) Lc Ac regs_c memc mdc).
    { apply (proj2 (call_pre_k_alloc B (aa_MR API) Lc Ac regs_c memc mdc)).
      apply (fchain_cp S K E L A mem md b F Lc Ac memc mdc ALLOC_STACK regs_c FC HK H63 Hra Hal
               ltac:(unfold ALLOC_STACK; lia) Hlo Hhi Htp).
      intros H. rewrite INIT in H. discriminate. }
    pose proof FREE as FR. unfold free_contract in FR. rewrite SEGS, FREE_PC in FR.
    eapply SR_bind.
    { apply (FR Lc Ac regs_c memc mdc p k (rfree_b b F));
        [exact CP | rewrite <- SEGS; exact HRO | exact Hp | rewrite EP; exact H10 | exact HRES]. }
    intros c2 (L2 & A2 & R2 & m2 & md2 & -> & POST & BLK & KEPT & RA2 & GK2 & UB2 & INIT2 & REG2 & RES2).
    pose proof POST as POSTk. apply (proj1 (call_post_k_alloc B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _)) in POSTk.
    pose proof POSTk as (PM & _ & _ & _ & _ & PR & _ & PF & _ & _).
    rewrite SEGS in PF.
    assert (FC2 : fchain B API S K E L A mem md b (F ++ [(ptr_addr L p, k)]) L2 A2 m2 md2).
    { apply (fchain_free B API AX CTX ERRNO_LOW S K E L A mem md b F Lc Ac regs_c memc mdc p k L2 A2 R2 m2 md2
               HM0 HK ltac:(lia) FC Hp Hlo Hhi POST BLK);
        [rewrite SEGS; exact RA2 | exact GK2 | exact UB2 | exact INIT2 | exact REG2 | exact RES2]. }
    rewrite <- (HPTR p k Hp), EP in FC2.
    apply (KC L2 A2 R2 m2 md2 FC2 PR).
    intros a Ha.
    assert (NB : ~ (ptr_addr Lc p <= a < ptr_addr Lc p + k)).
    { rewrite EP. intros Hr. destruct Ha as [Ha|Ha].
      - exact (block_not_hi_img B API AX Lc Ac memc mdc q k a HMc HQk Hr (or_intror (proj1 (GFACT a Ha)))).
      - assert (HH : hi_img B a) by (left; lia).
        exact (block_not_hi_img B API AX Lc Ac memc mdc q k a HMc HQk Hr HH). }
    destruct Ha as [Ha|Ha].
    + destruct (GFACT a Ha) as (I1 & _ & _ & I4). pose proof (rc_glob_low a Ha) as GL.
      assert (NS : ~ scratch_k B ALLOC_STACK regs_c a) by (unfold scratch_k, ALLOC_STACK; intros [H|H]; [lia | exact (I4 H)]).
      destruct (PF a (or_intror I1) (GOWN _ _ _ _ a HMc Ha) (GOWN _ _ _ _ a PM Ha) NS NB) as [E1 E2].
      split; [exact E1 | tauto].
    + assert (NS : ~ scratch_k B ALLOC_STACK regs_c a) by (unfold scratch_k, ALLOC_STACK; intros [H|H]; lia).
      assert (N1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a HMc Ho); lia).
      assert (N2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a PM Ho); lia).
      assert (HH : alloc_ceiling <= a < 2 ^ 64) by lia.
      destruct (PF a (or_introl HH) N1 N2 NS NB) as [E1 E2].
      split; [exact E1 | tauto].
  - change (ofst None) with 0 in H10.
    pose proof (FREE_NULL regs_c memc mdc Hra H10 Hh Hl) as F0. rewrite SEGS, FREE_PC in F0.
    eapply SR_bind; [exact F0|]. intros c ->.
    apply (KC Lc Ac regs_c memc mdc).
    + cbn [oblk]. rewrite app_nil_r. exact FC.
    + intros r _. reflexivity.
    + intros a _. split; [reflexivity | tauto].
Qed.

Lemma rc_rcf : forall S K E L A mem md b regs_c m1 R O (P : config -> Prop),
  aa_MR API L A mem md -> alloc_ceiling + K <= S -> S < 2 ^ 63 ->
  fchain B API S K E L A mem md b [] L A m1 md ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - RCF_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs_c) m1) ->
  getr regs_c 10 = Z_to_bv 64 (G_REC + OFF_CALLS) ->
  getr regs_c 11 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) ->
  g_rec_rep rsegs L A m1 R O ->
  (forall a, nargs_field (G_REC + OFF_CALLS) (length (r_calls R)) a -> E a /\ ~ (S - K <= a < S)) ->
  (forall L1 A1 regs1 m2 md1 Q,
     rep_at rsegs (blocks L A) m1 G_REC REC_SC R Q -> (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
     fchain B API S K E L A mem md b (concat (l_calls Q)) L1 A1 m2 md1 ->
     regs_preserved regs_c regs1 ->
     (forall a, in_globals frame_G a -> ~ nargs_field (G_REC + OFF_CALLS) (length (r_calls R)) a ->
        mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)) ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs m2 a)) ->
     SR rsegs (mkCfg (mkst regs1 (getr regs_c 1) m2 (seg_rom rsegs)) md1) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 REC_CALLS_FREE) m1 (seg_rom rsegs)) md) P.
Proof using SEGS ERRNO_LOW AX CTX RCFG.
  intros S K E L A mem md b regs_c m1 R O P HM0 HK H63 FC Hra Hal Hlo Hhi Htp Haux H10 H11 GR HNE KC.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. assert (RK : RCF_K = 8304) by reflexivity.
  pose proof FC as (HMc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _ & HRES).
  assert (CP : call_pre_k B (aa_MR API) RCF_K L A regs_c m1 md).
  { exact (fchain_cp S K E L A mem md b [] L A m1 md RCF_K regs_c FC HK H63 Hra Hal
             ltac:(unfold RCF_K, ALLOC_STACK; lia) Hlo Hhi Htp Haux). }
  pose proof RCFG as RC. unfold rec_calls_free_g_contract in RC. rewrite SEGS in RC.
  eapply SR_bind.
  { apply (RC L A regs_c m1 md R O b CP); [rewrite <- SEGS; exact HRO | exact H10 | exact H11 | exact GR | exact HRES]. }
  intros c' (L1 & A1 & regs1 & m2 & md1 & Q & -> & HR & HO & CPk & PERM & BK & UK & US & NB & GB & ROc & GK & INI & RGN
    & UNI & RESc).
  pose proof CPk as (PM & _ & _ & _ & _ & PR & _ & PF & _ & _).
  rewrite SEGS in PF.
  assert (FC1 : fchain B API S K E L A mem md b ([] ++ concat (l_calls Q)) L1 A1 m2 md1).
  { apply (fchain_call S K E L A mem md b [] L A regs_c m1 md RCF_K _ (concat (l_calls Q)) L1 A1 regs1 m2 md1
             HM0 HK H63 FC Hlo Hhi CPk);
      [intros a _ Ha; exact (HNE a Ha) | exact PERM | exact UK | exact US | exact ROc | exact GK
      | exact INI | exact RGN | exact RESc]. }
  cbn [app] in FC1. rewrite SEGS in HR, GB |- *.
  apply (KC L1 A1 regs1 m2 md1 Q HR HO FC1 PR GB).
  intros a Ha.
  assert (NS : ~ scratch_k B RCF_K regs_c a) by (unfold scratch_k; intros [H|H]; lia).
  assert (N1 : ~ owned B L A a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a HMc Ho); unfold RCF_K, ALLOC_STACK in *; lia).
  assert (N2 : ~ owned B L1 A1 a) by (intros Ho; pose proof (owned_low B _ LAWS _ _ _ _ a PM Ho); unfold RCF_K, ALLOC_STACK in *; lia).
  assert (NN : ~ nargs_field (G_REC + OFF_CALLS) (length (r_calls R)) a) by (intros H; apply (proj2 (HNE a H)); lia).
  assert (HH : alloc_ceiling <= a < 2 ^ 64) by lia.
  destruct (PF a (or_introl HH) N1 N2 NS NN) as [E1 E2].
  split; [exact E1 | tauto].
Qed.

Lemma blocks_once : forall L A mem md d n X Y, aa_MR API L A mem md -> 0 < n ->
  Permutation (blocks L A) (X ++ Y) -> In (d, n) X -> In (d, n) Y -> False.
Proof.
  intros L A mem md d n X Y HM Hn HP HX HY. pose proof (aa_laws API) as LAWS.
  destruct (in_split _ _ HX) as (x1 & x2 & EX). subst X.
  assert (HB : In (d, n) (blocks L A)).
  { eapply Permutation_in; [apply Permutation_sym; exact HP|].
    apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (in_split _ _ HB) as (b1 & b2 & EB).
  assert (P2 : Permutation (b1 ++ b2) (x1 ++ x2 ++ Y)).
  { apply (Permutation_app_inv _ _ _ _ (d, n)). rewrite <- EB. rewrite <- app_assoc in HP. exact HP. }
  assert (H3 : In (d, n) (b1 ++ b2)).
  { eapply Permutation_in; [apply Permutation_sym; exact P2|]. apply in_or_app. right. apply in_or_app. right. exact HY. }
  destruct (blocks_mid_disjoint B _ LAWS L A mem md b1 b2 d n d n HM EB H3) as [H|H]; lia.
Qed.

Theorem rec_clear_holds : rec_clear_contract B API.
Proof using SEGS FREE_PC ERRNO_LOW GOTG GFACT GOWN AX CTX RCFG FREE FREE_NULL.
  unfold rec_clear_contract.
  intros L A regs mem md R O b PRE RO GR RES.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  assert (RK : RCL_K = 8320) by reflexivity.
  set (n := length (r_calls R)) in *.
  set (E := rec_clear_writes n).
  pose proof (fchain_init B API (spZ regs) RCL_K E L A regs mem md b PRE RO RES eq_refl) as FC0.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & _).
  rewrite SEGS in GR, HWS |- *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8320) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb Eb]. exists bb. unfold mrd, wa. rewrite Eb. reflexivity. }
  pose proof GR as (Q0 & HRep0 & _).
  pose proof HRep0 as (_ & (G1 & _ & G3 & _) & HA0 & HP0 & HX0 & _).
  destruct (ans_facts _ _ _ _ _ HA0) as (AB0 & _).
  destruct (rep_facts _ _ _ _ _ HP0) as (RB0 & (rs0 & RSB0) & _).
  pose proof HX0 as (_ & _ & NRB0 & _).
  assert (NC0 : rw_cells rsegs mem 0x34030 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  assert (AN0 : rw_cells rsegs mem 0x343b8 [C8 (Z_to_bv 64 (ofst (l_answer Q0)))])
    by (apply cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact AB0]).
  assert (NR0 : rw_cells rsegs mem 0x343c0 [C4 (Z_to_bv 64 (r_nreplies R))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact NRB0]).
  assert (RP0 : rw_cells rsegs mem 0x343c8 [C8 (Z_to_bv 64 (ofst (l_reply Q0)))])
    by (apply cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact RB0]).
  assert (RS0 : rw_cells rsegs mem 0x343d0 [C8 rs0])
    by (apply cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact RSB0]).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold REC_CLEAR.
    eapply rc_run1; [exact ST | lia | lia | exact NC0 | lia | exact AN0 | exact NR0 | exact RP0 | exact RS0]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1 & _) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15ad4) by preg X1.
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 16)) by preg X1.
  assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33ff0) by preg X1.
  assert (E1_10 : getr R1 10 = Z_to_bv 64 0x34038) by preg X1.
  assert (E1_11 : getr R1 11 = Z_to_bv 64 (Z.of_nat n)) by preg X1.
  assert (KR1 : krest regs R1) by krest_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 16) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (FC1 : fchain B API (bv_unsigned sp) RCL_K E L A mem md b [] L A m1 md).
  { apply (fchain_own B API SEGS AX GOWN GFACT GOTG (bv_unsigned sp) RCL_K E L A mem md b [] L A mem md m1
             [(bv_unsigned sp - 16, bv_unsigned sp)] FC0 MU1 ltac:(rewrite SEGS; exact WM1) ltac:(lia) ltac:(lia)).
    intros a _ Ha. apply no1 in Ha. left. lia. }
  assert (GR1 : g_rec_rep rsegs L A m1 R O).
  { unfold g_rec_rep. apply (rec_rep_keep rsegs G_REC REC_SC L A mem m1 R O GR).
    - intros a Ha. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha.
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply out1; lia].
    - intros a Ha W. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha.
      assert (Ra : 0 <= a < 2 ^ 64) by lia.
      assert (Oa : outside [(bv_unsigned sp - 16, bv_unsigned sp)] a) by (apply out1; lia).
      exact (proj1 (munch_writable _ _ _ _ _ MU1 Ra Oa) W).
    - intros p k i Hp Hi.
      destruct (block_facts B _ LAWS L A mem md p k i HMR (rec_rep_O_in rsegs G_REC REC_SC L A mem R O (p, k) GR Hp) Hi)
        as (_ & B1 & B2 & _).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply out1; lia]. }
  apply (rc_rcf (bv_unsigned sp) RCL_K E L A mem md b R1 m1 R O _ HMR HCEIL H63 FC1).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL.
  - rewrite SP1. unfold RCF_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - exact (eq_trans (KR1 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) HTP).
  - intros HI. rewrite SP1. apply (auxv_pre_mono B _ (bv_unsigned sp)); [lia|].
    apply (rc_auxv L A mem md m1 [(bv_unsigned sp - 16, bv_unsigned sp)] (bv_unsigned sp) HMR (HAUX HI) MU1);
      intros a Ha; apply out1; lia.
  - rewrite E1_10. reflexivity.
  - exact E1_11.
  - exact GR1.
  - intros a Ha. split; [unfold E, rec_clear_writes; right; left; exact Ha|].
    destruct Ha as (i & Hi & Ha). change (length (r_calls R)) with n in Hi. unfold G_REC, OFF_CALLS in Ha. lia.
  - intros L1 A1 regs1 m2 md1 Q HR HO FC2 PR1 GB1 SK1.
    rewrite E1_1.
    pose proof FC2 as (HM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PERM2 & _).
    destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    assert (R2_2 : reg_get regs1 2 = Z_to_bv 64 (bv_unsigned sp - 16))
      by exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (R2_8 : reg_get regs1 8 = Z_to_bv 64 0x33ff0) by exact (eq_trans (PR1 8 ltac:(unfold callee_saved; lia)) E1_8).
    assert (KR2 : krest regs regs1) by exact (krest_trans _ _ _ KR1 (krest_pres _ _ PR1)).
    pose proof HR as (HS & (CL1 & CL2 & CL3 & CL4 & CL5 & CL6) & HA & HP & HX & HW).
    destruct (ans_facts _ _ _ _ _ HA) as (AB & AQ).
    destruct (rep_facts _ _ _ _ _ HP) as (RB & (rs & RSB) & RQ).
    pose proof HX as (_ & _ & NRB & _).
    assert (GK2 : forall a, G_REC <= a < G_REC + 16 \/ G_REC + 912 <= a < G_REC + 960 -> mbyte rsegs m2 a = mbyte rsegs m1 a).
    { intros a Ha. refine (proj1 (GB1 a _ _)).
      - apply fg_iff. unfold G_REC in Ha. lia.
      - intros (i & Hi & Hb). unfold G_REC, OFF_CALLS in *. lia. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (rw_keep (fun x => spZ R1 <= x < bv_unsigned sp) m1 m2 _ _ FR1 SK1). intros i Hi. cbn in Hi. rewrite SP1. lia. }
    assert (NC2 : rw_cells rsegs m2 (G_REC + OFF_NCALLS) [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))]).
    { apply (keep_c4 m1 m2 _ _ CL3); [unfold GLOB_LO, G_REC, OFF_NCALLS; lia | unfold GLOB_LO, GLOB_N, G_REC, OFF_NCALLS; lia |].
      intros i Hi. apply GK2. unfold G_REC, OFF_NCALLS. lia. }
    assert (AN2 : rw_cells rsegs m2 (G_REC + OFF_ANSWER) [C8 (Z_to_bv 64 (ofst (l_answer Q)))]).
    { apply (keep_c8 m1 m2 _ _ AB); [unfold GLOB_LO, G_REC, OFF_ANSWER; lia | unfold GLOB_LO, GLOB_N, G_REC, OFF_ANSWER; lia |].
      intros i Hi. apply GK2. unfold G_REC, OFF_ANSWER. lia. }
    assert (NR2 : rw_cells rsegs m2 (G_REC + OFF_NREPLIES) [C4 (Z_to_bv 64 (r_nreplies R))]).
    { apply (keep_c4 m1 m2 _ _ NRB);
        [unfold GLOB_LO, G_REC, OFF_NREPLIES; lia | unfold GLOB_LO, GLOB_N, G_REC, OFF_NREPLIES; lia |].
      intros i Hi. apply GK2. unfold G_REC, OFF_NREPLIES. lia. }
    assert (RP2 : rw_cells rsegs m2 (G_REC + OFF_REPLY) [C8 (Z_to_bv 64 (ofst (l_reply Q)))]).
    { apply (keep_c8 m1 m2 _ _ RB); [unfold GLOB_LO, G_REC, OFF_REPLY; lia | unfold GLOB_LO, GLOB_N, G_REC, OFF_REPLY; lia |].
      intros i Hi. apply GK2. unfold G_REC, OFF_REPLY. lia. }
    assert (RS2 : rw_cells rsegs m2 (G_REC + OFF_REPLY_SIZE) [C8 rs]).
    { apply (keep_c8 m1 m2 _ _ RSB);
        [unfold GLOB_LO, G_REC, OFF_REPLY_SIZE; lia | unfold GLOB_LO, GLOB_N, G_REC, OFF_REPLY_SIZE; lia |].
      intros i Hi. apply GK2. unfold G_REC, OFF_REPLY_SIZE. lia. }
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R2_2, R2_8.
      eapply rc_run2; [exact FR2 | exact NC2 | exact AN2 | exact NR2 | exact RP2 | exact RS2 | lia]. }
    intros ms3 (can3 & (m3 & -> & MU3 & WM3 & FR3 & NC3 & AN3 & NR3 & RP3 & RS3) & EQ3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    assert (E3_1 : getr R3 1 = Z_to_bv 64 0x15ae0) by preg X3.
    assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 16)) by preg X3.
    assert (E3_8 : getr R3 8 = Z_to_bv 64 0x33ff0) by preg X3.
    assert (E3_10 : getr R3 10 = Z_to_bv 64 (ofst (l_answer Q))) by preg X3.
    assert (KR3 : krest regs R3) by (apply (krest_trans _ _ _ KR2); krest_tac X3).
    assert (SP3 : spZ R3 = bv_unsigned sp - 16) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
    assert (FC3 : fchain B API (bv_unsigned sp) RCL_K E L A mem md b (concat (l_calls Q)) L1 A1 m3 md1).
    { apply (fchain_own B API SEGS AX GOWN GFACT GOTG (bv_unsigned sp) RCL_K E L A mem md b _ L1 A1 m2 md1 m3
               [(0x34030, 0x34034)] FC2 MU3 ltac:(rewrite SEGS; exact WM3) ltac:(lia) ltac:(lia)).
      intros a _ Ha. apply no1 in Ha. right.
      split; [unfold E, rec_clear_writes; left; unfold G_REC, OFF_NCALLS; lia | right; apply fg_iff; lia]. }
    apply (rc_free (bv_unsigned sp) RCL_K E L A mem md b (concat (l_calls Q)) L1 A1 R3 m3 md1 (l_answer Q) _
             HMR HCEIL H63 FC3).
    + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP3. replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring. rewrite Z.mod_add by lia.
      exact HAL.
    + rewrite SP3. unfold ALLOC_STACK. lia.
    + rewrite SP3. lia.
    + exact (eq_trans (KR3 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) HTP).
    + exact E3_10.
    + intros pn Epn. destruct (AQ pn Epn) as (Hin & _). apply (surv _ _ _ pn PERM2 Hin). intros Hc.
      refine (lay_D1 _ _ Q pn pn HW Hc _ eq_refl).
      apply in_or_app; right; apply in_or_app; left. rewrite Epn. left. reflexivity.
    + intros L2 A2 R4 m4 md2 FC4 PR3 CK3. rewrite E3_1.
      pose proof FC4 as (HM4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PERM4 & _).
      destruct (mr_model _ _ LAWS _ _ _ _ HM4) as (Hh4 & Hl4 & _).
      assert (R4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 16))
        by exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E3_2).
      assert (R4_8 : reg_get R4 8 = Z_to_bv 64 0x33ff0) by exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E3_8).
      assert (KR4 : krest regs R4) by exact (krest_trans _ _ _ KR3 (krest_pres _ _ PR3)).
      pose proof (rw_keep _ m3 m4 _ _ FR3 CK3 ltac:(intros i Hi; cbn in Hi; right; rewrite SP3; lia)) as FR4.
      pose proof (rw_keep _ m3 m4 _ _ NC3 CK3 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as NC4.
      pose proof (rw_keep _ m3 m4 _ _ AN3 CK3 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as AN4.
      pose proof (rw_keep _ m3 m4 _ _ NR3 CK3 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as NR4.
      pose proof (rw_keep _ m3 m4 _ _ RP3 CK3 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as RP4.
      pose proof (rw_keep _ m3 m4 _ _ RS3 CK3 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as RS4.
      eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R4_2, R4_8.
        eapply rc_run3; [exact FR4 | exact NC4 | exact AN4 | exact NR4 | exact RP4 | exact RS4 | lia]. }
      intros ms5 (can5 & (m5 & -> & MU5 & WM5 & FR5 & NC5 & AN5 & NR5 & RP5 & RS5) & EQ5).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
      assert (E5_1 : getr R5 1 = Z_to_bv 64 0x15aec) by preg X5.
      assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 16)) by preg X5.
      assert (E5_8 : getr R5 8 = Z_to_bv 64 0x33ff0) by preg X5.
      assert (E5_10 : getr R5 10 = Z_to_bv 64 (ofst (l_reply Q))) by preg X5.
      assert (KR5 : krest regs R5) by (apply (krest_trans _ _ _ KR4); krest_tac X5).
      assert (SP5 : spZ R5 = bv_unsigned sp - 16) by (unfold spZ; rewrite E5_2; apply unsigned_lit; lia).
      assert (FC5 : fchain B API (bv_unsigned sp) RCL_K E L A mem md b (concat (l_calls Q) ++ oblk (l_answer Q))
                      L2 A2 m5 md2).
      { apply (fchain_own B API SEGS AX GOWN GFACT GOTG (bv_unsigned sp) RCL_K E L A mem md b _ L2 A2 m4 md2 m5
                 [(0x343b8, 0x343c0)] FC4 MU5 ltac:(rewrite SEGS; exact WM5) ltac:(lia) ltac:(lia)).
        intros a _ Ha. apply no1 in Ha. right.
        split; [unfold E, rec_clear_writes; right; right; left; unfold G_REC, OFF_ANSWER, OFF_NREPLIES; lia
               | right; apply fg_iff; lia]. }
      apply (rc_free (bv_unsigned sp) RCL_K E L A mem md b (concat (l_calls Q) ++ oblk (l_answer Q)) L2 A2 R5 m5 md2
               (l_reply Q) _ HMR HCEIL H63 FC5).
      * rewrite E5_1. apply bv_eq. vm_compute. reflexivity.
      * rewrite SP5. replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring. rewrite Z.mod_add by lia.
        exact HAL.
      * rewrite SP5. unfold ALLOC_STACK. lia.
      * rewrite SP5. lia.
      * exact (eq_trans (KR5 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) HTP).
      * exact E5_10.
      * intros pn Epn. destruct (RQ pn Epn) as (Hin & _). apply (surv _ _ _ pn PERM4 Hin). intros Hc.
        apply in_app_or in Hc as [Hc|Hc].
        -- refine (lay_D1 _ _ Q pn pn HW Hc _ eq_refl).
           apply in_or_app; right; apply in_or_app; right. rewrite Epn. left. reflexivity.
        -- refine (lay_D2 _ _ Q pn pn HW Hc _ eq_refl). rewrite Epn. left. reflexivity.
      * intros L3 A3 R6 m6 md3 FC6 PR5 CK5. rewrite E5_1.
        pose proof FC6 as (HM6 & _).
        destruct (mr_model _ _ LAWS _ _ _ _ HM6) as (Hh6 & Hl6 & _).
        assert (R6_2 : reg_get R6 2 = Z_to_bv 64 (bv_unsigned sp - 16))
          by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E5_2).
        assert (R6_8 : reg_get R6 8 = Z_to_bv 64 0x33ff0) by exact (eq_trans (PR5 8 ltac:(unfold callee_saved; lia)) E5_8).
        assert (KR6 : krest regs R6) by exact (krest_trans _ _ _ KR5 (krest_pres _ _ PR5)).
        pose proof (rw_keep _ m5 m6 _ _ FR5 CK5 ltac:(intros i Hi; cbn in Hi; right; rewrite SP5; lia)) as FR6.
        pose proof (rw_keep _ m5 m6 _ _ NC5 CK5 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as NC6.
        pose proof (rw_keep _ m5 m6 _ _ AN5 CK5 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as AN6.
        pose proof (rw_keep _ m5 m6 _ _ NR5 CK5 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as NR6.
        pose proof (rw_keep _ m5 m6 _ _ RP5 CK5 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as RP6.
        pose proof (rw_keep _ m5 m6 _ _ RS5 CK5 ltac:(intros i Hi; cbn in Hi; left; apply fg_iff; lia)) as RS6.
        eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
        { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R6_2, R6_8.
          eapply rc_run4; [exact FR6 | exact NC6 | exact AN6 | exact NR6 | exact RP6 | exact RS6 | lia]. }
        intros ms7 (can7 & (m7 & -> & MU7 & WM7 & NC7 & AN7 & NR7 & RP7 & RS7) & EQ7).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7).
        assert (KR7 : krest regs R7) by (apply (krest_trans _ _ _ KR6); krest_tac X7).
        assert (FC7 : fchain B API (bv_unsigned sp) RCL_K E L A mem md b
                        ((concat (l_calls Q) ++ oblk (l_answer Q)) ++ oblk (l_reply Q)) L3 A3 m7 md3).
        { apply (fchain_own B API SEGS AX GOWN GFACT GOTG (bv_unsigned sp) RCL_K E L A mem md b _ L3 A3 m6 md3 m7
                   [(0x343c0, 0x343c4); (0x343c8, 0x343d8)] FC6 MU7 ltac:(rewrite SEGS; exact WM7) ltac:(lia) ltac:(lia)).
          intros a _ Ha. apply no2 in Ha. right. split; [| right; apply fg_iff; lia].
          unfold E, rec_clear_writes. right; right.
          destruct Ha as [Ha|Ha]; [left | right]; unfold G_REC, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE; lia. }
        assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
        rewrite RPC.
        apply SR_ret.
        assert (RP7r : regs_preserved regs R7).
        { intros r Hr. destruct (Z.eq_dec r 2) as [->|N2]; [preg X7|].
          destruct (Z.eq_dec r 8) as [->|N8]; [preg X7|]. exact (KR7 r Hr N2 N8). }
        set (D := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
        assert (FCD : fchain B API (bv_unsigned sp) RCL_K E L A mem md b D L3 A3 m7 md3)
          by (unfold D; rewrite app_assoc; exact FC7).
        pose proof (fchain_post B API (bv_unsigned sp) RCL_K E L A regs mem md b D L3 A3 R7 m7 md3 eq_refl FCD RP7r)
          as (POSTK & PERM & BK & UK & US & ROF & GKF & INIF & RGF & RESF).
        pose proof FCD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFR7 & _).
        rewrite SEGS in ROF, HFR7.
        assert (KEEP7 : forall x, in_globals frame_G x -> ~ E x ->
                  mbyte rsegs m7 x = mbyte rsegs mem x /\ (writable_at rsegs mem x <-> writable_at rsegs m7 x)).
        { intros x Hx Hn. destruct (GFACT x Hx) as (I1 & _ & _ & I4). pose proof (rc_glob_low x Hx).
          apply HFR7; [right; exact I1 | exact (GOWN _ _ _ _ x HMR Hx) | lia | exact I4 | exact Hn]. }
        assert (M1M : forall x, 0 <= x < bv_unsigned sp - 16 -> mbyte rsegs m1 x = mbyte rsegs mem x).
        { intros x Hx. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply out1; lia]. }
        assert (KRC : forall x, G_REC <= x < G_REC + 8 \/ G_REC + 944 <= x < G_REC + 960 \/ REC_SC <= x < REC_SC + SC_SIZE ->
                  mbyte rsegs m7 x = mbyte rsegs m1 x).
        { intros x Hx. assert (Hg : in_globals frame_G x) by (apply fg_iff; unfold G_REC, REC_SC, SC_SIZE in Hx; lia).
          assert (NE : ~ E x).
          { unfold E, rec_clear_writes. intros [H|[H|[H|H]]]; [| destruct H as (i & Hi & H) | |];
              unfold G_REC, REC_SC, SC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE in *;
              lia. }
          rewrite (proj1 (KEEP7 x Hg NE)). symmetry. apply M1M. pose proof (rc_glob_low x Hg). lia. }
        assert (SPD : forall pn x, In pn (l_spill Q) -> In x D -> fst x <> fst pn).
        { intros pn x Hp Hx. unfold D in Hx. apply in_app_or in Hx as [Hx|Hx].
          - exact (lay_D1 _ _ Q x pn HW Hx (in_or_app _ _ _ (or_introl Hp))).
          - intros Ef. exact (lay_D3 _ _ Q pn x HW Hp Hx (eq_sym Ef)). }
        exists L3, A3, R7, m7, md3, (l_spill Q), D.
        split; [reflexivity|].
        split; [exact POSTK|].
        split.
        { exists (RLay [] (l_spill Q) None None). split; [|intros pn; rewrite lay_spill_in; tauto].
          destruct HS as (S1 & S2 & S3 & _ & _).
          destruct HX as (X1' & X2' & _ & X4' & X5' & X6' & X7' & _ & X9' & X10').
          split.
          { split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
            split; apply glob_wr_at; unfold GLOB_LO, GLOB_N, G_REC, REC_SC, REC_SIZE, SC_SIZE; lia. }
          split.
          { split; [cbn; lia|]. split; [reflexivity|]. split; [exact (c4b _ _ _ NC7)|].
            split; [intros i c P Ec; destruct i; discriminate Ec|].
            split; [|exact CL6].
            apply (call_at_keep rsegs (blocks L A) (blocks L3 A3) m1 m7 REC_SC (r_spill R) (l_spill Q) CL5).
            - intros x Hx. apply KRC. right; right. unfold CALL_SIZE in Hx. unfold SC_SIZE. lia.
            - intros [p k] Hpn. pose proof (call_at_blocks rsegs _ _ _ _ _ (p, k) CL5 Hpn) as Hb. split.
              + apply (surv (blocks L A) (blocks L3 A3) D (p, k) PERM Hb). intros Hd. exact (SPD (p, k) (p, k) Hpn Hd eq_refl).
              + intros i Hi. cbn [fst snd] in *.
                assert (NM : ~ In p (map fst D))
                  by (intros Hm; apply in_map_iff in Hm as (x & Ex & Hx); exact (SPD (p, k) x Hpn Hx Ex)).
                pose proof (BK p k i Hb NM ltac:(lia)) as EB. rewrite SEGS in EB. rewrite EB.
                destruct (block_facts B _ LAWS L A mem md p k i HMR Hb ltac:(lia)) as (_ & B1 & B2 & _).
                symmetry. apply M1M. lia. }
          split; [exact (c8b _ _ _ AN7)|].
          split; [split; [exact (c8b _ _ _ RP7) | exact (c8b _ _ _ RS7)]|].
          split.
          { split; [apply (bytes_at_keep_in rsegs m1 m7 G_REC (G_REC + 8) _ _ X1');
                      [unfold OFF_REFUSE; lia | rewrite length_le4; unfold OFF_REFUSE; lia | intros x Hx; apply KRC; lia]|].
            split; [apply (bytes_at_keep_in rsegs m1 m7 G_REC (G_REC + 8) _ _ X2');
                      [unfold OFF_CODE; lia | rewrite length_le4; unfold OFF_CODE; lia | intros x Hx; apply KRC; lia]|].
            split; [exact (c4b _ _ _ NR7)|].
            split; [apply (bytes_at_keep_in rsegs m1 m7 (G_REC + 944) (G_REC + 960) _ _ X4');
                      [unfold OFF_STATE; lia | rewrite length_le8; unfold OFF_STATE; lia | intros x Hx; apply KRC; lia]|].
            split; [apply (bytes_at_keep_in rsegs m1 m7 (G_REC + 944) (G_REC + 960) _ _ X5');
                      [unfold OFF_HOST; lia | rewrite length_le8; unfold OFF_HOST; lia | intros x Hx; apply KRC; lia]|].
            split; [exact X6'|]. split; [exact X7'|]. split; [cbn; lia|]. split; [exact X9' | exact X10']. }
          exact (own_spill _ _ Q HW). }
        split.
        { intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app; right; apply in_or_app; left; exact Hpn. }
        split.
        { intros pn. split.
          - intros Hd. split.
            + apply HO. unfold D in Hd. unfold lay_blocks. apply in_app_or in Hd as [H|H];
                [apply in_or_app; left; exact H | apply in_or_app; right; apply in_or_app; right; exact H].
            + intros Hs. exact (SPD pn pn Hs Hd eq_refl).
          - intros (Ho & Hs). apply HO in Ho. unfold lay_blocks in Ho. unfold D.
            apply in_app_or in Ho as [H|H]; [apply in_or_app; left; exact H|].
            apply in_app_or in H as [H|H]; [contradiction | apply in_or_app; right; exact H]. }
        split; [exact PERM|].
        split.
        { intros [d k] Hpn.
          assert (Hb : In (d, k) (blocks L A))
            by (eapply Permutation_in; [apply Permutation_sym; exact PERM | apply in_or_app; left; exact Hpn]).
          destruct (In_dec pair_dec (d, k) O) as [Ho|Ho]; [|left; split; assumption].
          pose proof (rec_rep_pos rsegs G_REC REC_SC L A mem R O (d, k) GR Ho) as Hk. cbn [snd] in Hk.
          right. apply HO in Ho. unfold lay_blocks in Ho. apply in_app_or in Ho as [H|H].
          - exfalso. apply (blocks_once L A mem md d k (blocks L3 A3) D HMR Hk PERM Hpn).
            unfold D. apply in_or_app. left. exact H.
          - apply in_app_or in H as [H|H]; [exact H|]. exfalso.
            apply (blocks_once L A mem md d k (blocks L3 A3) D HMR Hk PERM Hpn).
            unfold D. apply in_or_app. right. exact H. }
        split; [exact BK|]. split; [exact UK|]. split; [exact US|].
        split; [exact KEEP7|].
        split; [exact ROF|]. split; [exact GKF|]. split; [exact INIF|]. split; [exact RGF|]. exact RESF.
Qed.

End Steps.
