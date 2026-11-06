(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 756 of its 937 lines of code are new or changed and 2376 lines of the source are left out. *)
(* Segment F18 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the range 0x82634-0x82648.
   ld a0,272(s1); beqz a0,82abc; li a2,6; ld a0,112(s1); mv a1,s2; jal wrapper_bcmp@0x82648; the run goes through the
   call to the return point 0x8264c. Entry cut Inv_B82634_at, exits Inv_B8264c_at (F19 entry) and Inv_B82abc_at (F30
   entry, the beqz target), all of lib/B/Prog/SlotInv.v. The word [s1+272] is b2z (t_8819 j) (SlotInv's FRB), and
   the entry cut pins it by t_8819: for t_8819 j = false it is 0, the beqz is taken and the run lands at 0x82abc with
   no memory change (t_k j = 0 there, so [s1+272] = t_k j as FTK asks); for t_8819 j = true it is nonzero, the beqz
   falls through, and the cut gives rec_inv and the two compare operands. The image-B port of lib/A/Prog/Seg/F18.v:
   image B keeps Phi in s2 (reg 18), the kind k in s8 (reg 24), the sum flag in s9 (reg 25); the record pointer kp
   is the spill s1+280, the word tested by the beqz is at s1+272, the bcmp operands at s1+112 / s1+96, the record
   body pointer Phi+18 at s1+312, 1 - sum_ok at s1+248, and j at s1+240 (LK). The wrapper's instrumented check of
   [s1+112] and s2 passes from their addressability. Adopt 6 (bc14aa7165): FTURN (the cursor spills
   [s1+224] / [s1+232] and the frame's bytes at Phi) and IFS (S j) (the two frame records and the local `first` in
   the frame body) cross the call: the spills lie in [A, A + 448) at or above sp, Phi's bytes in its live block
   below stklo, the records and `first` in the frame, all outside the wrapper's scratch [sp - BCMP_WRAP_K, sp). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
(* The fragment / identity record models (fg_next / fg_class, the rf_* length facts, ING_length), for the record
   lengths f18_FG_length / f18_ID_length; imported before the main imports below, so those keep their names. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memcmp_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

(* The wrapper's stack-scratch size is bcmp_wrap_c's constant, the one SlotInv's F18 / F19 cuts name. The v1.9.0
   addresses of the wrapper's runtime cells (bcmp_wrap_c's BCMP / REAL_BCMP / ... and memcmp_c's MEMCMP). *)
Local Notation BCMP_WRAP_K := BW.BCMP_WRAP_K.
Local Definition BCMP := 0x98930.
Local Definition REAL_BCMP := 0xa2610.
Local Definition REAL_MEMCMP := 0xa2608.
Local Definition GOT_CF := 0xa08e0.
Local Definition CF := 0x13b1e8.
Local Definition MEMCMP := 0x98a00.
Local Notation memcmp_model := SF.memcmp_model.

(* ---- The call on the normalized memory. Since push 5c no cut carries mem_inv (the entry pre gives ro_agree only),
   but the wrapper_bcmp contract asks for it, so seg_F18 runs f18_evt on MemNorm.normalize mem (no byte at a
   read-only address, so mem_inv holds there) and carries the run back to mem by MemNorm.evt_normalize. These
   lemmas move f18_evt's premises to the normalized memory and its post back. Every stack and shadow address is
   above the image top AC.GT, so no segment holds it and it is not read-only. ---- *)

Lemma f18_wx : MN.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* A segment that holds [x, x + n) ends at or below top (lib/B/BzBridge.v find_segment_below). *)
Lemma f18_seg_below : forall (segs : list Segment) top x n s,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true ->
  find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr]. apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f18_ro_hi : forall a, AC.GT <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. assert (HGT : AC.GT = 0x5fe000) by reflexivity. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. rewrite wa_unsigned in E by lia.
  destruct (f18_seg_below rsegs AC.GT a 1 s img_tops_true E ltac:(lia)) as [L|L]; lia.
Qed.

Lemma addressable_norm : forall m p n, MN.ro_agree rsegs m -> addressable m p n ->
  addressable (MN.normalize rsegs m) p n.
Proof.
  intros m p n HRO (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  rewrite <- (MN.mrd_rel rsegs m (MN.normalize rsegs m) _ (MN.mem_rel_normalize rsegs m HRO)). exact Hb.
Qed.

Lemma stk_norm : forall m lo hi, MN.ro_agree rsegs m -> stk rsegs m lo hi -> AC.GT <= lo ->
  stk rsegs (MN.normalize rsegs m) lo hi.
Proof.
  intros m lo hi HRO (H1 & H2 & H) Hlo. pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false) by (apply f18_ro_hi; lia).
  split.
  - rewrite (MN.wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (MN.mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma shadow_rw_norm : forall m, MN.ro_agree rsegs m -> shadow_rw m -> shadow_rw (MN.normalize rsegs m).
Proof.
  intros m HRO H a Ha. pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply f18_ro_hi. assert (HGT : AC.GT = 0x5fe000) by reflexivity.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  split.
  - rewrite (MN.wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (MN.mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma asan_cells_norm : forall m, MN.ro_agree rsegs m -> asan_cells m -> asan_cells (MN.normalize rsegs m).
Proof.
  intros m HRO H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply MN.bytes_at_normalize; assumption.
Qed.

(* The run's stack post, back on the real memory (lib/RoAdapt.v stk_back over lib/B/MemNorm.v). *)
Lemma stk_back : forall m m0 lo hi, MN.mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (MN.ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (MN.wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (MN.mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

(* A state related to an MS state by evt_normalize's ms_rel is that state with its own memory. *)
Lemma ms_rel_MS : forall s R F pc fc rv m0 ro,
  MN.ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ MN.mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' fc' m ro'] R F pc fc rv m0 ro (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hm).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *.
  subst. split; [reflexivity | exact Hm].
Qed.

(* ---- FLI (LK's frame-loop set) across the call: s11, the spill cells [A + off, A + off + 8) with off <= 304, all
   at or above sp, so outside the wrapper's scratch [sp - K, sp) (spill_outW), our[]'s addressability and the three
   frame records' addressability (RAD; the scratch is app memory, sl_addr_keep), the frame's stk (the scratch misses
   the frame) and KNT (adopt 11: the KIND_NAME table's bytes and addressability; the table [0x9f580, 0x9f5f0) is
   image memory below HIGHMEM_BEG, which the scratch misses). ---- *)
Lemma f18_spill_keep : forall regs regs' m m' W off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> 0 <= off <= 440 ->
  (forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x) ->
  Frame.munch W m m' -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v (A' & HA' & Hq) E9 Hoff HW MU.
  exists A'. split; [unfold rg in *; rewrite E9; exact HA'|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply (HW A' HA'). lia.
Qed.

Lemma f18_fli_keep : forall g fr regs regs' m m' W,
  FLI g fr regs m -> getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  (forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x) ->
  Frame.munch W m m' -> Frame.wmono rsegs m m' -> all_app W ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  FLI g fr regs' m'.
Proof.
  intros g fr regs regs' m m' W HF E9 E27 HWsp MU WM AW Hfr Himg.
  unfold FLI, RAD in HF |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    first [ match goal with HK : KNT m |- KNT m' =>
              destruct HK as (HKB & HKA); split;
              [ eapply fl_bytes; [exact HKB | exact MU |]; intros x Hx; apply Himg;
                change (Z.of_nat (length KNC.kind_name_bytes)) with 112 in Hx;
                unfold KNC.KIND_NAME, HIGHMEM_BEG in *; lia
              | eapply sl_addr_keep; [exact HKA | exact MU | exact AW] ] end
          | eapply f18_spill_keep; [eassumption | exact E9 | lia | exact HWsp | exact MU]
          | unfold rg in *; rewrite E27; assumption
          | eapply sl_addr_keep; [eassumption | exact MU | exact AW]
          | eapply (Frame.stk_transport rsegs W m m'); [eassumption | exact MU | exact WM |];
            intros x Hx; left; apply Hfr; lia ].
Qed.

(* FM (the fill-flag spill [A+184], s8 = k, s6 = 1, s9 = sum_ok and the block-pointer spill [A+312]) across the
   call: callee-saved registers and two spill cells at or above sp, outside the wrapper's scratch. *)
Lemma f18_fm_keep : forall g j phi fr regs regs' m m' W,
  FM g j phi fr regs m -> getr regs' 9 = getr regs 9 ->
  getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  (forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x) ->
  Frame.munch W m m' -> FM g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W (H184 & H24 & H22 & H25 & H312) E9 E22 E24 E25 HWsp MU.
  split; [exact (f18_spill_keep regs regs' m m' W 184 _ H184 E9 ltac:(lia) HWsp MU)|].
  split; [unfold rg in *; rewrite E24; exact H24|].
  split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E25; exact H25|].
  exact (f18_spill_keep regs regs' m m' W 312 _ H312 E9 ltac:(lia) HWsp MU).
Qed.

(* ---- The turn's two frame records keep fixed lengths (model): the fragment record t_FG j 72 bytes (fg_next keeps
   72 in every class) and the identity record t_ID j 38 bytes (every ingest keeps 38, RcIdentModel.ING_length).
   Copied from prover a Theorem Labs lane's lib/B/Prog/Seg/F20.v (a working branch 81dc3c31079, its rl_ lemmas), which this file does not
   import. IFS's transport across the call needs both records inside the frame body. ---- *)
Lemma f18_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.
Lemma f18_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.
Lemma f18_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. pose proof (f18_fg_n len g FR) as Hn. unfold fg_first, fg_body.
    rewrite !length_app, length_skipn, (RcFragLib.rf_bsl_length g 6 6),
      (RcFragLib.rf_bsl_length g 27 (fg_n g)) by lia.
    cbn [length]. lia.
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply RcFragLib.rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply RcFragLib.rf_clear_length, RcFragLib.rf_fg_join_length;
      solve [exact HL | exact HG | apply (f18_fg_n len); exact FR | apply f18_keep_T; exact KEEP].
Qed.
Lemma f18_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (f18_next_length 1 1 1 1 1); solve [exact IH | unfold t_g; apply fr50_length].
Qed.
Lemma f18_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn. cbv zeta.
    assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact IH | exact IH]. }
    assert (Hf : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                           (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
    { unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact Hr | exact Hr]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; exact Hf.
Qed.

(* FTURN across the call: the cursor spills [A+224] / [A+232] (at or above sp, outside the scratch) and the frame's
   bytes at Phi (at most len of them, inside Phi's live block, which the caller puts outside the scratch). *)
Lemma f18_turn_keep : forall g j phi regs regs' m m' W,
  FTURN g j phi regs m -> getr regs' 9 = getr regs 9 ->
  (forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x) ->
  (forall x, phi <= x < phi + t_len (g_in g) j -> Frame.outside W x) ->
  Frame.munch W m m' -> FTURN g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' W (H224 & H232 & Hphi & Hlen) E9 HWsp HWphi MU.
  split; [exact (f18_spill_keep regs regs' m m' W 224 _ H224 E9 ltac:(lia) HWsp MU)|].
  split; [exact (f18_spill_keep regs regs' m m' W 232 _ H232 E9 ltac:(lia) HWsp MU)|].
  split; [|exact Hlen].
  eapply fl_bytes; [exact Hphi | exact MU |]. intros x Hx. apply HWphi. lia.
Qed.

(* The body of the first-fragment state is at most 23 bytes (the bytes after position 27 of the 50-byte frame
   prefix t_g), so FSb's three byte groups lie inside `first`, [fr + 2880, fr + 2920) (Tac_ro.tr_body_length). *)
Lemma f18_body_length : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn. lia.
  - rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* IFS across the call: the identity record [fr + 2688, fr + 2726), the fragment record [fr + 2768, fr + 2840) and
   the local `first` [fr + 2880, fr + 2920) lie in the frame body, which the write misses; the write is app memory,
   so `first` stays addressable; FI reads the ghost bytes only. *)
Lemma f18_ifs_keep : forall g fr j regs regs' m m' W,
  IFS g fr j regs m -> Frame.munch W m m' -> all_app W ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  IFS g fr j regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr j regs regs' m m' W ((Hid & Hidok) & (Hfg & Hfgok) & HFS) MU AW HWfr.
  unfold FSj, FSb, u32, b8 in HFS. destruct HFS as (Hh & Hn & Hb & Hfst & HFI).
  pose proof (f18_body_length (g_in g) j) as Hbl.
  split; [split; [|exact Hidok]|split; [split; [|exact Hfgok]|]].
  - unfold IDBe in *. eapply fl_bytes; [exact Hid | exact MU |].
    rewrite f18_ID_length. intros x Hx. change (Z.of_nat 38) with 38 in Hx. apply HWfr. lia.
  - unfold FGBe in *. eapply fl_bytes; [exact Hfg | exact MU |].
    rewrite f18_FG_length. intros x Hx. change (Z.of_nat 72) with 72 in Hx. apply HWfr. lia.
  - unfold FSj, FSb, u32, b8.
    split; [apply (fl_bytes W m m' _ _ Hh MU); rewrite length_le4; intros x Hx; apply HWfr; lia|].
    split; [apply (fl_bytes W m m' _ _ Hn MU); cbn [length]; intros x Hx; apply HWfr; lia|].
    split; [apply (fl_bytes W m m' _ _ Hb MU); intros x Hx; apply HWfr; lia|].
    split; [exact (sl_addr_keep m m' W (fr + 2880) 40 Hfst MU AW) | exact HFI].
Qed.

(* A spill cell survives a register change that keeps s1 (no memory change). *)
Lemma f18_spill_reg : forall regs regs' m off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> spill regs' m off v.
Proof.
  intros regs regs' m off v (A' & HA' & Hq) E9. exists A'.
  split; [unfold rg in *; rewrite E9; exact HA' | exact Hq].
Qed.

(* LK (with FLI) survives a register change that keeps s1 and s11 (no memory change). *)
Lemma f18_lk_reg : forall g fr j regs regs' m,
  LK g fr j regs m -> getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 -> LK g fr j regs' m.
Proof.
  intros g fr j regs regs' m (Hj & H240 & HOUR & HFLI) E9 E27.
  split; [exact Hj|]. split; [exact (f18_spill_reg regs regs' m 240 _ H240 E9)|]. split; [exact HOUR|].
  unfold FLI in HFLI |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    first [ eapply f18_spill_reg; [eassumption | exact E9]
          | unfold rg in *; rewrite E27; assumption
          | assumption ].
Qed.

(* [A+272] = b2z (t_8819 j) and t_k j agree on the t_8819 j = false arm: ctrlparse gives kind 0 for a frame without
   the 0x8819 header (t_8819 inp j is cp_hdr (t_len inp j) (t_g inp j)). *)
Lemma f18_tk0 : forall inp j, t_8819 inp j = false -> t_k inp j = 0.
Proof.
  intros inp j H. unfold t_k, RcParse.ctrlparse.
  replace (RcParse.cp_hdr (t_len inp j) (t_g inp j)) with (t_8819 inp j) by reflexivity.
  rewrite H. reflexivity.
Qed.

Section F18.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HBC : BW.bcmp_wrap_contract.

Lemma f18_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (w272 vcmp lo : Z),
    s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 R ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 w272)) -> w272 <> 0 -> 0 <= w272 < 2 ^ 64 ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> (6 <= length ls)%nat ->
    bytes_at rsegs m R rs -> (6 <= length rs)%nat ->
    memcmp_model ls rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 6 -> addressable m R 6 ->
    app_mem (L + 6) -> app_mem (L + 7) -> app_mem (R + 6) -> app_mem (R + 7) ->
    (L + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 R) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8264c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82634) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs w272 vcmp lo -> -> HLb HRb H272 Hw272nz Hw272b H112 HBL HLls HBR HLrs Hmm HMI HADL HADR
    HaL6 HaL7 HaR6 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  assert (HL272 : ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 w272))).
  { pose proof (bytes_at_ov_read rsegs m (A + 272) (le8 (Z_to_bv 64 w272)) 0 8 H272 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL112 : ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 112) (le8 (Z_to_bv 64 L)) 0 8 H112 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  (* 0x82634 ld a0,272(s1); 0x82638 beqz a0,82abc: a0 = w272 <> 0, not taken *)
  step.
  step.
  replace (bv_eqb (Z_to_bv 64 w272) (Z_to_bv 64 0)) with false
    by (symmetry; apply bv_eqb_neq; intro Eq; apply Hw272nz;
        apply (f_equal bv_unsigned) in Eq; rewrite !unsigned_lit in Eq by lia; exact Eq).
  cbv iota.
  (* 0x8263c li a2,6; 0x82640 ld a0,112(s1); 0x82644 mv a1,s2; 0x82648 jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HBC as HB. unfold BW.bcmp_wrap_contract, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evt_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; exact HaR6.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & HBpl & HBpr).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x8264c)) with (Z_to_bv 64 0x8264c)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 0x8264c), a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* The t_8819 j = false arm, 0x82634 -> 0x82abc: ld a0,272(s1) reads the word 0 and the beqz at 0x82638 is taken. No
   memory change; a0 = 0. *)
Lemma f18_evt_skip :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 0)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                              (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 0x82abc) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82634) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A -> H272.
  assert (HL272 : ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 0))).
  { pose proof (bytes_at_ov_read rsegs m (A + 272) (le8 (Z_to_bv 64 0)) 0 8 H272 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  (* 0x82634 ld a0,272(s1); 0x82638 beqz a0,82abc: a0 = 0, taken *)
  step. step.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in replace cnd with v by (vm_compute; reflexivity); cbv iota
  | _ => idtac
  end.
  apply evt_done. reflexivity.
Qed.

(* Lib-evt -> SR bridge: the one place of this file that uses the lazy-model lemma AsanLift.evt_SR_canon_lazy. It is
   used by seg_F18 for the run 0x82634 -> 0x82abc (f18_evt_skip, no memory access but the word [s1+272]) and for the
   run 0x82634 -> 0x8264c (f18_evt). That run reads the words [s1+272, s1+280) and
   [s1+112, s1+120), the operand bytes [L, L+6) and [Phi, Phi+6) and their shadow bytes at (a >> 3) + 0x7fff8000, the
   runtime cells of the wrapper (REAL_BCMP 0xa2610, REAL_MEMCMP 0xa2608, GOT_CF 0xa08e0, CF+254 / CF+255 at
   0x13b2e6 / 0x13b2e7, the shadow-map cells of asan_cells), and writes only the wrapper's stack scratch
   [sp - 4560, sp) (BCMP_WRAP_K). sl_run in Tac_slot takes the UL evt and applies ul_entry, but the bcmp wrapper
   contract lives in Lib.Exec, so this run is a Lib.Exec.evt and feeds evt_SR_canon_lazy directly. *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* A cell at A' + d (0 <= d < 448) of the spill base A' = s1 lies at or above sp when s1 = A >= sp, so it is outside
   the wrapper's stack scratch [sp - K, sp). The two spill bases agree (A' = A) because a cell inside the scratch
   would put A' in [0, 2^64). *)
Lemma spill_outW : forall regs A A' sp x,
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> sp <= A -> rg regs 9 A' ->
  BCMP_WRAP_K + 448 <= sp -> sp <= 2 ^ 64 ->
  A' <= x < A' + 448 -> Frame.outside [(sp - BCMP_WRAP_K, sp)] x.
Proof.
  intros regs A A' sp x Hs1 HAb HspA HA' Hk Hsp Hx.
  cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
  unfold BCMP_WRAP_K in *.
  assert (Hb' : 0 <= A' < 2 ^ 64) by lia.
  assert (EA' : A' = A).
  { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in *; rewrite <- HA'; exact Hs1).
    apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
  subst A'. lia.
Qed.

(* FRA moves across a run that writes only a region W disjoint from the frame / spill / saved / shadow / low image
   (the wrapper_bcmp main-stack scratch [sp-K,sp), disjoint from the frame on the side stack for frames):
   Tac_slot.sl_stk_run, whose FakeStack-record premise comes from Tac_slot's fsrec_munch_lo and whose input-block
   premise from fra_in_apart, both from the premise that W writes nothing below stklo outside the frame body. The
   entry-anchored slot window [S - SLOT_STACK, S) on mem' is the caller's (bcmp_fra builds it from the call's stk
   post). *)
Lemma sl_stk_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 336 <= x < A + 344 -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 40 <= x < A + 56 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HSTKW HWframe HWimg HWspill HWsel
    HWsaved HWsh HWfs E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  pose proof HFRA as HF0. destruct HF0 as (A & sp & s5 & _ & HAH & _).
  apply (Tac_slot.sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK
           HSTKW HWframe HWimg HWspill HWsel HWsaved HWsh); [| | exact E2 | exact E3 | exact E4 | exact E8 |
           exact E9 | exact E19 | exact E26].
  - intros Hrec. eapply fsrec_munch_lo with (W := W); [exact Hrec | exact HAH | exact MU | exact HWfs].
  - (* the input block: below stklo and apart from the frame (fra_in_apart), so outside W by HWfs *)
    intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & Hxf & _). apply HWfs; [exact Hxlo | lia].
Qed.

(* bytes_at sub-range (local copy of lib.Prog.RcBoxLib.bytes_at_sub, imported qualified would shadow the step engine). *)
Lemma ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite firstn_length, skipn_length; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* The first 6 bytes of a carried byte list (the bcmp operands: only these are compared, and only these lie
   outside the wrapper's stack scratch by the cut's disjointness). *)
Lemma ba_first6 : forall m a bs, bytes_at rsegs m a bs -> (6 <= length bs)%nat ->
  bytes_at rsegs m a (firstn 6 bs) /\ length (firstn 6 bs) = 6%nat.
Proof.
  intros m a bs H Hl. split.
  - pose proof (ba_sub m a bs 0 6 H ltac:(lia)) as Hs. cbn [Z.of_nat skipn] in Hs.
    rewrite Z.add_0_r in Hs. exact Hs.
  - rewrite firstn_length. lia.
Qed.

Lemma memcmp_firstn : forall n l r, memcmp_model (firstn n l) (firstn n r) n = memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

Lemma out1 : forall lo hi x, (x < lo \/ hi <= x) -> Frame.outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn [Frame.outside]. split; [lia | exact I]. Qed.

Lemma bsl_len_le : forall bs k n, (length (RF.bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold RF.bsl. rewrite firstn_length. apply Nat.le_min_l. Qed.

(* SlotInv's record invariant rec_inv at Phi (= s2), the spill base A (= s1) and the record pointer kp (= [A+280]),
   across a write that misses Phi's 50 bytes, the spills [A+248, A+320) (rec_inv's [A+248] and [A+312]), the low
   image (the shadow bytes of Phi+14..Phi+17) and kp's halfword [kp+20, kp+22). Used by seg_F18 and seg_F19. *)
Lemma rec_inv_kept : forall g j phi A kp m m' W,
  rec_inv g j phi A kp m -> Frame.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> Frame.outside W x) ->
  (forall x, A + 248 <= x < A + 320 -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (0 <= kp -> kp + 22 <= 2 ^ 64 -> forall x, kp + 20 <= x < kp + 22 -> Frame.outside W x) ->
  rec_inv g j phi A kp m'.
Proof.
  intros g j phi A kp m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H312 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & H288 & Hf16 & Hkpub & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2)
    MU OWphi OWspill OWimg OWkp.
  assert (SHlo : forall t, 14 <= t <= 17 -> 0 <= Z.shiftr (phi + t) 3 + ASAN_K < HIGHMEM_BEG).
  { intros t Ht. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (shadow_of_app (phi + t) (Hpap (phi + t) ltac:(lia))) as His.
    unfold shadow_addr, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, ASAN_K in *.
    destruct His as [His|His]; lia. }
  unfold rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [unfold q64 in *; eapply fl_bytes; [exact H312 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [eapply fl_bytes; [exact H18 | exact MU | intros x Hx; apply OWphi; unfold t_blk in Hx;
            pose proof (bsl_len_le (t_g (g_in g) j) 18 32) as BL; change (Z.to_nat 32) with 32%nat in BL; lia]|].
  split; [eapply fl_bytes; [exact H34 | exact MU | intros x Hx; apply OWphi;
            pose proof (bsl_len_le (t_g (g_in g) j) 34 6) as BL; change (Z.to_nat 6) with 6%nat in BL; lia]|].
  exists field16, v14, v15, v16, v17.
  split; [unfold q64 in *; eapply fl_bytes; [exact H288 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [unfold u16 in *; eapply fl_bytes; [exact Hf16 | exact MU | rewrite length_le2; intros x Hx; apply (OWkp Hkp0 Hkpub); lia]|].
  split; [exact Hkpub|]. split; [exact Hkp0|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb14 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb15 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb16 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb17 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs14 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 14 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs15 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 15 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs16 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 16 ltac:(lia)); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs17 | exact MU | cbn [length]; intros x Hx; apply OWimg; pose proof (SHlo 17 ltac:(lia)); lia]|].
  split; [exact Heq1|]. exact Heq2.
Qed.

(* FRA and ENT across one wrapper_bcmp call from a FRA cut: the call writes only its main-stack scratch
   W = [sp - K, sp) (disjoint from the frame by fra_frame, below the spill base A, above the low image
   and the shadow, above stklo <= S - SLOT_STACK since S - 4096 < sp, and inside the slot window
   [S - SLOT_STACK, S)), keeps the FRA registers, keeps the entry-anchored slot window (outside W from mem, inside
   W from the call's stk post on [sp - FN_STACK, sp)), and materializes pages (mat_le). The run's memory has
   ro_agree (the call ran on the normalized memory, MemNorm.evt_normalize), not mem_inv. Since push 5c the cut
   carries ENT next to FRA: ent_store over the scratch write (its stack bounds and ownership half from the same
   a_laws_store that moves AH) and ent_mat over the model step. Shared by seg_F18 and seg_F19. *)
Lemma bcmp_fra : forall g fr hb regs regs' mem mem' md md' A,
  FRA B APIf ra g fr hb regs mem md ->
  ENT APIf g hb mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> AC.aspZ regs <= A ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  Frame.munch [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] mem mem' ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' A HFRA HENT Hs1 HAb HspA Hfrapp MU WM HroM HSTKW
    Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat.
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrw & _ & _ & _).
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, BCMP_WRAP_K, AF.SLOT_STACK; lia).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HSTKS : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K) (g_S g) Hwin
                ltac:(rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia)) as (Hw1 & Hw2).
    destruct (stk_split rsegs mem (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) (g_S g) Hw2
                ltac:(rewrite Haspz; unfold BCMP_WRAP_K; lia)) as (_ & Hw3).
    destruct (stk_split rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) HSTKW
                ltac:(unfold BCMP_WRAP_K, FN_STACK, AF.SLOT_STACK; lia)) as (_ & HwW).
    assert (Hw1' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K)).
    { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
      intros x Hx. left. apply out1. lia. }
    assert (Hw3' : stk rsegs mem' (AC.aspZ regs) (g_S g)).
    { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
      intros x Hx. left. apply out1. lia. }
    apply (stk_merge rsegs mem' _ (AC.aspZ regs) _); [| exact Hw3' | rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia].
    apply (stk_merge rsegs mem' _ (AC.aspZ regs - BCMP_WRAP_K) _); [exact Hw1' | exact HwW |].
    rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia. }
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  assert (Hallapp : all_app W).
  { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (Hwlo : AC.GT <= AC.aspZ regs - BCMP_WRAP_K)
    by (rewrite Haspz in *; unfold AC.GT, BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  assert (Hrtdj : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN, AC.GT, BCMP_WRAP_K in *.
    rewrite Haspz in *. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
    unfold AC.a_store_ok. right; left. rewrite Haspz in *.
    unfold BCMP_WRAP_K, AF.SLOT_STACK in *. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL)
    as [HAH' HownEq HSTKeq HSTKhieq].
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x).
  { intros A' HA' x Hx. subst W.
    apply (spill_outW regs A A' (AC.aspZ regs) x Hs1 HAb HspA HA'); [| unfold APPMEM_END in *; lia | exact Hx].
    rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run g fr hb regs regs' mem mem' md W HFRA MU WM HroM Hallapp Hrtdj HAH' HSTKeq HSTKS).
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. destruct Hdisjfr as [Hd|Hd]; unfold BCMP_WRAP_K in *; lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - intros A' HA' x Hx. apply (HA9 A' HA' x). lia.
    - intros A' HA' x Hx. apply (HA9 A' HA' x). lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K in *. lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      assert (Hin : in_shadow x).
      { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - intros x Hxlo _. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia.
    - exact Fr2.
    - exact Fr3.
    - exact Fr4.
    - exact Fr8.
    - exact Fr9.
    - exact Fr19.
    - exact Fr26. }
  assert (HWcases : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/
    (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
  { intros x Hx. subst W.
    destruct (Z_lt_le_dec x (AC.aspZ regs - BCMP_WRAP_K)) as [Hl|Hl]; [left; apply out1; left; exact Hl|].
    destruct (Z_lt_le_dec x (AC.aspZ regs)) as [Hh|Hh]; [|left; apply out1; right; exact Hh].
    right; left. rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia. }
  assert (HENT' : ENT APIf g hb mem' md).
  { apply (ent_store B APIf ra g fr hb regs mem mem' md [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]
             HENT HFRA MU HWcases HSTKeq HSTKhieq).
    intros a _ Hown0. exact (proj2 (HownEq a) Hown0). }
  split.
  { apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat. }
  eapply ent_mat; [exact HENT' | exact Hmat].
Qed.

(* The runtime cells the wrapper_bcmp contract reads, from the FRA runtime invariant. *)
Lemma bcmp_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\
  bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp mem md HRT.
  destruct HRT as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  split; [exact HAC0|]. split; [exact HSW0|].
  split; [apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity|].
  split; [apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity|].
  split; [exact HGOTCF|].
  split.
  { pose proof (ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

(* seg_F18 on SlotInv's cuts (S_F18 of the image-B segment forms). The entry cut pins the word [s1+272] by t_8819 j
   (adopt 6's short-arm guard: [A+272] = b2z (t_8819 j)), so the proof splits on t_8819 j, the value the beqz at
   0x82638 decides. t_8819 j = false: the word is 0, the beqz is taken, and the run reaches the F30 cut Inv_B82abc_at
   with only a0 changed (FTK's [A+272] = t_k j holds since t_k j = 0, f18_tk0). t_8819 j = true: the word is nonzero,
   the cut gives rec_inv and the two compare operands, and the run 0x82634 -> 0x8264c through the wrapper reaches the
   F19 cut Inv_B8264c_at. FRA gives what the cut text leaves out: the frame in app memory above GT (fra_app), the
   frame apart from the wrapper's scratch (fra_frame at K = BCMP_WRAP_K), sp <= APPMEM_END (sp <= A <= S <
   APPMEM_END), and Phi's live block below stklo (a_laws_blocks), so FTURN's Phi bytes miss the scratch. *)
Lemma seg_F18 : forall j : nat,
  Hat B APIf ra (Inv_B8264c_at B APIf ra) j -> Hat B APIf ra (Inv_B82abc_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82634_at B APIf ra) j.
Proof.
  intros j Hexit H30 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hs4 & HFM &
    (A & kp & w272 & Hs1 & HAb & HspA & Hs2 & Hs8 & Hs6 & H272 & Hw272b & H8819f & H8819t) & HTURN & HIFS).
  subst c. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (C8819 : t_8819 (g_in g) j = false \/ t_8819 (g_in g) j = true)
    by (destruct (t_8819 (g_in g) j); [right | left]; reflexivity).
  destruct C8819 as [E8819 | E8819].
  { (* t_8819 j = false: [A+272] = 0 = t_k j, the beqz at 0x82638 is taken to the F30 cut 0x82abc *)
    pose proof (H8819f E8819) as Ew. subst w272.
    pose proof (f18_tk0 (g_in g) j E8819) as Htk0.
    pose proof HFRA as HFRA2.
    destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
      Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
      Hspillq & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
      HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
    apply (sl_run_lib regs (Z_to_bv 64 0x82634) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x82abc /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 25 = getr regs 25 /\
         getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\ getr R0 26 = getr regs 26 /\
         getr R0 27 = getr regs 27)
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f18_evt_skip with (A := A).
        - unfold rg in Hs1; exact Hs1.
        - unfold q64 in H272; exact H272. }
      { intros ms' E.
        eexists _, (Z_to_bv 64 0x82abc), mem. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [unfold rg in Hs1; exact (eq_sym Hs1)|].
        do 7 (split; [reflexivity|]).
        reflexivity. }
    - intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er25 &
        Er22 & Er24 & Er26 & Er27) Hreg Hmat.
      subst pc' mem'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
      assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
      assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md').
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
          [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
      assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md')
        by (eapply ent_mat; [exact HENT | exact Hmat]).
      pose proof HFM as (H184 & H24 & H22 & H25 & H312).
      (* no memory change: the bundles move by the register equalities (an empty write set for the keep lemmas) *)
      assert (MU0 : Frame.munch [] mem mem) by (apply Frame.munch_refl).
      assert (HWsp0 : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside [] x)
        by (intros; exact I).
      assert (HIexit : Inv_B82abc_at B APIf ra g j
                         (mkCfg (mkst regs' (Z_to_bv 64 0x82abc) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA''|]. split; [exact HENT''|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
        split; [unfold rg in *; rewrite Fr18; exact Hs2|].
        split; [unfold rg in *; rewrite Fr20; exact Hs4|].
        split; [exact (f18_turn_keep g j phi regs regs' mem mem [] HTURN Fr9 HWsp0 (fun _ _ => I) MU0)|].
        split; [exact (f18_lk_reg g fr j regs regs' mem HLK Fr9 Fr27)|].
        split.
        { split; [exact (f18_spill_reg regs regs' mem 184 _ H184 Fr9)|].
          split; [unfold rg in *; rewrite Fr22; exact H22|].
          split; [unfold rg in *; rewrite Fr24; exact H24|].
          split; [exists A; split; [unfold rg in *; rewrite Fr9; exact Hs1 | rewrite Htk0; exact H272]|].
          unfold rg in *; rewrite Fr25; exact H25. }
        split; [exact (f18_ifs_keep g fr (S j) regs regs' mem mem [] HIFS MU0 I (fun _ _ => I))|].
        exact (f18_spill_reg regs regs' mem 312 _ H312 Fr9). }
      pose proof (H30 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR. }
  (* t_8819 j = true: [A+272] <> 0, the beqz falls through; the run goes through the wrapper call to 0x8264c *)
  destruct (H8819t E8819) as (Hw272nz & HRI & L & L2 & ls & rs & ls2 & rs2 &
     H112 & HLb & HBL & HLls & HBR & HLrs & Hmm & HADL & HADR & HaL6 & HaL7 & HaR6 & HaR7 & HdjL & HdjR & Hdj50 &
     Hdjkp &
     H96 & HL2b & HBL2 & HLls2 & HBR2 & HLrs2 & Hmm2 & HADL2 & HADR2 & HaL26 & HaL27 & HaR212 & HaR213 & HdjL2 & HdjR2).
  pose proof HRI as (Hphi0 & Hphi50 & _).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (_ & Hfrapp).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hfrw & _ & _ & _).
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, BCMP_WRAP_K, AF.SLOT_STACK; lia).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
  destruct (bcmp_cells sp mem md HRT) as (HAC0 & HSW0 & HRBc & HRMc & HGC & HC254 & HC255).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  (* Phi's live block (Phi, a_size len) ends at or below stklo <= sp - FN_STACK (fra_win), below the scratch *)
  destruct (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity))
    as [_ _ Hphiend _ _].
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HK1 : AC.aspZ regs - FN_STACK + BCMP_WRAP_K <= AC.aspZ regs)
    by (unfold FN_STACK, AF.SLOT_STACK, BCMP_WRAP_K; lia).
  assert (HK2 : HIGHMEM_BEG <= AC.aspZ regs - FN_STACK) by lia.
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x82634) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x8264c /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 26 = getr regs 26 /\
       getr R0 18 = getr regs 18 /\ getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\
       getr R0 27 = getr regs 27 /\ getr R0 20 = getr regs 20 /\ getr R0 25 = getr regs 25 /\
       getr R0 10 = Z_to_bv 64 0 /\
       Frame.munch W mem mem' /\ Frame.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* The wrapper contract asks for mem_inv, which the cut does not carry (push 5c): run f18_evt on the normalized
       memory (mem_inv_normalize) and carry the run back to mem by MemNorm.evt_normalize from FRA's ro_agree. *)
    pose proof (MN.mem_rel_normalize rsegs mem Hro) as REL0.
    eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (MN.evt_normalize rsegs); [exact f18_wx | exact Hro |].
      eapply f18_evt with (A := A) (L := L) (R := phi) (ls := ls) (rs := rs) (w272 := w272) (vcmp := 0)
        (lo := AC.aspZ regs - FN_STACK).
      - unfold rg in Hs1; exact Hs1.
      - unfold rg in Hs2; exact Hs2.
      - exact HLb.
      - lia.
      - unfold q64 in H272; exact (MN.bytes_at_normalize rsegs mem _ _ Hro H272).
      - exact Hw272nz.
      - exact Hw272b.
      - unfold q64 in H112; exact (MN.bytes_at_normalize rsegs mem _ _ Hro H112).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HBL).
      - exact HLls.
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HBR).
      - exact HLrs.
      - exact Hmm.
      - exact (MN.mem_inv_normalize rsegs mem).
      - exact (addressable_norm mem L 6 Hro HADL).
      - exact (addressable_norm mem phi 6 Hro HADR).
      - exact HaL6.
      - exact HaL7.
      - exact HaR6.
      - exact HaR7.
      - exact HdjL.
      - exact HdjR.
      - exact (stk_norm mem _ _ Hro HW0 ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia)).
      - exact HK1.
      - exact HK2.
      - exact HaspB.
      - exact (asan_cells_norm mem Hro HAC0).
      - exact (shadow_rw_norm mem Hro HSW0).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HRBc).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HRMc).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HGC).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HC254).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HC255). }
    { intros ms' (s0 & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
                  & E & MU & WM & MI' & ST' & AC' & SW') & REL & SAME).
      subst s0.
      destruct (ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
      eexists _, (Z_to_bv 64 0x8264c), (ms_mem ms'). split; [exact Ems|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [unfold rg in Hs1; rewrite Hs1; reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [unfold rg in Hs2; rewrite Hs2; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [exact (MN.munch_rel rsegs _ mem (MN.normalize rsegs mem) (ms_mem ms') m0' REL0 HREL SAME MU)|].
      split; [exact (MN.wmono_rel rsegs mem (MN.normalize rsegs mem) (ms_mem ms') m0' REL0 HREL SAME WM)|].
      split; [exact (MN.ro_agree_of_mem_rel rsegs (ms_mem ms') m0' HREL)|].
      exact (stk_back (ms_mem ms') m0' _ _ HREL ST'). }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er18 & Er22 & Er24 & Er27 &
      Er20 & Er25 & Er10 & MU & WM & HRO' & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact Er10).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    destruct (bcmp_fra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' A HFRA HENT Hs1 HAb HspA
                Hfrapp MU WM HRO' ST' Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat) as (HFRA'' & HENT'').
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (HOW : forall x, (x < AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= x) -> Frame.outside W x)
      by (intros x Hx; subst W; apply out1; exact Hx).
    assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x).
    { intros A' HA' x Hx. subst W.
      apply (spill_outW regs A A' (AC.aspZ regs) x Hs1 HAb HspA HA'); [| unfold APPMEM_END in *; lia | exact Hx].
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
    assert (HRI' : rec_inv g j phi A kp mem').
    { apply (rec_inv_kept g j phi A kp mem mem' W HRI MU).
      - intros x Hx. apply HOW. destruct Hdj50 as [Hd|Hd]; lia.
      - intros x Hx. apply HOW. lia.
      - intros x Hx. apply HOW. rewrite Haspz. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia.
      - intros Hkp0 Hkpb x Hx. apply HOW. destruct Hdjkp as [Hd|Hd]; lia. }
    assert (HWphi : forall x, phi <= x < phi + t_len (g_in g) j -> Frame.outside W x).
    { intros x Hx. apply HOW. left. unfold AC.a_size, flen in Hphiend.
      unfold FN_STACK, AF.SLOT_STACK, BCMP_WRAP_K in *. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia. }
    destruct (ba_first6 mem L2 ls2 HBL2 HLls2) as (HBL2f & HLf2).
    destruct (ba_first6 mem (phi + 6) rs2 HBR2 HLrs2) as (HBR2f & HRf2).
    assert (HIexit : Inv_B8264c_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x8264c) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|]. split; [exact HENT''|]. split; [exact Hgn|]. split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
        eapply sl_addr_keep; [exact Hphiad | exact MU | exact Hallapp]. }
      split.
      { destruct HLK as (Hj' & (A3 & HA3 & Hq240) & HOURb & HFLI). split; [exact Hj|]. split.
        - exists A3. split; [unfold rg in *; rewrite Fr9; exact HA3|].
          unfold q64 in *. eapply (fl_bytes W); [exact Hq240 | exact MU |]. rewrite length_le8. intros x Hx.
          subst W. apply (spill_outW regs A A3 (AC.aspZ regs) x Hs1 HAb HspA HA3); [| | lia].
          + rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
          + unfold APPMEM_END in *. lia.
        - split.
          + unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
            rewrite OUR_length. intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia.
          + apply (f18_fli_keep g fr regs regs' mem mem' W HFLI Fr9 Fr27 HA9 MU WM Hallapp).
            * intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia.
            * intros x Hx. apply HOW. left.
              rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
      split; [unfold rg in *; rewrite Fr20; exact Hs4|].
      split; [exact (f18_fm_keep g j phi fr regs regs' mem mem' W HFM Fr9 Fr22 Fr24 Fr25 HA9 MU)|].
      split.
      { exists A, kp, L2, (firstn 6 ls2), (firstn 6 rs2).
        split; [unfold rg; rewrite Fr9; exact Hs1|].
        split; [exact HAb|].
        split; [rewrite HaspEq; exact HspA|].
        split; [unfold rg; rewrite Fr18; exact Hs2|].
        split; [unfold rg; rewrite Fr24; exact Hs8|].
        split; [unfold q64 in *; eapply (fl_bytes W); [exact Hs6 | exact MU |]; rewrite length_le8; intros x Hx;
                apply HOW; lia|].
        split; [unfold rg; exact Fr10|].
        split; [exact HRI'|].
        split.
        { unfold q64 in *. eapply (fl_bytes W); [exact H96 | exact MU |]. rewrite length_le8. intros x Hx.
          apply HOW. lia. }
        split; [exact HL2b|].
        split.
        { eapply (fl_bytes W); [exact HBL2f | exact MU |]. rewrite HLf2. intros x Hx. apply HOW.
          destruct HdjL2 as [Hd|Hd]; lia. }
        split; [lia|].
        split.
        { eapply (fl_bytes W); [exact HBR2f | exact MU |]. rewrite HRf2. intros x Hx. apply HOW.
          destruct HdjR2 as [Hd|Hd]; lia. }
        split; [lia|].
        split; [rewrite memcmp_firstn; exact Hmm2|].
        split; [eapply sl_addr_keep; [exact HADL2 | exact MU | exact Hallapp]|].
        split; [eapply sl_addr_keep; [exact HADR2 | exact MU | exact Hallapp]|].
        split; [exact HaL26|]. split; [exact HaL27|]. split; [exact HaR212|]. split; [exact HaR213|].
        split; [rewrite HaspEq; exact HdjL2|].
        split; [rewrite HaspEq; exact HdjR2|].
        split; [rewrite HaspEq; exact Hdj50|].
        rewrite HaspEq; exact Hdjkp. }
      split; [exact (f18_turn_keep g j phi regs regs' mem mem' W HTURN Fr9 HA9 HWphi MU)|].
      exact (f18_ifs_keep g fr (S j) regs regs' mem mem' W HIFS MU Hallapp HWfr). }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F18.
