(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its addresses and numbers changed; 647 of its 671 lines of code are new or changed and 535 lines of the source are left out. *)
(* lib/A/ACtlG/F1.v -- GLUE for stage seg_F1 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:740).  A Theorem Labs lane; route (C) L3 switch by a Theorem Labs lane;
   single writer.  rule 24: no function proved.

   WHAT IT PROVES
     glue_seg_F1 : forall POST (j : nat),
       CF POST (ix_cut C_A81da4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81d40_at [Z.of_nat j])
   with ACtl.v's own CF / ix_cut / C_* notations, i.e. exactly ACtl.v's Section hypothesis seg_F1.

   THE SEGMENT (plan section 2.3 row 40): 0x81d40 -> the malloc entry 0x5337c, then the allocator, returning to
   the exit cut 0x81da4.  The run is a Theorem Labs lane's f1_evt_F (Seg/F1F.v:165) in this lane's narrowed form
   f1_evt_Fs (Seg/F1Fs.v): its two HIGH-byte regions are guarded by 2 <= left, because at left = 1 the byte
   q + 1 = p + n lies past the input block and no visibility fact of the core's world covers it.

   THE PROOF (glue-pattern.md G1-G5 with section 9 for the allocator)
   G1  unfold the entry cut C_A81d40_at (ACtlCutP.v:1955-1964): its index [Z.of_nat j] and its 8 conjuncts.
   G2  the run's premises from the body: register 9 = A and 26 = ASAN_K (FRAC), 22 = p + c and 25 = n - c (CUR
       inside LI), the two input bytes and their shadow bytes from f1_IN's addressable / bytes_at, the store_ok
       of [A + 224, A + 232) from the journal's stack-window presence.  Every bound from VISIBLE state: the
       input block (p, n) of ctl_base through the AR block law, FRAC's spill-base window, the frame law.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical map.
   G4  ProgBridge.fevt_of_evtF, then YA0nR.SRr_fevt_hid at RNG_W (w_H W3): the run WRITES [A + 224, A + 232),
       and the journal must cross it.  The five rng premises: ProgBridge.rng_of_visible of the two input bytes
       (ProgWorldVisHeap.heap_vis), their shadow bytes (KitMem.kitmem_rng_heap_sh1) and the spill cell
       (ProgWorldVisWin.win_vis on the journal's window).
   G5a the journal across the one store (YCbq.ajournal_exec, Wr = [A + 224, A + 232), KitMem.kitmem_awr_win).
   G5b the core's malloc rule AMALLOC4 (Reusable.YC5d.amalloc04_rule) under YA0n.SRr_bind at the run's end
       state, the entry 0x5337c = pc_wrap_malloc (TFIB_SYMS' ts_code): n = flen cx j = t_len (the run's a0,
       0 <= n <= 65535 by f1g_len_u16), o = sp - c_sp cx (FRAC's sp window and the journal's astk_ok:
       o mod 16 = 0, -4096 < o <= 0, so ASTACK - o <= LLVMF_STK), gp / tp (FRAC + afn_pre), ra = 0x81da4,
       the live bytes (YCbq.blocks_bytes_bsum + bsum_perm + the pre's LIVE_LIB), st_nev (the journal + the
       pre's EV_LIB, k <= 14 + 2 j, j <= 255), chain and trace by CHAIN_OF_CUT at (pc_malloc_ra0, 0x81da4),
       the meter by MO_MALLOC_OK.
   G5c the exit C_A81da4_at [j] at k + 1 from the rule's post: the live list gains (res, flen cx j); the
       callee-saved registers 2 3 4 8 9 18-21 26 by aregs_preserved; every memory conjunct of the body by
       ProgWorld.ctl_post_acall_kept on the four kept classes (the stack window above the callee's ASTACK
       window, the class-6 frame and its shadow off the new block by YCbq.sep_block_frame, the input block off
       the new block by YCbq.sep_blocks_pos), composed with the store's own agreement off [A + 224, A + 232);
       the new spill [A + 224] from Lib.Mem.bytes_at_write_same; HB and the input block's addressability by
       a Theorem Labs lane's PROVED ProgWorldShadow.ctl_block_shadow_of_AR at the post AR; the exit's ctl_rt_C (route (C):
       ctl_from carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3) by a Theorem Labs lane's ProgWorldCtlRtC.ctl_rt_C_of_AR at the
       post AR with APostBase.arodata_ok_journalP.  The entry's ctl_rt_C is not read: the run reads no shadow byte
       through it (its two shadow bytes come from f1_IN's addressable).

   FRAC RE-ESTABLISHED BY SHAPE (the trailer conjunct q64 m (fr + 4088) (flag_addr ..) of batch 3 included):
   across the store by KitMem.kitmem_frac_keep (munch over [A + 224, A + 232) + growth), along the register map
   by Kit.kit_frac_move, across the malloc by f1g_frac_mem below (its conjuncts walked generically: a spill
   word or the saved registers by the stack window, a frame word -- header and trailer -- by the frame, the
   frame-shadow list by the shadow).

   SECTION HYPOTHESES (exact texts below; listed in the lane report; each is in ACtl.v's Section on a working branch,
   same name and text)
   - ACtl.v's own, verbatim: LAWS (:237), TFIB_SYMS (:252), CHAIN_OF_CUT (:598-618).
   - AMALLOC4 (ACtl.v:282): the core's malloc rule, as the donor's walk takes it; ACtl.v discharges it with
     Reusable.YCbp.amalloc04_rule_triv at MT := ameter_triv.
   - MO_MALLOC_OK (ACtl.v:283): the meter obligation of amalloc04_rule, trivial at ameter_triv (YCbp.v:17-18).
   - (route (C): no VIS0 / OWNED_RO; ctl_rt_C_of_AR needs neither.)

   SHADOWED NAMES: the six modules that exist both as lib/Reusable/<X> and lib/A/Reusable/<X> (YI04 YI16 YK11
   YK1b YM05 YO09) and lib/Lib/<X> are named through the absolute Module aliases below, never by a partial name.

   BUILD STATE: in the commit message and the lane report (build label, Print Assumptions and the scripted
   closure scan naming every stand-in file the closure reaches). *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k A.AF0m A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.ACtlG.Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisHeap A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldShadow A.Prog.CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.Seg.F1 A.Prog.Seg.F1Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The six doubled modules and lib/Lib, by absolute name (the glue-base rule of 04:45Z). *)
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RAPB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LRg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module KM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.KitMem.
Module CP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Module CC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. Local transport lemmas.  ONE agreement notion: the two memories read the same through lib/Lib's mrd on a
   range.  ACtlCutP's body predicates are NOT convertible with SlotInv's (a Theorem Labs lane 04:4xZ, measured: f1_IN,
   b5_C, b5_PH differ), so Seg/F1.v's keep lemmas cannot be applied to them; these are their twins over
   ACtlCutP's predicates. *)

Definition agree_on (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a).

Lemma f1g_bytes : forall m m' a bs, LMem.bytes_at segs m a bs ->
  agree_on m m' a (a + Z.of_nat (length bs)) -> LMem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). apply HK. lia.
Qed.

Lemma f1g_addr : forall m m' p n, ART.addressable m p n ->
  (forall i, 0 <= i < n -> LMem.mrd A.Img0.rsegs m' (LMem.wa (ART.shadow_addr (p + i))) =
                           LMem.mrd A.Img0.rsegs m (LMem.wa (ART.shadow_addr (p + i)))) ->
  ART.addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) HK. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok).
  split; [exact Hap|]. exists b. split; [rewrite (HK i Hi); exact Hb | exact Hok].
Qed.

Lemma f1g_spill : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (A off v : Z),
  CP.spill regs m off v -> CC.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 408 ->
  RK11.getr regs' 9 = RK11.getr regs 9 ->
  agree_on m m' (A + off) (A + off + 8) ->
  CP.spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v (A' & H9' & Hq) H9 HA0 HA1 Hoff E9 HK.
  assert (Hb : 0 <= A' + off /\ A' + off + Z.of_nat (length (LMem.le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold CP.q64 in Hq; exact (LMem.bytes_at_bound segs m (A' + off) _ Hq)).
  rewrite LMem.length_le8 in Hb.
  assert (Em : A mod 2 ^ 64 = A' mod 2 ^ 64).
  { unfold CC.rgv in H9', H9. rewrite H9 in H9'.
    apply (f_equal (@bv_unsigned 64)) in H9'. rewrite !LMS.unsigned_lit_wrap in H9'. exact H9'. }
  assert (HAA : A' = A) by (clear - Em HA0 HA1 Hoff Hb; Z.div_mod_to_equations; lia).
  subst A'. exists A. split; [unfold CC.rgv in *; rewrite E9; exact H9|].
  unfold CP.q64 in *. apply (f1g_bytes m m'); [exact Hq|].
  rewrite LMem.length_le8. exact HK.
Qed.

(* A write outside a range leaves mrd there. *)
Lemma f1g_write_out : forall (m : word -> option byte) (a : Z) (bs : list byte) (x : Z),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> ~ (a <= x < a + Z.of_nat (length bs)) ->
  LMem.mrd A.Img0.rsegs (write_to_mem m (LMem.wa a) bs) (LMem.wa x) = LMem.mrd A.Img0.rsegs m (LMem.wa x).
Proof.
  intros m a bs x Ha Hl Hx Hout. unfold LMem.mrd.
  rewrite (LMem.write_to_mem_spec bs m a (LMem.wa x) Ha Hl).
  rewrite (LMem.wa_unsigned x Hx).
  destruct (Z.leb_spec0 a x), (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb];
    [exfalso; apply Hout; lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma f1g_write_grows : forall (m : word -> option byte) (a : Z) (bs : list byte) (x : word),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  m x <> None -> write_to_mem m (LMem.wa a) bs x <> None.
Proof.
  intros m a bs x Ha Hl Hm.
  rewrite (LMem.write_to_mem_spec bs m a x Ha Hl).
  destruct (Z.leb_spec0 a (bv_unsigned x)), (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs)));
    cbn [andb]; [| exact Hm | exact Hm | exact Hm].
  intros E. apply nth_error_None in E. lia.
Qed.

(* The same at the raw memory (the mrestrict form ajournal_exec takes, and Lib.Frame.munch). *)
Lemma f1g_write_out_raw : forall (m : word -> option byte) (a : Z) (bs : list byte) (x : word),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> ~ (a <= bv_unsigned x < a + Z.of_nat (length bs)) ->
  write_to_mem m (LMem.wa a) bs x = m x.
Proof.
  intros m a bs x Ha Hl Hout. rewrite (LMem.write_to_mem_spec bs m a x Ha Hl).
  destruct (Z.leb_spec0 a (bv_unsigned x)), (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs)));
    cbn [andb]; [exfalso; apply Hout; lia | reflexivity | reflexivity | reflexivity].
Qed.

(* Every read-only segment of image A ends at or below 0xa1000 (computation over A.Img0.rsegs). *)
Lemma f1g_ro_segs :
  forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa1000)) A.Img0.rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* The read-only span of the image lies below the sink's overflow head, the instance APostBase's
   arodata_ok_journalP takes (its Class ro_below_ofl, APostBase.v:28-29), at the empty [rlo, rhi). *)
Lemma f1g_ro_below : @RAPB.ro_below_ofl segs 0 0 A.AE2k.tfib_sink_head.
Proof.
  intros a [(s & Hs & Hw & Hr) | Hg]; [| lia].
  assert (Hofl : @RI16.sk_ofl_head A.AE2k.tfib_sink_head = 0x5fbf08) by (vm_compute; reflexivity).
  pose proof f1g_ro_segs as Hall. rewrite forallb_forall in Hall.
  pose proof (Hall s Hs) as Hb. rewrite Hw in Hb. cbn [orb] in Hb. apply Z.leb_le in Hb.
  rewrite Hofl. lia.
Qed.

(* The turn's frame length len = min(L, left - h) is a u16 (the malloc request of the segment). *)
Lemma f1g_len_u16 : forall inp j, 1 <= SM.t_left inp j -> 0 <= SM.t_len inp j <= 65535.
Proof.
  intros inp j Hl. unfold SM.t_left in Hl. unfold SM.t_len, SM.f_len, SM.f_L, SM.f_h.
  pose proof (bv_unsigned_in_range 8 (RIM.nthb inp (Z.to_nat (SM.fc inp j)))) as H0.
  pose proof (bv_unsigned_in_range 8 (RIM.nthb inp (Z.to_nat (SM.fc inp j + 1)))) as H1.
  change (bv_modulus 8) with 256 in H0, H1.
  change (bv_unsigned (RIM.nthb inp (Z.to_nat (SM.fc inp j)))) with (SM.inb inp (SM.fc inp j)) in H0.
  change (bv_unsigned (RIM.nthb inp (Z.to_nat (SM.fc inp j + 1)))) with (SM.inb inp (SM.fc inp j + 1)) in H1.
  destruct (2 <=? SM.f_left inp (SM.fc inp j)); lia.
Qed.

(* Find the conjunct of H that is the goal (the conjunct count is never named). *)
Ltac f1g_find H :=
  first [ exact H
        | let H1 := fresh "Hq" in let H2 := fresh "Hr" in
          destruct H as [H1 H2]; first [ exact H1 | f1g_find H2 ] ].

(* Walk a conjunction H and the goal's conjunction of the same shape in lock step, closing each goal conjunct with
   tac applied to the matching conjunct of H.  The record's conjunct count is never named. *)
Ltac f1g_peel H tac :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "Hc" in destruct H as [H1 H]; split; [tac H1 | f1g_peel H tac]
  | _ => tac H
  end.

(* FRAC across a memory change that keeps mrd on the spill window [spZ regs, c_sp cx), on the class-6 frame
   [fr, fr + 4096) and on its shadow [Sfr fr, Sfr fr + 512) -- the allocator's acall_kept classes.  BY SHAPE: a
   spill q64 or the saved registers by the window, a frame q64 (the header words and the trailer q64 at fr + 4088)
   by the frame, the frame-shadow list by the shadow, every register or arithmetic conjunct as is. *)
Lemma f1g_frac_mem : forall (B : RG0f.asyms) cx fr sel (regs : bvmap 5 word) (m m' : word -> option byte),
  CP.FRAC B cx fr sel regs m ->
  (forall a, RG0d.spZ regs <= a < CC.c_sp cx ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a)) ->
  (forall a, fr <= a < fr + 4096 ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a)) ->
  (forall a, CP.Sfr fr <= a < CP.Sfr fr + 512 ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a)) ->
  CP.FRAC B cx fr sel regs m'.
Proof.
  intros B cx fr sel regs m m' HF KS KF KH.
  unfold CP.FRAC in HF |- *. destruct HF as (A & sp & HF).
  pose proof HF as (_ & _ & EspZ & _ & _ & _ & _ & _ & _ & _ & _ & HAS & HspA & HfrA & HA416 & HSsp & HSapp & _).
  unfold CP.FRAME_BYTES, ART.APPMEM_END in *.
  assert (L8 : forall w : word, length (LMem.le8 w) = 8%nat) by (intros w; reflexivity).
  assert (MSA : forall a bs, sp <= a -> a + Z.of_nat (length bs) <= CC.c_sp cx ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 H. apply (KM.kitmem_bytes_at_mrd m m' a bs H). intros i Hi. apply KS. rewrite EspZ. lia. }
  assert (MF : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 H. apply (KM.kitmem_bytes_at_mrd m m' a bs H). intros i Hi. apply KF. lia. }
  assert (MH : forall bs, Z.of_nat (length bs) <= 512 ->
            LMem.bytes_at segs m (CP.Sfr fr) bs -> LMem.bytes_at segs m' (CP.Sfr fr) bs).
  { intros bs H1 H. apply (KM.kitmem_bytes_at_mrd m m' _ bs H). intros i Hi. apply KH. lia. }
  exists A, sp.
  unfold CP.q64 in *.
  f1g_peel HF ltac:(fun H =>
    first [ exact H
          | apply MSA; [lia | rewrite L8; lia | exact H]
          | apply MF; [lia | rewrite L8; lia | exact H]
          | (let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Hl := fresh "Hl" in
             destruct H as (sh & Hsh & Hl); exists sh; split; [|exact Hl];
             apply MH; [rewrite Hl; change CP.FRAME_SHADOW with 392; rewrite Z2Nat.id by lia; lia | exact Hsh])
          | (apply MSA; [lia | unfold CP.saved_bytes; rewrite !length_app, !L8; cbn; lia | exact H]) ]).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Section GlueF1.

(* ACtl.v's Section shape (ACtl.v:183-187), restricted to what this stage uses. *)
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {LS : RO09.lib_shape}.
Variable B : RG0f.asyms.
Variable MT : RC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:251-262, :306-307), verbatim. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation CB cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81d40_at := (ACtlCutP.C_A81d40_at B).
Local Notation C_A81da4_at := (ACtlCutP.C_A81da4_at B).

(* --- ACtl.v's own Section hypotheses, verbatim (ACtl.v:210, :225, :478-498). --- *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word)
    (pc0 ra : Z),
  CB cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* --- The allocator rule at 0x81da0 and its meter obligation (glue-pattern.md section 9; the donor's walk
   takes the rule the same way).  ACtl.v discharges AMALLOC4 with Reusable.YCbp.amalloc04_rule_triv and
   MO_MALLOC_OK by `exact I` at MT := ameter_triv (YCbp.v:17-18). --- *)
Hypothesis AMALLOC4 : Reusable.YC5d.amalloc04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MO_MALLOC_OK : forall (S : Reusable.YG00.astate) (n : Z), Reusable.YC5d.mo_ok MT S (Reusable.YC5d.mo_malloc MT n).

(* ---------------------------------------------------------------------------------------------------------
   The stage (ACtl.v:740, verbatim). *)
Lemma glue_seg_F1 : forall POST (j : nat), CF POST (ix_cut C_A81da4_at [Z.of_nat j]) -> CF POST (ix_cut C_A81d40_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:234-236; C_A81d40_at, ACtlCutP.v:1955-1964). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [CC.cut_body CP.C_A81d40_at CP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  cbv beta iota delta [CC.cut_kmax CC.ix_cut CP.C_A81d40_at CP.ixn nth] in Hk.
  rewrite Nat2Z.id in Hk.
  destruct Hb as (HPerm & HFRAC & Hn26 & HLI & HFLSH & HIN & H248 & HFLC).
  (* G2: the cut's shell facts, opened once. *)
  pose proof HFRAC as HFRACc.
  destruct HFRACc as (Asp & sp & H2sp & Hsp16 & Hspz & H4tp & H8 & H9 & H3gp & H19 & H26 & Hfr32 & HA32 &
    HAle & HspA & HfrA & HA416 & Hsplo & HspE & _).
  destruct HLI as ((Hj255 & H21 & HOUR) & (Hc0 & H22 & H25) & Hleft1 & HIFS).
  destruct HIN as (HaddrIN & HbytesIN).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & Hk0 & _).
  pose proof HB as (HPRE & Hsp1).
  pose proof HPRE as (HAFN & Hra0 & Hp10 & Hn11 & Hpn & Hnlen & Hgarr & Hfrs0 & Hnev0 & Hlive0 & Haro & _).
  pose proof HAFN as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk0 & _ & _ & _).
  (* the turn's cursor and the input block *)
  assert (Hnl : SM.nlen (CC.c_in cx) = CC.c_n cx) by (unfold SM.nlen; symmetry; exact Hnlen).
  assert (Hleftv : SM.t_left (CC.c_in cx) j = CC.c_n cx - SM.t_c (CC.c_in cx) j)
    by (unfold SM.t_left, SM.f_left, SM.t_c; rewrite Hnl; reflexivity).
  assert (Hnpos : 0 < CC.c_n cx) by lia.
  destruct Hpn as [(Hn0 & _) | (Hnr & HinP)]; [lia|].
  assert (HinP3 : In (CC.c_p cx, CC.c_n cx) (RG0d.ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPerm)); exact HinP).
  destruct (RG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx) HAR3 HinP3)
    as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & Hpair & Hnmax).
  pose proof (@RM05.alloc_ceiling_lt rc) as Hceil.
  assert (Hreq : RG00.req_size (CC.c_n cx) = CC.c_n cx)
    by (unfold RG00.req_size; destruct (Z.eqb_spec (CC.c_n cx) 0); lia).
  (* the frame base, from the journal's AR and the shell's frame law (glue-pattern.md G2) *)
  assert (Hin6 : In (6, CC.c_fpos cx) (RG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (RCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (CC.c_fpos cx) HAR3 Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  assert (Efr : fr = RG0f.frame_addr (CC.c_ly cx) 6 (CC.c_fpos cx)) by (apply HL; left; reflexivity).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : RG0f.frame_addr ly3 6 (CC.c_fpos cx) = fr) by (rewrite Efr; unfold RG0f.frame_addr; lia).
  rewrite Efr3 in Hf4096, Hfceil. change (RG00.fs_frame_bytes 6) with 4096 in Hfceil.
  rename Hf4096 into Hfr4096.
  unfold CP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HspE.
  assert (HA0 : 0 <= Asp) by lia.
  assert (HA64 : Asp + 416 <= 2 ^ 64) by lia.
  (* the stack window's placement (the journal's astk_ok at the entry layout) *)
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & Hstk3 & _).
  destruct Hstk3 as (Hc16 & _ & Hac0 & Hslo & _).
  unfold A.ACfn.LLVMF_STK in Hslo.
  pose proof (@RG0f.ASAN_CEIL_range rc) as Hacr. unfold RG0f.ASAN_CEIL in Hacr.
  (* the run's memory premises: the two checked bytes, their shadow bytes, and the spill store *)
  pose proof (ARF.addressable_sub mem3 (CC.c_p cx) (CC.c_n cx) (SM.t_c (CC.c_in cx) j) 1 HaddrIN
                ltac:(lia) ltac:(lia) ltac:(lia)) as HaddrQ.
  destruct (A.Prog.Seg.F1.f1_shadow1 mem3 (CC.c_p cx + SM.t_c (CC.c_in cx) j) HaddrQ) as (kz0 & HKZ0 & HKZok).
  pose proof (A.Prog.Seg.F1.f1_byte1 mem3 (CC.c_p cx) (SM.t_c (CC.c_in cx) j) (CC.c_in cx) HbytesIN ltac:(lia)
                ltac:(rewrite <- Hnlen; lia)) as HB0.
  (* the high byte and its shadow, only under 2 <= left (f1_evt_Fs's guard) *)
  assert (H2 : 2 <= SM.t_left (CC.c_in cx) j ->
    ART.addressable mem3 (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1) 1).
  { intros Hge.
    pose proof (ARF.addressable_sub mem3 (CC.c_p cx) (CC.c_n cx) (SM.t_c (CC.c_in cx) j + 1) 1 HaddrIN
                  ltac:(lia) ltac:(lia) ltac:(lia)) as Had1.
    rewrite Z.add_assoc in Had1. exact Had1. }
  (* G3: the cut's configuration in the run's state form, then the walk at the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (CC.cut_pc (ix_cut C_A81d40_at [Z.of_nat j])) with 0x81d40.
  apply (RA0nR.SRr_xregs_eqv segs W3 (LRg.mkR_of regs3) regs3 RK11.fp_regs
           (Z_to_bv 64 0x81d40) RK11.fp_csr None mem3 (RK11.seg_rom segs) md3 (POST cx));
    [| exact (LRg.xregs_eqv_sym _ _ (LRg.mkR_of_eqv regs3))].
  unfold LRg.mkR_of.
  (* the spill store [A + 224, A + 232) is writable: the journal's stack window is present *)
  assert (HWR : LMem.wr_at segs mem3 (Asp + 224) 8).
  { split; [lia|]. split; [lia|]. intros i Hi.
    destruct (HpresJ (Asp + 224 + i) ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hb).
    unfold wview. change (LMem.wa (Asp + 224 + i)) with (Z_to_bv 64 (Asp + 224 + i)).
    rewrite Hb. discriminate. }
  pose proof (LMem.wr_at_store_ok segs mem3 (Asp + 224) 8 0 8%nat HWR ltac:(lia) ltac:(lia)) as HSOK.
  rewrite Z.add_0_r in HSOK.
  (* the footprint regions, each from a visible region of the walk's state *)
  assert (Hvq : A.ProgBridge.range_visible (RA0n.w_H W3) (CC.c_p cx + SM.t_c (CC.c_in cx) j) 1).
  { apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx));
      [exact HAR3 | exact HinP3 | lia | lia]. }
  assert (Hvq1 : 2 <= SM.t_left (CC.c_in cx) j ->
                 A.ProgBridge.range_visible (RA0n.w_H W3) (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1) 1).
  { intros Hge.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx));
      [exact HAR3 | exact HinP3 | lia | lia]. }
  assert (Hvsp : A.ProgBridge.range_visible (RA0n.w_H W3) (Asp + 224) 8).
  { eapply (A.ProgWorldVisWin.win_vis B);
      [exact HJ | unfold A.ACfn.LLVMF_STK in *; lia ..]. }
  (* the high length byte and its shadow, as f1_evt_Fs takes them; the byte itself is the input's byte c + 1 *)
  assert (HI : exists k1 : byte, 2 <= SM.t_left (CC.c_in cx) j ->
    ov_read_bytes A.Img0.rsegs mem3
      (LMem.wa (Z.shiftr (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1) 3 + ART.ASAN_K)) 1 = Some [k1] /\
    (bv_signed k1 = 0 \/ (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1) mod 8 < bv_signed k1) /\
    ov_read_bytes A.Img0.rsegs mem3 (LMem.wa (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1)) 1 =
      Some [RIM.nthb (CC.c_in cx) (Z.to_nat (SM.t_c (CC.c_in cx) j + 1))]).
  { destruct (Z_lt_le_dec (SM.t_left (CC.c_in cx) j) 2) as [Hlt2 | Hge2].
    - exists kz0. intros Hc. exfalso. lia.
    - destruct (A.Prog.Seg.F1.f1_shadow1 mem3 (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1) (H2 Hge2))
        as (k1 & HK1 & Hk1).
      pose proof (A.Prog.Seg.F1.f1_byte1 mem3 (CC.c_p cx) (SM.t_c (CC.c_in cx) j + 1) (CC.c_in cx) HbytesIN
                    ltac:(lia) ltac:(rewrite <- Hnlen; lia)) as HB1.
      rewrite Z.add_assoc in HB1.
      exists k1. intros _. split; [exact HK1|]. split; [exact Hk1 | exact HB1]. }
  destruct HI as (k1 & HI).
  (* G4: the lift at the footprint RNG_W (w_H W3); the run writes [A + 224, A + 232). *)
  eapply (RA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
            (A.ProgBridge.RNG_W (RA0n.w_H W3)) _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply (A.Prog.Seg.F1Fs.f1_evt_Fs (A.ProgBridge.RNG_W (RA0n.w_H W3))) with
      (A := Asp) (q := CC.c_p cx + SM.t_c (CC.c_in cx) j) (left := SM.t_left (CC.c_in cx) j)
      (k0 := kz0) (k1 := k1) (b1 := RIM.nthb (CC.c_in cx) (Z.to_nat (SM.t_c (CC.c_in cx) j + 1))).
    - exact H9.
    - exact H22.
    - rewrite <- Hleftv in H25. exact H25.
    - exact H26.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HKZ0.
    - exact HKZok.
    - exact HB0.
    - exact HI.
    - exact HSOK.
    - replace (Z.shiftr (CC.c_p cx + SM.t_c (CC.c_in cx) j) 3 + ART.ASAN_K)
        with (ART.shadow_addr (CC.c_p cx + SM.t_c (CC.c_in cx) j))
        by (unfold ART.shadow_addr; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      apply (KM.kitmem_rng_heap_sh1 B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx));
        [exact HAR3 | exact HinP3 | lia | rewrite Hreq; lia].
    - exact (A.ProgBridge.rng_of_visible _ _ _ Hvq).
    - intros Hge.
      replace (Z.shiftr (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1) 3 + ART.ASAN_K)
        with (ART.shadow_addr (CC.c_p cx + SM.t_c (CC.c_in cx) j + 1))
        by (unfold ART.shadow_addr; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      apply (KM.kitmem_rng_heap_sh1 B LAWS ly3 S3 W3 mem3 md3 (CC.c_p cx) (CC.c_n cx));
        [exact HAR3 | exact HinP3 | lia | rewrite Hreq; lia].
    - intros Hge. exact (A.ProgBridge.rng_of_visible _ _ _ (Hvq1 Hge)).
    - exact (A.ProgBridge.rng_of_visible _ _ _ Hvsp). }
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (a1' & a2' & ->).
  cbn [ms_mem] in Hhid.
  (* G5a: the journal across the one store [A + 224, A + 232) (ajournal_exec, awr_byte's stack case). *)
  assert (HJ1 : RCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (CC.c_sp cx) []
                  (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx) (c_mem cx) (c_md cx)
                  (CC.cut_own (ix_cut C_A81d40_at [Z.of_nat j]) cx) ly3 S3 W3
                  (write_to_mem mem3 (LMem.wa (Asp + 224)) (LMem.le8 (Z_to_bv 64 (SM.t_left (CC.c_in cx) j -
                     SM.t_h (CC.c_in cx) j)))) md' k).
  { eapply (RCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun x => Asp + 224 <= x < Asp + 232).
    - exact HJ.
    - intros x Hx. unfold Reusable.YK04.mrestrict. destruct (RA0n.w_H W3 x); [reflexivity|].
      apply f1g_write_out_raw; rewrite ?LMem.length_le8;
        [lia | lia | intros Hc; apply Hx; cbn in Hc; lia].
    - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (RA0n.w_H W3 x); [exact Hx|].
      apply f1g_write_grows; rewrite ?LMem.length_le8; [lia | lia | exact Hx].
    - exact Hhid.
    - exact Hsbm.
    - intros a Ha. apply KM.kitmem_awr_win. unfold A.ACfn.LLVMF_STK. lia. }
  (* G5b: the core's malloc rule at the allocator entry 0x5337c (glue-pattern.md section 9). *)
  assert (Epc : RG0f.pc_wrap_malloc (RG0f.as_code B) = 0x5337c)
    by (rewrite (A.AF0m.ts_code _ TFIB_SYMS); reflexivity).
  assert (Hsaved : LMem.bytes_at segs mem3 (CC.c_sp cx - 104) (CP.saved_bytes cx)).
  { pose proof HFRAC as HFs. unfold CP.FRAC in HFs. destruct HFs as (A2 & sp2 & HFs). f1g_find HFs. }
  lazymatch goal with
  | |- RA0n.SRr _ _ (mkCfg (LMS.MS ?R _ _ _ _ ?mm _) _) _ => set (Rend := R) in *; set (mem1 := mm) in *
  end.
  assert (Hsaved1 : LMem.bytes_at segs mem1 (CC.c_sp cx - 104) (CP.saved_bytes cx)).
  { apply (f1g_bytes mem3 mem1); [exact Hsaved|].
    intros a Ha. rewrite KM.kitmem_saved_len in Ha. subst mem1.
    apply f1g_write_out; rewrite ?LMem.length_le8; [lia | lia | lia | lia]. }
  assert (EspR : RG0d.spZ Rend = sp) by exact Hspz.
  destruct (CHAIN_OF_CUT [] cx (CC.cut_own (ix_cut C_A81d40_at [Z.of_nat j]) cx) ly3 S3 W3 mem1 md' k Rend
              (RG0f.pc_malloc_ra0 (RG0f.as_code B)) 0x81da4 HB HJ1
              ltac:(exact H8) ltac:(reflexivity) Hsaved1
              ltac:(rewrite EspR; lia) ltac:(rewrite EspR; lia)
              ltac:(right; right; left; reflexivity)) as (ch & Hch & Htr).
  (* the request n = flen cx j = t_len, a u16, and the live bytes *)
  pose proof (f1g_len_u16 (CC.c_in cx) j ltac:(lia)) as Hlen.
  assert (Hlive3 : RG01.blocks_bytes S3 + CP.flen cx j <= RG01.LIVE_MAX).
  { rewrite (RCbq.blocks_bytes_bsum B ly3 S3), (RCbq.bsum_perm _ _ HPerm),
      <- (RCbq.blocks_bytes_bsum B (CC.c_ly cx) (CC.c_S cx)).
    unfold CP.flen. unfold A.ACfn.LIVE_LIB in Hlive0. unfold RG01.LIVE_MAX in *. lia. }
  change (RA0n.SRr segs W3 (mkCfg (RK11.mkst Rend (Z_to_bv 64 0x5337c) mem1 (RK11.seg_rom segs)) md') (POST cx)).
  rewrite <- Epc.
  refine (RA0n.SRr_bind segs W3 _ _ (POST cx)
    (AMALLOC4 W3 Rend mem1 A.ACfn.LLVMF_STK (CC.c_sp cx) [] (CC.c_ly cx) (CC.c_S cx) (CC.c_W cx)
       (c_mem cx) (c_md cx) (CC.cut_own (ix_cut C_A81d40_at [Z.of_nat j]) cx) ly3 S3 md' k (CP.flen cx j)
       (sp - CC.c_sp cx) (Z_to_bv 64 0x81da4) ch HJ1
       ltac:(reflexivity)
       ltac:(unfold CP.flen, RG00.MALLOC_MAX; lia)
       Hlive3
       ltac:(rewrite EspR; lia)
       ltac:(rewrite Zminus_mod, Hsp16, Hc16; reflexivity)
       ltac:(lia)
       ltac:(unfold RG0d.ASTACK, A.ACfn.LLVMF_STK; lia)
       ltac:(transitivity (RK11.getr (CC.c_regs cx) 3); [exact H3gp | exact Hgp0])
       H4tp
       ltac:(reflexivity)
       ltac:(vm_compute; reflexivity)
       ltac:(unfold A.ACfn.EV_LIB in Hnev0; lia)
       Hch Htr
       (MO_MALLOC_OK S3 _)) _).
  (* G5c: the continuation is the exit cut at ra = 0x81da4 *)
  intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & res & Ec2 & HJ2 & HPR & Hres & Hfr2 & Hres4096 & Hbl2 & HK & _).
  subst c2.
  pose proof HJ2 as (HAR2 & Hly2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  assert (Efr2 : RG0f.frame_addr ly2 6 (CC.c_fpos cx) = fr) by (rewrite Efr; unfold RG0f.frame_addr; lia).
  assert (Hin62 : In (6, CC.c_fpos cx) (RG01.frames S2)) by (rewrite Hfr2; exact Hin6).
  assert (Hres2 : In (res, CP.flen cx j) (RG0d.ablocks B ly2 S2))
    by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
  destruct (RG0d.al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (CP.flen cx j) HAR2 Hres2)
    as (_ & _ & _ & Hresapp & _ & _ & _).
  assert (HinP2 : In (CC.c_p cx, CC.c_n cx) (RG0d.ablocks B ly2 S2))
    by (rewrite Hbl2; apply in_or_app; left; exact HinP3).
  (* the callee-saved registers the exit body reads (aregs_preserved; Rend keeps them from regs3) *)
  assert (E2 : RK11.getr regs2 2 = RK11.getr regs3 2) by exact (HPR 2 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E3 : RK11.getr regs2 3 = RK11.getr regs3 3) by exact (HPR 3 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E4 : RK11.getr regs2 4 = RK11.getr regs3 4) by exact (HPR 4 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E8 : RK11.getr regs2 8 = RK11.getr regs3 8) by exact (HPR 8 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E9 : RK11.getr regs2 9 = RK11.getr regs3 9) by exact (HPR 9 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E19 : RK11.getr regs2 19 = RK11.getr regs3 19) by exact (HPR 19 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E21 : RK11.getr regs2 21 = RK11.getr regs3 21) by exact (HPR 21 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E26 : RK11.getr regs2 26 = RK11.getr regs3 26) by exact (HPR 26 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E18 : RK11.getr regs2 18 = Z_to_bv 64 (SM.t_len (CC.c_in cx) j))
    by exact (HPR 18 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (E20 : RK11.getr regs2 20 =
                Z_to_bv 64 (CC.c_p cx + SM.t_c (CC.c_in cx) j + Z.min 2 (SM.t_left (CC.c_in cx) j)))
    by exact (HPR 20 ltac:(unfold RG0d.acallee_saved; lia)).
  assert (HspZ2 : RG0d.spZ regs2 = sp) by (unfold RG0d.spZ in Hspz |- *; rewrite E2; exact Hspz).
  (* memory: the store keeps every byte off [A + 224, A + 232) ... *)
  assert (KS1 : forall a, 0 <= a < 2 ^ 64 -> ~ (Asp + 224 <= a < Asp + 232) ->
            LMem.mrd A.Img0.rsegs mem1 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a)).
  { intros a Ha Hn. subst mem1. apply f1g_write_out; rewrite ?LMem.length_le8; lia. }
  (* ... and the malloc keeps its four classes (ProgWorld.ctl_post_acall_kept): the stack window above sp, *)
  assert (KS2 : forall a, sp <= a < CC.c_sp cx ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem1 (LMem.wa a)).
  { intros a Ha.
    destruct (HpresJ a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (Hh & _).
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ HK Hwle (LMem.wa a) Hh).
    rewrite LMem.wa_unsigned by lia. left. split; [lia|]. lia. }
  (* the class-6 frame (off the new block) and its presence after the malloc, *)
  destruct (RG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (CC.c_fpos cx) HAR3 Hin6) as (_ & _ & Hfp3 & Hsh3).
  destruct (RG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (CC.c_fpos cx) HAR2 Hin62) as (_ & _ & Hfp2 & _).
  assert (KF2 : forall a, fr <= a < fr + 4096 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem1 (LMem.wa a) /\
            mem2 (LMem.wa a) <> None).
  { intros a Ha. split.
    - destruct (Hfp3 a ltac:(rewrite Efr3; change (RG00.fs_frame_bytes 6) with 4096; lia)) as ((Hh & _) & _).
      apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ HK Hwle (LMem.wa a) Hh).
      rewrite LMem.wa_unsigned by lia.
      right. right. right. exists 6, (CC.c_fpos cx). split; [exact Hin6|]. split.
      + left. unfold RG0n.in_zr, RCbq.frame_rng. cbn [fst snd]. rewrite Efr3.
        change (RG00.fs_frame_bytes 6) with 4096. lia.
      + intros HE. cbv beta in HE.
        pose proof (RCbq.sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 res (CP.flen cx j) 6
          (CC.c_fpos cx) HAR2 Hres2 Hin62) as Hd.
        unfold RG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efr2 in Hd.
        change (RG00.fs_frame_bytes 6) with 4096 in Hd. lia.
    - destruct (Hfp2 a ltac:(rewrite Efr2; change (RG00.fs_frame_bytes 6) with 4096; lia)) as ((_ & bb & Hbb) & _).
      change (LMem.wa a) with (Z_to_bv 64 a). rewrite Hbb. discriminate. }
  (* the frame's shadow (no shadow byte is in the new block, an application block), *)
  assert (KH2 : forall a, CP.Sfr fr <= a < CP.Sfr fr + 512 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem1 (LMem.wa a)).
  { intros a Ha. unfold CP.Sfr, ART.shadow_addr, ART.ASAN_K in Ha.
    destruct (Hsh3 (a - (fr / 8 + 0x7fff8000)) ltac:(change (RG00.fs_frame_bytes 6 / 8) with 512; lia))
      as ((Hh & _) & _).
    assert (Ea : RG0f.shadow_addr (RG0f.frame_addr ly3 6 (CC.c_fpos cx)) + (a - (fr / 8 + 0x7fff8000)) = a).
    { rewrite Efr3. unfold RG0f.shadow_addr, RG0f.SHADOW_OFF. lia. }
    rewrite Ea in Hh.
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ HK Hwle (LMem.wa a) Hh).
    rewrite LMem.wa_unsigned by lia.
    right. right. right. exists 6, (CC.c_fpos cx). split; [exact Hin6|]. split.
    - right. unfold RG0n.in_zr. cbn [fst snd]. rewrite Efr3.
      change (RG00.fs_frame_bytes 6 / 8) with 512.
      unfold RG0f.shadow_addr, RG0f.SHADOW_OFF. lia.
    - intros HE. cbv beta in HE.
      unfold RG0f.in_app, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Hresapp. lia. }
  (* and the input block (a live block, apart from the new one: YCbq.sep_blocks_pos at the post state) *)
  assert (KI : forall i, 0 <= i < CC.c_n cx ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa (CC.c_p cx + i)) =
            LMem.mrd A.Img0.rsegs mem3 (LMem.wa (CC.c_p cx + i))).
  { intros i Hi. rewrite <- (KS1 (CC.c_p cx + i)) by lia.
    destruct (Hppres (CC.c_p cx + i) ltac:(rewrite Hreq; lia)) as ((Hh & _) & _).
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem1 mem2 _ _ _ HK Hwle
             (LMem.wa (CC.c_p cx + i)) Hh).
    rewrite LMem.wa_unsigned by lia.
    right. left. exists (CC.c_p cx), (CC.c_n cx), i.
    split; [exact HinP3|]. split; [rewrite Hreq; lia|]. split; [reflexivity|].
    intros HE. cbv beta in HE.
    destruct (in_split _ _ HinP3) as (l1 & l2 & El).
    assert (Ebl : RG0d.ablocks B ly2 S2 = l1 ++ (CC.c_p cx, CC.c_n cx) :: l2 ++ (res, CP.flen cx j) :: []).
    { rewrite Hbl2, El, <- app_assoc. reflexivity. }
    pose proof (RCbq.sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 _ _ l1 l2 [] HAR2 Ebl) as Hd.
    unfold RCbq.block_rng, RG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
  (* the store and the malloc composed: mem2 against the entry memory mem3 *)
  assert (KS : forall a, sp <= a < CC.c_sp cx -> ~ (Asp + 224 <= a < Asp + 232) ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a)).
  { intros a Ha Hn. rewrite (KS2 a Ha). apply KS1; lia. }
  assert (KF : forall a, fr <= a < fr + 4096 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a)).
  { intros a Ha. rewrite (proj1 (KF2 a Ha)). apply KS1; lia. }
  assert (KH : forall a, CP.Sfr fr <= a < CP.Sfr fr + 512 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a)).
  { intros a Ha. rewrite (KH2 a Ha). unfold CP.Sfr, ART.shadow_addr, ART.ASAN_K in Ha. apply KS1; lia. }
  (* the movers, one per kind of body fact *)
  assert (MSP : forall off v, 0 <= off <= 408 -> off + 8 <= 224 \/ 232 <= off ->
            CP.spill regs3 mem3 off v -> CP.spill regs2 mem2 off v).
  { intros off v Hoff Hh Hs. apply (f1g_spill regs3 regs2 mem3 mem2 Asp off v Hs H9 HA0 HA64 Hoff E9).
    intros a Ha. apply KS; lia. }
  assert (MBY : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs mem2 a bs).
  { intros a bs H1 H3 H. apply (f1g_bytes mem3 mem2 a bs H). intros x Hx. apply KF. lia. }
  assert (MAD : forall p n, fr <= p -> p + n <= fr + 4096 -> ART.addressable mem3 p n -> ART.addressable mem2 p n).
  { intros p n H1 H3 H. apply (f1g_addr mem3 mem2 p n H). intros i Hi. apply KH.
    unfold CP.Sfr, ART.shadow_addr. lia. }
  assert (HbytesIN2 : LMem.bytes_at segs mem2 (CC.c_p cx) (CC.c_in cx)).
  { apply (f1g_bytes mem3 mem2 _ _ HbytesIN). intros a Ha.
    replace a with (CC.c_p cx + (a - CC.c_p cx)) by lia. apply KI. lia. }
  assert (HaddrIN2 : ART.addressable mem2 (CC.c_p cx) (CC.c_n cx)).
  { exact (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 (CC.c_p cx) (CC.c_n cx)
             (CC.c_p cx) (CC.c_n cx) HAR2 HinP2 ltac:(lia) ltac:(lia) ltac:(rewrite Hreq; lia)). }
  assert (Hsz : res + A.ACtlK.a_size (CP.flen cx j) <= res + RG00.req_size (CP.flen cx j)).
  { unfold A.ACtlK.a_size, RG00.req_size, CP.flen.
    destruct (Z.eqb_spec (SM.t_len (CC.c_in cx) j) 0); lia. }
  assert (LOUR : length (SM.OUR (CC.c_in cx)) = 6%nat)
    by (unfold SM.OUR; rewrite length_map, length_seq; reflexivity).
  destruct (A.Prog.Seg.F1.f1_FS_len (CC.c_in cx) j) as (LID & LFG).
  pose proof (A.Prog.Seg.F1.f1_body_len (CC.c_in cx) j) as LFB.
  (* the exit cut C_A81da4_at [j] (ACtlCutP.v:1968-1979) *)
  change (mkCfg (RK11.mkst regs2 (Z_to_bv 64 0x81da4) mem2 (RK11.seg_rom segs)) md2)
    with (RG0d.cfg_at segs (CC.cut_pc (ix_cut C_A81da4_at [Z.of_nat j])) regs2 mem2 md2).
  apply (HX cx [Z.of_nat j] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2).
  - rewrite Hfr2. exact HF.
  - exact HL.
  - (* the event bound: kmax 14 + 2 j + 1 >= k + 1 *)
    cbv beta iota delta [CC.cut_kmax CC.ix_cut CP.C_A81da4_at CP.ixn nth].
    rewrite Nat2Z.id. lia.
  - cbv beta iota zeta delta [CC.cut_body CC.ix_cut CP.C_A81da4_at CP.ixn nth].
    rewrite Nat2Z.id.
    split; [reflexivity|].
    exists res.
    split; [rewrite Hbl2; apply Permutation_app_tail; exact HPerm|].
    split.
    { (* FRAC: across the store by KitMem.kitmem_frac_keep, along the register map by Kit.kit_frac_move,
         across the malloc by f1g_frac_mem; each by shape, so the trailer q64 (fr + 4088) moves with the rest *)
      assert (HFRAC1 : CP.FRAC B cx fr fr regs3 mem1).
      { apply (KM.kitmem_frac_keep B cx fr fr regs3 mem3 mem1 [(Asp + 224, Asp + 232)] HFRAC).
        - intros x [Hx _]. subst mem1. apply f1g_write_out_raw; rewrite ?LMem.length_le8; lia.
        - intros x Hx. subst mem1. apply f1g_write_grows; rewrite ?LMem.length_le8; [lia | lia | exact Hx].
        - lia.
        - intros A' HA' x Hx. cbn [LFrm.outside]. split; [|exact I]. intros Hin.
          unfold CC.rgv in HA', H9. rewrite H9 in HA'.
          apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !LMS.unsigned_lit_wrap in HA'.
          clear - HA' Hx Hin. Z.div_mod_to_equations. lia.
        - intros x Hx. cbn [LFrm.outside]. split; [|exact I]. lia.
        - intros x Hx. cbn [LFrm.outside]. split; [|exact I]. lia. }
      apply (f1g_frac_mem B cx fr fr regs2 mem1 mem2).
      - exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 regs2 mem1 HFRAC1 E2 E3 E4 E8 E9 E19 E26).
      - intros a Ha. rewrite HspZ2 in Ha. apply KS2. lia.
      - intros a Ha. exact (proj1 (KF2 a Ha)).
      - exact KH2. }
    split; [exact Hn26|].
    split; [exact Hj255|].
    split; [exact Hres|].
    split.
    { (* HB: the new block is addressable for a_size (flen cx j) <= req_size (ctl_block_shadow_of_AR at S2) *)
      unfold CP.HB. split; [lia|].
      exact (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 res (CP.flen cx j)
               res (A.ACtlK.a_size (CP.flen cx j)) HAR2 Hres2 ltac:(lia)
               ltac:(unfold A.ACtlK.a_size; lia) Hsz). }
    split.
    { (* LK *)
      split; [exact Hj255|].
      split; [unfold CC.rgv in H21 |- *; rewrite E21; exact H21|].
      unfold CP.OURb in HOUR |- *. apply MBY; [lia | rewrite LOUR; lia | exact HOUR]. }
    split.
    { (* FC: the spill the run stored, then s4 = p + body and s2 = len, both kept by the callee *)
      split.
      { exists Asp. split; [unfold CC.rgv; rewrite E9; exact H9|].
        unfold CP.q64. apply (f1g_bytes mem1 mem2).
        - exact (LMem.bytes_at_write_same segs mem3 (Asp + 224)
                   (LMem.le8 (Z_to_bv 64 (SM.t_left (CC.c_in cx) j - SM.t_h (CC.c_in cx) j)))
                   ltac:(lia) ltac:(rewrite LMem.length_le8; lia)).
        - intros a Ha. rewrite LMem.length_le8 in Ha. apply KS2. lia. }
      split.
      { unfold CC.rgv. rewrite E20. f_equal.
        unfold SM.t_body, SM.f_body, SM.f_h, SM.t_c, SM.t_left. lia. }
      unfold CC.rgv. exact E18. }
    split.
    { (* FLSH *)
      destruct HFLSH as (HPRO & S128 & HSTK & S144 & HA2691).
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pinad &
        P184 & P256 & P264 & P272 & P32).
      split.
      { split; [exact (MSP 40 _ ltac:(lia) ltac:(lia) P40)|].
        split; [exact (MSP 120 _ ltac:(lia) ltac:(lia) P120)|].
        split; [exact (MSP 136 _ ltac:(lia) ltac:(lia) P136)|].
        split; [exact (MSP 160 _ ltac:(lia) ltac:(lia) P160)|].
        split; [exact (MSP 168 _ ltac:(lia) ltac:(lia) P168)|].
        split; [exact (MSP 176 _ ltac:(lia) ltac:(lia) P176)|].
        split; [exact (MSP 208 _ ltac:(lia) ltac:(lia) P208)|].
        split; [exact (MSP 248 _ ltac:(lia) ltac:(lia) P248)|].
        split; [apply MAD; [lia | lia | exact Pad]|].
        split; [exact HbytesIN2|].
        split; [intros _; exact HaddrIN2|].
        split; [exact (MSP 184 _ ltac:(lia) ltac:(lia) P184)|].
        split; [exact (MSP 256 _ ltac:(lia) ltac:(lia) P256)|].
        split; [exact (MSP 264 _ ltac:(lia) ltac:(lia) P264)|].
        split; [exact (MSP 272 _ ltac:(lia) ltac:(lia) P272)|].
        exact (MSP 32 _ ltac:(lia) ltac:(lia) P32). }
      split; [exact (MSP 128 _ ltac:(lia) ltac:(lia) S128)|].
      split.
      { split; [lia|]. split; [unfold CP.FRAME_BYTES; lia|]. intros a Ha. unfold CP.FRAME_BYTES in Ha.
        destruct (KF2 a ltac:(lia)) as (_ & Hn).
        destruct (mem2 (LMem.wa a)) as [b|] eqn:Eb; [|exfalso; exact (Hn eq_refl)].
        split; [exact (KM.kitmem_wview_some mem2 _ b Eb) | exists b; exact (KM.kitmem_mrd_some mem2 _ b Eb)]. }
      split; [exact (MSP 144 _ ltac:(lia) ltac:(lia) S144)|].
      apply MAD; [lia | lia | exact HA2691]. }
    split; [split; [exact HaddrIN2 | exact HbytesIN2]|].
    split; [exact (MSP 248 _ ltac:(lia) ltac:(lia) H248)|].
    split.
    { (* IFS: the turn's identity / fragment records and the first-fragment state, all frame bytes *)
      destruct HIFS as ((HID & Hidok) & (HFG & Hfgok) & (S104 & S112 & HFB & HFA & HFI)).
      split; [split; [unfold CP.IDBe in HID |- *; apply MBY; [lia | rewrite LID; lia | exact HID] | exact Hidok]|].
      split; [split; [unfold CP.FGBe in HFG |- *; apply MBY; [lia | rewrite LFG; lia | exact HFG] | exact Hfgok]|].
      split; [exact (MSP 104 _ ltac:(lia) ltac:(lia) S104)|].
      split; [exact (MSP 112 _ ltac:(lia) ltac:(lia) S112)|].
      split; [apply MBY; [lia | lia | exact HFB]|].
      split; [apply MAD; [lia | lia | exact HFA]|].
      exact HFI. }
    (* FLC *)
    destruct HFLC as (L256 & L184 & L192 & L80 & L88 & L96 & L272 & L264 & Lad1 & Lad2 & L72 & L64 & L56 & L48).
    split; [exact (MSP 256 _ ltac:(lia) ltac:(lia) L256)|].
    split; [exact (MSP 184 _ ltac:(lia) ltac:(lia) L184)|].
    split; [exact (MSP 192 _ ltac:(lia) ltac:(lia) L192)|].
    split; [exact (MSP 80 _ ltac:(lia) ltac:(lia) L80)|].
    split; [exact (MSP 88 _ ltac:(lia) ltac:(lia) L88)|].
    split; [exact (MSP 96 _ ltac:(lia) ltac:(lia) L96)|].
    split; [exact (MSP 272 _ ltac:(lia) ltac:(lia) L272)|].
    split; [exact (MSP 264 _ ltac:(lia) ltac:(lia) L264)|].
    split; [unfold CP.fragb in Lad1 |- *; apply MAD; [lia | lia | exact Lad1]|].
    split; [apply MAD; [lia | lia | exact Lad2]|].
    split; [exact (MSP 72 _ ltac:(lia) ltac:(lia) L72)|].
    split; [exact (MSP 64 _ ltac:(lia) ltac:(lia) L64)|].
    split; [exact (MSP 56 _ ltac:(lia) ltac:(lia) L56)|].
    exact (MSP 48 _ ltac:(lia) ltac:(lia) L48).
  - (* ctl_rt_C after the malloc: ctl_rt_C_of_AR at the post's AR and the kept read-only view *)
    assert (HRO0 : A.Prog.CtrlBase.arodata_okP segs 0 0 B
                     (RG0n.aview segs (RA0n.w_H (CC.c_W cx)) (CC.c_mem cx))).
    { intros a Ha Ho He. apply Haro; [|exact Ho | exact He].
      destruct Ha as [Ha | Ha]; [left; exact Ha | lia]. }
    pose proof (RAPB.arodata_ok_journalP (SK := A.AE2k.tfib_sink_head) segs 0 0
                  (fun a (Ha : 0 <= a < 0) => False_ind _ (ltac:(lia) : False)) (RO := f1g_ro_below) B
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO0) as HRO2.
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS 0 0 ly2 S2 W2 mem2 md2 HAR2 HRO2).
Qed.

End GlueF1.

Print Assumptions glue_seg_F1.
About glue_seg_F1.
