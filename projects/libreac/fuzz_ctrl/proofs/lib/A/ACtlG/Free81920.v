(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module paths and module names changed; 507 of its 559 lines of code are new or changed and 3060 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtl.v, with its module names, addresses and numbers changed; 409 of its 435 lines of code are new or changed and 533 lines of the source are left out. *)
(* lib/A/ACtlG/Free81920.v -- the ONE free-site lemma of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput:
   the round trip's `jal wrapper_free` at 0x81920, whose return address 0x81924 is the cut C_A81924_at.  Segments
   R13, R15, R16 and R20 all end there (plan section 2.5 row 0x81920: ONE lemma shared by the four, as ctrl's
   r_free_cont, Seg/R15.v:315).  Written by a Theorem Labs lane's glue lane; single writer.  Consumers: R15 / R16
   (a Theorem Labs lane), R13 (a Theorem Labs lane), R20 (a Theorem Labs lane).  rule 24: no function proved (the allocator step of a walk).

   WHAT IT PROVES
     glue_free_81920 : at the free's entry 0x53378 (a stage's pre-run end state, cfg_at_MS read backwards) with
       ra = 0x81924 and a0 = phi, the journal at the call state (own6, k <= 2b+1), the live list a permutation of
       the entry blocks ++ [(phi, rnb cx b)], and C_A81924_at's whole body at the CALL map R and the pre-free memory
       (its block list the entry blocks), the walk reaches POST if the exit cut C_A81924_at [b] does.

   THE PROOF (glue-pattern.md section 9, steps 2-4)
   - The core's free rule afree04_rule (YC5d.v:76), a Section hypothesis of the walk as in the donor (A/ACfj.v:110),
     applied directly at the call state through SRr_bind: its start pc is pc_wrap_free (as_code B) = 0x53378
     (CtrlTSyms' ts_code, AF0l.v:10).  Premises: the journal; (phi, n) live (the Permutation); a0 = phi; the stack
     offset o := sp - c_sp cx (FRAC: sp mod 16 = 0, c_sp cx - 4096 < sp <= A, A + 416 <= c_sp cx; astk_ok's
     sp0 mod 16 = 0), so ASTACK - o < 16384 + 4096 <= LLVMF_STK; gp / tp (FRAC + afn_pre); ra = 0x81924 and
     ret_ok; st_nev (journal + the pre's EV_LIB headroom, k <= 13); chain_pre and the call trace by CHAIN_OF_CUT at
     the pair (pc_free_ra0, 0x81924); the freed block is not an entry block (not_in_entry: the live list is a
     permutation of entry ++ [(phi, n)] and AR's blocks are pairwise disjoint with req_size n >= 1); the meter.
   - Its continuation is the exit cut at ra: journal at k + 1 (own6), frames unchanged, the live list l1 ++ l2 a
     permutation of the entry blocks (Permutation_app_inv), the callee-saved registers kept (aregs_preserved: every
     register C_A81924_at's body reads, 2 3 4 8 9 19 21 22 23 25 26, is callee-saved), and acall_kept.
   - The body's memory crosses the free through a Theorem Labs lane's ctl_post_acall_kept (mrd equality at a visible byte
     of a kept class): the spill area [sp, c_sp cx) is high memory above the free's stack window (journal's
     astk_ok and stack presence); the class-6 frame [fr, fr + 4096) and its shadow [Sfr fr, Sfr fr + 512) are a
     live frame of S3 (AR_frames_law: present and visible), disjoint from the freed block (sep_block_frame; the
     block is app memory, the shadow is not); the input block is a live block apart from the freed one
     (sep_blocks).  After the free the frame bytes are present again by AR_frames_law at S2, and the input
     block's shadow is addressable by A.ProgWorldShadow.ctl_block_shadow_of_AR (heap shadow is no kept class).
   - ctl_rt_C after the free (route (C)): A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post's AR, with the read-only view
     of the non-writable segments (rlo = rhi = 0) kept from the entry's arodata_okS by APostBase.arodata_ok_journalP.
   - FRAC's top bound is non-strict (c_sp cx <= APPMEM_END, batch 4 B5.4): every address the proof touches lies
     strictly below c_sp cx (the spill area [sp, c_sp cx), the frame [fr, fr + 4096) with fr + 3136 <= A <
     c_sp cx), so the non-strict bound gives each one's range; c_sp cx itself need not be strict.

   SECTION HYPOTHESES (exact text below)
   - LAWS (YCbq Section a0's), TFIB_SYMS (ACtl.v:191), CHAIN_OF_CUT (ACtl.v:434, verbatim with the six duplicated
     core modules written fully qualified): ACtl.v's own Section hypotheses.
   - AFREE4 : afree04_rule: the core's allocator rule, as the donor walk takes it (A/ACfj.v:110).
   - MOK_FREE : the meter admits a free at every state.  ACtl.v's top fixes MT := YCbp.ameter_triv, whose mo_ok is
     True (YCbp.v:17-18), so it is discharged there by `fun _ => I`.
   - (VIS0 / OWNED_RO are gone: ctl_rt_C_of_AR needs neither.  BLKSH is gone too (a Theorem Labs lane 13:12Z): the block-shadow
     fact is a Theorem Labs lane's PROVED A.ProgWorldShadow.ctl_block_shadow_of_AR, cited by name.)
   - The three pointwise keep helpers are KitMem.v's (a working branch 4a56e997c0f):
     A.ACtlG.KitMem.kitmem_bytes_at_mrd / kitmem_addressable_mrd / kitmem_rw_cells_mrd, cited by name.

   CLOSURE: every project Require below is qualified; no statement names a frame-route identifier.  Seg/R15.v is
   Required for its r15_RS_len (the 38 identity / 72 fragment bytes of RB).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are Reusable.YK11 (through the alias CK11, the core's module, fully
   qualified because ctrl's lib/A/Reusable/YK11 is also loaded) / Reusable.YG0d-qualified everywhere; lib/Lib's
   Mem / Step / Cells through the aliases LMem / LStep / LCells (lib/A/Bz/Lib twins are in the closure).

   BUILD STATE (route (C), type-check): rc=0 on a working branch (a working branch 1899bed1aee merged) through
   cb (BASE row 23b918fe0c2e, a build machine), no substitution; the build of record
   (cbrec) is named in the commit.  Print Assumptions glue_free_81920 = Rocq primitives only (no
   functional_extensionality: no lift here).  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* the core's twin modules by absolute name (a From-form would also match ctrl's lib/A/Reusable/<X> by suffix) *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
(* the other core Reusable modules through the core-copy prefix, so no line depends on a partial (suffix) match *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01 APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0l A.AF0m A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC A.ProgWorldShadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.CtrlBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.Seg.R15 A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's YK11 (lib/Reusable/YK11.v) and lib/Lib's Mem / Step / Cells, by their full paths: ctrl's
   lib/A/Reusable/YK11.v and lib/A/Bz/Lib/{Mem,Step,Cells}.v are also in this file's closure, so the partial names
   Reusable.YK11 and Lib.<X> are ambiguous. *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. List and address facts used once here. *)

(* A symmetric relation's pairwise holds along a permutation. *)
Lemma pairwise_perm : forall {X : Type} (Rr : X -> X -> Prop), (forall a b, Rr a b -> Rr b a) ->
  forall l l', Permutation l l' -> Reusable.YG0f.pairwise Rr l -> Reusable.YG0f.pairwise Rr l'.
Proof.
  intros X Rr Hsym l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' HP1 IH1 HP2 IH2];
    cbn [Reusable.YG0f.pairwise]; intros H.
  - exact I.
  - destruct H as [Hf Hp]. split; [|exact (IH Hp)].
    apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hf). exact (Permutation_in _ (Permutation_sym HP) Hz).
  - destruct H as [Hy [Hx Hp]]. inversion Hy as [|? ? Hyx Hyl]; subst.
    split; [constructor; [exact (Hsym _ _ Hyx) | exact Hx]|]. split; [exact Hyl | exact Hp].
  - exact (IH2 (IH1 H)).
Qed.

(* A block appended to a list it is already in would be live twice: AR's blocks are pairwise disjoint and every
   block has req_size >= 1, so the appended block is not in the list. *)
Lemma not_in_entry : forall (L E : list (Z * Z)) (x : Z * Z),
  Permutation L (E ++ [x]) ->
  Reusable.YG0f.pairwise Reusable.YG0f.zdisjoint (map (fun b => (fst b, Reusable.YG00.req_size (snd b))) L) ->
  0 <= snd x -> ~ In x E.
Proof.
  intros L E x HP Hpw Hx Hin.
  set (f := fun b : Z * Z => (fst b, Reusable.YG00.req_size (snd b))) in *.
  apply in_split in Hin as (e1 & e2 & ->).
  assert (Hsym : forall a b, Reusable.YG0f.zdisjoint a b -> Reusable.YG0f.zdisjoint b a)
    by (unfold Reusable.YG0f.zdisjoint; intros a b H; lia).
  pose proof (pairwise_perm _ Hsym _ _ (Permutation_map f HP) Hpw) as Hpw'.
  assert (Hd : Reusable.YG0f.zdisjoint (f x) (f x)).
  { apply (Reusable.YCbq.pairwise_zdisjoint_split _ (f x) (f x) Hpw').
    exists (map f e1), (map f e2), []. left.
    rewrite !map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. reflexivity. }
  pose proof (Reusable.YCbq.req_size_pos (snd x) Hx) as Hr.
  unfold Reusable.YG0f.zdisjoint in Hd. subst f. cbn [fst snd] in Hd. lia.
Qed.

(* A word read through a register that holds A' with Z_to_bv 64 A' = Z_to_bv 64 A is the address A + j. *)
Lemma wa_unsigned_congr : forall A' A j, Z_to_bv 64 A' = Z_to_bv 64 A -> 0 <= A + j < 2 ^ 64 ->
  bv_unsigned (LMem.wa (A' + j)) = A + j.
Proof.
  intros A' A j E Hr. unfold LMem.wa. rewrite Z_to_bv_unsigned.
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in *.
  rewrite Zplus_mod, E, <- Zplus_mod. apply Z.mod_small. exact Hr.
Qed.

(* The read-only span of the non-writable segments lies below the sink's overflow head (rlo = rhi = 0: no extra
   span), the instance APostBase.arodata_ok_journalP needs. *)
Lemma ro00_below : @Reusable.APostBase.ro_below_ofl segs 0 0 A.AE2k.tfib_sink_head.
Proof.
  intros a [(s & Hs & Hw & Hr) | Ha]; [|lia].
  assert (H : In (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs)).
  { exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs s Hs). }
  remember (Z.of_N (seg_base s)) as bs eqn:Eb. remember (Z.of_N (seg_size s)) as sz eqn:Ez.
  remember (seg_writable s) as w eqn:Ew. clear Eb Ez Ew Hs.
  assert (Eo : @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sk_ofl_head A.AE2k.tfib_sink_head = 0x5fbf08)
    by (vm_compute; reflexivity).
  rewrite Eo. vm_compute in H.
  repeat (destruct H as [H | H]; [injection H as <- <- <-; first [discriminate Hw | lia] |]).
  destruct H.
Qed.

Section GlueFree81920.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this lemma uses. *)
Context {fx : CK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :248), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81924_at := (ACtlCutP.C_A81924_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis AFREE4 : Reusable.YC5d.afree04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MOK_FREE : forall S, Reusable.YC5d.mo_ok MT S (Reusable.YC5d.mo_free MT).
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k
    (regsT : bvmap 5 word) (pc0 ra : Z),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  CK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  CK11.getr regsT 1 = Z_to_bv 64 ra ->
  LMem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 27) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 26) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 25) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 24) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 23) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 22) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 21) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 20) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 19) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 18) ++
     LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 9) ++ LMem.le8 (CK11.getr (ACtlCut.c_regs cx) 8) ++
     LMem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.

(* ---------------------------------------------------------------------------------------------------------
   1. C_A81924_at's body moves along a map that keeps the callee-saved registers, along memory kept on the bytes
   it reads, and to any live list that is a permutation of the entry blocks. *)

Lemma body924_regs : forall cx idx bl fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  ACtlCut.cut_body C_A81924_at cx idx bl fr fr regs m ->
  Reusable.YG0d.aregs_preserved regs regs' ->
  ACtlCut.cut_body C_A81924_at cx idx bl fr fr regs' m.
Proof.
  intros cx idx bl fr regs regs' m Hb HP.
  assert (E2 : CK11.getr regs' 2 = CK11.getr regs 2) by (apply (HP 2); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E3 : CK11.getr regs' 3 = CK11.getr regs 3) by (apply (HP 3); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E4 : CK11.getr regs' 4 = CK11.getr regs 4) by (apply (HP 4); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E8 : CK11.getr regs' 8 = CK11.getr regs 8) by (apply (HP 8); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E9 : CK11.getr regs' 9 = CK11.getr regs 9) by (apply (HP 9); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E19 : CK11.getr regs' 19 = CK11.getr regs 19) by (apply (HP 19); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E21 : CK11.getr regs' 21 = CK11.getr regs 21) by (apply (HP 21); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E22 : CK11.getr regs' 22 = CK11.getr regs 22) by (apply (HP 22); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E23 : CK11.getr regs' 23 = CK11.getr regs 23) by (apply (HP 23); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E25 : CK11.getr regs' 25 = CK11.getr regs 25) by (apply (HP 25); unfold Reusable.YG0d.acallee_saved; lia).
  assert (E26 : CK11.getr regs' 26 = CK11.getr regs 26) by (apply (HP 26); unfold Reusable.YG0d.acallee_saved; lia).
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at ACtlCutP.FRAC ACtlCutP.spill ACtlCutP.PRO
    ACtlCutP.RXS ACtlCutP.RB ACtlCutP.CUR ACtlCut.rgv Reusable.YG0d.spZ] in Hb |- *.
  rewrite E2, E3, E4, E8, E9, E19, E21, E22, E23, E25, E26. exact Hb.
Qed.

Lemma body924_bl : forall cx idx bl bl' fr (regs : bvmap 5 word) (m : word -> option byte),
  ACtlCut.cut_body C_A81924_at cx idx bl fr fr regs m ->
  Permutation bl' (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) ->
  ACtlCut.cut_body C_A81924_at cx idx bl' fr fr regs m.
Proof.
  intros cx idx bl bl' fr regs m Hb HP.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at] in Hb |- *.
  destruct Hb as (_ & Hb). exact (conj HP Hb).
Qed.

Lemma body924_mem : forall cx idx bl fr (regs : bvmap 5 word) (m m' : word -> option byte),
  ACtlCut.cut_body C_A81924_at cx idx bl fr fr regs m ->
  (forall x : word, Reusable.YG0d.spZ regs <= bv_unsigned x < ACtlCut.c_sp cx ->
     LMem.mrd A.Img0.rsegs m' x = LMem.mrd A.Img0.rsegs m x) ->
  (forall a, fr <= a < fr + 4096 ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a) /\
     m' (LMem.wa a) <> None) ->
  (forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a)) ->
  (forall i, 0 <= i < Z.of_nat (length (ACtlCut.c_in cx)) ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa (ACtlCut.c_p cx + i)) =
     LMem.mrd A.Img0.rsegs m (LMem.wa (ACtlCut.c_p cx + i))) ->
  (0 < ACtlCut.c_n cx -> A.AsanRT.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)) ->
  ACtlCut.cut_body C_A81924_at cx idx bl fr fr regs m'.
Proof.
  intros cx idx bl fr regs m m' Hb KS KF KH KI1 KI2.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at] in Hb |- *.
  destruct Hb as (Hperm & HFRAC & Hcn & Hb6 & R23 & HOUR & HOUTA & HRB & S128 & HPRO & S104 & S96 & S64 & R21 &
    S112 & S144 & S192 & HC2688 & HC2768 & S280 & S240 & HC3040 & HC3056 & S152 & HA2176 & HRXS).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & E4 & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA416 & HSsp & HSapp & HMEM).
  assert (HfrA' : fr + 3136 <= A) by exact HfrA.
  assert (HSapp' : ACtlCut.c_sp cx <= 0x800000000000) by exact HSapp.
  assert (Hsp0 : 0 <= sp) by (rewrite <- EspZ; unfold Reusable.YG0d.spZ; apply bv_unsigned_in_range).
  assert (L8 : forall w : word, length (LMem.le8 w) = 8%nat) by (intros w; reflexivity).
  (* the movers, one per kind of fact *)
  assert (MSA : forall a bs, sp <= a -> a + Z.of_nat (length bs) <= ACtlCut.c_sp cx ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' a bs H). intros i Hi. apply KS.
    rewrite LMem.wa_unsigned by lia. rewrite EspZ. lia. }
  assert (MS : forall off v, 0 <= off -> off + 8 <= 416 ->
            ACtlCutP.spill regs m off v -> ACtlCutP.spill regs m' off v).
  { intros off v Hoff0 Hoff (A' & HA' & Hq). exists A'. split; [exact HA'|].
    unfold ACtlCutP.q64 in *. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' _ _ Hq). intros i Hi. rewrite L8 in Hi.
    assert (EA : Z_to_bv 64 A' = Z_to_bv 64 A).
    { unfold ACtlCut.rgv in HA', E9. rewrite <- HA', <- E9. reflexivity. }
    replace (A' + off + i) with (A' + (off + i)) by lia. apply KS.
    rewrite (wa_unsigned_congr A' A (off + i) EA) by lia. rewrite EspZ. lia. }
  assert (MF : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' a bs H). intros i Hi.
    exact (proj1 (KF (a + i) ltac:(lia))). }
  assert (MC : forall a k junk, fr <= a -> a + Z.of_nat k <= fr + 4096 ->
            LStep.rw_cells segs m a [LCells.CB k junk] -> LStep.rw_cells segs m' a [LCells.CB k junk]).
  { intros a k junk H1 H2 H. apply (A.ACtlG.KitMem.kitmem_rw_cells_mrd m m' a _ H). intros i Hi.
    change (LCells.cells_size [LCells.CB k junk]) with (k + 0)%nat in Hi. rewrite Nat.add_0_r in Hi.
    exact (KF (a + i) ltac:(lia)). }
  assert (MA : forall p n, fr <= p -> p + n <= fr + 4096 ->
            A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n).
  { intros p n H1 H2 H. apply (A.ACtlG.KitMem.kitmem_addressable_mrd m m' p n H). intros i Hi. apply KH.
    unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. lia. }
  assert (MH : forall bs, Z.of_nat (length bs) <= 512 ->
            LMem.bytes_at segs m (ACtlCutP.Sfr fr) bs -> LMem.bytes_at segs m' (ACtlCutP.Sfr fr) bs).
  { intros bs H1 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' _ bs H). intros i Hi. apply KH. lia. }
  pose proof (A.Prog.Seg.R15.r15_RS_len (ACtlCut.c_in cx)) as HRS.
  assert (LOUR : length (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) = 6%nat)
    by (unfold A.Prog.SlotModel.OUR; rewrite length_map, length_seq; reflexivity).
  split; [exact Hperm|].
  split.
  { exists A, sp.
    do 17 (split; [assumption|]).
    (* FRAC's memory part, conjunct by conjunct and without naming them (so an appended conjunct, e.g. the
       announced fake-frame trailer word q64 m (fr + 4088) .., is carried the same way): a spill-area word, a frame
       word or the frame's shadow bytes *)
    let mem1 H :=
      first [ apply MSA; [lia | try unfold ACtlCutP.saved_bytes; rewrite ?length_app, ?L8; cbn; lia | exact H]
            | apply MF; [lia | rewrite ?L8; lia | exact H]
            | let sh := fresh "sh" in let Hs := fresh "Hs" in let Hl := fresh "Hl" in
              destruct H as (sh & Hs & Hl); exists sh; split;
              [apply MH; [rewrite Hl; unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES; cbn; lia | exact Hs]
              | exact Hl] ] in
    repeat match goal with
           | |- _ /\ _ => let H1 := fresh "HM" in destruct HMEM as [H1 HMEM]; split; [mem1 H1 |]
           end;
    mem1 HMEM. }
  split; [exact Hcn|]. split; [exact Hb6|]. split; [exact R23|].
  split; [unfold ACtlCutP.OURb in *; apply MF; [lia | rewrite LOUR; lia | exact HOUR]|].
  split; [unfold ACtlCutP.OUTA in *; apply MA; [lia | lia | exact HOUTA]|].
  split.
  { destruct HRB as (Hb6' & HCUR & HOUR' & R23' & HID & HFG).
    split; [exact Hb6'|]. split; [exact HCUR|].
    split; [unfold ACtlCutP.OURb in *; apply MF; [lia | rewrite LOUR; lia | exact HOUR']|].
    split; [exact R23'|].
    split; [unfold ACtlCutP.IDBr in *; apply MF; [lia | rewrite (proj1 (HRS _)); lia | exact HID]|].
    unfold ACtlCutP.FGBr in *; apply MF; [lia | rewrite (proj2 (HRS _)); lia | exact HFG]. }
  split; [apply MS; [lia | lia | exact S128]|].
  split.
  { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pinad &
      P184 & P256 & P264 & P272 & P32).
    split; [apply MS; [lia | lia | exact P40]|]. split; [apply MS; [lia | lia | exact P120]|].
    split; [apply MS; [lia | lia | exact P136]|]. split; [apply MS; [lia | lia | exact P160]|].
    split; [apply MS; [lia | lia | exact P168]|]. split; [apply MS; [lia | lia | exact P176]|].
    split; [apply MS; [lia | lia | exact P208]|]. split; [apply MS; [lia | lia | exact P248]|].
    split; [apply MA; [lia | lia | exact Pad]|].
    split; [exact (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' _ _ Pin KI1)|].
    split; [exact KI2|].
    split; [apply MS; [lia | lia | exact P184]|]. split; [apply MS; [lia | lia | exact P256]|].
    split; [apply MS; [lia | lia | exact P264]|]. split; [apply MS; [lia | lia | exact P272]|].
    apply MS; [lia | lia | exact P32]. }
  split; [apply MS; [lia | lia | exact S104]|]. split; [apply MS; [lia | lia | exact S96]|].
  split; [apply MS; [lia | lia | exact S64]|]. split; [exact R21|].
  split; [apply MS; [lia | lia | exact S112]|]. split; [apply MS; [lia | lia | exact S144]|].
  split; [apply MS; [lia | lia | exact S192]|].
  split; [destruct HC2688 as (idb & H); exists idb; apply MC; [lia | lia | exact H]|].
  split; [destruct HC2768 as (junk & H); exists junk; apply MC; [lia | lia | exact H]|].
  split; [apply MS; [lia | lia | exact S280]|]. split; [apply MS; [lia | lia | exact S240]|].
  split; [destruct HC3040 as (jy & H); exists jy; apply MC; [lia | lia | exact H]|].
  split; [destruct HC3056 as (junk & H); exists junk; apply MC; [lia | lia | exact H]|].
  split; [apply MS; [lia | lia | exact S152]|].
  split; [apply MA; [lia | lia | exact HA2176]|].
  destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & Xad).
  split; [apply MS; [lia | lia | exact X48]|]. split; [apply MS; [lia | lia | exact X56]|].
  split; [apply MS; [lia | lia | exact X88]|]. split; [apply MS; [lia | lia | exact X80]|].
  split; [apply MS; [lia | lia | exact X72]|]. split; [apply MS; [lia | lia | exact X8]|].
  split; [apply MS; [lia | lia | exact X0]|]. split; [apply MS; [lia | lia | exact X200]|].
  split; [apply MS; [lia | lia | exact X216]|].
  apply MA; [lia | lia | exact Xad].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The free at 0x81920. *)
Lemma glue_free_81920 : forall POST (b : nat) (cx : ACtlCut.ctlcx) (fr k : Z) ly3 S3 W3 (R : bvmap 5 word)
    (mem3 : word -> option byte) md3 (phi : Z),
  CF POST (ix_cut C_A81924_at [Z.of_nat b]) ->
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= 2 * Z.of_nat b + 1 ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3)
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.rnb cx b)]) ->
  ACtlCut.cut_body C_A81924_at cx [Z.of_nat b]
    (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) fr fr R mem3 ->
  CK11.getr R 1 = Z_to_bv 64 0x81924 -> CK11.getr R 10 = Z_to_bv 64 phi ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x53378 R mem3 md3) (POST cx).
Proof.
  intros POST b cx fr k ly3 S3 W3 R mem3 md3 phi HX HB HJ HF HL Hk HP Hbody Hra Ha0.
  set (n := ACtlCutP.rnb cx b) in *.
  set (entry := Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) in *.
  (* the entry facts *)
  pose proof HB as ((HAFN & Hraz & Hp10 & Hn11 & Hpn & Hlen & Hgarr & Hfr0 & Hnev0 & Hlive & Hro & Hsink & Hfd &
    Hfs & Hmeta & Hmo) & Hsp1).
  pose proof HAFN as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  (* the journal at the call *)
  pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & Hfrs3 & Hnev3 & Hk03 & F13 & F23 & F33 & F43 & Hgone3 &
    Hpres3 & Hstk3 & F53 & HQT3).
  pose proof Hstk3 as (Hc16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  (* the body at the call *)
  assert (Eix : ACtlCutP.ixn 0 [Z.of_nat b] = b) by (unfold ACtlCutP.ixn; cbn [nth]; apply Nat2Z.id).
  pose proof Hbody as Hb. cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at] in Hb.
  destruct Hb as (_ & HFRAC & Hcn & Hb6 & _). rewrite Eix in Hb6.
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & E4 & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA416 & HSsp & HSapp & _).
  assert (Hsaved : LMem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx)).
  { clear - HFRAC. destruct HFRAC as (A' & sp' & HFR).
    repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption. }
  assert (HfrA' : fr + 3136 <= A) by exact HfrA.
  assert (HSapp' : ACtlCut.c_sp cx <= 0x800000000000) by exact HSapp.
  (* the frame *)
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; lia).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
    as (Hf4096 & Hfceil & _).
  rewrite Efr3 in Hf4096, Hfceil. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_lt rc) as Hceil47.
  (* the freed block *)
  assert (Hphi3 : In (phi, n) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi n HAR3 Hphi3)
    as (_ & Hphi4096 & Hphiceil & Hphiapp & _ & Hpw3 & Hnr).
  assert (Hnot : ~ In (phi, n) entry) by exact (not_in_entry _ _ _ HP Hpw3 (proj1 Hnr)).
  pose proof (Reusable.YCbq.req_size_pos n (proj1 Hnr)) as Hreqn.
  (* the free's chain and call trace *)
  destruct (CHAIN_OF_CUT [] cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k R
              (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B)) 0x81924 HB HJ E8 Hra Hsaved
              ltac:(rewrite EspZ; lia) ltac:(rewrite EspZ; lia) ltac:(right; left; reflexivity)) as (ch & Hch & Htr).
  (* G9.2: the core's free rule at the call state *)
  assert (Epc : Reusable.YG0f.pc_wrap_free (Reusable.YG0f.as_code B) = 0x53378)
    by (rewrite (A.AF0m.ts_code _ TFIB_SYMS); reflexivity).
  change (Reusable.YG0d.cfg_at segs 0x53378 R mem3 md3)
    with (mkCfg (CK11.mkst R (Z_to_bv 64 0x53378) mem3 (CK11.seg_rom segs)) md3).
  rewrite <- Epc.
  refine (Reusable.YA0n.SRr_bind segs W3 _ _ (POST cx)
    (AFREE4 W3 R mem3 A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
       (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 md3 k phi n (sp - ACtlCut.c_sp cx)
       (Z_to_bv 64 0x81924) ch HJ Hphi3 Ha0
       ltac:(rewrite EspZ; lia)
       ltac:(rewrite Zminus_mod, Hsp16, Hc16; reflexivity)
       ltac:(lia)
       ltac:(unfold Reusable.YG0d.ASTACK, A.ACfn.LLVMF_STK; lia)
       ltac:(rewrite E3; exact Hgp0)
       E4 Hra
       ltac:(vm_compute; reflexivity)
       ltac:(unfold A.ACfn.EV_LIB in Hnev0; lia)
       Hch Htr
       (fun Hin => False_ind _ (Hnot Hin))
       (MOK_FREE S3)) _).
  (* G9.4: the continuation is the exit cut at ra = 0x81924 *)
  intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HPR & (l1 & l2 & El1 & El2) & Hfr2 & HK & _).
  subst c2.
  pose proof HJ2 as (HAR2 & Hly2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  assert (Efr2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; lia).
  assert (Hin62 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite Hfr2; exact Hin6).
  assert (Hperm2 : Permutation (l1 ++ l2) entry).
  { rewrite El1 in HP. pose proof (Permutation_app_inv l1 l2 entry [] (phi, n) HP) as H.
    rewrite app_nil_r in H. exact H. }
  (* memory kept across the free, on every byte the body reads *)
  assert (KS : forall x : word, Reusable.YG0d.spZ R <= bv_unsigned x < ACtlCut.c_sp cx ->
            LMem.mrd A.Img0.rsegs mem2 x = LMem.mrd A.Img0.rsegs mem3 x).
  { intros x Hx. rewrite EspZ in Hx.
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle x).
    - destruct (Hpres3 (bv_unsigned x) ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (Hh & _).
      (* the constant About names in this file's context (stdpp's; lib/Lib/MState and lib/A/Bz/Lib/MState restate it) *)
      rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hh. exact Hh.
    - left. unfold A.ACfn.LLVMF_STK in Hslo. split; [lia|]. lia. }
  assert (KF : forall a, fr <= a < fr + 4096 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a) /\
            mem2 (LMem.wa a) <> None).
  { intros a Ha.
    destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
      as (_ & _ & Hfp3 & _).
    destruct (Hfp3 a ltac:(rewrite Efr3; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia)) as ((Hh & _) & _).
    split.
    - apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle (LMem.wa a) Hh).
      rewrite LMem.wa_unsigned by lia.
      right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
      + left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      + intros HE. pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi n 6
          (ACtlCut.c_fpos cx) HAR3 Hphi3 Hin6) as Hd.
        unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efr3 in Hd.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hd. lia.
    - destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin62)
        as (_ & _ & Hfp2 & _).
      destruct (Hfp2 a ltac:(rewrite Efr2; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia))
        as ((_ & bb & Hbb) & _).
      unfold LMem.wa. rewrite Hbb. discriminate. }
  assert (KH : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a)).
  { intros a Ha. unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
    destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
      as (_ & _ & _ & Hsh3).
    destruct (Hsh3 (a - (fr / 8 + 0x7fff8000)) ltac:(change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; lia))
      as ((Hh & _) & _).
    assert (Ea : Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)) +
                   (a - (fr / 8 + 0x7fff8000)) = a).
    { rewrite Efr3. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
    rewrite Ea in Hh.
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle (LMem.wa a) Hh).
    rewrite LMem.wa_unsigned by lia.
    right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
    - right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
    - intros HE. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hphiapp.
      lia. }
  assert (KI1 : forall i, 0 <= i < Z.of_nat (length (ACtlCut.c_in cx)) ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa (ACtlCut.c_p cx + i)) =
            LMem.mrd A.Img0.rsegs mem3 (LMem.wa (ACtlCut.c_p cx + i))).
  { intros i Hi. rewrite <- Hlen in Hi.
    destruct Hpn as [(Hn0 & _) | (Hnpos & Hinp)]; [lia|].
    assert (Hinp3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinp. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hinp3)
      as (_ & Hp4096 & Hpceil & _ & Hppres & _ & Hcnr).
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) (proj1 Hcnr)) as Hreq.
    destruct (Hppres (ACtlCut.c_p cx + i) ltac:(lia)) as ((Hh & _) & _).
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle _ Hh).
    rewrite LMem.wa_unsigned by lia.
    right. left. exists (ACtlCut.c_p cx), (ACtlCut.c_n cx), i.
    split; [exact Hinp3|]. split; [lia|]. split; [reflexivity|].
    intros HE.
    assert (Hne : (ACtlCut.c_p cx, ACtlCut.c_n cx) <> (phi, n)) by (intros E; rewrite E in Hinp; exact (Hnot Hinp)).
    pose proof (Reusable.YCbq.sep_blocks segs B LAWS ly3 S3 W3 mem3 md3 _ _ _ _ HAR3 Hinp3 Hphi3 Hne) as Hd.
    unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KI2 : 0 < ACtlCut.c_n cx -> A.AsanRT.addressable mem2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
  { intros Hnpos'. destruct Hpn as [(Hn0 & _) | (Hnpos & Hinp)]; [lia|].
    assert (Hinp2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly2 S2)).
    { rewrite El2. apply (Permutation_in _ (Permutation_sym Hperm2)). exact Hinp. }
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as Hreq.
    exact (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
             (ACtlCut.c_p cx) (ACtlCut.c_n cx)
             HAR2 Hinp2 ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* the exit cut *)
  change (mkCfg (CK11.mkst regs2 (Z_to_bv 64 0x81924) mem2 (CK11.seg_rom segs)) md2)
    with (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81924_at [Z.of_nat b])) regs2 mem2 md2).
  apply (HX cx [Z.of_nat b] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2).
  - rewrite Hfr2. exact HF.
  - exact HL.
  - change (k + 1 <= 2 * Z.of_nat (ACtlCutP.ixn 0 [Z.of_nat b]) + 2). rewrite Eix. lia.
  - split; [reflexivity|].
    pose proof (body924_mem cx [Z.of_nat b] entry fr R mem3 mem2 Hbody KS KF KH KI1 KI2) as Hb1.
    pose proof (body924_regs cx [Z.of_nat b] entry fr R regs2 mem2 Hb1 HPR) as Hb2.
    refine (body924_bl cx [Z.of_nat b] entry _ fr regs2 mem2 Hb2 _).
    rewrite El2. exact Hperm2.
  - (* ctl_rt_C after the free: ctl_rt_C_of_AR at the post's AR and the kept read-only view *)
    assert (HRO0 : A.Prog.CtrlBase.arodata_okP segs 0 0 B
                     (Reusable.YG0n.aview segs (Reusable.YA0n.w_H (ACtlCut.c_W cx)) (ACtlCut.c_mem cx))).
    { intros a Ha Ho He. apply Hro; [|exact Ho | exact He].
      destruct Ha as [Ha | Ha]; [left; exact Ha | lia]. }
    pose proof (Reusable.APostBase.arodata_ok_journalP (SK := A.AE2k.tfib_sink_head) segs 0 0
                  (fun a (Ha : 0 <= a < 0) => False_ind _ (ltac:(lia) : False)) (RO := ro00_below) B
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO0) as HRO2.
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS 0 0 ly2 S2 W2 mem2 md2 HAR2 HRO2).
Qed.

End GlueFree81920.
