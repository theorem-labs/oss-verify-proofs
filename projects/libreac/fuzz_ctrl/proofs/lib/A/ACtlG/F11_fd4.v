(* lib/A/ACtlG/F11_fd4.v -- GLUE for stage seg_F11_fd4 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:774, piece W4b).  Written by a Theorem Labs lane; single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery); the worked example lib/A/ACtlG/A5.v.
   rule 24: no function proved (kind: segment lemma of a walk).

   WHAT IT PROVES
     glue_seg_F11_fd4 : forall POST (j : nat),
       CF POST (ix_cut C_A820ac_at [Z.of_nat j]) -> CF POST (ix_cut C_A8206c_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F11_fd4 (ACtl.v:774; glue comment ACtl.v:773: Seg/F11.v seg_F11_fd4 :1355 via _F, runs f11_loop :273,
   f11_fd4_evt :357).  Segment 0x8206c -> 0x820ac is the record-sum loop over the n0 = ir_s - 8 bytes
   [phi+34, phi+34+n0) of the 50-byte record block phi, then the mod-128 test 0x820a4-0x820a8 (not taken).

   THE RUN (one, PROVED): lib/A/Prog/Seg/F11F.v f11_fd4_evt_F (:221-263), Required qualified, no Section
   hypothesis.  F11F.v is a Theorem Labs lane's, taken by path from a working branch bf0fe242de5 (blob
   2a9b50649ca, branch commit e1170215d9a); the earlier text (commit 5dbd293c250) did not compile here
   (F11F.v:419 applied the RNG-first ingest contract with RNG last); f11_fd4_evt_F's statement is the same in
   both.  The run READS the record block [phi, phi+50) and its byte-exact shadow span, and WRITES NO MEMORY (its
   post carries the start memory m).  It has no call, so it is lifted whole (split rule 04:01Z: nothing split).

   THE PROOF (glue-pattern.md section 3)
   G1  unfold the entry cut C_A8206c_at (ACtlCutP.v:2166-2181): FRAC and b5_body with its 16 P conjuncts.
   G2  the run's premises, all from the entry cut and the journal:
         0 <= phi, phi + 50 <= 2^64, addressable m phi 50   from HB (phi, a_size (flen cx j)) and 50 <= flen cx j
                                                            (a_size n = Z.max n 1; APPMEM_END = 2^47);
         length g = 50, psum (skipn 34 g) n0 mod 128 = 0   Seg/F11.v f11_tg_len / f11_sum128, from ir (flen cx j) g
                                                            = true, the second half of the body's reply_ok;
         1 <= n0 <= 15                                      RcReply.ir_bytes (14 <= ir_s g <= 23);
         bytes_at segs m phi g                              b5_C's b5_PH under 50 <= flen cx j;
         rng (RNG_W (w_H W3)) phi 50                        A.ACtlG.KitMem.kitmem_rng_heap (= the PROVED
                                                            A.ProgWorldVisHeap.heap_vis) of the live block
                                                            (phi, flen cx j): In it by the body's Permutation, AR from
                                                            the journal, req_size (flen cx j) = flen cx j;
         rng .. (shadow_addr phi) (.. (phi+49) - .. + 1)    A.ACtlG.KitMem.kitmem_rng_heap_sh_span (heap_sh_vis's
                                                            8-aligned shadow word cover, narrowed to the byte-exact span).
       No bound is left open: every one comes from visible state (HB and the journal's AR).
   G3  the run starts at an EXPLICIT mkR map.  Its 26 kept-register binders are instantiated with the cut map's own
       values `Reusable.YK11.getr regs3 r`; the five pinned slots are the body's rgv facts (a0 = a5 = phi+34,
       a1 = n0, a4 = 0) and FRAC's s10 = ASAN_K.  The walk is moved from the cut's map regs3 to that map by
       Reusable.YA0nR.SRr_xregs_eqv, with Lib.Regs6ss.mkR_eqv_of (31 slot equations) for the equivalence.
   G4  lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, then YA0nR.SRr_fevt (a read-only run may use the
       plain lift) at RNG := ProgBridge.RNG_W (w_H W3), fp_avoids by ProgBridge.fp_avoids_RNG_W.
   G5  the exit cut C_A820ac_at (ACtlCutP.v:2185-2199) at the run's end map R:
         journal  ajournal_exec with the empty write set (memory unchanged, model materialized), as A5.v;
         frames, frame law, k bound   unchanged (own6 and kmax 14 + 2j + 1 on both cuts);
         body     FRAC by kit_frac_move (slot 26 of R is the literal ASAN_K, so FRAC needs the move); EVERY other
                  conjunct by plain `exact`: R holds `getr regs3 r` on every register the body reads (2 9 18 20-25
                  and 12 13), so getr R r computes to getr regs3 r and each ACtlCutP conjunct at R is CONVERTIBLE to
                  the entry's; rgv R 11 0 by reflexivity (slot 11 of R is 0).  No register-move lemma is used, so
                  the ACtlCutP / SlotInv transcription differences (a Theorem Labs lane 04:4xZ) do not arise here;
         ctl_rt_C unchanged (route (C)'s ctl_rt_C B ly3 S3 mem3 of a working branch shell: same ly3 S3, same memory).

   SECTION HYPOTHESES
   - LAWS: the core's AR law record (YCbq.v:207), as A5.v; ajournal_exec and the two KitMem heap rows take it.
   No other Section hypothesis.
   FROM THE SHARED KITS (Required qualified, never copied): A.ACtlG.Kit.kit_wx (SRr_fevt's image premise),
   A.ACtlG.Kit.kit_segs_low (ajournal_exec's), A.ACtlG.Kit.kit_frac_move (FRAC to the end map);
   A.ACtlG.KitMem.kitmem_rng_heap / kitmem_rng_heap_sh_span (the two footprint ranges).
   CITED BY NAME, PROVED on the base: A.Prog.Seg.F11F.f11_fd4_evt_F; A.Prog.Seg.F11.f11_tg_len / f11_sum128;
   Prog.RcReply.ir_bytes; A.ProgBridge.fevt_of_evtF / tfibsegs_rsegs / cfg_at_MS / RNG_W / fp_avoids_RNG_W;
   Reusable.YA0nR.SRr_xregs_eqv / SRr_fevt; Lib.Regs6ss.mkR_eqv_of / xregs_eqv_sym; Reusable.YCbq.ajournal_exec.

   NAMES.  Six core modules exist twice (lib/Reusable/<X> and lib/A/Reusable/<X>: YI04 YI16 YK11 YK1b YM05 YO09),
   and F11F's closure loads the lib/A copies and lib/A/Bz/Lib, so the twins are loaded by ABSOLUTE Require lines
   (as Kit.v (at head lib/A/ACtlG/Kit.v:53-59) / A5.v (at head lib/A/ACtlG/A5.v:93-96); the glue base from a working branch 46eb24cd4b3) and every project name here is written through a
   module alias of its FULL path (Module X := OSSVerify.Proofs.libreac.fuzz_ctrl.lib....), never a partial
   path; Lib.MState.MS likewise (a Theorem Labs lane's measurement).  getr / seg_rom / cfg_at appear only as XK11.* / XG0d.*
   (the check of glue-pattern.md section 2 (a working note, not in this delivery) hits only comments).

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z / porter 23:38Z): every Require is qualified (no Import / Export of a
   project module); no statement names a frame-route identifier.  The _F file Seg/F11F.v and its closure (which
   holds Seg/F11.v, SlotInv, AsanRTInv, Contract, FrameAPI, MemNorm) are allowed by rule 1.

   STAND-IN VALUES (a Theorem Labs lane 05:52Z): none read.  No ts_zsh / Tfib_* / am_const / AB01 / port_core_refused value; the
   only shadow read is the heap block's, through AR's shadow law (KitMem's heap rows).  FRAC is read by position from
   the front (destruct ends in `& _`) and carried by Kit.kit_frac_move at the SAME memory; no lemma here
   re-establishes FRAC / FRAHC at a new memory.

   ROUTE (C) BUILD STATE: type-check rc=0 on a working branch shell 1899bed1aee (cb build, a build machine, log
   (internal path), build 2026-10-29T13:05:56Z); build of record: a Theorem Labs lane's cbrec record
   over lib/A/ACtlG/L3W4bAudit.v (not in this delivery).  The paragraph below is the pre-route-(C) state.
   BUILD STATE (TYPE-CHECK ONLY on the glue branch's planning core; values do not count): wb4b.sh on VM
   a build machine at branch head c5d58e80468, rc=0: (internal path)
   build-20261029T072954Z.log compiled F11F.vo and F11_fd4.vo, build-20261029T073141Z.log the final proof text.
   No AD2l stand-in was needed (the closure does not reach lib/A/AD2l.v).  Print
   Assumptions glue_seg_F11_fd4 (below End): the Rocq primitive-type axioms and functional_extensionality_dep only.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YG00 Reusable.YG0f Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACtlK AsanRT ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F11 F11F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* Full-path aliases (see NAMES in the header). *)
Module XK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module XK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module XK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module XM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module XO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module XG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module XG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module XG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module XC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module XA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module XA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module XCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module XAB1v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Module XAE2k := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Module XACtlK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Module XART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module XCut := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Module XCutP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Module XPB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module XSM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module XF11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F11.
Module XF11F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F11F.
Module XRRP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.
Module XMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module XR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := XAB1v.tfibsegs.

Section GlueF11fd4.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : XK11.FPState} {rc : XM05.RunCeil} {LS : XO09.lib_shape}.
Variable B : XG0f.asyms.
Variable MT : XC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :277-278), with each name written through its alias. *)
Local Notation ix_cut := XCut.ix_cut.
Local Notation CF POST X :=
  (XCut.ctl_from (SK := XAE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8206c_at := (XCutP.C_A8206c_at B).
Local Notation C_A820ac_at := (XCutP.C_A820ac_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis): ACtl.v's Section hypothesis LAWS, in ACtl.v's own text
   (route (C) L3: a stage hypothesis has ACtl.v's name and text; Reusable.YG0d has no lib/A twin, so the partial path
   names the module XG0d aliases). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F11_fd4 : forall POST (j : nat), CF POST (ix_cut C_A820ac_at [Z.of_nat j]) -> CF POST (ix_cut C_A8206c_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] (ix_cut, ACtlCut.v:232-234; C_A8206c_at, ACtlCutP.v:2166-2181). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [XCut.cut_body XCutP.C_A8206c_at XCutP.ixn nth XCutP.b5_body] in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hcn & Hj255 & HHB & HFLSI & HLK & HC & HK & HRC & H50 & Hsum & Hok &
    HRP & R10 & R11 & R12 & R13 & R14 & R15 & HIDj & H17 & H240 & HPF).
  set (jj := Z.to_nat (Z.of_nat j)) in *.
  (* G2: the run's premises. *)
  pose proof HJ as (HAR & _).
  pose proof HFRAC as (Asp & sp & _ & _ & _ & _ & _ & _ & _ & _ & F26 & _).
  (* the record: 50 bytes, its n0 = ir_s - 8 bytes from offset 34 sum to 0 mod 128 (ir, from reply_ok) *)
  pose proof Hok as Hok'. unfold XRRP.reply_ok in Hok'. apply andb_prop in Hok'. destruct Hok' as [_ Hir].
  destruct (XRRP.ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _).
  pose proof (XF11.f11_tg_len (XCut.c_in cx) jj) as HGl.
  pose proof (XF11.f11_sum128 _ _ HGl Hir) as H128.
  assert (Hn0 : 1 <= XRRP.ir_s (XSM.t_g (XCut.c_in cx) jj) - 8 <= 15) by lia.
  (* the block's bounds and its first 50 bytes addressable (HB, with 50 <= flen cx j) *)
  pose proof HHB as (_ & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & Hab).
  assert (Hsz : XACtlK.a_size (XCutP.flen cx jj) = XCutP.flen cx jj) by (unfold XACtlK.a_size; lia).
  rewrite Hsz in Hpe, Hab.
  unfold XART.APPMEM_END in Hpe.
  assert (Hphi50 : phi + 50 <= 2 ^ 64) by lia.
  assert (Haddr50 : XART.addressable mem3 phi 50).
  { unfold XART.addressable. split; [lia|]. split; [lia|]. split; [unfold XART.APPMEM_END; lia|].
    intros i Hi. apply Hab. lia. }
  (* the record bytes (b5_C's b5_PH) *)
  pose proof HC as (_ & _ & _ & (HPHg & _) & _).
  pose proof (HPHg H50) as HG.
  (* the two footprint ranges, by the shared kit's heap rows (KitMem.v:661-690, built on the PROVED
     A.ProgWorldVisHeap.heap_vis / heap_sh_vis): the live block (phi, flen cx j) and the byte-exact shadow span of
     its first 50 bytes *)
  assert (Hin : In (phi, XCutP.flen cx jj) (XG0d.ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|]. apply in_or_app. right. left. reflexivity. }
  assert (Ereq : XG00.req_size (XCutP.flen cx jj) = XCutP.flen cx jj)
    by (unfold XG00.req_size; destruct (Z.eqb_spec (XCutP.flen cx jj) 0); lia).
  pose proof (A.ACtlG.KitMem.kitmem_rng_heap B LAWS ly3 S3 W3 mem3 md3 phi (XCutP.flen cx jj) phi 50 HAR Hin
                ltac:(lia) ltac:(rewrite Ereq; lia)) as RBUF.
  pose proof (A.ACtlG.KitMem.kitmem_rng_heap_sh_span B LAWS ly3 S3 W3 mem3 md3 phi (XCutP.flen cx jj) phi 50
                HAR Hin ltac:(lia) ltac:(lia) ltac:(rewrite Ereq; lia)) as RSHA.
  replace (phi + 50 - 1) with (phi + 49) in RSHA by ring.
  (* G4 (run): f11_fd4_evt_F at RNG_W, its kept registers the cut map's own values *)
  pose proof (XF11F.f11_fd4_evt_F (XPB.RNG_W (XA0n.w_H W3))
    (XK11.getr regs3 1) (XK11.getr regs3 2) (XK11.getr regs3 3) (XK11.getr regs3 4) (XK11.getr regs3 5)
    (XK11.getr regs3 6) (XK11.getr regs3 7) (XK11.getr regs3 8) (XK11.getr regs3 9) (XK11.getr regs3 12)
    (XK11.getr regs3 13) (XK11.getr regs3 18) (XK11.getr regs3 19) (XK11.getr regs3 20) (XK11.getr regs3 21)
    (XK11.getr regs3 22) (XK11.getr regs3 23) (XK11.getr regs3 24) (XK11.getr regs3 25) (XK11.getr regs3 27)
    (XK11.getr regs3 28) (XK11.getr regs3 29) (XK11.getr regs3 30) (XK11.getr regs3 31)
    (XK11.getr regs3 16) (XK11.getr regs3 17)
    XK11.fp_regs XK11.fp_csr mem3 phi _ _ Hp0 Hphi50 HGl Hn0 H128 HG Haddr50 RBUF RSHA) as HRUN.
  pose proof (XPB.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- XPB.tfibsegs_rsegs in HFS.
  (* G3: the cut's configuration in the run's state form, then the walk moved from regs3 to the run's map *)
  rewrite XPB.cfg_at_MS.
  change (XCut.cut_pc (ix_cut C_A8206c_at [Z.of_nat j])) with 0x8206c.
  eapply (XA0nR.SRr_xregs_eqv segs W3 _ regs3 XK11.fp_regs (Z_to_bv 64 0x8206c) XK11.fp_csr None mem3
            (XK11.seg_rom segs) md3 (POST cx)).
  - (* G4 (lift): a read-only run, plain SRr_fevt at RNG_W *)
    apply (XA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (XPB.RNG_W (XA0n.w_H W3)) _ (POST cx) HFS).
    + exact (XPB.fp_avoids_RNG_W (XA0n.w_H W3)).
    + (* G5: the end state MS R .. 0x820ac .. mem3, R the run's own end map *)
      intros ms' md' HQ0 Hsbm.
      destruct HQ0 as (a0' & a4' & a5' & a6' & a7' & Ems). subst ms'.
      match goal with |- context [XMS.MS ?R _ _ _ _ _ _] => set (Rx := R) end.
      change (XA0n.SRr segs W3 (XG0d.cfg_at segs (XCut.cut_pc (ix_cut C_A820ac_at [Z.of_nat j])) Rx mem3 md')
                (POST cx)).
      assert (K2 : XK11.getr Rx 2 = XK11.getr regs3 2) by reflexivity.
      assert (K3 : XK11.getr Rx 3 = XK11.getr regs3 3) by reflexivity.
      assert (K4 : XK11.getr Rx 4 = XK11.getr regs3 4) by reflexivity.
      assert (K8 : XK11.getr Rx 8 = XK11.getr regs3 8) by reflexivity.
      assert (K9 : XK11.getr Rx 9 = XK11.getr regs3 9) by reflexivity.
      assert (K19 : XK11.getr Rx 19 = XK11.getr regs3 19) by reflexivity.
      assert (K26 : XK11.getr Rx 26 = XK11.getr regs3 26).
      { transitivity (Z_to_bv 64 XART.ASAN_K); [reflexivity | symmetry; exact F26]. }
      apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 Rx mem3 md' Hbase).
      * (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643), as A5.v *)
        eapply (XCbq.ajournal_exec (SK := XAE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
          with (Wr := fun _ : Z => False);
          [exact HJ | intros x _; reflexivity | apply XK1b.mem_grows_refl | intros x _; reflexivity
          | exact Hsbm | intros a Ha; destruct Ha].
      * (* frames: own6 on both cuts *)
        exact HF.
      * (* the frame law: own6 on both cuts *)
        exact HL.
      * (* the event bound: kmax 14 + 2j + 1 on both cuts *)
        exact Hk.
      * (* the exit body, C_A820ac_at (ACtlCutP.v:2185-2199), at the same j and phi *)
        cbv beta iota zeta delta [XCut.cut_body XCut.ix_cut XCutP.C_A820ac_at XCutP.ixn nth XCutP.b5_body].
        split; [reflexivity|].
        split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 Rx mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
        exists phi.
        split; [exact Hperm|]. split; [exact Hcn|]. split; [exact Hj255|]. split; [exact HHB|].
        (* the register-reading conjuncts: convertible at Rx (getr Rx r computes to getr regs3 r) *)
        split; [exact HFLSI|]. split; [exact HLK|]. split; [exact HC|]. split; [exact HK|].
        split; [exact HRC|]. split; [exact H50|]. split; [exact Hsum|]. split; [exact Hok|].
        split; [exact HRP|].
        split; [unfold XCut.rgv; reflexivity|].
        split; [exact R12|]. split; [exact R13|]. split; [exact HIDj|].
        split; [exact H17|]. split; [exact H240|]. exact HPF.
      * (* ctl_rt_C: the entry cut's ly3 S3 and memory *)
        exact Hrt.
  - (* the run's start map is the cut map up to x0: 26 kept slots, a0 / a1 / a4 / a5 from the body, s10 from FRAC *)
    exact (XR6.xregs_eqv_sym _ _ (XR6.mkR_eqv_of regs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl R10 R11 eq_refl eq_refl R14 R15
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl F26
      eq_refl eq_refl eq_refl eq_refl eq_refl)).
Qed.

End GlueF11fd4.

Print Assumptions glue_seg_F11_fd4.
