(* lib/A/ACtlG/F28a.v -- GLUE for stage seg_F28a of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:829).  Written by a Theorem Labs lane (block of a Theorem Labs lane 03:48Z); single writer.
   rule 24: no function proved (proves no function; kind: segment lemma).  Pattern:
   glue-pattern.md (a working note, not in this delivery), shape of lib/A/ACtlG/A5.v.

   WHAT IT PROVES
     glue_seg_F28a : forall POST (j : nat),
       CF POST (ix_cut C_A826d4_at [Z.of_nat j]) -> CF POST (ix_cut C_A8265c_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F28a.  Segment F28a (Seg/F28a.v:1-9, seg_F28a :326) is the port-slot loop of the inlined
   check_ports, 0x8265c-0x826d0: 12 turns, a5 counts down from 12; turn i does the instrumented check of the byte
   blk[8 + i] at a0 = a4 = phi + 26 + i (the shadow byte at (a0 >> 3) + s10, s10 = ASAN_K), loads the code and
   counts it into a1 / a2 / a3, keeping the first code >= 4 in a6 / a7; `bnez a5,0x8265c` at 0x826c0 closes the
   loop and `j 0x826d4` at 0x826c4 reaches the exit cut.  The loop writes no memory.

   THE RUNS (a Theorem Labs lane's re-run, lib/A/Prog/Seg/F28aF.v on the glue base, Required, not assumed): f28_turn_F
   (one turn on the model, 0x8265c -> 0x826c0, two rng premises: the byte A and its shadow byte
   Z.shiftr A 3 + ASAN_K); f28_body_F is its inner run and is used through f28_turn_F.

   THE LOOP IS COMPOSED IN THIS STAGE, NOT IN AN _F FILE (a Theorem Labs lane 04:33Z and a Theorem Labs lane 04:23Z): there is
   NO F28a loop `_F` to look for.  Seg/F28a.v:356-394 is an `assert` inside seg_F28a, not a stated run, so
   a Theorem Labs lane's re-run has only the turn; and no other stage cites that loop, the walk's own loop combinators live
   in ACtl.v, and a composed-run file would be a second place stating the turn count.  f28a_loop_evtF below is the
   source's own induction on the down-counter, in evtF form: each turn is f28_turn_F; the back edge `bnez a5` at
   0x826c0 and the exit `j 0x826d4` at 0x826c4 are stepped with lib/Lib/StepF.v.  THE TWO BRANCH INSTRUCTIONS MAKE
   NO DATA ACCESS (a conditional branch and a jump: an instruction fetch is not an access, ExecF.v:98-101), which
   is why they carry no rng premise.  THE PER-TURN RNG PREMISES ARE DISCHARGED INSIDE THE QUANTIFIER, NEVER AS A
   BLANKET FOOTPRINT OVER THE LOOP: f28a_loop_evtF takes `forall k, (k < 12)%nat -> rng RNG (A0 + k) 1` and
   `forall k, (k < 12)%nat -> rng RNG (Z.shiftr (A0 + k) 3 + ASAN_K) 1`, exactly the two one-byte regions of
   f28_turn_F at turn k, and the glue proves each of them for the given k (HV1 / HV2 below, from AR's al_blocks /
   al_shadow at the live block (phi, flen cx j)); no range covering the loop as a whole appears anywhere.

   THE PROOF (glue-pattern.md section 3)
   G1  the entry cut at index [Z.of_nat j]: ix_cut's index equation, then C_A8265c_at's body (ACtlCutP.v:2675-2686):
       FRAC (ACtlCutP.v:982-997, its last conjunct the fake-frame trailer word q64 m (fr + 4088) (flag_addr ..))
       and b7_body (ACtlCutP.v:1065-1073) with its inner conjuncts (t_rp = 0, t_unk, registers 20 / 7, PORTS,
       FIRSTb, a0 = a4 = phi + 26, a5 = 12, a1 = a2 = a3 = a6 = 0).
   G2  the loop's premises, per turn k < 12, from VISIBLE state:
       - the code byte: B7K's bytes_at (phi + 18) (t_blk ..) and F28a.v's b7_blk_length / b7_firstn1 / b7_blk_pbs
         give ov_read_bytes of phi + 26 + k = blk[8 + k] = t_pbs[8 + k];
       - addressable (phi + 26 + k) 1: HB's addressable phi (a_size flen) with 50 <= flen (B7K), addressable_sub;
       - footprint of the byte: the live block (phi, flen cx j) is in the journal's ablocks (b7_body's Permutation),
         so A.ProgWorldVisHeap.heap_vis (a Theorem Labs lane's V3, stating A.ProgWorld.heap_vis_stmt; on the glue base)
         makes the byte's range visible; rng by ProgBridge.rng_of_visible;
       - footprint of the shadow byte: A.ProgWorldVisHeap.heap_sh_vis (V4, A.ProgWorld.heap_sh_vis_stmt) makes the
         shadow word cover [sh_al8_lo a, sh_al8_hi a 1) of the byte a visible; the shadow byte Z.shiftr a 3 + ASAN_K
         = AsanRT.shadow_addr a lies in it, so ProgBridge.range_visible_sub and rng_of_visible give its rng.
   G3  the cut's configuration in the run's state form (ProgBridge.cfg_at_MS), the walk moved from regs3 to the
       run's canonical start map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the lift: f28a_loop_evtF at RNG := ProgBridge.RNG_W (w_H W3), fevt_of_evtF / tfibsegs_rsegs, YA0nR.SRr_fevt
       (the loop reads memory and writes none; fp_avoids by ProgBridge.fp_avoids_RNG_W).
   G5  the loop ends at MS R .. 0x826d4 .. mem3, R = mkR of regs3's registers except t0 t1 a0-a7; the exit cut
       C_A826d4_at (ACtlCutP.v:2786-2798) is taken at regs := R, the same cx fr k ly3 S3 W3 mem3, model md':
         journal  ajournal_exec with the empty write set (memory unchanged, model materialized);
         frames, frame law, k bound (14 + 2j + 1 on both cuts), ctl_rt_C (route C, a working branch)   unchanged;
         body     FRAC, FLSI, B7K: R agrees with regs3 on every register they read (2 3 4 8 9 18-24 26), so each is
                  the entry's fact by conversion; FRAC's trailer word q64 mem3 (fr + 4088) (flag_addr (c_ly cx) 6
                  (c_fpos cx)) reads no register and the loop writes no memory, so the exit FRAC is the entry FRAC
                  (`exact`, same cx fr sel mem3); registers 20 / 7 likewise; PORTS / FIRSTb same memory;
                  registers 12 / 11 / 13 / 17 are the loop's counts after 12 turns, n_in / n_out by RcLeaf's
                  definitions.

   SECTION HYPOTHESES (exact text below; source)
   - LAWS: the core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:210 states it, the same text).
     ajournal_exec takes it, and so do heap_vis / heap_sh_vis.  It is the ONLY Section hypothesis, so ACtl.v
     discharges seg_F28a with `glue_seg_F28a B MT XM_LIB RLO RHI LAWS`.  ACtl.v's other Section hypotheses
     (RELRO_KIND_NAME, RELRO_CAT, RELRO_FRAMES, MO_LE, KREPLY, KPARSE, ...) are not used by this stage.
   No Section hypothesis for the run: Seg/F28aF.v is Required.

   FROM THE SHARED KIT lib/A/ACtlG/Kit.v (Required qualified, never copied):
   A.ACtlG.Kit.kit_wx (the image fact SRr_fevt takes) and A.ACtlG.Kit.kit_segs_low (the one ajournal_exec takes).
   Kit.kit_frac_move is not needed: FRAC moves to the end map by conversion (R carries regs3's registers).
   FROM lib/A/ProgWorldVisHeap.v (Required qualified): heap_vis, heap_sh_vis (above).

   CLOSURE: every Require is qualified and names the directory of the one file it means (`From ..lib.Reusable
   Require YK11 ..` for the core copies, `From ..lib.A.Reusable Require YK11` for ctrl's), never the partial
   `From ..fuzz_ctrl.lib Require Reusable.X` form, which matches four copies here (lib, lib/U, lib/A, lib/B; stage
   gate a Theorem Labs lane 04:5xZ); no statement names a frame-route identifier (the local loop lemma names A.AsanRT's
   addressable / ASAN_K, the allowed v1.9 AsanRT).  Every USE of the modules that exist in several copies (YI04 YI16
   YK11 YK1b YM05 YO09, and YP09) is written lib.Reusable.<X> (core) or A.Reusable.<X> (unit), the porter's allowed
   forms (a Theorem Labs lane 04:24Z), checked with Locate.
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only lib.Reusable.YK11 / A.Reusable.YK11 / Reusable.YG0d.  The
   blob of every frame-route file in the closure is in the commit message.

   BUILD STATE: type-check on glue base 480cae342a7 (interim core), closure reaches no stand-in.  The base's
   planning-core files (AE2k, AF0m, AF0l, ACej, ACeh) carry no port_core_refused_<hex> name in code, so the build
   substitutes nothing.  Not "compiled of record".  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* Every project Require names the DIRECTORY of the one file it means (From <dir> Require <file>), never the partial
   `From ..fuzz_ctrl.lib Require Reusable.X` form: in this tree that form matches up to four copies (lib/Reusable,
   lib/U/Reusable, lib/A/Reusable, lib/B/Reusable; also lib/Lib, lib/AZ/Lib, lib/A/Bz/Lib, lib/B/Bz/Lib for
   MState / Frame / Mem).  Each line below matches exactly one file (measured with git ls-files on the base). *)
(* the core copies of the twin modules (lib/Reusable) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YP09 YM05 YO09.
(* ctrl's unit copy of YK11 (lib/A/Reusable): f28_turn_F's seg_rom *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG01 YG00 YG0n YG0d YC5d YCbq YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k Img0 AsanRT AsanRTFacts ACtlK ACtlCut.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlCutP ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF MState Regs6ss Frame Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F28a F28aF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisHeap.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:176 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   The loop in evtF form.  Seg/F28a.v:356-394 (`assert LOOP` inside seg_F28a), restated over lib/Lib's footprint
   engine: the same induction on the down-counter n (turn i = 12 - n), each turn F28aF.f28_turn_F, the back edge
   `bnez a5,0x8265c` at 0x826c0 and the exit `j 0x826d4` at 0x826c4 stepped with Lib.StepF.  Generalised over the FP
   registers F / fcsr fc (f28_turn_F is), so that the core's fx instance meets it.  The two rng premises of each turn
   are quantified over the turn index k < 12. *)

(* `bnez a5`: replace the branch condition by its value (F28a.v:221-229, f28_br / f28_zdec, over evtF goals). *)
Local Ltac f28a_br v :=
  lazymatch goal with
  | |- Lib.ExecF.evtF _ _ _ (Lib.MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v
        by (symmetry; rewrite A.Prog.Seg.F28a.b7_eqb_small by lia;
            repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end;
            cbn [negb andb orb]; first [reflexivity | exfalso; lia]);
      cbv iota
  end.

Lemma f28a_loop_evtF :
  forall (RNG : Lib.ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mem : word -> option byte)
         (bs : list byte) (A0 : Z),
    (forall k, (k < 12)%nat -> A.AsanRT.addressable mem (A0 + Z.of_nat k) 1) ->
    (forall k, (k < 12)%nat ->
       ov_read_bytes A.Img0.rsegs mem (Z_to_bv 64 (A0 + Z.of_nat k)) 1 = Some [nth (8 + k) bs (Z_to_bv 8 0)]) ->
    (forall k, (k < 12)%nat -> Lib.ExecF.rng RNG (A0 + Z.of_nat k) 1) ->
    (forall k, (k < 12)%nat -> Lib.ExecF.rng RNG (Z.shiftr (A0 + Z.of_nat k) 3 + A.AsanRT.ASAN_K) 1) ->
    forall (n i : nat)
      (x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + n = 12)%nat -> (0 < n)%nat ->
    a0 = Z_to_bv 64 (A0 + Z.of_nat i) -> a4 = Z_to_bv 64 (A0 + Z.of_nat i) -> a5 = Z_to_bv 64 (Z.of_nat n) ->
    a1 = Z_to_bv 64 (Prog.RcLeaf.cnt Prog.RcLeaf.is_out bs i) ->
    a2 = Z_to_bv 64 (Prog.RcLeaf.cnt Prog.RcLeaf.is_in bs i) ->
    a3 = Z_to_bv 64 (Prog.RcLeaf.cnt A.Prog.SlotModel.is_empty bs i) ->
    a6 = Z_to_bv 64 (Prog.RcPorts.pu_first bs i) ->
    s10 = Z_to_bv 64 A.AsanRT.ASAN_K ->
    Lib.ExecF.evtF A.Img0.rsegs RNG
      (fun ms' => exists t0' t1' a0' a4' a5' a6' : word,
         ms' = Lib.MState.MS
                 (Lib.Frame.mkR x1 x2 x3 x4 t0' t1' t2 s0 s1 a0'
                    (Z_to_bv 64 (Prog.RcLeaf.cnt Prog.RcLeaf.is_out bs 12))
                    (Z_to_bv 64 (Prog.RcLeaf.cnt Prog.RcLeaf.is_in bs 12))
                    (Z_to_bv 64 (Prog.RcLeaf.cnt A.Prog.SlotModel.is_empty bs 12))
                    a4' a5' a6' (Z_to_bv 64 (Prog.RcPorts.pu_first bs 12))
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x826d4) fc None mem (lib.Reusable.YK11.seg_rom A.Img0.rsegs))
      (Lib.MState.MS
         (Lib.Frame.mkR x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x8265c) fc None mem (lib.Reusable.YK11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG F fc mem bs A0 HAd HRb HR1 HR2 n.
  (* the two YK11 copies' seg_rom have the same body (glue-pattern.md section 6); f28_turn_F is over ctrl's *)
  change (lib.Reusable.YK11.seg_rom A.Img0.rsegs) with (A.Reusable.YK11.seg_rom A.Img0.rsegs).
  induction n as [|n IH];
    intros i x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      Hin Hpos E0 E4 E5 E1 E2 E3 E6 E26; [lia|].
  (* turn i: 0x8265c -> 0x826c0 (F28aF.f28_turn_F) *)
  eapply Lib.ExecF.evtF_cut.
  { exact (A.Prog.Seg.F28aF.f28_turn_F RNG x1 x2 x3 x4 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
             s8 s9 s10 s11 t3 t4 t5 t6 F fc mem bs i (A0 + Z.of_nat i) (Z.of_nat (S n))
             E0 E4 E5 E1 E2 E3 E6 E26 (HAd i ltac:(lia)) (HRb i ltac:(lia)) (HR1 i ltac:(lia)) (HR2 i ltac:(lia))). }
  intros ms' (t0' & t1' & ->).
  (* 0x826c0 bnez a5,0x8265c *)
  Lib.StepF.step.
  destruct n as [|n'].
  - (* last turn: fall through, 0x826c4 j 0x826d4 *)
    f28a_br false.
    Lib.StepF.step.
    assert (Ei : i = 11%nat) by lia. subst i.
    apply Lib.ExecF.evtF_done. hnf. do 6 eexists. reflexivity.
  - f28a_br true.
    eapply (IH (S i)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia
                       | reflexivity | reflexivity | reflexivity | reflexivity | exact E26].
Qed.

Section GlueF28a.

(* ACtl.v's Section shape (ACtl.v:183-188, the core classes), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:257, :261-262, :342-343), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A8265c_at := (ACtlCutP.C_A8265c_at B).
Local Notation C_A826d4_at := (ACtlCutP.C_A826d4_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:210). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F28a : forall POST (j : nat), CF POST (ix_cut C_A826d4_at [Z.of_nat j]) -> CF POST (ix_cut C_A8265c_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:234-236; C_A8265c_at, ACtlCutP.v:2675-2686). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8265c_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & HB7).
  unfold ACtlCutP.b7_body in HB7.
  destruct HB7 as (phi & HP & Hn & Hj & HHB & HFLSI & HK & HQ).
  cbv beta in HQ.
  destruct HQ as (Hrp & Hunk & R20 & R7 & HPO & HFI & R10 & R14 & R15 & R11 & R12 & R13 & R16).
  pose proof HK as (_ & _ & _ & Hphi0 & Hphi50 & Hfl50 & Hblk & _).
  pose proof HFRAC as (Af & spf & _ & _ & _ & _ & _ & _ & _ & _ & R26 & _).
  pose proof HJ as (HAR & _).
  (* G2: the loop's premises, per turn k < 12, from visible state. *)
  (* the code byte blk[8 + k] = t_pbs[8 + k] at phi + 26 + k (Seg/F28a.v:341-350, over lib/Lib's bytes_at) *)
  assert (HRb : forall k, (k < 12)%nat ->
    ov_read_bytes A.Img0.rsegs mem3 (Z_to_bv 64 (phi + 26 + Z.of_nat k)) 1 =
    Some [nth (8 + k) (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j) (Z_to_bv 8 0)]).
  { intros k' Hk'.
    pose proof (Lib.Mem.bytes_at_ov_read segs mem3 (phi + 18) (A.Prog.SlotModel.t_blk (ACtlCut.c_in cx) j)
                  (8 + k') 1 Hblk ltac:(rewrite A.Prog.Seg.F28a.b7_blk_length; lia)) as E.
    rewrite (A.Prog.Seg.F28a.b7_firstn1 _ _ (Z_to_bv 8 0)) in E
      by (rewrite A.Prog.Seg.F28a.b7_blk_length; lia).
    rewrite A.Prog.Seg.F28a.b7_blk_pbs in E by lia.
    replace (phi + 18 + Z.of_nat (8 + k')) with (phi + 26 + Z.of_nat k') in E by lia.
    exact E. }
  (* addressable (phi + 26 + k) 1, from HB(phi) with 50 <= flen (Seg/F28a.v:351-354) *)
  assert (HAd : forall k, (k < 12)%nat -> A.AsanRT.addressable mem3 (phi + 26 + Z.of_nat k) 1).
  { intros k' Hk'. destruct HHB as (_ & Haddr). unfold A.ACtlK.a_size in Haddr.
    replace (phi + 26 + Z.of_nat k') with (phi + (26 + Z.of_nat k')) by lia.
    apply (A.AsanRTFacts.addressable_sub mem3 phi (Z.max (ACtlCutP.flen cx j) 1)); [exact Haddr | lia | lia | lia]. }
  (* the live block (phi, flen cx j) is in the journal's ablocks: heap_vis / heap_sh_vis apply to it *)
  assert (Hin : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  assert (Ereq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  (* footprint of the code byte of turn k: A.ProgWorldVisHeap.heap_vis over the live block *)
  assert (HV1 : forall k, (k < 12)%nat ->
    Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (phi + 26 + Z.of_nat k) 1).
  { intros k' Hk'. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) _ _ HAR Hin);
      rewrite ?Ereq; lia. }
  (* footprint of the shadow byte of turn k: A.ProgWorldVisHeap.heap_sh_vis gives the byte's shadow word cover,
     and the shadow byte lies in it *)
  assert (HV2 : forall k, (k < 12)%nat ->
    Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
      (Z.shiftr (phi + 26 + Z.of_nat k) 3 + A.AsanRT.ASAN_K) 1).
  { intros k' Hk'.
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j)
                (phi + 26 + Z.of_nat k') 1 HAR Hin ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia))
      as [E1 | Hvis]; [lia |].
    replace (Z.shiftr (phi + 26 + Z.of_nat k') 3 + A.AsanRT.ASAN_K)
      with (A.AsanRT.shadow_addr (phi + 26 + Z.of_nat k'))
      by (unfold A.AsanRT.shadow_addr; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ Hvis);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi; rewrite ?Z.add_simpl_r;
      set (y := A.AsanRT.shadow_addr (phi + 26 + Z.of_nat k')); Z.div_mod_to_equations; lia. }
  (* G3: the cut's configuration in the run's state form, then the walk moved to mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A8265c_at [Z.of_nat j])) with 0x8265c.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x8265c) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the loop from mkR_of regs3 (turn 0, counter 12) at RNG_W (w_H W3), and the lift. *)
  eassert (HRUN : Lib.ExecF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
    (Lib.MState.MS (Lib.Regs6ss.mkR_of regs3) lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x8265c)
       lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
  { unfold Lib.Regs6ss.mkR_of.
    eapply (f28a_loop_evtF _ _ _ mem3 (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j) (phi + 26)
              HAd HRb HV1 HV2 12 0).
    - lia.
    - lia.
    - replace (phi + 26 + Z.of_nat 0) with (phi + 26) by lia. exact R10.
    - replace (phi + 26 + Z.of_nat 0) with (phi + 26) by lia. exact R14.
    - exact R15.
    - exact R11.
    - exact R12.
    - exact R13.
    - exact R16.
    - exact R26. }
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
           (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the end state MS R .. 0x826d4 .. mem3; the exit cut is taken at regs := R. *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (t0' & t1' & a0' & a4' & a5' & a6' & Ems). subst ms'.
  match goal with |- context [Lib.MState.MS ?R0 _ (Z_to_bv 64 0x826d4) _ _ _ _] => set (R := R0) end.
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A826d4_at [Z.of_nat j])) R mem3 md')
            (POST cx)).
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A826d4_at (ACtlCutP.v:2690-2702), at the same frame index j *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A826d4_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|].
    rewrite Nat2Z.id.
    (* FRAC reads registers 2 3 4 8 9 19 26, which R carries from regs3; its trailer word q64 mem3 (fr + 4088) ..
       reads no register, and mem3 is the entry's memory: the exit FRAC is the entry FRAC by conversion *)
    split; [exact HFRAC|].
    unfold ACtlCutP.b7_body. exists phi.
    split; [exact HP|]. split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    (* FLSI reads register 9, B7K registers 9 18 21 22 23 24: R carries them from regs3 *)
    split; [exact HFLSI|]. split; [exact HK|].
    cbv beta.
    split; [exact Hrp|]. split; [exact Hunk|]. split; [exact R20|]. split; [exact R7|].
    split; [exact HPO|]. split; [exact HFI|].
    split; [unfold ACtlCut.rgv, Prog.RcLeaf.n_in; reflexivity|].
    split; [unfold ACtlCut.rgv, Prog.RcLeaf.n_out; reflexivity|].
    split; [unfold ACtlCut.rgv; reflexivity|].
    unfold ACtlCut.rgv; reflexivity.
  - (* ctl_rt_C B ly3 S3 mem3 (route C, a working branch): same state, and the memory is the entry cut's *)
    exact Hrt.
Qed.

End GlueF28a.

Print Assumptions glue_seg_F28a.
