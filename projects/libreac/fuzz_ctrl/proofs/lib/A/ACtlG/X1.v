(* lib/A/ACtlG/X1.v -- GLUE for stage seg_X1 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   W5 tail).  Written by a Theorem Labs lane; single writer.  rule 24: no function proved (stage glue of a walk;
   At ossv/recipes c5e779efe8c (2026-10-31), no released proof of this unit's LLVMFuzzerTestOneInput outside this unit).

   WHAT IT PROVES
     glue_seg_X1 : forall POST, CF POST C_A82b20 -> CF POST C_Jrel -> CF POST C_A82b04
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_X1.  Entry C_A82b04 (0x82b04); exits C_A82b20 (the memchr arm) and C_Jrel (the byte-20 = 0 arm).  Segment X1 is
   Seg/X12.v seg_X1 (:849 at U):
     0x82b04 ld a1,144(s1)   0x82b08 lbu a0,20(a1)   0x82b0c beqz a0,0x82b24
   byte 20 of the identity record at fr + 2688 decides the arm:
   - = 0 (X12.v :893-920): x12_b_evt to 0x82b24, then the shadow-fill tail to C_Jrel (lib/A/ACtlG/X2.v x2_tail);
   - <> 0 (X12.v :921-1039): 0x82b10 addi a0,a1,3; 0x82b14 li a2,17; 0x82b18 mv a1,zero; 0x82b1c jal 0x42974 (the
     memchr wrapper on [fr + 2691, fr + 2708)), returning to 0x82b20 = C_A82b20.

   THE MEMCHR CALL IS A SPLIT SITE (two Theorem Labs lanes 04:01Z rule, case (b): X12F.memchr_wrap_F is proved only at
   ExecF.RNG_all, X12F.memchr_wrap_F_all).  The stretch to the call is Seg/X12Fs.v x12_a_pre_Fs (this lane's split
   file of record, a working branch f3d1972c303); at the wrapper's entry 0x42974 the walk applies the memchr
   SITE RULE AMEMCHR_SITE (plan Appendix B), whose continuation at the return address is the exit cut C_A82b20.
   WHY NOT THE CORE'S OWN RULE: the planning core's PROVED memchr0_icpt_contractM (lib/A/AE6x.v:475, in the form of
   A/AE39.v:46 amemchr0_realizesM) requires k + 8 <= n; with n = 17 it covers only a NUL index k <= 9, and ctrl's NUL
   index in the 17-byte model name is any value below 17.

   THE PROOF (glue-pattern.md G1-G5)
   G1  C_A82b04's body: Permutation, FRAC, c_n bound, OURb, the [A + 144] spill (its base is FRAC's A,
       X12.x12_eq_of_bv'), the 21-byte identity-record prefix nm with a NUL in bytes 3..19, the 17 addressable bytes.
   byte 20 = 0:  G3 ProgBridge.cfg_at_MS + YA0nR.SRr_xregs_eqv; G4 X12F.x12_b_evt_F at RNG_W (w_H W3) (it reads
       [A + 144] and fr + 2708: the journal's stack window and the frame, both visible), YA0nR.SRr_fevt; G5 X2.x2_tail
       at the run's end map (journal by ajournal_exec with the empty write set, FRAC by Kit.kit_frac_move).
   byte 20 <> 0: G3 as above; G4 X12Fs.x12_a_pre_Fs at RNG_W (w_H W3), YA0nR.SRr_fevt; then the site rule by
       YA0n.SRr_bind.  Its premises from the cut: ecall_pre (the journal's AR, the stack window, gp / tp), the
       buffer's bytes present and off the wrapper's window (AR_frames_law, the stack above alloc_ceiling), amem_range
       and shadow_hull_vis (the frame's 512 shadow bytes, AR_frames_law), range_addressable (the body's addressable,
       read through the view), mconsts_view (ctl_rt_C's ro_agree on the read-only segment [0x10000, 0x30000)).  Its
       post to C_A82b20: journal by YCbq.ajournal_after_write over the wrapper's window [sp - ESTACK, sp) (awr_byte's
       stack case); FRAC / OURb through aregs_preserved and the kept view (Lib.Frame-free: a visible byte's view is
       its mrd; Batch3's trailer word at fr + 4088 is a frame byte, off the wrapper's window, kept like the header);
       a0 = fr + 2691 + k > 0 with k < 17 (first_byte against the body's NUL); ctl_rt_C (route (C)) by a Theorem Labs lane's PROVED
       A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post's AR, its arodata_okP from ctl_base's arodata_okS kept by the
       journal (YCbq ajournal conjunct :362) and by the rule's kept view.

   SECTION HYPOTHESES
   - RELRO_IMG, LAWS: ACtl.v's own (Section Ctl), mirrored.
   - AMEMCHR_SITE: the memchr site rule at 0x42974 with c := 0, n := 17 (plan Appendix B line "memchr(p+3, 0, 17)").
     TEXT transcribed from a Theorem Labs lane's amemchr_realizesM (a working branch 3b8a77d146c,
     proofs/libreac/fuzz_disco/lib/Rt/MemchrDef.v:36-51, blob of that file at that commit) into the ctrl core's own
     words (YG0d ecall_pre / src_ok / amem_range / shadow_hull_vis / first_byte / aregs_preserved / raZ / ESTACK, YG0v
     range_addressable, YG0n aview / apresent, YK04 same_but_materialized); its consts_view segs lo hi is the text
     of the core's A.AE39.mconsts_view (AE39.v:28-29) at the ruled lo / hi = 0x10350 / 0x10370 (AE39.v:30
     mc_bounds), written with those literals: A/AE39.v Requires A/AE3a.v, which does not build on the planning core
     (AE3a.v:48), so X1 does not Require it.  The literals are ctrl A's: in fuzz_ctrl.asan musl memchr (0x97b10)
     loads ONES from 0x10368 (0x97b68 auipc a3,0xfff79; 0x97b6c ld a3,-0x800(a3)) and HIGHS from 0x10350
     (0x97b70 auipc a4,0xfff78; 0x97b74 ld a4,0x7e0(a4)), and the image holds 0x8080808080808080 at 0x10350 and
     0x0101010101010100 at 0x10368 (capstone + ELF read of the unstripped binary).  OWNER a Theorem Labs lane (proved on
     disco, both images); ROUTE: cite it directly once a Theorem Labs lane relocates it into fuzz_ctrl's lib/Reusable.
   - TFIB_SYMS: A.AF0m.CtrlTSyms B, ACtl.v's own hypothesis (Section Ctl, ACtl.v:193 at the glue base), same text
     and the same place in the order; it is ctl_rt_C_of_AR's first premise.
   - route (C): the entry cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ACtlCut.ctl_from on a working branch shell).  Its
     shadow conjuncts are not read here (the site rule's premises read the frame's shadow through AR_frames_law);
     its ro_agree feeds mconsts_view; the byte-20 = 0 arm hands it to X2.x2_tail unchanged.  The exit C_A82b20's
     ctl_rt_C comes from a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR (lib/A/ProgWorldCtlRtC.v), which needs
     neither A.ProgWorld.AR_states_vis0_shadow nor A.ProgWorld.AR_states_owned_ro: the Section hypotheses VIS0 /
     OWNED_RO and the local ctlrt_of_AR notation are GONE.

   CLOSURE: as X2.v (full-path module aliases for every Reusable / Lib module, the six-module rule); gains
   Seg/X12Fs.v (Seg/X12F.v's closure), Reusable/APostBase.v (core), A/ProgWorld.v with A/AF0m.v, and A/ShadowRwOn.v,
   A/ACtlRtC.v, A/ProgWorldCtlRtC.v (a Theorem Labs lane's proof of ctl_rt_C_of_AR) with their closure.  Measured per build with
   closure_scan.py (sha256
   039e7d56edc3...); the file count and the stand-ins reached are in the lane report of each build.  No bare
   `Z_to_bv_bv_unsigned` in this file.

   DISCHARGE CALL in ACtl.v (the Section order of glue_seg_X1 on the route (C) walk shell; XN_LIB is not used and
   is not an argument):
     exact (glue_seg_X1 B MT XM_LIB RLO RHI RELRO_IMG LAWS TFIB_SYMS AMEMCHR_SITE)
   (fx / rc / LS stay implicit, resolved by ACtl.v's own Context instances.)

   BUILD STATE: see the commit message and the lane report (type-check; the label, the closure scan and
   `Print Assumptions glue_seg_X1` come with each build).  No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* reg_get (the explicit register binders of the _F runs are Regs6ss.mkR_of's fields), as YK11.v:11 imports it *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACfn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12Fs.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.X2.
Import ListNotations.
Local Open Scope Z_scope.

Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module RK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RE01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Module RAPB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module SMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SFN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module SX12 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12.
Module X12F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12F.
Module X12Fs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.X12Fs.
Module JX2 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.X2.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Proof-internal facts (no Section argument). *)

(* At a visible address the core's view is ctrl's mrd. *)
Lemma x1_aview_vis : forall (W : RA0n.world segs) (m : word -> option byte) (a : Z),
  RA0n.w_H W (Z_to_bv 64 a) = false ->
  RG0n.aview segs (RA0n.w_H W) m a = option_map (fun b : byte => bv_unsigned b) (LMM.mrd A.Img0.rsegs m (LMM.wa a)).
Proof.
  intros W m a Hv. unfold RG0n.aview, RP09.mbyte, RK04.mrestrict, LMM.mrd, LMM.wa. rewrite Hv. reflexivity.
Qed.

(* A byte list read from memory is read the same from a memory whose view agrees on its (visible) range. *)
Lemma x1_ba_view : forall (W : RA0n.world segs) (m m' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> RA0n.w_H W (Z_to_bv 64 x) = false /\
     RG0n.aview segs (RA0n.w_H W) m' x = RG0n.aview segs (RA0n.w_H W) m x) ->
  LMM.bytes_at A.Img0.rsegs m a bs -> LMM.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros W m m' a bs Hk (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H i Hi) as Hm.
  destruct (Hk (a + Z.of_nat i) ltac:(lia)) as (Hv & Heq).
  rewrite (x1_aview_vis W m' _ Hv), (x1_aview_vis W m _ Hv), Hm in Heq.
  destruct (nth_error bs i) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
  destruct (LMM.mrd A.Img0.rsegs m' (LMM.wa (a + Z.of_nat i))) as [b'|] eqn:E'; cbn [option_map] in Heq;
    [|discriminate Heq].
  injection Heq as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* A shadow value ctrl reads as non-negative signed is its unsigned value. *)
Lemma x1_unsigned_of_signed : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  destruct (Z_lt_ge_dec (bv_unsigned b) 128) as [Hl|Hg].
  - symmetry. unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia.
  - exfalso. unfold bv_signed, bv_swrap, bv_wrap in H. change (bv_half_modulus 8) with 128 in H.
    change (bv_modulus 8) with 256 in H, R. Z.div_mod_to_equations. lia.
Qed.

(* Every byte of [0x10000, 0x30000) is a read-only image byte (the image's first PT_LOAD, not writable). *)
Lemma x1_ro_first : forall x : word, 0x10000 <= bv_unsigned x < 0x30000 -> LMM.ro_addr A.Img0.rsegs x = true.
Proof.
  intros x Hx.
  assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s))
                            A.Img0.rsegs) 0 = Some (65536, 131072, false)) by (vm_compute; reflexivity).
  unfold LMM.ro_addr. destruct A.Img0.rsegs as [|s1 rest]; [discriminate|].
  cbn [map nth_error] in P. injection P as P1 P2 P3.
  cbn [find_segment]. rewrite P1, P2.
  match goal with |- context [if ?c then _ else _] =>
    replace c with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia) end.
  cbv beta iota. rewrite P3. reflexivity.
Qed.

Section GlueX1.

(* ACtl.v's Section Ctl shape (84ef756918c), in its order: the core class by full path, the same Variables and
   Hypotheses, except TFIB_LIB, which no glue step here reads; then this stage's named hypotheses.  TFIB_SYMS IS
   carried: it is the first premise of A.ProgWorldCtlRtC.ctl_rt_C_of_AR, and A.ProgWorld Requires A.AF0m itself,
   so the stand-in A/AF0m.v is in this file's closure either way.
   End GlueX1 keeps only what glue_seg_X1 uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : RG0f.asyms.
Variable MT : RC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* ACtl.v's RELRO_IMG: the read-only span [RLO, RHI) is image bytes. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> RG0d.in_img segs a.
(* The core's AR laws (YCbq.v Section a0's hypothesis; ACtl.v's LAWS). *)
Hypothesis LAWS : RG0d.AR_laws segs B.
(* ACtl.v's own TFIB_SYMS (Section Ctl, ACtl.v:193), ctl_rt_C_of_AR's first premise; same text, same place in the
   order. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* The memchr site rule at ctrl A's wrapper entry 0x42974, c := 0, n := 17: a Theorem Labs lane's amemchr_realizesM
   (a working branch 3b8a77d146c, fuzz_disco's lib/Rt/MemchrDef.v:36-51) in the ctrl core's words; consts_view = the text of
   the core's A.AE39.mconsts_view at [MC_LO, MC_HI) = [0x10350, 0x10370).  Owner a Theorem Labs lane; see the header. *)
Hypothesis AMEMCHR_SITE : forall ly S (W : RA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte) md x,
  RG0d.ecall_pre segs B ly S W regs mem md ->
  RK11.getr regs 10 = RG0d.w64 x -> RK11.getr regs 11 = RG0d.w64 0 -> RK11.getr regs 12 = RG0d.w64 17 ->
  0 <= 0 < 256 -> 0 <= 17 < 2 ^ 32 -> 0 < x -> x + 17 <= 2 ^ 63 ->
  RG0d.src_ok segs W regs mem x 17 -> RG0d.amem_range x 17 ->
  RG0v.range_addressable (RG0n.aview segs (RA0n.w_H W) mem) RG0f.SHADOW_OFF x 17 ->
  (0 < 17 -> RG0d.shadow_hull_vis (RG0n.aview segs (RA0n.w_H W) mem) x 17) ->
  (forall a, 0x10350 <= a < 0x10370 ->
     RG0n.aview segs (RA0n.w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (RK11.seg_rom segs (Z_to_bv 64 a))) ->
  RA0n.SRr segs W (RG0d.cfg_at segs 0x42974 regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = RG0d.cfg_at segs (RG0d.raZ regs) regs' mem' md' /\
       RG0n.AR segs B ly S W mem' md' /\ RG0d.aregs_preserved regs regs' /\ RK04.same_but_materialized md md' /\
       (exists k, RG0d.first_byte segs W mem x 17 0 k /\
                  RK11.getr regs' 10 = (if k <? 17 then RG0d.w64 (x + k) else RG0d.w64 0)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (RG0d.spZ regs - RG0d.ESTACK <= a < RG0d.spZ regs) ->
          RG0n.aview segs (RA0n.w_H W) mem' a = RG0n.aview segs (RA0n.w_H W) mem a) /\
       (forall a, RG0n.apresent (RA0n.w_H W) mem a -> RG0n.apresent (RA0n.w_H W) mem' a)).

(* route (C): VIS0 / OWNED_RO (A.ProgWorld.AR_states_vis0_shadow / AR_states_owned_ro) and the local ctlrt_of_AR
   notation are GONE: the exit's ctl_rt_C comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which needs neither. *)

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82b04 := (ACtlCutP.C_A82b04 B).
Local Notation C_A82b20 := (ACtlCutP.C_A82b20 B).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).

Lemma glue_seg_X1 : forall POST, CF POST C_A82b20 -> CF POST C_Jrel -> CF POST C_A82b04.
Proof.
  intros POST HX20 HXJ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A82b04 (ACtlCutP.v C_A82b04) *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82b04] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & Hour & Hsp144 & (nm & Hnm & Hnml & Hfb) & Hadr).
  pose proof HFRAC as (A & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsplo & Hcapp & Q304 & Q24 & Q16 & Qhdr & Qret & Hsh & Hsaved & Htrl).
  pose proof Hrt as (Hcells & Hcut & Himg & Hro).
  (* the journal: AR, layout, the image conjunct, the stack window, astk_ok *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & HF3 & _ & _ & Hpres & Hastk & _ & HQT).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  destruct Hastk as (_ & _ & Hc1 & Hc2 & Hc3 & _).
  destruct (@RG0f.ASAN_CEIL_range rc) as ((Hcl & Hch) & _). unfold RG0f.ASAN_CEIL in Hcl, Hch.
  unfold A.ACfn.LLVMF_STK in Hc2, Hpres.
  (* the frame and its 512 shadow bytes *)
  assert (Hin : In (6, ACtlCut.c_fpos cx) (RG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = RG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (EF3 : RG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold RG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Hfsb : RG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hfl : RG0d.AR_frames_law segs B) by (destruct LAWS; assumption).
  destruct (Hfl ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & Happ & Hby & Hshb).
  destruct (RCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & Hceilf & _).
  rewrite EF3, Hfsb in Happ, Hby, Hshb, Hceilf. change (4096 / 8) with 512 in Hshb.
  assert (ESh : RG0f.shadow_addr fr = ACtlCutP.Sfr fr).
  { unfold RG0f.shadow_addr, RG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K. lia. }
  rewrite ESh in Hshb.
  unfold RG0f.in_app, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Happ.
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in Hcapp.
  assert (HShv : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  pose proof (Z.div_mod fr 8 ltac:(lia)) as Dfr. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as Mfr.
  (* the frame bytes: visible and present *)
  assert (Hfv : forall a, fr <= a < fr + 4096 -> RA0n.w_H W3 (Z_to_bv 64 a) = false) by
    (intros a Ha; exact (proj1 (proj1 (Hby a Ha)))).
  (* the spill [A' + 144]: A' is FRAC's A *)
  destruct Hsp144 as (A1 & R9b & H144).
  unfold ACtlCut.rgv in R9, R9b.
  assert (EA1 : A1 = A).
  { apply (SX12.x12_eq_of_bv' A A1); [rewrite <- R9b; exact R9 |].
    unfold ACtlCutP.q64, LMM.bytes_at in H144. destruct H144 as (H1 & H2 & _). rewrite LMM.length_le8 in H2. lia. }
  subst A1.
  (* byte 20 of the identity record *)
  assert (HL1 : length (firstn 1 (skipn 20 nm)) = 1%nat) by (rewrite firstn_length, skipn_length; lia).
  pose proof (SX12.x12_ba_sub mem3 (fr + 2688) nm 20 1 Hnm ltac:(lia)) as H20.
  destruct (firstn 1 (skipn 20 nm)) as [|b20 tl] eqn:E20; [cbn [length] in HL1; lia|].
  destruct tl as [|b21 tl2]; [|cbn [length] in HL1; lia].
  replace (fr + 2688 + Z.of_nat 20) with (fr + 2708) in H20 by lia.
  (* the footprint ranges both runs read: [A + 144, A + 152) (stack window), fr + 2708 (frame) *)
  assert (Hv144 : PB.range_visible (RA0n.w_H W3) (A + 144) 8).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  assert (Hv20 : PB.range_visible (RA0n.w_H W3) (fr + 2708) 1).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (Hfv a ltac:(lia)). }
  (* G3: the cut's configuration, the walk moved to the run's canonical map *)
  rewrite PB.cfg_at_MS.
  change (ACtlCut.cut_pc C_A82b04) with 0x82b04.
  apply (RA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 RK11.fp_regs
           (Z_to_bv 64 0x82b04) RK11.fp_csr None mem3 (RK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  destruct (Z.eq_dec (bv_unsigned b20) 0) as [Hb0|Hbnz].
  - (* ---- byte 20 = 0: x12_b_evt to 0x82b24, then the shadow-fill tail to C_Jrel ---- *)
    pose proof (X12F.x12_b_evt_F (PB.RNG_W (RA0n.w_H W3))
      (reg_get regs3 1) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6) (reg_get regs3 7)
      (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
      (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
      (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
      (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
      (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
      (reg_get regs3 2) RK11.fp_regs RK11.fp_csr mem3 A fr b20
      R9 H144 H20 Hb0 (PB.rng_of_visible _ _ _ Hv144) (PB.rng_of_visible _ _ _ Hv20)) as HRUN.
    pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- PB.tfibsegs_rsegs in HFS.
    apply (RA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (RA0n.w_H W3)) _ (POST cx) HFS).
    { apply PB.fp_avoids_RNG_W. }
    intros ms' md' HQ0 Hsbm.
    subst ms'.
    match goal with |- RA0n.SRr _ _ (mkCfg (LMS.MS ?R0 _ _ _ _ _ _) _) _ => set (R := R0) end.
    change (RA0n.SRr segs W3 (RG0d.cfg_at segs 0x82b24 R mem3 md') (POST cx)).
    assert (K2 : RK11.getr R 2 = RK11.getr regs3 2) by reflexivity.
    assert (K3 : RK11.getr R 3 = RK11.getr regs3 3) by reflexivity.
    assert (K4 : RK11.getr R 4 = RK11.getr regs3 4) by reflexivity.
    assert (K8 : RK11.getr R 8 = RK11.getr regs3 8) by reflexivity.
    assert (K9 : RK11.getr R 9 = RK11.getr regs3 9) by reflexivity.
    assert (K19 : RK11.getr R 19 = RK11.getr regs3 19) by reflexivity.
    assert (K26 : RK11.getr R 26 = RK11.getr regs3 26) by reflexivity.
    apply (JX2.x2_tail B MT XM_LIB RLO RHI LAWS POST HXJ cx fr k ly3 S3 W3 R mem3 md' HB).
    + (* journal: no byte written, the model materialized *)
      eapply (RCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply RK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + exact HP.
    + exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26).
    + exact Hrt.
  - (* ---- byte 20 <> 0: the stretch to the memchr wrapper's entry, then the site rule, to C_A82b20 ---- *)
    pose proof (X12Fs.x12_a_pre_Fs (PB.RNG_W (RA0n.w_H W3))
      (reg_get regs3 1) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6) (reg_get regs3 7)
      (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
      (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
      (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
      (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
      (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
      (reg_get regs3 2) RK11.fp_regs RK11.fp_csr mem3 A fr b20
      R9 H144 H20 Hbnz (PB.rng_of_visible _ _ _ Hv144) (PB.rng_of_visible _ _ _ Hv20)) as HRUN.
    pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- PB.tfibsegs_rsegs in HFS.
    apply (RA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (RA0n.w_H W3)) _ (POST cx) HFS).
    { apply PB.fp_avoids_RNG_W. }
    intros ms' md' HQ0 Hsbm.
    subst ms'.
    match goal with |- RA0n.SRr _ _ (mkCfg (LMS.MS ?R0 _ _ _ _ _ _) _) _ => set (R := R0) end.
    change (RA0n.SRr segs W3 (RG0d.cfg_at segs 0x42974 R mem3 md') (POST cx)).
    assert (K1 : RK11.getr R 1 = Z_to_bv 64 0x82b20) by reflexivity.
    assert (K2 : RK11.getr R 2 = RK11.getr regs3 2) by reflexivity.
    assert (K3 : RK11.getr R 3 = RK11.getr regs3 3) by reflexivity.
    assert (K4 : RK11.getr R 4 = RK11.getr regs3 4) by reflexivity.
    assert (K8 : RK11.getr R 8 = RK11.getr regs3 8) by reflexivity.
    assert (K9 : RK11.getr R 9 = RK11.getr regs3 9) by reflexivity.
    assert (K19 : RK11.getr R 19 = RK11.getr regs3 19) by reflexivity.
    assert (K26 : RK11.getr R 26 = RK11.getr regs3 26) by reflexivity.
    assert (K10 : RK11.getr R 10 = RG0d.w64 (fr + 2691)) by reflexivity.
    assert (K11 : RK11.getr R 11 = RG0d.w64 0) by reflexivity.
    assert (K12 : RK11.getr R 12 = RG0d.w64 17) by reflexivity.
    assert (HspR : RG0d.spZ R = sp) by (unfold RG0d.spZ in *; rewrite K2; exact Hspz).
    (* the journal at the call: no byte written by the stretch, the model materialized *)
    assert (HJ1 : RCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
        (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
        (ACtlCut.cut_own C_A82b04 cx) ly3 S3 W3 mem3 md' k).
    { eapply (RCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply RK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha]. }
    pose proof HJ1 as (HAR1 & _).
    (* the entry's gp *)
    assert (Hgp : RK11.getr regs3 3 = RG0d.w64 (RG0f.as_gp B)).
    { pose proof HB as ((HAFN & _) & _). destruct HAFN as (_ & _ & _ & Hgp0 & _). rewrite R3. exact Hgp0. }
    (* the buffer [fr + 2691, fr + 2708) and its shadow *)
    assert (Hsdisj : forall a, fr <= a < fr + 4096 -> ~ (sp - RG0d.ESTACK <= a < sp)).
    { intros a Ha. unfold RG0d.ESTACK. lia. }
    eapply RA0n.SRr_bind.
    { apply (AMEMCHR_SITE ly3 S3 W3 R mem3 md' (fr + 2691)).
      - (* ecall_pre *)
        unfold RG0d.ecall_pre. rewrite HspR.
        split; [exact HAR1|].
        split; [rewrite K1; hnf; apply bv_eq; vm_compute; reflexivity|].
        split; [exact Hsp16|].
        split; [unfold RG0d.ESTACK; rewrite Elo; lia|].
        split; [rewrite Ehi; lia|].
        split; [intros a Ha; unfold RG0d.ESTACK in Ha; exact (Hpres a ltac:(lia))|].
        split; [rewrite K3; exact Hgp | rewrite K4; exact R4].
      - exact K10.
      - exact K11.
      - exact K12.
      - lia.
      - lia.
      - lia.
      - lia.
      - (* src_ok: present visible bytes of the frame, off the wrapper's window *)
        intros a Ha. rewrite HspR. split; [|apply Hsdisj; lia].
        rewrite (x1_aview_vis W3 mem3 a (Hfv a ltac:(lia))).
        destruct (proj2 (proj1 (Hby a ltac:(lia)))) as (b & Eb).
        unfold LMM.mrd, LMM.wa. rewrite Eb. discriminate.
      - (* amem_range: the frame is app memory *)
        unfold RG0d.amem_range, RG0f.kLowMemEnd, RG0f.kHighMemBeg, RG0f.kHighMemEnd. lia.
      - (* range_addressable: the body's addressable, read through the view *)
        intros x Hx.
        destruct Hadr as (_ & _ & _ & Hadr).
        destruct (Hadr (x - (fr + 2691)) ltac:(lia)) as (_ & b & Hb & Hok).
        replace (fr + 2691 + (x - (fr + 2691))) with x in Hb, Hok by lia.
        exists (bv_unsigned b).
        assert (Es : RG0v.shadow_of_addr RG0f.SHADOW_OFF x = ART.shadow_addr x).
        { unfold RG0v.shadow_of_addr, RG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K. lia. }
        rewrite Es.
        assert (Hsv : RA0n.w_H W3 (Z_to_bv 64 (ART.shadow_addr x)) = false).
        { pose proof (proj1 (proj1 (Hshb (ART.shadow_addr x - ACtlCutP.Sfr fr) ltac:(
            unfold ART.shadow_addr, ART.ASAN_K; rewrite HShv; Z.div_mod_to_equations; lia)))) as Hv.
          replace (ACtlCutP.Sfr fr + (ART.shadow_addr x - ACtlCutP.Sfr fr)) with (ART.shadow_addr x) in Hv by lia.
          exact Hv. }
        rewrite (x1_aview_vis W3 mem3 _ Hsv), Hb. split; [reflexivity|].
        unfold ART.shadow_ok in Hok. unfold RG0v.saddr_ok.
        destruct Hok as [H0 | (H1 & H2)].
        + left. rewrite x1_unsigned_of_signed by lia. exact H0.
        + right. rewrite x1_unsigned_of_signed by (pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia). lia.
      - (* shadow_hull_vis: the hull lies in the frame's 512 shadow bytes *)
        intros _ s Hs.
        assert (Hs' : ACtlCutP.Sfr fr <= s < ACtlCutP.Sfr fr + 512).
        { unfold RG0f.shadow_addr, RG0f.SHADOW_OFF in Hs. rewrite HShv. Z.div_mod_to_equations. lia. }
        destruct (proj1 (Hshb (s - ACtlCutP.Sfr fr) ltac:(lia))) as (Hv & b & Eb).
        replace (ACtlCutP.Sfr fr + (s - ACtlCutP.Sfr fr)) with s in Hv, Eb by lia.
        rewrite (x1_aview_vis W3 mem3 s Hv). unfold LMM.mrd, LMM.wa. rewrite Eb. discriminate.
      - (* mconsts_view: ctl_rt_C's ro_agree on the read-only first segment *)
        intros a Ha.
        assert (Hva : RA0n.w_H W3 (Z_to_bv 64 a) = false).
        { destruct (PB.img_vis_W W3) as (_ & _ & Hiv). apply Hiv.
          unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_LO,
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.IMG_HI. lia. }
        rewrite (x1_aview_vis W3 mem3 a Hva).
        assert (Hroa : LMM.ro_addr A.Img0.rsegs (LMM.wa a) = true).
        { apply x1_ro_first. rewrite LMM.wa_unsigned by lia. lia. }
        rewrite (Hro (LMM.wa a) Hroa). reflexivity. }
    (* the site rule's post, at the return address 0x82b20 = C_A82b20 *)
    intros W' c' _ (EW & regs' & mem' & md'' & Ec & HAR' & Hpreg & Hsbm' & (kk & Hfb' & Ha0) & Hview & Hpres').
    subst W' c'.
    replace (RG0d.raZ R) with 0x82b20 by (unfold RG0d.raZ; rewrite K1; reflexivity).
    change (RA0n.SRr segs W3 (RG0d.cfg_at segs (ACtlCut.cut_pc C_A82b20) regs' mem' md'') (POST cx)).
    (* the callee-saved registers *)
    assert (Hcs : forall r : Z, RG0d.acallee_saved r -> RK11.getr regs' (Z_to_bv 5 r) = RK11.getr R (Z_to_bv 5 r))
      by exact Hpreg.
    assert (P2 : RK11.getr regs' 2 = RK11.getr regs3 2).
    { rewrite <- K2. exact (Hcs 2 ltac:(unfold RG0d.acallee_saved; lia)). }
    assert (P3 : RK11.getr regs' 3 = RK11.getr regs3 3).
    { rewrite <- K3. exact (Hcs 3 ltac:(unfold RG0d.acallee_saved; lia)). }
    assert (P4 : RK11.getr regs' 4 = RK11.getr regs3 4).
    { rewrite <- K4. exact (Hcs 4 ltac:(unfold RG0d.acallee_saved; lia)). }
    assert (P8 : RK11.getr regs' 8 = RK11.getr regs3 8).
    { rewrite <- K8. exact (Hcs 8 ltac:(unfold RG0d.acallee_saved; lia)). }
    assert (P9 : RK11.getr regs' 9 = RK11.getr regs3 9).
    { rewrite <- K9. exact (Hcs 9 ltac:(unfold RG0d.acallee_saved; lia)). }
    assert (P19 : RK11.getr regs' 19 = RK11.getr regs3 19).
    { rewrite <- K19. exact (Hcs 19 ltac:(unfold RG0d.acallee_saved; lia)). }
    assert (P26 : RK11.getr regs' 26 = RK11.getr regs3 26).
    { rewrite <- K26. exact (Hcs 26 ltac:(unfold RG0d.acallee_saved; lia)). }
    (* the view outside the wrapper's window [sp - 4096, sp) *)
    rewrite HspR in Hview. unfold RG0d.ESTACK in Hview.
    assert (Hkeep : forall a bs, LMM.bytes_at A.Img0.rsegs mem3 a bs ->
        (forall x, a <= x < a + Z.of_nat (length bs) -> RA0n.w_H W3 (Z_to_bv 64 x) = false /\ 0 <= x < 2 ^ 64 /\
                   ~ (sp - 4096 <= x < sp)) ->
        LMM.bytes_at A.Img0.rsegs mem' a bs).
    { intros a bs Hba Hx. apply (x1_ba_view W3 mem3 mem' a bs); [|exact Hba].
      intros x Hxr. destruct (Hx x Hxr) as (Hv & Hr & Hw). split; [exact Hv | exact (Hview x Hr Hw)]. }
    assert (Hstkv : forall x, sp <= x < ACtlCut.c_sp cx -> RA0n.w_H W3 (Z_to_bv 64 x) = false /\ 0 <= x < 2 ^ 64 /\
                              ~ (sp - 4096 <= x < sp)).
    { intros x Hx. split; [exact (proj1 (Hpres x ltac:(lia))) | lia]. }
    assert (Hfrv : forall x, fr <= x < fr + 4096 -> RA0n.w_H W3 (Z_to_bv 64 x) = false /\ 0 <= x < 2 ^ 64 /\
                             ~ (sp - 4096 <= x < sp)).
    { intros x Hx. split; [exact (Hfv x Hx) | lia]. }
    apply (HX20 cx [] fr k ly3 S3 W3 regs' mem' md'' HB).
    + (* journal: ajournal_after_write over the wrapper's window *)
      eapply (RCbq.ajournal_after_write segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun a => sp - 4096 <= a < sp) (S' := S3);
        [exact HJ1 | intros a Ha Hw; exact (Hview a Ha Hw) | exact Hpres' | exact Hsbm'
        | intros a Ha; left; left; unfold A.ACfn.LLVMF_STK; lia | exact HAR' | reflexivity | reflexivity | lia
        | exact Hfrs | exact HQT].
    + exact HF.
    + exact HL.
    + exact Hk.
    + (* the exit body, C_A82b20 (ACtlCutP.v C_A82b20) *)
      cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A82b20].
      split; [exact HP|].
      split.
      { exists A, sp.
        split; [rewrite P2; exact R2|]. split; [exact Hsp16|].
        split; [unfold RG0d.spZ in *; rewrite P2; exact Hspz|].
        split; [rewrite P4; exact R4|].
        split; [unfold ACtlCut.rgv in *; rewrite P8; exact R8|].
        split; [unfold ACtlCut.rgv; rewrite P9; exact R9|].
        split; [rewrite P3; exact R3|].
        split; [unfold ACtlCut.rgv in *; rewrite P19; exact R19|].
        split; [unfold ACtlCut.rgv in *; rewrite P26; exact R26|].
        split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAc|]. split; [exact HspA|].
        split; [unfold ACtlCutP.FRAME_BYTES; exact HfrA|]. split; [exact HA416|]. split; [exact Hsplo|].
        split; [unfold ART.APPMEM_END; exact Hcapp|].
        split; [apply (Hkeep _ _ Q304); rewrite LMM.length_le8; intros x Hx; apply Hstkv; lia|].
        split; [apply (Hkeep _ _ Q24); rewrite LMM.length_le8; intros x Hx; apply Hstkv; lia|].
        split; [apply (Hkeep _ _ Q16); rewrite LMM.length_le8; intros x Hx; apply Hstkv; lia|].
        split; [apply (Hkeep _ _ Qhdr); rewrite LMM.length_le8; intros x Hx; apply Hfrv; lia|].
        split; [apply (Hkeep _ _ Qret); rewrite LMM.length_le8; intros x Hx; apply Hfrv; lia|].
        split.
        { destruct Hsh as (sh & Hsh1 & Hsh2). exists sh. split; [|exact Hsh2].
          apply (Hkeep _ _ Hsh1). rewrite Hsh2. change (Z.of_nat (Z.to_nat ACtlCutP.FRAME_SHADOW)) with 392.
          intros x Hx.
          destruct (proj1 (Hshb (x - ACtlCutP.Sfr fr) ltac:(lia))) as (Hv & _).
          replace (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) with x in Hv by lia.
          split; [exact Hv | lia]. }
        split; [apply (Hkeep _ _ Hsaved); rewrite JX2.JR.jr_saved_len; intros x Hx; apply Hstkv; lia|].
        (* Batch3's fake-frame trailer word at fr + 4088: a frame byte, off the wrapper's window. *)
        apply (Hkeep _ _ Htrl). rewrite LMM.length_le8. intros x Hx. apply Hfrv. lia. }
      split; [exact Hn|].
      split.
      { unfold ACtlCutP.OURb in *. apply (Hkeep _ _ Hour). rewrite SMO.OUR_length. intros x Hx. apply Hfrv. lia. }
      (* a0 = fr + 2691 + k, the NUL of the model name found (k < 17 by the body's NUL) *)
      assert (Hk17 : kk < 17).
      { destruct Hfb' as (Hk0 & Hne & _).
        destruct (Z_lt_ge_dec kk 17) as [Hlt|Hge]; [exact Hlt|exfalso].
        destruct (SFN.find_byte 0 (firstn 17 (skipn 3 nm))) as [j|] eqn:EFB; [|exact (Hfb eq_refl)].
        destruct (SFN.find_byte_Some 0 _ j EFB) as (Hjl & (bj & Ebj & Hbj) & _).
        rewrite firstn_length, skipn_length, Hnml in Hjl. cbn in Hjl.
        destruct (Hne (Z.of_nat j) ltac:(lia)) as (v & Hv & Hvne).
        pose proof (SX12.x12_ba_sub mem3 (fr + 2688) nm 3 17 Hnm ltac:(lia)) as Hbuf.
        destruct Hbuf as (_ & _ & Hbuf).
        pose proof (Hbuf j ltac:(rewrite firstn_length, skipn_length; lia)) as Hbj'.
        rewrite Ebj in Hbj'.
        replace (fr + 2688 + Z.of_nat 3 + Z.of_nat j) with (fr + 2691 + Z.of_nat j) in Hbj' by lia.
        rewrite (x1_aview_vis W3 mem3 (fr + 2691 + Z.of_nat j) (Hfv (fr + 2691 + Z.of_nat j) ltac:(lia))), Hbj' in Hv.
        cbn [option_map] in Hv. injection Hv as Hv. lia. }
      pose proof Hfb' as (Hkk0 & _).
      exists (fr + 2691 + kk). split; [|lia].
      unfold ACtlCut.a0v, ACtlCut.rgv. rewrite Ha0.
      replace (kk <? 17) with true by (symmetry; apply Z.ltb_lt; exact Hk17). reflexivity.
    + (* ctl_rt_C at the post memory: a Theorem Labs lane's PROVED ctl_rt_C_of_AR at the post's AR (route (C)) *)
      apply (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem' md'' HAR').
      (* arodata_okP of the post view: ctl_base's arodata_okS, kept by the journal and by the rule's view *)
      pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _) & _).
      intros a Hroa Hown Herr.
      assert (Hia : RG0d.in_img segs a).
      { destruct Hroa as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)]. }
      pose proof (A.ACtlG.Kit.kit_segs_low a Hia) as Hlow. unfold RG0f.kLowMemEnd in Hlow.
      rewrite (Hview a ltac:(lia) ltac:(lia)).
      rewrite (HF3 a Hia Hown Herr).
      * exact (Haro a Hroa Hown Herr).
      * (* fp_spares [] a: the empty footprint opens no sink *)
        intros (r & Hr & _). destruct Hr.
Qed.

End GlueX1.
