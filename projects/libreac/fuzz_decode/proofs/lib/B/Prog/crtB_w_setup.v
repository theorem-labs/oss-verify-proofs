(* crtB_w_setup: the SETUP piece of the cgif-form walk of check_round_trip, image B: CRT_RET_CALLOC (+0x94) to
   CRT_LOOP_IN (+0x10c) — the three NULL checks (none taken: the allocator rules give 4096 <= P, Q, R), the store
   of R to 8(sp), the `blez nch` (not taken: 2 <= nch), the loop constants and `fmv.w.x fa5,a1`.  It is one
   footprint run (lib/B/Prog/crtB_segs.v crt_seg4_F) carried into SRr by crtB_walk's crtB_run, with the inner
   journal re-established across the run by lib/Reusable/YCbq.v:636 ajournal_exec.
   It proves crtB_setup_stmt of lib/B/Prog/crtB_cuts.v: crtB_rules -> crtB_at_loopin -> crtB_at_calloc. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YK1b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg crtB_iface crtB_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_glue crtB_walk crtB_segs crtB_cells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require FloatExact.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK2 := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.

Section Setup.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation sink := dec_B_sink_head.
Local Notation segs := decodesegsB0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Local Notation GR r k := (YKK.getr r (Z_to_bv 5 k)).

Theorem crtB_setup : @crtB_setup_stmt fx rc B MT RO_RD.
Proof.
  unfold crtB_setup_stmt. intros RULES LOOPIN.
  unfold crtB_at_calloc.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
    ly1 S1 W1 mem1 md1 regs1 P Q R v0 v8 v32 HPRE HMID HREGS H10 H20 HFRAME HBLK HFRM.
  pose proof RULES as (_ & _ & _ & LAWS & MLAWS & _).
  pose proof HPRE as HPRE2.
  destruct HPRE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnch & Hns & Hkb & _).
  pose proof HMID as HMID2. destruct HMID2 as (HJ1 & HFR1 & HMO1 & HROM1).
  pose proof HBLK as HBLK2. destruct HBLK2 as (HPERM & HP0 & HQ0 & HR0).
  pose proof HREGS as HREGS2. destruct HREGS2 as (E2 & E3 & E4 & E18 & E21 & E24).
  pose proof HJ1 as HJ1c.
  destruct HJ1c as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES1 & HSTK1 & _ & _).
  pose proof HSTK1 as (Hsp16 & HstkK & Hceil & Hlo & Hhi & H47 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as (Hcm & _).
  (* the stack window of the inner journal, in numbers *)
  assert (HSP0 : 0 <= spZ regs - CRT_FRAME)
    by (unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  assert (HSP1 : spZ regs <= 2 ^ 47) by lia.
  assert (HSPW : forall a, spZ regs - DEC_CRT_STK <= a < spZ regs -> apresent (w_H W1) mem1 a) by exact HPRES1.
  assert (HFWIN : forall a, spZ regs - CRT_FRAME <= a < spZ regs -> apresent (w_H W1) mem1 a)
    by (intros a Ha; apply HSPW; unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
  assert (ESP : bv_unsigned (GR regs1 2) = spZ regs - CRT_FRAME).
  { replace (GR regs1 2) with (w64 (spZ regs - CRT_FRAME)) by (symmetry; exact E2).
    apply unsigned_lit. unfold CRT_FRAME in *. lia. }
  (* the three blocks: alignment and bounds, from AR's block law *)
  assert (HinP : In (P, 4 * (nch * ns)) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. right. right. left. reflexivity. }
  assert (HinQ : In (Q, 8 * nch) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. right. left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 HinP) as (HP16 & HP4096 & HPtop & _ & _ & _ & HPn).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 HinQ) as (HQ16 & HQ4096 & HQtop & _ & _ & _ & HQn).
  pose proof (req_size_pos (4 * (nch * ns)) ltac:(nia)) as HPrq.
  pose proof (req_size_pos (8 * nch) ltac:(nia)) as HQrq.
  assert (HPr : 0 < P < 2 ^ 64) by lia.
  assert (HQr : 0 < Q < 2 ^ 64) by lia.
  assert (HPm4 : P mod 4 = 0) by (Z.div_mod_to_equations; lia).
  assert (HQm8 : Q mod 8 = 0) by (Z.div_mod_to_equations; lia).
  (* R's range: the calloc's block is live too *)
  assert (HinR : In (R, 3 * (nch * ns)) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM|]. left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 HinR) as (_ & HR4096 & HRtop & _ & _ & _ & HRn).
  pose proof (req_size_pos (3 * (nch * ns)) ltac:(nia)) as HRrq.
  assert (HRr : 0 < R < 2 ^ 64) by lia.
  (* pcm lies in a caller block *)
  assert (HPCM : 0 <= pcm < 2 ^ 64).
  { pose proof HPRE as HP3.
    destruct HP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HbP & HbP1 & HbP2 & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1
      (Permutation_in _ (Permutation_sym HPERM) (in_cons _ _ _ (in_cons _ _ _ (in_cons _ _ _ HbP))))) as
      (_ & Hb1 & Hb2 & _ & _ & _ & Hbn).
    pose proof (req_size_pos nP ltac:(lia)) as Hbrq.
    lia. }
  (* the footprint run of seg4 *)
  pose proof (crt_seg4_F (LCK2.RNG_W (world segs) (@w_H segs) W1)
      (GR regs1 1) (GR regs1 2) (GR regs1 3) (GR regs1 4) (GR regs1 5) (GR regs1 6) (GR regs1 7)
      (GR regs1 8) (GR regs1 9) (GR regs1 10) (GR regs1 11) (GR regs1 12) (GR regs1 13) (GR regs1 14)
      (GR regs1 15) (GR regs1 16) (GR regs1 17) (GR regs1 18) (GR regs1 19) (GR regs1 20) (GR regs1 21)
      (GR regs1 22) (GR regs1 23) (GR regs1 24) (GR regs1 25) (GR regs1 26) (GR regs1 27) (GR regs1 28)
      (GR regs1 29) (GR regs1 30) (GR regs1 31)
      (@fp_regs fx) (@fp_csr fx) mem1
      v0 v8 (w64 (3 * (nch * ns))) (w64 audio) v32
      (GR regs 27) (GR regs 26) (GR regs 25) (GR regs 24) (GR regs 23) (GR regs 22) (GR regs 21) (GR regs 20)
      (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)
      P Q R pcm nch ns
      H10 E21 H20 E18 HPr HQr HRr HPCM HPm4 HQm8 Hnch Hns
      ltac:(rewrite ESP; exact HFRAME)
      ltac:(rewrite ESP; apply (crtB_rng_of_apresent W1 mem1 (spZ regs - CRT_FRAME) 160);
            [exact HSP0 | unfold CRT_FRAME in *; lia | intros a Ha; apply HFWIN; unfold CRT_FRAME in *; lia]))
    as HRUN.
  apply (crtB_run W1 regs1 mem1 md1 CRT_RET_CALLOC _ _ (crtB_evtF_grows _ _ _ HRUN)).
  intros ms' md' (ms0 & HPs & HEQ) HSBM.
  destruct HPs as (HPs0 & HGROW).
  destruct HPs0 as (F' & m' & wt0 & wt1 & wt2 & ws0 & wa0' & wa1' & wa3 & wa4 & wa6 & wa7 & ws9 & ws11 &
    wt3 & wt4 & wt5 & wt6 & w32 & Ems & HFR' & HMU & HWM & HUNB & HOTH &
    Bt0 & Bt1 & Bt2 & Bs0 & Ba3 & Ba4 & Ba6 & Ba7 & Bs9 & Bs11 & Bt3 & Bt4 & Bt5 & Bt6 & B32).
  subst ms0. cbn [ms_mem] in HGROW.
  pose proof (crtB_eqv_mkst _ _ _ _ _ _ _ HEQ) as Ems'.
  pose proof (fun (r : bv 5) (Hr : is_x0 r = false) =>
    crtB_ms_reg _ _ _ _ _ _ _ _ r HEQ Hr) as GEQ.
  (* the frame window is visible, so a hidden byte lies outside it *)
  assert (HHIDOUT : forall x : word, w_H W1 x = true -> ~ (spZ regs - CRT_FRAME <= bv_unsigned x < spZ regs)).
  { intros x Hx Hr. pose proof (HFWIN (bv_unsigned x) Hr) as (Hh & _).
    rewrite Z_to_bv_bv_unsigned in Hh. rewrite Hh in Hx. discriminate. }
  assert (HOUT : forall x : word, ~ (spZ regs - CRT_FRAME <= bv_unsigned x < spZ regs) -> m' x = mem1 x).
  { intros x Hx. apply HMU. cbn [outside]. rewrite ESP.
    split; [intros Hc; apply Hx; unfold CRT_FRAME in *; lia | exact I]. }
  (* the inner journal across the run *)
  assert (HJ2 : @ajournal rc sink segs B DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m' md' 3).
  { assert (HFR2 : forall x : word, ~ (spZ regs - CRT_FRAME <= bv_unsigned x < spZ regs) ->
      mrestrict (w_H W1) m' x = mrestrict (w_H W1) mem1 x)
      by (intros x Hx; unfold mrestrict; destruct (w_H W1 x); [reflexivity | exact (HOUT x Hx)]).
    assert (HGR2 : YK1b.mem_grows (mrestrict (w_H W1) mem1) (mrestrict (w_H W1) m'))
      by (apply crtB_mem_grows_restrict; exact HGROW).
    assert (HHID : forall x : word, w_H W1 x = true -> m' x = mem1 x)
      by (intros x Hx; apply HOUT; exact (HHIDOUT x Hx)).
    assert (HWB : forall a, (spZ regs - CRT_FRAME <= a < spZ regs) ->
      awr_byte DEC_CRT_STK (spZ regs) [] (ablocks B lyc Sc) (ablocks B ly1 S1) ly1 [] a)
      by (intros a Ha; unfold awr_byte; left;
          unfold CRT_FRAME, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia).
    eapply ajournal_exec with (Wr := fun a => spZ regs - CRT_FRAME <= a < spZ regs);
      solve [ exact LAWS | exact crtB_segs_low | exact HJ1 | exact HFR2 | exact HGR2 | exact HHID
            | exact HSBM | exact HWB ]. }
  (* rom_view on RO_RD is kept: the image is below the stack window *)
  assert (HROM2 : crtB_rom_on RO_RD W1 m').
  { intros a Hin Hrom. 
    assert (Him : in_img segs a) by (destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (crtB_segs_low a Him) as Hlow.
    assert (Hvis : w_H W1 (wa a) = false).
    { destruct (w_H W1 (wa a)) eqn:Ev; [exfalso|reflexivity].
      pose proof (w_Hoff W1 _ Ev) as Hfs.
      rewrite (wa_unsigned a ltac:(unfold kLowMemEnd in *; lia)) in Hfs.
      destruct Him as (sg & Hsg & Hr).
      exact (crt_find_none segs a 1 sg Hfs Hsg ltac:(lia) ltac:(lia)). }
    rewrite <- (HROM1 a Hin Hrom).
    rewrite (crtB_aview_mrd (w_H W1) m' a Hvis), (crtB_aview_mrd (w_H W1) mem1 a Hvis).
    unfold mrd. rewrite (HOUT (wa a) ltac:(rewrite (wa_unsigned a ltac:(unfold kLowMemEnd in *; lia));
      unfold CRT_FRAME, kLowMemEnd in *; lia)). reflexivity. }
  (* the register words at CRT_LOOP_IN, as w64 of their values *)
  assert (K5 : wt0 = w64 0) by (apply bv_eq; rewrite Bt0; symmetry; apply unsigned_lit; lia).
  assert (K6 : wt1 = w64 (4 * ns)) by (apply bv_eq; rewrite Bt1; symmetry; apply unsigned_lit; lia).
  assert (K7 : wt2 = w64 1) by (apply bv_eq; rewrite Bt2; symmetry; apply unsigned_lit; lia).
  assert (K16 : wa6 = w64 (2 ^ 64 - 1 - pcm)) by (apply bv_eq; rewrite Ba6; symmetry; apply unsigned_lit; lia).
  assert (K17 : wa7 = w64 0) by (apply bv_eq; rewrite Ba7; symmetry; apply unsigned_lit; lia).
  assert (K28 : wt3 = w64 CRT_T3)
    by (apply bv_eq; rewrite Bt3; symmetry; apply unsigned_lit; unfold CRT_T3; lia).
  assert (K29 : wt4 = w64 (3 * ns)) by (apply bv_eq; rewrite Bt4; symmetry; apply unsigned_lit; lia).
  assert (K30 : wt5 = w64 CRT_T5)
    by (apply bv_eq; rewrite Bt5; symmetry; apply unsigned_lit; unfold CRT_T5; lia).
  assert (K31 : wt6 = w64 (3 * ns)) by (apply bv_eq; rewrite Bt6; symmetry; apply unsigned_lit; lia).
  assert (K13 : wa3 = w64 0) by (apply bv_eq; rewrite Ba3; symmetry; apply unsigned_lit; lia).
  assert (K14 : wa4 = w64 0) by (apply bv_eq; rewrite Ba4; symmetry; apply unsigned_lit; lia).
  assert (K8 : ws0 = w64 P) by (apply bv_eq; rewrite Bs0; symmetry; apply unsigned_lit; lia).
  assert (K27 : ws11 = w64 P) by (apply bv_eq; rewrite Bs11; symmetry; apply unsigned_lit; lia).
  assert (K25 : ws9 = w64 pcm) by (apply bv_eq; rewrite Bs9; symmetry; apply unsigned_lit; lia).
  assert (K32 : w32 = w64 (2 ^ 64 - 1 - P))
    by (apply bv_eq; rewrite B32; symmetry; apply unsigned_lit; lia).
  (* land at CRT_LOOP_IN *)
  rewrite Ems'.
  apply (LOOPIN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
           ly1 S1 W1 m' md' (ms_regs ms') P Q R (YKK.mkFP F' (@fp_csr fx)) v0).
  - exact HPRE.
  - split; [exact HJ2|]. split; [exact HFR1|]. split; [exact HMO1 | exact HROM2].
  - split; [exact (eq_trans (GEQ (Z_to_bv 5 2) eq_refl) E2)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 3) eq_refl) E3)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 4) eq_refl) E4)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 18) eq_refl) E18)|].
    split; [exact (eq_trans (GEQ (Z_to_bv 5 21) eq_refl) E21)
           | exact (eq_trans (GEQ (Z_to_bv 5 24) eq_refl) E24)].
  - exact (eq_trans (GEQ (Z_to_bv 5 5) eq_refl) K5).
  - exact (eq_trans (GEQ (Z_to_bv 5 6) eq_refl) K6).
  - exact (eq_trans (GEQ (Z_to_bv 5 7) eq_refl) K7).
  - exact (eq_trans (GEQ (Z_to_bv 5 16) eq_refl) K16).
  - exact (eq_trans (GEQ (Z_to_bv 5 17) eq_refl) K17).
  - exact (eq_trans (GEQ (Z_to_bv 5 28) eq_refl) K28).
  - exact (eq_trans (GEQ (Z_to_bv 5 29) eq_refl) K29).
  - exact (eq_trans (GEQ (Z_to_bv 5 30) eq_refl) K30).
  - exact (eq_trans (GEQ (Z_to_bv 5 31) eq_refl) K31).
  - exact (eq_trans (GEQ (Z_to_bv 5 13) eq_refl) K13).
  - exact (eq_trans (GEQ (Z_to_bv 5 14) eq_refl) K14).
  - exact (eq_trans (GEQ (Z_to_bv 5 8) eq_refl) K8).
  - exact (eq_trans (GEQ (Z_to_bv 5 27) eq_refl) K27).
  - exact (eq_trans (GEQ (Z_to_bv 5 20) eq_refl) H20).
  - exact (eq_trans (GEQ (Z_to_bv 5 25) eq_refl) K25).
  - exact HFRM.
  - exact HUNB.
  - unfold crtB_frame. rewrite <- ESP. rewrite <- K32. exact HFR'.
  - exact HBLK.
Qed.
End Setup.
