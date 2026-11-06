(* lib/A/Prog/C_reac_ctrl_parseK.v -- fuzz_ctrl image A (asan, libreac v1.9.0): memory plumbing, the lifts and the
   window journal step of the cgif-form glue pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v).
   Ported from a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_parseK.v and lib/B/Prog/GlueLift.v @ 258208c7d59, image A addresses
   (A.Img0.rsegs, A.MemNorm / MemNormF / MemNormTr / ProgBridge / ImgBounds).  Ported lemmas, B name -> A name:
     C_reac_ctrl_parseK.rcpK_raw_SA / rcpK_outside_dec / rcpK_aview_eq / rcpK_apresent_eq / rcpK_u64 /
       rcpK_compose / rcpK_rw_cells_tr                                    -> the same names;
     GlueLift.rrB_lift_st                                                 -> rcpK_lift_st;
     GlueLift.rrB_seg_rom_above                                           -> rcpK_seg_rom_above (A's
       MemNormTr.find_segment_end_below / rsegs_below_img for B's BzBridge.find_segment_below);
     GlueLift.rrB_journal_gen / rrB_journal_win                           -> rcpK_journal_gen / rcpK_journal_win.
   New here: rcpK_lift_norm (rcpK_lift_st after MemNormF.evtF_normalize_ro: a run on normalize m, lifted with the real
   run, whose continuation also gets ms_rel / ro_same and the hidden bytes).
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step PropExec MState ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 MemNorm MemNormF MemNormTr ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YK1b YA0n YA0nR YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0d YCbq YP09.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module MNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RK04R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04R.
Module RK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Local Notation rsegs := AI0.rsegs (only parsing).

(* The register file at the first slot of __asan_stack_malloc_1 (reac_ctrl_parseF_bnd.BndFOn.PreCall's post; B's
   rcpB_regsE): ra = the return 0x835ec, sp = s1 = A = (S - 128) / 32 * 32 (reac_ctrl_parseF.ParseFOn.A S), s0 = S,
   a0 = 128, s4 / s5 / s6 = o / f / n, s9 = the shadow offset; the other registers are the stretch's. *)
Definition rcpK_regsE (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 : word) (f n o S : Z)
  : bvmap 5 word :=
  LF.mkR (Z_to_bv 64 0x835ec) (Z_to_bv 64 ((S - 128) / 32 * 32)) gp tp t0 t1 t2 (Z_to_bv 64 S)
    (Z_to_bv 64 ((S - 128) / 32 * 32)) (Z_to_bv 64 128) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f)
    (Z_to_bv 64 n) s7 s8 (LM.wa 0x7fff8000) s10 s11 t3 t4 t5 t6.

(* ---------------------------------------------------------------------------------------------------------
   1. Memory plumbing (B's C_reac_ctrl_parseK.v). *)

(* The prologue's run on normalize memc writes only [lo, hi): off it the real end memory m1 is memc. *)
Lemma rcpK_raw_SA : forall (memc m1 m1n : word -> option byte) (lo hi : Z),
  MN.mem_rel rsegs m1 m1n -> MN.ro_same rsegs memc m1 ->
  LF.munch [(lo, hi)] (MN.normalize rsegs memc) m1n ->
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m1 x = memc x.
Proof.
  intros memc m1 m1n lo hi [REL1 _] ROS MU x Hx.
  destruct (LM.ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
  pose proof (REL1 x) as E1. unfold MN.normalize in E1. rewrite R in E1.
  assert (Ho : LF.outside [(lo, hi)] (bv_unsigned x)) by (cbn [LF.outside]; split; [exact Hx | exact I]).
  pose proof (MU x Ho) as E2. unfold MN.normalize in E2. rewrite R in E2.
  rewrite <- E1, E2. reflexivity.
Qed.

(* outside is decidable (no classical axiom). *)
Lemma rcpK_outside_dec : forall (WR : list LF.ivl) (x : Z), LF.outside WR x \/ ~ LF.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [LF.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; destruct (Z_lt_le_dec x lo) as [L|L]; destruct (Z_lt_le_dec x hi) as [M|M];
    try (left; split; [lia | exact H]); right; intros [H1 H2]; try (apply H; exact H2); lia.
Qed.

Lemma rcpK_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Ha.
Qed.

Section K.
Context {fx : RK11.FPState} {rc : RM05.RunCeil}.
Variable B : RG0f.asyms.

Lemma rcpK_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  RG0n.aview rsegs H m' a = RG0n.aview rsegs H m a.
Proof.
  intros H m m' a E. unfold RG0n.aview, RP09.mbyte, RK04.mrestrict.
  rewrite E. reflexivity.
Qed.

Lemma rcpK_apresent_eq : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  RG0n.apresent H m a -> RG0n.apresent H m' a.
Proof. intros H m m' a E [Hh (b & Hb)]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.

(* The acall_kept of reac_ctrl_parse from the caller memory memc to its return memory m'.  A change from B: the
   prologue's raw keep is stated off the whole window [S - 8800, S) (image A's PreCall states its munch there). *)
Lemma rcpK_compose : forall lyc Sc (W : RA0n.world rsegs) (memc m1 mem2 m' : word -> option byte)
    (S A o : Z) (WR : list LF.ivl),
  RM05.alloc_ceiling <= S - 8800 -> S - 8800 <= A - RG0d.ESTACK -> A <= S - 128 -> S <= 2 ^ 64 ->
  (forall x : word, ~ (S - 8800 <= bv_unsigned x < S) -> m1 x = memc x) ->
  RCbq.acall_kept rsegs B lyc Sc W m1 W mem2 (A - RG0d.ESTACK) A (fun _ => False) ->
  LF.munch WR mem2 m' ->
  (* the caller's blocks, frames (and their shadow) and the image lie below the window *)
  (forall b m i, In (b, m) (RG0d.ablocks B lyc Sc) -> 0 <= i < RG00.req_size m ->
     0 <= b + i < S - 8800) ->
  (forall cid pos a, In (cid, pos) (RG01.frames Sc) ->
     (RG0n.in_zr a (RCbq.frame_rng lyc (cid, pos)) \/
      RG0n.in_zr a (RG0f.shadow_addr (RG0f.frame_addr lyc cid pos), RG00.fs_frame_bytes cid / 8)) ->
     0 <= a < S - 8800) ->
  (forall a, RG0d.in_img rsegs a -> 0 <= a < S - 8800) ->
  (* every byte WR names outside the window: below alloc_ceiling, not an image byte, and inside the output object
     if it is a byte of a caller's block or of a caller's frame or its shadow *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ LF.outside WR a -> ~ (S - 8800 <= a < S) ->
     a < RM05.alloc_ceiling /\ ~ RG0d.in_img rsegs a /\
     (forall b m i, In (b, m) (RG0d.ablocks B lyc Sc) -> 0 <= i < RG00.req_size m ->
        a = b + i -> o <= a < o + 36) /\
     (forall cid pos, In (cid, pos) (RG01.frames Sc) ->
        (RG0n.in_zr a (RCbq.frame_rng lyc (cid, pos)) \/
         RG0n.in_zr a (RG0f.shadow_addr (RG0f.frame_addr lyc cid pos), RG00.fs_frame_bytes cid / 8)) ->
        o <= a < o + 36)) ->
  (forall a, S - 8800 <= a < S -> RG0n.apresent (RA0n.w_H W) m' a) ->
  RCbq.acall_kept rsegs B lyc Sc W memc W m' (S - 8800) S (fun a => o <= a < o + 36).
Proof.
  intros lyc Sc W memc m1 mem2 m' S A o WR Hceil HA1 HA2 HS RA (K1 & K2 & K3 & K4 & K5 & K6) MU
    Hblk Hfrm Himg HWR HPR.
  pose proof (RCbq.asan_consts) as (C1 & _).
  assert (ES : RG0d.ESTACK = 4096) by reflexivity.
  (* the three raw steps at one address a in [0, 2^64) that WR does not name, outside [S - 8800, S) *)
  assert (RAW : forall a, 0 <= a < 2 ^ 64 -> LF.outside WR a -> ~ (S - 8800 <= a < S) ->
                  m' (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a) /\ m1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
  { intros a Ha Ho Hw. split.
    - apply MU. rewrite rcpK_u64 by lia. exact Ho.
    - apply RA. rewrite rcpK_u64 by lia. exact Hw. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* (1) above alloc_ceiling, off the window *)
    intros a Ha Hw.
    assert (Ho : LF.outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx Hw) as (Hlt & _). lia. }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' a E2).
    rewrite (K1 a Ha ltac:(unfold RG0d.ESTACK in *; lia)).
    exact (rcpK_aview_eq _ memc m1 a E1).
  - (* (2) the caller's blocks, off the output object *)
    intros b m i Hb Hi HE.
    pose proof (Hblk b m i Hb Hi) as Hlo.
    assert (Ho : LF.outside WR (b + i)).
    { destruct (rcpK_outside_dec WR (b + i)) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR (b + i) ltac:(lia) Hx ltac:(lia)) as (_ & _ & Hbk & _).
      exact (HE (Hbk b m i Hb Hi eq_refl)). }
    destruct (RAW (b + i) ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' (b + i) E2).
    rewrite (K2 b m i Hb Hi ltac:(intros [])).
    exact (rcpK_aview_eq _ memc m1 (b + i) E1).
  - (* (3) the image *)
    intros a Hi Hst Her.
    pose proof (Himg a Hi) as Hlo.
    assert (Ho : LF.outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx ltac:(lia)) as (_ & Hni & _). exact (Hni Hi). }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' a E2).
    rewrite (K3 a Hi Hst Her).
    exact (rcpK_aview_eq _ memc m1 a E1).
  - (* (4) the caller's frames and their shadow, off the output object *)
    intros cid pos a Hin Hr HE.
    pose proof (Hfrm cid pos a Hin Hr) as Hlo.
    assert (Ho : LF.outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx ltac:(lia)) as (_ & _ & _ & Hfk).
      exact (HE (Hfk cid pos Hin Hr)). }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' a E2).
    rewrite (K4 cid pos a Hin Hr ltac:(intros [])).
    exact (rcpK_aview_eq _ memc m1 a E1).
  - (* (5) presence above alloc_ceiling, off the window *)
    intros a Ha Hw Hp.
    assert (Ho : LF.outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx Hw) as (Hlt & _). lia. }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    apply (rcpK_apresent_eq _ mem2 m' a E2).
    apply (K5 a Ha ltac:(unfold RG0d.ESTACK in *; lia)).
    apply (rcpK_apresent_eq _ memc m1 a E1). exact Hp.
  - (* (6) the window is present at the end *)
    exact HPR.
Qed.

(* Cells that keep their bytes (mrd) and stay writable (stk) keep rw_cells. *)
Lemma rcpK_rw_cells_tr : forall (m m' : word -> option byte) p cs,
  LS.rw_cells rsegs m p cs ->
  (forall i, 0 <= i < Z.of_nat (LC.cells_size cs) -> LM.mrd rsegs m' (LM.wa (p + i)) = LM.mrd rsegs m (LM.wa (p + i))) ->
  LF.stk rsegs m' p (p + Z.of_nat (LC.cells_size cs)) ->
  LS.rw_cells rsegs m' p cs.
Proof.
  intros m m' p cs [[Hwf (H0 & H1 & Hb)] _] Hm (S0 & S1 & Hs).
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite <- (Hb i Hi). pose proof (LC.cells_bytes_length cs Hwf) as EL.
    apply Hm. lia.
  - split; [exact S0|]. split; [lia|]. intros i Hi. destruct (Hs (p + i) ltac:(lia)) as [Hw _]. exact Hw.
Qed.
End K.

(* ---------------------------------------------------------------------------------------------------------
   2. The lifts (B's GlueLift.v). *)
Section Lift.
Context {fx : RK11.FPState}.

(* rrB_lift_st: a footprint run under RNG_W (w_H W), lifted; the continuation gets the run itself (YK04R.fsteps),
   its post, the hidden bytes kept (YA0nR.SRr_fevt_hid) and the model's materialization. *)
Lemma rcpK_lift_st : RK04.wx_segs_nowrap rsegs ->
  forall (W : RA0n.world rsegs) (md : Model) R F pc fc rv (m ro : word -> option byte)
         (P : machine_state -> Prop) (Q : RA0n.world rsegs -> config -> Prop),
    LX.evtF rsegs (PB.RNG_W (RA0n.w_H W)) P (LMS.MS R F pc fc rv m ro) ->
    (forall ms' md',
       RK04R.fsteps rsegs (PB.RNG_W (RA0n.w_H W)) (LMS.MS R F pc fc rv m ro) ms' ->
       P ms' ->
       (forall x : word, RA0n.w_H W x = true -> ms_mem ms' x = m x) ->
       RK04.same_but_materialized md md' -> RA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    RA0n.SRr rsegs W (mkCfg (LMS.MS R F pc fc rv m ro) md) Q.
Proof.
  intros Hwx W md R F pc fc rv m ro P Q HE K.
  apply (RA0nR.SRr_fevt_hid rsegs Hwx W (LMS.MS R F pc fc rv m ro) md
           (PB.RNG_W (RA0n.w_H W))
           (fun s => RK04R.fsteps rsegs (PB.RNG_W (RA0n.w_H W)) (LMS.MS R F pc fc rv m ro) s /\ P s) Q).
  - destruct (PB.fevt_of_evtF _ _ _ HE) as (ms' & Hrun & HP).
    exists ms'. split; [exact Hrun | split; [exact Hrun | exact HP]].
  - apply PB.fp_avoids_RNG_W.
  - intros ms' md' [Hrun HP] Hhid Hs. exact (K ms' md' Hrun HP Hhid Hs).
Qed.

(* A run on normalize m (a footprint contract's form), lifted at the real memory m: MemNormF.evtF_normalize_ro moves
   it to m, rcpK_lift_st lifts it.  The continuation gets the real run, a P-state s0 that ms_rel relates to the real
   end state, ro_same of m and the end memory, and the hidden bytes kept. *)
Lemma rcpK_lift_norm : RK04.wx_segs_nowrap rsegs ->
  forall (W : RA0n.world rsegs) (md : Model) R F pc fc rv (m ro : word -> option byte)
         (P : machine_state -> Prop) (Q : RA0n.world rsegs -> config -> Prop),
    MN.ro_agree rsegs m ->
    LX.evtF rsegs (PB.RNG_W (RA0n.w_H W)) P (LMS.MS R F pc fc rv (MN.normalize rsegs m) ro) ->
    (forall ms' md',
       RK04R.fsteps rsegs (PB.RNG_W (RA0n.w_H W)) (LMS.MS R F pc fc rv m ro) ms' ->
       (exists s0, P s0 /\ MN.ms_rel rsegs ms' s0 /\ MN.ro_same rsegs m (ms_mem ms')) ->
       (forall x : word, RA0n.w_H W x = true -> ms_mem ms' x = m x) ->
       RK04.same_but_materialized md md' -> RA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    RA0n.SRr rsegs W (mkCfg (LMS.MS R F pc fc rv m ro) md) Q.
Proof.
  intros Hwx W md R F pc fc rv m ro P Q RO HE K.
  exact (rcpK_lift_st Hwx W md R F pc fc rv m ro _ Q
           (MNF.evtF_normalize_ro (PB.RNG_W (RA0n.w_H W)) P R F pc fc rv m ro RO HE) K).
Qed.
End Lift.

(* No segment of rsegs reaches IMG_HI: the rom is None there. *)
Lemma rcpK_seg_rom_above : forall a, IB.IMG_HI <= a < 2 ^ 64 -> LP.seg_rom rsegs (LM.wa a) = None.
Proof.
  intros a Ha. unfold LP.seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned (LM.wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. rewrite (LM.wa_unsigned a ltac:(unfold IB.IMG_HI in Ha; lia)) in E.
  destruct (MNT.find_segment_end_below rsegs IB.IMG_HI a 1 s MNT.rsegs_below_img E ltac:(lia)) as [L|L]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. The journal across a lifted stretch whose writes all lie above IMG_HI and are awr bytes (B's GlueLift.v
   Section Journal). *)
Section Journal.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : RG0f.asyms.
Hypothesis LAWS : RG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, RG0d.in_img rsegs a -> 0 <= a < RG0f.kLowMemEnd.

Lemma rcpK_journal_gen :
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc Sc (W : RA0n.world rsegs)
         memc mdc k (m1 mc : word -> option byte) mdc' (Wr : Z -> Prop),
    RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    (forall a, Wr a -> RCbq.awr_byte STK sp0 FP (RG0d.ablocks B ly S0) (RG0d.ablocks B lyc Sc) lyc own a) ->
    (forall a, Wr a -> IB.IMG_HI <= a < 2 ^ 64) ->
    (forall a, Wr a \/ ~ Wr a) ->
    (forall x : word, ~ Wr (bv_unsigned x) -> mc x = MN.normalize rsegs memc x) ->
    (forall a, Wr a -> exists b, LM.mrd rsegs mc (LM.wa a) = Some b) ->
    MN.mem_rel rsegs m1 mc -> MN.ro_same rsegs memc m1 ->
    (forall x : word, RA0n.w_H W x = true -> m1 x = memc x) ->
    RK04.same_but_materialized mdc mdc' ->
    RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc' k.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k m1 mc mdc' Wr HJ Hsub Himg Hdec MU Hrd
    [REL1 REL2] ROS Hhid Hsame.
  (* off Wr the real final byte is the caller's *)
  assert (OFF : forall x : word, ~ Wr (bv_unsigned x) -> m1 x = memc x).
  { intros x Hx. destruct (LM.ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
    pose proof (REL1 x) as E1. unfold MN.normalize in E1. rewrite R in E1.
    pose proof (MU x Hx) as E2. unfold MN.normalize in E2. rewrite R in E2. rewrite <- E1, E2. reflexivity. }
  eapply (RCbq.ajournal_exec rsegs B LAWS segs_low) with (Wr := Wr);
    [exact HJ | | | exact Hhid | exact Hsame | exact Hsub].
  - intros x Hx. unfold RK04.mrestrict. destruct (RA0n.w_H W x); [reflexivity|].
    exact (OFF x Hx).
  - intros x Hx. unfold RK04.mrestrict in *. destruct (RA0n.w_H W x); [exact Hx|].
    destruct (Hdec (bv_unsigned x)) as [HW|HW]; [|rewrite (OFF x HW); exact Hx].
    pose proof (Himg _ HW) as Hb.
    assert (Ex : LM.wa (bv_unsigned x) = x) by (unfold LM.wa; apply LMS.Z_to_bv_bv_unsigned).
    assert (R : LM.ro_addr rsegs x = false)
      by (rewrite <- Ex; apply MNT.ro_addr_above_img; lia).
    pose proof (REL1 x) as E1. unfold MN.normalize in E1. rewrite R in E1.
    destruct (Hrd (bv_unsigned x) HW) as [b Hrb]. rewrite Ex in Hrb.
    unfold LM.mrd in Hrb. destruct (mc x) as [c|] eqn:Ec.
    + rewrite <- E1. discriminate.
    + rewrite <- Ex in Hrb. rewrite (rcpK_seg_rom_above (bv_unsigned x) ltac:(lia)) in Hrb. discriminate Hrb.
Qed.

(* The window case, from munch over one range. *)
Lemma rcpK_journal_win :
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc Sc (W : RA0n.world rsegs)
         memc mdc k (m1 mc : word -> option byte) mdc' (lo hi : Z),
    RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    sp0 - STK <= lo -> hi <= sp0 -> IB.IMG_HI <= lo -> hi <= 2 ^ 64 ->
    LF.munch [(lo, hi)] (MN.normalize rsegs memc) mc ->
    (forall a, lo <= a < hi -> exists b, LM.mrd rsegs mc (LM.wa a) = Some b) ->
    MN.mem_rel rsegs m1 mc -> MN.ro_same rsegs memc m1 ->
    (forall x : word, RA0n.w_H W x = true -> m1 x = memc x) ->
    RK04.same_but_materialized mdc mdc' ->
    RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc' k.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k m1 mc mdc' lo hi HJ Hlo Hhi Himg Htop MU Hrd
    REL ROS Hhid Hsame.
  apply (rcpK_journal_gen STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k m1 mc mdc' (fun a => lo <= a < hi) HJ);
    [intros a Ha; left; lia | intros a Ha; lia | | | exact Hrd | exact REL | exact ROS | exact Hhid | exact Hsame].
  - intros a. destruct (Z_lt_le_dec a lo); [right; lia|]. destruct (Z_lt_le_dec a hi); [left; lia | right; lia].
  - intros x Hx. apply MU. cbn [LF.outside]. split; [exact Hx | exact I].
Qed.
End Journal.
