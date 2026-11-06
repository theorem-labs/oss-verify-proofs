(* lib/B/Prog/GlueLift.v -- the generic lift / footprint / journal tools of the fuzz_ctrl image-B glue
   (asan-ubsan, libreac v1.9.0).  Moved verbatim from lib/B/Prog/C_reac_ctrl_identity_replyPf.v at e026bdcbd0d
   (two Theorem Labs lanes 08:0xZ, the Require cycle parsePf -> identity_replyPf -> parsePf): a Theorem Labs lane's parse glue
   needs these lemmas, and the reply lane's top theorem needs parse's proof, so the shared home must not Require the
   reply glue.  This file Requires NO lib/B/Prog/C_reac_* file and no reac_ctrl_identity_reply* file.
   Names, statements and proofs are those of the Pf file; only the Section packaging and the module prefixes
   (MemNorm -> B.MemNorm, and the same for MemNormF / MemNormTr / ProgBridge / BzBridge, against the ambiguity
   between fuzz_ctrl/lib/MemNorm.v and fuzz_ctrl/lib/B/MemNorm.v) differ. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YA0n YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YI16 YG0f YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0n YG0v YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1b YP09 YA0o.   (* rrB_journal_free (Section JournalFree) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
Import ListNotations.
Open Scope Z_scope.

Section Lift.
Context {fx : lib.Reusable.YK11.FPState}.

(* The lift of one stretch.  P is the stretch's own post on the normalized memory; the continuation receives the
   REAL final state ms', related to a P-state s0 by ms_rel (registers, pc, and memory up to the read-only bytes) and
   keeping every read-only byte of m (ro_same), as MemNormF.evtF_normalize_ro states it, AND keeping every byte the
   world hides (YA0nR.SRr_fevt_hid): the journal step after a lifted run, YCbq.ajournal_exec, takes exactly that
   premise (YCbq.v:640).  General shape, for every stretch of every fake-stack callee. *)
Lemma rrB_lift : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall (W : lib.Reusable.YA0n.world rsegs) (md : Model) R F pc fc rv (m ro : word -> option byte)
         (P : machine_state -> Prop) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    B.MemNorm.ro_agree rsegs m ->
    ExecF.evtF rsegs (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) P
      (lib.Lib.MState.MS R F pc fc rv (B.MemNorm.normalize rsegs m) ro) ->
    (forall ms' md',
       (exists s0, P s0 /\ B.MemNorm.ms_rel rsegs ms' s0 /\ B.MemNorm.ro_same rsegs m (ms_mem ms')) ->
       (forall x : word, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = m x) ->
       lib.Reusable.YK04.same_but_materialized md md' -> lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    lib.Reusable.YA0n.SRr rsegs W (mkCfg (lib.Lib.MState.MS R F pc fc rv m ro) md) Q.
Proof.
  intros Hwx W md R F pc fc rv m ro P Q RO HE K.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid rsegs Hwx W (lib.Lib.MState.MS R F pc fc rv m ro) md
           (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
           (fun s => exists s0, P s0 /\ B.MemNorm.ms_rel rsegs s s0 /\ B.MemNorm.ro_same rsegs m (ms_mem s)) Q).
  - exact (B.ProgBridge.fevt_of_evtF _ _ _
             (B.MemNormF.evtF_normalize_ro (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) P R F pc fc rv m ro RO HE)).
  - apply B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' HP Hhid Hs. exact (K ms' md' HP Hhid Hs).
Qed.
(* ---- Footprint tools for a re-based stretch (generic, for every fake-stack lane).  A stretch run under a footprint
   R that AVOIDS a byte range keeps that range unchanged (YK04R.fsteps_restrict), and a run under a smaller footprint
   is a run under any larger one.  Use: the stretch after a fake-stack call never touches the allocator-owned hint
   word, whose 8 bytes the _F munch lists contain (unit decision 125's finding); running the stretch under
   rrB_avoid (RNG_W H) [hint] proves the word unchanged without copying any script. ---- *)
Lemma rrB_mstepsF_mono : forall (R R' : ExecF.footprint) ms ms', (forall b n, R b n -> R' b n) ->
  ExecF.mstepsF rsegs R ms ms' -> ExecF.mstepsF rsegs R' ms ms'.
Proof.
  intros R R' ms ms' HR H. induction H as [ms | ms ms1 ms2 [Hs (accs & E & Fa)] _ IH].
  - apply ExecF.mstepsF_refl.
  - eapply ExecF.mstepsF_cons; [|exact IH]. split; [exact Hs|]. exists accs. split; [exact E|].
    eapply Forall_impl; [|exact Fa]. intros acc Ha. unfold ExecF.acc_in in *. apply HR. exact Ha.
Qed.

Lemma rrB_evtF_mono : forall (R R' : ExecF.footprint) P ms, (forall b n, R b n -> R' b n) ->
  ExecF.evtF rsegs R P ms -> ExecF.evtF rsegs R' P ms.
Proof. intros R R' P ms HR (ms' & Hr & HP). exists ms'. split; [exact (rrB_mstepsF_mono R R' ms ms' HR Hr) | exact HP]. Qed.

Lemma rrB_evtF_keep : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall (R : ExecF.footprint) (H : word -> bool) P ms,
  lib.Reusable.YK04.H_off_segments rsegs H -> lib.Reusable.YK04R.fp_avoids H R -> ExecF.evtF rsegs R P ms ->
  ExecF.evtF rsegs R (fun ms' => P ms' /\ forall x, H x = true -> ms_mem ms' x = ms_mem ms x) ms.
Proof.
  intros Hwx R H P ms HH Hav (ms' & Hr & HP). exists ms'. split; [exact Hr|]. split; [exact HP|].
  destruct (lib.Reusable.YK04R.fsteps_restrict rsegs H HH Hwx R ms ms' (B.ProgBridge.fsteps_of_mstepsF R ms ms' Hr) Hav)
    as [_ E].
  intros x Hx. rewrite E at 1. cbn [ms_mem lib.Reusable.YK04.unrestrict].
  unfold lib.Reusable.YK04.munrestrict. rewrite Hx. reflexivity.
Qed.

(* The footprint R without the byte range [lo, hi), and the indicator of that range. *)
Definition rrB_avoid (R : ExecF.footprint) (lo hi : Z) : ExecF.footprint :=
  fun b n => R b n /\ b + Z.of_nat n <= 2 ^ 64 /\ (b + Z.of_nat n <= lo \/ hi <= b).
Definition rrB_inH (lo hi : Z) : word -> bool := fun x => (lo <=? bv_unsigned x) && (bv_unsigned x <? hi).

Lemma rrB_avoid_fp : forall R lo hi, lib.Reusable.YK04R.fp_avoids (rrB_inH lo hi) (rrB_avoid R lo hi).
Proof.
  intros R lo hi a n [_ [Hb D]] k Hk. unfold rrB_inH, lib.Reusable.YK04.woff.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. cbn [Z.of_N] in Ra.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  destruct D as [D | D].
  - apply andb_false_iff. left. apply Z.leb_gt. lia.
  - apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Lemma rrB_avoid_sub : forall R lo hi b n, rrB_avoid R lo hi b n -> R b n.
Proof. intros R lo hi b n [H _]. exact H. Qed.

Lemma rrB_rng_avoid : forall R lo hi l n, ExecF.rng R l n -> (l + n <= lo \/ hi <= l) ->
  ExecF.rng (rrB_avoid R lo hi) l n.
Proof.
  intros R lo hi l n (A & B & H) D. split; [lia|]. split; [lia|]. intros b j Hb Hj.
  split; [apply H; lia|]. split; [lia|]. destruct D as [D|D]; [left; lia | right; lia].
Qed.

(* A range above the image is off every segment of rsegs. *)
Lemma rrB_inH_off : forall lo hi, ImgBounds.IMG_HI <= lo ->
  lib.Reusable.YK04.H_off_segments rsegs (rrB_inH lo hi).
Proof.
  intros lo hi Hlo a Ha. unfold rrB_inH in Ha. apply andb_true_iff in Ha as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. cbn [Z.of_N] in Ra.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (B.BzBridge.find_segment_below rsegs ImgBounds.IMG_HI (bv_unsigned a) 1 s B.MemNormTr.rsegs_below_img E
              ltac:(lia)) as [L|L]; lia.
Qed.
(* A range inside the shadow region [LOWMEM_END, HIGHMEM_BEG) is apart from any short application range: the shadow
   of every application address (x < APPMEM_END) lies there, and the side stack (fs_place) is application memory. *)
Lemma rrB_shadow_vs_app : forall l n lo hi, LOWMEM_END <= l -> l + n <= HIGHMEM_BEG -> lo < hi ->
  app_mem lo -> app_mem (hi - 1) -> hi - lo <= HIGHMEM_BEG - LOWMEM_END -> l + n <= lo \/ hi <= l.
Proof.
  intros l n lo hi H1 H2 H3 A1 A2 H4. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma rrB_shadow_byte_in : forall x, 0 <= x < APPMEM_END ->
  LOWMEM_END <= x / 8 + ASAN_K /\ x / 8 + ASAN_K + 1 <= HIGHMEM_BEG.
Proof. intros x Hx. unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END, ASAN_K in *. Z.div_mod_to_equations. lia. Qed.
End Lift.

(* Moved UNCHANGED (only the name: rcpB_lift_st -> rrB_lift_st) from (internal path) (a Theorem Labs lane's parse glue). *)
Lemma rrB_lift_st : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall (W : lib.Reusable.YA0n.world rsegs) (md : Model) R F pc fc rv (m ro : word -> option byte)
         (P : machine_state -> Prop) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Lib.ExecF.evtF rsegs (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) P (MS R F pc fc rv m ro) ->
    (forall ms' md',
       lib.Reusable.YK04R.fsteps rsegs (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (MS R F pc fc rv m ro) ms' ->
       P ms' ->
       (forall x : word, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = m x) ->
       lib.Reusable.YK04.same_but_materialized md md' -> lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    lib.Reusable.YA0n.SRr rsegs W (mkCfg (MS R F pc fc rv m ro) md) Q.
Proof.
  intros Hwx W md R F pc fc rv m ro P Q HE K.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid rsegs Hwx W (MS R F pc fc rv m ro) md
           (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
           (fun s => lib.Reusable.YK04R.fsteps rsegs (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
                       (MS R F pc fc rv m ro) s /\ P s) Q).
  - destruct (lib.B.ProgBridge.fevt_of_evtF _ _ _ HE) as (ms' & Hrun & HP).
    exists ms'. split; [exact Hrun | split; [exact Hrun | exact HP]].
  - apply lib.B.ProgBridge.fp_avoids_RNG_W.
  - intros ms' md' [Hrun HP] Hhid Hs. exact (K ms' md' Hrun HP Hhid Hs).
Qed.

(* ---- The journal across a lifted stretch that writes only its own stack window [lo, hi) (S-A writes
   [S - 9072, S); every fake-stack callee's first stretch has this shape).  YCbq.ajournal_exec with Wr := [lo, hi):
   off the window the real final byte IS the caller's (read-only addresses by ro_same; the others because the real
   byte equals the normalized one, ms_rel, and the run's munch keeps the normalized one); inside the window the byte
   is present because it is readable and no segment reaches above IMG_HI, so mrd has no rom fallback there. ---- *)
Lemma rrB_seg_rom_above : forall a, ImgBounds.IMG_HI <= a < 2 ^ 64 -> lib.Lib.PropExec.seg_rom rsegs (lib.Lib.Mem.wa a) = None.
Proof.
  intros a Ha. unfold lib.Lib.PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned (lib.Lib.Mem.wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. rewrite (lib.Lib.Mem.wa_unsigned a ltac:(unfold ImgBounds.IMG_HI in Ha; lia)) in E.
  destruct (B.BzBridge.find_segment_below rsegs ImgBounds.IMG_HI a 1 s B.MemNormTr.rsegs_below_img E ltac:(lia))
    as [L|L]; lia.
Qed.

Section Journal.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* The two Section premises of YCbq's Section a0 (YCbq.v:204-208), for B's bundle.  segs_low: core, PENDING THE
   RECORD CORE (a refused name on line 25 of an earlier version of YCeg.v, not in this delivery).  Its statement is Reusable.YCeg.tfib_segs_low (at head lib/Reusable/YCeg.v:66, stated and
   proved), but that version of lib/Reusable/YCeg.v compiled on NO B base then: its line 25 named port_core_refused_103b0
   (a Theorem Labs lane's probe-free build, build 2026-10-29T05:06:50Z).  So YCeg is
   NOT Required.
   *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.

(* ---- The journal across ANY lifted stretch whose writes Wr all lie above IMG_HI and each is an awr_byte (the
   window arm, or in_frames: the stretch's own fake frame and that frame's shadow after a fake-stack call).  One
   lemma for the unit (a Theorem Labs lane 05:2xZ; frame case found by a Theorem Labs lane).  YCbq.ajournal_exec with Wr: off Wr the real
   final byte is the caller's (read-only addresses by MemNorm.ro_same; the others because the real byte equals the
   normalized one, ms_rel, and the run keeps the normalized one off Wr); on Wr the byte stays present because it is
   readable and no segment reaches above IMG_HI, so mrd has no rom fallback there. ---- *)
Lemma rrB_journal_gen :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
         memc mdc k (m1 mc : word -> option byte) mdc' (Wr : Z -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    (forall a, Wr a -> lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
                         (lib.Reusable.YG0d.ablocks B lyc Sc) lyc own a) ->
    (forall a, Wr a -> ImgBounds.IMG_HI <= a < 2 ^ 64) ->
    (forall a, Wr a \/ ~ Wr a) ->
    (forall x : word, ~ Wr (bv_unsigned x) -> mc x = B.MemNorm.normalize rsegs memc x) ->
    (forall a, Wr a -> exists b, lib.Lib.Mem.mrd rsegs mc (lib.Lib.Mem.wa a) = Some b) ->
    B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
    (forall x : word, lib.Reusable.YA0n.w_H W x = true -> m1 x = memc x) ->
    lib.Reusable.YK04.same_but_materialized mdc mdc' ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc' k.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k m1 mc mdc' Wr HJ Hsub Himg Hdec MU Hrd
    [REL1 REL2] ROS Hhid Hsame.
  (* off Wr the real final byte is the caller's *)
  assert (OFF : forall x : word, ~ Wr (bv_unsigned x) -> m1 x = memc x).
  { intros x Hx. destruct (lib.Lib.Mem.ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
    pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    pose proof (MU x Hx) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2. rewrite <- E1, E2. reflexivity. }
  eapply (lib.Reusable.YCbq.ajournal_exec rsegs B LAWS segs_low) with (Wr := Wr);
    [exact HJ | | | exact Hhid | exact Hsame | exact Hsub].
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict. destruct (lib.Reusable.YA0n.w_H W x); [reflexivity|].
    exact (OFF x Hx).
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict in *. destruct (lib.Reusable.YA0n.w_H W x); [exact Hx|].
    destruct (Hdec (bv_unsigned x)) as [HW|HW]; [|rewrite (OFF x HW); exact Hx].
    pose proof (Himg _ HW) as Hb.
    assert (Ex : lib.Lib.Mem.wa (bv_unsigned x) = x) by (unfold lib.Lib.Mem.wa; apply lib.Lib.MState.Z_to_bv_bv_unsigned).
    assert (R : lib.Lib.Mem.ro_addr rsegs x = false)
      by (rewrite <- Ex; apply B.MemNormTr.ro_addr_above_img; lia).
    pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    destruct (Hrd (bv_unsigned x) HW) as [b Hrb]. rewrite Ex in Hrb.
    unfold lib.Lib.Mem.mrd in Hrb. destruct (mc x) as [c|] eqn:Ec.
    + rewrite <- E1. discriminate.
    + rewrite <- Ex in Hrb. rewrite (rrB_seg_rom_above (bv_unsigned x) ltac:(lia)) in Hrb. discriminate Hrb.
Qed.

(* The window case (S-A: [S - 9072, S)), from munch over one range; its statement is unchanged since d37b6987833. *)
Lemma rrB_journal_win :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
         memc mdc k (m1 mc : word -> option byte) mdc' (lo hi : Z),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    sp0 - STK <= lo -> hi <= sp0 -> ImgBounds.IMG_HI <= lo -> hi <= 2 ^ 64 ->
    lib.Lib.Frame.munch [(lo, hi)] (B.MemNorm.normalize rsegs memc) mc ->
    (forall a, lo <= a < hi -> exists b, lib.Lib.Mem.mrd rsegs mc (lib.Lib.Mem.wa a) = Some b) ->
    B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
    (forall x : word, lib.Reusable.YA0n.w_H W x = true -> m1 x = memc x) ->
    lib.Reusable.YK04.same_but_materialized mdc mdc' ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc' k.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k m1 mc mdc' lo hi HJ Hlo Hhi Himg Htop MU Hrd
    REL ROS Hhid Hsame.
  apply (rrB_journal_gen STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k m1 mc mdc' (fun a => lo <= a < hi) HJ);
    [intros a Ha; left; lia | intros a Ha; lia | | | exact Hrd | exact REL | exact ROS | exact Hhid | exact Hsame].
  - intros a. destruct (Z_lt_le_dec a lo); [right; lia|]. destruct (Z_lt_le_dec a hi); [left; lia | right; lia].
  - intros x Hx. apply MU. cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
Qed.

(* ---- A journal STARTED at a state, without the achain conjunct of afn_pre (DEMAND item found by a Theorem Labs lane):
   YCbq.ajournal_init takes afn_pre WHOLE, but its proof (YCbq.v:385-394) uses only AR, astk_ok, the stack's
   presence and qtight - never achain, ret_ok, raZ, gp or tp.  So this twin, stated over sp0, closes it; the proof
   is ajournal_init's, line for line. ---- *)
Lemma rrB_ajournal_init_noch :
  forall STK sp0 FP ly S0 (W : lib.Reusable.YA0n.world rsegs) mem md,
    lib.Reusable.YG0n.AR rsegs B ly S0 W mem md ->
    lib.Reusable.YCbq.astk_ok STK ly sp0 ->
    (forall a, sp0 - STK <= a < sp0 -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a) ->
    lib.Reusable.YG01.qtight S0 ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W mem md [] ly S0 W mem md 0.
Proof using.
  intros STK sp0 FP ly S0 W mem md HAR Hstk Hpres HQT.
  split; [exact HAR|]. split; [apply lib.Reusable.YG0f.layout_le_refl|]. split; [lia|].
  split; [apply lib.Reusable.YA0n.wle_refl|]. split; [apply lib.Reusable.YCbq.aos_step_refl|].
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
  split; [exact Hpres|]. split; [exact Hstk|]. split; [intros; reflexivity | exact HQT].
Qed.
End Journal.

(* Moved here UNCHANGED from lib/B/Prog/C_reac_box_model_blockPf.v (a working branch 8d5b2e35119,
   a Theorem Labs lane; first Qed at 2e45e56a141), in its own Section so that Section Journal's arguments do not change.
   The only edit: the proof's two references to C_reac_ctrl_identity_replyPf.rrB_seg_rom_above name this file's
   rrB_seg_rom_above (the same lemma, moved here by a Theorem Labs lane), so that GlueLift.v Requires no C_reac_* file. *)
(* ---- The journal across a lifted stretch that FREES one fake frame by its flag byte (generic in cid; model_block's
   stretch B at cid 0, identity_reply's S-C at cid 1, agreed with a Theorem Labs lane 07:2xZ).  YCbq.ajournal_after_write with
   S' := stack_free_state cid pos Sc and own2 := own0: every written byte is an awr_byte or the frame's flag byte
   (the `aowned /\ app_addr /\ ~ in_img` arm, from frame_flag_lawP), the AR at S' by astack_free_law with the flag
   at 0.  This is the journal part of the core's YCbq.aj_flag_store (YCbq.v:2383-2435), for a run given by its
   memories in a Theorem Labs lane's rrB_journal_gen interface instead of a symbolic run. ---- *)
Section JournalFree.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
Hypothesis ASF : lib.Reusable.YG0d.astack_free_law rsegs B.
Hypothesis FFL : lib.Reusable.YCbq.frame_flag_lawP rsegs B.

Lemma rrB_journal_free :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own0 lyc Sc (W : lib.Reusable.YA0n.world rsegs)
         memc mdc k (m1 mc : word -> option byte) mdc' (Wr : Z -> Prop) (cid pos : Z),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((cid, pos) :: own0) lyc Sc W memc mdc k ->
    0 <= cid ->
    (forall a, Wr a -> lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
                         (lib.Reusable.YG0d.ablocks B lyc Sc) lyc ((cid, pos) :: own0) a \/
                       a = lib.Reusable.YG0f.flag_addr lyc cid pos) ->
    (forall a, Wr a -> ImgBounds.IMG_HI <= a < 2 ^ 64) ->
    (forall a, Wr a \/ ~ Wr a) ->
    (forall x : word, ~ Wr (bv_unsigned x) -> mc x = B.MemNorm.normalize rsegs memc x) ->
    (forall a, Wr a -> exists b, mrd rsegs mc (wa a) = Some b) ->
    ImgBounds.IMG_HI <= lib.Reusable.YG0f.flag_addr lyc cid pos < 2 ^ 64 ->
    mrd rsegs mc (wa (lib.Reusable.YG0f.flag_addr lyc cid pos)) = Some (Z_to_bv 8 0) ->
    B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
    (forall x : word, lib.Reusable.YA0n.w_H W x = true -> m1 x = memc x) ->
    lib.Reusable.YK04.same_but_materialized mdc mdc' ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own0 lyc
      (lib.Reusable.YG01.stack_free_state cid pos Sc) W m1 mdc' k.
Proof using LAWS segs_low ML ASF FFL.
  intros STK sp0 FP ly S0 W0 mem0 md0 own0 lyc Sc W memc mdc k m1 mc mdc' Wr cid pos HJ Hcid Hwr Himg Hdec MU Hrd
    HFimg Hflag0 [REL1 REL2] ROS Hhid Hsame.
  (* off Wr the real final byte is the caller's (as in rrB_journal_gen) *)
  assert (OFF : forall x : word, ~ Wr (bv_unsigned x) -> m1 x = memc x).
  { intros x Hx. destruct (ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
    pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    pose proof (MU x Hx) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2. rewrite <- E1, E2. reflexivity. }
  assert (Hfr' : forall x : word, ~ Wr (bv_unsigned x) ->
            lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m1 x =
            lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc x).
  { intros x Hx. unfold lib.Reusable.YK04.mrestrict. destruct (lib.Reusable.YA0n.w_H W x); [reflexivity|].
    exact (OFF x Hx). }
  (* the visible bytes present before are present after (as in rrB_journal_gen) *)
  assert (Hgr' : lib.Reusable.YK1b.mem_grows (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc)
                   (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) m1)).
  { intros x Hx. unfold lib.Reusable.YK04.mrestrict in *. destruct (lib.Reusable.YA0n.w_H W x); [exact Hx|].
    destruct (Hdec (bv_unsigned x)) as [HW|HW]; [|rewrite (OFF x HW); exact Hx].
    pose proof (Himg _ HW) as Hb.
    assert (Ex : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
    assert (R : ro_addr rsegs x = false)
      by (rewrite <- Ex; apply MemNormTr.ro_addr_above_img; lia).
    pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    destruct (Hrd (bv_unsigned x) HW) as [b Hrb]. rewrite Ex in Hrb.
    unfold mrd in Hrb. destruct (mc x) as [c|] eqn:Ec.
    + rewrite <- E1. discriminate.
    + rewrite <- Ex in Hrb.
      rewrite (rrB_seg_rom_above (bv_unsigned x) ltac:(lia)) in Hrb. discriminate Hrb. }
  assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
            lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a =
            lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc a).
  { intros a Ha HWa. apply lib.Reusable.YCbq.aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact HWa. }
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
  assert (Hin : In (cid, pos) (lib.Reusable.YG01.frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (FFL lyc Sc W memc mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
  (* the flag byte at 0 in the real end memory: visible (frame_flag_lawP), not read-only (above IMG_HI) *)
  assert (HF0 : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1
                  (lib.Reusable.YG0f.flag_addr lyc cid pos) = Some 0).
  { destruct Hfp as (Hh & _).
    set (fa := lib.Reusable.YG0f.flag_addr lyc cid pos) in *.
    assert (R : ro_addr rsegs (wa fa) = false) by (apply MemNormTr.ro_addr_above_img; lia).
    pose proof (REL1 (wa fa)) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    assert (Em1 : m1 (Z_to_bv 64 fa) = Some (Z_to_bv 8 0)).
    { change (Z_to_bv 64 fa) with (wa fa). rewrite <- E1.
      unfold mrd in Hflag0. destruct (mc (wa fa)) as [c|] eqn:Ec; [exact Hflag0|].
      rewrite (rrB_seg_rom_above fa ltac:(lia)) in Hflag0. discriminate Hflag0. }
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
    rewrite Hh, Em1. reflexivity. }
  pose proof (lib.Reusable.YA0o.same_but_materialized_wvb mdc mdc' Hsame) as Emd.
  pose proof (lib.Reusable.YG0n.am_wf _ _ _ _ (proj1 HAR)) as HWF.
  destruct (lib.Reusable.YG0d.ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
  assert (El1 : l1 = []).
  { destruct l1 as [|f l1']; [reflexivity|]. exfalso.
    rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
    pose proof (lib.Reusable.YCbq.sep_frames_pos rsegs B LAWS lyc Sc W memc mdc (cid, pos) (cid, pos) [] l1' l2 HAR
                  ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
    unfold lib.Reusable.YG0f.zdisjoint, lib.Reusable.YCbq.frame_rng in Hd. cbn [fst snd] in Hd.
    pose proof (lib.Reusable.YCbq.fs_frame_bytes_pos cid Hcid). lia. }
  subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
  assert (HAR' : lib.Reusable.YG0n.AR rsegs B lyc (lib.Reusable.YG01.stack_free_state cid pos Sc) W m1 mdc').
  { eapply (ASF lyc Sc W memc mdc m1 mdc' cid pos HAR Hin HF0).
    - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
      destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
      exact (proj1 (lib.Reusable.YCbq.awr_byte_cases rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
    - intros a Hv. eapply lib.Reusable.YCbq.aview_keeps_vis; [exact Hgr' | exact Hv].
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
    - intros a _ Hh. exact (Hhid _ Hh). }
  eapply (lib.Reusable.YCbq.ajournal_after_write rsegs B LAWS segs_low STK sp0 FP ly S0 W0 mem0 md0 ((cid, pos) :: own0)
            lyc Sc W memc mdc k m1 mdc' Wr (lib.Reusable.YG01.stack_free_state cid pos Sc) own0 HJ Heqw
            ltac:(intros a Ha; eapply lib.Reusable.YCbq.apresent_grows; [exact Hgr' | exact Ha]) Hsame).
  - intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  - exact HAR'.
  - unfold lib.Reusable.YG0d.ablocks. rewrite lib.Reusable.YG01.blocks_stack_free_state. reflexivity.
  - reflexivity.
  - cbn. lia.
  - etransitivity; [exact E2 | symmetry; exact E1].
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (lib.Reusable.YG01.qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
Qed.
End JournalFree.
