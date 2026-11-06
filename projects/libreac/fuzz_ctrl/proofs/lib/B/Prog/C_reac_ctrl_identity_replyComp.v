(* lib/B/Prog/C_reac_ctrl_identity_replyComp.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the composition of
   the stretches and events of pb_reac_ctrl_identity_reply (the cgif-form glue of reac_ctrl_identity_reply, 0x848fc), on
   the plan of record analyses/libreac/fuzz_ctrl/glue-B/identity_reply/pb_reac_ctrl_identity_reply.plan.md.

   Here: the JOURNAL STEP AFTER S-B (rrB_J_SB).  The stretch's post C_reac_ctrl_identity_replyPf.rrB_SBpost gives the
   real end state ms', related by MemNorm.ms_rel to an end state s0' of the normalized run (rrB_QSB over
   normalize rsegs mb), with mb's read-only bytes kept, the class-1 hint word [FS + 8, FS + 16) kept and the class-1
   flag byte [fs_flag FS 1 jj, fs_flag FS 1 jj + 1) kept.  The journal that held at the base memory mb is carried to
   ms_mem ms' by rrB_journal_gen with the write set
     rrB_WSB S G = [S - 9072, S) u [G, G + 128) u [shadow_addr G, shadow_addr G + 16),   G := fs_frame FS 1 jj
   (the window, the frame the class-1 request returned, that frame's 16 shadow bytes).  Both ends of rrB_QSB are
   covered: at reac_ctrl_parse's first slot the end memory is m5 (rBI's mc, then the 5 unpoison shadow bytes), at
   the -1 exit 0x84bdc it is rBI's mc itself.  rBI's own write list rWf also names the class-1 hint word and the
   class-1 flag byte, which the stretch does not write: both are allocator-owned and are not awr_bytes, so they stay
   out of the write set (unit decision 125's finding); rrB_SBpost keeps both.
   Every byte of the write set is an awr_byte: the window by the window arm (the window lies in [sp0 - STK, sp0)),
   the frame and its shadow by the in_frames arm (premise HFRAMES_C1). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_ctrl_identity_reply_c
  reac_ctrl_identity_replyRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YA0n YM05 YI16 YG0f YG0d YG0n YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP C_reac_ctrl_identity_replyLib.
(* rrB_SBpost and rrB_inH. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_reac_ctrl_identity_replyPf.
(* rrB_journal_gen (the journal across a lifted stretch) moved out of Pf into the shared GlueLift.v with its
   name and statement unchanged (a working branch aabcfc3744e, merged here as b9b1631c5b8). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import GlueLift.
Import ListNotations.
Open Scope Z_scope.

(* ---- The S-B stretch's own write set: the window, the frame G the class-1 request returned, that frame's 16
   shadow bytes.  NOT the class-1 hint word and NOT the class-1 flag byte (allocator-owned; the stretch does not
   write them).  rrB_journal_gen takes the write set as a predicate; this is the complement of Frame.outside over the
   three ranges, the predicate munch (and so rBI's rWf) uses. ---- *)
Definition rrB_WSB (S G : Z) : Z -> Prop :=
  fun a => ~ lib.Lib.Frame.outside [(S - 9072, S); (G, G + 128); (shadow_addr G, shadow_addr G + 16)] a.

Lemma rrB_in_dec : forall lo hi a : Z, lo <= a < hi \/ ~ (lo <= a < hi).
Proof.
  intros lo hi a. destruct (Z_lt_le_dec a lo) as [H1|H1]; [right; intros [H _]; lia|].
  destruct (Z_lt_le_dec a hi) as [H2|H2]; [left; lia | right; intros [_ H]; lia].
Qed.

Lemma rrB_WSB_iff : forall S G a, rrB_WSB S G a <->
  S - 9072 <= a < S \/ G <= a < G + 128 \/ shadow_addr G <= a < shadow_addr G + 16.
Proof.
  intros S G a. unfold rrB_WSB. cbn [lib.Lib.Frame.outside]. split.
  - intros H.
    destruct (rrB_in_dec (S - 9072) S a) as [A|A]; [left; exact A|].
    destruct (rrB_in_dec G (G + 128) a) as [C|C]; [right; left; exact C|].
    destruct (rrB_in_dec (shadow_addr G) (shadow_addr G + 16) a) as [D|D]; [right; right; exact D|].
    exfalso. apply H. split; [exact A|]. split; [exact C|]. split; [exact D | exact I].
  - intros [H|[H|H]] (H1 & H2 & H3 & _); contradiction.
Qed.

Lemma rrB_WSB_dec : forall S G a, rrB_WSB S G a \/ ~ rrB_WSB S G a.
Proof.
  intros S G a. destruct (rrB_WSB_iff S G a) as [I1 I2].
  destruct (rrB_in_dec (S - 9072) S a) as [A|A]; [left; apply I2; left; exact A|].
  destruct (rrB_in_dec G (G + 128) a) as [C|C]; [left; apply I2; right; left; exact C|].
  destruct (rrB_in_dec (shadow_addr G) (shadow_addr G + 16) a) as [D|D]; [left; apply I2; right; right; exact D|].
  right. intros H. apply I1 in H. destruct H as [H|[H|H]]; contradiction.
Qed.

Lemma rrB_WSB_out : forall S G a, ~ rrB_WSB S G a ->
  ~ (S - 9072 <= a < S) /\ ~ (G <= a < G + 128) /\ ~ (shadow_addr G <= a < shadow_addr G + 16).
Proof.
  intros S G a N. destruct (rrB_WSB_iff S G a) as [_ I2].
  split; [intros H; apply N, I2; left; exact H|].
  split; [intros H; apply N, I2; right; left; exact H|].
  intros H; apply N, I2; right; right; exact H.
Qed.

(* Off the read-only bytes, normalize does not change what mrd reads. *)
Lemma rrB_mrd_normalize : forall m x, lib.Lib.Mem.ro_addr rsegs x = false ->
  lib.Lib.Mem.mrd rsegs (B.MemNorm.normalize rsegs m) x = lib.Lib.Mem.mrd rsegs m x.
Proof. intros m x R. unfold lib.Lib.Mem.mrd, B.MemNorm.normalize. rewrite R. reflexivity. Qed.

Section Comp.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* The two Section premises of YCbq's Section a0 (YCbq.v:204-208), for B's bundle, as in
   C_reac_ctrl_identity_replyPf's Section Journal (rrB_journal_gen takes both).  segs_low: core, PENDING THE RECORD
   CORE (YCeg.v:25 refused name).  Its statement is Reusable.YCeg.tfib_segs_low (YCeg.v:64, stated and proved), but
   lib/Reusable/YCeg.v compiles on NO B base yet (line 25 names port_core_refused_103b0), so YCeg is NOT Required;
   when it compiles, segs_low := Reusable.YCeg.tfib_segs_low (tfibsegs = rsegs by ProgBridge.tfibsegs_rsegs). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.

(* ---- The journal after S-B.  The journal held at the base memory mb (the memory at the return 0x8497c of the
   class-1 request); after the lifted S-B stretch it holds at the real end memory ms_mem ms', at either end of the
   stretch.  The model step is the stretch's own (same_but_materialized mdc md').

   Obligation 2 (off the write set, the normalized end memory is normalize mb) is read off rBI and rrB_QSB:
     rBI.munch (rWf G jj 1) (normalize mb) mc   the run changed only the window, the hint word, the flag byte,
                                                 the frame and its 16 shadow bytes;
     rrB_QSB.munch [(G/8 + ASAN_K + 4, G/8 + ASAN_K + 9)] mc m5   (left end only) then only the 5 unpoison shadow
                                                 bytes, inside [shadow_addr G, shadow_addr G + 16);
     rrB_SBpost's hint keep                      the hint word [FS + 8, FS + 16) is normalize mb's;
     rrB_SBpost's flag keep                      the flag byte is normalize mb's.
   The readability of the write set at the end comes from its readability at mb (the window: the journal's own
   presence clause; the frame and its shadow: H_fr_stk, H_fr_shadow), moved to normalize mb above IMG_HI and along
   rBI.rr_rd_mono (normalize mb) mc and, at the left end, rrB_QSB.rr_rd_mono mc m5. ---- *)
Lemma rrB_J_SB :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (W : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) (mdc : Model) k
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fr len pa pp pn S FS : Z) (g : list byte) (jj : Z) (ms' : machine_state) (md' : Model),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W mb mdc k ->
    rrB_SBpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g jj W mdc ms' md' ->
    (* the window lies in the journal's stack range *)
    sp0 - STK <= S - 9072 -> S <= sp0 ->
    forall
    (* The frame facts at the base memory mb: the stk, shadow-zero and ASAN_GT conjuncts of
       B.ProgWorldAstack.ctl_fs_of_astack's conclusion at cid 1 (mem' := mb, fr := G, n := fs_B 1 = 128), the same
       conclusion that supplies rrB_SB_lifted's frame premises at mb (G + 120 and the flag byte).  The lead (a Theorem Labs lane)
       discharges them at the composition: ctl_fs_of_astack is applicable from fd812f73bc3 (rrB_E1 through
       lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc), with its own premises 0 <= cid <= 6, the [lo, spZ - ESTACK)
       range and presence, 1 <= L <= fs_frame_bytes 1, ctl_fs_geom_stmt and AR_laws taken there.  This lemma takes
       the conclusion conjuncts only, so it needs none of those premises itself. *)
    (H_fr_stk : lib.Lib.Frame.stk rsegs mb (fs_frame FS 1 jj) (fs_frame FS 1 jj + 128))
    (H_fr_shadow : lib.Lib.Mem.bytes_at rsegs mb (shadow_addr (fs_frame FS 1 jj)) (repeat (Z_to_bv 8 0) 16))
    (H_fr_gt : ASAN_GT <= fs_frame FS 1 jj)
    (* every byte of the frame G and of its 16 shadow bytes is an awr_byte (the in_frames arm, frame (1, jj)) *)
    (* OWNER PENDING: the lead (a Theorem Labs lane) discharges it at the composition; B.ProgWorldAstack.ctl_fs_of_astack is
       applicable from fd812f73bc3 (rrB_E1 re-proved through lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc) *)
    (HFRAMES_C1 : forall a,
       fs_frame FS 1 jj <= a < fs_frame FS 1 jj + 128 \/
       shadow_addr (fs_frame FS 1 jj) <= a < shadow_addr (fs_frame FS 1 jj) + 16 ->
       lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
         (lib.Reusable.YG0d.ablocks B lyc Sc) lyc own a),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W mb mdc k ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    fr len pa pp pn S FS g jj ms' md' HJ ((s0' & HQ & HREL & HROS & HKH & HKFL) & Hhid & Hsame) Hlo Hhi
    H_fr_stk H_fr_shadow H_fr_gt HFRAMES_C1.
  unfold rrB_QSB, rBI, rWf in HQ.
  set (G := fs_frame FS 1 jj) in *.
  (* the window: above alloc_ceiling (astk_ok) and present at mb (the journal's presence clause) *)
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR & HAS & _).
  destruct HAS as (_ & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as [Hceil _].
  assert (HW : 0x5fe000 + 9072 <= S <= 2 ^ 47) by lia.
  destruct H_fr_stk as (Hg0 & Hg1 & Hgrd).
  destruct H_fr_shadow as (_ & _ & Hsrd).
  assert (HDIV : 0 <= G / 8 /\ 8 * (G / 8) <= G) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
  (* every byte of the write set lies above IMG_HI *)
  assert (HIMG : forall a, rrB_WSB S G a -> ImgBounds.IMG_HI <= a < 2 ^ 64).
  { intros a Ha. apply rrB_WSB_iff in Ha. unfold shadow_addr, ASAN_K in Ha. unfold ASAN_GT in H_fr_gt.
    unfold ImgBounds.IMG_HI. lia. }
  (* every byte of the write set is readable at mb, so at normalize mb *)
  assert (HRDb : forall a, rrB_WSB S G a -> exists b, lib.Lib.Mem.mrd rsegs mb (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. apply rrB_WSB_iff in Ha. destruct Ha as [Ha|[Ha|Ha]].
    - destruct (HPR a ltac:(lia)) as [_ [b Eb]]. exists b.
      unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Eb. reflexivity.
    - exact (proj2 (Hgrd a Ha)).
    - assert (Ea : shadow_addr G + Z.of_nat (Z.to_nat (a - shadow_addr G)) = a) by (rewrite Z2Nat.id; lia).
      rewrite <- Ea.
      rewrite (Hsrd (Z.to_nat (a - shadow_addr G))) by (rewrite repeat_length; lia).
      destruct (nth_error (repeat (Z_to_bv 8 0) 16) (Z.to_nat (a - shadow_addr G))) as [b|] eqn:E;
        [exists b; reflexivity|].
      exfalso. apply nth_error_None in E. rewrite repeat_length in E. lia. }
  assert (HRDn : forall a, rrB_WSB S G a ->
            exists b, lib.Lib.Mem.mrd rsegs (B.MemNorm.normalize rsegs mb) (lib.Lib.Mem.wa a) = Some b).
  { intros a Ha. rewrite rrB_mrd_normalize; [exact (HRDb a Ha)|].
    apply B.MemNormTr.ro_addr_above_img. exact (HIMG a Ha). }
  (* the two ends of the run: off the write set, the hint word and the flag byte, the normalized end memory is
     normalize mb (rBI.munch, then the left end's 5-byte shadow munch); readability moves along rr_rd_mono *)
  assert (KR : (forall x : word, ~ rrB_WSB S G (bv_unsigned x) -> ~ (FS + 8 <= bv_unsigned x < FS + 16) ->
                  ~ (fs_flag FS 1 jj <= bv_unsigned x < fs_flag FS 1 jj + 1) ->
                  ms_mem s0' x = B.MemNorm.normalize rsegs mb x) /\
               (forall x : word, (exists b, lib.Lib.Mem.mrd rsegs (B.MemNorm.normalize rsegs mb) x = Some b) ->
                  exists b, lib.Lib.Mem.mrd rsegs (ms_mem s0') x = Some b)).
  { assert (Ehint : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
    destruct HQ as [(mc & m5 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 &
                     Es & (MUf & _ & RMf & _) & _ & MU5 & _ & RM5 & _) |
                    (mc & r & y1 & y2 & y5 & y6 & y7 & y9 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 &
                     y21 & y22 & y23 & y24 & y27 & y28 & y29 & y30 & y31 & Es & (MUf & _ & RMf & _) & _)];
      rewrite Es; cbn [lib.Lib.MState.MS ms_mem].
    - split.
      + intros x N1 N2 N3. destruct (rrB_WSB_out _ _ _ N1) as (W1 & W2 & W3).
        rewrite (MU5 x).
        * apply MUf. cbn [lib.Lib.Frame.outside]. rewrite Ehint. repeat split; lia.
        * cbn [lib.Lib.Frame.outside]. unfold shadow_addr in W3. split; [lia | exact I].
      + intros x Hx. apply RM5, RMf, Hx.
    - split.
      + intros x N1 N2 N3. destruct (rrB_WSB_out _ _ _ N1) as (W1 & W2 & W3).
        apply MUf. cbn [lib.Lib.Frame.outside]. rewrite Ehint. repeat split; lia.
      + intros x Hx. apply RMf, Hx. }
  destruct KR as [KEY READ].
  destruct HREL as (_ & _ & _ & _ & _ & _ & _ & HMR).
  apply (rrB_journal_gen B LAWS segs_low STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W mb mdc k
           (ms_mem ms') (ms_mem s0') md' (rrB_WSB S G) HJ).
  - (* each written byte is an awr_byte: the window arm, or the in_frames arm for the frame and its shadow *)
    intros a Ha. apply rrB_WSB_iff in Ha. destruct Ha as [Ha|Ha].
    + left. lia.
    + exact (HFRAMES_C1 a Ha).
  - exact HIMG.
  - intros a. exact (rrB_WSB_dec S G a).
  - (* off the write set the normalized end memory is normalize mb *)
    intros x Hx.
    destruct (rrB_in_dec (FS + 8) (FS + 16) (bv_unsigned x)) as [Hh|Hh].
    { apply HKH. unfold rrB_inH. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    destruct (rrB_in_dec (fs_flag FS 1 jj) (fs_flag FS 1 jj + 1) (bv_unsigned x)) as [Hf|Hf].
    { apply HKFL. unfold rrB_inH. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    exact (KEY x Hx Hh Hf).
  - intros a Ha. exact (READ _ (HRDn a Ha)).
  - exact HMR.
  - exact HROS.
  - exact Hhid.
  - exact Hsame.
Qed.
End Comp.
