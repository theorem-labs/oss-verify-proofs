(* settle_seg_runs: the model facts and the footprint runs (lib/Lib/ExecF.v evtF, stepped with lib/Lib/StepF.v) that
   the image-A caller-journal walk of settle (lib/A/Prog/settle_cgW.v) carries into SRr. Image A =
   fuzz_transport.asan e89be137db17, entry 0x83cac, 21 words; listing lib/A/Prog/DgnTransportList.v (the words after
   AF_settle).

   - settle_model: settle_m Bw ticked = Some (Bw', tt) gives each check's model premise at Bw (each check returns the
     world it was given) and the two branches of the code: g_raw Bw <> 0 and Bw' = Bw; or g_raw Bw = 0,
     check_latest_queue_m Bw = Some (Bw, tt), and ticked = 0 with Bw' = Bw, or ticked <> 0 with
     check_latest_drain_m Bw = Some (Bw', tt) and Bw' = Bw. No injection on a world-carrying option: settle_same_some
     reads the world out of the Some.
   - settle_run1_F, from the entry to the entry of check_ack_settle:
       0x83cac - 0x83cb4  sp = sp - 16; the 8-byte stores of ra and s0 at sp + 8 and sp + 0 (the frame);
       0x83cb8            s0 = a0 (ticked);
       0x83cbc            jal check_ack_settle (ra = 0x83cc0).
     The two stores write only the frame; the frame lies above the hull of the harness globals, so the world relation
     holds at the new memory with the same Bw (TWorldAKept.v csw_kept).
   - settle_jal2_F, settle_jal3_F, settle_jal4_F: the calls at 0x83cc0 (check_state_settle, ra = 0x83cc4), 0x83cc4
     (check_inflight_settle, ra = 0x83cc8) and 0x83cc8 (check_keepalive_settle, ra = 0x83ccc). Each changes ra only.
   - settle_run5_F, from 0x83ccc: a0 = the 4-byte signed load of g_raw (pc-relative, 0x5df0e0; no instrumented
     check); g_raw <> 0: ra and s0 loaded back from the frame, sp = sp + 16, ret; g_raw = 0: jal check_latest_queue
     (0x83ce8, ra = 0x83cec).
   - settle_run6_F, from 0x83cec: beqz s0 (s0 = ticked); ticked = 0: the return of 0x83cd8 - 0x83ce4; else ra and s0
     loaded back, sp = sp + 16, j check_latest_drain (0x83cfc, no link): the state at check_latest_drain's entry is
     settle's own entry state (ra, sp, s0) with the other registers as the run leaves them.
   None of runs 2 - 6 stores a byte. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c TWorldAKept.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The entry, the return addresses of the five calls, and the entries of the six callees (the tail jump's target
   last). *)
Definition SETTLE_ENTRY : Z := 0x83cac.
Definition SETTLE_R1 : Z := 0x83cc0.
Definition SETTLE_R2 : Z := 0x83cc4.
Definition SETTLE_R3 : Z := 0x83cc8.
Definition SETTLE_R4 : Z := 0x83ccc.
Definition SETTLE_R5 : Z := 0x83cec.
Definition SETTLE_CAS : Z := 0x85b04.
Definition SETTLE_CSS : Z := 0x85b34.
Definition SETTLE_CIS : Z := 0x85d50.
Definition SETTLE_CKS : Z := 0x85e14.
Definition SETTLE_CLQ : Z := 0x85e70.
Definition SETTLE_CLD : Z := 0x85fdc.

(* ---- the model ---- *)

(* The world out of a Some, without an injection on the world-carrying option. *)
Lemma settle_same_some : forall (B B1 : list byte) (u : unit), Some (B, tt) = Some (B1, u) -> B1 = B.
Proof.
  intros B B1 u H.
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) H) as HB.
  cbv beta iota in HB. symmetry. exact HB.
Qed.

(* Each check's model is a chain of tests ending in None or Some (B, tt): its world is the world it was given. *)
Ltac settle_same H :=
  cbv zeta in H;
  repeat first
    [ discriminate H
    | lazymatch type of H with
      | context [match ?x with Some _ => _ | None => _ end] => destruct x
      | context [if ?c then _ else _] => destruct c
      | context [TC.state_settle_loop ?f ?b ?i ?s ?w] => destruct (TC.state_settle_loop f b i s w)
      end ];
  exact (settle_same_some _ _ _ H).

Lemma settle_cas_same : forall B B1 u, TC.check_ack_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_ack_settle_m in H. settle_same H. Qed.
Lemma settle_css_same : forall B B1 u, TC.check_state_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_state_settle_m in H. settle_same H. Qed.
Lemma settle_cis_same : forall B B1 u, TC.check_inflight_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_inflight_settle_m in H. settle_same H. Qed.
Lemma settle_cks_same : forall B B1 u, TC.check_keepalive_settle_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_keepalive_settle_m in H. settle_same H. Qed.
Lemma settle_clq_same : forall B B1 u, TC.check_latest_queue_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_latest_queue_m in H. settle_same H. Qed.
Lemma settle_cld_same : forall B B1 u, TC.check_latest_drain_m B = Some (B1, u) -> B1 = B.
Proof. intros B B1 u H. unfold TC.check_latest_drain_m in H. settle_same H. Qed.

Lemma settle_model : forall B B' ticked,
  TC.settle_m B ticked = Some (B', tt) ->
  TC.check_ack_settle_m B = Some (B, tt) /\ TC.check_state_settle_m B = Some (B, tt) /\
  TC.check_inflight_settle_m B = Some (B, tt) /\ TC.check_keepalive_settle_m B = Some (B, tt) /\
  ((TW.g_raw B <> 0 /\ B' = B) \/
   (TW.g_raw B = 0 /\ TC.check_latest_queue_m B = Some (B, tt) /\
    ((ticked = 0 /\ B' = B) \/ (ticked <> 0 /\ TC.check_latest_drain_m B = Some (B', tt) /\ B' = B)))).
Proof.
  intros B B' ticked H. unfold TC.settle_m in H.
  destruct (TC.check_ack_settle_m B) as [[B1 u1]|] eqn:E1; cbv beta iota in H; [|discriminate H].
  pose proof (settle_cas_same _ _ _ E1) as X1. subst B1. destruct u1.
  destruct (TC.check_state_settle_m B) as [[B2 u2]|] eqn:E2; cbv beta iota in H; [|discriminate H].
  pose proof (settle_css_same _ _ _ E2) as X2. subst B2. destruct u2.
  destruct (TC.check_inflight_settle_m B) as [[B3 u3]|] eqn:E3; cbv beta iota in H; [|discriminate H].
  pose proof (settle_cis_same _ _ _ E3) as X3. subst B3. destruct u3.
  destruct (TC.check_keepalive_settle_m B) as [[B4 u4]|] eqn:E4; cbv beta iota in H; [|discriminate H].
  pose proof (settle_cks_same _ _ _ E4) as X4. subst B4. destruct u4.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  destruct (Z.eq_dec (TW.g_raw B) 0) as [G0|G0].
  - right. split; [exact G0|].
    assert (T0 : TC.truth (TW.g_raw B) = false) by (unfold TC.truth; rewrite G0; reflexivity).
    rewrite T0 in H. cbv beta iota delta [negb] in H.
    destruct (TC.check_latest_queue_m B) as [[B5 u5]|] eqn:E5; cbv beta iota in H; [|discriminate H].
    pose proof (settle_clq_same _ _ _ E5) as X5. subst B5. destruct u5.
    split; [reflexivity|].
    destruct (Z.eq_dec ticked 0) as [K0|K0].
    + left. split; [exact K0|].
      assert (TK : TC.truth ticked = false) by (unfold TC.truth; rewrite K0; reflexivity).
      rewrite TK in H. cbv beta iota in H. exact (settle_same_some _ _ _ H).
    + right. split; [exact K0|].
      assert (TK : TC.truth ticked = true) by (unfold TC.truth; apply negb_true_iff, Z.eqb_neq; exact K0).
      rewrite TK in H. cbv beta iota in H. split; [exact H|]. exact (settle_cld_same _ _ _ H).
  - left. split; [exact G0|].
    assert (T1 : TC.truth (TW.g_raw B) = true) by (unfold TC.truth; apply negb_true_iff, Z.eqb_neq; exact G0).
    rewrite T1 in H. cbv beta iota delta [negb] in H. exact (settle_same_some _ _ _ H).
Qed.

(* ---- the read of g_raw and the branch conditions ---- *)

(* A load of c bytes at b + k inside ONE payload row of a world table T reads sub Bw (o + k) c (the load step's read
   fact). *)
Lemma settle_rdf : forall segs T (m : word -> option byte) Bw o b n k (c : nat),
  tw_ok T ->
  tw_at T (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m (wa a))) Bw ->
  In (o, b, n) T -> 0 <= k -> k + Z.of_nat c <= n ->
  ov_read_bytes segs m (wa (b + k)) c = Some (TW.sub Bw (o + k) c).
Proof.
  intros segs T m Bw o b n k c Hok HW Hin Hk Hkc.
  pose proof (tw_row T o b n Hok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  assert (L : length (TW.sub Bw (o + k) c) = c).
  { apply TWorldLemmas.length_sub; [lia|]. rewrite (tw_len T _ Bw HW). unfold TW.W_LEN in *. lia. }
  pose proof (tw_bytes_at segs m T Bw o b n k c Hok HW Hin Hk Hkc) as BF.
  replace (wa (b + k)) with (wa (b + k + 0)) by (f_equal; lia).
  rewrite (bytes_at_read segs m (b + k) _ 0 c BF ltac:(lia)) by (rewrite L; lia).
  cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L. lia.
Qed.

(* The load of g_raw (0x5df0e0) at a memory m that holds the world. *)
Lemma settle_raw_read : forall (m : word -> option byte) Bw,
  tw_at TMAP_A (csw_view m) Bw ->
  ov_read_bytes rsegs m (wa 6156512) 4 = Some (TW.sub Bw TW.OFF_g_raw 4).
Proof.
  intros m Bw HW. unfold csw_view in HW.
  exact (settle_rdf rsegs TMAP_A m Bw TW.OFF_g_raw TA_g_raw TW.SZ_g_raw 0 4 TMAP_A_ok HW TMAP_A_g_raw
           ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia)).
Qed.

(* A branch condition over 64-bit words of Z values, decided by the Z facts in the context. *)
Ltac settle_cond :=
  unfold bv_ltu, bv_eqb; rewrite ?unsigned_lit_wrap;
  lazymatch goal with
  | |- negb _ = false => apply Bool.negb_false_iff
  | |- negb _ = true => apply Bool.negb_true_iff
  | _ => idtac
  end;
  lazymatch goal with
  | |- (_ <? _) = true => apply Z.ltb_lt
  | |- (_ <? _) = false => apply Z.ltb_ge
  | |- (_ =? _) = true => apply Z.eqb_eq
  | |- (_ =? _) = false => apply Z.eqb_neq
  end;
  Z.div_mod_to_equations; lia.
Ltac settle_br b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; settle_cond]
  end.

(* ---- run 1: from the entry to the entry of check_ack_settle ---- *)

(* What the run leaves at check_ack_settle's entry: ra = 0x83cc0, sp the entry sp less 16, s0 = a0, every other
   register the entry's; the frame written with s0 and ra (in address order); every byte outside the frame
   unchanged; the world relation at the new memory. *)
Definition settle_post1 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (ms' : machine_state) : Prop :=
  exists (s0' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 SETTLE_R1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0' s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 SETTLE_CAS) fc None m' (seg_rom rsegs) /\
    s0' = a0 /\
    munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra] /\
    tw_at TMAP_A (csw_view m') Bw.

Lemma settle_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    TG.G_HARNESS_HI <= bv_unsigned sp - 16 ->
    ExecF.rng RNG (bv_unsigned sp - 16) 16 ->
    ExecF.evtF rsegs RNG
      (settle_post1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw HW ST HLO HOFF RFR.
  unfold SETTLE_ENTRY.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold TG.G_HARNESS_HI in HOFF.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x83cac - 0x83cb4: the frame and the two saves; 0x83cb8: s0 = a0; 0x83cbc: the call *)
  step. step. step. step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  apply evtF_done. unfold settle_post1. eexists. exists m0.
  split; [reflexivity|].
  split; [first [reflexivity | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned]|].
  split; [exact MU1|]. split; [exact WM|]. split; [exact FR|].
  apply (csw_kept m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.

(* ---- runs 2 - 4: the calls of check_state_settle, check_inflight_settle and check_keepalive_settle ---- *)

Lemma settle_jal2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 SETTLE_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 SETTLE_CSS) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R1) fc None m (seg_rom rsegs)).
Proof. intros. unfold SETTLE_R1. step. apply evtF_done. reflexivity. Qed.

Lemma settle_jal3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 SETTLE_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 SETTLE_CIS) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R2) fc None m (seg_rom rsegs)).
Proof. intros. unfold SETTLE_R2. step. apply evtF_done. reflexivity. Qed.

Lemma settle_jal4_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 SETTLE_R4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 SETTLE_CKS) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R3) fc None m (seg_rom rsegs)).
Proof. intros. unfold SETTLE_R3. step. apply evtF_done. reflexivity. Qed.

(* ---- run 5: g_raw, then the return or the call of check_latest_queue ---- *)

Lemma settle_run5_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (vra vs0 : word),
    tw_at TMAP_A (csw_view m) Bw ->
    0 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 vs0; C8 vra] ->
    ExecF.rng RNG (bv_unsigned sp) 16 -> ExecF.rng RNG 6156512 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (TW.g_raw Bw <> 0 /\ exists a0' : word,
            ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 vs0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc vra) fc None m (seg_rom rsegs)) \/
         (TW.g_raw Bw = 0 /\ exists a0' : word,
            ms' = MS (mkR (Z_to_bv 64 SETTLE_R5) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 SETTLE_CLQ) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Bw vra vs0 HW Hsp0 Hsp1 FR RFR RRAW.
  unfold SETTLE_R4.
  pose proof (settle_raw_read m Bw HW) as RD.
  pose proof (TWorldLemmas.s32_range Bw TW.OFF_g_raw) as RG.
  (* 0x83ccc - 0x83cd0: a0 = g_raw *)
  step. step.
  rewrite ?lw_world. change (TW.s32_at Bw TW.OFF_g_raw) with (TW.g_raw Bw) in *.
  (* 0x83cd4: beqz a0 *)
  step.
  destruct (Z.eq_dec (TW.g_raw Bw) 0) as [G0|G0].
  - settle_br true.
    (* 0x83ce8: the call of check_latest_queue *)
    step.
    apply evtF_done. right. split; [exact G0|]. eexists. reflexivity.
  - settle_br false.
    (* 0x83cd8 - 0x83ce4: ra and s0 loaded back, sp = sp + 16, ret *)
    step. step. step. step.
    apply evtF_done. left. split; [exact G0|]. eexists. reflexivity.
Qed.

(* ---- run 6: s0 = ticked, then the return or the tail jump to check_latest_drain ---- *)

Lemma settle_run6_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ticked : Z) (vra vs0 : word),
    -2 ^ 31 <= ticked < 2 ^ 31 ->
    0 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 vs0; C8 vra] ->
    ExecF.rng RNG (bv_unsigned sp) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (ticked = 0 /\
          ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 vs0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc vra) fc None m (seg_rom rsegs)) \/
         (ticked <> 0 /\
          ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 vs0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 SETTLE_CLD) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 ticked) s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SETTLE_R5) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ticked vra vs0 Htk Hsp0 Hsp1 FR RFR.
  unfold SETTLE_R5.
  (* 0x83cec: beqz s0 *)
  step.
  destruct (Z.eq_dec ticked 0) as [K0|K0].
  - settle_br true.
    (* 0x83cd8 - 0x83ce4: ra and s0 loaded back, sp = sp + 16, ret *)
    step. step. step. step.
    apply evtF_done. left. split; [exact K0 | reflexivity].
  - settle_br false.
    (* 0x83cf0 - 0x83cfc: ra and s0 loaded back, sp = sp + 16, j check_latest_drain *)
    step. step. step. step.
    apply evtF_done. right. split; [exact K0 | reflexivity].
Qed.
