(* check_inflight_settle_seg_runs: the model facts and the two footprint runs (lib/Lib/ExecF.v evtF, stepped with
   lib/Lib/StepF.v) that the image-A caller-journal walk of check_inflight_settle (lib/A/Prog/check_inflight_settle_cgW.v)
   carries into SRr. Image A = fuzz_transport.asan e89be137db17, entry 0x85d50, 49 words; listing
   lib/A/Prog/DgnTransportList.v (the words after AF_check_inflight_settle).

   - cis_model: check_inflight_settle_m Bw = Some (Bw', tt) gives Bw' = Bw and the facts each trap test of the code
     needs (lib/Prog/T/check_inflight_settle.v cis_m_facts, without an injection on the world-carrying option).
   - cis_run1_F, from the entry to the entry of diginet_session_deadline:
       0x85d50 - 0x85d60  sp = sp - 32; the 8-byte stores of ra, s0, s1, s2 at sp + 24, 16, 8, 0 (the frame);
       0x85d64 - 0x85d74  a0 = GOT.acked, a1 = OW.acked (4-byte loads); bne a0, a1 to the trap: not taken;
       0x85d78 - 0x85d8c  s0 = &M; a0 = M.fly_on; s2 = g_now - 0x37c, s1 = g_cfg - 0x314; beqz a0 to 0x85dac;
       0x85d90 - 0x85da8  a0 = g_now - M.fly_sent, a1 = ack_timeout_ms * 1000; bgeu a0, a1 to the trap: not taken;
       0x85dac - 0x85db8  a1 = g_now, a0 = &g_s, jal diginet_session_deadline (ra = 0x85dbc).
     The four stores write only the frame; the frame lies above the hull of the harness globals, so the world relation
     holds at every memory of the run with the same Bw (TWorldA.v TMAP_A_kept), and each world load reads the model's
     bytes (cis_rdf, TWorldG.v tw_bytes_at).
   - cis_run2_F, from the return address 0x85dbc to the `ret`:
       0x85dbc - 0x85dd0  a1 = g_now; bltu a0, a1 to the trap: not taken (g_now <= d); a2 = 1000000;
                          a1 = g_now + 1000000; bltu a1, a0 to the trap: not taken;
       0x85dd4 - 0x85dd8  a1 = M.fly_on; beqz a1 to 0x85df4;
       0x85ddc - 0x85df0  a1 = ack_timeout_ms * 1000 + M.fly_sent; bltu a1, a0 to the trap: not taken;
       0x85df4 - 0x85e08  ra, s0, s1, s2 loaded back from the frame; sp = sp + 32; ret.
     It stores nothing.
   The trap block (0x85e0c, 0x85e10) is never reached: every branch to it is decided by the model facts. *)
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
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.

(* The entry, the return address of the call, the callee's entry, and the values the run leaves in s0, s1, s2 (the
   base of M; g_cfg - 0x314 and g_now - 0x37c, the auipc results the loads at +0x314 / +0x37c use) and in a0 at the
   call (the base of g_s). *)
Definition CIS_ENTRY : Z := 0x85d50.
Definition CIS_RET : Z := 0x85dbc.
Definition CIS_CALLEE : Z := 0x8a9d4.
Definition CIS_M : Z := 0x5df160.
Definition CIS_S1 : Z := 0x5ded88.
Definition CIS_S2 : Z := 0x5ded84.
Definition CIS_GS : Z := 0x5df9c0.

(* ---- the model ---- *)

Lemma cis_model : forall B B',
  TC.check_inflight_settle_m B = Some (B', tt) ->
  B' = B /\ TW.GOT_acked B = TW.OW_acked B /\
  (TW.M_fly_on B <> 0 -> TS0.u64 (TW.g_now B - TW.M_fly_sent B) < TC.h_ms_m (TW.Cfg_ack_timeout_ms B)) /\
  exists d, TS0.diginet_session_deadline_m B (TW.g_now B) = Some d /\
    TW.g_now B <= d /\ d <= TS0.u64 (TW.g_now B + 1000000) /\
    (TW.M_fly_on B <> 0 -> d <= TS0.u64 (TW.M_fly_sent B + TC.h_ms_m (TW.Cfg_ack_timeout_ms B))).
Proof.
  intros B B' H. unfold TC.check_inflight_settle_m in H.
  destruct (Z.eqb_spec (TW.GOT_acked B) (TW.OW_acked B)) as [E1|E1]; cbv beta iota delta [negb] in H;
    [|discriminate H].
  destruct (TC.truth (TW.M_fly_on B) && (TC.h_ms_m (TW.Cfg_ack_timeout_ms B) <=? TS0.u64 (TW.g_now B - TW.M_fly_sent B)))
    eqn:E2; cbv beta iota in H; [discriminate H|].
  destruct (TS0.diginet_session_deadline_m B (TW.g_now B)) as [d|] eqn:Ed; cbv beta iota in H; [|discriminate H].
  destruct ((d <? TW.g_now B) || (TS0.u64 (TW.g_now B + 1000000) <? d)) eqn:E3; cbv beta iota in H;
    [discriminate H|].
  destruct (TC.truth (TW.M_fly_on B) && (TS0.u64 (TW.M_fly_sent B + TC.h_ms_m (TW.Cfg_ack_timeout_ms B)) <? d)) eqn:E4;
    cbv beta iota in H; [discriminate H|].
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) H) as HB.
  cbv beta iota in HB.
  apply Bool.orb_false_iff in E3 as [E3a E3b]. apply Z.ltb_ge in E3a. apply Z.ltb_ge in E3b.
  split; [symmetry; exact HB|]. split; [exact E1|]. split.
  - intros N. apply Bool.andb_false_iff in E2 as [E2|E2].
    + unfold TC.truth in E2. apply Bool.negb_false_iff, Z.eqb_eq in E2. contradiction.
    + apply Z.leb_gt in E2. exact E2.
  - exists d. split; [reflexivity|]. split; [exact E3a|]. split; [exact E3b|].
    intros N. apply Bool.andb_false_iff in E4 as [E4|E4].
    + unfold TC.truth in E4. apply Bool.negb_false_iff, Z.eqb_eq in E4. contradiction.
    + apply Z.ltb_ge in E4. exact E4.
Qed.

(* ---- the reads and the branch conditions ---- *)

(* A load of c bytes at b + k inside ONE payload row of a world table T reads sub Bw (o + k) c, as the load step's
   read fact (check_keepalive_settle_F.v ckk_rdf). *)
Lemma cis_rdf : forall segs T (m : word -> option byte) Bw o b n k (c : nat),
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

(* The six world fields the code reads, as the load steps' read facts at a memory m that holds the world. *)
Lemma cis_reads : forall (m : word -> option byte) Bw,
  tw_at TMAP_A (csw_view m) Bw ->
  ov_read_bytes rsegs m (wa 6181816) 4 = Some (TW.sub Bw TW.A_GOT_acked 4) /\
  ov_read_bytes rsegs m (wa 6238520) 4 = Some (TW.sub Bw TW.A_OW_acked 4) /\
  ov_read_bytes rsegs m (wa 6156736) 4 = Some (TW.sub Bw TW.A_M_fly_on 4) /\
  ov_read_bytes rsegs m (wa 6156544) 8 = Some (TW.sub Bw TW.OFF_g_now 8) /\
  ov_read_bytes rsegs m (wa 6156752) 8 = Some (TW.sub Bw TW.A_M_fly_sent 8) /\
  ov_read_bytes rsegs m (wa 6156444) 4 = Some (TW.sub Bw TW.A_Cfg_ack_timeout_ms 4).
Proof.
  intros m Bw HW. unfold csw_view in HW.
  split; [exact (cis_rdf rsegs TMAP_A m Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 216 4 TMAP_A_ok HW TMAP_A_GOT
                   ltac:(lia) ltac:(unfold TW.SZ_GOT; lia))|].
  split; [exact (cis_rdf rsegs TMAP_A m Bw TW.OFF_OW TA_OW TW.SZ_OW 216 4 TMAP_A_ok HW TMAP_A_OW
                   ltac:(lia) ltac:(unfold TW.SZ_OW; lia))|].
  split; [exact (cis_rdf rsegs TMAP_A m Bw TW.OFF_M TA_M TW.SZ_M 96 4 TMAP_A_ok HW TMAP_A_M
                   ltac:(lia) ltac:(unfold TW.SZ_M; lia))|].
  split; [exact (cis_rdf rsegs TMAP_A m Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok HW TMAP_A_g_now
                   ltac:(lia) ltac:(unfold TW.SZ_g_now; lia))|].
  split; [exact (cis_rdf rsegs TMAP_A m Bw TW.OFF_M TA_M TW.SZ_M 112 8 TMAP_A_ok HW TMAP_A_M
                   ltac:(lia) ltac:(unfold TW.SZ_M; lia))|].
  exact (cis_rdf rsegs TMAP_A m Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 28 4 TMAP_A_ok HW TMAP_A_g_cfg
           ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
Qed.

(* The ranges of the six fields' values. *)
Lemma cis_ranges : forall Bw,
  -2^31 <= TW.GOT_acked Bw < 2^31 /\ -2^31 <= TW.OW_acked Bw < 2^31 /\ -2^31 <= TW.M_fly_on Bw < 2^31 /\
  0 <= TW.g_now Bw < 2^64 /\ 0 <= TW.M_fly_sent Bw < 2^64 /\ 0 <= TW.Cfg_ack_timeout_ms Bw < 2^32.
Proof.
  intros Bw.
  pose proof (TWorldLemmas.s32_range Bw TW.A_GOT_acked) as R1.
  pose proof (TWorldLemmas.s32_range Bw TW.A_OW_acked) as R2.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_fly_on) as R3.
  pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_now 8) as R4.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_fly_sent 8) as R5.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_Cfg_ack_timeout_ms 4) as R6.
  change (8 * Z.of_nat 8) with 64 in R4, R5. change (8 * Z.of_nat 4) with 32 in R6.
  unfold TW.GOT_acked, TW.OW_acked, TW.M_fly_on, TW.g_now, TW.M_fly_sent, TW.Cfg_ack_timeout_ms.
  repeat split; lia.
Qed.

(* A branch condition over 64-bit words of Z values, decided by the Z facts in the context. *)
Ltac cis_cond :=
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
Ltac cis_br b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; cis_cond]
  end.

(* The world loads leave TWorld's accessors (TWorldG.v lw_world / ld_world / lwu_world). *)
Ltac cis_fields Bw :=
  rewrite ?lw_world, ?ld_world, ?lwu_world;
  try change (TW.s32_at Bw TW.A_GOT_acked) with (TW.GOT_acked Bw);
  try change (TW.s32_at Bw TW.A_OW_acked) with (TW.OW_acked Bw);
  try change (TW.s32_at Bw TW.A_M_fly_on) with (TW.M_fly_on Bw);
  try change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw);
  try change (TW.u_at Bw TW.A_M_fly_sent 8) with (TW.M_fly_sent Bw);
  try change (TW.u_at Bw TW.A_Cfg_ack_timeout_ms 4) with (TW.Cfg_ack_timeout_ms Bw).

(* ---- the run from the entry to the call ---- *)

(* What the run leaves at the callee's entry: ra the call's return address, sp the entry sp less the frame, s0 / s1 /
   s2 the three bases, a0 = &g_s, a1 = g_now, a2 unknown, every other register the entry's; the frame written with
   s2, s1, s0, ra (in address order); every byte outside the frame unchanged; the world relation at the new memory. *)
Definition cis_post1 (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (ms' : machine_state) : Prop :=
  exists (a2' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 CIS_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2
                  (Z_to_bv 64 CIS_M) (Z_to_bv 64 CIS_S1) (Z_to_bv 64 CIS_GS) (Z_to_bv 64 (TW.g_now Bw))
                  a2' a3 a4 a5 a6 a7 (Z_to_bv 64 CIS_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CIS_CALLEE) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
    tw_at TMAP_A (csw_view m') Bw.

Lemma cis_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_A (csw_view m) Bw ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    TG.G_HARNESS_HI <= bv_unsigned sp - 32 ->
    TW.GOT_acked Bw = TW.OW_acked Bw ->
    (TW.M_fly_on Bw <> 0 ->
     (TW.g_now Bw - TW.M_fly_sent Bw) mod 2 ^ 64 < (TW.Cfg_ack_timeout_ms Bw * 1000) mod 2 ^ 64) ->
    ExecF.rng RNG (bv_unsigned sp - 32) 32 ->
    ExecF.rng RNG 6181816 4 -> ExecF.rng RNG 6238520 4 -> ExecF.rng RNG 6156736 4 ->
    ExecF.rng RNG 6156544 8 -> ExecF.rng RNG 6156752 8 -> ExecF.rng RNG 6156444 4 ->
    ExecF.evtF rsegs RNG
      (cis_post1 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIS_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw HW ST HLO HOFF EA FLY1 RFR RGOT ROW RFO RNOW RFS RACK.
  unfold CIS_ENTRY.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (cis_ranges Bw) as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6).
  unfold TG.G_HARNESS_HI in HOFF.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* 0x85d50 - 0x85d60: the frame and the four saves *)
  step. step. step. step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  assert (HW0 : tw_at TMAP_A (csw_view m0) Bw)
    by (apply (csw_kept m m0 _ _ Bw HW MU1); unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia).
  destruct (cis_reads m0 Bw HW0) as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6).
  (* 0x85d64 - 0x85d74: GOT.acked and OW.acked; bne not taken *)
  step. step. step. step. cis_fields Bw. rewrite EA.
  step. rewrite bv_eqb_refl. cbn [negb].
  (* 0x85d78 - 0x85d88: s0 = &M, a0 = M.fly_on, s2, s1 *)
  step. step. step. step. step. cis_fields Bw.
  (* 0x85dac - 0x85db8: a1 = g_now, a0 = &g_s, the call *)
  assert (TAIL : forall x10 x11 x12 : word,
    ExecF.evtF rsegs RNG
      (cis_post1 ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Bw)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 6156640) (Z_to_bv 64 6155656)
               x10 x11 x12 a3 a4 a5 a6 a7 (Z_to_bv 64 6155652) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 548268) fc None m0 (seg_rom rsegs))).
  { intros x10 x11 x12.
    step. step. step. step. cis_fields Bw.
    apply evtF_done. unfold cis_post1. exists x12, m0.
    split; [reflexivity|]. split; [exact MU1|]. split; [exact WM|]. split; [exact FR | exact HW0]. }
  (* 0x85d8c: beqz M.fly_on *)
  step.
  destruct (Z.eq_dec (TW.M_fly_on Bw) 0) as [F0|F0].
  { cis_br true. apply TAIL. }
  cis_br false.
  specialize (FLY1 F0).
  (* 0x85d90 - 0x85da8: g_now - M.fly_sent against ack_timeout_ms * 1000; bgeu not taken *)
  step. step. step. cis_fields Bw. step. step. step.
  step. cis_br false.
  apply TAIL.
Qed.

(* ---- the run from the callee's return to the return to the caller ---- *)

Lemma cis_run2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Bw : list byte) (d : Z) (vra vs0 vs1 vs2 : word),
    tw_at TMAP_A (csw_view m) Bw ->
    0 <= d < 2 ^ 64 ->
    TW.g_now Bw <= d -> d <= (TW.g_now Bw + 1000000) mod 2 ^ 64 ->
    (TW.M_fly_on Bw <> 0 ->
     d <= (TW.M_fly_sent Bw + (TW.Cfg_ack_timeout_ms Bw * 1000) mod 2 ^ 64) mod 2 ^ 64) ->
    0 <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
    ExecF.rng RNG (bv_unsigned sp) 32 ->
    ExecF.rng RNG 6156544 8 -> ExecF.rng RNG 6156736 4 -> ExecF.rng RNG 6156752 8 -> ExecF.rng RNG 6156444 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 vs0 vs1 (Z_to_bv 64 d) a1' a2' a3'
                       a4 a5 a6 a7 vs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 CIS_M) (Z_to_bv 64 CIS_S1) (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 CIS_S2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CIS_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Bw d vra vs0 vs1 vs2 HW Rd D1 D2 FLY2 Hsp0 Hsp1 FR RFR RNOW RFO RFS RACK.
  unfold CIS_M, CIS_S1, CIS_S2, CIS_RET.
  pose proof (cis_ranges Bw) as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6).
  destruct (cis_reads m Bw HW) as (_ & _ & RD3 & RD4 & RD5 & RD6).
  (* 0x85dbc - 0x85dc0: a1 = g_now; bltu d, g_now not taken *)
  step. cis_fields Bw.
  step. cis_br false.
  (* 0x85dc4 - 0x85dd0: a1 = g_now + 1000000; bltu a1, d not taken *)
  step. step. step.
  step. cis_br false.
  (* 0x85dd4 - 0x85dd8: a1 = M.fly_on; beqz to the epilogue *)
  step. cis_fields Bw.
  step.
  assert (EPI : forall x11 x12 x13 : word,
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 vs0 vs1 (Z_to_bv 64 d) a1' a2' a3'
                       a4 a5 a6 a7 vs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 6156640) (Z_to_bv 64 6155656) (Z_to_bv 64 d) x11 x12 x13
               a4 a5 a6 a7 (Z_to_bv 64 6155652) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 548340) fc None m (seg_rom rsegs))).
  { intros x11 x12 x13.
    step. step. step. step. step. step.
    apply evtF_done. exists x11, x12, x13. reflexivity. }
  destruct (Z.eq_dec (TW.M_fly_on Bw) 0) as [F0|F0].
  { cis_br true. apply EPI. }
  cis_br false.
  specialize (FLY2 F0).
  (* 0x85ddc - 0x85df0: ack_timeout_ms * 1000 + M.fly_sent; bltu not taken *)
  step. step. cis_fields Bw. step. step. step.
  step. cis_br false.
  apply EPI.
Qed.
