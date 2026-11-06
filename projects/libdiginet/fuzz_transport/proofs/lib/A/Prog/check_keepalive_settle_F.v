From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_keepalive_settle_c check_keepalive_settle_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_keepalive_settle_contract_F (image A, entry 0x85e14, frame 16 bytes), with StepF's step, in the
   form of check_state_wake_F.v, over the kit's world lemmas (TWorldG.v tw_bytes_at / lw_world / ld_world,
   TWorldA.v TMAP_A_kept). The lemmas before the theorem name no image, so image B's walk
   (lib/B/Prog/check_keepalive_settle_F.v) uses them too.

   The walk (statement comment, check_keepalive_settle_c.v:20-43):
     0x85e14-0x85e18  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x85e1c-0x85e20  a0 = g_raw (4-byte load at 0x5df0e0); 0x85e24 bnez a0 -> the return 0x85e5c.
     0x85e28-0x85e2c  a0 = 0x5df160 (M); 0x85e30 a1 = M.state; 0x85e34 a2 = 2; 0x85e38 bne a1,a2 -> 0x85e5c.
     0x85e3c          a1 = M.fly.on; 0x85e40 bnez a1 -> 0x85e5c.
     0x85e44-0x85e48  a1 = g_now (8 bytes at 0x5df100); 0x85e4c a2 = M.backoff_until; 0x85e50 bltu a1,a2 -> 0x85e5c.
     0x85e54          a0 = M.next_ka; 0x85e58 bgeu a1,a0 -> the trap path 0x85e68.
     0x85e5c-0x85e64  ld ra,8(sp); addi sp,sp,16; ret.
   The run writes only its frame, so after the ra store every load reads the world through the world relation at
   the new memory (TMAP_A_kept), as sub Bw (offset) n (ckk_rdf). When the four tests before 0x85e58 all fall through,
   the model premise (ckk_model) gives g_now < M.next_ka, so the bgeu is not taken and the trap path is never
   reached. *)

(* The model premise: the world is returned unchanged, and when the first four tests hold, the fifth does not.
   (lib/Prog/T/check_keepalive_settle.v cks_model, restated here over TWorld's names and without an injection on the
   world-carrying option.) *)
Lemma ckk_model : forall B B',
  TC.check_keepalive_settle_m B = Some (B', tt) ->
  B' = B /\
  (TW.s32_at B TW.OFF_g_raw = 0 -> TW.s32_at B TW.A_M_state = 2 -> TW.s32_at B TW.A_M_fly_on = 0 ->
   TW.u_at B TW.A_M_backoff_until 8 <= TW.u_at B TW.OFF_g_now 8 ->
   TW.u_at B TW.OFF_g_now 8 < TW.u_at B TW.A_M_next_ka 8).
Proof.
  intros B B' HM. unfold TC.check_keepalive_settle_m in HM.
  match type of HM with context [if ?c then _ else _] => destruct c eqn:C end; [discriminate HM|].
  split.
  { pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB. }
  intros E1 E2 E3 E4. apply Z.nle_gt. intros E5.
  apply Bool.not_true_iff_false in C. apply C.
  repeat (apply andb_true_intro; split).
  - unfold TC.truth. rewrite Bool.negb_involutive. apply Z.eqb_eq. exact E1.
  - apply Z.eqb_eq. exact E2.
  - unfold TC.truth. rewrite Bool.negb_involutive. apply Z.eqb_eq. exact E3.
  - apply Z.leb_le. exact E4.
  - apply Z.leb_le. exact E5.
Qed.

(* beqz / bne on two values in the signed 64-bit range, bltu / bgeu on two in the unsigned range: the Z test
   (lib/Prog/T/check_keepalive_settle.v cks_eqb / cks_ltu). *)
Lemma ckk_eqb : forall v w, -2^63 <= v < 2^63 -> -2^63 <= w < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  assert (D : (v - w) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  clear E N.
  apply Z.mod_divide in D; [|lia]. destruct D as [c Ec]. lia.
Qed.

Lemma ckk_ltu : forall v w, 0 <= v < 2^64 -> 0 <= w < 2^64 ->
  bv_ltu (Z_to_bv 64 v) (Z_to_bv 64 w) = (v <? w).
Proof. intros v w Hv Hw. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A load of c bytes at b + k inside ONE payload row of a world table T reads sub Bw (o + k) c, as the load step's
   read fact. *)
Lemma ckk_rdf : forall segs T (m : word -> option byte) Bw o b n k (c : nat),
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

(* the return at 0x85e5c: ld ra; addi sp; ret, and the post *)
Ltac ckk_ret FR ST sp HW0 :=
  step; step; step;
  apply evtF_done; do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  split; [release_frame FR ST (bv_unsigned sp); exact ST|];
  split; [reflexivity | exact HW0].

Theorem check_keepalive_settle_holds_F : check_keepalive_settle_contract_F.
Proof.
  unfold check_keepalive_settle_contract_F, CHECK_KEEPALIVE_SETTLE, CHECK_KEEPALIVE_SETTLE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RRAW RST RFLY RNOW RBO RKA.
  destruct (ckk_model Bw Bw' HM) as (-> & DUE). clear HM.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  rewrite check_keepalive_settle_raw_at in RRAW. rewrite check_keepalive_settle_state_at in RST.
  rewrite check_keepalive_settle_fly_on_at in RFLY. rewrite check_keepalive_settle_now_at in RNOW.
  rewrite check_keepalive_settle_backoff_at in RBO. rewrite check_keepalive_settle_next_ka_at in RKA.
  pose proof (TWorldLemmas.s32_range Bw TW.OFF_g_raw) as V1.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_state) as V2.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_fly_on) as V3.
  pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_now 8) as V4.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_backoff_until 8) as V5.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_M_next_ka 8) as V6.
  change (8 * Z.of_nat 8) with 64 in V4, V5, V6.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x85e14-0x85e18: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the world relation at the new memory, and the six world loads as read facts there *)
  assert (HW0 : tw_at TMAP_A (csw_view m0) Bw)
    by (apply (@TMAP_A_kept rsegs m m0 _ _ Bw HW MU1); unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia).
  pose proof (ckk_rdf rsegs TMAP_A m0 Bw TW.OFF_g_raw TA_g_raw TW.SZ_g_raw 0 4 TMAP_A_ok HW0 TMAP_A_g_raw
    ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia)) as RD1.
  change (TA_g_raw + 0) with 6156512 in RD1. change (TW.OFF_g_raw + 0) with TW.OFF_g_raw in RD1.
  pose proof (ckk_rdf rsegs TMAP_A m0 Bw TW.OFF_M TA_M TW.SZ_M 12 4 TMAP_A_ok HW0 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD2.
  change (TA_M + 12) with 6156652 in RD2. change (TW.OFF_M + 12) with TW.A_M_state in RD2.
  pose proof (ckk_rdf rsegs TMAP_A m0 Bw TW.OFF_M TA_M TW.SZ_M 96 4 TMAP_A_ok HW0 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD3.
  change (TA_M + 96) with 6156736 in RD3. change (TW.OFF_M + 96) with TW.A_M_fly_on in RD3.
  pose proof (ckk_rdf rsegs TMAP_A m0 Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok HW0 TMAP_A_g_now
    ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as RD4.
  change (TA_g_now + 0) with 6156544 in RD4. change (TW.OFF_g_now + 0) with TW.OFF_g_now in RD4.
  pose proof (ckk_rdf rsegs TMAP_A m0 Bw TW.OFF_M TA_M TW.SZ_M 56 8 TMAP_A_ok HW0 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD5.
  change (TA_M + 56) with 6156696 in RD5. change (TW.OFF_M + 56) with TW.A_M_backoff_until in RD5.
  pose proof (ckk_rdf rsegs TMAP_A m0 Bw TW.OFF_M TA_M TW.SZ_M 48 8 TMAP_A_ok HW0 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as RD6.
  change (TA_M + 48) with 6156688 in RD6. change (TW.OFF_M + 48) with TW.A_M_next_ka in RD6.
  (* 0x85e1c-0x85e20: a0 = g_raw; 0x85e24 bnez a0 *)
  step. step. rewrite lw_world.
  step. rewrite ckk_eqb by lia.
  destruct (Z.eqb_spec (TW.s32_at Bw TW.OFF_g_raw) 0) as [E1|E1]; cbn [negb]; [ | ckk_ret FR ST sp HW0].
  (* 0x85e28-0x85e2c: a0 = M; 0x85e30 a1 = M.state; 0x85e34 a2 = 2; 0x85e38 bne a1,a2 *)
  step. step. step. rewrite lw_world. step.
  step. rewrite ckk_eqb by lia.
  destruct (Z.eqb_spec (TW.s32_at Bw TW.A_M_state) 2) as [E2|E2]; cbn [negb]; [ | ckk_ret FR ST sp HW0].
  (* 0x85e3c: a1 = M.fly.on; 0x85e40 bnez a1 *)
  step. rewrite lw_world.
  step. rewrite ckk_eqb by lia.
  destruct (Z.eqb_spec (TW.s32_at Bw TW.A_M_fly_on) 0) as [E3|E3]; cbn [negb]; [ | ckk_ret FR ST sp HW0].
  (* 0x85e44-0x85e48: a1 = g_now; 0x85e4c a2 = M.backoff_until; 0x85e50 bltu a1,a2 *)
  step. step. rewrite ld_world. step. rewrite ld_world.
  step. rewrite ckk_ltu by lia.
  destruct (Z.ltb_spec (TW.u_at Bw TW.OFF_g_now 8) (TW.u_at Bw TW.A_M_backoff_until 8)) as [E4|E4]; cbn [negb];
    [ckk_ret FR ST sp HW0 | ].
  (* 0x85e54: a0 = M.next_ka; 0x85e58 bgeu a1,a0: not taken, by the model premise *)
  step. rewrite ld_world.
  step. rewrite ckk_ltu by lia.
  destruct (Z.ltb_spec (TW.u_at Bw TW.OFF_g_now 8) (TW.u_at Bw TW.A_M_next_ka 8)) as [E5|E5]; cbn [negb];
    [ckk_ret FR ST sp HW0 | exfalso; specialize (DUE E1 E2 E3 E4); lia].
Qed.

Print Assumptions check_keepalive_settle_holds_F.
