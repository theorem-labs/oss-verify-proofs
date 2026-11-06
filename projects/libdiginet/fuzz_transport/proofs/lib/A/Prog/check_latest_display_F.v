From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_latest_display_c check_latest_display_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldAKept.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_latest_display_contract_F (image A, entry 0x84844, frame 16 bytes), with StepF's step: each access
   side goal is closed from an rng fact for the accessed range. The world lemmas: tw_bytes_at and lw_world
   (TWorldG.v), TMAP_A_hull (TWorldA.v), csw_kept (TWorldAKept.v).

   The walk (listing DgnTransportList.v, slots 3448-3465):
     0x84844-0x84848  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x8484c-0x84850  auipc a0; addi a0,a0,..: a0 = 0x5df160 (M).
     0x84854          lw a1,72(a0): a1 = the 4-byte load at 0x5df1a8 = M.display_sent, sign-extended.
     0x84858          beqz a1, 0x84878.
     0x8485c          auipc a1.
     0x84860          ld a0,64(a0): a0 = the 8-byte load at 0x5df1a0 = M.last_display.
     0x84864          ld a1,..(a1): a1 = the 8-byte load at 0x5df100 = g_now.
     0x84868-0x8486c  auipc a2; lwu a2,..(a2): a2 = the 4-byte load at 0x5df0b0 = g_cfg.display_gap_us, zero-extended.
     0x84870          sub a1,a1,a0.
     0x84874          bltu a1,a2, 0x84884.
     0x84878-0x84880  ld ra,8(sp); addi sp,sp,16; ret.
   The trap path 0x84884 / 0x84888 (__asan_handle_no_return, abort) is never reached: by the world relation the
   loaded bytes are sub Bw A_M_display_sent 4, sub Bw A_M_last_display 8, sub Bw OFF_g_now 8 and
   sub Bw A_Cfg_display_gap_us 4, so the loaded values are M_display_sent Bw, M_last_display Bw, g_now Bw and
   Cfg_display_gap_us Bw (lw_world, ld_world, lwu_world), and the model premise check_latest_display_m Bw =
   Some (Bw', tt) gives Bw' = Bw and, when M_display_sent Bw is not 0, (g_now Bw - M_last_display Bw) mod 2^64 not
   below Cfg_display_gap_us Bw (cld_model), so bltu falls through (cld_ltu).

   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 payload ranges (off_stk premise), so every payload byte reads the same
   (csw_kept) and tw_at holds of the same Bw. *)

(* ld of the world's 8 bytes at k: TWorld's u_at. *)
Lemma ld_world : forall B k,
  bv_extract 0 64 (le_bytes_to_word (TW.sub B k 8)) = Z_to_bv 64 (TW.u_at B k 8).
Proof.
  intros B k. transitivity (le_bytes_to_word (TW.sub B k 8)); [|reflexivity].
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* lwu of the world's 4 bytes at k: TWorld's u_at. *)
Lemma lwu_world : forall B k,
  zext 64 (bv_extract 0 32 (le_bytes_to_word (TW.sub B k 4))) = Z_to_bv 64 (TW.u_at B k 4).
Proof.
  intros B k. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (TW.u_at B k 4).
  pose proof (TWorldLemmas.u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite bv_wrap_small by (unfold bv_modulus; change (Z.of_N 64) with 64; lia).
  change (Z.of_N 32) with 32. apply Z.mod_small. exact R.
Qed.

(* The length of a world slice inside W_LEN. *)
Lemma cld_len : forall v Bw k (c : nat), tw_at TMAP_A v Bw -> 0 <= k -> k + Z.of_nat c <= TW.W_LEN ->
  length (TW.sub Bw k c) = c.
Proof.
  intros v Bw k c HW Hk Hc. apply TWorldLemmas.length_sub; [exact Hk|].
  rewrite (tw_len TMAP_A v Bw HW). unfold TW.W_LEN in *. lia.
Qed.

(* The model premise, as the facts the two branches test (TCb.v check_latest_display_m). *)
Lemma cld_model : forall B B',
  TC.check_latest_display_m B = Some (B', tt) ->
  B' = B /\
  (TW.M_display_sent B <> 0 ->
   ((TW.g_now B - TW.M_last_display B) mod 2^64 <? TW.Cfg_display_gap_us B) = false).
Proof.
  intros B B' HM. unfold TC.check_latest_display_m, TC.truth in HM.
  destruct (Z.eqb_spec (TW.M_display_sent B) 0) as [E|E]; cbv beta iota delta [negb andb] in HM.
  - split; [|intros N; contradiction].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB.
  - match type of HM with (if ?c then _ else _) = _ => destruct c eqn:L end; [discriminate HM|].
    split; [|intros _; exact L].
    pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) HM)
      as HB.
    cbv beta iota in HB. symmetry. exact HB.
Qed.

(* beqz on a sign-extended 32-bit value that is not 0 falls through. *)
Lemma cld_ne0 : forall v, -2^63 <= v < 2^63 -> v <> 0 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv N. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* bltu (g - l) c with (g - l) mod 2^64 not below c falls through. *)
Lemma cld_ltu : forall g l c, 0 <= g < 2^64 -> 0 <= l < 2^64 -> 0 <= c < 2^64 ->
  ((g - l) mod 2^64 <? c) = false ->
  bv_ltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 g) - bv_unsigned (Z_to_bv 64 l))) (Z_to_bv 64 c) = false.
Proof.
  intros g l c Hg Hl Hc H. rewrite bv_ltu_Z, !unsigned_lit_wrap.
  rewrite (Z.mod_small g), (Z.mod_small l), (Z.mod_small c) by lia. exact H.
Qed.

Theorem check_latest_display_holds_F : check_latest_display_contract_F.
Proof.
  unfold check_latest_display_contract_F, CHECK_LATEST_DISPLAY, CHECK_LATEST_DISPLAY_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Bw Bw' HW HM ST HLO HOFF RFR RSENT RLAST RNOW RGAP.
  (* the model: Bw' = Bw, and the gap fact when M.display_sent is not 0 *)
  destruct (cld_model Bw Bw' HM) as [-> GAP]. clear HM.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_display_sent) as R0.
  assert (R1 : 0 <= TW.g_now Bw < 2^64) by exact (TWorldLemmas.u_at_range Bw TW.OFF_g_now 8).
  assert (R2 : 0 <= TW.M_last_display Bw < 2^64) by exact (TWorldLemmas.u_at_range Bw TW.A_M_last_display 8).
  assert (R3 : 0 <= TW.Cfg_display_gap_us Bw < 2^64).
  { pose proof (TWorldLemmas.u_at_range Bw TW.A_Cfg_display_gap_us 4) as R.
    change (8 * Z.of_nat 4) with 32 in R. unfold TW.Cfg_display_gap_us. lia. }
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  rewrite check_latest_display_sent_at in RSENT.
  rewrite check_latest_display_last_at in RLAST.
  rewrite check_latest_display_now_at in RNOW.
  rewrite check_latest_display_gap_at in RGAP.
  (* the bytes of the four members, as raw memory *)
  assert (L1 : length (TW.sub Bw TW.A_M_display_sent 4) = 4%nat)
    by (apply (cld_len _ Bw _ 4 HW); cbv [TW.A_M_display_sent TW.OFF_M TW.W_LEN]; lia).
  assert (L2 : length (TW.sub Bw TW.A_M_last_display 8) = 8%nat)
    by (apply (cld_len _ Bw _ 8 HW); cbv [TW.A_M_last_display TW.OFF_M TW.W_LEN]; lia).
  assert (L3 : length (TW.sub Bw TW.OFF_g_now 8) = 8%nat)
    by (apply (cld_len _ Bw _ 8 HW); cbv [TW.OFF_g_now TW.W_LEN]; lia).
  assert (L4 : length (TW.sub Bw TW.A_Cfg_display_gap_us 4) = 4%nat)
    by (apply (cld_len _ Bw _ 4 HW); cbv [TW.A_Cfg_display_gap_us TW.OFF_g_cfg TW.W_LEN]; lia).
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 72 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF1.
  change (TA_M + 72) with 6156712 in BF1. change (TW.OFF_M + 72) with TW.A_M_display_sent in BF1.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 64 8 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BF2.
  change (TA_M + 64) with 6156704 in BF2. change (TW.OFF_M + 64) with TW.A_M_last_display in BF2.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok HW TMAP_A_g_now
    ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as BF3.
  change (TA_g_now + 0) with 6156544 in BF3. change (TW.OFF_g_now + 0) with TW.OFF_g_now in BF3.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 48 4 TMAP_A_ok HW TMAP_A_g_cfg
    ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) as BF4.
  change (TA_g_cfg + 48) with 6156464 in BF4. change (TW.OFF_g_cfg + 48) with TW.A_Cfg_display_gap_us in BF4.
  (* keep the world's bytes off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj BF1 (conj BF2 (conj BF3 BF4))) as BFC. clear BF1 BF2 BF3 BF4.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x84844-0x84848: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct BFC as (BF1 & BF2 & BF3 & BF4).
  pose proof (bytes_tp m m0 _ _ 6156712 (TW.sub Bw TW.A_M_display_sent 4) MU1 ltac:(rewrite L1; lia) BF1)
    as BF1'.
  pose proof (bytes_tp m m0 _ _ 6156704 (TW.sub Bw TW.A_M_last_display 8) MU1 ltac:(rewrite L2; lia) BF2)
    as BF2'.
  pose proof (bytes_tp m m0 _ _ 6156544 (TW.sub Bw TW.OFF_g_now 8) MU1 ltac:(rewrite L3; lia) BF3) as BF3'.
  pose proof (bytes_tp m m0 _ _ 6156464 (TW.sub Bw TW.A_Cfg_display_gap_us 4) MU1 ltac:(rewrite L4; lia) BF4)
    as BF4'.
  assert (RD1 : ov_read_bytes rsegs m0 (wa 6156712) 4 = Some (TW.sub Bw TW.A_M_display_sent 4)).
  { replace (wa 6156712) with (wa (6156712 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6156712 _ 0 4 BF1' ltac:(lia)) by (rewrite L1; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L1. lia. }
  assert (RD2 : ov_read_bytes rsegs m0 (wa 6156704) 8 = Some (TW.sub Bw TW.A_M_last_display 8)).
  { replace (wa 6156704) with (wa (6156704 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6156704 _ 0 8 BF2' ltac:(lia)) by (rewrite L2; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L2. lia. }
  assert (RD3 : ov_read_bytes rsegs m0 (wa 6156544) 8 = Some (TW.sub Bw TW.OFF_g_now 8)).
  { replace (wa 6156544) with (wa (6156544 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6156544 _ 0 8 BF3' ltac:(lia)) by (rewrite L3; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L3. lia. }
  assert (RD4 : ov_read_bytes rsegs m0 (wa 6156464) 4 = Some (TW.sub Bw TW.A_Cfg_display_gap_us 4)).
  { replace (wa 6156464) with (wa (6156464 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6156464 _ 0 4 BF4' ltac:(lia)) by (rewrite L4; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite L4. lia. }
  clear BF1 BF2 BF3 BF4 BF1' BF2' BF3' BF4'.
  (* 0x8484c-0x84850: a0 = M; 0x84854: a1 = M.display_sent *)
  step. step. step.
  rewrite lw_world. change (TW.s32_at Bw TW.A_M_display_sent) with (TW.M_display_sent Bw).
  clear RD1.
  destruct (Z.eqb_spec (TW.M_display_sent Bw) 0) as [D|D].
  - (* 0x84858: beqz a1 taken: M.display_sent = 0 *)
    rewrite D.
    step. if_true.
    (* 0x84878-0x84880: ld ra; addi sp; ret *)
    step. step. step.
    apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [reflexivity|].
    apply (csw_kept m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
  - (* 0x84858: beqz a1 falls through: M.display_sent is not 0 *)
    step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false;
        [ cbv iota
        | symmetry; apply cld_ne0; [unfold TW.M_display_sent in *; lia | exact D] ]
    end.
    (* 0x8485c-0x84860: a0 = M.last_display *)
    step. step.
    rewrite ld_world. change (TW.u_at Bw TW.A_M_last_display 8) with (TW.M_last_display Bw).
    clear RD2.
    (* 0x84864: a1 = g_now *)
    step.
    rewrite ld_world. change (TW.u_at Bw TW.OFF_g_now 8) with (TW.g_now Bw).
    clear RD3.
    (* 0x84868-0x8486c: a2 = g_cfg.display_gap_us *)
    step. step.
    rewrite lwu_world. change (TW.u_at Bw TW.A_Cfg_display_gap_us 4) with (TW.Cfg_display_gap_us Bw).
    clear RD4.
    (* 0x84870: a1 = g_now - M.last_display; 0x84874: bltu a1,a2 falls through *)
    step. step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false;
        [ cbv iota
        | symmetry; apply cld_ltu; [exact R1 | exact R2 | exact R3 | exact (GAP D)] ]
    end.
    (* 0x84878-0x84880: ld ra; addi sp; ret *)
    step. step. step.
    apply evtF_done. do 4 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [reflexivity|].
    apply (csw_kept m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.

Print Assumptions check_latest_display_holds_F.
