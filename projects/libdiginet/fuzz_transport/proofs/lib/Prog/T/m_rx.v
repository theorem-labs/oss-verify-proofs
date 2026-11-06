From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import m_rx_c desk_named_c m_lost_c m_wake_c m_maybe_online_c m_tick_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import m_rx_epi m_rx_desk.
Import ListNotations.
Open Scope Z_scope.

(* ---------------- small comparison / literal helpers (local) ---------------- *)
Lemma mrx_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma mrx_eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma mrx_eqb0 : forall v, -2^63 <= v < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma mrx_eqb_small : forall v, -256 < v < 256 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* ---------------- frame-read helpers ---------------- *)
(* These let us read individual byte / word fields of the frame buffer at [tf_addr fr]. *)
Lemma mrx_rd_sub : forall m a bs k n, bytes_at rsegs m a bs ->
  0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof.
  intros m a bs k n H Hk Hn. unfold sub.
  apply (bytes_at_read rsegs m a bs k n H Hk). lia.
Qed.

Lemma mrx_lw_val : forall bs, length bs = 4%nat ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) = Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs)).
Proof.
  intros bs L. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. f_equal.
  pose proof (ble_range bs) as H. rewrite L in H. apply bv_wrap_small. unfold bv_modulus. cbn in H. lia.
Qed.

Lemma mrx_lbu_val : forall bs, length bs = 1%nat ->
  zext 64 (bv_extract 0 8 (le_bytes_to_word bs)) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (ble_range bs) as H. rewrite L in H. cbn in H.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). apply Z.mod_small. cbn. lia.
Qed.

Lemma mrx_ld_val : forall bs, bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs. transitivity (le_bytes_to_word bs); [|reflexivity].
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* bytes_le_to_Z [b] = bv_unsigned b *)
Lemma mrx_ble1_bv : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intros b. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. lia. Qed.

Lemma mrx_ble1 : forall bs k, 0 <= k -> k < Z.of_nat (length bs) ->
  bytes_le_to_Z (sub bs k 1) = bv_unsigned (nth (Z.to_nat k) bs (b8 0)).
Proof.
  intros bs k Hk Hl. unfold sub.
  destruct (skipn (Z.to_nat k) bs) as [|b bs'] eqn:ESK.
  - exfalso. apply (f_equal (@length _)) in ESK. rewrite length_skipn in ESK. cbn in ESK. lia.
  - cbn [firstn]. rewrite mrx_ble1_bv.
    pose proof (f_equal (fun l => nth 0%nat l (b8 0)) ESK) as E. cbn in E.
    rewrite List.nth_skipn, Nat.add_0_r in E. rewrite E. reflexivity.
Qed.

Lemma mrx_byte_at_zs : forall bs i, 0 <= i -> (Z.to_nat i < length bs)%nat ->
  byte_at (zs bs) i = bytes_le_to_Z (sub bs i 1).
Proof.
  intros bs i Hi Hl. rewrite mrx_ble1 by lia.
  unfold byte_at, zs.
  rewrite (nth_indep _ 0 (bv_unsigned (b8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

(* bytes_le_to_Z (sub bs k 1) in [0, 2^8). *)
Lemma mrx_sub1_range : forall bs k, 0 <= bytes_le_to_Z (sub bs k 1) < 2^8.
Proof.
  intros bs k. split; [apply bytes_le_to_Z_nonneg|].
  pose proof (bytes_le_to_Z_bound (sub bs k 1)) as H.
  pose proof (length_sub_le bs k 1). apply Z.lt_le_trans with (1 := H).
  apply Z.pow_le_mono_r; lia.
Qed.

(* The disassembly's assembly of 2 bytes into a 16-bit value *)
Lemma mrx_asm_be16 : forall x y, 0 <= x < 2^8 -> 0 <= y < 2^8 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 8)))
        (bv_unsigned (Z_to_bv 64 y))
  = x * 2^8 + y.
Proof.
  intros x y Hx Hy.
  rewrite (unsigned_lit x) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x * 2^8)) by lia.
  rewrite (unsigned_lit y) by lia.
  apply (lor_add (x * 2^8) y 8); [lia | lia |].
  change (2^8) with 256. rewrite Z_mod_mult. reflexivity.
Qed.

(* (byte-range reused from mrx_sub1_range directly.) *)

(* lbu of byte k of the frame block at tf_addr fr: the read by mrx_rd_sub, the value by mrx_lbu_val *)
Ltac mrx_lbu k :=
  lazymatch goal with HB : bytes_at rsegs _ (tf_addr ?fr) (tf_bytes ?fr) |- _ =>
    let RD := fresh "RD" in
    pose proof (mrx_rd_sub _ (tf_addr fr) (tf_bytes fr) k 1 HB ltac:(lia) ltac:(lia)) as RD;
    step; rewrite (mrx_lbu_val (sub (tf_bytes fr) k 1)) by (apply length_sub; lia); clear RD
  end.

(* ============================================================================
   The theorem: entry to 0x15528 here (short frame, prologue, ethertype, numbytes, the header bytes, the three
   MAC bcmps); the desk, the switch and the cmd branches are m_rx_desk.v, m_rx_body.v, m_rx_ann.v, m_rx_ack.v,
   m_rx_data.v, on the shared epilogue / m_tick / model split of m_rx_epi.v.
   ============================================================================ *)
Theorem m_rx_holds : bcmp_contract -> memcpy_contract -> desk_named_contract ->
  m_lost_contract -> m_wake_contract -> m_maybe_online_contract -> m_tick_contract ->
  m_rx_contract.
Proof.
  intros BC MC DN LC WC MOC TC.
  unfold m_rx_contract, m_rx_ENTRY, m_rx_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  intros F fc m lo B B' fr n r.
  intros -> -> HFR _HBND HS16 ST LO WOF MI WM MDL.
  (* Heap frame facts *)
  simpl in HFR. destruct HFR as (Hfa_pos & HBYTES & HFR_offW & HFR_offSP).
  unfold off_window in HFR_offSP. unfold off_world in HFR_offW.
  pose proof (bytes_at_bound rsegs m (tf_addr fr) (tf_bytes fr) HBYTES) as [_ Hfa_hi].
  (* Range for n via the model *)
  cbn [m_rx_m] in MDL.
  destruct ((n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n)) eqn:NR; [discriminate|].
  apply orb_false_iff in NR. destruct NR as [N0b NLb].
  apply Z.ltb_ge in N0b. apply Z.ltb_ge in NLb.
  (* 0 <= n <= length (tf_bytes fr) *)
  (* Frame goal preparation *)
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp);
                          (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  (* Entry: li a2, 30; bgeu a1, a2, 15648 *)
  step.
  step.
  rewrite mrx_ltu_lit by lia.
  destruct (Z.ltb_spec n 30) as [NSHORT|NLONG]; cbn [negb].
  { (* n < 30: machine returns 0 before prologue; model also returns Some(B,0). *)
    (* Reduce the model equation. *)
    unfold spec_read_frame in MDL.
    replace (n <? SPEC_BODY_AT) with true in MDL by (symmetry; apply Z.ltb_lt; unfold SPEC_BODY_AT; lia).
    cbv iota in MDL. cbn [sf_code negb Z.eqb] in MDL.
    inversion MDL as [[EB EBr]]. clear MDL. subst B' r.
    (* Machine: li a0, 0; ret *)
    step. step.
    apply evt_done. unfold QQ. do 15 eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM0|]. split; [exact MI|].
    split; [exact ST|]. exact WM.
  }
  (* n >= 30: enter prologue. *)
  unfold w_off_stack in WOF.
  wk_facts.
  carve_frame 128%nat ST.
  rename m into mI.
  do 15 step.
  (* now at pc 0x1542c: lbu a0, 12(s0). s0 = tf_addr fr. Memory is m0 after the sd stores. *)
  (* Rename for convenience *)
  lazymatch goal with H : rw_cells _ ?mm _ ?cs |- _ => rename mm into mP; set (FRC_PRO := cs) in H end.
  change QQ with (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B' r).
  unfold FRC_PRO in FR. clear FRC_PRO.
  assert (MDL0 : m_rx_m timg_plain (Some fr) B n = Some (B', r)).
  { cbn [m_rx_m]. destruct ((n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n)) eqn:NR2.
    - exfalso. apply orb_true_iff in NR2. destruct NR2 as [NR2|NR2]; apply Z.ltb_lt in NR2; lia.
    - exact MDL. }
  clear MDL. rename MDL0 into MDL.
  (* 0x1542c-0x15444: the ethertype, bytes 12 and 13 *)
  pose proof (mrx_rd_sub _ (tf_addr fr) (tf_bytes fr) 12 1 HBYTES ltac:(lia) ltac:(lia)) as RD.
  step. rewrite (mrx_lbu_val (sub (tf_bytes fr) 12 1)) by (apply length_sub; lia). clear RD.
  pose proof (mrx_rd_sub _ (tf_addr fr) (tf_bytes fr) 13 1 HBYTES ltac:(lia) ltac:(lia)) as RD.
  step. rewrite (mrx_lbu_val (sub (tf_bytes fr) 13 1)) by (apply length_sub; lia). clear RD.
  do 4 step.
  rewrite (mrx_asm_be16 _ _ (mrx_sub1_range _ _) (mrx_sub1_range _ _)).
  assert (ET : bytes_le_to_Z (sub (tf_bytes fr) 12 1) * 2^8 + bytes_le_to_Z (sub (tf_bytes fr) 13 1)
               = spec_be16 (zs (tf_bytes fr)) 12) by (symmetry; apply mrx_be16; lia).
  rewrite ET. clear ET.
  pose proof (mrx_be16_range (zs (tf_bytes fr)) 12) as RET.
  step.
  rewrite mrx_eqb_lit by lia.
  destruct (Z.eqb_spec (spec_be16 (zs (tf_bytes fr)) 12) 34911) as [EOK|EBAD]; cbn [negb].
  2: { rewrite (mrx_m_et timg_plain fr B n) in MDL by (try lia; exact EBAD).
       injection MDL as EB Er. subst B' r.
       step. mrx_epi_close. }
  (* 0x15448-0x15464: numbytes, bytes 14 and 15 *)
  pose proof (mrx_rd_sub _ (tf_addr fr) (tf_bytes fr) 14 1 HBYTES ltac:(lia) ltac:(lia)) as RD.
  step. rewrite (mrx_lbu_val (sub (tf_bytes fr) 14 1)) by (apply length_sub; lia). clear RD.
  pose proof (mrx_rd_sub _ (tf_addr fr) (tf_bytes fr) 15 1 HBYTES ltac:(lia) ltac:(lia)) as RD.
  step. rewrite (mrx_lbu_val (sub (tf_bytes fr) 15 1)) by (apply length_sub; lia). clear RD.
  do 2 step.
  rewrite (mrx_asm_be16 _ _ (mrx_sub1_range _ _) (mrx_sub1_range _ _)).
  assert (ENB : bytes_le_to_Z (sub (tf_bytes fr) 14 1) * 2^8 + bytes_le_to_Z (sub (tf_bytes fr) 15 1)
               = spec_be16 (zs (tf_bytes fr)) 14) by (symmetry; apply mrx_be16; lia).
  rewrite ENB. clear ENB.
  pose proof (mrx_be16_range (zs (tf_bytes fr)) 14) as RNB.
  step. step.
  rewrite mrx_ltu_lit by lia.
  destruct (Z.ltb_spec (spec_be16 (zs (tf_bytes fr)) 14) 16) as [NBS|NBL]; cbv iota.
  { rewrite (mrx_m_len timg_plain fr B n) in MDL by (first [lia | exact EOK | left; exact NBS]).
    injection MDL as EB Er. subst B' r.
    step. mrx_epi_close. }
  step. step.
  rewrite mrx_ltu_lit by lia.
  destruct (Z.ltb_spec (n + -14) (spec_be16 (zs (tf_bytes fr)) 14)) as [NBL2|NBS2]; cbn [negb].
  { rewrite (mrx_m_len timg_plain fr B n) in MDL by (first [lia | exact EOK | right; lia]).
    injection MDL as EB Er. subst B' r.
    step. mrx_epi_close. }
  rewrite (mrx_m_ok timg_plain fr B n) in MDL by (first [lia | exact EOK]).
  assert (FX : mrx_fix sp lo fr n) by (unfold mrx_fix; repeat split; first [assumption | lia]).
  (* 0x154a8-0x154dc: the header bytes 18 .. 28; s1 = the source MAC *)
  mrx_lbu 18. mrx_lbu 19. mrx_lbu 20. mrx_lbu 21. step.
  mrx_lbu 22. mrx_lbu 23. mrx_lbu 24. step.
  mrx_lbu 25. mrx_lbu 26. mrx_lbu 27. mrx_lbu 28. step.
  unfold bcmp_contract, BCMP in BC.
  unfold mrx_top in MDL.
  (* 0x154e0-0x154f4: bcmp (src, HOST, 6) == 0 drops it, a0 = 0 *)
  do 5 step.
  destruct (mrx_bcmp6 (mrx_src fr) HOST ltac:(unfold mrx_src; apply length_sub; lia) eq_refl)
    as (v1 & Hv1 & Rv1 & Ev1).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply BC with (ls := mrx_src fr) (rs := HOST) (v := v1);
      [ rewrite unsigned_lit by lia; unfold mrx_src; apply mrx_bytes_sub; [exact HBYTES | lia | lia]
      | rewrite unsigned_lit by lia; apply mrx_host_at; mrx_mi
      | rewrite unsigned_lit by lia; exact Hv1
      | mrx_mi ]
    | wk_post_call rsegs mm ]
  end.
  step.
  rewrite mrx_eqb_small by lia. rewrite Ev1.
  destruct (beq_bytes (mrx_src fr) HOST) eqn:SH; cbv iota.
  { apply Z.eqb_eq in Ev1. subst v1. cbn [orb] in MDL. cbv iota in MDL.
    injection MDL as EB Er. subst B' r.
    mrx_fr_merge_tac. mrx_epi_close. }
  (* 0x154f8-0x1550c: bcmp (dst, HOST, 6) == 0 goes on at 0x15528 *)
  do 5 step.
  destruct (mrx_bcmp6 (mrx_dst fr) HOST ltac:(unfold mrx_dst; apply length_sub; lia) eq_refl)
    as (v2 & Hv2 & Rv2 & Ev2).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply BC with (ls := mrx_dst fr) (rs := HOST) (v := v2);
      [ rewrite unsigned_lit by lia; unfold mrx_dst;
        let H0 := fresh in
        pose proof (mrx_bytes_sub _ (tf_addr fr) (tf_bytes fr) 0 6 HBYTES ltac:(lia) ltac:(lia)) as H0;
        rewrite Z.add_0_r in H0; exact H0
      | rewrite unsigned_lit by lia; apply mrx_host_at; mrx_mi
      | rewrite unsigned_lit by lia; exact Hv2
      | mrx_mi ]
    | wk_post_call rsegs mm ]
  end.
  step.
  rewrite mrx_eqb_small by lia. rewrite Ev2.
  destruct (beq_bytes (mrx_dst fr) HOST) eqn:DH; cbv iota.
  { cbn [orb negb andb] in MDL. cbv iota in MDL.
    eapply (mrx_desk BC MC DN LC WC MOC TC);
      [ exact FX | exact HBYTES | exact MU | exact WM0 | mrx_mi | exact ST | exact FR | exact WM | exact MDL
      | reflexivity .. ]. }
  (* 0x15510-0x15524: bcmp (dst, SPEC_BCAST, 6) != 0 drops it *)
  do 5 step.
  destruct (mrx_bcmp6 (mrx_dst fr) SPEC_BCAST ltac:(unfold mrx_dst; apply length_sub; lia) eq_refl)
    as (v3 & Hv3 & Rv3 & Ev3).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply BC with (ls := mrx_dst fr) (rs := SPEC_BCAST) (v := v3);
      [ rewrite unsigned_lit by lia; unfold mrx_dst;
        let H0 := fresh in
        pose proof (mrx_bytes_sub _ (tf_addr fr) (tf_bytes fr) 0 6 HBYTES ltac:(lia) ltac:(lia)) as H0;
        rewrite Z.add_0_r in H0; exact H0
      | rewrite unsigned_lit by lia; apply mrx_bcast_at; mrx_mi
      | rewrite unsigned_lit by lia; exact Hv3
      | mrx_mi ]
    | wk_post_call rsegs mm ]
  end.
  step.
  rewrite mrx_eqb_small by lia. rewrite Ev3.
  destruct (beq_bytes (mrx_dst fr) SPEC_BCAST) eqn:DB; cbn [negb]; cbv iota.
  - cbn [orb negb andb] in MDL. cbv iota in MDL.
    eapply (mrx_desk BC MC DN LC WC MOC TC);
      [ exact FX | exact HBYTES | exact MU | exact WM0 | mrx_mi | exact ST | exact FR | exact WM | exact MDL
      | reflexivity .. ].
  - cbn [orb negb andb] in MDL. cbv iota in MDL.
    injection MDL as EB Er. subst B' r.
    step. mrx_fr_merge_tac. mrx_epi_close.
Qed.
