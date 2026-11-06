(* The footprint twin of reac_ctrl_record_cksum_stamp.v (image B; RECIPE.md step 1 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG, by the script of reac_ctrl_record_cksum_stamp.v over StepF's step. Each access
   of the run is closed from one rng premise of reac_ctrl_record_cksum_stamp_contract_F: the frame stores and loads
   of ra and s0, the two 8-byte loads of the GOT cell and of the runtime cell that holds the shadow offset, the
   1-byte load of each checked byte of [a0, a0 + a1 - 1) and the 1-byte store of the stamp byte, and the 1-byte load
   of the shadow byte of each checked byte ((x >> 3) + ASAN_K, inside the byte-exact shadow span of the range).
   reac_ctrl_record_cksum_stamp.v and its theorem are unchanged; reac_ctrl_record_cksum_stamp_holds_of_F re-derives
   the old statement from the footprint form (reac_ctrl_record_cksum_stamp_contract_of_F, RNG_all). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import
  RcAsanRT reac_ctrl_record_cksum_stamp_c reac_ctrl_record_cksum_stamp.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The shadow byte of a checked byte x of [a, b] is inside the byte-exact shadow span of [a, b]; Z.div is opaque to
   lia, so both bounds come from Z.div_le_mono, here in a context with no other division. *)
Lemma rcsF_shadow1 : forall RNG K a b x,
  rng RNG (a / 8 + K) (b / 8 - a / 8 + 1) -> a <= x <= b -> rng RNG (x / 8 + K) 1.
Proof.
  intros RNG K a b x H Hx. eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono a x 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono x b 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The twin of reac_ctrl_record_cksum_stamp.v's Section Loop: the same script, with the data range and the shadow
   span of the checked bytes as rng premises. *)
Section LoopF.
  Variables (ra sp1 gp tp t2 s0 s1 a0 x14 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (off nn : Z) (bs : list byte) (W : list ivl)
    (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hq : bv_unsigned a0 <> 0.
  Hypothesis Hnn : Z.of_nat (length bs) <= nn.
  Hypothesis Hqn : bv_unsigned a0 + nn <= 2^64.
  Hypothesis HB : bytes_at rsegs m (bv_unsigned a0) bs.
  Hypothesis HSR : asan_shadow_rd rsegs m off (bv_unsigned a0) nn W.
  Hypothesis HAD : asan_addressable rsegs m off (bv_unsigned a0) nn.
  Hypothesis RDAT : rng RNG (bv_unsigned a0) nn.
  Hypothesis RSH : rng RNG (bv_unsigned a0 / 8 + off) ((bv_unsigned a0 + nn - 1) / 8 - bv_unsigned a0 / 8 + 1).

  Abbreviation ST pc x5 x6 x11 x12 x16 x17 :=
    (MS (mkR ra sp1 gp tp x5 x6 t2 s0 s1 a0 x11 x12 (Z_to_bv 64 off) x14 (v_sltu (Z_to_bv 64 0) a0) x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x5 x6 x11 x16 x17,
    evtF rsegs RNG Q (ST 0x83ca4 x5 x6 x11 (Z_to_bv 64 (psum bs (length bs))) x16 x17).

  Lemma reac_ctrl_record_cksum_stamp_loopF : forall n i x5 x6 x11 x16 x17,
    (i + n = length bs)%nat -> (0 < n)%nat ->
    bv_unsigned x17 = Z.of_nat n ->
    bv_unsigned x11 = bv_unsigned a0 + Z.of_nat i ->
    bv_unsigned x16 = bv_unsigned a0 + Z.of_nat i ->
    evtF rsegs RNG Q (ST 0x83c50 x5 x6 x11 (Z_to_bv 64 (psum bs i)) x16 x17).
  Proof using Hq Hnn Hqn HB HSR HAD RDAT RSH EXIT.
    induction n as [|n IH]; intros i x5 x6 x11 x16 x17 Hin Hn H17 H11 H16; [lia|].
    pose proof (zr_word a0) as Ra. unfold inr64 in Ra.
    assert (BODY : forall y5 y6,
      evtF rsegs RNG Q (ST 0x83c74 y5 y6 x11 (Z_to_bv 64 (psum bs i)) x16 x17)).
    { intros y5 y6.
      pose proof (rd_byte rsegs m (bv_unsigned a0) bs i HB ltac:(lia)) as RD.
      rewrite <- H16 in RD. rewrite (wa_of_var x16 (bv_unsigned x16) eq_refl) in RD.
      (* the checked byte itself: one byte of the data range *)
      assert (RD1 : rng RNG (bv_unsigned x16) 1) by (eapply rng_sub; [exact RDAT | lia | lia]).
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rc_eqb0 (bv_unsigned x17 + -1)) by lia.
      destruct n as [|n].
      - replace (bv_unsigned x17 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbv iota.
        replace (S i) with (length bs) by lia.
        apply EXIT.
      - replace (bv_unsigned x17 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbv iota. step.
        apply (IH (S i)); first [lia | rewrite unsigned_lit by lia; lia]. }
    step.
    rewrite (rc_ltu_ge a0 x11) by lia.
    step. step. step.
    rewrite (rc_ubchk a0 x11) by lia.
    step.
    rewrite (rc_neq0w a0) by exact Hq.
    destruct (asan_shadow_read rsegs m off (bv_unsigned a0) nn W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite H11. rewrite rc_shr3.
    (* the shadow byte of the checked byte *)
    assert (RS1 : rng RNG ((bv_unsigned a0 + Z.of_nat i) / 8 + off) 1)
      by (eapply rcsF_shadow1; [exact RSH | lia]).
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite H11. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((bv_unsigned a0 + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (bv_unsigned a0 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((bv_unsigned a0 + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End LoopF.

(* The twin of reac_ctrl_record_cksum_stamp.v's stamp_store: the same script on evtF goals (evtF_done for the
   postcondition). *)
Ltac stamp_storeF bs a0 a1 m m1 sp lo FR ST HB MU SUB WM WV HS QQ :=
  let FR2 := fresh "FR2" in let ST2 := fresh "ST2" in let B1 := fresh "B1" in let B2 := fresh "B2" in
  let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let MI2 := fresh "MI2" in let m2 := fresh "m2" in
  step; step; step;
  rewrite rc_le1_stamp;
  change ((- psum bs (length bs)) mod 128) with (stampck bs);
  change (Z_to_bv 64 (bv_unsigned a0 + bv_unsigned a1 - 1)) with (wa (bv_unsigned a0 + bv_unsigned a1 - 1));
  pose proof (rw_cells_frame rsegs m1 _ _ (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)] FR
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize length Nat.add]; lia)) as FR2;
  pose proof (stk_write rsegs m1 lo (bv_unsigned sp + -16) (bv_unsigned a0 + bv_unsigned a1 - 1)
                [Z_to_bv 8 (stampck bs)] ST ltac:(lia) ltac:(cbn [length]; lia)) as ST2;
  pose proof (bytes_at_write_same rsegs m1 (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
                ltac:(lia) ltac:(cbn [length]; lia)) as B1;
  pose proof (bytes_at_write_other rsegs m1 (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
                (bv_unsigned a0) bs HB ltac:(lia) ltac:(cbn [length]; lia) ltac:(left; lia)) as B2;
  pose proof (munch_write _ m m1 (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
                (munch_weaken _ _ m m1 SUB MU) ltac:(lia) ltac:(cbn [length]; lia)
                ltac:(cbn [inside length]; lia)) as MU2;
  pose proof (wmono_write rsegs m m1 (wa (bv_unsigned a0 + bv_unsigned a1 - 1)) [Z_to_bv 8 (stampck bs)] WM) as WM2;
  assert (MI2 : mem_inv rsegs m ->
                mem_inv rsegs (write_to_mem m1 (wa (bv_unsigned a0 + bv_unsigned a1 - 1)) [Z_to_bv 8 (stampck bs)]))
    by (let HI := fresh "HI" in
        intros HI; apply mem_inv_store; [exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact HS]);
  set (m2 := write_to_mem m1 (wa (bv_unsigned a0 + bv_unsigned a1 - 1)) [Z_to_bv 8 (stampck bs)]) in *;
  clearbody m2;
  step; step; step;
  release_frame FR2 ST2 (bv_unsigned sp);
  apply evtF_done; unfold QQ; cbv beta;
  do 10 eexists; exists m2; split; [reflexivity|];
  split; [exact B1|]; split; [exact B2|]; split; [apply rc_recsum_stamp|];
  split; [exact MU2|]; split; [exact WM2|]; split; [exact MI2 | exact ST2].

Theorem reac_ctrl_record_cksum_stamp_F_holds_on : reac_ctrl_record_cksum_stamp_contract_F_on.
Proof.
  unfold reac_ctrl_record_cksum_stamp_contract_F_on, REAC_CTRL_RECORD_CKSUM_STAMP,
    REAC_CTRL_RECORD_CKSUM_STAMP_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo bs Hn Hq Hqn Hlen HB HW HD ST HLO HCE HADR HWO RFR RGK RCK RDAT RSH.
  pose proof (rt_asan_rt m _ HCE HWO) as HRT.
  pose proof (rt_shadow_rd m _ _ _ HADR (fun x Hx => HWO x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m _ _ HADR) as HAD.
  (* the two runtime cells are read at literal addresses: keep unfolded copies of their rng premises *)
  pose proof RGK as RGz. unfold GOT_CELL_K in RGz.
  pose proof RCK as RCz. unfold CELL_K in RCz.
  set (off := ASAN_K) in HRT, HSR, HAD, RSH. clearbody off.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  pose proof (zr_word a0) as Ra. unfold inr64 in Ra.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  assert (Hlen' : Z.of_nat (length bs) = bv_unsigned a1 - 1) by lia.
  assert (SUB : sub_fp [(bv_unsigned sp - 16, bv_unsigned sp)]
                  [(bv_unsigned sp - 16, bv_unsigned sp);
                   (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)])
    by (intros x (H1 & _ & _); exact (conj H1 I)).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU SUB) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off _ _ _ _ HSR MU SUB) as HSR1.
  pose proof (asan_addressable_munch rsegs m m1 off _ _ _ _ HAD HSR MU SUB) as HAD1.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step.
  clear RG RC.
  step. step.
  match goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
  assert (TAIL : forall x5 x6 x11 x15 x16 x17,
    evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 t2 s0 s1 a0 x11
               (Z_to_bv 64 (psum bs (length bs))) (Z_to_bv 64 off) (Z_to_bv 64 (bv_unsigned a1 + -1))
               x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x83ca4) fc None m1 (seg_rom rsegs))).
  { intros x5 x6 x11 x15 x16 x17.
    pose proof (wr_at_store_ok rsegs m1 _ 1 0 1 HW ltac:(lia) ltac:(lia)) as HS.
    rewrite Z.add_0_r in HS.
    step.
    replace (bv_unsigned a1 + -1 + bv_unsigned a0) with (bv_unsigned a0 + bv_unsigned a1 - 1) by lia.
    step.
    rewrite (rc_ltu_ge a0 (Z_to_bv 64 (bv_unsigned a0 + bv_unsigned a1 - 1)))
      by (rewrite unsigned_lit by lia; lia).
    step. step. step. step.
    rewrite (rc_ubchk a0 (Z_to_bv 64 (bv_unsigned a0 + bv_unsigned a1 - 1)))
      by (try rewrite unsigned_lit by lia; lia).
    step.
    rewrite (rc_neq0w a0) by exact Hq.
    destruct (asan_shadow_read_at rsegs m1 off (bv_unsigned a0) (bv_unsigned a1) _ (bv_unsigned a1 - 1)
                ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 + off) HSR1 ltac:(lia)
                ltac:(unfold asan_shadow; rewrite Z.add_sub_assoc; reflexivity)) as (k & RK & BK).
    pose proof (HAD1 (bv_unsigned a1 - 1) k ltac:(lia) BK) as OK.
    unfold asan_ok in OK. rewrite Z.add_sub_assoc in OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (bv_unsigned a0 + bv_unsigned a1 - 1)) by lia. rewrite rc_shr3.
    (* the shadow byte of the stamp byte, the last byte of the range *)
    assert (RS1 : rng RNG ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 + off) 1)
      by (eapply rcsF_shadow1; [exact RSH | lia]).
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - stamp_storeF bs a0 a1 m m1 sp lo FR ST HB MU SUB WM WV HS QQ.
    - step.
      rewrite (unsigned_lit (bv_unsigned a0 + bv_unsigned a1 - 1)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((bv_unsigned a0 + bv_unsigned a1 - 1) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (bv_unsigned a0 + bv_unsigned a1 - 1) 8 ltac:(lia)); lia).
      replace ((bv_unsigned a0 + bv_unsigned a1 - 1) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      cbv iota.
      stamp_storeF bs a0 a1 m m1 sp lo FR ST HB MU SUB WM WV HS QQ. }
  step.
  unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 2)) with 2.
  destruct (Z.ltb_spec (bv_unsigned a1) 2) as [L|L]; cbv iota.
  - assert (P0 : psum bs (length bs) = 0)
      by (destruct bs; [reflexivity | cbn [length] in Hlen'; lia]).
    rewrite P0 in TAIL.
    step.
    apply TAIL.
  - step. step. step. step. step.
    refine (reac_ctrl_record_cksum_stamp_loopF ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t2 s0 s1 a0
              (Z_to_bv 64 (bv_unsigned a1 + -1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 off
              (bv_unsigned a1) bs _ QQ RNG Hq ltac:(lia) ltac:(lia) HB HSR1 HAD1 RDAT RSH
              (fun x5 x6 x11 x16 x17 => TAIL x5 x6 x11 (v_sltu (Z_to_bv 64 0) a0) x16 x17)
              (length bs) 0 t0 t1 a0 a0 (Z_to_bv 64 (bv_unsigned a1 + -1))
              ltac:(lia) ltac:(lia) ltac:(rewrite unsigned_lit by lia; lia) ltac:(lia) ltac:(lia)).
Qed.

(* The old statement, unchanged, in one line from the narrowed one (route (C), a Theorem Labs lane's X_on / X form).
   Its premise shadow_rw m is simply forgotten: this run never reads shadow through it. *)
Theorem reac_ctrl_record_cksum_stamp_F_holds : reac_ctrl_record_cksum_stamp_contract_F.
Proof. exact (reac_ctrl_record_cksum_stamp_contract_F_of_on reac_ctrl_record_cksum_stamp_F_holds_on). Qed.

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all. *)
Theorem reac_ctrl_record_cksum_stamp_holds_of_F : reac_ctrl_record_cksum_stamp_contract.
Proof. exact (reac_ctrl_record_cksum_stamp_contract_of_F reac_ctrl_record_cksum_stamp_F_holds). Qed.
