(* The footprint twin of reac_ctrl_block_cksum_stamp.v (image B; RECIPE.md step 1 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG, by the script of reac_ctrl_block_cksum_stamp.v over StepF's step. Each access of
   the run is closed from one rng premise of reac_ctrl_block_cksum_stamp_contract_F: the frame stores and loads of ra
   and s0, the two 8-byte loads of the GOT cell and of the runtime cell that holds the shadow offset, the 1-byte load
   of each of the 32 bytes of the block at q and the 1-byte store of the stamp byte at q + 31, and the 1-byte load of
   the shadow byte of each checked byte ((x >> 3) + ASAN_K, inside the byte-exact shadow span of the block).
   reac_ctrl_block_cksum_stamp.v and its theorem are unchanged; reac_ctrl_block_cksum_stamp_holds_of_F re-derives the
   old statement from the footprint form (reac_ctrl_block_cksum_stamp_contract_of_F, RNG_all). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcFin RcFinLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import
  RcAsanRT reac_ctrl_block_cksum_stamp_c reac_ctrl_block_cksum_stamp.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The shadow byte of a checked byte x of [a, b] is inside the byte-exact shadow span of [a, b]; Z.div is opaque to
   lia, so both bounds come from Z.div_le_mono, here in a context with no other division. *)
Lemma rbsF_shadow1 : forall RNG K a b x,
  rng RNG (a / 8 + K) (b / 8 - a / 8 + 1) -> a <= x <= b -> rng RNG (x / 8 + K) 1.
Proof.
  intros RNG K a b x H Hx. eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono a x 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono x b 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The twin of reac_ctrl_block_cksum_stamp.v's Section Loop: the same script, with the block and the shadow span of
   its checked bytes as rng premises. *)
Section LoopF.
  Variables (ra sp1 gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (B : list byte) (W : list ivl)
    (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hq : 0 < q.
  Hypothesis Hq32 : q + 32 <= 2^64.
  Hypothesis Hlen : length B = 32%nat.
  Hypothesis HB : bytes_at rsegs m q B.
  Hypothesis HSR : asan_shadow_rd rsegs m off q 32 W.
  Hypothesis HAD : asan_addressable rsegs m off q 32.
  Hypothesis RDAT : rng RNG q 32.
  Hypothesis RSH : rng RNG (q / 8 + off) ((q + 31) / 8 - q / 8 + 1).

  Abbreviation ST pc x5 x11 x12 x14 x16 x17 :=
    (MS (mkR ra sp1 gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 q) x11 x12 (Z_to_bv 64 off) x14 (Z_to_bv 64 1) x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x5 x11 x14 x16 x17,
    evtF rsegs RNG Q (ST 0x83b54 x5 x11 (Z_to_bv 64 (psum B 31)) x14 x16 x17).

  Lemma loopF : forall n i x5 x17,
    (i + n = 31)%nat -> (0 < n)%nat ->
    evtF rsegs RNG Q (ST 0x83b04 x5 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum B i))
                    (Z_to_bv 64 (31 - Z.of_nat i)) (Z_to_bv 64 (q + Z.of_nat i)) x17).
  Proof using Hq Hq32 Hlen HB HSR HAD RDAT RSH EXIT.
    induction n as [|n IH]; intros i x5 x17 Hin Hn; [lia|].
    pose proof (psum_range B i) as PR.
    assert (BODY : forall y5 y17,
      evtF rsegs RNG Q (ST 0x83b28 y5 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum B i))
                      (Z_to_bv 64 (31 - Z.of_nat i)) (Z_to_bv 64 (q + Z.of_nat i)) y17)).
    { intros y5 y17.
      pose proof (rd_byte rsegs m q B i HB ltac:(lia)) as RD.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rcf_eqb (31 - Z.of_nat i + -1) 0) by lia.
      destruct n as [|n].
      - replace (31 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. cbv iota.
        step.
        replace i with 30%nat in * by lia.
        apply EXIT.
      - replace (31 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb]. cbv iota.
        replace (31 - Z.of_nat i + -1) with (31 - Z.of_nat (S i)) by lia.
        replace (q + Z.of_nat i + 1) with (q + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    step.
    rewrite (rcf_ltu (q + Z.of_nat i) q) by lia.
    replace (q + Z.of_nat i <? q) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step. step. step.
    rewrite (rcf_chk (q + Z.of_nat i)) by lia. cbv iota.
    step.
    rewrite (rcf_eqb q 0) by lia. replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    destruct (asan_shadow_read rsegs m off q 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_shr3.
    (* the shadow byte of the checked byte *)
    assert (RS1 : rng RNG ((q + Z.of_nat i) / 8 + off) 1)
      by (eapply rbsF_shadow1; [exact RSH | lia]).
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((q + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (q + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((q + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.

  Lemma loop0F : forall x5 x17,
    evtF rsegs RNG Q (ST 0x83b04 x5 (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 31) (Z_to_bv 64 q) x17).
  Proof using Hq Hq32 Hlen HB HSR HAD RDAT RSH EXIT.
    intros x5 x17. pose proof (loopF 31 0 x5 x17 eq_refl ltac:(lia)) as L.
    replace (q + Z.of_nat 0) with q in L by lia. exact L.
  Qed.
End LoopF.

(* The twin of reac_ctrl_block_cksum_stamp.v's bcs_store: the same script on evtF goals (evtF_done for the
   postcondition). *)
Ltac bcs_storeF B q m m1 sp lo FR ST HB HW MU SUB WM WV QQ Hlen :=
  let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let MI2 := fresh "MI2" in let HB2 := fresh "HB2" in
  let HW2 := fresh "HW2" in let FR2 := fresh "FR2" in let ST2 := fresh "ST2" in let m2 := fresh "m2" in
  step; step;
  first [ rewrite (bcs_neg (psum B 31)) by lia | rewrite (bcs_neg' (psum B 31)) ];
  change (Z_to_bv 64 (q + 31)) with (wa (q + Z.of_nat 31));
  destruct (rcf_store1 rsegs _ m m1 q B 31 (Z_to_bv 8 ((- psum B 31) mod 256))
              (munch_weaken _ _ m m1 SUB MU) WM
              (fun HI => rc_mem_inv_frame rsegs m m1 _ _ HI MU WV)
              HB ltac:(rewrite Hlen; exact HW) ltac:(lia) ltac:(cbn [inside]; right; left; lia))
    as (MU2 & WM2 & MI2 & HB2 & HW2);
  pose proof (rw_cells_frame rsegs m1 _ _ (q + Z.of_nat 31) [Z_to_bv 8 ((- psum B 31) mod 256)] FR
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize length Nat.add]; lia)) as FR2;
  pose proof (stk_write rsegs m1 lo (bv_unsigned sp + -16) (q + Z.of_nat 31) [Z_to_bv 8 ((- psum B 31) mod 256)]
                ST ltac:(lia) ltac:(cbn [length]; lia)) as ST2;
  set (m2 := write_to_mem m1 (wa (q + Z.of_nat 31)) [Z_to_bv 8 ((- psum B 31) mod 256)]) in *;
  clearbody m2;
  step; step; step;
  release_frame FR2 ST2 (bv_unsigned sp);
  apply evtF_done; unfold QQ; cbv beta;
  do 9 eexists; exists m2; split; [reflexivity|];
  split; [exact MU2|]; split; [exact WM2|]; split; [exact MI2|];
  split; [rewrite Hlen in HW2; exact (rcf_rw32 rsegs m2 q (stamp32 B) (rcf_stamp32_len B Hlen) HB2 HW2)|];
  split; [exact (rcf_stamp32_sum B Hlen) | exact ST2].

Theorem reac_ctrl_block_cksum_stamp_F_holds_on : reac_ctrl_block_cksum_stamp_contract_F_on.
Proof.
  unfold reac_ctrl_block_cksum_stamp_contract_F_on, REAC_CTRL_BLOCK_CKSUM_STAMP, REAC_CTRL_BLOCK_CKSUM_STAMP_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q lo B Hq Hq32 -> HRW HD ST HLO HCE HADR HWO RFR RGK RCK RDAT RSH.
  destruct (rcf_rw32_inv rsegs m q B HRW) as (Hlen & HB & HW). clear HRW.
  assert (HL32 : Z.of_nat (length B) = 32) by lia.
  pose proof (rt_asan_rt m _ HCE HWO) as HRT.
  pose proof (rt_shadow_rd m q 32 _ HADR (fun x Hx => HWO x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m q 32 HADR) as HAD.
  (* the two runtime cells are read at literal addresses: keep unfolded copies of their rng premises *)
  pose proof RGK as RGz. unfold GOT_CELL_K in RGz.
  pose proof RCK as RCz. unfold CELL_K in RCz.
  set (off := ASAN_K) in HRT, HSR, HAD, RSH. clearbody off.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  assert (SUB : sub_fp [(bv_unsigned sp - 16, bv_unsigned sp)]
                  [(bv_unsigned sp - 16, bv_unsigned sp); (q + 31, q + 32)])
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
  step. step. step. step.
  clear RG RC.
  step. step.
  rewrite v_sltu_b2z. rewrite (unsigned_lit q) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  replace (0 <? q) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.b2z true) with 1.
  step. step.
  match goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
  assert (TAIL : forall x5 x11 x14 x16 x17,
    evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 q) x11
               (Z_to_bv 64 (psum B 31)) (Z_to_bv 64 off) x14 (Z_to_bv 64 1) x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x83b54) fc None m1 (seg_rom rsegs))).
  { intros x5 x11 x14 x16 x17.
    pose proof (psum_range B 31) as R31. change (Z.of_nat 31) with 31 in R31.
    step. step.
    rewrite (rcf_ltu_neg q (-31)) by lia.
    replace (q <? 2^64 + -31) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
    step.
    destruct (asan_shadow_read rsegs m1 off q 32 _ 31 HSR1 ltac:(lia)) as (k & RK & BK).
    pose proof (HAD1 31 k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    assert (HS : store_ok rsegs m1 (wa (q + 31)) 1 = true)
      by (apply (wr_at_store_ok rsegs m1 q 32 31 1 HW); lia).
    step.
    rewrite (unsigned_lit (q + 31)) by lia. rewrite rc_shr3.
    (* the shadow byte of the stamp byte, the last byte of the block *)
    assert (RS1 : rng RNG ((q + 31) / 8 + off) 1)
      by (eapply rbsF_shadow1; [exact RSH | lia]).
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - bcs_storeF B q m m1 sp lo FR ST HB HW MU SUB WM WV QQ Hlen.
    - step.
      rewrite (unsigned_lit (q + 31)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((q + 31) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (q + 31) 8 ltac:(lia)); lia).
      replace ((q + 31) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      cbv iota.
      bcs_storeF B q m m1 sp lo FR ST HB HW MU SUB WM WV QQ Hlen. }
  eapply loop0F; first [exact TAIL | eassumption].
Qed.

(* The old statement, unchanged, in one line from the narrowed one (route (C), a Theorem Labs lane's X_on / X form).
   Its premise shadow_rw m is simply forgotten: this run never reads shadow through it. *)
Theorem reac_ctrl_block_cksum_stamp_F_holds : reac_ctrl_block_cksum_stamp_contract_F.
Proof. exact (reac_ctrl_block_cksum_stamp_contract_F_of_on reac_ctrl_block_cksum_stamp_F_holds_on). Qed.

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all. *)
Theorem reac_ctrl_block_cksum_stamp_holds_of_F : reac_ctrl_block_cksum_stamp_contract.
Proof. exact (reac_ctrl_block_cksum_stamp_contract_of_F reac_ctrl_block_cksum_stamp_F_holds). Qed.
