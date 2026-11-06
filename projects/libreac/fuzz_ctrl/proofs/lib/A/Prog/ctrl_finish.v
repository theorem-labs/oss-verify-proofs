From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcFin RcFinLib RcRecLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT ctrl_finish_c.
Import ListNotations.
Open Scope Z_scope.

Lemma cfa_neg : forall s, 0 <= s < 2^64 ->
  le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((- s) mod 256)].
Proof.
  intros s Hs. rewrite (unsigned_lit s) by lia.
  unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma cfa_neg' : forall s, le1 (Z_to_bv 64 (0 - s)) = [Z_to_bv 8 ((- s) mod 256)].
Proof.
  intros s. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The block stamp loop (+0x100 .. +0x13c): 31 turns, each with the shadow check of its byte. *)
Section Blk.
  Variables (ra sp1 gp tp x5 x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (p off : Z) (bs : list byte) (W : list ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.
  Hypothesis Hl : length bs = 32%nat.
  Hypothesis HB : bytes_at rsegs mm (p + 18) bs.
  Hypothesis HSR : asan_shadow_rd rsegs mm off (p + 18) 32 W.
  Hypothesis HAD : asan_addressable rsegs mm off (p + 18) 32.

  Abbreviation BS pc x11 x12 x13 x15 x16 x17 :=
    (MS (mkR ra sp1 gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 p) x11 x12 x13 (Z_to_bv 64 off) x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Hypothesis EXIT : forall x12 x13 x15 x16 x17,
    evt rsegs Q (BS 0x85ad0 (Z_to_bv 64 (psum bs 31)) x12 x13 x15 x16 x17).

  Lemma blk_loop : forall k i x16 x17, (i + k = 31)%nat -> (0 < k)%nat ->
    evt rsegs Q (BS 0x85a94 (Z_to_bv 64 (psum bs i)) (Z_to_bv 64 (p + 18 + Z.of_nat i))
                    (Z_to_bv 64 (31 - Z.of_nat i)) (Z_to_bv 64 (p + 18 + Z.of_nat i)) x16 x17).
  Proof using Hp Hp50 Hl HB HSR HAD EXIT.
    induction k as [|k IH]; intros i x16 x17 Hik Hk; [lia|].
    pose proof (psum_range bs i) as PR.
    assert (BODY : forall y16 y17,
      evt rsegs Q (BS 0x85aa4 (Z_to_bv 64 (psum bs i)) (Z_to_bv 64 (p + 18 + Z.of_nat i))
                      (Z_to_bv 64 (31 - Z.of_nat i)) (Z_to_bv 64 (p + 18 + Z.of_nat i)) y16 y17)).
    { intros y16 y17.
      pose proof (rd_byte rsegs mm (p + 18) bs i HB ltac:(lia)) as RD.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rcf_eqb (31 - Z.of_nat i + -1) 0) by lia.
      destruct k as [|k].
      - replace (31 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. cbv iota.
        step.
        replace i with 30%nat in * by lia.
        apply EXIT.
      - replace (31 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb]. cbv iota.
        replace (31 - Z.of_nat i + -1) with (31 - Z.of_nat (S i)) by lia.
        replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    destruct (asan_shadow_read rsegs mm off (p + 18) 32 W (Z.of_nat i) HSR ltac:(lia)) as (k0 & RK & BK).
    pose proof (HAD (Z.of_nat i) k0 ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k0) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k0)) by lia.
    destruct (Z.eqb_spec (bv_signed k0) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 18 + Z.of_nat i) mod 8) (bv_signed k0))
        by (pose proof (Z.mod_pos_bound (p + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((p + 18 + Z.of_nat i) mod 8 <? bv_signed k0) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.

  Lemma blk0 : forall x11 x13 x15 x16 x17,
    evt rsegs Q (BS 0x85a88 x11 (Z_to_bv 64 (p + 18)) x13 x15 x16 x17).
  Proof using Hp Hp50 Hl HB HSR HAD EXIT.
    intros x11 x13 x15 x16 x17.
    step. step. step.
    pose proof (blk_loop 31 0 x16 x17 eq_refl ltac:(lia)) as L.
    replace (p + 18 + Z.of_nat 0) with (p + 18) in L by lia. exact L.
  Qed.
End Blk.

(* The record stamp loop (+0x90 .. +0xbc): n - 1 turns, each with the shadow check of its byte. *)
Section Rec.
  Variables (ra sp1 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x12 x15 x16 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (p off o n : Z) (Bo : list byte)
    (W : list ivl) (Q : machine_state -> Prop).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.
  Hypothesis Ho : 0 <= o.
  Hypothesis Hn : 2 <= n.
  Hypothesis Hon : o + n <= 31.
  Hypothesis HL : (Z.to_nat (n - 1) <= length Bo)%nat.
  Hypothesis HBo : bytes_at rsegs mm (p + 18 + o) Bo.
  Hypothesis HSR : asan_shadow_rd rsegs mm off (p + 18) 32 W.
  Hypothesis HAD : asan_addressable rsegs mm off (p + 18) 32.

  Abbreviation RS pc x5 x6 x7 x11 x13 x17 :=
    (MS (mkR ra sp1 gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 p) x11 x12 x13 (Z_to_bv 64 off) x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Hypothesis EXIT : forall x5 x6 x7 x11 x17,
    evt rsegs Q (RS 0x85a64 x5 x6 x7 x11 (Z_to_bv 64 (psum Bo (Z.to_nat (n - 1)))) x17).

  Lemma rec_loop : forall k i x5 x6 x7 x11 x17,
    (i + k = Z.to_nat (n - 1))%nat -> (0 < k)%nat ->
    bv_unsigned x11 = p + 18 + o + Z.of_nat i ->
    bv_unsigned x5 = p + 18 + o + Z.of_nat i ->
    bv_unsigned x17 = Z.of_nat k ->
    evt rsegs Q (RS 0x85a24 x5 x6 x7 x11 (Z_to_bv 64 (psum Bo i)) x17).
  Proof using Hp Hp50 Ho Hn Hon HL HBo HSR HAD EXIT.
    induction k as [|k IH]; intros i x5 x6 x7 x11 x17 Hik Hk H11 H5 H17; [lia|].
    pose proof (psum_range Bo i) as PR.
    assert (BODY : forall y6 y7, evt rsegs Q (RS 0x85a34 x5 y6 y7 x11 (Z_to_bv 64 (psum Bo i)) x17)).
    { intros y6 y7.
      pose proof (rd_byte rsegs mm (p + 18 + o) Bo i HBo ltac:(lia)) as RD.
      rewrite <- H5 in RD. rewrite (wa_of_var x5 (bv_unsigned x5) eq_refl) in RD.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rc_eqb0 (bv_unsigned x17 + -1)) by lia.
      destruct k as [|k].
      - replace (bv_unsigned x17 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. cbv iota.
        step.
        replace (S i) with (Z.to_nat (n - 1)) by lia.
        apply EXIT.
      - replace (bv_unsigned x17 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb]. cbv iota.
        apply (IH (S i)); first [lia | rewrite unsigned_lit by lia; lia]. }
    destruct (asan_shadow_read_at rsegs mm off (p + 18) 32 W (o + Z.of_nat i) ((p + 18 + o + Z.of_nat i) / 8 + off)
                HSR ltac:(lia)
                ltac:(unfold asan_shadow; replace (p + 18 + (o + Z.of_nat i)) with (p + 18 + o + Z.of_nat i) by lia;
                      reflexivity)) as (k0 & RK & BK).
    pose proof (HAD (o + Z.of_nat i) k0 ltac:(lia) BK) as OK.
    unfold asan_ok in OK. replace (p + 18 + (o + Z.of_nat i)) with (p + 18 + o + Z.of_nat i) in OK by lia.
    pose proof (rc_byte_signed k0) as KR.
    clear BK.
    step.
    rewrite H11. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k0)) by lia.
    destruct (Z.eqb_spec (bv_signed k0) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite H11. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 18 + o + Z.of_nat i) mod 8) (bv_signed k0))
        by (pose proof (Z.mod_pos_bound (p + 18 + o + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((p + 18 + o + Z.of_nat i) mod 8 <? bv_signed k0) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End Rec.

(* The store of the block's check byte at p + 49 and the epilogue (+0x150 .. +0x160). *)
Ltac blk_store bs p m mm sp lo FR ST HB HW Hl MU WM MI EQF CL QQ :=
  let MU3 := fresh "MU3" in let WM3 := fresh "WM3" in let MI3 := fresh "MI3" in let HB3 := fresh "HB3" in
  let HW3 := fresh "HW3" in let FR3 := fresh "FR3" in let ST3 := fresh "ST3" in let m3 := fresh "m3" in
  step; step;
  first [ rewrite (cfa_neg (psum bs 31)) by lia | rewrite (cfa_neg' (psum bs 31)) ];
  replace (Z_to_bv 64 (p + 49)) with (wa (p + 18 + Z.of_nat 31)) by (unfold wa; f_equal; lia);
  destruct (rcf_store1 rsegs _ m mm (p + 18) bs 31 (Z_to_bv 8 ((- psum bs 31) mod 256)) MU WM MI HB
              ltac:(rewrite Hl; exact HW) ltac:(lia) ltac:(cbn [inside]; lia))
    as (MU3 & WM3 & MI3 & HB3 & HW3);
  pose proof (rw_cells_frame rsegs mm _ _ (p + 18 + Z.of_nat 31) [Z_to_bv 8 ((- psum bs 31) mod 256)] FR
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize length Nat.add]; lia)) as FR3;
  pose proof (stk_write rsegs mm lo (bv_unsigned sp + -16) (p + 18 + Z.of_nat 31) [Z_to_bv 8 ((- psum bs 31) mod 256)]
                ST ltac:(lia) ltac:(cbn [length]; lia)) as ST3;
  set (m3 := write_to_mem mm (wa (p + 18 + Z.of_nat 31)) [Z_to_bv 8 ((- psum bs 31) mod 256)]) in *;
  clearbody m3;
  step; step; step;
  release_frame FR3 ST3 (bv_unsigned sp);
  apply evt_done; unfold QQ; cbv beta;
  do 11 eexists; exists m3; split; [reflexivity|];
  split; [exact MU3|]; split; [exact WM3|]; split; [exact MI3|]; split; [exact ST3|];
  intros _; rewrite Hl in HW3;
  split; [rewrite EQF; exact (rcf_rw32 rsegs m3 (p + 18) (stamp32 bs) (rcf_stamp32_len bs Hl) HB3 HW3) | exact CL].

(* From +0xf4 (the block stamp) to the return, on the memory mm that holds the block bs. *)
Ltac blk_path bs p off m mm sp lo FR ST HB HW Hl HSR HAD MU WM MI EQF CL QQ :=
  eapply blk0;
  [ lia | lia | exact Hl | exact HB | exact HSR | exact HAD | ];
  let y12 := fresh "y12" in let y13 := fresh "y13" in let y15 := fresh "y15" in let y16 := fresh "y16" in
  let y17 := fresh "y17" in let k := fresh "k" in let RK := fresh "RK" in let BK := fresh "BK" in
  let OK := fresh "OK" in let KR := fresh "KR" in let R31 := fresh "R31" in let HS := fresh "HS" in
  let K0 := fresh "K0" in
  intros y12 y13 y15 y16 y17;
  pose proof (psum_range bs 31) as R31; change (Z.of_nat 31) with 31 in R31;
  step;
  destruct (asan_shadow_read_at rsegs mm off (p + 18) 32 _ 31 ((p + 49) / 8 + off) HSR ltac:(lia)
              ltac:(unfold asan_shadow; replace (p + 18 + 31) with (p + 49) by lia; reflexivity)) as (k & RK & BK);
  pose proof (HAD 31 k ltac:(lia) BK) as OK;
  unfold asan_ok in OK; replace (p + 18 + 31) with (p + 49) in OK by lia;
  pose proof (rc_byte_signed k) as KR;
  clear BK;
  assert (HS : store_ok rsegs mm (wa (p + 49)) 1 = true)
    by (replace (p + 49) with (p + 18 + 31) by lia; apply (wr_at_store_ok rsegs mm (p + 18) 32 31 1 HW); lia);
  step;
  rewrite (unsigned_lit (p + 49)) by lia; rewrite rc_shr3;
  step;
  step;
  clear RK;
  step;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
  [ blk_store bs p m mm sp lo FR ST HB HW Hl MU WM MI EQF CL QQ
  | step;
    rewrite (unsigned_lit (p + 49)) by lia; rewrite rc_land7;
    step;
    rewrite (rc_lts_signed ((p + 49) mod 8) (bv_signed k))
      by (pose proof (Z.mod_pos_bound (p + 49) 8 ltac:(lia)); lia);
    replace ((p + 49) mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
    cbv iota;
    blk_store bs p m mm sp lo FR ST HB HW Hl MU WM MI EQF CL QQ ].

Theorem ctrl_finish_holds : ctrl_finish_contract.
Proof.
  unfold ctrl_finish_contract, CTRL_FINISH, CTRL_FINISH_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p f c o n lo row B -> -> Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE HSW HADf HADp HWO.
  assert (Z20 : zxb (nth 20 row (Z_to_bv 8 0)) = Z_to_bv 64 c) by (unfold zxb; rewrite <- Hc; reflexivity).
  assert (Z18 : zxb (nth 18 row (Z_to_bv 8 0)) = Z_to_bv 64 o) by (unfold zxb; rewrite <- Ho; reflexivity).
  assert (Z19 : zxb (nth 19 row (Z_to_bv 8 0)) = Z_to_bv 64 n) by (unfold zxb; rewrite <- Hn; reflexivity).
  pose proof (byte_range (nth 20 row (Z_to_bv 8 0))) as BRc.
  pose proof (byte_range (nth 18 row (Z_to_bv 8 0))) as BRo.
  pose proof (byte_range (nth 19 row (Z_to_bv 8 0))) as BRn.
  unfold ubat in Hc, Ho, Hn.
  assert (Hcases : c = 0 \/ c = 1 \/ c = 2) by lia.
  pose proof (bytes_at_bound rsegs m f row HR) as BF.
  pose proof (rt_asan_rt m _ HCE HWO) as HRT.
  pose proof (rt_shadow_rd m (f + 18) 3 _ HADf (fun x Hx => HWO x (or_intror (or_intror Hx)))) as HSRf.
  pose proof (rt_addressable m (f + 18) 3 HADf) as HAf.
  assert (HSRp : c = 1 \/ c = 2 ->
            asan_shadow_rd rsegs m ASAN_K (p + 18) 32 ((bv_unsigned sp - 16, bv_unsigned sp) :: fin_w c o n p))
    by (intros CC; exact (rt_shadow_rd m (p + 18) 32 _ (HADp CC) (fun x Hx => HWO x (or_intror (or_intror Hx))))).
  assert (HAp : c = 1 \/ c = 2 -> asan_addressable rsegs m ASAN_K (p + 18) 32)
    by (intros CC; exact (rt_addressable m (p + 18) 32 (HADp CC))).
  set (off := ASAN_K) in HRT, HSRf, HAf, HSRp, HAp. clearbody off.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  assert (SUB : sub_fp [(bv_unsigned sp - 16, bv_unsigned sp)]
                  ((bv_unsigned sp - 16, bv_unsigned sp) :: fin_w c o n p))
    by (intros x (H1 & _); exact (conj H1 I)).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU SUB) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off _ _ _ _ HSRf MU SUB) as HSRf1.
  pose proof (asan_addressable_munch rsegs m m1 off _ _ _ _ HAf HSRf MU SUB) as HAf1.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  pose proof (fun HI => rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) as MI1.
  pose proof (rd_byte rsegs m1 f row 20 HR ltac:(lia)) as RD20. change (Z.of_nat 20) with 20 in RD20.
  pose proof (rd_byte rsegs m1 f row 18 HR ltac:(lia)) as RD18. change (Z.of_nat 18) with 18 in RD18.
  pose proof (rd_byte rsegs m1 f row 19 HR ltac:(lia)) as RD19. change (Z.of_nat 19) with 19 in RD19.
  match goal with |- evt _ ?Q _ => set (QQ := Q) end.
  step. step. step.
  clear RG RC.
  step.
  (* +0x18 .. +0x24: the shadow check of f + 20 *)
  destruct (asan_shadow_read_at rsegs m1 off (f + 18) 3 _ 2 ((f + 20) / 8 + off) HSRf1 ltac:(lia)
              ltac:(unfold asan_shadow; replace (f + 18 + 2) with (f + 20) by lia; reflexivity)) as (k20 & RK & BK).
  pose proof (HAf1 2 k20 ltac:(lia) BK) as OK. unfold asan_ok in OK. replace (f + 18 + 2) with (f + 20) in OK by lia.
  pose proof (rc_byte_signed k20) as KR. clear BK.
  assert (PRO : forall y13 y15,
    evt rsegs QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f)
               (Z_to_bv 64 (f + 20)) y13 (Z_to_bv 64 off) y15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x859bc) fc None m1 (seg_rom rsegs))).
  { intros y13 y15. clear RK.
    step. rewrite Z20. step. step. step.
    rewrite (rcf_eqb c 1) by lia.
    destruct Hcases as [C | [C | C]].
    - (* c = 0: return *)
      replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. step.
      rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold QQ. cbv beta. rewrite C in Hc. subst c.
      do 11 eexists. exists m1. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
      intros [H | H]; discriminate H.
    - (* c = 1: block stamp *)
      replace (c =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      assert (CC : c = 1 \/ c = 2) by lia.
      destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW CC)) as (Hl & HB & HW).
      pose proof (HDp CC) as HDp'.
      pose proof (rc_bytes_at_munch rsegs _ m m1 (p + 18) B HB MU
                    ltac:(intros x Hx; cbn [outside]; split; [lia | exact I])) as HB1.
      pose proof (wr_at_transport rsegs m m1 (p + 18) 32 HW WM) as HW1.
      pose proof (asan_shadow_rd_munch rsegs m m1 off _ _ _ _ (HSRp CC) MU SUB) as HSRp1.
      pose proof (asan_addressable_munch rsegs m m1 off _ _ _ _ (HAp CC) (HSRp CC) MU SUB) as HAp1.
      rewrite C in Hc. subst c.
      pose proof (munch_weaken [(bv_unsigned sp + -16, bv_unsigned sp)]
                    [(bv_unsigned sp + -16, bv_unsigned sp); (p + 49, p + 50)] m m1
                    (fun x Hx => conj (proj1 Hx) I) MU) as MUW.
      assert (EQF : fin 1 o n B = stamp32 B) by reflexivity.
      assert (CL : closes 1 o n (fin 1 o n B) /\ (closes 1 o n B -> fin 1 o n B = B))
        by (split; [apply rcf_closes_fin; [exact Hl | left; reflexivity | intros H; discriminate H]
                   | intros HC; apply rcf_fin_same; [exact Hl | left; reflexivity | intros H; discriminate H
                                                     | exact HC]]).
      blk_path B p off m m1 sp lo FR ST HB1 HW1 Hl HSRp1 HAp1 MUW WM MI1 EQF CL QQ.
    - (* c = 2: record stamp, then block stamp *)
      replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. step.
      rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      assert (CC : c = 1 \/ c = 2) by lia.
      destruct (Hrec C) as [Hn2 Hon].
      destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW CC)) as (Hl & HB & HW).
      pose proof (HDp CC) as HDp'.
      pose proof (rc_bytes_at_munch rsegs _ m m1 (p + 18) B HB MU
                    ltac:(intros x Hx; cbn [outside]; split; [lia | exact I])) as HB1.
      pose proof (wr_at_transport rsegs m m1 (p + 18) 32 HW WM) as HW1.
      pose proof (asan_shadow_rd_munch rsegs m m1 off _ _ _ _ (HSRp CC) MU SUB) as HSRp1.
      pose proof (asan_addressable_munch rsegs m m1 off _ _ _ _ (HAp CC) (HSRp CC) MU SUB) as HAp1.
      rewrite C in Hc. subst c.
      pose proof (munch_weaken [(bv_unsigned sp + -16, bv_unsigned sp)]
                    [(bv_unsigned sp + -16, bv_unsigned sp); (p + 18 + o + n - 1, p + 18 + o + n);
                                  (p + 49, p + 50)] m m1 (fun x Hx => conj (proj1 Hx) I) MU) as MUW.
      assert (Ho0 : 0 <= o) by lia.
      (* +0x40 .. +0x50: the shadow check of f + 18 *)
      step.
      destruct (asan_shadow_read_at rsegs m1 off (f + 18) 3 _ 0 ((f + 18) / 8 + off) HSRf1 ltac:(lia)
                  ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k18 & RK18 & BK18).
      pose proof (HAf1 0 k18 ltac:(lia) BK18) as OK18. unfold asan_ok in OK18. rewrite Z.add_0_r in OK18.
      pose proof (rc_byte_signed k18) as KR18. clear BK18.
      assert (R1 : forall y15 y16,
        evt rsegs QQ
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f)
                   (Z_to_bv 64 (p + 18)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 off) y15 y16 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x859e8) fc None m1 (seg_rom rsegs))).
      { intros z15 z16. clear RK18.
        (* +0x54 .. +0x68: the shadow check of f + 19 and the load of o *)
        step.
        destruct (asan_shadow_read_at rsegs m1 off (f + 18) 3 _ 1 ((f + 19) / 8 + off) HSRf1 ltac:(lia)
                    ltac:(unfold asan_shadow; replace (f + 18 + 1) with (f + 19) by lia; reflexivity))
          as (k19 & RK19 & BK19).
        pose proof (HAf1 1 k19 ltac:(lia) BK19) as OK19. unfold asan_ok in OK19.
        replace (f + 18 + 1) with (f + 19) in OK19 by lia.
        pose proof (rc_byte_signed k19) as KR19. clear BK19.
        assert (R2 : forall y15 y16,
          evt rsegs QQ
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 o)
                     (Z_to_bv 64 (p + 18)) (Z_to_bv 64 (f + 19)) (Z_to_bv 64 off) y15 y16 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x85a00) fc None m1 (seg_rom rsegs))).
        { intros w15 w16. clear RK19.
          step. rewrite Z19.
          step. step. step.
          rewrite (rcf_ltu n 2) by lia. replace (n <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
          step. step. step. step. step.
          (* +0x90 .. +0xbc: the record stamp loop *)
          assert (HLo : (Z.to_nat (n - 1) <= length (skipn (Z.to_nat o) B))%nat) by (rewrite length_skipn; lia).
          pose proof (rcf_bytes_skipn rsegs m1 (p + 18) B (Z.to_nat o) ltac:(lia) HB1) as HBo.
          replace (p + 18 + Z.of_nat (Z.to_nat o)) with (p + 18 + o) in HBo by lia.
          eapply rec_loop with (o := o) (n := n) (Bo := skipn (Z.to_nat o) B) (k := Z.to_nat (n - 1)) (i := 0%nat);
            [ lia | lia | lia | lia | lia | exact HLo | exact HBo | exact HSRp1 | exact HAp1 | | lia | lia
            | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ].
          intros x5 x6 x7 x11 x17.
          pose proof (psum_range (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) as PRo.
          step. step.
          (* +0xd8 .. +0xe4: the shadow check of p + 18 + o + n - 1 *)
          destruct (asan_shadow_read_at rsegs m1 off (p + 18) 32 _ (o + n - 1) ((p + 18 + o + n + -1) / 8 + off)
                      HSRp1 ltac:(lia)
                      ltac:(unfold asan_shadow; replace (p + 18 + (o + n - 1)) with (p + 18 + o + n + -1) by lia;
                            reflexivity)) as (k3 & RK3 & BK3).
          pose proof (HAp1 (o + n - 1) k3 ltac:(lia) BK3) as OK3. unfold asan_ok in OK3.
          replace (p + 18 + (o + n - 1)) with (p + 18 + o + n + -1) in OK3 by lia.
          pose proof (rc_byte_signed k3) as KR3. clear BK3.
          assert (HS : store_ok rsegs m1 (wa (p + 18 + o + n + -1)) 1 = true)
            by (replace (p + 18 + o + n + -1) with (p + 18 + (o + n - 1)) by lia;
                apply (wr_at_store_ok rsegs m1 (p + 18) 32 (o + n - 1) 1 HW1); lia).
          assert (RST : forall v15 v16,
            evt rsegs QQ
              (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 p)
                       (Z_to_bv 64 (p + 18 + o + n + -1)) (Z_to_bv 64 (p + 18))
                       (Z_to_bv 64 (psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1)))) (Z_to_bv 64 off) v15 v16 x17
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x85a7c) fc None m1 (seg_rom rsegs))).
          { intros v15 v16. clear RK3.
            (* +0xe8 .. +0xf0: the record stamp's store *)
            step. step. step.
            rewrite (rcf_rec_byte (psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1)))) by lia.
            replace (Z_to_bv 64 (p + 18 + o + n + -1)) with (wa (p + 18 + Z.of_nat (Z.to_nat (o + n - 1))))
              by (unfold wa; f_equal; lia).
            destruct (rcf_store1 rsegs _ m m1 (p + 18) B (Z.to_nat (o + n - 1))
                        (Z_to_bv 8 ((- psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) mod 128))
                        MUW WM MI1 HB1 ltac:(rewrite Hl; exact HW1) ltac:(lia) ltac:(cbn [inside]; lia))
              as (MU2 & WM2 & MI2 & HB2 & HW2).
            rewrite Hl in HW2.
            pose proof (rw_cells_frame rsegs m1 _ _ (p + 18 + Z.of_nat (Z.to_nat (o + n - 1)))
                          [Z_to_bv 8 ((- psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) mod 128)] FR
                          ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize length Nat.add]; lia)) as FR2.
            pose proof (stk_write rsegs m1 lo (bv_unsigned sp + -16) (p + 18 + Z.of_nat (Z.to_nat (o + n - 1)))
                          [Z_to_bv 8 ((- psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) mod 128)]
                          ST ltac:(lia) ltac:(cbn [length]; lia)) as ST2.
            set (m2 := write_to_mem m1 (wa (p + 18 + Z.of_nat (Z.to_nat (o + n - 1))))
                         [Z_to_bv 8 ((- psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) mod 128)]) in *.
            clearbody m2.
            pose proof (asan_shadow_rd_munch rsegs m m2 off _ _ _ _ (HSRp CC) MU2 (fun x Hx => Hx)) as HSRp2.
            pose proof (asan_addressable_munch rsegs m m2 off _ _ _ _ (HAp CC) (HSRp CC) MU2 (fun x Hx => Hx))
              as HAp2.
            assert (HlR : length (rstamp B o n) = 32%nat) by (apply rcf_rstamp_len; lia).
            assert (EQF : fin 2 o n B = stamp32 (rstamp B o n)) by reflexivity.
            assert (CL : closes 2 o n (fin 2 o n B) /\ (closes 2 o n B -> fin 2 o n B = B))
              by (split; [apply rcf_closes_fin; [exact Hl | right; reflexivity | intros _; split; [lia | split; lia]]
                         | intros HC; apply rcf_fin_same;
                           [exact Hl | right; reflexivity | intros _; split; [lia | split; lia] | exact HC]]).
            blk_path (rstamp B o n) p off m m2 sp lo FR2 ST2 HB2 HW2 HlR HSRp2 HAp2 MU2 WM2 MI2 EQF CL QQ. }
          step.
          rewrite (unsigned_lit (p + 18 + o + n + -1)) by lia. rewrite rc_shr3.
          step. step. clear RK3.
          step.
          unfold sxb. rewrite (rc_eqb0_signed (bv_signed k3)) by lia.
          destruct (Z.eqb_spec (bv_signed k3) 0) as [K0|K0]; cbn [negb].
          - apply RST.
          - step.
            rewrite (unsigned_lit (p + 18 + o + n + -1)) by lia. rewrite rc_land7.
            step.
            rewrite (rc_lts_signed ((p + 18 + o + n + -1) mod 8) (bv_signed k3))
              by (pose proof (Z.mod_pos_bound (p + 18 + o + n + -1) 8 ltac:(lia)); lia).
            replace ((p + 18 + o + n + -1) mod 8 <? bv_signed k3) with true
              by (symmetry; apply Z.ltb_lt; destruct OK3; lia).
            cbv iota.
            apply RST. }
        step.
        rewrite (unsigned_lit (f + 19)) by lia. rewrite rc_shr3.
        step. step. clear RK19.
        step. rewrite Z18.
        step.
        unfold sxb. rewrite (rc_eqb0_signed (bv_signed k19)) by lia.
        destruct (Z.eqb_spec (bv_signed k19) 0) as [K0|K0]; cbn [negb].
        - apply R2.
        - step.
          rewrite (unsigned_lit (f + 19)) by lia. rewrite rc_land7.
          step.
          rewrite (rc_lts_signed ((f + 19) mod 8) (bv_signed k19))
            by (pose proof (Z.mod_pos_bound (f + 19) 8 ltac:(lia)); lia).
          replace ((f + 19) mod 8 <? bv_signed k19) with true by (symmetry; apply Z.ltb_lt; destruct OK19; lia).
          apply R2. }
      step.
      rewrite (unsigned_lit (f + 18)) by lia. rewrite rc_shr3.
      step. step. clear RK18.
      step.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k18)) by lia.
      destruct (Z.eqb_spec (bv_signed k18) 0) as [K0|K0]; cbn [negb].
      + apply R1.
      + step.
        rewrite (unsigned_lit (f + 18)) by lia. rewrite rc_land7.
        step.
        rewrite (rc_lts_signed ((f + 18) mod 8) (bv_signed k18))
          by (pose proof (Z.mod_pos_bound (f + 18) 8 ltac:(lia)); lia).
        replace ((f + 18) mod 8 <? bv_signed k18) with true by (symmetry; apply Z.ltb_lt; destruct OK18; lia).
        apply R1. }
  step.
  rewrite (unsigned_lit (f + 20)) by lia. rewrite rc_shr3.
  step. step. clear RK.
  step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed k20)) by lia.
  destruct (Z.eqb_spec (bv_signed k20) 0) as [K0|K0]; cbn [negb].
  - apply PRO.
  - step.
    rewrite (unsigned_lit (f + 20)) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed ((f + 20) mod 8) (bv_signed k20))
      by (pose proof (Z.mod_pos_bound (f + 20) 8 ltac:(lia)); lia).
    replace ((f + 20) mod 8 <? bv_signed k20) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia).
    apply PRO.
Qed.
