From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memcpy_c __errno_location_c send_line_c send_line_loop.
Import ListNotations.
Open Scope Z_scope.

Section Back.
Variables (sp gp tp s10 s11 wline wlen mx : word) (F : bvmap 5 word) (fc : bv 32) (B : list byte).
Hypothesis MC : memcpy_contract.
Hypothesis EL : __errno_location_contract.
Hypothesis HLB : Z.of_nat (length B) = bv_unsigned wlen.
Hypothesis HRE : 200728 <= bv_unsigned tp + -164.
Hypothesis HLG : bv_unsigned wline + bv_unsigned wlen <= 200640 \/ 200728 <= bv_unsigned wline.
Hypothesis HLE : bv_unsigned wline + bv_unsigned wlen <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= bv_unsigned wline.
Variables (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (lo : Z).

Definition sl_pre (cap out : word) (k : Z) (ev nk : word) (r : Z) (junk : list byte) (m1 : word -> option byte) : Prop :=
  0 <= k < bv_unsigned wlen /\ 0 <= r /\
  bv_unsigned nk + (bv_unsigned wlen - k) < 2^64 /\
  Z.min (bv_unsigned wlen - k) (bv_unsigned cap - bv_unsigned nk) <= r /\
  mem_inv rsegs m1 /\ bytes_at rsegs m1 (bv_unsigned wline) B /\
  rw_cells rsegs m1 200644 [C1 (Z_to_bv 8 0)] /\
  rw_cells rsegs m1 200652 [C1 (Z_to_bv 8 0)] /\
  rw_cells rsegs m1 200656 [C1 (Z_to_bv 8 0)] /\
  rw_cells rsegs m1 (bv_unsigned tp + -164) [C4 ev] /\
  bv_unsigned wlen < 2^63 /\
  ((bv_unsigned out + bv_unsigned nk + r <= 200640 \/ 200728 <= bv_unsigned out + bv_unsigned nk - k) /\
   (bv_unsigned out + bv_unsigned nk + r <= 134460 \/ 134464 <= bv_unsigned out + bv_unsigned nk - k)) /\
  (bv_unsigned out + bv_unsigned nk + r <= bv_unsigned tp + -164 \/
   bv_unsigned tp + -164 + 4 <= bv_unsigned out + bv_unsigned nk - k) /\
  (bv_unsigned wline + bv_unsigned wlen <= bv_unsigned out + bv_unsigned nk - k \/
   bv_unsigned out + bv_unsigned nk + r <= bv_unsigned wline) /\
  rw_cells rsegs m1 (bv_unsigned out + bv_unsigned nk - k)
    [CB (Z.to_nat k) (firstn (Z.to_nat k) B); CB (Z.to_nat r) junk].

Lemma sl_regrow : forall (cap0 out0 res : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word)
    k ev nk r junk m1 c,
  bv_unsigned res <> 0 ->
  rw_cells rsegs m1 134460 [C4 (Z_to_bv 64 3)] ->
  rw_cells rsegs m1 200696 [C8 mx; C8 nk; C8 cap0; C8 out0] ->
  sl_pre (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res k ev nk r junk m1 ->
  1 <= c <= bv_unsigned wlen - k -> c <= r ->
  c = (if bv_unsigned mx =? 0 then bv_unsigned wlen - k else Z.min (bv_unsigned wlen - k) (bv_unsigned mx)) ->
  evt rsegs (fun ms => exists m1', munch [(200712, 200728)] m1 m1' /\ wmono rsegs m1 m1' /\
      rw_cells rsegs m1' 134460 [C4 (Z_to_bv 64 3)] /\
      sl_inv tp wline wlen mx (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res B 0 0 k ev nk r junk m1' /\
      sl_post sp gp tp s10 s11 wline wlen mx (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res F fc B 0 0 k ev nk r m1' ms)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 wlen wline res x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 c) (Z_to_bv 64 (2 * (bv_unsigned nk + c))) (Z_to_bv 64 200640) (Z_to_bv 64 135664)
             (Z_to_bv 64 k) (Z_to_bv 64 3) (Z_to_bv 64 4) x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13288) fc None m1 (seg_rom rsegs)).
Proof using HLB HLE HLG HRE MC.
  intros cap0 out0 res x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 k ev nk r junk m1 c
    HR0 CCL COV PRE Hc Hcr Hcd.
  destruct PRE as (Hk & Hr0 & Hnw & Hmin & MI & BL & CBR & CDD & CEI & CER & H63 & HP & HPE & HPL & CO).
  pose proof (zr_word nk) as Rnk. pose proof (zr_word res) as Rres. pose proof (zr_word wlen) as Rlen.
  pose proof (zr_word wline) as Rline. pose proof (zr_word tp) as Rtp. unfold inr64 in *.
  pose proof (rw_cells_bound rsegs m1 _ _ CO) as BCO. cbn [cells_size csize] in BCO.
  pose proof (rw_cells_bound rsegs m1 _ _ CER) as BCE. cbn [cells_size csize] in BCE.
  pose proof (bytes_at_bound rsegs m1 _ _ BL) as BBL.
  pose proof (munch_refl [(200712, 200728)] m1) as MUs.
  pose proof (wmono_refl rsegs m1) as WMs.
  step. if_false.
  step. step. step. step. step. step.
  replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (bv_unsigned nk + c)) with (Z_to_bv 64 (c + bv_unsigned nk)) by (f_equal; lia).
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  assert (INV : sl_inv tp wline wlen mx (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res B 0 0 k ev nk r junk m2).
  { unfold sl_inv.
    split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. split; [lia|].
    split; [intros _; lia|]. split; [exact Hmin|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    intros _. split; [lia|]. split; [exact HP|]. split; [exact HPE|]. split; [exact HPL|]. assumption. }
  eapply evt_mono.
  - eapply (sl_tail sp gp tp s10 s11 wline wlen mx (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res F fc B MC HLB HRE HLG HLE);
      [exact INV | lia | lia | exact Hcd].
  - intros ms POST. exists m2. split; [exact MUs|]. split; [exact WMs|]. split; [exact CCL|].
    split; [exact INV | exact POST].
Qed.

Lemma sl_back : forall (jb : list byte) (cap0 out0 res : word)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) k ev nk r junk m1 c,
  bv_unsigned res <> 0 ->
  rw_cells rsegs m1 134460 [C4 (Z_to_bv 64 3)] ->
  rw_cells rsegs m1 200696 [C8 mx; C8 nk; C8 cap0; C8 out0] ->
  sl_pre (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res k ev nk r junk m1 ->
  sl_frame sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo jb m1 ->
  1 <= c <= bv_unsigned wlen - k -> c <= r ->
  c = (if bv_unsigned mx =? 0 then bv_unsigned wlen - k else Z.min (bv_unsigned wlen - k) (bv_unsigned mx)) ->
  bv_unsigned tp + -164 + 4 <= lo -> 200728 <= lo -> lo + 96 <= bv_unsigned sp ->
  bv_unsigned res + bv_unsigned nk + r <= lo ->
  evt rsegs (fun ms => exists m1', munch [(200712, 200728)] m1 m1' /\ wmono rsegs m1 m1' /\
      rw_cells rsegs m1' 134460 [C4 (Z_to_bv 64 3)] /\
      (sl_fin sp gp tp s10 s11 wline wlen mx (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res F fc B
         ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo 0 0 k ev nk r m1' ms \/
       sl_call sp gp tp s10 s11 wline wlen mx (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res F fc B
         ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo jb 0 0 k ev nk r m1' ms))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 wlen wline res x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 c) (Z_to_bv 64 (2 * (bv_unsigned nk + c))) (Z_to_bv 64 200640) (Z_to_bv 64 135664)
             (Z_to_bv 64 k) (Z_to_bv 64 3) (Z_to_bv 64 4) x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13288) fc None m1 (seg_rom rsegs)).
Proof using EL HLB HLE HLG HRE MC.
  intros jb cap0 out0 res x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 k ev nk r junk m1 c
    HR0 CCL COV PRE FRM Hc Hcr Hcd H1 H2 H3 HLO.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  eapply evt_cut; [eapply sl_regrow; eassumption|].
  intros ms (m2 & MUs & WMs & CCL2 & INV & POST).
  assert (FRM2 : sl_frame sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo jb m2).
  { destruct FRM as [FR ST]. pose proof (rw_cells_bound rsegs m1 _ _ FR) as BF.
    cbn [cells_size csize Nat.add] in BF. split.
    - eapply rw_cells_transport; [exact FR|exact MUs|exact WMs|]. cbn [disjoint_from cells_size csize Nat.add]. lia.
    - eapply stk_transport_disjoint; [exact ST|exact MUs|exact WMs|]. cbn [disjoint_from]. lia. }
  eapply evt_mono.
  - eapply (sl_post_out sp gp tp s10 s11 wline wlen mx (Z_to_bv 64 (2 * (bv_unsigned nk + c))) res F fc B
              MC EL HLB HRE HLG HLE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo jb);
      [exact POST | exact INV | exact FRM2 | exact H1 | exact H2 | exact H3 | intros _; exact HLO].
  - intros ms' H. exists m2. split; [exact MUs|]. split; [exact WMs|]. split; [exact CCL2|exact H].
Qed.

Lemma sl_front : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (junk : list byte) (cl br dd ei : Z) (nout cap out ev : word) (r : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp ->
  bv_unsigned tp + -164 + 4 <= lo -> 200728 <= lo ->
  mem_inv rsegs m -> bytes_at rsegs m (bv_unsigned wline) B ->
  (bv_unsigned wline + bv_unsigned wlen <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned wline) ->
  (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) -> (ei = 0 \/ ei = 1) ->
  rw_cells rsegs m 134460 [C4 (Z_to_bv 64 cl)] ->
  rw_cells rsegs m 200644 [C1 (Z_to_bv 8 br)] ->
  rw_cells rsegs m 200652 [C1 (Z_to_bv 8 dd)] ->
  rw_cells rsegs m 200656 [C1 (Z_to_bv 8 ei)] ->
  rw_cells rsegs m 200696 [C8 mx; C8 nout; C8 cap; C8 out] ->
  rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
  0 <= r -> Z.min (bv_unsigned wlen) (bv_unsigned cap - bv_unsigned nout) <= r ->
  (send_live cl br dd (bv_unsigned wlen) = true ->
     bv_unsigned wlen < 2^63 /\ bv_unsigned nout + bv_unsigned wlen < 2^64 /\
     ((bv_unsigned out + bv_unsigned nout + r <= 200640 \/ 200728 <= bv_unsigned out + bv_unsigned nout) /\
      (bv_unsigned out + bv_unsigned nout + r <= 134460 \/ 134464 <= bv_unsigned out + bv_unsigned nout)) /\
     (bv_unsigned out + bv_unsigned nout + r <= bv_unsigned tp + -164 \/
      bv_unsigned tp + -164 + 4 <= bv_unsigned out + bv_unsigned nout) /\
     (bv_unsigned wline + bv_unsigned wlen <= bv_unsigned out + bv_unsigned nout \/
      bv_unsigned out + bv_unsigned nout + r <= bv_unsigned wline) /\
     bv_unsigned out + bv_unsigned nout + r <= lo /\
     rw_cells rsegs m (bv_unsigned out + bv_unsigned nout) [CB (Z.to_nat r) junk]) ->
  evt rsegs (fun ms => exists jb m1, munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
      ((send_off cl br (bv_unsigned wlen) = true /\
        exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          ms = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3' t4' t5' t6') F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
          stk rsegs m1 lo (bv_unsigned sp)) \/
       (send_off cl br (bv_unsigned wlen) = false /\ cl = 3 /\ br = 0 /\
        (sl_fin sp gp tp s10 s11 wline wlen mx cap out F fc B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo dd ei 0 ev nout r
           m1 ms \/
         sl_call sp gp tp s10 s11 wline wlen mx cap out F fc B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo jb dd ei 0 ev nout r
           m1 ms))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 wline wlen a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x131bc) fc None m (seg_rom rsegs)).
Proof using EL HLB HLE HLG HRE MC.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk cl br dd ei nout cap out ev r
    ST HLO H1 H2 MI HB HLS Hcl Hbr Hdd Hei HCL HBR HDD HEI HOV HER Hr0 Hmin HLIVE.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word tp) as Rtp. pose proof (zr_word wline) as Ra0.
  pose proof (zr_word wlen) as Ra1. pose proof (zr_word out) as Rout. pose proof (zr_word nout) as Rnout.
  pose proof (zr_word cap) as Rcap. unfold inr64 in *.
  pose proof (bytes_at_bound rsegs m _ _ HB) as BHB.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  do 12 step.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -96) (CB _ ?j :: _) |- _ => set (jb := j) in H; rename H into FR end.
  destruct (Z.eq_dec (bv_unsigned wlen) 0) as [L0|L0].
  - step. if_true.
    eapply evt_mono; [eapply (sl_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo);
                      [lia | exact ST | exact FR] |].
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR).
    exists jb. eexists. split; [exact MU|]. split; [exact WM|]. left.
    split; [unfold send_off; rewrite (proj2 (Z.eqb_eq _ _) L0), !Bool.orb_true_r; reflexivity|].
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. split; [reflexivity|exact STR].
  - step. if_false. step. step.
    destruct Hcl as [-> | ->].
    + step. if_false.
      step. step. step. step. step. step.
      destruct Hbr as [-> | ->].
      * if_false. step. step. step. step.
        replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3) by (apply bv_eq; reflexivity).
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
        assert (Hoff : send_off 3 0 (bv_unsigned wlen) = false).
        { unfold send_off. rewrite (proj2 (Z.eqb_neq _ _) L0). reflexivity. }
        assert (Hlive : send_live 3 0 dd (bv_unsigned wlen) = (dd =? 0)).
        { unfold send_live. rewrite Hoff. reflexivity. }
        rewrite Hlive in HLIVE.
        assert (OUTC : dd = 0 ->
          bv_unsigned wlen < 2^63 /\ bv_unsigned nout + bv_unsigned wlen < 2^64 /\
          ((bv_unsigned out + bv_unsigned nout + r <= 200640 \/ 200728 <= bv_unsigned out + bv_unsigned nout) /\
           (bv_unsigned out + bv_unsigned nout + r <= 134460 \/ 134464 <= bv_unsigned out + bv_unsigned nout)) /\
          (bv_unsigned out + bv_unsigned nout + r <= bv_unsigned tp + -164 \/
           bv_unsigned tp + -164 + 4 <= bv_unsigned out + bv_unsigned nout) /\
          (bv_unsigned wline + bv_unsigned wlen <= bv_unsigned out + bv_unsigned nout \/
           bv_unsigned out + bv_unsigned nout + r <= bv_unsigned wline) /\
          bv_unsigned out + bv_unsigned nout + r <= lo /\
          rw_cells rsegs m1 (bv_unsigned out + bv_unsigned nout) [CB (Z.to_nat r) junk]).
        { intros D. rewrite D in HLIVE. destruct (HLIVE eq_refl) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
          pose proof (rw_cells_bound rsegs m _ _ C7) as BC7. cbn [cells_size csize] in BC7.
          split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
          split; [exact C6|].
          eapply rw_cells_transport; [exact C7 | exact MU | exact WM |].
          cbn [disjoint_from cells_size csize]. lia. }
        clear HLIVE.
        assert (INV : sl_inv tp wline wlen mx cap out B dd ei 0 ev nout r junk m1).
        { unfold sl_inv.
          split; [lia|]. split; [exact Hdd|]. split; [exact Hei|]. split; [lia|].
          split; [intros D; destruct (OUTC D) as (_ & C2 & _); lia|].
          split; [lia|].
          split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
          split; [assumption|]. split; [assumption|]. split; [assumption|].
          intros D. destruct (OUTC D) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
          replace (bv_unsigned out + bv_unsigned nout - 0) with (bv_unsigned out + bv_unsigned nout) by lia.
          split; [exact C1|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
          change [CB (Z.to_nat 0) (firstn (Z.to_nat 0) B); CB (Z.to_nat r) junk]
            with ([CB 0 []] ++ [CB (Z.to_nat r) junk]).
          pose proof (rw_cells_bound rsegs m1 _ _ C7) as BC7.
          apply sl_cells_app_r; [apply sl_cb_nil; lia|].
          change (Z.of_nat (cells_size [CB 0 []])) with 0. rewrite Z.add_0_r. exact C7. }
        eapply evt_mono.
        { eapply (sl_run sp gp tp s10 s11 wline wlen mx cap out F fc B MC EL HLB HRE HLG HLE
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 lo jb (S (Z.to_nat (2 * (bv_unsigned wlen - 0) + ei))));
            [ | exact INV | split; [exact FR | exact ST] | exact H1 | exact H2 | exact HLO | ].
          - lia.
          - intros D. destruct (OUTC D) as (_ & _ & _ & _ & _ & C6 & _). lia. }
        intros ms H. exists jb, m1. split; [exact MU|]. split; [exact WM|]. right.
        split; [exact Hoff|]. split; [reflexivity|]. split; [reflexivity|]. exact H.
      * if_true.
        eapply evt_mono; [eapply (sl_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo);
                          [lia | exact ST | exact FR] |].
        intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR).
        exists jb. eexists. split; [exact MU|]. split; [exact WM|]. left.
        split; [reflexivity|].
        exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. split; [reflexivity|exact STR].
    + step. if_true.
      eapply evt_mono; [eapply (sl_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo);
                        [lia | exact ST | exact FR] |].
      intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & STR).
      exists jb. eexists. split; [exact MU|]. split; [exact WM|]. left.
      split; [reflexivity|].
      exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. split; [reflexivity|exact STR].
Qed.

End Back.
