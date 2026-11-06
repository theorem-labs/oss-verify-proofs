From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c memcpy_c strlen_c box_name_ucall box_name_ubase box_name_useg_end box_name_useg_dp box_name_useg_tkz box_name_useg_tok.
Import ListNotations.
Open Scope Z_scope.

Section BoxName.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f i o : Z) (display display_len : word)
          (sd : list Z).
Hypothesis SBCH : sb_ch_contract.
Hypothesis DEC : sb_dec_contract.
Hypothesis MC : memcpy_contract.
Hypothesis SL : strlen_contract.

Notation S := (bv_unsigned sp).
Notation SVC := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation ACC := (bn_accept f sd i o (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                   (bv_unsigned display) (bv_unsigned display_len)).
Notation NM := (bn_NM f sd i o).
Notation LN := (firstn 23 NM).
Notation NOV := (if 23 <? Z.of_nat (length NM) then 1 else 0).
Hypothesis HIM : bn_image m (S - BN_K) S.

Notation W4 := (bn_w4 i o).
Notation STM := (bn_stem f sd).
Notation Q0 := (QQ ra sp gp tp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo f i o display display_len sd).
Ltac wd_common HB HC SB MI ST c X done P rest :=
  unfold BN_K in *;
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q0' & _); exact Q0');
  pose proof (bytes_at_bound _ _ _ _ HB) as BB; rewrite bn_bytes_length, !length_app in BB; cbn [length app] in BB; rewrite ?length_app in BB; cbn [length] in BB;
  pose proof (Forall_inv HC) as Hc; pose proof (Forall_inv_tail HC) as HC'; cbv beta in Hc;
  step; rewrite zl_c by lia; step; step;
  eapply (ch_call SBCH) with (A := S + -200) (B := S + -168) (cap := 24) (c := c) (lo := lo) (hi := S + -352) (s := X);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | reflexivity | lia | lia
    | exact SB | lia | exact MI | exact ST | lia | lia | lia |];
  intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3;
  assert (HB3 : bytes_at rsegs m3 P (bn_bytes ((done ++ [c]) ++ rest ++ [0])));
  [ rewrite <- app_assoc; cbn [app]; eapply bytes_at_keep; [exact HB | exact MU3 |];
    intros x Hx; rewrite bn_bytes_length, !length_app in Hx; cbn [length app outside] in *;
    rewrite ?length_app in *; cbn [length] in *; lia |];
  step; bfalse.

Lemma w4_loop : forall (Q : machine_state -> Prop) (rest done X : list Z) (c : Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (P : Z),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bytes_at rsegs m2 P (bn_bytes (done ++ c :: rest ++ [0])) -> Forall (fun c => 0 < c < 256) (c :: rest) ->
  (P + Z.of_nat (length done) + Z.of_nat (length rest) + 2 <= S + -200 \/ S + -144 <= P) ->
  sbx m2 (S + -200) (S + -168) 24 X -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     sbx m3 (S + -200) (S + -168) 24 (X ++ c :: rest) ->
     munch [(S + -200, S + -144)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 (Z_to_bv 64 (-1)) y10 y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 x21 x22 (Z_to_bv 64 (P + Z.of_nat (length done) + Z.of_nat (length rest) + 1))
                          x24 x25 x26 x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x14538) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-1)) (zxb (Z_to_bv 8 c))
                       x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (P + Z.of_nat (length done)))
                       x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1451c) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q rest. induction rest as [|c' rest IH];
    intros done X c m2 x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      P HLO S16 HB HC DJ SB MI ST K.
  - wd_common HB HC SB MI ST c X done P (@nil Z).
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (P + Z.of_nat (length done) + 1)) 1 = Some [Z_to_bv 8 0]).
    { pose proof (rd_mid m3 P (done ++ [c]) 0 [] HB3) as R. rewrite length_app in R. cbn [length] in R.
      replace (P + Z.of_nat (length done + 1)) with (P + Z.of_nat (length done) + 1) in R by lia. exact R. }
    step. step. step. bfalse.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length done) + Z.of_nat (length (@nil Z)) + 1)
      by (cbn [length]; lia).
    eapply K; [exact SB3 | | exact WM3 | exact MI3 | exact ST3].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
  - wd_common HB HC SB MI ST c X done P (c' :: rest).
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (P + Z.of_nat (length done) + 1)) 1 = Some [Z_to_bv 8 c']).
    { pose proof (rd_mid m3 P (done ++ [c]) c' (rest ++ [0]) HB3) as R. rewrite length_app in R. cbn [length] in R.
      replace (P + Z.of_nat (length done + 1)) with (P + Z.of_nat (length done) + 1) in R by lia. exact R. }
    pose proof (Forall_inv HC') as Hc'. cbv beta in Hc'.
    step. step. step. btrue.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length (done ++ [c]))) by (rewrite length_app; cbn [length]; lia).
    eapply (IH (done ++ [c]) (X ++ [c]) c' m3); [unfold BN_K; lia | exact S16 | exact HB3 | exact HC'
      | rewrite length_app; cbn [length] in *; lia | exact SB3 | exact MI3 | exact ST3 |].
    intros m4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
    rewrite <- app_assoc in SB4. cbn [app] in SB4.
    replace (P + Z.of_nat (length (done ++ [c])) + Z.of_nat (length rest) + 1)
      with (P + Z.of_nat (length done) + Z.of_nat (length (c' :: rest)) + 1) by (rewrite length_app; cbn [length]; lia).
    eapply K; [exact SB4 | | exact (wmono_trans _ _ _ _ WM3 WM4) | exact MI4 | exact ST4].
    apply (munch_trans _ m2 m3 m4); [|exact MU4].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
Qed.


Ltac sd_common HB HC SB MI ST c X done P rest :=
  unfold BN_K in *;
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q0' & _); exact Q0');
  pose proof (bytes_at_bound _ _ _ _ HB) as BB; rewrite bn_bytes_length, !length_app in BB; cbn [length app] in BB; rewrite ?length_app in BB; cbn [length] in BB;
  pose proof (Forall_inv HC) as Hc; pose proof (Forall_inv_tail HC) as HC'; cbv beta in Hc;
  step; rewrite zl_c by lia; step; step;
  eapply (ch_call SBCH) with (A := S + -200) (B := S + -168) (cap := 24) (c := c) (lo := lo) (hi := S + -352) (s := X);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | reflexivity | lia | lia
    | exact SB | lia | exact MI | exact ST | lia | lia | lia |];
  intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3;
  assert (HB3 : bytes_at rsegs m3 P (bn_bytes ((done ++ [c]) ++ rest ++ [0])));
  [ rewrite <- app_assoc; cbn [app]; eapply bytes_at_keep; [exact HB | exact MU3 |];
    intros x Hx; rewrite bn_bytes_length, !length_app in Hx; cbn [length app outside] in *;
    rewrite ?length_app in *; cbn [length] in *; lia |];
  step; bfalse.

Lemma stem_loop : forall (Q : machine_state -> Prop) (rest done X : list Z) (c : Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
    (P : Z),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bytes_at rsegs m2 P (bn_bytes (done ++ c :: rest ++ [0])) -> Forall (fun c => 0 < c < 256) (c :: rest) ->
  (P + Z.of_nat (length done) + Z.of_nat (length rest) + 2 <= S + -200 \/ S + -144 <= P) ->
  sbx m2 (S + -200) (S + -168) 24 X -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     sbx m3 (S + -200) (S + -168) 24 (X ++ c :: rest) ->
     munch [(S + -200, S + -144)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 (Z_to_bv 64 (-1)) y10 y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (P + Z.of_nat (length done) + Z.of_nat (length rest) + 1))
                          x26 x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x14480) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-1)) (zxb (Z_to_bv 8 c))
                       x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (P + Z.of_nat (length done)))
                       x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x14464) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q rest. induction rest as [|c' rest IH];
    intros done X c m2 x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      P HLO S16 HB HC DJ SB MI ST K.
  - sd_common HB HC SB MI ST c X done P (@nil Z).
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (P + Z.of_nat (length done) + 1)) 1 = Some [Z_to_bv 8 0]).
    { pose proof (rd_mid m3 P (done ++ [c]) 0 [] HB3) as R. rewrite length_app in R. cbn [length] in R.
      replace (P + Z.of_nat (length done + 1)) with (P + Z.of_nat (length done) + 1) in R by lia. exact R. }
    step. step. step. bfalse.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length done) + Z.of_nat (length (@nil Z)) + 1)
      by (cbn [length]; lia).
    eapply K; [exact SB3 | | exact WM3 | exact MI3 | exact ST3].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
  - sd_common HB HC SB MI ST c X done P (c' :: rest).
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (P + Z.of_nat (length done) + 1)) 1 = Some [Z_to_bv 8 c']).
    { pose proof (rd_mid m3 P (done ++ [c]) c' (rest ++ [0]) HB3) as R. rewrite length_app in R. cbn [length] in R.
      replace (P + Z.of_nat (length done + 1)) with (P + Z.of_nat (length done) + 1) in R by lia. exact R. }
    pose proof (Forall_inv HC') as Hc'. cbv beta in Hc'.
    step. step. step. btrue.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length (done ++ [c]))) by (rewrite length_app; cbn [length]; lia).
    eapply (IH (done ++ [c]) (X ++ [c]) c' m3); [unfold BN_K; lia | exact S16 | exact HB3 | exact HC'
      | rewrite length_app; cbn [length] in *; lia | exact SB3 | exact MI3 | exact ST3 |].
    intros m4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
    rewrite <- app_assoc in SB4. cbn [app] in SB4.
    replace (P + Z.of_nat (length (done ++ [c])) + Z.of_nat (length rest) + 1)
      with (P + Z.of_nat (length done) + Z.of_nat (length (c' :: rest)) + 1) by (rewrite length_app; cbn [length]; lia).
    eapply K; [exact SB4 | | exact (wmono_trans _ _ _ _ WM3 WM4) | exact MI4 | exact ST4].
    apply (munch_trans _ m2 m3 m4); [|exact MU4].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
Qed.


Lemma rec_cb : forall mm A p c n ov pad, rw_cells rsegs mm A [C8 p; C8 c; C8 n; C4 ov; C4 pad] ->
  rw_cells rsegs mm A [CB 24 (le8 p ++ le8 c ++ le8 n); C4 ov; C4 pad].
Proof.
  intros mm A p c n ov pad H. eapply rw_cells_conv; [exact H | |].
  - cbn [cells_wf cell_wf]. rewrite !length_app, !length_le8. repeat split.
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma w4_facts : bn_ok i = true -> bn_ok o = true ->
  length W4 = 4%nat /\ Forall (fun c => 0 < c < 256) W4 /\ Forall (fun c => 48 <= c <= 57) W4.
Proof.
  intros OKI OKO. destruct (bn_ok_dec i OKI) as (_ & Li & _ & _ & _ & Di & _).
  destruct (bn_ok_dec o OKO) as (_ & Lo & _ & _ & _ & Do & _).
  assert (DD : Forall (fun c => 48 <= c <= 57) W4) by (unfold bn_w4; apply Forall_app; split; assumption).
  split; [unfold bn_w4; rewrite length_app, Li, Lo; reflexivity|]. split; [|exact DD].
  eapply Forall_impl; [|exact DD]. intros c Hc. cbv beta in *. lia.
Qed.

Lemma seg_dash : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (j0 jrd jbd jrt jbt jw jgw : list byte) (pw : word),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat -> NM = STM ++ 45 :: W4 ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 8 j0; C8 display] ->
  rw_cells rsegs m2 (S + -336) [CB 32 jrd] ->
  rw_cells rsegs m2 (S + -304) [CB 48 jbd] ->
  rw_cells rsegs m2 (S + -256) [CB 32 jrt] ->
  rw_cells rsegs m2 (S + -224) [CB 24 jbt] ->
  sbx m2 (S + -200) (S + -168) 24 STM ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  bytes_at rsegs m2 (S + -109) (bn_bytes (W4 ++ [0])) ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) x23 display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14500) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 j0 jrd jbd jrt jbt jw jgw pw
    HLO S16 AOK BUFS NMB NM1 ENM ST2 MU2 WM2 MI2 SV2 DS2 RD2 BD2 RT2 BT2 SBN RW2 GW2 W4B.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct (w4_facts OKI OKO) as (LW & WC & WD).
  step. step. step.
  eapply (ch_call SBCH) with (A := S + -200) (B := S + -168) (cap := 24) (c := 45) (lo := lo) (hi := S + -352)
    (s := STM);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | reflexivity | lia | lia
    | exact SBN | lia | exact MI2 | exact ST2 | lia | lia | lia |].
  intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3.
  xport m2 m3 MU3 WM3.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MU3 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU3'.
  pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM3'.
  clear MU2 WM2 MU3 WM3 ST2 MI2 SBN.
  assert (LG : length jgw = 8%nat) by (destruct GW2 as [[Hwf _] _]; cbn in Hwf; tauto).
  apply u8arr_of_rw_cells in GW2.
  assert (R0 : 48 <= nth 0 W4 0 <= 57) by (rewrite Forall_forall in WD; apply WD; apply nth_In; lia).
  pose proof (rd_nth m3 (S + -109) (W4 ++ [0]) 0 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD0.
  rewrite app_nth1 in RD0 by lia. replace (S + -109 + Z.of_nat 0) with (S + -109) in RD0 by lia.
  step. step. bfalse.
  step. step.
  assert (EW : W4 = nth 0 W4 0 :: tl W4) by (destruct (bn_w4 i o) as [|c0 W']; [cbn in LW; lia | reflexivity]).
  pose proof W4B as W4B'. pose proof WC as WC'. rewrite EW in W4B', WC'.
  replace (Z_to_bv 64 (S + -109)) with (Z_to_bv 64 (S + -109 + Z.of_nat (length (@nil Z)))) by (f_equal; cbn [length]; lia).
  eapply (w4_loop Q0 (tl W4) [] (STM ++ [45]) (nth 0 W4 0) m3) with (P := S + -109);
    [unfold BN_K; lia | exact S16 | exact W4B' | exact WC' | cbn [length]; lia | exact SB3 | assumption | assumption |].
  intros m4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
  rewrite <- EW, <- app_assoc in SB4. cbn [app] in SB4. rewrite <- ENM in SB4.
  clear W4B' WC'.
  apply rw_cells_of_u8arr in GW2. rewrite LG in GW2.
  xport m3 m4 MU4 WM4.
  pose proof (munch_sub _ _ _ _ _ _ MU3' MU4 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU4'.
  pose proof (wmono_trans _ _ _ _ WM3' WM4) as WM4'.
  eapply seg_tok; try eassumption; unfold BN_K; try lia.
Qed.

Lemma seg_cmp : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word)
    (j0 jrd jbd jrt jbt jgw : list byte) (pw0 cw0 pw : word) (P : Z) (sl : list byte),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  Forall (fun c => 0 < c < 256) STM ->
  bytes_at rsegs m2 P (bn_bytes STM ++ Z_to_bv 8 0 :: sl) ->
  (- (P + Z.of_nat (length STM) + 1)) mod 8 <= Z.of_nat (length sl) -> 0 < P ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 8 j0; C8 display] ->
  rw_cells rsegs m2 (S + -336) [CB 32 jrd] ->
  rw_cells rsegs m2 (S + -304) [CB 48 jbd] ->
  rw_cells rsegs m2 (S + -256) [CB 32 jrt] ->
  rw_cells rsegs m2 (S + -224) [CB 24 jbt] ->
  sbx m2 (S + -200) (S + -168) 24 STM ->
  rw_cells rsegs m2 (S + -144) [C8 pw0; C8 cw0; C8 (Z_to_bv 64 4); C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  bytes_at rsegs m2 (S + -109) (bn_bytes (W4 ++ [0])) ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 P) display_len x25 x26 x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14480) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 j0 jrd jbd jrt jbt jgw
    pw0 cw0 pw P sl HLO S16 AOK BUFS NMB NM1 STC STB SLK P0 ST2 MU2 WM2 MI2 SV2 DS2 RD2 BD2 RT2 BT2 SBN RW2 GW2 W4B.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct (w4_facts OKI OKO) as (LW & WC & WD).
  pose proof (bytes_at_bound rsegs m2 P _ STB) as PB.
  rewrite length_app, bn_bytes_length in PB. cbn [length] in PB.
  destruct SBN as ((pn & RN2) & (rnm & Lnm & UNM)).
  step. step. step. bfalse.
  step. step.
  eapply evt_cut.
  { eapply SL with (str := bn_bytes STM) (slack := sl).
    - rewrite unsigned_lit by lia. exact STB.
    - apply bn_nz. exact STC.
    - rewrite unsigned_lit by lia. rewrite bn_bytes_length. exact SLK.
    - exact MI2. }
  intros ms' (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & E &
              MUc & WMc & MIc & STB3).
  subst ms'. rewrite unsigned_lit in STB3 by lia.
  rewrite (ret_pc_even 0x14494) by (cbn; lia).
  rewrite bn_bytes_length.
  pose proof (stk_keep _ _ _ _ _ ST2 MUc WMc ltac:(intros ?x ?Hx; exact I)) as ST3.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MUc ltac:(intros ?x ?Hx; exact I)) as MU3.
  pose proof (wmono_trans _ _ _ _ WM2 WMc) as WM3.
  clear STB ST2 MU2 WM2 MI2.
  xport m2 m3 MUc WMc.
  assert (SB3 : sbx m3 (S + -200) (S + -168) 24 STM).
  { split; [exists pn; exact RN2 | exists rnm; split; [exact Lnm | exact UNM]]. }
  clear RN2 UNM MUc WMc.
  step.
  destruct (Z.ltb_spec (Z.of_nat (length STM)) 4) as [Hl|Hl].
  - btrue.
    assert (ENM : NM = STM ++ 45 :: W4).
    { unfold bn_NM. cbv zeta. replace (4 <=? Z.of_nat (length STM)) with false by (symmetry; apply Z.leb_gt; lia).
      reflexivity. }
    apply rec_cb in RW2.
    eapply seg_dash; try eassumption; unfold BN_K; try lia.
  - bfalse.
    step. step. bfalse.
    step. step. step. bfalse.
    pose proof (proj1 (proj1 (bytes_at_app rsegs _ _ _ _) STB3)) as STB4.
    pose proof (bytes_skipn _ _ _ (length STM - 4) STB4 ltac:(lia)) as SKB.
    set (SK := skipn (length STM - 4) STM) in *.
    assert (LSK : length SK = 4%nat) by (unfold SK; rewrite length_skipn; lia).
    assert (SKC : Forall (fun c => 0 < c < 256) SK).
    { unfold SK. pose proof STC as Q. rewrite <- (firstn_skipn (length STM - 4) STM) in Q.
      apply Forall_app in Q. tauto. }
    assert (RS : forall j, (j < 4)%nat -> 0 < nth j SK 0 < 256)
      by (intros j Hj; rewrite Forall_forall in SKC; apply SKC; apply nth_In; lia).
    assert (RW : forall j, (j < 4)%nat -> 48 <= nth j W4 0 <= 57)
      by (intros j Hj; rewrite Forall_forall in WD; apply WD; apply nth_In; lia).
    pose proof (RS 0%nat ltac:(lia)) as RS0. pose proof (RS 1%nat ltac:(lia)) as RS1.
    pose proof (RS 2%nat ltac:(lia)) as RS2. pose proof (RS 3%nat ltac:(lia)) as RS3.
    pose proof (RW 0%nat ltac:(lia)) as RW0. pose proof (RW 1%nat ltac:(lia)) as RW1.
    pose proof (RW 2%nat ltac:(lia)) as RW2'. pose proof (RW 3%nat ltac:(lia)) as RW3.
    pose proof (rd_nth m3 (S + -109) (W4 ++ [0]) 0 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD0.
    pose proof (rd_nth m3 (S + -109) (W4 ++ [0]) 1 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD1.
    pose proof (rd_nth m3 (S + -109) (W4 ++ [0]) 2 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD2'.
    pose proof (rd_nth m3 (S + -109) (W4 ++ [0]) 3 W4B ltac:(rewrite length_app; cbn [length]; lia)) as RD3.
    rewrite app_nth1 in RD0, RD1, RD2', RD3 by lia.
    replace (S + -109 + Z.of_nat 0) with (S + -109) in RD0 by lia.
    replace (S + -109 + Z.of_nat 1) with (S + -108) in RD1 by lia.
    replace (S + -109 + Z.of_nat 2) with (S + -107) in RD2' by lia.
    replace (S + -109 + Z.of_nat 3) with (S + -106) in RD3 by lia.
    pose proof (rd_nth m3 _ SK 0 SKB ltac:(lia)) as RC0. pose proof (rd_nth m3 _ SK 1 SKB ltac:(lia)) as RC1.
    pose proof (rd_nth m3 _ SK 2 SKB ltac:(lia)) as RC2. pose proof (rd_nth m3 _ SK 3 SKB ltac:(lia)) as RC3.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 0) with (P + Z.of_nat (length STM) + -4) in RC0 by lia.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 1) with (P + Z.of_nat (length STM) + -3) in RC1 by lia.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 2) with (P + Z.of_nat (length STM) + -2) in RC2 by lia.
    replace (P + Z.of_nat (length STM - 4) + Z.of_nat 3) with (P + Z.of_nat (length STM) + -1) in RC3 by lia.
    assert (LG : length jgw = 8%nat) by (destruct GW2 as [[Hwf _] _]; cbn in Hwf; tauto).
    apply u8arr_of_rw_cells in GW2.
    do 20 step.
    step.
    rewrite c4v_eqb_x by lia.
    assert (ENM : NM = if (nth 0 SK 0 =? nth 0 W4 0) && (nth 1 SK 0 =? nth 1 W4 0) && (nth 2 SK 0 =? nth 2 W4 0) &&
                          (nth 3 SK 0 =? nth 3 W4 0) then STM else STM ++ 45 :: W4).
    { unfold bn_NM. cbv zeta. replace (4 <=? Z.of_nat (length STM)) with true by (symmetry; apply Z.leb_le; lia).
      rewrite andb_true_l. change (skipn (length STM - 4) STM) with SK. rewrite (bn_leq_nth4 _ _ LSK LW).
      reflexivity. }
    revert ENM.
    destruct ((nth 0 SK 0 =? nth 0 W4 0) && (nth 1 SK 0 =? nth 1 W4 0) && (nth 2 SK 0 =? nth 2 W4 0) &&
              (nth 3 SK 0 =? nth 3 W4 0)); intros ENM; cbv iota in ENM |- *.
    + rewrite <- ENM in SB3.
      apply rw_cells_of_u8arr in GW2. rewrite LG in GW2. apply rec_cb in RW2.
      eapply seg_tok; try eassumption; unfold BN_K; try lia.
    + apply rw_cells_of_u8arr in GW2. rewrite LG in GW2. apply rec_cb in RW2.
      eapply seg_dash; try eassumption; unfold BN_K; try lia.
Qed.

End BoxName.
