From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c memcpy_c strlen_c
  box_name_ucall box_name_ubase box_name_useg_end box_name_useg_dp.
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

Notation Q0 := (QQ ra sp gp tp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo f i o display display_len sd).

Ltac nd_common HB HC SB MI ST c X done P rest :=
  unfold BN_K in *;
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q0' & _); exact Q0');
  pose proof (bytes_at_bound _ _ _ _ HB) as BB; rewrite bn_bytes_length, !length_app in BB; cbn [length app] in BB; rewrite ?length_app in BB; cbn [length] in BB;
  pose proof (Forall_inv HC) as Hc; pose proof (Forall_inv_tail HC) as HC'; cbv beta in Hc;
  step; rewrite zl_c by lia; step; step;
  eapply (ch_call SBCH) with (A := S + -336) (B := S + -304) (cap := 48) (c := c) (lo := lo) (hi := S + -352) (s := X);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | reflexivity | lia | lia
    | exact SB | lia | exact MI | exact ST | lia | lia | lia |];
  intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3;
  assert (HB3 : bytes_at rsegs m3 P (bn_bytes ((done ++ [c]) ++ rest ++ [0])));
  [ rewrite <- app_assoc; cbn [app]; eapply bytes_at_keep; [exact HB | exact MU3 |];
    intros x Hx; rewrite bn_bytes_length, !length_app in Hx; cbn [length app outside] in *;
    rewrite ?length_app in *; cbn [length] in *; lia |];
  step; bfalse.

Lemma nmdp_loop : forall (Q : machine_state -> Prop) (rest done X : list Z) (c : Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (P : Z),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bytes_at rsegs m2 P (bn_bytes (done ++ c :: rest ++ [0])) -> Forall (fun c => 0 < c < 256) (c :: rest) ->
  (P + Z.of_nat (length done) + Z.of_nat (length rest) + 2 <= S + -336 \/ S + -256 <= P) ->
  sbx m2 (S + -336) (S + -304) 48 X -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     sbx m3 (S + -336) (S + -304) 48 (X ++ c :: rest) ->
     munch [(S + -336, S + -256)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 (Z_to_bv 64 (-1)) y10 y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 x21 x22 (Z_to_bv 64 (P + Z.of_nat (length done) + Z.of_nat (length rest) + 1))
                          x24 x25 x26 x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x15148) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-1)) (zxb (Z_to_bv 8 c))
                       x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (P + Z.of_nat (length done)))
                       x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1512c) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q rest. induction rest as [|c' rest IH];
    intros done X c m2 x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      P HLO S16 HB HC DJ SB MI ST K.
  - nd_common HB HC SB MI ST c X done P (@nil Z).
    assert (RD : ov_read_bytes rsegs m3 (Z_to_bv 64 (P + Z.of_nat (length done) + 1)) 1 = Some [Z_to_bv 8 0]).
    { pose proof (rd_mid m3 P (done ++ [c]) 0 [] HB3) as R. rewrite length_app in R. cbn [length] in R.
      replace (P + Z.of_nat (length done + 1)) with (P + Z.of_nat (length done) + 1) in R by lia. exact R. }
    step. step. step. bfalse.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length done) + Z.of_nat (length (@nil Z)) + 1)
      by (cbn [length]; lia).
    eapply K; [exact SB3 | | exact WM3 | exact MI3 | exact ST3].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
  - nd_common HB HC SB MI ST c X done P (c' :: rest).
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

Lemma rd_nth : forall mm P l j, bytes_at rsegs mm P (bn_bytes l) -> (j < length l)%nat ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (P + Z.of_nat j)) 1 = Some [Z_to_bv 8 (nth j l 0)].
Proof.
  intros mm P l j H Hj.
  pose proof (bytes_at_read rsegs mm _ _ (Z.of_nat j) 1 H ltac:(lia) ltac:(rewrite bn_bytes_length; lia)) as R.
  rewrite Nat2Z.id in R. unfold wa in R. rewrite R. f_equal. unfold bn_bytes.
  rewrite (bl_skipn_cons j (map (Z_to_bv 8) l) (Z_to_bv 8 0)) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

Lemma sbx_init : forall mm A B cap j,
  rw_cells rsegs mm A [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs mm B [CB (Z.to_nat cap) j] -> 1 <= cap -> sbx mm A B cap [].
Proof.
  intros mm A B cap j H1 H2 Hc. split.
  - exists (Z_to_bv 64 0). unfold rcells, nn, ovf. cbn [length].
    replace (Z.min (Z.of_nat 0) (cap - 1)) with 0 by lia.
    replace (cap - 1 <? Z.of_nat 0) with false by (symmetry; apply Z.ltb_ge; lia). exact H1.
  - rewrite firstn_nil. eapply rw_bbuf. exact H2.
Qed.

Lemma seg_tkz : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (j0 jrd jbd jw jgw : list byte) (pn pw : word),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) NM -> (1 <= length NM)%nat ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 8 j0; C8 display] ->
  rw_cells rsegs m2 (S + -336) [CB 32 jrd] ->
  rw_cells rsegs m2 (S + -304) [CB 48 jbd] ->
  sbx m2 (S + -256) (S + -224) 24 (bn_tk false LN) ->
  rw_cells rsegs m2 (S + -200)
    [C8 (Z_to_bv 64 (S + -168)); C8 (Z_to_bv 64 24); C8 (Z_to_bv 64 (Z.of_nat (length LN)));
     C4 (Z_to_bv 64 NOV); C4 pn] ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) x23 display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x150e4) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 j0 jrd jbd jw jgw pn pw
    HLO S16 AOK BUFS NMB NM1 ST2 MU2 WM2 MI2 SV2 DS2 RD2 BD2 SBT RN2 NM2 RW2 GW2.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  assert (LLN : (1 <= length LN <= 23)%nat) by (rewrite length_firstn; lia).
  assert (LNB : Forall (fun c => 0 < c < 256) LN).
  { pose proof NMB as Q. rewrite <- (firstn_skipn 23 NM) in Q. apply Forall_app in Q. tauto. }
  pose proof (bn_tk_len LN false) as LTK.
  destruct SBT as ((pt & RT2) & TKB). unfold rcells, nn, ovf in RT2.
  replace (Z.min (Z.of_nat (length (bn_tk false LN))) (24 - 1)) with (Z.of_nat (length (bn_tk false LN))) in RT2 by lia.
  replace (24 - 1 <? Z.of_nat (length (bn_tk false LN))) with false in RT2 by (symmetry; apply Z.ltb_ge; lia).
  rewrite firstn_all2 in TKB by lia.
  destruct TKB as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  step. step. step. bfalse.
  step. step. step. bfalse.
  step.
  pose proof (u8arr_store_ok rsegs m2 (S + -224) _ (Z.of_nat (length (bn_tk false LN))) _ UTK
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst UTK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  pose proof (bbuf_upd _ _ 24 _ _ _ HW Ltk ltac:(lia)) as TK3. clear HW.
  destruct TK3 as (rtk3 & Ltk3 & UTK3).
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM)) as [NMB2 _].
  pose proof (rd_nth m3 (S + -168) (LN ++ [0]) 0 NMB2 ltac:(rewrite length_app; cbn [length]; lia)) as RD0.
  rewrite app_nth1 in RD0 by lia. replace (S + -168 + Z.of_nat 0) with (S + -168) in RD0 by lia. clear NMB2.
  step. step. step.
  step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
  lazymatch goal with
  | H : rw_cells rsegs m4 (S + -336) [C8 ?p; C8 ?c; C8 ?n; C8 (Z_to_bv 64 0)] |- _ =>
      change [C8 p; C8 c; C8 n; C8 (Z_to_bv 64 0)] with ([C8 p; C8 c; C8 n] ++ [C8 (Z_to_bv 64 0)]) in H;
      apply conv_z8 in H; cbn [app] in H; rename H into RD4
  end.
  pose proof (sbx_init m4 (S + -336) (S + -304) 48 jbd RD4 BD2 ltac:(lia)) as SB4. clear RD4 BD2.
  assert (R0 : 0 < nth 0 LN 0 < 256) by (rewrite Forall_forall in LNB; apply LNB; apply nth_In; lia).
  step. bfalse.
  step. step.
  assert (ELN : LN = nth 0 LN 0 :: tl LN) by (destruct (firstn 23 NM) as [|c0 L']; [cbn in LLN; lia | reflexivity]).
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM)) as [NMB4 _].
  pose proof LNB as LNB4. rewrite ELN in NMB4, LNB4.
  replace (Z_to_bv 64 (S + -168)) with (Z_to_bv 64 (S + -168 + Z.of_nat (length (@nil Z)))) by (f_equal; cbn [length]; lia).
  eapply (nmdp_loop Q0 (tl LN) [] [] (nth 0 LN 0) m4) with (P := S + -168);
    [unfold BN_K; lia | exact S16 | exact NMB4 | exact LNB4 | cbn [length]; lia | exact SB4 | assumption | assumption |].
  intros m5 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB5 MU5 WM5 MI5 ST5.
  cbn [app] in SB5. rewrite <- ELN in SB5.
  clear NMB4 LNB4 SB4.
  xport m4 m5 MU5 WM5.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MU5 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU5'.
  pose proof (wmono_trans _ _ _ _ WM2 WM5) as WM5'.
  eapply seg_dp; try eassumption; unfold BN_K; try lia.
  - exists rtk3. split; [exact Ltk3 | exact UTK3].
  - exists rnm. split; [exact Lnm | exact UNM].
Qed.

End BoxName.
