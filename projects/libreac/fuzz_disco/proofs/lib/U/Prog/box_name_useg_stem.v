From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c memcpy_c strlen_c
  box_name_ucall box_name_ubase box_name_useg_end box_name_useg_dp box_name_useg_tkz box_name_useg_tok box_name_useg_cmp.
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

Lemma seg_stem : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word)
    (jds jrd jbd jrt jbt jrn jbn jrw jg3 jbw : list byte) (P : Z) (sl : list byte),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  Forall (fun c => 0 < c < 256) STM -> STM <> [] ->
  bytes_at rsegs m P (bn_bytes STM ++ Z_to_bv 8 0 :: sl) ->
  (- (P + Z.of_nat (length STM) + 1)) mod 8 <= Z.of_nat (length sl) -> 0 < P ->
  P + Z.of_nat (length STM) + 1 + Z.of_nat (length sl) <= S - BN_K \/ S <= P ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 16 jds] ->
  rw_cells rsegs m2 (S + -336) [CB 32 jrd] ->
  rw_cells rsegs m2 (S + -304) [CB 48 jbd] ->
  rw_cells rsegs m2 (S + -256) [CB 32 jrt] ->
  rw_cells rsegs m2 (S + -224) [CB 24 jbt] ->
  rw_cells rsegs m2 (S + -200) [CB 32 jrn] ->
  rw_cells rsegs m2 (S + -168) [CB 24 jbn] ->
  rw_cells rsegs m2 (S + -144) [CB 32 jrw] ->
  rw_cells rsegs m2 (S + -112) [CB 3 jg3] ->
  rw_cells rsegs m2 (S + -109) [CB 5 jbw] ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 display x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 P) display_len x25 x26 x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14f00) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 jds jrd jbd jrt jbt jrn jbn jrw
    jg3 jbw P sl HLO S16 AOK BUFS STC SNE STB SLK P0 PD ST2 MU2 WM2 MI2 SV2 DS2 RD2 BD2 RT2 BT2 RN2 BN2 RW2 G32 BW2.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct (bn_ok_dec i OKI) as (RI & _ & _ & DI & _).
  destruct (bn_ok_dec o OKO) as (RO & _ & _ & DO & _).
  destruct (w4_facts i o OKI OKO) as (LW & WC & WD).
  pose proof (bytes_at_bound rsegs m P _ STB) as PB.
  rewrite length_app, bn_bytes_length in PB. cbn [length] in PB.
  step. step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  lazymatch goal with
  | H : rw_cells rsegs m3 (S + -144) [C8 ?p; C8 ?c; C8 ?n; C8 (Z_to_bv 64 0)] |- _ =>
      change [C8 p; C8 c; C8 n; C8 (Z_to_bv 64 0)] with ([C8 p; C8 c; C8 n] ++ [C8 (Z_to_bv 64 0)]) in H;
      apply conv_z8 in H; cbn [app] in H; rename H into RW3
  end.
  pose proof (sbx_init m3 (S + -144) (S + -109) 5 jbw RW3 BW2 ltac:(lia)) as SBW. clear RW3 BW2.
  step. step. step. step.
  eapply (dec_call DEC) with (A := S + -144) (B := S + -109) (cap := 5) (v := i) (md := 2) (lo := lo) (s := []);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | lia | reflexivity | right; reflexivity
    | reflexivity | lia | exact SBW | lia | assumption | rewrite unsigned_lit by lia; assumption
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia |].
  intros m4 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB4 MU4 WM4 MI4 ST4.
  rewrite unsigned_lit in MU4, ST4 by lia.
  clear SBW.
  xport m3 m4 MU4 WM4.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MU4 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU4'.
  pose proof (wmono_trans _ _ _ _ WM2 WM4) as WM4'.
  clear MU2 WM2 MU4 WM4.
  step. step. step. step.
  eapply (dec_call DEC) with (A := S + -144) (B := S + -109) (cap := 5) (v := o) (md := 2) (lo := lo)
    (s := [] ++ sb_dec_D i 2);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | lia | reflexivity | right; reflexivity
    | reflexivity | lia | exact SB4 | lia | assumption | rewrite unsigned_lit by lia; assumption
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia |].
  intros m5 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB5 MU5 WM5 MI5 ST5.
  rewrite unsigned_lit in MU5, ST5 by lia.
  clear SB4.
  xport m4 m5 MU5 WM5.
  pose proof (munch_sub _ _ _ _ _ _ MU4' MU5 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU5'.
  pose proof (wmono_trans _ _ _ _ WM4' WM5) as WM5'.
  clear MU4' WM4' MU5 WM5.
  assert (EW : ([] ++ sb_dec_D i 2) ++ sb_dec_D o 2 = W4) by (rewrite DI, DO; reflexivity).
  rewrite EW in SB5.
  destruct SB5 as ((pw & RW5) & BW5). unfold rcells, nn, ovf in RW5.
  replace (Z.min (Z.of_nat (length W4)) (5 - 1)) with (Z.of_nat (length W4)) in RW5 by (rewrite LW; reflexivity).
  replace (5 - 1 <? Z.of_nat (length W4)) with false in RW5 by (rewrite LW; reflexivity).
  rewrite firstn_all2 in BW5 by (rewrite LW; cbn; lia).
  destruct BW5 as (rbw & Lbw & UBW).
  step. step. bfalse.
  step. step. bfalse.
  step. step. step.
  pose proof (u8arr_store_ok rsegs m5 (S + -109) _ (Z.of_nat (length W4)) _ UBW
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst UBW.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
  pose proof (bbuf_upd _ _ 5 _ _ _ HW Lbw ltac:(lia)) as BW6. clear HW.
  destruct BW6 as (rbw6 & Lbw6 & UBW6).
  step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
  lazymatch goal with
  | H : rw_cells rsegs m7 (S + -200) [C8 ?p; C8 ?c; C8 ?n; C8 (Z_to_bv 64 0)] |- _ =>
      change [C8 p; C8 c; C8 n; C8 (Z_to_bv 64 0)] with ([C8 p; C8 c; C8 n] ++ [C8 (Z_to_bv 64 0)]) in H;
      apply conv_z8 in H; cbn [app] in H; rename H into RN7
  end.
  pose proof (sbx_init m7 (S + -200) (S + -168) 24 jbn RN7 BN2 ltac:(lia)) as SBN. clear RN7 BN2.
  assert (R0 : 0 < nth 0 STM 0 < 256) by (rewrite Forall_forall in STC; apply STC; apply nth_In; destruct (bn_stem f sd); [congruence | cbn; lia]).
  lazymatch goal with H : munch _ m m7 |- _ => rename H into MU7 end.
  assert (STB7 : bytes_at rsegs m7 P (bn_bytes STM ++ Z_to_bv 8 0 :: sl)).
  { eapply bytes_at_transport; [exact STB | exact MU7 |]. cbn [disjoint_from].
    rewrite length_app, bn_bytes_length. cbn [length]. split; [lia | exact I]. }
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) STB7) as [STB1 _].
  pose proof (rd_nth m7 P STM 0 STB1 ltac:(destruct (bn_stem f sd); [congruence | cbn; lia])) as RD0.
  replace (P + Z.of_nat 0) with P in RD0 by lia. clear STB1.
  step. step. bfalse.
  step. step.
  assert (ESTM : STM = nth 0 STM 0 :: tl STM) by (destruct (bn_stem f sd); [congruence | reflexivity]).
  assert (LT : length STM = Datatypes.S (length (tl STM))) by (rewrite ESTM at 1; reflexivity).
  assert (STB8 : bytes_at rsegs m7 P (bn_bytes (STM ++ [0]))).
  { rewrite bn_bytes_app.
    replace (bn_bytes STM ++ Z_to_bv 8 0 :: sl) with ((bn_bytes STM ++ bn_bytes [0]) ++ sl) in STB7
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in STB7. tauto. }
  pose proof STB8 as HB8. pose proof STC as STC8. rewrite ESTM in HB8, STC8.
  replace (Z_to_bv 64 P) with (Z_to_bv 64 (P + Z.of_nat (length (@nil Z)))) by (f_equal; cbn [length]; lia).
  lazymatch goal with H : wmono rsegs m m7 |- _ => rename H into WM7 end.
  eapply stem_loop with (lo := lo) (Q := Q0) (rest := tl STM) (done := []) (X := []) (c := nth 0 STM 0) (m2 := m7) (P := P);
    [ .. | ];
    [ first [exact SBCH | exact S16 | exact HB8 | exact STC8 | exact SBN | assumption | (unfold BN_K; lia)
            | (cbn [length]; lia)] .. | ].
  intros m8 q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 SB8 MU8 WM8 MI8 ST8.
  cbn [app] in SB8. rewrite <- ESTM in SB8.
  clear HB8 STC8 STB8 STB7 SBN.
  xport m7 m8 MU8 WM8.
  pose proof (munch_sub _ _ _ _ _ _ MU7 MU8 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU8'.
  pose proof (wmono_trans _ _ _ _ WM7 WM8) as WM8'.
  clear MU7 WM7 MU8 WM8.
  assert (STB9 : bytes_at rsegs m8 P (bn_bytes STM ++ Z_to_bv 8 0 :: sl)).
  { eapply bytes_at_transport; [exact STB | exact MU8' |]. cbn [disjoint_from].
    rewrite length_app, bn_bytes_length. cbn [length]. split; [lia | exact I]. }
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UBW6)) as [W4B _].
  lazymatch goal with H : rw_cells rsegs m8 (S + -112) [CB 3 ?g] |- _ => rename H into G38 end.
  replace (S + -109) with (S + -112 + Z.of_nat 3) in UBW6 by lia.
  pose proof (rw_u8_cat _ _ _ _ _ G38 UBW6) as GW8.
  rewrite length_app, bn_bytes_length, Lbw6 in GW8. cbn [Nat.add] in GW8.
  assert (NMB : Forall (fun c => 0 < c < 256) NM) by (apply NM_chars; assumption).
  assert (NM1 : (1 <= length NM)%nat) by (pose proof (NM_len f sd i o); lia).
  rewrite LW in RW5.
  replace (P + Z.of_nat (length (@nil Z))) with P by (cbn [length]; lia).
  eapply seg_cmp; try eassumption; unfold BN_K; try lia.
Qed.

End BoxName.
