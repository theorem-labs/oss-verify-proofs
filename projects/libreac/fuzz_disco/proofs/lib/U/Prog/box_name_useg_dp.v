From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c memcpy_c strlen_c
  box_name_ucall box_name_ubase box_name_useg_end.
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

Lemma rd_mid : forall mm P done c rest, bytes_at rsegs mm P (bn_bytes (done ++ c :: rest)) ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (P + Z.of_nat (length done))) 1 = Some [Z_to_bv 8 c].
Proof.
  intros mm P done c rest H. rewrite bn_bytes_app in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite bn_bytes_length in H.
  pose proof (bytes_at_read rsegs mm _ _ 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
  unfold wa in R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma out_loop : forall (Q : machine_state -> Prop) (rest done X : list Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (P E : Z),
  lo + BN_K <= S -> S mod 16 = 0 -> rest <> [] -> E = P + Z.of_nat (length done) + Z.of_nat (length rest) ->
  bytes_at rsegs m2 P (bn_bytes (done ++ rest)) -> Forall (fun c => 0 <= c < 256) rest ->
  (E <= S - BN_K \/ S <= P) -> E < 2^64 ->
  sbx m2 (S + -336) (S + -304) 48 X -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     sbx m3 (S + -336) (S + -304) 48 (X ++ rest) ->
     munch [(S + -336, S + -256)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 (Z_to_bv 64 E) y10 y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 (Z_to_bv 64 E) x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x151c8) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (P + Z.of_nat (length done)))
                       x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 E) x22 x23 x24 x25 x26 x27
                       x28 x29 x30 x31)
                  F (Z_to_bv 64 0x151b4) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q rest. induction rest as [|c rest IH];
    intros done X m2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      P E HLO S16 NE HE HB HC DJ E64 SB MI ST K; [congruence|].
  clear NE. unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q0' & _); exact Q0').
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite bn_bytes_length, length_app in BB. cbn [length] in BB, HE.
  pose proof (Forall_inv HC) as Hc. pose proof (Forall_inv_tail HC) as HC'. cbv beta in Hc.
  pose proof (rd_mid _ _ _ _ _ HB) as RD.
  step. step. step.
  eapply (ch_call SBCH) with (A := S + -336) (B := S + -304) (cap := 48) (c := c) (lo := lo) (hi := S + -352) (s := X);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | rewrite bl_zxb by lia; reflexivity | lia | lia
    | exact SB | lia | exact MI | exact ST | lia | lia | lia |].
  intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3.
  pose proof (bytes_at_keep _ _ _ _ _ HB MU3) as HB3.
  step. step.
  destruct rest as [|c' rest'].
  - cbn [length] in HE. bfalse.
    replace (P + Z.of_nat (length done) + 1) with E by lia.
    eapply K; [exact SB3 | | exact WM3 | exact MI3 | exact ST3].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
  - cbn [length] in HE. btrue.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length (done ++ [c]))) by (rewrite length_app; cbn [length]; lia).
    eapply (IH (done ++ [c]) (X ++ [c]) m3); [lia | lia | discriminate | rewrite length_app; cbn [length]; lia | | exact HC'
      | lia | lia | exact SB3 | exact MI3 | exact ST3 |].
    + rewrite <- app_assoc. cbn [app]. apply HB3. intros x Hx. rewrite bn_bytes_length, length_app in Hx.
      cbn [length outside] in *. lia.
    + intros m4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
      rewrite <- app_assoc in SB4. cbn [app] in SB4.
      eapply K; [exact SB4 | | exact (wmono_trans _ _ _ _ WM3 WM4) | exact MI4 | exact ST4].
      apply (munch_trans _ m2 m3 m4); [|exact MU4].
      eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
Qed.

Lemma in_loop : forall (Q : machine_state -> Prop) (rest done X : list Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (P E : Z),
  lo + BN_K <= S -> S mod 16 = 0 -> rest <> [] -> E = P + Z.of_nat (length done) + Z.of_nat (length rest) ->
  bytes_at rsegs m2 P (bn_bytes (done ++ rest)) -> Forall (fun c => 0 <= c < 256) rest ->
  (E <= S - BN_K \/ S <= P) -> E < 2^64 ->
  sbx m2 (S + -336) (S + -304) 48 X -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     sbx m3 (S + -336) (S + -304) 48 (X ++ rest) ->
     munch [(S + -336, S + -256)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 (Z_to_bv 64 E) y10 y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 x21 (Z_to_bv 64 E) x23 x24 x25 x26 x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x15198) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (P + Z.of_nat (length done)))
                       x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 E) x23 x24 x25 x26 x27
                       x28 x29 x30 x31)
                  F (Z_to_bv 64 0x15184) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q rest. induction rest as [|c rest IH];
    intros done X m2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31
      P E HLO S16 NE HE HB HC DJ E64 SB MI ST K; [congruence|].
  clear NE. unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q0' & _); exact Q0').
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite bn_bytes_length, length_app in BB. cbn [length] in BB, HE.
  pose proof (Forall_inv HC) as Hc. pose proof (Forall_inv_tail HC) as HC'. cbv beta in Hc.
  pose proof (rd_mid _ _ _ _ _ HB) as RD.
  step. step. step.
  eapply (ch_call SBCH) with (A := S + -336) (B := S + -304) (cap := 48) (c := c) (lo := lo) (hi := S + -352) (s := X);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | rewrite bl_zxb by lia; reflexivity | lia | lia
    | exact SB | lia | exact MI | exact ST | lia | lia | lia |].
  intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3.
  pose proof (bytes_at_keep _ _ _ _ _ HB MU3) as HB3.
  step. step.
  destruct rest as [|c' rest'].
  - cbn [length] in HE. bfalse.
    replace (P + Z.of_nat (length done) + 1) with E by lia.
    eapply K; [exact SB3 | | exact WM3 | exact MI3 | exact ST3].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
  - cbn [length] in HE. btrue.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length (done ++ [c]))) by (rewrite length_app; cbn [length]; lia).
    eapply (IH (done ++ [c]) (X ++ [c]) m3); [lia | lia | discriminate | rewrite length_app; cbn [length]; lia | | exact HC'
      | lia | lia | exact SB3 | exact MI3 | exact ST3 |].
    + rewrite <- app_assoc. cbn [app]. apply HB3. intros x Hx. rewrite bn_bytes_length, length_app in Hx.
      cbn [length outside] in *. lia.
    + intros m4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
      rewrite <- app_assoc in SB4. cbn [app] in SB4.
      eapply K; [exact SB4 | | exact (wmono_trans _ _ _ _ WM3 WM4) | exact MI4 | exact ST4].
      apply (munch_trans _ m2 m3 m4); [|exact MU4].
      eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
Qed.

Lemma paren_loop : forall (Q : machine_state -> Prop) (rest done X : list Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (P E : Z),
  lo + BN_K <= S -> S mod 16 = 0 -> rest <> [] -> E = P + Z.of_nat (length done) + Z.of_nat (length rest) ->
  bytes_at rsegs m2 P (bn_bytes (done ++ rest)) -> Forall (fun c => 0 <= c < 256) rest ->
  (E <= S - BN_K \/ S <= P) -> E < 2^64 ->
  sbx m2 (S + -336) (S + -304) 48 X -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     sbx m3 (S + -336) (S + -304) 48 (X ++ rest) ->
     munch [(S + -336, S + -256)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 (Z_to_bv 64 E) y10 y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 x21 x22 (Z_to_bv 64 E) x24 x25 x26 x27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x15168) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (P + Z.of_nat (length done)))
                       x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 E) x24 x25 x26 x27
                       x28 x29 x30 x31)
                  F (Z_to_bv 64 0x15154) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q rest. induction rest as [|c rest IH];
    intros done X m2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      P E HLO S16 NE HE HB HC DJ E64 SB MI ST K; [congruence|].
  clear NE. unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q0' & _); exact Q0').
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite bn_bytes_length, length_app in BB. cbn [length] in BB, HE.
  pose proof (Forall_inv HC) as Hc. pose proof (Forall_inv_tail HC) as HC'. cbv beta in Hc.
  pose proof (rd_mid _ _ _ _ _ HB) as RD.
  step. step. step.
  eapply (ch_call SBCH) with (A := S + -336) (B := S + -304) (cap := 48) (c := c) (lo := lo) (hi := S + -352) (s := X);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | rewrite bl_zxb by lia; reflexivity | lia | lia
    | exact SB | lia | exact MI | exact ST | lia | lia | lia |].
  intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3.
  pose proof (bytes_at_keep _ _ _ _ _ HB MU3) as HB3.
  step. step.
  destruct rest as [|c' rest'].
  - cbn [length] in HE. bfalse.
    replace (P + Z.of_nat (length done) + 1) with E by lia.
    eapply K; [exact SB3 | | exact WM3 | exact MI3 | exact ST3].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
  - cbn [length] in HE. btrue.
    replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length (done ++ [c]))) by (rewrite length_app; cbn [length]; lia).
    eapply (IH (done ++ [c]) (X ++ [c]) m3); [lia | lia | discriminate | rewrite length_app; cbn [length]; lia | | exact HC'
      | lia | lia | exact SB3 | exact MI3 | exact ST3 |].
    + rewrite <- app_assoc. cbn [app]. apply HB3. intros x Hx. rewrite bn_bytes_length, length_app in Hx.
      cbn [length outside] in *. lia.
    + intros m4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
      rewrite <- app_assoc in SB4. cbn [app] in SB4.
      eapply K; [exact SB4 | | exact (wmono_trans _ _ _ _ WM3 WM4) | exact MI4 | exact ST4].
      apply (munch_trans _ m2 m3 m4); [|exact MU4].
      eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia.
Qed.

Lemma lit_get : forall mk P l, bn_lit m (S - BN_K) S P l -> munch [(S - BN_K, S)] m mk ->
  bytes_at rsegs mk P (bn_bytes ([] ++ l)) /\ (P + Z.of_nat (length l) <= S - BN_K \/ S <= P) /\
  P + Z.of_nat (length l) < 2^64.
Proof.
  intros mk P l (HB & DJ) MU.
  assert (HB2 : bytes_at rsegs mk P (bn_bytes (l ++ [0]))).
  { eapply bytes_at_transport; [exact HB | exact MU |]. rewrite bn_bytes_length, length_app. cbn [length].
    rewrite Nat2Z.inj_add. exact DJ. }
  pose proof (bytes_at_bound _ _ _ _ HB2) as BB. rewrite bn_bytes_length, length_app in BB. cbn [length] in BB.
  cbn [disjoint_from] in DJ.
  rewrite bn_bytes_app in HB2. apply bytes_at_app in HB2. destruct HB2 as [H _].
  split; [exact H|]. split; lia.
Qed.

Lemma sbx_fin : forall mm A B cap s, sbx mm A B cap s -> Z.of_nat (length s) < cap - 1 ->
  (exists pad, rw_cells rsegs mm A [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 (Z.of_nat (length s)));
                                    C4 (Z_to_bv 64 0); C4 pad]) /\ bbuf mm B (Z.to_nat cap) s.
Proof.
  intros mm A B cap s ((pad & RC) & BB) L. unfold rcells, nn, ovf in RC.
  replace (Z.min (Z.of_nat (length s)) (cap - 1)) with (Z.of_nat (length s)) in RC by lia.
  replace (cap - 1 <? Z.of_nat (length s)) with false in RC by (symmetry; apply Z.ltb_ge; lia).
  rewrite firstn_all2 in BB by lia.
  split; [exists pad; exact RC | exact BB].
Qed.

Ltac fa := repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil.

Lemma seg_dp : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (j0 jw jgw : list byte) (pt pn pw : word),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 8 j0; C8 display] ->
  sbx m2 (S + -336) (S + -304) 48 LN ->
  rw_cells rsegs m2 (S + -256)
    [C8 (Z_to_bv 64 (S + -224)); C8 (Z_to_bv 64 24); C8 (Z_to_bv 64 (Z.of_nat (length (bn_tk false LN))));
     C4 (Z_to_bv 64 0); C4 pt] ->
  bbuf m2 (S + -224) 24 (bn_tk false LN ++ [0]) ->
  rw_cells rsegs m2 (S + -200)
    [C8 (Z_to_bv 64 (S + -168)); C8 (Z_to_bv 64 24); C8 (Z_to_bv 64 (Z.of_nat (length LN)));
     C4 (Z_to_bv 64 NOV); C4 pn] ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) x23 display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x15148) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 j0 jw jgw pt pn pw
    HLO S16 AOK BUFS ST2 MU2 WM2 MI2 SV2 DS2 SB2 RT2 TK2 RN2 NM2 RW2 GW2.
  pose proof HIM as (_ & _ & _ & _ & _ & _ & LPA & LIN & LOU).
  destruct TK2 as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  destruct (bn_ok_dec i OKI) as (RI & _ & _ & _ & DI & _).
  destruct (bn_ok_dec o OKO) as (RO & _ & _ & _ & DO & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q' & _); exact Q').
  destruct (lit_get m2 BN_PAREN [32; 40] LPA MU2) as (PB & PD & PE).
  unfold BN_K, BN_PAREN in *.
  step. step. step.
  change (Z_to_bv 64 66471) with (Z_to_bv 64 (66471 + Z.of_nat (length (@nil Z)))).
  eapply (paren_loop Q0 [32; 40] [] LN m2) with (E := 66473);
    [unfold BN_K; lia | exact S16 | discriminate | cbn [length]; lia | exact PB | fa
    | cbn [length] in PD; unfold BN_K in *; lia | lia
    | exact SB2 | exact MI2 | exact ST2 |].
  intros m3 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3.
  clear PB PD PE.
  xport m2 m3 MU3 WM3.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MU3 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU3'.
  pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM3'.
  clear MU2 WM2 MU3 WM3 ST2 SB2 MI2.
  step. step. step. step.
  eapply (dec_call DEC) with (A := S + -336) (B := S + -304) (cap := 48) (v := i) (md := 1) (lo := lo)
    (s := LN ++ [32; 40]);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | lia | reflexivity | left; reflexivity
    | reflexivity | lia | exact SB3 | lia | exact MI3 | rewrite unsigned_lit by lia; exact ST3
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia |].
  intros m4 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
  rewrite unsigned_lit in MU4, ST4 by lia.
  xport m3 m4 MU4 WM4.
  pose proof (munch_sub _ _ _ _ _ _ MU3' MU4 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU4'.
  pose proof (wmono_trans _ _ _ _ WM3' WM4) as WM4'.
  clear MU3' WM3' MU4 WM4 ST3 SB3 MI3.
  destruct (lit_get m4 BN_IN [32; 105; 110; 32; 47; 32] LIN MU4') as (PB & PD & PE).
  unfold BN_IN in *.
  step. step. step.
  change (Z_to_bv 64 66347) with (Z_to_bv 64 (66347 + Z.of_nat (length (@nil Z)))).
  eapply (in_loop Q0 [32; 105; 110; 32; 47; 32] [] ((LN ++ [32; 40]) ++ sb_dec_D i 1) m4) with (E := 66353);
    [unfold BN_K; lia | exact S16 | discriminate | cbn [length]; lia | exact PB | fa
    | cbn [length] in PD; unfold BN_K in *; lia | lia
    | exact SB4 | exact MI4 | exact ST4 |].
  intros m5 u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 SB5 MU5 WM5 MI5 ST5.
  clear PB PD PE.
  xport m4 m5 MU5 WM5.
  pose proof (munch_sub _ _ _ _ _ _ MU4' MU5 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU5'.
  pose proof (wmono_trans _ _ _ _ WM4' WM5) as WM5'.
  clear MU4' WM4' MU5 WM5 ST4 SB4 MI4.
  step. step. step. step.
  eapply (dec_call DEC) with (A := S + -336) (B := S + -304) (cap := 48) (v := o) (md := 1) (lo := lo)
    (s := ((LN ++ [32; 40]) ++ sb_dec_D i 1) ++ [32; 105; 110; 32; 47; 32]);
    [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | lia | reflexivity | left; reflexivity
    | reflexivity | lia | exact SB5 | lia | exact MI5 | rewrite unsigned_lit by lia; exact ST5
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia |].
  intros m6 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 SB6 MU6 WM6 MI6 ST6.
  rewrite unsigned_lit in MU6, ST6 by lia.
  xport m5 m6 MU6 WM6.
  pose proof (munch_sub _ _ _ _ _ _ MU5' MU6 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU6'.
  pose proof (wmono_trans _ _ _ _ WM5' WM6) as WM6'.
  clear MU5' WM5' MU6 WM6 ST5 SB5 MI5.
  destruct (lit_get m6 BN_OUT [32; 111; 117; 116; 41] LOU MU6') as (PB & PD & PE).
  unfold BN_OUT in *.
  step. step. step.
  change (Z_to_bv 64 66726) with (Z_to_bv 64 (66726 + Z.of_nat (length (@nil Z)))).
  eapply (out_loop Q0 [32; 111; 117; 116; 41] []
            ((((LN ++ [32; 40]) ++ sb_dec_D i 1) ++ [32; 105; 110; 32; 47; 32]) ++ sb_dec_D o 1) m6)
    with (E := 66731);
    [unfold BN_K; lia | exact S16 | discriminate | cbn [length]; lia | exact PB | fa
    | cbn [length] in PD; unfold BN_K in *; lia | lia
    | exact SB6 | exact MI6 | exact ST6 |].
  intros m7 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 SB7 MU7 WM7 MI7 ST7.
  clear PB PD PE.
  xport m6 m7 MU7 WM7.
  pose proof (munch_sub _ _ _ _ _ _ MU6' MU7 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU7'.
  pose proof (wmono_trans _ _ _ _ WM6' WM7) as WM7'.
  clear MU6' WM6' MU7 WM7 ST6 SB6 MI6.
  assert (EDP : (((((LN ++ [32; 40]) ++ sb_dec_D i 1) ++ [32; 105; 110; 32; 47; 32]) ++ sb_dec_D o 1) ++
                 [32; 111; 117; 116; 41]) = bn_DP LN i o).
  { unfold bn_DP. rewrite DI, DO. rewrite <- !app_assoc. reflexivity. }
  rewrite EDP in SB7.
  assert (LLN : (length LN <= 23)%nat) by (rewrite length_firstn; lia).
  pose proof (bn_DP_len LN i o OKI OKO) as LDP.
  destruct (sbx_fin _ _ _ _ _ SB7 ltac:(lia)) as ((pd & RD7) & DP7).
  eapply seg_final; try eassumption; unfold BN_K; try lia.
  - exists rtk. split; [exact Ltk | exact UTK].
  - exists rnm. split; [exact Lnm | exact UNM].
Qed.

End BoxName.
