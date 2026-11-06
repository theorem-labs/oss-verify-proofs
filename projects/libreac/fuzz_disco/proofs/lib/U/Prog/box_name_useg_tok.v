From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c memcpy_c strlen_c
  box_name_ucall box_name_ubase box_name_useg_end box_name_useg_dp box_name_useg_tkz.
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

Lemma low_u : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (zxb (Z_to_bv 8 c)))
     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned
        (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 c)) + -65))) 255)) 26)) 5)))) = Z_to_bv 64 (bn_low c).
Proof.
  intros c Hc. rewrite (bl_zxb c Hc).
  assert (A : forallb (fun c => bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 c))
     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned
        (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 c) + -65))) 255)) 26)) 5))))) =? bn_low c)
     (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A.
  specialize (A c ltac:(apply in_map_iff; exists (Z.to_nat c); split; [lia | apply in_seq; lia])).
  apply Z.eqb_eq in A. apply bv_eq. rewrite A.
  pose proof (bn_low_rng c Hc) as R. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma tok_body : forall (Q : machine_state -> Prop) (k : nat) (L : list Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word) (pr cr ovr pdr : word),
  lo + BN_K <= S -> S mod 16 = 0 -> (k < length L)%nat -> (length L <= 23)%nat ->
  Forall (fun c => 0 < c < 256) L ->
  bytes_at rsegs m2 (S + -168) (bn_bytes (L ++ [0])) ->
  rw_cells rsegs m2 (S + -200) [C8 pr; C8 cr; C8 (Z_to_bv 64 (Z.of_nat (length L))); C4 ovr; C4 pdr] ->
  sbx m2 (S + -256) (S + -224) 24 (bn_tk false (firstn k L)) -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     sbx m3 (S + -256) (S + -224) 24 (bn_tk false (firstn (Datatypes.S k) L)) ->
     munch [(S + -256, S + -200)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 (Z_to_bv 64 45)
                          (Z_to_bv 64 (Z.of_nat (length L))) y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 x21 x22 (Z_to_bv 64 24) x24 (Z_to_bv 64 (Z.of_nat k))
                          (Z_to_bv 64 (tk_d (firstn (Datatypes.S k) L))) (Z_to_bv 64 (S + -168)) y28 y29 y30 y31)
                     F (Z_to_bv 64 0x150dc) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 45) (Z_to_bv 64 (Z.of_nat (length L)))
                       x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 24) x24
                       (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (tk_d (firstn k L))) (Z_to_bv 64 (S + -168))
                       x28 x29 x30 x31)
                  F (Z_to_bv 64 0x150a0) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q k L m2 x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31 pr cr ovr pdr
    HLO S16 HK HL HC HB RN SB MI ST K.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q0' & _); exact Q0').
  assert (Hc : 0 < nth k L 0 < 256) by (rewrite Forall_forall in HC; apply HC; apply nth_In; lia).
  pose proof (rd_nth m2 (S + -168) (L ++ [0]) k HB ltac:(rewrite length_app; cbn [length]; lia)) as RD.
  rewrite app_nth1 in RD by lia.
  pose proof (tk_d_rng (firstn k L)) as TR.
  pose proof (bn_low_rng (nth k L 0) ltac:(lia)) as (LR & _).
  assert (APP : bn_tk false (firstn (Datatypes.S k) L) = bn_tk false (firstn k L) ++ [bn_low (nth k L 0)] ->
                tk_d (firstn (Datatypes.S k) L) = tk_d (firstn k L) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 45)
                         (Z_to_bv 64 (Z.of_nat (length L))) (zxb (Z_to_bv 8 (nth k L 0)))
                         x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 24) x24
                         (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (tk_d (firstn k L))) (Z_to_bv 64 (S + -168))
                         x28 x29 x30 x31)
                    F (Z_to_bv 64 0x150bc) fc None m2 (seg_rom rsegs))).
  { intros E1 E2.
    step. step. step. step. step.
    lazymatch goal with
    | |- context [Z_to_bv 64 (Z.lor (bv_unsigned (zxb (Z_to_bv 8 ?c))) ?e)] =>
        replace (Z_to_bv 64 (Z.lor (bv_unsigned (zxb (Z_to_bv 8 c))) e)) with (Z_to_bv 64 (bn_low c))
          by (symmetry; apply low_u; lia)
    end.
    step. step.
    eapply (ch_call SBCH) with (A := S + -256) (B := S + -224) (cap := 24) (c := bn_low (nth k L 0)) (lo := lo)
      (hi := S + -352) (s := bn_tk false (firstn k L));
      [lia | reflexivity | rewrite unsigned_lit by lia; reflexivity | lia | reflexivity | lia | lia
      | exact SB | lia | exact MI | exact ST | lia | lia | lia |].
    intros m3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3.
    apply (rw_cells_transport rsegs [(S + -256, S + -256 + 32); (S + -224, S + -224 + 24)] m2 m3) in RN; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; repeat split; first [exact I | lia]].
    step.
    rewrite <- E2. eapply K; [rewrite E1; exact SB3 | | exact WM3 | exact MI3 | exact ST3].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *. lia. }
  pose proof (bn_tk_snoc L k HK) as TS. pose proof (tk_d_snoc L k HK) as DS.
  step. bfalse.
  step. step. step.
  destruct (Z.eqb_spec (nth k L 0) 45) as [C45|C45].
  - bfalse. step.
    destruct (existsb (fun c => c =? 45) (firstn k L)) eqn:EX.
    + assert (T1 : tk_d (firstn k L) = 1) by (unfold tk_d; rewrite EX; reflexivity).
      rewrite T1. btrue. rewrite <- T1.
      apply APP.
      * rewrite TS. reflexivity.
      * rewrite DS, T1. reflexivity.
    + assert (T0 : tk_d (firstn k L) = 0) by (unfold tk_d; rewrite EX; reflexivity).
      rewrite T0. bfalse. step. step.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 (tk_d (firstn (Datatypes.S k) L)))
        by (rewrite DS; reflexivity).
      assert (TS0 : bn_tk false (firstn (Datatypes.S k) L) = bn_tk false (firstn k L))
        by (rewrite TS; apply app_nil_r).
      eapply K; [rewrite TS0; exact SB | apply munch_refl | apply wmono_refl | exact MI | exact ST].
  - btrue. apply APP.
    + rewrite TS. reflexivity.
    + rewrite DS, orb_false_r. reflexivity.
Qed.

Lemma tok_loop : forall (Q : machine_state -> Prop) (j k : nat) (L : list Z) (m2 : word -> option byte)
    (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word) (pr cr ovr pdr : word),
  lo + BN_K <= S -> S mod 16 = 0 -> (k + Datatypes.S j = length L)%nat -> (length L <= 23)%nat ->
  Forall (fun c => 0 < c < 256) L ->
  bytes_at rsegs m2 (S + -168) (bn_bytes (L ++ [0])) ->
  rw_cells rsegs m2 (S + -200) [C8 pr; C8 cr; C8 (Z_to_bv 64 (Z.of_nat (length L))); C4 ovr; C4 pdr] ->
  sbx m2 (S + -256) (S + -224) 24 (bn_tk false (firstn k L)) -> mem_inv rsegs m2 -> stk rsegs m2 lo (S + -352) ->
  (forall (m3 : word -> option byte)
          (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y25 y26 y27 y28 y29 y30 y31 : word),
     sbx m3 (S + -256) (S + -224) 24 (bn_tk false L) ->
     munch [(S + -256, S + -200)] m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (S + -352) ->
     evt rsegs Q (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 x8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                          x18 x19 x20 x21 x22 y23 x24 y25 y26 y27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x150e4) fc None m3 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 (Z_to_bv 64 45) (Z_to_bv 64 (Z.of_nat (length L)))
                       x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 24) x24
                       (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (tk_d (firstn k L))) (Z_to_bv 64 (S + -168))
                       x28 x29 x30 x31)
                  F (Z_to_bv 64 0x150a0) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q j. induction j as [|j IH];
    intros k L m2 x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x28 x29 x30 x31 pr cr ovr pdr
      HLO S16 HK HL HC HB RN SB MI ST K;
    (eapply tok_body; [exact HLO | exact S16 | lia | exact HL | exact HC | exact HB | exact RN | exact SB | exact MI
                       | exact ST |]);
    intros m3 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SB3 MU3 WM3 MI3 ST3;
    unfold BN_K in *;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
    step; step.
  - bfalse.
    rewrite firstn_all2 in SB3 by lia.
    eapply K; [exact SB3 | exact MU3 | exact WM3 | exact MI3 | exact ST3].
  - btrue.
    replace (Z.of_nat k + 1) with (Z.of_nat (Datatypes.S k)) by lia.
    eapply (IH (Datatypes.S k) L m3); [unfold BN_K; lia | exact S16 | lia | exact HL | exact HC | | | exact SB3
      | exact MI3 | exact ST3 |].
    + eapply bytes_at_keep; [exact HB | exact MU3 |]. intros x Hx. rewrite bn_bytes_length, length_app in Hx.
      cbn [length outside] in *. lia.
    + apply (rw_cells_transport rsegs [(S + -256, S + -200)] m2 m3) in RN;
        [exact RN | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; repeat split; first [exact I | lia]].
    + intros m4 z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z23 z25 z26 z27 z28 z29 z30 z31 SB4 MU4 WM4 MI4 ST4.
      eapply K; [exact SB4 | exact (munch_trans _ _ _ _ MU3 MU4) | exact (wmono_trans _ _ _ _ WM3 WM4) | exact MI4
        | exact ST4].
Qed.

Lemma seg_tok : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (j0 jrd jbd jrt jbt jw jgw : list byte) (pw : word),
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
  rw_cells rsegs m2 (S + -256) [CB 32 jrt] ->
  rw_cells rsegs m2 (S + -224) [CB 24 jbt] ->
  sbx m2 (S + -200) (S + -168) 24 NM ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) x23 display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x15054) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x27 x28 x29 x30 x31 j0 jrd jbd jrt jbt jw jgw pw
    HLO S16 AOK BUFS NMB NM1 ST2 MU2 WM2 MI2 SV2 DS2 RD2 BD2 RT2 BT2 SBN RW2 GW2.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  assert (LLN : (1 <= length LN <= 23)%nat) by (rewrite length_firstn; lia).
  assert (LNB : Forall (fun c => 0 < c < 256) LN).
  { pose proof NMB as Q. rewrite <- (firstn_skipn 23 NM) in Q. apply Forall_app in Q. tauto. }
  destruct SBN as ((pn & RN2) & NB). unfold rcells, nn in RN2.
  replace (Z.min (Z.of_nat (length NM)) (24 - 1)) with (Z.of_nat (length LN)) in RN2 by (rewrite length_firstn; lia).
  destruct NB as (rnm & Lnm & UNM).
  change (firstn (Z.to_nat (24 - 1)) NM) with LN in UNM, Lnm.
  step. step. step. bfalse.
  step. step. step. bfalse.
  step. step.
  pose proof (u8arr_store_ok rsegs m2 (S + -168) _ (Z.of_nat (length LN)) _ UNM
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst UNM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  pose proof (bbuf_upd _ _ 24 _ _ _ HW Lnm ltac:(lia)) as NM3. clear HW.
  destruct NM3 as (rnm3 & Lnm3 & UNM3).
  step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
  lazymatch goal with
  | H : rw_cells rsegs m4 (S + -256) [C8 ?p; C8 ?c; C8 ?n; C8 (Z_to_bv 64 0)] |- _ =>
      change [C8 p; C8 c; C8 n; C8 (Z_to_bv 64 0)] with ([C8 p; C8 c; C8 n] ++ [C8 (Z_to_bv 64 0)]) in H;
      apply conv_z8 in H; cbn [app] in H; rename H into RT4
  end.
  pose proof (sbx_init m4 (S + -256) (S + -224) 24 jbt RT4 BT2 ltac:(lia)) as SBT. clear RT4 BT2.
  step. bfalse.
  step. step. step. step.
  pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM3)) as [NMB4 _].
  eapply (tok_loop Q0 (length LN - 1) 0 LN m4); [unfold BN_K; lia | exact S16 | lia | lia | exact LNB | exact NMB4
    | eassumption | exact SBT | assumption | assumption |].
  intros m5 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y23 y25 y26 y27 y28 y29 y30 y31 SB5 MU5 WM5 MI5 ST5.
  clear NMB4 SBT.
  xport m4 m5 MU5 WM5.
  pose proof (munch_sub _ _ _ _ _ _ MU2 MU5 ltac:(intros ?x ?Hx; cbn [outside] in *; lia)) as MU5'.
  pose proof (wmono_trans _ _ _ _ WM2 WM5) as WM5'.
  eapply seg_tkz; try eassumption; unfold BN_K; try lia.
  exists rnm3. split; [exact Lnm3 | exact UNM3].
Qed.

End BoxName.
