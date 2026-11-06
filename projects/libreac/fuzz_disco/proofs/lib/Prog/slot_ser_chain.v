From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_ser_defs slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c jtok_is_c strlen_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c json_scalar_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table disco_json_text reac_disco_table_json_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_Pq slot_ser slot_ser_J2 slot_ser_C1 slot_ser_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cons : forall m A B c cs, B = A + Z.of_nat (csize c) ->
  (rw_cells rsegs m A (c :: cs) <-> rw_cells rsegs m A [c] /\ rw_cells rsegs m B cs).
Proof.
  intros m A B c cs E. change (c :: cs) with ([c] ++ cs). rewrite rw_cells_app. cbn [cells_size].
  rewrite Nat.add_0_r. subst B. tauto.
Qed.

Lemma spill_iff : forall m X j0 j1 j2 j3 j4 h,
  rw_cells rsegs m X (spill_cells j0 j1 j2 j3 j4 h) <->
  rw_cells rsegs m X [CB 24 j0] /\ rw_cells rsegs m (X + 24) [C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 INV9)] /\ rw_cells rsegs m (X + 40) [CB 104 j1] /\
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 h)] /\ rw_cells rsegs m (X + 152) [CB 16 j2] /\
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 MS_NS)] /\ rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 STALE_NS)] /\
  rw_cells rsegs m (X + 184) [CB 24 j3] /\ rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 W0X0)] /\
  rw_cells rsegs m (X + 216) [CB 20 j4].
Proof.
  intros m X j0 j1 j2 j3 j4 h. unfold spill_cells.
  rewrite (rw_cons m X (X + 24)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 24) (X + 32)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 32) (X + 40)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 40) (X + 144)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 144) (X + 152)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 152) (X + 168)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 168) (X + 176)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 176) (X + 184)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 184) (X + 208)) by (cbn [csize]; lia).
  rewrite (rw_cons m (X + 208) (X + 216)) by (cbn [csize]; lia).
  tauto.
Qed.

Ltac out_all := intros x Hx; unfold SER_W in *; cbn [outside]; repeat split; try exact I; lia.
Ltac rwt H MU WM := eapply rw_tr; [exact H | exact MU | exact WM | cbn [cells_size csize spill_cells]; out_all].
Ltac bt H MU := eapply bytes_tr; [exact H | exact MU | rewrite ?length_le8; out_all].

Theorem slot_ser_chain_holds : reac_disco_table_json_contract -> strlen_contract -> json_scalar_contract ->
  jtok_is_contract -> reac_box_name_contract -> snprintf_stk_contract -> slot_ser_chain.
Proof.
  intros TJC SLC JS JT BNC SNK. split; [exact slot_R8_call|]. unfold ser_chain_B.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m canary
    X lo buf cap now n h i p T Lk Gt ob junk slk j0 j1 j2 j3 j4 j5 jw sv
    Esp Ea0 Es0 Es1 Es2 Es5 Es7 Es8 Es11 HX0 HX16 HX1 Hnow Hcap Hb Hb8 Hbl HIF HSL RB BS LT TOK
    SP R152 R200 RLK RGT RT ROB RW RSV JTB BN GG GW FC MI TM ST HLO HI.
  unfold OFF_LOCK, OFF_GATE, OFF_TABLE, OFF_OUR, OFF_WORK, OFF_SAVE in *.
  change TJ_K with 6224 in HLO. unfold IMG_END in HI.
  assert (HJL : JSON_SCALAR_L = 0x1fe28) by reflexivity. assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (HBN : BN_TS = 0x1fe40) by reflexivity. assert (LBN : Z.of_nat (length bn_table) = 24) by reflexivity.
  assert (HGG : GOT_GUARD = 0x1fee8) by reflexivity. assert (HGW : GUARD = 0x514d0) by reflexivity.
  pose proof SP as SPc.
  apply spill_iff in SPc as (P0 & P24 & P32 & P40 & P144 & P152 & P168 & P176 & P184 & P208 & P216).
  destruct (ser_split m X (X + 16) 16 8 24 j0 ltac:(lia) ltac:(lia) P0) as [Q0 Q16].
  destruct (ser_split m (X + 152) (X + 160) 8 8 16 j2 ltac:(lia) ltac:(lia) P152) as [_ Q160].
  destruct (ser_split m (X + 184) (X + 192) 8 16 24 j3 ltac:(lia) ltac:(lia) P184) as [Q184 Q192r].
  destruct (ser_split m (X + 192) (X + 200) 8 8 16 _ ltac:(lia) ltac:(lia) Q192r) as [Q192 _].
  destruct (ser_split m (X + 216) (X + 224) 8 12 20 j4 ltac:(lia) ltac:(lia) P216) as [Q216 Q224r].
  destruct (ser_split m (X + 224) (X + 232) 8 4 12 _ ltac:(lia) ltac:(lia) Q224r) as [Q224 Q232].
  destruct (ser_split m (X + 920) (X + 944) 24 1544 1568 jw ltac:(lia) ltac:(lia) RW) as [V920 V944r].
  destruct (ser_split m (X + 944) (X + 968) 24 1520 1544 _ ltac:(lia) ltac:(lia) V944r) as [V944 V968r].
  destruct (ser_split m (X + 968) (X + 992) 24 1496 1520 _ ltac:(lia) ltac:(lia) V968r) as [V968 V992r].
  destruct (ser_split m (X + 992) (X + 1024) 32 1464 1496 _ ltac:(lia) ltac:(lia) V992r) as [V992 V1024r].
  destruct (ser_split m (X + 1024) (X + 2320) 1296 168 1464 _ ltac:(lia) ltac:(lia) V1024r) as [V1024 V2320r].
  destruct (ser_split m (X + 2320) (X + 2344) 24 144 168 _ ltac:(lia) ltac:(lia) V2320r) as [V2320 V2344].
  clear Q192r Q224r V944r V968r V992r V1024r V2320r.
  pose proof (ser_cb_bytes _ _ _ _ RB) as JB. pose proof RB as RBw. apply ser_cb in RBw as (LJ & _ & _).
  subst sp a0 s0 s1 s2 s5 s7 s8 s11.
  eapply evt_cut.
  { eapply (slot_R8_ret TJC) with (X := X) (lo := lo) (buf := buf) (cap := cap) (now := now) (T := T) (junk := junk)
      (canary := canary);
      first [ reflexivity | eassumption | lia | (change TJ_K with 6224; lia) | (unfold IMG_END; lia) ]. }
  intros ms' (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 &
              F2 & fc2 & m2 & FC2 & FK2 & WM2 & MI2 & TM2 & ST2 & [(E2 & MU2) | (E2 & CL & MU2 & BT)]); subst ms'.
  - eapply evt_cut; [apply slot_R14|]. intros ms' E. cbv beta in E. subst ms'.
    assert (MUc : munch (SER_W lo X buf cap) m m2).
    { eapply munch_weaken; [|exact MU2]. unfold sub_fp, SER_W; cbn [outside]; intros; intuition lia. }
    apply evt_done. do 19 eexists. exists F2, fc2, m2, j0, j2, j3, j4, jw.
    split; [reflexivity|]. split; [exact FC2|]. split; [exact FK2|]. split; [exact MUc|]. split; [exact WM2|].
    split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
    split; [rwt SP MU2 WM2|]. split; [rwt R152 MU2 WM2|]. split; [rwt R200 MU2 WM2|].
    split; [rwt RLK MU2 WM2|]. split; [rwt RGT MU2 WM2|]. split; [rwt RT MU2 WM2|]. split; [rwt ROB MU2 WM2|].
    split; [rwt RW MU2 WM2|]. rwt RSV MU2 WM2.
  - assert (LT1 : length (firstn (Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1))
                           (skipn (Z.to_nat (Z.of_nat (length (tj_text T now)) + 1)) junk))
                   = Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1)).
    { rewrite length_firstn, length_skipn, LJ. lia. }
    pose proof (bytes_at_sub m buf junk (Z.of_nat (length (tj_text T now)) + 1)
                  (Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1)) JB ltac:(lia) ltac:(rewrite LJ; lia)) as TL.
    set (tl := firstn (Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1))
                 (skipn (Z.to_nat (Z.of_nat (length (tj_text T now)) + 1)) junk)) in TL, LT1.
    assert (TL2 : bytes_at rsegs m2 (buf + Z.of_nat (length (tj_text T now)) + 1) tl).
    { replace (buf + Z.of_nat (length (tj_text T now)) + 1) with (buf + (Z.of_nat (length (tj_text T now)) + 1))
        by lia.
      eapply bytes_tr; [exact TL | exact MU2 |]. rewrite LT1. out_all. }
    assert (SL2 : bytes_at rsegs m2 (buf + cap) slk) by bt BS MU2.
    assert (BSL : bytes_at rsegs m2 (buf + Z.of_nat (length (tj_text T now)) + 1) (tl ++ slk)).
    { apply bytes_at_app. split; [exact TL2|].
      replace (buf + Z.of_nat (length (tj_text T now)) + 1 + Z.of_nat (length tl)) with (buf + cap) by lia.
      exact SL2. }
    assert (ALN : (- (buf + Z.of_nat (length (tj_text T now)) + 1)) mod 8 <= Z.of_nat (length (tl ++ slk))).
    { rewrite length_app, Nat2Z.inj_add, LT1, Z2Nat.id by lia. Z.div_mod_to_equations. lia. }
    pose proof (img_free_out buf cap HIF ltac:(lia)) as DIMG.
    assert (JTB2 : bytes_at rsegs m2 JSON_SCALAR_L js_table) by bt JTB MU2.
    assert (BN2 : bytes_at rsegs m2 BN_TS bn_table) by bt BN MU2.
    assert (GG2 : bytes_at rsegs m2 GOT_GUARD (le8 (Z_to_bv 64 GUARD))) by bt GG MU2.
    assert (GW2 : bytes_at rsegs m2 GUARD (le8 canary)) by bt GW MU2.
    clear TL JB BS SL2 TL2 JTB BN GG GW.
    transport_after_call rsegs m m2 MU2 WM2.
    eapply evt_cut.
    { eapply (ser_tail SLC JS JT BNC SNK) with (X := X) (lo := lo) (buf := buf) (cap := cap) (now := now) (i := i)
        (p := p) (T := T) (slack := tl ++ slk) (canary := canary);
        try first [ reflexivity | exact BSL | exact ALN | eassumption | lia | (change TJ_K with 6224; lia)
              | (unfold IMG_END; lia) | (rewrite length_app; lia) ]. }
    intros ms' (t05 & t15 & t25 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s45 & s55 & s65 & s95 & s105 &
                t35 & t45 & t55 & t65 & F5 & fc5 & m5 & j0' & j192' & j216' & j224' & jw' &
                E5 & FC5 & FK5 & MU5 & WM5 & MI5 & TM5 & ST5 & C0' & C160' & C184' & C192' & C216' & C224' & CW').
    subst ms'. unfold W_TAIL in MU5.
    assert (MUc : munch (SER_W lo X buf cap) m m5).
    { eapply munch_trans; [eapply munch_weaken; [|exact MU2] | eapply munch_weaken; [|exact MU5]];
        unfold sub_fp, SER_W; cbn [outside]; intros; intuition lia. }
    pose proof (wmono_trans rsegs m m2 m5 WM2 WM5) as WMc.
    apply evt_done. do 19 eexists.
    exists F5, fc5, m5, (j0' ++ skipn 16 j0), (le8 (Z_to_bv 64 n) ++ le8 (Z_to_bv 64 i)),
      (le8 (Z_to_bv 64 p) ++ j192' ++ le8 (Z_to_bv 64 now)), (j216' ++ j224' ++ skipn 8 (skipn 8 j4)), jw'.
    split; [reflexivity|]. split; [exact FC5|].
    split; [intros k Hk; rewrite FK5 by exact Hk; apply FK2; exact Hk|].
    split; [exact MUc|]. split; [exact WMc|]. split; [exact MI5|]. split; [exact TM5|]. split; [exact ST5|].
    split.
    { apply spill_iff.
      split; [apply (ser_join m5 X (X + 16) 16 8 24); [lia | lia | exact C0' | rwt Q16 MU5 WM5]|].
      split; [rwt P24 MU5 WM5|]. split; [rwt P32 MU5 WM5|]. split; [rwt P40 MU5 WM5|]. split; [rwt P144 MU5 WM5|].
      split; [apply (ser_join m5 (X + 152) (X + 160) 8 8 16);
              [lia | lia | apply ser_c8; rwt R152 MU5 WM5 | apply ser_c8; exact C160']|].
      split; [rwt P168 MU5 WM5|]. split; [rwt P176 MU5 WM5|].
      split; [apply (ser_join m5 (X + 184) (X + 192) 8 16 24);
              [lia | lia | apply ser_c8; exact C184'
              | apply (ser_join m5 (X + 192) (X + 200) 8 8 16); [lia | lia | exact C192' | apply ser_c8; rwt R200 MU5 WM5]]|].
      split; [rwt P208 MU5 WM5|].
      apply (ser_join m5 (X + 216) (X + 224) 8 12 20);
        [lia | lia | exact C216' | apply (ser_join m5 (X + 224) (X + 232) 8 4 12); [lia | lia | exact C224' | rwt Q232 MU5 WM5]]. }
    split; [rwt R152 MU5 WM5|]. split; [rwt R200 MU5 WM5|]. split; [rwt RLK MU5 WM5|]. split; [rwt RGT MU5 WM5|].
    split; [rwt RT MU5 WM5|]. split; [rwt ROB MU5 WM5|]. split; [exact CW'|]. rwt RSV MU5 WM5.
Qed.
