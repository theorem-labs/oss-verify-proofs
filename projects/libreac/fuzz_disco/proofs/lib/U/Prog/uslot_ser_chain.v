From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_ser_defs slot_ser_pure slot_ser.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c snprintf_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c strlen_c disco_table_c json_scalar_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_defs uslot_ser_pure uslot_ser_tokb uslot_ser.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_Pq uslot_ser_iface uslot_ser_C1.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import jtok_is_c snprintf_stk_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require uslot_ser_J uslot_ser_P.
Open Scope Z_scope.

Lemma urw_cells_app : forall m A c1 c2,
  rw_cells rsegs m A (c1 ++ c2) <-> rw_cells rsegs m A c1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2.
Proof.
  intros m A c1 c2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (Ha & Hl & Hw)].
    rewrite cells_bytes_length in B2 by exact W1.
    split; split; try (split; assumption).
    + split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size c1) + i) with (A + (Z.of_nat (cells_size c1) + i)) by lia. apply Hw. lia.
  - intros [[[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)]].
    rewrite cells_bytes_length by exact W1.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size c1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size c1) + (i - Z.of_nat (cells_size c1))) by lia. apply Hw2. lia.
Qed.

Lemma urw_cons : forall m A B c cs, B = A + Z.of_nat (csize c) ->
  (rw_cells rsegs m A (c :: cs) <-> rw_cells rsegs m A [c] /\ rw_cells rsegs m B cs).
Proof.
  intros m A B c cs E. change (c :: cs) with ([c] ++ cs). rewrite urw_cells_app. cbn [cells_size].
  rewrite Nat.add_0_r. subst B. tauto.
Qed.

Lemma uspill_iff : forall m X j0 j1 j2 j3 j4 j5 j6 h,
  rw_cells rsegs m X (spill_cells j0 j1 j2 j3 j4 j5 j6 h X) <->
  rw_cells rsegs m X [CB 32 j0] /\ rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 INV9)] /\ rw_cells rsegs m (X + 48) [CB 72 j1] /\
  rw_cells rsegs m (X + 120) [C8 (Z_to_bv 64 STALE1)] /\ rw_cells rsegs m (X + 128) [C8 (Z_to_bv 64 0)] /\
  rw_cells rsegs m (X + 136) [CB 8 j2] /\ rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 MS_NS)] /\
  rw_cells rsegs m (X + 152) [CB 16 j3] /\ rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] /\
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] /\ rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 W0X0)] /\
  rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (nt (X + 1024)))] /\
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] /\ rw_cells rsegs m (X + 208) [CB 8 j4] /\
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] /\ rw_cells rsegs m (X + 224) [CB 32 j5] /\
  rw_cells rsegs m (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] /\ rw_cells rsegs m (X + 264) [CB 4 j6].
Proof.
  intros m X j0 j1 j2 j3 j4 j5 j6 h. unfold spill_cells.
  rewrite (urw_cons m X (X + 32)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 32) (X + 40)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 40) (X + 48)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 48) (X + 120)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 120) (X + 128)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 128) (X + 136)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 136) (X + 144)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 144) (X + 152)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 152) (X + 168)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 168) (X + 176)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 176) (X + 184)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 184) (X + 192)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 192) (X + 200)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 200) (X + 208)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 208) (X + 216)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 216) (X + 224)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 224) (X + 256)) by (cbn [csize]; lia).
  rewrite (urw_cons m (X + 256) (X + 264)) by (cbn [csize]; lia).
  tauto.
Qed.

Lemma uimg_free_res : forall D n lo len, pf_img_free D n -> 0 < n -> 0 < len ->
  In (lo, len) (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)) ->
  D + n <= lo \/ lo + len <= D.
Proof.
  intros D n lo len H Hn Hl Hin. apply in_map_iff in Hin. destruct Hin as [s [E Hs]].
  injection E as E1 E2.
  destruct (Z.leb_spec (D + n) lo) as [A|A]; [left; lia|].
  destruct (Z.leb_spec (lo + len) D) as [B|B]; [right; lia|].
  exfalso. apply (H (Z.max D lo - D) ltac:(lia) s Hs). rewrite E1, E2. lia.
Qed.

Ltac uresv_in := rewrite utj_resv; cbn [In]; repeat first [left; reflexivity | right].

Lemma uimg_free_out : forall D n, pf_img_free D n -> 0 < n -> D + n <= 0x10000 \/ 0x53000 <= D.
Proof.
  intros D n H Hn.
  pose proof (uimg_free_res D n 65536 8192 H Hn ltac:(lia) ltac:(uresv_in)).
  pose proof (uimg_free_res D n 73728 57344 H Hn ltac:(lia) ltac:(uresv_in)).
  pose proof (uimg_free_res D n 131072 4096 H Hn ltac:(lia) ltac:(uresv_in)).
  pose proof (uimg_free_res D n 135168 204800 H Hn ltac:(lia) ltac:(uresv_in)).
  lia.
Qed.

Ltac uout_all := intros x Hx; unfold uSER_W in *; cbn [outside]; repeat split; try exact I; lia.
Ltac urwt H MU WM := eapply urw_tr; [exact H | exact MU | exact WM | cbn [cells_size csize spill_cells]; uout_all].
Ltac ubt H MU := eapply ubytes_tr; [exact H | exact MU | rewrite ?length_le8; uout_all].

Theorem uslot_ser_chain_holds : U.Prog.reac_disco_table_json_c.reac_disco_table_json_contract -> strlen_contract ->
  user_J_spec -> user_P3_spec -> uslot_ser_chain.
Proof.
  intros TJC SLC SJ SP3. split; [exact uslot_R8_call|]. unfold uslot_ser_chain_B.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m canary
    X lo buf cap now n h i p T Lk Gt ob junk slk j0 j1 j2 j3 j4 j5 j6 jr jw sv
    Esp Ea0 Es2 Es5 Es8 Es10 Es11 HX0 HX16 HX1 Hnow Hcap Hb Hb8 Hbl HIF HSL RB BS LT TOK
    SP R136 R152 R160 R224 RLK RGT RT ROB RW RSV JTB BN GG GW FC MI TM ST HLO HI.
  unfold OFF_LOCK, OFF_GATE, OFF_TABLE, OFF_OUR, OFF_WORK, OFF_SAVE in *.
  change U.Prog.reac_disco_table_json_c.TJ_K with 6240 in HLO. unfold IMG_END in HI.
  assert (HJL : JSON_SCALAR_L = 0x205e0) by reflexivity. assert (LJS : Z.of_nat (length js_table) = 24) by reflexivity.
  assert (HBN : BN_TS = 0x205f8) by reflexivity. assert (LBN : Z.of_nat (length bn_table) = 24) by reflexivity.
  assert (HGG : GOT_GUARD = 0x206a0) by reflexivity. assert (HGW : GUARD = 0x51c90) by reflexivity.
  pose proof SP as SPc.
  apply uspill_iff in SPc as (P0 & P32 & P40 & P48 & P120 & P128 & P136 & P144 & P152 & P168 & P176 & P184 & P192 &
                              P200 & P208 & P216 & P224 & P256 & P264).
  destruct (user_split m X (X + 16) 16 16 32 j0 ltac:(lia) ltac:(lia) P0) as [Q0 Q16].
  destruct (user_split m (X + 224) (X + 232) 8 24 32 j5 ltac:(lia) ltac:(lia) P224) as [_ Q232].
  destruct (user_split m (X + 952) (X + 976) 24 1544 1568 jw ltac:(lia) ltac:(lia) RW) as [V952 V976r].
  destruct (user_split m (X + 976) (X + 1000) 24 1520 1544 _ ltac:(lia) ltac:(lia) V976r) as [V976 V1000r].
  destruct (user_split m (X + 1000) (X + 1024) 24 1496 1520 _ ltac:(lia) ltac:(lia) V1000r) as [V1000 V1024r].
  destruct (user_split m (X + 1024) (X + 1056) 32 1464 1496 _ ltac:(lia) ltac:(lia) V1024r) as [V1024 V1056r].
  destruct (user_split m (X + 1056) (X + 2352) 1296 168 1464 _ ltac:(lia) ltac:(lia) V1056r) as [V1056 V2352r].
  destruct (user_split m (X + 2352) (X + 2376) 24 144 168 _ ltac:(lia) ltac:(lia) V2352r) as [V2352 V2376].
  clear V976r V1000r V1024r V1056r V2352r.
  pose proof (user_cb_bytes _ _ _ _ RB) as JB. pose proof RB as RBw. apply user_cb in RBw as (LJ & _ & _).
  subst sp a0 s2 s5 s8 s10 s11.
  eapply evt_cut.
  { eapply (uslot_R8_ret TJC) with (X := X) (lo := lo) (buf := buf) (cap := cap) (now := now) (T := T) (junk := junk)
      (canary := canary);
      first [ reflexivity | eassumption | lia | (change U.Prog.reac_disco_table_json_c.TJ_K with 6240; lia)
            | (unfold IMG_END; lia) ]. }
  intros ms' (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 &
              F2 & fc2 & m2 & FC2 & FK2 & WM2 & MI2 & TM2 & ST2 & [(E2 & MU2) | (E2 & CL & MU2 & BT)]); subst ms'.
  - eapply evt_cut; [apply uslot_R14|]. intros ms' E. cbv beta in E. subst ms'.
    assert (MUc : munch (uSER_W lo X buf cap) m m2).
    { eapply munch_weaken; [|exact MU2]. unfold sub_fp, uSER_W; cbn [outside]; intros; intuition lia. }
    apply evt_done. do 21 eexists. exists F2, fc2, m2, j0, j4, j5, jw.
    split; [reflexivity|]. split; [exact FC2|]. split; [exact FK2|]. split; [exact MUc|]. split; [exact WM2|].
    split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
    split; [urwt SP MU2 WM2|]. split; [urwt R136 MU2 WM2|]. split; [urwt R152 MU2 WM2|].
    split; [urwt R160 MU2 WM2|]. split; [urwt R224 MU2 WM2|].
    split; [urwt RLK MU2 WM2|]. split; [urwt RGT MU2 WM2|]. split; [urwt RT MU2 WM2|]. split; [urwt ROB MU2 WM2|].
    split; [urwt RW MU2 WM2|]. urwt RSV MU2 WM2.
  - assert (LT1 : length (firstn (Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1))
                           (skipn (Z.to_nat (Z.of_nat (length (tj_text T now)) + 1)) junk))
                   = Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1)).
    { rewrite length_firstn, length_skipn, LJ. lia. }
    pose proof (ubytes_at_sub m buf junk (Z.of_nat (length (tj_text T now)) + 1)
                  (Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1)) JB ltac:(lia) ltac:(rewrite LJ; lia)) as TL.
    set (tl := firstn (Z.to_nat (cap - Z.of_nat (length (tj_text T now)) - 1))
                 (skipn (Z.to_nat (Z.of_nat (length (tj_text T now)) + 1)) junk)) in TL, LT1.
    pose proof (uimg_free_out buf cap HIF ltac:(lia)) as DIMG.
    assert (TL2 : bytes_at rsegs m2 (buf + Z.of_nat (length (tj_text T now)) + 1) tl).
    { replace (buf + Z.of_nat (length (tj_text T now)) + 1) with (buf + (Z.of_nat (length (tj_text T now)) + 1))
        by lia.
      eapply ubytes_tr; [exact TL | exact MU2 |]. rewrite LT1. uout_all. }
    assert (SL2 : bytes_at rsegs m2 (buf + cap) slk) by ubt BS MU2.
    assert (BSL : bytes_at rsegs m2 (buf + Z.of_nat (length (tj_text T now)) + 1) (tl ++ slk)).
    { apply bytes_at_app. split; [exact TL2|].
      replace (buf + Z.of_nat (length (tj_text T now)) + 1 + Z.of_nat (length tl)) with (buf + cap) by lia.
      exact SL2. }
    assert (ALN : (- (buf + Z.of_nat (length (tj_text T now)) + 1)) mod 8 <= Z.of_nat (length (tl ++ slk))).
    { rewrite length_app, Nat2Z.inj_add, LT1, Z2Nat.id by lia. Z.div_mod_to_equations. lia. }
    assert (JTB2 : bytes_at rsegs m2 JSON_SCALAR_L js_table) by ubt JTB MU2.
    assert (BN2 : bytes_at rsegs m2 BN_TS bn_table) by ubt BN MU2.
    assert (GG2 : bytes_at rsegs m2 GOT_GUARD (le8 (Z_to_bv 64 GUARD))) by ubt GG MU2.
    assert (GW2 : bytes_at rsegs m2 GUARD (le8 canary)) by ubt GW MU2.
    clear TL JB BS SL2 TL2 JTB BN GG GW.
    transport_after_call rsegs m m2 MU2 WM2.
    eapply evt_cut.
    { eapply (user_tail SLC SJ SP3) with (X := X) (lo := lo) (buf := buf) (cap := cap) (now := now) (T := T)
        (slack := tl ++ slk) (canary := canary);
        try first [ reflexivity | exact BSL | exact ALN | eassumption | lia
                  | (change U.Prog.reac_disco_table_json_c.TJ_K with 6240; lia)
                  | (unfold IMG_END; lia) | (rewrite length_app; lia) ]. }
    intros ms' (t05 & t15 & t25 & s05 & s15 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s45 & s55 & s65 & s75 & s95 &
                t35 & t45 & t55 & t65 & F5 & fc5 & m5 & j0' & j208' & j232' & jw' &
                E5 & FC5 & FK5 & MU5 & WM5 & MI5 & TM5 & ST5 & C0' & C208' & C232' & CW').
    subst ms'. unfold uW_TAIL in MU5.
    assert (MUc : munch (uSER_W lo X buf cap) m m5).
    { eapply munch_trans; [eapply munch_weaken; [|exact MU2] | eapply munch_weaken; [|exact MU5]];
        unfold sub_fp, uSER_W; cbn [outside]; intros; intuition lia. }
    pose proof (wmono_trans rsegs m m2 m5 WM2 WM5) as WMc.
    apply evt_done. do 21 eexists.
    exists F5, fc5, m5, (j0' ++ skipn 16 j0), j208', (le8 (Z_to_bv 64 now) ++ j232'), jw'.
    split; [reflexivity|]. split; [exact FC5|].
    split; [intros k Hk; rewrite FK5 by exact Hk; apply FK2; exact Hk|].
    split; [exact MUc|]. split; [exact WMc|]. split; [exact MI5|]. split; [exact TM5|]. split; [exact ST5|].
    split.
    { apply uspill_iff.
      split; [apply (user_join m5 X (X + 16) 16 16 32); [lia | lia | exact C0' | urwt Q16 MU5 WM5]|].
      split; [urwt P32 MU5 WM5|]. split; [urwt P40 MU5 WM5|]. split; [urwt P48 MU5 WM5|].
      split; [urwt P120 MU5 WM5|]. split; [urwt P128 MU5 WM5|]. split; [urwt P136 MU5 WM5|].
      split; [urwt P144 MU5 WM5|]. split; [urwt P152 MU5 WM5|]. split; [urwt P168 MU5 WM5|].
      split; [urwt P176 MU5 WM5|]. split; [urwt P184 MU5 WM5|]. split; [urwt P192 MU5 WM5|].
      split; [urwt P200 MU5 WM5|]. split; [exact C208'|]. split; [urwt P216 MU5 WM5|].
      split; [apply (user_join m5 (X + 224) (X + 232) 8 24 32);
              [lia | lia | apply user_c8; urwt R224 MU5 WM5 | exact C232']|].
      split; [urwt P256 MU5 WM5|]. urwt P264 MU5 WM5. }
    split; [urwt R136 MU5 WM5|]. split; [urwt R152 MU5 WM5|]. split; [urwt R160 MU5 WM5|].
    split; [urwt R224 MU5 WM5|]. split; [urwt RLK MU5 WM5|]. split; [urwt RGT MU5 WM5|].
    split; [urwt RT MU5 WM5|]. split; [urwt ROB MU5 WM5|]. split; [exact CW'|]. urwt RSV MU5 WM5.
Qed.

Theorem uslot_ser_chain_closed : U.Prog.reac_disco_table_json_c.reac_disco_table_json_contract -> strlen_contract ->
  json_scalar_contract -> jtok_is_contract -> reac_box_name_contract -> snprintf_stk_contract -> uslot_ser_chain.
Proof.
  intros TJC SLC JS JT BNC SNK.
  exact (uslot_ser_chain_holds TJC SLC (uslot_ser_J.uslot_ser_J JS JT) (uslot_ser_P.uslot_ser_P3 BNC SNK JT)).
Qed.
