From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_seg uslot_preds uslot_cells.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import memcpy_c find_entry_c role_of_c reac_hunt_observe_c check_sighting_c check_table_c classify_core_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_classify_c reac_disco_classify_on_segment_c reac_disco_gate_should_push_c bcmp_c reac_disco_table_observe_c reac_frame_clean_len_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_lib uslot_exit uslot_frame uslot_step uslot_hunt uslot_classify uslot_observe uslot_known uslot_newent.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_record uslot_sB1.
Import ListNotations.
Open Scope Z_scope.

Definition W_B2b (X h f len : Z) : list (Z * Z) :=
  [(LO X, X); (X + 48, X + 120); (X + 136, X + 144); (X + 152, X + 160); (X + 208, X + 216);
   (X + 232, X + 256); (X + 268, X + 944); (X + 1056, X + 1080); (h, h + 480); (f, f + len)].

Lemma j48_split : forall m X, junkb m (X + 48) 72 ->
  exists a b, rw_cells rsegs m (X + 48) [CB 8 a] /\ rw_cells rsegs m (X + 56) [CB 64 b].
Proof.
  intros m X [bs H]. exists (firstn 8 (skipn 0 bs)), (firstn 64 (skipn 8 bs)). split.
  - pose proof (rw_cb_sub m (X + 48) 72 bs 0 8 ltac:(lia) H) as H1.
    replace (X + 48 + Z.of_nat 0) with (X + 48) in H1 by lia. exact H1.
  - pose proof (rw_cb_sub m (X + 48) 72 bs 8 64 ltac:(lia) H) as H1.
    replace (X + 48 + Z.of_nat 8) with (X + 56) in H1 by lia. exact H1.
Qed.

Lemma j48_join : forall m X a cs, rw_cells rsegs m (X + 48) [CB 8 a] -> rw_cells rsegs m (X + 56) cs ->
  cells_size cs = 64%nat -> junkb m (X + 48) 72.
Proof.
  intros m X a cs H1 H2 Hs.
  pose proof (rw_join m (X + 48) (X + 56) [CB 8 a] cs ltac:(cbn [cells_size csize]; lia) H1 H2) as H.
  apply rw_flat in H. cbn [app cells_size csize] in H. rewrite Hs in H. eexists. exact H.
Qed.

Lemma j48_of : forall m X c48 c56 c64 cs, rw_cells rsegs m (X + 48) [c48] -> rw_cells rsegs m (X + 56) [c56] ->
  rw_cells rsegs m (X + 64) [c64] -> rw_cells rsegs m (X + 72) cs ->
  csize c48 = 8%nat -> csize c56 = 8%nat -> csize c64 = 8%nat -> cells_size cs = 48%nat -> junkb m (X + 48) 72.
Proof.
  intros m X c48 c56 c64 cs H48 H56 H64 H72 E48 E56 E64 E72.
  assert (J64 : rw_cells rsegs m (X + 64) ([c64] ++ cs))
    by (apply (rw_join m (X + 64) (X + 72) [c64] cs); [cbn [cells_size]; rewrite E64; lia | exact H64 | exact H72]).
  assert (J56 : rw_cells rsegs m (X + 56) ([c56] ++ [c64] ++ cs))
    by (apply (rw_join m (X + 56) (X + 64) [c56] ([c64] ++ cs)); [cbn [cells_size]; rewrite E56; lia | exact H56 | exact J64]).
  assert (J48 : rw_cells rsegs m (X + 48) ([c48] ++ [c56] ++ [c64] ++ cs))
    by (apply (rw_join m (X + 48) (X + 56) [c48] ([c56] ++ [c64] ++ cs)); [cbn [cells_size]; rewrite E48; lia | exact H48 | exact J56]).
  apply rw_flat in J48. cbn [app cells_size] in J48. rewrite E48, E56, E64, E72 in J48. eexists. exact J48.
Qed.

Ltac record_finish X d h pl regs0 i n now len f HXX HDD :=
  lazymatch goal with |- evt rsegs _ (MS ?R ?F _ ?fc None ?mm _) =>
    let HP := fresh "HP27" in
    assert (HP : P_R27 X d h pl regs0 i n now len f R mm) by
      (split; [eassumption|]; split; [eassumption|];
       split; [first [reflexivity | eassumption]|]; split; [first [reflexivity | eassumption]|];
       split; [eassumption|]; split; [eassumption|];
       split; [eassumption|]; split; [eassumption|];
       do 6 (split; [first [reflexivity | eassumption]|]);
       split; [eassumption|]; split; [eassumption|]; hdr_close);
    eapply evt_mono; [exact (R27_ev X d h pl regs0 i n now len f HXX HDD R F fc mm HP)|];
    intros ms (? & -> & HPf); do 2 eexists; exists FREE_PC; do 2 eexists;
    split; [reflexivity|]; split; [eassumption|]; split; [unfold W_B2b, LO, SLOT_FRAME, SLOT_STACK; eassumption|];
    split; [eassumption|]; split; [reflexivity|]; exact HPf
  end.

Lemma seg_B2b : memcpy_contract -> find_entry_contract -> reac_hunt_observe_contract -> check_sighting_contract ->
  check_table_contract -> reac_disco_classify_contract -> reac_disco_classify_on_segment_contract ->
  reac_disco_gate_should_push_contract -> bcmp_contract -> reac_disco_table_observe_contract -> role_of_contract ->
  forall X d h pl regs0 i n now len k f ob, xok X -> dok X d pl -> h mod 16 = 0 ->
  (f + len <= h \/ h + 480 <= f) ->
  (d + Z.of_nat (length pl) <= f \/ f + len <= d) ->
  (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  seg_ev R17_RET (W_B2b X h f len)
    (fun R m => P_FR X d h pl regs0 i n now len k f ob R m /\ fenv X [(f, len); (h, 480)] m)
    (fun q R m => q = FREE_PC /\ P_FFREE X d h pl regs0 i f R m).
Proof.
  intros MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC ROC X d h pl regs0 i n now len k f ob HX HD Hh16 HFH HFD HHD
    fx' regs m0 Hfc HI
    ((Hn & Hlen & Hl16 & Hk & G10 & G19 & G20 & G21 & G22 & G8 & G25 & G9 & G27 & [jf RF] &
      Hi & Hnow & G2 & G3 & G4 & G18 & G24 & G26 & Ci & Cn & HM) & (STK & HBK)).
  pose proof HX as HXX. pose proof HD as HDD.
  destruct (HBK f len (or_introl eq_refl)) as (Hf0 & Hf1 & _).
  destruct (HBK h 480 (or_intror (or_introl eq_refl))) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI, IMG_LO in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  pose proof (stk_sub m0 _ _ (X + 2624 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST. clear STK.
  hdr_open HM.
  destruct (rest_bytes m0 d pl n Hn BD) as [BR LR].
  assert (BRb : bytes_at rsegs m0 (d + (Z.of_nat (length pl) - n)) (firstn (Z.to_nat len) (rest_of pl n))).
  { rewrite <- (firstn_skipn (Z.to_nat len) (rest_of pl n)) in BR. apply bytes_at_app in BR. exact (proj1 BR). }
  assert (LRb : Z.of_nat (length (firstn (Z.to_nat len) (rest_of pl n))) = len) by (rewrite length_firstn; lia).
  assert (LU : length (our_of pl) = 6%nat) by (unfold our_of; rewrite length_map, length_seq; reflexivity).
  assert (H8 : h mod 8 = 0) by (clear - Hh16; Z.div_mod_to_equations; lia).
  assert (HDJ : 0 < len -> disj f len h 480) by (intros _; unfold disj; lia).
  pose proof (munch_refl (W_B2b X h f len) m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  unfold W_B2b, LO, SLOT_FRAME, SLOT_STACK in MU.
  unfold rmk. eapply evt_cut.
  { eapply uslot_R17_copy with (X := X) (f := f) (len := len) (body := d + (Z.of_nat (length pl) - n))
      (k := k) (Rb := firstn (Z.to_nat len) (rest_of pl n)); first [eassumption | lia]. }
  intros ms (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 &
    m1 & -> & MU1 & WM1 & MI1 & RF1 & C152b & C248f).
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  assert (BU : bytes_at rsegs m1 (X + 946) (our_of pl)) by (eapply rw_bytes; exact C946).
  destruct (Z.eq_dec k 2) as [->|Hk2].
  - change (r17_exit 2) with R18.
    assert (HAM : bytes_at rsegs m1 A_M (le8 (Z_to_bv 64 KM))).
    { apply R15_ro; [exact MI1|vm_compute; reflexivity]. }
    assert (HAT : bytes_at rsegs m1 A_T (le8 (Z_to_bv 64 KT))).
    { apply R15_ro; [exact MI1|vm_compute; reflexivity]. }
    eapply evt_cut.
    { eapply (uslot_R18 ROC HOC CSC CTC) with (X := X) (lo := X + 2624 - 65536) (f := f) (len := len)
        (h := h) (now := now) (Rb := firstn (Z.to_nat len) (rest_of pl n)) (H := Hunt) (OB := j1056) (U := our_of pl);
        first [reflexivity | eassumption | lia | unfold REAC_HUNT_OBSERVE_K; lia]. }
    intros ms (ra2 & t02 & t12 & t22 & s02 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & s52 & t32 & t42 & t52 & t62 &
      m2 & Hunt2 & S2 & -> & MU2 & WM2 & MI2 & ST2 & RF2 & CH2 & HOK2 & OUR2 & CS2 & BU2).
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    record_finish X d h pl regs0 i n now len f HXX HDD.
  - assert (HK01 : k = 0 \/ k = 1) by lia.
    eapply evt_cut.
    { eapply (uslot_R19_R21 CC0 CC1 CSC GSC BC) with (X := X) (lo := X + 2624 - 65536) (f := f) (len := len)
        (rem := n) (now := now) (k := k) (ob := ob) (Rb := firstn (Z.to_nat len) (rest_of pl n)) (U := our_of pl)
        (OB := j1056) (G := Gt) (Lb := Lk) (j208 := j208) (j232 := j232);
        first [reflexivity | eassumption | lia | unfold CLASSIFY_CORE_K; lia]. }
    intros ms (ra2 & t02 & t12 & t22 & s02 & s12 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & s52 & s62 & s72 & s112 &
      t32 & t42 & t52 & t62 & m2 & tgt & S2 & Gt2 & Lk2 & j2082 & j2322 & -> &
      MU2 & WM2 & MI2 & ST2 & C2082 & C2322 & CLK2 & CGT2 & GOK2 & CS2 & TARGET).
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    destruct TARGET as [->|(-> & LS2 & SS1 & SS2 & EJ208 & EJ232)].
    + record_finish X d h pl regs0 i n now len f HXX HDD.
    + subst j2082 j2322.
      pose proof TOK as (T1 & T2 & T3 & T4).
      assert (LT : length T = 400%nat) by exact (proj1 (proj1 (proj1 CT))).
      destruct (j48_split m2 X (ex_intro _ j48 C48)) as (j48a & j56 & C48a & C56). clear C48.
      eapply evt_cut.
      { eapply (uslot_R22 FEC) with (X := X) (lo := X + 2624 - 65536) (T := T) (G := S2);
          first [reflexivity | eassumption | lia | unfold FIND_ENTRY_K; lia]. }
      intros ms (ra3 & t03 & t13 & t23 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & t33 & t43 & t53 & t63 &
        m3 & r & -> & MU3 & WM3 & MI3 & ST3 & FR & OLD3 & C1363 & C2003 & C2403 & CT3 & CS3).
      transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3.
      pose proof (rw_flat m3 (X + 56) (old_cells T r) OLD3) as OLDf.
      change (cells_size (old_cells T r)) with 64%nat in OLDf. clear OLD3.
      eapply evt_cut.
      { eapply (uslot_R23 OBC CTC ROC) with (X := X) (lo := X + 2624 - 65536) (now := now)
          (op := bv_unsigned ob) (r := r) (T := T) (G := S2);
          first [reflexivity | eassumption | pose proof (byte_range ob); lia |
                 unfold REAC_DISCO_TABLE_OBSERVE_K; lia]. }
      intros ms (ra4 & t04 & t14 & t24 & s04 & s14 & a04 & a14 & a24 & a34 & a44 & a54 & a64 & a74 & t34 & t44 & t54 & t64 &
        m4 & Tnew & ret & -> & MU4 & WM4 & MI4 & ST4 & C2244 & C2404 & CT4 & CS4 & OM & TN1 & TN2 & TN3 & TN4).
      transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4.
      assert (OLD4 : rw_cells rsegs m4 (X + 56) (old_cells T r)) by (apply rw_unflat; [cbn; tauto | exact OLDf]).
      assert (TNOK : table_ok Tnew) by exact (conj TN1 (conj TN2 (conj TN3 TN4))).
      pose proof (own_bit_range (bv_unsigned ob)) as HOW.
      destruct (Z.ltb_spec r 0) as [Hr|Hr].
      * pose proof (unknown_arm T S2 (own_bit (bv_unsigned ob)) now Tnew ret r FR Hr OM) as ARM.
        eapply evt_cut.
        { eapply (uslot_R25_R26 BC) with (X := X) (now := now) (ow := own_bit (bv_unsigned ob))
            (ret := ret) (T := T) (G := S2) (T' := Tnew);
            first [reflexivity | eassumption | lia]. }
        intros ms (ra5 & t05 & t15 & t25 & a05 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s55 & s75 & t35 & t45 & t55 & t65 &
          m5 & -> & MU5 & WM5 & MI5 & CT5 & CS5).
        transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5.
        pose proof (j48_join m5 X j48a _ C48a OLDf eq_refl) as J48.
        record_finish X d h pl regs0 i n now len f HXX HDD.
      * clear OLDf. pose proof OLD4 as OLDs. unfold old_cells in OLDs.
        destruct (rw_cons_at m4 _ (X + 64) _ _ OLDs ltac:(cbn [csize]; lia)) as [O56 O64r].
        destruct (rw_cons_at m4 _ (X + 72) _ _ O64r ltac:(cbn [csize]; lia)) as [O64 O72].
        clear OLDs O64r O64.
        pose proof (rw_c8_cb m4 (X + 208) _ C2082) as C208b.
        eapply evt_cut.
        { eapply (uslot_R24 BC) with (X := X) (now := now) (ow := own_bit (bv_unsigned ob)) (r := r) (rem := n)
            (ret := ret) (T := T) (G := S2) (T' := Tnew) (j48 := j48a) (j208 := le8 (Z_to_bv 64 (bv_unsigned ob)));
            first [reflexivity | eassumption | lia]. }
        intros ms (ra5 & t05 & t15 & t25 & s05 & s15 & a05 & a15 & a25 & a35 & a45 & a55 & a65 & a75 &
          s55 & s65 & s75 & s95 & s115 & t35 & t45 & t55 & t65 & w48 & w64 & w208 &
          m5 & -> & MU5 & WM5 & MI5 & C485 & C645 & C2085 & CT5 & CS5).
        transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5.
        pose proof (j48_of m5 X _ _ _ _ C485 O56 C645 O72 eq_refl eq_refl eq_refl eq_refl) as J48.
        record_finish X d h pl regs0 i n now len f HXX HDD.
Qed.
