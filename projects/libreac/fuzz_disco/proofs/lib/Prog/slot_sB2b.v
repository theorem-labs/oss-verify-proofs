From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_seg slot_preds slot_cells slot_sB1 slot_sLatch.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c disco_table_c disco_table hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import memcpy_c find_entry_c reac_hunt_observe_c check_sighting_c check_table_c reac_disco_classify_c reac_disco_classify_on_segment_c reac_disco_gate_should_push_c bcmp_c reac_disco_table_observe_c reac_frame_clean_len_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_lib slot_frame slot_step slot_hunt slot_classify slot_observe slot_known slot_newent.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_record slot_exit.
Import ListNotations.
Open Scope Z_scope.

Definition W_B2b (X h f len : Z) : list (Z * Z) :=
  [(LO X, X); (X + 40, X + 144); (X + 152, X + 168); (X + 184, X + 200); (X + 216, X + 232);
   (X + 236, X + 912); (X + 1024, X + 1048); (h, h + 480); (f, f + len)].

Ltac record_finish X d h pl regs0 i n now len f HXX HDD :=
  lazymatch goal with |- evt rsegs _ (MS ?R ?F _ ?fc None ?mm _) =>
    let HP := fresh "HP27" in
    assert (HP : P_R27 X d h pl regs0 i n now len f R mm) by
      (split; [eassumption|]; split; [eassumption|];
       split; [first [reflexivity | eassumption]|]; split; [first [reflexivity | eassumption]|];
       split; [first [reflexivity | eassumption]|]; split; [eassumption|]; split; [eassumption|];
       split; [eassumption|]; split; [eassumption|];
       do 8 (split; [first [reflexivity | eassumption]|]); hdr_close);
    eapply evt_mono; [exact (R27_ev X d h pl regs0 i n now len f HXX HDD R F fc mm HP)|];
    intros ms (? & -> & HPf); do 2 eexists; exists FREE_PC; do 2 eexists;
    split; [reflexivity|]; split; [eassumption|]; split; [unfold W_B2b, LO, SLOT_FRAME, SLOT_STACK; eassumption|];
    split; [eassumption|]; split; [reflexivity|]; exact HPf
  end.

Lemma nseg_interval : forall a n, 0 < n -> (forall i, 0 <= i < n -> nseg (a + i)) ->
  a + n <= IMG_LO \/ IMG_HI <= a.
Proof.
  intros a n Hn H. pose proof (H 0 ltac:(lia)) as H0. unfold nseg in *.
  destruct H0 as [Hl|Hr]; [|right; lia].
  destruct (Z_le_dec (a + n) IMG_LO); [left; assumption|].
  pose proof (H (IMG_LO - a) ltac:(lia)) as H1. unfold IMG_LO, IMG_HI in *; lia.
Qed.

Lemma seg_B2b : memcpy_contract -> find_entry_contract -> reac_hunt_observe_contract -> check_sighting_contract ->
  check_table_contract -> reac_disco_classify_contract -> reac_disco_classify_on_segment_contract ->
  reac_disco_gate_should_push_contract -> bcmp_contract -> reac_disco_table_observe_contract ->
  forall X d h pl regs0 i n now len k f ob, xok X -> dok X d pl -> h mod 16 = 0 ->
  (f + len <= h \/ h + 480 <= f) ->
  (d + Z.of_nat (length pl) <= f \/ f + len <= d) ->
  (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  seg_ev R17_RET (W_B2b X h f len)
    (fun R m => P_FR X d h pl regs0 i n now len k f ob R m /\ fenv X [(f, len); (h, 480)] m)
    (fun q R m => q = FREE_PC /\ P_FFREE X d h pl regs0 i f R m).
Proof.
  intros MC FEC HOC CSC CTC CC0 CC1 GSC BC OBC X d h pl regs0 i n now len k f ob HX HD Hh16 HFH HFD HHD
    fx' regs m0 Hfc HI
    ((Hn & Hlen & Hl16 & Hk & G10 & G19 & G21 & G22 & G23 & G20 & G25 & C200n & C216op & [jf RF] &
      Hi & Hnow & G2 & G3 & G4 & G8 & G9 & G18 & G24 & G27 & HM) & (STK & HBK)).
  pose proof HX as HXX. pose proof HD as HDD.
  destruct (HBK f len (or_introl eq_refl)) as (Hf0 & Hf1 & Hfns & _).
  destruct (HBK h 480 (or_intror (or_introl eq_refl))) as (Hh0 & Hh1 & Hhns & _). clear HBK.
  pose proof (nseg_interval h 480 ltac:(lia) Hhns) as Hhimg.
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI, IMG_LO in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  pose proof (stk_sub m0 _ _ (X + 2592 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST. clear STK.
  hdr_open HM.
  destruct (rest_bytes m0 d pl n Hn BD) as [BR LR].
  assert (BRb : bytes_at rsegs m0 (d + (Z.of_nat (length pl) - n)) (firstn (Z.to_nat len) (rest_of pl n))).
  { rewrite <- (firstn_skipn (Z.to_nat len) (rest_of pl n)) in BR. apply bytes_at_app in BR. exact (proj1 BR). }
  assert (LRb : Z.of_nat (length (firstn (Z.to_nat len) (rest_of pl n))) = len) by (rewrite length_firstn; lia).
  assert (LU : length (our_of pl) = 6%nat) by (unfold our_of; rewrite map_length, length_seq; reflexivity).
  pose proof (munch_refl (W_B2b X h f len) m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  unfold W_B2b, LO, SLOT_FRAME, SLOT_STACK in MU.
  unfold rmk. eapply evt_cut.
  { eapply slot_R17_copy with (X := X) (f := f) (len := len) (body := d + (Z.of_nat (length pl) - n))
      (k := k) (Rb := firstn (Z.to_nat len) (rest_of pl n)); first [eassumption | lia]. }
  intros ms (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 &
    m1 & -> & MU1 & WM1 & MI1 & RF1 & C184b & C224f).
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  assert (BU : bytes_at rsegs m1 (X + 914) (our_of pl)) by (eapply rw_bytes; exact C914).
  destruct (Z.eq_dec k 2) as [->|Hk2].
  - change (r17_exit 2) with R18.
    assert (HAM : bytes_at rsegs m1 A_M (le8 (Z_to_bv 64 KM))).
    { apply R15_ro; [exact MI1|vm_compute; reflexivity]. }
    assert (HAT : bytes_at rsegs m1 A_T (le8 (Z_to_bv 64 KT))).
    { apply R15_ro; [exact MI1|vm_compute; reflexivity]. }
    eapply evt_cut.
    { eapply (slot_R18 FEC HOC CSC CTC) with (X := X) (lo := X + 2592 - 65536) (f := f) (len := len)
        (h := h) (i := i) (now := now) (Rb := firstn (Z.to_nat len) (rest_of pl n)) (H := Hunt) (U := our_of pl);
        first [reflexivity | eassumption | unfold MAX_OPS in *; lia | unfold classify_core_c.disj; lia | Z.div_mod_to_equations; lia]. }
    intros ms (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & s52 & t32 & t42 & t52 & t62 &
      m2 & Hunt2 & Sight2 & -> & MU2 & WM2 & MI2 & ST2 & RF2 & CH2 & HOK2 & OUR2 & CS2 & BU2).
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    record_finish X d h pl regs0 i n now len f HXX HDD.
  - assert (HK01 : k = 0 \/ k = 1) by lia.
    eapply evt_cut.
    { eapply (slot_R19_R21 CC0 CC1 CSC GSC BC) with (X := X) (lo := X + 2592 - 65536) (f := f) (len := len)
        (rem := n) (i := i) (now := now) (h := h) (k := k) (ob := ob)
        (Rb := firstn (Z.to_nat len) (rest_of pl n)) (U := our_of pl);
        first [reflexivity | eassumption | unfold MAX_OPS in *; lia]. }
    intros ms (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & s52 & s62 & s92 & s102 &
      t32 & t42 & t52 & t62 & m2 & tgt & S2 & Gt2 & Lk2 & j1522 & j1602 & j1922 & -> &
      MU2 & WM2 & MI2 & ST2 & C1522 & C1602 & C1922 & CLK2 & CGT2 & GOK2 & CS2 & TARGET).
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    destruct TARGET as [->|(-> & LS2 & SS1 & SS2 & EJ160 & EJ192)].
    + record_finish X d h pl regs0 i n now len f HXX HDD.
    + subst j1602 j1922.
      pose proof TOK as (T1 & T2 & T3 & T4).
      assert (LT : length T = 400%nat) by exact (proj1 (proj1 (proj1 CT))).
      eapply evt_cut.
      { eapply (slot_R22 FEC) with (X := X) (lo := X + 2592 - 65536) (T := T) (G := S2);
          first [reflexivity | eassumption | unfold FIND_ENTRY_K; lia]. }
      intros ms (ra3 & t03 & t13 & t23 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & t33 & t43 & t53 & t63 &
        m3 & r & jold & -> & MU3 & WM3 & MI3 & ST3 & FR & OLD3 & C1523 & CT3 & CS3).
      transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3.
      eapply evt_cut.
      { eapply (slot_R23 OBC CTC FEC) with (X := X) (lo := X + 2592 - 65536) (now := now)
          (op := bv_unsigned ob) (h := h) (i := i) (r := r) (T := T) (G := S2) (j := jold);
          first [reflexivity | eassumption | pose proof (byte_range ob); unfold CHECK_TABLE_K; lia]. }
      intros ms (ra4 & t04 & t14 & t24 & a04 & a14 & a24 & a34 & a44 & a54 & a64 & a74 & t34 & t44 & t54 & t64 &
        m4 & Tnew & ret & -> & MU4 & WM4 & MI4 & ST4 & OLD4 & C1444 & C1524 & C1604 & C2164 & CT4 & CS4 &
        OM & TN1 & TN2 & TN3 & TN4).
      transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4.
      assert (TNOK : table_ok Tnew) by exact (conj TN1 (conj TN2 (conj TN3 TN4))).
      pose proof (own_bit_range (bv_unsigned ob)) as HOW.
      destruct (Z.ltb_spec r 0) as [Hr|Hr].
      * pose proof (unknown_arm T S2 (own_bit (bv_unsigned ob)) now Tnew ret r FR Hr OM) as ARM.
        eapply evt_cut.
        { eapply (slot_R25_R26 BC) with (X := X) (now := now) (ow := own_bit (bv_unsigned ob)) (rem := n)
            (ret := ret) (T := T) (G := S2) (T' := Tnew);
            first [reflexivity | eassumption | lia]. }
        intros ms (ra5 & t05 & t15 & t25 & a05 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s55 & s105 & t35 & t45 & t55 & t65 &
          m5 & -> & MU5 & WM5 & MI5 & C1925 & CT5 & CS5).
        transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5.
        apply rw_flat in OLD4. change (cells_size (old_cells T r jold)) with 104%nat in OLD4.
        record_finish X d h pl regs0 i n now len f HXX HDD.
      * eapply evt_cut.
        { eapply (slot_R24 BC) with (X := X) (now := now) (ow := own_bit (bv_unsigned ob)) (r := r) (rem := n)
            (i := i) (ret := ret) (T := T) (G := S2) (T' := Tnew) (j := jold);
            first [reflexivity | eassumption | unfold MAX_OPS in *; lia]. }
        intros ms (ra5 & t05 & t15 & t25 & a05 & a15 & a25 & a35 & a45 & a55 & a65 & a75 & s55 & s65 & s95 & s105 &
          t35 & t45 & t55 & t65 & j2165 & m5 & j405 & -> & MU5 & WM5 & MI5 & C405 & C1525 & C1605 & C1925 & C2005 & C2165 & CT5 & CS5).
        transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5.
        record_finish X d h pl regs0 i n now len f HXX HDD.
Qed.
