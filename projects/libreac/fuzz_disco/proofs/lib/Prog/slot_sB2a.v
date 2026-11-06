From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_seg slot_preds slot_cells slot_sB1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c disco_table_c disco_table hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c reac_box_name_c json_scalar_c reac_disco_table_json_c slot_ser_defs slot_ser_iface slot_ser slot_ser_chain.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_sB3a.
Import ListNotations.
Open Scope Z_scope.

Definition ser_data (canary : word) (m : word -> option byte) : Prop :=
  bytes_at rsegs m JSON_SCALAR_L js_table /\ bytes_at rsegs m BN_TS bn_table /\
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ bytes_at rsegs m GUARD (le8 canary).

Definition P_SR (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now buf cap : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 2 <= cap <= 1280 /\
  getr R 10 = Z_to_bv 64 buf /\ getr R 21 = Z_to_bv 64 cap /\
  getr R 23 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\
  junkb m buf (Z.to_nat cap) /\ rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 n)] /\
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] /\ P_BASE X d h pl regs0 i now R m.

Definition P_SFREE (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now buf : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 1 = Z_to_bv 64 SER_FREE_RET /\ getr R 10 = Z_to_bv 64 buf /\ P_R15 X d h pl regs0 i n now R m.

Definition ser_extra (X buf cap : Z) (m : word -> option byte) : Prop :=
  exists slk canary, buf + cap + Z.of_nat (length slk) <= LO X /\ (- cap) mod 8 <= Z.of_nat (length slk) /\
    bytes_at rsegs m (buf + cap) slk /\ ser_data canary m.

Lemma seg_B2a : ser_chain_B -> forall X d h pl regs0 i n now buf cap,
  xok X -> dok X d pl -> 0 < buf -> buf mod 8 = 0 -> pf_img_free buf cap ->
  (buf + cap <= h \/ h + 480 <= buf) ->
  (d + Z.of_nat (length pl) <= buf \/ buf + cap <= d) ->
  seg_ev SER_RET (SER_W (LO X) X buf cap)
    (fun R m => P_SR X d h pl regs0 i n now buf cap R m /\ ser_extra X buf cap m /\ fenv X [(h, 480)] m)
    (fun q R m => q = SER_FREE /\ P_SFREE X d h pl regs0 i n now buf R m).
Proof.
  intros SERB X d h pl regs0 i n now buf cap HX HD Hb0 Hb8 HIF HBH HBD fx' regs m0 Hf HI
    ((Hn & Hcap & G10 & G21 & G23 & [jb RB] & C152n & C200n & Hi & Hnow & G2 & G3 & G4 & G8 & G9 & G18 & G24 & G27 & HM) &
      (slk & canary & Hbsl & Hsl & BSL & JS & BN & GG & GW) & (STK & HBK)).
  destruct (HBK h 480 (or_introl eq_refl)) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI. pose proof (MemNorm.mem_inv_cj_task rsegs m0 HI) as TM.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  pose proof (stk_sub m0 _ _ (X + 2592 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST. clear STK.
  hdr_open HM.
  assert (SP : rw_cells rsegs m0 X
    (spill_cells j0 j40 (le8 j152 ++ le8 j160) (le8 j184 ++ le8 j192 ++ le8 j200)
      (le8 j216 ++ le8 j224 ++ j232) h)).
  { apply spill_iff.
    split; [exact C0|]. split; [exact C24|]. split; [exact C32|]. split; [exact C40|]. split; [exact C144|].
    split.
    { eapply ser_join with (A2 := X + 160) (n1 := 8%nat) (n2 := 8%nat);
        [lia|reflexivity|apply ser_c8; exact C152|apply ser_c8; exact C160]. }
    split; [exact C168|]. split; [exact C176|]. split.
    { eapply ser_join with (A2 := X + 192) (n1 := 8%nat) (n2 := 16%nat);
        [lia|reflexivity|apply ser_c8; exact C184|].
      eapply ser_join with (A2 := X + 200) (n1 := 8%nat) (n2 := 8%nat);
        [lia|reflexivity|apply ser_c8; exact C192|apply ser_c8; exact C200]. }
    split; [exact C208|].
    eapply ser_join with (A2 := X + 224) (n1 := 8%nat) (n2 := 12%nat);
      [lia|reflexivity|apply ser_c8; exact C216|].
    eapply ser_join with (A2 := X + 232) (n1 := 8%nat) (n2 := 4%nat);
      [lia|reflexivity|apply ser_c8; exact C224|exact C232]. }
  assert (RW : rw_cells rsegs m0 (X + 920) [CB 1568 (j920 ++ j1024 ++ j1048)]).
  { eapply ser_join with (A2 := X + 1024) (n1 := 104%nat) (n2 := 1464%nat);
      [lia|reflexivity|exact C920|].
    eapply ser_join with (A2 := X + 1048) (n1 := 24%nat) (n2 := 1440%nat);
      [lia|reflexivity|exact C1024|exact C1048]. }
  assert (ROB : rw_cells rsegs m0 (X + 912) [CB 2 j912; CB 6 (our_of pl)]).
  { change [CB 2 j912; CB 6 (our_of pl)] with ([CB 2 j912] ++ [CB 6 (our_of pl)]).
    eapply rw_join with (B := X + 914); [cbn [cells_size csize]; lia|exact C912|exact C914]. }
  assert (LT : length T = 400%nat) by exact (proj1 (proj1 (proj1 CT))).
  pose proof (munch_refl (SER_W (X + 2592 - 65536) X buf cap) m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  unfold rmk. eapply evt_mono.
  { eapply SERB with (canary := canary) (X := X) (lo := X + 2592 - 65536) (buf := buf) (cap := cap)
      (now := now) (n := n) (h := h) (i := i) (p := d + (Z.of_nat (length pl) - n))
      (T := T) (Lk := Lk) (Gt := Gt) (ob := our_of pl) (junk := jb) (slk := slk) (j0 := j0) (j1 := j40)
      (j2 := le8 j152 ++ le8 j160) (j3 := le8 j184 ++ le8 j192 ++ le8 j200)
      (j4 := le8 j216 ++ le8 j224 ++ j232) (j5 := j912) (jw := j920 ++ j1024 ++ j1048) (sv := saved_of regs0);
      first [eassumption | exact Hf | change TJ_K with 6224; lia | unfold IMG_END; lia]. }
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s5' & s6' & s9' & s10' &
    t3' & t4' & t5' & t6' & F' & fc' & m1 & j0' & j2' & j3' & j4' & jw' & -> & HF & FK & MU1 & WM1 & MI1 & TM1 & ST1 &
    SP' & C152' & C200' & CLK' & CGT' & CT' & ROB' & RW' & CSV').
  unfold SER_W, OFF_LOCK, OFF_GATE, OFF_TABLE, OFF_OUR, OFF_WORK, OFF_SAVE in *.
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  apply spill_split in SP'.
  destruct SP' as (S0 & S24 & S32 & S40 & S144 & S152 & S160 & S168 & S176 & S184 & S192 & S200 & S208 & S216 & S224 & S232).
  destruct (junkb_sub m1 (X + 920) (X + 920) 1568 jw' 0 104 RW' ltac:(lia) ltac:(cbn; lia)) as [j920' S920].
  destruct (junkb_sub m1 (X + 920) (X + 1024) 1568 jw' 104 24 RW' ltac:(lia) ltac:(cbn; lia)) as [j1024' S1024].
  destruct (junkb_sub m1 (X + 920) (X + 1048) 1568 jw' 128 1440 RW' ltac:(lia) ltac:(cbn; lia)) as [j1048' S1048].
  do 2 eexists. exists SER_FREE. do 2 eexists.
  split; [reflexivity|]. split; [exact HF|]. split; [unfold SER_W, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
  split; [exact WM|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hn|]. split; [exact G23|]. split; [exact C152'|].
  split; [exact Hi|]. split; [exact Hnow|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G24|]. split; [exact G27|].
  hdr_close.
Qed.
