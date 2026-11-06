From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_seg uslot_preds uslot_cells.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c hunt_c uslot_sB3a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import printf_facts_c snprintf_c reac_box_name_c json_scalar_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_defs uslot_ser_iface.
Import ListNotations.
Open Scope Z_scope.

Definition ser_data (canary : word) (m : word -> option byte) : Prop :=
  bytes_at rsegs m JSON_SCALAR_L js_table /\ bytes_at rsegs m BN_TS bn_table /\
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ bytes_at rsegs m GUARD (le8 canary).

Definition P_SR (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now buf cap : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ 2 <= cap <= 1280 /\
  getr R 10 = Z_to_bv 64 buf /\ getr R 21 = Z_to_bv 64 cap /\ getr R 27 = Z_to_bv 64 1 /\
  junkb m buf (Z.to_nat cap) /\ rw_cells rsegs m (X + 136) [C8 (Z_to_bv 64 n)] /\
  rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 (d + (Z.of_nat (length pl) - n)))] /\
  P_BASE X d h pl regs0 i now R m.

Definition P_SFREE (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now buf : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 1 = Z_to_bv 64 uSER_FREE_RET /\ getr R 10 = Z_to_bv 64 buf /\ P_R15 X d h pl regs0 i n now R m.

Definition ser_extra (X buf cap : Z) (m : word -> option byte) : Prop :=
  exists slk canary, buf + cap + Z.of_nat (length slk) <= LO X /\ (- cap) mod 8 <= Z.of_nat (length slk) /\
    bytes_at rsegs m (buf + cap) slk /\ ser_data canary m.

Lemma u2a_cons : forall m A B c cs, B = A + Z.of_nat (csize c) -> rw_cells rsegs m A [c] -> rw_cells rsegs m B cs ->
  rw_cells rsegs m A (c :: cs).
Proof.
  intros m A B c cs E H1 H2.
  exact (rw_join m A B [c] cs ltac:(cbn [cells_size]; lia) H1 H2).
Qed.

Lemma u2a_cb : forall m A B n1 n2 a b, B = A + Z.of_nat n1 -> rw_cells rsegs m A [CB n1 a] -> rw_cells rsegs m B [CB n2 b] ->
  rw_cells rsegs m A [CB (n1 + n2) (a ++ b)].
Proof.
  intros m A B n1 n2 a b E H1 H2.
  pose proof (rw_join m A B [CB n1 a] [CB n2 b] ltac:(cbn [cells_size csize]; lia) H1 H2) as H.
  apply rw_flat in H. cbn [app cells_size cells_bytes csize cbytes] in H. rewrite app_nil_r, Nat.add_0_r in H. exact H.
Qed.

Lemma spill_join : forall m X j0 j1 j2 j3 j4 j5 j6 h,
  rw_cells rsegs m X [CB 32 j0] -> rw_cells rsegs m (X + 32) [C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 INV9)] -> rw_cells rsegs m (X + 48) [CB 72 j1] ->
  rw_cells rsegs m (X + 120) [C8 (Z_to_bv 64 STALE1)] -> rw_cells rsegs m (X + 128) [C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 136) [CB 8 j2] -> rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 MS_NS)] ->
  rw_cells rsegs m (X + 152) [CB 16 j3] -> rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 h)] ->
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] -> rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 W0X0)] ->
  rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (nt (X + 1024)))] ->
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] ->
  rw_cells rsegs m (X + 208) [CB 8 j4] -> rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] ->
  rw_cells rsegs m (X + 224) [CB 32 j5] -> rw_cells rsegs m (X + 256) [C8 (Z_to_bv 64 (nt (X + 280)))] ->
  rw_cells rsegs m (X + 264) [CB 4 j6] ->
  rw_cells rsegs m X (spill_cells j0 j1 j2 j3 j4 j5 j6 h X).
Proof.
  intros m X j0 j1 j2 j3 j4 j5 j6 h H0 H32 H40 H48 H120 H128 H136 H144 H152 H168 H176 H184 H192 H200 H208 H216
    H224 H256 H264.
  unfold spill_cells.
  apply (u2a_cons m X (X + 32)); [cbn [csize]; lia | exact H0 |].
  apply (u2a_cons m (X + 32) (X + 40)); [cbn [csize]; lia | exact H32 |].
  apply (u2a_cons m (X + 40) (X + 48)); [cbn [csize]; lia | exact H40 |].
  apply (u2a_cons m (X + 48) (X + 120)); [cbn [csize]; lia | exact H48 |].
  apply (u2a_cons m (X + 120) (X + 128)); [cbn [csize]; lia | exact H120 |].
  apply (u2a_cons m (X + 128) (X + 136)); [cbn [csize]; lia | exact H128 |].
  apply (u2a_cons m (X + 136) (X + 144)); [cbn [csize]; lia | exact H136 |].
  apply (u2a_cons m (X + 144) (X + 152)); [cbn [csize]; lia | exact H144 |].
  apply (u2a_cons m (X + 152) (X + 168)); [cbn [csize]; lia | exact H152 |].
  apply (u2a_cons m (X + 168) (X + 176)); [cbn [csize]; lia | exact H168 |].
  apply (u2a_cons m (X + 176) (X + 184)); [cbn [csize]; lia | exact H176 |].
  apply (u2a_cons m (X + 184) (X + 192)); [cbn [csize]; lia | exact H184 |].
  apply (u2a_cons m (X + 192) (X + 200)); [cbn [csize]; lia | exact H192 |].
  apply (u2a_cons m (X + 200) (X + 208)); [cbn [csize]; lia | exact H200 |].
  apply (u2a_cons m (X + 208) (X + 216)); [cbn [csize]; lia | exact H208 |].
  apply (u2a_cons m (X + 216) (X + 224)); [cbn [csize]; lia | exact H216 |].
  apply (u2a_cons m (X + 224) (X + 256)); [cbn [csize]; lia | exact H224 |].
  apply (u2a_cons m (X + 256) (X + 264)); [cbn [csize]; lia | exact H256 |].
  exact H264.
Qed.

Lemma seg_B2a : uslot_ser_chain_B -> forall X d h pl regs0 i n now buf cap,
  xok X -> dok X d pl -> 0 < buf -> buf mod 8 = 0 -> pf_img_free buf cap ->
  (buf + cap <= h \/ h + 480 <= buf) ->
  (d + Z.of_nat (length pl) <= buf \/ buf + cap <= d) ->
  seg_ev uSER_RET (uSER_W (LO X) X buf cap)
    (fun R m => P_SR X d h pl regs0 i n now buf cap R m /\ ser_extra X buf cap m /\ fenv X [(h, 480)] m)
    (fun q R m => q = uSER_FREE /\ P_SFREE X d h pl regs0 i n now buf R m).
Proof.
  intros SERB X d h pl regs0 i n now buf cap HX HD Hb0 Hb8 HIF HBH HBD fx' regs m0 Hf HI
    ((Hn & Hcap & G10 & G21 & G27 & [jb RB] & C136n & C152p & Hi & Hnow & G2 & G3 & G4 & G18 & G24 & G26 & Ci & Cn & HM) &
      (slk & canary & Hbsl & Hsl & BSL & JS & BN & GG & GW) & (STK & HBK)).
  destruct (HBK h 480 (or_introl eq_refl)) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI. pose proof (U.MemNorm.mem_inv_cj_task rsegs m0 HI) as TM.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  pose proof (stk_sub m0 _ _ (X + 2624 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST. clear STK.
  hdr_open HM.
  pose proof (rw_c8_cb m0 (X + 136) _ C136n) as P136.
  pose proof (u2a_cb m0 (X + 152) (X + 160) 8 8 _ _ ltac:(lia) (rw_c8_cb m0 (X + 152) _ C152p)
    (rw_c8_cb m0 (X + 160) _ Ci)) as P152.
  pose proof (rw_c8_cb m0 (X + 208) _ C208) as P208.
  pose proof (u2a_cb m0 (X + 224) (X + 232) 8 24 _ _ ltac:(lia) (rw_c8_cb m0 (X + 224) _ Cn)
    (u2a_cb m0 (X + 232) (X + 240) 8 16 _ _ ltac:(lia) (rw_c8_cb m0 (X + 232) _ C232)
      (u2a_cb m0 (X + 240) (X + 248) 8 8 _ _ ltac:(lia) (rw_c8_cb m0 (X + 240) _ C240)
        (rw_c8_cb m0 (X + 248) _ C248)))) as P224.
  pose proof (spill_join m0 X j0 j48 _ _ _ _ j264 h C0 C32 C40 C48 C120 C128 P136 C144 P152 C168 C176 C184 C192
    C200 P208 C216 P224 C256 C264) as SP.
  clear P136 P152 P208 P224.
  assert (ROB : rw_cells rsegs m0 (X + 944) [CB 2 j944; CB 6 (our_of pl)])
    by (apply (u2a_cons m0 (X + 944) (X + 946)); [cbn [csize]; lia | exact C944 | exact C946]).
  pose proof (u2a_cb m0 (X + 952) (X + 1056) 104 1464 _ _ ltac:(lia) C952
    (u2a_cb m0 (X + 1056) (X + 1080) 24 1440 _ _ ltac:(lia) C1056 C1080)) as RW.
  assert (LT : length T = 400%nat) by exact (proj1 (proj1 (proj1 CT))).
  assert (HTJ : X + 2624 - 65536 + U.Prog.reac_disco_table_json_c.TJ_K <= X)
    by (change U.Prog.reac_disco_table_json_c.TJ_K with 6240; lia).
  assert (HIE : IMG_END <= X + 2624 - 65536) by (unfold IMG_END; lia).
  pose proof (munch_refl (uSER_W (X + 2624 - 65536) X buf cap) m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  unfold rmk. eapply evt_mono.
  { eapply SERB with (canary := canary) (X := X) (lo := X + 2624 - 65536) (buf := buf) (cap := cap)
      (now := now) (n := n) (h := h) (i := i) (p := d + (Z.of_nat (length pl) - n))
      (T := T) (Lk := Lk) (Gt := Gt) (ob := our_of pl) (junk := jb) (slk := slk) (j0 := j0) (j1 := j48)
      (j2 := le8 (Z_to_bv 64 n)) (j3 := le8 (Z_to_bv 64 (d + (Z.of_nat (length pl) - n))) ++ le8 (Z_to_bv 64 i))
      (j4 := le8 j208) (j5 := le8 (Z_to_bv 64 now) ++ le8 j232 ++ le8 j240 ++ le8 j248) (j6 := j264)
      (jr := j944) (jw := j952 ++ j1056 ++ j1080) (sv := saved_of regs0);
      first [eassumption | exact Hf | lia]. }
  intros ms (t0' & t1' & t2' & s0' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s5' & s6' & s7' & s9' &
    t3' & t4' & t5' & t6' & F' & fc' & m1 & j0' & j4' & j5' & jw' & -> & HF & FK & MU1 & WM1 & MI1 & TM1 & ST1 &
    SP' & C136' & C152' & C160' & C224' & CLK' & CGT' & CT' & ROB' & RW' & CSV').
  unfold uSER_W, OFF_LOCK, OFF_GATE, OFF_TABLE, OFF_OUR, OFF_WORK, OFF_SAVE in *.
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  apply spill_split in SP'.
  destruct SP' as (S0 & S32 & S40 & S48 & S120 & S128 & S136 & S144 & S152 & S160 & S168 & S176 & S184 & S192 &
    S200 & S208 & S216 & S224 & S232 & S240 & S248 & S256 & S264).
  destruct (rw_cons_at m1 _ (X + 946) _ _ ROB' ltac:(cbn [csize]; lia)) as [R944 R946].
  destruct (junkb_sub m1 (X + 952) (X + 952) 1568 jw' 0 104 RW' ltac:(lia) ltac:(cbn; lia)) as [j952' S952].
  destruct (junkb_sub m1 (X + 952) (X + 1056) 1568 jw' 104 24 RW' ltac:(lia) ltac:(cbn; lia)) as [j1056' S1056].
  destruct (junkb_sub m1 (X + 952) (X + 1080) 1568 jw' 128 1440 RW' ltac:(lia) ltac:(cbn; lia)) as [j1080' S1080].
  do 2 eexists. exists uSER_FREE. do 2 eexists.
  split; [reflexivity|]. split; [exact HF|]. split; [unfold uSER_W, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
  split; [exact WM|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hn|]. split; [exact G27|]. split; [exact C136'|]. split; [exact C152'|].
  split; [exact Hi|]. split; [exact Hnow|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G18|]. split; [exact G24|]. split; [exact G26|]. split; [exact C160'|]. split; [exact C224'|].
  hdr_close.
Qed.
