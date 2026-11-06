From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_init_c reac_disco_gate_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_peer_lock_init_c reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_pin_c reac_hunt_silence_proven_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_exit slot_R0_R3 slot_init slot_seg slot_preds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_cells.
Import ListNotations.
Open Scope Z_scope.

Definition W_E2 (X h : Z) : list (Z * Z) := [(LO X, X); (X + 236, X + 912); (h, h + 480); (X, X + 236)].

Lemma seg_E2 : reac_disco_table_init_contract -> reac_disco_gate_init_contract ->
  reac_disco_peer_lock_init_contract -> reac_hunt_init_contract ->
  reac_hunt_pin_contract -> reac_hunt_silence_proven_contract ->
  forall X d h pl regs0, xok X -> dok X d pl -> (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  seg_ev R2_RET (W_E2 X h) (fun R m => P_R2 X d h pl regs0 R m /\ fenv X [(h, 480)] m)
    (fun q R m => (q = HDR /\ P_HDR X d h pl regs0 0 R m) \/ (q = EXIT /\ P_EXIT X h regs0 R m)).
Proof.
  intros TIC GIC LIC HIC PIC SIC X d h pl regs0 HX HD HDJ fx' regs m0 Hf HI
    ((G10 & G2 & G3 & G4 & G19 & G21 & G24 & SV & OU & BD & H16 & [jh HB]) & (STK & HBK)).
  destruct (HBK h 480 (or_introl eq_refl)) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  set (n := Z.of_nat (length pl)) in *.
  destruct (stk_cb m0 _ _ X 236 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jsp J0].
  destruct (stk_cb m0 _ _ (X + 236) 12 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jl J236].
  destruct (stk_cb m0 _ _ (X + 248) 264 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jg J248].
  destruct (stk_cb m0 _ _ (X + 512) 400 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jt J512].
  destruct (stk_cb m0 _ _ (X + 912) 2 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j912 J912].
  destruct (stk_cb m0 _ _ (X + 920) 104 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j920 J920].
  destruct (stk_cb m0 _ _ (X + 1024) 24 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j1024 J1024].
  destruct (stk_cb m0 _ _ (X + 1048) 1440 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j1048 J1048].
  pose proof (stk_sub m0 _ _ (X + 2592 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
  clear STK.
  pose proof (munch_refl (W_E2 X h) m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  unfold W_E2, LO, SLOT_FRAME, SLOT_STACK in MU.
  unfold rmk. eapply evt_cut.
  { eapply (slot_R2 TIC GIC LIC HIC PIC SIC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0
      X (X + 2592 - 65536) h (our_of pl) jt jg jl jh G2 G10); try eassumption; lia. }
  intros ms (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
    m1 & H & -> & MU1 & WM1 & MI1 & ST1 & RL1 & RG1 & RT1 & RU1 & RH1 & LK & GK & TK & HK & SUB).
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  eapply evt_cut.
  { eapply (slot_R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 X (n - pre_take n) h jsp
      G2 G19); [reflexivity | lia | lia | unfold pre_take; lia | eassumption | exact MI1]. }
  intros ms [(Hn0 & ->) | (Hn0 & a0'' & a1'' & a2'' & a3'' & a5'' & a6'' & m2 & j0 & j1 & j2 & j3 & j4 & -> &
    MU2 & WM2 & MI2 & SP2)].
  - apply evt_done. do 2 eexists. exists EXIT. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_E2, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. right. split; [reflexivity|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [reflexivity|]. eassumption.
  - transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    apply spill_split in SP2.
    destruct SP2 as (S0 & S24 & S32 & S40 & S144 & S152 & S160 & S168 & S176 & S184 & S192 & S200 & S208 & S216 &
      S224 & S232).
    apply evt_done. do 2 eexists. exists HDR. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_E2, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. left. split; [reflexivity|].
    exists (n - pre_take n), NOW0.
    assert (Hpt : 0 <= pre_take n <= n) by (unfold pre_take; lia).
    split; [lia|]. split; [unfold NOW0; lia|]. split; [unfold MAX_OPS; lia|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact G19|]. split; [reflexivity|].
    split; [etransitivity; [exact G21|]; apply f_equal; unfold n; lia|]. split; [exact G24|]. split; [reflexivity|].
    unfold hdr_mem.
    split; [exact S0|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|]. split; [exact S144|].
    split; [exact S152|]. split; [exact S160|]. split; [exact S168|]. split; [exact S176|].
    split; [exact S184|]. split; [exact S192|]. split; [exact S200|]. split; [exact S208|].
    split; [exact S216|]. split; [exact S224|]. split; [exact S232|].
    split; [eexists; eassumption|].
    split; [eexists; split; eassumption|].
    split; [eexists; split; eassumption|].
    split; [eexists; eassumption|]. split; [eassumption|].
    split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [eexists; eassumption|].
    split; [eassumption|].
    split; [exists H; split; [eassumption|]; split; eassumption|].
    eassumption.
Qed.
