From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_init_c reac_disco_gate_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_peer_lock_init_c reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_pin_c reac_hunt_silence_proven_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_exit uslot_R0_R3 uslot_init uslot_seg uslot_preds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_cells.
Import ListNotations.
Open Scope Z_scope.

Definition W_E2 (X h : Z) : list (Z * Z) := [(LO X, X); (X + 268, X + 944); (h, h + 480); (X, X + 268)].

Lemma seg_E2 : reac_disco_table_init_contract -> reac_disco_gate_init_contract ->
  reac_disco_peer_lock_init_contract -> reac_hunt_init_contract ->
  reac_hunt_pin_contract -> reac_hunt_silence_proven_contract ->
  forall X d h pl regs0, xok X -> dok X d pl -> (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  seg_ev R2_RET (W_E2 X h) (fun R m => P_R2 X d h pl regs0 R m /\ fenv X [(h, 480)] m)
    (fun q R m => (q = HDR /\ P_HDR X d h pl regs0 0 R m) \/ (q = EXIT /\ P_EXIT X h regs0 R m)).
Proof.
  intros TIC GIC LIC HIC PIC SIC X d h pl regs0 HX HD HDJ fx' regs m0 Hf HI
    ((G10 & G2 & G3 & G4 & G21 & G23 & G24 & SV & OU & BD & H16 & [jh HB]) & (STK & HBK)).
  destruct (HBK h 480 (or_introl eq_refl)) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  set (n := Z.of_nat (length pl)) in *.
  destruct (stk_cb m0 _ _ X 168 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [ja J0].
  destruct (stk_cb m0 _ _ (X + 168) 8 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jsp J168].
  destruct (stk_cb m0 _ _ (X + 176) 92 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jb J176].
  destruct (stk_cb m0 _ _ (X + 268) 12 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jl J268].
  destruct (stk_cb m0 _ _ (X + 280) 264 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jg J280].
  destruct (stk_cb m0 _ _ (X + 544) 400 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jt J544].
  destruct (stk_cb m0 _ _ (X + 944) 2 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j944 J944].
  destruct (stk_cb m0 _ _ (X + 952) 104 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j952 J952].
  destruct (stk_cb m0 _ _ (X + 1056) 24 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j1056 J1056].
  destruct (stk_cb m0 _ _ (X + 1080) 1440 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [j1080 J1080].
  pose proof (stk_sub m0 _ _ (X + 2624 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST.
  clear STK.
  pose proof (munch_refl (W_E2 X h) m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  unfold W_E2, LO, SLOT_FRAME, SLOT_STACK in MU.
  unfold rmk. eapply evt_cut.
  { eapply (uslot_R2 TIC GIC LIC HIC PIC SIC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0
      X (X + 2624 - 65536) h (our_of pl) jt jg jl jh jsp G2 G10); try eassumption; lia. }
  intros ms (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
    m1 & H & -> & MU1 & WM1 & MI1 & ST1 & C168 & RL1 & RG1 & RT1 & RU1 & RH1 & LK & GK & TK & HK & SUB).
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  assert (SP : rw_cells rsegs m1 X [CB 168 ja; C8 (Z_to_bv 64 h); CB 92 jb]).
  { apply (rw_join m1 X (X + 168) [CB 168 ja] [C8 (Z_to_bv 64 h); CB 92 jb]); [cbn [cells_size csize]; lia | exact J0|].
    apply (rw_join m1 (X + 168) (X + 176) [C8 (Z_to_bv 64 h)] [CB 92 jb]); [cbn [cells_size csize]; lia | exact C168 | exact J176]. }
  clear J0 J176.
  eapply evt_cut.
  { eapply (uslot_R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 X (n - pre_take n) h ja jb
      G2 G23); [lia | lia | unfold pre_take; lia | lia | clear - H16; Z.div_mod_to_equations; lia | exact SP | exact MI1]. }
  intros ms [(Hn0 & ->) | (Hn0 & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' &
    m2 & j0 & j1 & j2 & j3 & j4 & j5 & j6 & -> & MU2 & WM2 & MI2 & SP2)].
  - apply evt_done. do 2 eexists. exists EXIT. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_E2, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. right. split; [reflexivity|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; eassumption.
  - clear SP C168. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    apply spill_split in SP2.
    destruct SP2 as (S0 & S32 & S40 & S48 & S120 & S128 & S136 & S144 & S152 & S160 & S168 & S176 & S184 & S192 &
      S200 & S208 & S216 & S224 & S232 & S240 & S248 & S256 & S264).
    apply evt_done. do 2 eexists. exists HDR. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_E2, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. left. split; [reflexivity|].
    exists (n - pre_take n), NOW0.
    assert (Hpt : 0 <= pre_take n <= n) by (unfold pre_take; lia).
    split; [lia|]. split; [unfold NOW0; lia|]. split; [unfold MAX_OPS; lia|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [etransitivity; [exact G21|]; apply f_equal; unfold n; lia|]. split; [exact G23|].
    split; [exact G24|]. split; [reflexivity|]. split; [reflexivity|].
    unfold hdr_mem.
    split; [exact S0|]. split; [exact S32|]. split; [exact S40|]. split; [exact S48|]. split; [exact S120|].
    split; [exact S128|]. split; [exact S136|]. split; [exact S144|]. split; [exact S152|].
    split; [exact S160|]. split; [exact S168|]. split; [exact S176|]. split; [exact S184|].
    split; [exact S192|]. split; [exact S200|]. split; [exact S208|]. split; [exact S216|].
    split; [exact S224|]. split; [exact S232|]. split; [exact S240|]. split; [exact S248|].
    split; [exact S256|]. split; [exact S264|].
    split; [eexists; exact RL1|].
    split; [eexists; split; [exact RG1 | exact GK]|].
    split; [eexists; split; [exact RT1 | exact TK]|].
    split; [eexists; exact J944|]. split; [exact RU1|].
    split; [eexists; exact J952|]. split; [eexists; exact J1056|]. split; [eexists; exact J1080|].
    split; [exact SV|].
    split; [exists H; split; [exact RH1|]; split; [exact HK | exact SUB]|].
    exact BD.
Qed.
