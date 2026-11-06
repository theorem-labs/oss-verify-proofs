From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_seg slot_preds slot_cells slot_sB1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c disco_table_c disco_table hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_age_c reac_disco_table_age reac_hunt_step_c reac_hunt_verdict_name_c check_table_c reac_hunt_role_c reac_hunt_heard_anything_c slot_step slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_sLatch.
Import ListNotations.
Open Scope Z_scope.

Definition P_R15 (X d h : Z) (pl : list byte) (regs0 : bvmap 5 word) (i n now : Z)
    (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  0 <= n <= Z.of_nat (length pl) /\ getr R 23 = Z_to_bv 64 (d + (Z.of_nat (length pl) - n)) /\
  rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 n)] /\ P_BASE X d h pl regs0 i now R m.

Definition W_B3a (X h : Z) : list (Z * Z) := [(LO X, X); (h, h + 480)].

Lemma hs_our : forall h H now, hunt_ok H -> sub (hs_hunt h H now) 412 6 = sub H 412 6.
Proof.
  intros h H now (LH & TOK & _).
  assert (LT : length (hs_table H now) = 400%nat).
  { unfold hs_table. destruct (age_model (sub H 0 400) now) as [T r] eqn:E.
    exact (proj1 (age_model_post (sub H 0 400) now T r ltac:(apply length_sub; lia) TOK E)). }
  unfold hs_hunt, sub at 1.
  rewrite skipn_app, LT, skipn_all2 by lia. cbn [Nat.sub app].
  rewrite skipn_app, length_sub by lia. cbn [Nat.sub].
  rewrite firstn_app, length_skipn, length_sub by lia.
  cbn [Nat.sub]. rewrite firstn_O, app_nil_r.
  change (sub (sub H 400 40) 12 6 = sub H 412 6).
  rewrite sub_sub by lia. reflexivity.
Qed.

Lemma seg_B3a : reac_hunt_step_contract -> reac_hunt_verdict_name_contract -> check_table_contract ->
  reac_hunt_role_contract -> reac_hunt_heard_anything_contract ->
  forall X d h pl regs0 i n now, xok X -> dok X d pl -> h mod 16 = 0 ->
  (d + Z.of_nat (length pl) <= h \/ h + 480 <= d) ->
  seg_ev SER_FREE_RET (W_B3a X h)
    (fun R m => P_R15 X d h pl regs0 i n now R m /\ fenv X [(h, 480)] m)
    (P_NEXT X d h pl regs0 i).
Proof.
  intros HSC VNC CTC RLC HAC X d h pl regs0 i n now HX HD Hh16 HDJ fx' regs m0 Hf HI
    ((Hn & G23 & C152n & Hi & Hnow & G2 & G3 & G4 & G8 & G9 & G18 & G24 & G27 & HM) & (STK & HBK)).
  destruct (HBK h 480 (or_introl eq_refl)) as (Hh0 & Hh1 & _). clear HBK.
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  pose proof (stk_sub m0 _ _ (X + 2592 - 65536) X STK ltac:(lia) ltac:(lia) ltac:(lia)) as ST. clear STK.
  hdr_open HM.
  pose proof (hs_our h Hunt now HOK) as OUR'. rewrite OUR in OUR'.
  pose proof (munch_refl (W_B3a X h) m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  unfold W_B3a, LO, SLOT_FRAME, SLOT_STACK in MU.
  unfold rmk. eapply evt_cut.
  { eapply (slot_R15) with (X := X) (lo := X + 2592 - 65536) (h := h) (n := n)
      (p := d + (Z.of_nat (length pl) - n)) (now := now) (H := Hunt);
      first [eassumption | unfold REAC_HUNT_STEP_K, reac_master_only_cadence_ns_c.RT; lia]. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
    F' & m1 & -> & FK & MU1 & WM1 & MI1 & ST1 & C144' & C152' & CH' & HOK').
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  assert (R176 : ov_read_bytes rsegs m1 (wa (X + 176)) 8 = Some (le8 (Z_to_bv 64 STALE_NS))).
  { eapply rw_cells_read_at with (k := 0%nat) (c := C8 (Z_to_bv 64 STALE_NS));
      [exact C176|reflexivity|reflexivity|]; f_equal; lia. }
  eapply evt_mono.
  { eapply slot_R16 with (spz := X) (i := i) (n := n); first [reflexivity | eassumption | lia]. }
  intros ms ->.
  destruct (Z.ltb_spec i (MAX_OPS - 1)) as [Hil|Hih]; cbn [andb].
  - destruct (Z.eqb_spec n 0) as [Hnz|Hnz]; cbn [negb].
    + do 2 eexists. exists EXIT. do 2 eexists.
      split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_B3a, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
      split; [exact WM|]. right. split; [reflexivity|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [reflexivity|]. exact CSV.
    + do 2 eexists. exists HDR. do 2 eexists.
      split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_B3a, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
      split; [exact WM|]. left. split; [reflexivity|]. split; [lia|]. exists n, now.
      split; [lia|]. split; [exact Hnow|]. split; [lia|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [reflexivity|].
      split; [reflexivity|]. split; [exact G18|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact G24|]. split; [exact G27|]. hdr_close.
  - do 2 eexists. exists EXIT. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_B3a, LO, SLOT_FRAME, SLOT_STACK; exact MU|].
    split; [exact WM|]. right. split; [reflexivity|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [reflexivity|]. exact CSV.
Qed.
