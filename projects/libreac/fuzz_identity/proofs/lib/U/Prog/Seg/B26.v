From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU memchr_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab3.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma n26_find : forall l, (first_zero l < length l)%nat -> find_byte 0 l = Some (first_zero l).
Proof.
  induction l as [|b l IH]; cbn [length first_zero find_byte]; intros H; [lia|].
  unfold bz in *. revert H. destruct (bv_unsigned b =? 0) eqn:E; intros H; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma n26_mn17 : forall inp j,
  (first_zero (model_name (rec_id inp j)) < length (model_name (rec_id inp j)))%nat.
Proof.
  intros inp j. pose proof (name_str_len inp j) as H. unfold name_str in H.
  rewrite length_firstn in H.
  assert (Lm : length (model_name (rec_id inp j)) = 17%nat)
    by (unfold model_name, get, OFF_NAME, NAME_CAP; rewrite length_firstn, length_skipn, rec_id_length;
        unfold ID_SIZE; lia).
  rewrite Lm in *. lia.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis MEMCHR : memchr_contract.

Lemma seg_B26 : forall i,
  Hrec B APIf ra (Inv_U135d0_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U135c0_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x135c0 0x135d0 _ _ _
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ NMA g i /\
       getr regs 10 = Z_to_bv 64 (spk g 149 + wn (idS g i))) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E20 & E26 & E21 & HPL & HID & HAG & HBF & HLP) & E22 & ((E23 & E18 & E25 & E19 & E27) & E8) &
    E24 & HNMA).
  pose proof HREC as (Hi & E9 & HNR & HG24 & HHW & HEVb).
  pose proof HF as (HGV & E2 & E3 & E4 & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  destruct (tb_norm_frame B APIf ra empty FF g _ _ _ _ _ _ _ HF) as (HRO & MIn & WRn & STn).
  pose proof (n26_mn17 (g_in g) (S i)) as F17.
  change (rec_id (g_in g) (S i)) with (idS g i) in F17.
  exists [], ([(9%bv, Z_to_bv 64 (Z.of_nat i)); (20%bv, Z_to_bv 64 (rec_k (g_in g) i));
    (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i))); (21%bv, Z_to_bv 64 pl); (22%bv, Z_to_bv 64 (rec_addr (g_in g) i));
    (23%bv, Z_to_bv 64 (fw_milli (idS g i))); (18%bv, Z_to_bv 64 (has_fw (idS g i)));
    (25%bv, Z_to_bv 64 (major (idS g i))); (19%bv, Z_to_bv 64 (minor (idS g i)));
    (27%bv, Z_to_bv 64 (patch (idS g i))); (8%bv, Z_to_bv 64 (has_model_name (idS g i)));
    (24%bv, Z_to_bv 64 (rec_r (g_in g) i)); (10%bv, Z_to_bv 64 (spk g 149 + wn (idS g i)))] : list (reg * word)), [].
  split; [intros x H; exfalso; apply H; exact I|].
  split.
  - unfold rmk. rewrite E2, E3, E4, E9, E20, E26, E21, E22, E23, E18, E25, E19, E27, E8, E24.
    unfold fsp, SLOT_FRAME in *. unfold SLOT_K, SLOT_STACK in *.
    step. step. step. step.
    eapply Exec.evt_cut.
    { eapply MEMCHR with (buf := skipn 3 (idS g i)).
      - rewrite MState.unsigned_lit by lia.
        apply (bytes_at_normalize rsegs mem _ _ HRO).
        unfold IDb in HID. apply (n_bytes_at_skipn mem _ _ 3 _ HID).
        + rewrite rec_id_length. unfold ID_SIZE. lia.
        + unfold spk, fsp, SLOT_FRAME. lia.
      - rewrite !MState.unsigned_lit by lia. unfold memchr_ok.
        change (Z.to_nat 17) with 17%nat. change (0 mod 256) with 0.
        change (firstn 17 (skipn 3 (idS g i))) with (model_name (idS g i)).
        rewrite (n26_find _ F17). left. rewrite length_skipn. unfold idS. rewrite rec_id_length.
        unfold ID_SIZE. lia.
      - exact MIn. }
    intros ms' PO. destruct PO as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
      -> & MU & WM & _ & _).
    rewrite (MState.ret_pc_even 0x135d0) by (lia || reflexivity).
    match goal with |- context [memchr_res ?A ?C ?N ?BUF] =>
      replace (memchr_res A C N BUF) with (spk g 149 + wn (idS g i)) end.
    2: { rewrite !MState.unsigned_lit by lia. unfold memchr_res.
         change (Z.to_nat 17) with 17%nat. change (0 mod 256) with 0.
         change (firstn 17 (skipn 3 (idS g i))) with (model_name (idS g i)). rewrite (n26_find _ F17).
         unfold wn, spk, fsp, SLOT_FRAME. lia. }
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split; [exact MU|]. split; [exact WM|]. apply Forall_nil.
  - intros regs' mem' HRL MU _. tb_regs HRL.
    unfold RB12, REC, S6A, FALL, FNM, F7, F2, F9, F3, F11, F0, RRr.
    unfold NRb, G24, HWb, EVb, PLB, IDb, AGN, BEF, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3).
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
