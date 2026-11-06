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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uab3.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Ltac n27_cond :=
  unfold bv_eqb, bv_ltu, bv_leu; rewrite ?MState.unsigned_lit by lia;
  repeat match goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _))
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _))
  end;
  first [ reflexivity | apply Z.eqb_neq; lia | apply Z.eqb_eq; lia | apply Z.ltb_ge; lia | apply Z.ltb_lt; lia ].

Ltac n27_br b :=
  lazymatch goal with
  | |- Exec.evt _ _ (MState.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; n27_cond]
  end.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis BCMP : bcmp_contract.

Lemma seg_B27 : forall i,
  Hrec B APIf ra (Inv_U13604_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U135d0_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x135d0 0x13604 _ _ _
    (fun regs m => RB12 g i pl regs m /\ FNM g i regs /\ RRr g i regs /\ NMA g i /\
       getr regs 22 = Z_to_bv 64 (wn (idS g i)) /\ getr regs 8 = Z_to_bv 64 (wn (idS g i) + 1) /\
       getr regs 10 = Z_to_bv 64 0) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E20 & E26 & E21 & HPL & HID & HAG & HBF & HLP) & E22 & ((E23 & E18 & E25 & E19 & E27) & E8) &
    E24 & HNMA & E10).
  pose proof HREC as (Hi & E9 & HNR & HG24 & HHW & HEVb).
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  assert (Hin : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HM Hin) as [Hpl1 Hpl2].
  pose proof HF as (HGV & E2 & E3 & E4 & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  destruct (tb_norm_frame B APIf ra empty FF g _ _ _ _ _ _ _ HF) as (HRO & MIn & WRn & STn).
  pose proof HNMA as (HR1 & HA).
  destruct (n_nma (g_in g) i HR1 HA) as (HM1 & HW & HW1 & HWk & HFE).
  change (rec_id (g_in g) (S i)) with (idS g i) in HM1, HW, HFE.
  pose proof (name_len_le (rec_pl (g_in g) i)) as (HW16 & _).
  pose proof (rec_pl_length (g_in g) i) as Hpl.
  pose proof (rec_k_range (g_in g) i) as Hkr.
  pose proof (rec_id_length (g_in g) (S i)) as Hidl. change (rec_id (g_in g) (S i)) with (idS g i) in Hidl.
  unfold ID_SIZE in Hidl.
  assert (WB : 1 <= wn (idS g i) <= 16 /\ wn (idS g i) + 1 <= rec_k (g_in g) i) by lia.
  unfold PLB in HPL. pose proof (bytes_at_bound rsegs _ _ _ HPL) as Hplb. rewrite Hpl in Hplb.
  exists [], ([(9%bv, Z_to_bv 64 (Z.of_nat i)); (20%bv, Z_to_bv 64 (rec_k (g_in g) i));
    (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i))); (21%bv, Z_to_bv 64 pl);
    (23%bv, Z_to_bv 64 (fw_milli (idS g i))); (18%bv, Z_to_bv 64 (has_fw (idS g i)));
    (25%bv, Z_to_bv 64 (major (idS g i))); (19%bv, Z_to_bv 64 (minor (idS g i)));
    (27%bv, Z_to_bv 64 (patch (idS g i))); (24%bv, Z_to_bv 64 (rec_r (g_in g) i));
    (22%bv, Z_to_bv 64 (wn (idS g i))); (8%bv, Z_to_bv 64 (wn (idS g i) + 1));
    (10%bv, Z_to_bv 64 0)] : list (reg * word)), [].
  split; [intros x H; exfalso; apply H; exact I|].
  split.
  - unfold spk, fsp, SLOT_FRAME in E10. unfold F0 in E8. rewrite HM1 in E8.
    unfold rmk. rewrite E2, E3, E4, E9, E20, E26, E21, E22, E23, E18, E25, E19, E27, E8, E24, E10.
    unfold fsp, SLOT_FRAME in *. unfold SLOT_K, SLOT_STACK in *.
    step. n27_br false.
    step. n27_br false.
    step.
    step. n27_br false.
    step.
    replace (bv_unsigned (Z_to_bv 64 (g_S g - 384 + 149 + wn (idS g i))) - bv_unsigned (Z_to_bv 64 (g_S g - 384 + 149)))
      with (wn (idS g i)) by (rewrite !MState.unsigned_lit by lia; lia).
    step.
    step. n27_br false.
    step. step. step. n27_br false.
    step. step. step.
    eapply Exec.evt_cut.
    { eapply BCMP with (ls := skipn 3 (idS g i)) (rs := skipn 1 (rec_pl (g_in g) i)) (v := 0).
      - rewrite MState.unsigned_lit by lia.
        apply (bytes_at_normalize rsegs mem _ _ HRO).
        unfold IDb in HID. apply (n_bytes_at_skipn mem _ _ 3 _ HID);
          [rewrite rec_id_length; unfold ID_SIZE; lia | unfold spk, fsp, SLOT_FRAME; lia].
      - rewrite MState.unsigned_lit by lia.
        apply (bytes_at_normalize rsegs mem _ _ HRO).
        apply (n_bytes_at_skipn mem _ _ 1 _ HPL); [lia | lia].
      - rewrite MState.unsigned_lit by lia.
        match goal with |- context [Z.to_nat ?x] => replace (Z.to_nat x) with (name_len (rec_pl (g_in g) i)) by lia end.
        apply tb_mm_eq; [exact HFE | rewrite length_skipn; lia | rewrite length_skipn; lia].
      - exact MIn. }
    intros ms' PO. destruct PO as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
      -> & MU & WM & _ & _ & _).
    rewrite (MState.ret_pc_even 0x13604) by (lia || reflexivity).
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split; [exact MU|]. split; [exact WM|]. apply Forall_nil.
  - intros regs' mem' HRL MU _. tb_regs HRL.
    unfold RB12, REC, FNM, F7, F2, F9, F3, F11, RRr.
    unfold NRb, G24, HWb, EVb, PLB, IDb, AGN, BEF, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1' & HW2' & HW3').
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
