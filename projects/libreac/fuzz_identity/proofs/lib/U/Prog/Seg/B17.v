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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab3.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis BCMP : bcmp_contract.

Lemma seg_B17 : forall i,
  Hrec B APIf ra (Inv_U133bc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U133ac_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x133ac 0x133bc _ _ _
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\
       rec_r (g_in g) i = 0 /\ getr regs 10 = Z_to_bv 64 0) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E20 & E26 & E21 & HPL & HID & HAG & HBF & HLP) & E22 & ((E23 & E18 & E25 & E19 & E27) & E8) &
    E24 & Hr0 & _).
  pose proof HREC as (Hi & E9 & HNR & HG24 & HHW & HEV).
  pose proof HF as (HGV & E2 & E3 & E4 & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  destruct (tb_norm_frame B APIf ra empty FF g _ _ _ _ _ _ _ HF) as (HRO & MIn & WRn & STn).
  exists [], ([(9%bv, Z_to_bv 64 (Z.of_nat i)); (20%bv, Z_to_bv 64 (rec_k (g_in g) i));
    (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i))); (21%bv, Z_to_bv 64 pl); (22%bv, Z_to_bv 64 (rec_addr (g_in g) i));
    (23%bv, Z_to_bv 64 (fw_milli (idS g i))); (18%bv, Z_to_bv 64 (has_fw (idS g i)));
    (25%bv, Z_to_bv 64 (major (idS g i))); (19%bv, Z_to_bv 64 (minor (idS g i)));
    (27%bv, Z_to_bv 64 (patch (idS g i))); (8%bv, Z_to_bv 64 (has_model_name (idS g i)));
    (24%bv, Z_to_bv 64 (rec_r (g_in g) i)); (10%bv, Z_to_bv 64 0)] : list (reg * word)), [].
  split; [intros x H; exfalso; apply H; exact I|].
  split.
  - unfold rmk. rewrite E2, E3, E4, E9, E20, E26, E21, E22, E23, E18, E25, E19, E27, E8, E24.
    unfold fsp, SLOT_FRAME in *. unfold SLOT_K, SLOT_STACK in *.
    step. step. step. step.
    eapply Exec.evt_cut.
    { eapply BCMP with (ls := rec_id (g_in g) i) (rs := rec_id (g_in g) (S i)) (v := 0).
      - rewrite MState.unsigned_lit by lia. unfold BEF, spk, fsp, SLOT_FRAME in HBF.
        exact (bytes_at_normalize rsegs mem _ _ HRO HBF).
      - rewrite MState.unsigned_lit by lia. unfold IDb, spk, fsp, SLOT_FRAME in HID.
        exact (bytes_at_normalize rsegs mem _ _ HRO HID).
      - cbn [rec_id]. rewrite (ING_ignored _ _ _ Hr0). apply tb_mm_refl.
        rewrite rec_id_length. vm_compute. lia.
      - exact MIn. }
    intros ms' PO. destruct PO as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
      -> & MU & WM & _ & _ & _).
    rewrite (MState.ret_pc_even 0x133bc) by (lia || reflexivity).
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (constructor; [reflexivity|]); constructor|].
    split; [exact MU|]. split; [exact WM|]. constructor.
  - intros regs' mem' HRL MU _. tb_regs HRL.
    unfold RB12, REC, S6A, FALL, FNM, F7, F2, F9, F3, F11, F0, RRr.
    unfold NRb, G24, HWb, EVb, PLB, IDb, AGN, BEF, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3).
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
