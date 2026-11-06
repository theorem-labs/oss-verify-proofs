From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_identity_reac_ver_str_c.
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

Lemma seg_B24 : forall i,
  Hrec B APIf ra (Inv_U13558_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13540_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x13540 0x13558 _ _ _
    (fun regs m => V540 g i pl regs m /\ getr regs 10 = Z_to_bv 64 0) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as (((HREC & E20 & E26 & E21 & HPL & HID & HAG & HBF & HLP) & E22 & (E23 & E18 & E25 & E19 & E27) &
    E24 & HVB & HEN & HEV & E8 & HVR) & E10).
  unfold VER_LV in E10.
  pose proof HREC as (Hi & E9 & HNR & HG24 & HHW & HEVb).
  pose proof HF as (HGV & E2 & E3 & E4 & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  destruct (tb_norm_frame B APIf ra empty FF g _ _ _ _ _ _ _ HF) as (HRO & MIn & WRn & STn).
  pose proof (v2_LV (major (idS g i)) (minor (idS g i)) (patch (idS g i))) as HLV.
  pose proof (v2_EV_len (idS g i)) as HEQ.
  exists [], ([(8%bv, Z_to_bv 64 (zlen (EV (idS g i)))); (10%bv, Z_to_bv 64 0); (9%bv, Z_to_bv 64 (Z.of_nat i));
    (20%bv, Z_to_bv 64 (rec_k (g_in g) i)); (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)));
    (21%bv, Z_to_bv 64 pl); (22%bv, Z_to_bv 64 (rec_addr (g_in g) i));
    (23%bv, Z_to_bv 64 (fw_milli (idS g i))); (18%bv, Z_to_bv 64 (has_fw (idS g i)));
    (25%bv, Z_to_bv 64 (major (idS g i))); (19%bv, Z_to_bv 64 (minor (idS g i)));
    (27%bv, Z_to_bv 64 (patch (idS g i))); (24%bv, Z_to_bv 64 (rec_r (g_in g) i))] : list (reg * word)), [].
  split; [intros x H; exfalso; apply H; exact I|].
  split.
  - unfold cstr, spk, fsp, SLOT_FRAME in HEV, HVR.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HEV) as HEVn.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HVR) as HVRn.
    assert (EQ : (zlen (EV (idS g i)) =? lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_LV (major (idS g i)) (minor (idS g i))
                   (patch (idS g i))) = true)
      by (rewrite HEQ; apply Z.eqb_refl).
    unfold rmk. rewrite E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    unfold spk, fsp, SLOT_FRAME in *. unfold SLOT_K, SLOT_STACK in *.
    step.
    lazymatch goal with |- context [if ?c then _ else _] =>
      replace c with false; [cbv iota | symmetry; rewrite ?w0_lit, bv_lts_zero_r, MState.unsigned_lit by lia;
        apply Z.leb_gt; lia] end.
    step.
    lazymatch goal with |- context [if ?c then _ else _] =>
      replace c with false; [cbv iota | symmetry; rewrite tb_eqb_lit by lia; rewrite EQ; reflexivity] end.
    step. step. step. step.
    eapply Exec.evt_cut.
    { eapply BCMP with (ls := id_VER (idS g i) ++ [z8]) (rs := EV (idS g i) ++ [z8]) (v := 0).
      - rewrite MState.unsigned_lit by lia. exact HVRn.
      - rewrite MState.unsigned_lit by lia. exact HEVn.
      - rewrite MState.unsigned_lit by lia. rewrite v2_EV. apply tb_mm_refl.
        unfold zlen. rewrite length_app. cbn [length]. lia.
      - exact MIn. }
    intros ms' PO. destruct PO as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
      -> & MU & WM & _ & _ & _).
    rewrite (MState.ret_pc_even 0x13558) by (lia || reflexivity).
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split; [exact MU|]. split; [exact WM|]. apply Forall_nil.
  - intros regs' mem' HRL MU _. tb_regs HRL.
    unfold V540, RB12, REC, S6A, FNM, F7, F2, F9, F3, F11, RRr.
    unfold NRb, G24, HWb, EVb, PLB, IDb, AGN, BEF, LPm, cstr in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3).
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
