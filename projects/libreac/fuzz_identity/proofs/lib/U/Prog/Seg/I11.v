From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section I11.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis CC : reac_box_catalogue_contract.

Lemma seg_I11 : Hcut B APIf ra (Inv_U13e70 B APIf ra empty) -> Hcut B APIf ra (Inv_U13e54 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13e70. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM ((HI & R0) & E10 & E13).
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  destruct (HO R0) as (C1 & C2 & C3). destruct (Tac_si.n_r0 _ R0) as [Wk Ft].
  destruct (Tac_si.fits_unfold _ Ft) as (F1 & F2 & F3).
  destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMR & _).
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N2) as [BT1 BT2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  pose proof (Tac_si.tk_len (g_in g)) as TL.
  pose proof (Tac_si.caps_range (g_in g)) as CR. unfold bsz in BT2.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C2) as C2n.
  pose proof (cstr_byte _ _ _ (length (n_TK (g_in g))) C2n ltac:(lia)) as RT.
  rewrite Tac_si.nthb_snoc_eq in RT.
  pose proof (n_ld_le _ Wk) as LD.
  set (a := g_S g - 384 + 192).
  unfold zlen in E10. unfold rmk, Frame.mkR. rewrite E2, E10, E13, E21.
  step. ltu_off.
  step. step. change (zxb z8) with (Z_to_bv 64 0).
  step. br_if.
  pose proof (st_ok g (normalize rsegs mem) a 8 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  try change (Z_to_bv 64 a) with (wa a).
  try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)).
  set (z64 := le8 (Z_to_bv 64 0)).
  assert (L8 : length z64 = 8%nat) by apply length_le8.
  pose proof (Frame.munch_write [(a, a + 8)] (normalize rsegs mem) (normalize rsegs mem) a z64 (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(rewrite L8; unfold a; lia) ltac:(rewrite L8; cbn; lia)) as MU1.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) z64 (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Mem.wr_at_write rsegs (normalize rsegs mem) (g_S g - 65536) 65536 (wa a) z64 HWR0) as HWR1.
  remember (write_to_mem (normalize rsegs mem) (wa a) z64) as m1 eqn:Em1.
  step. step.
  eapply (cat_call CC) with (c := a).
  - unfold a. reflexivity.
  - unfold a. lia.
  - unfold a. Z.div_mod_to_equations. lia.
  - eapply wr_sub; [exact HWR1 | unfold a; lia | unfold a; lia | lia].
  - intros a1' m' HB MU WM.
    rewrite (MState.ret_pc_even 0x13e70) by (lia || reflexivity).
    assert (MUa : Frame.munch [(a, a + 8)] (normalize rsegs mem) m')
      by (apply (Frame.munch_trans _ _ m1 m'); [exact MU1 | exact MU]).
    assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) [(a, a + 8)])
      by (unfold a; repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
    pose proof (stk_after _ _ _ _ _ HSTK0 MUa (Frame.wmono_trans _ _ _ _ WM1 WM) ltac:(lia) ltac:(lia)) as STK1.
    apply (fin_mem g mem regs 0x13e70 _ _ m' (munch_SWIN g _ _ _ MUa FW) (Frame.wmono_trans _ _ _ _ WM1 WM) STK1);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    assert (KMm : KM _ mem m'') by exact (KM_of _ mem m' m'' HRO MUa HREL).
    assert (HO' : OUTS g nm tk dp m'')
      by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM
        (munch_SWIN g _ _ _ MUa FW) HREL HO).
    split; [split; [|exact R0]|split].
    + apply (IRb_keep g nm tk dp regs mem R' m'' _ HI KMm HO'); try (cbn; unfold spk, fsp, SLOT_FRAME, a, n_ln, n_ld in *; lia);
        kr HG.
    + apply (fin_bytes m'' m' _ _ HREL). unfold q64, CAT_N, spk, fsp, SLOT_FRAME. exact HB.
    + rewrite HG. greg2. reflexivity.
Qed.

End I11.
