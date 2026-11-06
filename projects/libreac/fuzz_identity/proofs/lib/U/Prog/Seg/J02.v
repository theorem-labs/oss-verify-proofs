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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU reac_box_catalogue_defect_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section J02.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis DEF : reac_box_catalogue_defect_contract.

Lemma seg_J02 : Hcut B APIf ra (Inv_U13ef8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13ee4 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13ef8. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM ((HI & R0) & HQ).
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & PS & _ & _ & HMR & _).
  unfold SLOT_K, SLOT_STACK in PS.
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  destruct (HO R0) as (C1 & C2 & C3).
  destruct (nr0_fits (g_in g) R0) as (Wk & F1 & F2 & F3).
  destruct (caps_range (g_in g)) as (K1 & K2 & K3 & K4 & K5 & K6).
  destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N3) as [BD1 BD2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold bsz in BD2.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C3) as C3n.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ56)) as R56. unfold spk, fsp, SLOT_FRAME in R56.
  unfold rmk, Frame.mkR. rewrite E2, E9, E22.
  step. step. step. step. step.
  eapply Exec.evt_cut.
  { eapply DEF with (lo := g_S g - 65536) (e := 0) (i := t_in (g_in g)) (o := t_out (g_in g)) (d := dp)
      (I := 0) (O := 0) (P := 0) (sP := []) (sd := n_EXP_DP (g_in g));
      rewrite ?(MState.unsigned_lit (g_S g - 384)) by lia; unfold REAC_BOX_CATALOGUE_DEFECT_FRAME.
    all: try first [reflexivity | lia | exact HMI0 | (intros H; exfalso; apply H; reflexivity)].
    - intros _. split; [exact C3n|]. split; [apply Tac_si.nzb_notin, Tac_si.nzb_EXP_DP, Wk|].
      left. unfold n_ld in F3. lia.
    - exact (proj1 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 384) (g_S g) HSTK0
        ltac:(lia))). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    -> & MU & WM & MI' & STK').
  rewrite (MState.unsigned_lit (g_S g - 384)) in MU, STK' by lia. unfold REAC_BOX_CATALOGUE_DEFECT_FRAME in MU.
  rewrite (MState.ret_pc_even 0x13ef8) by (lia || reflexivity).
  assert (STK2 : Frame.stk rsegs m' (g_S g - 65536) (g_S g)).
  { apply (Frame.stk_merge rsegs m' (g_S g - 65536) (g_S g - 384) (g_S g) STK'); [|lia].
    apply (Frame.stk_transport_disjoint rsegs _ (normalize rsegs mem) m' _ _
      (proj2 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 384) (g_S g) HSTK0 ltac:(lia)))
      MU WM). cbn. lia. }
  assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) [(g_S g - 384 - 16, g_S g - 384)])
    by (repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
  apply (fin_mem g mem regs 0x13ef8 _ _ m' (munch_SWIN g _ _ _ MU FW) WM STK2);
    [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m'' HG HREL. cbv beta.
  assert (KMm : KM _ mem m'') by exact (KM_of _ mem m' m'' HRO MU HREL).
  assert (HO' : OUTS g nm tk dp m'')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM (munch_SWIN g _ _ _ MU FW)
      HREL HO).
  assert (D4 : disjoint_from [(g_S g - 384 - 16, g_S g - 384)] (spk g 192) 8)
    by (cbn; unfold spk, fsp, SLOT_FRAME; lia).
  split; [split|split].
  - apply (IRb_keep g nm tk dp regs mem R' m'' _ HI KMm HO'); try (cbn; unfold spk, fsp, SLOT_FRAME, n_ld in *; lia);
      kr HG.
  - exact R0.
  - unfold q64 in HQ |- *. apply (KMm _ _ ltac:(rewrite length_le8; exact D4) HQ).
  - rewrite HG. greg2. reflexivity.
Qed.

End J02.
