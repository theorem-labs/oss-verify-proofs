From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import reac_box_catalogue_defect_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh2.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section J02.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis DEF : reac_box_catalogue_defect_contract.

Lemma seg_J02 : Hcut B APIf ra (Inv_K13c5c B APIf ra empty) -> Hcut B APIf ra (Inv_K13c48 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K13c5c. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (Tac_si.FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & PS & _ & _ & HMR & _).
  unfold SLOT_K, SLOT_STACK in PS.
  destruct HP as ([HI R0] & HQ).
  pose proof HI as (HID & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HO & HE).
  destruct (HO R0) as (C1 & C2 & C3).
  destruct (nr0_fits (g_in g) R0) as (Wk & F1 & F2 & F3).
  destruct (caps_range (g_in g)) as (K1 & K2 & K3 & K4 & K5 & K6).
  destruct (Tac_si.nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  pose proof (Tac_si.blk_range B APIf _ _ _ _ _ _ HMR N3) as [BD1 BD2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold bsz in BD2.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C3) as C3n.
  unfold rmk, Frame.mkR. rewrite E2, R9, R18, R22.
  step. step. step. step. step.
  eapply Exec.evt_cut.
  { eapply DEF with (lo := g_S g - 65536) (e := 0) (i := t_in (g_in g)) (o := t_out (g_in g)) (d := dp)
      (I := 0) (O := 0) (P := 0) (sP := []) (sd := n_EXP_DP (g_in g));
      rewrite ?(MState.unsigned_lit (g_S g - 368)) by lia; unfold REAC_BOX_CATALOGUE_DEFECT_FRAME.
    all: try first [reflexivity | lia | exact HMI0 | (intros H; exfalso; apply H; reflexivity)].
    - intros _. split; [exact C3n|]. split; [apply Tac_si.nzb_notin, Tac_si.nzb_EXP_DP, Wk|].
      left. unfold n_ld in F3. lia.
    - exact (proj1 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 368) (g_S g) HSTK0
        ltac:(lia))). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    -> & MU & WM & MI' & STK').
  rewrite (MState.unsigned_lit (g_S g - 368)) in MU, STK' by lia. unfold REAC_BOX_CATALOGUE_DEFECT_FRAME in MU.
  rewrite (MState.ret_pc_even 0x13c5c) by (lia || reflexivity).
  assert (STK2 : Frame.stk rsegs m' (g_S g - 65536) (g_S g)).
  { apply (Frame.stk_merge rsegs m' (g_S g - 65536) (g_S g - 368) (g_S g) STK'); [|lia].
    apply (Frame.stk_transport_disjoint rsegs _ (normalize rsegs mem) m' _ _
      (proj2 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 368) (g_S g) HSTK0 ltac:(lia)))
      MU WM). cbn. lia. }
  assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) [(g_S g - 368 - 16, g_S g - 368)])
    by (repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
  apply (fin_mem g mem regs 0x13c5c _ _ m' (munch_SWIN g _ _ _ MU FW) WM STK2);
    [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m'' HG HREL. cbv beta.
  assert (KMm : KM _ mem m'') by exact (KM_of _ mem m' m'' HRO MU HREL).
  assert (HO' : OUTS g nm tk dp m'')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM (munch_SWIN g _ _ _ MU FW)
      HREL HO).
  assert (D1 : disjoint_from [(g_S g - 368 - 16, g_S g - 368)] (spk g 130) 38)
    by (cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D2 : disjoint_from [(g_S g - 368 - 16, g_S g - 368)] (spk g 226) (n_ln (g_in g) + 1))
    by (cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D3 : disjoint_from [(g_S g - 368 - 16, g_S g - 368)] (spk g 48) (n_ld (g_in g) + 1))
    by (cbn; unfold spk, fsp, SLOT_FRAME; unfold n_ld in *; lia).
  assert (D4 : disjoint_from [(g_S g - 368 - 16, g_S g - 368)] (spk g 176) 8)
    by (cbn; unfold spk, fsp, SLOT_FRAME; lia).
  split; [split|split].
  - apply (IRb_keep g nm tk dp regs mem R' m'' _ HI KMm HO' D1 D2 D3); rewrite HG;
      first [reflexivity | rewrite R9; reflexivity | rewrite R18; reflexivity | rewrite R22; reflexivity].
  - exact R0.
  - unfold q64 in HQ |- *. apply (KMm _ _ ltac:(rewrite length_le8; exact D4) HQ).
  - rewrite HG. reflexivity.
Qed.

End J02.
