From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_si.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_sh2.
Import ListNotations.
Open Scope Z_scope.

Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CC : reac_box_catalogue_contract.

Lemma seg_I11 : Hcut B APIf ra (Inv_K13bf8 B APIf ra empty) -> Hcut B APIf ra (Inv_K13be0 B APIf ra empty).
Proof.
  intros H1 g c (nm & tk & dp & L & A & regs & mem & md & -> & HFR & HP & [HI R0] & H10).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (P1 & P2 & P3 & P4 & HMR & HRO & HSTK & HSW).
  pose proof HI as (HID & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HO & HE).
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold SLOT_K, SLOT_STACK in *.
  destruct (HO R0) as (C1 & C2 & C3).
  destruct (nmb_in _ _ _ _ _ _ HP) as (N1 & N2 & N3).
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N2) as [BT1 BT2].
  pose proof (tk_len (g_in g)) as TL.
  destruct (n_r0 _ R0) as [Wk Ft]. destruct (fits_unfold _ Ft) as (F1 & F2 & F3).
  pose proof (caps_range (g_in g)) as CR.
  pose proof (cstr_byte mem tk _ (length (n_TK (g_in g))) C2 ltac:(lia)) as RD.
  rewrite nthb_snoc_eq in RD.
  assert (WR : wr_at rsegs mem (fsp g + 176) 8).
  { split; [unfold fsp, SLOT_FRAME; lia|]. split; [unfold fsp, SLOT_FRAME; lia|]. intros i Hi.
    pose proof (HSW (fsp g + 176 + i) ltac:(unfold fsp, SLOT_FRAME; lia)) as W. unfold writable_at in W. exact W. }
  pose proof (wr_at_store_ok rsegs mem (fsp g + 176) 8 0 8 WR ltac:(lia) ltac:(lia)) as HSO.
  rewrite Z.add_0_r in HSO.
  eapply (run_close B APIf ra empty FF g _ _ L A regs mem md 0x13be0
    (KQ regs mem 0x13bf8 [(fsp g + 176, fsp g + 176 + 8)]
       (fun R m' => YK11.getr R 10 = Z_to_bv 64 CAT /\ q64 m' (spk g 176) CAT_N))); [exact HFR | |].
  - unfold rmk. rewrite R21, H10, P4.
    step. step.
    change (zxb z8) with (Z_to_bv 64 0).
    step. if_false.
    step. step. step.
    eapply (cat_call CC) with (c := fsp g + 176).
    + reflexivity.
    + unfold fsp, SLOT_FRAME. lia.
    + unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    + apply Mem.wr_at_write. exact WR.
    + intros a1' m' HB MU WM.
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [apply ret_lit; lia|]. split; [solve_keep|].
      assert (MU0 : munch [(fsp g + 176, fsp g + 176 + 8)] mem m').
      { eapply munch_trans; [|exact MU]. apply munch_write; [apply munch_refl | unfold fsp, SLOT_FRAME; lia |
          rewrite ?length_le8; cbn; unfold fsp, SLOT_FRAME; lia | rewrite ?length_le8; cbn; lia]. }
      split; [eapply munch_weaken; [|exact MU0]; intros x Hx; cbn in *; split; [lia | exact I]|].
      split; [eapply wmono_trans; [apply wmono_write; apply wmono_refl | exact WM]|].
      split; [apply (Tac_sh2.ro_agree_munch _ mem m' HRO MU0); repeat constructor; cbn [fst];
        unfold fsp, SLOT_FRAME; lia|].
      split; [reflexivity | exact HB].
  - intros R pc' mem' regs' (-> & HK & MU & WM & RO & H10' & HQ) ER.
    apply H1. eapply (close_IR B APIf ra empty FF) with (lo := fsp g + 176) (hi := fsp g + 176 + 8);
      [ | exact HFR | exact HP | exact HI | unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK; lia | right; lia |
        exact MU | exact WM | exact RO | eapply SKEEP_trans; [exact HK | exact ER] | ].
    + intros c Hc. exists nm, tk, dp. exact Hc.
    + intros HI'. split; [split; [exact HI' | exact R0]|]. split; [exact HQ | rewrite ER; exact H10'].
Qed.

End Seg.
