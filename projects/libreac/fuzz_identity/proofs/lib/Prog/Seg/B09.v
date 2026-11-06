From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb1 Tac_sj Tac_sb3b.
Import ListNotations.
Open Scope Z_scope.

Lemma kB09 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13118) x2 x3 x4 x5 x6 x7 x8 x9 x24 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x10 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 0x15440) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x1310c) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_B09 : forall i,
  Hrec B APIf ra (Inv_K13118_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1310c_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & gb & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (HB03 & HID & HBF & HRR & E24 & HLP & HPLg & HB8 & HAG & E10).
  pose proof (rec_k_range (g_in g) i) as Hk.
  assert (Hgb : In (gb, rec_k (g_in g) i + 1) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
  destruct (sj_in_blocks L A _ _ Hgb) as (p & Hp & Ep).
  eapply (run_to B APIf ra empty FF); [exact HF | apply kB09 | intros regs_c HG].
  apply (fb_free_call B APIf ra empty FF g (2 * Z.of_nat i + 2) (hb_pl g i pl) [] L A regs mem md regs_c p
    (rec_k (g_in g) i + 1)).
  - rewrite Ep. exact HF.
  - rewrite Ep. exact HP.
  - exact Hp.
  - lia.
  - rg HG.
  - rg HG.
  - rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG, Ep. exact E24.
  - intros L' A' regs' mem' md' HF' HP' RP' STK HBK.
    rewrite app_nil_r in HF', HP', HBK.
    replace (getr regs_c 1) with (Z_to_bv 64 0x13118) by (rewrite HG; reflexivity).
    pose proof (sj_segs B APIf ra empty FF) as ES. rewrite ES in STK, HBK.
    pose proof HF as (HGV & _).
    pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
    pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in HSc.
    assert (Hpl : In (pl, rec_k (g_in g) i) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
    destruct (t_block_range B APIf ra empty FF L A mem md _ _ (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF) Hpl)
      as [PL1 PL2].
    apply HX. exists pl.
    apply (cut_close B APIf ra empty _ _ _ _ _ L' A'); [exact HF' | exact HP' |].
    assert (MSK : forall a, fsp g <= a < fsp g + 368 -> mbyte rsegs mem' a = mbyte rsegs mem a)
      by (intros a Ha; apply STK; unfold fsp, SLOT_FRAME in *; lia).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + apply (fb_B03_keep g i pl regs regs' mem mem' HB03);
        [fb_cs RP' HG 19 | fb_cs RP' HG 20 | fb_cs RP' HG 21 | fb_cs RP' HG 22 | fb_cs RP' HG 23 | fb_cs RP' HG 26 |].
      intros a [Ha|[Ha|Ha]]; [apply MSK; lia | apply MSK; lia |].
      replace a with (pl + (a - pl)) by lia. apply (HBK pl (rec_k (g_in g) i)); [left; reflexivity | lia].
    + unfold IDb in *. apply (t_keep_at mem mem' _ _ HID). rewrite rec_id_length.
      intros x Hx. apply MSK. unfold spk, RcIdentModel.ID_SIZE in *. lia.
    + unfold BEF in *. apply (t_keep_at mem mem' _ _ HBF). rewrite rec_id_length.
      intros x Hx. apply MSK. unfold spk, RcIdentModel.ID_SIZE in *. lia.
    + unfold RRr in *. etransitivity; [exact (RP' 9 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact HRR.
    + unfold LPm, q64 in *. apply (t_keep_at mem mem' _ _ HLP). rewrite length_le8.
      intros x Hx. apply MSK. unfold spk in *. lia.
    + unfold AGN in *. apply (t_keep_at mem mem' _ _ HAG). rewrite rec_id_length.
      intros x Hx. apply MSK. unfold spk, RcIdentModel.ID_SIZE in *. lia.
    + etransitivity; [exact (RP' 25 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact E10.
Qed.

End S.
