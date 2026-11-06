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

Lemma kB05 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (r : Z),
  x10 = Z_to_bv 64 r -> r = 0 \/ r = 1 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x130bc) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 r) (v_addi x21 1) x11 x12 x13
                           x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 0x15580) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x130ac) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro r E10 Hr.
  subst x10.
  destruct Hr as [-> | ->]; step; try if_false; step; step; step; apply evt_done; reflexivity.
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_B05 : forall i,
  Hrec B APIf ra (Inv_K130bc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K130ac_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (HB03 & HID & HBF & E10).
  pose proof HB03 as ((HREC & E23 & E21 & E20) & E26 & E22 & HPL).
  pose proof HREC as (HiN & _).
  pose proof (rec_k_range (g_in g) i) as Hk.
  pose proof (nrec_range (g_in g)) as RN. change (nrec (g_in g)) with (NR g) in RN.
  pose proof HF as (HGV & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  eapply (run_to B APIf ra empty FF);
    [exact HF | apply kB05 with (r := rec_r (g_in g) i); [exact E10 | exact (rec_r_range (g_in g) i)]
    | intros regs1 HG].
  assert (A10 : getr regs1 10 = v_addi (getr regs 21) 1) by (rewrite HG; reflexivity).
  rewrite E21 in A10. unfold v_addi in A10. rewrite sj_unsigned in A10 by lia.
  apply (fb_malloc_call B APIf ra empty FF g (2 * Z.of_nat i + 1) (hb_pl g i pl) L A regs mem md regs1
    (rec_k (g_in g) i + 1)).
  - exact HF.
  - exact HP.
  - rg HG.
  - rg HG.
  - rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - exact A10.
  - lia.
  - unfold hb_pl. cbn. lia.
  - unfold hb_bytes, hb_pl. cbn. lia.
  - intros L' A' regs' mem' md' res HF' HP' RP' R10 STK HBK.
    replace (getr regs1 1) with (Z_to_bv 64 0x130bc) by (rewrite HG; reflexivity).
    apply HX. exists pl, res.
    replace (2 * Z.of_nat i + 2) with (2 * Z.of_nat i + 1 + 1) by lia.
    apply (cut_close B APIf ra empty _ _ _ _ _ L' A'); [exact HF' | exact HP' |].
    assert (MSK : forall a, fsp g <= a < fsp g + 368 -> mbyte rsegs mem' a = mbyte rsegs mem a)
      by (intros a Ha; apply STK; unfold fsp, SLOT_FRAME in *; lia).
    split; [|split; [|split; [|split]]].
    + apply (fb_B03_keep g i pl regs regs' mem mem' HB03);
        [fb_cs RP' HG 19 | fb_cs RP' HG 20 | fb_cs RP' HG 21 | fb_cs RP' HG 22 | fb_cs RP' HG 23 | fb_cs RP' HG 26 |].
      intros a [Ha|[Ha|Ha]]; [apply MSK; lia | apply MSK; lia |].
      replace a with (pl + (a - pl)) by lia. apply (HBK pl (rec_k (g_in g) i)); [left; reflexivity | lia].
    + unfold IDb in *. apply (t_keep_at mem mem' _ _ HID). rewrite rec_id_length.
      intros x Hx. apply MSK. unfold spk, RcIdentModel.ID_SIZE in *. lia.
    + unfold BEF in *. apply (t_keep_at mem mem' _ _ HBF). rewrite rec_id_length.
      intros x Hx. apply MSK. unfold spk, RcIdentModel.ID_SIZE in *. lia.
    + unfold RRr. fb_cs RP' HG 9.
    + exact R10.
Qed.

End S.
