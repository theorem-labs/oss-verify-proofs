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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sj Tac_sb3b.
Import ListNotations.
Open Scope Z_scope.

Lemma kB29a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x134d8) x2 x3 x4 x5 x6 x7 x8 x9 x22 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           (v_add x20 x21) x21 x22 x23 x24 x25 (v_sub x18 x21) x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 0x15440) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x134c8) fc None m ro).
Proof.
  intros. step. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma kB29b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 i nr : Z),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 40 < 2 ^ 64 -> x19 = Z_to_bv 64 i -> 0 <= i < 64 -> 0 <= nr <= 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 32)) 8 = Some (le8 (Z_to_bv 64 nr)) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 nr) x11 x12 x13 x14 x15 x16 x17 x18
                           (Z_to_bv 64 (i + 1)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 (if i + 1 =? nr then 0x134e4 else 0x12fc4)) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x134d8) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 i nr E2 H0 H1 E19 Hi Hn RD.
  subst x2 x19.
  step. step. step.
  rewrite fb_addiw by lia. rewrite sj_bv_eqb by lia.
  destruct (Z.eqb_spec (i + 1) nr); cbn [negb]; apply evt_done; reflexivity.
Qed.

Lemma b29_add : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b. unfold v_add. fb_arith. Qed.

Lemma b29_sub : forall a b, v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b. unfold v_sub. fb_arith. Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_B29 : forall i,
  Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) (S i) -> Hcut B APIf ra (Inv_K134e4 B APIf ra empty) ->
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i.
Proof.
  intros i HX HE g c (pl & HC).
  eapply (cut_open B APIf ra empty); [exact HC|].
  intros L A regs mem md HF HP (Hi & E19 & HNR & HG16 & HHW & HID & E20 & E21 & E18 & E22).
  assert (Hin : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (sj_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  pose proof (rec_k_range (g_in g) i) as Hk.
  pose proof (rec_bounds (g_in g) i) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
  pose proof (rec_c_range (g_in g) (S i)) as RC.
  pose proof (nrec_range (g_in g)) as RN. change (nrec (g_in g)) with (NR g) in RN.
  pose proof HF as (HGV & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  eapply (run_to B APIf ra empty FF); [exact HF | apply kB29a | intros regs_c HG].
  apply (fb_free_call B APIf ra empty FF g (2 * Z.of_nat i + 2) [] [] L A regs mem md regs_c p
    (rec_k (g_in g) i)).
  - rewrite Ep. exact HF.
  - rewrite Ep. exact HP.
  - exact Hp.
  - lia.
  - rg HG.
  - rg HG.
  - rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG, Ep. exact E22.
  - intros L' A' regs' mem' md' HF' HP' RP' STK _.
    change ([] ++ []) with (@nil (Z * Z)) in HF', HP'.
    replace (getr regs_c 1) with (Z_to_bv 64 0x134d8) by (rewrite HG; reflexivity).
    pose proof (sj_segs B APIf ra empty FF) as ES. rewrite ES in STK.
    assert (KP : forall a bs, fsp g <= a -> bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Ha H; exact (fb_keep mem mem' (fsp g) a bs STK Ha H)).
    assert (HNR' : NRb g mem') by (apply KP; [unfold spk; lia | exact HNR]).
    assert (HG16' : G16 g mem') by (apply KP; [unfold spk; lia | exact HG16]).
    assert (HID' : IDb g (S i) mem') by (apply KP; [unfold spk; lia | exact HID]).
    assert (HHW' : HWb g (S i) mem').
    { destruct HHW as (W1 & W2 & W3). split; [|split]; (apply KP; [unfold spk; lia|]); assumption. }
    assert (C19 : getr regs' 19 = Z_to_bv 64 (Z.of_nat i)).
    { etransitivity; [exact (RP' 19 ltac:(unfold callee_saved; lia))|]. rewrite HG. exact E19. }
    assert (C20 : getr regs' 20 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i))).
    { etransitivity; [exact (RP' 20 ltac:(unfold callee_saved; lia))|].
      transitivity (v_add (getr regs 20) (getr regs 21)); [rewrite HG; reflexivity|].
      rewrite E20, E21, b29_add. f_equal. lia. }
    assert (C26 : getr regs' 26 = Z_to_bv 64 (g_n g - rec_c (g_in g) (S i))).
    { etransitivity; [exact (RP' 26 ltac:(unfold callee_saved; lia))|].
      transitivity (v_sub (getr regs 18) (getr regs 21)); [rewrite HG; reflexivity|].
      rewrite E18, E21, b29_sub. f_equal. unfold g_n. lia. }
    pose proof HF' as (_ & Hsp' & _).
    eapply (run_to B APIf ra empty FF); [exact HF' | | intros regs2 HG2].
    { eapply kB29b with (sp0 := fsp g) (i := Z.of_nat i) (nr := NR g).
      - exact Hsp'.
      - unfold fsp, SLOT_FRAME. unfold SLOT_K, SLOT_STACK in HSc. lia.
      - unfold fsp, SLOT_FRAME. lia.
      - exact C19.
      - lia.
      - lia.
      - apply sj_bytes_le8. exact HNR'. }
    assert (D19 : getr regs2 19 = Z_to_bv 64 (Z.of_nat i + 1)) by (rewrite HG2; reflexivity).
    assert (D20 : getr regs2 20 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i))) by (rewrite HG2; exact C20).
    assert (D26 : getr regs2 26 = Z_to_bv 64 (g_n g - rec_c (g_in g) (S i))) by (rewrite HG2; exact C26).
    assert (HF2 : FR B APIf ra empty g (2 * Z.of_nat i + 2) [] L' A' regs2 mem' md')
      by (apply (FR_regs B APIf ra empty _ _ _ _ _ regs'); [exact HF' | rg HG2 | rg HG2 | rg HG2]).
    destruct (Z.eqb_spec (Z.of_nat i + 1) (NR g)) as [EN|EN].
    + apply HE. unfold Inv_K134e4. replace (2 * NR g) with (2 * Z.of_nat i + 2) by lia.
      apply (cut_close B APIf ra empty _ _ _ _ _ L' A'); [exact HF2 | exact HP' |].
      assert (ENn : nrecn (g_in g) = S i) by (unfold nrecn; change (nrec (g_in g)) with (NR g); lia).
      unfold CB, CUR, cT, NRn. rewrite ENn.
      split; [|rewrite D19, EN; reflexivity].
      split; [lia|]. split; [exact HNR'|]. split; [exact HG16'|]. split; [exact HHW'|].
      split; [|exact HID']. split; [unfold g_n in *; lia|]. split; [exact D20 | exact D26].
    + apply HX. unfold Inv_K12fc4_at. replace (2 * Z.of_nat (S i)) with (2 * Z.of_nat i + 2) by lia.
      apply (cut_close B APIf ra empty _ _ _ _ _ L' A'); [exact HF2 | exact HP' |].
      split; [|split; [|exact HID']].
      * split; [lia|]. split; [rewrite D19; f_equal; lia|].
        split; [exact HNR'|]. split; [exact HG16' | exact HHW'].
      * split; [unfold g_n in *; lia|]. split; [exact D20 | exact D26].
Qed.

End S.
