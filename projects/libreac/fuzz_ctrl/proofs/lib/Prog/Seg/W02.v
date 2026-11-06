(* Segment W02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13d4c, 0x13d54], declaration_of(row_i, sp+1792).
   K13d4c -> K13d58.
   libreac v1.9.0 (table 5a S_W02: IDENTICAL-RENUMBER, OLD 0x13d1c .. 0x13d24): pcs, the declaration buffer
   1776 -> 1792 (check_ports `first` / `a`), frame 1920 -> 1936; the rows are CAT + 296 i with CAT = 0x1ed30
   (SlotModel.v, checked by reflexivity), inside frame_RELRO's first block; cuts K13d1c -> K13d4c, K13d28 -> K13d58
   (SlotInv.v's renames), so seg_W02 is stated on the renamed cuts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcDecl RcMatchLib SlotModel SlotInv declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma w02_img_rows : forall i, (i < 11)%nat ->
  Image.image_bytes rsegs (CAT + CAT_ROW * Z.of_nat i) 296 = Some (rowb (Z.of_nat i)).
Proof.
  intros i Hi. unfold rowb, img.
  destruct (Image.image_bytes rsegs (CAT + CAT_ROW * Z.of_nat i) 296) eqn:E; [reflexivity|].
  exfalso.
  assert (H : forallb (fun i => match Image.image_bytes rsegs (CAT + CAT_ROW * Z.of_nat i) 296 with
                                | Some _ => true | None => false end) (seq 0 11) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)). rewrite E in H. discriminate.
Qed.

Lemma w02_rows_ok : forall i, (i < 11)%nat -> decl_ok (rowb (Z.of_nat i)) = true.
Proof.
  intros i Hi.
  assert (H : forallb (fun i => decl_ok (rowb (Z.of_nat i))) (seq 0 11) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. exact (H i ltac:(apply in_seq; lia)).
Qed.

Lemma w02_row_len : forall i, (i < 11)%nat -> length (rowb (Z.of_nat i)) = 296%nat.
Proof. intros i Hi. exact (Image.image_bytes_length rsegs 296 _ _ (w02_img_rows i Hi)). Qed.

Lemma kW02 : declaration_of_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
    x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp0 r lo : Z) (row ob : list byte),
  x2 = Z_to_bv 64 sp0 -> x23 = Z_to_bv 64 r ->
  0 <= r -> r mod 8 = 0 -> r + 296 <= sp0 - 64 -> 0 <= lo -> lo + 64 <= sp0 -> sp0 + 1936 < 2 ^ 64 ->
  stk rsegs m lo sp0 -> length row = 296%nat -> bytes_at rsegs m r row ->
  rw_cells rsegs m (sp0 + 1792) [CB 32 ob] -> mem_inv rsegs m -> decl_ok row = true ->
  Exec.evt rsegs
    (fun ms' => exists R m', ms' = MS R F (Z_to_bv 64 0x13d58) fc None m' (seg_rom rsegs) /\
       (getr R 10 = Z_to_bv 64 1 /\ getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\ getr R 4 = x4 /\
        getr R 8 = x8 /\ getr R 9 = x9 /\ getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\
        getr R 21 = x21 /\ getr R 22 = x22 /\ getr R 23 = Z_to_bv 64 r /\ getr R 24 = x24 /\ getr R 25 = x25 /\
        getr R 26 = x26 /\ getr R 27 = x27 /\
        munch [(sp0 - 64, sp0); (sp0 + 1792, sp0 + 1792 + 32)] m m' /\ wmono rsegs m m' /\
        bytes_at rsegs m' (sp0 + 1792) (decl row)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d4c) fc None m (seg_rom rsegs)).
Proof.
  intros DECL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m sp0 r lo row ob E2 E23 H0 H8 H1 H2 H3 H4 ST HL HB HW HMI Hok.
  subst x2 x23. step. step. step.
  eapply evt_cut.
  { eapply DECL with (lo := lo) (row := row) (ob := ob); unfold DECLARATION_OF_FRAME; rewrite ?unsigned_lit by lia.
    - exact ST.
    - lia.
    - exact H8.
    - exact HL.
    - exact HB.
    - exact HW.
    - lia.
    - lia.
    - lia.
    - exact HMI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST' & RW & BA).
  subst ms'. rewrite (b8_ret_pc 0x13d58) by lia. rewrite Hok in RW.
  rewrite !unsigned_lit in RW by lia.
  apply evt_done. eexists _, _. split; [reflexivity|]. rewrite Hok.
  repeat (split; [reflexivity|]).
  split; [intros x Hx; apply MU; cbn [outside] in Hx |- *; unfold DECLARATION_OF_FRAME;
          rewrite !unsigned_lit by lia; destruct Hx as (Hx1 & Hx2 & _); split; [lia | split; [lia | exact I]]|].
  split; [exact WM|]. exact (sl_rw_bytes _ _ _ _ RW).
Qed.

Ltac b8_out := cbn [outside]; repeat split; try exact I; lia.

Section W02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis DECL : declaration_of_contract.

Lemma seg_W02 : forall j i : nat, Hat2 B APIf ra (Inv_K13d58_at B APIf ra empty) j i ->
  Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i.
Proof.
  intros j i H1 g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP HWB.
  pose proof HWB as ((HC7 & Hsel) & Hi & H23 & H8 & Hprev).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HF) as HST.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & HREL & _).
  pose proof alloc_ceiling_value as HAC. pose proof sl_ceil as HSL.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Hin : In (phi, t_len (g_in g) j) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_block_pos B APIf ra empty g _ L A regs mem md _ _ HF Hin) as [Hph1 Hph2].
  set (r := CAT + CAT_ROW * Z.of_nat i) in *.
  assert (Hr : r = 0x1ed30 + 296 * Z.of_nat i) by reflexivity.
  assert (Hrow : bytes_at rsegs (normalize rsegs mem) r (rowb (Z.of_nat i))).
  { apply (cm_bytes_img rsegs _ r 296); [exact (w02_img_rows i ltac:(lia)) | lia | lia |].
    intros a Ha. apply (b8_relro_norm B APIf ra empty FF); [exact HREL | exact HMI | lia]. }
  destruct (sl_rw_of_stk (normalize rsegs mem) (g_S g - 65536) (g_S g) (g_S g - 1936 + 1792) 32 HST
              ltac:(lia) ltac:(lia)) as (ob & HOB).
  eapply (b8_mid B APIf ra empty FF g _ L A regs mem md (Z_to_bv 64 0x13d4c)
            [(g_S g - 1936 - 64, g_S g - 1936); (g_S g - 1936 + 1792, g_S g - 1936 + 1792 + 32)]).
  - exact HF.
  - exact HP.
  - intros x Hx O. unfold SLOT_K, SLOT_STACK. destruct (Z_le_dec (g_S g - 1936 - 64) x); destruct (Z_lt_dec x (g_S g - 1936));
      destruct (Z_le_dec (g_S g - 1936 + 1792) x); destruct (Z_lt_dec x (g_S g - 1936 + 1792 + 32)); try lia;
      exfalso; apply O; b8_out.
  - rewrite sl_mkR_of. eapply (kW02 DECL) with (sp0 := g_S g - 1936) (r := r) (lo := g_S g - 65536) (ob := ob).
    + exact Hsp.
    + exact H23.
    + lia.
    + rewrite Hr. Z.div_mod_to_equations. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + apply (b8_stk_sub _ _ _ _ _ _ HST); lia.
    + exact (w02_row_len i ltac:(lia)).
    + exact Hrow.
    + exact HOB.
    + exact (mem_inv_normalize rsegs mem).
    + exact (w02_rows_ok i ltac:(lia)).
  - intros ms (R & m' & -> & (H10 & E2 & E3 & E4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _)).
    exists R, (Z_to_bv 64 0x13d58), m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [rewrite E2; symmetry; exact Hsp|]. split; [exact E3 | exact E4].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HF'.
    destruct HQ as (R1 & m1 & E & (H10 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 &
                    E26 & E27 & MU & WM & BA)).
    injection E; intros; subst.
    apply H1. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A); [exact HF' | exact HP |].
    assert (G : forall r0, getr regs' r0 = getr R1 r0) by (intros r0; apply sl_getr_eqv; exact Hx).
    split; [split; [split|]|].
    + apply (b8_CC7_munch g j phi regs' mem m'
               [(g_S g - 1936 - 64, g_S g - 1936); (g_S g - 1936 + 1792, g_S g - 1936 + 1792 + 32)]);
        [| exact MU' |].
      * apply (b8_CC7_regs _ _ _ regs); [exact HC7 | rewrite G; assumption ..].
      * intros x Hx'. unfold spk, fsp, SLOT_FRAME in Hx'. b8_out.
    + exact Hsel.
    + split; [exact Hi|]. split; [unfold rg; rewrite G, E23; reflexivity|].
      split; [unfold rg; rewrite G, E8; exact H8 | exact Hprev].
    + split; [unfold rg; rewrite G; exact H10|].
      replace (spk g 1792) with (g_S g - 1936 + 1792) by (unfold spk, fsp, SLOT_FRAME; lia).
      exact (proj2 (bytes_at_rel rsegs m' m1 _ _ Hrel) BA).
Qed.

End W02.
