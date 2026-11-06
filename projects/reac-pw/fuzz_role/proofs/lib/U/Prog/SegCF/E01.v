(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 198 of its 225 lines of code are new or changed and 548 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/E01.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_pin's U/Prog/SegCF/E01.v, as libreac/fuzz_ctrl's released U/Prog/SegCF/*.v copy its
   U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the segment statements from
   SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator contracts in their cut-free
   forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment E01 of reac-pw/fuzz_role LLVMFuzzerTestOneInput (UBSan): [0x12ec0, 0x12f44], ENTRY -> K12f48
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_E01).
   The plain segment (lib/Prog/Seg/E01.v) with the UBSan numbers and the one UBSan check of this stretch:
   the prologue (0x12ec0 `addi sp,sp,-0x220`; ra, s0 .. s11 saved at S - 8 .. S - 104), the n >= 2^26 exit not
   taken (0x12ef8 `srli a2,a1,26`, 0x12efc `beqz a2`: GV bounds n below 2^26), 0x12f04 `mv s6,a0` and
   0x12f08 `beqz a1`: for the empty input 0x12f30 sets s2 = 0 and stores 0 in the frame cell sp + 0x10; else
   0x12f0c `addi a0,s6,1`, 0x12f10 `addi a2,zero,1` and the pointer-overflow check 0x12f14 `bltu a2,a0` (whose
   other side traps at 0x12f18 -> 0x14204 `unimp`), which is dead because the input block starts above 4096 and
   ends below the allocator ceiling, so data + 1 neither is 0 nor 1 nor wraps; then 0x12f1c `lbu a2,0(s6)`,
   0x12f20 `sd a2,0x10(sp)` (the flags byte into the frame cell), s2 = n - 1 and s6 = data + 1. Both paths join at
   0x12f38: s0 = 0x5000, s1 = 19744, a0 = s1, and malloc(19744) at 0x12f44 with ra = 0x12f48 through
   Tac_b1.b1_malloc_call from hb = [], whose continuation gives Inv_K12f48. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* ---- The quantities of the input cursor (SlotInv's g_fl, g_k, g_src for inp = g_in g, p = g_p g) ---- *)
Definition e01_fl (inp : list byte) : Z := match inp with [] => 0 | b :: _ => bv_unsigned b end.
Definition e01_k (inp : list byte) : Z := Z.of_nat (length inp) - Z.min 1 (Z.of_nat (length inp)).
Definition e01_src (p : Z) (inp : list byte) : Z := p + Z.min 1 (Z.of_nat (length inp)).

Lemma e01_rd0 : forall m (a : word) b l, bytes_at rsegs m (bv_unsigned a) (b :: l) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b l H.
  assert (E : a = wa (bv_unsigned a + Z.of_nat 0)).
  { unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. }
  rewrite E. rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b :: l) 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

(* 0x12ef8 `srli a2,a1,26`; 0x12efc `beqz a2`: taken for n < 2^26. *)
Lemma e01_cond : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Ltac e01_weq :=
  first [ reflexivity
        | apply e01_weq_l; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

(* A branch: keep the side the facts allow (the trap side of 0x12f14 is refuted from 0 < p). *)
Ltac e01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia)
  | _ => idtac
  end.

(* ---- The run: ENTRY to malloc's entry with ra = 0x12f48 ---- *)
Definition e01_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p : Z) (inp : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s6' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x12f48) (Z_to_bv 64 (bv_unsigned sp + -544)) gp tp t0' t1' t2' s0' s1' a0' a1' a2'
                  a3' a4' a5' a6' a7' s2' s3 s4 s5 s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x160ec) fc None m' (seg_rom rsegs) /\
    s0' = Z_to_bv 64 0x5000 /\ s1' = Z_to_bv 64 POD_PROPS /\ a0' = Z_to_bv 64 POD_PROPS /\
    s2' = Z_to_bv 64 (e01_k inp) /\ s6' = Z_to_bv 64 (e01_src p inp) /\
    Frame.munch [(bv_unsigned sp - 544, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
    bytes_at rsegs m' (bv_unsigned sp - 528) (le8 (Z_to_bv 64 (e01_fl inp))) /\
    bytes_at rsegs m' (bv_unsigned sp - 104)
      (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
       le8 s1 ++ le8 s0 ++ le8 ra).

(* The frame is carved in two: the thirteen saved registers at S - 104 (FRS) and, below them, the eight-byte
   flags cell at S - 528 with the gap above it (FRC). *)
Ltac e01_fin sp FRS FRC :=
  let SB := fresh "SB" in let SF := fresh "SF" in
  pose proof (sl_cells_bytes _ _ _ FRS) as SB;
  pose proof (sl_cells_bytes _ _ _ FRC) as SF;
  cbn [Cells.cells_bytes Cells.cbytes] in SB, SF; rewrite ?app_nil_r in SB, SF;
  apply bytes_at_app in SF; destruct SF as [SF _];
  lazymatch type of SB with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 104) in SB by lia end;
  lazymatch type of SF with bytes_at _ _ ?y _ => replace y with (bv_unsigned sp - 528) in SF by lia end;
  apply evt_done; unfold e01_post;
  do 20 eexists; split; [reflexivity|];
  split; [|split; [|split; [|split; [|split; [|split; [assumption|split; [assumption|
    split; [exact SF | exact SB]]]]]]]].

Ltac e01_eqs := unfold e01_k, e01_src, e01_fl, POD_PROPS; cbn [length]; e01_weq.

Lemma e01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (inp : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 544 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a0 = p -> bv_unsigned a1 = Z.of_nat (length inp) -> Z.of_nat (length inp) < 2 ^ 26 ->
    0 < p -> p + Z.of_nat (length inp) <= lo -> bytes_at rsegs m p inp ->
    evt rsegs (e01_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p inp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ec0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p inp ST LO HMI0 Ep Ha1 H26 Hp0 Hin Hb.
  subst p.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 104%nat ST.
  rename FR into FRS.
  carve_frame 424%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 424%nat _ [] [8%nat; 416%nat]) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  rename FR into FRC.
  do 16 step.
  if_true_by (e01_cond (bv_unsigned a1) ltac:(lia)).
  step. step.
  destruct inp as [|b0 rest]; cbn [length] in Ha1, H26, Hin.
  - (* n = 0: 0x12f30 .. 0x12f44 *)
    e01_if.
    do 6 step.
    e01_fin sp FRS FRC.
    all: e01_eqs.
  - (* n >= 1: the pointer check, the flags byte into the cell, the cursor *)
    e01_if.
    pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
    do 3 step.
    e01_if.
    do 9 step.
    e01_fin sp FRS FRC.
    all: e01_eqs.
Qed.

(* ---- The segment ---- *)
Ltac e01_rp RP Hx r :=
  etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|]; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.

Section E01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.

Lemma seg_E01 : S_E01 B APIf ra empty.
Proof.
  unfold S_E01. intros H1 g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres & Hfrm).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSK & HS47 & _ & HGsp & HGtp).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof sl_ceil as Hct.
  pose proof (ff_empty B APIf ra empty FF) as Hemp.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* The input block lies below alloc_ceiling, so below the stack window; its address is positive
     (an input block starts at 4096 or above; for the empty input the cursor is the `empty` global). *)
  assert (Hpb : 0 < g_p g /\ g_p g + g_n g <= g_S g - 65536).
  { destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hin)].
    - rewrite Hn0, Hpe, (ff_empty_val B APIf ra empty FF). lia.
    - destruct (b1_blk B APIf ra empty FF _ _ _ _ _ _ HM Hin) as (_ & Hb1 & Hb2). lia. }
  assert (Ep : bv_unsigned (YK11.getr (g_regs g) 10) = g_p g).
  { rewrite Hp. apply MState.unsigned_lit. lia. }
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = Z.of_nat (length (g_in g))).
  { rewrite Hn. apply MState.unsigned_lit. unfold g_n in *. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  assert (Hdat' : bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) (g_in g)).
  { apply (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs (g_mem g) HMI))).
    split; [lia|]. split; [unfold g_n in Hpb; lia|].
    intros k Hk. pose proof (Hdat (Z.of_nat k) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY.
    apply e01_evt with (lo := g_S g - 65536) (p := g_p g) (inp := g_in g).
    + rewrite Esp2. apply sl_stk_norm; [exact HMI | unfold SL_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + rewrite Esp2. lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + exact Ep.
    + exact En.
    + unfold g_n in Hn26. lia.
    + lia.
    + unfold g_n in Hpb. lia.
    + exact Hdat'.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s6' &
                    t3' & t4' & t5' & t6' & m'' & HE & E8 & E9 & E10 & E18 & E22 & MU & WM & SF & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB, SF.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 544, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SB) as SB'.
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SF) as SF'.
    assert (HFR : FR B APIf ra empty g [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (sl_fr_of B APIf ra empty FF) with (mem0 := g_mem g).
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact Hsn.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. exact Ha.
      - exact Hrel.
      - apply (sl_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 544) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -544)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal; lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - unfold saved_bytes, SLOT_SAVE. rewrite <- Hra. exact SB'. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x12f48) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 POD_PROPS) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g [] (g_L g) (g_A g) regs' m' (g_md g) regs' POD_PROPS);
      [exact HFR | cbn [app]; apply Permutation_refl | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10' | unfold POD_PROPS; lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 Hres16 HK HKH.
    rewrite E1. apply H1. exists res, fx, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF''|]. split; [exact HP''|].
    unfold rg. split; [exact Hres10|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [e01_rp RP Hx 22|]. split; [e01_rp RP Hx 18|].
    split.
    { apply (b1_ba_mbyte m').
      - unfold fsp, SLOT_FRAME. replace (g_S g - 544 + 0x10) with (g_S g - 528) by lia. exact SF'.
      - intros i Hi. rewrite length_le8 in Hi. apply HK. unfold fsp, SLOT_FRAME. lia. }
    split; [e01_rp RP Hx 9|]. e01_rp RP Hx 8.
Qed.

End E01.
