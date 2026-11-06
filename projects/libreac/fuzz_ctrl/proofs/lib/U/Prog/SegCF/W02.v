(* Segment W02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x14064, 0x1408c], row i of row_of_block:
   T70 (`mulh`/`srai 63` of i * 296, i in s3) and T71 (`sltu` carry of s4 = T' + 296 i) not taken (CATU, i <= 10), then
   declaration_of(row_i, sp+1792) (DECL; the row from frame_RELRO, decl_ok by declaration_of_rows). U14064 -> U14090.
   The run is checked for each i = 0 .. 10. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Ltac w02_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

Lemma w02_evt : declaration_of_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv i : Z) (row ob : list byte),
    sp = Z_to_bv 64 spv -> 16 <= spv -> spv + 1936 <= 2 ^ 64 ->
    s3 = Z_to_bv 64 i -> 0 <= i <= 10 -> s10 = Z_to_bv 64 0x1fcc8 -> s9 = Z_to_bv 64 (0x1fcc8 + 296 * i) ->
    stk rsegs m (spv - 16) spv -> length row = 296%nat -> bytes_at rsegs m (0x1fcc8 + 296 * i) row ->
    rw_cells rsegs m (spv + 1792) [CB 32 ob] -> mem_inv rsegs m -> 0x1fcc8 + 296 * i + 296 <= spv - 16 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x14090) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if decl_ok row then 1 else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (0x1fcc8 + 296 * i)) s5 s6 s7 s8 s9 s10 s11
                       t3' t4' t5' t6')
                  F (Z_to_bv 64 0x14090) fc None m' (seg_rom rsegs) /\
         munch [(spv - 16, spv); (spv + 1792, spv + 1792 + 32)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (spv + 1792) [CB 32 (if decl_ok row then decl row else ob)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14064) fc None m (seg_rom rsegs)).
Proof.
  intros DC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv i row ob -> Hs0 Hs1 -> Hi -> -> ST Hrow HB HO MI Hlo.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10)
    by lia.
  destruct Ei as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
  (step; step; step; step; step; w02_if false; step; step; step; w02_if false; step; step; step;
   eapply evt_cut;
   [ eapply DC with (lo := spv - 16) (row := row) (ob := ob);
     unfold DECLARATION_OF_FRAME; rewrite ?MState.unsigned_lit by lia;
     first [ exact ST | lia | exact Hrow | exact HB | exact HO | exact MI | (vm_compute; reflexivity)
           | (left; lia) | (right; lia) ]
   | intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                 E & MU & WM & MI' & ST' & HC & HR);
     subst ms';
     replace (ret_pc (Z_to_bv 64 0x14090)) with (Z_to_bv 64 0x14090)
       by (symmetry; apply ret_pc_even; [lia | reflexivity]);
     apply evt_done; exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m';
     rewrite ?MState.unsigned_lit in HC by lia;
     unfold DECLARATION_OF_FRAME in MU; rewrite ?MState.unsigned_lit in MU by lia;
     split; [reflexivity|];
     split; [first [exact MU | (replace (spv + 1792 + 32) with (spv + 1824) in MU by lia; exact MU)]|];
     split; [exact WM | exact HC] ]).
Qed.

Section W02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis DECL : declaration_of_contract.
Hypothesis DROWS : declaration_of_rows.

Lemma seg_W02 : forall j i : nat, Hat2 B APIf ra (Inv_U14090_at B APIf ra empty) j i ->
  Hat2 B APIf ra (Inv_U14064_at B APIf ra empty) j i.
Proof.
  intros j i H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HWB).
  pose proof HWB as (HRS & Hi & H26 & H19 & H25 & Hq & Hne).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & HREL & _).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u8_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  destruct (DROWS i ltac:(lia)) as (row & Himg & Hok & _).
  assert (Erow : rowb (Z.of_nat i) = row).
  { unfold rowb, img. change (CAT + CAT_ROW * Z.of_nat i) with (BOX_CATALOGUE + 296 * Z.of_nat i).
    rewrite Himg. reflexivity. }
  assert (HB : bytes_at rsegs (normalize rsegs mem) (0x1fcc8 + 296 * Z.of_nat i) row).
  { apply (u8_relro_bytes B APIf ra empty FF mem _ 296 row HREL); [exact Himg | lia | lia]. }
  pose proof (Image.image_bytes_length rsegs 296 _ row Himg) as Hrow.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1792) 32 ST ltac:(lia) ltac:(lia)) as (ob & HO).
  eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _
            [(g_S g - 1936 - 16, g_S g - 1936); (g_S g - 1936 + 1792, g_S g - 1936 + 1792 + 32)]);
    [exact HFR | exact HP | u8_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (w02_evt DECL) with (spv := g_S g - 1936) (i := Z.of_nat i) (row := row) (ob := ob);
      [exact Hsp | lia | lia | exact H19 | lia | exact H26 | exact H25 | | exact Hrow | exact HB | exact HO
      | exact (mem_inv_normalize rsegs mem) | lia].
    apply (u8_stk_sub _ _ _ _ _ ST); lia.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HC).
    injection HE; intros; subst.
    apply (H g). exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    destruct HRS as (HC7 & Hsel).
    assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
    split; [|split; [|split]].
    + split; [split; [|exact Hsel]|].
      { apply (u8_CC7_keep g j phi regs regs' mem m' _ HC7 HK MU'); u8_dj. }
      split; [exact Hi|].
      split; [unfold rg; rewrite HG; exact H26|].
      split; [unfold rg; rewrite HG; exact H19|].
      split; [unfold rg; rewrite HG; exact H25|].
      split; [apply (u8_q64 _ mem m' _ _ Hq MU'); u8_dj | exact Hne].
    + unfold rg. rewrite HG. reflexivity.
    + unfold rg. rewrite HG. rewrite Hok. reflexivity.
    + rewrite Hok in HC. apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)).
      unfold decl_i. try rewrite Erow. unfold spk, fsp, SLOT_FRAME.
      exact (u8_c_bytes _ _ _ HC).
Qed.

End W02.
