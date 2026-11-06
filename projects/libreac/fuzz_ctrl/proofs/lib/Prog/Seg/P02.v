(* Segment P02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x135b0, 0x135bc], K135b0 -> K135c0
   (memset of the frag at sp+82, 72 bytes, to 0). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. S_P02 is IDENTICAL-RENUMBER (plain segment table
   v190-segment-table-plain.md (a working note, not in this delivery)): the same 4 instructions at pc +0x10 (0x135a0 -> 0x135b0),
   frag sp+66 -> sp+82 (0x135b0 `addi a0,sp,82`), id sp+138 -> sp+154, frame 1920 -> 1936; n - c in s11 (CUR).
   Statements: seg_P02 names K135b0 / K135c0 for K135a0 / K135b0 (SlotInv.v's renames). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b3.
Import ListNotations.
Open Scope Z_scope.

Lemma p02_evt : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 82) [Cells.CB 72 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x135c0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (spv + 82))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x135c0) fc None m' (seg_rom rsegs) /\
         munch [(spv + 82, spv + 154)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 82) (repeat (Z_to_bv 8 0) 72))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x135b0) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv junk -> Hlo Hsp HC MI.
  do 4 step.
  eapply evt_cut.
  { eapply MSET with (junk := junk); [ | exact MI].
    rewrite !MState.unsigned_lit by lia. exact HC. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & Hz).
  subst ms'.
  rewrite !MState.unsigned_lit in MUc, Hz by lia.
  replace (spv + 82 + 72) with (spv + 154) in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x135c0)) with (Z_to_bv 64 0x135c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|].
  exact (sl_rw_bytes _ _ _ _ Hz).
Qed.

Section P02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MSET : memset_contract.

Lemma seg_P02 : Hcut B APIf ra (Inv_K135c0 B APIf ra empty) -> Hcut B APIf ra (Inv_K135b0 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HPB & HID).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 82) 72 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  eapply (b3_mid B APIf ra empty FF g [] L A regs mem md _ [(g_S g - 1936 + 82, g_S g - 1936 + 154)]);
    [exact HFR | exact HP | | | |].
  - intros x Hx O. apply (sl_fp1 g (g_S g - 1936 + 82) (g_S g - 1936 + 154) x);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
  - rewrite sl_mkR_of.
    apply (p02_evt MSET) with (spv := g_S g - 1936) (junk := junk);
      [exact Hsp | lia | lia | exact HC | exact (mem_inv_normalize rsegs mem)].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ).
    injection HE; intros; subst.
    destruct HPB as ((Hc & H21 & H27) & HOUR).
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [split; [exact Hc|] | ] | split].
    + unfold rg in *. rewrite !(sl_getr_eqv _ _ _ Hx). split; [exact H21 | exact H27].
    + unfold OURb, spk, fsp, SLOT_FRAME in *.
      apply (bytes_at_transport rsegs _ mem m' _ _ HOUR MU'). cbn [disjoint_from]. rewrite OUR_length.
      split; [lia | exact I].
    + unfold IDB, spk, fsp, SLOT_FRAME in *.
      apply (bytes_at_transport rsegs _ mem m' _ _ HID MU'). cbn [disjoint_from].
      split; [lia | exact I].
    + unfold FGB, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) HZ).
Qed.

End P02.
