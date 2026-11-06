(* Segment P02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x136ec, 0x136f8], U136ec -> U136fc
   (memset of the 72-byte frag at sp+120 to 0). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u3.
Import ListNotations.
Open Scope Z_scope.

Lemma p02_evt : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 120) [Cells.CB 72 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x136fc) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (spv + 120))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x136fc) fc None m' (seg_rom rsegs) /\
         munch [(spv + 120, spv + 192)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 120) (repeat (Z_to_bv 8 0) 72))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x136ec) fc None m (seg_rom rsegs)).
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
  replace (spv + 120 + 72) with (spv + 192) in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x136fc)) with (Z_to_bv 64 0x136fc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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

Lemma seg_P02 : Hcut B APIf ra (Inv_U136fc B APIf ra empty) -> Hcut B APIf ra (Inv_U136ec B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HPB & HID).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 120) 72 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  set (W := [(g_S g - 1936 + 120, g_S g - 1936 + 192)]).
  eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
  - intros x Hx O. apply (sl_fp1 g (g_S g - 1936 + 120) (g_S g - 1936 + 192) x);
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
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|]. split; [|split].
    + apply (u3_PB_keep g regs regs' mem m' W HPB MU').
      * unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
      * unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold IDB in *. apply (bytes_at_transport rsegs W mem m' _ _ HID MU'). rewrite u3_len_ID0.
      unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
    + unfold FGB, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) HZ).
Qed.

End P02.
