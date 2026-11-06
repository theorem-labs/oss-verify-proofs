(* Segment P01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13598, 0x135ac], K13598 -> K135b0
   (memset(sp+40, 0, 35) on `first`, then reac_identity_init on the id at sp+154). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. S_P01 is CHANGED here: SlotInv.v keeps K13598 at 0x13598 (the
   four branches into it and the 0x13594 fall-through land there), so v1.9's new memset of `first` (fuzz_ctrl.c
   v1.9.0:681-683; plain segment table v190-segment-table-plain.md (a working note, not in this delivery), whose alignment pc
   0x135a8 puts it into S_A02 / S_A03 / S_R23 / S_R24 instead) is the head of this segment. New walk (v1.9.0
   listing): 0x13598 `addi a0,sp,40`, 0x1359c `li a2,35`, 0x135a0 `li a1,0`, 0x135a4 `jal memset` (memset_contract,
   writes [sp+40, sp+75)), then the v1.8 pair 0x135a8 `addi a0,sp,154` (id 138 -> 154), 0x135ac `jal
   reac_identity_init` (writes [sp+154, sp+192)); exit K135b0 (renamed from K135a0, pc 0x135a0 -> 0x135b0).
   Frame 1920 -> 1936. Statements: seg_P01 names K135b0 for K135a0 (SlotInv.v's rename; the cut's body is v1.8's
   K135a0 body); p01_evt runs from 0x13598 to 0x135b0 and takes memset_contract and the 35 cells at sp+40. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv memset_c reac_identity_init_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b3.
Import ListNotations.
Open Scope Z_scope.

Lemma p01_evt : memset_contract -> reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (jf idb : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    rw_cells rsegs m (spv + 40) [Cells.CB 35 jf] ->
    rw_cells rsegs m (spv + 154) [Cells.CB 38 idb] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x135b0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (spv + 154))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x135b0) fc None m' (seg_rom rsegs) /\
         munch [(spv + 40, spv + 75); (spv + 154, spv + 192)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 154) (repeat (Z_to_bv 8 0) 38))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13598) fc None m (seg_rom rsegs)).
Proof.
  intros MSET IC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv jf idb -> Hlo Hsp Hev HCf HC MI.
  (* 0x13598 .. 0x135a4: memset(sp+40, 0, 35) *)
  do 4 step.
  eapply evt_cut.
  { eapply MSET with (junk := jf); [ | exact MI].
    rewrite !MState.unsigned_lit by lia. exact HCf. }
  intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 &
              E1 & MU1 & WM1 & MI1 & _).
  subst ms1.
  rewrite !MState.unsigned_lit in MU1 by lia.
  replace (spv + 40 + 35) with (spv + 75) in MU1 by lia.
  replace (ret_pc (Z_to_bv 64 0x135a8)) with (Z_to_bv 64 0x135a8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (HC1 : rw_cells rsegs m1 (spv + 154) [Cells.CB 38 idb]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ HC MU1 WM1). cbn [Cells.cells_size Cells.csize Nat.add disjoint_from].
    split; [lia | exact I]. }
  (* 0x135a8 .. 0x135ac: reac_identity_init(sp+154) *)
  step. step.
  eapply evt_cut.
  { eapply IC with (id := spv + 154) (idb := idb);
      [ first [reflexivity | apply bv_eq; reflexivity] | lia | intros _; split; [lia | exact HC1] | exact MI1 ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & _ & Hz).
  subst ms'. specialize (Hz ltac:(lia)).
  replace (spv + 154 + 38) with (spv + 192) in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x135b0)) with (Z_to_bv 64 0x135b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split.
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. unfold sub_fp. cbn [outside]. intros y [Hy _]. split; [exact Hy | exact I].
    - eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros y [_ [Hy _]].
      split; [exact Hy | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WMc)|].
  exact (sl_rw_bytes _ _ _ _ Hz).
Qed.

Section P01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MSET : memset_contract.
Hypothesis INIT : reac_identity_init_contract.

Lemma seg_P01 : Hcut B APIf ra (Inv_K135b0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13598 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HPB).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 40) 35 ST ltac:(lia) ltac:(lia)) as (jf & HCf).
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 154) 38 ST ltac:(lia) ltac:(lia)) as (idb & HC).
  eapply (b3_mid B APIf ra empty FF g [] L A regs mem md _
    [(g_S g - 1936 + 40, g_S g - 1936 + 75); (g_S g - 1936 + 154, g_S g - 1936 + 192)]);
    [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (b3_fp g _ x _ Hx O).
    repeat (apply Forall_cons; [cbn [fst snd]; unfold SLOT_K, SLOT_STACK; lia|]). apply Forall_nil.
  - rewrite sl_mkR_of.
    apply (p01_evt MSET INIT) with (spv := g_S g - 1936) (jf := jf) (idb := idb);
      [exact Hsp | lia | lia | lia | exact HCf | exact HC | exact (mem_inv_normalize rsegs mem)].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ).
    injection HE; intros; subst.
    destruct HPB as ((Hc & H21 & H27) & HOUR).
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [split; [exact Hc|] | ] | ].
    + unfold rg in *. rewrite !(sl_getr_eqv _ _ _ Hx). split; [exact H21 | exact H27].
    + unfold OURb, spk, fsp, SLOT_FRAME in *.
      apply (bytes_at_transport rsegs _ mem m' _ _ HOUR MU'). cbn [disjoint_from]. rewrite OUR_length.
      split; [lia|]. split; [lia | exact I].
    + unfold IDB, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) HZ).
Qed.

End P01.
