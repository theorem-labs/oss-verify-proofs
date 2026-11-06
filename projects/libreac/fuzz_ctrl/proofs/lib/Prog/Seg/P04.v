(* Segment P04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x135f0, 0x13610], K135f0 -> K13614
   (the reply's -1 passes 0x135f4; reac_ctrl_identity_fragment with fr = 0: FgRefuse, -1, no write). The
   fragment contract is the WIP statement reac_ctrl_identity_fragment_contract, taken as a Section Hypothesis. *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. S_P04 is IDENTICAL-RENUMBER (plain segment table
   v190-segment-table-plain.md (a working note, not in this delivery) 5a / 7a): the same 9 instructions at pc +0x10 (the abort
   target 0x13de4 -> 0x13e18 is not taken), frag sp+66 -> sp+82, pa / pp / pn sp+1776 / 1736 / 1672 -> sp+1792 /
   1752 / 1688, frame 1920 -> 1936; n - c in s11 (CUR). Statements: seg_P04 names K135f0 / K13614 for K135e0 /
   K13604 (SlotInv.v's renames). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcFrag reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b3.
Import ListNotations.
Open Scope Z_scope.

Lemma p04_refuse : forall f pa pp pn len st g, fg_class f 0 pa pp pn len st g = FgRefuse.
Proof.
  intros f pa pp pn len st g. unfold fg_class. replace (0 =? 0) with true by reflexivity.
  rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma p04_evt : reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (-1) -> 80 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    stk rsegs m (spv - 80) spv -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13614) sp gp tp t0' t1' t2' (Z_to_bv 64 (-1)) s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13614) fc None m' (seg_rom rsegs) /\
         munch [(spv - 80, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x135f0) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv -> -> Hlo Hsp Hev ST MI.
  step. step. if_false.
  do 7 step.
  eapply evt_cut.
  { eapply FRAG with (f := spv + 82) (fr := 0) (len := 0) (pa := spv + 1792) (pp := spv + 1752) (pn := spv + 1688)
      (st := repeat (Z_to_bv 8 0) 72) (g := repeat (Z_to_bv 8 0) 50).
    all: first [ reflexivity | lia | assumption | (intros _ Hf; exfalso; apply Hf; reflexivity)
               | (rewrite MState.unsigned_lit by lia; first [exact Hev | unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME; exact ST]) ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & _).
  subst ms'.
  rewrite p04_refuse in MUc |- *. cbn [fg_ret fg_fp] in MUc |- *.
  unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME in MUc. rewrite MState.unsigned_lit in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x13614)) with (Z_to_bv 64 0x13614) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MUc | exact WMc].
Qed.

Section P04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FRAG : reac_ctrl_identity_fragment_contract.

Lemma seg_P04 : Hcut B APIf ra (Inv_K13614 B APIf ra empty) -> Hcut B APIf ra (Inv_K135f0 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HP0 & HPZ & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (stk_split rsegs _ _ (g_S g - 1936 - 80) _ ST ltac:(lia)) as [_ ST2].
  destruct (stk_split rsegs _ _ (g_S g - 1936) _ ST2 ltac:(lia)) as [ST3 _].
  eapply (b3_mid B APIf ra empty FF g [] L A regs mem md _ [(g_S g - 1936 - 80, g_S g - 1936)]);
    [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (b3_fp g _ x _ Hx O).
    repeat (apply Forall_cons; [cbn [fst snd]; unfold SLOT_K, SLOT_STACK; lia|]). apply Forall_nil.
  - rewrite sl_mkR_of.
    apply (p04_evt FRAG) with (spv := g_S g - 1936);
      [exact Hsp | exact H10 | lia | lia | exact H16 | exact ST3 | exact (mem_inv_normalize rsegs mem)].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _).
    injection HE; intros; subst.
    destruct HP0 as (((Hc & H21 & H27) & HOUR) & HID & HFG). destruct HPZ as (HZ1 & HZ2).
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    unfold P0, PB, CUR, PZ, OURb, IDB, FGB, b8, rg, spk, fsp, SLOT_FRAME in *.
    rewrite !(sl_getr_eqv _ _ _ Hx).
    refine (conj (conj (conj (conj Hc (conj H21 H27)) _) (conj _ _)) (conj (conj _ _) (conj eq_refl eq_refl))).
    + apply (bytes_at_transport rsegs _ mem m' _ _ HOUR MU'). cbn [disjoint_from]. rewrite OUR_length.
      split; [lia | exact I].
    + apply (bytes_at_transport rsegs _ mem m' _ _ HID MU'). unfold RcIdentModel.ID0. rewrite repeat_length.
      unfold RcIdentModel.ID_SIZE. cbn [disjoint_from]. split; [lia | exact I].
    + apply (bytes_at_transport rsegs _ mem m' _ _ HFG MU'). unfold z72. rewrite repeat_length. cbn [disjoint_from].
      split; [lia | exact I].
    + apply (bytes_at_transport rsegs _ mem m' _ _ HZ1 MU'). cbn [disjoint_from length]. split; [lia | exact I].
    + apply (bytes_at_transport rsegs _ mem m' _ _ HZ2 MU'). rewrite repeat_length. cbn [disjoint_from].
      split; [lia | exact I].
Qed.

End P04.
