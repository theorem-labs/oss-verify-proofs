(* Segment P04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x1372c, 0x1374c], U1372c -> U13750
   (#32: reply's -1 = s0; reac_ctrl_identity_fragment(sp+120, 0, 0, sp+1792, sp+1752, sp+1688) refuses: -1, frag
   unchanged; the WIP ubsan fragment contract, frame 96). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u3.
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
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (-1) -> 96 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    stk rsegs m (spv - 96) spv -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13750) sp gp tp t0' t1' t2' (Z_to_bv 64 (-1)) s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13750) fc None m' (seg_rom rsegs) /\
         munch [(spv - 96, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1372c) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv -> -> Hlo Hsp Hev ST MI.
  step. step. if_false.
  do 7 step.
  eapply evt_cut.
  { eapply FRAG with (f := spv + 120) (fr := 0) (len := 0) (pa := spv + 1792) (pp := spv + 1752) (pn := spv + 1688)
      (st := repeat (Z_to_bv 8 0) 72) (g := repeat (Z_to_bv 8 0) 50).
    all: first [ reflexivity | lia | assumption | (intros _ Hf; exfalso; apply Hf; reflexivity)
               | (rewrite MState.unsigned_lit by lia; first [exact Hev | unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME; exact ST]) ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & _).
  subst ms'.
  rewrite p04_refuse in MUc |- *. cbn [fg_ret fg_fp] in MUc |- *.
  unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME in MUc. rewrite MState.unsigned_lit in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x13750)) with (Z_to_bv 64 0x13750) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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

Lemma seg_P04 : Hcut B APIf ra (Inv_U13750 B APIf ra empty) -> Hcut B APIf ra (Inv_U1372c B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HP0 & HPZ & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (stk_split rsegs _ _ (g_S g - 1936 - 96) _ ST ltac:(lia)) as [_ ST2].
  destruct (stk_split rsegs _ _ (g_S g - 1936) _ ST2 ltac:(lia)) as [ST3 _].
  set (W := [(g_S g - 1936 - 96, g_S g - 1936)]).
  eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (u3_fp g W x _ Hx O). unfold W.
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
    assert (HD : forall a n, 0 <= a -> Frame.disjoint_from W (g_S g - 1936 + a) n).
    { intros a n Ha. unfold W. cbn [disjoint_from]. split; [lia | exact I]. }
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split; [|split]].
    + apply (u3_P0_keep g regs regs' mem m' W HP0 MU').
      * unfold spk, fsp, SLOT_FRAME. apply HD. lia.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + apply (u3_PZ_keep g 0xee mem m' W HPZ MU'); unfold spk, fsp, SLOT_FRAME; apply HD; lia.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End P04.
