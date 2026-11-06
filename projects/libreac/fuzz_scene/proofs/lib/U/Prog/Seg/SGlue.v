From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv STac.
Import ListNotations.
Open Scope Z_scope.

Section Glue.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Abbreviation API := (APIf rc).
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR (APIf rc)).

Lemma sg_segs : ms_segs B = rsegs.
Proof. destruct FF as (H & _). exact H. Qed.

Lemma sg_md : forall L A mem md, MR L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof. intros L A mem md H. exact (KindBGlue.kb_md B API L A mem md H). Qed.

Lemma cut_open : forall g pc km hb P c (Q : config -> Prop),
  CUTST B APIf ra empty g pc km hb P c ->
  (forall L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) Q) ->
  SR segs c Q.
Proof.
  intros g pc km hb P c Q (L & A & regs & mem & md & -> & H1 & H2 & H3) K. exact (K L A regs mem md H1 H2 H3).
Qed.

Lemma cut_close : forall g pc km hb (P : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
  CUTST B APIf ra empty g pc km hb P (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md).
Proof.
  intros g pc km hb P L A regs mem md H1 H2 H3. exists L, A, regs, mem, md. split; [reflexivity|].
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma FR_MR : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md -> MR L A mem md.
Proof. intros g km hb L A regs mem md (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma sg_GV_S : forall g, GV B empty g -> spZ (g_regs g) = g_S g /\ alloc_ceiling + SLOT_K <= g_S g <= 2 ^ 47.
Proof.
  intros g (_ & _ & _ & _ & H1 & H2 & _ & H3 & _). unfold spZ. rewrite H3.
  pose proof alloc_ceiling_value. unfold SLOT_K, SLOT_STACK in *. rewrite unsigned_lit by lia. lia.
Qed.

Lemma post_FR : forall g km L A regs0 regs mem md,
  FR B APIf ra empty g km [] L A regs0 mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved (g_regs g) regs ->
  Post B APIf ra g (mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md).
Proof.
  intros g km L A regs0 regs mem md HF HP H10 HRP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & HWF & HBD & HIN & HVM & HFA & HFI & HFB & HER & HSN & HRES
    & HSW).
  destruct (sg_GV_S g HGV) as [HSP HS].
  exists L, A, regs, mem, md. split; [reflexivity|].
  split.
  - unfold lib_post. split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|].
    split; [exact H10|]. split; [exact HRP|]. split; [exact HVM|].
    split.
    { intros q k Hq. pose proof (ss_blocks_in (g_L g) (g_A g) q k Hq) as Hb.
      apply (Permutation_in _ (Permutation_sym HP)) in Hb.
      destruct (ss_blk_of L A _ _ Hb) as (q' & Hq' & E). exists q'. split; [exact Hq' | exact E]. }
    split.
    { intros a Ha Hn. unfold lib_scratch in Hn. rewrite HSP in Hn.
      assert (N1 : ~ (g_S g - SLOT_K <= a < g_S g)) by (unfold SLOT_K; tauto).
      assert (N2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (HFA a Ha N1 N2) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros a H1 H2 H3 H4. destruct (HFI a H1 H2 H3 H4) as [E1 E2]. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq _ Hi. apply (HFB (ptr_addr (g_L g) q) k i); [apply ss_blocks_in; exact Hq | exact Hi]. }
    intros a [Ha|Ha]; [apply HSW; rewrite HSP in Ha; unfold SLOT_K; exact Ha | apply HER; exact Ha].
  - split; [exact HSN|]. split; [exact HMI|].
    split.
    + exact (resb_end (g_b g) km A HRES).
    + intros i Hi. destruct HGV as (_ & [[Hn _]|[_ Hp]] & _); [lia|].
      apply (HFB (g_p g) (g_n g) i Hp Hi).
Qed.

End Glue.
