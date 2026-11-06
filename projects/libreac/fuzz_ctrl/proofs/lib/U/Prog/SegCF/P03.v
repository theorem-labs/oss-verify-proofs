(* Segment P03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x136fc, 0x13728], U136fc -> U1372c
   (code byte sp+1824 = 0xee, blk sp+192 .. 223 = 0, reac_ctrl_identity_reply(0, 0, sp+1792, sp+1752, sp+1688) = -1). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u3.
Import ListNotations.
Open Scope Z_scope.

Lemma p03_le1 : le1 (Z_to_bv 64 (-18)) = [Z_to_bv 8 0xee].
Proof. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma p03_evt : reac_ctrl_identity_reply_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> 176 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    rw_cells rsegs m (spv + 1824) [Cells.CB 1 j1] -> rw_cells rsegs m (spv + 192) [Cells.CB 32 j2] ->
    stk rsegs m (spv - 176) spv -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x1372c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x1372c) fc None m' (seg_rom rsegs) /\
         munch [(spv + 192, spv + 224); (spv + 1824, spv + 1825); (spv - 176, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1824) [Z_to_bv 8 0xee] /\ bytes_at rsegs m' (spv + 192) (repeat (Z_to_bv 8 0) 32))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x136fc) fc None m (seg_rom rsegs)).
Proof.
  intros RC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv j1 j2 -> Hlo Hsp Hev H1 H2 ST MI.
  pose proof (munch_refl [(spv + 192, spv + 224); (spv + 1824, spv + 1825); (spv - 176, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  rewrite p03_le1. mem_after_store.
  do 10 step.
  eapply evt_cut.
  { eapply RC with (fr := 0) (len := 0) (pa := spv + 1792) (pp := spv + 1752) (pn := spv + 1688) (S := spv)
      (g := repeat (Z_to_bv 8 0) 50) (ja := []) (jp := []) (jn := []).
    all: first [ reflexivity | apply bv_eq; reflexivity | unfold REAC_CTRL_IDENTITY_REPLY_K; lia
               | assumption | (intros Hf; cbn in Hf; discriminate Hf) ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & _).
  subst ms'.
  unfold reac_ctrl_identity_reply_fp, reply_ok, reply_args, REAC_CTRL_IDENTITY_REPLY_K in MUc.
  cbn [negb andb Z.eqb app] in MUc.
  pose proof (sl_cells_bytes _ _ _ H1) as B1. pose proof (sl_cells_bytes _ _ _ H2) as B2.
  match type of B1 with bytes_at _ _ _ ?bs => replace bs with [Z_to_bv 8 0xee] in B1 by (vm_compute; reflexivity) end.
  match type of B2 with bytes_at _ _ _ ?bs => replace bs with (repeat (Z_to_bv 8 0) 32) in B2 by (vm_compute; reflexivity) end.
  replace (ret_pc (Z_to_bv 64 0x1372c)) with (Z_to_bv 64 0x1372c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [apply (u3_munch_join _ _ _ _ _ MU MUc); intros x Hx; cbn [Frame.outside] in *; split; [lia | exact I]|].
  split; [exact (wmono_trans rsegs _ _ _ WM WMc)|].
  split.
  - apply (bytes_at_transport rsegs _ _ m' _ _ B1 MUc). cbn [disjoint_from length]. split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ _ m' _ _ B2 MUc). rewrite repeat_length. cbn [disjoint_from].
    split; [lia | exact I].
Qed.

Section P03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis REPLY : reac_ctrl_identity_reply_contract.

Lemma seg_P03 : Hcut B APIf ra (Inv_U1372c B APIf ra empty) -> Hcut B APIf ra (Inv_U136fc B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HP0).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1824) 1 ST ltac:(lia) ltac:(lia)) as (j1 & HC1).
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 192) 32 ST ltac:(lia) ltac:(lia)) as (j2 & HC2).
  destruct (stk_split rsegs _ _ (g_S g - 1936 - 176) _ ST ltac:(lia)) as [_ ST2].
  destruct (stk_split rsegs _ _ (g_S g - 1936) _ ST2 ltac:(lia)) as [ST3 _].
  set (W := [(g_S g - 1936 + 192, g_S g - 1936 + 224); (g_S g - 1936 + 1824, g_S g - 1936 + 1825);
             (g_S g - 1936 - 176, g_S g - 1936)]).
  eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (u3_fp g W x _ Hx O). unfold W.
    repeat (apply Forall_cons; [cbn [fst snd]; unfold SLOT_K, SLOT_STACK; lia|]). apply Forall_nil.
  - rewrite sl_mkR_of.
    apply (p03_evt REPLY) with (spv := g_S g - 1936) (j1 := j1) (j2 := j2);
      [exact Hsp | lia | lia | exact H16 | exact HC1 | exact HC2 | exact ST3 | exact (mem_inv_normalize rsegs mem)].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ1 & HZ2).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|]. unfold PZ.
    split; [|split; [split|]].
    + apply (u3_P0_keep g regs regs' mem m' W HP0 MU').
      * unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold b8, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) HZ1).
    + unfold spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) HZ2).
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End P03.
