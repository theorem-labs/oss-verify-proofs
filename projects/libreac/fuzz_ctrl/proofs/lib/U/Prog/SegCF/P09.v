(* Segment P09 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x1379c, 0x137cc], U1379c -> U137d0
   (j = 0) or U140f8 (left = n - c0 = 0: `beqz s6` at 0x137b0 to 0x140f8). #38, #39: kind_name(14) = QMARK = "?"
   (read-only image bytes). Then s1 = j = 0, s0 = sp+128 (OVF), s2 = 1 (S2, A2) and the -7 pair at sp+8
   ((-3 << 33) - 7, M7). `first` = 0 (FS_0) holds since the memset at 0x136d4 (FIRST0, in PB). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u3.
Import ListNotations.
Open Scope Z_scope.

(* The q64 a C8 cell holds, with its closed value normalized. *)
Ltac p09_q64 H :=
  let B := fresh "B" in
  pose proof (sl_cells_bytes _ _ _ H) as B; cbn [Cells.cells_bytes Cells.cbytes] in B; rewrite app_nil_r in B;
  unfold q64;
  lazymatch type of B with
  | bytes_at _ _ _ (le8 ?v) => lazymatch goal with
      | |- bytes_at _ _ _ (le8 (Z_to_bv 64 ?z)) =>
          replace v with (Z_to_bv 64 z) in B by (apply bv_eq; vm_compute; reflexivity); exact B
      end
  end.

Lemma p09_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv nl : Z) (j1 : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 QMARK -> s6 = Z_to_bv 64 nl -> 0 <= nl < 2 ^ 64 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 8) [Cells.CB 8 j1] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' =>
         (nl = 0 /\ exists a0' a1' a2' : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x140f8) fc None m (seg_rom rsegs)) \/
         (nl <> 0 /\ exists (a0' a1' a2' : word) (m' : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (spv + 128)) (Z_to_bv 64 0) a0' a1' a2' a3 a4 a5 a6 a7
                          (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x137d0) fc None m' (seg_rom rsegs) /\
            munch [(spv + 8, spv + 16)] m m' /\ wmono rsegs m m' /\ q64 m' (spv + 8) 0xfffffff9fffffff9))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1379c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv nl j1 -> -> -> Hnl Hlo Hsp H8 MI.
  pose proof (munch_refl [(spv + 8, spv + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HQ0 : bytes_at rsegs m QMARK [Z_to_bv 8 63]) by (apply rc_ro_in_image; [exact MI | vm_compute; reflexivity]).
  assert (HQ1 : bytes_at rsegs m (QMARK + 1) [Z_to_bv 8 0])
    by (apply rc_ro_in_image; [exact MI | vm_compute; reflexivity]).
  pose proof (u3_ld1 m _ _ HQ0) as HR0. pose proof (u3_ld1 m _ _ HQ1) as HR1.
  unfold QMARK in HR0. let q1 := eval vm_compute in (QMARK + 1) in change (QMARK + 1) with q1 in HR1.
  step. step. step. if_false. step. step. if_false.
  step.
  destruct (Z.eq_dec nl 0) as [E0 | E0].
  - subst nl. if_true. apply evt_done. left. split; [reflexivity|]. do 3 eexists. reflexivity.
  - if_false_by (u3_eqb0 nl ltac:(lia)).
    do 7 step.
    apply evt_done. right. split; [exact E0|].
    do 4 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. p09_q64 H8.
Qed.

Section P09.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_P09 : Hat B APIf ra (Inv_U137d0_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_U140f8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U1379c B APIf ra empty).
Proof.
  intros H1 H2 g c (L & A & regs & mem & md & -> & HFR & HP & HP0 & HZ & H10).
  pose proof HFR as (HGV & _).
  pose proof HGV as (Hn26 & _).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (u3_P0_parts g regs mem HP0) as ((Hc & Hpc & Hnc) & HOUR & HID & HFG & HF0).
  assert (Hc0 : 0 <= c0 (g_in g) <= g_n g) by (unfold c0, g_n in *; lia).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 8) 8 ST ltac:(lia) ltac:(lia)) as (j1 & C8).
  set (W := [(g_S g - 1936 + 8, g_S g - 1936 + 16)]).
  eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (u3_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
    apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  - rewrite sl_mkR_of.
    apply (p09_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (g_S g - 1936) (g_n g - c0 (g_in g)) j1);
      [exact Hsp | exact H10 | exact Hnc | lia | lia | lia | exact C8 | exact (mem_inv_normalize rsegs mem)].
  - intros ms [(_ & ? & ? & ? & ->) | (_ & ? & ? & ? & m' & -> & MU & WM & _)].
    + do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    assert (HW : forall a n, g_S g - 1936 + 16 <= a -> disjoint_from W a n).
    { intros a n Ha. unfold W. cbn [disjoint_from]. split; [lia | exact I]. }
    assert (KID : IDB g m' RcIdentModel.ID0).
    { unfold IDB, spk, fsp, SLOT_FRAME in *. apply (bytes_at_transport rsegs W mem m' _ _ HID MU').
      apply HW; lia. }
    destruct HQ as [(E0 & ? & ? & ? & HE) | (E0 & ? & ? & ? & m'' & HE & _ & _ & B8)].
    + injection HE; intros; subst.
      apply H2. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      rewrite (u3_fJ0 (g_in g)) by (unfold g_n in E0; lia).
      unfold IDj, IDb. split; [exact KID | exact u3_id_ok_ID0].
    + injection HE; intros; subst.
      unfold q64 in B8.
      apply H1. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      apply u3_LI0.
      * unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * unfold OURb, spk, fsp, SLOT_FRAME in *. apply (bytes_at_transport rsegs W mem m' _ _ HOUR MU').
        rewrite OUR_length. apply HW; lia.
      * unfold M7, q64, spk, fsp, SLOT_FRAME. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) B8).
      * unfold rg, spk, fsp, SLOT_FRAME. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * unfold CUR, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx). split; [lia|]. split; [exact Hpc | exact Hnc].
      * unfold g_n in *. lia.
      * exact KID.
      * unfold FGB, spk, fsp, SLOT_FRAME in *. apply (bytes_at_transport rsegs W mem m' _ _ HFG MU').
        rewrite z72_length. apply HW; lia.
      * unfold spk, fsp, SLOT_FRAME in *. apply (bytes_at_transport rsegs W mem m' _ _ HF0 MU').
        rewrite repeat_length. apply HW; lia.
Qed.

End P09.
