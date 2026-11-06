(* Segment P06 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13760, 0x13770], U13760 -> U13774
   (#34: ports_parse's -1; reac_ports_parse(0, 0) = -1, no write). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u3.
Import ListNotations.
Open Scope Z_scope.

Lemma p06_nok : forall p bs, ports_ok p 0 bs = false.
Proof.
  intros p bs. unfold ports_ok. replace (negb (0 =? 0)) with false by reflexivity.
  rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma p06_evt : reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    evt rsegs
      (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
         ms' = MS (mkR (Z_to_bv 64 0x13774) sp gp tp t0' t1' t2 (Z_to_bv 64 (-1)) s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13774) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13760) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step. step. if_false. do 3 step.
  eapply evt_cut.
  { eapply PP with (p := 0) (q := 0) (bs := repeat (Z_to_bv 8 0) 20).
    all: first [ reflexivity | lia | (intros _ Hq; exfalso; apply Hq; reflexivity) ]. }
  intros ms' (t0' & t1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & Hm).
  rewrite p06_nok in E, Hm. subst ms' m'.
  replace (ret_pc (Z_to_bv 64 0x13774)) with (Z_to_bv 64 0x13774) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 9 eexists. reflexivity.
Qed.

Section P06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PP : reac_ports_parse_contract.

Lemma seg_P06 : Hcut B APIf ra (Inv_U13774 B APIf ra empty) -> Hcut B APIf ra (Inv_U13760 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & HP0 & HPZ & H10).
  eapply (u3_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (u3_fp g _ x _ Hx O). apply Forall_nil.
  - rewrite sl_mkR_of. apply (p06_evt PP). exact H10.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & HE).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|]. split; [|split; [|split]].
    + apply (u3_P0_keep g regs regs' mem m' [] HP0 MU' I).
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + exact (u3_PZ_keep g 0xee mem m' [] HPZ MU' I I).
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End P06.
