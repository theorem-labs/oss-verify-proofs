(* Segment X02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x14110, 0x14150], the epilogue. U14110 -> 0x14114:
   0x14110 `beqz a0` (#94) is not taken, a0 = the address of the first 0 of model_name(ID_J) in [sp+79, sp+96]
   (C14). U14114 -> RET: a0 = 0, ra and s0-s11 reloaded from the saved bytes at [S - 104, S) (FR), sp = S, then
   `ret` to R (FR2'). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Ltac x02_cond := unfold_cond; fold_lit_ux; rewrite ?MState.unsigned_lit by lia; solve_cond_rec.
Ltac x02_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (symmetry; x02_cond); cbv iota
  end.

Lemma x02_ret_pc_ra : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. assert (E : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity. }
  rewrite E. apply ret_pc_even; [apply Z.mod_pos_bound; lia|].
  rewrite <- Znumtheory.Zmod_div_mod; [exact Hz | lia | lia | exists (2 ^ 63); reflexivity].
Qed.

Lemma x02_ld : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof. intros m a v H. pose proof (u8_ovr m a _ H) as E. rewrite length_le8 in E. exact E. Qed.

(* A load of the saved-register area: the hypothesis whose address equals the load's. *)
Ltac x02_rd :=
  match goal with
  | H : bytes_at _ _ ?a (le8 _) |- ov_read_bytes _ _ (wa ?b) 8 = Some _ =>
      replace b with a by lia; apply x02_ld; exact H
  end.

Lemma x02_fz : forall l, (RcIdentModel.first_zero l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [RcIdentModel.first_zero length]; [lia|]. destruct (Z.eqb _ 0); lia. Qed.

Lemma x02_fz_mn : forall idb, (RcIdentModel.first_zero (RcIdentModel.model_name idb) <= 17)%nat.
Proof.
  intros idb. pose proof (x02_fz (RcIdentModel.model_name idb)) as H.
  unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.NAME_CAP in *. rewrite length_firstn in H. lia.
Qed.

(* 0x14110 `beqz a0` not taken: a0 = v <> 0. *)
Lemma x02_nz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    a0 = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) F (Z_to_bv 64 0x14114) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14110) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m v -> Hv.
  step. x02_if false.
  apply evt_done. reflexivity.
Qed.

(* 0x14114 .. 0x14150: a0 = 0, the 13 reloads, sp += 1936, ret. *)
Lemma x02_epi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z)
         (r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : word),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 1928)) 8 = Some (le8 r1) ->
    ov_read_bytes rsegs m (wa (spv + 1920)) 8 = Some (le8 r8) ->
    ov_read_bytes rsegs m (wa (spv + 1912)) 8 = Some (le8 r9) ->
    ov_read_bytes rsegs m (wa (spv + 1904)) 8 = Some (le8 r18) ->
    ov_read_bytes rsegs m (wa (spv + 1896)) 8 = Some (le8 r19) ->
    ov_read_bytes rsegs m (wa (spv + 1888)) 8 = Some (le8 r20) ->
    ov_read_bytes rsegs m (wa (spv + 1880)) 8 = Some (le8 r21) ->
    ov_read_bytes rsegs m (wa (spv + 1872)) 8 = Some (le8 r22) ->
    ov_read_bytes rsegs m (wa (spv + 1864)) 8 = Some (le8 r23) ->
    ov_read_bytes rsegs m (wa (spv + 1856)) 8 = Some (le8 r24) ->
    ov_read_bytes rsegs m (wa (spv + 1848)) 8 = Some (le8 r25) ->
    ov_read_bytes rsegs m (wa (spv + 1840)) 8 = Some (le8 r26) ->
    ov_read_bytes rsegs m (wa (spv + 1832)) 8 = Some (le8 r27) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR r1 (Z_to_bv 64 (spv + 1936)) gp tp t0 t1 t2 r8 r9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6) F (ret_pc r1) fc None m
                     (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14114) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv r1 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 -> H0 H1
    R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  rewrite ?MState.unsigned_lit by lia.
  apply evt_done. reflexivity.
Qed.

Section X02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_X02 : Hcut B APIf ra (Inv_U14110 B APIf ra empty) /\ Hcut B APIf ra (Inv_U14114 B APIf ra empty).
Proof.
  assert (H24 : Hcut B APIf ra (Inv_U14114 B APIf ra empty)).
  { intros g c (L & A & regs & mem & md & -> & HF & HP & _).
    pose proof HF as (HGV & _ & Hgp & Htp & HSV & _).
    pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & E2 & _).
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF) as (Hsp & H16 & HSK & HS47 & HMI).
    unfold saved_bytes in HSV.
    repeat (apply bytes_at_app in HSV; destruct HSV as [?B HSV]; rewrite length_le8 in HSV).
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    eapply (u8_run_to B APIf ra empty FF); [exact HF | | intros regs' HG].
    - unfold rmk. eapply x02_epi with (spv := g_S g - 1936); [exact Hsp | lia | lia | x02_rd ..].
    - rewrite (x02_ret_pc_ra ra (u8_ra_even B APIf ra empty FF)). apply SR_ret.
      apply (u8_post_FR B APIf ra empty g L A regs regs' mem md HF HP).
      + etransitivity; [apply HG|]. reflexivity.
      + intros r Hr. unfold callee_saved in Hr.
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
          r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          (etransitivity; [apply HG|]); try reflexivity.
        * transitivity (Z_to_bv 64 (g_S g)); [|symmetry; exact E2].
          transitivity (Z_to_bv 64 (g_S g - 1936 + 1936)); [reflexivity | f_equal; lia].
        * exact Hgp.
        * exact Htp. }
  split; [|exact H24].
  intros g c (L & A & regs & mem & md & -> & HF & HP & (HID & Hhas & H10)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (x02_fz_mn (t_ID (g_in g) (fJ (g_in g)))) as Hfz.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  eapply (u8_run_to B APIf ra empty FF);
    [exact HF | unfold rmk; eapply x02_nz; [exact H10 | unfold spk, fsp, SLOT_FRAME; lia] |].
  intros regs' HG. apply H24. apply (u8_cut_close B APIf ra empty _ _ _ _ L A); [| exact HP | exact I].
  apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HF | rewrite HG; reflexivity ..].
Qed.

End X02.
