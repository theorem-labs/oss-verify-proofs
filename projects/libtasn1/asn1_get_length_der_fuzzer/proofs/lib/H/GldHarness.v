(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib Require Import NElim. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RegFold. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc Require JunkAbs.


From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.H Require Import GldProof.
Import ListNotations.
Open Scope bv_scope.


Definition hrn_prog : RStep.ptree :=
  (PNode 20%Z
    (PLeaf
      (PJ_OpImm_ALU_ADD_nnn 0 12 0 512 4
      (PJ_Branch_BC_LTU_nnn 4 12 11 28 4
      (PJ_OpImm_ALU_ADD_nnn 8 2 2 4080 4
      (PJ_Store_SZ8_nnn 12 2 1 8 4
      (PJ_OpImm_ALU_ADD_nnn 16 12 2 4 4 nil))))))
    (PLeaf
      (PJ_Jal_nn 20 1 20 4
      (PJ_Load_SZ8_true_nnn 24 1 2 8 4
      (PJ_OpImm_ALU_ADD_nnn 28 2 2 16 4
      (PJ_OpImm_ALU_ADD_nnn 32 10 0 0 4
      (PJ_Jalr_nnn 36 0 1 0 4 nil))))))).

Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.solve_load ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.solve_cond ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.step ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.stepz ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.simp_regs ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.

Section Segs.
  Variable segs : list Segment.
  Lemma rw_cells_app_split : forall m A cs1 cs2,
    rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
  Proof.
    intros m A cs1 cs2 [[Hwf HB] (W0 & W1 & W)].
    apply cells_wf_app in Hwf. destruct Hwf as [H1 H2].
    rewrite cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
    rewrite (cells_bytes_length cs1 H1) in B2. rewrite cells_size_app, Nat2Z.inj_add in W1, W.
    pose proof (bytes_at_bound _ _ _ _ B1) as BB1.
    split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
    - apply W. lia.
    - replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply W. lia.
  Qed.
  Lemma rw_cells_app_join : forall m A cs1 cs2,
    rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
  Proof.
    intros m A cs1 cs2 [[H1 B1] (W0 & W1 & W)] [[H2 B2] (V0 & V1 & V)].
    split; [split|].
    - apply cells_wf_app. split; assumption.
    - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 H1). exact B2.
    - rewrite cells_size_app, Nat2Z.inj_add. split; [lia|]. split; [lia|]. intros i Hi.
      destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply W; lia|].
      replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply V. lia.
  Qed.
End Segs.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_hrn : CodeAtT img_segs (sym 0x12a54) hrn_prog}.
  Context {RB_hrn : RelCode (sym 0x12a54) 40}.

  (* What the harness needs from asn1_get_length_der at sym 0x12a54 + 40: the UBSan
     build's lemma, whose premises are a superset of the plain build's. *)
  Definition gld_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (bs : list byte),
    bytes_at img_segs m (bv_unsigned a0) der ->
    bv_unsigned a0 <> 0%Z ->
    a1 = Z_to_bv 64 (Z.of_nat (length der)) -> (length der <= 512)%nat ->
    rw_cells img_segs m (bv_unsigned a2) [CB 4 bs] ->
    bv_unsigned a2 <> 0%Z -> (bv_unsigned a2 mod 4 = 0)%Z ->
    (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned a2)%Z ->
    evt img_segs (gld_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 der m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x12a54 + 40)) fc None m (seg_rom img_segs)).
  Context {SPEC_gld : gld_contract}.

(* LLVMFuzzerTestOneInput returns 0 to its caller with every callee-saved register
   (sp included) restored, having changed only its own 16-byte frame below sp. *)
Definition hrn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p : word) (der : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)%Z] m m' /\ wmono img_segs m m'
    /\ stk img_segs m' lo (bv_unsigned sp) /\ bytes_at img_segs m' (bv_unsigned p) der.

Lemma hrn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (der : list byte) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at img_segs m (bv_unsigned a0) der -> bv_unsigned a0 <> 0%Z ->
  a1 = Z_to_bv 64 (Z.of_nat (length der)) ->
  (bv_unsigned a0 + Z.of_nat (length der) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt img_segs (hrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 der lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x12a54)) fc None m (seg_rom img_segs)).
Proof.
  intros until lo. intros ST LO AL DER A0NZ -> SEP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)%Z] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ DER) as PB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  zstep. zstep. if_cases K; zify_cond K.
  { (* size > 512: return 0 at once *) zstep. zstep. finish. }
  carve_frame 16%nat ST.
  zstep. zstep.
  eapply (rw_cells_cb_split img_segs _ _ _ _ 4%nat 4%nat) in FR; [ | reflexivity | reflexivity ].
  cbn [cb_split cb_pieces csize Nat.ltb Nat.leb Nat.eqb andb Nat.sub Nat.add app] in FR.
  apply (rw_cells_app_split img_segs _ _ [_] [_; _]) in FR. destruct FR as [FR1 FR].
  apply (rw_cells_app_split img_segs _ _ [_] [_]) in FR. destruct FR as [FR2 FR3].
  cbn [cells_size csize Nat.add] in FR2, FR3.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -12)) = (bv_unsigned sp + -12)%Z)
    by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  replace (bv_unsigned sp + -16 + Z.of_nat 4)%Z with (bv_unsigned sp + -12)%Z in FR2 by lia.
  zstep. zstep.
  call SPEC_gld.
  all: rewrite ?Esp; try reflexivity; try eassumption; try lia.
  replace (bv_unsigned sp + -16 + Z.of_nat 4 + Z.of_nat 4)%Z with (bv_unsigned sp + -8)%Z in FR3 by lia.
  rewrite Esp in POST.
  zstep. zstep. zstep. zstep.
  (* give the frame back: [junk; *len; saved ra] covers [sp - 16, sp) *)
  match goal with H : rw_cells _ ?mm (bv_unsigned sp + -12) [C4 ?v] |- _ =>
    assert (FRa : rw_cells img_segs mm (bv_unsigned sp + -16) ([CB 4 (firstn 4 jk)] ++ [C4 v] ++ [C8 ra]));
    [ apply rw_cells_app_join; [exact FR1|]; cbn [cells_size csize Nat.add];
      replace (bv_unsigned sp + -16 + Z.of_nat 4)%Z with (bv_unsigned sp + -12)%Z by lia;
      apply rw_cells_app_join; [exact H|]; cbn [cells_size csize Nat.add];
      replace (bv_unsigned sp + -12 + Z.of_nat 4)%Z with (bv_unsigned sp + -8)%Z by lia; exact FR3
    | ] end.
  cbn [app] in FRa.
  release_frame FRa ST (bv_unsigned sp).
  finish.
Qed.
End Img.
