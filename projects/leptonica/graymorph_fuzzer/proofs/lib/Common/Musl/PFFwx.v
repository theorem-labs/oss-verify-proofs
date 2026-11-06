(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase Memcpy.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFSnw.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition fwx_regions (sp0 sp : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp - 64), 64%Z); (Z_to_bv 64 (sp0 - 2080), 2000%Z);
   (Z_to_bv 64 (sp0 - 2360), 8%Z); (Z_to_bv 64 (sp0 - 2344), 8%Z); (Z_to_bv 64 (sp0 - 2168), 16%Z);
   (Z_to_bv 64 (sp0 - 2752), 80%Z)].
End GD_1.

(* [comment removed for export] *)
Section GD_2.
  Context {RL : Reloc}.
Definition FILEst (m : word -> option byte) (sp0 u j : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 (sp0 - 2360)) 8 = Some (W8 (sp0 - 2752 + u))
  /\ rdn SEGS m (Z_to_bv 64 (sp0 - 2344)) 8 = Some (W8 (sp0 - 2752))
  /\ CKst m sp0 j
  /\ (0 <= u <= 80)%Z
  /\ defined m (sp0 - 2752) u.
End GD_2.

(* [comment removed for export] *)
Section GD_3.
  Context {RL : Reloc}.
Record FILEc (m : word -> option byte) (sp0 : Z) : Prop := FILEC {
  Fc_flags : rdn SEGS m (Z_to_bv 64 (sp0 - 2400)) 1 = Some [Z_to_bv 8 0];
  Fc_wend  : rdn SEGS m (Z_to_bv 64 (sp0 - 2368)) 8 = Some (W8 (sp0 - 2672));
  Fc_write : rdn SEGS m (Z_to_bv 64 (sp0 - 2328)) 8 = Some (X8 (rl dF_1c80c 0x1c80c));
  Fc_buf   : rdn SEGS m (Z_to_bv 64 (sp0 - 2312)) 8 = Some (W8 (sp0 - 2752));
  Fc_lbf   : rdn SEGS m (Z_to_bv 64 (sp0 - 2256)) 4 = Some (W4 4294967295);
  Fc_ck    : rdn SEGS m (Z_to_bv 64 (sp0 - 2248)) 8 = Some (W8 (sp0 - 2168)) }.
End GD_3.

(* [comment removed for export] *)
Ltac frame_rdn_keep FM :=
  rewrite (frame_mod_rdn SEGS _ _ _ _ _ FM);
  [ | intros i Hi; cbn [outside]; unfold in_rng; unorm; repeat split; lia | unorm; lia ].

Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma FILEc_fwx : forall m m' sp0 sp,
  (4096 <= sp0 < 2 ^ 63)%Z -> (64 <= sp <= sp0 - 2768)%Z ->
  FILEc m sp0 -> frame_mod m m' (fwx_regions sp0 sp) -> FILEc m' sp0.
Proof.
  intros m m' sp0 sp H0 H1 FC FM. unfold fwx_regions in FM. destruct FC.
  split; frame_rdn_keep FM; assumption.
Qed.
End VP1.

Section FWX.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Variables (m : word -> option byte) (sp u j s l : Z) (bs : list byte).
  Hypothesis F : FRM sp0 mem0 m.
  Hypothesis Hsp : (sp0 - FR + 64 <= sp /\ sp <= sp0 - 2768)%Z.
  Hypothesis FC : FILEc m sp0.
  Hypothesis FS : FILEst m sp0 u j.
  Hypothesis Hl : (0 <= l < 2 ^ 32)%Z.
  Hypothesis Hs : rdn SEGS m (Z_to_bv 64 s) (Z.to_nat l) = Some bs.
  Hypothesis Hsrng : (0 <= s /\ (s + l <= sp0 - FR \/ (sp <= s /\ s + l <= sp0 - 2768)))%Z.

  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.

  Ltac sok := soks CTX.

  Lemma fwx_regions_sub : forall a, outside a [(Z_to_bv 64 (sp0 - FR), FR)] -> outside a (fwx_regions sp0 sp).
  Proof.
    pose proof Hcsp as Hsp0.
    intros a Ho. unfold fwx_regions. cbn [outside] in Ho |- *. unfold in_rng in *. lay.
    revert Ho. unorm. intros Ho. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition fwxM1 (regs : bvmap 5 word) (ret : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp - 8)) (X8 ret))
      (Z_to_bv 64 (sp - 16)) (X8 (getr regs 8)))
      (Z_to_bv 64 (sp - 24)) (X8 (getr regs 9)))
      (Z_to_bv 64 (sp - 32)) (X8 (getr regs 18)))
      (Z_to_bv 64 (sp - 40)) (X8 (getr regs 19)))
      (Z_to_bv 64 (sp - 48)) (X8 (getr regs 20)))
      (Z_to_bv 64 (sp - 56)) (X8 (getr regs 21)).

  Ltac prologue regs ret :=
    stepiv constr:(F_17b9c) constr:(D_17b9c) (Z_to_bv 64 (sp - 64)) ltac:(zval);                 (* [comment removed for export] *)
    stepST constr:(F_17ba0) constr:(D_17ba0) (Z_to_bv 64 (sp - 8)) ret ltac:(sok);                (* [comment removed for export] *)
    stepST constr:(F_17ba4) constr:(D_17ba4) (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok);     (* [comment removed for export] *)
    stepST constr:(F_17ba8) constr:(D_17ba8) (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok);     (* [comment removed for export] *)
    stepST constr:(F_17bac) constr:(D_17bac) (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok);    (* [comment removed for export] *)
    stepST constr:(F_17bb0) constr:(D_17bb0) (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok);    (* [comment removed for export] *)
    stepST constr:(F_17bb4) constr:(D_17bb4) (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(sok);    (* [comment removed for export] *)
    stepST constr:(F_17bb8) constr:(D_17bb8) (Z_to_bv 64 (sp - 56)) (getr regs 21) ltac:(sok);    (* [comment removed for export] *)
    stepn constr:(F_17bbc) constr:(D_17bbc);                                                      (* [comment removed for export] *)
    stepn constr:(F_17bc0) constr:(D_17bc0);                                                      (* [comment removed for export] *)
    stepLD8 constr:(F_17bc4) constr:(D_17bc4) (Z_to_bv 64 (sp0 - 2672));                          (* [comment removed for export] *)
    stepn constr:(F_17bc8) constr:(D_17bc8);                                                      (* [comment removed for export] *)
    stepb_ft constr:(F_17bcc) constr:(D_17bcc) ltac:(cond_lia);                                   (* [comment removed for export] *)
    stepLD8 constr:(F_17bd0) constr:(D_17bd0) (Z_to_bv 64 (sp0 - 2752 + u));                      (* [comment removed for export] *)
    stepiv constr:(F_17bd4) constr:(D_17bd4) (Z_to_bv 64 (80 - u)) ltac:(zval).                   (* [comment removed for export] *)

  Theorem fwritex_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 10 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 l -> getr regs 12 = Z_to_bv 64 (sp0 - 2400) ->
    exists r m',
      msteps SEGS (mkst regs (rl dF_17b9c 0x17b9c) m rom) (mkst r ret m' rom)
      /\ (keeps_cs regs r /\ getr r 10 = Z_to_bv 64 l
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)
          /\ frame_mod m m' (fwx_regions sp0 sp)).
  Proof.
    intros regs ret Hret H1 H2 H10 H11 H12.
    pose proof Hcsp as Hsp0. lay.
    destruct FC as [Cflags Cwend Cwrite Cbuf Clbf Cck].
    destruct FS as (Swpos & Swbase & (Scs & Scn & Sj) & Su & Sdef).
    pose proof (rdn_length _ _ _ _ _ Hs) as Lbs.
    set (M1 := fwxM1 regs ret).
    assert (GM1 : mem_grows m M1) by (unfold M1, fwxM1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (FM1 : frame_mod m M1 (fwx_regions sp0 sp)).
    { unfold M1, fwxM1, fwx_regions. frame_tac Lbs. apply frame_mod_refl. }
    assert (F1 : FRM sp0 mem0 M1) by (eapply FRM_sub; [exact F | exact FM1 | apply fwx_regions_sub]).
    assert (M1ra : rdn SEGS M1 (Z_to_bv 64 (sp - 8)) 8 = Some (X8 ret)) by (unfold M1, fwxM1; rdn_solve).
    assert (M1s0 : rdn SEGS M1 (Z_to_bv 64 (sp - 16)) 8 = Some (X8 (getr regs 8))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1s1 : rdn SEGS M1 (Z_to_bv 64 (sp - 24)) 8 = Some (X8 (getr regs 9))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1s2 : rdn SEGS M1 (Z_to_bv 64 (sp - 32)) 8 = Some (X8 (getr regs 18))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1s3 : rdn SEGS M1 (Z_to_bv 64 (sp - 40)) 8 = Some (X8 (getr regs 19))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1s4 : rdn SEGS M1 (Z_to_bv 64 (sp - 48)) 8 = Some (X8 (getr regs 20))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1s5 : rdn SEGS M1 (Z_to_bv 64 (sp - 56)) 8 = Some (X8 (getr regs 21))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1wr : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2328)) 8 = Some (X8 (rl dF_1c80c 0x1c80c))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1lbf : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2256)) 4 = Some (W4 4294967295)) by (unfold M1, fwxM1; rdn_solve).
    assert (M1ck : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2248)) 8 = Some (W8 (sp0 - 2168))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1wpos : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2360)) 8 = Some (W8 (sp0 - 2752 + u))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1wbase : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2344)) 8 = Some (W8 (sp0 - 2752))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1buf : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2312)) 8 = Some (W8 (sp0 - 2752))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1cs : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2168)) 8 = Some (W8 (sp0 - 2080 + j))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1cn : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2160)) 8 = Some (W8 (1999 - j))) by (unfold M1, fwxM1; rdn_solve).
    assert (M1src : rdn SEGS M1 (Z_to_bv 64 s) (Z.to_nat l) = Some bs) by (unfold M1, fwxM1; rdn_solve).
    destruct (Z_lt_le_dec (80 - u) l) as [Hdirect|Hfits].
    - (* [comment removed for export] *)
      eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c80c 0x1c80c) M1 rom)
        (fun r => getr r 1 = ret /\ getr r 2 = Z_to_bv 64 sp /\ getr r 10 = Z_to_bv 64 (sp0 - 2400)
                  /\ getr r 11 = Z_to_bv 64 s /\ getr r 12 = Z_to_bv 64 l /\ keeps_cs regs r)).
      { eexists. split.
        - prologue regs ret.
          stepb_ft F_17bd8 D_17bd8 ltac:(cond_lia).                                 (* [comment removed for export] *)
          stepLD8 F_17bdc D_17bdc (rl dF_1c80c 0x1c80c).                             (* [comment removed for export] *)
          stepn F_17be0 D_17be0.                                                    (* [comment removed for export] *)
          stepn F_17be4 D_17be4.                                                    (* [comment removed for export] *)
          stepn F_17be8 D_17be8.                                                    (* [comment removed for export] *)
          stepLD8 F_17bec D_17bec ret.                                              (* [comment removed for export] *)
          stepLD8 F_17bf0 D_17bf0 (getr regs 8).                                    (* [comment removed for export] *)
          stepLD8 F_17bf4 D_17bf4 (getr regs 9).                                    (* [comment removed for export] *)
          stepLD8 F_17bf8 D_17bf8 (getr regs 18).                                   (* [comment removed for export] *)
          stepLD8 F_17bfc D_17bfc (getr regs 19).                                   (* [comment removed for export] *)
          stepLD8 F_17c00 D_17c00 (getr regs 20).                                   (* [comment removed for export] *)
          stepLD8 F_17c04 D_17c04 (getr regs 21).                                   (* [comment removed for export] *)
          stepiv F_17c08 D_17c08 (Z_to_bv 64 sp) ltac:(zval).                       (* [comment removed for export] *)
          stepretK F_17c0c D_17c0c F_1c80c ltac:(gres; rwH; bveq).   (* [comment removed for export] *)
          unfold M1, fwxM1. apply mst_refl.
        - cbv beta. repeat split; gres; rwH; try reflexivity. keeps_cs_fin H1. }
      cbv beta. intros r1 (R1 & R2 & R10 & R11 & R12 & K1).
      destruct (sn_write_run sp0 mem0 cv rom CTX M1 sp u j s l bs F1 ltac:(lay; lia) M1ck M1wpos M1wbase M1buf
                  ltac:(split; [exact M1cs | split; [exact M1cn | exact Sj]]) Su
                  ltac:(eapply defined_grows; [exact GM1 | exact Sdef]) Hl M1src ltac:(lay; lia)
                  r1 ret Hret R1 R2 R10 R11 R12)
        as (r2 & m2 & RUN & K2 & A10 & W1 & W2 & [j2 [Hj2 CK2]] & FR2).
      exists r2, m2. split; [exact RUN|].
      split; [eapply keeps_cs_trans; eassumption|]. split; [exact A10|]. split.
      + exists 0%Z, j2. split; [|exact Hj2]. split; [|split; [exact W2 | split; [exact CK2 | split; [lia | apply defined_0]]]].
        rewrite Z.add_0_r. exact W1.
      + eapply frame_mod_weaken; [| exact (frame_mod_trans _ _ _ _ _ FM1 FR2)].
        intros a Ho. unfold fwx_regions, snw_regions in *. cbn [outside app] in Ho |- *. tauto.
    - (* [comment removed for export] *)
      assert (MC : mcH M1 (Z_to_bv 64 (sp0 - 2752 + u)) (Z_to_bv 64 s) l bs).
      { split.
        - lia.
        - exact Lbs.
        - rewrite Lbs. exact M1src.
        - rewrite Lbs. eapply (FRM_sok sp0 mem0 cv CTX); [exact F1 | lay; lia | lay; lia].
        - unorm. lia.
        - unorm. lia.
        - unorm. lia. }
      eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_1c9b4 0x1c9b4) M1 rom)
        (fun r => getr r 1 = (rl dF_17b9c 0x17ca0) /\ getr r 10 = Z_to_bv 64 (sp0 - 2752 + u)
                  /\ getr r 11 = Z_to_bv 64 s /\ getr r 12 = Z_to_bv 64 l
                  /\ getr r 2 = Z_to_bv 64 (sp - 64) /\ getr r 8 = Z_to_bv 64 (sp0 - 2400) /\ getr r 9 = Z_to_bv 64 l
                  /\ getr r 19 = Z_to_bv 64 0
                  /\ agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r)).
      { eexists. split.
        - prologue regs ret.
          stepb_tk F_17bd8 D_17bd8 ltac:(cond_lia).                                 (* [comment removed for export] *)
          stepLD F_17c10 D_17c10 (W4 4294967295) (Z_to_bv 64 4294967295) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).  (* [comment removed for export] *)
          stepn F_17c14 D_17c14.                                                    (* [comment removed for export] *)
          stepb_tk F_17c18 D_17c18 ltac:(reflexivity).                               (* [comment removed for export] *)
          stepn F_17c94 D_17c94.                                                    (* [comment removed for export] *)
          stepn F_17c98 D_17c98.                                                    (* [comment removed for export] *)
          stepn F_17c9c D_17c9c.                                                    (* [comment removed for export] *)
          unfold M1, fwxM1. apply mst_refl.
        - postR. }
      cbv beta. intros r1 (R1 & R10 & R11 & R12 & R2 & R8 & R9 & R19 & RCS).
      eapply (runs_trans1m SEGS _ (fun r => mkst r (rl dF_17b9c 0x17ca0) (wbytes M1 (Z_to_bv 64 (sp0 - 2752 + u)) bs) rom)
        (fun r => keeps r1 r)).
      { destruct (ref_memcpy M1 (Z_to_bv 64 (sp0 - 2752 + u)) (Z_to_bv 64 s) l bs rom MC r1 (rl dF_17b9c 0x17ca0)
                  ltac:(rl_ret_ok) R1 R10 R11 R12) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | exact K2]. }
      cbv beta. intros r2 K2.
      assert (T2 : getr r2 2 = Z_to_bv 64 (sp - 64)) by (rewrite (K2 2%bv) by kept_reg; exact R2).
      assert (T8 : getr r2 8 = Z_to_bv 64 (sp0 - 2400)) by (rewrite (K2 8%bv) by kept_reg; exact R8).
      assert (T9 : getr r2 9 = Z_to_bv 64 l) by (rewrite (K2 9%bv) by kept_reg; exact R9).
      assert (T19 : getr r2 19 = Z_to_bv 64 0) by (rewrite (K2 19%bv) by kept_reg; exact R19).
      assert (RCS2 : agree_but [1; 2; 8; 9; 18; 19; 20; 21] regs r2) by (eapply agree_but_keeps; [exact RCS | exact K2]).
      eexists. eexists. split.
      + stepLD8 F_17ca0 D_17ca0 (Z_to_bv 64 (sp0 - 2752 + u)).                   (* [comment removed for export] *)
        stepiv F_17ca4 D_17ca4 (Z_to_bv 64 (sp0 - 2752 + (u + l))) ltac:(zval).   (* [comment removed for export] *)
        stepST F_17ca8 D_17ca8 (Z_to_bv 64 (sp0 - 2360)) (Z_to_bv 64 (sp0 - 2752 + (u + l))) ltac:(sok).  (* [comment removed for export] *)
        stepiv F_17cac D_17cac (Z_to_bv 64 l) ltac:(zval).                         (* [comment removed for export] *)
        stepLD8 F_17cb0 D_17cb0 ret.                                                (* [comment removed for export] *)
        stepLD8 F_17cb4 D_17cb4 (getr regs 8).                                      (* [comment removed for export] *)
        stepLD8 F_17cb8 D_17cb8 (getr regs 9).                                      (* [comment removed for export] *)
        stepLD8 F_17cbc D_17cbc (getr regs 18).                                     (* [comment removed for export] *)
        stepLD8 F_17cc0 D_17cc0 (getr regs 19).                                     (* [comment removed for export] *)
        stepLD8 F_17cc4 D_17cc4 (getr regs 20).                                     (* [comment removed for export] *)
        stepLD8 F_17cc8 D_17cc8 (getr regs 21).                                     (* [comment removed for export] *)
        stepiv F_17ccc D_17ccc (Z_to_bv 64 sp) ltac:(zval).                         (* [comment removed for export] *)
        stepret F_17cd0 D_17cd0 ret ltac:(reflexivity).
        apply mst_refl.
      + split; [keeps_cs_fin RCS2|]. split; [gres; reflexivity|]. split.
        * exists (u + l)%Z, j. split; [|lia]. split; [rdn_solve|]. split; [rdn_solve|]. split; [|split; [lia|]].
          -- split; [rdn_solve | split; [rdn_solve | exact Sj]].
          -- apply defined_app; [| |lia].
             ++ eapply defined_grows; [| eapply defined_grows; [exact GM1 | exact Sdef]].
                eapply mem_grows_trans; apply wbytes_grows.
             ++ eapply defined_grows; [apply wbytes_grows|].
                replace l with (Z.of_nat (length bs)) by lia. apply defined_wbytes; lia.
        * unfold fwx_regions. frame_tac Lbs. first [exact FM1 | apply frame_mod_refl].
  Qed.
End FWX.
