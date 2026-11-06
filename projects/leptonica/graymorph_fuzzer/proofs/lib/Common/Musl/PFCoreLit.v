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
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_18000_19000.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFCore.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).

Section LIT.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.

  Ltac sok := soks CTX.
  Variables (g3 g4 : word).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (m : word -> option byte) (p n c : Z) (byt : Z -> Z).
  Hypothesis Hn : (1 <= n)%Z.
  Hypothesis Hp : (IMG_LO <= p /\ p + n < IMG_TOP)%Z.
  Hypothesis BYrd : forall q, (p <= q <= p + n)%Z -> rdn SEGS m (Z_to_bv 64 q) 1 = Some [Z_to_bv 8 (byt q)].
  Hypothesis BYlit : forall q, (p <= q < p + n)%Z -> (1 <= byt q <= 255 /\ byt q <> 37)%Z.
  Hypothesis BYend : byt (p + n)%Z = c.
  Hypothesis Hc : c = 0%Z \/ (c = 37%Z /\ exists d, rdn SEGS m (Z_to_bv 64 (p + n + 1)) 1 = Some [Z_to_bv 8 d] /\ (0 <= d <= 255)%Z /\ d <> 37%Z).

  (* [comment removed for export] *)
  Lemma scan_loop : forall k (i : Z) r,
    (Z.of_nat k = n - 1 - i)%Z -> (0 <= i < n)%Z ->
    getr r 10 = Z_to_bv 64 (byt (p + i)%Z) -> getr r 21 = Z_to_bv 64 (p + i) -> getr r 8 = Z_to_bv 64 37 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x18040) m rom) (mkst r' (rl dF_17f6c 0x18084) m rom)
      /\ getr r' 10 = Z_to_bv 64 (p + n) /\ getr r' 21 = Z_to_bv 64 (p + n)
      /\ (forall x : reg, x <> 10 -> x <> 11 -> x <> 12 -> x <> 21 -> getr r' x = getr r x).
  Proof.
    pose proof Hcsp as Hsp0. lay.
    induction k as [|k IH]; intros i r Hk Hi R10 R21 R8.
    - (* [comment removed for export] *)
      assert (Ei : (i = n - 1)%Z) by lia.
      pose proof (BYlit (p + i)%Z ltac:(lia)) as BL.
      destruct Hc as [C0 | [C37 (d & Rd & Hd & Hd37)]].
      + (* [comment removed for export] *)
        eexists. split.
        * stepb_ft F_18040 D_18040 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).     (* [comment removed for export] *)
          stepLBU F_18044 D_18044 (Z_to_bv 8 (byt (p + n)%Z))
            ltac:(unfold v_addi; unorm; replace (p + i + 1)%Z with (p + n)%Z by lia; apply BYrd; lia).        (* [comment removed for export] *)
          rewrite (u8_of_Z (byt (p + n)%Z)) by (rewrite BYend; lia).
          stepiv F_18048 D_18048 (Z_to_bv 64 (p + n)) ltac:(zval).                                   (* [comment removed for export] *)
          stepb_ft F_1804c D_1804c ltac:(rewrite BYend, C0; apply c_eq_refl).                       (* [comment removed for export] *)
          stepn F_18050 D_18050.                                                                      (* [comment removed for export] *)
          stepn F_18054 D_18054.                                                                      (* [comment removed for export] *)
          apply mst_refl.
        * split; [gres; reflexivity|]. split; [gres; reflexivity|].
          intros x N10 N11 N12 N21. repeat (rewrite getr_other by assumption). reflexivity.
      + (* [comment removed for export] *)
        eexists. split.
        * stepb_ft F_18040 D_18040 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).     (* [comment removed for export] *)
          stepLBU F_18044 D_18044 (Z_to_bv 8 (byt (p + n)%Z))
            ltac:(unfold v_addi; unorm; replace (p + i + 1)%Z with (p + n)%Z by lia; apply BYrd; lia).        (* [comment removed for export] *)
          rewrite (u8_of_Z (byt (p + n)%Z)) by (rewrite BYend; lia).
          stepiv F_18048 D_18048 (Z_to_bv 64 (p + n)) ltac:(zval).                                   (* [comment removed for export] *)
          stepb_tk F_1804c D_1804c ltac:(rewrite BYend, C37; rewrite c_eq_Z by lia; reflexivity).  (* [comment removed for export] *)
          stepb_tk F_18040 D_18040 ltac:(rwH; rewrite BYend, C37; apply c_eq_refl).                 (* [comment removed for export] *)
          stepn F_18058 D_18058.                                                                      (* [comment removed for export] *)
          stepn F_1805c D_1805c.                                                                      (* [comment removed for export] *)
          stepLBU F_18060 D_18060 (Z_to_bv 8 d) ltac:(unfold v_addi; unorm; exact Rd).                     (* [comment removed for export] *)
          rewrite (u8_of_Z d) by lia.
          stepb_tk F_18064 D_18064 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).        (* [comment removed for export] *)
          stepn F_18080 D_18080.                                                                      (* [comment removed for export] *)
          apply mst_refl.
        * split; [gres; reflexivity|]. split; [gres; reflexivity|].
          intros x N10 N11 N12 N21. repeat (rewrite getr_other by assumption). reflexivity.
    - (* [comment removed for export] *)
      pose proof (BYlit (p + i)%Z ltac:(lia)) as BL.
      pose proof (BYlit (p + i + 1)%Z ltac:(lia)) as BL1.
      eapply (runs_trans SEGS _ (fun r1 => mkst r1 (rl dF_17f6c 0x18040) m rom)
        (fun r1 => getr r1 10 = Z_to_bv 64 (byt (p + (i + 1))%Z) /\ getr r1 21 = Z_to_bv 64 (p + (i + 1)) /\ getr r1 8 = Z_to_bv 64 37
                   /\ (forall x : reg, x <> 10 -> x <> 11 -> x <> 12 -> x <> 21 -> getr r1 x = getr r x))).
      + eexists. split.
        * stepb_ft F_18040 D_18040 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).     (* [comment removed for export] *)
          stepLBU F_18044 D_18044 (Z_to_bv 8 (byt (p + i + 1)%Z)) ltac:(unfold v_addi; unorm; apply BYrd; lia).  (* [comment removed for export] *)
          rewrite (u8_of_Z (byt (p + i + 1)%Z)) by lia.
          stepiv F_18048 D_18048 (Z_to_bv 64 (p + (i + 1))) ltac:(zval).                             (* [comment removed for export] *)
          stepb_tk F_1804c D_1804c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).            (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. replace (p + (i + 1))%Z with (p + i + 1)%Z by lia.
          split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; exact R8|].
          intros x N10 N11 N12 N21. repeat (rewrite getr_other by assumption). reflexivity.
      + cbv beta. intros r1 (Q10 & Q21 & Q8 & QK).
        destruct (IH (i + 1)%Z r1 ltac:(lia) ltac:(lia) Q10 Q21 Q8) as (r' & RUN & A & B & K').
        exists r'. split; [exact RUN|]. split; [exact A|]. split; [exact B|].
        intros x N10 N11 N12 N21. rewrite (K' x) by assumption. apply QK; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma lit_scan : forall r (f cnt l : Z),
    pcR sp0 g3 g4 r f p cnt l -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + n <= INT_MAX)%Z -> (0 <= f < 2 ^ 64)%Z ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x18094) m rom)
      /\ getr r' 3 = g3 /\ getr r' 4 = g4
      /\ getr r' 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r' 8 = Z_to_bv 64 37 /\ getr r' 9 = Z_to_bv 64 INT_MAX
      /\ getr r' 19 = Z_to_bv 64 (cnt + l) /\ getr r' 20 = Z_to_bv 64 f /\ getr r' 21 = Z_to_bv 64 (p + n)
      /\ getr r' 23 = Z_to_bv 64 p /\ getr r' 26 = Z_to_bv 64 n /\ getr r' 22 = Z_to_bv 64 n
      /\ getr r' 18 = Z_to_bv 64 (INT_MAX - (cnt + l)).
  Proof.
    intros r f cnt l (R3 & R4 & R2 & R8 & R9 & R19 & R20 & R21 & R26) Hc0 Hl Hcl Hf.
    pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    pose proof (BYlit p ltac:(lia)) as BL0.
    eapply (runs_trans SEGS _ (fun r1 => mkst r1 (rl dF_17f6c 0x18040) m rom)
      (fun r1 => getr r1 10 = Z_to_bv 64 (byt (p + 0)%Z) /\ getr r1 21 = Z_to_bv 64 (p + 0) /\ getr r1 8 = Z_to_bv 64 37
                 /\ getr r1 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r1 9 = Z_to_bv 64 2147483647
                 /\ getr r1 19 = Z_to_bv 64 (cnt + l) /\ getr r1 20 = Z_to_bv 64 f /\ getr r1 23 = Z_to_bv 64 p
                 /\ getr r1 3 = g3 /\ getr r1 4 = g4)).
    { eexists. split.
      - stepn F_1801c D_1801c; rwH; rewrite (v_subw_Z 2147483647 cnt) by lia.                     (* [comment removed for export] *)
        stepiv F_18020 D_18020 (Z_to_bv 64 l) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia). (* [comment removed for export] *)
        stepb_ft F_18024 D_18024 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).             (* [comment removed for export] *)
        stepn F_18028 D_18028.                                                                       (* [comment removed for export] *)
        stepLBU F_1802c D_1802c (Z_to_bv 8 (byt p)) ltac:(addr_norm; apply BYrd; lia).              (* [comment removed for export] *)
        rewrite (u8_of_Z (byt p)) by lia.
        stepn F_18030 D_18030; rwH; rewrite (v_addw_Z l cnt) by lia.                              (* [comment removed for export] *)
        stepb_ft F_18034 D_18034 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).               (* [comment removed for export] *)
        stepn F_18038 D_18038.                                                                       (* [comment removed for export] *)
        stepb_ft F_1803c D_1803c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).               (* [comment removed for export] *)
        apply mst_refl.
      - cbv beta. rewrite Z.add_0_r. repeat split; gres; rwH; try reflexivity; f_equal; lia. }
    cbv beta. intros r1 (Q10 & Q21 & Q8 & Q2 & Q9 & Q19 & Q20 & Q23 & Q3 & Q4).
    eapply (runs_trans SEGS _ (fun r2 => mkst r2 (rl dF_17f6c 0x18084) m rom)
      (fun r2 => getr r2 10 = Z_to_bv 64 (p + n) /\ getr r2 21 = Z_to_bv 64 (p + n)
                 /\ (forall x : reg, x <> 10 -> x <> 11 -> x <> 12 -> x <> 21 -> getr r2 x = getr r1 x))).
    { exact (scan_loop (Z.to_nat (n - 1)) 0 r1 ltac:(lia) ltac:(lia) Q10 Q21 Q8). }
    cbv beta. intros r2 (T10 & T21 & TK).
    assert (T2 : getr r2 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite TK by (intros E; discriminate E); exact Q2).
    assert (T8 : getr r2 8 = Z_to_bv 64 37) by (rewrite TK by (intros E; discriminate E); exact Q8).
    assert (T9 : getr r2 9 = Z_to_bv 64 2147483647) by (rewrite TK by (intros E; discriminate E); exact Q9).
    assert (T19 : getr r2 19 = Z_to_bv 64 (cnt + l)) by (rewrite TK by (intros E; discriminate E); exact Q19).
    assert (T20 : getr r2 20 = Z_to_bv 64 f) by (rewrite TK by (intros E; discriminate E); exact Q20).
    assert (T23 : getr r2 23 = Z_to_bv 64 p) by (rewrite TK by (intros E; discriminate E); exact Q23).
    assert (T3 : getr r2 3 = g3) by (rewrite TK by (intros E; discriminate E); exact Q3).
    assert (T4 : getr r2 4 = g4) by (rewrite TK by (intros E; discriminate E); exact Q4).
    eexists. split.
    - stepiv F_18084 D_18084 (Z_to_bv 64 n) ltac:(zval).                                            (* [comment removed for export] *)
      stepn F_18088 D_18088; rwH; rewrite (v_subw_Z 2147483647 (cnt + l)) by lia.                 (* [comment removed for export] *)
      stepb_ft F_1808c D_1808c ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).               (* [comment removed for export] *)
      stepiv F_18090 D_18090 (Z_to_bv 64 n) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia).  (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lit_tail1 : forall r (cnt' : Z),
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 8 = Z_to_bv 64 37 -> getr r 9 = Z_to_bv 64 INT_MAX ->
    getr r 19 = Z_to_bv 64 cnt' -> getr r 20 = Z_to_bv 64 0 -> getr r 21 = Z_to_bv 64 (p + n) ->
    getr r 26 = Z_to_bv 64 n -> getr r 22 = Z_to_bv 64 n -> getr r 3 = g3 -> getr r 4 = g4 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x18094) m rom) (mkst r' (rl dF_17f6c 0x1801c) m rom)
      /\ pcR sp0 g3 g4 r' 0 (p + n) cnt' n.
  Proof.
    intros r cnt' R2 R8 R9 R19 R20 R21 R26 R22 R3 R4. pose proof Hcsp as Hsp0. lay.
    eexists. split.
    - stepb_tk F_18094 D_18094 ltac:(rwH; apply c_eq_refl).                                      (* [comment removed for export] *)
      stepb_ft F_18018 D_18018 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).          (* [comment removed for export] *)
      apply mst_refl.
    - unfold pcR. repeat split; gres; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma lit_tail2 : forall r (cnt' u j : Z),
    FRM sp0 mem0 m -> FILEc m sp0 -> FILEst m sp0 u j -> (cnt' + n <= INT_MAX)%Z -> (0 <= cnt')%Z ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 8 = Z_to_bv 64 37 -> getr r 9 = Z_to_bv 64 INT_MAX ->
    getr r 19 = Z_to_bv 64 cnt' -> getr r 20 = Z_to_bv 64 (sp0 - 2400) -> getr r 21 = Z_to_bv 64 (p + n) ->
    getr r 26 = Z_to_bv 64 n -> getr r 22 = Z_to_bv 64 n -> getr r 23 = Z_to_bv 64 p ->
    getr r 3 = g3 -> getr r 4 = g4 ->
    exists r' m',
      msteps SEGS (mkst r (rl dF_17f6c 0x18094) m rom) (mkst r' (rl dF_17f6c 0x1801c) m' rom)
      /\ (pcR sp0 g3 g4 r' (sp0 - 2400) (p + n) cnt' n
          /\ frame_mod m m' (fwx_regions sp0 (sp0 - 3312))
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)).
  Proof.
    intros r cnt' u j F FC FS Hcn Hc0 R2 R8 R9 R19 R20 R21 R26 R22 R23 R3 R4. pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    pose proof (Fc_flags _ _ FC) as Cfl.
    (* [comment removed for export] *)
    set (bs := map (fun i => Z_to_bv 8 (byt (p + Z.of_nat i))) (seq 0 (Z.to_nat n))).
    assert (Hbs : rdn SEGS m (Z_to_bv 64 p) (Z.to_nat n) = Some bs).
    { subst bs. apply (rdn_of_bytes SEGS m (Z.to_nat n) p (fun q => Z_to_bv 8 (byt q))); [lia|lia|].
      intros i Hi. apply BYrd. lia. }
    eapply (runs_trans1m SEGS _ (fun r1 => mkst r1 (rl dF_17b9c 0x17b9c) m rom)
      (fun r1 => getr r1 1 = (rl dF_17f6c 0x180b4) /\ getr r1 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r1 10 = Z_to_bv 64 p
                 /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 12 = Z_to_bv 64 (sp0 - 2400)
                 /\ getr r1 8 = Z_to_bv 64 37 /\ getr r1 9 = Z_to_bv 64 2147483647 /\ getr r1 19 = Z_to_bv 64 cnt'
                 /\ getr r1 20 = Z_to_bv 64 (sp0 - 2400) /\ getr r1 21 = Z_to_bv 64 (p + n) /\ getr r1 26 = Z_to_bv 64 n
                 /\ getr r1 22 = Z_to_bv 64 n /\ getr r1 3 = g3 /\ getr r1 4 = g4)).
    { eexists. split.
      - stepb_ft F_18094 D_18094 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).        (* [comment removed for export] *)
        stepLBU F_18098 D_18098 (Z_to_bv 8 0) ltac:(addr_norm; exact Cfl).                        (* [comment removed for export] *)
        stepn F_1809c D_1809c.                                                                     (* [comment removed for export] *)
        stepb_ft F_180a0 D_180a0 ltac:(apply c_eq_refl).                                           (* [comment removed for export] *)
        stepn F_180a4 D_180a4.                                                                     (* [comment removed for export] *)
        stepn F_180a8 D_180a8.                                                                     (* [comment removed for export] *)
        stepn F_180ac D_180ac.                                                                     (* [comment removed for export] *)
        stepn F_180b0 D_180b0.                                                                     (* [comment removed for export] *)
        apply mst_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; bveq. }
    cbv beta. intros r1 (Q1 & Q2 & Q10 & Q11 & Q12 & Q8 & Q9 & Q19 & Q20 & Q21 & Q26 & Q22 & Q3 & Q4).
    destruct (fwritex_run sp0 mem0 cv rom CTX m (sp0 - 3312) u j p n bs F ltac:(lay; lia) FC FS ltac:(lia) Hbs
                ltac:(lay; lia) r1 (rl dF_17f6c 0x180b4) ltac:(rl_ret_ok) Q1 Q2 Q10 Q11 Q12)
      as (r2 & m2 & RUN & K' & A10 & ST' & FM').
    assert (T2 : getr r2 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite (K' 2%bv) by kept_reg; exact Q2).
    assert (T22 : getr r2 22 = Z_to_bv 64 n) by (rewrite (K' 22%bv) by kept_reg; exact Q22).
    eexists. exists m2. split.
    - eapply msteps_trans; [exact RUN|].
      stepn F_180b4 D_180b4.                                                                       (* [comment removed for export] *)
      stepb_ft F_18018 D_18018 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).          (* [comment removed for export] *)
      apply mst_refl.
    - split; [|split; [exact FM' | exact ST']].
      unfold pcR. repeat split; gres; try assumption;
        first [ rewrite (K' 3%bv) by kept_reg | rewrite (K' 4%bv) by kept_reg
              | rewrite (K' 8%bv) by kept_reg | rewrite (K' 9%bv) by kept_reg | rewrite (K' 19%bv) by kept_reg
              | rewrite (K' 20%bv) by kept_reg | rewrite (K' 21%bv) by kept_reg | rewrite (K' 26%bv) by kept_reg ];
        assumption.
  Qed.
End LIT.
