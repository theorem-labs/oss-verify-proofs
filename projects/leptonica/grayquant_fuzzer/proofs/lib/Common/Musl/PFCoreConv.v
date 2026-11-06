(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_18000_19000 RImg.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFCore PFPop.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).

Section CONV.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.

  Ltac sok := soks CTX.
  Variables (g3 g4 : word).     (* [comment removed for export] *)

  Variables (m : word -> option byte) (p : Z) (c : fconv).
  Hypothesis Hp : (IMG_LO <= p /\ p + conv_len c < IMG_TOP)%Z.
  Hypothesis B0 : rdn SEGS m (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 37].
  Hypothesis B1 : rdn SEGS m (Z_to_bv 64 (p + 1)) 1 = Some [Z_to_bv 8 (conv_c1 c)].
  Hypothesis B2 : c = Czu -> rdn SEGS m (Z_to_bv 64 (p + 2)) 1 = Some [Z_to_bv 8 117].

  (* [comment removed for export] *)
  Lemma conv_head : forall r (f cnt l : Z),
    pcR sp0 g3 g4 r f p cnt l -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z -> (0 <= f < 2 ^ 64)%Z ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x18094) m rom)
      /\ getr r' 3 = g3 /\ getr r' 4 = g4
      /\ getr r' 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r' 8 = Z_to_bv 64 37 /\ getr r' 9 = Z_to_bv 64 INT_MAX
      /\ getr r' 19 = Z_to_bv 64 (cnt + l) /\ getr r' 20 = Z_to_bv 64 f /\ getr r' 21 = Z_to_bv 64 p
      /\ getr r' 23 = Z_to_bv 64 p /\ getr r' 26 = Z_to_bv 64 0 /\ getr r' 22 = Z_to_bv 64 0
      /\ getr r' 18 = Z_to_bv 64 (INT_MAX - (cnt + l)).
  Proof.
    intros r f cnt l (R3 & R4 & R2 & R8 & R9 & R19 & R20 & R21 & R26) Hc0 Hl Hcl Hf.
    pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    assert (C1 : (0 <= conv_c1 c <= 255 /\ conv_c1 c <> 37)%Z) by (destruct c; cbn; lia).
    assert (CL : (2 <= conv_len c <= 3)%Z) by (destruct c; cbn; lia).
    eexists. split.
    - stepn F_1801c D_1801c; rwH; rewrite (v_subw_Z 2147483647 cnt) by lia.                     (* [comment removed for export] *)
      stepiv F_18020 D_18020 (Z_to_bv 64 l) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia). (* [comment removed for export] *)
      stepb_ft F_18024 D_18024 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).             (* [comment removed for export] *)
      stepn F_18028 D_18028.                                                                       (* [comment removed for export] *)
      stepLBU F_1802c D_1802c (Z_to_bv 8 37) ltac:(addr_norm; exact B0).                          (* [comment removed for export] *)
      stepn F_18030 D_18030; rwH; rewrite (v_addw_Z l cnt) by lia.                              (* [comment removed for export] *)
      stepb_ft F_18034 D_18034 ltac:(cond_vm).                                    (* [comment removed for export] *)
      stepn F_18038 D_18038.                                                                       (* [comment removed for export] *)
      stepb_ft F_1803c D_1803c ltac:(cond_vm).                                    (* [comment removed for export] *)
      stepb_tk F_18040 D_18040 ltac:(rwH; apply c_eq_refl).                                       (* [comment removed for export] *)
      stepn F_18058 D_18058.                                                                       (* [comment removed for export] *)
      stepn F_1805c D_1805c.                                                                       (* [comment removed for export] *)
      stepLBU F_18060 D_18060 (Z_to_bv 8 (conv_c1 c)) ltac:(addr_norm; exact B1).                (* [comment removed for export] *)
      rewrite (u8_of_Z (conv_c1 c)) by lia.
      stepb_tk F_18064 D_18064 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).          (* [comment removed for export] *)
      stepn F_18080 D_18080.                                                                       (* [comment removed for export] *)
      stepiv F_18084 D_18084 (Z_to_bv 64 0) ltac:(zval).                                           (* [comment removed for export] *)
      stepn F_18088 D_18088; rwH; rewrite (v_subw_Z 2147483647 (l + cnt)) by lia.                (* [comment removed for export] *)
      stepb_ft F_1808c D_1808c ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).              (* [comment removed for export] *)
      stepn F_18090 D_18090.                                                                       (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma conv_out0_p1 : forall r,
    getr r 20 = Z_to_bv 64 0 -> getr r 22 = Z_to_bv 64 0 ->
    exists r', msteps SEGS (mkst r (rl dF_17f6c 0x18094) m rom) (mkst r' (rl dF_17f6c 0x180b8) m rom)
               /\ (forall x : reg, getr r' x = getr r x).
  Proof.
    intros r R20 R22. eexists. split.
    - stepb_tk F_18094 D_18094 ltac:(rwH; apply c_eq_refl).                                      (* [comment removed for export] *)
      stepb_tk F_18018 D_18018 ltac:(rwH; apply c_eq_refl).                                      (* [comment removed for export] *)
      apply mst_refl.
    - intros x. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma conv_out0_p2 : forall r (u j : Z),
    FRM sp0 mem0 m -> FILEc m sp0 -> FILEst m sp0 u j ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 20 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 22 = Z_to_bv 64 0 -> getr r 23 = Z_to_bv 64 p ->
    exists r' m',
      msteps SEGS (mkst r (rl dF_17f6c 0x18094) m rom) (mkst r' (rl dF_17f6c 0x180b8) m' rom)
      /\ (agree_but [1%bv] r r' /\ getr r' 2 = Z_to_bv 64 (sp0 - 3312)
          /\ frame_mod m m' (fwx_regions sp0 (sp0 - 3312))
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)).
  Proof.
    intros r u j F FC FS R2 R20 R22 R23. pose proof Hcsp as Hsp0. lay.
    assert (CL : (2 <= conv_len c <= 3)%Z) by (destruct c; cbn; lia).
    pose proof (Fc_flags _ _ FC) as Cfl.
    assert (Hbs : rdn SEGS m (Z_to_bv 64 p) (Z.to_nat 0) = Some []) by reflexivity.
    eapply (runs_trans1m SEGS _ (fun r1 => mkst r1 (rl dF_17b9c 0x17b9c) m rom)
      (fun r1 => getr r1 1 = (rl dF_17f6c 0x180b4) /\ getr r1 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r1 10 = Z_to_bv 64 p
                 /\ getr r1 11 = Z_to_bv 64 0 /\ getr r1 12 = Z_to_bv 64 (sp0 - 2400)
                 /\ getr r1 22 = Z_to_bv 64 0 /\ agree_but [1] r r1)).
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
      - postR. }
    cbv beta. intros r1 (Q1 & Q2 & Q10 & Q11 & Q12 & Q22 & QA).
    destruct (fwritex_run sp0 mem0 cv rom CTX m (sp0 - 3312) u j p 0 [] F ltac:(lay; lia) FC FS ltac:(lia) Hbs
                ltac:(lay; lia) r1 (rl dF_17f6c 0x180b4) ltac:(rl_ret_ok) Q1 Q2 Q10 Q11 Q12)
      as (r2 & m2 & RUN & K' & A10 & ST' & FM').
    assert (T22 : getr r2 22 = Z_to_bv 64 0) by (rewrite (K' 22%bv) by kept_reg; exact Q22).
    eexists. exists m2. split.
    - eapply msteps_trans; [exact RUN|].
      stepn F_180b4 D_180b4.                                                                       (* [comment removed for export] *)
      stepb_tk F_18018 D_18018 ltac:(rwH; apply c_eq_refl).                                      (* [comment removed for export] *)
      apply mst_refl.
    - split; [|split; [|split; [exact FM' | exact ST']]].
      + eapply agree_but_keeps_cs; [exact QA | exact K'].
      + rewrite (K' 2%bv) by kept_reg. exact Q2.
  Qed.

  (* [comment removed for export] *)
  Ltac img_rd F C :=
    rl_addfold; rl_norm_s; rewrite ?v_addi_0; rl_addfold;
    lazymatch goal with
    | |- rdn _ _ (rl ?d ?c) ?n = _ =>
        change (rl d c) with (Z_to_bv 64 (c + d));
        rewrite (FRM_img _ _ _ CTX _ _ _ F); [exact C | lay; lia | lay; cbn; lia]
    end.

  (* [comment removed for export] *)
  Ltac parse_prefix F CH :=
      stepLBU constr:(F_180b8) constr:(D_180b8) (Z_to_bv 8 CH) ltac:(addr_norm; exact B1);                         (* [comment removed for export] *)
      stepiv constr:(F_180bc) constr:(D_180bc) (Z_to_bv 64 (p + 1)) ltac:(zval);                                    (* [comment removed for export] *)
      stepn constr:(F_180c0) constr:(D_180c0);                                                                       (* [comment removed for export] *)
      stepn constr:(F_180c4) constr:(D_180c4);                                                                       (* [comment removed for export] *)
      stepn constr:(F_180c8) constr:(D_180c8);                                                                       (* [comment removed for export] *)
      stepb_tk constr:(F_180cc) constr:(D_180cc) ltac:(cond_vm);                                    (* [comment removed for export] *)
      stepn constr:(F_180fc) constr:(D_180fc);                                                                       (* [comment removed for export] *)
      stepLD8 constr:(F_18100) constr:(D_18100) (Z_to_bv 64 75913);                                                 (* [comment removed for export] *)
      stepn constr:(F_18104) constr:(D_18104);                                                                       (* [comment removed for export] *)
      stepn constr:(F_18108) constr:(D_18108);                                                                       (* [comment removed for export] *)
      stepb_tk constr:(F_1810c) constr:(D_1810c) ltac:(cond_vm);                                    (* [comment removed for export] *)
      stepn constr:(F_18188) constr:(D_18188);                                                                       (* [comment removed for export] *)
      stepn constr:(F_1818c) constr:(D_1818c);                                                                       (* [comment removed for export] *)
      stepb_ft constr:(F_18190) constr:(D_18190) ltac:(cond_vm);                                    (* [comment removed for export] *)
      stepn constr:(F_18194) constr:(D_18194);                                                                       (* [comment removed for export] *)
      stepn constr:(F_18198) constr:(D_18198);                                                                       (* [comment removed for export] *)
      stepn constr:(F_1819c) constr:(D_1819c);                                                                       (* [comment removed for export] *)
      stepb_tk constr:(F_181a0) constr:(D_181a0) ltac:(cond_vm);                                    (* [comment removed for export] *)
      stepLBU constr:(F_1827c) constr:(D_1827c) (Z_to_bv 8 CH) ltac:(addr_norm; exact B1);                         (* [comment removed for export] *)
      stepn constr:(F_18280) constr:(D_18280);                                                                       (* [comment removed for export] *)
      stepb_tk constr:(F_18284) constr:(D_18284) ltac:(cond_vm);                                    (* [comment removed for export] *)
      stepn constr:(F_182d4) constr:(D_182d4);                                                                       (* [comment removed for export] *)
      stepn constr:(F_182d8) constr:(D_182d8);                                                                       (* [comment removed for export] *)
      stepn constr:(F_182dc) constr:(D_182dc);                                                                       (* [comment removed for export] *)
      stepn constr:(F_182e0) constr:(D_182e0);                                                                       (* [comment removed for export] *)
      stepn constr:(F_182e4) constr:(D_182e4);                                                                       (* [comment removed for export] *)
      stepn constr:(F_182e8) constr:(D_182e8);                                                                       (* [comment removed for export] *)
      stepn constr:(F_183b4) constr:(D_183b4);                                                                       (* [comment removed for export] *)
      stepn constr:(F_183b8) constr:(D_183b8).                                                                       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac parse_state F C BY CH TY POS :=
      stepLBU constr:(F_183bc) constr:(D_183bc) (Z_to_bv 8 CH) ltac:(addr_norm; exact BY);                         (* [comment removed for export] *)
      stepn constr:(F_183c0) constr:(D_183c0);                                                                       (* [comment removed for export] *)
      stepb_ft constr:(F_183c4) constr:(D_183c4) ltac:(cond_vm);                                    (* [comment removed for export] *)
      stepn constr:(F_183c8) constr:(D_183c8);                                                                       (* [comment removed for export] *)
      stepn constr:(F_183cc) constr:(D_183cc);                                                                       (* [comment removed for export] *)
      stepn constr:(F_183d0) constr:(D_183d0);                                                                       (* [comment removed for export] *)
      stepn constr:(F_183d4) constr:(D_183d4);                                                                       (* [comment removed for export] *)
      stepn constr:(F_183d8) constr:(D_183d8);                                                                       (* [comment removed for export] *)
      stepn constr:(F_183dc) constr:(D_183dc);                                                                       (* [comment removed for export] *)
      stepLBU constr:(F_183e0) constr:(D_183e0) (Z_to_bv 8 TY) ltac:(img_rd F C);                                     (* [comment removed for export] *)
      stepn constr:(F_183e4) constr:(D_183e4);                                                                       (* [comment removed for export] *)
      stepiv constr:(F_183e8) constr:(D_183e8) (Z_to_bv 64 POS) ltac:(zval).                                         (* [comment removed for export] *)

  Lemma conv_parse : forall r regs ret,
    FRM sp0 mem0 m -> PCc m sp0 cv regs ret ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 21 = Z_to_bv 64 p ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x180b8) m rom) (mkst r' (rl dF_17f6c 0x18434) m rom)
      /\ getr r' 11 = Z_to_bv 64 (conv_type c) /\ getr r' 27 = Z_to_bv 64 (conv_ps c)
      /\ getr r' 21 = Z_to_bv 64 (p + conv_len c)
      /\ getr r' 5 = Z_to_bv 64 0 /\ getr r' 25 = Z_to_bv 64 18446744073709551615
      /\ getr r' 24 = Z_to_bv 64 0 /\ getr r' 22 = Z_to_bv 64 0 /\ getr r' 10 = Z_to_bv 64 18446744073709551615
      /\ (forall x : reg, In x [3; 4; 2; 8; 9; 18; 19; 20; 23; 26]%bv -> getr r' x = getr r x).
  Proof.
    intros r regs ret F PC R2 R21. pose proof Hcsp as Hsp0. lay.
    pose proof (Pc80 _ _ _ _ _ PC) as C80.
    destruct c; cbn [conv_c1 conv_type conv_ps conv_len] in *.
    - (* [comment removed for export] *) eexists. split.
      + parse_prefix F 115%Z.
        parse_state F img_11622_1 B1 115%Z 9%Z (p + 2)%Z.
        stepb_ft F_183ec D_183ec ltac:(cond_vm).                                  (* [comment removed for export] *)
        stepn F_183f0 D_183f0.                                                                     (* [comment removed for export] *)
        stepb_ft F_183f4 D_183f4 ltac:(cond_vm).                                  (* [comment removed for export] *)
        stepb_ft F_183f8 D_183f8 ltac:(cond_vm).                                  (* [comment removed for export] *)
        stepb_tk F_183fc D_183fc ltac:(cond_vm).                                  (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; try reflexivity; try (f_equal; lia).
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    - (* [comment removed for export] *) eexists. split.
      + parse_prefix F 100%Z.
        parse_state F img_11613_1 B1 100%Z 10%Z (p + 2)%Z.
        stepb_ft F_183ec D_183ec ltac:(cond_vm).
        stepn F_183f0 D_183f0.
        stepb_ft F_183f4 D_183f4 ltac:(cond_vm).
        stepb_ft F_183f8 D_183f8 ltac:(cond_vm).
        stepb_tk F_183fc D_183fc ltac:(cond_vm).
        apply mst_refl.
      + repeat split; gres; try reflexivity; try (f_equal; lia).
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    - (* [comment removed for export] *) eexists. split.
      + parse_prefix F 117%Z.
        parse_state F img_11624_1 B1 117%Z 11%Z (p + 2)%Z.
        stepb_ft F_183ec D_183ec ltac:(cond_vm).
        stepn F_183f0 D_183f0.
        stepb_ft F_183f4 D_183f4 ltac:(cond_vm).
        stepb_ft F_183f8 D_183f8 ltac:(cond_vm).
        stepb_tk F_183fc D_183fc ltac:(cond_vm).
        apply mst_refl.
      + repeat split; gres; try reflexivity; try (f_equal; lia).
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    - (* [comment removed for export] *) pose proof (B2 eq_refl) as B2'. eexists. split.
      + parse_prefix F 122%Z.
        parse_state F img_11629_1 B1 122%Z 6%Z (p + 2)%Z.
        stepb_tk F_183ec D_183ec ltac:(cond_vm).                                  (* [comment removed for export] *)
        parse_state F img_11780_1 B2' 117%Z 20%Z (p + 3)%Z.
        stepb_ft F_183ec D_183ec ltac:(cond_vm).                                  (* [comment removed for export] *)
        stepn F_183f0 D_183f0.
        stepb_ft F_183f4 D_183f4 ltac:(cond_vm).
        stepb_ft F_183f8 D_183f8 ltac:(cond_vm).
        stepb_tk F_183fc D_183fc ltac:(cond_vm).
        apply mst_refl.
      + repeat split; gres; try reflexivity; try (f_equal; lia).
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma conv_pass1_exit : forall r,
    getr r 20 = Z_to_bv 64 0 ->
    exists r', msteps SEGS (mkst r (rl dF_17f6c 0x18434) m rom) (mkst r' (rl dF_17f6c 0x18d48) m rom)
               /\ getr r' 19 = Z_to_bv 64 0 /\ (forall x : reg, x <> 19 -> getr r' x = getr r x).
  Proof.
    intros r R20. eexists. split.
    - stepb_tk F_18434 D_18434 ltac:(rwH; apply c_eq_refl).                                      (* [comment removed for export] *)
      stepn F_18cc4 D_18cc4.                                                                       (* [comment removed for export] *)
      stepn F_18cc8 D_18cc8.                                                                       (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity|]. intros x Hx. rewrite getr_other by exact Hx. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma conv_pop : forall r regs ret (k : Z) (w : word),
    FRM sp0 mem0 m -> PCc m sp0 cv regs ret ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56 + 8 * k)) -> VAslot m sp0 k w -> (0 <= k < 7)%Z ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 20 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 11 = Z_to_bv 64 (conv_type c) -> getr r 5 = Z_to_bv 64 0 ->
    exists r' (v : word),
      msteps SEGS (mkst r (rl dF_17f6c 0x18434) m rom) (mkst r' (rl dF_17f6c 0x1844c) (popM sp0 m k v) rom)
      /\ ((c = Cs \/ c = Czu) -> v = w)
      /\ getr r' 5 = Z_to_bv 64 0
      /\ (forall x : reg, In x [3; 4; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros r regs ret k w F PC Hap2 Hslot Hk R2 R20 R11 R5. pose proof Hcsp as Hsp0. lay.
    assert (CL : (2 <= conv_len c <= 3)%Z) by (destruct c; cbn; lia).
    pose proof (Pc72 _ _ _ _ _ PC) as C72.
    assert (S1 : exists r1, msteps SEGS (mkst r (rl dF_17f6c 0x18434) m rom) (mkst r1 (rl dF_18d9c 0x18d9c) m rom)
              /\ (getr r1 1 = (rl dF_17f6c 0x18448) /\ getr r1 10 = Z_to_bv 64 (sp0 - 3200)
                 /\ getr r1 11 = Z_to_bv 64 (conv_type c) /\ getr r1 12 = Z_to_bv 64 (sp0 - 2768)
                 /\ getr r1 26 = Z_to_bv 64 0
                 /\ (forall x : reg, In x [3; 4; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv -> getr r1 x = getr r x))).
    { eexists. split.
      - stepb_ft F_18434 D_18434 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).      (* [comment removed for export] *)
        stepiv F_18438 D_18438 (Z_to_bv 64 (sp0 - 3200)) ltac:(zval).                             (* [comment removed for export] *)
        stepLD8 F_1843c D_1843c (Z_to_bv 64 (sp0 - 2768)).                                        (* [comment removed for export] *)
        stepn F_18440 D_18440.                                                                     (* [comment removed for export] *)
        stepn F_18444 D_18444.                                                                     (* [comment removed for export] *)
        apply mst_refl.
      - split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; exact R11|]. split; [gres; reflexivity|].
        split; [gres; exact R5|].
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx. }
    destruct S1 as (r1 & RUN1 & Q1 & Q10 & Q11 & Q12 & Q26 & QK).
    destruct (pop_arg_run sp0 mem0 cv rom CTX m k w (conv_type c) F Hap2 Hslot Hk r1 (rl dF_17f6c 0x18448)
                ltac:(rl_ret_ok) Q1 Q10 Q11 Q12 ltac:(destruct c; cbn; lia))
      as (r2 & v & RUN & Hv & K2).
    eexists. exists v. split; [|split; [|split]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN|].
      stepn F_18448 D_18448.                                                                       (* [comment removed for export] *)
      apply mst_refl.
    - intros Hc. apply Hv. destruct Hc as [-> | ->]; cbn; lia.
    - gres. rewrite K2 by (intros E; discriminate E). exact Q26.
    - intros x Hx. pose proof (QK x Hx) as E. cbv [In] in Hx.
      repeat (destruct Hx as [<-|Hx]; [gres; rewrite K2 by (intros E'; discriminate E'); exact E|]). destruct Hx.
  Qed.

  (* [comment removed for export] *)
  Definition conv_tgt (c0 : fconv) : word :=
    match c0 with Cs => (rl dF_17f6c 0x1854c) | Cd => (rl dF_17f6c 0x18504) | _ => (rl dF_17f6c 0x1863c) end.

  Ltac disp_steps F C BY T TBL FT :=
      stepLBU constr:(F_1844c) constr:(D_1844c) (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve);                           (* [comment removed for export] *)
      stepn constr:(F_18450) constr:(D_18450);                                                                       (* [comment removed for export] *)
      stepb_ft constr:(F_18454) constr:(D_18454) ltac:(apply c_eq_refl);                                             (* [comment removed for export] *)
      stepLBU constr:(F_18458) constr:(D_18458) (Z_to_bv 8 T) ltac:(addr_norm; rdn_solve);                           (* [comment removed for export] *)
      stepn constr:(F_1845c) constr:(D_1845c); rwH;                                                                  (* [comment removed for export] *)
      stepn constr:(F_18460) constr:(D_18460);                                                                       (* [comment removed for export] *)
      stepn constr:(F_18464) constr:(D_18464);                                                                       (* [comment removed for export] *)
      stepn constr:(F_18468) constr:(D_18468);                                                                       (* [comment removed for export] *)
      stepn constr:(F_1846c) constr:(D_1846c);                                                                       (* [comment removed for export] *)
      stepb_tk constr:(F_18470) constr:(D_18470) ltac:(cond_vm);                                                     (* [comment removed for export] *)
      stepn constr:(F_18478) constr:(D_18478); rwH;                                                                  (* [comment removed for export] *)
      stepLD8 constr:(F_1847c) constr:(D_1847c) (Z_to_bv 64 18446744073709486079);                                  (* [comment removed for export] *)
      stepn constr:(F_18480) constr:(D_18480); rwH;                                                                  (* [comment removed for export] *)
      stepb_tk constr:(F_18484) constr:(D_18484) ltac:(cond_vm);                                                     (* [comment removed for export] *)
      stepn constr:(F_1848c) constr:(D_1848c);                                                                       (* [comment removed for export] *)
      stepn constr:(F_18490) constr:(D_18490);                                                                       (* [comment removed for export] *)
      stepb_ft constr:(F_18494) constr:(D_18494) ltac:(cond_vm);                                                     (* [comment removed for export] *)
      stepn constr:(F_18498) constr:(D_18498);                                                                       (* [comment removed for export] *)
      stepn constr:(F_1849c) constr:(D_1849c);                                                                       (* [comment removed for export] *)
      stepn constr:(F_184a0) constr:(D_184a0);                                                                       (* [comment removed for export] *)
      stepn constr:(F_184a4) constr:(D_184a4);                                                                       (* [comment removed for export] *)
      stepLD constr:(F_184a8) constr:(D_184a8) (W4 TBL) (Z_to_bv 64 TBL) ltac:(img_rd F C) ltac:(apply bytes_le_to_Z_4; u_norm; lia);  (* [comment removed for export] *)
      rewrite (v_lw_small TBL) by lia;
      stepn constr:(F_184ac) constr:(D_184ac);                                                                       (* [comment removed for export] *)
      rewrite rl_rel_add;
      stepretK constr:(F_184b0) constr:(D_184b0) FT ltac:(rwH; reflexivity).                                          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma conv_dispatch : forall (m1 : word -> option byte) r regs ret,
    FRM sp0 mem0 m1 -> PCc m1 sp0 cv regs ret -> FILEc m1 sp0 ->
    rdn SEGS m1 (Z_to_bv 64 (p + 1)) 1 = Some [Z_to_bv 8 (conv_c1 c)] ->
    (c = Czu -> rdn SEGS m1 (Z_to_bv 64 (p + 2)) 1 = Some [Z_to_bv 8 117]) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 20 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 21 = Z_to_bv 64 (p + conv_len c) -> getr r 24 = Z_to_bv 64 0 -> getr r 27 = Z_to_bv 64 (conv_ps c) ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x1844c) m1 rom) (mkst r' (conv_tgt c) m1 rom)
      /\ getr r' 26 = Z_to_bv 64 0 /\ getr r' 16 = Z_to_bv 64 (conv_last c)
      /\ (forall x : reg, In x [3; 4; 2; 5; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros m1 r regs ret F1 PC1 FC1 C1 C2 R2 R20 R21 R24 R27. pose proof Hcsp as Hsp0. lay.
    pose proof (Pc48 _ _ _ _ _ PC1) as P48. pose proof (Fc_flags _ _ FC1) as Cfl.
    destruct c; cbn [conv_c1 conv_len conv_ps conv_tgt conv_last] in *.
    - assert (BT : rdn SEGS m1 (Z_to_bv 64 (p + 2 - 1)) 1 = Some [Z_to_bv 8 115]) by (replace (p + 2 - 1)%Z with (p + 1)%Z by lia; exact C1).
      eexists. split.
      + disp_steps F1 img_11570_4 BT 115%Z ((0x1854c + dF_17f6c) - (0x114a8 + dA_114a8))%Z F_1854c. apply mst_refl.
      + split; [gres; reflexivity|]. split; [gres; reflexivity|].
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    - assert (BT : rdn SEGS m1 (Z_to_bv 64 (p + 2 - 1)) 1 = Some [Z_to_bv 8 100]) by (replace (p + 2 - 1)%Z with (p + 1)%Z by lia; exact C1).
      eexists. split.
      + disp_steps F1 img_11534_4 BT 100%Z ((0x18504 + dF_17f6c) - (0x114a8 + dA_114a8))%Z F_18504. apply mst_refl.
      + split; [gres; reflexivity|]. split; [gres; reflexivity|].
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    - assert (BT : rdn SEGS m1 (Z_to_bv 64 (p + 2 - 1)) 1 = Some [Z_to_bv 8 117]) by (replace (p + 2 - 1)%Z with (p + 1)%Z by lia; exact C1).
      eexists. split.
      + disp_steps F1 img_11578_4 BT 117%Z ((0x1863c + dF_17f6c) - (0x114a8 + dA_114a8))%Z F_1863c. apply mst_refl.
      + split; [gres; reflexivity|]. split; [gres; reflexivity|].
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    - pose proof (C2 eq_refl) as BT.
      eexists. split.
      + disp_steps F1 img_11578_4 BT 117%Z ((0x1863c + dF_17f6c) - (0x114a8 + dA_114a8))%Z F_1863c. apply mst_refl.
      + split; [gres; reflexivity|]. split; [gres; reflexivity|].
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.
End CONV.
