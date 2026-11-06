(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17LeptStderr V17LeptBase V17_code_133ec_14000 V17_code_14000_15000 V17_code_15000_16000 V17_code_16000_17000.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Lemma or_2_2 : v_or (Z_to_bv 64 2) (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section KernSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU17} {P16 : V17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Definition KF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (w h d : Z) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 44)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 52)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 44)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
      (Z_to_bv 64 (s - 52)) (word_to_le_bytes 4 (Z_to_bv 64 d)).

  Lemma KF_out : forall m s ret regs w h d (x : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 64 <= u x < s)%Z -> KF m s ret regs w h d x = m x.
  Proof.
    intros m s ret regs w h d x Hs Hs64 N1. unfold KF.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition kcells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) (w h : Z) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
    rdn SEGS M (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
    rdn SEGS M (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)).

  Lemma kcells_KF : forall m s ret regs w h d, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kcells (KF m s ret regs w h d) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) w h.
  Proof.
    intros m s ret regs w h d Hs Hs64. unfold kcells, KF. repeat split; rdn_chain.
  Qed.

  Lemma kcells_frame : forall M M' s ret s0v s1v s2v s3v w h, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kcells M s ret s0v s1v s2v s3v w h -> (forall x : word, (s - 48 <= u x < s)%Z -> M' x = M x) -> kcells M' s ret s0v s1v s2v s3v w h.
  Proof.
    intros M M' s ret s0v s1v s2v s3v w h Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7) E.
    unfold kcells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6 | rewrite <- C7];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (0x20000 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> (4096 <= pix)%Z -> (pix + 64 <= s - 64)%Z -> (s mod 16 = 0)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 2 -> getr regs 12 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x16158 : word) m rom) (mkst regs' (0x16198 : word) (KF m s ret regs (p_w v) (p_h v) (p_d v)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 2
      /\ getr regs' 10 = Z_to_bv 64 (p_d v) /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 PX Gp Hpix Hs16 ALp SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_d _ WF).
    assert (AL44 : ((s - 44) mod 4 = 0)%Z) by (replace (s - 44)%Z with (s + (-44))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (AL48 : ((s - 48) mod 4 = 0)%Z) by (replace (s - 48)%Z with (s + (-48))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (AL52 : ((s - 52) mod 4 = 0)%Z) by (replace (s - 52)%Z with (s + (-52))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    eexists. split.
    - zv F_1605c D_1605c (Z_to_bv 64 (s - 64)).
      stepST F_16060 D_16060 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16064 D_16064 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_16068 D_16068 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1606c D_1606c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_16070 D_16070 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_16074 D_16074 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_16078 D_16078. sn F_1607c D_1607c. sn F_16080 D_16080.
      zv F_16084 D_16084 (Z_to_bv 64 (s - 44)). zv F_16088 D_16088 (Z_to_bv 64 (s - 48)). zv F_1608c D_1608c (Z_to_bv 64 (s - 52)).
      sn F_16090 D_16090.
      (* [comment removed for export] *)
      zand F_14148 D_14148 andi_3 AL44.
      stepb_ft F_1414c D_1414c ltac:(condZ).
      stepb_ft F_14150 D_14150 ltac:(condZ).
      stepST F_14154 D_14154 (Z_to_bv 64 (s - 44)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_14158 D_14158 andi_3 AL48.
      stepb_ft F_1415c D_1415c ltac:(condZ).
      stepb_ft F_14160 D_14160 ltac:(condZ).
      stepST F_14164 D_14164 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_14168 D_14168 andi_3 AL52.
      stepb_ft F_1416c D_1416c ltac:(condZ).
      stepb_ft F_14170 D_14170 ltac:(condZ).
      stepST F_14174 D_14174 (Z_to_bv 64 (s - 52)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_14178 D_14178 ltac:(condZ).
      zand F_1417c D_1417c andi_7 ALp.
      stepb_ft F_14180 D_14180 ltac:(condZ).
      zlit F_14184 D_14184 (Z_to_bv 64 0).
      stepb_ft F_14188 D_14188 ltac:(condZ).
      stepLD F_1418c D_1418c (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_14190 D_14190 (Z_to_bv 64 (s - 44)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_14194 D_14194 ltac:(condZ).
      zlit F_14198 D_14198 (Z_to_bv 64 0).
      stepb_ft F_1419c D_1419c ltac:(condZ).
      stepLD F_141a0 D_141a0 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_141a4 D_141a4 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      stepb_ft F_141a8 D_141a8 ltac:(condZ).
      zlit F_141ac D_141ac (Z_to_bv 64 0).
      stepb_ft F_141b0 D_141b0 ltac:(condZ).
      stepLD F_141b4 D_141b4 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia.
      stepST F_141b8 D_141b8 (Z_to_bv 64 (s - 52)) (Z_to_bv 64 (p_d v)) ltac:(sok_in SOK).
      sn F_141bc D_141bc.
      stepret F_141c0 D_141c0 (0x16190 : word) ltac:(bveq).
      stepLD F_16094 D_16094 (word_to_le_bytes 4 (Z_to_bv 64 (p_d v))) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_d v)) by lia.
      sn F_16098 D_16098.
      unfold KF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_B : forall regs m (s w h : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= w < 2 ^ 31)%Z -> (3 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 8 -> getr regs 11 = Z_to_bv 64 8 ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x16198 : word) m rom) (mkst regs' (0x15ca0 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x161b8 /\ getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 w
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh Rw Rh H2 H10 H11 H18 H19. eexists. split.
    - stepb_ft F_1609c D_1609c ltac:(condZ).                                          (* [comment removed for export] *)
      stepat F_160a0 D_160a0 (Z_to_bv 64 2) ltac:(gres; pin; imm_norm; exact or_2_2).  (* [comment removed for export] *)
      stepb_ft F_160a4 D_160a4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_160a8 D_160a8 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      stepb_ft F_160ac D_160ac ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_160b0 D_160b0 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepb_ft F_160b4 D_160b4 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_160b8 D_160b8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_Bd : forall regs m (s d : Z),
    (0 <= d < 2 ^ 31)%Z -> d <> 8%Z ->
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) ->
    rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 8 ->
    exists regs',
      msteps SEGS (mkst regs (0x16198 : word) m rom) (mkst regs' (0x13ba4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x1626c
      /\ getr regs' 10 = Z_to_bv 64 0x10bf6 /\ getr regs' 11 = Z_to_bv 64 0x10b6d /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s d Hd NE Rg Rs H2 H10 H11. eexists. split.
    - stepb_tk F_1609c D_1609c ltac:(condZ).
      sn F_1611c D_1611c.
      stepLD F_16120 D_16120 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16124 D_16124 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16128 D_16128.
      stepb_ft F_1612c D_1612c ltac:(condZ).
      sn F_16130 D_16130. sn F_16134 D_16134. sn F_16138 D_16138. sn F_1613c D_1613c. sn F_16140 D_16140.
      sn F_16168 D_16168. sn F_1616c D_1616c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_Bc : forall regs m (s w h : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (h <= 2 \/ w <= 2)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) ->
    rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 8 -> getr regs 11 = Z_to_bv 64 8 ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x16198 : word) m rom) (mkst regs' (0x13ba4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x1626c
      /\ getr regs' 10 = Z_to_bv 64 0x10aca /\ getr regs' 11 = Z_to_bv 64 0x10b6d /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh HC Rw Rh Rg Rs H2 H10 H11 H18 H19.
    destruct (Z_lt_ge_dec 2 h) as [Hh3|Hh2].
    - assert (Hw2 : (w <= 2)%Z) by lia. eexists. split.
      + stepb_ft F_1609c D_1609c ltac:(condZ).
        stepat F_160a0 D_160a0 (Z_to_bv 64 2) ltac:(gres; pin; imm_norm; exact or_2_2).
        stepb_ft F_160a4 D_160a4 ltac:(condZ).
        stepLD F_160a8 D_160a8 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepb_ft F_160ac D_160ac ltac:(condZ).
        stepLD F_160b0 D_160b0 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small w) by lia.
        stepb_tk F_160b4 D_160b4 ltac:(condZ).                                        (* [comment removed for export] *)
        sn F_16144 D_16144.
        stepLD F_16148 D_16148 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_1614c D_1614c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_16150 D_16150.
        stepb_ft F_16154 D_16154 ltac:(condZ).
        sn F_16158 D_16158. sn F_1615c D_1615c. sn F_16160 D_16160. sn F_16164 D_16164.
        sn F_16168 D_16168. sn F_1616c D_1616c.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + stepb_ft F_1609c D_1609c ltac:(condZ).
        stepat F_160a0 D_160a0 (Z_to_bv 64 2) ltac:(gres; pin; imm_norm; exact or_2_2).
        stepb_ft F_160a4 D_160a4 ltac:(condZ).
        stepLD F_160a8 D_160a8 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
        rewrite (v_lw_small h) by lia.
        stepb_tk F_160ac D_160ac ltac:(condZ).                                        (* [comment removed for export] *)
        sn F_16144 D_16144.
        stepLD F_16148 D_16148 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_1614c D_1614c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_16150 D_16150.
        stepb_ft F_16154 D_16154 ltac:(condZ).
        sn F_16158 D_16158. sn F_1615c D_1615c. sn F_16160 D_16160. sn F_16164 D_16164.
        sn F_16168 D_16168. sn F_1616c D_1616c.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_X0 : forall regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x1626c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v Hs Hs64 Hret R1 R2 R3 R4 R5 H2 H10. eexists. split.
    - sn F_16170 D_16170. sn F_16174 D_16174.
      sn F_1617c D_1617c.
      stepLD8 F_16180 D_16180 ret. stepLD8 F_16184 D_16184 s0v. stepLD8 F_16188 D_16188 s1v. stepLD8 F_1618c D_1618c s2v. stepLD8 F_16190 D_16190 s3v.
      zv F_16194 D_16194 (Z_to_bv 64 s).
      stepret F_16198 D_16198 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_X2 : forall regs m (s : Z) (ret s0v s1v s2v s3v kel : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 9 = kel ->
    exists regs',
      msteps SEGS (mkst regs (0x16278 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = kel
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v kel Hs Hs64 Hret R1 R2 R3 R4 R5 H2 H9. eexists. split.
    - sn F_1617c D_1617c.
      stepLD8 F_16180 D_16180 ret. stepLD8 F_16184 D_16184 s0v. stepLD8 F_16188 D_16188 s1v. stepLD8 F_1618c D_1618c s2v. stepLD8 F_16190 D_16190 s3v.
      zv F_16194 D_16194 (Z_to_bv 64 s).
      stepret F_16198 D_16198 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_C1 : forall regs m (kel : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (kel mod 8 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 (kel + 8)) 8 = true ->
    getr regs 10 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x161b8 : word) m rom)
                  (mkst regs' (0x162c4 : word) (wbytes (wbytes m (Z_to_bv 64 (kel + 8)) (word_to_le_bytes 4 (Z_to_bv 64 2)))
                                                      (Z_to_bv 64 (kel + 12)) (word_to_le_bytes 4 (Z_to_bv 64 2))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 9 = Z_to_bv 64 kel
      /\ regs_agree (fun r => In r [9; 10]%list) regs regs'.
  Proof.
    intros regs m kel Hk Hk64 ALk SOK H10 H18 H19. eexists. split.
    - sn F_160bc D_160bc.
      stepb_ft F_160c0 D_160c0 ltac:(condZ).
      zand F_160c4 D_160c4 andi_7 ALk.
      stepb_ft F_160c8 D_160c8 ltac:(condZ).
      stepST F_160cc D_160cc (Z_to_bv 64 (kel + 8)) (Z_to_bv 64 2) ltac:(sok_in SOK).
      stepST F_160d0 D_160d0 (Z_to_bv 64 (kel + 12)) (Z_to_bv 64 2) ltac:(sok_in SOK).
      sn F_160d4 D_160d4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_C0 : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) ->
    rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x161b8 : word) m rom) (mkst regs' (0x13ad4 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x162c4 /\ getr regs' 9 = Z_to_bv 64 0
      /\ getr regs' 10 = Z_to_bv 64 0x103f4 /\ getr regs' 11 = Z_to_bv 64 0x104b7 /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - sn F_160bc D_160bc.
      stepb_tk F_160c0 D_160c0 ltac:(condZ).
      sn F_1619c D_1619c.
      stepLD F_161a0 D_161a0 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_161a4 D_161a4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_161a8 D_161a8.
      stepb_ft F_161ac D_161ac ltac:(condZ).
      sn F_161b0 D_161b0. sn F_161b4 D_161b4. sn F_161b8 D_161b8. sn F_161bc D_161bc. sn F_161c0 D_161c0. sn F_161c4 D_161c4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_D : forall regs m (s w h : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x162c4 : word) m rom) (mkst regs' (0x162ec : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh Rw Rh H2. eexists. split.
    - stepLD F_161c8 D_161c8 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      stepb_ft F_161cc D_161cc ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_161d0 D_161d0 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      sn F_161d4 D_161d4. sn F_161d8 D_161d8.
      stepb_ft F_161e8 D_161e8 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_161ec D_161ec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L1 : forall regs m (s i j : Z) (pix : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 8 = pix -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x162ec : word) m rom) (mkst regs' (0x146b0 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x16300 /\ getr regs' 10 = pix
      /\ getr regs' 11 = Z_to_bv 64 j /\ getr regs' 12 = Z_to_bv 64 i /\ getr regs' 13 = Z_to_bv 64 (s - 56)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s i j pix Hs Hs64 H2 H8 H18 H19. eexists. split.
    - zv F_161f0 D_161f0 (Z_to_bv 64 (s - 56)).
      sn F_161f4 D_161f4. sn F_161f8 D_161f8. sn F_161fc D_161fc. sn F_16200 D_16200.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L2 : forall regs m (s val : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= val < 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 56)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 val)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x16300 : word) m rom) (mkst regs' (0x16304 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 val
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s val Hs Hs64 Hv Rv H2. eexists. split.
    - stepLD F_16204 D_16204 (word_to_le_bytes 4 (Z_to_bv 64 val)) (Z_to_bv 64 val) ltac:(addr_norm; exact Rv) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L3 : forall regs m (i j : Z) (kel : word),
    getr regs 9 = kel -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x16308 : word) m rom) (mkst regs' (0x16044 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x16318 /\ getr regs' 10 = kel
      /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 j
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m i j kel H9 H18 H19. eexists. split.
    - sn F_1620c D_1620c. sn F_16210 D_16210. sn F_16214 D_16214. sn F_16218 D_16218.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L4a : forall regs m (s w h i j : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (0 <= j)%Z -> (j + 1 < w)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x16318 : word) m rom) (mkst regs' (0x162ec : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 18 = Z_to_bv 64 i /\ getr regs' 19 = Z_to_bv 64 (j + 1)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 19]%list) regs regs'.
  Proof.
    intros regs m s w h i j Hs Hs64 Hw Hj Hj1 Rw H2 H18 H19. eexists. split.
    - stepLD F_1621c D_1621c (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepiv F_16220 D_16220 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_tk F_16224 D_16224 ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L4b : forall regs m (s w h i j : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= j)%Z -> (j + 1 = w)%Z -> (0 <= i)%Z -> (i + 1 < h)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x16318 : word) m rom) (mkst regs' (0x162ec : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 18 = Z_to_bv 64 (i + 1) /\ getr regs' 19 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s w h i j Hs Hs64 Hw Hh Hj Hj1 Hi Hi1 Rw Rh H2 H18 H19. eexists. split.
    - stepLD F_1621c D_1621c (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepiv F_16220 D_16220 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_ft F_16224 D_16224 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_16228 D_16228.
      stepLD F_161dc D_161dc (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      stepiv F_161e0 D_161e0 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_ft F_161e4 D_161e4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_161e8 D_161e8 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_161ec D_161ec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_L4c : forall regs m (s w h i j : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= j)%Z -> (j + 1 = w)%Z -> (0 <= i)%Z -> (i + 1 = h)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (0x16318 : word) m rom) (mkst regs' (0x16278 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s w h i j Hs Hs64 Hw Hh Hj Hj1 Hi Hi1 Rw Rh H2 H18 H19. eexists. split.
    - stepLD F_1621c D_1621c (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small w) by lia.
      stepiv F_16220 D_16220 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_ft F_16224 D_16224 ltac:(condZ).
      sn F_16228 D_16228.
      stepLD F_161dc D_161dc (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small h) by lia.
      stepiv F_161e0 D_161e0 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; apply zbv_addiw_small; lia).
      stepb_tk F_161e4 D_161e4 ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End KernSegs.
