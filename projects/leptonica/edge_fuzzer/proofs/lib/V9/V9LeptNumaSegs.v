(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptNuma LeptNumaW.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9_code_edA.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Ltac peelZ := repeat (rewrite rdn_wbytes_out_Z by (rewrite ?length_Z_to_le_bytes; zlen; lia_fast)).
(* [comment removed for export] *)
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac snez1 F D := sn F D; fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac sltu0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
Ltac slti0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
Ltac stepLD8z F D vv H := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; peelZ; exact H) ltac:(apply bytes_le_to_Z_8).

Section NumaSegs.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NCF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

Definition nccells (M : word -> option byte) (s : Z) (ret s0v s1v : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v).

Lemma nccells_NCF : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  nccells (NCF m s ret regs) s ret (getr regs 8) (getr regs 9).
Proof. intros m s ret regs Hs Hs64. unfold nccells, NCF. repeat split; rdn_chain. Qed.

(* [comment removed for export] *)
Lemma nc_A : forall regs m (s n : Z) (ret : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= n <= 20000)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (0x61688 : word) m rom) (mkst regs' (0xe2480 : word) (NCF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x616c0
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 32 /\ getr regs' 8 = Z_to_bv 64 (numa_n0 n)
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11]%list) regs regs'.
Proof.
  intros regs m s n ret Hs Hs64 Hn SOK H2 H1 H10.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite numa_n0_0. eexists. split.
    + zv F_61630 D_61630 (Z_to_bv 64 (s - 32)).
      stepST F_61634 D_61634 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_61638 D_61638 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6163c D_6163c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_61640 D_61640. sn F_61644 D_61644.
      stepiv F_61648 D_61648 (Z_to_bv 64 18446744073609551615) ltac:(gres; pin; imm_norm; exact numa_k1).
      sn F_6164c D_6164c.
      stepiv F_61650 D_61650 (Z_to_bv 64 18446744073609551616) ltac:(gres; pin; imm_norm; exact numa_k0).
      stepb_ft F_61654 D_61654 ltac:(condZ).
      sn F_61658 D_61658.
      sn F_6165c D_6165c. sn F_61660 D_61660. sn F_61664 D_61664.
      unfold NCF. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - rewrite numa_n0_pos by lia. eexists. split.
    + zv F_61630 D_61630 (Z_to_bv 64 (s - 32)).
      stepST F_61634 D_61634 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_61638 D_61638 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6163c D_6163c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_61640 D_61640. sn F_61644 D_61644.
      stepiv F_61648 D_61648 (Z_to_bv 64 18446744073609551615) ltac:(gres; pin; imm_norm; exact numa_k1).
      sn F_6164c D_6164c. fixv (Z_to_bv 64 (18446744073609551615 + n)) ltac:(pin; rewrite numa_addw by lia; reflexivity).
      stepiv F_61650 D_61650 (Z_to_bv 64 18446744073609551616) ltac:(gres; pin; imm_norm; exact numa_k0).
      stepb_tk F_61654 D_61654 ltac:(condZ).
      sn F_6165c D_6165c. sn F_61660 D_61660. sn F_61664 D_61664.
      unfold NCF. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma nc_B : forall regs m (na nalloc : Z),
  getr regs 10 = Z_to_bv 64 na -> getr regs 8 = Z_to_bv 64 nalloc ->
  exists regs',
    msteps SEGS (mkst regs (0x616c0 : word) m rom) (mkst regs' (0xe2480 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x616d0 /\ getr regs' 10 = Z_to_bv 64 nalloc /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 9 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof.
  intros regs m na nalloc H10 H8. eexists. split.
  - sn F_61668 D_61668. sn F_6166c D_6166c. sn F_61670 D_61670. sn F_61674 D_61674. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Definition NCH (m : word -> option byte) (na nalloc arr : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (na + 24)) (word_to_le_bytes 8 (Z_to_bv 64 arr)))
    (Z_to_bv 64 na) (word_to_le_bytes 4 (Z_to_bv 64 nalloc)))
    (Z_to_bv 64 (na + 4)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (na + 8)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
    (Z_to_bv 64 (na + 12)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (na + 16)) (word_to_le_bytes 4 (Z_to_bv 64 1065353216)).

Lemma nc_C : forall regs m (s na nalloc arr : Z) (ret s0v s1v : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 < 2 ^ 64)%Z -> (na mod 8 = 0)%Z -> ret_ok ret ->
  store_ok SEGS m (Z_to_bv 64 na) 32 = true -> (na + 32 <= s - 32 \/ s <= na)%Z ->
  nccells m s ret s0v s1v ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 9 = Z_to_bv 64 na -> getr regs 8 = Z_to_bv 64 nalloc ->
  exists regs',
    msteps SEGS (mkst regs (0x616d0 : word) m rom) (mkst regs' ret (NCH m na nalloc arr) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s na nalloc arr ret s0v s1v Hs Hs64 Harr Hna Hna64 ALna Hret SOK DJ (C1 & C2 & C3) H2 H10 H9 H8.
  eexists. split.
  - stepb_ft F_61678 D_61678 ltac:(condZ).                                           (* [comment removed for export] *)
    zand F_6167c D_6167c andi_7 ALna. stepb_ft F_61680 D_61680 ltac:(condZ).          (* [comment removed for export] *)
    stepST F_61684 D_61684 (Z_to_bv 64 (na + 24)) (Z_to_bv 64 arr) ltac:(sok_in SOK).
    stepb_ft F_61688 D_61688 ltac:(condZ).
    stepST F_6168c D_6168c (Z_to_bv 64 na) (Z_to_bv 64 nalloc) ltac:(sok_in SOK).
    stepST F_61690 D_61690 (Z_to_bv 64 (na + 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepfence F_61694 D_61694.
    sn F_61698 D_61698.
    stepST F_6169c D_6169c (Z_to_bv 64 (na + 8)) (Z_to_bv 64 1) ltac:(sok_in SOK).
    sn F_616a0 D_616a0.
    stepfence F_616a4 D_616a4.
    stepST F_616a8 D_616a8 (Z_to_bv 64 (na + 12)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepST F_616ac D_616ac (Z_to_bv 64 (na + 16)) (Z_to_bv 64 1065353216) ltac:(sok_in SOK).
    sn F_616b0 D_616b0. sn F_61720 D_61720.
    stepLD8 F_61724 D_61724 ret. stepLD8 F_61728 D_61728 s0v. stepLD8 F_6172c D_6172c s1v.
    zv F_61730 D_61730 (Z_to_bv 64 s).
    stepret F_61734 D_61734 ret ltac:(bveq).
    unfold NCH. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NDF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

Definition ndcells (M : word -> option byte) (s : Z) (ret s0v s1v : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v).

Lemma ndcells_NDF : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ndcells (NDF m s ret regs) s ret (getr regs 8) (getr regs 9).
Proof. intros m s ret regs Hs Hs64. unfold ndcells, NDF. repeat split; rdn_chain. Qed.

(* [comment removed for export] *)
Lemma nd_A : forall regs m (s pp na arr : Z) (ret : word),
  (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 32)%Z -> (na mod 16 = 0)%Z -> (1 <= arr < 2 ^ 64)%Z ->
  (pp mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 (na + 8)) 4 = true ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 na) -> rdn SEGS m (Z_to_bv 64 (na + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (na + 24)) 8 = Some (Z_to_le_bytes 8 arr) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
  exists regs',
    msteps SEGS (mkst regs (0x61794 : word) m rom)
                (mkst regs' (0xe25b8 : word) (wbytes (NDF m s ret regs) (Z_to_bv 64 (na + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x617e4 /\ getr regs' 10 = Z_to_bv 64 arr
    /\ getr regs' 8 = Z_to_bv 64 na /\ getr regs' 9 = Z_to_bv 64 pp
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s pp na arr ret Hs Hpp Hpp64 Hna Hna2 Hal Harr ALpp SOK SOKr Rpp Rrc Rarr H2 H1 H10.
  assert (ALna : (na mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r na); apply mod16_plus_mod8; [exact Hal | reflexivity]).
  eexists. split.
  - zv F_6173c D_6173c (Z_to_bv 64 (s - 32)).
    stepST F_61740 D_61740 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_61744 D_61744 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_61748 D_61748 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepb_ft F_6174c D_6174c ltac:(condZ).
    zand F_61750 D_61750 andi_7 ALpp. stepb_ft F_61754 D_61754 ltac:(condZ).          (* [comment removed for export] *)
    stepLD F_61758 D_61758 (Z_to_le_bytes 8 na) (Z_to_bv 64 na) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply lez8; lia).
    stepb_ft F_6175c D_6175c ltac:(condZ).
    zand F_61760 D_61760 andi_7 ALna. stepb_ft F_61764 D_61764 ltac:(condZ).          (* [comment removed for export] *)
    zv F_61768 D_61768 (Z_to_bv 64 (na + 8)).
    sn F_6176c D_6176c.
    chain_step;
      [ reflexivity
      | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_61770 eq_refl D_61770);
        [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
        | gres; repeat rdn_peel1; exact Rrc
        | apply lez4; lia
        | gres; sok_in SOKr ]
      | step_simpl ].
    gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite (v_lw_small 1) by lia.
    sn F_61774 D_61774.
    stepb_ft F_61778 D_61778 ltac:(condZ).
    sn F_6177c D_6177c.
    stepLD F_61780 D_61780 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; repeat rdn_peel1; exact Rarr) ltac:(apply lez8; lia).
    stepb_ft F_61784 D_61784 ltac:(condZ).
    sn F_61788 D_61788.
    unfold NDF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma nd_B : forall regs m (na : Z), getr regs 8 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x617e4 : word) m rom) (mkst regs' (0xe25b8 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x617ec /\ getr regs' 10 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m na H8. eexists. split.
  - sn F_6178c D_6178c. sn F_61790 D_61790. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma nd_C : forall regs m (s pp : Z) (ret s0v s1v : word),
  (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> ret_ok ret ->
  store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> ndcells m s ret s0v s1v ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 9 = Z_to_bv 64 pp ->
  exists regs',
    msteps SEGS (mkst regs (0x617ec : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
Proof.
  intros regs m s pp ret s0v s1v Hs Hpp Hpp64 Hret SOK (C1 & C2 & C3) H2 H9.
  eexists. split.
  - sn F_61794 D_61794.
    stepST F_61798 D_61798 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
    sn F_6179c D_6179c.
    stepLD8 F_617d8 D_617d8 ret. stepLD8 F_617dc D_617dc s0v. stepLD8 F_617e0 D_617e0 s1v.
    zv F_617e4 D_617e4 (Z_to_bv 64 s).
    stepret F_617e8 D_617e8 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NAF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (reg_get (@fp_regs fx) 8)).

Definition nacells (M : word -> option byte) (s : Z) (ret s0v s1v : word) (fs0b : list byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some fs0b.

Lemma nacells_NAF : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  nacells (NAF m s ret regs) s ret (getr regs 8) (getr regs 9) (word_to_le_bytes 8 (reg_get (@fp_regs fx) 8)).
Proof. intros m s ret regs Hs Hs64. unfold nacells, NAF. repeat split; rdn_chain. Qed.

(* [comment removed for export] *)
Lemma na_P_lt : forall regs m (s na nalloc n : Z) (ret : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 32)%Z -> (0 <= n < nalloc)%Z -> (nalloc < 2 ^ 31)%Z -> (na mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  rdn SEGS m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc) -> rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x61848 : word) m rom) (mkst regs' (0x618b8 : word) (NAF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 9 = Z_to_bv 64 n
    /\ regs_agree (fun r => In r [2; 9; 11]%list) regs regs'.
Proof.
  intros regs m s na nalloc n ret Hs Hs64 Hna Hna2 Hn Hnal ALna SOK Rnal Rn H2 H1 H10.
  eexists. split.
  - zv F_617f0 D_617f0 (Z_to_bv 64 (s - 32)).
    stepST F_617f4 D_617f4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_617f8 D_617f8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_617fc D_617fc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    chain_step; [ reflexivity
                | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 32)); [exact F_61800 | reflexivity | exact D_61800 | gres; imm_norm; addr_tac | sok_in SOK]
                | step_simpl ].
    stepb_ft F_61804 D_61804 ltac:(condZ).
    zand F_61808 D_61808 andi_7 ALna. stepb_ft F_6180c D_6180c ltac:(condZ).          (* [comment removed for export] *)
    stepLD F_61810 D_61810 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    rewrite (v_lw_small nalloc) by lia.
    stepLD F_61814 D_61814 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    stepb_tk F_61818 D_61818 ltac:(condZ).
    unfold NAF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma na_P_ge : forall regs m (s na nalloc n : Z) (ret : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 32)%Z -> (0 <= nalloc <= n)%Z -> (n < 2 ^ 31)%Z -> (na mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  rdn SEGS m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc) -> rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x61848 : word) m rom) (mkst regs' (0x61878 : word) (NAF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 9 = Z_to_bv 64 n /\ getr regs' 8 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [2; 8; 9; 11]%list) regs regs'.
Proof.
  intros regs m s na nalloc n ret Hs Hs64 Hna Hna2 Hn Hnal ALna SOK Rnal Rn H2 H1 H10.
  eexists. split.
  - zv F_617f0 D_617f0 (Z_to_bv 64 (s - 32)).
    stepST F_617f4 D_617f4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_617f8 D_617f8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_617fc D_617fc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    chain_step; [ reflexivity
                | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 32)); [exact F_61800 | reflexivity | exact D_61800 | gres; imm_norm; addr_tac | sok_in SOK]
                | step_simpl ].
    stepb_ft F_61804 D_61804 ltac:(condZ).
    zand F_61808 D_61808 andi_7 ALna. stepb_ft F_6180c D_6180c ltac:(condZ).
    stepLD F_61810 D_61810 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    rewrite (v_lw_small nalloc) by lia.
    stepLD F_61814 D_61814 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    stepb_ft F_61818 D_61818 ltac:(condZ).
    sn F_6181c D_6181c.
    unfold NAF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma na_F1 : forall regs m,
  exists fr, msteps SEGS (mkst regs (0x61878 : word) m rom) (@mkst (mkFP fr (@fp_csr fx)) regs (0x6187c : word) m rom).
Proof.
  intros regs m.
  destruct (fp_step_fsgnj fx SEGS regs (0x61878 : word) m rom W_61820 F_SGNJ FMT_S 8 10 10 F_61820 eq_refl D_61820) as (fr & ST).
  exists fr. eapply mst_step; [reflexivity | exact ST |]. step_simpl. apply mst_refl.
Qed.
Lemma na_F2 : forall regs m,
  exists fr, msteps SEGS (mkst regs (0x61880 : word) m rom) (@mkst (mkFP fr (@fp_csr fx)) regs (0x61884 : word) m rom).
Proof.
  intros regs m.
  destruct (fp_step_fsgnj fx SEGS regs (0x61880 : word) m rom W_61828 F_SGNJ FMT_S 10 8 8 F_61828 eq_refl D_61828) as (fr & ST).
  exists fr. eapply mst_step; [reflexivity | exact ST |]. step_simpl. apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma na_G1 : forall regs m (na : Z), getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x6187c : word) m rom) (mkst regs' (0x619bc : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x61880 /\ getr regs' 10 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1]%list) regs regs'.
Proof.
  intros regs m na H10. eexists. split.
  - sn F_61824 D_61824. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma na_G2 : forall regs m (na : Z),
  getr regs 10 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x61884 : word) m rom) (mkst regs' (0x618b8 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof.
  intros regs m na H10 H8. eexists. split.
  - sn F_6182c D_6182c. sn F_61830 D_61830.
    stepb_tk F_61834 D_61834 ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma na_T : forall regs m (s na arr n : Z) (ret s0v s1v : word) (fs0b : list byte),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 32)%Z -> (1 <= arr)%Z -> (arr + 4 * n + 4 <= s - 32)%Z -> (0 <= n < 2 ^ 31 - 1)%Z ->
  (na + 32 <= arr \/ arr + 4 * n + 4 <= na)%Z -> (arr mod 4 = 0)%Z -> ret_ok ret -> length fs0b = 8%nat ->
  rdn SEGS m (Z_to_bv 64 (na + 24)) 8 = Some (Z_to_le_bytes 8 arr) -> rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
  store_ok SEGS m (Z_to_bv 64 (arr + 4 * n)) 4 = true -> store_ok SEGS m (Z_to_bv 64 (na + 4)) 4 = true ->
  nacells m s ret s0v s1v fs0b ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 na -> getr regs 9 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (0x618b8 : word) m rom)
                (@mkst (mkFP (bvmap_set 8 (bv_extract 0 64 (le_bytes_to_word fs0b)) (@fp_regs fx)) (@fp_csr fx)) regs' ret
                       (wbytes (wbytes m (Z_to_bv 64 (arr + 4 * n)) (Z_to_le_bytes 4 (u (low32 (reg_get (@fp_regs fx) 10)))))
                               (Z_to_bv 64 (na + 4)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros regs m s na arr n ret s0v s1v fs0b Hs Hs64 Hna Hna2 Harr Harr2 Hn DJ ALarr Hret Hlen Rarr Rn SOKc SOKn (C1 & C2 & C3 & C4) H2 H10 H9.
  assert (ALc : ((arr + 4 * n) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALarr).
  eexists. split.
  - stepLD F_61860 D_61860 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply lez8; lia).
    stepiv F_61864 D_61864 (Z_to_bv 64 (4 * n)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    zv F_61868 D_61868 (Z_to_bv 64 (arr + 4 * n)).
    snez1 F_6186c D_6186c.                                                          (* [comment removed for export] *)
    seqz0 F_61870 D_61870.                                                          (* [comment removed for export] *)
    stepb_ft F_61874 D_61874 ltac:(condR).                                          (* [comment removed for export] *)
    sltu0 F_61878 D_61878.                                                          (* [comment removed for export] *)
    slti0 F_6187c D_6187c.                                                          (* [comment removed for export] *)
    sn F_61880 D_61880. sn F_61884 D_61884.                                         (* [comment removed for export] *)
    stepb_ft F_61888 D_61888 ltac:(condR).                                          (* [comment removed for export] *)
    stepb_ft F_6188c D_6188c ltac:(condZ).                                          (* [comment removed for export] *)
    zand F_61890 D_61890 andi_3 ALc. stepb_ft F_61894 D_61894 ltac:(condZ).          (* [comment removed for export] *)
    stepLD F_61898 D_61898 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    sn F_6189c D_6189c. fixv (Z_to_bv 64 (n + 1)) ltac:(pin; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
    chain_step; [ reflexivity
                | eapply fp_step_fsw with (a := Z_to_bv 64 (arr + 4 * n)); [exact F_618a0 | reflexivity | exact D_618a0 | gres; imm_norm; addr_tac | exact SOKc]
                | step_simpl ].
    stepb_ft F_618a4 D_618a4 ltac:(condZ).                                          (* [comment removed for export] *)
    sn F_618a8 D_618a8.
    stepST F_618ac D_618ac (Z_to_bv 64 (na + 4)) (Z_to_bv 64 (n + 1)) ltac:(store_ok_peel; exact SOKn).
    sn F_618b0 D_618b0. sn F_618f8 D_618f8.
    stepLD8z F_618fc D_618fc ret C1. stepLD8z F_61900 D_61900 s0v C2. stepLD8z F_61904 D_61904 s1v C3.
    chain_step; [ reflexivity
                | eapply fp_step_fld with (a := Z_to_bv 64 (s - 32)) (bs := fs0b);
                  [exact F_61908 | reflexivity | exact D_61908 | gres; imm_norm; addr_tac | peelZ; exact C4]
                | step_simpl ].
    zv F_6190c D_6190c (Z_to_bv 64 s).
    stepret F_61910 D_61910 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NEF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)).

Definition necells (M : word -> option byte) (s : Z) (ret s0v : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v).

Lemma necells_NEF : forall m s ret regs, (16 <= s)%Z -> (s < 2 ^ 64)%Z -> necells (NEF m s ret regs) s ret (getr regs 8).
Proof. intros m s ret regs Hs Hs64. unfold necells, NEF. repeat split; rdn_chain. Qed.

(* [comment removed for export] *)
Lemma ne_A : forall regs m (s na nalloc : Z) (ret : word),
  (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 16)%Z -> (0 <= nalloc <= 50000000)%Z -> (na mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
  rdn SEGS m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x619bc : word) m rom) (mkst regs' (0x5e334 : word) (NEF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x61a54
    /\ getr regs' 10 = Z_to_bv 64 (na + 24) /\ getr regs' 11 = Z_to_bv 64 (4 * nalloc) /\ getr regs' 12 = Z_to_bv 64 (8 * nalloc)
    /\ getr regs' 8 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12; 13]%list) regs regs'.
Proof.
  intros regs m s na nalloc ret Hs Hs64 Hna Hna2 Hnal ALna SOK Rnal H2 H1 H10.
  eexists. split.
  - zv F_61964 D_61964 (Z_to_bv 64 (s - 16)).
    stepST F_61968 D_61968 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_6196c D_6196c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    zand F_61970 D_61970 andi_7 ALna. stepb_ft F_61974 D_61974 ltac:(condZ).          (* [comment removed for export] *)
    stepLD F_61978 D_61978 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    sn F_6197c D_6197c. sn F_61980 D_61980.
    stepb_tk F_61984 D_61984 ltac:(condZ).
    sn F_619b0 D_619b0. sn F_619b4 D_619b4.
    stepb_tk F_619b8 D_619b8 ltac:(condZ).
    stepiv F_619e4 D_619e4 (Z_to_bv 64 (4 * nalloc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    stepiv F_619e8 D_619e8 (Z_to_bv 64 (8 * nalloc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    zv F_619ec D_619ec (Z_to_bv 64 (na + 24)).
    sn F_619f0 D_619f0. sn F_619f4 D_619f4. sn F_619f8 D_619f8.
    unfold NEF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ne_B : forall regs m (s na nalloc arr' : Z) (ret s0v : word),
  (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 16)%Z -> (0 <= nalloc <= 50000000)%Z -> (1 <= arr' < 2 ^ 64)%Z -> ret_ok ret ->
  store_ok SEGS m (Z_to_bv 64 na) 32 = true ->
  rdn SEGS m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc) -> necells m s ret s0v ->
  getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 arr' -> getr regs 8 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x61a54 : word) m rom)
                (mkst regs' ret (wbytes (wbytes m (Z_to_bv 64 (na + 24)) (word_to_le_bytes 8 (Z_to_bv 64 arr')))
                                        (Z_to_bv 64 na) (word_to_le_bytes 4 (Z_to_bv 64 (2 * nalloc)))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s na nalloc arr' ret s0v Hs Hs64 Hna Hna2 Hnal Harr Hret SOK Rnal (C1 & C2) H2 H10 H8.
  eexists. split.
  - stepST F_619fc D_619fc (Z_to_bv 64 (na + 24)) (Z_to_bv 64 arr') ltac:(sok_in SOK).
    stepb_ft F_61a00 D_61a00 ltac:(condZ).
    sn F_61a04 D_61a04.
    stepLD F_61a08 D_61a08 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    rewrite (v_lw_small nalloc) by lia.
    sn F_61a0c D_61a0c.
    sn F_61a10 D_61a10. fixv (Z_to_bv 64 (nalloc + 1073741824)) ltac:(pin; rewrite zbv_addw_small by lia; reflexivity).   (* [comment removed for export] *)
    stepb_ft F_61a14 D_61a14 ltac:(condZ).                                          (* [comment removed for export] *)
    sn F_61a18 D_61a18.
    stepiv F_61a1c D_61a1c (Z_to_bv 64 (2 * nalloc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    stepST F_61a20 D_61a20 (Z_to_bv 64 na) (Z_to_bv 64 (2 * nalloc)) ltac:(sok_in SOK).
    sn F_61a24 D_61a24.
    stepLD8 F_61a64 D_61a64 ret. stepLD8 F_61a68 D_61a68 s0v.
    zv F_61a6c D_61a6c (Z_to_bv 64 s).
    stepret F_61a70 D_61a70 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RNF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

Definition rncells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

Lemma rncells_RNF : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rncells (RNF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19).
Proof. intros m s ret regs Hs Hs64. unfold rncells, RNF. repeat split; rdn_chain. Qed.

(* [comment removed for export] *)
Lemma rn_A : forall regs m (s pp ind old new : Z) (ret : word),
  (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= s - 48)%Z -> (0 <= ind < 2 ^ 64)%Z -> (1 <= new < 2 ^ 64)%Z -> (pp mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 ind) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp -> getr regs 11 = Z_to_bv 64 old -> getr regs 12 = Z_to_bv 64 new ->
  exists regs',
    msteps SEGS (mkst regs (0x5e334 : word) m rom) (mkst regs' (0xe2480 : word) (RNF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5e378 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 new
    /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 ind /\ getr regs' 18 = Z_to_bv 64 old /\ getr regs' 19 = Z_to_bv 64 new
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
Proof.
  intros regs m s pp ind old new ret Hs Hs64 Hpp Hpp2 Hind Hnew ALpp SOK Rpp H2 H1 H10 H11 H12.
  eexists. split.
  - zv F_5e2dc D_5e2dc (Z_to_bv 64 (s - 48)).
    stepST F_5e2e0 D_5e2e0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_5e2e4 D_5e2e4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_5e2e8 D_5e2e8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_5e2ec D_5e2ec (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_5e2f0 D_5e2f0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_5e2f4 D_5e2f4 ltac:(condZ).
    sn F_5e2f8 D_5e2f8.
    zand F_5e2fc D_5e2fc andi_7 ALpp. stepb_ft F_5e300 D_5e300 ltac:(condZ).          (* [comment removed for export] *)
    stepLD F_5e304 D_5e304 (Z_to_le_bytes 8 ind) (Z_to_bv 64 ind) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply lez8; lia).
    stepb_ft F_5e308 D_5e308 ltac:(condZ).
    sn F_5e30c D_5e30c. sn F_5e310 D_5e310. sn F_5e314 D_5e314. sn F_5e318 D_5e318. sn F_5e31c D_5e31c.
    unfold RNF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rn_B : forall regs m (ind old new nb : Z),
  (1 <= ind < 2 ^ 64)%Z -> (1 <= nb < 2 ^ 64)%Z -> (0 <= old < new)%Z -> (new < 2 ^ 64)%Z ->
  getr regs 10 = Z_to_bv 64 nb -> getr regs 9 = Z_to_bv 64 ind -> getr regs 18 = Z_to_bv 64 old -> getr regs 19 = Z_to_bv 64 new ->
  exists regs',
    msteps SEGS (mkst regs (0x5e378 : word) m rom) (mkst regs' (0xf0a88 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x5e398 /\ getr regs' 10 = Z_to_bv 64 nb /\ getr regs' 11 = Z_to_bv 64 ind /\ getr regs' 12 = Z_to_bv 64 old
    /\ getr regs' 19 = Z_to_bv 64 nb
    /\ regs_agree (fun r => In r [1; 11; 12; 19]%list) regs regs'.
Proof.
  intros regs m ind old new nb Hind Hnb Hold Hnew H10 H9 H18 H19.
  eexists. split.
  - stepb_ft F_5e320 D_5e320 ltac:(condZ).
    stepb_ft F_5e324 D_5e324 ltac:(condZ).
    stepb_tk F_5e328 D_5e328 ltac:(condZ).
    sn F_5e330 D_5e330. sn F_5e334 D_5e334. sn F_5e338 D_5e338. sn F_5e33c D_5e33c.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rn_C : forall regs m (ind : Z), getr regs 9 = Z_to_bv 64 ind ->
  exists regs',
    msteps SEGS (mkst regs (0x5e398 : word) m rom) (mkst regs' (0xe25b8 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x5e3a0 /\ getr regs' 10 = Z_to_bv 64 ind
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m ind H9. eexists. split.
  - sn F_5e340 D_5e340. sn F_5e344 D_5e344. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rn_D : forall regs m (s pp nb : Z) (ret s0v s1v s2v s3v : word),
  (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= s - 48)%Z -> ret_ok ret ->
  store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> rncells m s ret s0v s1v s2v s3v ->
  getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pp -> getr regs 19 = Z_to_bv 64 nb ->
  exists regs',
    msteps SEGS (mkst regs (0x5e3a0 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 nb
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
Proof.
  intros regs m s pp nb ret s0v s1v s2v s3v Hs Hs64 Hpp Hpp2 Hret SOK (C1 & C2 & C3 & C4 & C5) H2 H8 H19.
  eexists. split.
  - sn F_5e348 D_5e348. sn F_5e34c D_5e34c.
    stepST F_5e3a4 D_5e3a4 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
    sn F_5e3a8 D_5e3a8.
    stepLD8 F_5e404 D_5e404 ret. stepLD8 F_5e408 D_5e408 s0v. stepLD8 F_5e40c D_5e40c s1v. stepLD8 F_5e410 D_5e410 s2v. stepLD8 F_5e414 D_5e414 s3v.
    zv F_5e418 D_5e418 (Z_to_bv 64 s).
    stepret F_5e41c D_5e41c ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

End NumaSegs.
