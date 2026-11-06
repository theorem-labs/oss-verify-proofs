(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptNuma LeptNumaW.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9_code_edA.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Ltac peelZ := repeat (rewrite rdn_wbytes_out_Z by (rewrite ?length_Z_to_le_bytes; zlen; lia_fast)).
Ltac stepLD8z F D vv H := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; peelZ; exact H) ltac:(apply bytes_le_to_Z_8).

Section NumaSegs.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NCF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)).

Definition nccells (M : word -> option byte) (s : Z) (ret s0v s1v s2v : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v).

Lemma nccells_NCF : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  nccells (NCF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18).
Proof. intros m s ret regs Hs Hs64. unfold nccells, NCF. repeat split; rdn_chain. Qed.

(* [comment removed for export] *)
Lemma nc_A : forall regs m (s n : Z) (ret : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= n <= 20000)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (0x609ec : word) m rom) (mkst regs' (0xd78cc : word) (NCF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x60a2c
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 32 /\ getr regs' 8 = Z_to_bv 64 (numa_n0 n) /\ getr regs' 18 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 18]%list) regs regs'.
Proof.
  intros regs m s n ret Hs Hs64 Hn SOK H2 H1 H10.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite numa_n0_0. eexists. split.
    + zv F_60994 D_60994 (Z_to_bv 64 (s - 32)).
      stepST F_60998 D_60998 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6099c D_6099c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_609a0 D_609a0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_609a4 D_609a4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      sn F_609a8 D_609a8. sn F_609ac D_609ac.
      stepiv F_609b0 D_609b0 (Z_to_bv 64 18446744073609551615) ltac:(gres; pin; imm_norm; exact numa_k1).
      sn F_609b4 D_609b4.
      stepiv F_609b8 D_609b8 (Z_to_bv 64 18446744073609551616) ltac:(gres; pin; imm_norm; exact numa_k0).
      stepb_ft F_609bc D_609bc ltac:(condZ).
      sn F_609c0 D_609c0.
      sn F_609c4 D_609c4. sn F_609c8 D_609c8. sn F_609cc D_609cc. sn F_609d0 D_609d0.
      unfold NCF. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  - rewrite numa_n0_pos by lia. eexists. split.
    + zv F_60994 D_60994 (Z_to_bv 64 (s - 32)).
      stepST F_60998 D_60998 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6099c D_6099c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_609a0 D_609a0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_609a4 D_609a4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      sn F_609a8 D_609a8. sn F_609ac D_609ac.
      stepiv F_609b0 D_609b0 (Z_to_bv 64 18446744073609551615) ltac:(gres; pin; imm_norm; exact numa_k1).
      sn F_609b4 D_609b4. fixv (Z_to_bv 64 (18446744073609551615 + n)) ltac:(pin; rewrite numa_addw by lia; reflexivity).
      stepiv F_609b8 D_609b8 (Z_to_bv 64 18446744073609551616) ltac:(gres; pin; imm_norm; exact numa_k0).
      stepb_tk F_609bc D_609bc ltac:(condZ).
      sn F_609c4 D_609c4. sn F_609c8 D_609c8. sn F_609cc D_609cc. sn F_609d0 D_609d0.
      unfold NCF. apply mst_refl.
    + repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma nc_B : forall regs m (na nalloc : Z),
  getr regs 10 = Z_to_bv 64 na -> getr regs 8 = Z_to_bv 64 nalloc ->
  exists regs',
    msteps SEGS (mkst regs (0x60a2c : word) m rom) (mkst regs' (0xd78cc : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x60a3c /\ getr regs' 10 = Z_to_bv 64 nalloc /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 9 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof.
  intros regs m na nalloc H10 H8. eexists. split.
  - sn F_609d4 D_609d4. sn F_609d8 D_609d8. sn F_609dc D_609dc. sn F_609e0 D_609e0. apply mst_refl.
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

Lemma nc_C : forall regs m (s na nalloc arr : Z) (ret s0v s1v s2v : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 < 2 ^ 64)%Z -> ret_ok ret ->
  store_ok SEGS m (Z_to_bv 64 na) 32 = true -> (na + 32 <= s - 32 \/ s <= na)%Z ->
  nccells m s ret s0v s1v s2v ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 9 = Z_to_bv 64 na -> getr regs 8 = Z_to_bv 64 nalloc ->
  getr regs 18 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs (0x60a3c : word) m rom) (mkst regs' ret (NCH m na nalloc arr) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs'.
Proof.
  intros regs m s na nalloc arr ret s0v s1v s2v Hs Hs64 Harr Hna Hna64 Hret SOK DJ (C1 & C2 & C3 & C4) H2 H10 H9 H8 H18.
  eexists. split.
  - stepST F_609e4 D_609e4 (Z_to_bv 64 (na + 24)) (Z_to_bv 64 arr) ltac:(sok_in SOK).
    stepb_ft F_609e8 D_609e8 ltac:(condZ).
    stepST F_609ec D_609ec (Z_to_bv 64 na) (Z_to_bv 64 nalloc) ltac:(sok_in SOK).
    stepST F_609f0 D_609f0 (Z_to_bv 64 (na + 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepfence F_609f4 D_609f4.
    stepST F_609f8 D_609f8 (Z_to_bv 64 (na + 8)) (Z_to_bv 64 1) ltac:(sok_in SOK).
    stepfence F_609fc D_609fc.
    sn F_60a00 D_60a00.
    stepST F_60a04 D_60a04 (Z_to_bv 64 (na + 12)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepST F_60a08 D_60a08 (Z_to_bv 64 (na + 16)) (Z_to_bv 64 1065353216) ltac:(sok_in SOK).
    sn F_60a0c D_60a0c. sn F_60a7c D_60a7c.
    stepLD8 F_60a80 D_60a80 ret. stepLD8 F_60a84 D_60a84 s0v. stepLD8 F_60a88 D_60a88 s1v. stepLD8 F_60a8c D_60a8c s2v.
    zv F_60a90 D_60a90 (Z_to_bv 64 s).
    stepret F_60a94 D_60a94 ret ltac:(bveq).
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
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 (na + 8)) 4 = true ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 na) -> rdn SEGS m (Z_to_bv 64 (na + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (na + 24)) 8 = Some (Z_to_le_bytes 8 arr) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
  exists regs',
    msteps SEGS (mkst regs (0x60af0 : word) m rom)
                (mkst regs' (0xd7a04 : word) (wbytes (NDF m s ret regs) (Z_to_bv 64 (na + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x60b30 /\ getr regs' 10 = Z_to_bv 64 arr
    /\ getr regs' 8 = Z_to_bv 64 na /\ getr regs' 9 = Z_to_bv 64 pp
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s pp na arr ret Hs Hpp Hpp64 Hna Hna2 Hal Harr SOK SOKr Rpp Rrc Rarr H2 H1 H10.
  eexists. split.
  - zv F_60a98 D_60a98 (Z_to_bv 64 (s - 32)).
    stepST F_60a9c D_60a9c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_60aa0 D_60aa0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_60aa4 D_60aa4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepb_ft F_60aa8 D_60aa8 ltac:(condZ).
    stepLD F_60aac D_60aac (Z_to_le_bytes 8 na) (Z_to_bv 64 na) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply lez8; lia).
    stepb_ft F_60ab0 D_60ab0 ltac:(condZ).
    zv F_60ab4 D_60ab4 (Z_to_bv 64 (na + 8)).
    sn F_60ab8 D_60ab8.
    chain_step;
      [ reflexivity
      | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_60abc eq_refl D_60abc);
        [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
        | gres; repeat rdn_peel1; exact Rrc
        | apply lez4; lia
        | gres; sok_in SOKr ]
      | step_simpl ].
    gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite (v_lw_small 1) by lia.
    sn F_60ac0 D_60ac0.
    stepb_ft F_60ac4 D_60ac4 ltac:(condZ).
    sn F_60ac8 D_60ac8.
    stepLD F_60acc D_60acc (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; repeat rdn_peel1; exact Rarr) ltac:(apply lez8; lia).
    stepb_ft F_60ad0 D_60ad0 ltac:(condZ).
    sn F_60ad4 D_60ad4.
    unfold NDF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma nd_B : forall regs m (na : Z), getr regs 8 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x60b30 : word) m rom) (mkst regs' (0xd7a04 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x60b38 /\ getr regs' 10 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m na H8. eexists. split.
  - sn F_60ad8 D_60ad8. sn F_60adc D_60adc. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma nd_C : forall regs m (s pp : Z) (ret s0v s1v : word),
  (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> ret_ok ret ->
  store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> ndcells m s ret s0v s1v ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 9 = Z_to_bv 64 pp ->
  exists regs',
    msteps SEGS (mkst regs (0x60b38 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
Proof.
  intros regs m s pp ret s0v s1v Hs Hpp Hpp64 Hret SOK (C1 & C2 & C3) H2 H9.
  eexists. split.
  - sn F_60ae0 D_60ae0.
    stepST F_60ae4 D_60ae4 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
    sn F_60ae8 D_60ae8.
    stepLD8 F_60b24 D_60b24 ret. stepLD8 F_60b28 D_60b28 s0v. stepLD8 F_60b2c D_60b2c s1v.
    zv F_60b30 D_60b30 (Z_to_bv 64 s).
    stepret F_60b34 D_60b34 ret ltac:(bveq).
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
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 32)%Z -> (0 <= n < nalloc)%Z -> (nalloc < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  rdn SEGS m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc) -> rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x60b90 : word) m rom) (mkst regs' (0x60c44 : word) (NAF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 8 = Z_to_bv 64 n /\ getr regs' 12 = Z_to_bv 64 n
    /\ regs_agree (fun r => In r [2; 8; 11; 12]%list) regs regs'.
Proof.
  intros regs m s na nalloc n ret Hs Hs64 Hna Hna2 Hn Hnal SOK Rnal Rn H2 H1 H10.
  eexists. split.
  - zv F_60b38 D_60b38 (Z_to_bv 64 (s - 32)).
    stepST F_60b3c D_60b3c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_60b40 D_60b40 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_60b44 D_60b44 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    chain_step; [ reflexivity
                | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 32)); [exact F_60b48 | reflexivity | exact D_60b48 | gres; imm_norm; addr_tac | sok_in SOK]
                | step_simpl ].
    stepb_ft F_60b4c D_60b4c ltac:(condZ).
    stepLD F_60b50 D_60b50 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    rewrite (v_lw_small nalloc) by lia.
    stepLD F_60b54 D_60b54 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    sn F_60b58 D_60b58.
    stepb_tk F_60b5c D_60b5c ltac:(condZ).
    unfold NAF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma na_P_ge : forall regs m (s na nalloc n : Z) (ret : word),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 32)%Z -> (0 <= nalloc <= n)%Z -> (n < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  rdn SEGS m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc) -> rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x60b90 : word) m rom) (mkst regs' (0x60bb8 : word) (NAF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 8 = Z_to_bv 64 n
    /\ regs_agree (fun r => In r [2; 8; 11; 12]%list) regs regs'.
Proof.
  intros regs m s na nalloc n ret Hs Hs64 Hna Hna2 Hn Hnal SOK Rnal Rn H2 H1 H10.
  eexists. split.
  - zv F_60b38 D_60b38 (Z_to_bv 64 (s - 32)).
    stepST F_60b3c D_60b3c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_60b40 D_60b40 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_60b44 D_60b44 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    chain_step; [ reflexivity
                | eapply fp_step_fsd with (a := Z_to_bv 64 (s - 32)); [exact F_60b48 | reflexivity | exact D_60b48 | gres; imm_norm; addr_tac | sok_in SOK]
                | step_simpl ].
    stepb_ft F_60b4c D_60b4c ltac:(condZ).
    stepLD F_60b50 D_60b50 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    rewrite (v_lw_small nalloc) by lia.
    stepLD F_60b54 D_60b54 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    sn F_60b58 D_60b58.
    stepb_ft F_60b5c D_60b5c ltac:(condZ).
    unfold NAF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma na_F1 : forall regs m,
  exists fr, msteps SEGS (mkst regs (0x60bb8 : word) m rom) (@mkst (mkFP fr (@fp_csr fx)) regs (0x60bbc : word) m rom).
Proof.
  intros regs m.
  destruct (fp_step_fsgnj fx SEGS regs (0x60bb8 : word) m rom W_60b60 F_SGNJ FMT_S 8 10 10 F_60b60 eq_refl D_60b60) as (fr & ST).
  exists fr. eapply mst_step; [reflexivity | exact ST |]. step_simpl. apply mst_refl.
Qed.
Lemma na_F2 : forall regs m,
  exists fr, msteps SEGS (mkst regs (0x60c40 : word) m rom) (@mkst (mkFP fr (@fp_csr fx)) regs (0x60c44 : word) m rom).
Proof.
  intros regs m.
  destruct (fp_step_fsgnj fx SEGS regs (0x60c40 : word) m rom W_60be8 F_SGNJ FMT_S 10 8 8 F_60be8 eq_refl D_60be8) as (fr & ST).
  exists fr. eapply mst_step; [reflexivity | exact ST |]. step_simpl. apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma na_G1 : forall regs m (na : Z), getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x60bbc : word) m rom) (mkst regs' (0x60cbc : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x60bc4 /\ getr regs' 9 = Z_to_bv 64 na /\ getr regs' 10 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1; 9]%list) regs regs'.
Proof.
  intros regs m na H10. eexists. split.
  - sn F_60b64 D_60b64. sn F_60b68 D_60b68. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma na_G2 : forall regs m (na n : Z),
  (1 <= na)%Z -> (na + 32 < 2 ^ 64)%Z -> (0 <= n < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x60bc4 : word) m rom) (mkst regs' (0x60c40 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 12 = Z_to_bv 64 n
    /\ regs_agree (fun r => In r [10; 12]%list) regs regs'.
Proof.
  intros regs m na n Hna Hna64 Hn Rn H10 H9. eexists. split.
  - stepb_tk F_60b6c D_60b6c ltac:(condZ).
    sn F_60be0 D_60be0.
    stepLD F_60be4 D_60be4 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
    rewrite (v_lw_small n) by lia.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma na_T : forall regs m (s na arr n : Z) (ret s0v s1v : word) (fs0b : list byte),
  (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 32)%Z -> (1 <= arr)%Z -> (arr + 4 * n + 4 <= s - 32)%Z -> (0 <= n < 2 ^ 31 - 1)%Z ->
  (na + 32 <= arr \/ arr + 4 * n + 4 <= na)%Z -> ret_ok ret -> length fs0b = 8%nat ->
  rdn SEGS m (Z_to_bv 64 (na + 24)) 8 = Some (Z_to_le_bytes 8 arr) ->
  store_ok SEGS m (Z_to_bv 64 (arr + 4 * n)) 4 = true -> store_ok SEGS m (Z_to_bv 64 (na + 4)) 4 = true ->
  nacells m s ret s0v s1v fs0b ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 na -> getr regs 8 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (0x60c44 : word) m rom)
                (@mkst (mkFP (bvmap_set 8 (bv_extract 0 64 (le_bytes_to_word fs0b)) (@fp_regs fx)) (@fp_csr fx)) regs' ret
                       (wbytes (wbytes m (Z_to_bv 64 (arr + 4 * n)) (Z_to_le_bytes 4 (u (low32 (reg_get (@fp_regs fx) 10)))))
                               (Z_to_bv 64 (na + 4)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13]%list) regs regs'.
Proof.
  intros regs m s na arr n ret s0v s1v fs0b Hs Hs64 Hna Hna2 Harr Harr2 Hn DJ Hret Hlen Rarr SOKc SOKn (C1 & C2 & C3 & C4) H2 H10 H8 H12.
  eexists. split.
  - sn F_60bec D_60bec.
    stepLD F_60bf0 D_60bf0 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply lez8; lia).
    stepiv F_60bf4 D_60bf4 (Z_to_bv 64 (4 * n)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    zv F_60bf8 D_60bf8 (Z_to_bv 64 (arr + 4 * n)).
    zv F_60bfc D_60bfc (Z_to_bv 64 (n + 1)).
    chain_step; [ reflexivity
                | eapply fp_step_fsw with (a := Z_to_bv 64 (arr + 4 * n)); [exact F_60c00 | reflexivity | exact D_60c00 | gres; imm_norm; addr_tac | exact SOKc]
                | step_simpl ].
    stepST F_60c04 D_60c04 (Z_to_bv 64 (na + 4)) (Z_to_bv 64 (n + 1)) ltac:(store_ok_peel; exact SOKn).
    sn F_60c08 D_60c08.
    stepLD8z F_60c0c D_60c0c ret C1. stepLD8z F_60c10 D_60c10 s0v C2. stepLD8z F_60c14 D_60c14 s1v C3.
    chain_step; [ reflexivity
                | eapply fp_step_fld with (a := Z_to_bv 64 (s - 32)) (bs := fs0b);
                  [exact F_60c18 | reflexivity | exact D_60c18 | gres; imm_norm; addr_tac | peelZ; exact C4]
                | step_simpl ].
    zv F_60c1c D_60c1c (Z_to_bv 64 s).
    stepret F_60c20 D_60c20 ret ltac:(bveq).
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
  (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 16)%Z -> (0 <= nalloc <= 50000000)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
  rdn SEGS m (Z_to_bv 64 na) 4 = Some (Z_to_le_bytes 4 nalloc) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 na ->
  exists regs',
    msteps SEGS (mkst regs (0x60cbc : word) m rom) (mkst regs' (0x5dc24 : word) (NEF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x60d4c
    /\ getr regs' 10 = Z_to_bv 64 (na + 24) /\ getr regs' 11 = Z_to_bv 64 (4 * nalloc) /\ getr regs' 12 = Z_to_bv 64 (8 * nalloc)
    /\ getr regs' 8 = Z_to_bv 64 na
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12; 13]%list) regs regs'.
Proof.
  intros regs m s na nalloc ret Hs Hs64 Hna Hna2 Hnal SOK Rnal H2 H1 H10.
  eexists. split.
  - zv F_60c64 D_60c64 (Z_to_bv 64 (s - 16)).
    stepST F_60c68 D_60c68 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_60c6c D_60c6c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepLD F_60c70 D_60c70 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    sn F_60c74 D_60c74. sn F_60c78 D_60c78.
    stepb_tk F_60c7c D_60c7c ltac:(condZ).
    sn F_60ca8 D_60ca8. sn F_60cac D_60cac.
    stepb_tk F_60cb0 D_60cb0 ltac:(condZ).
    stepiv F_60cdc D_60cdc (Z_to_bv 64 (4 * nalloc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    stepiv F_60ce0 D_60ce0 (Z_to_bv 64 (8 * nalloc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    zv F_60ce4 D_60ce4 (Z_to_bv 64 (na + 24)).
    sn F_60ce8 D_60ce8. sn F_60cec D_60cec. sn F_60cf0 D_60cf0.
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
    msteps SEGS (mkst regs (0x60d4c : word) m rom)
                (mkst regs' ret (wbytes (wbytes m (Z_to_bv 64 (na + 24)) (word_to_le_bytes 8 (Z_to_bv 64 arr')))
                                        (Z_to_bv 64 na) (word_to_le_bytes 4 (Z_to_bv 64 (2 * nalloc)))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 12]%list) regs regs'.
Proof.
  intros regs m s na nalloc arr' ret s0v Hs Hs64 Hna Hna2 Hnal Harr Hret SOK Rnal (C1 & C2) H2 H10 H8.
  eexists. split.
  - stepST F_60cf4 D_60cf4 (Z_to_bv 64 (na + 24)) (Z_to_bv 64 arr') ltac:(sok_in SOK).
    stepb_ft F_60cf8 D_60cf8 ltac:(condZ).
    sn F_60cfc D_60cfc.
    stepLD F_60d00 D_60d00 (Z_to_le_bytes 4 nalloc) (Z_to_bv 64 nalloc) ltac:(addr_norm; repeat rdn_peel1; exact Rnal) ltac:(apply lez4; lia).
    rewrite (v_lw_small nalloc) by lia.
    stepiv F_60d04 D_60d04 (Z_to_bv 64 (2 * nalloc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
    stepST F_60d08 D_60d08 (Z_to_bv 64 na) (Z_to_bv 64 (2 * nalloc)) ltac:(sok_in SOK).
    sn F_60d0c D_60d0c.
    stepLD8 F_60d4c D_60d4c ret. stepLD8 F_60d50 D_60d50 s0v.
    zv F_60d54 D_60d54 (Z_to_bv 64 s).
    stepret F_60d58 D_60d58 ret ltac:(bveq).
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
  (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= s - 48)%Z -> (0 <= ind < 2 ^ 64)%Z -> (1 <= new < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 ind) ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp -> getr regs 11 = Z_to_bv 64 old -> getr regs 12 = Z_to_bv 64 new ->
  exists regs',
    msteps SEGS (mkst regs (0x5dc24 : word) m rom) (mkst regs' (0xd78cc : word) (RNF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5dc60 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 new
    /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 ind /\ getr regs' 18 = Z_to_bv 64 old /\ getr regs' 19 = Z_to_bv 64 new
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
Proof.
  intros regs m s pp ind old new ret Hs Hs64 Hpp Hpp2 Hind Hnew SOK Rpp H2 H1 H10 H11 H12.
  eexists. split.
  - zv F_5dbcc D_5dbcc (Z_to_bv 64 (s - 48)).
    stepST F_5dbd0 D_5dbd0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_5dbd4 D_5dbd4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_5dbd8 D_5dbd8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_5dbdc D_5dbdc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_5dbe0 D_5dbe0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepb_ft F_5dbe4 D_5dbe4 ltac:(condZ).
    sn F_5dbe8 D_5dbe8.
    stepLD F_5dbec D_5dbec (Z_to_le_bytes 8 ind) (Z_to_bv 64 ind) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply lez8; lia).
    stepb_ft F_5dbf0 D_5dbf0 ltac:(condZ).
    sn F_5dbf4 D_5dbf4. sn F_5dbf8 D_5dbf8. sn F_5dbfc D_5dbfc. sn F_5dc00 D_5dc00. sn F_5dc04 D_5dc04.
    unfold RNF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rn_B : forall regs m (ind old new nb : Z),
  (1 <= ind < 2 ^ 64)%Z -> (1 <= nb < 2 ^ 64)%Z -> (0 <= old < new)%Z -> (new < 2 ^ 64)%Z ->
  getr regs 10 = Z_to_bv 64 nb -> getr regs 9 = Z_to_bv 64 ind -> getr regs 18 = Z_to_bv 64 old -> getr regs 19 = Z_to_bv 64 new ->
  exists regs',
    msteps SEGS (mkst regs (0x5dc60 : word) m rom) (mkst regs' (0xe5ed4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x5dc80 /\ getr regs' 10 = Z_to_bv 64 nb /\ getr regs' 11 = Z_to_bv 64 ind /\ getr regs' 12 = Z_to_bv 64 old
    /\ getr regs' 19 = Z_to_bv 64 nb
    /\ regs_agree (fun r => In r [1; 11; 12; 19]%list) regs regs'.
Proof.
  intros regs m ind old new nb Hind Hnb Hold Hnew H10 H9 H18 H19.
  eexists. split.
  - stepb_ft F_5dc08 D_5dc08 ltac:(condZ).
    stepb_ft F_5dc0c D_5dc0c ltac:(condZ).
    stepb_tk F_5dc10 D_5dc10 ltac:(condZ).
    sn F_5dc18 D_5dc18. sn F_5dc1c D_5dc1c. sn F_5dc20 D_5dc20. sn F_5dc24 D_5dc24.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rn_C : forall regs m (ind : Z), getr regs 9 = Z_to_bv 64 ind ->
  exists regs',
    msteps SEGS (mkst regs (0x5dc80 : word) m rom) (mkst regs' (0xd7a04 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x5dc88 /\ getr regs' 10 = Z_to_bv 64 ind
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m ind H9. eexists. split.
  - sn F_5dc28 D_5dc28. sn F_5dc2c D_5dc2c. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rn_D : forall regs m (s pp nb : Z) (ret s0v s1v s2v s3v : word),
  (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= s - 48)%Z -> ret_ok ret ->
  store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> rncells m s ret s0v s1v s2v s3v ->
  getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pp -> getr regs 19 = Z_to_bv 64 nb ->
  exists regs',
    msteps SEGS (mkst regs (0x5dc88 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 nb
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
Proof.
  intros regs m s pp nb ret s0v s1v s2v s3v Hs Hs64 Hpp Hpp2 Hret SOK (C1 & C2 & C3 & C4 & C5) H2 H8 H19.
  eexists. split.
  - sn F_5dc30 D_5dc30. sn F_5dc34 D_5dc34.
    stepST F_5dc8c D_5dc8c (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
    sn F_5dc90 D_5dc90.
    stepLD8 F_5dcec D_5dcec ret. stepLD8 F_5dcf0 D_5dcf0 s0v. stepLD8 F_5dcf4 D_5dcf4 s1v. stepLD8 F_5dcf8 D_5dcf8 s2v. stepLD8 F_5dcfc D_5dcfc s3v.
    zv F_5dd00 D_5dd00 (Z_to_bv 64 s).
    stepret F_5dd04 D_5dd04 ret ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

End NumaSegs.
