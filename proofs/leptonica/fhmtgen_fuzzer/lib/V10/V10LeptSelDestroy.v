(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSlots LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptSel_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhFG.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptSelSegs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoom10.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SelDestroy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsD.
Variable rom : word -> option byte.

  Definition SDF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  Definition sdcells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

  Lemma sdcells_SDF : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    sdcells (SDF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19).
  Proof. intros m s ret regs Hs Hs64. unfold sdcells, SDF. repeat split; rdn_chain. Qed.

  (* [comment removed for export] *)
  Lemma sd_A : forall regs m (s pp sel sy : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> (pp + 8 <= s - 48 \/ s <= pp)%Z ->
    (1 <= sel)%Z -> (sel + 32 <= s - 48)%Z -> (1 <= sy < 2 ^ 31)%Z -> (pp mod 8 = 0)%Z -> (sel mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 sel) -> rdn SEGS m (Z_to_bv 64 sel) 4 = Some (Z_to_le_bytes 4 sy) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x26f58 : word) m rom) (mkst regs' (0x26fa0 : word) (SDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 sel
      /\ getr regs' 18 = Z_to_bv 64 (8 * 0) /\ getr regs' 19 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp sel sy ret Hs Hs64 Hpp Hpp64 DJ Hsel Hsel2 Hsy ALpp ALsel SOK Rpp Rsy H2 H1 H10.
    eexists. split.
    - zv F_26e5c D_26e5c (Z_to_bv 64 (s - 48)).
      stepST F_26e60 D_26e60 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_26e64 D_26e64 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_26e68 D_26e68 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_26e6c D_26e6c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_26e70 D_26e70 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_26e74 D_26e74 ltac:(condZ).
      sn F_26e78 D_26e78.
      zand F_26e7c D_26e7c andi_7 ALpp. stepb_ft F_26e80 D_26e80 ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_26e84 D_26e84 (Z_to_le_bytes 8 sel) (Z_to_bv 64 sel) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply lez8; lia).
      stepb_ft F_26e88 D_26e88 ltac:(condZ).
      zand F_26e8c D_26e8c andi_7 ALsel. stepb_ft F_26e90 D_26e90 ltac:(condZ).         (* [comment removed for export] *)
      stepLD F_26e94 D_26e94 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; repeat rdn_peel1; exact Rsy) ltac:(apply lez4; lia).
      rewrite (v_lw_small sy) by lia.
      stepb_ft F_26e98 D_26e98 ltac:(condZ).
      sn F_26e9c D_26e9c. sn F_26ea0 D_26ea0.
      unfold SDF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sd_H : forall regs m (sel data i row : Z),
    (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * i + 8 < 2 ^ 64)%Z -> (0 <= i < 2 ^ 31)%Z -> (0 <= row < 2 ^ 64)%Z ->
    (data mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) -> rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
    getr regs 9 = Z_to_bv 64 sel -> getr regs 18 = Z_to_bv 64 (8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x26fa0 : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x26fd4 /\ getr regs' 10 = Z_to_bv 64 row
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m sel data i row Hs Hs64 Hd Hd64 Hi Hrow ALd Rd Rr H9 H18.
    assert (ALc : ((data + 8 * i) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALd).
    eexists. split.
    - stepLD F_26ea4 D_26ea4 (Z_to_le_bytes 8 data) (Z_to_bv 64 data) ltac:(addr_norm; exact Rd) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      zv F_26ea8 D_26ea8 (Z_to_bv 64 (data + 8 * i)).                                 (* [comment removed for export] *)
      stepb_ft F_26eac D_26eac ltac:(condZ).                                          (* [comment removed for export] *)
      snez1 F_26eb0 D_26eb0.                                                          (* [comment removed for export] *)
      seqz0 F_26eb4 D_26eb4.                                                          (* [comment removed for export] *)
      zlit F_26eb8 D_26eb8 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_26ebc D_26ebc ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_26ec0 D_26ec0 ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_26ec4 D_26ec4 (Z_to_bv 64 (data + 8 * i)).                                 (* [comment removed for export] *)
      zand F_26ec8 D_26ec8 andi_7 ALc. stepb_ft F_26ecc D_26ecc ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_26ed0 D_26ed0 (Z_to_le_bytes 8 row) (Z_to_bv 64 row) ltac:(addr_norm; exact Rr) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      sn F_26ed4 D_26ed4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sd_N_cont : forall regs m (sel sy i : Z),
    (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 sel) 4 = Some (Z_to_le_bytes 4 sy) ->
    getr regs 9 = Z_to_bv 64 sel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x26fd4 : word) m rom) (mkst regs' (0x26fa0 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun r => In r [10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m sel sy i Hs Hs64 Hi Hi1 Hsy Rsy H9 H18 H19.
    eexists. split.
    - stepLD F_26ed8 D_26ed8 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply lez4; lia).
      rewrite (v_lw_small sy) by lia.
      zv F_26edc D_26edc (Z_to_bv 64 (i + 1)).
      zv F_26ee0 D_26ee0 (Z_to_bv 64 (8 * (i + 1))).
      stepb_tk F_26ee4 D_26ee4 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma sd_N_last : forall regs m (sel sy i data : Z),
    (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = sy)%Z -> (sy < 2 ^ 31)%Z -> (0 <= data < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 sel) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
    getr regs 9 = Z_to_bv 64 sel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x26fd4 : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x26fec /\ getr regs' 10 = Z_to_bv 64 data
      /\ regs_agree (fun r => In r [1; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m sel sy i data Hs Hs64 Hi Hi1 Hsy Hd Rsy Rd H9 H18 H19.
    eexists. split.
    - stepLD F_26ed8 D_26ed8 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply lez4; lia).
      rewrite (v_lw_small sy) by lia.
      zv F_26edc D_26edc (Z_to_bv 64 (i + 1)).
      zv F_26ee0 D_26ee0 (Z_to_bv 64 (8 * (i + 1))).
      stepb_ft F_26ee4 D_26ee4 ltac:(condZ).
      stepLD F_26ee8 D_26ee8 (Z_to_le_bytes 8 data) (Z_to_bv 64 data) ltac:(addr_norm; exact Rd) ltac:(apply lez8; lia).
      sn F_26eec D_26eec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sd_D : forall regs m (sel name : Z),
    (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (1 <= name < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 name) -> getr regs 9 = Z_to_bv 64 sel ->
    exists regs',
      msteps SEGS (mkst regs (0x26fec : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x26ff8 /\ getr regs' 10 = Z_to_bv 64 name
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m sel name Hs Hs64 Hn Rn H9. eexists. split.
    - stepLD F_26ef0 D_26ef0 (Z_to_le_bytes 8 name) (Z_to_bv 64 name) ltac:(addr_norm; exact Rn) ltac:(apply lez8; lia).
      stepb_ft F_26ef4 D_26ef4 ltac:(condZ).
      sn F_26ef8 D_26ef8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sd_E : forall regs m (sel : Z), getr regs 9 = Z_to_bv 64 sel ->
    exists regs',
      msteps SEGS (mkst regs (0x26ff8 : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x27000 /\ getr regs' 10 = Z_to_bv 64 sel
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m sel H9. eexists. split.
    - sn F_26efc D_26efc. sn F_26f00 D_26f00. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sd_F : forall regs m (s pp : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> (pp + 8 <= s - 48 \/ s <= pp)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> sdcells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x27000 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v s2v s3v Hs Hs64 Hpp Hpp64 DJ Hret SOK (C1 & C2 & C3 & C4 & C5) H2 H8.
    eexists. split.
    - stepST F_26f04 D_26f04 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      sn F_26f08 D_26f08.
      stepLD8 F_26f4c D_26f4c ret. stepLD8 F_26f50 D_26f50 s0v. stepLD8 F_26f54 D_26f54 s1v. stepLD8 F_26f58 D_26f58 s2v. stepLD8 F_26f5c D_26f5c s3v.
      zv F_26f60 D_26f60 (Z_to_bv 64 s).
      stepret F_26f64 D_26f64 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsD.

Lemma sdcells_FRM : forall C M M' s ret s0v s1v s2v s3v, Cok C -> FRM C (s - 48) M M' ->
  (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z ->
  sdcells M s ret s0v s1v s2v s3v -> sdcells M' s ret s0v s1v s2v s3v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold sdcells.
  rewrite !(FRM_rdn16 C (s - 48) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

#[local] Definition sd_rest : list (bv 5) := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition sdst (C : lctx) (A : AS) (m : word -> option byte) (s sel : Z) (v : selv) (regs : bvmap 5 word) (i : Z)
                (A1 : AS) (M1 : word -> option byte) : Prop :=
  POSTM C A1 s m M1 /\ sub_live A1 A /\
  sdcells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) /\
  live A1 (Z_to_bv 64 sel) = Some 32%Z /\ live A1 (Z_to_bv 64 (v_data v)) = Some (8 * v_sy v)%Z /\
  (forall j, (i <= j < v_sy v)%Z -> live A1 (Z_to_bv 64 (v_rows v j)) = Some (4 * v_sx v)%Z) /\
  (forall j, (0 <= j < i)%Z -> live A1 (Z_to_bv 64 (v_rows v j)) = None) /\
  (forall q, (forall j, (0 <= j < v_sy v)%Z -> q <> Z_to_bv 64 (v_rows v j)) -> live A1 q = live A q).

(* [comment removed for export] *)
Lemma sd_loop : forall (k : nat) C A m md regs (s pp sel : Z) (v : selv) (S : TSet) A1 M1 vm1 r (i : Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 ->
  sel_at (alloc_top (c_vm C)) A m sel v -> sel_off (c_A0 C) sel v ->
  (Z.of_nat k = v_sy v - 1 - i)%Z -> (0 <= i < v_sy v)%Z ->
  W C A1 M1 (with_vmmaps vm1 md) -> roomtr A (m_vmmaps md) A1 vm1 0 0 -> sdst C A m s sel v regs i A1 M1 ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pp -> getr r 9 = Z_to_bv 64 sel -> getr r 18 = Z_to_bv 64 (8 * i) -> getr r 19 = Z_to_bv 64 i ->
  getr r 4 = Z_to_bv 64 0x45480 -> (forall x, In x sd_rest -> getr r x = getr regs x) ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> roomtr A (m_vmmaps md) A' vm' 0 0 ->
     POSTM C A' s m m' -> sub_live A' A -> sdcells m' s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
     live A' (Z_to_bv 64 sel) = Some 32%Z -> live A' (Z_to_bv 64 (v_data v)) = None ->
     (forall j, (0 <= j < v_sy v)%Z -> live A' (Z_to_bv 64 (v_rows v j)) = None) ->
     (forall q, q <> Z_to_bv 64 (v_data v) -> (forall j, (0 <= j < v_sy v)%Z -> q <> Z_to_bv 64 (v_rows v j)) -> live A' q = live A q) ->
     getr r' 2 = Z_to_bv 64 (s - 48) -> getr r' 8 = Z_to_bv 64 pp -> getr r' 9 = Z_to_bv 64 sel -> getr r' 4 = Z_to_bv 64 0x45480 ->
     (forall x, In x sd_rest -> getr r' x = getr regs x) ->
     realizes SEGS (mkCfg (mkst r' (0x26fec : word) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0x26fa0 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros C A m md regs s pp sel v S A1 M1 vm1 r i CK Hs16 Hlo Hhi H4 SA SO0 Hk Hi HW HRT (PM & SUB & CE & Ls & Ld & ROWL & DONE & RQ)
    R2 R8 R9 R18 R19 R4 RR HK;
    pose proof SA as (Hsy & Hsx & (Gs & TOPs & _) & LsA & Rs & (Gd & TOPd & ALd) & LdA & NEd & ROWS & DIST);
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LLU16] in *; unfold ALLOC_STACK in Hlo; unfold sd_rest in RR;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    destruct (ROWS i Hi) as ((Gr & TOPr & _) & LrA & NErd & NErs & Bi);
    (* [comment removed for export] *)
    assert (Rs1 : RECat M1 sel (sel_flds (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) (v_name v)))
      by (apply (RECat_POSTM C A1 s m M1 (Z_to_bv 64 sel) 32 _ _ Rs PM Ls); rewrite u_Z2bv by lia; [lia | cbn; lia]);
    pose proof (REC_rd' SEGS M1 sel _ 0 4 (Z_to_bv 64 sel) (v_sy v) Rs1 ltac:(cbn; lia) eq_refl ltac:(cbn [fld_off sel_flds Z.of_nat]; f_equal; lia) eq_refl) as Rsy;
    pose proof (REC_rd' SEGS M1 sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data v) Rs1 ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rdt;
    assert (Bi1 : bytes_at M1 (v_data v + 8 * i) (Z_to_le_bytes 8 (v_rows v i)))
      by (apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia]; rewrite length_Z_to_le_bytes; intros x Hx;
          exact (LIVK_in A1 m M1 (v_data v) (8 * v_sy v) x (proj2 PM) Ld ltac:(lia) ltac:(lia) ltac:(lia)));
    pose proof (bytes_at_rdn SEGS M1 (v_data v + 8 * i) (Z_to_le_bytes 8 (v_rows v i)) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) Bi1) as Rri;
    rewrite length_Z_to_le_bytes in Rri;
    destruct (sd_H al_rom r M1 sel (v_data v) i (v_rows v i) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (bok_mod8 _ _ _ (conj Gd (conj TOPd ALd))) Rdt Rri R9 R18)
      as (r1 & RUN1 & Q1 & Q10 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity);
    assert (Lr0 : live (c_A0 C) (Z_to_bv 64 (v_rows v i)) = None) by (apply SO0; right; right; exists i; split; [exact Hi | reflexivity]);
    (apply (W_free16 C A1 M1 _ r1 (Z_to_bv 64 (v_rows v i)) (Z_to_bv 64 0x26fd4) (4 * v_sx v) (s - 48) S CK HW Q10 (ROWL i ltac:(lia)) Lr0 Q1
             ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG1 4) by notin_lit; exact R4)
             ltac:(rewrite (AG1 2) by notin_lit; exact R2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)));
    intros A2 m2 vm2 r2 HW2 CS2 Li2 LEQ2 PM2 HRT2; rewrite ?with_vmmaps_twice in HW2 |- *;
    replace (Z_to_bv 64 0x26fd4) with (0x26fd4 : word) by (apply bv_eq; reflexivity);
    assert (HRTb : roomtr A (m_vmmaps md) A2 vm2 0 0) by (apply (roomtr_trans A (m_vmmaps md) A1 vm1 A2 vm2 0 0 0 0 HRT (roomtr_wv _ _ _ _ _ _ _ HRT2)); lia);
    assert (NEsi : Z_to_bv 64 sel <> Z_to_bv 64 (v_rows v i)) by (apply zbv_ne; lia);
    assert (NEdi : Z_to_bv 64 (v_data v) <> Z_to_bv 64 (v_rows v i)) by (apply zbv_ne; lia);
    assert (NEji : forall j, (0 <= j < v_sy v)%Z -> j <> i -> Z_to_bv 64 (v_rows v j) <> Z_to_bv 64 (v_rows v i))
      by (intros j Hj NE; destruct (ROWS j Hj) as ((? & ? & _) & _); apply zbv_ne; [lia | lia | apply (DIST j i); lia]);
    assert (Ls2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NEsi); exact Ls);
    assert (Ld2 : live A2 (Z_to_bv 64 (v_data v)) = Some (8 * v_sy v)%Z) by (rewrite (LEQ2 _ NEdi); exact Ld);
    assert (SUB21 : sub_live A2 A1)
      by (intros q kq Lq; destruct (bv_eq_dec _ q (Z_to_bv 64 (v_rows v i))) as [->|NE]; [rewrite Li2 in Lq; discriminate | rewrite <- (LEQ2 q NE); exact Lq]);
    assert (SUB2 : sub_live A2 A) by (eapply sub_live_trans; eassumption);
    assert (PM2' : POSTM C A2 s m m2)
      by (eapply POSTM_trans; [apply (POSTM_sub C A2 A1 _ _ _ SUB21); exact PM | eapply POSTM_mono; [|exact PM2]; lia]);
    pose proof (sdcells_FRM C M1 m2 s _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE) as CE2;
    assert (Rs2 : RECat m2 sel (sel_flds (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) (v_name v)))
      by (apply (RECat_POSTM C A2 s m m2 (Z_to_bv 64 sel) 32 _ _ Rs PM2' Ls2); rewrite u_Z2bv by lia; [lia | cbn; lia]);
    pose proof (REC_rd' SEGS m2 sel _ 0 4 (Z_to_bv 64 sel) (v_sy v) Rs2 ltac:(cbn; lia) eq_refl ltac:(cbn [fld_off sel_flds Z.of_nat]; f_equal; lia) eq_refl) as Rsy2;
    pose proof (REC_rd' SEGS m2 sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data v) Rs2 ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rdt2;
    assert (DONE2 : forall j, (0 <= j < i + 1)%Z -> live A2 (Z_to_bv 64 (v_rows v j)) = None)
      by (intros j Hj; destruct (Z.eq_dec j i) as [->|NE]; [exact Li2|]; rewrite (LEQ2 _ (NEji j ltac:(lia) NE)); apply DONE; lia);
    assert (RQ2 : forall q, (forall j, (0 <= j < v_sy v)%Z -> q <> Z_to_bv 64 (v_rows v j)) -> live A2 q = live A q)
      by (intros q NQr; rewrite (LEQ2 q (NQr i ltac:(lia))); exact (RQ q NQr));
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (rewrite (CS2 2%bv cs2); rewrite (AG1 2) by notin_lit; exact R2);
    assert (E8 : getr r2 8 = Z_to_bv 64 pp) by (rewrite (CS2 8%bv cs8); rewrite (AG1 8) by notin_lit; exact R8);
    assert (E9 : getr r2 9 = Z_to_bv 64 sel) by (rewrite (CS2 9%bv cs9); rewrite (AG1 9) by notin_lit; exact R9);
    assert (E18 : getr r2 18 = Z_to_bv 64 (8 * i)) by (rewrite (CS2 18%bv cs18); rewrite (AG1 18) by notin_lit; exact R18);
    assert (E19 : getr r2 19 = Z_to_bv 64 i) by (rewrite (CS2 19%bv cs19); rewrite (AG1 19) by notin_lit; exact R19);
    assert (E4 : getr r2 4 = Z_to_bv 64 0x45480) by (rewrite (CS2 4%bv cs4); rewrite (AG1 4) by notin_lit; exact R4);
    assert (RR2 : forall x, In x sd_rest -> getr r2 x = getr regs x)
      by (intros x Hx; rewrite <- (RR x Hx); unfold sd_rest in Hx; cbn [In] in Hx;
          repeat (destruct Hx as [<-|Hx]; [first [ rewrite (CS2 _ cs3) | rewrite (CS2 _ cs4) | rewrite (CS2 _ cs20) | rewrite (CS2 _ cs21) | rewrite (CS2 _ cs22)
                                                 | rewrite (CS2 _ cs23) | rewrite (CS2 _ cs24) | rewrite (CS2 _ cs25) | rewrite (CS2 _ cs26) | rewrite (CS2 _ cs27) ];
                                           apply AG1; notin_lit|]); destruct Hx).
  - (* [comment removed for export] *)
    destruct (sd_N_last al_rom r2 m2 sel (v_sy v) i (v_data v) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rsy2 Rdt2 E9 E18 E19)
      as (r3 & RUN3 & P1 & P10 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity).
    assert (Ld0 : live (c_A0 C) (Z_to_bv 64 (v_data v)) = None) by (apply SO0; right; left; reflexivity).
    apply (W_free16 C A2 m2 _ r3 (Z_to_bv 64 (v_data v)) (Z_to_bv 64 0x26fec) (8 * v_sy v) (s - 48) S CK HW2 P10 Ld2 Ld0 P1
             ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG3 4) by notin_lit; exact E4)
             ltac:(rewrite (AG3 2) by notin_lit; exact E2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A3 m3 vm3 r4 HW3 CS3 Ld3 LEQ3 PM3 HRT3. rewrite ?with_vmmaps_twice in HW3 |- *.
    replace (Z_to_bv 64 0x26fec) with (0x26fec : word) by (apply bv_eq; reflexivity).
    assert (SUB32 : sub_live A3 A2)
      by (intros q kq Lq; destruct (bv_eq_dec _ q (Z_to_bv 64 (v_data v))) as [->|NE]; [rewrite Ld3 in Lq; discriminate | rewrite <- (LEQ3 q NE); exact Lq]).
    apply (HK A3 m3 vm3 r4 HW3).
    + apply (roomtr_trans A (m_vmmaps md) A2 vm2 A3 vm3 0 0 0 0 HRTb (roomtr_wv _ _ _ _ _ _ _ HRT3)); lia.
    + eapply POSTM_trans; [apply (POSTM_sub C A3 A2 _ _ _ SUB32); exact PM2' | eapply POSTM_mono; [|exact PM3]; lia].
    + eapply sub_live_trans; eassumption.
    + exact (sdcells_FRM C m2 m3 s _ _ _ _ _ CK (proj1 PM3) ltac:(lia) ltac:(lia) CE2).
    + rewrite (LEQ3 (Z_to_bv 64 sel) ltac:(apply zbv_ne; lia)). exact Ls2.
    + exact Ld3.
    + intros j Hj. destruct (ROWS j Hj) as ((G1 & G2 & _) & _ & G3 & _). rewrite (LEQ3 (Z_to_bv 64 (v_rows v j)) ltac:(apply zbv_ne; lia)). apply DONE2. lia.
    + intros q NQd NQr. rewrite (LEQ3 q NQd). exact (RQ2 q NQr).
    + rewrite (CS3 2%bv cs2). rewrite (AG3 2) by notin_lit. exact E2.
    + rewrite (CS3 8%bv cs8). rewrite (AG3 8) by notin_lit. exact E8.
    + rewrite (CS3 9%bv cs9). rewrite (AG3 9) by notin_lit. exact E9.
    + rewrite (CS3 4%bv cs4). rewrite (AG3 4) by notin_lit. exact E4.
    + intros x Hx. rewrite <- (RR2 x Hx). unfold sd_rest in Hx. cbn [In] in Hx.
      repeat (destruct Hx as [<-|Hx]; [first [ rewrite (CS3 _ cs3) | rewrite (CS3 _ cs4) | rewrite (CS3 _ cs20) | rewrite (CS3 _ cs21) | rewrite (CS3 _ cs22)
                                             | rewrite (CS3 _ cs23) | rewrite (CS3 _ cs24) | rewrite (CS3 _ cs25) | rewrite (CS3 _ cs26) | rewrite (CS3 _ cs27) ];
                                       apply AG3; notin_lit|]). destruct Hx.
  - (* [comment removed for export] *)
    destruct (sd_N_cont al_rom r2 m2 sel (v_sy v) i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rsy2 E9 E18 E19) as (r3 & RUN3 & P18 & P19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (IH C A m md regs s pp sel v S A2 m2 vm2 r3 (i + 1)%Z CK Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi H4 SA SO0 ltac:(lia) ltac:(lia) HW2 HRTb); try exact HK; try exact P18; try exact P19.
    + split; [exact PM2'|]. split; [exact SUB2|]. split; [exact CE2|]. split; [exact Ls2|]. split; [exact Ld2|].
      split; [intros j Hj; rewrite (LEQ2 _ (NEji j ltac:(lia) ltac:(lia))); apply ROWL; lia|]. split; [exact DONE2 | exact RQ2].
    + rewrite (AG3 2) by notin_lit. exact E2.
    + rewrite (AG3 8) by notin_lit. exact E8.
    + rewrite (AG3 9) by notin_lit. exact E9.
    + rewrite (AG3 4) by notin_lit. exact E4.
    + intros x Hx. rewrite (AG3 x); [exact (RR2 x Hx)|]. unfold sd_rest in Hx. cbn [In] in *. intros HH.
      repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx.
Qed.

(* [comment removed for export] *)
Theorem selDestroy_W : forall C A m md regs (s pp sel : Z) (v : selv) (nm : list byte) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 sel) ->
  sel_at (alloc_top (c_vm C)) A m sel v -> selname_at (alloc_top (c_vm C)) A m (v_name v) nm -> (forall p, sel_blk sel v p -> p <> v_name v) ->
  sel_off (c_A0 C) sel v -> live (c_A0 C) (Z_to_bv 64 (v_name v)) = None ->
  (forall p k, sb = Some (p, k) -> forall q, seln_blk sel v q -> p <> Z_to_bv 64 q) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (forall q, seln_blk sel v q -> live A' (Z_to_bv 64 q) = None) ->
     (forall q, (forall p, seln_blk sel v p -> q <> Z_to_bv 64 p) -> live A' q = live A q) -> sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x26f58 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sel v nm sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 SL ALpp Rpp SA NA NBN SO0 Ln0 DISJ HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof SA as (Hsy & Hsx & (Gs & TOPs & _) & Ls & Rs & (Gd & TOPd & _) & Ld & NEd & ROWS & DIST).
  pose proof NA as ((Gn & TOPn & _) & Ln & _).
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 48 \/ s <= pp)%Z) by lia.
  pose proof (REC_rd' SEGS m sel _ 0 4 (Z_to_bv 64 sel) (v_sy v) Rs ltac:(cbn; lia) eq_refl ltac:(cbn [fld_off sel_flds Z.of_nat]; f_equal; lia) eq_refl) as Rsy.
  destruct (sd_A al_rom regs m s pp sel (v_sy v) ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) DJ ltac:(lia) ltac:(lia) ltac:(lia) ALpp (bok_mod8 _ _ _ (proj1 (proj2 (proj2 SA))))
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp Rsy H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := SDF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold SDF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (sdcells_SDF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  assert (SD0 : sdst C A m s sel v regs 0 A M1).
  { split; [exact PM1|]. split; [apply sub_live_refl|]. split; [exact CE1|]. split; [exact Ls|]. split; [exact Ld|].
    split; [intros j Hj; destruct (ROWS j ltac:(lia)) as (_ & G & _); exact G|]. split; [intros j Hj; lia | intros q _; reflexivity]. }
  apply (sd_loop (Z.to_nat (v_sy v - 1)) C A m md regs s pp sel v S A M1 (m_vmmaps md) r1 0 CK Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi H4 SA SO0
           ltac:(lia) ltac:(lia) HW1 ltac:(apply roomtr_refl; lia) SD0 Q2 Q8 Q9 Q18 Q19
           ltac:(rewrite (AG1 4) by notin_lit; exact H4)
           ltac:(intros x Hx; apply AG1; unfold sd_rest in Hx; cbn [In] in *; intros HH;
                 repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx)).
  clear SD0. intros A3 m3 vm3 r3 HW3 HRT3 PM3 SUB3 CE3 Ls3 Ld3 DONE3 RQ3 E2 E8 E9 E4 RR3.
  (* [comment removed for export] *)
  assert (NEnd : Z_to_bv 64 (v_name v) <> Z_to_bv 64 (v_data v)) by (apply zbv_ne; [lia | lia |]; exact (not_eq_sym (NBN _ (or_intror (or_introl eq_refl))))).
  assert (NEnr : forall j, (0 <= j < v_sy v)%Z -> Z_to_bv 64 (v_name v) <> Z_to_bv 64 (v_rows v j)).
  { intros j Hj. destruct (ROWS j Hj) as ((G1 & G2 & _) & _). apply zbv_ne; [lia | lia |]. exact (not_eq_sym (NBN _ (or_intror (or_intror (ex_intro _ j (conj Hj eq_refl)))))). }
  assert (NEns : Z_to_bv 64 (v_name v) <> Z_to_bv 64 sel) by (apply zbv_ne; [lia | lia |]; exact (not_eq_sym (NBN _ (or_introl eq_refl)))).
  assert (Ln3 : live A3 (Z_to_bv 64 (v_name v)) = Some (Z.of_nat (length nm) + 1)%Z) by (rewrite (RQ3 _ NEnd NEnr); exact Ln).
  assert (Rs3 : RECat m3 sel (sel_flds (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) (v_name v)))
    by (apply (RECat_POSTM C A3 s m m3 (Z_to_bv 64 sel) 32 _ _ Rs PM3 Ls3); rewrite u_Z2bv by lia; [lia | cbn; lia]).
  pose proof (REC_rd' SEGS m3 sel _ 5 8 (Z_to_bv 64 (sel + 24)) (v_name v) Rs3 ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rnm.
  destruct (sd_D al_rom r3 m3 sel (v_name v) ltac:(lia) ltac:(lia) ltac:(lia) Rnm E9) as (r4 & RUN4 & P1 & P10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity).
  apply (W_free16 C A3 m3 _ r4 (Z_to_bv 64 (v_name v)) (Z_to_bv 64 0x26ff8) _ (s - 48) S CK HW3 P10 Ln3 Ln0 P1
           ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG4 4) by notin_lit; exact E4)
           ltac:(rewrite (AG4 2) by notin_lit; exact E2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A4 m4 vm4 r5 HW4 CS4 Ln4 LEQ4 PM4 HRT4. rewrite ?with_vmmaps_twice in HW4 |- *.
  replace (Z_to_bv 64 0x26ff8) with (0x26ff8 : word) by (apply bv_eq; reflexivity).
  assert (F9 : getr r5 9 = Z_to_bv 64 sel) by (rewrite (CS4 9%bv cs9); rewrite (AG4 9) by notin_lit; exact E9).
  destruct (sd_E al_rom r5 m4 sel F9) as (r6 & RUN6 & V1 & V10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
  replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity).
  assert (Ls4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ (not_eq_sym NEns)); exact Ls3).
  assert (F2 : getr r5 2 = Z_to_bv 64 (s - 48)) by (rewrite (CS4 2%bv cs2); rewrite (AG4 2) by notin_lit; exact E2).
  assert (F4 : getr r5 4 = Z_to_bv 64 0x45480) by (rewrite (CS4 4%bv cs4); rewrite (AG4 4) by notin_lit; exact E4).
  apply (W_free16 C A4 m4 _ r6 (Z_to_bv 64 sel) (Z_to_bv 64 0x27000) 32 (s - 48) S CK HW4 V10 Ls4 (SO0 sel (or_introl eq_refl)) V1
           ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG6 4) by notin_lit; exact F4)
           ltac:(rewrite (AG6 2) by notin_lit; exact F2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A5 m5 vm5 r7 HW5 CS5 Ls5 LEQ5 PM5 HRT5. rewrite ?with_vmmaps_twice in HW5 |- *.
  replace (Z_to_bv 64 0x27000) with (0x27000 : word) by (apply bv_eq; reflexivity).
  (* [comment removed for export] *)
  assert (SUB43 : sub_live A4 A3)
    by (intros q kq Lq; destruct (bv_eq_dec _ q (Z_to_bv 64 (v_name v))) as [->|NE]; [rewrite Ln4 in Lq; discriminate | rewrite <- (LEQ4 q NE); exact Lq]).
  assert (SUB54 : sub_live A5 A4)
    by (intros q kq Lq; destruct (bv_eq_dec _ q (Z_to_bv 64 sel)) as [->|NE]; [rewrite Ls5 in Lq; discriminate | rewrite <- (LEQ5 q NE); exact Lq]).
  assert (SUB5 : sub_live A5 A) by (eapply sub_live_trans; [exact SUB54 | eapply sub_live_trans; [exact SUB43 | exact SUB3]]).
  assert (PM5' : POSTM C A5 s m m5).
  { eapply POSTM_trans; [apply (POSTM_sub C A5 A3 _ _ _ (sub_live_trans _ _ _ SUB54 SUB43)); exact PM3|].
    eapply POSTM_trans; [apply (POSTM_sub C A5 A4 _ _ _ SUB54); eapply POSTM_mono; [|exact PM4]; lia | eapply POSTM_mono; [|exact PM5]; lia]. }
  assert (OTHER : forall q, (forall p, seln_blk sel v p -> q <> Z_to_bv 64 p) -> live A5 q = live A q).
  { intros q NQ. rewrite (LEQ5 q (NQ sel (or_introl (or_introl eq_refl)))). rewrite (LEQ4 q (NQ _ (or_intror eq_refl))).
    apply RQ3; [exact (NQ _ (or_introl (or_intror (or_introl eq_refl)))) | intros j Hj; exact (NQ _ (or_introl (or_intror (or_intror (ex_intro _ j (conj Hj eq_refl))))))]. }
  assert (SL5 : slotok C A5 s pp sb).
  { apply (slot_keep C A A5 s pp sb SL). intros p0 n0 E. apply OTHER. intros p Hp. exact (DISJ p0 n0 E p Hp). }
  pose proof (slot_sok C A5 m5 _ s pp sb CK HW5 SL5 ltac:(lia)) as SOKp. rewrite p16_segs in SOKp.
  pose proof (sdcells_FRM C m4 m5 s _ _ _ _ _ CK (proj1 PM5) ltac:(lia) ltac:(lia)
                (sdcells_FRM C m3 m4 s _ _ _ _ _ CK (proj1 PM4) ltac:(lia) ltac:(lia) CE3)) as CE5.
  assert (G2 : getr r7 2 = Z_to_bv 64 (s - 48)) by (rewrite (CS5 2%bv cs2); rewrite (AG6 2) by notin_lit; exact F2).
  assert (G8 : getr r7 8 = Z_to_bv 64 pp)
    by (rewrite (CS5 8%bv cs8); rewrite (AG6 8) by notin_lit; rewrite (CS4 8%bv cs8); rewrite (AG4 8) by notin_lit; exact E8).
  destruct (sd_F al_rom r7 m5 s pp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) DJ
              ltac:(rewrite H1; exact Hret) SOKp CE5 G2 G8) as (r8 & RUN8 & Z2 & Z1 & Z8 & Z9 & Z18 & Z19 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN8 |].
  set (M6 := wbytes m5 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (HW6 : W C A5 M6 (with_vmmaps vm5 md)) by (subst M6; apply (slot_W C A5 m5 _ s pp sb _ CK HW5 SL5 ltac:(lia)); rewrite length_N_to_le_bytes; reflexivity).
  rewrite H1. apply (HK A5 M6 vm5 r8 HW6).
  - assert (REST : forall x, In x sd_rest -> getr r8 x = getr regs x).
    { intros x Hx. rewrite <- (RR3 x Hx). unfold sd_rest in Hx. cbn [In] in Hx.
      repeat (destruct Hx as [<-|Hx];
              [rewrite (AG8 _) by notin_lit;
               first [ rewrite (CS5 _ cs3) | rewrite (CS5 _ cs4) | rewrite (CS5 _ cs20) | rewrite (CS5 _ cs21) | rewrite (CS5 _ cs22)
                     | rewrite (CS5 _ cs23) | rewrite (CS5 _ cs24) | rewrite (CS5 _ cs25) | rewrite (CS5 _ cs26) | rewrite (CS5 _ cs27) ];
               rewrite (AG6 _) by notin_lit;
               first [ rewrite (CS4 _ cs3) | rewrite (CS4 _ cs4) | rewrite (CS4 _ cs20) | rewrite (CS4 _ cs21) | rewrite (CS4 _ cs22)
                     | rewrite (CS4 _ cs23) | rewrite (CS4 _ cs24) | rewrite (CS4 _ cs25) | rewrite (CS4 _ cs26) | rewrite (CS4 _ cs27) ];
               apply AG4; notin_lit|]). destruct Hx. }
    apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | exact Z8 | exact Z9 | exact Z18 | exact Z19 | apply REST; unfold sd_rest; in_lit ].
  - intros q [[->|[->|(j & Hj & ->)]]| ->].
    + exact Ls5.
    + rewrite (LEQ5 (Z_to_bv 64 (v_data v)) ltac:(apply zbv_ne; lia)). rewrite (LEQ4 _ (not_eq_sym NEnd)). exact Ld3.
    + destruct (ROWS j Hj) as ((G1 & G2' & _) & _ & _ & G3 & _). rewrite (LEQ5 (Z_to_bv 64 (v_rows v j)) ltac:(apply zbv_ne; lia)).
      rewrite (LEQ4 _ (not_eq_sym (NEnr j Hj))). exact (DONE3 j Hj).
    + rewrite (LEQ5 _ NEns). exact Ln4.
  - exact OTHER.
  - exact SUB5.
  - eapply POSTD_trans; [apply (POSTD_of_POSTM C A5 A5 s pp m m5 PM5'); apply sub_live_refl|].
    subst M6. apply POSTD_slotw; [rewrite length_N_to_le_bytes; reflexivity | lia | lia].
  - subst M6. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - apply (roomtr_trans A (m_vmmaps md) A4 vm4 A5 vm5 0 0 0 0); [| exact (roomtr_wv _ _ _ _ _ _ _ HRT5) | lia | lia].
    apply (roomtr_trans A (m_vmmaps md) A3 vm3 A4 vm4 0 0 0 0 HRT3 (roomtr_wv _ _ _ _ _ _ _ HRT4)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsA.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma sad_A : forall regs m (s pp sela n : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> (pp + 8 <= s - 48 \/ s <= pp)%Z ->
    (1 <= sela)%Z -> (sela + 16 <= s - 48)%Z -> (1 <= n < 2 ^ 31)%Z -> (pp mod 8 = 0)%Z -> (sela mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 sela) -> rdn SEGS m (Z_to_bv 64 sela) 4 = Some (Z_to_le_bytes 4 n) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x26eac : word) m rom) (mkst regs' (0x26ef4 : word) (SDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 sela
      /\ getr regs' 18 = Z_to_bv 64 (8 * 0) /\ getr regs' 19 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp sela n ret Hs Hs64 Hpp Hpp64 DJ Hsel Hsel2 Hn ALpp ALs SOK Rpp Rn H2 H1 H10.
    eexists. split.
    - zv F_26db0 D_26db0 (Z_to_bv 64 (s - 48)).
      stepST F_26db4 D_26db4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_26db8 D_26db8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_26dbc D_26dbc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_26dc0 D_26dc0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_26dc4 D_26dc4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_26dc8 D_26dc8 ltac:(condZ).
      sn F_26dcc D_26dcc.
      zand F_26dd0 D_26dd0 andi_7 ALpp. stepb_ft F_26dd4 D_26dd4 ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_26dd8 D_26dd8 (Z_to_le_bytes 8 sela) (Z_to_bv 64 sela) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply lez8; lia).
      stepb_ft F_26ddc D_26ddc ltac:(condZ).
      zand F_26de0 D_26de0 andi_7 ALs. stepb_ft F_26de4 D_26de4 ltac:(condZ).           (* [comment removed for export] *)
      stepLD F_26de8 D_26de8 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepb_ft F_26dec D_26dec ltac:(condZ).
      sn F_26df0 D_26df0. sn F_26df4 D_26df4.
      unfold SDF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sad_H : forall regs m (sela arr i : Z),
    (1 <= sela)%Z -> (sela + 16 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * i + 8 < 2 ^ 64)%Z -> (0 <= i < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (sela + 8)) 8 = Some (Z_to_le_bytes 8 arr) ->
    getr regs 9 = Z_to_bv 64 sela -> getr regs 18 = Z_to_bv 64 (8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x26ef4 : word) m rom) (mkst regs' (0x26f58 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x26f14 /\ getr regs' 10 = Z_to_bv 64 (arr + 8 * i)
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m sela arr i Hs Hs64 Ha Ha64 Hi Ra H9 H18.
    eexists. split.
    - stepLD F_26df8 D_26df8 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Ra) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      zv F_26dfc D_26dfc (Z_to_bv 64 (arr + 8 * i)).                                  (* [comment removed for export] *)
      stepb_ft F_26e00 D_26e00 ltac:(condZ).                                          (* [comment removed for export] *)
      snez1 F_26e04 D_26e04.                                                          (* [comment removed for export] *)
      seqz0 F_26e08 D_26e08.                                                          (* [comment removed for export] *)
      zlit F_26e0c D_26e0c (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_26e10 D_26e10 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_26e14 D_26e14.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sad_N_cont : forall regs m (sela n i : Z),
    (1 <= sela)%Z -> (sela + 16 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 sela) 4 = Some (Z_to_le_bytes 4 n) ->
    getr regs 9 = Z_to_bv 64 sela -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x26f14 : word) m rom) (mkst regs' (0x26ef4 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun r => In r [10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m sela n i Hs Hs64 Hi Hi1 Hn Rn H9 H18 H19.
    eexists. split.
    - stepLD F_26e18 D_26e18 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      zv F_26e1c D_26e1c (Z_to_bv 64 (i + 1)).
      zv F_26e20 D_26e20 (Z_to_bv 64 (8 * (i + 1))).
      stepb_tk F_26e24 D_26e24 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma sad_N_last : forall regs m (sela n i : Z),
    (1 <= sela)%Z -> (sela + 16 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 sela) 4 = Some (Z_to_le_bytes 4 n) ->
    getr regs 9 = Z_to_bv 64 sela -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x26f14 : word) m rom) (mkst regs' (0x26f24 : word) m rom)
      /\ regs_agree (fun r => In r [10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m sela n i Hs Hs64 Hi Hi1 Hn Rn H9 H18 H19.
    eexists. split.
    - stepLD F_26e18 D_26e18 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      zv F_26e1c D_26e1c (Z_to_bv 64 (i + 1)).
      zv F_26e20 D_26e20 (Z_to_bv 64 (8 * (i + 1))).
      stepb_ft F_26e24 D_26e24 ltac:(condZ).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sad_D : forall regs m (sela arr : Z),
    (1 <= sela)%Z -> (sela + 16 < 2 ^ 64)%Z -> (0 <= arr < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (sela + 8)) 8 = Some (Z_to_le_bytes 8 arr) -> getr regs 9 = Z_to_bv 64 sela ->
    exists regs',
      msteps SEGS (mkst regs (0x26f24 : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x26f2c /\ getr regs' 10 = Z_to_bv 64 arr
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m sela arr Hs Hs64 Ha Ra H9. eexists. split.
    - stepLD F_26e28 D_26e28 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Ra) ltac:(apply lez8; lia).
      sn F_26e2c D_26e2c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sad_E : forall regs m (sela : Z), getr regs 9 = Z_to_bv 64 sela ->
    exists regs',
      msteps SEGS (mkst regs (0x26f2c : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x26f34 /\ getr regs' 10 = Z_to_bv 64 sela
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m sela H9. eexists. split.
    - sn F_26e30 D_26e30. sn F_26e34 D_26e34. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sad_F : forall regs m (s pp : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> (pp + 8 <= s - 48 \/ s <= pp)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> sdcells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x26f34 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v s2v s3v Hs Hs64 Hpp Hpp64 DJ Hret SOK (C1 & C2 & C3 & C4 & C5) H2 H8.
    eexists. split.
    - stepST F_26e38 D_26e38 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      stepLD8 F_26e3c D_26e3c ret. stepLD8 F_26e40 D_26e40 s0v. stepLD8 F_26e44 D_26e44 s1v. stepLD8 F_26e48 D_26e48 s2v. stepLD8 F_26e4c D_26e4c s3v.
      zv F_26e50 D_26e50 (Z_to_bv 64 s).
      stepret F_26e54 D_26e54 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsA.

(* [comment removed for export] *)
Lemma sdcells_POSTD : forall C A M M' s pp ret s0v s1v s2v s3v, Cok C -> POSTD C A (s - 48) pp M M' ->
  (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z -> (pp + 8 <= s - 48)%Z ->
  sdcells M s ret s0v s1v s2v s3v -> sdcells M' s ret s0v s1v s2v s3v.
Proof.
  intros C A M M' s pp ret s0v s1v s2v s3v CK PD Hlo Hhi Hpp (C1 & C2 & C3 & C4 & C5).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold sdcells.
  assert (E : forall a, (s - 48 <= a)%Z -> (a + 8 <= s)%Z -> rdn SEGS M' (Z_to_bv 64 a) 8 = rdn SEGS M (Z_to_bv 64 a) 8).
  { intros a Ha1 Ha2. rewrite <- p16_segs. apply (POSTD_rdn_above C A (s - 48) pp M M' a 8 CK PD); lia. }
  rewrite !E by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma sad_round : forall C A m md regs (s pp sela arr : Z) (sels : Z -> Z) (vs : Z -> selv) (S : TSet) A1 M1 vm1 r (i : Z),
  Cok C -> W C A m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELADESTROY_STACK <= s)%Z -> (s <= c_top C)%Z ->
  sela_hm (alloc_top (c_vm C)) A m sela arr sels vs -> sela_off (c_A0 C) sela arr 10 sels vs -> (0 <= i < 10)%Z ->
  W C A1 M1 (with_vmmaps vm1 md) -> roomtr A (m_vmmaps md) A1 vm1 0 0 ->
  sela_dst C A m s arr sels vs i A1 M1 -> sdcells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pp -> getr r 9 = Z_to_bv 64 sela -> getr r 18 = Z_to_bv 64 (8 * i) -> getr r 19 = Z_to_bv 64 i ->
  getr r 4 = Z_to_bv 64 0x45480 -> (forall x, In x sd_rest -> getr r x = getr regs x) ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> roomtr A (m_vmmaps md) A' vm' 0 0 ->
     sela_dst C A m s arr sels vs (i + 1) A' m' -> sdcells m' s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
     getr r' 2 = Z_to_bv 64 (s - 48) -> getr r' 8 = Z_to_bv 64 pp -> getr r' 9 = Z_to_bv 64 sela -> getr r' 18 = Z_to_bv 64 (8 * i) -> getr r' 19 = Z_to_bv 64 i ->
     getr r' 4 = Z_to_bv 64 0x45480 -> (forall x, In x sd_rest -> getr r' x = getr regs x) ->
     realizes SEGS (mkCfg (mkst r' (0x26f14 : word) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0x26ef4 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A m md regs s pp sela arr sels vs S A1 M1 vm1 r i CK HW0 Hs16 Hlo Hhi SH SO0 Hi HW HRT SD CE R2 R8 R9 R18 R19 R4 RR HK.
  pose proof SH as [SA SHAPES].
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold SELADESTROY_STACK, ALLOC_STACK in Hlo. unfold sd_rest in RR.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof SA as (_ & (Gs & TOPs & _) & _ & _ & (Ga & TOPa & ALa) & _ & NEa & CELLS & _).
  assert (ALc : ((arr + 8 * i) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact (bok_mod8 _ _ _ (conj Ga (conj TOPa ALa)))).
  pose proof (sela_dst_hdr C A m md s _ sela arr 10 sels vs hm_name i A1 M1 CK HW0 AT SA ltac:(lia) SD) as Rs1.
  destruct (sela_dst_live C A m s _ sela arr 10 sels vs hm_name i A1 M1 AT SA ltac:(lia) SD) as (Ls1 & La1 & _).
  destruct (sela_dst_cell C A m md s _ sela arr 10 sels vs hm_name i A1 M1 i CK HW0 AT SA ltac:(lia) SD ltac:(lia)) as (Bi1 & SAi & NAi).
  destruct (CELLS i Hi) as (_ & _ & _ & NHi & NBNi).
  pose proof (REC_rd' SEGS M1 sela _ 2 8 (Z_to_bv 64 (sela + 8)) arr Rs1 ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rarr.
  pose proof (bytes_at_rdn SEGS M1 (arr + 8 * i) (Z_to_le_bytes 8 (sels i)) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) Bi1) as Rci.
  rewrite length_Z_to_le_bytes in Rci.
  destruct (sad_H al_rom r M1 sela arr i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rarr R9 R18) as (r1 & RUN1 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (SL : slotok C A1 (s - 48) (arr + 8 * i) (Some (Z_to_bv 64 arr, 400%Z))).
  { cbn. rewrite u_Z2bv by lia. split; [exact La1|]. split; [exact (SO0 arr (or_intror (or_introl eq_refl)))|]. lia. }
  apply (selDestroy_W C A1 M1 _ r1 (s - 48) (arr + 8 * i) (sels i) (vs i) (hm_name i) (Some (Z_to_bv 64 arr, 400%Z)) (Z_to_bv 64 0x26f14) S CK HW
           ltac:(rewrite (AG1 2) by notin_lit; exact R2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold ALLOC_STACK; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(rewrite (AG1 4) by notin_lit; exact R4) Q10 SL ALc Rci SAi NAi NBNi).
  { intros p Hp. apply SO0. right; right. exists i. split; [exact Hi | left; exact Hp]. }
  { apply SO0. right; right. exists i. split; [exact Hi | right; reflexivity]. }
  { intros p0 k0 E q Hq. injection E as <- <-.
    destruct (sela_blk_w _ A m sela arr 10 sels vs hm_name i q AT SA Hi Hq) as (_ & _ & X & _). intros E. apply X. symmetry. exact E. }
  intros A2 m2 vm2 r2 HW2 CS2 DEAD2 OTH2 SUB2 PD2 RD2 HRT2. rewrite ?with_vmmaps_twice in HW2 |- *.
  replace (Z_to_bv 64 0x26f14) with (0x26f14 : word) by (apply bv_eq; reflexivity).
  apply (HK A2 m2 vm2 r2 HW2).
  - apply (roomtr_trans A (m_vmmaps md) A1 vm1 A2 vm2 0 0 0 0 HRT (roomtr_wv _ _ _ _ _ _ _ HRT2)); lia.
  - exact (sela_dst_step C A m s (s - 48) _ sela arr 10 sels vs hm_name i A1 M1 A2 m2 AT SA Hi ltac:(lia) SD DEAD2 OTH2 SUB2 PD2).
  - exact (sdcells_POSTD C A2 M1 m2 s (arr + 8 * i) _ _ _ _ _ CK PD2 ltac:(lia) ltac:(lia) ltac:(lia) CE).
  - rewrite (CS2 2%bv cs2). rewrite (AG1 2) by notin_lit. exact R2.
  - rewrite (CS2 8%bv cs8). rewrite (AG1 8) by notin_lit. exact R8.
  - rewrite (CS2 9%bv cs9). rewrite (AG1 9) by notin_lit. exact R9.
  - rewrite (CS2 18%bv cs18). rewrite (AG1 18) by notin_lit. exact R18.
  - rewrite (CS2 19%bv cs19). rewrite (AG1 19) by notin_lit. exact R19.
  - rewrite (CS2 4%bv cs4). rewrite (AG1 4) by notin_lit. exact R4.
  - intros x Hx. rewrite <- (RR x Hx). unfold sd_rest in Hx. cbn [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [first [ rewrite (CS2 _ cs3) | rewrite (CS2 _ cs4) | rewrite (CS2 _ cs20) | rewrite (CS2 _ cs21) | rewrite (CS2 _ cs22)
                                           | rewrite (CS2 _ cs23) | rewrite (CS2 _ cs24) | rewrite (CS2 _ cs25) | rewrite (CS2 _ cs26) | rewrite (CS2 _ cs27) ];
                                     apply AG1; notin_lit|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma sad_loop : forall (k : nat) C A m md regs (s pp sela arr : Z) (sels : Z -> Z) (vs : Z -> selv) (S : TSet) A1 M1 vm1 r (i : Z),
  Cok C -> W C A m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELADESTROY_STACK <= s)%Z -> (s <= c_top C)%Z ->
  sela_hm (alloc_top (c_vm C)) A m sela arr sels vs -> sela_off (c_A0 C) sela arr 10 sels vs ->
  (Z.of_nat k = 10 - 1 - i)%Z -> (0 <= i < 10)%Z ->
  W C A1 M1 (with_vmmaps vm1 md) -> roomtr A (m_vmmaps md) A1 vm1 0 0 ->
  sela_dst C A m s arr sels vs i A1 M1 -> sdcells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pp -> getr r 9 = Z_to_bv 64 sela -> getr r 18 = Z_to_bv 64 (8 * i) -> getr r 19 = Z_to_bv 64 i ->
  getr r 4 = Z_to_bv 64 0x45480 -> (forall x, In x sd_rest -> getr r x = getr regs x) ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> roomtr A (m_vmmaps md) A' vm' 0 0 ->
     sela_dst C A m s arr sels vs 10 A' m' -> sdcells m' s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
     getr r' 2 = Z_to_bv 64 (s - 48) -> getr r' 8 = Z_to_bv 64 pp -> getr r' 9 = Z_to_bv 64 sela -> getr r' 4 = Z_to_bv 64 0x45480 ->
     (forall x, In x sd_rest -> getr r' x = getr regs x) ->
     realizes SEGS (mkCfg (mkst r' (0x26f24 : word) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0x26ef4 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros C A m md regs s pp sela arr sels vs S A1 M1 vm1 r i CK HW0 Hs16 Hlo Hhi SH SO0 Hk Hi HW HRT SD CE R2 R8 R9 R18 R19 R4 RR HK;
    apply (sad_round C A m md regs s pp sela arr sels vs S A1 M1 vm1 r i CK HW0 Hs16 Hlo Hhi SH SO0 Hi HW HRT SD CE R2 R8 R9 R18 R19 R4 RR);
    intros A2 m2 vm2 r2 HW2 HRT2 SD2 CE2 E2 E8 E9 E18 E19 E4 RR2;
    pose proof SH as [SA SHAPES];
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LLU16] in *;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    pose proof SA as (_ & (Gs & TOPs & _) & _);
    pose proof (sela_dst_hdr C A m md s _ sela arr 10 sels vs hm_name (i + 1) A2 m2 CK HW0 AT SA ltac:(lia) SD2) as Rs2;
    pose proof (REC_rd' SEGS m2 sela _ 0 4 (Z_to_bv 64 sela) 10 Rs2 ltac:(cbn; lia) eq_refl ltac:(cbn [fld_off sela_flds Z.of_nat]; f_equal; lia) eq_refl) as Rn2.
  - (* [comment removed for export] *)
    destruct (sad_N_last al_rom r2 m2 sela 10 i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rn2 E9 E18 E19) as (r3 & RUN3 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    replace (i + 1)%Z with 10%Z in SD2 by lia.
    apply (HK A2 m2 vm2 r3 HW2 HRT2 SD2 CE2).
    + rewrite (AG3 2) by notin_lit. exact E2.
    + rewrite (AG3 8) by notin_lit. exact E8.
    + rewrite (AG3 9) by notin_lit. exact E9.
    + rewrite (AG3 4) by notin_lit. exact E4.
    + intros x Hx. rewrite (AG3 x); [exact (RR2 x Hx)|]. unfold sd_rest in Hx. cbn [In] in *. intros HH.
      repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx.
  - (* [comment removed for export] *)
    destruct (sad_N_cont al_rom r2 m2 sela 10 i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rn2 E9 E18 E19) as (r3 & RUN3 & P18 & P19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply (IH C A m md regs s pp sela arr sels vs S A2 m2 vm2 r3 (i + 1)%Z CK HW0 Hs16 Hlo Hhi SH SO0 ltac:(lia) ltac:(lia) HW2 HRT2 SD2 CE2); try exact HK; try exact P18; try exact P19.
    + rewrite (AG3 2) by notin_lit. exact E2.
    + rewrite (AG3 8) by notin_lit. exact E8.
    + rewrite (AG3 9) by notin_lit. exact E9.
    + rewrite (AG3 4) by notin_lit. exact E4.
    + intros x Hx. rewrite (AG3 x); [exact (RR2 x Hx)|]. unfold sd_rest in Hx. cbn [In] in *. intros HH.
      repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx.
Qed.

(* [comment removed for export] *)
Theorem selaDestroy_W : selaDestroy_contract.
Proof.
  intros C A m md regs s pp sela arr sels vs ret S CK HW H2 Hs16 Hlo Hpp Hpphi ALpp H1 Hret H4 H10 Rpp SH SO0 HK.
  unfold PC_selaDestroy. replace (Z_to_bv 64 0x26eac) with (0x26eac : word) by (apply bv_eq; reflexivity).
  pose proof SH as [SA SHAPES].
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 48 + 48 + 1024 <= s)%Z) by (unfold SELADESTROY_STACK, ALLOC_STACK in Hlo; lia).
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof SA as (_ & (Gs & TOPs & ALs) & Ls & Rs & (Ga & TOPa & _) & La & NEa & _).
  pose proof (REC_rd' SEGS m sela _ 0 4 (Z_to_bv 64 sela) 10 Rs ltac:(cbn; lia) eq_refl ltac:(cbn [fld_off sela_flds Z.of_nat]; f_equal; lia) eq_refl) as Rn.
  destruct (sad_A al_rom regs m s pp sela 10 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp (bok_mod8 _ _ _ (conj Gs (conj TOPs ALs)))
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp Rn H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := SDF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold SDF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (sdcells_SDF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  apply (sad_loop 9 C A m md regs s pp sela arr sels vs S A M1 (m_vmmaps md) r1 0 CK HW Hs16 Hlo ltac:(lia) SH SO0 ltac:(lia) ltac:(lia) HW1
           ltac:(apply roomtr_refl; lia) (sela_dst_0 C A m s arr sels vs M1 PM1) CE1 Q2 Q8 Q9 Q18 Q19
           ltac:(rewrite (AG1 4) by notin_lit; exact H4)
           ltac:(intros x Hx; apply AG1; unfold sd_rest in Hx; cbn [In] in *; intros HH;
                 repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx)).
  intros A3 m3 vm3 r3 HW3 HRT3 SD3 CE3 E2 E8 E9 E4 RR3.
  (* [comment removed for export] *)
  pose proof (sela_dst_hdr C A m md s _ sela arr 10 sels vs hm_name 10 A3 m3 CK HW AT SA ltac:(lia) SD3) as Rs3.
  destruct (sela_dst_live C A m s _ sela arr 10 sels vs hm_name 10 A3 m3 AT SA ltac:(lia) SD3) as (Ls3 & La3 & _).
  pose proof (REC_rd' SEGS m3 sela _ 2 8 (Z_to_bv 64 (sela + 8)) arr Rs3 ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rarr3.
  destruct (sad_D al_rom r3 m3 sela arr ltac:(lia) ltac:(lia) ltac:(lia) Rarr3 E9) as (r4 & RUN4 & P1 & P10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity).
  apply (W_free16 C A3 m3 _ r4 (Z_to_bv 64 arr) (Z_to_bv 64 0x26f2c) 400 (s - 48) S CK HW3 P10 La3 (SO0 arr (or_intror (or_introl eq_refl))) P1
           ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG4 4) by notin_lit; exact E4)
           ltac:(rewrite (AG4 2) by notin_lit; exact E2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A4 m4 vm4 r5 HW4 CS4 La4 LEQ4 PM4 HRT4. rewrite ?with_vmmaps_twice in HW4 |- *.
  replace (Z_to_bv 64 0x26f2c) with (0x26f2c : word) by (apply bv_eq; reflexivity).
  (* [comment removed for export] *)
  assert (F9 : getr r5 9 = Z_to_bv 64 sela) by (rewrite (CS4 9%bv cs9); rewrite (AG4 9) by notin_lit; exact E9).
  assert (F2 : getr r5 2 = Z_to_bv 64 (s - 48)) by (rewrite (CS4 2%bv cs2); rewrite (AG4 2) by notin_lit; exact E2).
  assert (F4 : getr r5 4 = Z_to_bv 64 0x45480) by (rewrite (CS4 4%bv cs4); rewrite (AG4 4) by notin_lit; exact E4).
  destruct (sad_E al_rom r5 m4 sela F9) as (r6 & RUN6 & V1 & V10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
  replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity).
  assert (NEsa : Z_to_bv 64 sela <> Z_to_bv 64 arr) by (apply zbv_ne; [lia | lia |]; intros E; apply NEa; symmetry; exact E).
  assert (Ls4 : live A4 (Z_to_bv 64 sela) = Some 16%Z) by (rewrite (LEQ4 _ NEsa); exact Ls3).
  apply (W_free16 C A4 m4 _ r6 (Z_to_bv 64 sela) (Z_to_bv 64 0x26f34) 16 (s - 48) S CK HW4 V10 Ls4 (SO0 sela (or_introl eq_refl)) V1
           ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG6 4) by notin_lit; exact F4)
           ltac:(rewrite (AG6 2) by notin_lit; exact F2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A5 m5 vm5 r7 HW5 CS5 Ls5 LEQ5 PM5 HRT5. rewrite ?with_vmmaps_twice in HW5 |- *.
  replace (Z_to_bv 64 0x26f34) with (0x26f34 : word) by (apply bv_eq; reflexivity).
  (* [comment removed for export] *)
  destruct (sela_dst_off C A m s _ sela arr 10 sels vs hm_name A3 m3 A4 A5 AT SA SD3 La4 LEQ4 Ls5 LEQ5) as (OFF5 & ONLY5 & SUB53).
  assert (SUB54 : sub_live A5 A4)
    by (intros q kq Lq; destruct (bv_eq_dec _ q (Z_to_bv 64 sela)) as [->|NE]; [rewrite Ls5 in Lq; discriminate | rewrite <- (LEQ5 q NE); exact Lq]).
  assert (PM35 : POSTM C A5 s m3 m5).
  { eapply POSTM_trans; [apply (POSTM_sub C A5 A4 _ _ _ SUB54); eapply POSTM_mono; [|exact PM4]; lia | eapply POSTM_mono; [|exact PM5]; lia]. }
  pose proof (sela_dst_POSTM C A m s _ sela arr 10 sels vs hm_name A3 m3 _ A5 m5 CK HW3 AT SA SD3 SUB53 (OFF5 arr (or_intror (or_introl eq_refl))) PM35) as PM5'.
  pose proof (sdcells_FRM C m4 m5 s _ _ _ _ _ CK (proj1 PM5) ltac:(lia) ltac:(lia)
                (sdcells_FRM C m3 m4 s _ _ _ _ _ CK (proj1 PM4) ltac:(lia) ltac:(lia) CE3)) as CE5.
  assert (G2 : getr r7 2 = Z_to_bv 64 (s - 48)) by (rewrite (CS5 2%bv cs2); rewrite (AG6 2) by notin_lit; exact F2).
  assert (G8 : getr r7 8 = Z_to_bv 64 pp)
    by (rewrite (CS5 8%bv cs8); rewrite (AG6 8) by notin_lit; rewrite (CS4 8%bv cs8); rewrite (AG4 8) by notin_lit; exact E8).
  destruct (sad_F al_rom r7 m5 s pp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(rewrite H1; exact Hret) (W_sok_win C A5 m5 _ pp 8 CK HW5 ltac:(lia) ltac:(cbn; lia)) CE5 G2 G8) as (r8 & RUN8 & Z2 & Z1 & Z8 & Z9 & Z18 & Z19 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN8 |].
  set (M6 := wbytes m5 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP6 : W C A5 M6 (with_vmmaps vm5 md) /\ POSTM C A5 (pp + 8) m5 M6) by (subst M6; wp_win CK).
  destruct WP6 as [HW6 PM6].
  rewrite H1. apply (HK A5 M6 vm5 r8 HW6).
  - assert (REST : forall x, In x sd_rest -> getr r8 x = getr regs x).
    { intros x Hx. rewrite <- (RR3 x Hx). unfold sd_rest in Hx. cbn [In] in Hx.
      repeat (destruct Hx as [<-|Hx];
              [rewrite (AG8 _) by notin_lit;
               first [ rewrite (CS5 _ cs3) | rewrite (CS5 _ cs4) | rewrite (CS5 _ cs20) | rewrite (CS5 _ cs21) | rewrite (CS5 _ cs22)
                     | rewrite (CS5 _ cs23) | rewrite (CS5 _ cs24) | rewrite (CS5 _ cs25) | rewrite (CS5 _ cs26) | rewrite (CS5 _ cs27) ];
               rewrite (AG6 _) by notin_lit;
               first [ rewrite (CS4 _ cs3) | rewrite (CS4 _ cs4) | rewrite (CS4 _ cs20) | rewrite (CS4 _ cs21) | rewrite (CS4 _ cs22)
                     | rewrite (CS4 _ cs23) | rewrite (CS4 _ cs24) | rewrite (CS4 _ cs25) | rewrite (CS4 _ cs26) | rewrite (CS4 _ cs27) ];
               apply AG4; notin_lit|]). destruct Hx. }
    apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | exact Z8 | exact Z9 | exact Z18 | exact Z19 | apply REST; unfold sd_rest; in_lit ].
  - exact OFF5.
  - exact ONLY5.
  - eapply POSTM_trans; [eapply POSTM_mono; [|exact PM5']; lia | exact PM6].
  - subst M6. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros a Ha. subst M6. rewrite wbytes_outside by (rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
    destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga' & N2 & N3 & N4 & _).
    apply (proj1 PM5'); try assumption; [intros [_ X]; lia | unfold scratch; lia].
  - apply (roomtr_trans A (m_vmmaps md) A4 vm4 A5 vm5 0 0 0 0); [| exact (roomtr_wv _ _ _ _ _ _ _ HRT5) | lia | lia].
    apply (roomtr_trans A (m_vmmaps md) A3 vm3 A4 vm4 0 0 0 0 HRT3 (roomtr_wv _ _ _ _ _ _ _ HRT4)); lia.
Qed.

End SelDestroy.
