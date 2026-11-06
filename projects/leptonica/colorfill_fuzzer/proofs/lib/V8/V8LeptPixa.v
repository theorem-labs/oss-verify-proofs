(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptArith2 LibAtomic LeptRecs LeptSlots.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8LeptStderr V8LeptBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8CL7a.
Import V8CL7a.V8LeptErr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8LeptBoxa V8_code_13734_14000 V8_code_14000_15000 V8_code_17000_18000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomCF.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Local Ltac forall_cells := repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

(* [comment removed for export] *)
Definition pixa_flds (n na rc parr ba : Z) : list fld := [(4%nat, n); (4%nat, na); (4%nat, rc); (4%nat, 0%Z); (8%nat, parr); (8%nat, ba)].

(* [comment removed for export] *)
Lemma pclamp0 : (zx (sw32 (0 + 18446744073709451615)) <? zx 18446744073709451616)%Z = true.
Proof. vm_compute. reflexivity. Qed.

Section Pixa.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma PIXA_rd_n : forall m px n na rc parr ba, RECat m px (pixa_flds n na rc parr ba) -> rdn SEGS m (Z_to_bv 64 px) 4 = Some (Z_to_le_bytes 4 n).
Proof. intros m px n na rc parr ba R. eapply (REC_rd' SEGS _ _ (pixa_flds n na rc parr ba) 0 4); [exact R | cbn; lia | reflexivity | cbn [fld_off pixa_flds Z.of_nat]; f_equal; lia | reflexivity]. Qed.
Lemma PIXA_rd_rc : forall m px n na rc parr ba, RECat m px (pixa_flds n na rc parr ba) -> rdn SEGS m (Z_to_bv 64 (px + 8)) 4 = Some (Z_to_le_bytes 4 rc).
Proof. intros m px n na rc parr ba R. eapply (REC_rd' SEGS _ _ (pixa_flds n na rc parr ba) 2 4); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma PIXA_rd_parr : forall m px n na rc parr ba, RECat m px (pixa_flds n na rc parr ba) -> rdn SEGS m (Z_to_bv 64 (px + 16)) 8 = Some (Z_to_le_bytes 8 parr).
Proof. intros m px n na rc parr ba R. eapply (REC_rd' SEGS _ _ (pixa_flds n na rc parr ba) 4 8); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma PIXA_rd_ba : forall m px n na rc parr ba, RECat m px (pixa_flds n na rc parr ba) -> rdn SEGS m (Z_to_bv 64 (px + 24)) 8 = Some (Z_to_le_bytes 8 ba).
Proof. intros m px n na rc parr ba R. eapply (REC_rd' SEGS _ _ (pixa_flds n na rc parr ba) 5 8); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma PIXA_wf : forall m px n na rc parr ba, RECat m px (pixa_flds n na rc parr ba) ->
  (0 <= n < 2 ^ 32)%Z /\ (0 <= na < 2 ^ 32)%Z /\ (0 <= parr < 2 ^ 64)%Z /\ (0 <= ba < 2 ^ 64)%Z /\ (0 <= px)%Z /\ (px + 32 < 2 ^ 64)%Z.
Proof. intros m px n na rc parr ba (H0 & H1 & WF & _). cbn in H1, WF. lia. Qed.

Section Segs.
Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).

  (* [comment removed for export] *)
  Definition pcF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).
  Definition pdF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).
  Definition pc_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9)]%Z.
  Definition pd_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9); (s - 32, getr R 18); (s - 40, getr R 19)]%Z.
  Lemma pcF_cells : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> pc_cells (pcF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold pc_cells, pcF. cbn [cellsZ]. repeat split; rdn_solve. Qed.
  Lemma pdF_cells : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z -> pd_cells (pdF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold pd_cells, pdF. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  (* [comment removed for export] *)
  Lemma pc_A : forall regs m (s : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x145d8 : word) m rom) (mkst regs' (0x17b1c : word) (pcF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x145f8
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 32 /\ getr regs' 9 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10.
    eexists. split.
    - zv F_144d4 D_144d4 (Z_to_bv 64 (s - 32)).
      stepST F_144d8 D_144d8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_144dc D_144dc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_144e0 D_144e0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_144e4 D_144e4. sn F_144e8 D_144e8. sn F_144ec D_144ec. sn F_144f0 D_144f0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pc_B : forall regs m (s px : Z),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= px)%Z -> (px + 32 < 2 ^ 64)%Z -> (px mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 px) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 px -> getr regs 9 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x145f8 : word) m rom)
                  (mkst regs' (0x17b1c : word)
                     (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 px)))
                             (Z_to_bv 64 px) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (px + 4)) (word_to_le_bytes 4 (Z_to_bv 64 20)))
                             (Z_to_bv 64 (px + 8)) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x14648
      /\ getr regs' 10 = Z_to_bv 64 20 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 9 = Z_to_bv 64 20 /\ getr regs' 8 = Z_to_bv 64 px
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s px Hs Hs64 Hpx Hpx64 ALpx SOK SOKp H2 H10 H9.
    eexists. split.
    - stepST F_144f4 D_144f4 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 px) ltac:(sok_in SOK).
      stepb_ft F_144f8 D_144f8 ltac:(condZ).
      sn F_144fc D_144fc.
      zand F_14500 D_14500 andi_7 ALpx. stepb_ft F_14504 D_14504 ltac:(condZ).
      sn F_14508 D_14508. sn F_1450c D_1450c.
      sn F_14510 D_14510.                                       (* [comment removed for export] *)
      sn F_14514 D_14514.
      stepb_ft F_14518 D_14518 ltac:(first [condZ | vm_compute; reflexivity]).
      sn F_1451c D_1451c.
      stepST F_14520 D_14520 (Z_to_bv 64 px) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      stepST F_14524 D_14524 (Z_to_bv 64 (px + 4)) (Z_to_bv 64 20) ltac:(sok_in SOKp).
      stepfence F_14528 D_14528.
      sn F_1452c D_1452c.
      stepST F_14530 D_14530 (Z_to_bv 64 (px + 8)) (Z_to_bv 64 1) ltac:(sok_in SOKp).
      stepfence F_14534 D_14534.
      sn F_14538 D_14538. sn F_1453c D_1453c. sn F_14540 D_14540.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pc_C : forall regs m (px parr : Z),
    (1 <= px)%Z -> (px + 32 < 2 ^ 64)%Z -> (0 <= parr < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 px) 32 = true ->
    getr regs 10 = Z_to_bv 64 parr -> getr regs 8 = Z_to_bv 64 px -> getr regs 9 = Z_to_bv 64 20 ->
    exists regs',
      msteps SEGS (mkst regs (0x14648 : word) m rom)
                  (mkst regs' (0x1494c : word) (wbytes m (Z_to_bv 64 (px + 16)) (word_to_le_bytes 8 (Z_to_bv 64 parr))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x14654 /\ getr regs' 10 = Z_to_bv 64 20 /\ getr regs' 8 = Z_to_bv 64 px /\ getr regs' 9 = Z_to_bv 64 20
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m px parr Hpx Hpx64 Hparr SOKp H10 H8 H9.
    eexists. split.
    - stepST F_14544 D_14544 (Z_to_bv 64 (px + 16)) (Z_to_bv 64 parr) ltac:(sok_in SOKp).
      sn F_14548 D_14548. sn F_1454c D_1454c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pc_D : forall regs m (s px parr ba : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= px)%Z -> (px + 32 < 2 ^ 64)%Z -> (1 <= parr < 2 ^ 64)%Z -> (1 <= ba < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 px) 32 = true -> (px + 32 <= s - 32)%Z ->
    rdn SEGS m (Z_to_bv 64 (px + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 ba -> getr regs 8 = Z_to_bv 64 px ->
    exists regs',
      msteps SEGS (mkst regs (0x14654 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (px + 24)) (word_to_le_bytes 8 (Z_to_bv 64 ba))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 px
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s px parr ba ret s0v s1v Hs Hs64 Hpx Hpx64 Hparr Hba Hret SOKp DJ Rparr R8 R16 R24 H2 H10 H8.
    eexists. split.
    - stepLD F_14550 D_14550 (Z_to_le_bytes 8 parr) (Z_to_bv 64 parr) ltac:(addr_norm; exact Rparr) ltac:(apply lez8; lia).
      stepST F_14554 D_14554 (Z_to_bv 64 (px + 24)) (Z_to_bv 64 ba) ltac:(sok_in SOKp).
      stepb_ft F_14558 D_14558 ltac:(condZ).
      stepb_tk F_1455c D_1455c ltac:(condZ).
      sn F_145a0 D_145a0.
      stepLD8 F_145a4 D_145a4 ret. stepLD8 F_145a8 D_145a8 s0v. stepLD8 F_145ac D_145ac s1v.
      zv F_145b0 D_145b0 (Z_to_bv 64 s).
      stepret F_145b4 D_145b4 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_A : forall regs m (s pp v : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 v) -> (pp + 8 <= s - 48 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x146c0 : word) m rom) (mkst regs' (0x146e8 : word) (pdF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 v /\ getr regs' 10 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [2; 8; 11]%list) regs regs'.
  Proof.
    intros regs m s pp v ret Hs Hs64 Hpp Hpp64 Hv ALpp SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_145bc D_145bc (Z_to_bv 64 (s - 48)).
      stepST F_145c0 D_145c0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_145c4 D_145c4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_145c8 D_145c8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_145cc D_145cc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_145d0 D_145d0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_145d4 D_145d4 ltac:(condZ).
      zand F_145d8 D_145d8 andi_7 ALpp. stepb_ft F_145dc D_145dc ltac:(condZ).
      stepLD F_145e0 D_145e0 (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_epi : forall regs m (s : Z) (ret : word) (R : bvmap 5 word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (0x147b0 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9 /\ getr regs' 18 = getr R 18 /\ getr regs' 19 = getr R 19
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret R Hs Hs64 Hret CE H2. destruct CE as (C8 & C16 & C24 & C32 & C40 & _).
    eexists. split.
    - stepLD8 F_146ac D_146ac ret. stepLD8 F_146b0 D_146b0 (getr R 8). stepLD8 F_146b4 D_146b4 (getr R 9).
      stepLD8 F_146b8 D_146b8 (getr R 18). stepLD8 F_146bc D_146bc (getr R 19).
      zv F_146c0 D_146c0 (Z_to_bv 64 s).
      stepret F_146c4 D_146c4 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pd_Z : forall regs m,
    getr regs 8 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x146e8 : word) m rom) (mkst regs (0x147b0 : word) m rom).
  Proof. intros regs m H8. stepb_tk F_145e4 D_145e4 ltac:(condZ). apply mst_refl. Qed.

  (* [comment removed for export] *)
  Lemma pd_N : forall regs m (px pp na parr ba : Z),
    (px mod 16 = 0)%Z -> (1 <= px)%Z -> RECat m px (pixa_flds 0 na 1 parr ba) ->
    store_ok SEGS m (Z_to_bv 64 px) 32 = true ->
    getr regs 8 = Z_to_bv 64 px -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x146e8 : word) m rom)
                  (mkst regs' (0x17c54 : word) (wbytes m (Z_to_bv 64 (px + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = Z_to_bv 64 px /\ getr regs' 9 = Z_to_bv 64 pp /\ getr regs' 10 = Z_to_bv 64 parr /\ getr regs' 1 = Z_to_bv 64 0x14754
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m px pp na parr ba Hal Hpx R SOKp H8 H10. pose proof (PIXA_wf m px 0 na 1 parr ba R) as (_ & Wna & Wparr & Wba & _ & Wpx).
    assert (AL8 : (px mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r px); apply mod16_plus_mod8; [exact Hal | reflexivity]).
    eexists. split.
    - stepb_ft F_145e4 D_145e4 ltac:(condZ).
      zand F_145e8 D_145e8 andi_7 AL8. stepb_ft F_145ec D_145ec ltac:(condZ).
      zv F_145f0 D_145f0 (Z_to_bv 64 (px + 8)).
      sn F_145f4 D_145f4.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_145f8 eq_refl D_145f8);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; exact (PIXA_rd_rc m px 0 na 1 parr ba R)
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 1) by lia.
      sn F_145fc D_145fc.
      stepb_ft F_14600 D_14600 ltac:(condZ).
      sn F_14604 D_14604.
      stepLD F_14608 D_14608 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact (PIXA_rd_n m px 0 na 1 parr ba R)) ltac:(apply lez4; lia).
      stepb_tk F_1460c D_1460c ltac:(condZ).
      stepLD F_14648 D_14648 (Z_to_le_bytes 8 parr) (Z_to_bv 64 parr) ltac:(addr_norm; repeat rdn_peel1; exact (PIXA_rd_parr m px 0 na 1 parr ba R)) ltac:(apply lez8; lia).
      sn F_1464c D_1464c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_D : forall regs m (px : Z),
    (0 <= px)%Z -> (px + 32 < 2 ^ 64)%Z -> getr regs 8 = Z_to_bv 64 px ->
    exists regs',
      msteps SEGS (mkst regs (0x14754 : word) m rom) (mkst regs' (0x14a20 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x1475c /\ getr regs' 10 = Z_to_bv 64 (px + 24) /\ getr regs' 8 = Z_to_bv 64 px
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m px Hpx Hpx64 H8. eexists. split.
    - zv F_14650 D_14650 (Z_to_bv 64 (px + 24)). sn F_14654 D_14654. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_E : forall regs m (px : Z),
    getr regs 8 = Z_to_bv 64 px ->
    exists regs',
      msteps SEGS (mkst regs (0x1475c : word) m rom) (mkst regs' (0x17c54 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x14764 /\ getr regs' 10 = Z_to_bv 64 px
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m px H8. eexists. split.
    - sn F_14658 D_14658. sn F_1465c D_1465c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_F : forall regs m (pp : Z),
    (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 9 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x14764 : word) m rom)
                  (mkst regs' (0x147b0 : word) (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 10 = Z_to_bv 64 pp /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m pp Hpp Hpp64 SOKp H9. eexists. split.
    - sn F_14660 D_14660.
      stepST F_14664 D_14664 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKp).
      sn F_14668 D_14668.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pdF_out : forall m s ret regs (x : word), (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 48 \/ s <= u x)%Z -> pdF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold pdF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.
Lemma pcF_out : forall m s ret regs (x : word), (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 24 \/ s <= u x)%Z -> pcF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold pcF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cellsZ_pd : forall C A s pp m m' l, Cok C -> POSTD C A s pp m m' -> c_top C - LSTK <= s ->
  Forall (fun av => s <= fst av /\ fst av + 8 <= 2 ^ 64 /\ (pp + 8 <= fst av \/ fst av + 8 <= pp)) l -> cellsZ m l -> cellsZ m' l.
Proof.
  intros C A s pp m m' l CK PD Hlo HL. induction l as [|[a v] t IH]; intros CE; [exact I|].
  destruct CE as [R CE]. inversion HL as [|x t' (Ha & Hn & Hd) HL']; subst. cbn in Ha, Hn, Hd.
  split; [| exact (IH HL' CE)]. rewrite <- pu8_segs, (POSTD_rdn_above C A s pp m m' a 8 CK PD); [rewrite pu8_segs; exact R | lia | cbn; lia | lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma boxa_at_keep0 : forall C A A' m m' ba na arr,
  boxa_at C A m ba 0 na arr 0 ->
  live A' (Z_to_bv 64 ba) = live A (Z_to_bv 64 ba) -> live A' (Z_to_bv 64 arr) = live A (Z_to_bv 64 arr) ->
  (forall x : word, ba <= u x < ba + 24 -> m' x = m x) ->
  boxa_at C A' m' ba 0 na arr 0.
Proof.
  intros C A A' m m' ba na arr (R & Hal & Lba & L0ba & ARR) Eba Earr AG.
  split; [apply (RECat_frame m m' ba _ R); intros x Hx; apply AG; cbn in Hx; lia|].
  split; [exact Hal|]. split; [rewrite Eba; exact Lba|]. split; [exact L0ba|].
  destruct ARR as [[Harr0 _] | (Larr & L0arr & Hna & NE & _)]; [left; split; [exact Harr0 | reflexivity]|].
  right. split; [rewrite Earr; exact Larr|]. split; [exact L0arr|]. split; [exact Hna|]. split; [exact NE|]. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixa_at (C : lctx) (A : AS) (m : word -> option byte) (px na parr ba bna barr : Z) : Prop :=
  RECat m px (pixa_flds 0 na 1 parr ba) /\ (px mod 16 = 0)%Z /\
  live A (Z_to_bv 64 px) = Some 32%Z /\ live (c_A0 C) (Z_to_bv 64 px) = None /\
  live A (Z_to_bv 64 parr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 parr) = None /\ (1 <= na)%Z /\ parr <> px /\
  boxa_at C A m ba 0 bna barr 0 /\ ba <> px /\ ba <> parr /\ barr <> px /\ barr <> parr.

(* [comment removed for export] *)
Definition pixa_gat (C : lctx) (A : AS) (m : word -> option byte) (px na parr ba bna barr : Z) : Prop :=
  RECat m px (pixa_flds 0 na 1 parr ba) /\ (px mod 16 = 0)%Z /\
  live A (Z_to_bv 64 px) = Some 32%Z /\ live (c_A0 C) (Z_to_bv 64 px) = None /\
  (parr = 0%Z \/ (live A (Z_to_bv 64 parr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 parr) = None /\ (1 <= na)%Z /\ parr <> px)) /\
  (ba = 0%Z \/ (boxa_at C A m ba 0 bna barr 0 /\ ba <> px /\ ba <> parr /\ barr <> px /\ barr <> parr)).

Lemma pixa_at_gat : forall C A m px na parr ba bna barr, pixa_at C A m px na parr ba bna barr -> pixa_gat C A m px na parr ba bna barr.
Proof.
  intros C A m px na parr ba bna barr (R & Hal & Lpx & L0px & Lparr & L0parr & Hna & NE1 & BA & NE2 & NE3 & NE4 & NE5).
  do 4 (split; [assumption|]). split; right; [split; [exact Lparr | split; [exact L0parr | split; [exact Hna | exact NE1]]]
                                             |split; [exact BA | split; [exact NE2 | split; [exact NE3 | split; [exact NE4 | exact NE5]]]]].
Qed.

Theorem pixaDestroy_null_W : forall C A m md regs (s pp : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x146c0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL ALpp Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 48 \/ s <= pp)%Z) by lia.
  destruct (pd_A al_rom regs m s pp 0 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (pdF m s ret regs) md /\ POSTM C A s m (pdF m s ret regs)) by (unfold pdF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (pd_Z al_rom r1 _ Q8) |].
  destruct (pd_epi al_rom r1 (pdF m s ret regs) s ret regs ltac:(lia) ltac:(lia) Hret (pdF_cells m s ret regs ltac:(lia) ltac:(lia)) Q2)
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & V18 & V19 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN6 |].
  apply (HK _ r6 HW1); [| exact PM1].
  apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?H2; try reflexivity.
  all: rewrite (AG6 _) by notin_lit; csr; reflexivity.
Qed.

Theorem pixaDestroy_gen_W : forall C A m md regs (s pp px na parr ba bna barr : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 px) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  pixa_gat C A m px na parr ba bna barr ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 px /\ p <> Z_to_bv 64 parr /\ p <> Z_to_bv 64 ba /\ p <> Z_to_bv 64 barr) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 px) = None -> live A' (Z_to_bv 64 parr) = None ->
     (ba <> 0%Z -> live A' (Z_to_bv 64 ba) = None /\ live A' (Z_to_bv 64 barr) = None) ->
     (forall q, q <> Z_to_bv 64 px -> q <> Z_to_bv 64 parr -> q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 barr -> live A' q = live A q) ->
     sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x146c0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp px na parr ba bna barr sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 SL ALpp Rpp Z0 PX DISJ HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold ALLOC_STACK in Hlo.
  destruct PX as (R & Hal & Lpx & L0px & PARR & BA).
  pose proof (PIXA_wf m px 0 na 1 parr ba R) as (_ & Wna & Wparr & Wba & Wpx0 & Wpx).
  destruct (blk_range C A m md (Z_to_bv 64 px) 32 CK HW Lpx ltac:(lia)) as [Gpx TOPpx]. rewrite u_Z2bv in Gpx, TOPpx by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  (* [comment removed for export] *)
  assert (NEpp : Z_to_bv 64 px <> Z_to_bv 64 parr).
  { destruct PARR as [-> | (_ & _ & _ & NE1)]; [exact (zneq_w px 0 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (zneq_w px parr ltac:(lia) ltac:(lia) (not_eq_sym NE1))]. }
  assert (NEB : ba <> 0%Z ->
            Z_to_bv 64 px <> Z_to_bv 64 ba /\ Z_to_bv 64 px <> Z_to_bv 64 barr /\ Z_to_bv 64 ba <> Z_to_bv 64 parr /\ Z_to_bv 64 barr <> Z_to_bv 64 parr).
  { intros NZ. destruct BA as [-> | ((RB & Halb & Lba & L0ba & ARRB) & NE2 & NE3 & NE4 & NE5)]; [lia|].
    pose proof (BOXA_wf m ba 0 bna 1 barr RB) as (_ & Wbna & Wbarr & _ & _).
    destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Gba TOPba]. rewrite u_Z2bv in Gba, TOPba by lia.
    split; [exact (zneq_w px ba ltac:(lia) ltac:(lia) (not_eq_sym NE2))|]. split; [exact (zneq_w px barr ltac:(lia) ltac:(lia) (not_eq_sym NE4))|].
    split; [exact (zneq_w ba parr ltac:(lia) ltac:(lia) NE3) | exact (zneq_w barr parr ltac:(lia) ltac:(lia) NE5)]. }
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (DJ : (pp + 8 <= s - 48 \/ s <= pp)%Z) by lia.
  (* [comment removed for export] *)
  destruct (pd_A al_rom regs m s pp px ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (pdF m s ret regs) md /\ POSTM C A s m (pdF m s ret regs)) by (unfold pdF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  (* [comment removed for export] *)
  assert (R1 : RECat (pdF m s ret regs) px (pixa_flds 0 na 1 parr ba)).
  { apply (RECat_frame m _ px _ R). intros x Hx. cbn in Hx. apply pdF_out; lia. }
  assert (SOKpx : store_ok SEGS (pdF m s ret regs) (Z_to_bv 64 px) 32 = true).
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (pdF m s ret regs x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined _ px _ x R1 ltac:(cbn; lia) E). }
  destruct (pd_N al_rom r1 (pdF m s ret regs) px pp na parr ba Hal ltac:(lia) R1 SOKpx Q8 Q10) as (r2 & RUN2 & P2 & P8 & P9 & P10 & P1 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes (pdF m s ret regs) (Z_to_bv 64 (px + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (HW2 : W C A M2 md).
  { subst M2. apply (W_store_blk C A _ md (Z_to_bv 64 px) _ 32 _ CK HW1 Lpx L0px); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (R2 : RECat M2 px (pixa_flds 0 na 0 parr ba)).
  { subst M2. eapply (REC_wr' _ _ (pixa_flds 0 na 1 parr ba) _ 2 4); [exact R1 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity]. }
  assert (CE2 : pd_cells M2 s ret regs).
  { unfold pd_cells. apply (cellsZ_out (pdF m s ret regs) M2 px (px + 32)).
    - intros x Hx. subst M2. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - clear -HsR TOPpx T1 Hlo PIN7. forall_cells.
    - exact (pdF_cells m s ret regs ltac:(lia) ltac:(lia)). }
  assert (P2' : getr r2 2 = Z_to_bv 64 (s - 48)) by (rewrite P2; exact Q2).
  assert (P4 : getr r2 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  (* [comment removed for export] *)
  assert (JOIN1 : forall A1 m1 vm1 r3, W C A1 m1 (with_vmmaps vm1 md) -> cs_kept r2 r3 ->
            live A1 (Z_to_bv 64 parr) = None -> (forall q, q <> Z_to_bv 64 parr -> live A1 q = live A q) -> sub_live A1 A ->
            POSTM C A1 (s - 48) M2 m1 ->
            roomtr A (m_vmmaps md) A1 vm1 0 0 ->
            realizes SEGS (mkCfg (mkst r3 (0x14754 : word) m1 al_rom) (with_vmmaps vm1 md)) S).
  { intros A1 m1 vm1 r3 HWa CSa Lparr1 LEQ1 SUB1 PMa HRTa.
    assert (Lpx1 : live A1 (Z_to_bv 64 px) = Some 32%Z) by (rewrite (LEQ1 _ NEpp); exact Lpx).
    assert (E8 : getr r3 8 = Z_to_bv 64 px) by (csr; reflexivity).
    destruct (pd_D al_rom r3 m1 px ltac:(lia) ltac:(lia) E8) as (r4 & RUN4 & U2 & U1 & U10 & U8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
    assert (R3 : RECat m1 px (pixa_flds 0 na 0 parr ba)).
    { apply (RECat_POSTM C A1 (s - 48) M2 m1 (Z_to_bv 64 px) 32 _ _ R2 PMa Lpx1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
    assert (U2' : getr r4 2 = Z_to_bv 64 (s - 48)) by (rewrite U2; csr; reflexivity).
    assert (U4 : getr r4 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    assert (SLh : slotok C A1 (s - 48) (px + 24) (Some (Z_to_bv 64 px, 32%Z))).
    { cbn. rewrite u_Z2bv by lia. split; [exact Lpx1|]. split; [exact L0px|]. lia. }
    (* [comment removed for export] *)
    assert (JOIN2 : forall A2 m2 vm2 r5, W C A2 m2 (with_vmmaps vm2 md) -> cs_kept r4 r5 ->
              (ba <> 0%Z -> live A2 (Z_to_bv 64 ba) = None /\ live A2 (Z_to_bv 64 barr) = None) ->
              (forall q, (ba <> 0%Z -> q <> Z_to_bv 64 ba /\ q <> Z_to_bv 64 barr) -> live A2 q = live A1 q) -> sub_live A2 A1 ->
              POSTD C A2 (s - 48) (px + 24) m1 m2 ->
              roomtr A (m_vmmaps md) A2 vm2 0 0 ->
              realizes SEGS (mkCfg (mkst r5 (0x1475c : word) m2 al_rom) (with_vmmaps vm2 md)) S).
    { intros A2 m2 vm2 r5 HWb CSb LB2 LEQ2 SUB2 PD2 HRTb.
      assert (Lpx2 : live A2 (Z_to_bv 64 px) = Some 32%Z).
      { rewrite (LEQ2 _ ltac:(intros NZ; destruct (NEB NZ) as (X1 & X2 & _); split; [exact X1 | exact X2])). exact Lpx1. }
      assert (V8 : getr r5 8 = Z_to_bv 64 px) by (csr; reflexivity).
      destruct (pd_E al_rom r5 m2 px V8) as (r6 & RUN6 & X2 & X1 & X10 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN6 |].
      assert (X2' : getr r6 2 = Z_to_bv 64 (s - 48)) by (rewrite X2; csr; reflexivity).
      assert (X4 : getr r6 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
      (* [comment removed for export] *)
      replace (0x17c54 : word) with (Z_to_bv 64 0x17c54) by (apply bv_eq; reflexivity).
      apply (W_free16 C A2 m2 _ r6 (Z_to_bv 64 px) (Z_to_bv 64 0x14764) 32 (s - 48) S CK HWb X10 Lpx2 L0px X1
               ltac:(red; apply bv_eq; reflexivity) X4 X2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
      intros A3 m3 vm3 r7 HWc CSc Lpx3 LEQ3 PMc HRTc. rewrite with_vmmaps_twice in HWc. rewrite with_vmmaps_twice.
      replace (Z_to_bv 64 0x14764) with (0x14764 : word) by (apply bv_eq; reflexivity).
      assert (SUB3 : sub_live A3 A2).
      { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 px)) as [->|NE]; [congruence|]. rewrite <- (LEQ3 q NE). exact L. }
      (* [comment removed for export] *)
      assert (SL3 : slotok C A3 s pp sb).
      { apply (slot_keep C A A3 s pp sb SL). intros p k E. pose proof (DISJ p k E) as (D1 & D2 & D3 & D4).
        rewrite (LEQ3 p D1), (LEQ2 p ltac:(intros _; split; [exact D3 | exact D4])). exact (LEQ1 p D2). }
      pose proof (slot_sok C A3 m3 _ s pp sb CK HWc SL3 ltac:(lia)) as SOKp. rewrite pu8_segs in SOKp.
      assert (Y9 : getr r7 9 = Z_to_bv 64 pp) by (csr; reflexivity).
      destruct (pd_F al_rom r7 m3 pp ltac:(lia) ltac:(lia) SOKp Y9) as (r8 & RUN8 & Y2 & Y10 & AG8).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN8 |].
      set (M4 := wbytes m3 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
      assert (HW4 : W C A3 M4 (with_vmmaps vm3 md)).
      { subst M4. apply (slot_W C A3 m3 _ s pp sb _ CK HWc SL3 ltac:(lia)). rewrite length_N_to_le_bytes. reflexivity. }
      assert (CE4 : pd_cells M4 s ret regs).
      { unfold pd_cells. apply (cellsZ_out m3 M4 pp (pp + 8)).
        - intros x Hx. subst M4. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
        - clear -DJ HsR. forall_cells.
        - apply (cellsZ_frm C (s - 48) m2 m3); [exact CK | exact (proj1 PMc) | lia | clear -HsR; forall_cells |].
          apply (cellsZ_pd C A2 (s - 48) (px + 24) m1 m2); [exact CK | exact PD2 | lia | clear -HsR TOPpx T1 Hlo PIN7; forall_cells |].
          apply (cellsZ_frm C (s - 48) M2 m1); [exact CK | exact (proj1 PMa) | lia | clear -HsR; forall_cells | exact CE2]. }
      assert (Y2' : getr r8 2 = Z_to_bv 64 (s - 48)) by (rewrite Y2; csr; reflexivity).
      destruct (pd_epi al_rom r8 M4 s ret regs ltac:(lia) ltac:(lia) Hret CE4 Y2') as (r9 & RUN9 & V2 & V1 & V8' & V9 & V18 & V19 & AG9).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN9 |].
      apply (HK A3 M4 vm3 r9 HW4).
      - apply cs_kept_intro; rewrite ?V2, ?V8', ?V9, ?V18, ?V19, ?H2; try reflexivity.
        all: rewrite (AG9 _) by notin_lit; rewrite (AG8 _) by notin_lit; csr; reflexivity.
      - exact Lpx3.
      - rewrite (LEQ3 _ (not_eq_sym NEpp)).
        rewrite (LEQ2 _ ltac:(intros NZ; destruct (NEB NZ) as (_ & _ & Y3 & Y4); split; [exact (not_eq_sym Y3) | exact (not_eq_sym Y4)])).
        exact Lparr1.
      - intros NZ. destruct (NEB NZ) as (Nb1 & Nb2 & _). destruct (LB2 NZ) as [Lba2 Lbarr2].
        rewrite (LEQ3 _ (not_eq_sym Nb1)), (LEQ3 _ (not_eq_sym Nb2)). split; [exact Lba2 | exact Lbarr2].
      - intros q N1 N2 N3 N4. rewrite (LEQ3 q N1), (LEQ2 q ltac:(intros _; split; [exact N3 | exact N4])). exact (LEQ1 q N2).
      - exact (sub_live_trans _ _ _ SUB3 (sub_live_trans _ _ _ SUB2 SUB1)).
      - (* [comment removed for export] *)
        pose proof (sub_live_trans _ _ _ SUB3 SUB2) as SUB31. pose proof (sub_live_trans _ _ _ SUB31 SUB1) as SUB30.
        apply (POSTD_trans C A3 s pp m (pdF m s ret regs) M4); [exact (POSTD_of_POSTM C A A3 s pp m _ PM1 SUB30)|].
        apply (POSTD_trans C A3 s pp (pdF m s ret regs) M2 M4).
        { subst M2. apply (POSTD_deadw C A A3 _ md (Z_to_bv 64 px) _ 32 _ s pp CK HW1 Lpx Lpx3 SUB30); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
        apply (POSTD_trans C A3 s pp M2 m1 M4); [apply (POSTD_of_POSTM C A1 A3); [eapply POSTM_mono; [|exact PMa]; lia | exact SUB31]|].
        apply (POSTD_trans C A3 s pp m1 m2 M4).
        { apply (POSTD_of_POSTM C A3 A3); [| apply sub_live_refl]. apply (POSTM_mono C A3 (s - 48) s); [lia|].
          apply (POSTD_POSTM_blk C A3 A2 m2 (with_vmmaps vm2 md) (Z_to_bv 64 px) 32 (s - 48) (px + 24) m1 m2 CK HWb Lpx2); [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | exact Lpx3 | exact SUB3 |].
          exact (POSTD_sub C A2 A3 _ _ _ _ SUB3 PD2). }
        apply (POSTD_trans C A3 s pp m2 m3 M4); [apply (POSTD_of_POSTM C A3 A3); [eapply POSTM_mono; [|exact PMc]; lia | apply sub_live_refl]|].
        subst M4. apply POSTD_slotw; [rewrite length_N_to_le_bytes; reflexivity | lia | lia].
      - subst M4. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
      - clear HRTa. room_tac. }
    (* [comment removed for export] *)
    assert (AL24 : ((px + 24) mod 8 = 0)%Z) by (apply mod16_plus_mod8; [exact Hal | reflexivity]).
    destruct BA as [Eb | ((RB & Halb & Lba & L0ba & ARRB) & NE2 & NE3 & NE4 & NE5)].
    - (* [comment removed for export] *)
      apply (boxaDestroy_null_W C A1 m1 _ r4 (s - 48) (px + 24) (Some (Z_to_bv 64 px, 32%Z)) (Z_to_bv 64 0x1475c) S CK HWa U2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 SLh AL24).
      { rewrite <- Eb at 1. exact (PIXA_rd_ba m1 px 0 na 0 parr ba R3). }
      intros m2 r5 HWb CSb PMb.
      replace (Z_to_bv 64 0x1475c) with (0x1475c : word) by (apply bv_eq; reflexivity).
      apply (JOIN2 A1 m2 vm1 r5 HWb CSb); [intros NZ; exfalso; exact (NZ Eb) | intros q _; reflexivity | apply sub_live_refl
                                          | exact (POSTD_of_POSTM C A1 A1 (s - 48) (px + 24) m1 m2 PMb (sub_live_refl A1)) | exact HRTa].
    - (* [comment removed for export] *)
      pose proof (BOXA_wf m ba 0 bna 1 barr RB) as (_ & Wbna & Wbarr & _ & _). pose proof (RECat_range m ba _ RB) as [Wba0 Wba24]. cbn in Wba24.
      destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Gba TOPba]. rewrite u_Z2bv in Gba, TOPba by lia.
      pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lpx Lba (zneq_w px ba ltac:(lia) ltac:(lia) (not_eq_sym NE2))) as Dpb.
      rewrite !u_Z2bv in Dpb by lia. change (round16 32) with 32%Z in Dpb. change (round16 24) with 32%Z in Dpb.
      assert (BA1 : boxa_at C A1 m1 ba 0 bna barr 0).
      { apply (boxa_at_keep0 C A A1 m m1 ba bna barr (conj RB (conj Halb (conj Lba (conj L0ba ARRB))))).
        - apply LEQ1. exact (zneq_w ba parr ltac:(lia) ltac:(lia) NE3).
        - apply LEQ1. exact (zneq_w barr parr ltac:(lia) ltac:(lia) NE5).
        - intros x Hx. rewrite (LIVK_byte A1 M2 m1 (Z_to_bv 64 ba) 24 x (proj2 PMa)); [| rewrite (LEQ1 _ (zneq_w ba parr ltac:(lia) ltac:(lia) NE3)); exact Lba | rewrite u_Z2bv by lia; lia].
          subst M2. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia). apply pdF_out; lia. }
      apply (boxaDestroy_W C A1 m1 _ r4 (s - 48) (px + 24) ba 0 bna barr 0 (Some (Z_to_bv 64 px, 32%Z)) (Z_to_bv 64 0x1475c) S CK HWa U2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) U1
               ltac:(red; apply bv_eq; reflexivity) U4 U10 SLh AL24).
      { exact (PIXA_rd_ba m1 px 0 na 0 parr ba R3). }
      { exact Z0. }
      { exact BA1. }
      { intros p k E. injection E as <- <-. split; [exact (zneq_w px ba ltac:(lia) ltac:(lia) (not_eq_sym NE2))|].
        split; [exact (zneq_w px barr ltac:(lia) ltac:(lia) (not_eq_sym NE4)) | intros X; discriminate X]. }
      intros A2 m2 vm2 r5 HWb CSb Lba2 Lbarr2 _ LEQ2 SUB2 PD2 RD2 HRTb2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
      replace (Z_to_bv 64 0x1475c) with (0x1475c : word) by (apply bv_eq; reflexivity).
      apply (JOIN2 A2 m2 vm2 r5 HWb CSb); [intros _; split; [exact Lba2 | exact Lbarr2] | | exact SUB2 | exact PD2 | room_tac].
      intros q Hq. destruct (Hq ltac:(lia)) as [N3 N4]. exact (LEQ2 q N3 N4 ltac:(intros X; discriminate X)). }
  (* [comment removed for export] *)
  replace (0x17c54 : word) with (Z_to_bv 64 0x17c54) by (apply bv_eq; reflexivity).
  destruct PARR as [Ep | (Lparr & L0parr & Hna & NE1)].
  - rewrite Ep in P10.
    apply (W_free0_8 C A M2 md r2 (Z_to_bv 64 0x14754) (s - 48) S CK HW2 Z0 P10 P1 ltac:(red; apply bv_eq; reflexivity) P4 P2'
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r3 HWa CSa L01 LEQ1 PMa HRTa.
    replace (Z_to_bv 64 0x14754) with (0x14754 : word) by (apply bv_eq; reflexivity).
    assert (SUB1 : sub_live A1 A).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE]; [rewrite L01 in L; discriminate L|]. rewrite <- (LEQ1 q NE). exact L. }
    rewrite Ep in JOIN1. apply (JOIN1 A1 m1 vm1 r3 HWa CSa L01 LEQ1 SUB1); [exact (POSTM_sub C A1 A (s - 48) M2 m1 SUB1 PMa) | exact HRTa].
  - destruct (blk_range C A m md (Z_to_bv 64 parr) (8 * na) CK HW Lparr ltac:(lia)) as [Gparr TOPparr]. rewrite u_Z2bv in Gparr, TOPparr by lia.
    apply (W_free16 C A M2 md r2 (Z_to_bv 64 parr) (Z_to_bv 64 0x14754) (8 * na) (s - 48) S CK HW2 P10 Lparr L0parr P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r3 HWa CSa Lparr1 LEQ1 PMa HRTa.
    replace (Z_to_bv 64 0x14754) with (0x14754 : word) by (apply bv_eq; reflexivity).
    assert (SUB1 : sub_live A1 A).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 parr)) as [->|NE]; [congruence|]. rewrite <- (LEQ1 q NE). exact L. }
    exact (JOIN1 A1 m1 vm1 r3 HWa CSa Lparr1 LEQ1 SUB1 PMa HRTa).
Qed.

(* [comment removed for export] *)
Theorem pixaDestroy_W : forall C A m md regs (s pp px na parr ba bna barr : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 px) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  pixa_at C A m px na parr ba bna barr ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 px /\ p <> Z_to_bv 64 parr /\ p <> Z_to_bv 64 ba /\ p <> Z_to_bv 64 barr) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 px) = None -> live A' (Z_to_bv 64 parr) = None -> live A' (Z_to_bv 64 ba) = None -> live A' (Z_to_bv 64 barr) = None ->
     (forall q, q <> Z_to_bv 64 px -> q <> Z_to_bv 64 parr -> q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 barr -> live A' q = live A q) ->
     sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x146c0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp px na parr ba bna barr sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 SL ALpp Rpp Z0 PX DISJ HK.
  pose proof PX as (_ & _ & _ & _ & _ & _ & _ & _ & (RB & _ & Lba & _) & _).
  pose proof (RECat_range m ba _ RB) as [Wba0 Wba24]. cbn in Wba24.
  destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Gba _]. rewrite u_Z2bv in Gba by lia.
  apply (pixaDestroy_gen_W C A m md regs s pp px na parr ba bna barr sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 SL ALpp Rpp Z0
           (pixa_at_gat _ _ _ _ _ _ _ _ _ PX) DISJ).
  intros A' m' vm' regs' HW' CS' L1 L2 L34 LEQ SUB PD RD HRT. destruct (L34 ltac:(lia)) as [L3 L4].
  exact (HK A' m' vm' regs' HW' CS' L1 L2 L3 L4 LEQ SUB PD RD HRT).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixa_new (C : lctx) (A A' : AS) (m' : word -> option byte) (px parr ba barr : Z) : Prop :=
  pixa_at C A' m' px 20 parr ba 20 barr /\ (1 <= barr)%Z /\
  live A (Z_to_bv 64 px) = None /\ live A (Z_to_bv 64 parr) = None /\ live A (Z_to_bv 64 ba) = None /\ live A (Z_to_bv 64 barr) = None /\
  live A' (Z_to_bv 64 barr) = Some 160%Z /\ live (c_A0 C) (Z_to_bv 64 barr) = None /\
  (forall q, q <> Z_to_bv 64 px -> q <> Z_to_bv 64 parr -> q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 barr -> live A' q = live A q).


Theorem pixaCreate_sure_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 0 ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixa <= kR)%Z -> (RB_pixa 20 <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists px parr ba barr : Z, getr regs' 10 = Z_to_bv 64 px /\ pixa_new C A A' m' px parr ba barr) ->
     aroom A' vm' (kR - RK_pixa) (bR - RB_pixa 20) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x145d8 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Z0A Z0 kR bR Hrm Hrk Hrb HK.
  pose proof (alloc_margin_le (1 * 32)) as MG1. pose proof (alloc_margin_le (20 * 8)) as MG2. unfold RK_pixa, RK_boxa in Hrk. unfold RB_pixa, RB_boxa in Hrb.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold LSF in *.
  assert (HsR : (0x523f0 + 8192 <= s < 2 ^ 63)%Z) by lia.
  destruct (pc_A al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (pcF m s ret regs) md /\ POSTM C A s m (pcF m s ret regs)) by (unfold pcF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  replace (0x17b1c : word) with (Z_to_bv 64 0x17b1c) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A _ md r1 1 32 kR bR (Z_to_bv 64 0x145f8) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  replace (Z_to_bv 64 0x145f8) with (0x145f8 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r2 9 = Z_to_bv 64 0) by (csr; reflexivity).
  assert (E4a : getr r2 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  assert (CEa : pc_cells m1 s ret regs).
  { unfold pc_cells. apply (cellsZ_frm C (s - 32) (pcF m s ret regs) m1); [exact CK | exact (proj1 PMa) | lia | clear -HsR; forall_cells | exact (pcF_cells m s ret regs ltac:(lia) ltac:(lia))]. }
  pose proof CEa as (C8 & C16 & C24 & _).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) as SOKs.
  - (* [comment removed for export] *)
    assert (Hpx : (1 <= u res)%Z /\ (u res + 32 <= alloc_top (c_vm C))%Z).
    { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 32 + 15) / 16)%Z with 2%Z in TOP. lia. }
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
    set (px := u res) in *. clearbody px.
    rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (ALpx : (px mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r px); apply mod16_plus_mod8; [exact AL16 | reflexivity]).
    assert (Z0_1 : live A1 (Z_to_bv 64 0) = None) by (rewrite (LEQ _ (zneq_w 0 px ltac:(lia) ltac:(lia) ltac:(lia))); exact Z0A).
    assert (REC0 : RECat m1 px (zflds [4; 4; 4; 4; 8; 8]%nat)).
    { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
      unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
    assert (SOKpx : store_ok SEGS m1 (Z_to_bv 64 px) 32 = true).
    { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m1 px _ x REC0 ltac:(cbn; lia) E). }
    destruct (pc_B al_rom r2 m1 s px ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpx SOKs SOKpx E2a Hres E8a) as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (Ms := wbytes m1 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 px))).
    set (M2 := wbytes (wbytes (wbytes Ms _ _) _ _) _ _).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (WPs : W C A1 Ms (with_vmmaps vm1 md) /\ POSTM C A s m Ms).
    { subst Ms. apply (WP_win C A1 A m m1 _ _ _ s CK); [| exact SUBa | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
      split; [exact HWa | exact PMa']. }
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
    { subst M2.
      do 3 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 px) _ 32); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
      exact WPs. }
    destruct WP2 as [HW2 PM2].
    assert (REC2 : RECat M2 px (pixa_flds 0 20 1 0 0)).
    { subst M2 Ms. unfold pixa_flds.
      eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 20%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 2 4); [| cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity].
      eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 1 4); [| cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity].
      eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 0 4); [| cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity].
      apply RECat_out; [exact REC0 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (CE2 : pc_cells M2 s ret regs).
    { unfold pc_cells. apply (cellsZ_out m1 M2 px (s - 24)); [| clear -HsR Hpx T1 Hlo PIN7; forall_cells | exact CEa].
      intros x Hx. subst M2 Ms. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (P4 : getr r3 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    (* [comment removed for export] *)
    replace (0x17b1c : word) with (Z_to_bv 64 0x17b1c) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A1 M2 _ r3 20 8 (kR - 1) (bR - alloc_margin (1 * 32)) (Z_to_bv 64 0x14648) (s - 32) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact Hroom1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hroom2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x14648) with (0x14648 : word) by (apply bv_eq; reflexivity).
    pose proof (blk_range C A1 M2 _ (Z_to_bv 64 px) 32 CK HW2 L1 ltac:(lia)) as [Gpx _]. rewrite u_Z2bv in Gpx by lia.
    (* [comment removed for export] *)
    assert (PARR : exists parr : Z, res2 = Z_to_bv 64 parr /\ (0 <= parr < 2 ^ 64)%Z /\
              live A2 (Z_to_bv 64 px) = Some 32%Z /\ live A2 (Z_to_bv 64 0) = None /\
              (forall q, q <> Z_to_bv 64 parr -> live A2 q = live A1 q) /\
              (parr = 0%Z \/ (live A2 (Z_to_bv 64 parr) = Some 160%Z /\ live (c_A0 C) (Z_to_bv 64 parr) = None /\ live A1 (Z_to_bv 64 parr) = None /\ parr <> px /\ (1 <= parr)%Z)) /\ parr <> 0%Z).
    { exists (u res2). pose proof (u64_range res2) as Hr2.
        assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
        assert (NE : Z_to_bv 64 px <> res2) by (intros E; rewrite <- E in K0; congruence).
        assert (NE0 : Z_to_bv 64 0 <> res2) by (intros E; rewrite <- E in Hnz2; rewrite u_Z2bv in Hnz2 by lia; lia).
        rewrite <- Eres2. split; [reflexivity|]. split; [lia|].
        split; [rewrite (KEQ _ NE); exact L1|]. split; [rewrite (KEQ _ NE0); exact Z0_1|].
        split; [exact KEQ|]. split; [| exact Hnz2]. right. change (20 * 8)%Z with 160%Z in K1. split; [exact K1|]. split; [exact K00|]. split; [exact K0|].
        split; [| lia]. intros E. apply NE. rewrite <- E. apply zbv_self. }
    destruct PARR as (parr & -> & Hparr & Lpx2 & Z0_2 & LEQ2 & PARR & NZparr).
    assert (SUBb : sub_live A1 A2).
    { intros q k L. rewrite (LEQ2 q); [exact L|]. intros ->. destruct PARR as [-> | (_ & _ & X & _)]; congruence. }
    pose proof (sub_live_trans _ _ _ SUBa SUBb) as SUBab.
    assert (REC3 : RECat m2 px (pixa_flds 0 20 1 0 0)).
    { apply (RECat_POSTM C A1 (s - 32) M2 m2 (Z_to_bv 64 px) 32 _ _ REC2 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
    assert (SOKpx2 : store_ok SEGS m2 (Z_to_bv 64 px) 32 = true).
    { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 px _ x REC3 ltac:(cbn; lia) E). }
    assert (F9 : getr r4 8 = Z_to_bv 64 px) by (csr; reflexivity).
    assert (F8 : getr r4 9 = Z_to_bv 64 20) by (csr; reflexivity).
    destruct (pc_C al_rom r4 m2 px parr ltac:(lia) ltac:(lia) Hparr SOKpx2 Hres2 F9 F8) as (r5 & RUN5 & U2 & U1 & U10 & U9 & U8 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
    set (M3 := wbytes m2 _ _).
    assert (HW3 : W C A2 M3 (with_vmmaps vm2 md)).
    { subst M3. apply (W_store_blk C A2 m2 _ (Z_to_bv 64 px) _ 32 _ CK HWb Lpx2 L00); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (PM3 : POSTM C A s m M3).
    { apply (POSTM_trans C A s m M2 M3); [exact PM2|]. apply (POSTM_trans C A s M2 m2 M3); [apply (POSTM_sub C A A1 _ _ _ SUBa); eapply POSTM_mono; [|exact PMb]; lia|].
      subst M3. apply (POSTM_blk C A A2 m2 _ (Z_to_bv 64 px) _ 32 _ s CK HWb Lpx2 L0 SUBab); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    assert (REC4 : RECat M3 px (pixa_flds 0 20 1 parr 0)).
    { subst M3. eapply (REC_wr' _ _ (pixa_flds 0 20 1 0 0) _ 4 8); [exact REC3 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity]. }
    assert (CE3 : pc_cells M3 s ret regs).
    { unfold pc_cells. apply (cellsZ_out m2 M3 px (px + 32)); [| clear -HsR Hpx T1 Hlo PIN7; forall_cells |].
      - intros x Hx. subst M3. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
      - apply (cellsZ_frm C (s - 32) M2 m2); [exact CK | exact (proj1 PMb) | lia | clear -HsR; forall_cells | exact CE2]. }
    assert (U2' : getr r5 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; csr; reflexivity).
    assert (U4 : getr r5 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    (* [comment removed for export] *)
    apply (boxaCreate_sure_W C A2 M3 _ r5 (s - 32) 20 (Z_to_bv 64 0x14654) S CK HW3 U2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U4 U10 ltac:(lia) Z0_2 Z0
             (kR - 1 - 1) (bR - alloc_margin (1 * 32) - alloc_margin (20 * 8)) ltac:(rewrite with_vmmaps_vmmaps; exact Hroom2) ltac:(unfold RK_boxa; lia) ltac:(unfold RB_boxa; lia)).
    intros A3 m3 vm3 r6 HWc CSc PMc OUTc Hroom3. rewrite with_vmmaps_twice in HWc. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x14654) with (0x14654 : word) by (apply bv_eq; reflexivity).
    assert (V2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (V9 : getr r6 8 = Z_to_bv 64 px) by (csr; reflexivity).
    assert (V4 : getr r6 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    (* [comment removed for export] *)
    assert (BA : exists ba barr : Z, getr r6 10 = Z_to_bv 64 ba /\ (0 <= ba < 2 ^ 64)%Z /\ (0 <= barr < 2 ^ 64)%Z /\
              (forall q, (ba <> 0%Z -> q <> Z_to_bv 64 ba /\ q <> Z_to_bv 64 barr) -> live A3 q = live A2 q) /\
              ((ba = 0%Z /\ barr = 0%Z) \/ (boxa_new C A2 A3 m3 ba 20 barr /\ ba <> px /\ barr <> px /\ ba <> parr /\ barr <> parr /\ (4096 <= ba)%Z)) /\ ba <> 0%Z).
    { destruct OUTc as (ba & barr & A10 & BN).
      exists ba, barr. pose proof BN as (RB & _ & Hbarr & _ & NEab & Lb2 & Lr2 & _ & _ & Lb3 & Lr3 & LEQ3 & _).
        pose proof (BOXA_wf m3 ba 0 20 1 barr RB) as (_ & _ & Wbarr & Wba0 & Wba).
        destruct (blk_range C A3 m3 _ (Z_to_bv 64 ba) 24 CK HWc Lb3 ltac:(lia)) as [Gba _]. rewrite u_Z2bv in Gba by lia.
        split; [exact A10|]. split; [lia|]. split; [lia|]. split; [intros q Hq; destruct (Hq ltac:(lia)) as [Y1 Y2]; exact (LEQ3 q Y1 Y2)|].
        split; [| clear -Gba; lia]. right. split; [exact BN|].
        split; [intros ->; congruence|]. split; [intros ->; congruence|].
        destruct PARR as [-> | (Lp2 & _)]; [split; [lia | split; lia] | split; [intros ->; congruence | split; [intros ->; congruence | lia]]]. }
    destruct BA as (ba & barr & A10 & Hba & Hbarr & LEQ3 & BA & NZba).
    assert (Lpx3 : live A3 (Z_to_bv 64 px) = Some 32%Z).
    { rewrite (LEQ3 (Z_to_bv 64 px)); [exact Lpx2|]. intros NZ. destruct BA as [[-> ->] | (BN & N1 & N2 & _)]; [lia|].
      split; [exact (zneq_w px ba ltac:(lia) ltac:(lia) (not_eq_sym N1)) | exact (zneq_w px barr ltac:(lia) ltac:(lia) (not_eq_sym N2))]. }
    assert (REC5 : RECat m3 px (pixa_flds 0 20 1 parr 0)).
    { apply (RECat_POSTM C A2 (s - 32) M3 m3 (Z_to_bv 64 px) 32 _ _ REC4 PMc Lpx2); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
    assert (CE5 : pc_cells m3 s ret regs).
    { unfold pc_cells. apply (cellsZ_frm C (s - 32) M3 m3); [exact CK | exact (proj1 PMc) | lia | clear -HsR; forall_cells | exact CE3]. }
    pose proof CE5 as (D8 & D16 & D24 & _).
    assert (PM5 : POSTM C A s m m3).
    { apply (POSTM_trans C A s m M3 m3); [exact PM3|]. apply (POSTM_sub C A A2 _ _ _ SUBab). eapply POSTM_mono; [|exact PMc]. lia. }
    assert (LAparr : parr <> 0%Z -> live A (Z_to_bv 64 parr) = None).
    { intros NZ. destruct PARR as [-> | (_ & _ & X & _)]; [lia|]. destruct (live A (Z_to_bv 64 parr)) as [k|] eqn:E; [pose proof (SUBa _ _ E); congruence | reflexivity]. }
    assert (SOKpx3 : store_ok SEGS m3 (Z_to_bv 64 px) 32 = true).
    { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m3 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m3 px _ x REC5 ltac:(cbn; lia) E). }
    pose proof (PIXA_rd_parr m3 px 0 20 1 parr 0 REC5) as Rparr.
    destruct (Sumbool.sumbool_or _ _ _ _ (Z.eq_dec parr 0) (Z.eq_dec ba 0)) as [CLEAN | BOTH]; cycle 1.
    + (* [comment removed for export] *)
      destruct PARR as [Hparr0 | (Lparr2 & L0parr & LAparr1 & NEpp & Hparr1)]; [exfalso; clear -BOTH Hparr0; tauto|].
      destruct BA as [[Hba0 _] | (BN & N1 & N2 & N3 & N4 & Gba)]; [exfalso; clear -BOTH Hba0; tauto|].
      pose proof BN as (RB & Halb & Hbarr1 & Halr & NEab & Lb2 & Lr2 & L0b & L0r & Lb3 & Lr3 & LEQ3' & TOPb1 & TOPb2).
      destruct (pc_D al_rom r6 m3 s px parr ba ret (getr regs 8) (getr regs 9)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKpx3 ltac:(lia) Rparr D8 D16 D24 V2 A10 V9)
        as (r7 & RUN7 & W2 & W1 & W10 & W8 & W9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN7 |].
      set (M4 := wbytes m3 _ _).
      assert (SUBc : sub_live A2 A3) by (eapply sub_live_new2; [exact Lb2 | exact Lr2 | exact Lb3 | exact Lr3 | exact LEQ3']).
      assert (WP4 : W C A3 M4 (with_vmmaps vm3 md) /\ POSTM C A s m M4).
      { subst M4. apply (WP_blk C A A3 m m3 _ (Z_to_bv 64 px) _ 32); [exact CK | | exact Lpx3 | exact L0 | exact L00 | exact (sub_live_trans _ _ _ SUBab SUBc) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWc | exact PM5]. }
      destruct WP4 as [HW4 PM4].
      apply (HK A3 M4 vm3 r7 HW4).
      * apply cs_kept_intro; csr; rewrite ?W8, ?W9; try reflexivity.
      * exact PM4.
      * exists px, parr, ba, barr. split; [exact W10|].
        assert (LA3 : forall q, q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 barr -> q <> Z_to_bv 64 parr -> q <> Z_to_bv 64 px -> live A3 q = live A q).
        { intros q Y1 Y2 Y3 Y4. rewrite (LEQ3' q Y1 Y2), (LEQ2 q Y3). exact (LEQ q Y4). }
        split.
        -- split; [| split; [exact AL16 | split; [exact Lpx3 | split; [exact L00|]]]].
           { subst M4. eapply (REC_wr' _ _ (pixa_flds 0 20 1 parr 0) _ 5 8); [exact REC5 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity]. }
           split; [rewrite (LEQ3' _ (not_eq_sym (zneq_w ba parr ltac:(lia) ltac:(lia) N3)) (not_eq_sym (zneq_w barr parr ltac:(lia) ltac:(lia) N4))); exact Lparr2|].
           split; [exact L0parr|]. split; [lia|]. split; [exact NEpp|].
           split; [| split; [exact N1 | split; [exact N3 | split; [exact N2 | exact N4]]]].
           apply (boxa_new_at C A2 A3 _ ba 20 barr ltac:(lia)).
           pose proof BN as (RB' & rest). split; [| exact rest].
           subst M4. apply RECat_out; [exact RB' | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [flds_len boxa_flds Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
           pose proof (ai_live_disjoint A3 m3 _ _ _ _ _ (w_inv _ _ _ _ HWc) Lpx3 Lb3 (zneq_w px ba ltac:(lia) ltac:(lia) (not_eq_sym N1))) as D.
           rewrite !u_Z2bv in D by lia. change (round16 32) with 32%Z in D. change (round16 24) with 32%Z in D. lia.
        -- split; [lia|]. split; [exact L0|]. split; [rewrite <- (LEQ _ (zneq_w parr px ltac:(lia) ltac:(lia) NEpp)); exact LAparr1|].
           split; [rewrite <- (LEQ _ (zneq_w ba px ltac:(lia) ltac:(lia) N1)), <- (LEQ2 _ (zneq_w ba parr ltac:(lia) ltac:(lia) N3)); exact Lb2|].
           split; [rewrite <- (LEQ _ (zneq_w barr px ltac:(lia) ltac:(lia) N2)), <- (LEQ2 _ (zneq_w barr parr ltac:(lia) ltac:(lia) N4)); exact Lr2|].
           split; [exact Lr3|]. split; [exact L0r|].
           intros q Y1 Y2 Y3 Y4. exact (LA3 q Y3 Y4 Y2 Y1).
      * unfold RK_pixa, RB_pixa. unfold RK_boxa, RB_boxa in *. apply (aroom_mono A3 vm3 _ _ _ _ Hroom3); lia.
    + (* [comment removed for export] *)
      exfalso. destruct CLEAN as [X|X]; [exact (NZparr X) | exact (NZba X)].
Qed.

(* [comment removed for export] *)
Theorem pixaCreate_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 0 ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixa <= kR)%Z -> (RB_pixa 20 <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists px parr ba barr : Z, getr regs' 10 = Z_to_bv 64 px /\ pixa_new C A A' m' px parr ba barr) ) ->
     aroom A' vm' (kR - RK_pixa) (bR - RB_pixa 20) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x145d8 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Z0A Z0 kR bR Hrm Hrk Hrb HK.
  apply (pixaCreate_sure_W C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Z0A Z0 kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' RES Hrm'. apply (HK A' m' vm' regs' HW' CS' PM'); [right; exact RES | exact Hrm'].
Qed.
End Pixa.
