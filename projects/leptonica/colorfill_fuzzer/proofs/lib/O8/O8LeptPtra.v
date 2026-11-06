(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptArith2 LibAtomic LeptRecs LeptSlots.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8LeptStderr O8LeptBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8CL7a.
Import O8CL7a.O8LeptErr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8LeptBoxa O8_code_13660_14000 O8_code_14000_15000 O8_code_17000_18000.
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
Definition ptra_flds (na n arr : Z) : list fld := [(4%nat, na); (4%nat, n); (8%nat, arr)].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma nclamp6_ok : forall n, (1 <= n <= 1000000)%Z ->
  (zx (sw32 (n + 18446744073708551615)) <? zx 18446744073708551616)%Z = false.
Proof. intros n H. unfold zx, sw32. apply Z.ltb_ge. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Ptra.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL8} {PN8 : O8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma PTRA_rd_n : forall m pa na n arr, RECat m pa (ptra_flds na n arr) -> rdn SEGS m (Z_to_bv 64 (pa + 4)) 4 = Some (Z_to_le_bytes 4 n).
Proof. intros m pa na n arr R. eapply (REC_rd' SEGS _ _ (ptra_flds na n arr) 1 4); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma PTRA_rd_na : forall m pa na n arr, RECat m pa (ptra_flds na n arr) -> rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 na).
Proof. intros m pa na n arr R. eapply (REC_rd' SEGS _ _ (ptra_flds na n arr) 0 4); [exact R | cbn; lia | reflexivity | cbn [fld_off ptra_flds Z.of_nat]; f_equal; lia | reflexivity]. Qed.
Lemma PTRA_rd_arr : forall m pa na n arr, RECat m pa (ptra_flds na n arr) -> rdn SEGS m (Z_to_bv 64 (pa + 8)) 8 = Some (Z_to_le_bytes 8 arr).
Proof. intros m pa na n arr R. eapply (REC_rd' SEGS _ _ (ptra_flds na n arr) 2 8); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma PTRA_wf : forall m pa na n arr, RECat m pa (ptra_flds na n arr) ->
  (0 <= na < 2 ^ 32)%Z /\ (0 <= n < 2 ^ 32)%Z /\ (0 <= arr < 2 ^ 64)%Z /\ (0 <= pa)%Z /\ (pa + 16 < 2 ^ 64)%Z.
Proof. intros m pa na n arr (H0 & H1 & WF & _). cbn in H1, WF. lia. Qed.

(* [comment removed for export] *)
Definition ptra_at (C : lctx) (A : AS) (m : word -> option byte) (pa na arr : Z) : Prop :=
  RECat m pa (ptra_flds na 0 arr) /\
  live A (Z_to_bv 64 pa) = Some 16%Z /\ live (c_A0 C) (Z_to_bv 64 pa) = None /\
  (arr = 0%Z \/ (live A (Z_to_bv 64 arr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\ (1 <= na)%Z /\ arr <> pa)).

(* [comment removed for export] *)
Definition ptra_new (C : lctx) (A A' : AS) (m' : word -> option byte) (pa na arr : Z) : Prop :=
  RECat m' pa (ptra_flds na 0 arr) /\ (1 <= arr)%Z /\ arr <> pa /\
  live A (Z_to_bv 64 pa) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 pa) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 pa) = Some 16%Z /\ live A' (Z_to_bv 64 arr) = Some (8 * na)%Z /\
  (forall q, q <> Z_to_bv 64 pa -> q <> Z_to_bv 64 arr -> live A' q = live A q).

Lemma ptra_new_at : forall C A A' m' pa na arr, (1 <= na)%Z -> ptra_new C A A' m' pa na arr -> ptra_at C A' m' pa na arr.
Proof.
  intros C A A' m' pa na arr Hna (R & Harr & NE & L1 & L2 & L01 & L02 & La & Lb & LEQ).
  split; [exact R|]. split; [exact La|]. split; [exact L01|]. right. split; [exact Lb|]. split; [exact L02|]. split; [exact Hna | exact NE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsN.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Definition ndF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
      (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
      (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
      (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
      (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
      (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).

  Definition nd_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9); (s - 32, getr R 18); (s - 40, getr R 19);
              (s - 48, getr R 20); (s - 56, getr R 21); (s - 64, getr R 22); (s - 72, getr R 23);
              (s - 80, getr R 24); (s - 88, getr R 25); (s - 96, getr R 26); (s - 104, getr R 27)]%Z.

  Lemma ndF_cells : forall m s ret regs, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> nd_cells (ndF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold nd_cells, ndF. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  (* [comment removed for export] *)
  Lemma nd_A : forall regs m (s pp v : Z) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 v) -> (pp + 8 <= s - 112 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x142c0 : word) m rom) (mkst regs' (0x14304 : word) (ndF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 9 = Z_to_bv 64 v /\ getr regs' 8 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s pp v ret Hs Hs64 Hpp Hpp64 Hv SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_141bc D_141bc (Z_to_bv 64 (s - 112)).
      stepST F_141c0 D_141c0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_141c4 D_141c4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_141c8 D_141c8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_141cc D_141cc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_141d0 D_141d0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_141d4 D_141d4 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_141d8 D_141d8 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_141dc D_141dc (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_141e0 D_141e0 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_141e4 D_141e4 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_141e8 D_141e8 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_141ec D_141ec (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_141f0 D_141f0 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      stepb_ft F_141f4 D_141f4 ltac:(condZ).
      sn F_141f8 D_141f8.
      stepLD F_141fc D_141fc (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nd_epi : forall regs m (s : Z) (ret : word) (R : bvmap 5 word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> nd_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs',
      msteps SEGS (mkst regs (0x1441c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9 /\ getr regs' 18 = getr R 18 /\ getr regs' 19 = getr R 19
      /\ getr regs' 20 = getr R 20 /\ getr regs' 21 = getr R 21 /\ getr regs' 22 = getr R 22 /\ getr regs' 23 = getr R 23
      /\ getr regs' 24 = getr R 24 /\ getr regs' 25 = getr R 25 /\ getr regs' 26 = getr R 26 /\ getr regs' 27 = getr R 27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret R Hs Hs64 Hret CE H2.
    destruct CE as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104 & _).
    eexists. split.
    - stepLD8 F_14318 D_14318 ret.
      stepLD8 F_1431c D_1431c (getr R 8).
      stepLD8 F_14320 D_14320 (getr R 9).
      stepLD8 F_14324 D_14324 (getr R 18).
      stepLD8 F_14328 D_14328 (getr R 19).
      stepLD8 F_1432c D_1432c (getr R 20).
      stepLD8 F_14330 D_14330 (getr R 21).
      stepLD8 F_14334 D_14334 (getr R 22).
      stepLD8 F_14338 D_14338 (getr R 23).
      stepLD8 F_1433c D_1433c (getr R 24).
      stepLD8 F_14340 D_14340 (getr R 25).
      stepLD8 F_14344 D_14344 (getr R 26).
      stepLD8 F_14348 D_14348 (getr R 27).
      zv F_1434c D_1434c (Z_to_bv 64 s).
      stepret F_14350 D_14350 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nd_Z : forall regs m,
    getr regs 9 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x14304 : word) m rom) (mkst regs (0x1441c : word) m rom).
  Proof. intros regs m H9. stepb_tk F_14200 D_14200 ltac:(condZ). apply mst_refl. Qed.

  (* [comment removed for export] *)
  Lemma nd_N : forall regs m (pa na arr : Z),
    (1 <= pa)%Z -> RECat m pa (ptra_flds na 0 arr) ->
    getr regs 9 = Z_to_bv 64 pa ->
    exists regs',
      msteps SEGS (mkst regs (0x14304 : word) m rom) (mkst regs' (0x17454 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 pa /\ getr regs' 10 = Z_to_bv 64 arr /\ getr regs' 1 = Z_to_bv 64 0x143ac
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pa na arr Hpa R H9. pose proof (PTRA_wf m pa na 0 arr R) as (Wna & _ & Warr & _ & Wpa).
    eexists. split.
    - stepb_ft F_14200 D_14200 ltac:(condZ).
      stepLD F_14204 D_14204 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact (PTRA_rd_n m pa na 0 arr R)) ltac:(apply lez4; lia).
      stepb_tk F_14208 D_14208 ltac:(condZ).
      stepLD F_142a0 D_142a0 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact (PTRA_rd_arr m pa na 0 arr R)) ltac:(apply lez8; lia).
      sn F_142a4 D_142a4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nd_D : forall regs m (pa : Z),
    getr regs 9 = Z_to_bv 64 pa ->
    exists regs',
      msteps SEGS (mkst regs (0x143ac : word) m rom) (mkst regs' (0x17454 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 1 = Z_to_bv 64 0x143b4 /\ getr regs' 9 = Z_to_bv 64 pa
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pa H9. eexists. split.
    - sn F_142a8 D_142a8. sn F_142ac D_142ac. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nd_E : forall regs m (pp : Z),
    (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 8 = Z_to_bv 64 pp ->
    msteps SEGS (mkst regs (0x143b4 : word) m rom)
                (mkst regs (0x1441c : word) (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom).
  Proof.
    intros regs m pp Hpp Hpp64 SOKp H8.
    stepST F_142b0 D_142b0 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKp).
    sn F_142b4 D_142b4.
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma nc_A : forall regs m (s n : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= n <= 1000000)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x1420c : word) m rom)
                  (mkst regs' (0x1731c : word)
                     (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                             (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                             (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x14244
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 16 /\ getr regs' 8 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n ret Hs Hs64 Hn SOK H2 H1 H10.
    eexists. split.
    - zv F_14108 D_14108 (Z_to_bv 64 (s - 32)).
      stepST F_1410c D_1410c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14110 D_14110 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14114 D_14114 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_14118 D_14118. sn F_1411c D_1411c. sn F_14120 D_14120.
      sn F_14124 D_14124. fixv (Z_to_bv 64 (sw32 (n + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      sn F_14128 D_14128.
      stepb_tk F_1412c D_1412c ltac:(pin; rewrite c_ltu_zx; apply nclamp6_ok; lia).
      sn F_14134 D_14134. sn F_14138 D_14138. sn F_1413c D_1413c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nc_B : forall regs m (s n pa : Z),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pa < 2 ^ 64)%Z -> (0 <= n < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 pa -> getr regs 8 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x14244 : word) m rom)
                  (mkst regs' (0x1731c : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pa))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x14258
      /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 8 = Z_to_bv 64 n /\ getr regs' 9 = Z_to_bv 64 pa
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n pa Hs Hs64 Hpa Hn SOK H2 H10 H8.
    eexists. split.
    - sn F_14140 D_14140.                                       (* [comment removed for export] *)
      stepST F_14144 D_14144 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pa) ltac:(sok_in SOK).
      sn F_14148 D_14148. sn F_1414c D_1414c. sn F_14150 D_14150.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma nc_C : forall regs m (s pa arr n : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z -> (0 <= n < 2 ^ 31)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pa) 16 = true -> (pa + 16 <= s - 32 \/ s <= pa)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 9 = Z_to_bv 64 pa -> getr regs 8 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x14258 : word) m rom)
                  (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (pa + 8)) (word_to_le_bytes 8 (Z_to_bv 64 arr)))
                                          (Z_to_bv 64 pa) (word_to_le_bytes 4 (Z_to_bv 64 n)))
                                          (Z_to_bv 64 (pa + 4)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pa arr n ret s0v s1v Hs Hs64 Harr Hpa Hpa64 Hn Hret SOKp DJ R8 R16 R24 H2 H10 H9 H8.
    eexists. split.
    - stepST F_14154 D_14154 (Z_to_bv 64 (pa + 8)) (Z_to_bv 64 arr) ltac:(sok_in SOKp).
      stepb_ft F_14158 D_14158 ltac:(condZ).
      sn F_1415c D_1415c.
      stepST F_14160 D_14160 (Z_to_bv 64 pa) (Z_to_bv 64 n) ltac:(sok_in SOKp).
      stepST F_14164 D_14164 (Z_to_bv 64 (pa + 4)) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      sn F_14168 D_14168.
      stepLD8 F_141a8 D_141a8 ret.
      stepLD8 F_141ac D_141ac s0v.
      stepLD8 F_141b0 D_141b0 s1v.
      zv F_141b4 D_141b4 (Z_to_bv 64 s).
      stepret F_141b8 D_141b8 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End SegsN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ndF_out : forall m s ret regs (x : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 112 \/ s <= u x)%Z -> ndF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold ndF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

Lemma RECat_ndF : forall m s ret regs p fs, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> RECat m p fs ->
  (p + Z.of_nat (flds_len fs) <= s - 112)%Z -> RECat (ndF m s ret regs) p fs.
Proof. intros m s ret regs p fs Hs Hs64 R Hp. apply (RECat_frame m _ p fs R). intros x Hx. apply ndF_out; lia. Qed.

Lemma nd_T2 : forall C m regs md1 (A1 : AS) (m1 : word -> option byte) r2 (s pp pa : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A1 m1 md1 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr r2 2 = Z_to_bv 64 (s - 112) -> getr r2 9 = Z_to_bv 64 pa -> getr r2 8 = Z_to_bv 64 pp -> getr r2 4 = Z_to_bv 64 0x31370 ->
  getr r2 3 = getr regs 3 ->
  nd_cells m1 s ret regs ->
  slotok C A1 s pp sb -> (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pa) ->
  live A1 (Z_to_bv 64 pa) = Some 16%Z -> live (c_A0 C) (Z_to_bv 64 pa) = None -> (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z ->
  (forall Af, sub_live Af A1 -> live Af (Z_to_bv 64 pa) = None -> POSTD C Af s pp m m1) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md1) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pa) = None -> (forall q, q <> Z_to_bv 64 pa -> live A' q = live A1 q) -> sub_live A' A1 ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A1 (m_vmmaps md1) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md1)) S) ->
  realizes SEGS (mkCfg (mkst r2 (0x143ac : word) m1 al_rom) md1) S.
Proof.
  intros C m regs md1 A1 m1 r2 s pp pa sb ret S CK HW1 Hs16 Hlo Hhi Hret H2 H4 R2 R9 R8 R4 R3 CE1 SL1 DISJ Lpa L0pa Hpa Hpa64 PRE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold ALLOC_STACK in Hlo.
  pose proof (slot_range C A1 m1 md1 s pp sb CK HW1 SL1 ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A1 m1 md1 s pp sb CK HW1 SL1 ltac:(lia)) as SW.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (DJ : (pp + 8 <= s - 112 \/ s <= pp)%Z) by lia.
  destruct (nd_D al_rom r2 m1 pa R9) as (r3 & RUN3 & Q10 & Q1 & Q9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
  assert (Q2 : getr r3 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (Q4 : getr r3 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
  replace (0x17454 : word) with (Z_to_bv 64 0x17454) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 m1 md1 r3 (Z_to_bv 64 pa) (Z_to_bv 64 0x143b4) 16 (s - 112) S CK HW1 Q10 Lpa L0pa Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 HW2 CS2 Lpa2 LEQ2 PM2 HRT2.
  replace (Z_to_bv 64 0x143b4) with (0x143b4 : word) by (apply bv_eq; reflexivity).
  assert (SUB2 : sub_live A2 A1).
  { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 pa)) as [->|NE]; [congruence|]. rewrite <- (LEQ2 q NE). exact L. }
  assert (SL2 : slotok C A2 s pp sb).
  { apply (slot_keep C A1 A2 s pp sb SL1). intros p k E. apply LEQ2. exact (DISJ p k E). }
  pose proof (slot_sok C A2 m2 _ s pp sb CK HW2 SL2 ltac:(lia)) as SOKp. rewrite p8_segs in SOKp.
  assert (E8 : getr r4 8 = Z_to_bv 64 pp) by (csr; reflexivity).
  pose proof (nd_E al_rom r4 m2 pp ltac:(lia) ltac:(lia) SOKp E8) as RUN5.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  set (M3 := wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (HW3 : W C A2 M3 (with_vmmaps vm2 md1)).
  { subst M3. apply (slot_W C A2 m2 _ s pp sb _ CK HW2 SL2 ltac:(lia)). rewrite length_N_to_le_bytes. reflexivity. }
  assert (CE3 : nd_cells M3 s ret regs).
  { unfold nd_cells. apply (cellsZ_out m2 M3 pp (pp + 8)).
    - intros x Hx. subst M3. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - clear -DJ HsR. forall_cells.
    - apply (cellsZ_frm C (s - 112) m1 m2); [exact CK | exact (proj1 PM2) | lia | | exact CE1].
      clear -HsR. forall_cells. }
  assert (E2' : getr r4 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  destruct (nd_epi al_rom r4 M3 s ret regs ltac:(lia) ltac:(lia) Hret CE3 E2')
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN6 |].
  apply (HK A2 M3 vm2 r6 HW3).
  - apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?V27, ?H2; try reflexivity.
    + rewrite (AG6 3) by notin_lit. csr. reflexivity.
    + rewrite (AG6 4) by notin_lit. csr. reflexivity.
  - exact Lpa2.
  - exact LEQ2.
  - exact SUB2.
  - eapply POSTD_trans; [exact (PRE A2 SUB2 Lpa2)|].
    apply (POSTD_trans C A2 s pp m1 m2 M3); [apply (POSTD_of_POSTM C A2 A2); [eapply POSTM_mono; [|exact PM2]; lia | apply sub_live_refl]|].
    subst M3. apply POSTD_slotw; [rewrite length_N_to_le_bytes; reflexivity | lia | lia].
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma nd_T1 : forall C m regs mdx (Ax : AS) (mx : word -> option byte) rx (s pp pa na arr : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C Ax mx mdx ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr rx 2 = Z_to_bv 64 (s - 112) -> getr rx 1 = Z_to_bv 64 0x143ac -> getr rx 10 = Z_to_bv 64 arr ->
  getr rx 9 = Z_to_bv 64 pa -> getr rx 8 = Z_to_bv 64 pp -> getr rx 4 = Z_to_bv 64 0x31370 -> getr rx 3 = getr regs 3 ->
  nd_cells mx s ret regs ->
  slotok C Ax s pp sb -> (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pa /\ p <> Z_to_bv 64 arr) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  live Ax (Z_to_bv 64 pa) = Some 16%Z -> live (c_A0 C) (Z_to_bv 64 pa) = None -> (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z ->
  (0 <= arr < 2 ^ 64)%Z ->
  (arr = 0%Z \/ (live Ax (Z_to_bv 64 arr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\ (1 <= na)%Z /\ arr <> pa)) ->
  (forall Af, sub_live Af Ax -> live Af (Z_to_bv 64 pa) = None -> live Af (Z_to_bv 64 arr) = None -> POSTD C Af s pp m mx) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' mdx) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pa) = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 pa -> q <> Z_to_bv 64 arr -> live A' q = live Ax q) -> sub_live A' Ax ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr Ax (m_vmmaps mdx) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' mdx)) S) ->
  realizes SEGS (mkCfg (mkst rx (Z_to_bv 64 0x17454) mx al_rom) mdx) S.
Proof.
  intros C m regs mdx Ax mx rx s pp pa na arr sb ret S CK HWx Hs16 Hlo Hhi Hret H2 H4 R2 R1 R10 R9 R8 R4 R3 CEx SLx DISJ Z0
         Lpa L0pa Hpa Hpa64 Harr ARR PRE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold ALLOC_STACK in Hlo.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (NEpa : Z_to_bv 64 pa <> Z_to_bv 64 arr).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. destruct ARR as [-> | (_ & _ & _ & NE)]; lia. }
  assert (KONT : forall A1 m1 vm1 r2, W C A1 m1 (with_vmmaps vm1 mdx) -> cs_kept rx r2 ->
     live A1 (Z_to_bv 64 arr) = None -> (forall q, q <> Z_to_bv 64 arr -> live A1 q = live Ax q) -> sub_live A1 Ax ->
     POSTM C A1 (s - 112) mx m1 ->
     roomtr Ax (m_vmmaps mdx) A1 vm1 0 0 ->
     realizes SEGS (mkCfg (mkst r2 (Z_to_bv 64 0x143ac) m1 al_rom) (with_vmmaps vm1 mdx)) S).
  { intros A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 SUB1 PM1 HRT1.
    assert (Lpa1 : live A1 (Z_to_bv 64 pa) = Some 16%Z) by (rewrite (LEQ1 _ NEpa); exact Lpa).
    replace (Z_to_bv 64 0x143ac) with (0x143ac : word) by (apply bv_eq; reflexivity).
    apply (nd_T2 C m regs (with_vmmaps vm1 mdx) A1 m1 r2 s pp pa sb ret S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi Hret H2 H4);
      [csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | | | | exact Lpa1 | exact L0pa | exact Hpa | exact Hpa64 | |].
    - unfold nd_cells. apply (cellsZ_frm C (s - 112) mx m1); [exact CK | exact (proj1 PM1) | lia | | exact CEx].
      clear -HsR. forall_cells.
    - apply (slot_keep C Ax A1 s pp sb SLx). intros p k E. apply LEQ1. exact (proj2 (DISJ p k E)).
    - intros p k E. exact (proj1 (DISJ p k E)).
    - intros Af SUBf Lf.
      assert (Lfa : live Af (Z_to_bv 64 arr) = None).
      { destruct (live Af (Z_to_bv 64 arr)) as [k|] eqn:E; [|reflexivity]. pose proof (SUBf _ _ E). congruence. }
      eapply POSTD_trans; [apply PRE; [exact (sub_live_trans _ _ _ SUBf SUB1) | exact Lf | exact Lfa]|].
      apply (POSTD_of_POSTM C A1 Af); [eapply POSTM_mono; [|exact PM1]; lia | exact SUBf].
    - intros A' m' vm' regs' HW' CS' Lpa' LEQ' SUB' PD' RD' HRT'. rewrite with_vmmaps_twice in HW'. rewrite with_vmmaps_twice.
      apply (HK A' m' vm' regs' HW' CS' Lpa').
      + rewrite (LEQ' _ (not_eq_sym NEpa)). exact La1.
      + intros q N1 N2. rewrite (LEQ' q N1). exact (LEQ1 q N2).
      + exact (sub_live_trans _ _ _ SUB' SUB1).
      + exact PD'.
      + exact RD'.
      + room_tac. }
  destruct ARR as [Harr0 | (Larr & L0arr & Hna & NEarr)].
  - rewrite Harr0 in R10.
    apply (W_free0_8 C Ax mx mdx rx (Z_to_bv 64 0x143ac) (s - 112) S CK HWx Z0 R10 R1 ltac:(red; apply bv_eq; reflexivity) R4 R2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r2 HW1 CS1 L01 LEQ1 PM1 HRT1. rewrite Harr0 in KONT.
    assert (SUB1 : sub_live A1 Ax).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE]; [congruence|]. rewrite <- (LEQ1 q NE). exact L. }
    apply (KONT A1 m1 vm1 r2 HW1 CS1 L01 LEQ1 SUB1); [exact (POSTM_sub C A1 Ax _ _ _ SUB1 PM1) | exact HRT1].
  - apply (W_free16 C Ax mx mdx rx (Z_to_bv 64 arr) (Z_to_bv 64 0x143ac) (8 * na) (s - 112) S CK HWx R10 Larr L0arr R1
             ltac:(red; apply bv_eq; reflexivity) R4 R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 PM1 HRT1.
    assert (SUB1 : sub_live A1 Ax).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|NE]; [congruence|]. rewrite <- (LEQ1 q NE). exact L. }
    exact (KONT A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 SUB1 PM1 HRT1).
Qed.

Theorem numaaDestroy_W : forall C A m md regs (s pp pa na arr : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pa) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  ptra_at C A m pa na arr ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pa /\ p <> Z_to_bv 64 arr) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pa) = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 pa -> q <> Z_to_bv 64 arr -> live A' q = live A q) -> sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x142c0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pa na arr sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 SL Rpp Z0 PA DISJ HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold ALLOC_STACK in Hlo.
  destruct PA as (R & Lpa & L0pa & ARR).
  pose proof (PTRA_wf m pa na 0 arr R) as (Wna & _ & Warr & Wpa0 & Wpa).
  destruct (blk_range C A m md (Z_to_bv 64 pa) 16 CK HW Lpa ltac:(lia)) as [Gpa TOPpa]. rewrite u_Z2bv in Gpa, TOPpa by lia.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (DJ : (pp + 8 <= s - 112 \/ s <= pp)%Z) by lia.
  destruct (nd_A al_rom regs m s pp pa ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (ndF m s ret regs) md /\ POSTM C A s m (ndF m s ret regs)) by (unfold ndF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (R1 : RECat (ndF m s ret regs) pa (ptra_flds na 0 arr)) by (apply RECat_ndF; [lia | lia | exact R | cbn; lia]).
  destruct (nd_N al_rom r1 (ndF m s ret regs) pa na arr ltac:(lia) R1 Q9) as (r2 & RUN2 & P9 & P10 & P1 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  replace (0x17454 : word) with (Z_to_bv 64 0x17454) by (apply bv_eq; reflexivity).
  apply (nd_T1 C m regs md A (ndF m s ret regs) r2 s pp pa na arr sb ret S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi Hret H2 H4);
    [csr; reflexivity | exact P1 | exact P10 | exact P9 | csr; reflexivity | csr; reflexivity | csr; reflexivity
    | exact (ndF_cells m s ret regs ltac:(lia) ltac:(lia)) | exact SL | exact DISJ | exact Z0 | exact Lpa | exact L0pa | lia | lia | exact Warr | exact ARR | |].
  - intros Af SUBf _ _. exact (POSTD_of_POSTM C A Af s pp m _ PM1 SUBf).
  - exact HK.
Qed.

(* [comment removed for export] *)
Theorem numaaDestroy_null_W : forall C A m md regs (s pp : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x142c0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 112 \/ s <= pp)%Z) by lia.
  destruct (nd_A al_rom regs m s pp 0 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (ndF m s ret regs) md /\ POSTM C A s m (ndF m s ret regs)) by (unfold ndF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (nd_Z al_rom r1 _ Q9) |].
  destruct (nd_epi al_rom r1 (ndF m s ret regs) s ret regs ltac:(lia) ltac:(lia) Hret (ndF_cells m s ret regs ltac:(lia) ltac:(lia)) Q2)
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN6 |].
  apply (HK _ r6 HW1); [| exact PM1].
  apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?V27, ?H2; try reflexivity.
  - rewrite (AG6 3) by notin_lit. csr. reflexivity.
  - rewrite (AG6 4) by notin_lit. csr. reflexivity.
Qed.


Theorem numaaCreate_sure_W : forall C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 1000000)%Z ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_naa <= kR)%Z -> (RB_naa n <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists pa arr : Z, getr regs' 10 = Z_to_bv 64 pa /\ ptra_new C A A' m' pa n arr) ->
     aroom A' vm' (kR - RK_naa) (bR - RB_naa n) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1420c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb HK.
  pose proof (alloc_margin_le (1 * 16)) as MG1. pose proof (alloc_margin_le (n * 8)) as MG2. unfold RK_naa in Hrk. unfold RB_naa in Hrb.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold LSF in *.
  assert (HsR : (0x52000 + 8192 <= s < 2 ^ 63)%Z) by lia.
  destruct (nc_A al_rom regs m s n ret ltac:(lia) ltac:(lia) Hn (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
  replace (0x1731c : word) with (Z_to_bv 64 0x1731c) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 16 kR bR (Z_to_bv 64 0x14244) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  replace (Z_to_bv 64 0x14244) with (0x14244 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r2 8 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E4a : getr r2 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R24 : rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  - (* [comment removed for export] *)
    assert (Hpa : (1 <= u res)%Z /\ (u res + 16 <= alloc_top (c_vm C))%Z).
    { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 16 + 15) / 16)%Z with 1%Z in TOP. lia. }
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
    set (pa := u res) in *. clearbody pa.
    rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (REC0 : RECat m1 pa (zflds [4; 4; 8]%nat)).
    { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
      unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
    destruct (nc_B al_rom r2 m1 s n pa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) E2a Hres E8a)
      as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (M2 := wbytes m1 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pa))).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
    { subst M2. apply (WP_win C A1 A m m1 _ _ _ s CK); [| exact SUBa | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
      split; [exact HWa | exact PMa']. }
    destruct WP2 as [HW2 PM2].
    assert (REC2 : RECat M2 pa (zflds [4; 4; 8]%nat)).
    { subst M2. apply RECat_out; [exact REC0 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (P4 : getr r3 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    replace (0x1731c : word) with (Z_to_bv 64 0x1731c) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A1 M2 _ r3 n 8 (kR - 1) (bR - alloc_margin (1 * 16)) (Z_to_bv 64 0x14258) (s - 32) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact Hroom1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hroom2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x14258) with (0x14258 : word) by (apply bv_eq; reflexivity).
    assert (F2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (F9 : getr r4 9 = Z_to_bv 64 pa) by (csr; reflexivity).
    assert (F8 : getr r4 8 = Z_to_bv 64 n) by (csr; reflexivity).
    assert (F4 : getr r4 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    pose proof (blk_range C A1 M2 _ (Z_to_bv 64 pa) 16 CK HW2 L1 ltac:(lia)) as [Gpa _]. rewrite u_Z2bv in Gpa by lia.
    assert (REC4 : RECat m2 pa (zflds [4; 4; 8]%nat)).
    { apply (RECat_POSTM C A1 (s - 32) M2 m2 (Z_to_bv 64 pa) 16 _ _ REC2 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
    assert (SOKp2 : store_ok SEGS m2 (Z_to_bv 64 pa) 16 = true).
    { rewrite <- p8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 pa _ x REC4 ltac:(cbn; lia) E). }
    assert (S8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 8) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rdn_solve. }
    assert (S16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 16) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rdn_solve. }
    assert (S24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 24) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rdn_solve. }
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    + (* [comment removed for export] *)
      assert (Harr : (1 <= u res2)%Z /\ (u res2 + round16 (8 * n) <= alloc_top (c_vm C))%Z).
      { pose proof (u64_range res2). replace (n * 8)%Z with (8 * n)%Z in TOPb by lia. lia. }
      assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
      set (arr := u res2) in *. clearbody arr.
      rewrite Eres2 in Hres2, K0, K1, K00, KEQ.
      pose proof (round16_ge (8 * n) ltac:(lia)) as RG.
      assert (NE : arr <> pa).
      { intros E. rewrite E in K0. rewrite K0 in L1. discriminate L1. }
      destruct (nc_C al_rom r4 m2 s pa arr n ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKp2 ltac:(lia)
                  S8 S16 S24 F2 Hres2 F9 F8) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      set (M4 := wbytes (wbytes (wbytes m2 _ _) _ _) _ _).
      assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
      assert (Lpa2 : live A2 (Z_to_bv 64 pa) = Some 16%Z) by (rewrite (KEQ _ (zneq_w pa arr ltac:(lia) ltac:(lia) (not_eq_sym NE))); exact L1).
      assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A s m M4).
      { subst M4.
        do 3 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pa) _ 16); [exact CK | | exact Lpa2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
        split; [exact HWb | exact PMb']. }
      destruct WP4 as [HW4 PM4].
      apply (HK A2 M4 vm2 r5 HW4).
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; reflexivity.
      * exact PM4.
      * exists pa, arr. split; [exact V10|].
        split.
        { subst M4. unfold ptra_flds.
          eapply (REC_wr' _ _ [(4%nat, n); (4%nat, 0%Z); (8%nat, arr)] _ 1 4);
            [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
          eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr)] _ 0 4);
            [ | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ].
          eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 2 8);
            [ exact REC4 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
        split; [lia|]. split; [exact NE|].
        split; [exact L0|]. split; [rewrite <- (LEQ _ (zneq_w arr pa ltac:(lia) ltac:(lia) NE)); exact K0|].
        split; [exact L00|]. split; [exact K00|]. split; [exact Lpa2|]. split; [replace (8 * n)%Z with (n * 8)%Z by lia; exact K1|].
        intros q N1 N2; rewrite (KEQ q N2); exact (LEQ q N1).
      * unfold RK_naa, RB_naa. apply (aroom_mono A2 vm2 _ _ _ _ Hroom2); lia.
Qed.

(* [comment removed for export] *)
Theorem numaaCreate_W : forall C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 1000000)%Z ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_naa <= kR)%Z -> (RB_naa n <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pa arr : Z, getr regs' 10 = Z_to_bv 64 pa /\ ptra_new C A A' m' pa n arr) ) ->
     aroom A' vm' (kR - RK_naa) (bR - RB_naa n) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1420c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb HK.
  apply (numaaCreate_sure_W C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' RES Hrm'. apply (HK A' m' vm' regs' HW' CS' PM'); [right; exact RES | exact Hrm'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsD.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Definition ddF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
      (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
      (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
      (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
      (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
      (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).

  Definition dd_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9); (s - 32, getr R 18); (s - 40, getr R 19);
              (s - 48, getr R 20); (s - 56, getr R 21); (s - 64, getr R 22); (s - 72, getr R 23);
              (s - 80, getr R 24); (s - 88, getr R 25); (s - 96, getr R 26); (s - 104, getr R 27)]%Z.

  Lemma ddF_cells : forall m s ret regs, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> dd_cells (ddF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold dd_cells, ddF. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  (* [comment removed for export] *)
  Lemma dd_A : forall regs m (s pp v : Z) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 v) -> (pp + 8 <= s - 112 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x14074 : word) m rom) (mkst regs' (0x140b8 : word) (ddF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 9 = Z_to_bv 64 v /\ getr regs' 8 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s pp v ret Hs Hs64 Hpp Hpp64 Hv SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_13f70 D_13f70 (Z_to_bv 64 (s - 112)).
      stepST F_13f74 D_13f74 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13f78 D_13f78 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13f7c D_13f7c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_13f80 D_13f80 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_13f84 D_13f84 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_13f88 D_13f88 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_13f8c D_13f8c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_13f90 D_13f90 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_13f94 D_13f94 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_13f98 D_13f98 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_13f9c D_13f9c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_13fa0 D_13fa0 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_13fa4 D_13fa4 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      stepb_ft F_13fa8 D_13fa8 ltac:(condZ).
      sn F_13fac D_13fac.
      stepLD F_13fb0 D_13fb0 (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma dd_epi : forall regs m (s : Z) (ret : word) (R : bvmap 5 word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> dd_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs',
      msteps SEGS (mkst regs (0x141d0 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9 /\ getr regs' 18 = getr R 18 /\ getr regs' 19 = getr R 19
      /\ getr regs' 20 = getr R 20 /\ getr regs' 21 = getr R 21 /\ getr regs' 22 = getr R 22 /\ getr regs' 23 = getr R 23
      /\ getr regs' 24 = getr R 24 /\ getr regs' 25 = getr R 25 /\ getr regs' 26 = getr R 26 /\ getr regs' 27 = getr R 27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret R Hs Hs64 Hret CE H2.
    destruct CE as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104 & _).
    eexists. split.
    - stepLD8 F_140cc D_140cc ret.
      stepLD8 F_140d0 D_140d0 (getr R 8).
      stepLD8 F_140d4 D_140d4 (getr R 9).
      stepLD8 F_140d8 D_140d8 (getr R 18).
      stepLD8 F_140dc D_140dc (getr R 19).
      stepLD8 F_140e0 D_140e0 (getr R 20).
      stepLD8 F_140e4 D_140e4 (getr R 21).
      stepLD8 F_140e8 D_140e8 (getr R 22).
      stepLD8 F_140ec D_140ec (getr R 23).
      stepLD8 F_140f0 D_140f0 (getr R 24).
      stepLD8 F_140f4 D_140f4 (getr R 25).
      stepLD8 F_140f8 D_140f8 (getr R 26).
      stepLD8 F_140fc D_140fc (getr R 27).
      zv F_14100 D_14100 (Z_to_bv 64 s).
      stepret F_14104 D_14104 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma dd_Z : forall regs m,
    getr regs 9 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x140b8 : word) m rom) (mkst regs (0x141d0 : word) m rom).
  Proof. intros regs m H9. stepb_tk F_13fb4 D_13fb4 ltac:(condZ). apply mst_refl. Qed.

  (* [comment removed for export] *)
  Lemma dd_N : forall regs m (pa na arr : Z),
    (1 <= pa)%Z -> RECat m pa (ptra_flds na 0 arr) ->
    getr regs 9 = Z_to_bv 64 pa ->
    exists regs',
      msteps SEGS (mkst regs (0x140b8 : word) m rom) (mkst regs' (0x17454 : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 pa /\ getr regs' 10 = Z_to_bv 64 arr /\ getr regs' 1 = Z_to_bv 64 0x14160
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pa na arr Hpa R H9. pose proof (PTRA_wf m pa na 0 arr R) as (Wna & _ & Warr & _ & Wpa).
    eexists. split.
    - stepb_ft F_13fb4 D_13fb4 ltac:(condZ).
      stepLD F_13fb8 D_13fb8 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact (PTRA_rd_n m pa na 0 arr R)) ltac:(apply lez4; lia).
      stepb_tk F_13fbc D_13fbc ltac:(condZ).
      stepLD F_14054 D_14054 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact (PTRA_rd_arr m pa na 0 arr R)) ltac:(apply lez8; lia).
      sn F_14058 D_14058.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma dd_D : forall regs m (pa : Z),
    getr regs 9 = Z_to_bv 64 pa ->
    exists regs',
      msteps SEGS (mkst regs (0x14160 : word) m rom) (mkst regs' (0x17454 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 1 = Z_to_bv 64 0x14168 /\ getr regs' 9 = Z_to_bv 64 pa
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pa H9. eexists. split.
    - sn F_1405c D_1405c. sn F_14060 D_14060. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma dd_E : forall regs m (pp : Z),
    (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 8 = Z_to_bv 64 pp ->
    msteps SEGS (mkst regs (0x14168 : word) m rom)
                (mkst regs (0x141d0 : word) (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom).
  Proof.
    intros regs m pp Hpp Hpp64 SOKp H8.
    stepST F_14064 D_14064 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKp).
    sn F_14068 D_14068.
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma dc_A : forall regs m (s n : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= n <= 1000000)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x13fc0 : word) m rom)
                  (mkst regs' (0x1731c : word)
                     (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                             (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                             (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x13ff8
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 16 /\ getr regs' 8 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n ret Hs Hs64 Hn SOK H2 H1 H10.
    eexists. split.
    - zv F_13ebc D_13ebc (Z_to_bv 64 (s - 32)).
      stepST F_13ec0 D_13ec0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13ec4 D_13ec4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13ec8 D_13ec8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13ecc D_13ecc. sn F_13ed0 D_13ed0. sn F_13ed4 D_13ed4.
      sn F_13ed8 D_13ed8. fixv (Z_to_bv 64 (sw32 (n + 18446744073708551615))) ltac:(rewrite v_addw_Z; reflexivity).
      sn F_13edc D_13edc.
      stepb_tk F_13ee0 D_13ee0 ltac:(pin; rewrite c_ltu_zx; apply nclamp6_ok; lia).
      sn F_13ee8 D_13ee8. sn F_13eec D_13eec. sn F_13ef0 D_13ef0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma dc_B : forall regs m (s n pa : Z),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pa < 2 ^ 64)%Z -> (0 <= n < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 pa -> getr regs 8 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x13ff8 : word) m rom)
                  (mkst regs' (0x1731c : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pa))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x1400c
      /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 8 = Z_to_bv 64 n /\ getr regs' 9 = Z_to_bv 64 pa
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n pa Hs Hs64 Hpa Hn SOK H2 H10 H8.
    eexists. split.
    - sn F_13ef4 D_13ef4.                                       (* [comment removed for export] *)
      stepST F_13ef8 D_13ef8 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pa) ltac:(sok_in SOK).
      sn F_13efc D_13efc. sn F_13f00 D_13f00. sn F_13f04 D_13f04.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma dc_C : forall regs m (s pa arr n : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z -> (0 <= n < 2 ^ 31)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pa) 16 = true -> (pa + 16 <= s - 32 \/ s <= pa)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 9 = Z_to_bv 64 pa -> getr regs 8 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x1400c : word) m rom)
                  (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (pa + 8)) (word_to_le_bytes 8 (Z_to_bv 64 arr)))
                                          (Z_to_bv 64 pa) (word_to_le_bytes 4 (Z_to_bv 64 n)))
                                          (Z_to_bv 64 (pa + 4)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pa arr n ret s0v s1v Hs Hs64 Harr Hpa Hpa64 Hn Hret SOKp DJ R8 R16 R24 H2 H10 H9 H8.
    eexists. split.
    - stepST F_13f08 D_13f08 (Z_to_bv 64 (pa + 8)) (Z_to_bv 64 arr) ltac:(sok_in SOKp).
      stepb_ft F_13f0c D_13f0c ltac:(condZ).
      sn F_13f10 D_13f10.
      stepST F_13f14 D_13f14 (Z_to_bv 64 pa) (Z_to_bv 64 n) ltac:(sok_in SOKp).
      stepST F_13f18 D_13f18 (Z_to_bv 64 (pa + 4)) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      sn F_13f1c D_13f1c.
      stepLD8 F_13f5c D_13f5c ret.
      stepLD8 F_13f60 D_13f60 s0v.
      stepLD8 F_13f64 D_13f64 s1v.
      zv F_13f68 D_13f68 (Z_to_bv 64 s).
      stepret F_13f6c D_13f6c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End SegsD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ddF_out : forall m s ret regs (x : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 112 \/ s <= u x)%Z -> ddF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold ddF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

Lemma RECat_ddF : forall m s ret regs p fs, (112 <= s)%Z -> (s < 2 ^ 64)%Z -> RECat m p fs ->
  (p + Z.of_nat (flds_len fs) <= s - 112)%Z -> RECat (ddF m s ret regs) p fs.
Proof. intros m s ret regs p fs Hs Hs64 R Hp. apply (RECat_frame m _ p fs R). intros x Hx. apply ddF_out; lia. Qed.

Lemma dd_T2 : forall C m regs md1 (A1 : AS) (m1 : word -> option byte) r2 (s pp pa : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A1 m1 md1 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr r2 2 = Z_to_bv 64 (s - 112) -> getr r2 9 = Z_to_bv 64 pa -> getr r2 8 = Z_to_bv 64 pp -> getr r2 4 = Z_to_bv 64 0x31370 ->
  getr r2 3 = getr regs 3 ->
  dd_cells m1 s ret regs ->
  slotok C A1 s pp sb -> (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pa) ->
  live A1 (Z_to_bv 64 pa) = Some 16%Z -> live (c_A0 C) (Z_to_bv 64 pa) = None -> (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z ->
  (forall Af, sub_live Af A1 -> live Af (Z_to_bv 64 pa) = None -> POSTD C Af s pp m m1) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md1) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pa) = None -> (forall q, q <> Z_to_bv 64 pa -> live A' q = live A1 q) -> sub_live A' A1 ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A1 (m_vmmaps md1) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md1)) S) ->
  realizes SEGS (mkCfg (mkst r2 (0x14160 : word) m1 al_rom) md1) S.
Proof.
  intros C m regs md1 A1 m1 r2 s pp pa sb ret S CK HW1 Hs16 Hlo Hhi Hret H2 H4 R2 R9 R8 R4 R3 CE1 SL1 DISJ Lpa L0pa Hpa Hpa64 PRE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold ALLOC_STACK in Hlo.
  pose proof (slot_range C A1 m1 md1 s pp sb CK HW1 SL1 ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A1 m1 md1 s pp sb CK HW1 SL1 ltac:(lia)) as SW.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (DJ : (pp + 8 <= s - 112 \/ s <= pp)%Z) by lia.
  destruct (dd_D al_rom r2 m1 pa R9) as (r3 & RUN3 & Q10 & Q1 & Q9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
  assert (Q2 : getr r3 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (Q4 : getr r3 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
  replace (0x17454 : word) with (Z_to_bv 64 0x17454) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 m1 md1 r3 (Z_to_bv 64 pa) (Z_to_bv 64 0x14168) 16 (s - 112) S CK HW1 Q10 Lpa L0pa Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 HW2 CS2 Lpa2 LEQ2 PM2 HRT2.
  replace (Z_to_bv 64 0x14168) with (0x14168 : word) by (apply bv_eq; reflexivity).
  assert (SUB2 : sub_live A2 A1).
  { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 pa)) as [->|NE]; [congruence|]. rewrite <- (LEQ2 q NE). exact L. }
  assert (SL2 : slotok C A2 s pp sb).
  { apply (slot_keep C A1 A2 s pp sb SL1). intros p k E. apply LEQ2. exact (DISJ p k E). }
  pose proof (slot_sok C A2 m2 _ s pp sb CK HW2 SL2 ltac:(lia)) as SOKp. rewrite p8_segs in SOKp.
  assert (E8 : getr r4 8 = Z_to_bv 64 pp) by (csr; reflexivity).
  pose proof (dd_E al_rom r4 m2 pp ltac:(lia) ltac:(lia) SOKp E8) as RUN5.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  set (M3 := wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (HW3 : W C A2 M3 (with_vmmaps vm2 md1)).
  { subst M3. apply (slot_W C A2 m2 _ s pp sb _ CK HW2 SL2 ltac:(lia)). rewrite length_N_to_le_bytes. reflexivity. }
  assert (CE3 : dd_cells M3 s ret regs).
  { unfold dd_cells. apply (cellsZ_out m2 M3 pp (pp + 8)).
    - intros x Hx. subst M3. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - clear -DJ HsR. forall_cells.
    - apply (cellsZ_frm C (s - 112) m1 m2); [exact CK | exact (proj1 PM2) | lia | | exact CE1].
      clear -HsR. forall_cells. }
  assert (E2' : getr r4 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  destruct (dd_epi al_rom r4 M3 s ret regs ltac:(lia) ltac:(lia) Hret CE3 E2')
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN6 |].
  apply (HK A2 M3 vm2 r6 HW3).
  - apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?V27, ?H2; try reflexivity.
    + rewrite (AG6 3) by notin_lit. csr. reflexivity.
    + rewrite (AG6 4) by notin_lit. csr. reflexivity.
  - exact Lpa2.
  - exact LEQ2.
  - exact SUB2.
  - eapply POSTD_trans; [exact (PRE A2 SUB2 Lpa2)|].
    apply (POSTD_trans C A2 s pp m1 m2 M3); [apply (POSTD_of_POSTM C A2 A2); [eapply POSTM_mono; [|exact PM2]; lia | apply sub_live_refl]|].
    subst M3. apply POSTD_slotw; [rewrite length_N_to_le_bytes; reflexivity | lia | lia].
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma dd_T1 : forall C m regs mdx (Ax : AS) (mx : word -> option byte) rx (s pp pa na arr : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C Ax mx mdx ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr rx 2 = Z_to_bv 64 (s - 112) -> getr rx 1 = Z_to_bv 64 0x14160 -> getr rx 10 = Z_to_bv 64 arr ->
  getr rx 9 = Z_to_bv 64 pa -> getr rx 8 = Z_to_bv 64 pp -> getr rx 4 = Z_to_bv 64 0x31370 -> getr rx 3 = getr regs 3 ->
  dd_cells mx s ret regs ->
  slotok C Ax s pp sb -> (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pa /\ p <> Z_to_bv 64 arr) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  live Ax (Z_to_bv 64 pa) = Some 16%Z -> live (c_A0 C) (Z_to_bv 64 pa) = None -> (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z ->
  (0 <= arr < 2 ^ 64)%Z ->
  (arr = 0%Z \/ (live Ax (Z_to_bv 64 arr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\ (1 <= na)%Z /\ arr <> pa)) ->
  (forall Af, sub_live Af Ax -> live Af (Z_to_bv 64 pa) = None -> live Af (Z_to_bv 64 arr) = None -> POSTD C Af s pp m mx) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' mdx) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pa) = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 pa -> q <> Z_to_bv 64 arr -> live A' q = live Ax q) -> sub_live A' Ax ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr Ax (m_vmmaps mdx) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' mdx)) S) ->
  realizes SEGS (mkCfg (mkst rx (Z_to_bv 64 0x17454) mx al_rom) mdx) S.
Proof.
  intros C m regs mdx Ax mx rx s pp pa na arr sb ret S CK HWx Hs16 Hlo Hhi Hret H2 H4 R2 R1 R10 R9 R8 R4 R3 CEx SLx DISJ Z0
         Lpa L0pa Hpa Hpa64 Harr ARR PRE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold ALLOC_STACK in Hlo.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (NEpa : Z_to_bv 64 pa <> Z_to_bv 64 arr).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. destruct ARR as [-> | (_ & _ & _ & NE)]; lia. }
  assert (KONT : forall A1 m1 vm1 r2, W C A1 m1 (with_vmmaps vm1 mdx) -> cs_kept rx r2 ->
     live A1 (Z_to_bv 64 arr) = None -> (forall q, q <> Z_to_bv 64 arr -> live A1 q = live Ax q) -> sub_live A1 Ax ->
     POSTM C A1 (s - 112) mx m1 ->
     roomtr Ax (m_vmmaps mdx) A1 vm1 0 0 ->
     realizes SEGS (mkCfg (mkst r2 (Z_to_bv 64 0x14160) m1 al_rom) (with_vmmaps vm1 mdx)) S).
  { intros A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 SUB1 PM1 HRT1.
    assert (Lpa1 : live A1 (Z_to_bv 64 pa) = Some 16%Z) by (rewrite (LEQ1 _ NEpa); exact Lpa).
    replace (Z_to_bv 64 0x14160) with (0x14160 : word) by (apply bv_eq; reflexivity).
    apply (dd_T2 C m regs (with_vmmaps vm1 mdx) A1 m1 r2 s pp pa sb ret S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi Hret H2 H4);
      [csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | | | | exact Lpa1 | exact L0pa | exact Hpa | exact Hpa64 | |].
    - unfold dd_cells. apply (cellsZ_frm C (s - 112) mx m1); [exact CK | exact (proj1 PM1) | lia | | exact CEx].
      clear -HsR. forall_cells.
    - apply (slot_keep C Ax A1 s pp sb SLx). intros p k E. apply LEQ1. exact (proj2 (DISJ p k E)).
    - intros p k E. exact (proj1 (DISJ p k E)).
    - intros Af SUBf Lf.
      assert (Lfa : live Af (Z_to_bv 64 arr) = None).
      { destruct (live Af (Z_to_bv 64 arr)) as [k|] eqn:E; [|reflexivity]. pose proof (SUBf _ _ E). congruence. }
      eapply POSTD_trans; [apply PRE; [exact (sub_live_trans _ _ _ SUBf SUB1) | exact Lf | exact Lfa]|].
      apply (POSTD_of_POSTM C A1 Af); [eapply POSTM_mono; [|exact PM1]; lia | exact SUBf].
    - intros A' m' vm' regs' HW' CS' Lpa' LEQ' SUB' PD' RD' HRT'. rewrite with_vmmaps_twice in HW'. rewrite with_vmmaps_twice.
      apply (HK A' m' vm' regs' HW' CS' Lpa').
      + rewrite (LEQ' _ (not_eq_sym NEpa)). exact La1.
      + intros q N1 N2. rewrite (LEQ' q N1). exact (LEQ1 q N2).
      + exact (sub_live_trans _ _ _ SUB' SUB1).
      + exact PD'.
      + exact RD'.
      + room_tac. }
  destruct ARR as [Harr0 | (Larr & L0arr & Hna & NEarr)].
  - rewrite Harr0 in R10.
    apply (W_free0_8 C Ax mx mdx rx (Z_to_bv 64 0x14160) (s - 112) S CK HWx Z0 R10 R1 ltac:(red; apply bv_eq; reflexivity) R4 R2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r2 HW1 CS1 L01 LEQ1 PM1 HRT1. rewrite Harr0 in KONT.
    assert (SUB1 : sub_live A1 Ax).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE]; [congruence|]. rewrite <- (LEQ1 q NE). exact L. }
    apply (KONT A1 m1 vm1 r2 HW1 CS1 L01 LEQ1 SUB1); [exact (POSTM_sub C A1 Ax _ _ _ SUB1 PM1) | exact HRT1].
  - apply (W_free16 C Ax mx mdx rx (Z_to_bv 64 arr) (Z_to_bv 64 0x14160) (8 * na) (s - 112) S CK HWx R10 Larr L0arr R1
             ltac:(red; apply bv_eq; reflexivity) R4 R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 PM1 HRT1.
    assert (SUB1 : sub_live A1 Ax).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|NE]; [congruence|]. rewrite <- (LEQ1 q NE). exact L. }
    exact (KONT A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 SUB1 PM1 HRT1).
Qed.

Theorem l_dnaaDestroy_W : forall C A m md regs (s pp pa na arr : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pa) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  ptra_at C A m pa na arr ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pa /\ p <> Z_to_bv 64 arr) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pa) = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 pa -> q <> Z_to_bv 64 arr -> live A' q = live A q) -> sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14074 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pa na arr sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 SL Rpp Z0 PA DISJ HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold ALLOC_STACK in Hlo.
  destruct PA as (R & Lpa & L0pa & ARR).
  pose proof (PTRA_wf m pa na 0 arr R) as (Wna & _ & Warr & Wpa0 & Wpa).
  destruct (blk_range C A m md (Z_to_bv 64 pa) 16 CK HW Lpa ltac:(lia)) as [Gpa TOPpa]. rewrite u_Z2bv in Gpa, TOPpa by lia.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (DJ : (pp + 8 <= s - 112 \/ s <= pp)%Z) by lia.
  destruct (dd_A al_rom regs m s pp pa ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (ddF m s ret regs) md /\ POSTM C A s m (ddF m s ret regs)) by (unfold ddF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (R1 : RECat (ddF m s ret regs) pa (ptra_flds na 0 arr)) by (apply RECat_ddF; [lia | lia | exact R | cbn; lia]).
  destruct (dd_N al_rom r1 (ddF m s ret regs) pa na arr ltac:(lia) R1 Q9) as (r2 & RUN2 & P9 & P10 & P1 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  replace (0x17454 : word) with (Z_to_bv 64 0x17454) by (apply bv_eq; reflexivity).
  apply (dd_T1 C m regs md A (ddF m s ret regs) r2 s pp pa na arr sb ret S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi Hret H2 H4);
    [csr; reflexivity | exact P1 | exact P10 | exact P9 | csr; reflexivity | csr; reflexivity | csr; reflexivity
    | exact (ddF_cells m s ret regs ltac:(lia) ltac:(lia)) | exact SL | exact DISJ | exact Z0 | exact Lpa | exact L0pa | lia | lia | exact Warr | exact ARR | |].
  - intros Af SUBf _ _. exact (POSTD_of_POSTM C A Af s pp m _ PM1 SUBf).
  - exact HK.
Qed.

(* [comment removed for export] *)
Theorem l_dnaaDestroy_null_W : forall C A m md regs (s pp : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14074 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 112 \/ s <= pp)%Z) by lia.
  destruct (dd_A al_rom regs m s pp 0 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (ddF m s ret regs) md /\ POSTM C A s m (ddF m s ret regs)) by (unfold ddF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (dd_Z al_rom r1 _ Q9) |].
  destruct (dd_epi al_rom r1 (ddF m s ret regs) s ret regs ltac:(lia) ltac:(lia) Hret (ddF_cells m s ret regs ltac:(lia) ltac:(lia)) Q2)
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN6 |].
  apply (HK _ r6 HW1); [| exact PM1].
  apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?V27, ?H2; try reflexivity.
  - rewrite (AG6 3) by notin_lit. csr. reflexivity.
  - rewrite (AG6 4) by notin_lit. csr. reflexivity.
Qed.


Theorem l_dnaaCreate_sure_W : forall C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 1000000)%Z ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_naa <= kR)%Z -> (RB_naa n <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists pa arr : Z, getr regs' 10 = Z_to_bv 64 pa /\ ptra_new C A A' m' pa n arr) ->
     aroom A' vm' (kR - RK_naa) (bR - RB_naa n) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x13fc0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb HK.
  pose proof (alloc_margin_le (1 * 16)) as MG1. pose proof (alloc_margin_le (n * 8)) as MG2. unfold RK_naa in Hrk. unfold RB_naa in Hrb.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL8] in *. unfold LSF in *.
  assert (HsR : (0x52000 + 8192 <= s < 2 ^ 63)%Z) by lia.
  destruct (dc_A al_rom regs m s n ret ltac:(lia) ltac:(lia) Hn (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
  replace (0x1731c : word) with (Z_to_bv 64 0x1731c) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 16 kR bR (Z_to_bv 64 0x13ff8) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  replace (Z_to_bv 64 0x13ff8) with (0x13ff8 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r2 8 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E4a : getr r2 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R24 : rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  - (* [comment removed for export] *)
    assert (Hpa : (1 <= u res)%Z /\ (u res + 16 <= alloc_top (c_vm C))%Z).
    { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 16 + 15) / 16)%Z with 1%Z in TOP. lia. }
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
    set (pa := u res) in *. clearbody pa.
    rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (REC0 : RECat m1 pa (zflds [4; 4; 8]%nat)).
    { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
      unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
    destruct (dc_B al_rom r2 m1 s n pa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) E2a Hres E8a)
      as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (M2 := wbytes m1 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pa))).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
    { subst M2. apply (WP_win C A1 A m m1 _ _ _ s CK); [| exact SUBa | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
      split; [exact HWa | exact PMa']. }
    destruct WP2 as [HW2 PM2].
    assert (REC2 : RECat M2 pa (zflds [4; 4; 8]%nat)).
    { subst M2. apply RECat_out; [exact REC0 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (P4 : getr r3 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    replace (0x1731c : word) with (Z_to_bv 64 0x1731c) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A1 M2 _ r3 n 8 (kR - 1) (bR - alloc_margin (1 * 16)) (Z_to_bv 64 0x1400c) (s - 32) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact Hroom1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hroom2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x1400c) with (0x1400c : word) by (apply bv_eq; reflexivity).
    assert (F2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (F9 : getr r4 9 = Z_to_bv 64 pa) by (csr; reflexivity).
    assert (F8 : getr r4 8 = Z_to_bv 64 n) by (csr; reflexivity).
    assert (F4 : getr r4 4 = Z_to_bv 64 0x31370) by (csr; reflexivity).
    pose proof (blk_range C A1 M2 _ (Z_to_bv 64 pa) 16 CK HW2 L1 ltac:(lia)) as [Gpa _]. rewrite u_Z2bv in Gpa by lia.
    assert (REC4 : RECat m2 pa (zflds [4; 4; 8]%nat)).
    { apply (RECat_POSTM C A1 (s - 32) M2 m2 (Z_to_bv 64 pa) 16 _ _ REC2 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
    assert (SOKp2 : store_ok SEGS m2 (Z_to_bv 64 pa) 16 = true).
    { rewrite <- p8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 pa _ x REC4 ltac:(cbn; lia) E). }
    assert (S8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 8) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rdn_solve. }
    assert (S16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 16) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rdn_solve. }
    assert (S24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 24) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rdn_solve. }
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    + (* [comment removed for export] *)
      assert (Harr : (1 <= u res2)%Z /\ (u res2 + round16 (8 * n) <= alloc_top (c_vm C))%Z).
      { pose proof (u64_range res2). replace (n * 8)%Z with (8 * n)%Z in TOPb by lia. lia. }
      assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
      set (arr := u res2) in *. clearbody arr.
      rewrite Eres2 in Hres2, K0, K1, K00, KEQ.
      pose proof (round16_ge (8 * n) ltac:(lia)) as RG.
      assert (NE : arr <> pa).
      { intros E. rewrite E in K0. rewrite K0 in L1. discriminate L1. }
      destruct (dc_C al_rom r4 m2 s pa arr n ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKp2 ltac:(lia)
                  S8 S16 S24 F2 Hres2 F9 F8) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      set (M4 := wbytes (wbytes (wbytes m2 _ _) _ _) _ _).
      assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
      assert (Lpa2 : live A2 (Z_to_bv 64 pa) = Some 16%Z) by (rewrite (KEQ _ (zneq_w pa arr ltac:(lia) ltac:(lia) (not_eq_sym NE))); exact L1).
      assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A s m M4).
      { subst M4.
        do 3 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pa) _ 16); [exact CK | | exact Lpa2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
        split; [exact HWb | exact PMb']. }
      destruct WP4 as [HW4 PM4].
      apply (HK A2 M4 vm2 r5 HW4).
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; reflexivity.
      * exact PM4.
      * exists pa, arr. split; [exact V10|].
        split.
        { subst M4. unfold ptra_flds.
          eapply (REC_wr' _ _ [(4%nat, n); (4%nat, 0%Z); (8%nat, arr)] _ 1 4);
            [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
          eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr)] _ 0 4);
            [ | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ].
          eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 2 8);
            [ exact REC4 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
        split; [lia|]. split; [exact NE|].
        split; [exact L0|]. split; [rewrite <- (LEQ _ (zneq_w arr pa ltac:(lia) ltac:(lia) NE)); exact K0|].
        split; [exact L00|]. split; [exact K00|]. split; [exact Lpa2|]. split; [replace (8 * n)%Z with (n * 8)%Z by lia; exact K1|].
        intros q N1 N2; rewrite (KEQ q N2); exact (LEQ q N1).
      * unfold RK_naa, RB_naa. apply (aroom_mono A2 vm2 _ _ _ _ Hroom2); lia.
Qed.

(* [comment removed for export] *)
Theorem l_dnaaCreate_W : forall C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31370 ->
  getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 1000000)%Z ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_naa <= kR)%Z -> (RB_naa n <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pa arr : Z, getr regs' 10 = Z_to_bv 64 pa /\ ptra_new C A A' m' pa n arr) ) ->
     aroom A' vm' (kR - RK_naa) (bR - RB_naa n) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x13fc0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb HK.
  apply (l_dnaaCreate_sure_W C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' RES Hrm'. apply (HK A' m' vm' regs' HW' CS' PM'); [right; exact RES | exact Hrm'].
Qed.

End Ptra.
