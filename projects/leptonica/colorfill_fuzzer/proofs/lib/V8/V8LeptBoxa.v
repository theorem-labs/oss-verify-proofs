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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8CL8a.
Import V8CL8a.V8LeptBox.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8_code_13734_14000 V8_code_14000_15000 V8_code_17000_18000.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomCF.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition boxa_flds (n na rc arr : Z) : list fld := [(4%nat, n); (4%nat, na); (4%nat, rc); (4%nat, 0%Z); (8%nat, arr)].
(* [comment removed for export] *)
Definition box1_flds (x y w h : Z) : list fld := [(4%nat, x); (4%nat, y); (4%nat, w); (4%nat, h); (4%nat, 1%Z)].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma nclamp_ok : forall n, (1 <= n <= 10000000)%Z ->
  (zx (sw32 (n + 18446744073699551615)) <? zx 18446744073699551616)%Z = false.
Proof. intros n H. unfold zx, sw32. apply Z.ltb_ge. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Boxa.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma BOXA_rd_n : forall m ba n na rc arr, RECat m ba (boxa_flds n na rc arr) -> rdn SEGS m (Z_to_bv 64 ba) 4 = Some (Z_to_le_bytes 4 n).
Proof. intros m ba n na rc arr R. eapply (REC_rd' SEGS _ _ (boxa_flds n na rc arr) 0 4); [exact R | cbn; lia | reflexivity | cbn [fld_off boxa_flds Z.of_nat]; f_equal; lia | reflexivity]. Qed.
Lemma BOXA_rd_rc : forall m ba n na rc arr, RECat m ba (boxa_flds n na rc arr) -> rdn SEGS m (Z_to_bv 64 (ba + 8)) 4 = Some (Z_to_le_bytes 4 rc).
Proof. intros m ba n na rc arr R. eapply (REC_rd' SEGS _ _ (boxa_flds n na rc arr) 2 4); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma BOXA_rd_arr : forall m ba n na rc arr, RECat m ba (boxa_flds n na rc arr) -> rdn SEGS m (Z_to_bv 64 (ba + 16)) 8 = Some (Z_to_le_bytes 8 arr).
Proof. intros m ba n na rc arr R. eapply (REC_rd' SEGS _ _ (boxa_flds n na rc arr) 4 8); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma BOX1_rd_rc : forall m b x y w h, RECat m b (box1_flds x y w h) -> rdn SEGS m (Z_to_bv 64 (b + 16)) 4 = Some (Z_to_le_bytes 4 1).
Proof. intros m b x y w h R. eapply (REC_rd' SEGS _ _ (box1_flds x y w h) 4 4); [exact R | cbn; lia | reflexivity | reflexivity | reflexivity]. Qed.
Lemma BOXA_wf : forall m ba n na rc arr, RECat m ba (boxa_flds n na rc arr) ->
  (0 <= n < 2 ^ 32)%Z /\ (0 <= na < 2 ^ 32)%Z /\ (0 <= arr < 2 ^ 64)%Z /\ (0 <= ba)%Z /\ (ba + 24 < 2 ^ 64)%Z.
Proof. intros m ba n na rc arr (H0 & H1 & WF & _). cbn in H1, WF. lia. Qed.

Section Segs.
Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Definition bdF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
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
      (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)).

  (* [comment removed for export] *)
  Definition bd_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9); (s - 32, getr R 18); (s - 40, getr R 19);
              (s - 48, getr R 20); (s - 56, getr R 21); (s - 64, getr R 22); (s - 72, getr R 23);
              (s - 80, getr R 24); (s - 88, getr R 25); (s - 96, getr R 26)]%Z.

  Lemma bdF_cells : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> bd_cells (bdF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold bd_cells, bdF. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  (* [comment removed for export] *)
  Lemma bd_A : forall regs m (s pp v : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 v) -> (pp + 8 <= s - 96 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x14a20 : word) m rom) (mkst regs' (0x14a64 : word) (bdF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 8 = Z_to_bv 64 v /\ getr regs' 10 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [2; 8; 11]%list) regs regs'.
  Proof.
    intros regs m s pp v ret Hs Hs64 Hpp Hpp64 Hv ALpp SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_1491c D_1491c (Z_to_bv 64 (s - 96)).
      stepST F_14920 D_14920 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14924 D_14924 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14928 D_14928 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1492c D_1492c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_14930 D_14930 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_14934 D_14934 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_14938 D_14938 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_1493c D_1493c (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_14940 D_14940 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_14944 D_14944 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_14948 D_14948 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_1494c D_1494c (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepb_ft F_14950 D_14950 ltac:(condZ).
      zand F_14954 D_14954 andi_7 ALpp. stepb_ft F_14958 D_14958 ltac:(condZ).
      stepLD F_1495c D_1495c (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_epi : forall regs m (s : Z) (ret : word) (R : bvmap 5 word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> bd_cells m s ret R ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x14bb0 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = getr R 8 /\ getr regs' 9 = getr R 9 /\ getr regs' 18 = getr R 18 /\ getr regs' 19 = getr R 19
      /\ getr regs' 20 = getr R 20 /\ getr regs' 21 = getr R 21 /\ getr regs' 22 = getr R 22 /\ getr regs' 23 = getr R 23
      /\ getr regs' 24 = getr R 24 /\ getr regs' 25 = getr R 25 /\ getr regs' 26 = getr R 26
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s ret R Hs Hs64 Hret CE H2.
    destruct CE as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & _).
    eexists. split.
    - stepLD8 F_14aac D_14aac ret.
      stepLD8 F_14ab0 D_14ab0 (getr R 8).
      stepLD8 F_14ab4 D_14ab4 (getr R 9).
      stepLD8 F_14ab8 D_14ab8 (getr R 18).
      stepLD8 F_14abc D_14abc (getr R 19).
      stepLD8 F_14ac0 D_14ac0 (getr R 20).
      stepLD8 F_14ac4 D_14ac4 (getr R 21).
      stepLD8 F_14ac8 D_14ac8 (getr R 22).
      stepLD8 F_14acc D_14acc (getr R 23).
      stepLD8 F_14ad0 D_14ad0 (getr R 24).
      stepLD8 F_14ad4 D_14ad4 (getr R 25).
      stepLD8 F_14ad8 D_14ad8 (getr R 26).
      zv F_14adc D_14adc (Z_to_bv 64 s).
      stepret F_14ae0 D_14ae0 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_Z : forall regs m,
    getr regs 8 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x14a64 : word) m rom) (mkst regs (0x14bb0 : word) m rom).
  Proof. intros regs m H8. stepb_tk F_14960 D_14960 ltac:(condZ). apply mst_refl. Qed.

  (* [comment removed for export] *)
  Lemma bd_N : forall regs m (ba pp n na arr : Z),
    (ba mod 16 = 0)%Z -> (1 <= ba)%Z -> RECat m ba (boxa_flds n na 1 arr) -> (n < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 ba) 24 = true ->
    getr regs 8 = Z_to_bv 64 ba -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x14a64 : word) m rom)
                  (mkst regs' (0x14a8c : word) (wbytes m (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 8 = Z_to_bv 64 ba /\ getr regs' 19 = Z_to_bv 64 pp /\ getr regs' 10 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [10; 11; 12; 19]%list) regs regs'.
  Proof.
    intros regs m ba pp n na arr Hal Hba R Hn SOKb H8 H10. pose proof (BOXA_wf m ba n na 1 arr R) as (Wn & Wna & Warr & _ & Wba).
    assert (AL8 : (ba mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r ba); apply mod16_plus_mod8; [exact Hal | reflexivity]).
    eexists. split.
    - stepb_ft F_14960 D_14960 ltac:(condZ).
      zand F_14964 D_14964 andi_7 AL8. stepb_ft F_14968 D_14968 ltac:(condZ).
      zv F_1496c D_1496c (Z_to_bv 64 (ba + 8)).
      sn F_14970 D_14970.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_14974 eq_refl D_14974);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; exact (BOXA_rd_rc m ba n na 1 arr R)
          | apply lez4; lia
          | gres; sok_in SOKb ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 1) by lia.
      sn F_14978 D_14978.
      stepb_ft F_1497c D_1497c ltac:(condZ).
      sn F_14980 D_14980.
      stepLD F_14984 D_14984 (Z_to_le_bytes 4 n) (Z_to_bv 64 n)
        ltac:(addr_norm; repeat rdn_peel1; exact (BOXA_rd_n m ba n na 1 arr R)) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_B0 : forall regs m (ba arr : Z),
    (0 <= arr < 2 ^ 64)%Z -> (1 <= ba)%Z -> (ba + 24 < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (ba + 16)) 8 = Some (Z_to_le_bytes 8 arr) ->
    getr regs 8 = Z_to_bv 64 ba -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x14a8c : word) m rom) (mkst regs' (0x17c54 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 arr /\ getr regs' 1 = Z_to_bv 64 0x14ba0 /\ getr regs' 8 = Z_to_bv 64 ba
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m ba arr Harr Hba Hba64 Rarr H8 H10.
    eexists. split.
    - stepb_tk F_14988 D_14988 ltac:(condZ).
      stepLD F_14a94 D_14a94 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply lez8; lia).
      sn F_14a98 D_14a98.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_B1 : forall regs m (ba arr b0 na rc x y w h : Z),
    (1 <= arr)%Z -> (arr + 8 <= 2 ^ 64)%Z -> (1 <= ba)%Z -> (b0 mod 16 = 0)%Z -> (1 <= b0)%Z -> (arr mod 8 = 0)%Z ->
    RECat m ba (boxa_flds 1 na rc arr) -> RECat m b0 (box1_flds x y w h) ->
    rdn SEGS m (Z_to_bv 64 arr) 8 = Some (Z_to_le_bytes 8 b0) ->
    rdn SEGS m (Z_to_bv 64 0x207a0) 8 = Some (Z_to_le_bytes 8 0x21810) ->
    store_ok SEGS m (Z_to_bv 64 b0) 20 = true ->
    getr regs 8 = Z_to_bv 64 ba -> getr regs 10 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x14a8c : word) m rom)
                  (mkst regs' (0x17c54 : word) (wbytes m (Z_to_bv 64 (b0 + 16)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 10 = Z_to_bv 64 b0 /\ getr regs' 1 = Z_to_bv 64 0x14b20 /\ getr regs' 8 = Z_to_bv 64 ba
      /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0 /\ getr regs' 26 = Z_to_bv 64 arr
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 18; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m ba arr b0 na rc x y w h Harr Harr64 Hba Hal Hb0 ALarr R RB Rb0 Rg SOKb H8 H10.
    pose proof (BOXA_wf m ba 1 na rc arr R) as (_ & Wna & Warr & _ & Wba). pose proof (RECat_range m b0 _ RB) as [_ Wb0]. cbn in Wb0.
    assert (ALb4 : (b0 mod 4 = 0)%Z) by (rewrite <- (Z.add_0_r b0); apply mod16_plus_mod4; [exact Hal | reflexivity]).
    eexists. split.
    - stepb_ft F_14988 D_14988 ltac:(condZ).
      sn F_1498c D_1498c.
      sn F_14990 D_14990.
      sn F_14994 D_14994.
      sn F_14998 D_14998.
      sn F_1499c D_1499c.
      stepLD F_149a0 D_149a0 (Z_to_le_bytes 8 0x21810) (Z_to_bv 64 0x21810) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      sn F_149a4 D_149a4.
      sn F_149a8 D_149a8.
      sn F_149ac D_149ac.
      sn F_149b0 D_149b0.
      sn F_149b4 D_149b4.
      sn F_149b8 D_149b8.
      stepLD F_149d0 D_149d0 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact (BOXA_rd_arr m ba 1 na rc arr R)) ltac:(apply lez8; lia).
      zv F_149d4 D_149d4 (Z_to_bv 64 arr).                                             (* [comment removed for export] *)
      stepb_ft F_149d8 D_149d8 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_149dc D_149dc. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_149e0 D_149e0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_149e4 D_149e4 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_149e8 D_149e8 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_149ec D_149ec ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_149f0 D_149f0 (Z_to_bv 64 arr).                                             (* [comment removed for export] *)
      zand F_149f4 D_149f4 andi_7 ALarr. stepb_ft F_149f8 D_149f8 ltac:(condZ).
      stepLD F_149fc D_149fc (Z_to_le_bytes 8 b0) (Z_to_bv 64 b0) ltac:(addr_norm; exact Rb0) ltac:(apply lez8; lia).
      stepb_ft F_14a00 D_14a00 ltac:(condZ).
      zand F_14a04 D_14a04 andi_3 ALb4. stepb_ft F_14a08 D_14a08 ltac:(condZ).
      zv F_14a0c D_14a0c (Z_to_bv 64 (b0 + 16)).
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_14a10 eq_refl D_14a10);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; exact (BOX1_rd_rc m b0 x y w h RB)
          | apply lez4; lia
          | gres; sok_in SOKb ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 1) by lia.
      stepb_ft F_14a14 D_14a14 ltac:(condZ).
      sn F_14a18 D_14a18.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_C1 : forall regs m (ba arr na rc : Z),
    (1 <= arr)%Z -> (arr + 8 <= 2 ^ 64)%Z -> (1 <= ba)%Z ->
    RECat m ba (boxa_flds 1 na rc arr) -> (arr + 8 <= ba \/ ba + 24 <= arr)%Z ->
    store_ok SEGS m (Z_to_bv 64 arr) 8 = true ->
    getr regs 8 = Z_to_bv 64 ba -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 arr ->
    exists regs',
      msteps SEGS (mkst regs (0x14b20 : word) m rom)
                  (mkst regs' (0x17c54 : word) (wbytes m (Z_to_bv 64 arr) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 10 = Z_to_bv 64 arr /\ getr regs' 1 = Z_to_bv 64 0x14ba0 /\ getr regs' 8 = Z_to_bv 64 ba
      /\ regs_agree (fun r => In r [1; 10; 20; 21]%list) regs regs'.
  Proof.
    intros regs m ba arr na rc Harr Harr64 Hba R DJ SOKa H8 H20 H21 H26.
    pose proof (BOXA_wf m ba 1 na rc arr R) as (_ & Wna & Warr & _ & Wba).
    eexists. split.
    - sn F_14a1c D_14a1c.
      stepST F_149bc D_149bc (Z_to_bv 64 arr) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKa).
      stepLD F_149c0 D_149c0 (Z_to_le_bytes 4 1) (Z_to_bv 64 1)
        ltac:(addr_norm; repeat rdn_peel1; exact (BOXA_rd_n m ba 1 na rc arr R)) ltac:(apply lez4; lia).
      sn F_149c4 D_149c4.
      sn F_149c8 D_149c8.
      stepb_tk F_149cc D_149cc ltac:(condZ).
      stepLD F_14a94 D_14a94 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr)
        ltac:(addr_norm; repeat rdn_peel1; exact (BOXA_rd_arr m ba 1 na rc arr R)) ltac:(apply lez8; lia).
      sn F_14a98 D_14a98.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_D : forall regs m (ba : Z),
    getr regs 8 = Z_to_bv 64 ba ->
    exists regs',
      msteps SEGS (mkst regs (0x14ba0 : word) m rom) (mkst regs' (0x17c54 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 ba /\ getr regs' 1 = Z_to_bv 64 0x14ba8 /\ getr regs' 8 = Z_to_bv 64 ba
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m ba H8. eexists. split.
    - sn F_14a9c D_14a9c. sn F_14aa0 D_14aa0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_E : forall regs m (pp : Z),
    (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 19 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x14ba8 : word) m rom)
                  (mkst regs' (0x14bb0 : word) (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 10 = Z_to_bv 64 pp /\ getr regs' 2 = getr regs 2
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m pp Hpp Hpp64 SOKp H19. eexists. split.
    - sn F_14aa4 D_14aa4.
      stepST F_14aa8 D_14aa8 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKp).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ba_A : forall regs m (s n : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= n <= 10000000)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x1494c : word) m rom)
                  (mkst regs' (0x17b1c : word)
                     (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                             (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                             (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x1496c
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 24 /\ getr regs' 9 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n ret Hs Hs64 Hn SOK H2 H1 H10.
    eexists. split.
    - zv F_14848 D_14848 (Z_to_bv 64 (s - 32)).
      stepST F_1484c D_1484c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14850 D_14850 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14854 D_14854 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_14858 D_14858. sn F_1485c D_1485c. sn F_14860 D_14860. sn F_14864 D_14864.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma ba_B : forall regs m (s n ba : Z),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= n <= 10000000)%Z -> (1 <= ba)%Z -> (ba + 24 < 2 ^ 64)%Z -> (ba mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 ba) 24 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 ba -> getr regs 9 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x1496c : word) m rom)
                  (mkst regs' (0x17b1c : word)
                     (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
                             (Z_to_bv 64 ba) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (ba + 4)) (word_to_le_bytes 4 (Z_to_bv 64 n)))
                             (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x149bc
      /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 9 = Z_to_bv 64 n /\ getr regs' 8 = Z_to_bv 64 ba
      /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n ba Hs Hs64 Hn Hba Hba64 ALba SOK SOKb H2 H10 H9.
    eexists. split.
    - stepST F_14868 D_14868 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 ba) ltac:(sok_in SOK).
      stepb_ft F_1486c D_1486c ltac:(condZ).
      sn F_14870 D_14870.
      zand F_14874 D_14874 andi_7 ALba. stepb_ft F_14878 D_14878 ltac:(condZ).
      sn F_1487c D_1487c. sn F_14880 D_14880.
      sn F_14884 D_14884. fixv (Z_to_bv 64 (sw32 (n + 18446744073699551615))) ltac:(rewrite v_addw_Z; reflexivity).
      sn F_14888 D_14888.
      stepb_tk F_1488c D_1488c ltac:(pin; rewrite c_ltu_zx; apply nclamp_ok; lia).
      stepST F_14894 D_14894 (Z_to_bv 64 ba) (Z_to_bv 64 0) ltac:(sok_in SOKb).
      stepST F_14898 D_14898 (Z_to_bv 64 (ba + 4)) (Z_to_bv 64 n) ltac:(sok_in SOKb).
      stepfence F_1489c D_1489c.
      sn F_148a0 D_148a0.
      stepST F_148a4 D_148a4 (Z_to_bv 64 (ba + 8)) (Z_to_bv 64 1) ltac:(sok_in SOKb).
      stepfence F_148a8 D_148a8.
      sn F_148ac D_148ac. sn F_148b0 D_148b0. sn F_148b4 D_148b4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ba_C : forall regs m (s ba arr : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> (1 <= ba)%Z -> (ba + 24 < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 ba) 24 = true -> (ba + 24 <= s - 32 \/ s <= ba)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 8 = Z_to_bv 64 ba ->
    exists regs',
      msteps SEGS (mkst regs (0x149bc : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (ba + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 ba /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ba arr ret s0v s1v Hs Hs64 Harr Hba Hba64 Hret SOKb DJ R8 R16 R24 H2 H10 H8.
    eexists. split.
    - stepST F_148b8 D_148b8 (Z_to_bv 64 (ba + 16)) (Z_to_bv 64 arr) ltac:(sok_in SOKb).
      stepb_tk F_148bc D_148bc ltac:(condZ).
      sn F_14900 D_14900.
      stepLD8 F_14904 D_14904 ret.
      stepLD8 F_14908 D_14908 s0v.
      stepLD8 F_1490c D_1490c s1v.
      zv F_14910 D_14910 (Z_to_bv 64 s).
      stepret F_14914 D_14914 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition babF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  (* [comment removed for export] *)
  Lemma bab_T : forall regs m (s : Z) (ret s0v s1v s2v s3v : word) (msg : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 0x10c09 ->
    exists regs',
      msteps SEGS (mkst regs (0x14df8 : word) m rom) (mkst regs' (0x13e24 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10c09
      /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v msg Hs Hs64 R8 R16 R24 R32 R40 H2 H10 H11.
    eexists. split.
    - sn F_14cf4 D_14cf4.
      stepLD8 F_14cf8 D_14cf8 ret. stepLD8 F_14cfc D_14cfc s0v. stepLD8 F_14d00 D_14d00 s1v. stepLD8 F_14d04 D_14d04 s2v. stepLD8 F_14d08 D_14d08 s3v.
      zv F_14d0c D_14d0c (Z_to_bv 64 s).
      sn F_14d10 D_14d10.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bab_N1 : forall regs m (s : Z) (ret bx : word),
    (0x523f0 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 0x207a0) 8 = Some (Z_to_le_bytes 8 0x21810) ->
    rdn SEGS m (Z_to_bv 64 0x21810) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = bx ->
    exists regs',
      msteps SEGS (mkst regs (0x14bec : word) m rom) (mkst regs' (0x14df8 : word) (babF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 0x10539 /\ getr regs' 11 = Z_to_bv 64 0x10c09
      /\ regs_agree (fun r => In r [2; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s ret bx Hs Hs64 SOK Rg Rs H2 H1 H10 H11.
    eexists. split.
    - zv F_14ae8 D_14ae8 (Z_to_bv 64 (s - 48)).
      stepST F_14aec D_14aec (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14af0 D_14af0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14af4 D_14af4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_14af8 D_14af8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_14afc D_14afc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_tk F_14b00 D_14b00 ltac:(condZ).
      sn F_14b7c D_14b7c.
      stepLD F_14b80 D_14b80 (Z_to_le_bytes 8 0x21810) (Z_to_bv 64 0x21810) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply lez8; lia).
      stepLD F_14b84 D_14b84 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply lez4; lia).
      sn F_14b88 D_14b88.
      stepb_ft F_14b8c D_14b8c ltac:(condZ).
      sn F_14b90 D_14b90. sn F_14b94 D_14b94. sn F_14b98 D_14b98. sn F_14b9c D_14b9c. sn F_14ba0 D_14ba0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bab_N2 : forall regs m (s ba : Z) (ret : word),
    (0x523f0 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= ba < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 0x207a0) 8 = Some (Z_to_le_bytes 8 0x21810) ->
    rdn SEGS m (Z_to_bv 64 0x21810) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 ba -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x14bec : word) m rom) (mkst regs' (0x14df8 : word) (babF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 0x10bf9 /\ getr regs' 11 = Z_to_bv 64 0x10c09
      /\ regs_agree (fun r => In r [2; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s ba ret Hs Hs64 Hba SOK Rg Rs H2 H1 H10 H11.
    eexists. split.
    - zv F_14ae8 D_14ae8 (Z_to_bv 64 (s - 48)).
      stepST F_14aec D_14aec (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14af0 D_14af0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14af4 D_14af4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_14af8 D_14af8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_14afc D_14afc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_14b00 D_14b00 ltac:(condZ).
      stepb_tk F_14b04 D_14b04 ltac:(condZ).
      sn F_14ba4 D_14ba4.
      stepLD F_14ba8 D_14ba8 (Z_to_le_bytes 8 0x21810) (Z_to_bv 64 0x21810) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply lez8; lia).
      stepLD F_14bac D_14bac (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply lez4; lia).
      sn F_14bb0 D_14bb0.
      stepb_ft F_14bb4 D_14bb4 ltac:(condZ).
      sn F_14bb8 D_14bb8. sn F_14bbc D_14bbc. sn F_14bc0 D_14bc0. sn F_14bc4 D_14bc4. sn F_14bc8 D_14bc8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bab_B : forall regs m (s ba bx n na rc arr : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= ba)%Z -> (1 <= bx < 2 ^ 64)%Z -> (0 <= n < na)%Z -> (na < 2 ^ 31)%Z -> (1 <= arr)%Z -> (arr + 8 * na <= 2 ^ 64)%Z ->
    ret_ok ret -> (ba mod 8 = 0)%Z -> (arr mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> RECat m ba (boxa_flds n na rc arr) ->
    (ba + 24 <= s - 48)%Z -> (arr + 8 * na <= s - 48)%Z -> (arr + 8 * na <= ba \/ ba + 24 <= arr)%Z ->
    store_ok SEGS m (Z_to_bv 64 (arr + 8 * n)) 8 = true -> store_ok SEGS m (Z_to_bv 64 ba) 4 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 ba -> getr regs 11 = Z_to_bv 64 bx -> getr regs 12 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x14bec : word) m rom)
                  (mkst regs' ret (wbytes (wbytes (babF m s ret regs) (Z_to_bv 64 (arr + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 bx)))
                                          (Z_to_bv 64 ba) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ba bx n na rc arr ret Hs Hs64 Hba Hbx Hn Hna Harr Harr64 Hret ALba ALarr SOK R D1 D2 D3 SOKa SOKb H2 H1 H10 H11 H12.
    pose proof (BOXA_wf m ba n na rc arr R) as (Wn & Wna & Warr & _ & Wba).
    assert (ALan : ((arr + 8 * n) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALarr).
    assert (R' : RECat (babF m s ret regs) ba (boxa_flds n na rc arr)).
    { unfold babF. repeat (apply RECat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact R. }
    eexists. split.
    - zv F_14ae8 D_14ae8 (Z_to_bv 64 (s - 48)).
      stepST F_14aec D_14aec (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14af0 D_14af0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14af4 D_14af4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_14af8 D_14af8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_14afc D_14afc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_14b00 D_14b00 ltac:(condZ).
      stepb_ft F_14b04 D_14b04 ltac:(condZ).
      stepb_tk F_14b08 D_14b08 ltac:(condZ).
      change (wbytes (wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) _ _) _ _) with (babF m s ret regs).
      zand F_14be0 D_14be0 andi_7 ALba. stepb_ft F_14be4 D_14be4 ltac:(condZ).        (* [comment removed for export] *)
      stepLD F_14be8 D_14be8 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact (BOXA_rd_n _ ba n na rc arr R')) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepLD F_14bec D_14bec (Z_to_le_bytes 4 na) (Z_to_bv 64 na)
        ltac:(addr_norm; eapply (REC_rd' SEGS _ _ (boxa_flds n na rc arr) 1 4); [exact R' | cbn; lia | reflexivity | reflexivity | reflexivity]) ltac:(apply lez4; lia).
      rewrite (v_lw_small na) by lia.
      stepb_tk F_14bf0 D_14bf0 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_14c7c D_14c7c (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact (BOXA_rd_arr _ ba n na rc arr R')) ltac:(apply lez8; lia).
      stepiv F_14c80 D_14c80 (Z_to_bv 64 (8 * n)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
      zv F_14c84 D_14c84 (Z_to_bv 64 (arr + 8 * n)).                                   (* [comment removed for export] *)
      sn F_14c88 D_14c88. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_14c8c D_14c8c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      stepb_ft F_14c90 D_14c90 ltac:(condZ).                                          (* [comment removed for export] *)
      stepat F_14c94 D_14c94 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_sltu_ge; lia).     (* [comment removed for export] *)
      stepat F_14c98 D_14c98 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_slti0; lia).       (* [comment removed for export] *)
      zlit F_14c9c D_14c9c (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      zlit F_14ca0 D_14ca0 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_14ca4 D_14ca4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_14ca8 D_14ca8 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_14cac D_14cac andi_7 ALan. stepb_ft F_14cb0 D_14cb0 ltac:(condZ).        (* [comment removed for export] *)
      stepLD F_14cb4 D_14cb4 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; exact (BOXA_rd_n _ ba n na rc arr R')) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepiv F_14cb8 D_14cb8 (Z_to_bv 64 (n + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepST F_14cbc D_14cbc (Z_to_bv 64 (arr + 8 * n)) (Z_to_bv 64 bx) ltac:(sok_in SOKa).
      stepb_ft F_14cc0 D_14cc0 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_14cc4 D_14cc4.
      stepST F_14cc8 D_14cc8 (Z_to_bv 64 ba) (Z_to_bv 64 (n + 1)) ltac:(sok_in SOKb).
      sn F_14ccc D_14ccc. sn F_14d14 D_14d14.
      unfold babF.
      stepLD8 F_14d18 D_14d18 ret. stepLD8 F_14d1c D_14d1c (getr regs 8). stepLD8 F_14d20 D_14d20 (getr regs 9).
      stepLD8 F_14d24 D_14d24 (getr regs 18). stepLD8 F_14d28 D_14d28 (getr regs 19).
      zv F_14d2c D_14d2c (Z_to_bv 64 s).
      stepret F_14d30 D_14d30 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bdF_out : forall m s ret regs (x : word), (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 96 \/ s <= u x)%Z -> bdF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold bdF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

Lemma RECat_bdF : forall m s ret regs p fs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> RECat m p fs ->
  (p + Z.of_nat (flds_len fs) <= s - 96)%Z -> RECat (bdF m s ret regs) p fs.
Proof. intros m s ret regs p fs Hs Hs64 R Hp. apply (RECat_frame m _ p fs R). intros x Hx. apply bdF_out; lia. Qed.

Lemma rdn_bdF : forall m s ret regs (a : Z) (k : nat), (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a < 2 ^ 64)%Z ->
  (a + Z.of_nat k <= s - 96 \/ (s <= a /\ a + Z.of_nat k <= 2 ^ 64))%Z ->
  rdn SEGS (bdF m s ret regs) (Z_to_bv 64 a) k = rdn SEGS m (Z_to_bv 64 a) k.
Proof.
  intros m s ret regs a k Hs Hs64 Ha Hk. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply bdF_out; lia.
Qed.

Lemma W_free0_8 : forall C A m md regs (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
      live A' (Z_to_bv 64 0) = None -> (forall q, q <> Z_to_bv 64 0 -> live A' q = live A q) -> POSTM C A s m m' ->
      roomtr A (m_vmmaps md) A' vm' 0 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x17c54) m al_rom) md) S.
Proof. intros until S. rewrite <- pu8_segs, <- pu8_free, <- pu8_tp. exact (W_free0_l C A m md regs ret s S). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bd_T2 : forall C m regs md1 (A1 : AS) (m1 : word -> option byte) r2 (s pp ba : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A1 m1 md1 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr r2 2 = Z_to_bv 64 (s - 96) -> getr r2 8 = Z_to_bv 64 ba -> getr r2 19 = Z_to_bv 64 pp -> getr r2 4 = Z_to_bv 64 0x31b70 ->
  getr r2 3 = getr regs 3 -> getr r2 27 = getr regs 27 ->
  bd_cells m1 s ret regs ->
  slotok C A1 s pp sb -> (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 ba) ->
  live A1 (Z_to_bv 64 ba) = Some 24%Z -> live (c_A0 C) (Z_to_bv 64 ba) = None -> (1 <= ba)%Z -> (ba + 24 < 2 ^ 64)%Z ->
  (forall Af, sub_live Af A1 -> live Af (Z_to_bv 64 ba) = None -> POSTD C Af s pp m m1) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md1) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 ba) = None -> (forall q, q <> Z_to_bv 64 ba -> live A' q = live A1 q) -> sub_live A' A1 ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A1 (m_vmmaps md1) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md1)) S) ->
  realizes SEGS (mkCfg (mkst r2 (0x14ba0 : word) m1 al_rom) md1) S.
Proof.
  intros C m regs md1 A1 m1 r2 s pp ba sb ret S CK HW1 Hs16 Hlo Hhi Hret H2 H4 R2 R8 R19 R4 R3 R27 CE1 SL1 DISJ Lba L0ba Hba Hba64 PRE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold ALLOC_STACK in Hlo.
  pose proof (slot_range C A1 m1 md1 s pp sb CK HW1 SL1 ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A1 m1 md1 s pp sb CK HW1 SL1 ltac:(lia)) as SW.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (DJ : (pp + 8 <= s - 96 \/ s <= pp)%Z) by lia.
  destruct (bd_D al_rom r2 m1 ba R8) as (r3 & RUN3 & Q10 & Q1 & Q8 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
  assert (Q2 : getr r3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (Q4 : getr r3 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  replace (0x17c54 : word) with (Z_to_bv 64 0x17c54) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 m1 md1 r3 (Z_to_bv 64 ba) (Z_to_bv 64 0x14ba8) 24 (s - 96) S CK HW1 Q10 Lba L0ba Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 HW2 CS2 Lba2 LEQ2 PM2 HRT2.
  replace (Z_to_bv 64 0x14ba8) with (0x14ba8 : word) by (apply bv_eq; reflexivity).
  assert (SUB2 : sub_live A2 A1).
  { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 ba)) as [->|NE]; [congruence|]. rewrite <- (LEQ2 q NE). exact L. }
  assert (SL2 : slotok C A2 s pp sb).
  { apply (slot_keep C A1 A2 s pp sb SL1). intros p k E. apply LEQ2. exact (DISJ p k E). }
  pose proof (slot_sok C A2 m2 _ s pp sb CK HW2 SL2 ltac:(lia)) as SOKp. rewrite pu8_segs in SOKp.
  assert (E19 : getr r4 19 = Z_to_bv 64 pp) by (csr; reflexivity).
  destruct (bd_E al_rom r4 m2 pp ltac:(lia) ltac:(lia) SOKp E19) as (r5 & RUN5 & P10 & P2 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  set (M3 := wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (HW3 : W C A2 M3 (with_vmmaps vm2 md1)).
  { subst M3. apply (slot_W C A2 m2 _ s pp sb _ CK HW2 SL2 ltac:(lia)). rewrite length_N_to_le_bytes. reflexivity. }
  assert (CE3 : bd_cells M3 s ret regs).
  { unfold bd_cells. apply (cellsZ_out m2 M3 pp (pp + 8)).
    - intros x Hx. subst M3. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - clear -DJ HsR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - apply (cellsZ_frm C (s - 96) m1 m2); [exact CK | exact (proj1 PM2) | lia | | exact CE1].
      clear -HsR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (E2' : getr r5 2 = Z_to_bv 64 (s - 96)) by (rewrite P2; csr; reflexivity).
  destruct (bd_epi al_rom r5 M3 s ret regs ltac:(lia) ltac:(lia) Hret CE3 E2')
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN6 |].
  apply (HK A2 M3 vm2 r6 HW3).
  - apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?H2; try reflexivity.
    + rewrite (AG6 3) by notin_lit. rewrite (AG5 3) by notin_lit. csr. reflexivity.
    + rewrite (AG6 4) by notin_lit. rewrite (AG5 4) by notin_lit. csr. reflexivity.
    + rewrite (AG6 27) by notin_lit. rewrite (AG5 27) by notin_lit. csr. reflexivity.
  - exact Lba2.
  - exact LEQ2.
  - exact SUB2.
  - eapply POSTD_trans; [exact (PRE A2 SUB2 Lba2)|].
    eapply POSTD_trans; [apply (POSTD_of_POSTM C A2 A2); [eapply POSTM_mono; [|exact PM2]; lia | apply sub_live_refl]|].
    subst M3. apply POSTD_slotw; [rewrite length_N_to_le_bytes; reflexivity | lia | lia].
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma bd_T1 : forall C m regs mdx (Ax : AS) (mx : word -> option byte) rx (s pp ba na arr : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C Ax mx mdx ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr rx 2 = Z_to_bv 64 (s - 96) -> getr rx 1 = Z_to_bv 64 0x14ba0 -> getr rx 10 = Z_to_bv 64 arr ->
  getr rx 8 = Z_to_bv 64 ba -> getr rx 19 = Z_to_bv 64 pp -> getr rx 4 = Z_to_bv 64 0x31b70 ->
  getr rx 3 = getr regs 3 -> getr rx 27 = getr regs 27 ->
  bd_cells mx s ret regs ->
  slotok C Ax s pp sb -> (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 ba /\ p <> Z_to_bv 64 arr) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  live Ax (Z_to_bv 64 ba) = Some 24%Z -> live (c_A0 C) (Z_to_bv 64 ba) = None -> (1 <= ba)%Z -> (ba + 24 < 2 ^ 64)%Z ->
  (0 <= arr < 2 ^ 64)%Z ->
  (arr = 0%Z \/ (live Ax (Z_to_bv 64 arr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\ arr <> ba)) ->
  (forall Af, sub_live Af Ax -> live Af (Z_to_bv 64 ba) = None -> live Af (Z_to_bv 64 arr) = None -> POSTD C Af s pp m mx) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' mdx) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 ba) = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 arr -> live A' q = live Ax q) -> sub_live A' Ax ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr Ax (m_vmmaps mdx) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' mdx)) S) ->
  realizes SEGS (mkCfg (mkst rx (Z_to_bv 64 0x17c54) mx al_rom) mdx) S.
Proof.
  intros C m regs mdx Ax mx rx s pp ba na arr sb ret S CK HWx Hs16 Hlo Hhi Hret H2 H4 R2 R1 R10 R8 R19 R4 R3 R27 CEx SLx DISJ Z0
         Lba L0ba Hba Hba64 Harr ARR PRE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold ALLOC_STACK in Hlo.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (NEba : Z_to_bv 64 ba <> Z_to_bv 64 arr).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. destruct ARR as [-> | (_ & _ & NE)]; lia. }
  assert (KONT : forall A1 m1 vm1 r2, W C A1 m1 (with_vmmaps vm1 mdx) -> cs_kept rx r2 ->
     live A1 (Z_to_bv 64 arr) = None -> (forall q, q <> Z_to_bv 64 arr -> live A1 q = live Ax q) -> sub_live A1 Ax ->
     POSTM C A1 (s - 96) mx m1 ->
     roomtr Ax (m_vmmaps mdx) A1 vm1 0 0 ->
     realizes SEGS (mkCfg (mkst r2 (Z_to_bv 64 0x14ba0) m1 al_rom) (with_vmmaps vm1 mdx)) S).
  { intros A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 SUB1 PM1 HRT1.
    assert (Lba1 : live A1 (Z_to_bv 64 ba) = Some 24%Z) by (rewrite (LEQ1 _ NEba); exact Lba).
    replace (Z_to_bv 64 0x14ba0) with (0x14ba0 : word) by (apply bv_eq; reflexivity).
    apply (bd_T2 C m regs (with_vmmaps vm1 mdx) A1 m1 r2 s pp ba sb ret S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi Hret H2 H4);
      [csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity | | | | exact Lba1 | exact L0ba | exact Hba | exact Hba64 | |].
    - unfold bd_cells. apply (cellsZ_frm C (s - 96) mx m1); [exact CK | exact (proj1 PM1) | lia | | exact CEx].
      clear -HsR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - apply (slot_keep C Ax A1 s pp sb SLx). intros p k E. apply LEQ1. exact (proj2 (DISJ p k E)).
    - intros p k E. exact (proj1 (DISJ p k E)).
    - intros Af SUBf Lf.
      assert (Lfa : live Af (Z_to_bv 64 arr) = None).
      { destruct (live Af (Z_to_bv 64 arr)) as [k|] eqn:E; [|reflexivity]. pose proof (SUBf _ _ E). congruence. }
      eapply POSTD_trans; [apply PRE; [exact (sub_live_trans _ _ _ SUBf SUB1) | exact Lf | exact Lfa]|].
      apply (POSTD_of_POSTM C A1 Af); [eapply POSTM_mono; [|exact PM1]; lia | exact SUBf].
    - intros A' m' vm' regs' HW' CS' Lba' LEQ' SUB' PD' RD' HRT'. rewrite with_vmmaps_twice in HW'. rewrite with_vmmaps_twice.
      apply (HK A' m' vm' regs' HW' CS' Lba').
      + rewrite (LEQ' _ (not_eq_sym NEba)). exact La1.
      + intros q N1 N2. rewrite (LEQ' q N1). exact (LEQ1 q N2).
      + exact (sub_live_trans _ _ _ SUB' SUB1).
      + exact PD'.
      + exact RD'.
      + room_tac. }
  destruct ARR as [Harr0 | (Larr & L0arr & NEarr)].
  - (* [comment removed for export] *)
    rewrite Harr0 in R10.
    apply (W_free0_8 C Ax mx mdx rx (Z_to_bv 64 0x14ba0) (s - 96) S CK HWx Z0 R10 R1 ltac:(red; apply bv_eq; reflexivity) R4 R2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r2 HW1 CS1 L01 LEQ1 PM1 HRT1. rewrite Harr0 in KONT.
    assert (SUB1 : sub_live A1 Ax).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE]; [congruence|]. rewrite <- (LEQ1 q NE). exact L. }
    apply (KONT A1 m1 vm1 r2 HW1 CS1 L01 LEQ1 SUB1); [exact (POSTM_sub C A1 Ax _ _ _ SUB1 PM1) | exact HRT1].
  - (* [comment removed for export] *)
    apply (W_free16 C Ax mx mdx rx (Z_to_bv 64 arr) (Z_to_bv 64 0x14ba0) (8 * na) (s - 96) S CK HWx R10 Larr L0arr R1
             ltac:(red; apply bv_eq; reflexivity) R4 R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 PM1 HRT1.
    assert (SUB1 : sub_live A1 Ax).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|NE]; [congruence|]. rewrite <- (LEQ1 q NE). exact L. }
    exact (KONT A1 m1 vm1 r2 HW1 CS1 La1 LEQ1 SUB1 PM1 HRT1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition box1_at (C : lctx) (A : AS) (m : word -> option byte) (b : Z) : Prop :=
  (exists x y w h, RECat m b (box1_flds x y w h)) /\ (b mod 16 = 0)%Z /\
  live A (Z_to_bv 64 b) = Some 20%Z /\ live (c_A0 C) (Z_to_bv 64 b) = None.

(* [comment removed for export] *)
Definition boxa_at (C : lctx) (A : AS) (m : word -> option byte) (ba n na arr b0 : Z) : Prop :=
  RECat m ba (boxa_flds n na 1 arr) /\ (ba mod 16 = 0)%Z /\
  live A (Z_to_bv 64 ba) = Some 24%Z /\ live (c_A0 C) (Z_to_bv 64 ba) = None /\
  ( (arr = 0%Z /\ n = 0%Z)
  \/ (live A (Z_to_bv 64 arr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\ (1 <= na)%Z /\ arr <> ba /\
      (n = 0%Z \/ (n = 1%Z /\ rdn SEGS m (Z_to_bv 64 arr) 8 = Some (Z_to_le_bytes 8 b0) /\ box1_at C A m b0 /\ b0 <> ba /\ b0 <> arr)))).

Local Ltac forall_cells := repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

Theorem boxaDestroy_W : forall C A m md regs (s pp ba n na arr b0 : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 ba) ->
  live (c_A0 C) (Z_to_bv 64 0) = None ->
  boxa_at C A m ba n na arr b0 ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 ba /\ p <> Z_to_bv 64 arr /\ (n = 1%Z -> p <> Z_to_bv 64 b0)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 ba) = None -> live A' (Z_to_bv 64 arr) = None -> (n = 1%Z -> live A' (Z_to_bv 64 b0) = None) ->
     (forall q, q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 arr -> (n = 1%Z -> q <> Z_to_bv 64 b0) -> live A' q = live A q) ->
     sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14a20 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp ba n na arr b0 sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 SL ALpp Rpp Z0 BA DISJ HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold ALLOC_STACK in Hlo.
  destruct BA as (R & Hal & Lba & L0ba & ARR).
  pose proof (BOXA_wf m ba n na 1 arr R) as (Wn & Wna & Warr & Wba0 & Wba).
  destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Gba TOPba]. rewrite u_Z2bv in Gba, TOPba by lia.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (HsR : (4200 <= s < 2 ^ 63)%Z) by lia.
  assert (DJ : (pp + 8 <= s - 96 \/ s <= pp)%Z) by lia.
  assert (Hn : (n = 0 \/ n = 1)%Z) by (destruct ARR as [[_ ->]|(_ & _ & _ & _ & [->|[-> _]])]; lia).
  (* [comment removed for export] *)
  destruct (bd_A al_rom regs m s pp ba ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
              (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (bdF m s ret regs) md /\ POSTM C A s m (bdF m s ret regs)) by (unfold bdF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  (* [comment removed for export] *)
  assert (R1 : RECat (bdF m s ret regs) ba (boxa_flds n na 1 arr)) by (apply RECat_bdF; [lia | lia | exact R | cbn; lia]).
  assert (SOKba : store_ok SEGS (bdF m s ret regs) (Z_to_bv 64 ba) 24 = true).
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (bdF m s ret regs x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined _ ba _ x R1 ltac:(cbn; lia) E). }
  destruct (bd_N al_rom r1 (bdF m s ret regs) ba pp n na arr Hal ltac:(lia) R1 ltac:(lia) SOKba Q8 Q10) as (r2 & RUN2 & P8 & P19 & P10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes (bdF m s ret regs) (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (HW2 : W C A M2 md).
  { subst M2. apply (W_store_blk C A _ md (Z_to_bv 64 ba) _ 24 _ CK HW1 Lba L0ba); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (R2 : RECat M2 ba (boxa_flds n na 0 arr)).
  { subst M2. eapply (REC_wr' _ _ (boxa_flds n na 1 arr) _ 2 4); [exact R1 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity]. }
  assert (CE2 : bd_cells M2 s ret regs).
  { unfold bd_cells. apply (cellsZ_out (bdF m s ret regs) M2 ba (ba + 24)).
    - intros x Hx. subst M2. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - clear -HsR TOPba T1 Hlo PIN7. forall_cells.
    - exact (bdF_cells m s ret regs ltac:(lia) ltac:(lia)). }
  assert (PRE2 : forall Af, sub_live Af A -> live Af (Z_to_bv 64 ba) = None -> POSTD C Af s pp m M2).
  { intros Af SUBf Lf. eapply POSTD_trans; [exact (POSTD_of_POSTM C A Af s pp m _ PM1 SUBf)|].
    subst M2. apply (POSTD_deadw C A Af _ md (Z_to_bv 64 ba) _ 24 _ s pp CK HW1 Lba Lf SUBf); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (P2 : getr r2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (P4 : getr r2 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  assert (P3 : getr r2 3 = getr regs 3) by (csr; reflexivity).
  assert (P27 : getr r2 27 = getr regs 27) by (csr; reflexivity).
  (* [comment removed for export] *)
  assert (K0 : n = 0%Z ->
    (arr = 0%Z \/ (live A (Z_to_bv 64 arr) = Some (8 * na)%Z /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\ arr <> ba)) ->
    realizes SEGS (mkCfg (mkst r2 (0x14a8c : word) M2 al_rom) md) S).
  { intros Hn0 ARR0. subst n.
    destruct (bd_B0 al_rom r2 M2 ba arr Warr ltac:(lia) ltac:(lia) (BOXA_rd_arr M2 ba 0 na 0 arr R2) P8 P10) as (r3 & RUN3 & U10 & U1 & U8 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    replace (0x17c54 : word) with (Z_to_bv 64 0x17c54) by (apply bv_eq; reflexivity).
    apply (bd_T1 C m regs md A M2 r3 s pp ba na arr sb ret S CK HW2 Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi Hret H2 H4);
      [csr; reflexivity | exact U1 | exact U10 | exact U8 | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity
      | exact CE2 | exact SL | | exact Z0 | exact Lba | exact L0ba | lia | lia | exact Warr | exact ARR0 | |].
    - intros p k E. pose proof (DISJ p k E) as (D1 & D2 & _). split; assumption.
    - intros Af SUBf Lf _. exact (PRE2 Af SUBf Lf).
    - intros A' m' vm' regs' HW' CS' L1 L2 LEQ SUB PD RD HRT'.
      apply (HK A' m' vm' regs' HW' CS' L1 L2); [intros E; discriminate E | | exact SUB | exact PD | exact RD | room_tac].
      intros q N1 N2 _. exact (LEQ q N1 N2). }
  destruct ARR as [[Harr0 Hn0] | (Larr & L0arr & Hna & NEarr & NB)].
  { apply (K0 Hn0). left. exact Harr0. }
  destruct (blk_range C A m md (Z_to_bv 64 arr) (8 * na) CK HW Larr ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Larr) as (_ & ALarr16 & _). rewrite u_Z2bv in ALarr16 by lia.
  assert (ALarr : (arr mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r arr); apply mod16_plus_mod8; [exact ALarr16 | reflexivity]).
  destruct NB as [Hn0 | (Hn1 & Rb0 & (BX & Halb & Lb0 & L0b0) & NE1 & NE2)].
  { apply (K0 Hn0). right. split; [exact Larr | split; [exact L0arr | exact NEarr]]. }
  (* [comment removed for export] *)
  clear K0. subst n. destruct BX as (x & y & w & h & RB).
  pose proof (RECat_range m b0 _ RB) as [Wb00 Wb0]. cbn in Wb0.
  destruct (blk_range C A m md (Z_to_bv 64 b0) 20 CK HW Lb0 ltac:(lia)) as [Gb0 TOPb0]. rewrite u_Z2bv in Gb0, TOPb0 by lia.
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lba Lb0 (zneq_w ba b0 ltac:(lia) ltac:(lia) (not_eq_sym NE1))) as Dab.
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lba Larr (zneq_w ba arr ltac:(lia) ltac:(lia) (not_eq_sym NEarr))) as Daa.
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Larr Lb0 (zneq_w arr b0 ltac:(lia) ltac:(lia) (not_eq_sym NE2))) as Dab0.
  rewrite !u_Z2bv in Dab, Daa, Dab0 by lia. change (round16 24) with 32%Z in *. change (round16 20) with 32%Z in *.
  pose proof (round16_ge (8 * na) ltac:(lia)) as RG.
  assert (RB2 : RECat M2 b0 (box1_flds x y w h)).
  { subst M2. apply RECat_out; [apply RECat_bdF; [lia | lia | exact RB | cbn; lia] | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (Rb0' : rdn SEGS M2 (Z_to_bv 64 arr) 8 = Some (Z_to_le_bytes 8 b0)).
  { subst M2. rewrite rdn_wbytes_out_Z by (zlen; lia). rewrite rdn_bdF by lia. exact Rb0. }
  assert (SOKb0 : store_ok SEGS M2 (Z_to_bv 64 b0) 20 = true).
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x0 Hx. cbn in Hx.
    unfold wview. destruct (M2 x0) eqn:E; [discriminate|]. exfalso. exact (RECat_defined _ b0 _ x0 RB2 ltac:(cbn; lia) E). }
  destruct (bd_B1 al_rom r2 M2 ba arr b0 na 0 x y w h ltac:(lia) ltac:(lia) ltac:(lia) Halb ltac:(lia) ALarr R2 RB2 Rb0' (W_sev_got C A M2 md HW2) SOKb0 P8 P10)
    as (r3 & RUN3 & U10 & U1 & U8 & U20 & U21 & U26 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  set (M3 := wbytes M2 (Z_to_bv 64 (b0 + 16)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (HW3 : W C A M3 md).
  { subst M3. apply (W_store_blk C A _ md (Z_to_bv 64 b0) _ 20 _ CK HW2 Lb0 L0b0); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (U2 : getr r3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (U4 : getr r3 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  replace (0x17c54 : word) with (Z_to_bv 64 0x17c54) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M3 md r3 (Z_to_bv 64 b0) (Z_to_bv 64 0x14b20) 20 (s - 96) S CK HW3 U10 Lb0 L0b0 U1
           ltac:(red; apply bv_eq; reflexivity) U4 U2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r4 HWa CSa Lb0a LEQa PMa HRTa.
  replace (Z_to_bv 64 0x14b20) with (0x14b20 : word) by (apply bv_eq; reflexivity).
  assert (SUBa : sub_live A1 A).
  { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 b0)) as [->|NE]; [congruence|]. rewrite <- (LEQa q NE). exact L. }
  assert (Lba1 : live A1 (Z_to_bv 64 ba) = Some 24%Z) by (rewrite (LEQa _ (zneq_w ba b0 ltac:(lia) ltac:(lia) (not_eq_sym NE1))); exact Lba).
  assert (Larr1 : live A1 (Z_to_bv 64 arr) = Some (8 * na)%Z) by (rewrite (LEQa _ (zneq_w arr b0 ltac:(lia) ltac:(lia) (not_eq_sym NE2))); exact Larr).
  (* [comment removed for export] *)
  assert (R3 : RECat m1 ba (boxa_flds 1 na 0 arr)).
  { apply (RECat_POSTM C A1 (s - 96) M3 m1 (Z_to_bv 64 ba) 24); [| exact PMa | exact Lba1 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; cbn; lia].
    subst M3. apply RECat_out; [exact R2 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (SOKarr : store_ok SEGS m1 (Z_to_bv 64 arr) 8 = true).
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x0 Hx. cbn in Hx.
    unfold wview. destruct (m1 x0) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A1 m1 _ (Z_to_bv 64 arr) (8 * na) x0 CK HWa Larr1 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  assert (E8 : getr r4 8 = Z_to_bv 64 ba) by (csr; reflexivity).
  assert (E20 : getr r4 20 = Z_to_bv 64 0) by (csr; reflexivity).
  assert (E21 : getr r4 21 = Z_to_bv 64 0) by (csr; reflexivity).
  assert (E26 : getr r4 26 = Z_to_bv 64 arr) by (csr; reflexivity).
  destruct (bd_C1 al_rom r4 m1 ba arr na 0 ltac:(lia) ltac:(lia) ltac:(lia) R3 ltac:(lia) SOKarr E8 E20 E21 E26) as (r5 & RUN5 & V10 & V1 & V8 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN5 |].
  set (M4 := wbytes m1 (Z_to_bv 64 arr) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (HW4 : W C A1 M4 (with_vmmaps vm1 md)).
  { subst M4. apply (W_store_blk C A1 _ _ (Z_to_bv 64 arr) _ (8 * na) _ CK HWa Larr1 L0arr); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (CE4 : bd_cells M4 s ret regs).
  { unfold bd_cells. apply (cellsZ_out m1 M4 arr (arr + 8)).
    - intros x0 Hx. subst M4. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    - clear -HsR TOParr Hna T1 Hlo PIN7. forall_cells.
    - apply (cellsZ_frm C (s - 96) M3 m1); [exact CK | exact (proj1 PMa) | lia | clear -HsR; forall_cells |].
      apply (cellsZ_out M2 M3 b0 (b0 + 20)); [| clear -HsR TOPb0 T1 Hlo PIN7; forall_cells | exact CE2].
      intros x0 Hx. subst M3. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  replace (0x17c54 : word) with (Z_to_bv 64 0x17c54) by (apply bv_eq; reflexivity).
  apply (bd_T1 C m regs (with_vmmaps vm1 md) A1 M4 r5 s pp ba na arr sb ret S CK HW4 Hs16 ltac:(unfold ALLOC_STACK; lia) Hhi Hret H2 H4);
    [csr; reflexivity | exact V1 | exact V10 | exact V8 | csr; reflexivity | csr; reflexivity | csr; reflexivity | csr; reflexivity
    | exact CE4 | | | exact Z0 | exact Lba1 | exact L0ba | lia | lia | exact Warr | right; split; [exact Larr1 | split; [exact L0arr | exact NEarr]] | |].
  - apply (slot_keep C A A1 s pp sb SL). intros p k E. apply LEQa. exact (proj2 (proj2 (DISJ p k E)) eq_refl).
  - intros p k E. pose proof (DISJ p k E) as (D1 & D2 & _). split; assumption.
  - intros Af SUBf Lf Lfa.
    assert (Lfb : live Af (Z_to_bv 64 b0) = None).
    { destruct (live Af (Z_to_bv 64 b0)) as [k|] eqn:E; [|reflexivity]. pose proof (SUBf _ _ E). congruence. }
    pose proof (sub_live_trans _ _ _ SUBf SUBa) as SUBf0.
    apply (POSTD_trans C Af s pp m M2); [exact (PRE2 Af SUBf0 Lf)|].
    apply (POSTD_trans C Af s pp M2 M3).
    { subst M3. apply (POSTD_deadw C A Af M2 md (Z_to_bv 64 b0) _ 20 _ s pp CK HW2 Lb0 Lfb SUBf0); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
    apply (POSTD_trans C Af s pp M3 m1); [apply (POSTD_of_POSTM C A1 Af); [eapply POSTM_mono; [|exact PMa]; lia | exact SUBf]|].
    subst M4. apply (POSTD_deadw C A1 Af m1 _ (Z_to_bv 64 arr) _ (8 * na) _ s pp CK HWa Larr1 Lfa SUBf); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia].
  - intros A' m' vm' regs' HW' CS' L1 L2 LEQ SUB PD RD HRT'. rewrite with_vmmaps_twice in HW'. rewrite with_vmmaps_twice.
    apply (HK A' m' vm' regs' HW' CS' L1 L2).
    + intros _. destruct (live A' (Z_to_bv 64 b0)) as [k|] eqn:E; [|reflexivity]. pose proof (SUB _ _ E). congruence.
    + intros q N1 N2 N3. rewrite (LEQ q N1 N2). apply LEQa. exact (N3 eq_refl).
    + exact (sub_live_trans _ _ _ SUB SUBa).
    + exact PD.
    + exact RD.
    + room_tac.
Qed.

(* [comment removed for export] *)
Theorem boxaDestroy_null_W : forall C A m md regs (s pp : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14a20 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL ALpp Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 96 \/ s <= pp)%Z) by lia.
  destruct (bd_A al_rom regs m s pp 0 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
              (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (bdF m s ret regs) md /\ POSTM C A s m (bdF m s ret regs)) by (unfold bdF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (bd_Z al_rom r1 _ Q8) |].
  destruct (bd_epi al_rom r1 (bdF m s ret regs) s ret regs ltac:(lia) ltac:(lia) Hret (bdF_cells m s ret regs ltac:(lia) ltac:(lia)) Q2)
    as (r6 & RUN6 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN6 |].
  apply (HK _ r6 HW1); [| exact PM1].
  apply cs_kept_intro; rewrite ?V2, ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?H2; try reflexivity.
  - rewrite (AG6 3) by notin_lit. csr. reflexivity.
  - rewrite (AG6 4) by notin_lit. csr. reflexivity.
  - rewrite (AG6 27) by notin_lit. csr. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str_boxaCreate : str16 0x102a4 10. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Definition boxa_new (C : lctx) (A A' : AS) (m' : word -> option byte) (ba na arr : Z) : Prop :=
  RECat m' ba (boxa_flds 0 na 1 arr) /\ (ba mod 16 = 0)%Z /\ (1 <= arr)%Z /\ (arr mod 16 = 0)%Z /\ arr <> ba /\
  live A (Z_to_bv 64 ba) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 ba) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 ba) = Some 24%Z /\ live A' (Z_to_bv 64 arr) = Some (8 * na)%Z /\
  (forall q, q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 arr -> live A' q = live A q) /\
  (ba + 32 <= alloc_top (c_vm C))%Z /\ (arr + round16 (8 * na) <= alloc_top (c_vm C))%Z.

Lemma boxa_new_at : forall C A A' m' ba na arr, (1 <= na)%Z -> boxa_new C A A' m' ba na arr -> boxa_at C A' m' ba 0 na arr 0.
Proof.
  intros C A A' m' ba na arr Hna (R & Hal & Harr & Hala & NE & L1 & L2 & L01 & L02 & La & Lb & LEQ & T1 & T2).
  split; [exact R|]. split; [exact Hal|]. split; [exact La|]. split; [exact L01|].
  right. split; [exact Lb|]. split; [exact L02|]. split; [exact Hna|]. split; [exact NE|]. left. reflexivity.
Qed.

Theorem boxaCreate_sure_W : forall C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 10000000)%Z ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_boxa <= kR)%Z -> (RB_boxa n <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists ba arr : Z, getr regs' 10 = Z_to_bv 64 ba /\ boxa_new C A A' m' ba n arr) ->
     aroom A' vm' (kR - RK_boxa) (bR - RB_boxa n) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1494c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb HK.
  pose proof (alloc_margin_le (1 * 24)) as HAM1. pose proof (alloc_margin_le (n * 8)) as HAM2. unfold RK_boxa in Hrk. unfold RB_boxa in Hrb.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold LSF in *.
  assert (HsR : (0x523f0 + 8192 <= s < 2 ^ 63)%Z) by lia.
  (* [comment removed for export] *)
  destruct (ba_A al_rom regs m s n ret ltac:(lia) ltac:(lia) Hn (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  replace (0x17b1c : word) with (Z_to_bv 64 0x17b1c) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 24 kR bR (Z_to_bv 64 0x1496c) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrm1.
  replace (Z_to_bv 64 0x1496c) with (0x1496c : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r2 9 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E4a : getr r2 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R24 : rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  (* [comment removed for export] *)
    assert (Hba : (1 <= u res)%Z /\ (u res + 32 <= alloc_top (c_vm C))%Z).
    { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 24 + 15) / 16)%Z with 2%Z in TOP. lia. }
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
    set (ba := u res) in *. clearbody ba.
    rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (REC0 : RECat m1 ba (zflds [4; 4; 4; 4; 8]%nat)).
    { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
      unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
    assert (SOKb : store_ok SEGS m1 (Z_to_bv 64 ba) 24 = true).
    { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m1 ba _ x REC0 ltac:(cbn; lia) E). }
    destruct (ba_B al_rom r2 m1 s n ba ltac:(lia) ltac:(lia) Hn ltac:(lia) ltac:(lia)
                ltac:(rewrite <- (Z.add_0_r ba); apply mod16_plus_mod8; [exact AL16 | reflexivity])
                (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) SOKb E2a Hres E8a)
      as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (M2 := wbytes m1 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 ba))).
    set (M3 := wbytes (wbytes (wbytes M2 _ _) _ _) _ _).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
    { subst M2. apply (WP_win C A1 A m m1 _ _ _ s CK); [| exact SUBa | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
      split; [exact HWa | exact PMa']. }
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3.
      do 3 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 ba) _ 24); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
      exact WP2. }
    destruct WP3 as [HW3 PM3].
    assert (REC3 : RECat M3 ba (boxa_flds 0 n 1 0)).
    { subst M3 M2. unfold boxa_flds.
      eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, n); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 2 4);
        [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
      eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 1 4);
        [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
      eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 0 4);
        [ | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ].
      apply RECat_out; [exact REC0 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (P4 : getr r3 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    (* [comment removed for export] *)
    replace (0x17b1c : word) with (Z_to_bv 64 0x17b1c) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A1 M3 _ r3 n 8 (kR - 1) (bR - alloc_margin (1 * 24)) (Z_to_bv 64 0x149bc) (s - 32) S CK HW3 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hrm2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x149bc) with (0x149bc : word) by (apply bv_eq; reflexivity).
    assert (F2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (F9 : getr r4 8 = Z_to_bv 64 ba) by (csr; reflexivity).
    assert (F4 : getr r4 4 = Z_to_bv 64 0x31b70) by (csr; reflexivity).
    pose proof (blk_range C A1 M3 _ (Z_to_bv 64 ba) 24 CK HW3 L1 ltac:(lia)) as [Gba _]. rewrite u_Z2bv in Gba by lia.
    assert (REC4 : RECat m2 ba (boxa_flds 0 n 1 0)).
    { apply (RECat_POSTM C A1 (s - 32) M3 m2 (Z_to_bv 64 ba) 24 _ _ REC3 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
    assert (SOKb2 : store_ok SEGS m2 (Z_to_bv 64 ba) 24 = true).
    { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 ba _ x REC4 ltac:(cbn; lia) E). }
    assert (S8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite (FRM_rdn16 C (s - 32) M3 m2 (s - 8) 8 CK (proj1 PMb)) by (cbn; lia). subst M3 M2. rdn_solve. }
    assert (S16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite (FRM_rdn16 C (s - 32) M3 m2 (s - 16) 8 CK (proj1 PMb)) by (cbn; lia). subst M3 M2. rdn_solve. }
    assert (S24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite (FRM_rdn16 C (s - 32) M3 m2 (s - 24) 8 CK (proj1 PMb)) by (cbn; lia). subst M3 M2. rdn_solve. }
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    (* [comment removed for export] *)
      assert (Harr : (1 <= u res2)%Z /\ (u res2 + round16 (8 * n) <= alloc_top (c_vm C))%Z).
      { pose proof (u64_range res2). replace (n * 8)%Z with (8 * n)%Z in TOPb by lia. lia. }
      assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
      set (arr := u res2) in *. clearbody arr.
      rewrite Eres2 in Hres2, K0, K1, K00, KEQ.
      pose proof (round16_ge (8 * n) ltac:(lia)) as RG.
      assert (NE : arr <> ba).
      { intros E. rewrite E in K0. rewrite K0 in L1. discriminate L1. }
      destruct (ba_C al_rom r4 m2 s ba arr ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKb2 ltac:(lia)
                  S8 S16 S24 F2 Hres2 F9) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      set (M4 := wbytes m2 _ _).
      assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
      assert (Lba2 : live A2 (Z_to_bv 64 ba) = Some 24%Z) by (rewrite (KEQ _ (zneq_w ba arr ltac:(lia) ltac:(lia) (not_eq_sym NE))); exact L1).
      assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A s m M4).
      { subst M4. apply (WP_blk C A A2 m m2 _ (Z_to_bv 64 ba) _ 24); [exact CK | | exact Lba2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWb | exact PMb']. }
      destruct WP4 as [HW4 PM4].
      apply (HK A2 M4 vm2 r5 HW4).
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; reflexivity.
      * exact PM4.
      * exists ba, arr. split; [exact V10|].
        split.
        { subst M4. unfold boxa_flds. replace (8 * n)%Z with (8 * n)%Z by reflexivity.
          eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, n); (4%nat, 1%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 4 8);
            [ exact REC4 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
        split; [exact AL16|]. split; [lia|]. split; [exact AL16b|]. split; [exact NE|].
        split; [exact L0|]. split; [rewrite <- (LEQ _ (zneq_w arr ba ltac:(lia) ltac:(lia) NE)); exact K0|].
        split; [exact L00|]. split; [exact K00|]. split; [exact Lba2|]. split; [replace (8 * n)%Z with (n * 8)%Z by lia; exact K1|].
        split; [intros q N1 N2; rewrite (KEQ q N2); exact (LEQ q N1)|].
        split; lia.
      * apply (aroom_mono A2 vm2 (kR - 1 - 1) (bR - alloc_margin (1 * 24) - alloc_margin (n * 8))); [exact Hrm2 | unfold RK_boxa; lia | unfold RB_boxa; lia].
Qed.

(* [comment removed for export] *)
Theorem boxaCreate_W : forall C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 10000000)%Z ->
  live A (Z_to_bv 64 0) = None -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_boxa <= kR)%Z -> (RB_boxa n <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists ba arr : Z, getr regs' 10 = Z_to_bv 64 ba /\ boxa_new C A A' m' ba n arr) ) ->
     aroom A' vm' (kR - RK_boxa) (bR - RB_boxa n) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1494c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb HK.
  apply (boxaCreate_sure_W C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn Z0A Z0 kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' X1 X2 X3 X4 X5. apply (HK A' m' vm' regs' X1 X2 X3); [right; exact X4 | exact X5].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str_boxa_not_defined : str16 0x10539 16. Proof. str16_tac. Qed.
Lemma str_box_not_defined : str16 0x10bf9 15. Proof. str16_tac. Qed.
Lemma str_boxaAddBox : str16 0x10c09 10. Proof. str16_tac. Qed.

Lemma babF_cells : forall m s ret regs (a : Z), (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS (babF m s ret regs) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS (babF m s ret regs) (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
  rdn SEGS (babF m s ret regs) (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
  rdn SEGS (babF m s ret regs) (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
  rdn SEGS (babF m s ret regs) (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)).
Proof. intros m s ret regs a Hs Hs64. unfold babF. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Theorem boxaAddBox_err_W : forall C A m md regs (s ba : Z) (bx ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 ba -> getr regs 11 = bx -> (ba = 0%Z \/ ((1 <= ba < 2 ^ 64)%Z /\ bx = Z_to_bv 64 0)) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 1 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14bec : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ba bx ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 CASE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (RUN : exists regs' (msg : Z) (k : Z), msteps SEGS (mkst regs (0x14bec : word) m al_rom) (mkst regs' (0x14df8 : word) (babF m s ret regs) al_rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10c09
      /\ regs_agree (fun r => In r [2; 10; 11]%list) regs regs' /\ str16 msg k).
  { destruct CASE as [-> | [Hba ->]].
    - destruct (bab_N1 al_rom regs m s ret bx ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10 H11) as (r1 & RUN1 & Q2 & Q10 & Q11 & AG1).
      exists r1, 0x10539%Z, 16%Z. repeat split; try assumption; apply str_boxa_not_defined.
    - destruct (bab_N2 al_rom regs m s ba ret ltac:(lia) ltac:(lia) Hba SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10 H11) as (r1 & RUN1 & Q2 & Q10 & Q11 & AG1).
      exists r1, 0x10bf9%Z, 15%Z. repeat split; try assumption; apply str_box_not_defined. }
  destruct RUN as (r1 & msg & k & RUN1 & Q2 & Q10 & Q11 & AG1 & Smsg).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (babF m s ret regs) md /\ POSTM C A s m (babF m s ret regs)) by (unfold babF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (babF_cells m s ret regs 0 ltac:(lia) ltac:(lia)) as (C8 & C16 & C24 & C32 & C40).
  destruct (bab_T al_rom r1 (babF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) msg ltac:(lia) ltac:(lia)
              C8 C16 C24 C32 C40 Q2 Q10 Q11) as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P8 & P9 & P18 & P19 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  apply (returnErrorInt_W C A _ md r2 s msg 0x10c09 k 10 ret (Z_to_bv 64 1) S CK HW1 P2 Hs16 ltac:(unfold LSF; lia) Hhi P1 Hret P10 P11 P12 Smsg str_boxaAddBox).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?P8, ?P9, ?P18, ?P19; reflexivity.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A _ md m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

(* [comment removed for export] *)
Theorem boxaAddBox_W : forall C A m md regs (s ba bx n na rc arr : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 ba -> getr regs 11 = Z_to_bv 64 bx -> getr regs 12 = Z_to_bv 64 0 ->
  (1 <= bx < 2 ^ 64)%Z -> RECat m ba (boxa_flds n na rc arr) -> (0 <= n < na)%Z -> (na < 2 ^ 31)%Z -> arr <> ba ->
  live A (Z_to_bv 64 ba) = Some 24%Z -> live (c_A0 C) (Z_to_bv 64 ba) = None ->
  live A (Z_to_bv 64 arr) = Some (8 * na)%Z -> live (c_A0 C) (Z_to_bv 64 arr) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     RECat m' ba (boxa_flds (n + 1) na rc arr) -> rdn SEGS m' (Z_to_bv 64 (arr + 8 * n)) 8 = Some (Z_to_le_bytes 8 bx) ->
     (forall Ar, sub_live Ar A -> live Ar (Z_to_bv 64 ba) = None -> live Ar (Z_to_bv 64 arr) = None -> POSTM C Ar s m m') ->
     (* [comment removed for export] *)
     (forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 arr -> u q <= u x < u q + k -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14bec : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ba bx n na rc arr ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Hbx R Hn Hna NE Lba L0ba Larr L0arr HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU8] in *.
  pose proof (BOXA_wf m ba n na rc arr R) as (Wn & Wna & Warr & Wba0 & Wba).
  destruct (blk_range C A m md (Z_to_bv 64 ba) 24 CK HW Lba ltac:(lia)) as [Gba TOPba]. rewrite u_Z2bv in Gba, TOPba by lia.
  destruct (blk_range C A m md (Z_to_bv 64 arr) (8 * na) CK HW Larr ltac:(lia)) as [Garr TOParr]. rewrite u_Z2bv in Garr, TOParr by lia.
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Larr Lba (zneq_w arr ba ltac:(lia) ltac:(lia) NE)) as D.
  rewrite !u_Z2bv in D by lia. change (round16 24) with 32%Z in D. pose proof (round16_ge (8 * na) ltac:(lia)) as RG.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (SOKa : store_ok SEGS m (Z_to_bv 64 (arr + 8 * n)) 8 = true).
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A m md (Z_to_bv 64 arr) (8 * na) x CK HW Larr ltac:(rewrite u_Z2bv by lia; lia)) as (_ & Dx & _). exact (Dx E). }
  assert (SOKb : store_ok SEGS m (Z_to_bv 64 ba) 4 = true).
  { rewrite <- pu8_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m ba _ x R ltac:(cbn; lia) E). }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lba) as (_ & ALba16 & _). rewrite u_Z2bv in ALba16 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Larr) as (_ & ALarr16 & _). rewrite u_Z2bv in ALarr16 by lia.
  destruct (bab_B al_rom regs m s ba bx n na rc arr ret ltac:(lia) ltac:(lia) ltac:(lia) Hbx Hn Hna ltac:(lia) ltac:(lia) Hret
              ltac:(rewrite <- (Z.add_0_r ba); apply mod16_plus_mod8; [exact ALba16 | reflexivity])
              ltac:(rewrite <- (Z.add_0_r arr); apply mod16_plus_mod8; [exact ALarr16 | reflexivity]) SOK R
              ltac:(lia) ltac:(lia) ltac:(lia) SOKa SOKb H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := babF m s ret regs).
  set (M2 := wbytes M1 (Z_to_bv 64 (arr + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 bx))).
  set (M3 := wbytes M2 (Z_to_bv 64 ba) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))).
  assert (HW1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold babF; wp_win CK). destruct HW1 as [HW1 PM1].
  assert (HW2 : W C A M2 md).
  { subst M2. apply (W_store_blk C A M1 md (Z_to_bv 64 arr) _ (8 * na) _ CK HW1 Larr L0arr); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (HW3 : W C A M3 md).
  { subst M3. apply (W_store_blk C A M2 md (Z_to_bv 64 ba) _ 24 _ CK HW2 Lba L0ba); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  apply (HK M3 r1 HW3).
  - apply cs_kept_intro; csr; reflexivity.
  - exact Q10.
  - subst M3 M2 M1. eapply (REC_wr' _ _ (boxa_flds n na rc arr) _ 0 4); [ | cbn; lia | cbn; lia | reflexivity | cbn [fld_off boxa_flds Z.of_nat]; f_equal; lia | reflexivity ].
    apply RECat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    unfold babF. repeat (apply RECat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact R.
  - subst M3 M2. rewrite rdn_wbytes_out_Z by (zlen; lia). rewrite <- (w2b_Z 8 bx) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros Ar SUB La Lr. apply (POSTM_trans C Ar s m M1 M3); [exact (POSTM_sub C Ar A _ _ _ SUB PM1)|].
    apply (POSTM_trans C Ar s M1 M2 M3).
    + subst M2. apply (POSTM_blk C Ar A M1 md (Z_to_bv 64 arr) _ (8 * na) _ s CK HW1 Larr Lr SUB); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia].
    + subst M3. apply (POSTM_blk C Ar A M2 md (Z_to_bv 64 ba) _ 24 _ s CK HW2 Lba La SUB); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia].
  - intros q k x Lq N1 N2 Hx.
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lq Lba N1) as D1.
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lq Larr N2) as D2.
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lq) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0) as RGq.
    destruct (w_vm _ _ _ _ HW) as (_ & Etop & _). rewrite Etop in TOPq.
    rewrite !u_Z2bv in D1, D2 by lia. change (round16 24) with 32%Z in D1.
    subst M3 M2 M1. unfold babF. clear -Hx D1 D2 RGq RG TOPq T1 Hlo Hhi T2 T3 PIN7 Gba Garr Wba TOParr Hn.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.
End Boxa.
