(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptArith2 LibAtomic LeptRecs LeptSlots LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2_code_pixaCreate V2_code_boxaCreate.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Local Ltac forall_cells := repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

Definition pixa_flds (n na rc parr ba : Z) : list fld := [(4%nat, n); (4%nat, na); (4%nat, rc); (4%nat, 0%Z); (8%nat, parr); (8%nat, ba)].
Definition boxa_flds (n na rc arr : Z) : list fld := [(4%nat, n); (4%nat, na); (4%nat, rc); (4%nat, 0%Z); (8%nat, arr)].

Section BoxaPC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition boxa_new (C : lctx) (A A' : AS) (m' : word -> option byte) (ba na arr : Z) : Prop :=
  RECat m' ba (boxa_flds 0 na 1 arr) /\ (ba mod 16 = 0)%Z /\ (1 <= arr)%Z /\ (arr mod 16 = 0)%Z /\ arr <> ba /\
  live A (Z_to_bv 64 ba) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 ba) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 ba) = Some 24%Z /\ live A' (Z_to_bv 64 arr) = Some (8 * na)%Z /\
  (forall q, q <> Z_to_bv 64 ba -> q <> Z_to_bv 64 arr -> live A' q = live A q) /\
  (ba + 32 <= alloc_top (c_vm C))%Z /\ (arr + round16 (8 * na) <= alloc_top (c_vm C))%Z.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bxc_nclamp_ok : forall n, (1 <= n <= 10000000)%Z ->
  (zx (sw32 (n + 18446744073699551615)) <? zx 18446744073699551616)%Z = false.
Proof. intros n H. unfold zx, sw32. apply Z.ltb_ge. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Segs.
Variable rom : word -> option byte.
  Ltac bxc_zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac bxc_zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
  Lemma ba_A : forall regs m (s n : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= n <= 10000000)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x18ecc : word) m rom)
                  (mkst regs' (0x3c0f8 : word)
                     (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                             (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                             (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x18eec
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 24 /\ getr regs' 9 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n ret Hs Hs64 Hn SOK H2 H1 H10.
    eexists. split.
    - zv F_18ecc D_18ecc (Z_to_bv 64 (s - 32)).
      stepST F_18ed0 D_18ed0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_18ed4 D_18ed4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_18ed8 D_18ed8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_18edc D_18edc. sn F_18ee0 D_18ee0. sn F_18ee4 D_18ee4. sn F_18ee8 D_18ee8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ba_B : forall regs m (s n ba : Z),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= n <= 10000000)%Z -> (1 <= ba)%Z -> (ba + 24 < 2 ^ 64)%Z -> (ba mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 ba) 24 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 ba -> getr regs 9 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x18eec : word) m rom)
                  (mkst regs' (0x3c0f8 : word)
                     (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
                             (Z_to_bv 64 ba) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (ba + 4)) (word_to_le_bytes 4 (Z_to_bv 64 n)))
                             (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x18f3c
      /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 9 = Z_to_bv 64 n /\ getr regs' 8 = Z_to_bv 64 ba
      /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s n ba Hs Hs64 Hn Hba Hba64 ALba SOK SOKb H2 H10 H9.
    eexists. split.
    - stepST F_18eec D_18eec (Z_to_bv 64 (s - 32)) (Z_to_bv 64 ba) ltac:(sok_in SOK).
      stepb_ft F_18ef0 D_18ef0 ltac:(condZ).
      sn F_18ef4 D_18ef4.
      bxc_zand F_18ef8 D_18ef8 andi_7 ALba. stepb_ft F_18efc D_18efc ltac:(condZ).
      sn F_18f00 D_18f00. sn F_18f04 D_18f04.
      sn F_18f08 D_18f08. fixv (Z_to_bv 64 (sw32 (n + 18446744073699551615))) ltac:(rewrite v_addw_Z; reflexivity).
      sn F_18f0c D_18f0c.
      stepb_tk F_18f10 D_18f10 ltac:(pin; rewrite c_ltu_zx; apply bxc_nclamp_ok; lia).
      stepST F_18f18 D_18f18 (Z_to_bv 64 ba) (Z_to_bv 64 0) ltac:(sok_in SOKb).
      stepST F_18f1c D_18f1c (Z_to_bv 64 (ba + 4)) (Z_to_bv 64 n) ltac:(sok_in SOKb).
      stepfence F_18f20 D_18f20.
      sn F_18f24 D_18f24.
      stepST F_18f28 D_18f28 (Z_to_bv 64 (ba + 8)) (Z_to_bv 64 1) ltac:(sok_in SOKb).
      stepfence F_18f2c D_18f2c.
      sn F_18f30 D_18f30. sn F_18f34 D_18f34. sn F_18f38 D_18f38.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ba_C : forall regs m (s ba arr : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> (1 <= ba)%Z -> (ba + 24 < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 ba) 24 = true -> (ba + 24 <= s - 32 \/ s <= ba)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 8 = Z_to_bv 64 ba ->
    exists regs',
      msteps SEGS (mkst regs (0x18f3c : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (ba + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 ba /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ba arr ret s0v s1v Hs Hs64 Harr Hba Hba64 Hret SOKb DJ R8 R16 R24 H2 H10 H8.
    eexists. split.
    - stepST F_18f3c D_18f3c (Z_to_bv 64 (ba + 16)) (Z_to_bv 64 arr) ltac:(sok_in SOKb).
      stepb_tk F_18f40 D_18f40 ltac:(condZ).
      sn F_18f84 D_18f84.
      stepLD8 F_18f88 D_18f88 ret.
      stepLD8 F_18f8c D_18f8c s0v.
      stepLD8 F_18f90 D_18f90 s1v.
      zv F_18f94 D_18f94 (Z_to_bv 64 s).
      stepret F_18f98 D_18f98 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma bxc_boxaCreate_sure_W : forall C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 10000000)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (2 <= kR)%Z -> (alloc_margin (1 * 24) + alloc_margin (n * 8) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists ba arr : Z, getr regs' 10 = Z_to_bv 64 ba /\ boxa_new C A A' m' ba n arr) ->
     aroom A' vm' (kR - 2) (bR - alloc_margin (1 * 24) - alloc_margin (n * 8)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x18ecc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s n ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hn kR bR Hrm Hrk Hrb HK.
  pose proof (alloc_margin_le (1 * 24)) as HAM1. pose proof (alloc_margin_le (n * 8)) as HAM2. pose proof (alloc_margin_ge (1 * 24) ltac:(lia)) as HAG1. pose proof (alloc_margin_ge (n * 8) ltac:(lia)) as HAG2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (HsR : (0x77000 + 8192 <= s < 2 ^ 63)%Z) by lia.
  destruct (ba_A al_rom regs m s n ret ltac:(lia) ltac:(lia) Hn (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  replace (0x3c0f8 : word) with (Z_to_bv 64 0x3c0f8) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 24 kR bR (Z_to_bv 64 0x18eec) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrm1.
  replace (Z_to_bv 64 0x18eec) with (0x18eec : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r2 9 = Z_to_bv 64 n) by (csr; reflexivity).
  assert (E4a : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R24 : rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
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
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
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
    assert (P4 : getr r3 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
    replace (0x3c0f8 : word) with (Z_to_bv 64 0x3c0f8) by (apply bv_eq; reflexivity).
    apply (W_calloc16_sure C A1 M3 _ r3 n 8 (kR - 1) (bR - alloc_margin (1 * 24)) (Z_to_bv 64 0x18f3c) (s - 32) S CK HW3 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hrm2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
    replace (Z_to_bv 64 0x18f3c) with (0x18f3c : word) by (apply bv_eq; reflexivity).
    assert (F2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (F9 : getr r4 8 = Z_to_bv 64 ba) by (csr; reflexivity).
    assert (F4 : getr r4 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
    pose proof (blk_range C A1 M3 _ (Z_to_bv 64 ba) 24 CK HW3 L1 ltac:(lia)) as [Gba _]. rewrite u_Z2bv in Gba by lia.
    assert (REC4 : RECat m2 ba (boxa_flds 0 n 1 0)).
    { apply (RECat_POSTM C A1 (s - 32) M3 m2 (Z_to_bv 64 ba) 24 _ _ REC3 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
    assert (SOKb2 : store_ok SEGS m2 (Z_to_bv 64 ba) 24 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 ba _ x REC4 ltac:(cbn; lia) E). }
    assert (S8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite (FRM_rdn16 C (s - 32) M3 m2 (s - 8) 8 CK (proj1 PMb)) by (cbn; lia). subst M3 M2. rdn_solve. }
    assert (S16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite (FRM_rdn16 C (s - 32) M3 m2 (s - 16) 8 CK (proj1 PMb)) by (cbn; lia). subst M3 M2. rdn_solve. }
    assert (S24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite (FRM_rdn16 C (s - 32) M3 m2 (s - 24) 8 CK (proj1 PMb)) by (cbn; lia). subst M3 M2. rdn_solve. }
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
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
      * apply (aroom_mono A2 vm2 (kR - 1 - 1) (bR - alloc_margin (1 * 24) - alloc_margin (n * 8))); [exact Hrm2 | lia | lia].
Qed.

Theorem boxaCreate10_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 10 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (2 <= kR)%Z -> (alloc_margin (1 * 24) + alloc_margin (10 * 8) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists ba arr : Z, getr regs' 10 = Z_to_bv 64 ba /\ boxa_new C A A' m' ba 10 arr) ->
     aroom A' vm' (kR - 2) (bR - alloc_margin (1 * 24) - alloc_margin (10 * 8)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x18ecc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 kR bR Hrm Hrk Hrb HK.
  exact (bxc_boxaCreate_sure_W C A m md regs s 10 ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 ltac:(lia) kR bR Hrm Hrk Hrb HK).
Qed.

End BoxaPC.

Section PixaPC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section PSegs.
Variable rom : word -> option byte.
  Ltac pcz_and F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Definition pcF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).
  Definition pc_cells (m : word -> option byte) (s : Z) (ret : word) (R : bvmap 5 word) : Prop :=
    cellsZ m [(s - 8, ret); (s - 16, getr R 8); (s - 24, getr R 9)]%Z.
  Lemma pcF_cells : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> pc_cells (pcF m s ret regs) s ret regs.
  Proof. intros m s ret regs Hs Hs64. unfold pc_cells, pcF. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  Lemma pc_A : forall regs m (s : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 10 ->
    exists regs',
      msteps SEGS (mkst regs (0x18258 : word) m rom) (mkst regs' (0x3c0f8 : word) (pcF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x18278
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 32 /\ getr regs' 9 = Z_to_bv 64 10
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10.
    eexists. split.
    - zv F_18258 D_18258 (Z_to_bv 64 (s - 32)).
      stepST F_1825c D_1825c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_18260 D_18260 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_18264 D_18264 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_18268 D_18268. sn F_1826c D_1826c. sn F_18270 D_18270. sn F_18274 D_18274.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pc_B : forall regs m (s px : Z),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= px)%Z -> (px + 32 < 2 ^ 64)%Z -> (px mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 px) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 px -> getr regs 9 = Z_to_bv 64 10 ->
    exists regs',
      msteps SEGS (mkst regs (0x18278 : word) m rom)
                  (mkst regs' (0x3c0f8 : word)
                     (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 px)))
                             (Z_to_bv 64 px) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (px + 4)) (word_to_le_bytes 4 (Z_to_bv 64 10)))
                             (Z_to_bv 64 (px + 8)) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x182c8
      /\ getr regs' 10 = Z_to_bv 64 10 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 9 = Z_to_bv 64 10 /\ getr regs' 8 = Z_to_bv 64 px
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s px Hs Hs64 Hpx Hpx64 ALpx SOK SOKp H2 H10 H9.
    eexists. split.
    - stepST F_18278 D_18278 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 px) ltac:(sok_in SOK).
      stepb_ft F_1827c D_1827c ltac:(condZ).
      sn F_18280 D_18280.
      pcz_and F_18284 D_18284 andi_7 ALpx. stepb_ft F_18288 D_18288 ltac:(condZ).
      sn F_1828c D_1828c. sn F_18290 D_18290.
      sn F_18294 D_18294.
      sn F_18298 D_18298.
      stepb_tk F_1829c D_1829c ltac:(first [condZ | vm_compute; reflexivity]).
      stepST F_182a4 D_182a4 (Z_to_bv 64 px) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      stepST F_182a8 D_182a8 (Z_to_bv 64 (px + 4)) (Z_to_bv 64 10) ltac:(sok_in SOKp).
      stepfence F_182ac D_182ac.
      sn F_182b0 D_182b0.
      stepST F_182b4 D_182b4 (Z_to_bv 64 (px + 8)) (Z_to_bv 64 1) ltac:(sok_in SOKp).
      stepfence F_182b8 D_182b8.
      sn F_182bc D_182bc. sn F_182c0 D_182c0. sn F_182c4 D_182c4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pc_C : forall regs m (px parr : Z),
    (1 <= px)%Z -> (px + 32 < 2 ^ 64)%Z -> (0 <= parr < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 px) 32 = true ->
    getr regs 10 = Z_to_bv 64 parr -> getr regs 8 = Z_to_bv 64 px -> getr regs 9 = Z_to_bv 64 10 ->
    exists regs',
      msteps SEGS (mkst regs (0x182c8 : word) m rom)
                  (mkst regs' (0x18ecc : word) (wbytes m (Z_to_bv 64 (px + 16)) (word_to_le_bytes 8 (Z_to_bv 64 parr))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x182d4 /\ getr regs' 10 = Z_to_bv 64 10 /\ getr regs' 8 = Z_to_bv 64 px /\ getr regs' 9 = Z_to_bv 64 10
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m px parr Hpx Hpx64 Hparr SOKp H10 H8 H9.
    eexists. split.
    - stepST F_182c8 D_182c8 (Z_to_bv 64 (px + 16)) (Z_to_bv 64 parr) ltac:(sok_in SOKp).
      sn F_182cc D_182cc. sn F_182d0 D_182d0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pc_D : forall regs m (s px parr ba : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= px)%Z -> (px + 32 < 2 ^ 64)%Z -> (1 <= parr < 2 ^ 64)%Z -> (1 <= ba < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 px) 32 = true -> (px + 32 <= s - 32)%Z ->
    rdn SEGS m (Z_to_bv 64 (px + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 ba -> getr regs 8 = Z_to_bv 64 px ->
    exists regs',
      msteps SEGS (mkst regs (0x182d4 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (px + 24)) (word_to_le_bytes 8 (Z_to_bv 64 ba))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 px
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s px parr ba ret s0v s1v Hs Hs64 Hpx Hpx64 Hparr Hba Hret SOKp DJ Rparr R8 R16 R24 H2 H10 H8.
    eexists. split.
    - stepLD F_182d4 D_182d4 (Z_to_le_bytes 8 parr) (Z_to_bv 64 parr) ltac:(addr_norm; exact Rparr) ltac:(apply lez8; lia).
      stepST F_182d8 D_182d8 (Z_to_bv 64 (px + 24)) (Z_to_bv 64 ba) ltac:(sok_in SOKp).
      stepb_ft F_182dc D_182dc ltac:(condZ).
      stepb_tk F_182e0 D_182e0 ltac:(condZ).
      sn F_18324 D_18324.
      stepLD8 F_18328 D_18328 ret. stepLD8 F_1832c D_1832c s0v. stepLD8 F_18330 D_18330 s1v.
      zv F_18334 D_18334 (Z_to_bv 64 s).
      stepret F_18338 D_18338 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End PSegs.
End PixaPC.

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.


Definition PIXAC_WIN : Z := 2048.
Definition STOPS : list Z := [246008]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_pixaCreate : Z := 98904.

(* [comment removed for export] *)
Definition pixa_cells (m : word -> option byte) (pa parr ba barr n : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 (pa + 0)) 4 = Some (Z_to_le_bytes 4 n) /\ rdn SEGS m (Z_to_bv 64 (pa + 4)) 4 = Some (Z_to_le_bytes 4 10) /\
  rdn SEGS m (Z_to_bv 64 (pa + 8)) 4 = Some (Z_to_le_bytes 4 1) /\ rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) /\
  rdn SEGS m (Z_to_bv 64 (pa + 24)) 8 = Some (Z_to_le_bytes 8 ba) /\
  rdn SEGS m (Z_to_bv 64 (ba + 0)) 4 = Some (Z_to_le_bytes 4 0) /\ rdn SEGS m (Z_to_bv 64 (ba + 4)) 4 = Some (Z_to_le_bytes 4 10) /\
  rdn SEGS m (Z_to_bv 64 (ba + 8)) 4 = Some (Z_to_le_bytes 4 1) /\ rdn SEGS m (Z_to_bv 64 (ba + 16)) 8 = Some (Z_to_le_bytes 8 barr).

(* [comment removed for export] *)
Definition pixa_blks (C : lctx) (A : AS) (pa parr ba barr : Z) : Prop :=
  (0 <= pa < 2 ^ 64)%Z /\ (0 <= parr < 2 ^ 64)%Z /\ (0 <= ba < 2 ^ 64)%Z /\ (0 <= barr < 2 ^ 64)%Z /\
  live A (Z_to_bv 64 pa) = Some 32%Z /\ live A (Z_to_bv 64 parr) = Some 80%Z /\ live A (Z_to_bv 64 ba) = Some 24%Z /\ live A (Z_to_bv 64 barr) = Some 80%Z /\
  live (c_A0 C) (Z_to_bv 64 pa) = None /\ live (c_A0 C) (Z_to_bv 64 parr) = None /\ live (c_A0 C) (Z_to_bv 64 ba) = None /\ live (c_A0 C) (Z_to_bv 64 barr) = None.

(* [comment removed for export] *)
Definition pixa_new10 (C : lctx) (A A' : AS) (m' : word -> option byte) (pa parr ba barr : Z) : Prop :=
  pixa_cells m' pa parr ba barr 0 /\ pixa_blks C A' pa parr ba barr /\
  live A (Z_to_bv 64 pa) = None /\ live A (Z_to_bv 64 parr) = None /\ live A (Z_to_bv 64 ba) = None /\ live A (Z_to_bv 64 barr) = None /\
  (forall q : word, ~ In q [Z_to_bv 64 barr; Z_to_bv 64 ba; Z_to_bv 64 parr; Z_to_bv 64 pa] -> live A' q = live A q) /\ parr <> barr.

Lemma pxc_am : forall n, (0 <= n <= 2028)%Z -> alloc_margin n = (2 ^ 17)%Z.
Proof. intros n Hn. unfold alloc_margin. replace (n <=? 2028)%Z with true by (symmetry; apply Z.leb_le; lia). lia. Qed.

Lemma pxc_bwf : forall m ba n na rc arr, RECat m ba (boxa_flds n na rc arr) ->
  (0 <= n < 2 ^ 32)%Z /\ (0 <= na < 2 ^ 32)%Z /\ (0 <= arr < 2 ^ 64)%Z /\ (0 <= ba)%Z /\ (ba + 24 < 2 ^ 64)%Z.
Proof. intros m ba n na rc arr (H0 & H1 & WF & _). cbn in H1, WF. lia. Qed.

Lemma pxc_cells : forall m pa parr ba barr, RECat m pa (pixa_flds 0 10 1 parr ba) -> RECat m ba (boxa_flds 0 10 1 barr) ->
  pixa_cells m pa parr ba barr 0.
Proof.
  intros m pa parr ba barr RP RB. unfold pixa_cells.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - eapply (REC_rd' SEGS _ _ (pixa_flds 0 10 1 parr ba) 0 4); [exact RP | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (pixa_flds 0 10 1 parr ba) 1 4); [exact RP | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (pixa_flds 0 10 1 parr ba) 2 4); [exact RP | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (pixa_flds 0 10 1 parr ba) 4 8); [exact RP | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (pixa_flds 0 10 1 parr ba) 5 8); [exact RP | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (boxa_flds 0 10 1 barr) 0 4); [exact RB | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (boxa_flds 0 10 1 barr) 1 4); [exact RB | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (boxa_flds 0 10 1 barr) 2 4); [exact RB | cbn; lia | reflexivity | reflexivity | reflexivity].
  - eapply (REC_rd' SEGS _ _ (boxa_flds 0 10 1 barr) 4 8); [exact RB | cbn; lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma pixaCreate10_W : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PIXAC_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 10 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (4 <= kR)%Z -> (4 * 2 ^ 17 <= bR)%Z ->
  (forall A' m' vm' regs' (pa parr ba barr : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' -> sub_live A A' ->
      getr regs' 10 = Z_to_bv 64 pa -> pixa_new10 C A A' m' pa parr ba barr ->
      aroom A' vm' (kR - 4) (bR - 4 * 2 ^ 17) ->
      realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixaCreate) m al_rom) md) S.
Proof.
  intros fx C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 kR bR Hrm Hrk Hrb HK.
  unfold PIXAC_WIN in Hlo.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg]. pose proof LSTK_val as LS.
  assert (IMG : (0 <= alloc_top (c_vm C))%Z) by (pose proof Cimg as X; cbn in X; lia).
  assert (GTOP : (alloc_top (c_vm C) + 8192 <= s - 32)%Z) by lia.
  replace (Z_to_bv 64 PC_pixaCreate) with (0x18258 : word) by (apply bv_eq; reflexivity).
  destruct (pc_A (fx := fx) al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (pcF m s ret regs) md /\ POSTM C A s m (pcF m s ret regs)) by (unfold pcF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  replace (0x3c0f8 : word) with (Z_to_bv 64 0x3c0f8) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure (fx := fx) C A _ md r1 1 32 kR bR (Z_to_bv 64 0x18278) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(rewrite pxc_am by lia; lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  replace (Z_to_bv 64 0x18278) with (0x18278 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9a : getr r2 9 = Z_to_bv 64 10) by (csr; reflexivity).
  assert (CEa : pc_cells m1 s ret regs).
  { unfold pc_cells. apply (cellsZ_frm C (s - 32) (pcF m s ret regs) m1); [exact CK | exact (proj1 PMa) | lia | forall_cells | exact (pcF_cells m s ret regs ltac:(lia) ltac:(lia))]. }
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) as SOKs.
  assert (Hpx : (1 <= u res)%Z /\ (u res + 32 <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 32 + 15) / 16)%Z with 2%Z in TOP. lia. }
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (px := u res) in *. clearbody px.
  rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  assert (ALpx : (px mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r px); apply mod16_plus_mod8; [exact AL16 | reflexivity]).
  assert (REC0 : RECat m1 px (zflds [4; 4; 4; 4; 8; 8]%nat)).
  { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
    unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
  assert (SOKpx : store_ok SEGS m1 (Z_to_bv 64 px) 32 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m1 px _ x REC0 ltac:(cbn; lia) E). }
  destruct (pc_B (fx := fx) al_rom r2 m1 s px ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpx SOKs SOKpx E2a Hres E9a)
    as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P9 & AG3).
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
  assert (REC2 : RECat M2 px (pixa_flds 0 10 1 0 0)).
  { subst M2 Ms. unfold pixa_flds.
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 10%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 2 4); [| cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity].
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 1 4); [| cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity].
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 0 4); [| cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity].
    apply RECat_out; [exact REC0 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (CE2 : pc_cells M2 s ret regs).
  { unfold pc_cells. apply (cellsZ_out m1 M2 px (s - 24)); [| forall_cells | exact CEa].
    intros x Hx. subst M2 Ms. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (P4 : getr r3 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  replace (0x3c0f8 : word) with (Z_to_bv 64 0x3c0f8) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure (fx := fx) C A1 M2 _ r3 10 8 (kR - 1) (bR - alloc_margin (1 * 32)) (Z_to_bv 64 0x182c8) (s - 32) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hroom1) ltac:(lia) ltac:(rewrite !pxc_am by lia; lia) ltac:(unfold ROOM_NMAX; lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hroom2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
  replace (Z_to_bv 64 0x182c8) with (0x182c8 : word) by (apply bv_eq; reflexivity).
  pose proof (blk_range C A1 M2 _ (Z_to_bv 64 px) 32 CK HW2 L1 ltac:(lia)) as [Gpx _]. rewrite u_Z2bv in Gpx by lia.
  assert (PARR : exists parr : Z, res2 = Z_to_bv 64 parr /\ (0 <= parr < 2 ^ 64)%Z /\
            live A2 (Z_to_bv 64 px) = Some 32%Z /\
            (forall q, q <> Z_to_bv 64 parr -> live A2 q = live A1 q) /\
            live A2 (Z_to_bv 64 parr) = Some 80%Z /\ live (c_A0 C) (Z_to_bv 64 parr) = None /\ live A1 (Z_to_bv 64 parr) = None /\
            parr <> px /\ (1 <= parr)%Z).
  { exists (u res2). pose proof (u64_range res2) as Hr2.
    assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
    assert (NE : Z_to_bv 64 px <> res2) by (intros E; rewrite <- E in K0; congruence).
    rewrite <- Eres2. split; [reflexivity|]. split; [lia|].
    split; [rewrite (KEQ _ NE); exact L1|].
    split; [exact KEQ|]. change (10 * 8)%Z with 80%Z in K1. split; [exact K1|]. split; [exact K00|]. split; [exact K0|].
    split; [| lia]. intros E. apply NE. rewrite <- E. apply zbv_self. }
  destruct PARR as (parr & -> & Hparr & Lpx2 & LEQ2 & Lparr2 & L0parr & LAparr1 & NEpp & Hparr1).
  assert (SUBb : sub_live A1 A2).
  { intros q k L. rewrite (LEQ2 q); [exact L|]. intros ->. congruence. }
  pose proof (sub_live_trans _ _ _ SUBa SUBb) as SUBab.
  assert (REC3 : RECat m2 px (pixa_flds 0 10 1 0 0)).
  { apply (RECat_POSTM C A1 (s - 32) M2 m2 (Z_to_bv 64 px) 32 _ _ REC2 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
  assert (SOKpx2 : store_ok SEGS m2 (Z_to_bv 64 px) 32 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 px _ x REC3 ltac:(cbn; lia) E). }
  assert (F9 : getr r4 8 = Z_to_bv 64 px) by (csr; reflexivity).
  assert (F8 : getr r4 9 = Z_to_bv 64 10) by (csr; reflexivity).
  destruct (pc_C (fx := fx) al_rom r4 m2 px parr ltac:(lia) ltac:(lia) Hparr SOKpx2 Hres2 F9 F8) as (r5 & RUN5 & U2 & U1 & U10 & U9 & U8 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
  set (M3 := wbytes m2 _ _).
  assert (HW3 : W C A2 M3 (with_vmmaps vm2 md)).
  { subst M3. apply (W_store_blk C A2 m2 _ (Z_to_bv 64 px) _ 32 _ CK HWb Lpx2 L00); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (PM3 : POSTM C A s m M3).
  { apply (POSTM_trans C A s m M2 M3); [exact PM2|]. apply (POSTM_trans C A s M2 m2 M3); [apply (POSTM_sub C A A1 _ _ _ SUBa); eapply POSTM_mono; [|exact PMb]; lia|].
    subst M3. apply (POSTM_blk C A A2 m2 _ (Z_to_bv 64 px) _ 32 _ s CK HWb Lpx2 L0 SUBab); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  assert (REC4 : RECat M3 px (pixa_flds 0 10 1 parr 0)).
  { subst M3. eapply (REC_wr' _ _ (pixa_flds 0 10 1 0 0) _ 4 8); [exact REC3 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity]. }
  assert (CE3 : pc_cells M3 s ret regs).
  { unfold pc_cells. apply (cellsZ_out m2 M3 px (px + 32)); [| forall_cells |].
    - intros x Hx. subst M3. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
    - apply (cellsZ_frm C (s - 32) M2 m2); [exact CK | exact (proj1 PMb) | lia | forall_cells | exact CE2]. }
  assert (U2' : getr r5 2 = Z_to_bv 64 (s - 32)) by (rewrite U2; csr; reflexivity).
  assert (U4 : getr r5 4 = Z_to_bv 64 352880) by (csr; reflexivity).
  apply (boxaCreate10_W (fx := fx) C A2 M3 _ r5 (s - 32) (Z_to_bv 64 0x182d4) S CK HW3 U2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U4 U10
           (kR - 1 - 1) (bR - alloc_margin (1 * 32) - alloc_margin (10 * 8)) ltac:(rewrite with_vmmaps_vmmaps; exact Hroom2) ltac:(lia)
           ltac:(rewrite !pxc_am by lia; lia)).
  intros A3 m3 vm3 r6 HWc CSc PMc OUTc Hroom3. rewrite with_vmmaps_twice in HWc. rewrite with_vmmaps_twice.
  replace (Z_to_bv 64 0x182d4) with (0x182d4 : word) by (apply bv_eq; reflexivity).
  assert (V2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (V9 : getr r6 8 = Z_to_bv 64 px) by (csr; reflexivity).
  destruct OUTc as (ba & barr & A10 & BN).
  pose proof BN as (RB & Halb & Hbarr1 & Halr & NEab & Lb2 & Lr2 & L0b & L0r & Lb3 & Lr3 & LEQ3 & TOPb1 & TOPb2).
  pose proof (pxc_bwf m3 ba 0 10 1 barr RB) as (_ & _ & Wbarr & Wba0 & Wba).
  destruct (blk_range C A3 m3 _ (Z_to_bv 64 ba) 24 CK HWc Lb3 ltac:(lia)) as [Gba _]. rewrite u_Z2bv in Gba by lia.
  assert (N1 : ba <> px) by (intros ->; congruence).
  assert (N2 : barr <> px) by (intros ->; congruence).
  assert (N3 : ba <> parr) by (intros ->; congruence).
  assert (N4 : barr <> parr) by (intros ->; congruence).
  assert (Lpx3 : live A3 (Z_to_bv 64 px) = Some 32%Z).
  { rewrite (LEQ3 (Z_to_bv 64 px)); [exact Lpx2 | exact (zneq_w px ba ltac:(lia) ltac:(lia) (not_eq_sym N1)) | exact (zneq_w px barr ltac:(lia) ltac:(lia) (not_eq_sym N2))]. }
  assert (REC5 : RECat m3 px (pixa_flds 0 10 1 parr 0)).
  { apply (RECat_POSTM C A2 (s - 32) M3 m3 (Z_to_bv 64 px) 32 _ _ REC4 PMc Lpx2); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
  assert (CE5 : pc_cells m3 s ret regs).
  { unfold pc_cells. apply (cellsZ_frm C (s - 32) M3 m3); [exact CK | exact (proj1 PMc) | lia | forall_cells | exact CE3]. }
  pose proof CE5 as (D8 & D16 & D24 & _).
  assert (PM5 : POSTM C A s m m3).
  { apply (POSTM_trans C A s m M3 m3); [exact PM3|]. apply (POSTM_sub C A A2 _ _ _ SUBab). eapply POSTM_mono; [|exact PMc]. lia. }
  assert (LAparr : live A (Z_to_bv 64 parr) = None).
  { destruct (live A (Z_to_bv 64 parr)) as [k|] eqn:E; [pose proof (SUBa _ _ E); congruence | reflexivity]. }
  assert (SOKpx3 : store_ok SEGS m3 (Z_to_bv 64 px) 32 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m3 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m3 px _ x REC5 ltac:(cbn; lia) E). }
  assert (Rparr : rdn SEGS m3 (Z_to_bv 64 (px + 16)) 8 = Some (Z_to_le_bytes 8 parr)).
  { eapply (REC_rd' SEGS _ _ (pixa_flds 0 10 1 parr 0) 4 8); [exact REC5 | cbn; lia | reflexivity | reflexivity | reflexivity]. }
  destruct (pc_D (fx := fx) al_rom r6 m3 s px parr ba ret (getr regs 8) (getr regs 9)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKpx3 ltac:(lia) Rparr D8 D16 D24 V2 A10 V9)
    as (r7 & RUN7 & W2 & W1 & W10 & W8 & W9 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN7 |].
  set (M4 := wbytes m3 _ _).
  assert (SUBc : sub_live A2 A3) by (eapply sub_live_new2; [exact Lb2 | exact Lr2 | exact Lb3 | exact Lr3 | exact LEQ3]).
  assert (WP4 : W C A3 M4 (with_vmmaps vm3 md) /\ POSTM C A s m M4).
  { subst M4. apply (WP_blk C A A3 m m3 _ (Z_to_bv 64 px) _ 32); [exact CK | | exact Lpx3 | exact L0 | exact L00 | exact (sub_live_trans _ _ _ SUBab SUBc)
                                                                 | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWc | exact PM5]. }
  destruct WP4 as [HW4 PM4].
  assert (REC6 : RECat M4 px (pixa_flds 0 10 1 parr ba)).
  { subst M4. eapply (REC_wr' _ _ (pixa_flds 0 10 1 parr 0) _ 5 8); [exact REC5 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity]. }
  assert (RB4 : RECat M4 ba (boxa_flds 0 10 1 barr)).
  { subst M4. apply RECat_out; [exact RB | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [flds_len boxa_flds Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
    pose proof (ai_live_disjoint A3 m3 _ _ _ _ _ (w_inv _ _ _ _ HWc) Lpx3 Lb3 (zneq_w px ba ltac:(lia) ltac:(lia) (not_eq_sym N1))) as D.
    rewrite !u_Z2bv in D by lia. change (round16 32) with 32%Z in D. change (round16 24) with 32%Z in D. lia. }
  apply (HK A3 M4 vm3 r7 px parr ba barr HW4).
  - apply cs_kept_intro; csr; rewrite ?W8, ?W9; try reflexivity.
  - exact PM4.
  - exact (sub_live_trans _ _ _ SUBab SUBc).
  - exact W10.
  - split; [exact (pxc_cells M4 px parr ba barr REC6 RB4) |].
    split.
    + refine (conj _ (conj _ (conj _ (conj _ _)))); [lia | lia | lia | lia |].
      split; [exact Lpx3 |].
      split; [rewrite (LEQ3 _ (not_eq_sym (zneq_w ba parr ltac:(lia) ltac:(lia) N3)) (not_eq_sym (zneq_w barr parr ltac:(lia) ltac:(lia) N4))); exact Lparr2 |].
      split; [exact Lb3 |].
      split; [change (8 * 10)%Z with 80%Z in Lr3; exact Lr3 |].
      split; [exact L00 |]. split; [exact L0parr |]. split; [exact L0b | exact L0r].
    + split; [exact L0 |]. split; [exact LAparr |].
      split; [rewrite <- (LEQ _ (zneq_w ba px ltac:(lia) ltac:(lia) N1)), <- (LEQ2 _ (zneq_w ba parr ltac:(lia) ltac:(lia) N3)); exact Lb2 |].
      split; [rewrite <- (LEQ _ (zneq_w barr px ltac:(lia) ltac:(lia) N2)), <- (LEQ2 _ (zneq_w barr parr ltac:(lia) ltac:(lia) N4)); exact Lr2 |].
      split; [| exact (not_eq_sym N4)].
      intros q Hq. rewrite (LEQ3 q), (LEQ2 q), (LEQ q); [reflexivity | ..];
        intros E; apply Hq; rewrite E; cbn [In]; repeat first [left; reflexivity | right].
  - replace (kR - 4)%Z with (kR - 1 - 1 - 2)%Z by lia.
    replace (bR - 4 * 2 ^ 17)%Z with (bR - alloc_margin (1 * 32) - alloc_margin (10 * 8) - alloc_margin (1 * 24) - alloc_margin (10 * 8))%Z
      by (rewrite !pxc_am by lia; lia).
    exact Hroom3.
Qed.
End Chain.
