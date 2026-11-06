(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib MemsetLib As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm8ArtLeaf Pm8ArtAllocG Pm8ArtPoison ArtRuns ArtRunsMem Pm8ArtFp Pm8IntMemset Pm8ArtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_8c000_8d000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_ia_k1 : nat := Z.to_nat 40.
Definition art_ia_k2 : nat := Z.to_nat 0x40000.
Definition art_ia_k3 : nat := Z.to_nat 0xd80.
Definition art_ia_k4 : nat := Z.to_nat 0x40248.
Lemma art_ia_k1_Z : Z.of_nat art_ia_k1 = 40. Proof. unfold art_ia_k1. apply Z2Nat.id. lia. Qed.
Lemma art_ia_k2_Z : Z.of_nat art_ia_k2 = 0x40000. Proof. unfold art_ia_k2. apply Z2Nat.id. lia. Qed.
Lemma art_ia_k3_Z : Z.of_nat art_ia_k3 = 0xd80. Proof. unfold art_ia_k3. apply Z2Nat.id. lia. Qed.
Lemma art_ia_k4_Z : Z.of_nat art_ia_k4 = 0x40248. Proof. unfold art_ia_k4. apply Z2Nat.id. lia. Qed.
Global Opaque art_ia_k1 art_ia_k2 art_ia_k3 art_ia_k4.

Lemma art_cbyte0 : cbyte (Z_to_bv 64 0) = Z_to_bv 8 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Definition art_ia_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8
    (Wf (Wf (Wf (Wn 1 (Wf
      (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
          0x1ec448 256)
      0x1debc8 art_ia_k1 0) 0x15dbc0 0) 0x15dbc8 art_ia_k2 0) 0x19dc00 art_ia_k3 0) 0x19e980 art_ia_k4 0)
    0x19e980 4096) 0x19e988 0x19e990) 0x1ec448 1) 0x1ec449 0.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_int_memset0 : forall (X rom : word -> option byte) a (k : nat) regs (ret : word),
  wokA X a k -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (Z.of_nat k) -> getr regs 1 = ret ->
  exists regs', msteps ASEGS (mkst regs (0x92640 : word) X rom) (mkst regs' ret (Wf X a k 0) rom) /\ getr regs' 10 = Z_to_bv 64 a /\ ms_agree regs regs'.
Proof.
  intros X rom a k regs ret OK Ha Hk Hret H10 H11 H12 H1.
  pose proof (int_memset_run X (Z_to_bv 64 a) (Z_to_bv 64 0) ret (Z.of_nat k) rom ltac:(lia) ltac:(rewrite art_u_lit by lia; lia)) as T.
  rewrite Nat2Z.id in T. specialize (T OK Hret regs H10 H11 H12 H1 ltac:(rewrite art_u_lit by lia; lia)).
  rewrite art_cbyte0 in T. exact T.
Qed.

Ltac zmemset0 D K EK RET Wb rnew HK :=
  match goal with |- msteps _ (mkst ?R _ ?X ?rom) _ =>
    let RUN := fresh "RUN" in let A10 := fresh "A10" in
    destruct (art_int_memset0 X rom D K R RET ltac:(apply (wr_wok _ _ _ _ Wb); rewrite ?EK; lia) ltac:(lia) ltac:(rewrite EK; lia)
                ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite EK; reflexivity) ltac:(gres; bveq)) as (rnew & RUN & A10 & HK);
    eapply msteps_trans; [exact RUN|]; clear RUN
  end.
Ltac zkeep HK rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite (ms_agree_getr _ _ i HK) by (cbv; intuition discriminate); gres; rwH; reflexivity).

Lemma art_ia_init_run : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x6b3000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1ec448 4 0 -> wrA M 0x1ec448 4 -> wrA M 0x15dbc0 0x81030 ->
  cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 ->
  exists regs', msteps ASEGS (mkst regs (0x8cb40 : word) M rom) (mkst regs' raw (art_ia_mem M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x15dbc0 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2.
  pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
  eassert (RUN0a : msteps ASEGS (mkst regs (0x8cb40 : word) M rom) _).
  {
    zstep F_8caf0 D_8caf0.
    zsd F_8caf4 D_8caf4 (sp - 8) (U raw) ltac:(rewok W).
    zsd F_8caf8 D_8caf8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_8cafc D_8cafc (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_8cb00 D_8cb00 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_8cb04 D_8cb04 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_8cb08 D_8cb08. zstep F_8cb0c D_8cb0c.
    destruct (cell4_split M 0x1ec448 0 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & Cb1 & Cb2).
    change (0 mod 256) with 0 in Cb0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cb0' : cellA X 0x1ec448 1 0) by (recell Cb0) end.
    zlb F_8cb10 D_8cb10 0x1ec448 Cb0'.
    stepfence F_8cb14 D_8cb14.
    zbft F_8cb18 D_8cb18.
    zstep F_8cb1c D_8cb1c. zstep F_8cb20 D_8cb20. zstep F_8cb24 D_8cb24.
    stepn F_8cb28 D_8cb28. rwH. zclosed 0x1ec448.
    stepn F_8cb2c D_8cb2c. rwH. zclosed 1.
    stepn F_8cb30 D_8cb30. rwH. zclosed 8.
    stepn F_8cb34 D_8cb34. rwH. zclosed 65280.
    stepn F_8cb38 D_8cb38. rwH. zclosed 256.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cw' : cellA X 0x1ec448 4 0) by (recell Cw); assert (Ww' : wokA X 0x1ec448 4) by (rewok Ww) end.
    zcas6 F_8cb3c D_8cb3c F_8cb40 D_8cb40 F_8cb44 D_8cb44 F_8cb48 D_8cb48 F_8cb4c D_8cb4c F_8cb50 D_8cb50 0x1ec448 0 256 256 256 Cw' Ww'.
    zbft F_8cb54 D_8cb54.
    stepn F_8cb58 D_8cb58. rwH. zclosed 0.
    stepn F_8cb5c D_8cb5c. rwH. zclosed 0.
    zbft F_8cb60 D_8cb60.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cw1 : cellA X 0x1ec448 4 256) by (apply cell_Wn_hit; lia);
      destruct (cell4_split X 0x1ec448 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (Cl0 & _ & Cl2) end.
    change (256 mod 256) with 0 in Cl0. change (256 / 65536) with 0 in Cl2.
    zlb F_8cb64 D_8cb64 0x1ec448 Cl0.
    zbft F_8cb68 D_8cb68.
    zstep F_8cb6c D_8cb6c. zstep F_8cb70 D_8cb70. zstep F_8cb74 D_8cb74.
    stepn F_8cb78 D_8cb78. rwH. zclosed 0x81008.
    zstep F_8cb7c D_8cb7c. zstep F_8cb80 D_8cb80. zstep F_8cb84 D_8cb84.
    stepn F_8cb88 D_8cb88.
    apply mst_refl. }
  match type of RUN0a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb0 : wrA X 0x15dbc0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x1debc8 art_ia_k1 R (0x8cbdc : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb0); rewrite ?art_ia_k1_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k1_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k1_Z; reflexivity) ltac:(gres; bveq)) as (r1 & RUN0b & _ & HK1) end.
  zkeep HK1 r1 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK1 r1 (8%bv : reg) (Z_to_bv 64 0x1ec448). zkeep HK1 r1 (9%bv : reg) (Z_to_bv 64 0x15dbc0).
  match type of RUN0b with msteps _ _ ?S1 => eassert (RUN1a : msteps ASEGS S1 _) end.
  {
    zsb F_8cb8c D_8cb8c 0x15dbc0 0 ltac:(zwok').
    zstep F_8cb90 D_8cb90. zstep F_8cb94 D_8cb94. zstep F_8cb98 D_8cb98. zstep F_8cb9c D_8cb9c.
    stepn F_8cba0 D_8cba0.
    apply mst_refl. }
  match type of RUN1a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb1 : wrA X 0x15dbc0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x15dbc8 art_ia_k2 R (0x8cbf4 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb1); rewrite ?art_ia_k2_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k2_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k2_Z; reflexivity) ltac:(gres; bveq)) as (r2 & RUN1b & _ & HK2) end.
  zkeep HK2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK2 r2 (8%bv : reg) (Z_to_bv 64 0x1ec448). zkeep HK2 r2 (9%bv : reg) (Z_to_bv 64 0x15dbc0).
  zkeep HK2 r2 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN1b with msteps _ _ ?S1 => eassert (RUN2a : msteps ASEGS S1 _) end.
  {
    stepn F_8cba4 D_8cba4. rwH. zclosed 0x40040.
    zstep F_8cba8 D_8cba8. zstep F_8cbac D_8cbac.
    stepn F_8cbb0 D_8cbb0. rwH. zclosed 0xd80.
    zstep F_8cbb4 D_8cbb4.
    stepn F_8cbb8 D_8cbb8.
    apply mst_refl. }
  match type of RUN2a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb2 : wrA X 0x15dbc0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x19dc00 art_ia_k3 R (0x8cc0c : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb2); rewrite ?art_ia_k3_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k3_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k3_Z; reflexivity) ltac:(gres; bveq)) as (r3 & RUN2b & _ & HK3) end.
  zkeep HK3 r3 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK3 r3 (8%bv : reg) (Z_to_bv 64 0x1ec448). zkeep HK3 r3 (9%bv : reg) (Z_to_bv 64 0x15dbc0).
  zkeep HK3 r3 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN2b with msteps _ _ ?S1 => eassert (RUN3a : msteps ASEGS S1 _) end.
  {
    zstep F_8cbbc D_8cbbc.
    stepn F_8cbc0 D_8cbc0. rwH. zclosed 0x40dc0.
    zstep F_8cbc4 D_8cbc4.
    stepn F_8cbc8 D_8cbc8. rwH. zclosed 0x40248.
    zstep F_8cbcc D_8cbcc.
    stepn F_8cbd0 D_8cbd0.
    apply mst_refl. }
  match type of RUN3a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb3 : wrA X 0x15dbc0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x19e980 art_ia_k4 R (0x8cc24 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb3); rewrite ?art_ia_k4_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k4_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k4_Z; reflexivity) ltac:(gres; bveq)) as (r4 & RUN3b & _ & HK4) end.
  zkeep HK4 r4 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK4 r4 (8%bv : reg) (Z_to_bv 64 0x1ec448). zkeep HK4 r4 (9%bv : reg) (Z_to_bv 64 0x15dbc0).
  zkeep HK4 r4 (18%bv : reg) (Z_to_bv 64 266240).

  eexists. split.
  { eapply msteps_trans; [exact RUN0a|]. eapply msteps_trans; [exact RUN0b|]. eapply msteps_trans; [exact RUN1a|]. eapply msteps_trans; [exact RUN1b|]. eapply msteps_trans; [exact RUN2a|]. eapply msteps_trans; [exact RUN2b|]. eapply msteps_trans; [exact RUN3a|]. eapply msteps_trans; [exact RUN3b|].
    zstep F_8cbd4 D_8cbd4.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cps1' : cellA X 0x153118 8 0x1ec460) by zcell; assert (Cps2' : cellA X 0x1ec460 8 4096) by zcell end.
    zld F_8cbd8 D_8cbd8 0x153118 Cps1'.
    zld F_8cbdc D_8cbdc 0x1ec460 Cps2'.
    zbtk F_8cbe0 D_8cbe0.
    zstep F_8cbec D_8cbec.
    stepn F_8cbf0 D_8cbf0. rwH. zclosed 0x40dd0.
    zstep F_8cbf4 D_8cbf4. zstep F_8cbf8 D_8cbf8.
    zsd F_8cbfc D_8cbfc 0x19e980 4096 ltac:(zwok').
    zsd F_8cc00 D_8cc00 0x19e988 0x19e990 ltac:(zwok').
    stepfence F_8cc04 D_8cc04.
    zsb F_8cc08 D_8cc08 0x1ec448 1 ltac:(zwok').
    stepfence F_8cc0c D_8cc0c.
    zsb F_8cc10 D_8cc10 0x1ec449 0 ltac:(zwok').
    zstep F_8cc14 D_8cc14. zstep F_8cc18 D_8cc18.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cra : cellA X (sp - 8) 8 (U raw)) by zcell; assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
      assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
      assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell end.
    zld F_8cc1c D_8cc1c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_8cc20 D_8cc20 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
    zld F_8cc24 D_8cc24 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
    zld F_8cc28 D_8cc28 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
    zld F_8cc2c D_8cc2c (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
    zstep F_8cc30 D_8cc30.
    stepret F_8cc34 D_8cc34 raw ltac:(gres; reflexivity).
    apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | reflexivity | unfold art_ia_mem; zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [repeat first [ progress gres | match goal with HK : ms_agree _ ?ri |- context [getr ?ri ?q] => rewrite (ms_agree_getr _ _ q HK) by (cbv; intuition discriminate) end ]; reflexivity|]).
  destruct Hr.
Qed.

Lemma art_cell8_zero : forall (M : word -> option byte) a, 0 <= a -> a + 8 < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) -> cellA M a 8 0.
Proof.
  intros M a Ha Ha' B. unfold cell.
  assert (E : forall (n : nat) j, 0 <= j -> j + Z.of_nat n <= 8 -> rdn ASEGS M (Z_to_bv 64 (a + j)) n = Some (repeat (Z_to_bv 8 0) n)).
  { induction n as [|n IH]; intros j Hj Hn; [reflexivity|]. cbn [rdn repeat]. rewrite (B j) by lia.
    replace ((Z_to_bv 64 (a + j) + 1)%bv : word) with (Z_to_bv 64 (a + (j + 1)) : word).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_unsigned (1 : bv 64)%bv) with 1.
        rewrite (Z.mod_small (a + j)) by lia. rewrite !Z.mod_small by lia. lia. }
    rewrite IH by lia. reflexivity. }
  specialize (E 8%nat 0 ltac:(lia) ltac:(cbn; lia)). rewrite Z.add_0_r in E. rewrite E. reflexivity.
Qed.

Lemma art_ia_run : forall regs (M rom : word -> option byte) (raw : word) (sp : Z) (ia : bool),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x6b3000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1ec448 4 (if ia then 1 else 0) -> wrA M 0x1ec448 4 -> wrA M 0x15dbc0 0x81030 ->
  cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 ->
  (ia = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0x15dbc8 + 8 * k) 8 0) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x8cb40 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 10 = Z_to_bv 64 0x15dbc0 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0x15dbc0, 0x81030); (0x1ec448, 4)] M M'
    /\ cellA M' 0x1ec448 4 1 /\ (forall k, 0 <= k < 2 ^ 15 -> cellA M' (0x15dbc8 + 8 * k) 8 0).
Proof.
  intros regs M rom raw sp ia H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2 L1.
  destruct ia.
  -
    destruct (cell4_split M 0x1ec448 1 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & _ & _). change (1 mod 256) with 1 in Cb0.
    pose proof (art_int_alloc_fn regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cb0) as RUN.
    eexists. eexists. split; [exact RUN|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|].
    split. { eapply art_agree_sub; [zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. repeat split; lia. }
    split; [recell Cw|].
    intros k Hk. specialize (L1 eq_refl k Hk). recell L1.
  -
    destruct (art_ia_init_run regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2) as (regs' & RUN & P10 & P1 & P2 & PK).
    pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
    exists regs', (art_ia_mem M sp raw regs). split; [exact RUN|]. split; [exact P10|]. split; [exact P1|]. split; [exact P2|]. split; [exact PK|].
    split; [unfold art_ia_mem; zgrows|].
    split. { eapply art_agree_sub; [unfold art_ia_mem; zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. rewrite ?K1, ?K2, ?K3, ?K4. repeat split; lia. }
    split.
    +
      change (cellA (art_ia_mem M sp raw regs) 0x1ec448 4 (1 + 256 * 0 + 65536 * 0)).
      apply cell4_join; [lia|lia|lia|lia|lia| | | ].
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 3 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
        apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|].
        match goal with |- cellA ?X _ _ _ => assert (Cw1 : cellA X 0x1ec448 4 256) by (apply cell_Wn_hit; lia);
          destruct (cell4_split X 0x1ec448 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (_ & _ & Cl2) end.
        change (256 / 65536) with 0 in Cl2. exact Cl2.
    + intros k Hk. unfold art_ia_mem.
      do 4 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      do 2 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      apply art_cell8_zero; [lia|lia|]. intros i Hi. replace (0x15dbc8 + 8 * k + i) with (0x15dbc8 + (8 * k + i)) by lia. apply Wf_inside; lia.
Qed.
End FPX.
