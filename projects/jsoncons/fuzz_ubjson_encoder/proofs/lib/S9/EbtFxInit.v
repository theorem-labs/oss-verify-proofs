(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib MemsetLib As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison ArtRuns ArtRunsMem EbtFp Eb0IntMemset EbtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r6b6d0_6b828.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
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
          0x1d5b88 256)
      0x1c8308 art_ia_k1 0) 0x147300 0) 0x147308 art_ia_k2 0) 0x187340 art_ia_k3 0) 0x1880c0 art_ia_k4 0)
    0x1880c0 4096) 0x1880c8 0x1880d0) 0x1d5b88 1) 0x1d5b89 0.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_int_memset0 : forall (X rom : word -> option byte) a (k : nat) regs (ret : word),
  wokA X a k -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (Z.of_nat k) -> getr regs 1 = ret ->
  exists regs', msteps ASEGS (mkst regs (0x8c60c : word) X rom) (mkst regs' ret (Wf X a k 0) rom) /\ getr regs' 10 = Z_to_bv 64 a /\ ms_agree regs regs'.
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

#[using="Type"] Lemma art_ia_init_run : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1d5b88 4 0 -> wrA M 0x1d5b88 4 -> wrA M 0x147300 0x81030 ->
  cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  exists regs', msteps ASEGS (mkst regs (0x86b0c : word) M rom) (mkst regs' raw (art_ia_mem M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x147300 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2.
  pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
  eassert (RUN0a : msteps ASEGS (mkst regs (0x86b0c : word) M rom) _).
  {
    zstep F_86abc D_86abc.
    zsd F_86ac0 D_86ac0 (sp - 8) (U raw) ltac:(rewok W).
    zsd F_86ac4 D_86ac4 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_86ac8 D_86ac8 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_86acc D_86acc (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_86ad0 D_86ad0 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_86ad4 D_86ad4. zstep F_86ad8 D_86ad8.
    destruct (cell4_split M 0x1d5b88 0 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & Cb1 & Cb2).
    change (0 mod 256) with 0 in Cb0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cb0' : cellA X 0x1d5b88 1 0) by (recell Cb0) end.
    zlb F_86adc D_86adc 0x1d5b88 Cb0'.
    stepfence F_86ae0 D_86ae0.
    zbft F_86ae4 D_86ae4.
    zstep F_86ae8 D_86ae8. zstep F_86aec D_86aec. zstep F_86af0 D_86af0.
    stepn F_86af4 D_86af4. rwH. zclosed 0x1d5b88.
    stepn F_86af8 D_86af8. rwH. zclosed 1.
    stepn F_86afc D_86afc. rwH. zclosed 8.
    stepn F_86b00 D_86b00. rwH. zclosed 65280.
    stepn F_86b04 D_86b04. rwH. zclosed 256.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cw' : cellA X 0x1d5b88 4 0) by (recell Cw); assert (Ww' : wokA X 0x1d5b88 4) by (rewok Ww) end.
    zcas6 F_86b08 D_86b08 F_86b0c D_86b0c F_86b10 D_86b10 F_86b14 D_86b14 F_86b18 D_86b18 F_86b1c D_86b1c 0x1d5b88 0 256 256 256 Cw' Ww'.
    zbft F_86b20 D_86b20.
    stepn F_86b24 D_86b24. rwH. zclosed 0.
    stepn F_86b28 D_86b28. rwH. zclosed 0.
    zbft F_86b2c D_86b2c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cw1 : cellA X 0x1d5b88 4 256) by (apply cell_Wn_hit; lia);
      destruct (cell4_split X 0x1d5b88 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (Cl0 & _ & Cl2) end.
    change (256 mod 256) with 0 in Cl0. change (256 / 65536) with 0 in Cl2.
    zlb F_86b30 D_86b30 0x1d5b88 Cl0.
    zbft F_86b34 D_86b34.
    zstep F_86b38 D_86b38. zstep F_86b3c D_86b3c. zstep F_86b40 D_86b40.
    stepn F_86b44 D_86b44. rwH. zclosed 0x81008.
    zstep F_86b48 D_86b48. zstep F_86b4c D_86b4c. zstep F_86b50 D_86b50.
    stepn F_86b54 D_86b54.
    apply mst_refl. }
  match type of RUN0a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb0 : wrA X 0x147300 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x1c8308 art_ia_k1 R (0x86ba8 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb0); rewrite ?art_ia_k1_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k1_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k1_Z; reflexivity) ltac:(gres; bveq)) as (r1 & RUN0b & _ & HK1) end.
  zkeep HK1 r1 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK1 r1 (8%bv : reg) (Z_to_bv 64 0x1d5b88). zkeep HK1 r1 (9%bv : reg) (Z_to_bv 64 0x147300).
  match type of RUN0b with msteps _ _ ?S1 => eassert (RUN1a : msteps ASEGS S1 _) end.
  {
    zsb F_86b58 D_86b58 0x147300 0 ltac:(zwok').
    zstep F_86b5c D_86b5c. zstep F_86b60 D_86b60. zstep F_86b64 D_86b64. zstep F_86b68 D_86b68.
    stepn F_86b6c D_86b6c.
    apply mst_refl. }
  match type of RUN1a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb1 : wrA X 0x147300 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x147308 art_ia_k2 R (0x86bc0 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb1); rewrite ?art_ia_k2_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k2_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k2_Z; reflexivity) ltac:(gres; bveq)) as (r2 & RUN1b & _ & HK2) end.
  zkeep HK2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK2 r2 (8%bv : reg) (Z_to_bv 64 0x1d5b88). zkeep HK2 r2 (9%bv : reg) (Z_to_bv 64 0x147300).
  zkeep HK2 r2 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN1b with msteps _ _ ?S1 => eassert (RUN2a : msteps ASEGS S1 _) end.
  {
    stepn F_86b70 D_86b70. rwH. zclosed 0x40040.
    zstep F_86b74 D_86b74. zstep F_86b78 D_86b78.
    stepn F_86b7c D_86b7c. rwH. zclosed 0xd80.
    zstep F_86b80 D_86b80.
    stepn F_86b84 D_86b84.
    apply mst_refl. }
  match type of RUN2a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb2 : wrA X 0x147300 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x187340 art_ia_k3 R (0x86bd8 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb2); rewrite ?art_ia_k3_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k3_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k3_Z; reflexivity) ltac:(gres; bveq)) as (r3 & RUN2b & _ & HK3) end.
  zkeep HK3 r3 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK3 r3 (8%bv : reg) (Z_to_bv 64 0x1d5b88). zkeep HK3 r3 (9%bv : reg) (Z_to_bv 64 0x147300).
  zkeep HK3 r3 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN2b with msteps _ _ ?S1 => eassert (RUN3a : msteps ASEGS S1 _) end.
  {
    zstep F_86b88 D_86b88.
    stepn F_86b8c D_86b8c. rwH. zclosed 0x40dc0.
    zstep F_86b90 D_86b90.
    stepn F_86b94 D_86b94. rwH. zclosed 0x40248.
    zstep F_86b98 D_86b98.
    stepn F_86b9c D_86b9c.
    apply mst_refl. }
  match type of RUN3a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb3 : wrA X 0x147300 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x1880c0 art_ia_k4 R (0x86bf0 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb3); rewrite ?art_ia_k4_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k4_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k4_Z; reflexivity) ltac:(gres; bveq)) as (r4 & RUN3b & _ & HK4) end.
  zkeep HK4 r4 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK4 r4 (8%bv : reg) (Z_to_bv 64 0x1d5b88). zkeep HK4 r4 (9%bv : reg) (Z_to_bv 64 0x147300).
  zkeep HK4 r4 (18%bv : reg) (Z_to_bv 64 266240).

  eexists. split.
  { eapply msteps_trans; [exact RUN0a|]. eapply msteps_trans; [exact RUN0b|]. eapply msteps_trans; [exact RUN1a|]. eapply msteps_trans; [exact RUN1b|]. eapply msteps_trans; [exact RUN2a|]. eapply msteps_trans; [exact RUN2b|]. eapply msteps_trans; [exact RUN3a|]. eapply msteps_trans; [exact RUN3b|].
    zstep F_86ba0 D_86ba0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cps1' : cellA X 0x13d8a8 8 0x1d5ba0) by zcell; assert (Cps2' : cellA X 0x1d5ba0 8 4096) by zcell end.
    zld F_86ba4 D_86ba4 0x13d8a8 Cps1'.
    zld F_86ba8 D_86ba8 0x1d5ba0 Cps2'.
    zbtk F_86bac D_86bac.
    zstep F_86bb8 D_86bb8.
    stepn F_86bbc D_86bbc. rwH. zclosed 0x40dd0.
    zstep F_86bc0 D_86bc0. zstep F_86bc4 D_86bc4.
    zsd F_86bc8 D_86bc8 0x1880c0 4096 ltac:(zwok').
    zsd F_86bcc D_86bcc 0x1880c8 0x1880d0 ltac:(zwok').
    stepfence F_86bd0 D_86bd0.
    zsb F_86bd4 D_86bd4 0x1d5b88 1 ltac:(zwok').
    stepfence F_86bd8 D_86bd8.
    zsb F_86bdc D_86bdc 0x1d5b89 0 ltac:(zwok').
    zstep F_86be0 D_86be0. zstep F_86be4 D_86be4.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cra : cellA X (sp - 8) 8 (U raw)) by zcell; assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
      assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
      assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell end.
    zld F_86be8 D_86be8 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_86bec D_86bec (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
    zld F_86bf0 D_86bf0 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
    zld F_86bf4 D_86bf4 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
    zld F_86bf8 D_86bf8 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
    zstep F_86bfc D_86bfc.
    stepret F_86c00 D_86c00 raw ltac:(gres; reflexivity).
    apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | reflexivity | unfold art_ia_mem; zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [repeat first [ progress gres | match goal with HK : ms_agree _ ?ri |- context [getr ?ri ?q] => rewrite (ms_agree_getr _ _ q HK) by (cbv; intuition discriminate) end ]; reflexivity|]).
  destruct Hr.
Qed.

#[using="Type"] Lemma art_cell8_zero : forall (M : word -> option byte) a, 0 <= a -> a + 8 < 2 ^ 64 ->
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

#[using="Type"] Lemma art_ia_run : forall regs (M rom : word -> option byte) (raw : word) (sp : Z) (ia : bool),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1d5b88 4 (if ia then 1 else 0) -> wrA M 0x1d5b88 4 -> wrA M 0x147300 0x81030 ->
  cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  (ia = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0x147308 + 8 * k) 8 0) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x86b0c : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 10 = Z_to_bv 64 0x147300 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0x147300, 0x81030); (0x1d5b88, 4)] M M'
    /\ cellA M' 0x1d5b88 4 1 /\ (forall k, 0 <= k < 2 ^ 15 -> cellA M' (0x147308 + 8 * k) 8 0).
Proof.
  intros regs M rom raw sp ia H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2 L1.
  destruct ia.
  -
    destruct (cell4_split M 0x1d5b88 1 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & _ & _). change (1 mod 256) with 1 in Cb0.
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
      change (cellA (art_ia_mem M sp raw regs) 0x1d5b88 4 (1 + 256 * 0 + 65536 * 0)).
      apply cell4_join; [lia|lia|lia|lia|lia| | | ].
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 3 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
        apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|].
        match goal with |- cellA ?X _ _ _ => assert (Cw1 : cellA X 0x1d5b88 4 256) by (apply cell_Wn_hit; lia);
          destruct (cell4_split X 0x1d5b88 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (_ & _ & Cl2) end.
        change (256 / 65536) with 0 in Cl2. exact Cl2.
    + intros k Hk. unfold art_ia_mem.
      do 4 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      do 2 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      apply art_cell8_zero; [lia|lia|]. intros i Hi. replace (0x147308 + 8 * k + i) with (0x147308 + (8 * k + i)) by lia. apply Wf_inside; lia.
Qed.
End FPX.
