(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib MemsetLib As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac ArtLeaf ArtAllocG ArtPoison ArtRuns ArtRunsMem ArtFp As0IntMemset ArtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_6b860_6b9b8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition art_ia_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8
    (Wf (Wf (Wf (Wn 1 (Wf
      (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
          0x16d5c8 256)
      0x15fd48 art_ia_k1 0) 0xded40 0) 0xded48 art_ia_k2 0) 0x11ed80 art_ia_k3 0) 0x11fb00 art_ia_k4 0)
    0x11fb00 4096) 0x11fb08 0x11fb10) 0x16d5c8 1) 0x16d5c9 0.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_int_memset0 : forall (X rom : word -> option byte) a (k : nat) regs (ret : word),
  wokA X a k -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (Z.of_nat k) -> getr regs 1 = ret ->
  exists regs', msteps ASEGS (mkst regs (0x71360 : word) X rom) (mkst regs' ret (Wf X a k 0) rom) /\ getr regs' 10 = Z_to_bv 64 a /\ ms_agree regs regs'.
Proof.
  intros X rom a k regs ret OK Ha Hk Hret H10 H11 H12 H1.
  pose proof (int_memset_run X (Z_to_bv 64 a) (Z_to_bv 64 0) ret (Z.of_nat k) rom ltac:(lia) ltac:(rewrite art_u_lit by lia; lia)) as T.
  rewrite Nat2Z.id in T. specialize (T OK Hret regs H10 H11 H12 H1 ltac:(rewrite art_u_lit by lia; lia)).
  rewrite art_cbyte0 in T. exact T.
Qed.

(* [comment removed for export] *)
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
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x633000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x16d5c8 4 0 -> wrA M 0x16d5c8 4 -> wrA M 0xded40 0x81030 ->
  cellA M 0xd5898 8 0x16d5e0 -> cellA M 0x16d5e0 8 4096 ->
  exists regs', msteps ASEGS (mkst regs (0x6b860 : word) M rom) (mkst regs' raw (art_ia_mem M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 0xded40 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2.
  pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
  eassert (RUN0a : msteps ASEGS (mkst regs (0x6b860 : word) M rom) _).
  {
    zstep F_6b860 D_6b860.
    zsd F_6b864 D_6b864 (sp - 8) (U raw) ltac:(rewok W).
    zsd F_6b868 D_6b868 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_6b86c D_6b86c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_6b870 D_6b870 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_6b874 D_6b874 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_6b878 D_6b878. zstep F_6b87c D_6b87c.
    destruct (cell4_split M 0x16d5c8 0 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & Cb1 & Cb2).
    change (0 mod 256) with 0 in Cb0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cb0' : cellA X 0x16d5c8 1 0) by (recell Cb0) end.
    zlb F_6b880 D_6b880 0x16d5c8 Cb0'.
    stepfence F_6b884 D_6b884.
    zbft F_6b888 D_6b888.
    zstep F_6b88c D_6b88c. zstep F_6b890 D_6b890. zstep F_6b894 D_6b894.
    stepn F_6b898 D_6b898. rwH. zclosed 0x16d5c8.
    stepn F_6b89c D_6b89c. rwH. zclosed 1.
    stepn F_6b8a0 D_6b8a0. rwH. zclosed 8.
    stepn F_6b8a4 D_6b8a4. rwH. zclosed 65280.
    stepn F_6b8a8 D_6b8a8. rwH. zclosed 256.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cw' : cellA X 0x16d5c8 4 0) by (recell Cw); assert (Ww' : wokA X 0x16d5c8 4) by (rewok Ww) end.
    zcas6 F_6b8ac D_6b8ac F_6b8b0 D_6b8b0 F_6b8b4 D_6b8b4 F_6b8b8 D_6b8b8 F_6b8bc D_6b8bc F_6b8c0 D_6b8c0 0x16d5c8 0 256 256 256 Cw' Ww'.
    zbft F_6b8c4 D_6b8c4.
    stepn F_6b8c8 D_6b8c8. rwH. zclosed 0.
    stepn F_6b8cc D_6b8cc. rwH. zclosed 0.
    zbft F_6b8d0 D_6b8d0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cw1 : cellA X 0x16d5c8 4 256) by (apply cell_Wn_hit; lia);
      destruct (cell4_split X 0x16d5c8 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (Cl0 & _ & Cl2) end.
    change (256 mod 256) with 0 in Cl0. change (256 / 65536) with 0 in Cl2.
    zlb F_6b8d4 D_6b8d4 0x16d5c8 Cl0.
    zbft F_6b8d8 D_6b8d8.
    zstep F_6b8dc D_6b8dc. zstep F_6b8e0 D_6b8e0. zstep F_6b8e4 D_6b8e4.
    stepn F_6b8e8 D_6b8e8. rwH. zclosed 0x81008.
    zstep F_6b8ec D_6b8ec. zstep F_6b8f0 D_6b8f0. zstep F_6b8f4 D_6b8f4.
    stepn F_6b8f8 D_6b8f8.
    apply mst_refl. }
  match type of RUN0a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb0 : wrA X 0xded40 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x15fd48 art_ia_k1 R (0x6b8fc : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb0); rewrite ?art_ia_k1_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k1_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k1_Z; reflexivity) ltac:(gres; bveq)) as (r1 & RUN0b & _ & HK1) end.
  zkeep HK1 r1 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK1 r1 (8%bv : reg) (Z_to_bv 64 0x16d5c8). zkeep HK1 r1 (9%bv : reg) (Z_to_bv 64 0xded40).
  match type of RUN0b with msteps _ _ ?S1 => eassert (RUN1a : msteps ASEGS S1 _) end.
  {
    zsb F_6b8fc D_6b8fc 0xded40 0 ltac:(zwok').
    zstep F_6b900 D_6b900. zstep F_6b904 D_6b904. zstep F_6b908 D_6b908. zstep F_6b90c D_6b90c.
    stepn F_6b910 D_6b910.
    apply mst_refl. }
  match type of RUN1a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb1 : wrA X 0xded40 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0xded48 art_ia_k2 R (0x6b914 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb1); rewrite ?art_ia_k2_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k2_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k2_Z; reflexivity) ltac:(gres; bveq)) as (r2 & RUN1b & _ & HK2) end.
  zkeep HK2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK2 r2 (8%bv : reg) (Z_to_bv 64 0x16d5c8). zkeep HK2 r2 (9%bv : reg) (Z_to_bv 64 0xded40).
  zkeep HK2 r2 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN1b with msteps _ _ ?S1 => eassert (RUN2a : msteps ASEGS S1 _) end.
  {
    stepn F_6b914 D_6b914. rwH. zclosed 0x40040.
    zstep F_6b918 D_6b918. zstep F_6b91c D_6b91c.
    stepn F_6b920 D_6b920. rwH. zclosed 0xd80.
    zstep F_6b924 D_6b924.
    stepn F_6b928 D_6b928.
    apply mst_refl. }
  match type of RUN2a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb2 : wrA X 0xded40 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x11ed80 art_ia_k3 R (0x6b92c : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb2); rewrite ?art_ia_k3_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k3_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k3_Z; reflexivity) ltac:(gres; bveq)) as (r3 & RUN2b & _ & HK3) end.
  zkeep HK3 r3 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK3 r3 (8%bv : reg) (Z_to_bv 64 0x16d5c8). zkeep HK3 r3 (9%bv : reg) (Z_to_bv 64 0xded40).
  zkeep HK3 r3 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN2b with msteps _ _ ?S1 => eassert (RUN3a : msteps ASEGS S1 _) end.
  {
    zstep F_6b92c D_6b92c.
    stepn F_6b930 D_6b930. rwH. zclosed 0x40dc0.
    zstep F_6b934 D_6b934.
    stepn F_6b938 D_6b938. rwH. zclosed 0x40248.
    zstep F_6b93c D_6b93c.
    stepn F_6b940 D_6b940.
    apply mst_refl. }
  match type of RUN3a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb3 : wrA X 0xded40 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x11fb00 art_ia_k4 R (0x6b944 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb3); rewrite ?art_ia_k4_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k4_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k4_Z; reflexivity) ltac:(gres; bveq)) as (r4 & RUN3b & _ & HK4) end.
  zkeep HK4 r4 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK4 r4 (8%bv : reg) (Z_to_bv 64 0x16d5c8). zkeep HK4 r4 (9%bv : reg) (Z_to_bv 64 0xded40).
  zkeep HK4 r4 (18%bv : reg) (Z_to_bv 64 266240).
  (* [comment removed for export] *)
  eexists. split.
  { eapply msteps_trans; [exact RUN0a|]. eapply msteps_trans; [exact RUN0b|]. eapply msteps_trans; [exact RUN1a|]. eapply msteps_trans; [exact RUN1b|]. eapply msteps_trans; [exact RUN2a|]. eapply msteps_trans; [exact RUN2b|]. eapply msteps_trans; [exact RUN3a|]. eapply msteps_trans; [exact RUN3b|].
    zstep F_6b944 D_6b944.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cps1' : cellA X 0xd5898 8 0x16d5e0) by zcell; assert (Cps2' : cellA X 0x16d5e0 8 4096) by zcell end.
    zld F_6b948 D_6b948 0xd5898 Cps1'.
    zld F_6b94c D_6b94c 0x16d5e0 Cps2'.
    zbtk F_6b950 D_6b950.
    zstep F_6b95c D_6b95c.
    stepn F_6b960 D_6b960. rwH. zclosed 0x40dd0.
    zstep F_6b964 D_6b964. zstep F_6b968 D_6b968.
    zsd F_6b96c D_6b96c 0x11fb00 4096 ltac:(zwok').
    zsd F_6b970 D_6b970 0x11fb08 0x11fb10 ltac:(zwok').
    stepfence F_6b974 D_6b974.
    zsb F_6b978 D_6b978 0x16d5c8 1 ltac:(zwok').
    stepfence F_6b97c D_6b97c.
    zsb F_6b980 D_6b980 0x16d5c9 0 ltac:(zwok').
    zstep F_6b984 D_6b984. zstep F_6b988 D_6b988.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cra : cellA X (sp - 8) 8 (U raw)) by zcell; assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
      assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
      assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell end.
    zld F_6b98c D_6b98c (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_6b990 D_6b990 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
    zld F_6b994 D_6b994 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
    zld F_6b998 D_6b998 (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
    zld F_6b99c D_6b99c (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
    zstep F_6b9a0 D_6b9a0.
    stepret F_6b9a4 D_6b9a4 raw ltac:(gres; reflexivity).
    apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | reflexivity | unfold art_ia_mem; zmem_eq]. }
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [repeat first [ progress gres | match goal with HK : ms_agree _ ?ri |- context [getr ?ri ?q] => rewrite (ms_agree_getr _ _ q HK) by (cbv; intuition discriminate) end ]; reflexivity|]).
  destruct Hr.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma art_ia_run : forall regs (M rom : word -> option byte) (raw : word) (sp : Z) (ia : bool),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x633000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x16d5c8 4 (if ia then 1 else 0) -> wrA M 0x16d5c8 4 -> wrA M 0xded40 0x81030 ->
  cellA M 0xd5898 8 0x16d5e0 -> cellA M 0x16d5e0 8 4096 ->
  (ia = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0xded48 + 8 * k) 8 0) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x6b860 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 10 = Z_to_bv 64 0xded40 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0xded40, 0x81030); (0x16d5c8, 4)] M M'
    /\ cellA M' 0x16d5c8 4 1 /\ (forall k, 0 <= k < 2 ^ 15 -> cellA M' (0xded48 + 8 * k) 8 0).
Proof.
  intros regs M rom raw sp ia H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2 L1.
  destruct ia.
  - (* [comment removed for export] *)
    destruct (cell4_split M 0x16d5c8 1 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & _ & _). change (1 mod 256) with 1 in Cb0.
    pose proof (art_int_alloc_fn regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cb0) as RUN.
    eexists. eexists. split; [exact RUN|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|].
    split. { eapply art_agree_sub; [zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. repeat split; lia. }
    split; [recell Cw|].
    intros k Hk. specialize (L1 eq_refl k Hk). recell L1.
  - (* [comment removed for export] *)
    destruct (art_ia_init_run regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2) as (regs' & RUN & P10 & P1 & P2 & PK).
    pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
    exists regs', (art_ia_mem M sp raw regs). split; [exact RUN|]. split; [exact P10|]. split; [exact P1|]. split; [exact P2|]. split; [exact PK|].
    split; [unfold art_ia_mem; zgrows|].
    split. { eapply art_agree_sub; [unfold art_ia_mem; zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. rewrite ?K1, ?K2, ?K3, ?K4. repeat split; lia. }
    split.
    + (* [comment removed for export] *)
      change (cellA (art_ia_mem M sp raw regs) 0x16d5c8 4 (1 + 256 * 0 + 65536 * 0)).
      apply cell4_join; [lia|lia|lia|lia|lia| | | ].
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 3 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
        apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|].
        match goal with |- cellA ?X _ _ _ => assert (Cw1 : cellA X 0x16d5c8 4 256) by (apply cell_Wn_hit; lia);
          destruct (cell4_split X 0x16d5c8 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (_ & _ & Cl2) end.
        change (256 / 65536) with 0 in Cl2. exact Cl2.
    + intros k Hk. unfold art_ia_mem.
      do 4 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      do 2 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      apply art_cell8_zero; [lia|lia|]. intros i Hi. replace (0xded48 + 8 * k + i) with (0xded48 + (8 * k + i)) by lia. apply Wf_inside; lia.
Qed.
End FPX.
