(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac RefMemcpyLib MemsetLib As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm5ArtLeaf Pm5ArtAllocG Pm5ArtPoison ArtRuns ArtRunsMem Pm5ArtFp Pm5IntMemset Pm5ArtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_8e000_8f000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
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
          0x1fd248 256)
      0x1ef9c8 art_ia_k1 0) 0x16e9c0 0) 0x16e9c8 art_ia_k2 0) 0x1aea00 art_ia_k3 0) 0x1af780 art_ia_k4 0)
    0x1af780 4096) 0x1af788 0x1af790) 0x1fd248 1) 0x1fd249 0.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_int_memset0 : forall (X rom : word -> option byte) a (k : nat) regs (ret : word),
  wokA X a k -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (Z.of_nat k) -> getr regs 1 = ret ->
  exists regs', msteps ASEGS (mkst regs (0x942dc : word) X rom) (mkst regs' ret (Wf X a k 0) rom) /\ getr regs' 10 = Z_to_bv 64 a /\ ms_agree regs regs'.
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
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x6c4000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1fd248 4 0 -> wrA M 0x1fd248 4 -> wrA M 0x16e9c0 0x81030 ->
  cellA M 0x1644f8 8 0x1fd260 -> cellA M 0x1fd260 8 4096 ->
  exists regs', msteps ASEGS (mkst regs (0x8e7dc : word) M rom) (mkst regs' raw (art_ia_mem M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x16e9c0 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2.
  pose proof art_ia_k1_Z as K1. pose proof art_ia_k2_Z as K2. pose proof art_ia_k3_Z as K3. pose proof art_ia_k4_Z as K4.
  eassert (RUN0a : msteps ASEGS (mkst regs (0x8e7dc : word) M rom) _).
  {
    zstep F_8e794 D_8e794.
    zsd F_8e798 D_8e798 (sp - 8) (U raw) ltac:(rewok W).
    zsd F_8e79c D_8e79c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_8e7a0 D_8e7a0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_8e7a4 D_8e7a4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_8e7a8 D_8e7a8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_8e7ac D_8e7ac. zstep F_8e7b0 D_8e7b0.
    destruct (cell4_split M 0x1fd248 0 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & Cb1 & Cb2).
    change (0 mod 256) with 0 in Cb0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cb0' : cellA X 0x1fd248 1 0) by (recell Cb0) end.
    zlb F_8e7b4 D_8e7b4 0x1fd248 Cb0'.
    stepfence F_8e7b8 D_8e7b8.
    zbft F_8e7bc D_8e7bc.
    zstep F_8e7c0 D_8e7c0. zstep F_8e7c4 D_8e7c4. zstep F_8e7c8 D_8e7c8.
    stepn F_8e7cc D_8e7cc. rwH. zclosed 0x1fd248.
    stepn F_8e7d0 D_8e7d0. rwH. zclosed 1.
    stepn F_8e7d4 D_8e7d4. rwH. zclosed 8.
    stepn F_8e7d8 D_8e7d8. rwH. zclosed 65280.
    stepn F_8e7dc D_8e7dc. rwH. zclosed 256.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cw' : cellA X 0x1fd248 4 0) by (recell Cw); assert (Ww' : wokA X 0x1fd248 4) by (rewok Ww) end.
    zcas6 F_8e7e0 D_8e7e0 F_8e7e4 D_8e7e4 F_8e7e8 D_8e7e8 F_8e7ec D_8e7ec F_8e7f0 D_8e7f0 F_8e7f4 D_8e7f4 0x1fd248 0 256 256 256 Cw' Ww'.
    zbft F_8e7f8 D_8e7f8.
    stepn F_8e7fc D_8e7fc. rwH. zclosed 0.
    stepn F_8e800 D_8e800. rwH. zclosed 0.
    zbft F_8e804 D_8e804.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cw1 : cellA X 0x1fd248 4 256) by (apply cell_Wn_hit; lia);
      destruct (cell4_split X 0x1fd248 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (Cl0 & _ & Cl2) end.
    change (256 mod 256) with 0 in Cl0. change (256 / 65536) with 0 in Cl2.
    zlb F_8e808 D_8e808 0x1fd248 Cl0.
    zbft F_8e80c D_8e80c.
    zstep F_8e810 D_8e810. zstep F_8e814 D_8e814. zstep F_8e818 D_8e818.
    stepn F_8e81c D_8e81c. rwH. zclosed 0x81008.
    zstep F_8e820 D_8e820. zstep F_8e824 D_8e824. zstep F_8e828 D_8e828.
    stepn F_8e82c D_8e82c.
    apply mst_refl. }
  match type of RUN0a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb0 : wrA X 0x16e9c0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x1ef9c8 art_ia_k1 R (0x8e878 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb0); rewrite ?art_ia_k1_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k1_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k1_Z; reflexivity) ltac:(gres; bveq)) as (r1 & RUN0b & _ & HK1) end.
  zkeep HK1 r1 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK1 r1 (8%bv : reg) (Z_to_bv 64 0x1fd248). zkeep HK1 r1 (9%bv : reg) (Z_to_bv 64 0x16e9c0).
  match type of RUN0b with msteps _ _ ?S1 => eassert (RUN1a : msteps ASEGS S1 _) end.
  {
    zsb F_8e830 D_8e830 0x16e9c0 0 ltac:(zwok').
    zstep F_8e834 D_8e834. zstep F_8e838 D_8e838. zstep F_8e83c D_8e83c. zstep F_8e840 D_8e840.
    stepn F_8e844 D_8e844.
    apply mst_refl. }
  match type of RUN1a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb1 : wrA X 0x16e9c0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x16e9c8 art_ia_k2 R (0x8e890 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb1); rewrite ?art_ia_k2_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k2_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k2_Z; reflexivity) ltac:(gres; bveq)) as (r2 & RUN1b & _ & HK2) end.
  zkeep HK2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK2 r2 (8%bv : reg) (Z_to_bv 64 0x1fd248). zkeep HK2 r2 (9%bv : reg) (Z_to_bv 64 0x16e9c0).
  zkeep HK2 r2 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN1b with msteps _ _ ?S1 => eassert (RUN2a : msteps ASEGS S1 _) end.
  {
    stepn F_8e848 D_8e848. rwH. zclosed 0x40040.
    zstep F_8e84c D_8e84c. zstep F_8e850 D_8e850.
    stepn F_8e854 D_8e854. rwH. zclosed 0xd80.
    zstep F_8e858 D_8e858.
    stepn F_8e85c D_8e85c.
    apply mst_refl. }
  match type of RUN2a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb2 : wrA X 0x16e9c0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x1aea00 art_ia_k3 R (0x8e8a8 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb2); rewrite ?art_ia_k3_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k3_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k3_Z; reflexivity) ltac:(gres; bveq)) as (r3 & RUN2b & _ & HK3) end.
  zkeep HK3 r3 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK3 r3 (8%bv : reg) (Z_to_bv 64 0x1fd248). zkeep HK3 r3 (9%bv : reg) (Z_to_bv 64 0x16e9c0).
  zkeep HK3 r3 (19%bv : reg) (Z_to_bv 64 262144).
  match type of RUN2b with msteps _ _ ?S1 => eassert (RUN3a : msteps ASEGS S1 _) end.
  {
    zstep F_8e860 D_8e860.
    stepn F_8e864 D_8e864. rwH. zclosed 0x40dc0.
    zstep F_8e868 D_8e868.
    stepn F_8e86c D_8e86c. rwH. zclosed 0x40248.
    zstep F_8e870 D_8e870.
    stepn F_8e874 D_8e874.
    apply mst_refl. }
  match type of RUN3a with msteps _ _ (mkst ?R _ ?X _) => assert (Wb3 : wrA X 0x16e9c0 0x81030) by zwr;
    destruct (art_int_memset0 X rom 0x1af780 art_ia_k4 R (0x8e8c0 : bv 64)%bv ltac:(apply (wr_wok _ _ _ _ Wb3); rewrite ?art_ia_k4_Z; lia) ltac:(lia) ltac:(rewrite art_ia_k4_Z; lia) ltac:(unfold ret_ok; bveq)
                ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rewrite art_ia_k4_Z; reflexivity) ltac:(gres; bveq)) as (r4 & RUN3b & _ & HK4) end.
  zkeep HK4 r4 (2%bv : reg) (Z_to_bv 64 (sp + -48)). zkeep HK4 r4 (8%bv : reg) (Z_to_bv 64 0x1fd248). zkeep HK4 r4 (9%bv : reg) (Z_to_bv 64 0x16e9c0).
  zkeep HK4 r4 (18%bv : reg) (Z_to_bv 64 266240).
  (* [comment removed for export] *)
  eexists. split.
  { eapply msteps_trans; [exact RUN0a|]. eapply msteps_trans; [exact RUN0b|]. eapply msteps_trans; [exact RUN1a|]. eapply msteps_trans; [exact RUN1b|]. eapply msteps_trans; [exact RUN2a|]. eapply msteps_trans; [exact RUN2b|]. eapply msteps_trans; [exact RUN3a|]. eapply msteps_trans; [exact RUN3b|].
    zstep F_8e878 D_8e878.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cps1' : cellA X 0x1644f8 8 0x1fd260) by zcell; assert (Cps2' : cellA X 0x1fd260 8 4096) by zcell end.
    zld F_8e87c D_8e87c 0x1644f8 Cps1'.
    zld F_8e880 D_8e880 0x1fd260 Cps2'.
    zbtk F_8e884 D_8e884.
    zstep F_8e890 D_8e890.
    stepn F_8e894 D_8e894. rwH. zclosed 0x40dd0.
    zstep F_8e898 D_8e898. zstep F_8e89c D_8e89c.
    zsd F_8e8a0 D_8e8a0 0x1af780 4096 ltac:(zwok').
    zsd F_8e8a4 D_8e8a4 0x1af788 0x1af790 ltac:(zwok').
    stepfence F_8e8a8 D_8e8a8.
    zsb F_8e8ac D_8e8ac 0x1fd248 1 ltac:(zwok').
    stepfence F_8e8b0 D_8e8b0.
    zsb F_8e8b4 D_8e8b4 0x1fd249 0 ltac:(zwok').
    zstep F_8e8b8 D_8e8b8. zstep F_8e8bc D_8e8bc.
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cra : cellA X (sp - 8) 8 (U raw)) by zcell; assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
      assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
      assert (Cs3 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell end.
    zld F_8e8c0 D_8e8c0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
    zld F_8e8c4 D_8e8c4 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
    zld F_8e8c8 D_8e8c8 (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
    zld F_8e8cc D_8e8cc (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
    zld F_8e8d0 D_8e8d0 (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
    zstep F_8e8d4 D_8e8d4.
    stepret F_8e8d8 D_8e8d8 raw ltac:(gres; reflexivity).
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
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 48 <= sp -> sp < 2 ^ 64 -> 0x6c4000 + 48 <= sp ->
  wrA M (sp - 48) 48 -> cellA M 0x1fd248 4 (if ia then 1 else 0) -> wrA M 0x1fd248 4 -> wrA M 0x16e9c0 0x81030 ->
  cellA M 0x1644f8 8 0x1fd260 -> cellA M 0x1fd260 8 4096 ->
  (ia = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0x16e9c8 + 8 * k) 8 0) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x8e7dc : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 10 = Z_to_bv 64 0x16e9c0 /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0x16e9c0, 0x81030); (0x1fd248, 4)] M M'
    /\ cellA M' 0x1fd248 4 1 /\ (forall k, 0 <= k < 2 ^ 15 -> cellA M' (0x16e9c8 + 8 * k) 8 0).
Proof.
  intros regs M rom raw sp ia H1 Hret H2 Hsp Hsp' IMG W Cw Ww Wbss Cps1 Cps2 L1.
  destruct ia.
  - (* [comment removed for export] *)
    destruct (cell4_split M 0x1fd248 1 ltac:(lia) ltac:(lia) ltac:(lia) Cw) as (Cb0 & _ & _). change (1 mod 256) with 1 in Cb0.
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
      change (cellA (art_ia_mem M sp raw regs) 0x1fd248 4 (1 + 256 * 0 + 65536 * 0)).
      apply cell4_join; [lia|lia|lia|lia|lia| | | ].
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. zcell.
      * unfold art_ia_mem. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        do 3 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
        apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
        apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|].
        match goal with |- cellA ?X _ _ _ => assert (Cw1 : cellA X 0x1fd248 4 256) by (apply cell_Wn_hit; lia);
          destruct (cell4_split X 0x1fd248 256 ltac:(lia) ltac:(lia) ltac:(lia) Cw1) as (_ & _ & Cl2) end.
        change (256 / 65536) with 0 in Cl2. exact Cl2.
    + intros k Hk. unfold art_ia_mem.
      do 4 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      do 2 (apply cell_Wf_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      apply art_cell8_zero; [lia|lia|]. intros i Hi. replace (0x16e9c8 + 8 * k + i) with (0x16e9c8 + (8 * k + i)) by lia. apply Wf_inside; lia.
Qed.
End FPX.
