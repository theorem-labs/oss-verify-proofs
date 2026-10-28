(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptExecSq O23_code_t_udd.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyT O23LeptPixCreateT2 O23LeptCloseSpec O23LeptCascW O23LeptTextSelW O23LeptMorphSeqSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptSelGP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptUddSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecW LeptExecB LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23ExecUb V23_code_frontB_uddF.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelGP.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.
Ltac fpn := cbn [fp_regs fp_csr].
Ltac fari F D Hz := chain_step; [ reflexivity | eapply fpv_step_fari; [exact F | reflexivity | exact D | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fsqrt F D Hz := chain_step; [ reflexivity | eapply fpv_step_fsqrt; [exact F | reflexivity | exact D | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvtfx F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x with (df := FMT_S) (sgn := true) (bits := 32%Z);
                                                  [exact F | reflexivity | exact D | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvtds F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f with (df := FMT_D) (sf := FMT_S);
                                                  [exact F | reflexivity | exact D | right; split; reflexivity | left; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac fcvtsd F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f with (df := FMT_S) (sf := FMT_D);
                                                  [exact F | reflexivity | exact D | left; split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.

Lemma ud_urange : forall x : word, (0 <= bv_unsigned x < 2 ^ 64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range _ x) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R. exact R. Qed.
Lemma ud_rdn_w2z : forall (m : word -> option byte) (a : Z) (x : word),
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 x) -> rdn SEGS m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 (bv_unsigned x)).
Proof.
  intros m a x H. pose proof (ud_urange x) as Rx.
  rewrite <- (w2b_Z 8 (bv_unsigned x) Rx), zbv_self. exact H.
Qed.

#[local] Ltac exB_sc_hook ::= v23_sc_hook.
Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Instance ud_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).
Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac fsd F D aa SOK := chain_step; [ reflexivity | eapply fp_step_fsd with (a := aa); [exact F | reflexivity | exact D | gres; imm_norm; addr_tac | sok_in SOK] | step_simpl ]; fpn.
Ltac fld F D aa bb R := chain_step; [ reflexivity | eapply fp_step_fld with (a := aa) (bs := bb); [exact F | reflexivity | exact D | gres; imm_norm; addr_tac | exact R] | step_simpl ]; fpn.

(* [comment removed for export] *)
Lemma ud_P : forall fr cs regs m (s pconf : Z) (ret : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  (1 <= pconf)%Z ->
  (pconf + 4 <= 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 256 = true ->
  store_ok SEGS m (Z_to_bv 64 pconf) 4 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 1 = ret ->
  getr regs 11 = Z_to_bv 64 pconf ->
  (pconf mod 4 = 0)%Z ->
  exists regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (0xaf8a0 : word) m rom) (@mkst (mkFP fr cs) regs' (0xaf8f8 : word) (O23LeptSelGP.wr4 (O23LeptUddSegs.UDF m s ret regs fr) pconf 0) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 256)
    /\ getr regs' 8 = Z_to_bv 64 pconf
    /\ getr regs' 19 = getr regs 10
    /\ regs_agree (fun r => In r [2; 8; 10; 19]%list) regs regs'.
Proof.
  intros fr cs regs m s pconf ret H0 H1 H2 H3 SOK SOKp R2 R1 R11 ALp.
  replace (0xaf8a0 : word) with (Z_to_bv 64 0xaf8a0) by (apply bv_eq; reflexivity).
  replace (0xaf8f8 : word) with (Z_to_bv 64 0xaf8f8) by (apply bv_eq; reflexivity).
  pose proof (u64_range (reg_get fr 8%bv)) as F8. pose proof (u64_range (reg_get fr 9%bv)) as F9.
  pose proof I as FZ.
  ex_entry regs [s; pconf; bv_unsigned (reg_get fr 8%bv); bv_unsigned (reg_get fr 9%bv)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pconf; bv_unsigned (reg_get fr 8%bv); bv_unsigned (reg_get fr 9%bv)]) m
                 [KWr (SA (EVar 32) (-256)) 256; KWr (SA (EVar 33) 0) 4; KRange (EVar 33) 1 (2 ^ 64 - 4); KAlign (EVar 33) 4]%Z) by ex_know regs.
  pose proof HR as HRo. exb_open HR HK ST. clear HR.
  exb_drive 60%nat [0xaf8f8%Z] (SCR [] [] []) [(8%nat, 34%nat); (9%nat, 35%nat)] HK ST FZ.
  exb_exit ST R HR Hlf Hms.
  exists R. split.
  - unfold O23LeptSelGP.wr4, O23LeptUddSegs.UDF. rewrite <- (zbv_self (reg_get fr 8%bv)), <- (zbv_self (reg_get fr 9%bv)). ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR); ex_agree HRo HR.
Qed.

(* [comment removed for export] *)
Lemma ud_P0 : forall fr cs regs m (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) ->
  rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v11) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 f0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 f1) ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  getr regs 19 = Z_to_bv 64 0 ->
  exists fr' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (0xaf8f8 : word) m rom) (@mkst (mkFP fr' cs) regs' (0x63670 : word) (m) rom)
    /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 1 = ret
    /\ getr regs' 10 = Z_to_bv 64 0x1189d
    /\ getr regs' 11 = Z_to_bv 64 0x1cabf
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 8 = v0
    /\ getr regs' 9 = v1
    /\ getr regs' 18 = v2
    /\ getr regs' 19 = v3
    /\ getr regs' 20 = v4
    /\ getr regs' 21 = v5
    /\ getr regs' 22 = v6
    /\ getr regs' 23 = v7
    /\ getr regs' 24 = v8
    /\ getr regs' 25 = v9
    /\ getr regs' 26 = v10
    /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros fr cs regs m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1 Hs Hs64 RG RS R8 R16 R24 R32 R40 R48 R56 R64 R72 R80 R88 R96 R104 R112 R120 H2 H19.
  replace (0xaf8f8 : word) with (Z_to_bv 64 0xaf8f8) by (apply bv_eq; reflexivity).
  replace (0x63670 : word) with (Z_to_bv 64 0x63670) by (apply bv_eq; reflexivity).
  pose proof I as FZ.
  ex_entryL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; f0; f1] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; f0; f1] regs [s]) m
                 [KRange (EVar 47) 256 (2 ^ 64 - 1);
                  KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
                  KWord (SA (EVar 47) (-8)) 8 (EVar 0); KWord (SA (EVar 47) (-16)) 8 (EVar 1); KWord (SA (EVar 47) (-24)) 8 (EVar 2);
                  KWord (SA (EVar 47) (-32)) 8 (EVar 3); KWord (SA (EVar 47) (-40)) 8 (EVar 4); KWord (SA (EVar 47) (-48)) 8 (EVar 5);
                  KWord (SA (EVar 47) (-56)) 8 (EVar 6); KWord (SA (EVar 47) (-64)) 8 (EVar 7); KWord (SA (EVar 47) (-72)) 8 (EVar 8);
                  KWord (SA (EVar 47) (-80)) 8 (EVar 9); KWord (SA (EVar 47) (-88)) 8 (EVar 10); KWord (SA (EVar 47) (-96)) 8 (EVar 11);
                  KWord (SA (EVar 47) (-104)) 8 (EVar 12); KWord (SA (EVar 47) (-112)) 8 (EVar 13); KWord (SA (EVar 47) (-120)) 8 (EVar 14)]%Z)
    by (ex_know regs).
  pose proof HR as HRo. exb_open HR HK ST. clear HR.
  exb_drive 80%nat [0x63670%Z] (SCR [] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (@mkst (mkFP ?frx _) _ _ _ _) => exists frx, R end. split.
  - ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR); ex_agree HRo HR.
Qed.

(* [comment removed for export] *)
Lemma ud_P1 : forall (fx : FPState) regs m (pixs : Z),
  (1 <= pixs)%Z ->
  (pixs + 64 <= 2 ^ 64)%Z ->
  (pixs mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 19 = Z_to_bv 64 pixs ->
  getr regs 12 = Z_to_bv 64 0 ->
  getr regs 13 = Z_to_bv 64 0 ->
  getr regs 14 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf8f8 : word) m rom) (@mkst fx regs' (0xa5894 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf948
    /\ getr regs' 10 = Z_to_bv 64 0x1e73b
    /\ getr regs' 11 = Z_to_bv 64 5
    /\ getr regs' 12 = Z_to_bv 64 6
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 9 = Z_to_bv 64 0
    /\ getr regs' 18 = Z_to_bv 64 70
    /\ getr regs' 26 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18; 26]%list) regs regs'.
Proof.
  intros fx regs m pixs H0 H1 H2 H3 H4 H5 H6 H7.
  replace (0xaf8f8 : word) with (Z_to_bv 64 0xaf8f8) by (apply bv_eq; reflexivity).
  replace (0xa5894 : word) with (Z_to_bv 64 0xa5894) by (apply bv_eq; reflexivity).
  ex_entry regs [pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [pixs]) m [KRange (EVar 32) 1 (2 ^ 64 - 64); KAlign (EVar 32) 8; KWord (SA (EVar 32) 8) 4 (ELit 1)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa5894%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_S1 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf948 : word) m rom) (@mkst fx regs' (0xa5894 : word) (O23LeptUddSegs.wr8w m (s - 176) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf968
    /\ getr regs' 10 = Z_to_bv 64 0x10c18
    /\ getr regs' 11 = Z_to_bv 64 5
    /\ getr regs' 12 = Z_to_bv 64 6
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 24 = getr regs 10
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 24]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xaf948 : word) with (Z_to_bv 64 0xaf948) by (apply bv_eq; reflexivity).
  replace (0xa5894 : word) with (Z_to_bv 64 0xa5894) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-176)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0xa5894%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_S2 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 184)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf968 : word) m rom) (@mkst fx regs' (0xa5894 : word) (O23LeptUddSegs.wr8w m (s - 184) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf988
    /\ getr regs' 10 = Z_to_bv 64 0x1304c
    /\ getr regs' 11 = Z_to_bv 64 5
    /\ getr regs' 12 = Z_to_bv 64 6
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 25 = getr regs 10
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 25]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xaf968 : word) with (Z_to_bv 64 0xaf968) by (apply bv_eq; reflexivity).
  replace (0xa5894 : word) with (Z_to_bv 64 0xa5894) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-184)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0xa5894%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_S3 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 192)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf988 : word) m rom) (@mkst fx regs' (0xa5894 : word) (O23LeptUddSegs.wr8w m (s - 192) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf9a8
    /\ getr regs' 10 = Z_to_bv 64 0x17281
    /\ getr regs' 11 = Z_to_bv 64 5
    /\ getr regs' 12 = Z_to_bv 64 6
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 21 = getr regs 10
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 21]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xaf988 : word) with (Z_to_bv 64 0xaf988) by (apply bv_eq; reflexivity).
  replace (0xa5894 : word) with (Z_to_bv 64 0xa5894) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-192)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0xa5894%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_S4 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf9a8 : word) m rom) (@mkst fx regs' (0xa663c : word) (O23LeptUddSegs.wr8w m (s - 200) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf9c4
    /\ getr regs' 10 = getr regs 19
    /\ getr regs' 11 = Z_to_bv 64 0x17f63
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 22 = getr regs 10
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 22]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xaf9a8 : word) with (Z_to_bv 64 0xaf9a8) by (apply bv_eq; reflexivity).
  replace (0xa663c : word) with (Z_to_bv 64 0xa663c) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-200)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0xa663c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_M : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 256)) 256 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  getr regs 26 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf9c4 : word) m rom) (@mkst fx regs' (0xafbac : word) (O23LeptUddSegs.wr8w (O23LeptUddSegs.wr8w m (s - 136) (getr regs 10)) (s - 168) (Z_to_bv 64 0)) rom)
    /\ getr regs' 23 = getr regs 10
    /\ getr regs' 20 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [20; 23]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3 H4.
  replace (0xaf9c4 : word) with (Z_to_bv 64 0xaf9c4) by (apply bv_eq; reflexivity).
  replace (0xafbac : word) with (Z_to_bv 64 0xafbac) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-256)) 256]%Z) by (ex_know regs).
  ex_run 400%nat [0xafbac%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1a : forall (fx : FPState) regs m,
  exists regs',
    msteps SEGS (@mkst fx regs (0xafbac : word) m rom) (@mkst fx regs' (0xa2088 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafbbc
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = getr regs 23
    /\ getr regs' 12 = getr regs 24
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m .
  replace (0xafbac : word) with (Z_to_bv 64 0xafbac) by (apply bv_eq; reflexivity).
  replace (0xa2088 : word) with (Z_to_bv 64 0xa2088) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []%Z) by (ex_know regs).
  ex_run 400%nat [0xa2088%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1b : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 144)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafbbc : word) m rom) (@mkst fx regs' (0xa2088 : word) (O23LeptUddSegs.wr8w m (s - 144) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafbd0
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = getr regs 23
    /\ getr regs' 12 = getr regs 25
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xafbbc : word) with (Z_to_bv 64 0xafbbc) by (apply bv_eq; reflexivity).
  replace (0xa2088 : word) with (Z_to_bv 64 0xa2088) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-144)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0xa2088%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1c : forall (fx : FPState) regs m (s : Z) (p1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 p1) ->
  store_ok SEGS m (Z_to_bv 64 (s - 152)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafbd0 : word) m rom) (@mkst fx regs' (0x7e558 : word) (O23LeptUddSegs.wr8w m (s - 152) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafbe4
    /\ getr regs' 10 = p1
    /\ getr regs' 11 = p1
    /\ getr regs' 12 = getr regs 10
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s p1 H0 H1 H2 H3 H4.
  apply ud_rdn_w2z in H2.
  pose proof (ud_urange p1).
  replace (0xafbd0 : word) with (Z_to_bv 64 0xafbd0) by (apply bv_eq; reflexivity).
  replace (0x7e558 : word) with (Z_to_bv 64 0x7e558) by (apply bv_eq; reflexivity).
  ex_entry regs [s; bv_unsigned p1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned p1]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 33); KWr (SA (EVar 32) (-152)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0x7e558%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1d : forall (fx : FPState) regs m (s : Z) (p1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 p1) ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  getr regs 20 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafbe4 : word) m rom) (@mkst fx regs' (0xa6c38 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc10
    /\ getr regs' 10 = p1
    /\ getr regs' 11 = Z_to_bv 64 1
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 14 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros fx regs m s p1 H0 H1 H2 H3 H4.
  apply ud_rdn_w2z in H2.
  pose proof (ud_urange p1).
  replace (0xafbe4 : word) with (Z_to_bv 64 0xafbe4) by (apply bv_eq; reflexivity).
  replace (0xa6c38 : word) with (Z_to_bv 64 0xa6c38) by (apply bv_eq; reflexivity).
  ex_entry regs [s; bv_unsigned p1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned p1]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 33)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa6c38%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1e : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc10 : word) m rom) (@mkst fx regs' (0x7e6fc : word) (O23LeptUddSegs.wr8w m (s - 160) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc20
    /\ getr regs' 10 = getr regs 10
    /\ getr regs' 11 = Z_to_bv 64 (s - 124)
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xafc10 : word) with (Z_to_bv 64 0xafc10) by (apply bv_eq; reflexivity).
  replace (0x7e6fc : word) with (Z_to_bv 64 0x7e6fc) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-160)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0x7e6fc%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1f : forall (fx : FPState) regs m (s : Z) (p1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 p1) ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  getr regs 9 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc20 : word) m rom) (@mkst fx regs' (0x6df98 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc40
    /\ getr regs' 10 = Z_to_bv 64 (s - 144)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
Proof.
  intros fx regs m s p1 H0 H1 H2 H3 H4.
  apply ud_rdn_w2z in H2.
  pose proof (ud_urange p1).
  replace (0xafc20 : word) with (Z_to_bv 64 0xafc20) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s; bv_unsigned p1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned p1]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 33)]%Z) by (ex_know regs).
  ex_run 60%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1g : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc40 : word) m rom) (@mkst fx regs' (0x6df98 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc48
    /\ getr regs' 10 = Z_to_bv 64 (s - 152)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafc40 : word) with (Z_to_bv 64 0xafc40) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B1h : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc48 : word) m rom) (@mkst fx regs' (0x6df98 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc50
    /\ getr regs' 10 = Z_to_bv 64 (s - 160)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafc48 : word) with (Z_to_bv 64 0xafc48) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2a : forall (fx : FPState) regs m,
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc50 : word) m rom) (@mkst fx regs' (0xa2088 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc60
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = getr regs 23
    /\ getr regs' 12 = getr regs 21
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m .
  replace (0xafc50 : word) with (Z_to_bv 64 0xafc50) by (apply bv_eq; reflexivity).
  replace (0xa2088 : word) with (Z_to_bv 64 0xa2088) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []%Z) by (ex_know regs).
  ex_run 400%nat [0xa2088%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2b : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 144)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc60 : word) m rom) (@mkst fx regs' (0xa2088 : word) (O23LeptUddSegs.wr8w m (s - 144) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc74
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = getr regs 23
    /\ getr regs' 12 = getr regs 22
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xafc60 : word) with (Z_to_bv 64 0xafc60) by (apply bv_eq; reflexivity).
  replace (0xa2088 : word) with (Z_to_bv 64 0xa2088) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-144)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0xa2088%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2c : forall (fx : FPState) regs m (s : Z) (p1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 p1) ->
  store_ok SEGS m (Z_to_bv 64 (s - 152)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc74 : word) m rom) (@mkst fx regs' (0x7e558 : word) (O23LeptUddSegs.wr8w m (s - 152) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafc88
    /\ getr regs' 10 = p1
    /\ getr regs' 11 = p1
    /\ getr regs' 12 = getr regs 10
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s p1 H0 H1 H2 H3 H4.
  apply ud_rdn_w2z in H2.
  pose proof (ud_urange p1).
  replace (0xafc74 : word) with (Z_to_bv 64 0xafc74) by (apply bv_eq; reflexivity).
  replace (0x7e558 : word) with (Z_to_bv 64 0x7e558) by (apply bv_eq; reflexivity).
  ex_entry regs [s; bv_unsigned p1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned p1]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 33); KWr (SA (EVar 32) (-152)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0x7e558%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2d : forall (fx : FPState) regs m (s : Z) (p1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 p1) ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  getr regs 20 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafc88 : word) m rom) (@mkst fx regs' (0xa6c38 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafcb4
    /\ getr regs' 10 = p1
    /\ getr regs' 11 = Z_to_bv 64 1
    /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ getr regs' 14 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros fx regs m s p1 H0 H1 H2 H3 H4.
  apply ud_rdn_w2z in H2.
  pose proof (ud_urange p1).
  replace (0xafc88 : word) with (Z_to_bv 64 0xafc88) by (apply bv_eq; reflexivity).
  replace (0xa6c38 : word) with (Z_to_bv 64 0xa6c38) by (apply bv_eq; reflexivity).
  ex_entry regs [s; bv_unsigned p1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned p1]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 33)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa6c38%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2e : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafcb4 : word) m rom) (@mkst fx regs' (0x7e6fc : word) (O23LeptUddSegs.wr8w m (s - 160) (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafcc4
    /\ getr regs' 10 = getr regs 10
    /\ getr regs' 11 = Z_to_bv 64 (s - 128)
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2 H3.
  replace (0xafcb4 : word) with (Z_to_bv 64 0xafcb4) by (apply bv_eq; reflexivity).
  replace (0x7e6fc : word) with (Z_to_bv 64 0x7e6fc) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-160)) 8]%Z) by (ex_know regs).
  ex_run 400%nat [0x7e6fc%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2f : forall (fx : FPState) regs m (s : Z) (p1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 p1) ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  getr regs 9 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafcc4 : word) m rom) (@mkst fx regs' (0x6df98 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafce4
    /\ getr regs' 10 = Z_to_bv 64 (s - 144)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
Proof.
  intros fx regs m s p1 H0 H1 H2 H3 H4.
  apply ud_rdn_w2z in H2.
  pose proof (ud_urange p1).
  replace (0xafcc4 : word) with (Z_to_bv 64 0xafcc4) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s; bv_unsigned p1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; bv_unsigned p1]) m [KWord (SA (EVar 32) (-144)) 8 (EVar 33)]%Z) by (ex_know regs).
  ex_run 60%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2g : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafce4 : word) m rom) (@mkst fx regs' (0x6df98 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafcec
    /\ getr regs' 10 = Z_to_bv 64 (s - 152)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafce4 : word) with (Z_to_bv 64 0xafce4) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_B2h : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafcec : word) m rom) (@mkst fx regs' (0x6df98 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafcf4
    /\ getr regs' 10 = Z_to_bv 64 (s - 160)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafcec : word) with (Z_to_bv 64 0xafcec) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_F : forall fr cs regs m (s pconf : Z) (b0 b1 : list byte),
  (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pconf)%Z -> (pconf + 4 <= 2 ^ 64)%Z -> frm_zero cs ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some b0 -> length b0 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some b1 -> length b1 = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pconf) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 8 = Z_to_bv 64 pconf -> getr regs 9 = Z_to_bv 64 0 -> getr regs 18 = Z_to_bv 64 70 ->
  reach SEGS (@mkst (mkFP fr cs) regs (0xafcf4 : word) m rom)
    (fun fin => exists fr' cs' regs' (M' : word -> option byte),
       fin = @mkst (mkFP fr' cs') regs' (0x6df98 : word) M' rom /\ frm_zero cs' /\
       (M' = m \/ exists y, (0 <= y < 2 ^ 32)%Z /\ M' = wbytes m (Z_to_bv 64 pconf) (Z_to_le_bytes 4 y)) /\
       getr regs' 1 = Z_to_bv 64 0xafdc4 /\ getr regs' 10 = Z_to_bv 64 (s - 136) /\
       regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs').
Proof.
  intros fr cs regs m s pconf b0 b1 Hs Hs64 Hp1 Hp4 FZ R0 L0 R1 L1 SOKp H2 H8 H9 H18.
  lazymatch goal with |- reach _ _ ?P => set (PP := P) end.
  lazymatch type of F_afd38 with fetch_word _ ?p = _ =>
    assert (K68 : forall fr' cs' R (M' : word -> option byte), frm_zero cs' ->
       (M' = m \/ exists y, (0 <= y < 2 ^ 32)%Z /\ M' = wbytes m (Z_to_bv 64 pconf) (Z_to_le_bytes 4 y)) ->
       regs_agree (fun r => In r [10; 11; 12]%list) regs R -> reach SEGS (@mkst (mkFP fr' cs') R p M' rom) PP)
  end.
  { intros fr' cs' R M' FZ' HM AG.
    assert (G9 : getr R 9 = Z_to_bv 64 0) by (rewrite (AG 9%bv); [exact H9 | notin_lit]).
    assert (G2 : getr R 2 = Z_to_bv 64 (s - 256)) by (rewrite (AG 2%bv); [exact H2 | notin_lit]).
    eapply reach_msteps.
    { chain_step; [ reflexivity
                  | eapply step_beq_tk; [exact F_afd38 | reflexivity | exact D_afd38 | rewrite G9, getr_zero; reflexivity]
                  | step_simpl ].
      lazymatch goal with |- msteps ?sg (mkst _ ?p _ _) _ =>
        let f := eval vm_compute in (fetch_word sg p) in
        lazymatch f with Some ?w =>
          assert (FA : fetch_word sg p = Some w) by (vm_cast_no_check (eq_refl (Some w)));
          let d := eval vm_compute in (decode_any w) in assert (DA : decode_any w = d) by (vm_cast_no_check (eq_refl d))
        end
      end.
      stepi FA DA.
      lazymatch goal with |- msteps ?sg (mkst _ ?p _ _) _ =>
        let f := eval vm_compute in (fetch_word sg p) in
        lazymatch f with Some ?w =>
          assert (FB : fetch_word sg p = Some w) by (vm_cast_no_check (eq_refl (Some w)));
          let d := eval vm_compute in (decode_any w) in assert (DB : decode_any w = d) by (vm_cast_no_check (eq_refl d))
        end
      end.
      stepj FB DB.
      apply mst_refl. }
    apply reach_done. unfold PP. cbv beta.
    do 4 eexists. split; [reflexivity |]. split; [exact FZ' |]. split; [exact HM |].
    split; [lazymatch goal with |- getr (regupd ?X ?r1 ?v) ?r2 = _ => replace r2 with r1 by (apply bv_eq; reflexivity); rewrite getr_same by (intro HH; apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH) end; apply bv_eq; reflexivity |].
    split; [lazymatch goal with |- getr (regupd (regupd ?X ?ra ?va) ?rb ?vb) ?r = _ =>
              rewrite getr_other by (intro HH; apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH);
              replace r with ra by (apply bv_eq; reflexivity);
              rewrite getr_same by (intro HH; apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH) end;
            lazymatch goal with |- context [getr R ?k] =>
              assert (G2k : getr R k = Z_to_bv 64 (s - 256)) by (rewrite <- G2; f_equal; apply bv_eq; reflexivity); rewrite G2k end;
            imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia |].
    intros r Hr.
    rewrite getr_other by (intro HE; apply Hr; rewrite HE; cbn [In]; left; apply bv_eq; reflexivity).
    rewrite getr_other by (intro HE; apply Hr; rewrite HE; cbn [In]; right; left; apply bv_eq; reflexivity).
    apply AG. intro HI. apply Hr. cbn [In] in *. tauto. }
  lazymatch type of F_afd08 with fetch_word _ ?p = _ =>
    assert (K20 : forall R, regs_agree (fun r => In r [10; 11; 12]%list) regs R -> reach SEGS (@mkst (mkFP fr cs) R p m rom) PP)
  end.
  { intros R AG.
    assert (G8 : getr R 8 = Z_to_bv 64 pconf) by (rewrite (AG 8%bv); [exact H8 | notin_lit]).
    eapply reach_msteps; [fcvtfx F_afd08 D_afd08 FZ; fcvtfx F_afd0c D_afd0c FZ; apply mst_refl |].
    destruct (c_lts (getr R 18) (getr R 12)) eqn:E2.
    - eapply reach_msteps.
      { chain_step; [reflexivity | eapply step_bge_ft; [exact F_afd10 | reflexivity | exact D_afd10 | exact E2] | step_simpl ].
        fari F_afd14 D_afd14 FZ. fari F_afd18 D_afd18 FZ. fcvtds F_afd1c D_afd1c FZ. fcvtds F_afd20 D_afd20 FZ.
        fsqrt F_afd24 D_afd24 FZ. fari F_afd28 D_afd28 FZ. fari F_afd2c D_afd2c FZ. fcvtsd F_afd30 D_afd30 FZ.
        chain_step; [ reflexivity
                    | eapply fp_step_fsw with (a := Z_to_bv 64 pconf);
                      [ exact F_afd34 | reflexivity | exact D_afd34
                      | rewrite G8; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia
                      | exact SOKp ]
                    | step_simpl ]; fpn.
        apply mst_refl. }
      apply K68; [fz FZ | | exact AG].
      right. eexists. split; cycle 1; [reflexivity | apply fp_u32_range].
    - eapply reach_msteps; [chain_step; [reflexivity | eapply step_bge_tk; [exact F_afd10 | reflexivity | exact D_afd10 | exact E2] | step_simpl]; apply mst_refl |].
      apply K68; [fz FZ | left; reflexivity | exact AG]. }
  assert (BB0 : (0 <= bytes_le_to_Z b0 < 2 ^ 64)%Z)
    by (pose proof (bytes_le_to_Z_nonneg b0); pose proof (bytes_le_to_Z_bound b0) as X; rewrite L0 in X; cbn in X; lia).
  assert (BB1 : (0 <= bytes_le_to_Z b1 < 2 ^ 64)%Z)
    by (pose proof (bytes_le_to_Z_nonneg b1); pose proof (bytes_le_to_Z_bound b1) as X; rewrite L1 in X; cbn in X; lia).
  eapply reach_msteps.
  { chain_step; [ reflexivity
                | eapply step_lw with (bs := b0) (v := Z_to_bv 64 (bytes_le_to_Z b0));
                  [ exact F_afcf4 | reflexivity | exact D_afcf4
                  | rewrite H2; imm_norm; unfold v_addi; rewrite u_Z2bv by lia;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?e) _ = _ => replace e with (s - 124)%Z by lia end; exact R0
                  | rewrite u_Z2bv by lia; reflexivity ]
                | step_simpl ].
    chain_step; [ reflexivity
                | eapply step_lw with (bs := b1) (v := Z_to_bv 64 (bytes_le_to_Z b1));
                  [ exact F_afcf8 | reflexivity | exact D_afcf8
                  | repeat first [rewrite getr_same by (intro HH; apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH) | rewrite getr_other by (intro HH; apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH)]; rewrite H2; imm_norm; unfold v_addi; rewrite u_Z2bv by lia;
                    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?e) _ = _ => replace e with (s - 128)%Z by lia end; exact R1
                  | rewrite u_Z2bv by lia; reflexivity ]
                | step_simpl ].
    stepi F_afcfc D_afcfc.
    apply mst_refl. }
  lazymatch goal with |- reach _ (mkst ?R _ _ _) _ => destruct (c_lts (getr R 11) (getr R 10)) eqn:E1 end.
  - eapply reach_msteps; [chain_step; [reflexivity | eapply step_blt_tk; [exact F_afd00 | reflexivity | exact D_afd00 | exact E1] | step_simpl]; apply mst_refl |].
    apply K20. solve_regs_agree.
  - eapply reach_msteps.
    { chain_step; [reflexivity | eapply step_blt_ft; [exact F_afd00 | reflexivity | exact D_afd00 | exact E1] | step_simpl].
      stepi F_afd04 D_afd04.
      apply mst_refl. }
    apply K20. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma ud_T1 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafdc4 : word) m rom) (@mkst fx regs' (0x6df98 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafdcc
    /\ getr regs' 10 = Z_to_bv 64 (s - 168)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafdc4 : word) with (Z_to_bv 64 0xafdc4) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_T2 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafdcc : word) m rom) (@mkst fx regs' (0xa4c74 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafdd4
    /\ getr regs' 10 = Z_to_bv 64 (s - 176)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafdcc : word) with (Z_to_bv 64 0xafdcc) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_T3 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafdd4 : word) m rom) (@mkst fx regs' (0xa4c74 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafddc
    /\ getr regs' 10 = Z_to_bv 64 (s - 184)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafdd4 : word) with (Z_to_bv 64 0xafdd4) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_T4 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafddc : word) m rom) (@mkst fx regs' (0xa4c74 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafde4
    /\ getr regs' 10 = Z_to_bv 64 (s - 192)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafddc : word) with (Z_to_bv 64 0xafddc) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_T5 : forall (fx : FPState) regs m (s : Z),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xafde4 : word) m rom) (@mkst fx regs' (0xa4c74 : word) (m) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xafdec
    /\ getr regs' 10 = Z_to_bv 64 (s - 200)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s H0 H1 H2.
  replace (0xafde4 : word) with (Z_to_bv 64 0xafde4) by (apply bv_eq; reflexivity).
  replace (0xa4c74 : word) with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m []%Z) by (ex_know regs).
  ex_run 400%nat [0xa4c74%Z] (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  exists R'. split.
  - unfold O23LeptUddSegs.wr8w. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma ud_X : forall fr cs regs m (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1 : word),
  (256 <= s)%Z ->
  (s < 2 ^ 64)%Z ->
  ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v11) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 f0) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 f1) ->
  getr regs 2 = Z_to_bv 64 (s - 256) ->
  exists fr' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (0xafdec : word) m rom) (@mkst (mkFP fr' cs) regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 8 = v0
    /\ getr regs' 9 = v1
    /\ getr regs' 18 = v2
    /\ getr regs' 19 = v3
    /\ getr regs' 20 = v4
    /\ getr regs' 21 = v5
    /\ getr regs' 22 = v6
    /\ getr regs' 23 = v7
    /\ getr regs' 24 = v8
    /\ getr regs' 25 = v9
    /\ getr regs' 26 = v10
    /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros fr cs regs m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 f0 f1 Hs Hs64 Hret R8 R16 R24 R32 R40 R48 R56 R64 R72 R80 R88 R96 R104 R112 R120 H2.
  replace (0xafdec : word) with (Z_to_bv 64 0xafdec) by (apply bv_eq; reflexivity).
  pose proof I as FZ.
  ex_entryL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; f0; f1] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; f0; f1] regs [s]) m
                 [KRange (EVar 47) 256 (2 ^ 64 - 1);
                  KWord (SA (EVar 47) (-8)) 8 (EVar 0); KWord (SA (EVar 47) (-16)) 8 (EVar 1); KWord (SA (EVar 47) (-24)) 8 (EVar 2);
                  KWord (SA (EVar 47) (-32)) 8 (EVar 3); KWord (SA (EVar 47) (-40)) 8 (EVar 4); KWord (SA (EVar 47) (-48)) 8 (EVar 5);
                  KWord (SA (EVar 47) (-56)) 8 (EVar 6); KWord (SA (EVar 47) (-64)) 8 (EVar 7); KWord (SA (EVar 47) (-72)) 8 (EVar 8);
                  KWord (SA (EVar 47) (-80)) 8 (EVar 9); KWord (SA (EVar 47) (-88)) 8 (EVar 10); KWord (SA (EVar 47) (-96)) 8 (EVar 11);
                  KWord (SA (EVar 47) (-104)) 8 (EVar 12); KWord (SA (EVar 47) (-112)) 8 (EVar 13); KWord (SA (EVar 47) (-120)) 8 (EVar 14)]%Z)
    by (ex_know regs).
  pose proof HR as HRo. exb_open HR HK ST. clear HR.
  exb_adrive 20%nat 400%nat (@nil Z) (@nil (nat * nat)) HK ST FZ.
  exb_ret ST ret (eq_refl ret) Hret R HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (@mkst (mkFP ?frx _) _ _ _ _) => exists frx, R end. split.
  - ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR); ex_agree HRo HR.
Qed.

End Segs.
