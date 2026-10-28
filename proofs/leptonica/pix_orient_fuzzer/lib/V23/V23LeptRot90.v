(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec LeptExecW LeptExecFP LeptExecB LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23_code_r90a_rot90.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptRot90.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma r90_and_0 : forall p k : Z, (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p mod (k + 1) = 0)%Z -> (k = 3 \/ k = 7)%Z ->
  alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 k) = Z_to_bv 64 0.
Proof.
  intros p k Hp Hk Hm Hk37. rewrite alu_and. unfold v_and. rewrite !u_Z2bv by lia.
  destruct Hk37 as [-> | ->].
  - change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. change (3 + 1)%Z with 4%Z in Hm. rewrite Hm. reflexivity.
  - change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z. change (7 + 1)%Z with 8%Z in Hm. rewrite Hm. reflexivity.
Qed.

Ltac r90_and0 := first [ rewrite (r90_and_0 _ 3) by (first [lia | assumption]) | rewrite (r90_and_0 _ 7) by (first [lia | assumption]) ].
Ltac r90_sc_hook :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ => repeat r90_and0; vm_compute; reflexivity
  end.
#[local] Ltac exB_sc_hook ::= r90_sc_hook.
Ltac r90_ext := repeat (rewrite (ext_val_sx_id 4 (Z_to_bv 64 _)) by (rewrite ?u_Z2bv by lia; cbn; lia)).
Ltac r90_fin R0 HR0 HR Hms :=
  match type of Hms with msteps _ _ (mkst ?Rf _ _ _) => exists Rf end; split;
  [ ex_mem2 R0 Hms
  | repeat split; try solve [exB_reg R0 HR; r90_ext; first [reflexivity | apply bv_eq; rewrite ?u_Z2bv by lia; reflexivity | apply bv_eq; vm_compute; reflexivity]]; ex_agree HR0 HR ].

Definition PC_pixRotate90 : Z := 0x9713c.

(* [comment removed for export] *)
Definition FR90 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
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
(* [comment removed for export] *)
Definition DIM90 (m : word -> option byte) (s : Z) (w h d : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
    (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 d)).
Definition MR90_A (m : word -> option byte) (s : Z) (v : pixv) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  DIM90 (FR90 m s ret regs) s (p_w v) (p_h v) (p_d v).
Definition MR90_D (m : word -> option byte) (s pixd datad : Z) : word -> option byte :=
  wbytes (O23LeptRot90.MR90_C m pixd) (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 datad)).
Definition R90C (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19); (s - 48, getr regs 20);
   (s - 56, getr regs 21); (s - 64, getr regs 22); (s - 72, getr regs 23); (s - 80, getr regs 24); (s - 88, getr regs 25);
   (s - 96, getr regs 26); (s - 104, getr regs 27)]%Z.

Section Rot90.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma r90_A : forall regs m (s pixs dir : Z) (v : pixv) (ret : word),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs v ->
    (pixs + 64 <= s - 192 \/ s <= pixs)%Z -> p_d v = 1%Z -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z ->
    (dir = 1 \/ dir = -1)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 192)) 192 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 dir ->
    exists regs',
      msteps SEGS (mkst regs (0x9713c : word) m rom) (mkst regs' (0x6da3c : word) (MR90_A m s v ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 192) /\ getr regs' 1 = Z_to_bv 64 0x971d0
      /\ getr regs' 10 = Z_to_bv 64 (p_h v) /\ getr regs' 11 = Z_to_bv 64 (p_w v) /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 19 = Z_to_bv 64 dir
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19]%list) regs regs'.
  Proof.
    intros regs m s pixs dir v ret Hs Hs64 Hs16 Hp ALp PX DJ Hd Hw Hh Hdir SOK H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (PIX_rd_w SEGS _ _ _ PX) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch. pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    rewrite Hd in Cd. unfold MR90_A. rewrite Hd. unfold DIM90, FR90. subst ret.
    replace (0x9713c : word) with (Z_to_bv 64 0x9713c) by (apply bv_eq; reflexivity).
    replace (0x6da3c : word) with (Z_to_bv 64 0x6da3c) by (apply bv_eq; reflexivity).
    destruct Hdir as [-> | ->].
    -
      ex_entry regs [s; pixs; p_w v; p_h v] HR.
      assert (HK : know_ok SEGS (ex_env regs [s; pixs; p_w v; p_h v]) m
        [KWr (SA (EVar 32) (-192)) 192; KRange (EVar 32) 192 (2 ^ 64 - 1); KAlign (EVar 32) 16; KRange (EVar 33) 1 (2 ^ 64 - 65); KAlign (EVar 33) 8;
         KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35); KWord (SA (EVar 33) 8) 4 (ELit 1);
         KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000;
         KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-192)) 192]%Z) by (ex_know regs).
      ex_open HR HK Hms Hlf.
      ex_cont 40%nat [0x6e2a4%Z] (SCR [] [] []) HR Hlf HK Hms.
      ex_cont 60%nat [0x97190%Z] (SCR [] [] []) HR Hlf HK Hms.
      ex_cont 60%nat [0x6da3c%Z] (SCR [] [] []) HR Hlf HK Hms.
      r90_fin regs HRo HR Hms.
    -
      ex_entry regs [s; pixs; p_w v; p_h v] HR.
      assert (HK : know_ok SEGS (ex_env regs [s; pixs; p_w v; p_h v]) m
        [KWr (SA (EVar 32) (-192)) 192; KRange (EVar 32) 192 (2 ^ 64 - 1); KAlign (EVar 32) 16; KRange (EVar 33) 1 (2 ^ 64 - 65); KAlign (EVar 33) 8;
         KWord (SA (EVar 33) 0) 4 (EVar 34); KWord (SA (EVar 33) 4) 4 (EVar 35); KWord (SA (EVar 33) 8) 4 (ELit 1);
         KRange (EVar 34) 1 20000; KRange (EVar 35) 1 20000;
         KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-192)) 192]%Z) by (ex_know regs).
      ex_open HR HK Hms Hlf.
      ex_cont 40%nat [0x6e2a4%Z] (SCR [] [] []) HR Hlf HK Hms.
      ex_cont 60%nat [0x97190%Z] (SCR [] [] []) HR Hlf HK Hms.
      ex_cont 60%nat [0x6da3c%Z] (SCR [] [] []) HR Hlf HK Hms.
      r90_fin regs HRo HR Hms.
  Qed.

  Lemma r90_N1 : forall regs M,
    rdn SEGS M (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) ->
    rdn SEGS M (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x971d4) M rom) (mkst regs' (Z_to_bv 64 0x63740) M rom)
      /\ getr regs' 1 = Z_to_bv 64 0x97a50 /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x193f3 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs M RG RV H10.
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs (@nil Z)) M
      [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3)]%Z) by (ex_know regs).
    ex_run 100%nat [0x63740%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
  Qed.

  Lemma r90_N : forall regs m (s : Z),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    rdn SEGS (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) ->
    rdn SEGS (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x971d0 : word) m rom) (mkst regs' (0x63740 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x97a50 /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x193f3 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK RG RV H2 H10.
    replace (0x971d0 : word) with (Z_to_bv 64 0x971d0) by (apply bv_eq; reflexivity).
    replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
    ex_entry regs [s] HR.
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-128)) 8; KRange (EVar 32) 192 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 4%nat [0x971d4%Z] (SCR [] [] []) HR HK R1 HR1 Hms.
    assert (Hms1 : msteps SEGS (mkst regs (Z_to_bv 64 0x971d0) m rom)
      (mkst R1 (Z_to_bv 64 0x971d4) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)) by (ex_mem regs Hms).
    assert (B10 : getr R1 10 = Z_to_bv 64 0) by (ex_reg regs HR1).
    destruct (r90_N1 R1 _ RG RV B10) as (R2 & Hms2 & C1 & C10 & C11 & C12 & AG2).
    exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] |].
    repeat split; try assumption.
    eapply regs_agree_trans; [ex_agree HR HR1 | exact AG2].
  Qed.

  Lemma r90_NE : forall regs m (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9); (s - 32, v18); (s - 40, v19); (s - 48, v20); (s - 56, v21);
              (s - 64, v22); (s - 72, v23); (s - 80, v24); (s - 88, v25); (s - 96, v26); (s - 104, v27)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 192) ->
    exists regs',
      msteps SEGS (mkst regs (0x97a50 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 10
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Hs64 Hret
      (R8 & R16 & R24 & R32 & R40 & R48 & R56 & R64 & R72 & R80 & R88 & R96 & R104 & _) H2.
    eexists. split.
    - sn F_97a50 D_97a50.
      stepLD8 F_98a30 D_98a30 ret. stepLD8 F_98a34 D_98a34 v8. stepLD8 F_98a38 D_98a38 v9.
      stepLD8 F_98a3c D_98a3c v18. stepLD8 F_98a40 D_98a40 v19. stepLD8 F_98a44 D_98a44 v20.
      stepLD8 F_98a48 D_98a48 v21. stepLD8 F_98a4c D_98a4c v22. stepLD8 F_98a50 D_98a50 v23.
      stepLD8 F_98a54 D_98a54 v24. stepLD8 F_98a58 D_98a58 v25. stepLD8 F_98a5c D_98a5c v26.
      stepLD8 F_98a60 D_98a60 v27.
      zv F_98a64 D_98a64 (Z_to_bv 64 s). stepret F_98a68 D_98a68 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma r90_B : forall regs m (s pixd : Z),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x971d0 : word) m rom) (mkst regs' (0x6e4cc : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x971e0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = getr regs 9
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp SOK H2 H10.
    replace (0x971d0 : word) with (Z_to_bv 64 0x971d0) by (apply bv_eq; reflexivity).
    replace (0x6e4cc : word) with (Z_to_bv 64 0x6e4cc) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pixd] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixd]) m
      [KWr (SA (EVar 32) (-128)) 8; KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 20%nat [0x6e4cc%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
  Qed.

  Lemma r90_Tw : forall regs M,
    rdn SEGS M (Z_to_bv 64 0x1f768) 4 = Some (Z_to_le_bytes 4 490244) ->
    getr regs 11 = Z_to_bv 64 0x1f768 -> getr regs 12 = Z_to_bv 64 0x1f768 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x97260) M rom) (mkst regs' (Z_to_bv 64 0x9726c) M rom)
      /\ regs_agree (fun r => In r [11]%list) regs regs'.
  Proof.
    intros regs M RT H11 H12.
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs (@nil Z)) M [KWord (SA (ELit 0) 0x1f768) 4 (ELit 490244)]%Z) by (ex_know regs).
    ex_run 20%nat [0x9726c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | ex_agree HR HR'].
  Qed.

  Lemma r90_Tc : forall regs M,
    rdn SEGS M (Z_to_bv 64 0x1f6e8) 4 = Some (Z_to_le_bytes 4 491364) ->
    getr regs 11 = Z_to_bv 64 0x1f6e8 -> getr regs 12 = Z_to_bv 64 0x1f6e8 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x97640) M rom) (mkst regs' (Z_to_bv 64 0x9764c) M rom)
      /\ regs_agree (fun r => In r [11]%list) regs regs'.
  Proof.
    intros regs M RT H11 H12.
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs (@nil Z)) M [KWord (SA (ELit 0) 0x1f6e8) 4 (ELit 491364)]%Z) by (ex_know regs).
    ex_run 20%nat [0x9764c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | ex_agree HR HR'].
  Qed.

  Ltac r90_pre PXd PXs Hxs Hys Hfs Hss :=
    let Hd0 := fresh "Hd0" in let Hd64 := fresh "Hd64" in let WFd := fresh "WFd" in
    let Hs0 := fresh "Hs0" in let Hs64' := fresh "Hs64'" in let WFs := fresh "WFs" in
    let Rfmt := fresh "Rfmt" in let Rspp := fresh "Rspp" in
    pose proof PXd as (Hd0 & Hd64 & WFd & _); pose proof PXs as (Hs0 & Hs64' & WFs & _);
    pose proof (wf_data _ WFd); pose proof (wf_wpl _ WFd); pose proof (wf_data _ WFs); pose proof (wf_wpl _ WFs);
    pose proof (O23LeptRot90.r90_rd_res0 SEGS _ _ _ PXs Hxs Hys);
    pose proof (PIX_rd_fmt SEGS _ _ _ PXs) as Rfmt; rewrite Hfs in Rfmt;
    pose proof (PIX_rd_spp SEGS _ _ _ PXs) as Rspp; rewrite Hss in Rspp;
    pose proof (PIX_rd_data SEGS _ _ _ PXs); pose proof (PIX_rd_wpl SEGS _ _ _ PXs);
    pose proof (PIX_rd_data SEGS _ _ _ PXd); pose proof (PIX_rd_wpl SEGS _ _ _ PXd).
  Ltac r90_know regs m s pixd pixs vd vs HR HK :=
    ex_entry regs [s; pixd; pixs; p_data vs; p_wpl vs; p_data vd; p_wpl vd] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; pixs; p_data vs; p_wpl vs; p_data vd; p_wpl vd]) m
      [KWr (SA (EVar 33) 0) 64; KWr (SA (EVar 32) (-136)) 8;
       KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 65); KAlign (EVar 33) 8;
       KRange (EVar 34) 1 (2 ^ 64 - 65); KAlign (EVar 34) 8;
       KWord (SA (EVar 32) (-128)) 8 (EVar 33); KWord (SA (EVar 32) (-116)) 4 (ELit 1);
       KWord (SA (EVar 34) 24) 8 (ELit 0); KWord (SA (EVar 34) 32) 4 (ELit 0); KWord (SA (EVar 34) 12) 4 (ELit 1);
       KWord (SA (EVar 34) 56) 8 (EVar 35); KWord (SA (EVar 34) 16) 4 (EVar 36);
       KWord (SA (EVar 33) 56) 8 (EVar 37); KWord (SA (EVar 33) 16) 4 (EVar 38);
       KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1);
       KDisj (SA (EVar 33) 0) 64 (SA (EVar 34) 0) 64;
       KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-192)) 192;
       KDisj (SA (EVar 34) 0) 64 (SA (EVar 32) (-192)) 192]%Z) by (ex_know regs).
  Ltac r90_post AG2 regs HR HR1 :=
    repeat split; try solve [rewrite AG2 by (cbn [In]; intuition discriminate); exB_reg regs HR1; r90_ext;
      first [reflexivity | apply bv_eq; rewrite ?u_Z2bv by lia; reflexivity | apply bv_eq; vm_compute; reflexivity]];
    eapply regs_agree_trans; [ex_agree HR HR1 | eapply regs_agree_mono; [| exact AG2]; incl_list].

  Lemma r90_Cw : forall regs m (s pixd pixs : Z) (vd vs : pixv),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (1 <= pixs)%Z -> pixd <> pixs -> (pixd mod 8 = 0)%Z -> (pixs mod 8 = 0)%Z ->
    (pixd + 64 <= s - 192)%Z -> (pixs + 64 <= s - 192 \/ s <= pixs)%Z -> (pixd + 64 <= pixs \/ pixs + 64 <= pixd)%Z ->
    PIXat m pixd vd -> PIXat m pixs vs -> p_xres vd = 0%Z -> p_yres vd = 0%Z -> p_fmt vd = 0%Z -> p_spp vd = 1%Z ->
    p_xres vs = 0%Z -> p_yres vs = 0%Z -> p_fmt vs = 0%Z -> p_spp vs = 1%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> store_ok SEGS m (Z_to_bv 64 (s - 136)) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS (MR90_D m s pixd (p_data vd)) (Z_to_bv 64 0x1f768) 4 = Some (Z_to_le_bytes 4 490244) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 19 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x971e0 : word) m rom) (mkst regs' (0x9726c : word) (MR90_D m s pixd (p_data vd)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 192) /\ getr regs' 10 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 8 = Z_to_bv 64 (p_data vs)
      /\ getr regs' 18 = Z_to_bv 64 (p_wpl vs) /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 19 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs vd vs Hs Hs64 Hd1 Hs1 Hne ALd ALs DJd DJs DJds PXd PXs Hxd Hyd Hfd Hsd Hxs Hys Hfs Hss
      SOKd SOK136 R128 R116 RT H2 H9 H19.
    r90_pre PXd PXs Hxs Hys Hfs Hss.
    replace (0x971e0 : word) with (Z_to_bv 64 0x971e0) by (apply bv_eq; reflexivity).
    replace (0x9726c : word) with (Z_to_bv 64 0x9726c) by (apply bv_eq; reflexivity).
    r90_know regs m s pixd pixs vd vs HR HK.
    ex_run 400%nat [0x97260%Z] (SCR [false; false; false] [] []) HR HK R1 HR1 Hms.
    assert (Hms1 : msteps SEGS (mkst regs (Z_to_bv 64 0x971e0) m rom) (mkst R1 (Z_to_bv 64 0x97260) (MR90_D m s pixd (p_data vd)) rom))
      by (unfold MR90_D, O23LeptRot90.MR90_C; ex_mem2 regs Hms).
    assert (B11 : getr R1 11 = Z_to_bv 64 0x1f768) by (ex_reg regs HR1).
    assert (B12 : getr R1 12 = Z_to_bv 64 0x1f768) by (ex_reg regs HR1).
    destruct (r90_Tw R1 _ RT B11 B12) as (R2 & Hms2 & AG2).
    exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] |].
    r90_post AG2 regs HR HR1.
  Qed.

  Lemma r90_Cc : forall regs m (s pixd pixs : Z) (vd vs : pixv),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (1 <= pixs)%Z -> pixd <> pixs -> (pixd mod 8 = 0)%Z -> (pixs mod 8 = 0)%Z ->
    (pixd + 64 <= s - 192)%Z -> (pixs + 64 <= s - 192 \/ s <= pixs)%Z -> (pixd + 64 <= pixs \/ pixs + 64 <= pixd)%Z ->
    PIXat m pixd vd -> PIXat m pixs vs -> p_xres vd = 0%Z -> p_yres vd = 0%Z -> p_fmt vd = 0%Z -> p_spp vd = 1%Z ->
    p_xres vs = 0%Z -> p_yres vs = 0%Z -> p_fmt vs = 0%Z -> p_spp vs = 1%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> store_ok SEGS m (Z_to_bv 64 (s - 136)) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS (MR90_D m s pixd (p_data vd)) (Z_to_bv 64 0x1f6e8) 4 = Some (Z_to_le_bytes 4 491364) ->
    getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 19 = Z_to_bv 64 (-1) ->
    exists regs',
      msteps SEGS (mkst regs (0x971e0 : word) m rom) (mkst regs' (0x9764c : word) (MR90_D m s pixd (p_data vd)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 192) /\ getr regs' 10 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 8 = Z_to_bv 64 (p_data vs)
      /\ getr regs' 18 = Z_to_bv 64 (p_wpl vs) /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 19 = Z_to_bv 64 (-1)
      /\ regs_agree (fun r => In r [1; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs vd vs Hs Hs64 Hd1 Hs1 Hne ALd ALs DJd DJs DJds PXd PXs Hxd Hyd Hfd Hsd Hxs Hys Hfs Hss
      SOKd SOK136 R128 R116 RT H2 H9 H19.
    r90_pre PXd PXs Hxs Hys Hfs Hss.
    replace (0x971e0 : word) with (Z_to_bv 64 0x971e0) by (apply bv_eq; reflexivity).
    replace (0x9764c : word) with (Z_to_bv 64 0x9764c) by (apply bv_eq; reflexivity).
    r90_know regs m s pixd pixs vd vs HR HK.
    ex_run 400%nat [0x97640%Z] (SCR [false; false; false] [] []) HR HK R1 HR1 Hms.
    assert (Hms1 : msteps SEGS (mkst regs (Z_to_bv 64 0x971e0) m rom) (mkst R1 (Z_to_bv 64 0x97640) (MR90_D m s pixd (p_data vd)) rom))
      by (unfold MR90_D, O23LeptRot90.MR90_C; ex_mem2 regs Hms).
    assert (B11 : getr R1 11 = Z_to_bv 64 0x1f6e8) by (ex_reg regs HR1).
    assert (B12 : getr R1 12 = Z_to_bv 64 0x1f6e8) by (ex_reg regs HR1).
    destruct (r90_Tc R1 _ RT B11 B12) as (R2 & Hms2 & AG2).
    exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] |].
    r90_post AG2 regs HR HR1.
  Qed.

  Lemma r90_E : forall regs m (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 pd : word),
    (192 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9); (s - 32, v18); (s - 40, v19); (s - 48, v20); (s - 56, v21);
              (s - 64, v22); (s - 72, v23); (s - 80, v24); (s - 88, v25); (s - 96, v26); (s - 104, v27); (s - 128, pd)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 192) ->
    exists regs',
      msteps SEGS (mkst regs (0x98a2c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = pd
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 pd Hs Hs64 Hret
      (R8 & R16 & R24 & R32 & R40 & R48 & R56 & R64 & R72 & R80 & R88 & R96 & R104 & R128 & _) H2.
    eexists. split.
    - stepLD8 F_98a2c D_98a2c pd.
      stepLD8 F_98a30 D_98a30 ret. stepLD8 F_98a34 D_98a34 v8. stepLD8 F_98a38 D_98a38 v9.
      stepLD8 F_98a3c D_98a3c v18. stepLD8 F_98a40 D_98a40 v19. stepLD8 F_98a44 D_98a44 v20.
      stepLD8 F_98a48 D_98a48 v21. stepLD8 F_98a4c D_98a4c v22. stepLD8 F_98a50 D_98a50 v23.
      stepLD8 F_98a54 D_98a54 v24. stepLD8 F_98a58 D_98a58 v25. stepLD8 F_98a5c D_98a5c v26.
      stepLD8 F_98a60 D_98a60 v27.
      zv F_98a64 D_98a64 (Z_to_bv 64 s). stepret F_98a68 D_98a68 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End Rot90.
