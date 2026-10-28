(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptArithB GrayACELib LeptRop.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecX LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2LeptAmbSegs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptGrayA V2LeptRop_iface V2LeptBl_iface V2LeptRop2Gset V2_code_pixAddMirroredBorder.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac am_norm :=
  rewrite ?alu_add, ?alu_sub, ?w_addw, ?w_subw, ?ex_ptr_val, ?zbv_addi, ?zbv_add, ?zbv_sub;
  rewrite ?zaddw_s by lia; rewrite ?zsubw_s by lia; rewrite ?zbv_add, ?zbv_sub.
Ltac am_fin := try first [ reflexivity | (repeat rewrite ex_sx32 by lia; reflexivity)
                         | (am_norm; first [ reflexivity | (f_equal; lia) ])
                         | (apply bv_eq; reflexivity) ].
#[local] Ltac exB_sc_hook ::= first [ (am_norm; ex_br) ].
Lemma am_m1 : Z_to_bv 64 (-1) = Z_to_bv 64 (2 ^ 64 - 1).
Proof. apply bv_eq; reflexivity. Qed.
Ltac am_sc := lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      first [ (am_norm; rewrite ?am_m1; ex_br)
            | (match goal with H : (?a = 0)%Z |- _ => subst a end; vm_compute; reflexivity) ]
  end.
Ltac am_val regs :=
  try unfold ex_env; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  repeat rewrite ex_sx32 by lia; am_norm; first [ (f_equal; lia) | reflexivity ].
Ltac am_mem regs Hms :=
  eapply ex_msteps_mem; [exact Hms|]; cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | first [ solve [ex_bytes_eq regs] | (f_equal; try am_val regs) ] ]);
  try reflexivity.

Definition AM_RA : Z := 0x1c4c4.
Definition AM_H1 : Z := 0x1c4d8.
Definition AM_R1 : Z := 0x1c50c.
Definition AM_X1 : Z := 0x1c518.
Definition AM_H2 : Z := 0x1c520.
Definition AM_R2 : Z := 0x1c578.
Definition AM_X2 : Z := 0x1c580.
Definition AM_H3 : Z := 0x1c590.
Definition AM_R3 : Z := 0x1c5e4.
Definition AM_X3 : Z := 0x1c5f0.
Definition AM_H4 : Z := 0x1c5f8.
Definition AM_R4 : Z := 0x1c670.
Definition AM_X4 : Z := 0x1c678.
Definition AM_RET : Z := 0x1c734.

Section AmbSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma am_A : forall regs m (s pixs l r t b : Z) (vs : pixv) (ret : word),
    (256 <= s < 2 ^ 63)%Z -> (s mod 16 = 0)%Z ->
    (4096 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    (0 <= l < 2 ^ 31)%Z -> (0 <= r < 2 ^ 31)%Z -> (0 <= t < 2 ^ 31)%Z -> (0 <= b < 2 ^ 31)%Z ->
    (l <= p_w vs)%Z -> (r <= p_w vs)%Z -> (t <= p_h vs)%Z -> (b <= p_h vs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 l -> getr regs 12 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 t -> getr regs 14 = Z_to_bv 64 b ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 PC_pixAddMirroredBorder) m rom)
                  (mkst regs' (Z_to_bv 64 PC_pixAddBorderGeneral) (DIM2 (FRM9 m s ret regs) s (p_w vs) (p_h vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 AM_RA
      /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 l /\ getr regs' 12 = Z_to_bv 64 r
      /\ getr regs' 13 = Z_to_bv 64 t /\ getr regs' 14 = Z_to_bv 64 b /\ getr regs' 15 = Z_to_bv 64 0
      /\ getr regs' 20 = Z_to_bv 64 pixs /\ getr regs' 19 = Z_to_bv 64 l /\ getr regs' 18 = Z_to_bv 64 r
      /\ getr regs' 9 = Z_to_bv 64 t /\ getr regs' 8 = Z_to_bv 64 b
      /\ regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixs l r t b vs ret Hs ALs Hp1 Hp2 ALp PX APs Hl Hr Ht Hb Hlw Hrw Hth Hbh SOK H2 H1 H10 H11 H12 H13 H14.
    subst ret.
    pose proof (PIX_rd_w SEGS m pixs vs PX) as RW. pose proof (PIX_rd_h SEGS m pixs vs PX) as RH.
    destruct PX as (_ & _ & WF & _). pose proof (wf_w _ WF) as Hw. pose proof (wf_h _ WF) as Hh.
    unfold PC_pixAddMirroredBorder, PC_pixAddBorderGeneral, AM_RA.
    ex_entry regs [s; pixs; l; r; t; b; p_w vs; p_h vs] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixs; l; r; t; b; p_w vs; p_h vs]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 4096 (2 ^ 63);
                    KRange (EVar 34) 0 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1);
                    KRange (EVar 38) 0 (2 ^ 31 - 1); KRange (EVar 39) 0 (2 ^ 31 - 1);
                    KAlign (EVar 32) 16; KAlign (EVar 33) 8;
                    KWr (SA (EVar 32) (-96)) 96;
                    KWord (SA (EVar 33) 0) 4 (EVar 38); KWord (SA (EVar 33) 4) 4 (EVar 39);
                    KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-96)) 96]) by (ex_know regs).
    ex_run 300%nat [0x1c144%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
    all: try am_sc.
    exists R'. split.
    { unfold DIM2, FRM9. first [ex_mem regs Hms | am_mem regs Hms]. all: symmetry; am_val regs. }
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_B0 : forall regs m (pixd l : Z),
    (1 <= l < 2 ^ 31)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 19 = Z_to_bv 64 l ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_RA) m rom) (mkst regs' (Z_to_bv 64 AM_H1) m rom)
      /\ getr regs' 20 = Z_to_bv 64 pixd /\ getr regs' 21 = Z_to_bv 64 (l - 1) /\ getr regs' 23 = Z_to_bv 64 (-1) /\ getr regs' 22 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros regs m pixd l Hl H10 H19.
    unfold AM_RA, AM_H1.
    ex_entry regs [pixd; l] HR.
    assert (HK : know_ok SEGS (ex_env regs [pixd; l]) m [KRange (EVar 33) 1 (2 ^ 31 - 1)]) by (ex_know regs).
    ex_run 20%nat [0x1c4d8%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_L1 : forall regs m (s pixd t h a l j : Z),
    (96 <= s)%Z -> (s < 2 ^ 63)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= l)%Z -> (0 <= j)%Z -> (l + j < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
    getr regs 21 = Z_to_bv 64 a -> getr regs 19 = Z_to_bv 64 l -> getr regs 22 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_H1) m rom)
                  (mkst regs' (Z_to_bv 64 PC_pixRasterop) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 t))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 AM_R1
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 a /\ getr regs' 12 = Z_to_bv 64 t /\ getr regs' 13 = Z_to_bv 64 1
      /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixd /\ getr regs' 17 = Z_to_bv 64 (l + j)
      /\ regs_agree (fun x => In x [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixd t h a l j Hs1 Hs2 Hh Hl Hj Hlj Hrd Hso H2 H20 H9 H21 H19 H22.
    unfold AM_H1, AM_R1, PC_pixRasterop.
    ex_entry regs [(s - 96)%Z; pixd; t; a; l; j; h] HR.
    assert (HK : know_ok SEGS (ex_env regs [(s - 96)%Z; pixd; t; a; l; j; h]) m
              [KRange (EVar 32) 0 (2 ^ 63 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1);
               KRange (EVar 38) 0 (2 ^ 31 - 1); KWr (SA (EVar 32) 0) 8; KWord (SA (EVar 32) 16) 4 (EVar 38)])
      by (ex_know regs).
    ex_run 40%nat [160752%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms |].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_N1 : forall (last : bool) regs m (a c : Z),
    (0 <= a < 2 ^ 31)%Z -> (0 <= c < 2 ^ 31 - 1)%Z -> (if last then a = 0 else 0 < a)%Z ->
    getr regs 21 = Z_to_bv 64 a -> getr regs 22 = Z_to_bv 64 c -> getr regs 23 = Z_to_bv 64 (-1) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_R1) m rom) (mkst regs' (Z_to_bv 64 (if last then AM_X1 else AM_H1)) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (a - 1) /\ getr regs' 22 = Z_to_bv 64 (c + 1)
      /\ regs_agree (fun x => In x [21; 22]%list) regs regs'.
  Proof.
    intros last regs m a c Ha Hc Hl H21 H22 H23.
    unfold AM_R1, AM_X1, AM_H1.
    ex_entry regs [a; c; (-1)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [a; c; (-1)%Z]) m
                   [KRange (EVar 32) 0 (2 ^ 31 - 1); KRange (EVar 33) 0 (2 ^ 31 - 2)]) by (ex_know regs).
    destruct last; cbv beta iota in Hl |- *.
    - ex_run 20%nat [0x1c518%Z; 0x1c4d8%Z] (SCR [false] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
    - ex_run 20%nat [0x1c518%Z; 0x1c4d8%Z] (SCR [true] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_B1 : forall regs m (r : Z),
    (1 <= r < 2 ^ 31)%Z -> getr regs 18 = Z_to_bv 64 r ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_X1) m rom) (mkst regs' (Z_to_bv 64 AM_H2) m rom)
      /\ getr regs' 21 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [21]%list) regs regs'.
  Proof.
    intros regs m r Hr H18.
    unfold AM_X1, AM_H2.
    ex_entry regs [r] HR.
    assert (HK : know_ok SEGS (ex_env regs [r]) m [KRange (EVar 32) 1 (2 ^ 31 - 1)]) by (ex_know regs).
    ex_run 20%nat [0x1c520%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
  Qed.

  Ltac am_l2sc := rewrite ?ex_sx32 by lia; rewrite ?m_mul, ?zbv_mul; am_norm; rewrite ?m_mul, ?zbv_mul, ?zbv_add;
    try (match goal with |- branch_taken BC_NE (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) = _ => replace y with x by lia end); ex_br.
  Ltac am_l2fin := rewrite ?ex_sx32 by lia; rewrite ?m_mul, ?zbv_mul; am_norm; am_norm; first [ reflexivity | (f_equal; lia) ].
  (* [comment removed for export] *)
  Lemma am_L2 : forall regs m (s pixd t w h l j : Z),
    (96 <= s)%Z -> (s < 2 ^ 63)%Z -> (0 <= w)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= l)%Z -> (0 <= j)%Z -> (l + w + j < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
    getr regs 19 = Z_to_bv 64 l -> getr regs 21 = Z_to_bv 64 j ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_H2) m rom)
                  (mkst regs' (Z_to_bv 64 PC_pixRasterop) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 t))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 AM_R2
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (l + w + j) /\ getr regs' 12 = Z_to_bv 64 t /\ getr regs' 13 = Z_to_bv 64 1
      /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixd /\ getr regs' 17 = Z_to_bv 64 (l + w - 1 - j)
      /\ regs_agree (fun x => In x [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixd t w h l j Hs1 Hs2 Hw Hh Hl Hj Hsum Rw Rh SOK H2 H20 H9 H19 H21.
    unfold AM_H2, AM_R2, PC_pixRasterop.
    ex_entry regs [(s - 96)%Z; pixd; t; l; j; w; h] HR.
    assert (HK : know_ok SEGS (ex_env regs [(s - 96)%Z; pixd; t; l; j; w; h]) m
              [KRange (EVar 32) 0 (2 ^ 63 - 97); KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1);
               KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1);
               KWr (SA (EVar 32) 0) 8; KWord (SA (EVar 32) 20) 4 (EVar 37); KWord (SA (EVar 32) 16) 4 (EVar 38)])
      by (ex_know regs).
    ex_run 60%nat [160752%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
    all: try am_l2sc.
    exists R'. split; [ex_mem regs Hms |].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: try am_l2fin.
    all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_N2 : forall (last : bool) regs m (j r : Z),
    (0 <= j)%Z -> (j + 1 <= r < 2 ^ 31)%Z -> (if last then j + 1 = r else j + 1 < r)%Z ->
    getr regs 21 = Z_to_bv 64 j -> getr regs 18 = Z_to_bv 64 r ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_R2) m rom) (mkst regs' (Z_to_bv 64 (if last then AM_X2 else AM_H2)) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun x => In x [21]%list) regs regs'.
  Proof.
    intros last regs m j r Hj Hr Hl H21 H18.
    unfold AM_R2, AM_X2, AM_H2.
    ex_entry regs [j; r] HR.
    assert (HK : know_ok SEGS (ex_env regs [j; r]) m
                   [KRange (EVar 32) 0 (2 ^ 31 - 2); KRange (EVar 33) 1 (2 ^ 31 - 1)]) by (ex_know regs).
    destruct last; cbv beta iota in Hl |- *.
    - ex_run 20%nat [0x1c580%Z; 0x1c520%Z] (SCR [false] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
    - ex_run 20%nat [0x1c580%Z; 0x1c520%Z] (SCR [true] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_B2 : forall regs m (t : Z),
    (1 <= t < 2 ^ 31)%Z -> getr regs 9 = Z_to_bv 64 t ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_X2) m rom) (mkst regs' (Z_to_bv 64 AM_H3) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (t - 1) /\ getr regs' 23 = Z_to_bv 64 (-1) /\ getr regs' 22 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [21; 22; 23]%list) regs regs'.
  Proof.
    intros regs m t Ht H9.
    unfold AM_X2, AM_H3.
    ex_entry regs [t] HR.
    assert (HK : know_ok SEGS (ex_env regs [t]) m [KRange (EVar 32) 1 (2 ^ 31 - 1)]) by (ex_know regs).
    ex_run 20%nat [0x1c590%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: try am_sc.
    exists R'. split; [ex_mem regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_L3 : forall regs m (s pixd t w l r a i : Z),
    (96 <= s)%Z -> (s < 2 ^ 63)%Z -> (0 <= w)%Z -> (0 <= l)%Z -> (0 <= r)%Z -> (l + w + r < 2 ^ 31)%Z ->
    (0 <= t)%Z -> (0 <= i)%Z -> (t + i < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
    getr regs 19 = Z_to_bv 64 l -> getr regs 18 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 a -> getr regs 22 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_H3) m rom)
                  (mkst regs' (Z_to_bv 64 PC_pixRasterop) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 (t + i)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 AM_R3
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 a /\ getr regs' 13 = Z_to_bv 64 (l + w + r)
      /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixd /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixd t w l r a i Hs1 Hs2 Hw Hl Hr Hlwr Ht Hi Hti Hrd Hso H2 H20 H9 H19 H18 H21 H22.
    unfold AM_H3, AM_R3, PC_pixRasterop.
    ex_entry regs [(s - 96)%Z; pixd; t; l; r; a; i; w] HR.
    assert (HK : know_ok SEGS (ex_env regs [(s - 96)%Z; pixd; t; l; r; a; i; w]) m
              [KRange (EVar 32) 0 (2 ^ 63 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1);
               KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1); KRange (EVar 39) 0 (2 ^ 31 - 1);
               KWr (SA (EVar 32) 0) 8; KWord (SA (EVar 32) 20) 4 (EVar 39)])
      by (ex_know regs).
    ex_run 60%nat [160752%Z] (SCR [false; false; false] [] []) HR HK R' HR' Hms.
    all: try solve [rewrite ?ex_sx32 by lia; am_norm; ex_br].
    exists R'. split;
      [ eapply ex_msteps_mem; [exact Hms|]; cbn [mem_denot s_log e_addr e_width e_val];
        apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs |];
        f_equal; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
        am_norm; first [reflexivity | (f_equal; lia)] |].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
    all: rewrite ?ex_sx32 by lia; am_norm; first [reflexivity | (f_equal; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma am_N3 : forall (last : bool) regs m (a c : Z),
    (0 <= a < 2 ^ 31)%Z -> (0 <= c < 2 ^ 31 - 1)%Z -> (if last then a = 0 else 0 < a)%Z ->
    getr regs 21 = Z_to_bv 64 a -> getr regs 22 = Z_to_bv 64 c -> getr regs 23 = Z_to_bv 64 (-1) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_R3) m rom) (mkst regs' (Z_to_bv 64 (if last then AM_X3 else AM_H3)) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (a - 1) /\ getr regs' 22 = Z_to_bv 64 (c + 1)
      /\ regs_agree (fun x => In x [21; 22]%list) regs regs'.
  Proof.
    intros last regs m a c Ha Hc Hl H21 H22 H23.
    unfold AM_R3, AM_X3, AM_H3.
    ex_entry regs [a; c; (-1)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [a; c; (-1)%Z]) m
                   [KRange (EVar 32) 0 (2 ^ 31 - 1); KRange (EVar 33) 0 (2 ^ 31 - 2)]) by (ex_know regs).
    destruct last; cbv beta iota in Hl |- *.
    - ex_run 20%nat [0x1c5f0%Z; 0x1c590%Z] (SCR [false] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
    - ex_run 20%nat [0x1c5f0%Z; 0x1c590%Z] (SCR [true] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_B3 : forall regs m (b : Z),
    (1 <= b < 2 ^ 31)%Z -> getr regs 8 = Z_to_bv 64 b ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_X3) m rom) (mkst regs' (Z_to_bv 64 AM_H4) m rom)
      /\ getr regs' 21 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [21]%list) regs regs'.
  Proof.
    intros regs m b Hb H8.
    unfold AM_X3, AM_H4.
    ex_entry regs [b] HR.
    assert (HK : know_ok SEGS (ex_env regs [b]) m [KRange (EVar 32) 1 (2 ^ 31 - 1)]) by (ex_know regs).
    ex_run 20%nat [0x1c5f8%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: try am_sc.
    exists R'. split; [ex_mem regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
  Qed.

  Ltac am4_n := rewrite ?ex_sx32 by lia; rewrite ?m_mul, ?zbv_mul; do 3 am_norm.
  Ltac am4_sc := am4_n;
    first [ ex_br
          | lazymatch goal with |- branch_taken _ (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) = _ =>
              replace y with x by lia; cbn [branch_taken]; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity end ].
  Ltac am4_fin := am4_n; first [ reflexivity | (f_equal; lia) ].

  (* [comment removed for export] *)
  Lemma am_L4 : forall regs m (s pixd t w h l r i : Z),
    (96 <= s)%Z -> (s < 2 ^ 63)%Z -> (0 <= w)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= l)%Z -> (0 <= r)%Z -> (l + w + r < 2 ^ 31)%Z ->
    (0 <= t)%Z -> (0 <= i)%Z -> (t + h + i < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 t ->
    getr regs 19 = Z_to_bv 64 l -> getr regs 18 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_H4) m rom)
                  (mkst regs' (Z_to_bv 64 PC_pixRasterop) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 (t + h - 1 - i)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 AM_R4
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (t + h + i) /\ getr regs' 13 = Z_to_bv 64 (l + w + r)
      /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixd /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixd t w h l r i Hs1 Hs2 Hw Hh Hl Hr Hlwr Ht Hi Hthi Rw Rh SOK H2 H20 H9 H19 H18 H21.
    unfold AM_H4, AM_R4, PC_pixRasterop.
    ex_entry regs [(s - 96)%Z; pixd; t; l; r; i; w; h] HR.
    assert (HK : know_ok SEGS (ex_env regs [(s - 96)%Z; pixd; t; l; r; i; w; h]) m
              [KRange (EVar 32) 0 (2 ^ 63 - 97); KRange (EVar 34) 0 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1);
               KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1);
               KRange (EVar 39) 0 (2 ^ 31 - 1);
               KWr (SA (EVar 32) 0) 8; KWord (SA (EVar 32) 20) 4 (EVar 38); KWord (SA (EVar 32) 16) 4 (EVar 39)])
      by (ex_know regs).
    ex_run 60%nat [160752%Z] (SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    all: try (lazymatch goal with |- branch_taken _ _ _ = _ => am4_sc end).
    exists R'. split.
    { eapply ex_msteps_mem; [exact Hms|]. cbn [mem_denot s_log e_addr e_width e_val].
      apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | ]. f_equal. ex_val regs. am4_fin. }
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
    all: am_fin.
    all: try am4_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma am_N4 : forall (last : bool) regs m (i b : Z),
    (0 <= i)%Z -> (i + 1 <= b < 2 ^ 31)%Z -> (if last then i + 1 = b else i + 1 < b)%Z ->
    getr regs 21 = Z_to_bv 64 i -> getr regs 8 = Z_to_bv 64 b ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_R4) m rom) (mkst regs' (Z_to_bv 64 (if last then AM_X4 else AM_H4)) m rom)
      /\ getr regs' 21 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun x => In x [21]%list) regs regs'.
  Proof.
    intros last regs m i b Hi Hb Hl H21 H8.
    unfold AM_R4, AM_X4, AM_H4.
    ex_entry regs [i; b] HR.
    assert (HK : know_ok SEGS (ex_env regs [i; b]) m
                   [KRange (EVar 32) 0 (2 ^ 31 - 2); KRange (EVar 33) 1 (2 ^ 31 - 1)]) by (ex_know regs).
    destruct last; cbv beta iota in Hl |- *.
    - ex_run 20%nat [0x1c678%Z; 0x1c5f8%Z] (SCR [false] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
    - ex_run 20%nat [0x1c678%Z; 0x1c5f8%Z] (SCR [true] [] []) HR HK R' HR' Hms.
      all: try am_sc.
      exists R'. split; [ex_mem regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR'].
      all: am_fin.
  Qed.

  Lemma am_wz : forall w : word, exists z, w = Z_to_bv 64 z /\ (0 <= z < 2 ^ 64)%Z.
  Proof.
    intros w. exists (bv_unsigned w). split; [symmetry; apply Z_to_bv_bv_unsigned |].
    pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr. first [exact Hr | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma am_E : forall regs r0 m (s res : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 63)%Z -> ret_ok ret -> cellsZ m (frameM s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 20 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 AM_X4) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 res
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s res ret Hs1 Hs2 Hret HC H2 H20.
    unfold frameM in HC; cbn [cellsZ] in HC.
    destruct HC as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & _).
    destruct (am_wz ret) as (z1 & E1 & B1). subst ret.
    destruct (am_wz (getr r0 8)) as (z8 & E8 & B8). rewrite E8 in C8.
    destruct (am_wz (getr r0 9)) as (z9 & E9 & B9). rewrite E9 in C9.
    destruct (am_wz (getr r0 18)) as (z18 & E18 & B18). rewrite E18 in C18.
    destruct (am_wz (getr r0 19)) as (z19 & E19 & B19). rewrite E19 in C19.
    destruct (am_wz (getr r0 20)) as (z20 & E20 & B20). rewrite E20 in C20.
    destruct (am_wz (getr r0 21)) as (z21 & E21 & B21). rewrite E21 in C21.
    destruct (am_wz (getr r0 22)) as (z22 & E22 & B22). rewrite E22 in C22.
    destruct (am_wz (getr r0 23)) as (z23 & E23 & B23). rewrite E23 in C23.
    unfold AM_X4.
    ex_entry regs [(s - 96)%Z; res; z1; z8; z9; z18; z19; z20; z21; z22; z23] HR.
    assert (HK : know_ok SEGS (ex_env regs [(s - 96)%Z; res; z1; z8; z9; z18; z19; z20; z21; z22; z23]) m
              [KRange (EVar 32) 0 (2 ^ 63 - 1);
               KWord (SA (EVar 32) 88) 8 (EVar 34); KWord (SA (EVar 32) 80) 8 (EVar 35); KWord (SA (EVar 32) 72) 8 (EVar 36);
               KWord (SA (EVar 32) 64) 8 (EVar 37); KWord (SA (EVar 32) 56) 8 (EVar 38); KWord (SA (EVar 32) 48) 8 (EVar 39);
               KWord (SA (EVar 32) 40) 8 (EVar 40); KWord (SA (EVar 32) 32) 8 (EVar 41); KWord (SA (EVar 32) 24) 8 (EVar 42)])
      by (ex_know regs).
    ex_run 40%nat [116532%Z] (SCR [] [] []) HR HK R' HR' Hms.
    assert (Hms2 : msteps SEGS (mkst regs (Z_to_bv 64 116344) m rom) (mkst R' (Z_to_bv 64 116532) m rom))
      by (ex_mem regs Hms).
    eexists. split.
    - eapply msteps_trans; [exact Hms2|].
      stepret F_1c734 D_1c734 (Z_to_bv 64 z1) ltac:(idtac; ex_reg regs HR').
      apply mst_refl.
    - split; [ex_reg regs HR' |]. split; [ex_reg regs HR' |]. split; [ex_reg regs HR' |].
      split; [| ex_agree HR HR'].
      intros x Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
      all: rewrite ?E8, ?E9, ?E18, ?E19, ?E20, ?E21, ?E22, ?E23; ex_reg regs HR'.
      all: am_fin.
  Qed.

End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition amfr (m : word -> option byte) (s : Z) (ret : word) (r0 : bvmap 5 word) (w h : Z) : Prop :=
  cellsZ m (frameM s ret r0) /\
  rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m (Z_to_bv 64 (s - 80)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)).

Ltac amfr_rd := repeat (rewrite rdn_wbytes_out_Z by (zlen; lia_fast));
  first [apply rdn_wbytes_hit8 | apply rdn_wbytes_hit4]; rewrite ?u_Z2bv by lia; lia.

Lemma amfr_init : forall m s ret regs w h, (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  amfr (DIM2 (FRM9 m s ret regs) s w h) s ret regs w h.
Proof.
  intros m s ret regs w h Hs1 Hs2.
  unfold amfr, frameM, DIM2, FRM9. cbn [cellsZ].
  repeat match goal with |- _ /\ _ => split | |- True => exact I end.
  all: amfr_rd.
Qed.

Lemma amfr_frm : forall C s' m m' s ret r0 w h, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 80)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  amfr m s ret r0 w h -> amfr m' s ret r0 w h.
Proof.
  intros C s' m m' s ret r0 w h CK F Hlo Hs' Hs1 Hs2 [Hc [Hw Hh]].
  pose proof (frameM_bounds s ret r0 Hs1 Hs2) as FB.
  split; [| split].
  - eapply cellsZ_frm; [exact CK | exact F | exact Hlo | | exact Hc].
    revert FB. apply Forall_impl. intros [a v] Hb. cbn [fst] in *. lia.
  - rewrite (FRM_rdn16 C s' m m' (s - 76) 4 CK F) by (cbn; lia). exact Hw.
  - rewrite (FRM_rdn16 C s' m m' (s - 80) 4 CK F) by (cbn; lia). exact Hh.
Qed.

Lemma amfr_out : forall m m' (lo hi : Z) s ret r0 w h, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 80 \/ s <= lo)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  amfr m s ret r0 w h -> amfr m' s ret r0 w h.
Proof.
  intros m m' lo hi s ret r0 w h OUT Hd Hs1 Hs2 [Hc [Hw Hh]].
  pose proof (frameM_bounds s ret r0 Hs1 Hs2) as FB.
  split; [| split].
  - eapply cellsZ_out; [exact OUT | | exact Hc].
    revert FB. apply Forall_impl. intros [a v] Hb. cbn [fst] in *. lia.
  - rewrite <- Hw. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia |].
    intros x Hx. apply OUT. cbn in Hx. lia.
  - rewrite <- Hh. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia |].
    intros x Hx. apply OUT. cbn in Hx. lia.
Qed.

End AmbSegs.
