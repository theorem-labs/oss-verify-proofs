(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptExec LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRotLR.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PC_pixFlipLR : Z := 0x98b88.

(* [comment removed for export] *)
Definition FRLR (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
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
Definition DIMLR (m : word -> option byte) (s : Z) (w h d : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 120)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 124)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 120)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
    (Z_to_bv 64 (s - 124)) (word_to_le_bytes 4 (Z_to_bv 64 d)).
(* [comment removed for export] *)
Definition PCFLR (m : word -> option byte) (s pix : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (Z_to_bv 64 0x98c10)))
    (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
    (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
    (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pix)).
Definition MLR_A (m : word -> option byte) (s pix : Z) (v : pixv) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  PCFLR (DIMLR (FRLR m s ret regs) s (p_w v) (p_h v) (p_d v)) s pix regs.
Definition MLR_D (m : word -> option byte) (s w : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 (w + 7))))
    (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 ((w + 7) / 8))).

Ltac lr_beq regs :=
  first [ reflexivity
        | solve [f_equal; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
                 repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
                 rewrite ?ex_sx32 by lia; first [reflexivity | f_equal; lia]]
        | solve [ex_bytes_eq regs] ].
Ltac lr_mem regs Hms :=
  eapply ex_msteps_mem; [exact Hms | cbn [mem_denot s_log e_addr e_width e_val];
    repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | lr_beq regs ]); reflexivity].

Section RotLR.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma lr_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (4096 + 208 <= s)%Z -> (s < 2 ^ 48)%Z -> (s mod 16 = 0)%Z ->
    (4096 <= pix)%Z -> (pix + 64 < 2 ^ 48)%Z -> (pix mod 8 = 0)%Z ->
    PIXat m pix v -> (pix + 64 <= s - 208 \/ s <= pix)%Z -> p_d v = 1%Z ->
    (1 <= p_w v)%Z -> (1 <= p_h v)%Z -> (1 <= p_wpl v)%Z -> (4096 <= p_data v < 2 ^ 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98b88) m rom) (mkst regs' (Z_to_bv 64 0x10e6e0) (MLR_A m s pix v ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0x98c60
      /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 1
      /\ getr regs' 8 = Z_to_bv 64 (p_data v) /\ getr regs' 9 = Z_to_bv 64 pix /\ getr regs' 18 = Z_to_bv 64 (p_wpl v)
      /\ getr regs' 19 = Z_to_bv 64 256 /\ getr regs' 20 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs2 Hsa Hp Hp2 Hpa PX Hsep Hd Hw Hh Hwpl Hdat SOK H2 H1 H10 H11.
    pose proof PX as PXc. destruct PXc as (_ & _ & WF & _). destruct WF.
    pose proof (PIX_rd_w SEGS m pix v PX) as Rw. pose proof (PIX_rd_h SEGS m pix v PX) as Rh.
    pose proof (PIX_rd_d SEGS m pix v PX) as Rd. pose proof (PIX_rd_wpl SEGS m pix v PX) as Rwpl.
    pose proof (PIX_rd_data SEGS m pix v PX) as Rdat. rewrite Hd in Rd.
    ex_entry regs [pix; p_w v; p_h v; p_wpl v; p_data v]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [pix; p_w v; p_h v; p_wpl v; p_data v]%Z) m
      [KRange (EVar 2) (4096 + 208) (2 ^ 48); KAlign (EVar 2) 16; KWr (SA (EVar 2) (-208)) 208;
       KRange (EVar 32) 4096 (2 ^ 48); KAlign (EVar 32) 8;
       KDisj (SA (EVar 2) (-208)) 208 (SA (EVar 32) 0) 64;
       KWord (SA (EVar 32) 0) 4 (EVar 33); KWord (SA (EVar 32) 4) 4 (EVar 34); KWord (SA (EVar 32) 8) 4 (ELit 1);
       KWord (SA (EVar 32) 16) 4 (EVar 35); KWord (SA (EVar 32) 56) 8 (EVar 36);
       KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 1 (2 ^ 31 - 1);
       KRange (EVar 36) 4096 (2 ^ 48)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x10e6e0]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - lr_mem regs Hms.
    - repeat split; try (ex_reg regs HR'; try (rewrite ex_sx32 by lia; reflexivity)). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_T0 : forall regs m (tab : Z), (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z -> getr regs 10 = Z_to_bv 64 tab ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98c60) m rom) (mkst regs' (Z_to_bv 64 0x98c70) m rom)
      /\ getr regs' 9 = Z_to_bv 64 tab /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 tab
      /\ regs_agree (fun r => In r [9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m tab Ht Ht2 H10.
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m [KRange (EVar 10) 4096 (2 ^ 48)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
    ex_run 50%nat [0x98c70]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'; try (apply zbv_snez; lia)). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_T1n : forall regs m (tab i : Z),
    (0 <= i)%Z -> (i + 1 < 256)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (tab + i)) 1 = true ->
    getr regs 9 = Z_to_bv 64 tab -> getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 1 ->
    getr regs 12 = Z_to_bv 64 (tab + i) -> getr regs 19 = Z_to_bv 64 (256 - i) ->
    exists regs' (x : word),
      msteps SEGS (mkst regs (Z_to_bv 64 0x98c70) m rom)
                  (mkst regs' (Z_to_bv 64 0x98c70) (wbytes m (Z_to_bv 64 (tab + i)) (word_to_le_bytes 1 x)) rom)
      /\ getr regs' 9 = Z_to_bv 64 tab /\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 1
      /\ getr regs' 12 = Z_to_bv 64 (tab + (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (256 - (i + 1))
      /\ regs_agree (fun r => In r [10; 12; 13; 14; 19]%list) regs regs'.
  Proof.
    intros regs m tab i Hi Hi1 Ht Ht2 SOK H9 H10 H11 H12 H19.
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KRange (EVar 9) 4096 (2 ^ 48); KRange (EVar 10) 0 254; KRange (EVar 12) 4096 (2 ^ 48 + 254); KRange (EVar 19) 2 256]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
    ex_run 300%nat [0x98c70; 0x10e6e0]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. eexists. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    rewrite Z.add_0_r; exact SOK.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_T1x : forall regs m (tab i wpl : Z),
    (i = 255)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
    store_ok SEGS m (Z_to_bv 64 (tab + i)) 1 = true ->
    getr regs 9 = Z_to_bv 64 tab -> getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 1 ->
    getr regs 12 = Z_to_bv 64 (tab + i) -> getr regs 19 = Z_to_bv 64 (256 - i) -> getr regs 18 = Z_to_bv 64 wpl ->
    exists regs' (x : word),
      msteps SEGS (mkst regs (Z_to_bv 64 0x98c70) m rom)
                  (mkst regs' (Z_to_bv 64 0x10e6e0) (wbytes m (Z_to_bv 64 (tab + i)) (word_to_le_bytes 1 x)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x98e94 /\ getr regs' 10 = Z_to_bv 64 wpl /\ getr regs' 11 = Z_to_bv 64 4
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 19]%list) regs regs'.
  Proof.
    intros regs m tab i wpl Hi Ht Ht2 SOK H9 H10 H11 H12 H19 H18. subst i.
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KRange (EVar 9) 4096 (2 ^ 48); KRange (EVar 10) 255 255; KRange (EVar 12) 4096 (2 ^ 48 + 255); KRange (EVar 19) 1 1]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
    ex_run 300%nat [0x98c70; 0x10e6e0]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. eexists. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: try (rewrite ?Z.add_0_r; exact SOK).
  Qed.

  (* [comment removed for export] *)
  Lemma lr_Rn : forall regs m (s h i wpl : Z),
    (4096 + 208 <= s < 2 ^ 48)%Z -> (0 <= i)%Z -> (i + 1 < h < 2 ^ 31)%Z -> (1 <= wpl < 2 ^ 29)%Z -> (4 * wpl * h <= 2 ^ 26)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 18 = Z_to_bv 64 wpl -> getr regs 23 = Z_to_bv 64 (wpl * i) ->
    getr regs 26 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x99068) m rom) (mkst regs' (Z_to_bv 64 0x98f6c) m rom)
      /\ getr regs' 26 = Z_to_bv 64 (i + 1) /\ getr regs' 23 = Z_to_bv 64 (wpl * (i + 1))
      /\ regs_agree (fun r => In r [10; 11; 23; 26]%list) regs regs'.
  Proof.
    intros regs m s h i wpl Hs Hi Hh Hw Hwh Rh H2 H18 H23 H26.
    assert (Hwi : (0 <= wpl * i)%Z) by nia.
    assert (Hwi1 : (wpl * (i + 1) <= 2 ^ 24)%Z) by nia.
    ex_entry regs [s; h; wpl; i]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; h; wpl; i]%Z) m
                   [KRange (EVar 32) (4096 + 208) (2 ^ 48); KWord (SA (EVar 32) (-120)) 4 (EVar 33)]%Z) by (ex_know regs).
    ex_run 300%nat [0x98f6c]%Z (SCR [false; true] [] []) HR HK R' HR' Hms.
    all: try (solve [rewrite ?w_addw, ?zbv_addw_small by lia; ex_br]).
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'; rewrite ?zbv_addw_small by lia; try reflexivity; try (f_equal; lia)).
      ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_Rx : forall regs m (s h i buf : Z),
    (4096 + 208 <= s < 2 ^ 48)%Z -> (0 <= i)%Z -> (i + 1 = h)%Z -> (h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 26 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 buf ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x99068) m rom) (mkst regs' (Z_to_bv 64 0x10e818) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x99790 /\ getr regs' 10 = Z_to_bv 64 buf
      /\ regs_agree (fun r => In r [1; 10; 11; 23; 26]%list) regs regs'.
  Proof.
    intros regs m s h i buf Hs Hi Hh Hh2 Rh H2 H26 H19.
    ex_entry regs [s; h; i; buf]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; h; i; buf]%Z) m
                   [KRange (EVar 32) (4096 + 208) (2 ^ 48); KWord (SA (EVar 32) (-120)) 4 (EVar 33)]%Z) by (ex_know regs).
    ex_run 300%nat [0x10e818]%Z (SCR [false; false] [] []) HR HK R' HR' Hms.
    all: try (solve [rewrite ?w_addw, ?zbv_addw_small by lia; ex_br]).
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_F : forall regs m (tab : Z), (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z -> getr regs 9 = Z_to_bv 64 tab ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x99790) m rom) (mkst regs' (Z_to_bv 64 0x10e818) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x9979c /\ getr regs' 10 = Z_to_bv 64 tab
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m tab Ht Ht2 H9.
    ex_entry regs [tab]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [tab]%Z) m []%Z) by (ex_know regs).
    ex_run 300%nat [0x10e818]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: try (solve [ex_br]).
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_G : forall regs m (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 pd : word),
    (4096 + 208 <= s < 2 ^ 48)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9); (s - 32, v18); (s - 40, v19); (s - 48, v20); (s - 56, v21);
              (s - 64, v22); (s - 72, v23); (s - 80, v24); (s - 88, v25); (s - 96, v26); (s - 104, v27); (s - 112, pd)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 160) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x9979c) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = pd
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20
      /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25
      /\ getr regs' 26 = v26 /\ getr regs' 27 = v27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 pd Hs Hret HC H2.
    cbn [cellsZ] in HC.
    destruct HC as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    ex_entryL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; pd] regs [s] HR.
    assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; pd] regs [s]) m
                   [KRange (EVar 46) (4096 + 208) (2 ^ 48);
                    KWord (SA (EVar 46) (-8)) 8 (EVar 0); KWord (SA (EVar 46) (-16)) 8 (EVar 1);
                    KWord (SA (EVar 46) (-24)) 8 (EVar 2); KWord (SA (EVar 46) (-32)) 8 (EVar 3);
                    KWord (SA (EVar 46) (-40)) 8 (EVar 4); KWord (SA (EVar 46) (-48)) 8 (EVar 5);
                    KWord (SA (EVar 46) (-56)) 8 (EVar 6); KWord (SA (EVar 46) (-64)) 8 (EVar 7);
                    KWord (SA (EVar 46) (-72)) 8 (EVar 8); KWord (SA (EVar 46) (-80)) 8 (EVar 9);
                    KWord (SA (EVar 46) (-88)) 8 (EVar 10); KWord (SA (EVar 46) (-96)) 8 (EVar 11);
                    KWord (SA (EVar 46) (-104)) 8 (EVar 12); KWord (SA (EVar 46) (-112)) 8 (EVar 13)]%Z) by (ex_know regs).
    ex_run 300%nat (@nil Z) (SCR [] [] []) HR HK R' HR' Hms.
    assert (AG : regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs R') by (ex_agree HR HR').
    assert (G1 : getr R' 1 = ret) by (ex_reg regs HR').
    assert (G2 : getr R' 2 = Z_to_bv 64 s) by (ex_reg regs HR').
    assert (G10 : getr R' 10 = pd) by (ex_reg regs HR').
    assert (G8 : getr R' 8 = v8) by (ex_reg regs HR').
    assert (G9 : getr R' 9 = v9) by (ex_reg regs HR').
    assert (G18 : getr R' 18 = v18) by (ex_reg regs HR').
    assert (G19 : getr R' 19 = v19) by (ex_reg regs HR').
    assert (G20 : getr R' 20 = v20) by (ex_reg regs HR').
    assert (G21 : getr R' 21 = v21) by (ex_reg regs HR').
    assert (G22 : getr R' 22 = v22) by (ex_reg regs HR').
    assert (G23 : getr R' 23 = v23) by (ex_reg regs HR').
    assert (G24 : getr R' 24 = v24) by (ex_reg regs HR').
    assert (G25 : getr R' 25 = v25) by (ex_reg regs HR').
    assert (G26 : getr R' 26 = v26) by (ex_reg regs HR').
    assert (G27 : getr R' 27 = v27) by (ex_reg regs HR').
    cbn [mem_denot] in Hms.
    exists R'. split.
    - eapply msteps_trans; [exact Hms|].
      lazymatch type of Hms with msteps _ _ (mkst _ (Z_to_bv 64 ?p) _ _) => ex_fetch SEGS p F D end.
      lazymatch type of D with decode_any ?w = _ =>
        assert (Dj : decode_any w = Some (Jalr 0 1 0, 4%Z)) by (rewrite D; f_equal; f_equal; f_equal; apply bv_eq; reflexivity) end.
      eapply mst_step; [reflexivity | eapply step_jalr_x0; [exact F | reflexivity | exact Dj | exact G1] |].
      match goal with |- msteps _ (mkst _ ?t _ _) _ => replace t with ret by (symmetry; exact (Hret : v_jalr ret 0 = ret)) end.
      apply mst_refl.
    - repeat split; assumption.
  Qed.

  Lemma v23lr_addw : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof.
    intros a b H. rewrite v_addw_Z. unfold sw32. f_equal. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma v23lr_mul : forall a b : Z, Sem.mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof.
    intros a b. rewrite m_mul. apply zbv_mul.
  Qed.

  Lemma v23lr_add : forall a b : Z, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof.
    intros a b. rewrite <- alu_add. apply ex_ptr_val.
  Qed.

  Lemma v23lr_srl : forall a k : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= k < 64)%Z -> v_srl (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a / 2 ^ k).
  Proof.
    intros a k Ha Hk. unfold v_srl. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.

  Lemma v23lr_and31 : forall w : Z, (0 <= w < 2 ^ 64)%Z -> v_and (Z_to_bv 64 w) (Z_to_bv 64 31) = Z_to_bv 64 (w mod 32).
  Proof.
    intros w Hw. unfold v_and. rewrite !u_Z2bv by lia. rewrite land31 by lia. reflexivity.
  Qed.

  Lemma v23lr_db : forall w : Z, (1 <= w < 2 ^ 30)%Z ->
    v_srl (Sem.mul_div M_MUL (Z_to_bv 64 536870912) (v_addw (v_addw (Z_to_bv 64 w) (Z_to_bv 64 7))
      (v_srl (Sem.mul_div M_MUL (Z_to_bv 64 2) (v_addw (Z_to_bv 64 w) (Z_to_bv 64 7))) (Z_to_bv 64 61)))) (Z_to_bv 64 32)
    = Z_to_bv 64 ((w + 7) / 8).
  Proof.
    intros w Hw.
    rewrite (v23lr_addw w 7) by lia. rewrite (v23lr_mul 2 (w + 7)). rewrite (v23lr_srl (2 * (w + 7)) 61) by lia.
    rewrite (Z.div_small (2 * (w + 7)) (2 ^ 61)) by lia.
    rewrite (v23lr_addw (w + 7) 0) by lia. rewrite (v23lr_mul 536870912 (w + 7 + 0)). rewrite v23lr_srl by lia.
    f_equal. rewrite Z.add_0_r. replace (2 ^ 32)%Z with (536870912 * 8)%Z by reflexivity.
    rewrite <- Z.div_div by lia. rewrite (Z.mul_comm 536870912 (w + 7)). rewrite Z.div_mul by lia. reflexivity.
  Qed.

  Lemma v23lr_flag : forall q : Z, (1 <= q < 2 ^ 31)%Z ->
    v_xor (v_slt (v_addw (Z_to_bv 64 q) (Z_to_bv 64 (-1))) (Z_to_bv 64 q)) (Z_to_bv 64 1) = Z_to_bv 64 0.
  Proof.
    intros q Hq. rewrite v23lr_addw by lia. unfold v_slt, c_lts, bv_lts. rewrite !GrayLib.bv_signed_Zs by lia.
    replace (q + -1 <? q)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    unfold v_xor. rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_Bh : forall regs m (s w h wpl data buf tab : Z),
    (4096 + 208 <= s)%Z -> (s < 2 ^ 48)%Z ->
    (1 <= w < 2 ^ 30)%Z -> (1 <= h < 2 ^ 31)%Z -> (1 <= wpl < 2 ^ 29)%Z -> (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z ->
    (w mod 32 <> 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS m (Z_to_bv 64 0x1f7e8) 4 = Some (Z_to_le_bytes 4 497396) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 data -> getr regs 9 = Z_to_bv 64 tab ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 18 = Z_to_bv 64 wpl ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98e94) m rom) (mkst regs' (Z_to_bv 64 0x875f4) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x98f0c
      /\ getr regs' 10 = Z_to_bv 64 data /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 wpl
      /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 h /\ getr regs' 16 = Z_to_bv 64 (32 - w mod 32)
      /\ getr regs' 19 = Z_to_bv 64 buf /\ getr regs' 20 = Z_to_bv 64 (4 * wpl)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s w h wpl data buf tab Hs1 Hs2 Hw Hh Hwpl Hb1 Hb2 Hwm Rw Rh Rd Rj H2 H8 H9 H10 H18.
    ex_entry regs [w; h; wpl; buf]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [w; h; wpl; buf]%Z) m
      [KRange (EVar 2) (4096 + 48) (2 ^ 48);
       KWord (SA (EVar 2) 44) 4 (EVar 32); KWord (SA (EVar 2) 40) 4 (EVar 33); KWord (SA (EVar 2) 36) 4 (ELit 1);
       KWord (SA (ELit 0) 0x1f7e8) 4 (ELit 497396);
       KRange (EVar 32) 1 (2 ^ 30 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 29 - 1);
       KRange (EVar 35) 4096 (2 ^ 48)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x875f4]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'; first [ (apply ex_sx32; lia)
          | (rewrite ex_sx32 by lia; rewrite v23lr_and31 by lia; rewrite v23lr_mul, v23lr_add; f_equal; lia) | idtac ]).
        ex_agree HR HR'. }
    pose proof (Z.mod_pos_bound w 32 ltac:(lia)). rewrite ex_sx32 by lia. rewrite alu_and, v23lr_and31 by lia. ex_br.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_Bn : forall regs m (s w wpl buf : Z),
    (4096 + 208 <= s)%Z -> (s < 2 ^ 48)%Z ->
    (1 <= w < 2 ^ 30)%Z -> (1 <= wpl < 2 ^ 29)%Z -> (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z ->
    (w mod 32 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS m (Z_to_bv 64 0x1f7e8) 4 = Some (Z_to_le_bytes 4 497396) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 buf -> getr regs 18 = Z_to_bv 64 wpl ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98e94) m rom) (mkst regs' (Z_to_bv 64 0x98f10) m rom)
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 19 = Z_to_bv 64 buf /\ getr regs' 20 = Z_to_bv 64 (4 * wpl)
      /\ regs_agree (fun r => In r [10; 11; 12; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s w wpl buf Hs1 Hs2 Hw Hwpl Hb1 Hb2 Hwm Rw Rd Rj H2 H10 H18.
    ex_entry regs [w; wpl; buf]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [w; wpl; buf]%Z) m
      [KRange (EVar 2) (4096 + 48) (2 ^ 48);
       KWord (SA (EVar 2) 44) 4 (EVar 32); KWord (SA (EVar 2) 36) 4 (ELit 1);
       KWord (SA (ELit 0) 0x1f7e8) 4 (ELit 497396);
       KRange (EVar 32) 1 (2 ^ 30 - 1); KRange (EVar 33) 1 (2 ^ 29 - 1);
       KRange (EVar 34) 4096 (2 ^ 48)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x98f10]%Z (SCR [true] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'; first [ (apply ex_sx32; lia) | idtac ]).
        ex_agree HR HR'. }
    pose proof (Z.mod_pos_bound w 32 ltac:(lia)). rewrite ex_sx32 by lia. rewrite alu_and, v23lr_and31 by lia. ex_br.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_C : forall regs m (s w : Z), (4096 + 208 <= s)%Z -> (s < 2 ^ 48)%Z -> (1 <= w < 2 ^ 30)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98f0c) m rom) (mkst regs' (Z_to_bv 64 0x98f10) m rom)
      /\ getr regs' 10 = Z_to_bv 64 w /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s w Hs1 Hs2 Hw Rw H2.
    ex_entry regs [w]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [w]%Z) m
      [KRange (EVar 2) (4096 + 48) (2 ^ 48); KWord (SA (EVar 2) 44) 4 (EVar 32); KRange (EVar 32) 1 (2 ^ 30 - 1)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 100%nat [0x98f10]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - split; [ex_reg regs HR'; first [apply ex_sx32; lia | idtac] |]. ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_D : forall regs m (s w h wpl data buf tab : Z),
    (4096 + 208 <= s)%Z -> (s < 2 ^ 48)%Z -> (1 <= w < 2 ^ 30)%Z -> (1 <= h < 2 ^ 31)%Z -> (1 <= wpl < 2 ^ 29)%Z ->
    (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
    (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (buf mod 4 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 data -> getr regs 9 = Z_to_bv 64 tab -> getr regs 10 = Z_to_bv 64 w ->
    getr regs 18 = Z_to_bv 64 wpl -> getr regs 19 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 (4 * wpl) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98f10) m rom) (mkst regs' (Z_to_bv 64 0x98f6c) (MLR_D m s w) rom)
      /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 3
      /\ getr regs' 25 = Z_to_bv 64 (4 * wpl - 1) /\ getr regs' 26 = Z_to_bv 64 0 /\ getr regs' 27 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 11; 12; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s w h wpl data buf tab Hs1 Hs2 Hw Hh Hwpl Hd1 Hd2 Ht1 Ht2 Hb1 Hb2 Hb3 SOK Rh H2 H8 H9 H10 H18 H19 H20.
    assert (Hd3 : (data < 2 ^ 48)%Z) by nia.
    ex_entry regs [w; h; wpl; data; tab]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [w; h; wpl; data; tab]%Z) m
      [KRange (EVar 2) (4096 + 48) (2 ^ 48); KWr (SA (EVar 2) 0) 160; KWord (SA (EVar 2) 40) 4 (EVar 33);
       KRange (EVar 32) 1 (2 ^ 30 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 29 - 1);
       KRange (EVar 20) 4 (2 ^ 31 - 4); KRange (EVar 35) 4096 (2 ^ 48); KRange (EVar 36) 4096 (2 ^ 48);
       KRange (EVar 19) 4096 (2 ^ 48); KAlign (EVar 19) 4]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x98f6c]%Z (SCR [false; false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - unfold MLR_D. eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
        repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | ex_bytes_eq regs ]).
        all: first [ reflexivity | (symmetry; apply v23lr_db; lia) | (symmetry; apply v23lr_flag; lia) | (rewrite v23lr_addw by lia; reflexivity) ].
      - repeat split; try (ex_reg regs HR'; first [ (apply zbv_snez; lia) | (rewrite v23lr_addw by lia; f_equal; lia) | idtac ]).
        ex_agree HR HR'. }
    rewrite w_addw, v23lr_addw by lia. ex_br.
  Qed.

  Lemma v23lrE_add : forall a b : Z, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof. intros a b. rewrite <- alu_add. apply ex_ptr_val. Qed.

  Lemma v23lrE_sltu0 : forall a b : Z, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z -> v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
  Proof. intros a b Hb Ha. apply zbv_sltu_ge; lia. Qed.

  Lemma v23lrE_slt0 : forall a : Z, (0 <= a < 2 ^ 63)%Z -> v_slt (Z_to_bv 64 a) (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof.
    intros a Ha. unfold v_slt, c_lts, bv_lts.
    rewrite !GrayLib.bv_signed_Zs by lia.
    destruct (Z.ltb_spec a 0); [lia | reflexivity].
  Qed.

  Lemma v23lrE_xor : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
  Proof. intros a b Ha Hb. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.

  Lemma v23lrE_xor3 : forall p : Z, (0 <= p < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 p) (Z_to_bv 64 3) = Z_to_bv 64 (flip3 p).
  Proof. intros p Hp. rewrite v23lrE_xor by lia. unfold flip3. rewrite lxor3_eq by lia. reflexivity. Qed.

  Lemma v23lrE_and3 : forall d k : Z, (d mod 4 = 0)%Z -> (0 <= d + 4 * k < 2 ^ 64)%Z ->
    v_and (Z_to_bv 64 (d + 4 * k)) (Z_to_bv 64 3) = Z_to_bv 64 0.
  Proof.
    intros d k Hd Hk. unfold v_and. rewrite !u_Z2bv by lia.
    change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z.
    rewrite Z.add_mod by lia. rewrite Hd. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
  Qed.

  Lemma v23lrE_flip3_rng : forall p : Z, (0 <= p)%Z -> (0 <= flip3 p)%Z /\ (p - 3 <= flip3 p <= p + 3)%Z.
  Proof.
    intros p Hp. unfold flip3. pose proof (Z.mod_pos_bound p 4 ltac:(lia)). pose proof (Z.mod_le p 4 ltac:(lia) ltac:(lia)). lia.
  Qed.

  Ltac v23lrE_sc :=
    rewrite ?w_addw, ?w_subw, ?w_mulw, ?m_mul, ?alu_add, ?alu_sub, ?alu_xor, ?alu_sltu, ?alu_slt, ?alu_and;
    repeat first
      [ rewrite zbv_mul
      | rewrite v23lrE_add
      | rewrite zbv_addi
      | rewrite v_addw_Z
      | rewrite v_subw_Z
      | rewrite Z.lxor_0_l
      | rewrite Z.lxor_0_r
      | rewrite zbv_mulw_small by (first [lia | nia])
      | rewrite sw32_small by (first [lia | nia])
      | rewrite v23lrE_sltu0 by (first [lia | nia])
      | rewrite v23lrE_slt0 by (first [lia | nia])
      | rewrite v23lrE_and3 by (first [assumption | lia | nia])
      | rewrite v23lrE_xor3 by (first [lia | nia])
      | rewrite v23lrE_xor by (first [lia | nia]) ].

  Ltac v23lrE_reg regs HR' :=
    lazymatch goal with
    | |- getr _ ?k = _ =>
        rewrite (reg_val _ _ _ k HR');
        match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
        ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
        repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
        v23lrE_sc; first [reflexivity | (f_equal; first [lia | nia])]
    end.

  Ltac v23lrE_at H :=
    match goal with |- context [Z_to_bv 64 ?a] =>
      match type of H with context [Z_to_bv 64 ?a'] =>
        replace a with a' by (rewrite ?Z.add_0_r; first [reflexivity | lia | (f_equal; lia)]); exact H end end.

  Ltac v23lrE_sc2 :=
    first
      [ solve [v23lrE_sc; ex_br]
      | solve [v23lrE_sc; match goal with H : store_ok _ _ _ _ = true |- _ => v23lrE_at H end]
      | solve [match goal with H : rdn _ _ _ 1 = Some [?b] |- _ =>
                 exists [b]; split; [v23lrE_sc; v23lrE_at H | cbn [extz]; rewrite bytes_le_single; reflexivity] end]
      | solve [v23lrE_sc; match goal with |- context [flip3 ?p] => pose proof (v23lrE_flip3_rng p ltac:(lia)) end;
               rewrite ?u_Z2bv by lia; repeat split; lia] ].

  (* [comment removed for export] *)
  Lemma lr_H : forall regs m (s wpl h data buf i : Z),
    (0 <= i < h)%Z -> (1 <= wpl)%Z -> (4 * wpl * h <= 2 ^ 26)%Z -> (4096 <= data)%Z -> (data + 4 * wpl * h < 2 ^ 48)%Z ->
    (data mod 4 = 0)%Z -> (4096 + 208 <= s < 2 ^ 48)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 data -> getr regs 18 = Z_to_bv 64 wpl ->
    getr regs 19 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 (4 * wpl) -> getr regs 26 = Z_to_bv 64 i -> getr regs 27 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98f6c) m rom) (mkst regs' (Z_to_bv 64 0x11e154) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x98fc0 /\ getr regs' 10 = Z_to_bv 64 buf
      /\ getr regs' 11 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 12 = Z_to_bv 64 (4 * wpl)
      /\ getr regs' 21 = Z_to_bv 64 (data + 4 * wpl * i)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 21]%list) regs regs'.
  Proof.
    intros regs m s wpl h data buf i Hi Hw Hwh Hd Hd2 Hda Hs Hz H2 H8 H18 H19 H20 H26 H27.
    assert (Hr : (wpl <= 2 ^ 24)%Z /\ (h <= 2 ^ 26)%Z /\ (0 <= i * wpl)%Z /\ (4 * (i * wpl) + 4 * wpl <= 4 * wpl * h)%Z) by (repeat split; nia).
    ex_entry regs [s; wpl; data; buf; i; 4 * wpl]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; wpl; data; buf; i; 4 * wpl]%Z) m
      [KRange (EVar 32) 4304 (2 ^ 48); KWord (SA (EVar 32) (-144)) 8 (ELit 0);
       KRange (EVar 33) 1 (2 ^ 24); KRange (EVar 34) 4096 (2 ^ 48); KRange (EVar 36) 0 (2 ^ 26)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x11e154]%Z (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
    all: try v23lrE_sc2.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (v23lrE_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_E0 : forall regs m (s w db wpl data i : Z),
    (4096 + 208 <= s < 2 ^ 48)%Z -> (1 <= w < 2 ^ 30)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 db)) ->
    rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 7))) ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 data -> getr regs 23 = Z_to_bv 64 (wpl * i) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0x98fc0) m rom) (mkst regs' (Z_to_bv 64 0x98fe4) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 (data + 4 * wpl * i)
      /\ getr regs' 12 = Z_to_bv 64 db /\ getr regs' 13 = Z_to_bv 64 (data + 4 * wpl * i)
      /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s w db wpl data i Hs Hw Hdb Hz1 Hw7 H2 H8 H23.
    ex_entry regs [s; w + 7; db]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; w + 7; db]%Z) m
      [KRange (EVar 32) 4304 (2 ^ 48); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-152)) 8 (ELit 0);
       KWord (SA (EVar 32) (-136)) 8 (EVar 33); KRange (EVar 33) 8 (2 ^ 30 + 7)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x98fe4]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (v23lrE_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma lr_E1n : forall regs m (wpl buf tab line j db : Z) (b1 b2 : byte),
    (0 <= j)%Z -> (j + 1 < db)%Z -> (db <= 4 * wpl)%Z -> (1 <= wpl < 2 ^ 29)%Z ->
    (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
    (4096 <= line)%Z -> (line + 4 * wpl < 2 ^ 48)%Z ->
    rdn SEGS m (Z_to_bv 64 (flip3 (buf + (4 * wpl - 1 - j)))) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (tab + u b1)) 1 = Some [b2] ->
    store_ok SEGS m (Z_to_bv 64 (flip3 (line + j))) 1 = true ->
    getr regs 9 = Z_to_bv 64 tab -> getr regs 19 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 line ->
    getr regs 22 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 3 -> getr regs 25 = Z_to_bv 64 (4 * wpl - 1) -> getr regs 27 = Z_to_bv 64 1 ->
    getr regs 10 = Z_to_bv 64 j -> getr regs 11 = Z_to_bv 64 (line + j) -> getr regs 12 = Z_to_bv 64 (db - j) ->
    getr regs 13 = Z_to_bv 64 (line + j) ->
    exists regs' (bb : byte),
      msteps SEGS (mkst regs (Z_to_bv 64 0x98fe4) m rom) (mkst regs' (Z_to_bv 64 0x98fe4) (wbytes m (Z_to_bv 64 (flip3 (line + j))) [bb]) rom)
      /\ getr regs' 10 = Z_to_bv 64 (j + 1) /\ getr regs' 11 = Z_to_bv 64 (line + (j + 1))
      /\ getr regs' 12 = Z_to_bv 64 (db - (j + 1)) /\ getr regs' 13 = Z_to_bv 64 (line + (j + 1))
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m wpl buf tab line j db b1 b2 Hj Hjd Hdb Hw Hb Hb2 Ht Ht2 Hl Hl2 Hr1 Hr2 SOK H9 H19 H21 H22 H24 H25 H27 H10 H11 H12 H13.
    pose proof (u8_range b1) as Hu1. pose proof (u8_range b2) as Hu2.
    ex_entry regs [buf; tab; line; j; db; 4 * wpl; line + j; db - j; u b1; u b2]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [buf; tab; line; j; db; 4 * wpl; line + j; db - j; u b1; u b2]%Z) m
      [KRange (EVar 32) 4096 (2 ^ 48); KRange (EVar 33) 4096 (2 ^ 48); KRange (EVar 34) 4096 (2 ^ 48);
       KRange (EVar 35) 0 (2 ^ 31); KRange (EVar 36) 1 (2 ^ 31); KRange (EVar 37) 4 (2 ^ 31);
       KRange (EVar 38) 4096 (2 ^ 48); KRange (EVar 39) 1 (2 ^ 31); KRange (EVar 40) 0 255; KRange (EVar 41) 0 255]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x98fe4; 0x99068]%Z (SCR [false; false; false; false; false; false; true] [EVar 40; EVar 41] []) HR HK R' HR' Hms.
    all: try v23lrE_sc2.
    exists R'. eexists. split.
    - eapply ex_msteps_mem; [exact Hms |].
      cbn [mem_denot s_log e_addr e_width e_val].
      apply ex_wbytes_eq; [reflexivity | | reflexivity].
      ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add].
      v23lrE_sc. rewrite Z.add_0_r. reflexivity.
    - repeat split; try (v23lrE_reg regs HR'). ex_agree HR HR'.
  Qed.


  (* [comment removed for export] *)
  Lemma lr_E1e : forall regs m (wpl buf tab line j db : Z) (b1 b2 : byte),
    (0 <= j)%Z -> (j + 1 = db)%Z -> (db <= 4 * wpl)%Z -> (1 <= wpl < 2 ^ 29)%Z ->
    (4096 <= buf)%Z -> (buf + 4 * wpl < 2 ^ 48)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 48)%Z ->
    (4096 <= line)%Z -> (line + 4 * wpl < 2 ^ 48)%Z ->
    rdn SEGS m (Z_to_bv 64 (flip3 (buf + (4 * wpl - 1 - j)))) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (tab + u b1)) 1 = Some [b2] ->
    store_ok SEGS m (Z_to_bv 64 (flip3 (line + j))) 1 = true ->
    getr regs 9 = Z_to_bv 64 tab -> getr regs 19 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 line ->
    getr regs 22 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 3 -> getr regs 25 = Z_to_bv 64 (4 * wpl - 1) -> getr regs 27 = Z_to_bv 64 1 ->
    getr regs 10 = Z_to_bv 64 j -> getr regs 11 = Z_to_bv 64 (line + j) -> getr regs 12 = Z_to_bv 64 (db - j) ->
    getr regs 13 = Z_to_bv 64 (line + j) ->
    exists regs' (bb : byte),
      msteps SEGS (mkst regs (Z_to_bv 64 0x98fe4) m rom) (mkst regs' (Z_to_bv 64 0x99068) (wbytes m (Z_to_bv 64 (flip3 (line + j))) [bb]) rom)
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m wpl buf tab line j db b1 b2 Hj Hjd Hdb Hw Hb Hb2 Ht Ht2 Hl Hl2 Hr1 Hr2 SOK H9 H19 H21 H22 H24 H25 H27 H10 H11 H12 H13.
    pose proof (u8_range b1) as Hu1. pose proof (u8_range b2) as Hu2.
    ex_entry regs [buf; tab; line; j; db; 4 * wpl; line + j; db - j; u b1; u b2]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [buf; tab; line; j; db; 4 * wpl; line + j; db - j; u b1; u b2]%Z) m
      [KRange (EVar 32) 4096 (2 ^ 48); KRange (EVar 33) 4096 (2 ^ 48); KRange (EVar 34) 4096 (2 ^ 48);
       KRange (EVar 35) 0 (2 ^ 31); KRange (EVar 36) 1 (2 ^ 31); KRange (EVar 37) 4 (2 ^ 31);
       KRange (EVar 38) 4096 (2 ^ 48); KRange (EVar 39) 1 (2 ^ 31); KRange (EVar 40) 0 255; KRange (EVar 41) 0 255]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x98fe4; 0x99068]%Z (SCR [false; false; false; false; false; false; false] [EVar 40; EVar 41] []) HR HK R' HR' Hms.
    all: try v23lrE_sc2.
    exists R'. eexists. split.
    - eapply ex_msteps_mem; [exact Hms |].
      cbn [mem_denot s_log e_addr e_width e_val].
      apply ex_wbytes_eq; [reflexivity | | reflexivity].
      ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add].
      v23lrE_sc. rewrite Z.add_0_r. reflexivity.
    - repeat split; try (v23lrE_reg regs HR'). ex_agree HR HR'.
  Qed.

End Segs.
End RotLR.
