(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec LeptExecX LeptExecFP LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require LeptRop.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRbLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23_code_red_rb2 V23_code_red_acc.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PC_pixReduceRankBinary2 : Z := 0xa6f20.

(* [comment removed for export] *)
Definition FRB (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
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
Definition DIMB (m : word -> option byte) (s : Z) (w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 h)).
Definition MRB_A (m : word -> option byte) (s : Z) (v : pixv) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  DIMB (FRB m s ret regs) s (p_w v) (p_h v).
(* [comment removed for export] *)
Definition MRB_A2 (m : word -> option byte) (s : Z) (v : pixv) : word -> option byte :=
  wbytes (wbytes m (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 (p_wpl v))))
    (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 (p_data v))).

Definition MRB_C (m : word -> option byte) (s pixd : Z) : word -> option byte :=
  wbytes (wbytes m (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
    (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)).
Definition MRB_D (m : word -> option byte) (s pixd tab wpls wpld h datas : Z) : word -> option byte :=
  let m1 := wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
              (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 tab)))
              (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 wpls)) in
  let m2 := if (wpls <? 2 * wpld)%Z then m1 else wbytes m1 (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 (2 * wpld))) in
  wbytes (wbytes (wbytes (wbytes (wbytes m2
    (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 (h - 1))))
    (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 (4 * wpls))))
    (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (Z_to_bv 64 (2 * wpls))))
    (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 (datas + 4 * wpls))))
    (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 0x3fffffff)).

Lemma rb_half : forall w : Z, (0 <= w < 2 ^ 31)%Z ->
  v_sraw (v_add (v_srlw (ext_val true 0 4 (Z_to_bv 64 w)) (Z_to_bv 64 31)) (ext_val true 0 4 (Z_to_bv 64 w))) (Z_to_bv 64 1) = Z_to_bv 64 (w / 2).
Proof.
  intros w Hw. rewrite !ex_sx32 by lia.
  assert (E1 : v_srlw (Z_to_bv 64 w) (Z_to_bv 64 31) = Z_to_bv 64 0).
  { rewrite <- w_srlw. apply bv_eq. rewrite (u_srlw_small (Z_to_bv 64 w) (Z_to_bv 64 31) 31).
    - rewrite !u_Z2bv by lia. change (31 mod 32)%Z with 31%Z. apply Z.div_small. lia.
    - rewrite u_Z2bv by lia. reflexivity.
    - rewrite u_Z2bv by lia. lia.
    - rewrite u_Z2bv by lia. change (31 mod 32)%Z with 31%Z. rewrite Z.div_small by lia. lia. }
  rewrite E1, zbv_add. replace (0 + w)%Z with w by lia.
  rewrite <- w_sraw. apply bv_eq.
  assert (Hd : (0 <= w / 2 <= w)%Z) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite (u_sraw_small (Z_to_bv 64 w) (Z_to_bv 64 1) 1).
  - rewrite !u_Z2bv by lia. reflexivity.
  - rewrite u_Z2bv by lia. reflexivity.
  - rewrite u_Z2bv by lia. lia.
Qed.

Section Rb2.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Context {fx : FPState}.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma rb_A1 : forall regs m (s pixs tab : Z) (v : pixv) (ret : word),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs v ->
    (pixs + 64 <= s - 208 \/ s <= pixs)%Z -> p_d v = 1%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
    getr regs 12 = Z_to_bv 64 tab ->
    exists regs',
      msteps SEGS (mkst regs (0xa6f20 : word) m rom) (mkst regs' (0xa7048 : word) (MRB_A m s v ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 208) /\ getr regs' 18 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 1
      /\ getr regs' 21 = Z_to_bv 64 tab
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s pixs tab v ret Hs Hs64 Hs16 Hp1 ALp PX DJ Hd SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    pose proof (PIX_rd_w SEGS _ _ _ PX) as RW. pose proof (PIX_rd_h SEGS _ _ _ PX) as RH.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as RD. rewrite Hd in RD.
    replace (0xa6f20 : word) with (Z_to_bv 64 0xa6f20) by (apply bv_eq; reflexivity).
    replace (0xa7048 : word) with (Z_to_bv 64 0xa7048) by (apply bv_eq; reflexivity).
    ex_entry regs [p_w v; p_h v] HR.
    assert (HK : know_ok SEGS (ex_env regs [p_w v; p_h v]) m
                   [KWr (SA (EVar 2) (-208)) 208;
                    KRange (EVar 2) 256 (2 ^ 64 - 1); KRange (EVar 10) 1 (2 ^ 64 - 65);
                    KAlign (EVar 2) 16; KAlign (EVar 10) 8;
                    KDisj (SA (EVar 10) 0) 64 (SA (EVar 2) (-208)) 208;
                    KWord (SA (EVar 10) 8) 4 (ELit 1); KWord (SA (EVar 10) 0) 4 (EVar 32); KWord (SA (EVar 10) 4) 4 (EVar 33)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 300%nat [0xa7048]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - unfold MRB_A, DIMB, FRB. subst ret. ex_mem2 regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_Ah : forall regs m (s : Z),
    (0x130000 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 208) ->
    exists regs',
      msteps SEGS (mkst regs (0xa7048 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa73b4 /\ getr regs' 10 = Z_to_bv 64 0x16370 /\ getr regs' 11 = Z_to_bv 64 0x16386
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 RH RG RV H2.
    replace (0xa7048 : word) with (Z_to_bv 64 0xa7048) by (apply bv_eq; reflexivity).
    replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
    ex_entry regs [s] HR.
    assert (HK : know_ok SEGS (ex_env regs [s]) m
                   [KRange (EVar 32) 0x130000 (2 ^ 64 - 1);
                    KWord (SA (EVar 32) (-112)) 4 (ELit 1);
                    KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x63740]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_A2 : forall regs m (s pixs h : Z) (v : pixv),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs v ->
    (pixs + 64 <= s - 208 \/ s <= pixs)%Z -> (2 <= h < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 136)) 16 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0xa7048 : word) m rom) (mkst regs' (0x70a54 : word) (MRB_A2 m s v) rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa70a0 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pixs h v Hs Hs64 Hp1 ALp PX DJ Hh SOK RH H2 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rdat.
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as RWPL. pose proof (PIX_rd_data SEGS _ _ _ PX) as RDAT.
    replace (0xa7048 : word) with (Z_to_bv 64 0xa7048) by (apply bv_eq; reflexivity).
    replace (0x70a54 : word) with (Z_to_bv 64 0x70a54) by (apply bv_eq; reflexivity).
    ex_entry regs [s; h; p_wpl v; p_data v] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; h; p_wpl v; p_data v]) m
                   [KWr (SA (EVar 32) (-136)) 16;
                    KRange (EVar 32) 256 (2 ^ 64 - 1); KRange (EVar 18) 1 (2 ^ 64 - 65); KRange (EVar 33) 2 (2 ^ 31 - 1);
                    KAlign (EVar 18) 8;
                    KDisj (SA (EVar 18) 0) 64 (SA (EVar 32) (-136)) 16;
                    KWord (SA (EVar 32) (-112)) 4 (EVar 33);
                    KWord (SA (EVar 18) 16) 4 (EVar 34); KWord (SA (EVar 18) 56) 8 (EVar 35)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 200%nat [0x70a54]%Z (SCR [true] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - unfold MRB_A2. ex_mem2 regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_B : forall regs m (s w h : Z),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 208) ->
    exists regs',
      msteps SEGS (mkst regs (0xa70a0 : word) m rom) (mkst regs' (0x6da3c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa70c8 /\ getr regs' 10 = Z_to_bv 64 (w / 2) /\ getr regs' 11 = Z_to_bv 64 (h / 2)
      /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s w h Hs Hs64 Hw Hh RW RH H2.
    replace (0xa70a0 : word) with (Z_to_bv 64 0xa70a0) by (apply bv_eq; reflexivity).
    replace (0x6da3c : word) with (Z_to_bv 64 0x6da3c) by (apply bv_eq; reflexivity).
    ex_entry regs [s; w; h] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; w; h]) m
                   [KRange (EVar 32) 256 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1);
                    KWord (SA (EVar 32) (-108)) 4 (EVar 33); KWord (SA (EVar 32) (-112)) 4 (EVar 34)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x6da3c]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'); try (apply rb_half; lia). ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_Cn : forall regs m (s : Z),
    (0x130000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 120)) 8 = true ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa70c8 : word) m rom)
                  (mkst regs' (0x63740 : word) (wbytes m (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa73b4 /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x16386
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK RG RV H2 H10.
    replace (0xa70c8 : word) with (Z_to_bv 64 0xa70c8) by (apply bv_eq; reflexivity).
    replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
    ex_entry regs [s] HR.
    assert (HK : know_ok SEGS (ex_env regs [s]) m
                   [KWr (SA (EVar 32) (-120)) 8;
                    KRange (EVar 32) 0x130000 (2 ^ 64 - 1);
                    KDisj (SA (ELit 0) 0x126a70) 8 (SA (EVar 32) (-120)) 8;
                    KDisj (SA (ELit 0) 0x127c60) 4 (SA (EVar 32) (-120)) 8;
                    KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x63740]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_E : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, s0v); (s - 24, s1v); (s - 32, s2v); (s - 40, s3v); (s - 48, s4v); (s - 56, s5v);
              (s - 64, s6v); (s - 72, s7v); (s - 80, s8v); (s - 88, s9v); (s - 96, s10v); (s - 104, s11v)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 208) ->
    exists regs',
      msteps SEGS (mkst regs (0xa73b4 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 10
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v
      /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v Hs Hs64 Hret CE H2.
    cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    eexists. split.
    - stepj F_a73b4 D_a73b4.
      stepLD8 F_a7a68 D_a7a68 ret. stepLD8 F_a7a6c D_a7a6c s0v. stepLD8 F_a7a70 D_a7a70 s1v.
      stepLD8 F_a7a74 D_a7a74 s2v. stepLD8 F_a7a78 D_a7a78 s3v. stepLD8 F_a7a7c D_a7a7c s4v.
      stepLD8 F_a7a80 D_a7a80 s5v. stepLD8 F_a7a84 D_a7a84 s6v. stepLD8 F_a7a88 D_a7a88 s7v.
      stepLD8 F_a7a8c D_a7a8c s8v. stepLD8 F_a7a90 D_a7a90 s9v. stepLD8 F_a7a94 D_a7a94 s10v.
      stepLD8 F_a7a98 D_a7a98 s11v.
      zv F_a7a9c D_a7a9c (Z_to_bv 64 s).
      stepret F_a7aa0 D_a7aa0 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma rb_D : forall regs m (s pixd tab h wpls datas : Z) (vd : pixv),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd mod 8 = 0)%Z -> PIXat m pixd vd ->
    (pixd + 64 <= s - 208 \/ s <= pixd)%Z ->
    (1 <= tab < 2 ^ 64)%Z -> (2 <= h < 2 ^ 31)%Z ->
    (1 <= wpls < 2 ^ 24)%Z -> (1 <= p_wpl vd < 2 ^ 24)%Z -> (1 <= datas < 2 ^ 64)%Z -> (datas mod 4 = 0)%Z ->
    (1 <= p_data vd)%Z -> (p_data vd mod 4 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 208)) 72 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wpls)) ->
    rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
    rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 tab ->
    getr regs 20 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0xa70f0) m rom)
                  (mkst regs' (Z_to_bv 64 0xa71e8) (MRB_D m s pixd tab wpls (p_wpl vd) h datas) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 208)
      /\ getr regs' 10 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 11 = Z_to_bv 64 tab /\ getr regs' 14 = Z_to_bv 64 (4 * wpls)
      /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0 /\ getr regs' 17 = Z_to_bv 64 0 /\ getr regs' 5 = Z_to_bv 64 0
      /\ getr regs' 7 = Z_to_bv 64 (2 ^ 64 - 1 - tab) /\ getr regs' 18 = Z_to_bv 64 (p_data vd) /\ getr regs' 20 = Z_to_bv 64 2
      /\ getr regs' 22 = Z_to_bv 64 0xffffffffaaaaaaaa /\ getr regs' 24 = Z_to_bv 64 1 /\ getr regs' 28 = Z_to_bv 64 0
      /\ getr regs' 29 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 24; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s pixd tab h wpls datas vd Hs Hs64 Hp1 ALp PX DJ Htab Hh Hwpls Hwpl Hda1 ALda Hdd1 ALdd SOK RWS RDA RH H2 H19 H21 H20.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as RWPL. pose proof (PIX_rd_data SEGS _ _ _ PX) as RDAT.
    ex_entry regs [s; h; wpls; datas; p_wpl vd; p_data vd] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; h; wpls; datas; p_wpl vd; p_data vd]) m
                   [KWr (SA (EVar 32) (-208)) 72;
                    KRange (EVar 32) 256 (2 ^ 64 - 1); KRange (EVar 19) 1 (2 ^ 64 - 65); KRange (EVar 21) 1 (2 ^ 64 - 1);
                    KRange (EVar 33) 2 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 24 - 1); KRange (EVar 36) 1 (2 ^ 24 - 1);
                    KRange (EVar 35) 1 (2 ^ 64 - 1); KRange (EVar 37) 1 (2 ^ 64 - 1);
                    KAlign (EVar 19) 8; KAlign (EVar 35) 4; KAlign (EVar 37) 4;
                    KDisj (SA (EVar 19) 0) 64 (SA (EVar 32) (-208)) 72;
                    KWord (SA (EVar 32) (-136)) 8 (EVar 34); KWord (SA (EVar 32) (-128)) 8 (EVar 35);
                    KWord (SA (EVar 32) (-112)) 4 (EVar 33);
                    KWord (SA (EVar 19) 16) 4 (EVar 36); KWord (SA (EVar 19) 56) 8 (EVar 37)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    assert (XN : v_xor (Z_to_bv 64 tab) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - tab)).
    { unfold v_xor. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1)%Z. rewrite u_Z2bv by lia. f_equal.
      apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec.
      replace (2 ^ 64 - 1 - tab)%Z with ((Z.lnot tab) mod 2 ^ 64)%Z.
      2:{ unfold Z.lnot. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
      destruct (Z_lt_ge_dec n 64).
      - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
        replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia.
        apply Bool.xorb_true_r.
      - rewrite Z.mod_pow2_bits_high by lia.
        replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
        rewrite Bool.xorb_false_r.
        destruct (Z.eq_dec tab 0) as [->|NZ]; [apply Z.bits_0|].
        apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia. }
    destruct (wpls <? 2 * p_wpl vd)%Z eqn:Emin;
      [ pose proof (proj1 (Z.ltb_lt _ _) Emin) as Lmin | pose proof (proj1 (Z.ltb_ge _ _) Emin) as Lmin ].
    all: let d := lazymatch type of Emin with _ = true => constr:(true) | _ = false => constr:(false) end in
         lazymatch goal with |- context [mkst _ (Z_to_bv 64 ?b) (MRB_D _ _ _ _ _ _ _ _) _] =>
           ex_run 400%nat [b]%Z (SCR [d; false] [] []) HR HK R' HR' Hms end.
    all: lazymatch goal with
         | Hms : msteps _ _ _ |- exists _, _ =>
             exists R'; split;
             [ unfold MRB_D; rewrite Emin; cbv beta iota zeta;
               eapply ex_msteps_mem; [exact Hms|]; cbn [mem_denot s_log e_addr e_width e_val];
               repeat (apply ex_wbytes_eq;
                       [ | ex_addr_eq regs
                         | first [ solve [ex_bytes_eq regs]
                                 | (ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; f_equal; ex_ext;
                                    try (rewrite DitherLib.dl_addw by lia; f_equal; lia);
                                    try (rewrite w_sllw, ex_sllw_small by lia; f_equal; rewrite Z.pow_1_r; lia)) ] ]);
               reflexivity
             | repeat split; try (ex_agree HR HR'); try (ex_reg regs HR');
               try (rewrite ?ex_sx32, ?m_mul, ?zbv_mul, ?zbv_snez by lia; first [reflexivity | exact XN]) ]
         | |- _ => idtac
         end.
    all: try (rewrite !ex_sx32 by lia; rewrite DitherLib.dl_addw by lia; rewrite alu_slt; unfold v_slt, c_lts, bv_lts;
              rewrite !GrayLib.bv_signed_Zs by lia;
              let Lt := fresh "Lt" in assert (Lt : (h + -1 <? h)%Z = true) by (apply Z.ltb_lt; lia); rewrite Lt; reflexivity).
    all: try (rewrite !ex_sx32 by lia; rewrite w_sllw, ex_sllw_small by lia; rewrite Z.pow_1_r; ex_br).
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Ltac rbt_mw F D v := stepat F D v ltac:(gres; pin; rewrite zbv_mulw_small by lia; reflexivity).
  Ltac rbt_aw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
  Ltac rbt_sl F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; ring).
  Ltac rbt_sz F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
  Ltac rbt_ge F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; apply zbv_sltu_ge; lia).
  Ltac rbt_sn F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_slti0; lia).
  Ltac rbt_nz F D := stepat F D (Z_to_bv 64 1) ltac:(gres; pin; apply zbv_snez; lia).
  Ltac rbt_z F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
  Ltac rbt_not F D v := stepiv F D v ltac:(gres; pin; imm_norm; apply LeptRop.zbv_not; lia).

  (* [comment removed for export] *)
  Lemma rb_R : forall regs m (s k wpls wpld datas datad tab : Z),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= k)%Z -> (2 * k * wpls < 2 ^ 31)%Z -> (k * wpld < 2 ^ 31)%Z ->
    (1 <= wpls < 2 ^ 24)%Z -> (1 <= wpld < 2 ^ 24)%Z ->
    (1 <= datas)%Z -> (datas + 8 * wpls * k + 8 * wpls < 2 ^ 64)%Z ->
    (1 <= datad)%Z -> (datad + 4 * wpld * k + 4 * wpld < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wpls)) ->
    rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
    rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.min wpls (2 * wpld)))) ->
    rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (4 * wpls))) ->
    rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (datas + 4 * wpls))) ->
    getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 14 = Z_to_bv 64 (4 * wpls) ->
    getr regs 15 = Z_to_bv 64 (2 * k * wpls) -> getr regs 16 = Z_to_bv 64 (k * wpld) -> getr regs 17 = Z_to_bv 64 k ->
    getr regs 5 = Z_to_bv 64 (2 * k) -> getr regs 18 = Z_to_bv 64 datad -> getr regs 29 = Z_to_bv 64 1 ->
    getr regs 11 = Z_to_bv 64 tab ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0xa71e8) m rom) (mkst regs' (Z_to_bv 64 0xa72bc) m rom)
      /\ getr regs' 26 = Z_to_bv 64 (datas + 8 * wpls * k) /\ getr regs' 25 = Z_to_bv 64 (datas + 8 * wpls * k)
      /\ getr regs' 1 = Z_to_bv 64 (datad + 4 * wpld * k) /\ getr regs' 27 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 0
      /\ getr regs' 8 = Z_to_bv 64 (datad + 4 * wpld * k) /\ getr regs' 19 = Z_to_bv 64 (datad + 4 * wpld * k)
      /\ getr regs' 12 = Z_to_bv 64 (datas + 8 * wpls * k + 4 * wpls)
      /\ getr regs' 6 = Z_to_bv 64 (2 ^ 64 - 1 - (datas + 8 * wpls * k + 4 * wpls))
      /\ getr regs' 30 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 (Z.min wpls (2 * wpld))
      /\ regs_agree (fun r => In r [1; 6; 8; 12; 13; 19; 21; 23; 25; 26; 27; 30; 31]%list) regs regs'.
  Proof.
    intros regs m s k wpls wpld datas datad tab Hs Hs64 Hk Hm1 Hm2 Hws Hwd Hda1 Hdar Hdd1 Hddr
      R136 R128 R144 R176 R184 H2 H10 H14 H15 H16 H17 H5 H18 H29 H11.
    assert (Hkw : (0 <= k * wpls)%Z) by nia. assert (Hkd : (0 <= k * wpld)%Z) by nia.
    assert (Hkw2 : (0 <= 2 * k * wpls)%Z) by nia. assert (Hk1 : (k <= 2 * k * wpls)%Z) by nia.
    assert (Hk2 : (k <= k * wpld)%Z) by nia.
    assert (Hkw8 : (0 <= 8 * wpls * k)%Z) by nia. assert (Hkd4 : (0 <= 4 * wpld * k)%Z) by nia.
    replace (Z_to_bv 64 0xa71e8) with (0xa71e8 : word) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 0xa72bc) with (0xa72bc : word) by (apply bv_eq; reflexivity).
    eexists. split.
    - stepLD8 F_a71e8 D_a71e8 (Z_to_bv 64 wpls).
      zv F_a71ec D_a71ec (Z_to_bv 64 (2 * k * wpls)).
      rbt_mw F_a71f0 D_a71f0 (Z_to_bv 64 (2 * k * wpls)).
      stepb_ft F_a71f4 D_a71f4 ltac:(condZ).
      rbt_aw F_a71f8 D_a71f8 (Z_to_bv 64 (2 * k * wpls)).
      rbt_sl F_a71fc D_a71fc (Z_to_bv 64 (8 * wpls * k)).
      stepLD8 F_a7200 D_a7200 (Z_to_bv 64 datas).
      zv F_a7204 D_a7204 (Z_to_bv 64 (datas + 8 * wpls * k)).
      rbt_sz F_a7208 D_a7208.
      stepb_ft F_a720c D_a720c ltac:(condZ).
      stepLD8 F_a7210 D_a7210 (Z_to_bv 64 datas).
      rbt_ge F_a7214 D_a7214.
      rbt_sn F_a7218 D_a7218.
      rbt_z F_a721c D_a721c (Z_to_bv 64 0).
      rbt_z F_a7220 D_a7220 (Z_to_bv 64 1).
      stepb_ft F_a7224 D_a7224 ltac:(condZ).
      zv F_a7228 D_a7228 (Z_to_bv 64 (k * wpld)).
      rbt_mw F_a722c D_a722c (Z_to_bv 64 (k * wpld)).
      stepb_ft F_a7230 D_a7230 ltac:(condZ).
      rbt_nz F_a7234 D_a7234.
      rbt_aw F_a7238 D_a7238 (Z_to_bv 64 (k * wpld)).
      rbt_sl F_a723c D_a723c (Z_to_bv 64 (4 * wpld * k)).
      zv F_a7240 D_a7240 (Z_to_bv 64 (datad + 4 * wpld * k)).
      rbt_sz F_a7244 D_a7244.
      stepb_ft F_a7248 D_a7248 ltac:(condZ).
      rbt_ge F_a724c D_a724c.
      rbt_sn F_a7250 D_a7250.
      rbt_z F_a7254 D_a7254 (Z_to_bv 64 0).
      rbt_z F_a7258 D_a7258 (Z_to_bv 64 1).
      stepb_ft F_a725c D_a725c ltac:(condZ).
      stepLD8 F_a7260 D_a7260 (Z_to_bv 64 (Z.min wpls (2 * wpld))).
      stepb_ft F_a7264 D_a7264 ltac:(condZ).
      zv F_a7268 D_a7268 (Z_to_bv 64 0).
      rbt_sl F_a726c D_a726c (Z_to_bv 64 (4 * wpld * k)).
      rbt_sl F_a7270 D_a7270 (Z_to_bv 64 (8 * wpls * k)).
      stepLD8 F_a7274 D_a7274 (Z_to_bv 64 wpls).
      rbt_sn F_a7278 D_a7278.
      stepLD8 F_a727c D_a727c (Z_to_bv 64 (4 * wpls)).
      zv F_a7280 D_a7280 (Z_to_bv 64 (datas + 8 * wpls * k + 4 * wpls)).
      zv F_a7284 D_a7284 (Z_to_bv 64 (datas + 8 * wpls * k + 4 * wpls)).
      zv F_a7288 D_a7288 (Z_to_bv 64 (datad + 4 * wpld * k)).
      stepLD8 F_a728c D_a728c (Z_to_bv 64 datas).
      zv F_a7290 D_a7290 (Z_to_bv 64 (datas + 8 * wpls * k)).
      stepLD8 F_a7294 D_a7294 (Z_to_bv 64 (datas + 4 * wpls)).
      zv F_a7298 D_a7298 (Z_to_bv 64 (datas + 8 * wpls * k + 4 * wpls)).
      rbt_nz F_a729c D_a729c.
      rbt_ge F_a72a0 D_a72a0.
      rbt_z F_a72a4 D_a72a4 (Z_to_bv 64 0).
      rbt_z F_a72a8 D_a72a8 (Z_to_bv 64 1).
      rbt_z F_a72ac D_a72ac (Z_to_bv 64 1).
      rbt_not F_a72b0 D_a72b0 (Z_to_bv 64 (2 ^ 64 - 1 - (datas + 8 * wpls * k + 4 * wpls))).
      stepLD8 F_a72b4 D_a72b4 (Z_to_bv 64 (Z.min wpls (2 * wpld))).
      zv F_a72b8 D_a72b8 (Z_to_bv 64 (datad + 4 * wpld * k)).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma rbw_x2b : forall d, (0 <= d)%Z -> (0 <= Z.lxor d 2 <= d + 2)%Z.
  Proof.
    intros d Hd. rewrite rbl_lxor2_eq by lia. pose proof (Z.mod_pos_bound d 4 ltac:(lia)) as Hm.
    pose proof (Z.mod_le d 4 Hd ltac:(lia)) as Hle.
    rewrite rbl_lxor_small_2 by lia. destruct (Z.ltb_spec (d mod 4) 2); lia.
  Qed.

  Lemma rbw_srl56 : forall a : word, (0 <= bv_unsigned (alu64 ALU_SRL a (Z_to_bv 64 56)) < 256)%Z.
  Proof.
    intros a. rewrite alu_srl. unfold v_srl. pose proof (u64_range a) as Ha.
    change (bv_unsigned (Z_to_bv 64 56) mod 64)%Z with 56%Z. rewrite Z.shiftr_div_pow2 by lia.
    assert (B : (0 <= bv_unsigned a / 2 ^ 56 < 256)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite u_Z2bv by lia. exact B.
  Qed.

  Lemma rbw_srlw24 : forall a : word,
    (0 <= bv_unsigned (sext 64 (alu32 ALU_SRL (low32 a) (low32 (Z_to_bv 64 24)))) < 256)%Z.
  Proof.
    intros a. rewrite w_srlw. unfold v_srlw.
    change (bv_unsigned (Z_to_bv 64 24) mod 32)%Z with 24%Z. rewrite Z.shiftr_div_pow2 by lia.
    assert (Hw : (0 <= bv_wrap 32 (bv_unsigned a) < 2 ^ 32)%Z)
      by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32)%Z with (2 ^ 32)%Z; apply Z.mod_pos_bound; lia).
    assert (B : (0 <= bv_wrap 32 (bv_unsigned a) / 2 ^ 24 < 256)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite swrap32_small by lia. rewrite u_Z2bv by lia. exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_W : forall regs m (lines lines2 o d lined tab cnt v1 v2 : Z) (tb : Z -> byte),
    (1 <= lines)%Z -> (0 <= o)%Z -> (lines + o + 4 < 2 ^ 64)%Z -> ((lines + o) mod 4 = 0)%Z ->
    (1 <= lines2)%Z -> (lines2 + o + 4 < 2 ^ 64)%Z -> ((lines2 + o) mod 4 = 0)%Z ->
    (4096 <= lined)%Z -> (lined <= d)%Z -> (d + 4 < 2 ^ 64)%Z -> (d mod 2 = 0)%Z ->
    (0 <= tab)%Z -> (tab + 256 < 2 ^ 64)%Z -> (1 <= cnt < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (lines + o)) 4 = Some (Z_to_le_bytes 4 v1) ->
    rdn SEGS m (Z_to_bv 64 (lines2 + o)) 4 = Some (Z_to_le_bytes 4 v2) ->
    (forall i : Z, (0 <= i < 256)%Z -> rdn SEGS m (Z_to_bv 64 (tab + i)) 1 = Some [tb i]) ->
    store_ok SEGS m (Z_to_bv 64 (Z.lxor d 2)) 2 = true ->
    getr regs 25 = Z_to_bv 64 lines -> getr regs 26 = Z_to_bv 64 lines -> getr regs 21 = Z_to_bv 64 o ->
    getr regs 12 = Z_to_bv 64 lines2 -> getr regs 6 = Z_to_bv 64 (2 ^ 64 - 1 - lines2) ->
    getr regs 29 = Z_to_bv 64 1 -> getr regs 24 = Z_to_bv 64 1 -> getr regs 30 = Z_to_bv 64 1 ->
    getr regs 7 = Z_to_bv 64 (2 ^ 64 - 1 - tab) -> getr regs 22 = Z_to_bv 64 0xffffffffaaaaaaaa ->
    getr regs 19 = Z_to_bv 64 d -> getr regs 8 = Z_to_bv 64 d -> getr regs 1 = Z_to_bv 64 lined ->
    getr regs 27 = Z_to_bv 64 1 -> getr regs 28 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 2 ->
    getr regs 11 = Z_to_bv 64 tab -> getr regs 23 = Z_to_bv 64 cnt ->
    exists regs' (wv : word),
      msteps SEGS (mkst regs (Z_to_bv 64 0xa72bc) m rom)
                  (mkst regs' (Z_to_bv 64 0xa735c) (wbytes m (Z_to_bv 64 (Z.lxor d 2)) (word_to_le_bytes 2 wv)) rom)
      /\ getr regs' 19 = Z_to_bv 64 (d + 2) /\ getr regs' 8 = Z_to_bv 64 (d + 2) /\ getr regs' 21 = Z_to_bv 64 (o + 4)
      /\ getr regs' 23 = Z_to_bv 64 (cnt - 1)
      /\ regs_agree (fun r => In r [8; 9; 13; 19; 21; 23; 31]%list) regs regs'.
  Proof.
    intros regs m lines lines2 o d lined tab cnt v1 v2 tb Hl Ho Hlo ALl Hl2 Hl2o ALl2 Hld Hldd Hd4 ALd Ht Ht2 Hc RV1 RV2 RT SOK
      H25 H26 H21 H12 H6 H29 H24 H30 H7 H22 H19 H8 H1 H27 H28 H20 H11 H23.
    remember (2 ^ 64 - 1 - lines2)%Z as nl2 eqn:Enl2. remember (2 ^ 64 - 1 - tab)%Z as ntab eqn:Entab.
    assert (ALo1 : ((o + lines) mod 4 = 0)%Z) by (rewrite Z.add_comm; exact ALl).
    assert (ALo2 : ((o + lines2) mod 4 = 0)%Z) by (rewrite Z.add_comm; exact ALl2).
    set (z1 := extz true 4 (bytes_le_to_Z (Z_to_le_bytes 4 v1))). set (z2 := extz true 4 (bytes_le_to_Z (Z_to_le_bytes 4 v2))).
    pose (Wor := alu64 ALU_OR (Z_to_bv 64 z2) (Z_to_bv 64 z1)).
    pose (Y := alu64 ALU_AND (alu64 ALU_OR (mul_div M_MUL (Z_to_bv 64 2) Wor) Wor) (Z_to_bv 64 0xffffffffaaaaaaaa)).
    pose (X0 := alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 0x81000000000000) Y) (Z_to_bv 64 56)).
    pose (X1 := sext 64 (alu32 ALU_SRL (low32 (mul_div M_MUL (Z_to_bv 64 129) Y)) (low32 (Z_to_bv 64 24)))).
    pose (t0 := extz false 1 (bytes_le_to_Z [tb (bv_unsigned X0)])).
    pose (t1 := extz false 1 (bytes_le_to_Z [tb (bv_unsigned X1)])).
    ex_entry regs [z1; z2; t0; t1] HR.
    assert (HK : know_ok SEGS (ex_env regs [z1; z2; t0; t1]) m
                   [KRange (EVar 25) 1 (2 ^ 64 - 5); KRange (EVar 26) 1 (2 ^ 64 - 5); KRange (EVar 21) 0 (2 ^ 64 - 6);
                    KRange (EVar 12) 1 (2 ^ 64 - 5); KRange (EVar 11) 0 (2 ^ 64 - 257);
                    KRange (EVar 19) 1 (2 ^ 64 - 5); KRange (EVar 8) 1 (2 ^ 64 - 5); KRange (EVar 1) 1 (2 ^ 64 - 5);
                    KRange (EVar 23) 1 (2 ^ 31 - 1);
                    KAlign (EAlu ALU_ADD (EVar 21) (EVar 25)) 4; KRange (EAlu ALU_ADD (EVar 21) (EVar 25)) 1 (2 ^ 64 - 5);
                    KAlign (EAlu ALU_ADD (EVar 21) (EVar 26)) 4; KRange (EAlu ALU_ADD (EVar 21) (EVar 26)) 1 (2 ^ 64 - 5);
                    KAlign (EAlu ALU_ADD (EVar 21) (EVar 12)) 4; KRange (EAlu ALU_ADD (EVar 21) (EVar 12)) 1 (2 ^ 64 - 5);
                    KAlign (EVar 19) 2; KAlign (EVar 8) 2]%Z).
    { ex_know regs.
      all: let kd := (ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
                      rewrite ?H21, ?H25, ?H26, ?H12; apply ex_ptr_val) in
           match goal with
           | |- kentry_ok _ _ _ (KAlign (EAlu ALU_ADD (EVar 21) (EVar 12)) _) =>
               eapply ex_kalign with (b := (o + lines2)%Z); [kd | lia | lia | exact ALo2]
           | |- kentry_ok _ _ _ (KRange (EAlu ALU_ADD (EVar 21) (EVar 12)) _ _) =>
               eapply ex_krange with (b := (o + lines2)%Z); [kd | lia | lia]
           | |- kentry_ok _ _ _ (KAlign (EAlu ALU_ADD (EVar 21) _) _) =>
               eapply ex_kalign with (b := (o + lines)%Z); [kd | lia | lia | exact ALo1]
           | |- kentry_ok _ _ _ (KRange (EAlu ALU_ADD (EVar 21) _) _ _) =>
               eapply ex_krange with (b := (o + lines)%Z); [kd | lia | lia]
           | |- ?g => fail 1 "LEFT:" g
           end. }
    ex_run 300%nat [0xa735c]%Z
      (SCR [false; false; false; false; false; false; false; false; false; false; false; false] [EVar 32; EVar 33; EVar 35; EVar 34] [])
      HR HK R' HR' Hms.
    all: try (match goal with |- store_ok _ _ _ _ = true =>
                rewrite v_addi_0, alu_xor; unfold v_xor; rewrite !u_Z2bv by lia; exact SOK end).
    all: try (pose proof (rbw_x2b d ltac:(lia)) as X2;
              rewrite ?alu_xor; unfold v_xor; rewrite (u_Z2bv d), (u_Z2bv 2) by lia; rewrite ?u_Z2bv by lia; lia).
    all: try (exists (Z_to_le_bytes 4 v1); split;
              [match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (lines + o)%Z by lia end; exact RV1 | reflexivity]).
    all: try (exists (Z_to_le_bytes 4 v2); split;
              [match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (lines2 + o)%Z by lia end; exact RV2 | reflexivity]).
    all: try (match goal with |- exists bs, rdn _ _ (v_addi (alu64 ALU_ADD (Z_to_bv 64 ?tb0) ?X) 0) 1 = Some bs /\ _ =>
                assert (B : (0 <= bv_unsigned X < 256)%Z) by first [apply rbw_srl56 | apply rbw_srlw24];
                exists [tb (bv_unsigned X)]; split;
                [ rewrite v_addi_0; rewrite <- (zbv_self X) at 1; rewrite ex_ptr_val; apply RT; exact B
                | reflexivity ] end).
    all: try (match goal with |- context [alu64 ALU_ADD (Z_to_bv 64 ?tb0) ?X] =>
                assert (B : (0 <= bv_unsigned X < 256)%Z) by first [apply rbw_srl56 | apply rbw_srlw24];
                rewrite <- (zbv_self X), ex_ptr_val; rewrite ?u_Z2bv by lia; lia end).
    all: try (match goal with |- branch_taken BC_LTU _ ?X = false =>
                assert (B : (0 <= bv_unsigned X < 256)%Z) by first [apply rbw_srl56 | apply rbw_srlw24];
                solve [ex_br] end).
    all: try (match goal with |- branch_taken _ _ _ = false => solve [ex_br] end).
    1: { exists R'. eexists. split.
         - eapply ex_msteps_mem; [exact Hms |].
           cbn [mem_denot s_log e_addr e_width e_val].
           apply ex_wbytes_eq; [ reflexivity | | reflexivity ].
           assert (E19 : edenot (ex_env regs [z1; z2; t0; t1]) (EVar 19) = Z_to_bv 64 d) by ex_eden regs.
           unfold adenot. cbn [a_base a_off edenot]. cbn [edenot] in E19. rewrite E19.
           rewrite ?v_addi_0, ?alu_xor. unfold v_xor. rewrite (u_Z2bv d), (u_Z2bv 2) by lia. reflexivity.
         - repeat split; try (ex_reg regs HR'). all: try (ex_agree HR HR'). }
  Qed.

  Lemma rb_Wn : forall regs m (c : Z), (1 <= c < 2 ^ 63)%Z -> getr regs 23 = Z_to_bv 64 c ->
    msteps SEGS (mkst regs (Z_to_bv 64 0xa735c) m rom) (mkst regs (Z_to_bv 64 0xa72bc) m rom).
  Proof.
    intros regs m c Hc H23.
    replace (Z_to_bv 64 0xa735c) with (0xa735c : word) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 0xa72bc) with (0xa72bc : word) by (apply bv_eq; reflexivity).
    stepb_tk F_a735c D_a735c ltac:(condZ).
    apply mst_refl.
  Qed.
  Lemma rb_Wx : forall regs m, getr regs 23 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (Z_to_bv 64 0xa735c) m rom) (mkst regs (Z_to_bv 64 0xa7360) m rom).
  Proof.
    intros regs m H23.
    replace (Z_to_bv 64 0xa735c) with (0xa735c : word) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 0xa7360) with (0xa7360 : word) by (apply bv_eq; reflexivity).
    stepb_ft F_a735c D_a735c ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_Rn : forall regs m (s k h wpls wpld : Z),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= k)%Z -> (2 * k + 2 < h - 1)%Z -> (h < 2 ^ 31)%Z ->
    (1 <= wpls < 2 ^ 24)%Z -> (1 <= wpld < 2 ^ 24)%Z -> ((2 * k + 2) * wpls < 2 ^ 31)%Z -> ((k + 1) * wpld < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3fffffff)) ->
    rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 * wpls))) ->
    rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (h - 1))) ->
    getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 17 = Z_to_bv 64 k -> getr regs 5 = Z_to_bv 64 (2 * k) ->
    getr regs 16 = Z_to_bv 64 (k * wpld) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 15 = Z_to_bv 64 (2 * k * wpls) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0xa7360) m rom) (mkst regs' (Z_to_bv 64 0xa71e8) m rom)
      /\ getr regs' 17 = Z_to_bv 64 (k + 1) /\ getr regs' 5 = Z_to_bv 64 (2 * (k + 1))
      /\ getr regs' 16 = Z_to_bv 64 ((k + 1) * wpld) /\ getr regs' 15 = Z_to_bv 64 (2 * (k + 1) * wpls)
      /\ regs_agree (fun r => In r [5; 12; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s k h wpls wpld Hs Hs64 Hk Hkh Hh Hws Hwd Hm1 Hm2 R160 R168 R152 H2 H17 H5 H16 H10 H15.
    assert (Hkw : (0 <= k * wpls)%Z) by nia. assert (Hkd : (0 <= k * wpld)%Z) by nia.
    ex_entry regs [s; 2 * wpls; h - 1]%Z HR.
    lazymatch type of R160 with rdn _ _ _ _ = Some (word_to_le_bytes 8 (Z_to_bv 64 ?c)) =>
    assert (HK : know_ok SEGS (ex_env regs [s; 2 * wpls; h - 1]%Z) m
                   [KRange (EVar 32) 256 (2 ^ 64 - 1); KRange (EVar 33) 2 (2 ^ 25); KRange (EVar 34) 3 (2 ^ 31 - 2);
                    KRange (EVar 17) 0 (2 ^ 30 - 2); KRange (EVar 5) 0 (2 ^ 31 - 4);
                    KWord (SA (EVar 32) (-160)) 8 (ELit c); KWord (SA (EVar 32) (-168)) 8 (EVar 33);
                    KWord (SA (EVar 32) (-152)) 8 (EVar 34)]%Z) end.
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0xa71e8]%Z (SCR [true] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR');
          try (rewrite ?ex_ptr_val, ?alu_add, ?zbv_add, ?w_addw, ?v_addw_Z, ?v_addiw_Z; rewrite ?ex_sx32 by lia;
               rewrite ?sw32_small by lia; first [reflexivity | f_equal; lia | f_equal; nia]).
        ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_Rx : forall regs m (s k h wpls wpld pixd tab : Z)
      (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> (0 <= k)%Z -> (0 <= h - 1 <= 2 * k + 2)%Z -> (k < 2 ^ 29)%Z ->
    (1 <= wpls < 2 ^ 24)%Z -> (1 <= wpld < 2 ^ 24)%Z -> ((2 * k + 2) * wpls < 2 ^ 31)%Z -> ((k + 1) * wpld < 2 ^ 31)%Z ->
    (1 <= tab < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3fffffff)) ->
    rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 * wpls))) ->
    rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (h - 1))) ->
    rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tab)) ->
    rdn SEGS m (Z_to_bv 64 (s - 200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    cellsZ m [(s - 8, ret); (s - 16, s0v); (s - 24, s1v); (s - 32, s2v); (s - 40, s3v); (s - 48, s4v); (s - 56, s5v);
              (s - 64, s6v); (s - 72, s7v); (s - 80, s8v); (s - 88, s9v); (s - 96, s10v); (s - 104, s11v)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 17 = Z_to_bv 64 k -> getr regs 5 = Z_to_bv 64 (2 * k) ->
    getr regs 16 = Z_to_bv 64 (k * wpld) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 15 = Z_to_bv 64 (2 * k * wpls) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 0xa7360) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v
      /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun r => In r [1; 2; 5; 8; 9; 10; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s k h wpls wpld pixd tab ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
      Hs Hs64 Hret Hk Hkh Hk29 Hws Hwd Hm1 Hm2 Htab Hpd R160 R168 R152 R208 R200 CE H2 H17 H5 H16 H10 H15.
    cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    assert (Hkw : (0 <= k * wpls)%Z) by nia. assert (Hkd : (0 <= k * wpld)%Z) by nia.
    ex_entry regs [s; 2 * wpls; h - 1; tab; pixd]%Z HR.
    lazymatch type of R160 with rdn _ _ _ _ = Some (word_to_le_bytes 8 (Z_to_bv 64 ?c)) =>
    assert (HK : know_ok SEGS (ex_env regs [s; 2 * wpls; h - 1; tab; pixd]%Z) m
                   [KRange (EVar 32) 256 (2 ^ 64 - 1); KRange (EVar 33) 2 (2 ^ 25); KRange (EVar 35) 1 (2 ^ 64 - 1);
                    KRange (EVar 17) 0 (2 ^ 29 - 1); KRange (EVar 5) 0 (2 ^ 30 - 2);
                    KWord (SA (EVar 32) (-160)) 8 (ELit c); KWord (SA (EVar 32) (-168)) 8 (EVar 33);
                    KWord (SA (EVar 32) (-152)) 8 (EVar 34); KWord (SA (EVar 32) (-208)) 8 (EVar 35);
                    KWord (SA (EVar 32) (-200)) 8 (EVar 36)]%Z) end.
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0xa7a68]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { assert (HM : msteps SEGS (mkst regs (Z_to_bv 64 0xa7360) m rom) (mkst R' (Z_to_bv 64 0xa7a68) m rom))
        by (ex_mem regs Hms).
      assert (G2 : getr R' 2 = Z_to_bv 64 (s - 208)) by (ex_reg regs HR').
      assert (G10 : getr R' 10 = Z_to_bv 64 pixd) by (ex_reg regs HR').
      assert (AG : regs_agree (fun r => In r [1; 2; 5; 8; 9; 10; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list)
                     regs R') by (ex_agree HR HR').
      clear Hms HR' HR HK.
      eexists. split.
      - eapply msteps_trans; [exact HM |].
        replace (Z_to_bv 64 0xa7a68) with (0xa7a68 : word) by (apply bv_eq; reflexivity).
        stepLD8 F_a7a68 D_a7a68 ret. stepLD8 F_a7a6c D_a7a6c s0v. stepLD8 F_a7a70 D_a7a70 s1v.
        stepLD8 F_a7a74 D_a7a74 s2v. stepLD8 F_a7a78 D_a7a78 s3v. stepLD8 F_a7a7c D_a7a7c s4v.
        stepLD8 F_a7a80 D_a7a80 s5v. stepLD8 F_a7a84 D_a7a84 s6v. stepLD8 F_a7a88 D_a7a88 s7v.
        stepLD8 F_a7a8c D_a7a8c s8v. stepLD8 F_a7a90 D_a7a90 s9v. stepLD8 F_a7a94 D_a7a94 s10v.
        stepLD8 F_a7a98 D_a7a98 s11v.
        zv F_a7a9c D_a7a9c (Z_to_bv 64 s).
        stepret F_a7aa0 D_a7aa0 ret ltac:(bveq).
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity.
        repeat (apply regs_agree_upd; [ in_list | ]); exact AG. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

End Segs.

(* [comment removed for export] *)
Lemma rb_C : forall (rom : word -> option byte) (fr : bvmap 5 word) (cs : bv 32) regs m (s pixd pixs : Z) (vs : pixv),
  (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd + 64 < 2 ^ 64)%Z -> (pixd mod 8 = 0)%Z ->
  (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> pixd <> pixs ->
  PIXat m pixs vs -> p_xres vs = 0%Z -> p_yres vs = 0%Z ->
  (pixs + 64 <= s - 208 \/ s <= pixs)%Z -> (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z -> (pixd + 64 <= s - 208 \/ s <= pixd)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 120)) 8 = true -> store_ok SEGS m (Z_to_bv 64 (pixd + 24)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
  exists fr' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0xa70c8) m rom) (@mkst (mkFP fr' cs) regs' (Z_to_bv 64 0x6f748) (MRB_C m s pixd) rom)
    /\ fpv_read fr' FMT_S 10 = 0x3f000000%Z /\ fpv_read fr' FMT_S 11 = 0x3f000000%Z
    /\ (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r)
    /\ getr regs' 1 = Z_to_bv 64 0xa70f0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 19 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros rom fr cs regs m s pixd pixs vs Hs Hs64 Hd1 Hd64 ALd Hp1 ALp NE PX Hxr Hyr DJ1 DJ2 DJ3 SOK1 SOK2 H2 H10 H18.
  pose proof PX as (Hp0 & Hp64 & WF & BA).
  assert (RRES : rdn SEGS m (Z_to_bv 64 (pixs + 24)) 8 = Some (Z_to_le_bytes 8 0)).
  { assert (L64 : length (pix_bytes vs) = 64%nat) by (unfold pix_bytes; rewrite !length_app, !length_Z_to_le_bytes; reflexivity).
    pose proof (bytes_at_field SEGS m pixs (pix_bytes vs) 24 8 ltac:(lia) ltac:(rewrite L64; lia) ltac:(rewrite L64; lia) BA) as BF.
    unfold pix_bytes in BF. rewrite Hxr, Hyr in BF.
    change (pixs + 24)%Z with (pixs + Z.of_nat 24)%Z. rewrite BF. vm_compute. reflexivity. }
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m
                 [KWr (SA (EVar 32) (-120)) 8; KWr (SA (EVar 10) 24) 8;
                  KRange (EVar 32) 256 (2 ^ 64 - 1); KRange (EVar 10) 1 (2 ^ 64 - 65); KRange (EVar 18) 1 (2 ^ 64 - 65);
                  KAlign (EVar 10) 8; KAlign (EVar 18) 8;
                  KDisj (SA (EVar 18) 24) 8 (SA (EVar 32) (-120)) 8; KDisj (SA (EVar 18) 0) 64 (SA (EVar 10) 0) 64;
                  KWord (SA (EVar 18) 24) 8 (ELit 0)]%Z).
  { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
  exb_open HR HK ST.
  lazymatch goal with |- context [@mkst _ _ (Z_to_bv 64 ?b) (MRB_C _ _ _) _] =>
    exb_drive 300%nat [b]%Z (SCR [false] [] []) (@nil (nat * nat)) HK ST FZ end.
  exb_exit ST R' HR' Hlf Hms.
  eexists _, R'. split.
  { unfold MRB_C. ex_mem2 regs Hms. }
  repeat split.
  all: try (ex_agree HR HR').
  all: try (ex_reg regs HR').
  all: try (erewrite fr_read by reflexivity; rewrite fr_get; vm_compute; reflexivity).
  all: try (let r := fresh "r" in let Hr := fresh "Hr" in
            intros r Hr; rewrite fr_get; cbn [fs_list In] in Hr;
            repeat (destruct Hr as [Hr|Hr]);
            first [ solve [destruct Hr]
                  | match type of Hr with ?k = bv_unsigned r =>
                      let Er := fresh "Er" in assert (Er : r = Z_to_bv 5 k) by (apply bv_eq; rewrite <- Hr; reflexivity);
                      subst r; reflexivity end ]).
  all: match goal with |- ?g => fail 1 "LEFTC:" g end.
Qed.
End Rb2.
