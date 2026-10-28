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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecX LeptExecB GrayLib DitherLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2_code_pixCopyResolution V2_code_pixGetRGBComponent.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptRgbsSegs.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Ltac condS :=
  idtac; pin; rewrite ?c_lts_Zs by lia;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | reflexivity ]; lia.

(* [comment removed for export] *)
Ltac ldcell F D a z :=
  stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z)
    ltac:(rdn_addr a; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.

(* [comment removed for export] *)
Ltac ldhyp F D a z R :=
  stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(rdn_addr a; exact R) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.

#[local] Ltac exB_sc_hook ::= first [ (rs_norm; ex_br) ].
Ltac rc_isc R SOK :=
  try (match goal with |- exists bs, rdn _ _ _ 1 = Some bs /\ _ =>
         eexists; split;
         [ rewrite ?ex_ptr_val; rewrite ?dl_xor3 by lia; rewrite ?zbv_addi, ?Z.add_0_r; apply R; lia
         | unfold extz; rewrite lez_u by (first [lia | cbn; lia]); rewrite u_Z2bv by lia; reflexivity ] end);
  try (match goal with |- store_ok _ _ _ 1 = true =>
         rewrite ?ex_ptr_val; rewrite ?dl_xor3 by lia; rewrite ?zbv_addi, ?Z.add_0_r; apply SOK; lia end).
Ltac rc_imem regs Hms AE :=
  eapply ex_msteps_mem; [exact Hms|]; cbn [mem_denot s_log e_addr e_width e_val];
  apply ex_wbytes_eq; [ reflexivity
                      | ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
                        rewrite ?ex_ptr_val; rewrite ?dl_xor3 by lia; rewrite ?zbv_addi, ?Z.add_0_r; apply AE; lia
                      | ex_bytes_eq regs ].

Section RgbcSegs.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Notation w4 x := (word_to_le_bytes 4 x) (only parsing).

(* [comment removed for export] *)
Definition FRM10 (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 (getr regs 1)))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)).
(* [comment removed for export] *)
Definition DIMc (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 84)) (w4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 88)) (w4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 84)) (w4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 88)) (w4 (Z_to_bv 64 h)).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma rc_A : forall (fx : FPState) regs m (s pixs comp w h : Z),
    (256 <= s < 2 ^ 63)%Z -> (s mod 16 = 0)%Z -> (4096 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z ->
    (0 <= comp <= 2)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
    rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 32) -> rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
    (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 comp ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b5fc) m rom) (@mkst fx regs' (Z_to_bv 64 0x192d0) (DIMc (FRM10 m s regs) s w h) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x1b758
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 8
      /\ getr regs' 18 = Z_to_bv 64 pixs /\ getr regs' 19 = Z_to_bv 64 comp
      /\ regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros fx regs m s pixs comp w h Hs ALs Hp1 Hp2 ALp Hc Hw Hh SOK Sw Sh Sd Scm APs H2 H10 H11.
    ex_entry regs [s; pixs; comp; w; h] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixs; comp; w; h]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 4096 (2 ^ 63); KRange (EVar 34) 0 2;
                    KRange (EVar 35) 1 (2 ^ 31 - 1); KRange (EVar 36) 1 (2 ^ 31 - 1);
                    KAlign (EVar 32) 16; KAlign (EVar 33) 8;
                    KWr (SA (EVar 32) (-96)) 96;
                    KWord (SA (EVar 33) 0) 4 (EVar 35); KWord (SA (EVar 33) 4) 4 (EVar 36); KWord (SA (EVar 33) 8) 4 (ELit 32);
                    KWord (SA (EVar 33) 48) 8 (ELit 0);
                    KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-96)) 96]).
    { ex_know regs. }
    ex_run 600%nat [0x192d0%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold DIMc, FRM10; ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try rs_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_B : forall (fx : FPState) regs m (pixd pixs : Z),
    (4096 <= pixd)%Z -> (pixd + 64 < 2 ^ 63)%Z -> (4096 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b758) m rom) (@mkst fx regs' (Z_to_bv 64 0x19bf4) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1b768 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ getr regs' 20 = Z_to_bv 64 pixd
      /\ regs_agree (fun x => In x [1; 10; 11; 20]%list) regs regs'.
  Proof.
    intros fx regs m pixd pixs Hd1 Hd2 Hp1 Hp2 H10 H18.
    ex_entry regs [pixd; pixs] HR.
    assert (HK : know_ok SEGS (ex_env regs [pixd; pixs]) m [KRange (EVar 32) 4096 (2 ^ 63); KRange (EVar 33) 4096 (2 ^ 63)]).
    { ex_know regs. }
    ex_run 50%nat [0x19bf4%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try rs_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_C : forall (fx : FPState) regs m (s pixs pixd comp h wpls wpld datas datad : Z),
    (256 <= s < 2 ^ 63)%Z -> (4096 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z ->
    (4096 <= pixd)%Z -> (pixd + 64 < 2 ^ 63)%Z -> (pixd mod 8 = 0)%Z ->
    (0 <= comp <= 2)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= wpls < 2 ^ 31)%Z -> (0 <= wpld < 2 ^ 31)%Z ->
    (4096 <= datas < 2 ^ 63)%Z -> (4096 <= datad < 2 ^ 63)%Z ->
    rdn SEGS m (Z_to_bv 64 (pixd + 16)) 4 = Some (Z_to_le_bytes 4 wpld) -> rdn SEGS m (Z_to_bv 64 (pixd + 56)) 8 = Some (Z_to_le_bytes 8 datad) ->
    rdn SEGS m (Z_to_bv 64 (pixs + 16)) 4 = Some (Z_to_le_bytes 4 wpls) -> rdn SEGS m (Z_to_bv 64 (pixs + 56)) 8 = Some (Z_to_le_bytes 8 datas) ->
    rdn SEGS m (Z_to_bv 64 (s - 88)) 4 = Some (Z_to_le_bytes 4 h) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 19 = Z_to_bv 64 comp ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b768) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b7e0) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 5 = Z_to_bv 64 3 /\ getr regs' 6 = Z_to_bv 64 pixd
      /\ getr regs' 8 = Z_to_bv 64 wpls /\ getr regs' 9 = Z_to_bv 64 wpld /\ getr regs' 10 = Z_to_bv 64 datad
      /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 0
      /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 1 /\ getr regs' 16 = Z_to_bv 64 comp
      /\ getr regs' 17 = Z_to_bv 64 (datas + comp) /\ getr regs' 18 = Z_to_bv 64 datas
      /\ regs_agree (fun x => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros fx regs m s pixs pixd comp h wpls wpld datas datad Hs Hp1 Hp2 ALp Hd1 Hd2 ALd Hc Hh Hws Hwd Hds Hdd Dwpl Ddat Swpl Sdat Rh
      H2 H18 H20 H19.
    ex_entry regs [s; pixs; pixd; comp; h; wpls; wpld; datas; datad] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixs; pixd; comp; h; wpls; wpld; datas; datad]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 4096 (2 ^ 63); KRange (EVar 34) 4096 (2 ^ 63); KRange (EVar 35) 0 2;
                    KRange (EVar 36) 1 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1);
                    KRange (EVar 39) 4096 (2 ^ 63); KRange (EVar 40) 4096 (2 ^ 63);
                    KAlign (EVar 33) 8; KAlign (EVar 34) 8;
                    KWord (SA (EVar 34) 16) 4 (EVar 38); KWord (SA (EVar 34) 56) 8 (EVar 40);
                    KWord (SA (EVar 33) 16) 4 (EVar 37); KWord (SA (EVar 33) 56) 8 (EVar 39);
                    KWord (SA (EVar 32) (-88)) 4 (EVar 36)]).
    { ex_know regs. }
    ex_run 300%nat [0x1b7e0%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try rs_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_OH : forall (fx : FPState) regs m (s i h w wpls wpld datas datad comp : Z),
    (256 <= s < 2 ^ 63)%Z -> (0 <= i < h)%Z -> (h <= 20000)%Z -> (1 <= w <= 20000)%Z -> (0 <= wpls)%Z -> (0 <= wpld)%Z ->
    (wpls * h <= 2 ^ 24)%Z -> (wpld * h <= 2 ^ 24)%Z ->
    (4096 <= datas)%Z -> (datas + 2 ^ 26 < 2 ^ 61)%Z -> (4096 <= datad)%Z -> (datad + 2 ^ 26 < 2 ^ 61)%Z -> (0 <= comp <= 2)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 84)) 4 = Some (Z_to_le_bytes 4 w) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 13 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (i * wpls) -> getr regs 12 = Z_to_bv 64 (i * wpld) ->
    getr regs 8 = Z_to_bv 64 wpls -> getr regs 9 = Z_to_bv 64 wpld -> getr regs 18 = Z_to_bv 64 datas -> getr regs 10 = Z_to_bv 64 datad ->
    getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 (datas + comp) -> getr regs 16 = Z_to_bv 64 comp ->
    getr regs 5 = Z_to_bv 64 3 ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b7e0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1b874) m rom)
      /\ getr regs' 7 = Z_to_bv 64 (datas + 4 * (i * wpls)) /\ getr regs' 19 = Z_to_bv 64 (datas + 4 * (i * wpls))
      /\ getr regs' 20 = Z_to_bv 64 (datas + 4 * (i * wpls) + comp) /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * (i * wpls) + comp)
      /\ getr regs' 22 = Z_to_bv 64 (datad + 4 * (i * wpld)) /\ getr regs' 28 = Z_to_bv 64 (datad + 4 * (i * wpld))
      /\ getr regs' 31 = Z_to_bv 64 (datad + 4 * (i * wpld)) /\ getr regs' 29 = Z_to_bv 64 0 /\ getr regs' 30 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [7; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros fx regs m s i h w wpls wpld datas datad comp Hs Hi Hh Hw Hws Hwd Hwsh Hwdh Hds1 Hds2 Hdd1 Hdd2 Hc Rw
      H2 H13 H11 H12 H8 H9 H18 H10 H14 H15 H17 H16 H5.
    assert (Hils : (0 <= i * wpls <= 2 ^ 24)%Z) by nia. assert (Hild : (0 <= i * wpld <= 2 ^ 24)%Z) by nia.
    assert (Hws' : (wpls <= 2 ^ 24)%Z) by nia. assert (Hwd' : (wpld <= 2 ^ 24)%Z) by nia.
    ex_entry regs [s; i; wpls; wpld; datas; datad; comp; w; (i * wpls)%Z; (i * wpld)%Z; (datas + comp)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; i; wpls; wpld; datas; datad; comp; w; (i * wpls)%Z; (i * wpld)%Z; (datas + comp)%Z]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 0 20000; KRange (EVar 34) 0 (2 ^ 24); KRange (EVar 35) 0 (2 ^ 24);
                    KRange (EVar 36) 4096 (2 ^ 61); KRange (EVar 37) 4096 (2 ^ 61); KRange (EVar 38) 0 2; KRange (EVar 39) 1 20000;
                    KRange (EVar 40) 0 (2 ^ 24); KRange (EVar 41) 0 (2 ^ 24);
                    KWord (SA (EVar 32) (-84)) 4 (EVar 39)]).
    { ex_know regs. }
    ex_run 200%nat [0x1b874%Z; 0x1b7cc%Z] (SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try rs_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_I : forall (last : bool) (fx : FPState) regs m (s lines lined comp j w v : Z),
    (256 <= s < 2 ^ 63)%Z -> (4096 <= lines)%Z -> (lines + 4 * w + 4 < 2 ^ 61)%Z -> (4096 <= lined)%Z -> (lined + w + 4 <= s - 96)%Z ->
    (0 <= comp <= 2)%Z -> (0 <= j < w)%Z -> (w <= 20000)%Z -> (0 <= v <= 255)%Z -> (if last then j + 1 = w else j + 1 < w)%Z ->
    rdn SEGS m (Z_to_bv 64 (xor3 (lines + comp + 4 * j))) 1 = Some (Z_to_le_bytes 1 v) ->
    store_ok SEGS m (Z_to_bv 64 (xor3 (lined + j))) 1 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 84)) 4 = Some (Z_to_le_bytes 4 w) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 lines -> getr regs 20 = Z_to_bv 64 (lines + comp) ->
    getr regs 21 = Z_to_bv 64 (lines + comp) -> getr regs 22 = Z_to_bv 64 (lined + j) -> getr regs 29 = Z_to_bv 64 (4 * j) ->
    getr regs 30 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 lined -> getr regs 7 = Z_to_bv 64 lines -> getr regs 28 = Z_to_bv 64 lined ->
    getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 3 ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b874) m rom)
                  (@mkst fx regs' (Z_to_bv 64 (if last then 0x1b7cc else 0x1b874))
                         (wbytes m (Z_to_bv 64 (xor3 (lined + j))) (word_to_le_bytes 1 (Z_to_bv 64 v))) rom)
      /\ getr regs' 22 = Z_to_bv 64 (lined + (j + 1)) /\ getr regs' 29 = Z_to_bv 64 (4 * (j + 1)) /\ getr regs' 30 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun x => In x [22; 23; 24; 29; 30]%list) regs regs'.
  Proof.
    intros last fx regs m s lines lined comp j w v Hs Hls Hls2 Hld Hld2 Hc Hj Hw Hv Hlast R SOK Rw
      H2 H19 H20 H21 H22 H29 H30 H31 H7 H28 H14 H15 H5.
    ex_entry regs [s; lines; lined; comp; j; w; v; (lines + comp)%Z; (lined + j)%Z; (4 * j)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; lines; lined; comp; j; w; v; (lines + comp)%Z; (lined + j)%Z; (4 * j)%Z]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 4096 (2 ^ 61); KRange (EVar 34) 4096 (2 ^ 63); KRange (EVar 35) 0 2;
                    KRange (EVar 36) 0 20000; KRange (EVar 37) 1 20000; KRange (EVar 38) 0 255; KRange (EVar 39) 4096 (2 ^ 62);
                    KRange (EVar 40) 4096 (2 ^ 63); KRange (EVar 41) 0 80000;
                    KWord (SA (EVar 32) (-84)) 4 (EVar 37)]).
    { ex_know regs. }
    assert (RD : forall a, a = (lines + comp + 4 * j)%Z -> rdn SEGS m (Z_to_bv 64 (bytea a)) 1 = Some (Z_to_le_bytes 1 v)) by (intros a ->; exact R).
    assert (SOK' : forall a, a = (lined + j)%Z -> store_ok SEGS m (Z_to_bv 64 (bytea a)) 1 = true) by (intros a ->; exact SOK).
    assert (AE : forall a, a = (lined + j)%Z -> Z_to_bv 64 (xor3 (lined + j)) = Z_to_bv 64 (bytea a)) by (intros a ->; reflexivity).
    assert (XB : (lined + j - 3 <= bytea (lined + j) <= lined + j + 3)%Z)
      by (unfold bytea; pose proof (Z.mod_pos_bound (lined + j) 4 ltac:(lia)); lia).
    destruct last.
    - ex_run 100%nat [0x1b874%Z; 0x1b7cc%Z] (SCR [false; false; false; false] [EVar 38] []) HR HK R' HR' Hms.
      all: rc_isc RD SOK'.
      all: try (rewrite ?dl_xor3 by lia; rewrite !u_Z2bv by lia; lia).
      exists R'. split; [rc_imem regs Hms AE|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try rs_fin.
    - ex_run 100%nat [0x1b874%Z; 0x1b7cc%Z] (SCR [false; false; false; true] [EVar 38] []) HR HK R' HR' Hms.
      all: rc_isc RD SOK'.
      all: try (rewrite ?dl_xor3 by lia; rewrite !u_Z2bv by lia; lia).
      exists R'. split; [rc_imem regs Hms AE|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try rs_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_ON : forall (last : bool) (fx : FPState) regs m (s i h wpls wpld : Z),
    (256 <= s < 2 ^ 63)%Z -> (0 <= i < h)%Z -> (h <= 20000)%Z -> (0 <= wpls)%Z -> (0 <= wpld)%Z ->
    (wpls * h <= 2 ^ 24)%Z -> (wpld * h <= 2 ^ 24)%Z -> (if last then i + 1 = h else i + 1 < h)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 88)) 4 = Some (Z_to_le_bytes 4 h) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 13 = Z_to_bv 64 i -> getr regs 8 = Z_to_bv 64 wpls -> getr regs 9 = Z_to_bv 64 wpld ->
    getr regs 11 = Z_to_bv 64 (i * wpls) -> getr regs 12 = Z_to_bv 64 (i * wpld) ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b7cc) m rom) (@mkst fx regs' (Z_to_bv 64 (if last then 0x1b8e4 else 0x1b7e0)) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 ((i + 1) * wpls) /\ getr regs' 12 = Z_to_bv 64 ((i + 1) * wpld)
      /\ regs_agree (fun x => In x [7; 11; 12; 13]%list) regs regs'.
  Proof.
    intros last fx regs m s i h wpls wpld Hs Hi Hh Hws Hwd Hwsh Hwdh Hlast Rh H2 H13 H8 H9 H11 H12.
    assert (Hils : (0 <= (i + 1) * wpls <= 2 ^ 24)%Z) by nia. assert (Hild : (0 <= (i + 1) * wpld <= 2 ^ 24)%Z) by nia.
    assert (Hils0 : (0 <= i * wpls <= 2 ^ 24)%Z) by nia. assert (Hild0 : (0 <= i * wpld <= 2 ^ 24)%Z) by nia.
    assert (Hws' : (wpls <= 2 ^ 24)%Z) by nia. assert (Hwd' : (wpld <= 2 ^ 24)%Z) by nia.
    ex_entry regs [s; i; h; wpls; wpld; (i * wpls)%Z; (i * wpld)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; i; h; wpls; wpld; (i * wpls)%Z; (i * wpld)%Z]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 0 20000; KRange (EVar 34) 1 20000; KRange (EVar 35) 0 (2 ^ 24);
                    KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24);
                    KWord (SA (EVar 32) (-88)) 4 (EVar 34)]).
    { ex_know regs. }
    destruct last.
    - ex_run 20%nat [0x1b7e0%Z; 0x1b8e4%Z] (SCR [true] [] []) HR HK R' HR' Hms.
      exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try rs_fin.
    - ex_run 20%nat [0x1b7e0%Z; 0x1b8e4%Z] (SCR [false] [] []) HR HK R' HR' Hms.
      exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try rs_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma rc_E : forall (fx : FPState) regs m (s pixd z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 : Z),
    (256 <= s < 2 ^ 63)%Z -> (4096 <= pixd < 2 ^ 63)%Z -> ret_ok (Z_to_bv 64 z1) ->
    (0 <= z1 < 2 ^ 64)%Z -> (0 <= z8 < 2 ^ 64)%Z -> (0 <= z9 < 2 ^ 64)%Z -> (0 <= z18 < 2 ^ 64)%Z -> (0 <= z19 < 2 ^ 64)%Z ->
    (0 <= z20 < 2 ^ 64)%Z -> (0 <= z21 < 2 ^ 64)%Z -> (0 <= z22 < 2 ^ 64)%Z -> (0 <= z23 < 2 ^ 64)%Z -> (0 <= z24 < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (Z_to_le_bytes 8 z1) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (Z_to_le_bytes 8 z8) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (Z_to_le_bytes 8 z9) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 z18) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 z19) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 z20) ->
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 z21) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 z22) ->
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 z23) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 z24) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 6 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b8e4) m rom) (@mkst fx regs' (Z_to_bv 64 z1) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = Z_to_bv 64 z1 /\ getr regs' 8 = Z_to_bv 64 z8 /\ getr regs' 9 = Z_to_bv 64 z9
      /\ getr regs' 18 = Z_to_bv 64 z18 /\ getr regs' 19 = Z_to_bv 64 z19 /\ getr regs' 20 = Z_to_bv 64 z20 /\ getr regs' 21 = Z_to_bv 64 z21
      /\ getr regs' 22 = Z_to_bv 64 z22 /\ getr regs' 23 = Z_to_bv 64 z23 /\ getr regs' 24 = Z_to_bv 64 z24
      /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s pixd z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 Hs Hp Hret B1 B8 B9 B18 B19 B20 B21 B22 B23 B24
      R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 H2 H6.
    ex_entry regs [s; pixd; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24]) m
                   [KRange (EVar 32) 256 (2 ^ 63);
                    KWord (SA (EVar 32) (-8)) 8 (EVar 34); KWord (SA (EVar 32) (-16)) 8 (EVar 35); KWord (SA (EVar 32) (-24)) 8 (EVar 36);
                    KWord (SA (EVar 32) (-32)) 8 (EVar 37); KWord (SA (EVar 32) (-40)) 8 (EVar 38); KWord (SA (EVar 32) (-48)) 8 (EVar 39);
                    KWord (SA (EVar 32) (-56)) 8 (EVar 40); KWord (SA (EVar 32) (-64)) 8 (EVar 41); KWord (SA (EVar 32) (-72)) 8 (EVar 42);
                    KWord (SA (EVar 32) (-80)) 8 (EVar 43)]).
    { ex_know regs. }
    ex_run 40%nat [0x1b94c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    assert (Hms2 : msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b8e4) m rom) (@mkst fx R' (Z_to_bv 64 0x1b94c) m rom))
      by (ex_mem2 regs Hms).
    eexists. split.
    - eapply msteps_trans; [exact Hms2|].
      stepret F_1b94c D_1b94c (Z_to_bv 64 z1) ltac:(idtac; ex_reg regs HR').
      apply mst_refl.
    - repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try rs_fin.
  Qed.

End Segs.
End RgbcSegs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
