(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoom14 GrayACELib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptStderr V14LeptBase V14LeptUb.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14CL7a.
Import V14CL7a.V14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptPixHdr V14LeptCmap2 V14LeptPixCopy V14LeptGrayD_iface V14LeptGrayA V14LeptGrayD V14_code_gmD_drv.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition PC_pixErodeGray3 : Z := 0x2724c.
Definition PC_pixDilateGray3 : Z := 0x28214.
Definition PC_pixOpenGray3 : Z := 0x291dc.
Definition PC_pixCloseGray3 : Z := 0x29454.
(* [comment removed for export] *)
Definition GM3_STACK : Z := 64 + G3H_STACK.

Section GrayDrv.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gray3_contract (entry RK RB : Z) : Prop :=
  forall C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GM3_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP14 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 3 -> getr regs 12 = Z_to_bv 64 1 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK <= kR)%Z -> (RB <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (d = 8%Z /\ cm = 0%Z /\ exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ pix_fresh C A A' m' pixd w h 8 data) ) ->
     aroom A' vm' (kR - RK) (bR - RB) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 entry) m al_rom) md) S.

(* [comment removed for export] *)
Definition gray3_null_contract (entry : Z) : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GM3_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 entry) m al_rom) md) S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FRd (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

Definition cells5 (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

Lemma cells5_FRd : forall m s ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells5 (FRd m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19).
Proof. intros m s ret regs Hs Hs64. unfold cells5, FRd. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Lemma cells5_out : forall m m' (s : Z) ret s0v s1v s2v s3v,
  (forall x : word, (s - 40 <= u x < s)%Z -> m' x = m x) -> (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells5 m s ret s0v s1v s2v s3v -> cells5 m' s ret s0v s1v s2v s3v.
Proof.
  intros m m' s ret s0v s1v s2v s3v OUT Hs Hs64 (R1 & R2 & R3 & R4 & R5). unfold cells5.
  repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]).
Qed.

Lemma cells5_frm : forall C s' m m' s ret s0v s1v s2v s3v, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 40)%Z -> (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells5 m s ret s0v s1v s2v s3v -> cells5 m' s ret s0v s1v s2v s3v.
Proof.
  intros C s' m m' s ret s0v s1v s2v s3v CK F Hlo Hs' Hs Hs64 (R1 & R2 & R3 & R4 & R5). unfold cells5.
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma cell_frm : forall C s' m m' (a : Z) bs, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some bs -> rdn SEGS m' (Z_to_bv 64 a) 8 = Some bs.
Proof. intros C s' m m' a bs CK F Hlo Ha Ha64 R. rewrite (FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). exact R. Qed.

Lemma cell_out : forall m m' (a : Z) bs, (forall x : word, (a <= u x < a + 8)%Z -> m' x = m x) -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some bs -> rdn SEGS m' (Z_to_bv 64 a) 8 = Some bs.
Proof.
  intros m m' a bs OUT Ha Ha64 R.
  etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | exact R].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition err_exit (regs regs' : bvmap 5 word) (s : Z) (ret : word) (msg proc : Z) : Prop :=
  getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 proc /\ getr regs' 12 = Z_to_bv 64 0
  /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
  /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19]%list) regs regs'.

Definition hd_null_spec (pc0 : word) (msg proc : Z) : Prop :=
  forall rom regs m (s : Z) (ret : word),
    (250000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs pc0 m rom) (mkst regs' (0x1554c : word) (FRd m s ret regs) rom) /\ err_exit regs regs' s ret msg proc.

Definition hd_depth_spec (pc0 : word) (msg proc : Z) : Prop :=
  forall rom regs m (s pixs : Z) (vs : pixv) (ret : word),
    (250000 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> p_d vs <> 8%Z -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs', msteps SEGS (mkst regs pc0 m rom) (mkst regs' (0x1554c : word) (FRd m s ret regs) rom) /\ err_exit regs regs' s ret msg proc.

Definition hd_cmap_spec (pc0 : word) (msg proc : Z) : Prop :=
  forall rom regs m (s pixs : Z) (vs : pixv) (ret : word),
    (250000 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> p_d vs = 8%Z -> p_cmap vs <> 0%Z -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs', msteps SEGS (mkst regs pc0 m rom) (mkst regs' (0x1554c : word) (FRd m s ret regs) rom) /\ err_exit regs regs' s ret msg proc.

(* [comment removed for export] *)
Definition hd_ok_spec (pc0 raB : word) (val : Z) : Prop :=
  forall rom regs m (s pixs : Z) (vs : pixv) (ret : word),
    (250000 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> p_d vs = 8%Z -> p_cmap vs = 0%Z -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 3 -> getr regs 12 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs pc0 m rom) (mkst regs' (Z_to_bv 64 PC_pixAddBorderGeneral) (FRd m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raB /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 8 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 8 /\ getr regs' 15 = Z_to_bv 64 val
      /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19]%list) regs regs'.

(* [comment removed for export] *)
Definition segB_spec (raB raC : word) (g3a : Z) : Prop :=
  forall rom regs m (s a0v : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a0v < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 a0v -> getr regs 9 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs raB m rom) (mkst regs' (Z_to_bv 64 g3a) (wbytes m (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 a0v))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raC /\ getr regs' 10 = Z_to_bv 64 a0v
      /\ regs_agree (fun r => In r [1]%list) regs regs'.

(* [comment removed for export] *)
Definition segC_spec (raC raD : word) : Prop :=
  forall rom regs m (s a0v : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a0v < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 a0v ->
    exists regs', msteps SEGS (mkst regs raC m rom) (mkst regs' (Z_to_bv 64 PC_pixRemoveBorderGeneral) (wbytes m (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 a0v))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raD /\ getr regs' 10 = Z_to_bv 64 a0v
      /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 8 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 8
      /\ regs_agree (fun r => In r [1; 11; 12; 13; 14]%list) regs regs'.

(* [comment removed for export] *)
Definition segC1_spec (raC raC2 : word) (val2 : Z) : Prop :=
  forall rom regs m (s a0v : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a0v < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 a0v ->
    exists regs', msteps SEGS (mkst regs raC m rom) (mkst regs' (Z_to_bv 64 PC_pixSetBorderVal) (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 a0v))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raC2 /\ getr regs' 10 = Z_to_bv 64 a0v /\ getr regs' 8 = Z_to_bv 64 a0v
      /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 8 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 8 /\ getr regs' 15 = Z_to_bv 64 val2
      /\ regs_agree (fun r => In r [1; 8; 11; 12; 13; 14; 15]%list) regs regs'.

Definition segC2_spec (raC2 raC3 : word) (g3b : Z) : Prop :=
  forall rom regs m (s : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs', msteps SEGS (mkst regs raC2 m rom) (mkst regs' (Z_to_bv 64 g3b) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raC3 /\ getr regs' 10 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.

Definition segC3_spec (raC3 raC4 : word) : Prop :=
  forall rom regs m (s a0v : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a0v < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 a0v ->
    exists regs', msteps SEGS (mkst regs raC3 m rom) (mkst regs' (0x15cf4 : word) (wbytes m (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 a0v))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raC4 /\ getr regs' 10 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.

Definition segC4_spec (raC4 raD : word) : Prop :=
  forall rom regs m (s a0v : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a0v < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 a0v) ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs', msteps SEGS (mkst regs raC4 m rom) (mkst regs' (Z_to_bv 64 PC_pixRemoveBorderGeneral) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raD /\ getr regs' 10 = Z_to_bv 64 a0v
      /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 8 /\ getr regs' 13 = Z_to_bv 64 2 /\ getr regs' 14 = Z_to_bv 64 8
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.

(* [comment removed for export] *)
Definition segD_spec (raD raE : word) : Prop :=
  forall rom regs m (s : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs', msteps SEGS (mkst regs raD m rom) (mkst regs' (0x15cf4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raE /\ getr regs' 10 = Z_to_bv 64 (s - 56) /\ getr regs' 8 = getr regs 10
      /\ regs_agree (fun r => In r [1; 8; 10]%list) regs regs'.

Definition segE_spec (raE raF : word) : Prop :=
  forall rom regs m (s : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs', msteps SEGS (mkst regs raE m rom) (mkst regs' (0x15cf4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = raF /\ getr regs' 10 = Z_to_bv 64 (s - 64)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.

(* [comment removed for export] *)
Definition segF_spec (raF : word) : Prop :=
  forall rom regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells5 m s ret s0v s1v s2v s3v -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs', msteps SEGS (mkst regs raF m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsDN.
Variable rom : word -> option byte.
  Lemma pixDestroy_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs', msteps SEGS (mkst regs (0x15cf4 : word) m rom)
      (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                  (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hpp Hpp64 ALpp Hret SOK Rpp H2 H1 H10. eexists. split.
    - zv F_15bf8 D_15bf8 (Z_to_bv 64 (s - 32)).
      stepST F_15bfc D_15bfc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15c00 D_15c00 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15c04 D_15c04 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_15c08 D_15c08 ltac:(condZ).
      guard8 F_15c0c D_15c0c ALpp. stepb_ft F_15c10 D_15c10 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_15c14 D_15c14 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Rpp) ltac:(apply W2Lib.lez8; lia).
      stepb_tk F_15c18 D_15c18 ltac:(condZ).
      stepLD8 F_15cc0 D_15cc0 ret. stepLD8 F_15cc4 D_15cc4 (getr regs 8). stepLD8 F_15cc8 D_15cc8 (getr regs 9).
      zv F_15ccc D_15ccc (Z_to_bv 64 s). stepret F_15cd0 D_15cd0 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsDN.

Lemma pixDestroy_null_W : forall C A m md regs (s pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> (forall x : word, ~ (s - 32 <= u x < s)%Z -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15cf4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp ret S CK HW H2 Hlo Hpp Hpphi ALpp H1 Hret H10 Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  destruct (pixDestroy_null al_rom regs m s pp ret ltac:(lia) Hpp ltac:(lia) ALpp Hret (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  apply (HK M1 r1 HW1).
  - apply cs_kept_intro; csr; try reflexivity.
  - exact PM1.
  - intros x Hx. subst M1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix_own (C : lctx) (A Ak : AS) (mk : word -> option byte) (p wd hd d dat : Z) : Prop :=
  (4096 <= p)%Z /\ (p + 64 <= alloc_top (c_vm C))%Z /\ (p mod 16 = 0)%Z /\
  (4096 <= dat)%Z /\ (dat + 4 * (wpl_of wd d * hd) <= alloc_top (c_vm C))%Z /\ (dat mod 16 = 0)%Z /\ p <> dat /\
  live A (Z_to_bv 64 p) = None /\ live A (Z_to_bv 64 dat) = None /\
  live (c_A0 C) (Z_to_bv 64 p) = None /\ live (c_A0 C) (Z_to_bv 64 dat) = None /\
  live Ak (Z_to_bv 64 p) = Some 64%Z /\ live Ak (Z_to_bv 64 dat) = Some (4 * (wpl_of wd d * hd))%Z /\
  PIXat mk p (hdv wd hd d 0 dat).

Lemma pix_fresh_own : forall C A A' m' p wd hd d dat, pix_fresh C A A' m' p wd hd d dat -> pix_own C A A' m' p wd hd d dat.
Proof. intros C A A' m' p wd hd d dat (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & _ & PX). unfold pix_own. tauto. Qed.

Lemma pix_fresh_leq : forall C A A' m' p wd hd d dat, pix_fresh C A A' m' p wd hd d dat ->
  forall q, q <> Z_to_bv 64 p -> q <> Z_to_bv 64 dat -> live A' q = live A q.
Proof. intros C A A' m' p wd hd d dat (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEQ & _). exact LEQ. Qed.

Lemma pix_own_fresh : forall C A A' m' p wd hd d dat, pix_own C A A' m' p wd hd d dat ->
  (forall q, q <> Z_to_bv 64 p -> q <> Z_to_bv 64 dat -> live A' q = live A q) -> pix_fresh C A A' m' p wd hd d dat.
Proof. intros C A A' m' p wd hd d dat (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & PX) LEQ. unfold pix_fresh. tauto. Qed.

Lemma sub_live_none : forall A A' q, sub_live A A' -> live A' q = None -> live A q = None.
Proof. intros A A' q SUB L. destruct (live A q) as [k|] eqn:E; [|reflexivity]. rewrite (SUB q k E) in L. discriminate. Qed.

(* [comment removed for export] *)
Lemma pix_own_base : forall C A0 A Ak mk p wd hd d dat, pix_own C A Ak mk p wd hd d dat -> sub_live A0 A -> pix_own C A0 Ak mk p wd hd d dat.
Proof.
  intros C A0 A Ak mk p wd hd d dat (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & PX) SUB. unfold pix_own.
  pose proof (sub_live_none A0 A _ SUB P8). pose proof (sub_live_none A0 A _ SUB P9). tauto.
Qed.

(* [comment removed for export] *)
Lemma pix_own_keep : forall C A Ak Ak' mk mk' p wd hd d dat, pix_own C A Ak mk p wd hd d dat ->
  live Ak' (Z_to_bv 64 p) = live Ak (Z_to_bv 64 p) -> live Ak' (Z_to_bv 64 dat) = live Ak (Z_to_bv 64 dat) ->
  LIVK Ak' mk mk' -> pix_own C A Ak' mk' p wd hd d dat.
Proof.
  intros C A Ak Ak' mk mk' p wd hd d dat (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & PX) E1 E2 LK.
  rewrite <- E1 in P12. rewrite <- E2 in P13. unfold pix_own. repeat (split; [assumption|]).
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  apply (PIXat_frame mk); [exact PX|]. intros x Hx. exact (LIVK_at Ak' mk mk' p 64 x LK P12 ltac:(lia) ltac:(lia) Hx).
Qed.

(* [comment removed for export] *)
Lemma pix_own_out : forall C A Ak mk p wd hd d dat (wa : word) ws, pix_own C A Ak mk p wd hd d dat ->
  (u wa + Z.of_nat (length ws) <= 2 ^ 64)%Z -> (alloc_top (c_vm C) <= u wa)%Z -> pix_own C A Ak (wbytes mk wa ws) p wd hd d dat.
Proof.
  intros C A Ak mk p wd hd d dat wa ws (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & PX) Hw Ha.
  unfold pix_own. repeat (split; [assumption|]). apply PIXat_out; [exact PX | exact Hw | lia].
Qed.

Lemma notin4 : forall (q a b c d : word), ~ In q [a; b; c; d] -> q <> a /\ q <> b /\ q <> c /\ q <> d.
Proof. intros q a b c d H. cbn [In] in H. repeat split; intros ->; apply H; tauto. Qed.

Lemma live_ne : forall (A : AS) (p q : word) k, live A p = None -> live A q = Some k -> p <> q.
Proof. intros A p q k L0 L1 E. rewrite E in L0. congruence. Qed.

Lemma raster_pos : forall w h d, hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (0 < 4 * (wpl_of w d * h))%Z.
Proof.
  intros w h d (DV & Hw2 & Hh2 & Hsz) Hw Hh. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwr.
  assert (1 * 1 <= wpl_of w d * h)%Z by (apply Z.mul_le_mono_nonneg; lia). lia.
Qed.

(* [comment removed for export] *)
Ltac pm_step SUB PM := eapply POSTM_trans; [eapply POSTM_sub; [exact SUB | eapply POSTM_mono; [|exact PM]; lia] |].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drv.
(* [comment removed for export] *)
Variables (pc0 : word) (raB raC raC2 raC3 raC4 raD raE raF : word) (val1 val2 : Z) (g3a g3b : Z) (msg_n msg_d msg_c proc : Z) (kn kd kc kp : Z).
Hypothesis S_null : hd_null_spec pc0 msg_n proc.
Hypothesis S_depth : hd_depth_spec pc0 msg_d proc.
Hypothesis S_cmap : hd_cmap_spec pc0 msg_c proc.
Hypothesis S_ok : hd_ok_spec pc0 raB val1.
Hypothesis S_B : segB_spec raB raC g3a.
Hypothesis S_C : segC_spec raC raD.
Hypothesis S_C1 : segC1_spec raC raC2 val2.
Hypothesis S_C2 : segC2_spec raC2 raC3 g3b.
Hypothesis S_C3 : segC3_spec raC3 raC4.
Hypothesis S_C4 : segC4_spec raC4 raD.
Hypothesis S_D : segD_spec raD raE.
Hypothesis S_E : segE_spec raE raF.
Hypothesis S_F : segF_spec raF.
Hypothesis RO_B : ret_ok raB.
Hypothesis RO_C : ret_ok raC.
Hypothesis RO_C2 : ret_ok raC2.
Hypothesis RO_C3 : ret_ok raC3.
Hypothesis RO_C4 : ret_ok raC4.
Hypothesis RO_D : ret_ok raD.
Hypothesis RO_E : ret_ok raE.
Hypothesis RO_F : ret_ok raF.
Hypothesis STR_n : str16 msg_n kn.
Hypothesis STR_d : str16 msg_d kd.
Hypothesis STR_c : str16 msg_c kc.
Hypothesis STR_p : str16 proc kp.
Hypothesis Hval1 : (val1 = 0 \/ val1 = 255)%Z.
Hypothesis Hval2 : (0 <= val2 < 2 ^ 64)%Z.
(* [comment removed for export] *)
Hypothesis ABG : pixAddBorderGeneral_contract.
Hypothesis RBG : pixRemoveBorderGeneral_contract.
Hypothesis RBGn : pixRemoveBorderGeneral_null_contract.
Hypothesis G3a : gray3h_contract g3a RK_pixcopy RB_pixcopy14.
Hypothesis G3an : gray3h_null_contract g3a.
Hypothesis G3b : gray3h_contract g3b RK_pixcopy RB_pixcopy14.
Hypothesis G3bn : gray3h_null_contract g3b.

(* [comment removed for export] *)
Abbreviation DR := ([3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list (bv 5)).

(* [comment removed for export] *)
Definition hk8_stmt (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h : Z) (ret : word) (S : TSet) (kR bR RK RB : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ pix_fresh C A A' m' pixd w h 8 data) ) ->
     aroom A' vm' (kR - RK) (bR - RB) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Definition mid_ok_stmt (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h : Z) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A1 m1 vm1 r1 (pixb datab wb hb : Z),
  wb = (w + 4 + 8)%Z -> hb = (h + 2 + 8)%Z ->
  W C A1 m1 (with_vmmaps vm1 md) -> POSTM C A s m m1 ->
  cells5 m1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  pix_fresh C A A1 m1 pixb wb hb 8 datab -> hdr_ok wb hb 8 ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
  getr r1 2 = Z_to_bv 64 (s - 64) -> getr r1 10 = Z_to_bv 64 pixb -> getr r1 9 = Z_to_bv 64 1 -> getr r1 19 = Z_to_bv 64 1 ->
  (forall x, In x DR -> getr r1 x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r1 raB m1 al_rom) (with_vmmaps vm1 md)) S.

Definition mid_null_stmt (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s : Z) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A1 m1 vm1 r1,
  W C A1 m1 (with_vmmaps vm1 md) -> (forall q, live A1 q = live A q) -> POSTM C A s m m1 ->
  cells5 m1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
  getr r1 2 = Z_to_bv 64 (s - 64) -> getr r1 10 = Z_to_bv 64 0 -> getr r1 9 = Z_to_bv 64 1 -> getr r1 19 = Z_to_bv 64 1 ->
  (forall x, In x DR -> getr r1 x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r1 raB m1 al_rom) (with_vmmaps vm1 md)) S.

Section Arm.
(* [comment removed for export] *)
Variables (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h : Z) (ret : word) (S : TSet) (kR bR RK RB : Z).
Hypothesis CK : Cok C.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + GM3_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hret : ret_ok ret.
Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
Hypothesis H4 : getr regs 4 = Z_to_bv 64 TP14.
Hypothesis HOK : hdr_ok w h 8.
Hypothesis Hw : (1 <= w)%Z.
Hypothesis Hh : (1 <= h)%Z.
Hypothesis Hrk : (RK <= kR)%Z.
Hypothesis Hrb : (RB <= bR)%Z.
Hypothesis HK8 : hk8_stmt C A m md regs s w h ret S kR bR RK RB.

(* [comment removed for export] *)
Definition res_ok (A3 : AS) (m3 : word -> option byte) (r3 : bvmap 5 word) (own : list word) : Prop :=
  (getr r3 10 = Z_to_bv 64 0 /\ forall q, ~ In q own -> live A3 q = live A q)
  \/ (exists pixd datad, getr r3 10 = Z_to_bv 64 pixd /\ pix_own C A A3 m3 pixd w h 8 datad /\
        ~ In (Z_to_bv 64 pixd) own /\ ~ In (Z_to_bv 64 datad) own /\
        forall q, ~ In q own -> q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad -> live A3 q = live A q).

(* [comment removed for export] *)
Lemma tail_ok : forall A3 m3 vm3 r3 (pixb datab pixbd databd wb hb : Z),
  W C A3 m3 (with_vmmaps vm3 md) -> POSTM C A s m m3 -> sub_live A A3 ->
  cells5 m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  rdn SEGS m3 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixb) ->
  rdn SEGS m3 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixbd) ->
  pix_own C A A3 m3 pixb wb hb 8 datab -> pix_own C A A3 m3 pixbd wb hb 8 databd ->
  (1 <= wb)%Z -> (1 <= hb)%Z -> hdr_ok wb hb 8 ->
  Z_to_bv 64 pixbd <> Z_to_bv 64 pixb -> Z_to_bv 64 pixbd <> Z_to_bv 64 datab ->
  Z_to_bv 64 databd <> Z_to_bv 64 pixb -> Z_to_bv 64 databd <> Z_to_bv 64 datab ->
  res_ok A3 m3 r3 [Z_to_bv 64 pixb; Z_to_bv 64 datab; Z_to_bv 64 pixbd; Z_to_bv 64 databd] ->
  aroom A3 vm3 (kR - RK) (bR - RB) ->
  getr r3 2 = Z_to_bv 64 (s - 64) -> (forall x, In x DR -> getr r3 x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r3 raD m3 al_rom) (with_vmmaps vm3 md)) S.
Proof.
  intros A3 m3 vm3 r3 pixb datab pixbd databd wb hb HW3 PM3 SUB3 CE3 Rb Rbd OWNb OWNbd Hwb Hhb HOKb N1 N2 N3 N4 RES Hrm3 Q2 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold GM3_STACK, G3H_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (raster_pos wb hb 8 HOKb Hwb Hhb) as Rpos.
  (* [comment removed for export] *)
  destruct (S_D al_rom r3 m3 s ltac:(lia) ltac:(lia) Q2) as (r4 & RUN4 & E2 & E1 & E10 & E8 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  pose proof OWNb as (Gb & TOPb & ALb & Gdb & TOPdb & ALdb & NEb & LAb & LAdb & L0b & L0db & L3b & L3db & PXb).
  pose proof OWNbd as (Gbd & TOPbd & ALbd & Gdbd & TOPdbd & ALdbd & NEbd & LAbd & LAdbd & L0bd & L0dbd & L3bd & L3dbd & PXbd).
  apply (pixDestroy_keep_W C A3 m3 (with_vmmaps vm3 md) r4 (s - 64) (s - 56) pixb (4 * (wpl_of wb 8 * hb)) (hdv wb hb 8 0 datab) raE S CK HW3 E2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) E1 RO_E
           ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) E10 Rb PXb eq_refl eq_refl eq_refl L3b L0b L3db L0db Rpos ltac:(cbn; lia)).
  intros A4 m4 vm4 r5 HW4 CS5 L4b L4db LEQ4 PM4 R4b OUT4 RT4. cbn [p_data hdv] in L4db, LEQ4. rewrite with_vmmaps_twice in HW4 |- *.
  assert (SUB4 : sub_live A A4).
  { intros q k Lq. rewrite LEQ4; [exact (SUB3 q k Lq) | intros ->; congruence | intros ->; congruence]. }
  assert (PM4' : POSTM C A s m m4).
  { eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C A A4); [exact SUB4|]. eapply POSTM_mono; [|exact PM4]. lia. }
  assert (CE4 : cells5 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_frm C (s - 56 + 8) m3 m4 s); [exact CK | exact (proj1 PM4) | lia | lia | lia | lia | exact CE3]. }
  assert (Rbd4 : rdn SEGS m4 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixbd)).
  { apply (cell_out m3 m4 (s - 64)); [intros x Hx; apply OUT4; lia | lia | lia | exact Rbd]. }
  assert (OWNbd4 : pix_own C A A4 m4 pixbd wb hb 8 databd).
  { apply (pix_own_keep C A A3 A4 m3 m4); [exact OWNbd | apply LEQ4; assumption | apply LEQ4; assumption | exact (proj2 PM4)]. }
  (* [comment removed for export] *)
  assert (F2 : getr r5 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_E al_rom r5 m4 s ltac:(lia) ltac:(lia) F2) as (r6 & RUN6 & G2 & G1 & G10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
  pose proof OWNbd4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L4bd & L4dbd & PXbd4).
  apply (pixDestroy_keep_W C A4 m4 (with_vmmaps vm4 md) r6 (s - 64) (s - 64) pixbd (4 * (wpl_of wb 8 * hb)) (hdv wb hb 8 0 databd) raF S CK HW4 G2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) G1 RO_F
           ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) G10 Rbd4 PXbd4 eq_refl eq_refl eq_refl L4bd L0bd L4dbd L0dbd Rpos ltac:(cbn; lia)).
  intros A5 m5 vm5 r7 HW5 CS7 L5bd L5dbd LEQ5 PM5 R5bd OUT5 RT5. cbn [p_data hdv] in L5dbd, LEQ5. rewrite with_vmmaps_twice in HW5 |- *.
  assert (SUB5 : sub_live A A5).
  { intros q k Lq. rewrite LEQ5; [exact (SUB4 q k Lq) | intros ->; congruence | intros ->; congruence]. }
  assert (PM5' : POSTM C A s m m5).
  { eapply POSTM_trans; [exact PM4'|]. apply (POSTM_sub C A A5); [exact SUB5|]. eapply POSTM_mono; [|exact PM5]. lia. }
  assert (CE5 : cells5 m5 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_frm C (s - 64 + 8) m4 m5 s); [exact CK | exact (proj1 PM5) | lia | lia | lia | lia | exact CE4]. }
  (* [comment removed for export] *)
  assert (I2 : getr r7 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_F al_rom r7 m5 s ret _ _ _ _ ltac:(lia) ltac:(lia) Hret CE5 I2) as (r8 & RUN8 & Y2 & Y1 & Y10 & Y8 & Y9 & Y18 & Y19 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN8 |].
  assert (Z10 : getr r8 10 = getr r3 10) by (rewrite Y10; csr; reflexivity).
  assert (LEQF : forall q, (forall q', ~ In q' [Z_to_bv 64 pixb; Z_to_bv 64 datab; Z_to_bv 64 pixbd; Z_to_bv 64 databd] -> q' = q -> live A3 q' = live A q') -> live A5 q = live A q).
  { intros q HQ.
    destruct (bv_eq_dec _ q (Z_to_bv 64 pixbd)) as [->|Nq3]; [rewrite L5bd, LAbd; reflexivity|].
    destruct (bv_eq_dec _ q (Z_to_bv 64 databd)) as [->|Nq4]; [rewrite L5dbd, LAdbd; reflexivity|].
    rewrite (LEQ5 q Nq3 Nq4).
    destruct (bv_eq_dec _ q (Z_to_bv 64 pixb)) as [->|Nq1]; [rewrite L4b, LAb; reflexivity|].
    destruct (bv_eq_dec _ q (Z_to_bv 64 datab)) as [->|Nq2]; [rewrite L4db, LAdb; reflexivity|].
    rewrite (LEQ4 q Nq1 Nq2). apply HQ; [| reflexivity]. cbn [In]. intros [X|[X|[X|[X|[]]]]]; congruence. }
  apply (HK8 A5 m5 vm5 r8 HW5).
  - apply cs_kept_intro; csr; try reflexivity.
  - exact PM5'.
  - destruct RES as [[R10 LEQ3] | (pixd & datad & R10 & OWNd & NId & NIdd & LEQ3)].
    + left. split; [rewrite Z10; exact R10|]. intros q. apply LEQF. intros q' NI _. exact (LEQ3 q' NI).
    + right. exists pixd, datad. split; [rewrite Z10; exact R10|].
      destruct (notin4 _ _ _ _ _ NId) as (D1 & D2 & D3 & D4). destruct (notin4 _ _ _ _ _ NIdd) as (D5 & D6 & D7 & D8).
      apply pix_own_fresh.
      * apply (pix_own_keep C A A4 A5 m4 m5); [| apply LEQ5; assumption | apply LEQ5; assumption | exact (proj2 PM5)].
        apply (pix_own_keep C A A3 A4 m3 m4); [exact OWNd | apply LEQ4; assumption | apply LEQ4; assumption | exact (proj2 PM4)].
      * intros q Nq1 Nq2. apply LEQF. intros q' NI ->. exact (LEQ3 q NI Nq1 Nq2).
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma tail_null : forall Ak mk vmk r,
  W C Ak mk (with_vmmaps vmk md) -> (forall q, live Ak q = live A q) -> POSTM C A s m mk ->
  cells5 mk s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ->
  rdn SEGS mk (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS mk (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 0) ->
  aroom Ak vmk (kR - RK) (bR - RB) ->
  getr r 2 = Z_to_bv 64 (s - 64) -> getr r 10 = Z_to_bv 64 0 -> (forall x, In x DR -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r raD mk al_rom) (with_vmmaps vmk md)) S.
Proof.
  intros Ak mk vmk r HWk LQ PMk CEk Rb Rbd Hrmk Q2 Q10 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold GM3_STACK, G3H_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (sub_live_eq A Ak LQ) as SUBk.
  destruct (S_D al_rom r mk s ltac:(lia) ltac:(lia) Q2) as (r4 & RUN4 & E2 & E1 & E10 & E8 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN4 |].
  apply (pixDestroy_null_W C Ak mk (with_vmmaps vmk md) r4 (s - 64) (s - 56) raE S CK HWk E2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) E1 RO_E E10 Rb).
  intros m4 r5 HW4 CS5 PM4 OUT4.
  assert (CE4 : cells5 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out mk m4 s); [intros x Hx; apply OUT4; lia | lia | lia | exact CEk]. }
  assert (Rbd4 : rdn SEGS m4 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 0)).
  { apply (cell_out mk m4 (s - 64)); [intros x Hx; apply OUT4; lia | lia | lia | exact Rbd]. }
  assert (F2 : getr r5 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_E al_rom r5 m4 s ltac:(lia) ltac:(lia) F2) as (r6 & RUN6 & G2 & G1 & G10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
  apply (pixDestroy_null_W C Ak m4 (with_vmmaps vmk md) r6 (s - 64) (s - 64) raF S CK HW4 G2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) G1 RO_F G10 Rbd4).
  intros m5 r7 HW5 CS7 PM5 OUT5.
  assert (CE5 : cells5 m5 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m4 m5 s); [intros x Hx; apply OUT5; lia | lia | lia | exact CE4]. }
  assert (I2 : getr r7 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_F al_rom r7 m5 s ret _ _ _ _ ltac:(lia) ltac:(lia) Hret CE5 I2) as (r8 & RUN8 & Y2 & Y1 & Y10 & Y8 & Y9 & Y18 & Y19 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN8 |].
  apply (HK8 Ak m5 vmk r8 HW5).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PMk|]. apply (POSTM_sub C A Ak); [exact SUBk|].
    eapply POSTM_trans; [eapply POSTM_mono; [|exact PM4]; lia | eapply POSTM_mono; [|exact PM5]; lia].
  - left. split; [| exact LQ]. rewrite Y10. csr. reflexivity.
  - exact Hrmk.
Qed.

(* [comment removed for export] *)
Section M3.
Hypothesis ERK : RK = RK_gm3.
Hypothesis ERB : RB = RB_gm3.

Lemma mid3_ok : mid_ok_stmt C A m md regs s w h ret S kR bR.
Proof.
  unfold mid_ok_stmt.
  intros A1 m1 vm1 r1 pixb datab wb hb Ewb Ehb HW1 PM1 CE1 FRb HOKb Hrm1 Q2 Q10 Q9 Q19 RR.
  assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z) by (clear; room_consts; lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold GM3_STACK, G3H_STACK, RBG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hwb : (1 <= wb)%Z) by lia. assert (Hhb : (1 <= hb)%Z) by lia.
  pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRb) as OWNb1. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRb) as LEQ1.
  pose proof (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRb) as SUB1.
  pose proof OWNb1 as (Gb & TOPb & ALb & Gdb & TOPdb & ALdb & NEb & LAb & LAdb & L0b & L0db & L1b & L1db & PXb1).
  (* [comment removed for export] *)
  destruct (S_B al_rom r1 m1 s pixb ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A1 m1 _ (s - 64) 64 CK HW1 ltac:(lia) ltac:(cbn; lia)) Q2 Q10 Q9 Q19)
    as (r2 & RUN2 & E2 & E1 & E10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes m1 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixb))).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (s - 56 <= u x < s - 48)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. apply (wbytes_out_Z _ (s - 56) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (PXb2 : PIXat M2 pixb (hdv wb hb 8 0 datab)) by (apply (PIXat_frame m1); [exact PXb1 | intros x Hx; apply OUT2; lia]).
  assert (CE2 : cells5 M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m1 M2 s); [intros x Hx; apply OUT2; lia | lia | lia | exact CE1]. }
  assert (Rb2 : rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixb)).
  { subst M2. rewrite <- (w2b_Z 8 pixb) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  rewrite <- (with_vmmaps_vmmaps vm1 md) in Hrm1.
  apply (G3a C A1 M2 (with_vmmaps vm1 md) r2 (s - 64)%Z pixb wb hb datab (CMAPV 0 0 0 0 0) raC S CK HW2 E2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold G3H_STACK, LSF; lia) ltac:(lia) E1 RO_C ltac:(csr; reflexivity) E10 PXb2 (conj Hwb (conj Hhb HOKb)) L1b L1db
           (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z Hrm1 ltac:(unfold RK_gm3 in ERK; lia) ltac:(unfold RB_gm3 in ERB; lia)).
  intros A2 m2 vm2 r3 pixbd databd HW3 CS3 PM3 R10 PT PXb3 Hrm2. rewrite with_vmmaps_twice in HW3 |- *.
  pose proof (pixt_new_fresh _ _ _ _ _ _ _ _ _ _ PT) as FRbd.
  pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRbd) as OWNbd2. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRbd) as LEQ2.
  pose proof (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRbd) as SUB2.
  pose proof OWNbd2 as (Gbd & TOPbd & ALbd & Gdbd & TOPdbd & ALdbd & NEbd & L1bd & L1dbd & L0bd & L0dbd & L2bd & L2dbd & PXbd2).
  (* [comment removed for export] *)
  assert (F2 : getr r3 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C al_rom r3 m2 s pixbd ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A2 m2 _ (s - 64) 64 CK HW3 ltac:(lia) ltac:(cbn; lia)) F2 R10)
    as (r4 & RUN4 & G2 & G1 & G10 & G11 & G12 & G13 & G14 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  set (M3 := wbytes m2 (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 pixbd))).
  assert (WP4 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A2 s m2 M3) by (subst M3; wp_win CK).
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (s - 64 <= u x < s - 56)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. apply (wbytes_out_Z _ (s - 64) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (PXbd4 : PIXat M3 pixbd (hdv wb hb 8 0 databd)) by (apply (PIXat_frame m2); [exact PXbd2 | intros x Hx; apply OUT4; lia]).
  assert (PXb4 : PIXat M3 pixb (hdv wb hb 8 0 datab)) by (apply (PIXat_frame m2); [exact PXb3 | intros x Hx; apply OUT4; lia]).
  rewrite <- (with_vmmaps_vmmaps vm2 md) in Hrm2.
  apply (RBG C A2 M3 (with_vmmaps vm2 md) r4 (s - 64)%Z pixbd wb hb 8%Z databd 4%Z 8%Z 2%Z 8%Z raD S CK HW4 G2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold RBG_STACK, LSF; lia) ltac:(lia) G1 RO_D ltac:(csr; reflexivity) G10 G11 G12 G13 G14 PXbd4 HOKb ltac:(right; reflexivity) L2bd L2dbd
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)
           (kR - RK_pixcopy - RK_pixcopy)%Z (bR - RB_pixcopy14 - RB_pixcopy14)%Z Hrm2 ltac:(unfold RK_gm3 in ERK; lia) ltac:(unfold RB_gm3 in ERB; lia)).
  intros A3 m3 vm3 r5 HW5 CS5 PM5 RES Hrm3. rewrite with_vmmaps_twice in HW5 |- *.
  (* [comment removed for export] *)
  assert (SUB3 : sub_live A2 A3).
  { destruct RES as [[_ LQ] | (pixd & datad & _ & _ & FRd)]; [exact (sub_live_eq A2 A3 LQ) | exact (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRd)]. }
  pose proof (SUB2 _ _ L1b) as L2b. pose proof (SUB2 _ _ L1db) as L2db.
  assert (LKb : forall mk, LIVK A2 M3 mk -> forall x : word, (pixb <= u x < pixb + 64)%Z -> mk x = M3 x)
    by (intros mk LK x Hx; exact (LIVK_at A2 M3 mk pixb 64 x LK L2b ltac:(lia) ltac:(lia) Hx)).
  assert (LKbd : forall mk, LIVK A2 M3 mk -> forall x : word, (pixbd <= u x < pixbd + 64)%Z -> mk x = M3 x)
    by (intros mk LK x Hx; exact (LIVK_at A2 M3 mk pixbd 64 x LK L2bd ltac:(lia) ltac:(lia) Hx)).
  apply (tail_ok A3 m3 vm3 r5 pixb datab pixbd databd wb hb HW5).
  - eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C A A1); [exact SUB1|].
    eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [eapply POSTM_mono; [|exact PM3]; lia|].
    apply (POSTM_sub C A1 A2); [exact SUB2|]. eapply POSTM_trans; [exact PM4 | eapply POSTM_mono; [|exact PM5]; lia].
  - exact (sub_live_trans _ _ _ SUB1 (sub_live_trans _ _ _ SUB2 SUB3)).
  - apply (cells5_frm C (s - 64) M3 m3 s); [exact CK | exact (proj1 PM5) | lia | lia | lia | lia |].
    apply (cells5_out m2 M3 s); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cells5_frm C (s - 64) M2 m2 s); [exact CK | exact (proj1 PM3) | lia | lia | lia | lia | exact CE2].
  - apply (cell_frm C (s - 64) M3 m3 (s - 56)); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
    apply (cell_out m2 M3 (s - 56)); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cell_frm C (s - 64) M2 m2 (s - 56)); [exact CK | exact (proj1 PM3) | lia | lia | lia | exact Rb2].
  - apply (cell_frm C (s - 64) M3 m3 (s - 64)); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
    subst M3. rewrite <- (w2b_Z 8 pixbd) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - unfold pix_own. repeat (split; [assumption|]). split; [exact (SUB3 _ _ L2b)|]. split; [exact (SUB3 _ _ L2db)|].
    apply (PIXat_frame M3); [exact PXb4 | exact (LKb m3 (proj2 PM5))].
  - unfold pix_own. do 7 (split; [assumption|]). split; [exact (sub_live_none A A1 _ SUB1 L1bd)|]. split; [exact (sub_live_none A A1 _ SUB1 L1dbd)|].
    do 2 (split; [assumption|]). split; [exact (SUB3 _ _ L2bd)|]. split; [exact (SUB3 _ _ L2dbd)|].
    apply (PIXat_frame M3); [exact PXbd4 | exact (LKbd m3 (proj2 PM5))].
  - exact Hwb.
  - exact Hhb.
  - exact HOKb.
  - exact (live_ne A1 _ _ _ L1bd L1b).
  - exact (live_ne A1 _ _ _ L1bd L1db).
  - exact (live_ne A1 _ _ _ L1dbd L1b).
  - exact (live_ne A1 _ _ _ L1dbd L1db).
  - destruct RES as [[R0 LQ] | (pixd & datad & R0 & HOKd & FRd)].
    + left. split; [exact R0|]. intros q NI. destruct (notin4 _ _ _ _ _ NI) as (D1 & D2 & D3 & D4).
      rewrite LQ. rewrite (LEQ2 q D3 D4). exact (LEQ1 q D1 D2).
    + right. exists pixd, datad. split; [exact R0|].
      replace (wb - 4 - 8)%Z with w in FRd by lia. replace (hb - 2 - 8)%Z with h in FRd by lia.
      pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRd) as OWNd. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRd) as LEQ3.
      pose proof OWNd as (_ & _ & _ & _ & _ & _ & _ & L2d & L2dd & _).
      split; [exact (pix_own_base C A A2 A3 m3 _ _ _ _ _ OWNd (sub_live_trans _ _ _ SUB1 SUB2))|].
      split; [cbn [In]; intros [X|[X|[X|[X|[]]]]]; rewrite <- X in L2d; congruence|].
      split; [cbn [In]; intros [X|[X|[X|[X|[]]]]]; rewrite <- X in L2dd; congruence|].
      intros q NI Nq1 Nq2. destruct (notin4 _ _ _ _ _ NI) as (D1 & D2 & D3 & D4).
      rewrite (LEQ3 q Nq1 Nq2). rewrite (LEQ2 q D3 D4). exact (LEQ1 q D1 D2).
  - unfold RK_gm3 in ERK. unfold RB_gm3 in ERB. rewrite ERK, ERB.
    eapply aroom_mono; [exact Hrm3 | lia | lia].
  - csr. reflexivity.
  - intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma mid3_null : mid_null_stmt C A m md regs s ret S kR bR.
Proof.
  unfold mid_null_stmt.
  intros A1 m1 vm1 r1 HW1 LQ PM1 CE1 Hrm1 Q2 Q10 Q9 Q19 RR.
  assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z) by (clear; room_consts; lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold GM3_STACK, G3H_STACK, RBG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (sub_live_eq A A1 LQ) as SUB1.
  destruct (S_B al_rom r1 m1 s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A1 m1 _ (s - 64) 64 CK HW1 ltac:(lia) ltac:(cbn; lia)) Q2 Q10 Q9 Q19)
    as (r2 & RUN2 & E2 & E1 & E10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes m1 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (s - 56 <= u x < s - 48)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. apply (wbytes_out_Z _ (s - 56) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (CE2 : cells5 M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m1 M2 s); [intros x Hx; apply OUT2; lia | lia | lia | exact CE1]. }
  assert (Rb2 : rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 0)).
  { subst M2. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  apply (G3an C A1 M2 (with_vmmaps vm1 md) r2 (s - 64)%Z raC S CK HW2 E2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold G3H_STACK, LSF; lia) ltac:(lia) E1 RO_C E10).
  intros m2 r3 HW3 CS3 PM3 R10.
  assert (F2 : getr r3 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C al_rom r3 m2 s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A1 m2 _ (s - 64) 64 CK HW3 ltac:(lia) ltac:(cbn; lia)) F2 R10)
    as (r4 & RUN4 & G2 & G1 & G10 & G11 & G12 & G13 & G14 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  set (M3 := wbytes m2 (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP4 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A1 s m2 M3) by (subst M3; wp_win CK).
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (s - 64 <= u x < s - 56)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. apply (wbytes_out_Z _ (s - 64) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  apply (RBGn C A1 M3 (with_vmmaps vm1 md) r4 (s - 64)%Z raD S CK HW4 G2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold RBG_STACK, LSF; lia) ltac:(lia) G1 RO_D G10).
  intros m3 r5 HW5 CS5 PM5 R0.
  apply (tail_null A1 m3 vm1 r5 HW5 LQ).
  - eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C A A1); [exact SUB1|].
    eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [eapply POSTM_mono; [|exact PM3]; lia|].
    eapply POSTM_trans; [exact PM4 | eapply POSTM_mono; [|exact PM5]; lia].
  - apply (cells5_frm C (s - 64) M3 m3 s); [exact CK | exact (proj1 PM5) | lia | lia | lia | lia |].
    apply (cells5_out m2 M3 s); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cells5_frm C (s - 64) M2 m2 s); [exact CK | exact (proj1 PM3) | lia | lia | lia | lia | exact CE2].
  - apply (cell_frm C (s - 64) M3 m3 (s - 56)); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
    apply (cell_out m2 M3 (s - 56)); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cell_frm C (s - 64) M2 m2 (s - 56)); [exact CK | exact (proj1 PM3) | lia | lia | lia | exact Rb2].
  - apply (cell_frm C (s - 64) M3 m3 (s - 64)); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
    subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - unfold RK_gm3 in ERK. unfold RB_gm3 in ERB. rewrite ERK, ERB. eapply aroom_mono; [exact Hrm1 | lia | lia].
  - csr. reflexivity.
  - exact R0.
  - intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
Qed.
End M3.

(* [comment removed for export] *)
Section M4.
Hypothesis ERK : RK = RK_gm4.
Hypothesis ERB : RB = RB_gm4.

Lemma mid4_ok : mid_ok_stmt C A m md regs s w h ret S kR bR.
Proof.
  unfold mid_ok_stmt.
  intros A1 m1 vm1 r1 pixb datab wb hb Ewb Ehb HW1 PM1 CE1 FRb HOKb Hrm1 Q2 Q10 Q9 Q19 RR.
  assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z) by (clear; room_consts; lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold GM3_STACK, G3H_STACK, RBG_STACK, SBV_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hwb : (1 <= wb)%Z) by lia. assert (Hhb : (1 <= hb)%Z) by lia.
  pose proof (raster_pos wb hb 8 HOKb Hwb Hhb) as Rpos.
  pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRb) as OWNb1. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRb) as LEQ1.
  pose proof (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRb) as SUB1.
  pose proof OWNb1 as (Gb & TOPb & ALb & Gdb & TOPdb & ALdb & NEb & LAb & LAdb & L0b & L0db & L1b & L1db & PXb1).
  (* [comment removed for export] *)
  destruct (S_B al_rom r1 m1 s pixb ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A1 m1 _ (s - 64) 64 CK HW1 ltac:(lia) ltac:(cbn; lia)) Q2 Q10 Q9 Q19)
    as (r2 & RUN2 & E2 & E1 & E10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes m1 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixb))).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (s - 56 <= u x < s - 48)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. apply (wbytes_out_Z _ (s - 56) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (PXb2 : PIXat M2 pixb (hdv wb hb 8 0 datab)) by (apply (PIXat_frame m1); [exact PXb1 | intros x Hx; apply OUT2; lia]).
  assert (CE2 : cells5 M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m1 M2 s); [intros x Hx; apply OUT2; lia | lia | lia | exact CE1]. }
  assert (Rb2 : rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixb)).
  { subst M2. rewrite <- (w2b_Z 8 pixb) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  rewrite <- (with_vmmaps_vmmaps vm1 md) in Hrm1.
  apply (G3a C A1 M2 (with_vmmaps vm1 md) r2 (s - 64)%Z pixb wb hb datab (CMAPV 0 0 0 0 0) raC S CK HW2 E2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold G3H_STACK, LSF; lia) ltac:(lia) E1 RO_C ltac:(csr; reflexivity) E10 PXb2 (conj Hwb (conj Hhb HOKb)) L1b L1db
           (kR - RK_pixcopy)%Z (bR - RB_pixcopy14)%Z Hrm1 ltac:(unfold RK_gm4 in ERK; lia) ltac:(unfold RB_gm4 in ERB; lia)).
  intros A2 m2 vm2 r3 pixt datat HW3 CS3 PM3 R10 PT PXb3 Hrm2. rewrite with_vmmaps_twice in HW3 |- *.
  pose proof (pixt_new_fresh _ _ _ _ _ _ _ _ _ _ PT) as FRt.
  pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRt) as OWNt2. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRt) as LEQ2.
  pose proof (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRt) as SUB2.
  pose proof OWNt2 as (Gt & TOPt & ALt & Gdt & TOPdt & ALdt & NEt & L1t & L1dt & L0t & L0dt & L2t & L2dt & PXt2).
  pose proof (SUB2 _ _ L1b) as L2b. pose proof (SUB2 _ _ L1db) as L2db.
  (* [comment removed for export] *)
  assert (F2 : getr r3 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C1 al_rom r3 m2 s pixt ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A2 m2 _ (s - 64) 64 CK HW3 ltac:(lia) ltac:(cbn; lia)) F2 R10)
    as (r4 & RUN4 & G2 & G1 & G10 & G8 & G11 & G12 & G13 & G14 & G15 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  set (M3 := wbytes m2 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixt))).
  assert (WP4 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A2 s m2 M3) by (subst M3; wp_win CK).
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. apply (wbytes_out_Z _ (s - 48) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (PXt4 : PIXat M3 pixt (hdv wb hb 8 0 datat)) by (apply (PIXat_frame m2); [exact PXt2 | intros x Hx; apply OUT4; lia]).
  assert (PXb4 : PIXat M3 pixb (hdv wb hb 8 0 datab)) by (apply (PIXat_frame m2); [exact PXb3 | intros x Hx; apply OUT4; lia]).
  assert (Rt4 : rdn SEGS M3 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixt)).
  { subst M3. rewrite <- (w2b_Z 8 pixt) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  apply (pixSetBorderVal_W C A1 A2 M3 (with_vmmaps vm2 md) r4 (s - 64)%Z pixt wb hb 0%Z datat 4%Z 8%Z 2%Z 8%Z val2 raC2 S CK HW4 SUB2 G2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold SBV_STACK, LSF; lia) ltac:(lia) G1 RO_C2 G10 G11 G12 G13 G14 G15
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hval2 PXt4 (conj Hwb (conj Hhb HOKb)) L2t L2dt L1dt L0dt ltac:(apply zbv_ne2; lia)).
  intros m3 r5 HW5 CS5 PM5 PXt5 FR5 _.
  (* [comment removed for export] *)
  assert (H2' : getr r5 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C2 al_rom r5 m3 s ltac:(lia) ltac:(lia) H2') as (r6 & RUN6 & I2 & I1 & I10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
  assert (I10' : getr r6 10 = Z_to_bv 64 pixt) by (rewrite I10; csr; reflexivity).
  rewrite <- (with_vmmaps_vmmaps vm2 md) in Hrm2.
  apply (G3b C A2 m3 (with_vmmaps vm2 md) r6 (s - 64)%Z pixt wb hb datat (CMAPV 0 0 0 0 0) raC3 S CK HW5 I2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold G3H_STACK, LSF; lia) ltac:(lia) I1 RO_C3 ltac:(csr; reflexivity) I10' PXt5 (conj Hwb (conj Hhb HOKb)) L2t L2dt
           (kR - RK_pixcopy - RK_pixcopy)%Z (bR - RB_pixcopy14 - RB_pixcopy14)%Z Hrm2 ltac:(unfold RK_gm4 in ERK; lia) ltac:(unfold RB_gm4 in ERB; lia)).
  intros A3 m4 vm3 r7 pixbd databd HW7 CS7 PM7 R10' PT' PXt7 Hrm3. rewrite with_vmmaps_twice in HW7 |- *.
  pose proof (pixt_new_fresh _ _ _ _ _ _ _ _ _ _ PT') as FRbd.
  pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRbd) as OWNbd3. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRbd) as LEQ3.
  pose proof (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRbd) as SUB3.
  pose proof OWNbd3 as (Gbd & TOPbd & ALbd & Gdbd & TOPdbd & ALdbd & NEbd & L2bd & L2dbd & L0bd & L0dbd & L3bd & L3dbd & PXbd3).
  pose proof (SUB3 _ _ L2b) as L3b. pose proof (SUB3 _ _ L2db) as L3db. pose proof (SUB3 _ _ L2t) as L3t. pose proof (SUB3 _ _ L2dt) as L3dt.
  (* [comment removed for export] *)
  assert (J2 : getr r7 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C3 al_rom r7 m4 s pixbd ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A3 m4 _ (s - 64) 64 CK HW7 ltac:(lia) ltac:(cbn; lia)) J2 R10')
    as (r8 & RUN8 & K2 & K1 & K10 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
  set (M5 := wbytes m4 (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 pixbd))).
  assert (WP8 : W C A3 M5 (with_vmmaps vm3 md) /\ POSTM C A3 s m4 M5) by (subst M5; wp_win CK).
  destruct WP8 as [HW8 PM8].
  assert (OUT8 : forall x : word, ~ (s - 64 <= u x < s - 56)%Z -> M5 x = m4 x).
  { intros x Hx. subst M5. apply (wbytes_out_Z _ (s - 64) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (PXt8 : PIXat M5 pixt (hdv wb hb 8 0 datat)) by (apply (PIXat_frame m4); [exact PXt7 | intros x Hx; apply OUT8; lia]).
  (* [comment removed for export] *)
  assert (FR5' : forall x : word, (s - 64 <= u x < s)%Z -> m3 x = M3 x) by (intros x Hx; apply FR5; lia).
  assert (CE8 : cells5 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m4 M5 s); [intros x Hx; apply OUT8; lia | lia | lia |].
    apply (cells5_frm C (s - 64) m3 m4 s); [exact CK | exact (proj1 PM7) | lia | lia | lia | lia |].
    apply (cells5_out M3 m3 s); [intros x Hx; apply FR5'; lia | lia | lia |].
    apply (cells5_out m2 M3 s); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cells5_frm C (s - 64) M2 m2 s); [exact CK | exact (proj1 PM3) | lia | lia | lia | lia | exact CE2]. }
  assert (Rb8 : rdn SEGS M5 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixb)).
  { apply (cell_out m4 M5 (s - 56)); [intros x Hx; apply OUT8; lia | lia | lia |].
    apply (cell_frm C (s - 64) m3 m4 (s - 56)); [exact CK | exact (proj1 PM7) | lia | lia | lia |].
    apply (cell_out M3 m3 (s - 56)); [intros x Hx; apply FR5'; lia | lia | lia |].
    apply (cell_out m2 M3 (s - 56)); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cell_frm C (s - 64) M2 m2 (s - 56)); [exact CK | exact (proj1 PM3) | lia | lia | lia | exact Rb2]. }
  assert (Rt8 : rdn SEGS M5 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixt)).
  { apply (cell_out m4 M5 (s - 48)); [intros x Hx; apply OUT8; lia | lia | lia |].
    apply (cell_frm C (s - 64) m3 m4 (s - 48)); [exact CK | exact (proj1 PM7) | lia | lia | lia |].
    apply (cell_out M3 m3 (s - 48)); [intros x Hx; apply FR5'; lia | lia | lia | exact Rt4]. }
  assert (Rbd8 : rdn SEGS M5 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixbd)).
  { subst M5. rewrite <- (w2b_Z 8 pixbd) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  assert (PXb8 : PIXat M5 pixb (hdv wb hb 8 0 datab)).
  { apply (PIXat_frame m4); [| intros x Hx; apply OUT8; lia].
    apply (PIXat_frame m3); [| intros x Hx; exact (LIVK_at A2 m3 m4 pixb 64 x (proj2 PM7) L2b ltac:(lia) ltac:(lia) Hx)].
    apply (PIXat_frame M3); [exact PXb4 | intros x Hx; exact (LIVK_at A1 M3 m3 pixb 64 x (proj2 PM5) L1b ltac:(lia) ltac:(lia) Hx)]. }
  assert (PXbd8 : PIXat M5 pixbd (hdv wb hb 8 0 databd)) by (apply (PIXat_frame m4); [exact PXbd3 | intros x Hx; apply OUT8; lia]).
  apply (pixDestroy_keep_W C A3 M5 (with_vmmaps vm3 md) r8 (s - 64) (s - 48) pixt (4 * (wpl_of wb 8 * hb)) (hdv wb hb 8 0 datat) raC4 S CK HW8 K2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) K1 RO_C4
           ltac:(csr; reflexivity) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) K10 Rt8 PXt8 eq_refl eq_refl eq_refl L3t L0t L3dt L0dt Rpos ltac:(cbn; lia)).
  intros A4 m5 vm4 r9 HW9 CS9 L4t L4dt LEQ4 PM9 R9t OUT9 RT9. cbn [p_data hdv] in L4dt, LEQ4. rewrite with_vmmaps_twice in HW9 |- *.
  assert (Nbt : Z_to_bv 64 pixb <> Z_to_bv 64 pixt) by (intros X; rewrite X in L1b; congruence).
  assert (Nbdt : Z_to_bv 64 pixb <> Z_to_bv 64 datat) by (intros X; rewrite X in L1b; congruence).
  assert (Ndbt : Z_to_bv 64 datab <> Z_to_bv 64 pixt) by (intros X; rewrite X in L1db; congruence).
  assert (Ndbdt : Z_to_bv 64 datab <> Z_to_bv 64 datat) by (intros X; rewrite X in L1db; congruence).
  assert (Nbdt' : Z_to_bv 64 pixbd <> Z_to_bv 64 pixt) by (exact (live_ne A2 _ _ _ L2bd L2t)).
  assert (Nbddt : Z_to_bv 64 pixbd <> Z_to_bv 64 datat) by (exact (live_ne A2 _ _ _ L2bd L2dt)).
  assert (Ndbdt' : Z_to_bv 64 databd <> Z_to_bv 64 pixt) by (exact (live_ne A2 _ _ _ L2dbd L2t)).
  assert (Ndbddt : Z_to_bv 64 databd <> Z_to_bv 64 datat) by (exact (live_ne A2 _ _ _ L2dbd L2dt)).
  pose proof (eq_trans (LEQ4 _ Nbt Nbdt) L3b) as L4b. pose proof (eq_trans (LEQ4 _ Ndbt Ndbdt) L3db) as L4db.
  pose proof (eq_trans (LEQ4 _ Nbdt' Nbddt) L3bd) as L4bd. pose proof (eq_trans (LEQ4 _ Ndbdt' Ndbddt) L3dbd) as L4dbd.
  pose proof (sub_live_none A A1 _ SUB1 L1t) as LAt. pose proof (sub_live_none A A1 _ SUB1 L1dt) as LAdt.
  assert (SUBA3 : sub_live A A3) by (exact (sub_live_trans _ _ _ SUB1 (sub_live_trans _ _ _ SUB2 SUB3))).
  assert (SUBA4 : sub_live A A4).
  { intros q k Lq. rewrite LEQ4; [exact (SUBA3 q k Lq) | intros ->; congruence | intros ->; congruence]. }
  (* [comment removed for export] *)
  assert (Rbd9 : rdn SEGS m5 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 pixbd)).
  { apply (cell_out M5 m5 (s - 64)); [intros x Hx; apply OUT9; lia | lia | lia | exact Rbd8]. }
  assert (Rb9 : rdn SEGS m5 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 pixb)).
  { apply (cell_out M5 m5 (s - 56)); [intros x Hx; apply OUT9; lia | lia | lia | exact Rb8]. }
  assert (CE9 : cells5 m5 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_frm C (s - 48 + 8) M5 m5 s); [exact CK | exact (proj1 PM9) | lia | lia | lia | lia | exact CE8]. }
  assert (PXb9 : PIXat m5 pixb (hdv wb hb 8 0 datab))
    by (apply (PIXat_frame M5); [exact PXb8 | intros x Hx; exact (LIVK_at A4 M5 m5 pixb 64 x (proj2 PM9) L4b ltac:(lia) ltac:(lia) Hx)]).
  assert (PXbd9 : PIXat m5 pixbd (hdv wb hb 8 0 databd))
    by (apply (PIXat_frame M5); [exact PXbd8 | intros x Hx; exact (LIVK_at A4 M5 m5 pixbd 64 x (proj2 PM9) L4bd ltac:(lia) ltac:(lia) Hx)]).
  assert (L2' : getr r9 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C4 al_rom r9 m5 s pixbd ltac:(lia) ltac:(lia) ltac:(lia) Rbd9 L2') as (r10 & RUN10 & N2 & N1 & N10 & N11 & N12 & N13 & N14 & AG10).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN10 |].
  assert (Hrm4 : aroom A4 (m_vmmaps (with_vmmaps vm4 md)) (kR - RK_pixcopy - RK_pixcopy - RK_pixcopy) (bR - RB_pixcopy14 - RB_pixcopy14 - RB_pixcopy14)).
  { rewrite with_vmmaps_vmmaps. rewrite with_vmmaps_vmmaps in RT9.
    pose proof (RT9 _ _ Hrm3 ltac:(unfold RK_gm4 in ERK; lia) ltac:(unfold RB_gm4 in ERB; lia)) as X. rewrite !Z.sub_0_r in X. exact X. }
  apply (RBG C A4 m5 (with_vmmaps vm4 md) r10 (s - 64)%Z pixbd wb hb 8%Z databd 4%Z 8%Z 2%Z 8%Z raD S CK HW9 N2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold RBG_STACK, LSF; lia) ltac:(lia) N1 RO_D ltac:(csr; reflexivity) N10 N11 N12 N13 N14 PXbd9 HOKb ltac:(right; reflexivity) L4bd L4dbd
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)
           _ _ Hrm4 ltac:(unfold RK_gm4 in ERK; lia) ltac:(unfold RB_gm4 in ERB; lia)).
  intros A5 m6 vm5 r11 HW11 CS11 PM11 RES Hrm5. rewrite with_vmmaps_twice in HW11 |- *.
  assert (SUB5 : sub_live A4 A5).
  { destruct RES as [[_ LQ] | (pixd & datad & _ & _ & FRd)]; [exact (sub_live_eq A4 A5 LQ) | exact (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRd)]. }
  (* [comment removed for export] *)
  assert (LEQA4 : forall q, ~ In q [Z_to_bv 64 pixb; Z_to_bv 64 datab; Z_to_bv 64 pixbd; Z_to_bv 64 databd] -> live A4 q = live A q).
  { intros q NI. destruct (notin4 _ _ _ _ _ NI) as (D1 & D2 & D3 & D4).
    destruct (bv_eq_dec _ q (Z_to_bv 64 pixt)) as [->|Nq1]; [rewrite L4t, LAt; reflexivity|].
    destruct (bv_eq_dec _ q (Z_to_bv 64 datat)) as [->|Nq2]; [rewrite L4dt, LAdt; reflexivity|].
    rewrite (LEQ4 q Nq1 Nq2). rewrite (LEQ3 q D3 D4). rewrite (LEQ2 q Nq1 Nq2). exact (LEQ1 q D1 D2). }
  apply (tail_ok A5 m6 vm5 r11 pixb datab pixbd databd wb hb HW11).
  - pose proof (sub_live_trans _ _ _ SUB1 SUB2) as SUBA2.
    pm_step (sub_live_refl A) PM1. pm_step SUB1 PM2. pm_step SUB1 PM3. pm_step SUBA2 PM4. pm_step SUB1 PM5. pm_step SUBA2 PM7.
    pm_step SUBA3 PM8. pm_step SUBA4 PM9. eapply POSTM_sub; [exact SUBA4 | eapply POSTM_mono; [|exact PM11]; lia].
  - exact (sub_live_trans _ _ _ SUBA4 SUB5).
  - apply (cells5_frm C (s - 64) m5 m6 s); [exact CK | exact (proj1 PM11) | lia | lia | lia | lia | exact CE9].
  - apply (cell_frm C (s - 64) m5 m6 (s - 56)); [exact CK | exact (proj1 PM11) | lia | lia | lia | exact Rb9].
  - apply (cell_frm C (s - 64) m5 m6 (s - 64)); [exact CK | exact (proj1 PM11) | lia | lia | lia | exact Rbd9].
  - unfold pix_own. repeat (split; [assumption|]). split; [exact (SUB5 _ _ L4b)|]. split; [exact (SUB5 _ _ L4db)|].
    apply (PIXat_frame m5); [exact PXb9 | intros x Hx; exact (LIVK_at A4 m5 m6 pixb 64 x (proj2 PM11) L4b ltac:(lia) ltac:(lia) Hx)].
  - unfold pix_own. do 7 (split; [assumption|]).
    split; [exact (sub_live_none A A2 _ (sub_live_trans _ _ _ SUB1 SUB2) L2bd)|]. split; [exact (sub_live_none A A2 _ (sub_live_trans _ _ _ SUB1 SUB2) L2dbd)|].
    do 2 (split; [assumption|]). split; [exact (SUB5 _ _ L4bd)|]. split; [exact (SUB5 _ _ L4dbd)|].
    apply (PIXat_frame m5); [exact PXbd9 | intros x Hx; exact (LIVK_at A4 m5 m6 pixbd 64 x (proj2 PM11) L4bd ltac:(lia) ltac:(lia) Hx)].
  - exact Hwb.
  - exact Hhb.
  - exact HOKb.
  - exact (live_ne A2 _ _ _ L2bd L2b).
  - exact (live_ne A2 _ _ _ L2bd L2db).
  - exact (live_ne A2 _ _ _ L2dbd L2b).
  - exact (live_ne A2 _ _ _ L2dbd L2db).
  - destruct RES as [[R0 LQ] | (pixd & datad & R0 & HOKd & FRd)].
    + left. split; [exact R0|]. intros q NI. rewrite LQ. exact (LEQA4 q NI).
    + right. exists pixd, datad. split; [exact R0|].
      replace (wb - 4 - 8)%Z with w in FRd by lia. replace (hb - 2 - 8)%Z with h in FRd by lia.
      pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRd) as OWNd. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRd) as LEQ5.
      pose proof OWNd as (_ & _ & _ & _ & _ & _ & _ & L4d & L4dd & _).
      split; [exact (pix_own_base C A A4 A5 m6 _ _ _ _ _ OWNd SUBA4)|].
      split; [cbn [In]; intros [X|[X|[X|[X|[]]]]]; rewrite <- X in L4d; congruence|].
      split; [cbn [In]; intros [X|[X|[X|[X|[]]]]]; rewrite <- X in L4dd; congruence|].
      intros q NI Nq1 Nq2. rewrite (LEQ5 q Nq1 Nq2). exact (LEQA4 q NI).
  - unfold RK_gm4 in ERK. unfold RB_gm4 in ERB. rewrite ERK, ERB.
    eapply aroom_mono; [exact Hrm5 | lia | lia].
  - csr. reflexivity.
  - intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma mid4_null : mid_null_stmt C A m md regs s ret S kR bR.
Proof.
  unfold mid_null_stmt.
  intros A1 m1 vm1 r1 HW1 LQ PM1 CE1 Hrm1 Q2 Q10 Q9 Q19 RR.
  assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z) by (clear; room_consts; lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold GM3_STACK, G3H_STACK, RBG_STACK, SBV_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (sub_live_eq A A1 LQ) as SUB1.
  destruct (S_B al_rom r1 m1 s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A1 m1 _ (s - 64) 64 CK HW1 ltac:(lia) ltac:(cbn; lia)) Q2 Q10 Q9 Q19)
    as (r2 & RUN2 & E2 & E1 & E10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes m1 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (s - 56 <= u x < s - 48)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. apply (wbytes_out_Z _ (s - 56) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (CE2 : cells5 M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m1 M2 s); [intros x Hx; apply OUT2; lia | lia | lia | exact CE1]. }
  assert (Rb2 : rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 0)).
  { subst M2. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  apply (G3an C A1 M2 (with_vmmaps vm1 md) r2 (s - 64)%Z raC S CK HW2 E2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold G3H_STACK, LSF; lia) ltac:(lia) E1 RO_C E10).
  intros m2 r3 HW3 CS3 PM3 R10.
  (* [comment removed for export] *)
  assert (F2 : getr r3 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C1 al_rom r3 m2 s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A1 m2 _ (s - 64) 64 CK HW3 ltac:(lia) ltac:(cbn; lia)) F2 R10)
    as (r4 & RUN4 & G2 & G1 & G10 & G8 & G11 & G12 & G13 & G14 & G15 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  set (M3 := wbytes m2 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP4 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A1 s m2 M3) by (subst M3; wp_win CK).
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. apply (wbytes_out_Z _ (s - 48) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (Rt4 : rdn SEGS M3 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 0)).
  { subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  apply (pixSetBorderVal_null_W C A1 M3 (with_vmmaps vm1 md) r4 (s - 64)%Z raC2 S CK HW4 G2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold SBV_STACK, LSF; lia) ltac:(lia) G1 RO_C2 G10).
  intros m3 r5 HW5 CS5 PM5 _.
  (* [comment removed for export] *)
  assert (H2' : getr r5 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C2 al_rom r5 m3 s ltac:(lia) ltac:(lia) H2') as (r6 & RUN6 & I2 & I1 & I10 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
  assert (I10' : getr r6 10 = Z_to_bv 64 0) by (rewrite I10; csr; reflexivity).
  apply (G3bn C A1 m3 (with_vmmaps vm1 md) r6 (s - 64)%Z raC3 S CK HW5 I2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold G3H_STACK, LSF; lia) ltac:(lia) I1 RO_C3 I10').
  intros m4 r7 HW7 CS7 PM7 R10'.
  (* [comment removed for export] *)
  assert (J2 : getr r7 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C3 al_rom r7 m4 s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A1 m4 _ (s - 64) 64 CK HW7 ltac:(lia) ltac:(cbn; lia)) J2 R10')
    as (r8 & RUN8 & K2 & K1 & K10 & AG8).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
  set (M5 := wbytes m4 (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (WP8 : W C A1 M5 (with_vmmaps vm1 md) /\ POSTM C A1 s m4 M5) by (subst M5; wp_win CK).
  destruct WP8 as [HW8 PM8].
  assert (OUT8 : forall x : word, ~ (s - 64 <= u x < s - 56)%Z -> M5 x = m4 x).
  { intros x Hx. subst M5. apply (wbytes_out_Z _ (s - 64) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
  assert (CE8 : cells5 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m4 M5 s); [intros x Hx; apply OUT8; lia | lia | lia |].
    apply (cells5_frm C (s - 64) m3 m4 s); [exact CK | exact (proj1 PM7) | lia | lia | lia | lia |].
    apply (cells5_frm C (s - 64) M3 m3 s); [exact CK | exact (proj1 PM5) | lia | lia | lia | lia |].
    apply (cells5_out m2 M3 s); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cells5_frm C (s - 64) M2 m2 s); [exact CK | exact (proj1 PM3) | lia | lia | lia | lia | exact CE2]. }
  assert (Rb8 : rdn SEGS M5 (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 0)).
  { apply (cell_out m4 M5 (s - 56)); [intros x Hx; apply OUT8; lia | lia | lia |].
    apply (cell_frm C (s - 64) m3 m4 (s - 56)); [exact CK | exact (proj1 PM7) | lia | lia | lia |].
    apply (cell_frm C (s - 64) M3 m3 (s - 56)); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
    apply (cell_out m2 M3 (s - 56)); [intros x Hx; apply OUT4; lia | lia | lia |].
    apply (cell_frm C (s - 64) M2 m2 (s - 56)); [exact CK | exact (proj1 PM3) | lia | lia | lia | exact Rb2]. }
  assert (Rt8 : rdn SEGS M5 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 0)).
  { apply (cell_out m4 M5 (s - 48)); [intros x Hx; apply OUT8; lia | lia | lia |].
    apply (cell_frm C (s - 64) m3 m4 (s - 48)); [exact CK | exact (proj1 PM7) | lia | lia | lia |].
    apply (cell_frm C (s - 64) M3 m3 (s - 48)); [exact CK | exact (proj1 PM5) | lia | lia | lia | exact Rt4]. }
  assert (Rbd8 : rdn SEGS M5 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 0)).
  { subst M5. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
  apply (pixDestroy_null_W C A1 M5 (with_vmmaps vm1 md) r8 (s - 64) (s - 48) raC4 S CK HW8 K2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) K1 RO_C4 K10 Rt8).
  intros m5 r9 HW9 CS9 PM9 OUT9.
  (* [comment removed for export] *)
  assert (Rbd9 : rdn SEGS m5 (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 0)).
  { apply (cell_out M5 m5 (s - 64)); [intros x Hx; apply OUT9; lia | lia | lia | exact Rbd8]. }
  assert (L2' : getr r9 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  destruct (S_C4 al_rom r9 m5 s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) Rbd9 L2') as (r10 & RUN10 & N2 & N1 & N10 & N11 & N12 & N13 & N14 & AG10).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN10 |].
  apply (RBGn C A1 m5 (with_vmmaps vm1 md) r10 (s - 64)%Z raD S CK HW9 N2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold RBG_STACK, LSF; lia) ltac:(lia) N1 RO_D N10).
  intros m6 r11 HW11 CS11 PM11 R0.
  apply (tail_null A1 m6 vm1 r11 HW11 LQ).
  - pm_step (sub_live_refl A) PM1. pm_step SUB1 PM2. pm_step SUB1 PM3. pm_step SUB1 PM4. pm_step SUB1 PM5. pm_step SUB1 PM7.
    pm_step SUB1 PM8. pm_step SUB1 PM9. eapply POSTM_sub; [exact SUB1 | eapply POSTM_mono; [|exact PM11]; lia].
  - apply (cells5_frm C (s - 64) m5 m6 s); [exact CK | exact (proj1 PM11) | lia | lia | lia | lia |].
    apply (cells5_out M5 m5 s); [intros x Hx; apply OUT9; lia | lia | lia | exact CE8].
  - apply (cell_frm C (s - 64) m5 m6 (s - 56)); [exact CK | exact (proj1 PM11) | lia | lia | lia |].
    apply (cell_out M5 m5 (s - 56)); [intros x Hx; apply OUT9; lia | lia | lia | exact Rb8].
  - apply (cell_frm C (s - 64) m5 m6 (s - 64)); [exact CK | exact (proj1 PM11) | lia | lia | lia | exact Rbd9].
  - unfold RK_gm4 in ERK. unfold RB_gm4 in ERB. rewrite ERK, ERB. eapply aroom_mono; [exact Hrm1 | lia | lia].
  - csr. reflexivity.
  - exact R0.
  - intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
Qed.
End M4.
End Arm.

(* [comment removed for export] *)
Lemma err_W : forall C A m md regs r1 (s msg kmsg : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GM3_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  str16 msg kmsg -> err_exit regs r1 s ret msg proc ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r1 (0x1554c : word) (FRd m s ret regs) al_rom) md) S.
Proof.
  intros C A m md regs r1 s msg kmsg ret S CK HW H2 Hs16 Hlo Hhi Hret STRm (Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & AG1) HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold GM3_STACK, G3H_STACK, LSF in *.
  assert (WP1 : W C A (FRd m s ret regs) md /\ POSTM C A s m (FRd m s ret regs)) by (unfold FRd; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRd m s ret regs) in *.
  apply (returnErrorPtr_W C A M1 md r1 s msg proc kmsg kp ret (Z_to_bv 64 0) S CK HW1 Q2 Hs16 ltac:(unfold LSF; lia) Hhi Q1 Hret Q10 Q11 Q12 STRm STR_p).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PM1|].
    eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

(* [comment removed for export] *)
Lemma drv_W : forall (entry RK RB : Z), pc0 = Z_to_bv 64 entry -> (RK_pixcopy <= RK)%Z -> (RB_pixcopy14 <= RB)%Z ->
  (forall C A m md regs s w h ret S kR bR, Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GM3_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
     getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 TP14 -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z -> (RK <= kR)%Z -> (RB <= bR)%Z ->
     hk8_stmt C A m md regs s w h ret S kR bR RK RB ->
     mid_ok_stmt C A m md regs s w h ret S kR bR /\ mid_null_stmt C A m md regs s ret S kR bR) ->
  gray3_contract entry RK RB.
Proof.
  intros entry RK RB Epc HRK HRB MID. unfold gray3_contract.
  intros C A m md regs s pixs w h d cm datas ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PX HOK Hw Hh Lp Ld kR bR Hrm Hrk Hrb HK.
  rewrite <- Epc.
  assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z) by (clear; room_consts; lia).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia. pose proof (al16_mod8 _ ALp16) as AL8p.
  assert (Hlo' : (c_top C - LSTK + (64 + (160 + 176 + 16 + 3376)) <= s)%Z) by (unfold GM3_STACK, G3H_STACK, LSF in Hlo; exact Hlo).
  pose proof (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  (* [comment removed for export] *)
  assert (HKE : forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
                  realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S).
  { intros m' regs' X1 X2 X3 X4. pose proof (HK A m' (m_vmmaps md) regs') as X. rewrite with_vmmaps_same in X.
    apply (X X1 X2 X3); [left; split; [exact X4 | reflexivity]|]. apply (aroom_mono A _ kR bR); [exact Hrm | lia | lia]. }
  destruct (Z.eq_dec d 8) as [->|Nd].
  2:{ destruct (S_depth al_rom regs m s pixs (hdv w h d cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) AL8p PX Nd ltac:(lia) SOK
                  (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10) as (r1 & RUN1 & EX).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
      exact (err_W C A m md regs r1 s msg_d kd ret S CK HW H2 Hs16 Hlo Hhi Hret STR_d EX HKE). }
  destruct (Z.eq_dec cm 0) as [->|Ncm].
  2:{ destruct (S_cmap al_rom regs m s pixs (hdv w h 8 cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) AL8p PX eq_refl Ncm ltac:(lia) SOK
                  (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10) as (r1 & RUN1 & EX).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
      exact (err_W C A m md regs r1 s msg_c kc ret S CK HW H2 Hs16 Hlo Hhi Hret STR_c EX HKE). }
  (* [comment removed for export] *)
  destruct (S_ok al_rom regs m s pixs (hdv w h 8 0 datas) ret ltac:(lia) ltac:(lia) ltac:(lia) AL8p PX eq_refl eq_refl ltac:(lia) SOK H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q9 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FRd m s ret regs) md /\ POSTM C A s m (FRd m s ret regs)) by (unfold FRd; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRd m s ret regs) in *.
  pose proof (cells5_FRd m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 64 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FRd. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PX1 : PIXat M1 pixs (hdv w h 8 0 datas)) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (HSZ : ((w + 4 + 8) * (h + 2 + 8) <= 400000000)%Z).
  { pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl8_ge w ltac:(lia)) as Hw4.
    pose proof (Z.mul_le_mono_nonneg_r w (4 * wpl_of w 8) h ltac:(lia) Hw4) as X.
    replace ((w + 4 + 8) * (h + 2 + 8))%Z with (w * h + 10 * w + 12 * h + 120)%Z by ring. lia. }
  assert (HV : (val1 = 0 \/ val1 = 2 ^ 8 - 1)%Z) by (change (2 ^ 8 - 1)%Z with 255%Z; exact Hval1).
  replace (Z_to_bv 64 TP14) with (Z_to_bv 64 0x44140) in H4 by reflexivity.
  apply (ABG C A M1 md r1 (s - 64)%Z pixs w h 8%Z datas 4%Z 8%Z 2%Z 8%Z val1 raB S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold ABG_STACK, LSF; lia) ltac:(lia) Q1 RO_B ltac:(csr; reflexivity) Q10 Q11 Q12 Q13 Q14 Q15 PX1 HOK Hw Hh ltac:(right; reflexivity) Lp Ld
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) HV HSZ kR bR Hrm ltac:(lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HW2 CS2 PM2 RES Hrm1.
  assert (HK8' : hk8_stmt C A m md regs s w h ret S kR bR RK RB).
  { intros A' m' vm' regs' X1 X2 X3 X4 X5. apply (HK A' m' vm' regs' X1 X2 X3); [| exact X5].
    destruct X4 as [L|R]; [left; exact L | right; split; [reflexivity | split; [reflexivity | exact R]]]. }
  destruct (MID C A m md regs s w h ret S kR bR CK Hs16 Hlo Hhi Hret H2 H4 HOK Hw Hh Hrk Hrb HK8') as [MOK MNULL].
  assert (PMa : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]).
  assert (CEa : cells5 m1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_frm C (s - 64) M1 m1 s); [exact CK | exact (proj1 PM2) | lia | lia | lia | lia | exact CE1]. }
  assert (RRa : forall x, In x DR -> getr r2 x = getr regs x).
  { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx. }
  destruct RES as [[R0 LQ] | (pixb & datab & R0 & HOKb & FRb)].
  - apply (MNULL A1 m1 vm1 r2 HW2 LQ PMa CEa Hrm1); [csr; reflexivity | exact R0 | csr; reflexivity | csr; reflexivity | exact RRa].
  - apply (MOK A1 m1 vm1 r2 pixb datab (w + 4 + 8)%Z (h + 2 + 8)%Z eq_refl eq_refl HW2 PMa CEa FRb HOKb Hrm1);
      [csr; reflexivity | exact R0 | csr; reflexivity | csr; reflexivity | exact RRa].
Qed.

(* [comment removed for export] *)
Lemma drv_null_W : forall (entry : Z), pc0 = Z_to_bv 64 entry -> gray3_null_contract entry.
Proof.
  intros entry Epc. unfold gray3_null_contract.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK. rewrite <- Epc.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + (64 + (160 + 176 + 16 + 3376)) <= s)%Z) by (unfold GM3_STACK, G3H_STACK, LSF in Hlo; exact Hlo).
  pose proof (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (S_null al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10) as (r1 & RUN1 & EX).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  exact (err_W C A m md regs r1 s msg_n kn ret S CK HW H2 Hs16 Hlo Hhi Hret STR_n EX HK).
Qed.
End Drv.
End GrayDrv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
