(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec LeptExecX LeptExecB GrayLib DitherLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_pixGetExtremeValue.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gev_init (typ : Z) : Z := if (typ =? 4)%Z then 100000%Z else (-1)%Z.
(* [comment removed for export] *)
Definition gev_step (typ e v : Z) : Z := if ((typ =? 4)%Z && (v <? e)%Z) || ((typ =? 5)%Z && (e <? v)%Z) then v else e.
(* [comment removed for export] *)
Definition gev_ok (typ e : Z) : Prop := e = gev_init typ \/ (0 <= e <= 255)%Z.

Lemma gev_init_range : forall typ, (-1 <= gev_init typ <= 100000)%Z.
Proof. intros typ. unfold gev_init. destruct (typ =? 4)%Z; lia. Qed.

Lemma gev_ok_range : forall typ e, gev_ok typ e -> (-1 <= e <= 100000)%Z.
Proof. intros typ e [-> | H]; [apply gev_init_range | lia]. Qed.

(* [comment removed for export] *)
Lemma gev_step_byte : forall typ e v, (typ = 4 \/ typ = 5)%Z -> gev_ok typ e -> (0 <= v <= 255)%Z -> (0 <= gev_step typ e v <= 255)%Z.
Proof.
  intros typ e v Ht [-> | He] Hv; unfold gev_step, gev_init;
    destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb andb orb]; repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

Lemma gev_step_range : forall typ e v, (-1 <= e <= 100000)%Z -> (0 <= v <= 255)%Z -> (-1 <= gev_step typ e v <= 100000)%Z.
Proof. intros typ e v He Hv. unfold gev_step. destruct (_ || _)%bool; lia. Qed.

(* [comment removed for export] *)
Lemma v_slt_Zs : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  v_slt (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if (a <? b)%Z then 1 else 0).
Proof. intros a b Ha Hb. unfold v_slt, c_lts, bv_lts. rewrite !bv_signed_Zs by lia. destruct (a <? b)%Z; reflexivity. Qed.

Lemma v_and_bits : forall (p q : bool),
  v_and (Z_to_bv 64 (if p then 1 else 0)) (Z_to_bv 64 (if q then 1 else 0)) = Z_to_bv 64 (if p && q then 1 else 0).
Proof. intros [|] [|]; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma v_or_bits : forall (p q : bool),
  v_or (Z_to_bv 64 (if p then 1 else 0)) (Z_to_bv 64 (if q then 1 else 0)) = Z_to_bv 64 (if p || q then 1 else 0).
Proof. intros [|] [|]; apply bv_eq; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_seqz_m : forall typ k, (typ = 4 \/ typ = 5)%Z -> (k = 4 \/ k = 5)%Z ->
  v_sltu (Z_to_bv 64 (typ + - k)) (Z_to_bv 64 1) = Z_to_bv 64 (if (typ =? k)%Z then 1 else 0).
Proof. intros typ k [-> | ->] [-> | ->]; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma gv_and255 : forall x, (0 <= x < 256)%Z -> v_and (Z_to_bv 64 x) (Z_to_bv 64 255) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold v_and. rewrite !u_Z2bv by lia. change 255%Z with (Z.ones 8).
  rewrite Z.land_ones by lia. rewrite Z.mod_small by (change (2 ^ 8)%Z with 256%Z; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac gev_typ_hook :=
  match goal with
  | H : (4 <= ?t <= 5)%Z |- _ =>
      let E := fresh "E" in assert (E : t = 4%Z \/ t = 5%Z) by lia; destruct E as [E | E]; rewrite E; cond_compute
  end.
Ltac gev_typ_eq :=
  match goal with
  | H : (4 <= ?t <= 5)%Z |- context [gev_init ?t] =>
      let E := fresh "E" in assert (E : t = 4%Z \/ t = 5%Z) by lia; destruct E as [E | E]; rewrite E; apply bv_eq; cond_compute
  end.
(* [comment removed for export] *)
Ltac gv_norm :=
  rewrite ?w_mulw, ?w_addw, ?m_mul, ?alu_add, ?alu_sltu, ?alu_slt, ?alu_xor;
  rewrite ?zbv_mulw_small by lia; rewrite ?zbv_mul; rewrite ?zbv_addw_small by lia; rewrite ?zbv_mul, ?zbv_add;
  rewrite ?exB_ovf_idiom by lia; rewrite ?zbv_sltu_ge by lia.
Ltac gv_sc := gv_norm; ex_br.
Ltac gv_fin := first [ gev_typ_eq | (repeat rewrite ex_sx32 by lia; reflexivity) | (rewrite zbv_snez by lia; reflexivity)
                     | (rewrite gv_and255 by lia; reflexivity) | (gv_norm; first [ reflexivity | (f_equal; lia) ]) ].
(* [comment removed for export] *)
Ltac gv_cond :=
  rewrite ?alu_and, ?alu_or, ?alu_slt, ?alu_sltu, ?alu_add, ?zbv_add;
  rewrite ?gv_and255 by lia;
  rewrite !v_slt_Zs by lia;
  match goal with H : (4 <= ?t <= 5)%Z |- _ =>
    let E := fresh "E" in assert (E : t = 4%Z \/ t = 5%Z) by lia; destruct E as [E | E]; rewrite E end;
  destruct (_ <? _)%Z; destruct (_ <? _)%Z; apply bv_eq; cond_compute.
#[local] Ltac exB_sc_hook ::= first [ gev_typ_hook | gv_sc ].

Section Segs.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Definition FRG (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 (getr regs 1)))
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
Definition GVA (m : word -> option byte) (s cellp : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (FRG m s regs) (Z_to_bv 64 cellp) (word_to_le_bytes 4 (Z_to_bv 64 (-1))).

(* [comment removed for export] *)
Definition GVB (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
    (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 8)).

  (* [comment removed for export] *)
  Lemma gv_A : forall (fx : FPState) regs m (s pixs typ cellp : Z),
    (256 <= s < 2 ^ 63)%Z -> (s <= cellp)%Z -> (cellp + 4 < 2 ^ 63)%Z -> (cellp mod 4 = 0)%Z ->
    (4096 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z -> (4 <= typ <= 5)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true -> store_ok SEGS m (Z_to_bv 64 cellp) 4 = true ->
    rdn SEGS m (Z_to_bv 64 (pixs + 48)) 8 = Some (Z_to_le_bytes 8 0) ->
    (pixs + 64 <= s - 128 \/ s <= pixs)%Z -> (pixs + 64 <= cellp \/ cellp + 4 <= pixs)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 typ ->
    getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 15 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 cellp ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eba8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ed54) (GVA m s cellp regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 typ
      /\ getr regs' 19 = Z_to_bv 64 cellp /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 5; 9; 10; 11; 17; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros fx regs m s pixs typ cellp Hs Hc1 Hc2 ALc Hp1 Hp2 ALp Ht SOK SOKc Ccm APs APc H2 H10 H11 H12 H13 H14 H15 H16.
    ex_entry regs [s; pixs; typ; cellp] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixs; typ; cellp]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 4096 (2 ^ 63); KRange (EVar 34) 4 5; KRange (EVar 35) 256 (2 ^ 63);
                    KAlign (EVar 33) 8; KAlign (EVar 35) 4;
                    KWr (SA (EVar 32) (-128)) 128; KWr (SA (EVar 35) 0) 4;
                    KWord (SA (EVar 33) 48) 8 (ELit 0);
                    KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-128)) 128; KDisj (SA (EVar 33) 0) 64 (SA (EVar 35) 0) 4;
                    KDisj (SA (EVar 35) 0) 4 (SA (EVar 32) (-128)) 128]).
    { ex_know regs. }
    ex_run 100%nat [0x1ed54%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold GVA, FRG; ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  Qed.

  (* [comment removed for export] *)
  Lemma gv_B : forall (fx : FPState) regs m (s pixs typ cellp w h wpl data : Z),
    (256 <= s < 2 ^ 63)%Z -> (s mod 16 = 0)%Z -> (4096 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 8 = 0)%Z -> (4 <= typ <= 5)%Z ->
    (256 <= cellp < 2 ^ 63)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= wpl < 2 ^ 31)%Z -> (4096 <= data < 2 ^ 63)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true ->
    rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
    rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) -> rdn SEGS m (Z_to_bv 64 (pixs + 16)) 4 = Some (Z_to_le_bytes 4 wpl) ->
    rdn SEGS m (Z_to_bv 64 (pixs + 56)) 8 = Some (Z_to_le_bytes 8 data) ->
    (pixs + 64 <= s - 128 \/ s <= pixs)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 typ ->
    getr regs 19 = Z_to_bv 64 cellp -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ed54) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ef60) (GVB m s w h) rom)
      /\ getr regs' 8 = Z_to_bv 64 data /\ getr regs' 10 = Z_to_bv 64 wpl /\ getr regs' 11 = Z_to_bv 64 typ
      /\ getr regs' 12 = Z_to_bv 64 (gev_init typ) /\ getr regs' 13 = Z_to_bv 64 h /\ getr regs' 14 = Z_to_bv 64 cellp
      /\ getr regs' 15 = Z_to_bv 64 1 /\ getr regs' 16 = Z_to_bv 64 0 /\ getr regs' 7 = Z_to_bv 64 0 /\ getr regs' 17 = Z_to_bv 64 w
      /\ getr regs' 5 = Z_to_bv 64 1 /\ getr regs' 6 = Z_to_bv 64 wpl /\ getr regs' 28 = Z_to_bv 64 1 /\ getr regs' 29 = Z_to_bv 64 3
      /\ regs_agree (fun r => In r [1; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29]%list) regs regs'.
  Proof.
    intros fx regs m s pixs typ cellp w h wpl data Hs ALs Hp1 Hp2 ALp Ht Hc Hw Hh Hwpl Hd SOK Rw Rh Rd Rwpl Rdat APs
      H2 H9 H18 H23 H19 H20 H21 H22.
    ex_entry regs [s; pixs; typ; cellp; w; h; wpl; data] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixs; typ; cellp; w; h; wpl; data]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 4096 (2 ^ 63); KRange (EVar 34) 4 5; KRange (EVar 35) 256 (2 ^ 63);
                    KRange (EVar 36) 1 (2 ^ 31 - 1); KRange (EVar 37) 1 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1);
                    KRange (EVar 39) 4096 (2 ^ 63);
                    KAlign (EVar 32) 16; KAlign (EVar 33) 8;
                    KWr (SA (EVar 32) (-128)) 128;
                    KWord (SA (EVar 33) 0) 4 (EVar 36); KWord (SA (EVar 33) 4) 4 (EVar 37); KWord (SA (EVar 33) 8) 4 (ELit 8);
                    KWord (SA (EVar 33) 16) 4 (EVar 38); KWord (SA (EVar 33) 56) 8 (EVar 39);
                    KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-128)) 128]).
    { ex_know regs. }
    ex_run 300%nat [0x1ef60%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold GVB; ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try gv_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma gv_OH : forall (fx : FPState) regs m (i h w wpl data e : Z),
    (0 <= i < h)%Z -> (h <= 20000)%Z -> (1 <= w <= 20000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * h) <= 2 ^ 26)%Z ->
    (4096 <= data)%Z -> (data + 2 ^ 26 < 2 ^ 63)%Z -> (-1 <= e <= 100000)%Z ->
    getr regs 7 = Z_to_bv 64 i -> getr regs 16 = Z_to_bv 64 (i * wpl) -> getr regs 8 = Z_to_bv 64 data ->
    getr regs 10 = Z_to_bv 64 wpl -> getr regs 17 = Z_to_bv 64 w -> getr regs 28 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 e ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ef60) m rom) (@mkst fx regs' (Z_to_bv 64 0x1efd0) m rom)
      /\ getr regs' 30 = Z_to_bv 64 (data + 4 * (i * wpl)) /\ getr regs' 18 = Z_to_bv 64 (data + 4 * (i * wpl))
      /\ getr regs' 19 = Z_to_bv 64 (data + 4 * (i * wpl)) /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 31 = Z_to_bv 64 0
      /\ getr regs' 20 = Z_to_bv 64 e
      /\ regs_agree (fun r => In r [9; 18; 19; 20; 30; 31]%list) regs regs'.
  Proof.
    intros fx regs m i h w wpl data e Hi Hh Hw Hwpl Hwh Hd1 Hd2 He H7 H16 H8 H10 H17 H28 H12.
    assert (Hiw : (0 <= i * wpl <= 2 ^ 24)%Z) by nia. assert (Hwp : (wpl <= 2 ^ 24)%Z) by nia.
    ex_entry regs [i; wpl; data; w; e; (i * wpl)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [i; wpl; data; w; e; (i * wpl)%Z]) m
                   [KRange (EVar 32) 0 20000; KRange (EVar 33) 0 (2 ^ 24); KRange (EVar 34) 4096 (2 ^ 63);
                    KRange (EVar 35) 1 20000; KRange (EVar 37) 0 (2 ^ 24)]).
    { ex_know regs. }
    ex_run 100%nat [0x1efd0%Z] (SCR [false; false; false; false] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try gv_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma gv_I1 : forall (fx : FPState) regs m (line j typ e v : Z),
    (4096 <= line)%Z -> (line + 2 ^ 26 < 2 ^ 63)%Z -> (0 <= j < 20000)%Z -> (4 <= typ <= 5)%Z -> (-1 <= e <= 100000)%Z -> (0 <= v <= 255)%Z ->
    rdn SEGS m (Z_to_bv 64 (bytea (line + j))) 1 = Some (Z_to_le_bytes 1 v) ->
    getr regs 18 = Z_to_bv 64 (line + j) -> getr regs 19 = Z_to_bv 64 (line + j) -> getr regs 9 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 j ->
    getr regs 30 = Z_to_bv 64 line -> getr regs 28 = Z_to_bv 64 1 -> getr regs 29 = Z_to_bv 64 3 -> getr regs 15 = Z_to_bv 64 1 ->
    getr regs 11 = Z_to_bv 64 typ -> getr regs 20 = Z_to_bv 64 e ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1efd0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f02c) m rom)
      /\ getr regs' 22 = Z_to_bv 64 (if ((typ =? 4)%Z && (v <? e)%Z) || ((typ =? 5)%Z && (e <? v)%Z) then 1 else 0)
      /\ getr regs' 12 = Z_to_bv 64 v /\ getr regs' 21 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun r => In r [12; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m line j typ e v Hl1 Hl2 Hj Ht He Hv R H18 H19 H9 H31 H30 H28 H29 H15 H11 H20.
    ex_entry regs [line; j; typ; e; v; (line + j)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [line; j; typ; e; v; (line + j)%Z]) m
                   [KRange (EVar 32) 4096 (2 ^ 63); KRange (EVar 33) 0 20000; KRange (EVar 34) 4 5; KRange (EVar 36) 0 255;
                    KRange (EVar 37) 4096 (2 ^ 63)]).
    { ex_know regs. }
    ex_run 100%nat [0x1f02c%Z] (SCR [false; false; false; false] [EVar 36] []) HR HK R' HR' Hms.
    all: try (match goal with |- exists bs, rdn _ _ _ 1 = Some bs /\ _ =>
                exists (Z_to_le_bytes 1 v); split;
                [ rewrite dl_xor3 by lia; rewrite zbv_addi, Z.add_0_r; exact R
                | unfold extz; rewrite lez_u by (first [lia | cbn; lia]); rewrite u_Z2bv by lia; reflexivity ] end).
    exists R'. split; [ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try gv_fin.
    all: try gv_cond.
  Qed.

  (* [comment removed for export] *)
  Lemma gv_I2 : forall (t last : bool) (fx : FPState) regs m (j w p e v : Z),
    (0 <= j < w)%Z -> (w <= 20000)%Z -> (4096 <= p)%Z -> (p + 1 < 2 ^ 63)%Z -> (if last then j + 1 = w else j + 1 < w)%Z ->
    getr regs 22 = Z_to_bv 64 (if t then 1 else 0) -> getr regs 12 = Z_to_bv 64 v -> getr regs 20 = Z_to_bv 64 e ->
    getr regs 21 = Z_to_bv 64 (j + 1) -> getr regs 9 = Z_to_bv 64 j -> getr regs 31 = Z_to_bv 64 j ->
    getr regs 18 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 p -> getr regs 5 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
    getr regs 17 = Z_to_bv 64 w ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f02c) m rom) (@mkst fx regs' (Z_to_bv 64 (if last then 0x1f038 else 0x1efd0)) m rom)
      /\ getr regs' 20 = Z_to_bv 64 (if t then v else e) /\ getr regs' 12 = Z_to_bv 64 (if t then v else e)
      /\ getr regs' 9 = Z_to_bv 64 (j + 1) /\ getr regs' 31 = Z_to_bv 64 (j + 1)
      /\ getr regs' 18 = Z_to_bv 64 (p + 1) /\ getr regs' 19 = Z_to_bv 64 (p + 1) /\ getr regs' 21 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun r => In r [9; 12; 18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros t last fx regs m j w p e v Hj Hw Hp1 Hp2 Hlast H22 H12 H20 H21 H9 H31 H18 H19 H5 H15 H17.
    destruct t; cbv beta iota in H22.
    all: ex_entry regs [j; w; p; e; v; (j + 1)%Z] HR.
    all: assert (HK : know_ok SEGS (ex_env regs [j; w; p; e; v; (j + 1)%Z]) m
                   [KRange (EVar 32) 0 20000; KRange (EVar 33) 1 20000; KRange (EVar 34) 4096 (2 ^ 63); KRange (EVar 37) 1 20000])
      by (ex_know regs).
    all: destruct last; cbv beta iota in Hlast;
      [ ex_run 40%nat [0x1f038%Z; 0x1efd0%Z] (SCR [true] [] []) HR HK R' HR' Hms
      | ex_run 40%nat [0x1f038%Z; 0x1efd0%Z] (SCR [false] [] []) HR HK R' HR' Hms ].
    all: exists R'; split; [ex_mem2 regs Hms|].
    all: repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
    all: try gv_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma gv_ON : forall (last : bool) (fx : FPState) regs m (i h wpl : Z),
    (0 <= i < h)%Z -> (h <= 20000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * h) <= 2 ^ 26)%Z -> (if last then i + 1 = h else i + 1 < h)%Z ->
    getr regs 7 = Z_to_bv 64 i -> getr regs 15 = Z_to_bv 64 1 -> getr regs 16 = Z_to_bv 64 (i * wpl) -> getr regs 6 = Z_to_bv 64 wpl ->
    getr regs 13 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f038) m rom) (@mkst fx regs' (Z_to_bv 64 (if last then 0x1f050 else 0x1ef60)) m rom)
      /\ getr regs' 7 = Z_to_bv 64 (i + 1) /\ getr regs' 16 = Z_to_bv 64 ((i + 1) * wpl)
      /\ regs_agree (fun r => In r [7; 16; 30]%list) regs regs'.
  Proof.
    intros last fx regs m i h wpl Hi Hh Hwpl Hwh Hlast H7 H15 H16 H6 H13.
    assert (Hiw : (0 <= i * wpl /\ (i + 1) * wpl <= 2 ^ 24)%Z) by nia. assert (Hwp : (wpl <= 2 ^ 24)%Z) by nia.
    ex_entry regs [i; h; wpl; (i * wpl)%Z] HR.
    assert (HK : know_ok SEGS (ex_env regs [i; h; wpl; (i * wpl)%Z]) m
                   [KRange (EVar 32) 0 20000; KRange (EVar 33) 1 20000; KRange (EVar 34) 0 (2 ^ 24); KRange (EVar 35) 0 (2 ^ 24)])
      by (ex_know regs).
    destruct last; cbv beta iota in Hlast.
    - ex_run 40%nat [0x1f050%Z; 0x1ef60%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
      exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try gv_fin.
    - ex_run 40%nat [0x1f050%Z; 0x1ef60%Z] (SCR [false; true] [] []) HR HK R' HR' Hms.
      exists R'. split; [ex_mem2 regs Hms|].
      repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try gv_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma gv_E : forall (fx : FPState) regs m (s cellp e z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 : Z),
    (256 <= s < 2 ^ 63)%Z -> (256 <= cellp < 2 ^ 63)%Z -> (cellp mod 4 = 0)%Z -> (cellp + 4 <= s - 128 \/ s <= cellp)%Z ->
    (0 <= e <= 255)%Z -> ret_ok (Z_to_bv 64 z1) ->
    (0 <= z1 < 2 ^ 64)%Z -> (0 <= z8 < 2 ^ 64)%Z -> (0 <= z9 < 2 ^ 64)%Z -> (0 <= z18 < 2 ^ 64)%Z -> (0 <= z19 < 2 ^ 64)%Z ->
    (0 <= z20 < 2 ^ 64)%Z -> (0 <= z21 < 2 ^ 64)%Z -> (0 <= z22 < 2 ^ 64)%Z -> (0 <= z23 < 2 ^ 64)%Z -> (0 <= z24 < 2 ^ 64)%Z ->
    (0 <= z25 < 2 ^ 64)%Z -> (0 <= z26 < 2 ^ 64)%Z -> (0 <= z27 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 cellp) 4 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (Z_to_le_bytes 8 z1) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (Z_to_le_bytes 8 z8) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (Z_to_le_bytes 8 z9) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 z18) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 z19) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 z20) ->
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 z21) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 z22) ->
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 z23) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 z24) ->
    rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 z25) -> rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 z26) ->
    rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 z27) ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 14 = Z_to_bv 64 cellp -> getr regs 12 = Z_to_bv 64 e ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f050) m rom)
                  (@mkst fx regs' (Z_to_bv 64 z1) (wbytes m (Z_to_bv 64 cellp) (word_to_le_bytes 4 (Z_to_bv 64 e))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = Z_to_bv 64 z1 /\ getr regs' 8 = Z_to_bv 64 z8 /\ getr regs' 9 = Z_to_bv 64 z9
      /\ getr regs' 18 = Z_to_bv 64 z18 /\ getr regs' 19 = Z_to_bv 64 z19 /\ getr regs' 20 = Z_to_bv 64 z20 /\ getr regs' 21 = Z_to_bv 64 z21
      /\ getr regs' 22 = Z_to_bv 64 z22 /\ getr regs' 23 = Z_to_bv 64 z23 /\ getr regs' 24 = Z_to_bv 64 z24 /\ getr regs' 25 = Z_to_bv 64 z25
      /\ getr regs' 26 = Z_to_bv 64 z26 /\ getr regs' 27 = Z_to_bv 64 z27 /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros fx regs m s cellp e z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 Hs Hc ALc APc He Hret
      B1 B8 B9 B18 B19 B20 B21 B22 B23 B24 B25 B26 B27 SOKc R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 H2 H14 H12.
    ex_entry regs [s; cellp; e; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; cellp; e; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27]) m
                   [KRange (EVar 32) 256 (2 ^ 63); KRange (EVar 33) 256 (2 ^ 63); KAlign (EVar 33) 4; KWr (SA (EVar 33) 0) 4;
                    KDisj (SA (EVar 33) 0) 4 (SA (EVar 32) (-128)) 128;
                    KWord (SA (EVar 32) (-8)) 8 (EVar 35); KWord (SA (EVar 32) (-16)) 8 (EVar 36); KWord (SA (EVar 32) (-24)) 8 (EVar 37);
                    KWord (SA (EVar 32) (-32)) 8 (EVar 38); KWord (SA (EVar 32) (-40)) 8 (EVar 39); KWord (SA (EVar 32) (-48)) 8 (EVar 40);
                    KWord (SA (EVar 32) (-56)) 8 (EVar 41); KWord (SA (EVar 32) (-64)) 8 (EVar 42); KWord (SA (EVar 32) (-72)) 8 (EVar 43);
                    KWord (SA (EVar 32) (-80)) 8 (EVar 44); KWord (SA (EVar 32) (-88)) 8 (EVar 45); KWord (SA (EVar 32) (-96)) 8 (EVar 46);
                    KWord (SA (EVar 32) (-104)) 8 (EVar 47)]).
    { ex_know regs. }
    ex_run 80%nat [0x1eef0%Z] (SCR [] [] []) HR HK R' HR' Hms.
    assert (Hms2 : msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f050) m rom)
                     (@mkst fx R' (Z_to_bv 64 0x1eef0) (wbytes m (Z_to_bv 64 cellp) (word_to_le_bytes 4 (Z_to_bv 64 e))) rom))
      by (ex_mem2 regs Hms).
    eexists. split.
    - eapply msteps_trans; [exact Hms2|].
      stepret F_1eef0 D_1eef0 (Z_to_bv 64 z1) ltac:(idtac; ex_reg regs HR').
      apply mst_refl.
    - repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
      all: try gv_fin.
  Qed.

End Segs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
