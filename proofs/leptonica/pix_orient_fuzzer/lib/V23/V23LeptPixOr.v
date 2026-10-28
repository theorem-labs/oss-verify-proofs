(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptUb V23LeptRop_iface V23LeptRop V23LeptRopClip V23LeptRopP14.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRop2C.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecX.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Definition PC_pixOr : Z := 0x7e558.
Definition POR_STACK : Z := 48 + ROP_STACK.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition POF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
     (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
     (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
     (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
     (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
     (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).
(* [comment removed for export] *)
Definition POC (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (pix1 pix2 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (POF m s ret regs)
     (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x7e5ac)))
     (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 pix1)))
     (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 pix2)))
     (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (Z_to_bv 64 pix1)))
     (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 1)).
(* [comment removed for export] *)
Definition POM (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (pix1 pix2 : Z) : word -> option byte :=
  wbytes (POC m s ret regs pix1 pix2) (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

Lemma POF_outside : forall m s ret regs (a : word), (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 96 <= bv_unsigned a < s)%Z ->
  POF m s ret regs a = m a.
Proof.
  intros m s ret regs a Hs Hs2 Ha. pose proof (u64_range a). unfold POF.
  repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). reflexivity.
Qed.
Lemma POC_outside : forall m s ret regs pix1 pix2 (a : word), (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 96 <= bv_unsigned a < s)%Z ->
  POC m s ret regs pix1 pix2 a = m a.
Proof.
  intros m s ret regs pix1 pix2 a Hs Hs2 Ha. pose proof (u64_range a). unfold POC, POF.
  repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). reflexivity.
Qed.
Lemma POM_outside : forall m s ret regs pix1 pix2 (a : word), (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 96 <= bv_unsigned a < s)%Z ->
  POM m s ret regs pix1 pix2 a = m a.
Proof.
  intros m s ret regs pix1 pix2 a Hs Hs2 Ha. pose proof (u64_range a). unfold POM, POC, POF.
  repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). reflexivity.
Qed.

Section PixOr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.

Section Segs.
  Variable rom : word -> option byte.

  Import SX2. Import SX2S.

  Lemma v23pA_and7 : forall p : Z, (0 <= p < 2 ^ 64)%Z -> (p mod 8 = 0)%Z -> v_and (Z_to_bv 64 p) (Z_to_bv 64 7) = Z_to_bv 64 0.
  Proof.
    intros p Hp Hm. unfold v_and. rewrite !u_Z2bv by lia.
    change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z. rewrite Hm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma por_A : forall regs m (s pix1 pix2 : Z) (v1 v2 : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix1 < 2 ^ 64)%Z -> (1 <= pix2 < 2 ^ 64)%Z -> Z_to_bv 64 pix1 <> Z_to_bv 64 pix2 ->
    (pix1 mod 8 = 0)%Z -> (pix2 mod 8 = 0)%Z ->
    PIXat m pix1 v1 -> PIXat m pix2 v2 -> p_d v1 = 1%Z -> p_d v2 = 1%Z -> (0 <= p_w v1 < 2 ^ 31)%Z -> (0 <= p_h v1 < 2 ^ 31)%Z ->
    (pix1 + 64 <= s - 96 \/ s <= pix1)%Z -> (pix2 + 64 <= s - 96 \/ s <= pix2)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 ->
    getr regs 12 = Z_to_bv 64 pix2 ->
    exists regs',
      msteps SEGS (mkst regs (0x7e558 : word) m rom) (mkst regs' (0x7f13c : word) (POM m s ret regs pix1 pix2) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x7e5ec
      /\ getr regs' 10 = Z_to_bv 64 pix1 /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 (p_w v1) /\ getr regs' 14 = Z_to_bv 64 (p_h v1) /\ getr regs' 15 = Z_to_bv 64 14
      /\ getr regs' 16 = Z_to_bv 64 pix2 /\ getr regs' 17 = Z_to_bv 64 0
      /\ getr regs' 8 = Z_to_bv 64 pix1 /\ getr regs' 9 = Z_to_bv 64 pix2
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pix1 pix2 v1 v2 ret Hs Hs64 Hp1 Hp2 NE Ha1 Ha2 PX1 PX2 Hd1 Hd2 Hw Hh Hsep1 Hsep2 SOK H2 H1 H10 H11 H12.
    subst ret.
    pose proof (PIX_rd_w SEGS m pix1 v1 PX1) as Rw. pose proof (PIX_rd_h SEGS m pix1 v1 PX1) as Rh.
    pose proof (PIX_rd_d SEGS m pix1 v1 PX1) as Rd1. pose proof (PIX_rd_d SEGS m pix2 v2 PX2) as Rd2.
    rewrite Hd1 in Rd1. rewrite Hd2 in Rd2.
    pose proof PX1 as (_ & P1 & _). pose proof PX2 as (_ & P2 & _).
    assert (NEz : pix1 <> pix2) by (intros E; apply NE; rewrite E; reflexivity).
    replace (0x7e558 : word) with (Z_to_bv 64 0x7e558) by (apply bv_eq; reflexivity).
    replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pix1; pix2; p_w v1; p_h v1]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pix1; pix2; p_w v1; p_h v1]%Z) m
      [KRange (EVar 32) 96 (2 ^ 64 - 1); KWr (SA (EVar 32) (-96)) 96;
       KRange (EVar 33) 1 (2 ^ 64 - 65); KRange (EVar 34) 1 (2 ^ 64 - 65);
       KDisj (SA (EVar 32) (-96)) 96 (SA (EVar 33) 0) 64; KDisj (SA (EVar 32) (-96)) 96 (SA (EVar 34) 0) 64;
       KWord (SA (EVar 33) 0) 4 (EVar 35); KWord (SA (EVar 33) 4) 4 (EVar 36); KWord (SA (EVar 33) 8) 4 (ELit 1);
       KWord (SA (EVar 34) 8) 4 (ELit 1);
       KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 800%nat [0x7f13c]%Z (SCR [false; false; false; false; false] [] []) HR HK R' HR' Hms.
    all: try (solve [rewrite ?alu_and, ?v23pA_and7 by lia; ex_br]).
    exists R'. split.
    - unfold POM, POC, POF. ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'; try (rewrite ex_sx32 by lia; reflexivity)). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma por_Z : forall regs m (s pix1 : Z) (ret v0 v1 v2 v3 : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pix1 ->
    exists regs',
      msteps SEGS (mkst regs (0x7e5ec : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 pix1 /\ getr regs' 1 = ret
      /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pix1 ret v0 v1 v2 v3 Hs Hs64 Hret R0 R1 R2 R3 R4 H2 H8.
    replace (0x7e5ec : word) with (Z_to_bv 64 0x7e5ec) by (apply bv_eq; reflexivity).
    ex_entryL [ret; v0; v1; v2; v3] regs [s; pix1] HR.
    assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3] regs [s; pix1]) m
                   [KRange (EVar 37) 48 (2 ^ 64 - 1);
                    KWord (SA (EVar 37) (-8)) 8 (EVar 0); KWord (SA (EVar 37) (-16)) 8 (EVar 1);
                    KWord (SA (EVar 37) (-24)) 8 (EVar 2); KWord (SA (EVar 37) (-32)) 8 (EVar 3);
                    KWord (SA (EVar 37) (-40)) 8 (EVar 4)]%Z) by (ex_know regs).
    ex_run 100%nat (@nil Z) (SCR [] [] []) HR HK R' HR' Hms.
    assert (G1 : getr R' 1 = ret) by (ex_reg regs HR').
    assert (G2 : getr R' 2 = Z_to_bv 64 s) by (ex_reg regs HR').
    assert (G10 : getr R' 10 = Z_to_bv 64 pix1) by (ex_reg regs HR').
    assert (G8 : getr R' 8 = v0) by (ex_reg regs HR').
    assert (G9 : getr R' 9 = v1) by (ex_reg regs HR').
    assert (G18 : getr R' 18 = v2) by (ex_reg regs HR').
    assert (G19 : getr R' 19 = v3) by (ex_reg regs HR').
    assert (AG : regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs R') by (ex_agree HR HR').
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

End Segs.

Ltac por_sc := rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac por_rd := repeat first [ rewrite rdn_wbytes_hit8 by por_sc | rewrite rdn_wbytes_out by por_sc ]; reflexivity.

Lemma POM_cells : forall m s ret regs pix1 pix2, (96 <= s < 2 ^ 64)%Z ->
  rdn SEGS (POM m s ret regs pix1 pix2) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS (POM m s ret regs pix1 pix2) (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
  rdn SEGS (POM m s ret regs pix1 pix2) (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
  rdn SEGS (POM m s ret regs pix1 pix2) (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
  rdn SEGS (POM m s ret regs pix1 pix2) (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
  rdn SEGS (POM m s ret regs pix1 pix2) (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros m s ret regs pix1 pix2 Hs. unfold POM, POC, POF. repeat split; por_rd.
Qed.

(* [comment removed for export] *)
Definition pixOr_inplace_contract : Prop :=
  forall C Ar A m md regs (s pix1 pix2 : Z) (v1 v2 : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + POR_STACK <= s)%Z -> (s + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 -> getr regs 12 = Z_to_bv 64 pix2 ->
  PIXat m pix1 v1 -> PIXat m pix2 v2 -> p_d v1 = 1%Z -> p_d v2 = 1%Z ->
  rop_shape (p_w v1) (p_h v1) 1 (p_wpl v1) -> rop_shape (p_w v2) (p_h v2) 1 (p_wpl v2) ->
  live A (Z_to_bv 64 pix1) = Some 64%Z -> live A (Z_to_bv 64 pix2) = Some 64%Z -> Z_to_bv 64 pix1 <> Z_to_bv 64 pix2 ->
  Z_to_bv 64 pix1 <> Z_to_bv 64 (p_data v1) -> Z_to_bv 64 pix2 <> Z_to_bv 64 (p_data v1) ->
  live A (Z_to_bv 64 (p_data v1)) = Some (4 * (p_wpl v1 * p_h v1))%Z -> live Ar (Z_to_bv 64 (p_data v1)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data v1)) = None ->
  live A (Z_to_bv 64 (p_data v2)) = Some (4 * (p_wpl v2 * p_h v2))%Z -> Z_to_bv 64 (p_data v2) <> Z_to_bv 64 (p_data v1) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pix1 v1 -> PIXat m' pix2 v2 ->
      (forall a : word, ~ scratch C s a -> ~ (p_data v1 <= bv_unsigned a < p_data v1 + 4 * (p_wpl v1 * p_h v1))%Z -> m' a = m a) ->
      getr regs' 10 = Z_to_bv 64 pix1 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixOr) m al_rom) md) S.

Theorem pixOr_inplace_W : pixOr_inplace_contract.
Proof.
  unfold pixOr_inplace_contract.
  intros C Ar A m md regs s pix1 pix2 v1 v2 ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 PX1 PX2 Hd1 Hd2 RS1 RS2
    Lp1 Lp2 NE12 NE1d NE2d Ld1 Lrd1 L0d1 Ld2 NEd K.
  pose proof CK as [CK1 CK2 CK3 CK4 CK5]. pose proof LSTK_val as HLS. unfold POR_STACK, ROP_STACK in Hlo.
  pose proof (u64_range (c_sp0 C)) as Hsp.
  destruct (blk_range C A m md (Z_to_bv 64 pix1) 64 CK HW Lp1 ltac:(lia)) as [G1a G1b].
  destruct (blk_range C A m md (Z_to_bv 64 pix2) 64 CK HW Lp2 ltac:(lia)) as [G2a G2b].
  pose proof (u64_range (Z_to_bv 64 pix1)). pose proof (u64_range (Z_to_bv 64 pix2)).
  pose proof PX1 as (Hp1a & Hp1b & WF1 & _). pose proof PX2 as (Hp2a & Hp2b & WF2 & _).
  rewrite u_Z2bv in G1a, G1b, G2a, G2b by lia.
  destruct WF1, WF2.
  destruct RS1 as (RD1 & RW1 & RH1 & RWP1 & RM1). destruct RS2 as (RD2 & RW2 & RH2 & RWP2 & RM2).
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true) by (apply (W_sok_win C A m md (s - 96) 96 CK HW); cbn [Z.of_nat]; lia).
  replace (Z_to_bv 64 PC_pixOr) with (0x7e558 : word) by (apply bv_eq; reflexivity).
  assert (A1 : (pix1 mod 8 = 0)%Z).
  { destruct (ai_live_hull A m (m_vmmaps md) _ 64 (w_inv _ _ _ _ HW) Lp1) as (_ & X & _). rewrite u_Z2bv in X by lia.
    clear - X; Z.div_mod_to_equations; lia. }
  assert (A2 : (pix2 mod 8 = 0)%Z).
  { destruct (ai_live_hull A m (m_vmmaps md) _ 64 (w_inv _ _ _ _ HW) Lp2) as (_ & X & _). rewrite u_Z2bv in X by lia.
    clear - X; Z.div_mod_to_equations; lia. }
  destruct (por_A al_rom regs m s pix1 pix2 v1 v2 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NE12 A1 A2 PX1 PX2 Hd1 Hd2
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := POM m s ret regs pix1 pix2).
  assert (HWM : W C A M1 md).
  { subst M1. unfold POM, POC, POF.
    repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    exact HW. }
  assert (PMA : POSTM C Ar s m M1).
  { apply (POSTM_sub C Ar A); [exact SUB|]. apply (POSTM_range C A m md M1 (s - 96) s s CK HW); [| lia | lia | lia].
    intros a Ha. subst M1. apply POM_outside; [lia | lia | exact Ha]. }
  destruct (POM_cells m s ret regs pix1 pix2 ltac:(lia)) as (C8 & C16 & C24 & C32 & C40 & C48). fold M1 in C8, C16, C24, C32, C40, C48.
  assert (PXM1 : PIXat M1 pix1 v1).
  { apply (PIXat_frame m M1 pix1 v1 PX1). intros x Hx. subst M1. apply POM_outside; lia. }
  assert (PXM2 : PIXat M1 pix2 v2).
  { apply (PIXat_frame m M1 pix2 v2 PX2). intros x Hx. subst M1. apply POM_outside; lia. }
  replace (0x7f13c : word) with (Z_to_bv 64 PC_pixRasterop) by (apply bv_eq; reflexivity).
  apply (pixRasterop_op14clip_W C Ar A M1 md r1 (s - 48)%Z pix1 0%Z 0%Z (p_w v1) (p_h v1) pix2 0%Z 0%Z v1 v2 (Z_to_bv 64 0x7e5ec) S
           CK HWM SUB Q2 ltac:(clear - Hs16; Z.div_mod_to_equations; lia) ltac:(unfold ROP_STACK; lia) ltac:(lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 C48 PXM1 PXM2 ltac:(lia) Hd1).
  all: try (rewrite ?Hd1, ?Hd2; split; [lia | repeat split; lia || assumption]).
  all: try lia.
  - left. cbv [O23LeptRopClip.clip_d O23LeptRopClip.clip_s]. cbn. split; reflexivity.
  - exact Lp1.
  - exact Lp2.
  - exact NE1d.
  - exact NE2d.
  - exact Ld1.
  - exact Lrd1.
  - exact L0d1.
  - exact Ld2.
  - exact NEd.
  - intros m2 r2 HW2 CS2 PM2 PX1' PX2' FR2 R10'.
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (rewrite (cs_kept_get r1 r2 2 CS2 cs2); exact Q2).
    assert (E8 : getr r2 8 = Z_to_bv 64 pix1) by (rewrite (cs_kept_get r1 r2 8 CS2 cs8); exact Q8).
    assert (D8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret))
      by (rewrite (FRM_rdn16 C (s - 48) M1 m2 (s - 8) 8 CK (proj1 PM2)) by (cbn; lia); exact C8).
    assert (D16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)))
      by (rewrite (FRM_rdn16 C (s - 48) M1 m2 (s - 16) 8 CK (proj1 PM2)) by (cbn; lia); exact C16).
    assert (D24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)))
      by (rewrite (FRM_rdn16 C (s - 48) M1 m2 (s - 24) 8 CK (proj1 PM2)) by (cbn; lia); exact C24).
    assert (D32 : rdn SEGS m2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)))
      by (rewrite (FRM_rdn16 C (s - 48) M1 m2 (s - 32) 8 CK (proj1 PM2)) by (cbn; lia); exact C32).
    assert (D40 : rdn SEGS m2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)))
      by (rewrite (FRM_rdn16 C (s - 48) M1 m2 (s - 40) 8 CK (proj1 PM2)) by (cbn; lia); exact C40).
    replace (Z_to_bv 64 0x7e5ec) with (0x7e5ec : word) by (apply bv_eq; reflexivity).
    destruct (por_Z al_rom r2 m2 s pix1 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) Hret
                D8 D16 D24 D32 D40 E2 E8) as (r3 & RUN3 & Z2 & Z10 & Z1 & Z8 & Z9 & Z18 & Z19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    apply K; [exact HW2 | | | exact PX1' | exact PX2' | | exact Z10].
    + apply cs_kept_intro; try assumption.
      * rewrite Z2, H2. reflexivity.
      * rewrite (AG3 3) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 3 CS2 cs3). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 4) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 4 CS2 cs4). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 20) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 20 CS2 cs20). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 21) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 21 CS2 cs21). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 22) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 22 CS2 cs22). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 23) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 23 CS2 cs23). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 24) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 24 CS2 cs24). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 25) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 25 CS2 cs25). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 26) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 26 CS2 cs26). apply AG1. cbn [In]; intuition discriminate.
      * rewrite (AG3 27) by (cbn [In]; intuition discriminate). rewrite (cs_kept_get r1 r2 27 CS2 cs27). apply AG1. cbn [In]; intuition discriminate.
    + eapply POSTM_trans; [exact PMA | eapply POSTM_mono; [| exact PM2]; lia].
    + intros a Hsc Hrow. rewrite (FR2 a ltac:(unfold scratch in *; lia) Hrow). subst M1. apply POM_outside; [lia | lia |].
      unfold scratch in Hsc. lia.
Qed.

End PixOr.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
