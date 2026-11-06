(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_np4 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2 AXG_nf2b AXG_nf3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_npf AXG_nf6.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfsc OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.AXG_nf4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.AXG_nf5 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gp AXG_gp2 AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b AXG_gf3 AXG_gf4.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_gf2b.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b.AXG_gf2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf4 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf2b.AXG_gf5.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.


Lemma gmAc_frame : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 ->
  ~ (SP - 2048 <= x < SP) -> ~ (CA <= x < CA + 2592) -> ~ (RI <= x < RI + 8) ->
  gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x HSP H1 H2 H3 H4 Hx Q1 Q2 Q3. unfold gmAc.
  rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite ic_keep; [| lia | lia | exact Hx | intros i Hi; lia].
  rewrite (wchainS_frame_in (L1a c CA v1 v8 v9 v18 v19 v20) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
Lemma gmAc_grows : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  mem_grows m (gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27).
Proof.
  intros. unfold gmAc.
  apply (mem_grows_trans _ _ _ (wchainS_grows (L1a c CA v1 v8 v9 v18 v19 v20) m SP)).
  apply (mem_grows_trans _ _ _ (ic_grows _ CA)).
  apply (mem_grows_trans _ _ _ (wchainS_grows (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP)).
  apply (mem_grows_trans _ (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))).
  - apply grows_wb. apply mem_grows_refl.
  - apply wchainS_grows.
Qed.

(* [comment removed for export] *)
Lemma gmAc_rd3 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> wl_chk (gL3a c CA n RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 ->
  rd (gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof. intros. unfold gmAc. apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | assumption]. Qed.
Lemma gmAc_rd2 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> wl_chk (L2a c CA n g21 g22 g23 g24 g25 g26 g27) k 8 = Some v -> -208 <= k -> k + 8 <= 0 ->
  rd (gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold gmAc.
  apply (rd_frame (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply wb_other; [lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma gmAc_rd1 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> 0 <= CA -> CA + 4096 <= SP - 2048 ->
  wl_chk (L1a c CA v1 v8 v9 v18 v19 v20) k 8 = Some v -> -80 <= k -> k + 8 <= 0 ->
  rd (gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 H3 H4 Hc Hk1 Hk2. unfold gmAc.
  apply (rd_frame (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-208) (-80)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply ic_keep; [lia | lia | lia | intros i Hi; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma gmAc_frame_f : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 ->
  ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) -> ~ (RI <= x < RI + 8) ->
  gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x HSP H1 H2 H3 H4 Hx Q1 Q2 Q3. unfold gmAc.
  rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite ic_keep; [| lia | lia | exact Hx | exact Q2].
  rewrite (wchainS_frame_in (L1a c CA v1 v8 v9 v18 v19 v20) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
(* [comment removed for export] *)
Lemma gmAc_rdRI : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  rd (gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) RI 8 1152921504606846976.
Proof.
  intros. unfold gmAc.
  apply (rd_frame (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx. apply (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply wb_rd_hit; [lia | lia | cbn; lia].
Qed.
Lemma gmAc_rd_ic : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 i,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> 0 <= CA -> CA + 4096 <= SP - 2048 -> (CA + 4096 <= RI \/ RI + 128 <= CA) -> 1 <= i <= 31 ->
  rd (gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (CA + 80 * i + 4) 4 (mc_tbl i) /\
  rd (gmAc m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (CA + 80 * i + 8) 8 (sz_tbl i).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 i HSP H1 H2 H3 H4 H5 Hi. unfold gmAc.
  destruct (ic_rd (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA i ltac:(lia) ltac:(lia) Hi) as [X1 X2].
  assert (FR : forall x, CA + 80 * i + 4 <= x < CA + 80 * i + 16 ->
            wchainS (wbytes (wchainS (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976))) SP (gL3a c CA n RI RB FA) (wa x) =
            ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA (wa x)).
  { intros x Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    apply (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia]. }
  split; [apply (rd_frame (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply FR; lia | exact X1]
         | apply (rd_frame (ic_mem (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) CA)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply FR; lia | exact X2]].
Qed.

(* [comment removed for export] *)
Definition gMA_OK (m mA0 : word -> option byte) (regs : bvmap 5 word) (SP CA c RI RB FA : Z) : Prop :=
  (forall k v, wl_chk (gL3a c CA (mc_tbl c / 2) RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall k v, wl_chk (L2a c CA (mc_tbl c / 2) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
      -208 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall k v, wl_chk (L1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))) k 8 = Some v ->
      -80 <= k -> k + 8 <= 0 -> rd mA0 (SP + k) 8 v) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
     ~ (RI <= x < RI + 8) -> mA0 (wa x) = m (wa x)) /\
  rd mA0 RI 8 1152921504606846976 /\
  (rd mA0 (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd mA0 (CA + 80 * c + 8) 8 (sz_tbl c)) /\
  mem_grows m mA0.

(* [comment removed for export] *)
Section FU.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m mA0 : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP st st2 TP K TSDA PT T mm1 mm2 : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Let SHv := Z.shiftr (SB + 4294967296 * c) 3 + 2147450880.
Let SHFv := Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880.
(* [comment removed for export] *)
Definition gCHC (x : Z) : Prop :=
  SP - 2048 <= x < SP \/ CA <= x < CA + 2592 \/ RIv <= x < RIv + 128 \/ T + 2872 <= x < T + 2888 \/ RBv <= x < RBv + 262144 \/
  FAv <= x < FAv + 262144 \/ SHv <= x < SHv + 32768 \/ SHFv <= x < SHFv + 32768.
Definition gENVC (x : Z) : Prop :=
  65536 <= x < 143360 \/ 904176 <= x < 904248 \/ 912208 <= x < 912216 \/ 923512 <= x < 923537 \/ 935452 <= x < 935464 \/ 937400 <= x < 937408 \/
  940704 <= x < 940728 \/ 1525856 <= x < 1525864 \/ 1534328 <= x < 1534336 \/ 1534444 <= x < 1534445 \/
  TP - 88 <= x < TP - 80 \/ TSDA + 8 * K <= x < TSDA + 8 * K + 8 \/ PT + 152 <= x < PT + 160.
Definition gCELLS_B (x : Z) : Prop :=
  SP - 2048 <= x < SP \/ CA <= x < CA + 2592 \/ RIv <= x < RIv + 128 \/ T + 2872 <= x < T + 2888 \/
  SHv <= x < SHv + 32768 \/ SHFv <= x < SHFv + 32768 \/ gENVC x.
Definition gCELLS_C (x : Z) : Prop := gCELLS_B x \/ FAv <= x < FAv + 262144.

Hypothesis Hc : c = cls_of ND.
Hypothesis HND : 1 <= ND <= 65536.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis H4 : getr regs 4 = wa TP.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HCT : CA = T + 208.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HO : objs_ok_p (SP - 2048) T RIv TP TSDA PT.
Hypothesis HK : 0 <= K <= 1023.
Hypothesis Hvals : 0 <= st < 2^64 /\ 0 <= st2 < 2^64 /\ 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64.
Hypothesis HENV : forall x, gENVC x -> ~ gCHC x.
Hypothesis HSHs : shsep T RIv TP TSDA PT SHv.
Hypothesis HSHF : shsep T RIv TP TSDA PT SHFv.
(* [comment removed for export] *)
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Ist2 : rd m (CA + 2584) 8 st2.
Hypothesis Iwc : wr m CA 2592.
Hypothesis Iri : forall i, 0 <= i < 16 -> rd m (RIv + 8 * i) 8 0.
Hypothesis Iwri : wr m RIv 128.
Hypothesis Imm1 : rd m (T + 2872) 8 mm1.
Hypothesis Imm2 : rd m (T + 2880) 8 mm2.
Hypothesis Iwt : wr m (T + 2872) 16.
Hypothesis Iwsh : wr m SHv 32768.
Hypothesis Iwshf : wr m SHFv 32768.
(* [comment removed for export] *)
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Icf144 : rd m 1534328 8 0.
Hypothesis Idpm : rd m 1534444 1 0.
Hypothesis Ips1 : rd m 935452 1 1.
Hypothesis Ips2 : rd m 904208 8 937400.
Hypothesis Ips3 : rd m 937400 8 2147450880.
Hypothesis Ips4 : rd m 904216 8 940712.
Hypothesis Ips5 : rd m 940712 8 0.
Hypothesis Ips6 : rd m 904224 8 940720.
Hypothesis Ips7 : rd m 940720 8 0.
Hypothesis Ips8 : rd m 904232 8 940704.
Hypothesis Ips9 : rd m 940704 8 140737488355327.
Hypothesis Ips10 : rd m 904240 8 912208.
Hypothesis Ips11 : rd m 912208 8 864392.
Hypothesis Itls1 : rd m 935456 1 1.
Hypothesis Itls2 : rd m 935460 4 K.
Hypothesis Itls3 : rd m (TP - 88) 8 TSDA.
Hypothesis Itls4 : rd m (TSDA + 8 * K) 8 PT.
Hypothesis Itls5 : rd m (PT + 152) 8 T.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.
(* [comment removed for export] *)
Hypothesis HMA : gMA_OK m mA0 regs SP CA c RIv RBv FAv.

(* [comment removed for export] *)
#[using="ND Hc HND HSP HCA HCT HSB HO HK"] Lemma gfu_geo : 2^46 + 4096 <= SP <= 2^47 /\ 1 <= c <= 30 /\ 4304 <= CA /\ CA + 4096 <= SP - 2048 /\ CA = T + 208 /\
  17594333495296 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\
  RIv = SB + 137438953472 + 128 * c /\ RBv = SB + 4294967296 * c /\ FAv = RBv + 3758096384 /\
  8 * (SHv - 2147450880) = RBv /\ 8 * (SHFv - 2147450880) = FAv /\
  4096 <= T /\ T + 4096 <= SP - 2048 - 256 /\ 4096 <= TP /\ TP <= SP - 2048 - 256 /\
  1 <= TSDA /\ TSDA + 8192 <= SP - 2048 - 256 /\ 1 <= PT /\ PT + 160 <= SP - 2048 - 256 /\ 0 <= K <= 1023.
Proof. LiaFast.lf_pins (fun (ND Hc HND HSP HCA HCT HSB HO HK : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  assert (E3 : RBv mod 8 = 0).
  { unfold RBv. destruct HSB as (_ & Hm & _). pose proof (Z.div_mod SB 4096 ltac:(lia)) as E. rewrite Hm, Z.add_0_r in E. rewrite E.
    replace (4096 * (SB / 4096) + 4294967296 * c) with ((512 * (SB / 4096) + 536870912 * c) * 8) by ring. apply Z.mod_mul. lia. }
  assert (E1 : 8 * (SHv - 2147450880) = RBv).
  { unfold SHv. fold RBv. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. pose proof (Z.div_mod RBv 8 ltac:(lia)) as E. rewrite E3 in E. lia. }
  assert (E2 : 8 * (SHFv - 2147450880) = FAv).
  { unfold SHFv. fold FAv. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    assert (E4 : FAv mod 8 = 0).
    { unfold FAv. fold RBv. replace (RBv + 3758096384) with (RBv + 469762048 * 8) by ring. rewrite Z.mod_add by lia. exact E3. }
    pose proof (Z.div_mod FAv 8 ltac:(lia)) as E. rewrite E4 in E. lia. }
  unfold objs_ok_p, t_place in HO. unfold FAv, RBv in *. clear - Hcr5 HSP HCA HCT HSB E1 E2 HO HK. unfold RIv in *. lia.
Qed.
(* [comment removed for export] *)
#[using="SP TP TSDA PT HO"] Lemma gfu_d_ri_t : RIv + 128 <= T \/ T + 4096 <= RIv.
Proof. LiaFast.lf_pins (fun (SP TP TSDA PT HO : LiaFast.U) => LiaFast.u0). unfold objs_ok_p in HO. clear - HO. tauto. Qed.

Ltac zg := let G := fresh "G" in pose proof gfu_geo as G; clear - G; lia.
Ltac zg1 H := let G := fresh "G" in pose proof gfu_geo as G; clear - G H; lia.
Ltac zg2 H1 H2 := let G := fresh "G" in pose proof gfu_geo as G; clear - G H1 H2; lia.
Ltac zg3 H1 H2 H3 := let G := fresh "G" in pose proof gfu_geo as G; clear - G H1 H2 H3; lia.
(* [comment removed for export] *)
Ltac pick := first [ lia | left; lia | right; pick ].
Ltac envc Hx := unfold gENVC; let G := fresh "G" in pose proof gfu_geo as G; clear - G Hx; pick.


(* [comment removed for export] *)
Definition gmB0 : word -> option byte := kz mA0 RBv 262144.

#[using="regs FAv HMA"] Lemma gmB0_frame : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
  ~ (RIv <= x < RIv + 8) -> ~ (RBv <= x < RBv + 262144) -> gmB0 (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (regs FAv HMA : LiaFast.U) => LiaFast.u0).
  intros x Hx Q1 Q2 Q3 Q4. unfold gmB0. rewrite kz_out by assumption.
  destruct HMA as (_ & _ & _ & FR & _). exact (FR x Hx Q1 Q2 Q3).
Qed.
#[using="regs ND TP K TSDA PT Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma gmB0_env : forall x, 0 <= x < 2^64 -> ~ gCHC x -> gmB0 (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (regs ND TP K TSDA PT Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros x Hx Q. unfold gCHC in Q. apply gmB0_frame; [exact Hx | zg1 Q | intros i Hi; zg2 Q Hi | zg1 Q | zg1 Q].
Qed.
#[using="regs CA SP RIv FAv HMA"] Lemma gmB0_grows : mem_grows m gmB0.
Proof. LiaFast.lf_pins (fun (regs CA SP RIv FAv HMA : LiaFast.U) => LiaFast.u0). unfold gmB0. destruct HMA as (_ & _ & _ & _ & _ & _ & GA). exact (mem_grows_trans _ _ _ GA (kz_grows _ _ _)). Qed.
(* [comment removed for export] *)
#[using="m regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma gmB0_slot3 : forall k v, wl_chk (gL3a c CA (mc_tbl c / 2) RIv RBv FAv) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd gmB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold gmB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (S3 & _). exact (S3 k v Hk K1 K2).
Qed.
#[using="m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma gmB0_slot2 : forall k v, wl_chk (L2a c CA (mc_tbl c / 2) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
  -208 <= k -> k + 8 <= 0 -> rd gmB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold gmB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (_ & S2 & _). exact (S2 k v Hk K1 K2).
Qed.
#[using="m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma gmB0_slot1 : forall k v, wl_chk (L1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))) k 8 = Some v ->
  -80 <= k -> k + 8 <= 0 -> rd gmB0 (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m ND TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. unfold gmB0. apply (rd_frame mA0); [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; apply kz_out; zg3 K1 K2 Hx |].
  destruct HMA as (_ & _ & S1 & _). exact (S1 k v Hk K1 K2).
Qed.
(* [comment removed for export] *)
#[using="regs CA ND SP T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA"] Lemma gmB0_envrd : forall a w v, 0 <= a -> (forall x, a <= x < a + Z.of_nat w -> gENVC x) -> a + Z.of_nat w <= 2^64 -> rd m a w v -> rd gmB0 a w v.
Proof. LiaFast.lf_pins (fun (regs CA ND SP T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA : LiaFast.U) => LiaFast.u0).
  intros a w v Ha HE Hw H. apply (rd_frame m gmB0); [exact Ha | exact Hw | | exact H].
  intros x Hx. apply gmB0_env; [lia | apply HENV; exact (HE x Hx)].
Qed.
(* [comment removed for export] *)
#[using="regs ND SP TP K TSDA PT FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA"] Lemma gmB0_keep : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
  (T + 2872 <= a /\ a + Z.of_nat w <= T + 2888) \/ (CA + 2576 <= a /\ a + Z.of_nat w <= CA + 2592) \/ (RIv + 8 <= a /\ a + Z.of_nat w <= RIv + 128) ->
  rd m a w v -> rd gmB0 a w v.
Proof. LiaFast.lf_pins (fun (regs ND SP TP K TSDA PT FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw Hr H. pose proof gfu_d_ri_t as D1. pose proof HSEP as D2.
  apply (rd_frame m gmB0); [exact Ha | lia | | exact H].
  intros x Hx. apply gmB0_frame; [lia | | | | ].
  - pose proof gfu_geo as G. clear - G Hr Hx D1 D2. lia.
  - intros i Hi. pose proof gfu_geo as G. clear - G Hr Hx D1 D2 Hi. lia.
  - pose proof gfu_geo as G. clear - G Hr Hx D1 D2. lia.
  - pose proof gfu_geo as G. clear - G Hr Hx D1 D2. lia.
Qed.
(* [comment removed for export] *)
#[using="m regs CA ND SP TP K TSDA PT T FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA"] Lemma gmB0_mu : rd gmB0 RIv 8 1152921504606846976.
Proof. LiaFast.lf_pins (fun (m regs CA ND SP TP K TSDA PT T FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA : LiaFast.U) => LiaFast.u0).
  unfold gmB0. apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; zg1 Hx |].
  destruct HMA as (_ & _ & _ & _ & MU & _). exact MU.
Qed.
#[using="m regs ND SP TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA"] Lemma gmB0_ic : rd gmB0 (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd gmB0 (CA + 80 * c + 8) 8 (sz_tbl c).
Proof. LiaFast.lf_pins (fun (m regs ND SP TP K TSDA PT T RIv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA : LiaFast.U) => LiaFast.u0).
  pose proof HSEP as D. destruct HMA as (_ & _ & _ & _ & _ & (X1 & X2) & _). unfold gmB0.
  split; [apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; [zg1 Hx | pose proof gfu_geo as G; clear - G D Hx; lia] | exact X1]
         | apply (rd_frame mA0); [zg | cbn; zg | intros x Hx; cbn in Hx; apply kz_out; [zg1 Hx | pose proof gfu_geo as G; clear - G D Hx; lia] | exact X2]].
Qed.

(* [comment removed for export] *)
Definition gPB (mB : word -> option byte) : Prop :=
  (forall x, SHv <= x < SHv + 32768 -> mB (wa x) = Some (Z_to_bv 8 250)) /\
  rd mB (SP - 448 + 88) 8 515004 /\ rd mB (SP - 448 + 80) 8 262144 /\ rd mB (SP - 448 + 72) 8 FAv /\
  rd mB (SP - 448 + 64) 8 262144 /\ rd mB (SP - 448 + 56) 8 RIv /\ rd mB (SP - 448 + 48) 8 262144 /\
  rd mB (SP - 352 + 24) 8 271780 /\ rd mB (SP - 352 + 16) 8 262144 /\ rd mB (SP - 352 + 8) 8 FAv /\ rd mB (SP - 352 + 0) 8 262144 /\
  rd mB (SP - 280) 8 281044 /\ rd mB (SP - 288) 8 RIv /\ rd mB (SP - 296) 8 (262144 / (sz_tbl c)) /\
  rd mB (SP - 304) 8 RBv /\ rd mB (SP - 312) 8 (262144 / (sz_tbl c)) /\
  rd mB (RIv + 48) 8 262144 /\ rd mB (T + 2872) 8 (mm1 + 1) /\ rd mB (T + 2880) 8 (mm2 + 262144) /\ rd mB (CA + 2584) 8 (st2 + 262144).
Definition gFRB (m0 mB : word -> option byte) : Prop :=
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP - 272) -> ~ (SHv <= x < SHv + 32768) -> ~ (RIv + 48 <= x < RIv + 56) ->
     ~ (CA + 2584 <= x < CA + 2592) -> ~ (T + 2872 <= x < T + 2888) -> mB (wa x) = m0 (wa x)) /\ mem_grows m0 mB.

Section SB.
Variable mB0' : word -> option byte.
Hypothesis HB0 : agree_on gCELLS_B mB0' gmB0.

#[using="FAv HB0"] Lemma gb_rd : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> gCELLS_B x) -> rd gmB0 a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (FAv HB0 : LiaFast.U) => LiaFast.u0). intros a w v Ha Hw HS H. apply (rd_agree gCELLS_B mB0' gmB0); [exact HB0 | exact Ha | lia | exact HS | exact H]. Qed.
#[using="mA0 regs RBv FAv HMA HB0"] Lemma gb_wr : forall a n, 0 <= a -> a + n <= 2^63 -> (forall x, a <= x < a + n -> gCELLS_B x) -> wr m a n -> wr mB0' a n.
Proof. LiaFast.lf_pins (fun (mA0 regs RBv FAv HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a n Ha Hn HS H. apply (wr_agree gCELLS_B mB0' gmB0); [exact HB0 | exact Ha | lia | exact HS |].
  exact (wr_grows m gmB0 _ _ gmB0_grows H).
Qed.
#[using="mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA HB0"] Lemma gb_env : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> gENVC x) -> rd m a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HENV HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HE H. apply gb_rd; [exact Ha | exact Hw | intros x Hx; unfold gCELLS_B; do 6 right; exact (HE x Hx) |].
  apply gmB0_envrd; [exact Ha | exact HE | lia | exact H].
Qed.
#[using="m mA0 regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma gb_slot3 : forall k v, wl_chk (gL3a c CA (mc_tbl c / 2) RIv RBv FAv) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 regs ND TP K TSDA PT T SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply gb_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold gCELLS_B; left; zg3 K1 K2 Hx |].
  apply gmB0_slot3; assumption.
Qed.
#[using="m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma gb_slot2 : forall k v, wl_chk (L2a c CA (mc_tbl c / 2) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))) k 8 = Some v ->
  -208 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply gb_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold gCELLS_B; left; zg3 K1 K2 Hx |].
  apply gmB0_slot2; assumption.
Qed.
#[using="m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma gb_slot1 : forall k v, wl_chk (L1a c CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))) k 8 = Some v ->
  -80 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (m mA0 ND SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros k v Hk K1 K2. apply gb_rd; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold gCELLS_B; left; zg3 K1 K2 Hx |].
  apply gmB0_slot1; assumption.
Qed.
#[using="m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0"] Lemma gb_mu : rd mB0' RIv 8 1152921504606846976.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0). apply gb_rd; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold gCELLS_B; do 2 right; left; clear - Hx; lia | exact gmB0_mu]. Qed.
#[using="m mA0 regs ND SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0"] Lemma gb_ic : rd mB0' (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd mB0' (CA + 80 * c + 8) 8 (sz_tbl c).
Proof. LiaFast.lf_pins (fun (m mA0 regs ND SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  destruct gmB0_ic as [X1 X2].
  split; (apply gb_rd; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold gCELLS_B; right; left; clear - Hx Hcr5; lia | assumption]).
Qed.
#[using="mA0 regs ND SP TP K TSDA PT RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0"] Lemma gb_keep : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
  (T + 2872 <= a /\ a + Z.of_nat w <= T + 2888) \/ (CA + 2576 <= a /\ a + Z.of_nat w <= CA + 2592) \/ (RIv + 8 <= a /\ a + Z.of_nat w <= RIv + 128) ->
  rd m a w v -> rd mB0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs ND SP TP K TSDA PT RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw Hr H. apply gb_rd; [exact Ha | exact Hw | | apply gmB0_keep; assumption].
  intros x Hx. unfold gCELLS_B. pose proof gfu_geo as G. clear - G Hr Hx. destruct Hr as [Hr|[Hr|Hr]]; [do 3 right; left; lia | right; left; lia | do 2 right; left; lia].
Qed.
#[using="m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA HB0"] Lemma gb_stk : stk_ok SEGS mB0' (wa SP) 2048.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA HB0 : LiaFast.U) => LiaFast.u0).
  apply (stk_ok_agree gCELLS_B mB0' gmB0); [exact HB0 | zg | zg | intros x Hx; unfold gCELLS_B; left; exact Hx |].
  exact (stk_ok_grows m gmB0 (wa SP) 2048 gmB0_grows HSTK).
Qed.

Ltac benv H := apply gb_env; [zg | cbn; zg | intros x Hx; cbn in Hx; envc Hx | exact H].

#[using="m mA0 regs ND st K TSDA PT SHFv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh Iprem Igot Ipsz Icf Icf144 Idpm Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HMA HB0"] Lemma gstageB : forall R1', getr R1' 1 = wa 481796 -> getr R1' 2 = wa (SP - 400) -> getr R1' 4 = wa TP -> getr R1' 8 = wa 262144 ->
  getr R1' 10 = wa RBv -> getr R1' 21 = wa (sz_tbl c) -> getr R1' 22 = wa 923480 ->
  exists R2 mB, msteps SEGS (mkst R1' (wa 0x73c48) mB0' rom) (mkst R2 (wa 0x73c44) mB rom) /\
    EC R2 FAv /\ getr R2 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R2 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 448) /\
    getr R2 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R2 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R2 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
    getr R2 (Z_to_bv 5 (Z.of_nat 4)) = wa TP /\ getr R2 (Z_to_bv 5 (Z.of_nat 3)) = getr R1' (Z_to_bv 5 (Z.of_nat 3)) /\
    gPB mB /\ gFRB mB0' mB.
Proof. LiaFast.lf_pins (fun (m mA0 regs ND st K TSDA PT SHFv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh Iprem Igot Ipsz Icf Icf144 Idpm Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HMA HB0 : LiaFast.U) => LiaFast.u0).
  intros R1' Q1 Q2 Q4 Q8 Q10 Q21 Q22.
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  assert (Hst3 : 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64 /\ 0 <= st2 < 2^64) by (clear - Hvals; lia).
  assert (FRI : forall i, 1 <= i < 16 -> rd mB0' (RIv + 8 * i) 8 0).
  { intros i Hi. apply gb_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))]. }
  destruct (gsegB rom mB0' R1' CA c SB SP TP K TSDA PT T mm1 mm2 st2 Hcr5 HSP HCT HO HSB HK ltac:(clear - HCA; lia) HSHs Hst3 Q1 Q2 Q4 Q8 Q10 Q21 Q22)
    as (R2 & mB & Hms & B1 & B2 & B8 & B10 & B11 & B12 & B13 & B14 & B15 & B17 & B21 & B22 & B4 & B3 & BSH & S88 & S80 & S72 & S64 & S56 & S48 &
        N24 & N16 & N8 & N0 & E40 & E32 & E24 & E16 & E8 & BRI48 & BM1 & BM2 & BST2 & BFR & BG).
  - exact gb_stk.
  - replace (SP - 400 + 88) with (SP + -312) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 80) with (SP + -320) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 72) with (SP + -328) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 64) with (SP + -336) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 56) with (SP + -344) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 400 + 48) with (SP + -352) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 24) with (SP + -280) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 16) with (SP + -288) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 8) with (SP + -296) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - replace (SP - 304 + 0) with (SP + -304) by ring. apply gb_slot3; [reflexivity | lia | lia].
  - benv Icf.
  - benv Icf144.
  - benv Idpm.
  - benv Igot.
  - benv Ipsz.
  - benv Ips1.
  - benv Ips2.
  - benv Ips3.
  - benv Ips4.
  - benv Ips5.
  - benv Ips6.
  - benv Ips7.
  - benv Ips8.
  - benv Ips9.
  - benv Ips10.
  - benv Ips11.
  - benv Itls1.
  - benv Itls2.
  - benv Itls3.
  - benv Itls4.
  - benv Itls5.
  - apply gb_keep; [zg | cbn; zg | left; cbn; lia | exact Imm1].
  - apply gb_keep; [zg | cbn; zg | left; cbn; lia | exact Imm2].
  - apply gb_keep; [zg | cbn; zg | right; left; cbn; lia | exact Ist2].
  - apply gb_wr; [zg | zg | intros x Hx; unfold gCELLS_B; do 3 right; left; clear - Hx; lia | exact Iwt].
  - apply gb_wr; [zg | zg | intros x Hx; unfold gCELLS_B; right; left; clear - Hx; lia |].
    intros d k Hd Hk. replace (CA + 2584 + d) with (CA + (2584 + d)) by ring. apply Iwc; lia.
  - exact (FRI 2 ltac:(lia)).
  - exact (FRI 3 ltac:(lia)).
  - exact (FRI 4 ltac:(lia)).
  - exact (FRI 6 ltac:(lia)).
  - apply gb_wr; [zg | zg | intros x Hx; unfold gCELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
  - benv Iprem.
  - apply gb_wr; [zg | zg | intros x Hx; unfold gCELLS_B; do 4 right; left; clear - Hx; lia | exact Iwsh].
  - exists R2, mB. split; [exact Hms|]. split; [unfold EC; repeat split; first [assumption | (rewrite B10; f_equal; unfold FAv; ring)]|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B8|]. split; [exact B21|]. split; [exact B22|]. split; [exact B4|]. split; [exact B3|].
    split; [|split; [exact BFR | exact BG]].
    unfold gPB. split; [exact BSH|].
    split; [exact S88|]. split; [exact S80|]. split; [exact S72|]. split; [exact S64|]. split; [exact S56|]. split; [exact S48|].
    split; [exact N24|]. split; [exact N16|]. split; [exact N8|]. split; [exact N0|].
    split; [exact E40|]. split; [exact E32|]. split; [exact E24|]. split; [exact E16|]. split; [exact E8|].
    split; [exact BRI48|]. split; [exact BM1|]. split; [exact BM2|]. exact BST2.
Qed.

(* [comment removed for export] *)
Definition gCHB (x : Z) : Prop :=
  SP - 2048 <= x < SP - 272 \/ SHv <= x < SHv + 32768 \/ RIv + 48 <= x < RIv + 56 \/ CA + 2584 <= x < CA + 2592 \/ T + 2872 <= x < T + 2888.
#[using="Type"] Lemma gchb_chc : forall x, gCHB x -> gCHC x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x H. unfold gCHB in H. unfold gCHC. destruct H as [H|[H|[H|[H|H]]]].
  - left. clear - H. lia.
  - do 6 right. left. exact H.
  - do 2 right. left. clear - H. lia.
  - right. left. clear - H. lia.
  - do 3 right. left. exact H.
Qed.
#[using="ND RBv Hc HND HSP HCA HCT HSB HSEP HO HK HENV"] Lemma gfa_sep : forall x, gCELLS_B x -> ~ (FAv <= x < FAv + 262144).
Proof. LiaFast.lf_pins (fun (ND RBv Hc HND HSP HCA HCT HSB HSEP HO HK HENV : LiaFast.U) => LiaFast.u0).
  intros x Hx. unfold gCELLS_B in Hx. destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]].
  - zg1 Hx.
  - pose proof HSEP as D. pose proof gfu_geo as G. clear - G D Hx. lia.
  - zg1 Hx.
  - pose proof HSEP as D. pose proof gfu_geo as G. clear - G D Hx. lia.
  - zg1 Hx.
  - zg1 Hx.
  - intro F. apply (HENV x Hx). unfold gCHC. do 5 right. left. exact F.
Qed.

Section SC.
Variables (mB mC0' : word -> option byte).
Hypothesis HPB : gPB mB.
Hypothesis HFB : gFRB mB0' mB.
Hypothesis HC0 : agree_on gCELLS_C mC0' (kz mB FAv 262144).

#[using="ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HC0"] Lemma gc_of_mB : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> gCELLS_B x) -> rd mB a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HS H. apply (rd_agree gCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | exact Ha | lia | intros x Hx; left; exact (HS x Hx) |].
  apply (rd_frame mB); [exact Ha | lia | intros x Hx; apply kz_out; [lia | exact (gfa_sep x (HS x Hx))] | exact H].
Qed.
#[using="ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0"] Lemma gc_of_mB0' : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> gCELLS_B x /\ ~ gCHB x) -> rd mB0' a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (ND RBv FAv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HS H. apply gc_of_mB; [exact Ha | exact Hw | intros x Hx; exact (proj1 (HS x Hx)) |].
  destruct HFB as [FR _]. apply (rd_frame mB0'); [exact Ha | lia | | exact H].
  intros x Hx. destruct (HS x Hx) as [_ N]. unfold gCHB in N.
  apply FR; [lia | intro F; apply N; left; exact F | intro F; apply N; right; left; exact F | intro F; apply N; do 2 right; left; exact F
            | intro F; apply N; do 3 right; left; exact F | intro F; apply N; do 4 right; exact F].
Qed.
#[using="mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HMA mB0' HB0 mB HFB HC0"] Lemma gc_env : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> gENVC x) -> rd m a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (mA0 regs CA ND c SB SP T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v Ha Hw HE H. apply gc_of_mB0'; [exact Ha | exact Hw | | apply gb_env; assumption].
  intros x Hx. split; [unfold gCELLS_B; do 6 right; exact (HE x Hx) | intro F; exact (HENV x (HE x Hx) (gchb_chc x F))].
Qed.
(* [comment removed for export] *)
#[using="CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0"] Lemma gc_slot : forall k v, -272 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v -> rd mC0' (SP + k) 8 v.
Proof. LiaFast.lf_pins (fun (CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros k v K1 K2 H. apply gc_of_mB0'; [zg2 K1 K2 | cbn; zg2 K1 K2 | | exact H].
  intros x Hx. cbn in Hx. split; [unfold gCELLS_B; left; zg3 K1 K2 Hx | unfold gCHB; zg3 K1 K2 Hx].
Qed.
(* [comment removed for export] *)
#[using="m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs Iri HMA mB0' HB0 mB HFB HC0"] Lemma gc_ri : forall i, 1 <= i < 16 -> i <> 6 -> rd mC0' (RIv + 8 * i) 8 0.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs Iri HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i Hi Hi6. pose proof gfu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D3 : RIv + 128 <= SHv \/ SHv + 32768 <= RIv) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply gc_of_mB0'; [zg1 Hi | cbn; zg1 Hi | |].
  - intros x Hx. cbn in Hx. split; [unfold gCELLS_B; do 2 right; left; clear - Hi Hx; lia |].
    unfold gCHB. pose proof gfu_geo as G. clear - G Hi Hi6 Hx D1 D2 D3. lia.
  - apply gb_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))].
Qed.
#[using="mA0 regs RBv FAv HMA mB0' HB0 mB HFB HC0"] Lemma gc_wr : forall a n, 0 <= a -> a + n <= 2^63 -> (forall x, a <= x < a + n -> gCELLS_B x) -> wr m a n -> wr mC0' a n.
Proof. LiaFast.lf_pins (fun (mA0 regs RBv FAv HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a n Ha Hn HS H. apply (wr_agree gCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | exact Ha | lia | intros x Hx; left; exact (HS x Hx) |].
  apply (wr_grows mB); [apply kz_grows|]. apply (wr_grows mB0'); [exact (proj2 HFB)|]. apply gb_wr; assumption.
Qed.
#[using="m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA mB0' HB0 mB HFB HC0"] Lemma gc_stk : stk_ok SEGS mC0' (wa SP) 2048.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND c SB TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HSTK HCA HCT HSB HO HK HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  apply (stk_ok_agree gCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | zg | zg | intros x Hx; left; unfold gCELLS_B; left; exact Hx |].
  apply (stk_ok_grows mB); [apply kz_grows|]. apply (stk_ok_grows mB0'); [exact (proj2 HFB)|]. exact gb_stk.
Qed.
#[using="CA ND SP TP K TSDA PT T RIv RBv SHv SHFv Hc HND HSP HCA HCT HSB HO HK mB HC0"] Lemma gc_wfa : wr mC0' FAv 262144.
Proof. LiaFast.lf_pins (fun (CA ND SP TP K TSDA PT T RIv RBv SHv SHFv Hc HND HSP HCA HCT HSB HO HK mB HC0 : LiaFast.U) => LiaFast.u0).
  apply (wr_agree gCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | zg | zg | intros x Hx; right; exact Hx |].
  apply kz_wr; zg.
Qed.
#[using="m mA0 regs CA ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HIMG HMA mB0' HB0 mB HFB HC0"] Lemma gc_img : forall i, 65536 <= i < 143360 -> mC0' (Z_to_bv 64 i) = None.
Proof. LiaFast.lf_pins (fun (m mA0 regs CA ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HIMG HMA mB0' HB0 mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i Hi. assert (HE : gENVC i) by (unfold gENVC; left; exact Hi).
  assert (HCB : gCELLS_B i) by (unfold gCELLS_B; do 6 right; exact HE).
  apply (agree_none gCELLS_C mC0' (kz mB FAv 262144)); [exact HC0 | clear - Hi; lia | left; exact HCB |].
  change (Z_to_bv 64 i) with (wa i). rewrite kz_out; [| clear - Hi; lia | exact (gfa_sep i HCB)].
  destruct HFB as [FR _].
  assert (N : ~ gCHB i) by (intro F; exact (HENV i HE (gchb_chc i F))). unfold gCHB in N.
  rewrite FR; [| clear - Hi; lia | intro F; apply N; left; exact F | intro F; apply N; right; left; exact F | intro F; apply N; do 2 right; left; exact F
               | intro F; apply N; do 3 right; left; exact F | intro F; apply N; do 4 right; exact F].
  rewrite (HB0 i ltac:(clear - Hi; lia) HCB). rewrite gmB0_env; [| clear - Hi; lia | exact (HENV i HE)]. exact (HIMG i Hi).
Qed.

(* [comment removed for export] *)
#[using="CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0"] Lemma gc_riw : forall i v, 0 <= i < 16 -> i <> 6 -> rd mB0' (RIv + 8 * i) 8 v -> rd mC0' (RIv + 8 * i) 8 v.
Proof. LiaFast.lf_pins (fun (CA ND SP TP K TSDA PT T RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros i v Hi Hi6 H. pose proof gfu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D3 : RIv + 128 <= SHv \/ SHv + 32768 <= RIv) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply gc_of_mB0'; [zg1 Hi | cbn; zg1 Hi | | exact H].
  intros x Hx. cbn in Hx. split; [unfold gCELLS_B; do 2 right; left; clear - Hi Hx; lia |].
  unfold gCHB. pose proof gfu_geo as G. clear - G Hi Hi6 Hx D1 D2 D3. lia.
Qed.
(* [comment removed for export] *)
#[using="ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0"] Lemma gc_cache : forall a w v, CA <= a -> a + Z.of_nat w <= CA + 2584 -> rd mB0' a w v -> rd mC0' a w v.
Proof. LiaFast.lf_pins (fun (ND c SB SP TP K TSDA PT T RIv RBv FAv SHv SHFv Hc HND HSP HCA HCT HSB HSEP HO HK HENV HSHs mB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros a w v K1 K2 H. pose proof gfu_d_ri_t as D1. pose proof HSEP as D2.
  assert (D4 : T + 4096 <= SHv \/ SHv + 32768 <= T) by (unfold shsep in HSHs; clear - HSHs; tauto).
  apply gc_of_mB0'; [zg2 K1 K2 | zg2 K1 K2 | | exact H].
  intros x Hx. split; [unfold gCELLS_B; right; left; clear - K1 K2 Hx; lia |].
  unfold gCHB. pose proof gfu_geo as G. clear - G K1 K2 Hx D1 D2 D4. lia.
Qed.

Ltac zc := cbv; let X := fresh in intro X; discriminate X.
Ltac cenv H := apply gc_env; [zg | cbn; zg | intros x Hx; cbn in Hx; envc Hx | exact H].

#[using="m mA0 ND st st2 K TSDA PT mm1 mm2 RIv SHv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf ISB IRIB Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HIMG HMA mB0' HB0 mB HPB HFB HC0"] Lemma gstageC : forall R2', getr R2' 1 = wa 481796 -> getr R2' 2 = wa (SP - 448) -> getr R2' 4 = wa TP -> getr R2' 8 = wa 262144 ->
  getr R2' 10 = wa FAv -> getr R2' 21 = wa (sz_tbl c) -> getr R2' 22 = wa 923480 ->
  exists R3 m3, msteps SEGS (mkst R2' (wa 0x73c48) mC0' rom) (mkst R3 (wa 0x43f08) m3 rom) /\
    getr R3 (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\ getr R3 (Z_to_bv 5 (Z.of_nat 10)) = wa RBv /\
    (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    (forall k, In k [3; 4]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr R2' (Z_to_bv 5 (Z.of_nat k))) /\
    INV_G m3 CA SB c (sz_tbl c) (mc_tbl c / 2) (262144 / (sz_tbl c)) 1 /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (SHFv <= x < SHFv + 32768) -> ~ (T + 2872 <= x < T + 2888) ->
        ~ (FAv <= x < FAv + 262144) -> ~ owned_C CA SB c x -> m3 (wa x) = mC0' (wa x)) /\ mem_grows mC0' m3.
Proof. LiaFast.lf_pins (fun (m mA0 ND st st2 K TSDA PT mm1 mm2 RIv SHv Hc HND HSP HSTK HCA HCT HSB HSEP HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf ISB IRIB Icf Icf144 Ips1 Ips2 Ips3 Ips4 Ips5 Ips6 Ips7 Ips8 Ips9 Ips10 Ips11 Itls1 Itls2 Itls3 Itls4 Itls5 HIMG HMA mB0' HB0 mB HPB HFB HC0 : LiaFast.U) => LiaFast.u0).
  intros R2' Q1 Q2 Q4 Q8 Q10 Q21 Q22.
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  destruct HPB as (BSH & S88 & S80 & S72 & S64 & S56 & S48 & N24 & N16 & N8 & N0 & E40 & E32 & E24 & E16 & E8 & BRI48 & BM1 & BM2 & BST2).
  set (mm1' := (mm1 + 1) mod 2^64). set (mm2' := (mm2 + 262144) mod 2^64).
  assert (Hst' : 0 <= mm1' < 2^64 /\ 0 <= mm2' < 2^64) by (unfold mm1', mm2'; split; apply Z.mod_pos_bound; lia).
  assert (W : forall a v, SP - 2048 <= a -> a + 8 <= SP -> rd mB a 8 v -> rd mC0' a 8 v).
  { intros a v K1 K2 H. apply gc_of_mB; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold gCELLS_B; left; clear - K1 K2 Hx; lia | exact H]. }
  assert (WT : forall a v, T + 2872 <= a -> a + 8 <= T + 2888 -> rd mB a 8 v -> rd mC0' a 8 v).
  { intros a v K1 K2 H. apply gc_of_mB; [zg2 K1 K2 | cbn; zg2 K1 K2 | intros x Hx; cbn in Hx; unfold gCELLS_B; do 3 right; left; clear - K1 K2 Hx; lia | exact H]. }
  destruct (gsegC1 rom mC0' R2' c SB SP TP K TSDA PT T mm1' mm2' Hcr5 HSP HO HSB HK HSHF Hst' Q1 Q2 Q4 Q8 Q10 Q21 Q22)
    as (R3' & mC1 & Hms1 & C2r & C4 & C8 & C10 & C11 & C12 & C13 & C18 & C19 & C21 & C22 & C3 & CSHF & CRI24 & CM1 & CM2 & CFR & CG).
  - exact gc_stk.
  - apply W; [clear; lia | clear; lia | exact S88].
  - apply W; [clear; lia | clear; lia | exact S80].
  - apply W; [clear; lia | clear; lia | exact S72].
  - apply W; [clear; lia | clear; lia | exact S64].
  - apply W; [clear; lia | clear; lia | exact S56].
  - apply W; [clear; lia | clear; lia | exact S48].
  - apply W; [clear; lia | clear; lia | exact N24].
  - apply W; [clear; lia | clear; lia | exact N16].
  - apply W; [clear; lia | clear; lia | exact N8].
  - apply W; [clear; lia | clear; lia | exact N0].
  - apply W; [clear; lia | clear; lia | exact E40].
  - apply W; [clear; lia | clear; lia | exact E32].
  - apply W; [clear; lia | clear; lia | exact E24].
  - apply W; [clear; lia | clear; lia | exact E16].
  - apply W; [clear; lia | clear; lia | exact E8].
  - cenv Icf.
  - cenv Icf144.
  - cenv Ips1.
  - cenv Ips2.
  - cenv Ips3.
  - cenv Ips4.
  - cenv Ips5.
  - cenv Ips6.
  - cenv Ips7.
  - cenv Ips8.
  - cenv Ips9.
  - cenv Ips10.
  - cenv Ips11.
  - cenv Itls1.
  - cenv Itls2.
  - cenv Itls3.
  - cenv Itls4.
  - cenv Itls5.
  - apply WT; [clear; lia | clear; lia | unfold mm1'; apply rd_mod64; exact BM1].
  - apply WT; [clear; lia | clear; lia | unfold mm2'; apply rd_mod64; exact BM2].
  - apply gc_wr; [zg | zg | intros x Hx; unfold gCELLS_B; do 3 right; left; clear - Hx; lia | exact Iwt].
  - pose proof (gc_ri 4 ltac:(lia) ltac:(lia)) as X. replace (RIv + 8 * 4) with (RIv + 32) in X by ring. exact X.
  - apply gc_wr; [zg | zg | intros x Hx; unfold gCELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
  - apply gc_wr; [zg | zg | intros x Hx; unfold gCELLS_B; do 5 right; left; clear - Hx; lia | exact Iwshf].
  - (* [comment removed for export] *)
    pose proof gfu_d_ri_t as D1. pose proof HSEP as D2.
    assert (D3f : RIv + 128 <= SHFv \/ SHFv + 32768 <= RIv) by (unfold shsep in HSHF; clear - HSHF; tauto).
    assert (D4f : T + 4096 <= SHFv \/ SHFv + 32768 <= T) by (unfold shsep in HSHF; clear - HSHF; tauto).
    assert (K1 : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 ->
              (forall x, a <= x < a + Z.of_nat w -> ~ (SP - 2048 <= x < SP - 320) /\ ~ (SHFv <= x < SHFv + 32768) /\ ~ (RIv + 24 <= x < RIv + 32) /\ ~ (T + 2872 <= x < T + 2888)) ->
              rd mC0' a w v -> rd mC1 a w v).
    { intros a w v Ha Hw HS H. apply (rd_frame mC0'); [exact Ha | clear - Hw; lia | | exact H].
      intros x Hx. destruct (HS x Hx) as (N1 & N2 & N3 & N4). apply CFR; [clear - Ha Hw Hx; lia | exact N1 | exact N2 | exact N3 | exact N4]. }
    assert (KS : forall k v, -272 <= k -> k + 8 <= 0 -> rd mB0' (SP + k) 8 v -> rd mC1 (SP + k) 8 v).
    { intros k v K1' K2' H. apply K1; [zg2 K1' K2' | cbn; zg2 K1' K2' | | apply gc_slot; assumption].
      intros x Hx. cbn in Hx. pose proof gfu_geo as G. clear - G K1' K2' Hx. lia. }
    assert (KE : forall a w v, 0 <= a -> a + Z.of_nat w <= 2^63 -> (forall x, a <= x < a + Z.of_nat w -> gENVC x) -> rd m a w v -> rd mC1 a w v).
    { intros a w v Ha Hw HE H. apply K1; [exact Ha | exact Hw | | apply gc_env; assumption].
      intros x Hx. pose proof (HENV x (HE x Hx)) as N. unfold gCHC in N.
      split; [intro F; apply N; left; clear - F; lia|]. split; [intro F; apply N; do 7 right; exact F|].
      split; [intro F; apply N; do 2 right; left; clear - F; lia | intro F; apply N; do 3 right; left; exact F]. }
    assert (KR : forall i v, 0 <= i < 16 -> i <> 6 -> i <> 3 -> rd mB0' (RIv + 8 * i) 8 v -> rd mC1 (RIv + 8 * i) 8 v).
    { intros i v Hi H6 H3 H. apply K1; [zg1 Hi | cbn; zg1 Hi | | apply gc_riw; assumption].
      intros x Hx. cbn in Hx. pose proof gfu_geo as G. clear - G Hi H3 Hx D1 D3f. lia. }
    assert (KR0 : forall i, 1 <= i < 16 -> i <> 6 -> i <> 3 -> rd mC1 (RIv + 8 * i) 8 0).
    { intros i Hi H6 H3. apply KR; [clear - Hi; lia | exact H6 | exact H3 |].
      apply gb_keep; [zg1 Hi | cbn; zg1 Hi | right; right; cbn; zg1 Hi | exact (Iri i ltac:(lia))]. }
    assert (KC : forall a w v, CA <= a -> a + Z.of_nat w <= CA + 2584 -> rd mB0' a w v -> rd mC1 a w v).
    { intros a w v K1' K2' H. apply K1; [zg2 K1' K2' | zg2 K1' K2' | | apply gc_cache; assumption].
      intros x Hx. pose proof gfu_geo as G. clear - G K1' K2' Hx D1 D2 D4f. lia. }
    assert (KW : forall a n, wr mC0' a n -> wr mC1 a n) by (intros a n H; exact (wr_grows mC0' mC1 a n CG H)).
    destruct gb_ic as [BIC1 BIC2].
    destruct (gsegC2 rom mC1 R3' CA ND c SB SP 0 st
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
                (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27))))
                Hc HND HSP HCA HSB HSEP ltac:(clear - Hvals; lia)
                ltac:(regzG; exact C2r) ltac:(regzG; exact C8) ltac:(regzG; exact C10) ltac:(regzG; exact C11) ltac:(regzG; exact C12) ltac:(regzG; exact C13)
                ltac:(regzG; exact C19) ltac:(regzG; exact C21))
      as (R3 & m3 & Hms2 & F2 & F10 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & FK & FINV & FFR & FG).
    + exact (stk_ok_grows mC0' mC1 (wa SP) 2048 CG gc_stk).
    + replace (SP - 216) with (SP + -216) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 224) with (SP + -224) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 232) with (SP + -232) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 240) with (SP + -240) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 248) with (SP + -248) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 256) with (SP + -256) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 264) with (SP + -264) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 272) with (SP + -272) by ring. apply KS; [zc | zc | apply gb_slot3; [reflexivity | zc | zc]].
    + replace (SP - 88) with (SP + -88) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 96) with (SP + -96) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 104) with (SP + -104) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 112) with (SP + -112) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 120) with (SP + -120) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 128) with (SP + -128) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 136) with (SP + -136) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 144) with (SP + -144) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 152) with (SP + -152) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 160) with (SP + -160) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 168) with (SP + -168) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 176) with (SP + -176) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 184) with (SP + -184) by ring. apply KS; [zc | zc | apply gb_slot2; [reflexivity | zc | zc]].
    + replace (SP - 72) with (SP + -72) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 64) with (SP + -64) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 56) with (SP + -56) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 48) with (SP + -48) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 40) with (SP + -40) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 32) with (SP + -32) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 24) with (SP + -24) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 16) with (SP + -16) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + replace (SP - 8) with (SP + -8) by ring. apply KS; [zc | zc | apply gb_slot1; [reflexivity | zc | zc]].
    + repeat match goal with |- _ /\ _ => split end; first [exact (proj1 (bvu_rng _)) | exact (proj2 (bvu_rng _))].
    + pose proof (KR 0 1152921504606846976 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. apply X. exact gb_mu.
    + exact (KR0 2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 5 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + apply K1; [zg | cbn; zg | |].
      * intros x Hx. cbn in Hx. pose proof gfu_geo as G. clear - G Hx D1 D3f. lia.
      * apply gc_of_mB; [zg | cbn; zg | intros x Hx; cbn in Hx; unfold gCELLS_B; do 2 right; left; clear - Hx; lia | exact BRI48].
    + exact (KR0 7 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + exact (KR0 9 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + apply KW. apply gc_wr; [zg | zg | intros x Hx; unfold gCELLS_B; do 2 right; left; clear - Hx; lia | exact Iwri].
    + apply KC; [clear - Hcr5; lia | cbn; clear - Hcr5; lia | exact BIC1].
    + apply KC; [clear - Hcr5; lia | cbn; clear - Hcr5; lia | exact BIC2].
    + apply KW. apply gc_wr; [zg | zg | intros x Hx; unfold gCELLS_B; right; left; clear - Hx; lia | exact Iwc].
    + apply KE; [clear; lia | cbn; clear; lia | intros x Hx; cbn in Hx; envc Hx | exact ISB].
    + apply KE; [clear; lia | cbn; clear; lia | intros x Hx; cbn in Hx; envc Hx | exact IRIB].
    + apply KC; [clear; lia | cbn; clear; lia |]. apply gb_keep; [zg | cbn; zg | right; left; cbn; clear; lia | exact Ist].
    + apply KW. exact gc_wfa.
    + intros i Hi. change (Z_to_bv 64 i) with (wa i).
      assert (HE : gENVC i) by (unfold gENVC; left; exact Hi). pose proof (HENV i HE) as N. unfold gCHC in N.
      rewrite CFR; [exact (gc_img i Hi) | clear - Hi; lia | intro F; apply N; left; clear - F; lia | intro F; apply N; do 7 right; exact F
                   | intro F; apply N; do 2 right; left; clear - F; lia | intro F; apply N; do 3 right; left; exact F].
    + exists R3, m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
      split; [exact F2|]. split; [exact F10|].
      split.
      { intros k Hk. cbn [In] in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
          first [rewrite F1 | rewrite F8 | rewrite F9 | rewrite F18 | rewrite F19 | rewrite F20 | rewrite F21 | rewrite F22 | rewrite F23
                | rewrite F24 | rewrite F25 | rewrite F26 | rewrite F27]; apply wa_u. }
      split.
      { intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
        - rewrite (FK 3%nat ltac:(left; reflexivity)). exact C3.
        - rewrite (FK 4%nat ltac:(right; left; reflexivity)). rewrite C4. symmetry. regzH Q4. exact Q4. }
      split; [exact FINV|].
      split; [| exact (mem_grows_trans _ _ _ CG FG)].
      intros x Hx N1 N2 N3 N4 N5. rewrite FFR; [| exact Hx | exact N4 | exact N5].
      apply CFR; [exact Hx | intro F; apply N1; clear - F; lia | exact N2 | | exact N3].
      intro F. apply N5. unfold owned_C. right. left. clear - F. lia.
Qed.
End SC.
End SB.
End FU.

(* [comment removed for export] *)
Section VA.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP sz0 st : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Hypothesis Hc : c = cls_of ND.
Hypothesis HND : 1 <= ND <= 65536.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hvals : 0 <= sz0 < 2^64 /\ 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 0.
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 sz0.
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis Iri : forall i, 0 <= i < 16 -> rd m (RIv + 8 * i) 8 0.
Hypothesis Iwri : wr m RIv 128.
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Idpm : rd m 1534444 1 0.

#[using="ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm"] Lemma gstageA : exists R1 mA, msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R1 (wa 0x73c44) mA rom) /\
  EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  gMA_OK m mA regs SP CA c RIv RBv FAv /\
  (forall i, 1 <= i <= 31 -> rd mA (CA + 80 * i + 4) 4 (mc_tbl i) /\ rd mA (CA + 80 * i + 8) 8 (sz_tbl i)) /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
     ~ (RIv <= x < RIv + 8) -> mA (wa x) = m (wa x)).
Proof. LiaFast.lf_pins (fun (ND sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  assert (G : 2^46 <= SP <= 2^47 /\ 0 <= CA /\ CA + 4096 <= SP - 2048 /\ 0 <= RIv /\ RIv + 128 <= SP - 2048 /\ (CA + 4096 <= RIv \/ RIv + 128 <= CA))
    by (unfold RIv; clear - Hcr5 HSP HCA HSB HSEP; lia).
  destruct (gsegA rom m regs CA ND c SB SP sz0 st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem
              ltac:(pose proof (Iri 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X)
              ltac:(pose proof (Iri 2 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 4 ltac:(lia)) as X; exact X)
              ltac:(pose proof (Iri 6 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 7 ltac:(lia)) as X; exact X)
              Iwri Igot Ipsz Icf Idpm)
    as (R1 & mA & Hms & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A21 & A22 & AK & EMA).
  exists R1, mA. split; [exact Hms|]. split; [unfold EC; repeat split; assumption|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [exact A21|]. split; [exact A22|]. split; [exact AK|].
  fold RIv RBv FAv in EMA. rewrite EMA. clear - G Hcr5.
  split; [|split].
  - unfold gMA_OK. split; [|split; [|split; [|split; [|split; [|split]]]]].
    + intros k v Hk K1 K2. apply gmAc_rd3; [lia | exact Hk | exact K1 | exact K2].
    + intros k v Hk K1 K2. apply gmAc_rd2; [lia | lia | lia | exact Hk | exact K1 | exact K2].
    + intros k v Hk K1 K2. apply gmAc_rd1; [lia | lia | lia | lia | lia | exact Hk | exact K1 | exact K2].
    + intros x Hx Q1 Q2 Q3. apply gmAc_frame_f; [lia | lia | lia | lia | lia | exact Hx | exact Q1 | exact Q2 | exact Q3].
    + apply gmAc_rdRI; lia.
    + apply gmAc_rd_ic; [lia | lia | lia | lia | lia | tauto | lia].
    + apply gmAc_grows.
  - intros i Hi. apply gmAc_rd_ic; [lia | lia | lia | lia | lia | tauto | exact Hi].
  - intros x Hx Q1 Q2 Q3. apply gmAc_frame_f; [lia | lia | lia | lia | lia | exact Hx | exact Q1 | exact Q2 | exact Q3].
Qed.
End VA.

(* [comment removed for export] *)
Lemma gmAd_grows : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  mem_grows m (gmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27).
Proof.
  intros. unfold gmAd.
  apply (mem_grows_trans _ _ _ (wchainS_grows (L1a c CA v1 v8 v9 v18 v19 v20) m SP)).
  apply (mem_grows_trans _ _ _ (wchainS_grows (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP)).
  apply (mem_grows_trans _ (wbytes (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))).
  - apply grows_wb. apply mem_grows_refl.
  - apply wchainS_grows.
Qed.
Lemma gmAd_rd3 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> wl_chk (gL3a c CA n RI RB FA) k 8 = Some v -> -2048 <= k -> k + 8 <= 0 ->
  rd (gmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof. intros. unfold gmAd. apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | assumption]. Qed.
Lemma gmAd_rd2 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 -> wl_chk (L2a c CA n g21 g22 g23 g24 g25 g26 g27) k 8 = Some v -> -208 <= k -> k + 8 <= 0 ->
  rd (gmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold gmAd.
  apply (rd_frame (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    apply wb_other; [lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma gmAd_rd1 : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  wl_chk (L1a c CA v1 v8 v9 v18 v19 v20) k 8 = Some v -> -80 <= k -> k + 8 <= 0 ->
  rd (gmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) (SP + k) 8 v.
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 k v HSP H1 H2 Hc Hk1 Hk2. unfold gmAd.
  apply (rd_frame (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx.
    rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) (-208)); [| lia | lia | reflexivity | reflexivity | lia | lia].
    rewrite wb_other; [| lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
    apply (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-208) (-80)); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply rd_wchainS; [lia | lia | reflexivity | lia | cbn; lia | lia | exact Hc].
Qed.
Lemma gmAd_frame_f : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= 2^63 -> 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (RI <= x < RI + 8) ->
  gmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 (wa x) = m (wa x).
Proof.
  intros m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27 x HSP H3 H4 Hx Q1 Q3. unfold gmAd.
  rewrite (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite wb_other; [| exact Hx | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  rewrite (wchainS_frame_in (L2a c CA n g21 g22 g23 g24 g25 g26 g27) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  rewrite (wchainS_frame_in (L1a c CA v1 v8 v9 v18 v19 v20) _ SP (-2048) 0); [| lia | lia | reflexivity | reflexivity | exact Hx | lia].
  reflexivity.
Qed.
Lemma gmAd_rdRI : forall m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27,
  2^46 <= SP <= 2^47 -> 0 <= RI -> RI + 128 <= SP - 2048 ->
  rd (gmAd m SP CA c n RI RB FA v1 v8 v9 v18 v19 v20 g21 g22 g23 g24 g25 g26 g27) RI 8 1152921504606846976.
Proof.
  intros. unfold gmAd.
  apply (rd_frame (wbytes (wchainS (wchainS m SP (L1a c CA v1 v8 v9 v18 v19 v20)) SP (L2a c CA n g21 g22 g23 g24 g25 g26 g27)) (wa RI) (word_to_le_bytes 8 (wa 1152921504606846976)))); [lia | cbn; lia | |].
  - intros x Hx. cbn in Hx. apply (wchainS_frame_in (gL3a c CA n RI RB FA) _ SP (-2048) 0); [lia | lia | reflexivity | reflexivity | lia | lia].
  - apply wb_rd_hit; [lia | lia | cbn; lia].
Qed.

Section VB.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB SP st : Z).
Let RIv := SB + 137438953472 + 128 * c.
Let RBv := SB + 4294967296 * c.
Let FAv := SB + 4294967296 * c + 3758096384.
Hypothesis Hc : c = cls_of ND.
Hypothesis HND : 1 <= ND <= 65536.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis Hvals : 0 <= st < 2^64.
Hypothesis Icnt : rd m (CA + 80 * c) 4 0.
Hypothesis Imc : rd m (CA + 80 * c + 4) 4 (mc_tbl c).
Hypothesis Isz : rd m (CA + 80 * c + 8) 8 (sz_tbl c).
Hypothesis Ist : rd m (CA + 2576) 8 st.
Hypothesis Iwc : wr m CA 2592.
Hypothesis Iri : forall i, 0 <= i < 16 -> rd m (RIv + 8 * i) 8 0.
Hypothesis Iwri : wr m RIv 128.
Hypothesis ISB : rd m 923512 8 SB.
Hypothesis IRIB : rd m 923528 8 (SB + 137438953472).
Hypothesis Irtoi : rd m 923520 4 4294967295.
Hypothesis Iprem : rd m 923536 1 0.
Hypothesis Igot : rd m 904176 8 1525856.
Hypothesis Ipsz : rd m 1525856 8 4096.
Hypothesis Icf : rd m 904192 8 1534184.
Hypothesis Idpm : rd m 1534444 1 0.

#[using="ND st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm"] Lemma gstageA' : exists R1 mA, msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R1 (wa 0x73c44) mA rom) /\
  EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
  getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
  (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
  gMA_OK m mA regs SP CA c RIv RBv FAv /\
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (RIv <= x < RIv + 8) -> mA (wa x) = m (wa x)).
Proof. LiaFast.lf_pins (fun (ND st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP Hvals Icnt Imc Isz Ist Iwc Iri Iwri ISB IRIB Irtoi Iprem Igot Ipsz Icf Idpm : LiaFast.U) => LiaFast.u0).
  assert (Hcr5 : 1 <= c <= 30) by (rewrite Hc; apply cls_of_rng; exact HND).
  assert (G : 2^46 <= SP <= 2^47 /\ 0 <= CA /\ CA + 4096 <= SP - 2048 /\ 0 <= RIv /\ RIv + 128 <= SP - 2048 /\ (CA + 4096 <= RIv \/ RIv + 128 <= CA))
    by (unfold RIv; clear - Hcr5 HSP HCA HSB HSEP; lia).
  assert (Hsz : 0 <= sz_tbl c < 2^64) by (destruct (gsz_rng c Hcr5) as (Hq & _); clear - Hq; lia).
  destruct (gsegA' rom m regs CA ND c SB SP (sz_tbl c) st Hc HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP (conj Hsz Hvals) Icnt Imc Isz Ist Iwc ISB IRIB Irtoi Iprem
              ltac:(pose proof (Iri 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X)
              ltac:(pose proof (Iri 2 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 4 ltac:(lia)) as X; exact X)
              ltac:(pose proof (Iri 6 ltac:(lia)) as X; exact X) ltac:(pose proof (Iri 7 ltac:(lia)) as X; exact X)
              Iwri Igot Ipsz Icf Idpm)
    as (R1 & mA & Hms & A1 & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A21 & A22 & AK & EMA).
  exists R1, mA. split; [exact Hms|]. split; [unfold EC; repeat split; assumption|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A8|]. split; [exact A21|]. split; [exact A22|]. split; [exact AK|].
  fold RIv RBv FAv in EMA. rewrite EMA.
  assert (FRd : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (RIv <= x < RIv + 8) ->
            gmAd m SP CA c (mc_tbl c / 2) RIv RBv FAv
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26))))
              (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (wa x) = m (wa x)).
  { intros x Hx Q1 Q3. apply gmAd_frame_f; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hx | exact Q1 | exact Q3]. }
  split; [|exact FRd].
  unfold gMA_OK. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros k v Hk K1 K2. apply gmAd_rd3; [clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros k v Hk K1 K2. apply gmAd_rd2; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros k v Hk K1 K2. apply gmAd_rd1; [clear - G; lia | clear - G; lia | clear - G; lia | exact Hk | exact K1 | exact K2].
  - intros x Hx Q1 _ Q3. exact (FRd x Hx Q1 Q3).
  - apply gmAd_rdRI; clear - G; lia.
  - split.
    + apply (rd_frame m); [clear - G Hcr5; lia | cbn; clear - G Hcr5; lia | | exact Imc].
      intros x Hx. cbn in Hx. apply FRd; [clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia].
    + apply (rd_frame m); [clear - G Hcr5; lia | cbn; clear - G Hcr5; lia | | exact Isz].
      intros x Hx. cbn in Hx. apply FRd; [clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia | clear - G Hcr5 Hx; lia].
  - apply gmAd_grows.
Qed.
End VB.
