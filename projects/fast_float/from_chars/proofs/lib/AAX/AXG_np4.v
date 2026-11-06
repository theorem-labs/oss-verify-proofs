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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0rz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0rz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_nprz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_nprz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ng0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ng0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_ngtz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma wb_rd_hit_s : forall m SP c w v, (1 <= w <= 8)%nat -> 2^20 <= SP <= 2^47 -> 0 <= c <= 8192 ->
  rd (wbytes m (wa (SP - c)) (word_to_le_bytes w (wa v))) (SP - c) w v.
Proof. intros m SP c w v Hw HS Hc. apply wb_rd_hit; lia. Qed.
Lemma wb_rd_other_s : forall m SP c w v c' bs, 2^20 <= SP <= 2^47 -> 0 <= c <= 8192 -> (w <= 8)%nat -> 0 <= c' <= 8192 ->
  (length bs <= 8)%nat -> (c' + Z.of_nat w <= c \/ c + Z.of_nat (length bs) <= c') -> rd m (SP - c) w v -> rd (wbytes m (wa (SP - c')) bs) (SP - c) w v.
Proof. intros m SP c w v c' bs HS Hc Hw Hc' Hl Hd H. apply wb_rd_other; [lia | lia | lia | lia | lia | exact H]. Qed.
Ltac rrs HS H := repeat first [
    lazymatch goal with
    | |- rd (wbytes _ (wa (?S - _)) _) (?S - _) _ _ =>
        first [ (apply wb_rd_hit_s; [clear; lia | exact HS | clear; lia])
              | (apply wb_rd_other_s; [exact HS | clear; lia | clear; lia | clear; lia | lenq; clear; lia | lenq; clear; lia | ]) ]
    end
  | (apply wb_rd_hit; [clear; lia | clear - H; lia | lenq; clear - H; lia])
  | (apply wb_rd_other; [clear - H; lia | lenq; clear - H; lia | clear - H; lia | lenq; clear - H; lia | lenq; clear - H; lia | ]) ].
Ltac nsub := rewrite ?addneg; rewrite <- ?Z.sub_add_distr.
Lemma stk_ok_move : forall m SP s K, 0 <= SP < 2^64 -> 0 <= s < 2^64 -> stk_ok SEGS m (wa SP) 2048 ->
  SP - 2048 <= s - K -> s <= SP -> 0 <= K -> stk_ok SEGS m (wa s) K.
Proof. intros m SP s K H1 H2 H H3 H4 H5 a k A1 A2. apply H; rewrite u_wa_small in * by slia; slia. Qed.


(* [comment removed for export] *)
Definition m1c (m : word -> option byte) (SP v1 v8 v9 v18 v19 v20 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (SP - 8)) (word_to_le_bytes 8 (wa (v1)))) (wa (SP - 16)) (word_to_le_bytes 8 (wa (v8)))) (wa (SP - 24)) (word_to_le_bytes 8 (wa (v9)))) (wa (SP - 32)) (word_to_le_bytes 8 (wa (v18)))) (wa (SP - 40)) (word_to_le_bytes 8 (wa (v19)))) (wa (SP - 48)) (word_to_le_bytes 8 (wa (v20))).
Definition m2c (m : word -> option byte) (SP c REC : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (SP - (48 + 8))) (word_to_le_bytes 8 (wa (278424)))) (wa (SP - (48 + 16))) (word_to_le_bytes 8 (wa (c)))) (wa (SP - (48 + 24))) (word_to_le_bytes 8 (wa (REC))).
Definition m3c (m : word -> option byte) (SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (SP - (80 + 8))) (word_to_le_bytes 8 (wa (279672)))) (wa (SP - (80 + 16))) (word_to_le_bytes 8 (wa (REC)))) (wa (SP - (80 + 24))) (word_to_le_bytes 8 (wa (nc)))) (wa (SP - (80 + 32))) (word_to_le_bytes 8 (wa (8)))) (wa (SP - (80 + 40))) (word_to_le_bytes 8 (wa (CA)))) (wa (SP - (80 + 48))) (word_to_le_bytes 8 (wa (923480)))) (wa (SP - (80 + 56))) (word_to_le_bytes 8 (wa (g21)))) (wa (SP - (80 + 64))) (word_to_le_bytes 8 (wa (g22)))) (wa (SP - (80 + 72))) (word_to_le_bytes 8 (wa (g23)))) (wa (SP - (80 + 80))) (word_to_le_bytes 8 (wa (g24)))) (wa (SP - (80 + 88))) (word_to_le_bytes 8 (wa (g25)))) (wa (SP - (80 + 96))) (word_to_le_bytes 8 (wa (g26)))) (wa (SP - (80 + 104))) (word_to_le_bytes 8 (wa (g27)))) (wa (RI)) (word_to_le_bytes 8 (wa (1152921504606846976)))) (wa (RI + 16)) (word_to_le_bytes 8 (wa (-1 * nc + nf))).
Definition m5c (m : word -> option byte) (RI REC CA nc na sz st : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (RI + 72)) (word_to_le_bytes 8 (wa (nc + na)))) (wa (RI)) (word_to_le_bytes 8 (wa (0)))) (wa (REC)) (word_to_le_bytes 4 (wa (nc)))) (wa (REC)) (word_to_le_bytes 4 (wa (nc - 1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))).

Ltac wbo Hx := repeat (rewrite wb_other by first [exact Hx | (lenq; lia) | lia]).

Lemma m1c_frame : forall m SP v1 v8 v9 v18 v19 v20 x, 2^20 <= SP <= 2^47 -> 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) ->
  m1c m SP v1 v8 v9 v18 v19 v20 (wa x) = m (wa x).
Proof. intros m SP v1 v8 v9 v18 v19 v20 x HS Hx H. unfold m1c. wbo Hx. reflexivity. Qed.
Lemma m2c_frame : forall m SP c REC x, 2^20 <= SP <= 2^47 -> 0 <= x < 2^64 -> ~ (SP - 72 <= x < SP - 48) -> m2c m SP c REC (wa x) = m (wa x).
Proof. intros m SP c REC x HS Hx H. unfold m2c. wbo Hx. reflexivity. Qed.
Lemma m3c_frame : forall m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf x, 2^20 <= SP <= 2^47 -> 0 <= RI -> RI + 24 <= 2^64 ->
  0 <= x < 2^64 -> ~ (SP - 184 <= x < SP - 80) -> ~ (RI <= x < RI + 24) -> m3c m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf (wa x) = m (wa x).
Proof. intros m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf x HS HR1 HR2 Hx H1 H2. unfold m3c. wbo Hx. reflexivity. Qed.
Lemma m5c_frame : forall m RI REC CA nc na sz st x, 0 <= RI -> RI + 80 <= 2^64 -> 0 <= REC -> REC + 4 <= 2^64 -> 0 <= CA -> CA + 2584 <= 2^64 ->
  0 <= x < 2^64 -> ~ (RI <= x < RI + 8) -> ~ (RI + 72 <= x < RI + 80) -> ~ (REC <= x < REC + 4) -> ~ (CA + 2576 <= x < CA + 2584) ->
  m5c m RI REC CA nc na sz st (wa x) = m (wa x).
Proof. intros m RI REC CA nc na sz st x H1 H2 H3 H4 H5 H6 Hx F1 F2 F3 F4. unfold m5c. wbo Hx. reflexivity. Qed.
Lemma m1c_grows : forall m SP v1 v8 v9 v18 v19 v20, mem_grows m (m1c m SP v1 v8 v9 v18 v19 v20).
Proof. intros. unfold m1c. growsc. Qed.
Lemma m2c_grows : forall m SP c REC, mem_grows m (m2c m SP c REC).
Proof. intros. unfold m2c. growsc. Qed.
Lemma m3c_grows : forall m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf, mem_grows m (m3c m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf).
Proof. intros. unfold m3c. growsc. Qed.
Lemma m5c_grows : forall m RI REC CA nc na sz st, mem_grows m (m5c m RI REC CA nc na sz st).
Proof. intros. unfold m5c. growsc. Qed.

Lemma subadd : forall S a b, S - a + b = S - (a - b).
Proof. intros. ring. Qed.

(* [comment removed for export] *)
Lemma slots_ok : forall m SP v1 v8 v9 v18 v19 v20 c REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf,
  2^20 <= SP <= 2^47 -> 0 <= RI /\ RI + 24 <= SP - 256 ->
  let M := m3c (m2c (m1c m SP v1 v8 v9 v18 v19 v20) SP c REC) SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf in
  rd M (SP - 208 + 120) 8 279672 /\
  rd M (SP - 208 + 112) 8 REC /\
  rd M (SP - 208 + 104) 8 nc /\
  rd M (SP - 208 + 96) 8 8 /\
  rd M (SP - 208 + 88) 8 CA /\
  rd M (SP - 208 + 80) 8 923480 /\
  rd M (SP - 208 + 72) 8 g21 /\
  rd M (SP - 208 + 64) 8 g22 /\
  rd M (SP - 208 + 56) 8 g23 /\
  rd M (SP - 208 + 48) 8 g24 /\
  rd M (SP - 208 + 40) 8 g25 /\
  rd M (SP - 208 + 32) 8 g26 /\
  rd M (SP - 208 + 24) 8 g27 /\
  rd M (SP - 208 + 136) 8 REC /\
  rd M (SP - 208 + 144) 8 c /\
  rd M (SP - 208 + 152) 8 278424 /\
  rd M (SP - 208 + 160) 8 v20 /\
  rd M (SP - 208 + 168) 8 v19 /\
  rd M (SP - 208 + 176) 8 v18 /\
  rd M (SP - 208 + 184) 8 v9 /\
  rd M (SP - 208 + 192) 8 v8 /\
  rd M (SP - 208 + 200) 8 v1.
Proof.
  intros m SP v1 v8 v9 v18 v19 v20 c REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf HS H M. unfold M, m3c, m2c, m1c.
  assert (HH : 2^20 <= SP <= 2^47 /\ 0 <= RI /\ RI + 24 <= SP - 256) by lia. clear H.
  repeat split; rewrite subadd; rrs HS HH.
Qed.

Lemma m3c_RI : forall m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf, 0 <= RI -> RI + 24 <= 2^64 ->
  rd (m3c m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf) RI 8 1152921504606846976 /\
  rd (m3c m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf) (RI + 16) 8 (-1 * nc + nf).
Proof.
  intros m SP REC nc CA g21 g22 g23 g24 g25 g26 g27 RI nf H1 H2. unfold m3c. split.
  - apply wb_rd_other; [lia | lenq; lia | lia | lenq; lia | lenq; lia |]. apply wb_rd_hit; lenq; lia.
  - apply wb_rd_hit; lenq; lia.
Qed.

Lemma m5c_rd : forall m RI REC CA nc na sz st, 0 <= CA -> CA <= REC -> REC + 80 <= CA + 2560 -> CA + 2592 <= 2^64 -> 0 <= RI -> RI + 128 <= 2^64 ->
  (RI + 128 <= CA \/ CA + 2592 <= RI) ->
  rd (m5c m RI REC CA nc na sz st) REC 4 (nc - 1) /\ rd (m5c m RI REC CA nc na sz st) RI 8 0 /\
  rd (m5c m RI REC CA nc na sz st) (RI + 72) 8 (nc + na) /\ rd (m5c m RI REC CA nc na sz st) (CA + 2576) 8 (sz + st).
Proof.
  intros m RI REC CA nc na sz st H1 H2 H3 H4 H5 H6 H7. unfold m5c. split; [|split; [|split]].
  all: repeat first [ (apply wb_rd_hit; lenq; lia) | (apply wb_rd_other; [lia | lenq; lia | lia | lenq; lia | lenq; lia |]) ].
Qed.

Section NR.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB sz nc newc j SP : Z).
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis I : INV_C m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 4194304 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

#[using="CA ND SB SP"] Lemma srlw1 : forall R V mc, nth 2 V 0 = mc -> 0 <= mc < 2^31 ->
  bv_unsigned (edenot (Ez R V) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = mc / 2.
Proof. LiaFast.lf_pins (fun (CA ND SB SP : LiaFast.U) => LiaFast.u0).
  intros R V mc Hv Hm. cbn [edenot]. rewrite w_srlw. unfold v_srlw, ext_val.
  rewrite (zatom R V 34 mc eq_refl Hv) by lia. rewrite ext_Z_lo32_small by lia.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 mc)) with (bv_unsigned (wa mc)). rewrite (u_wa_small mc) by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small mc) by lia.
  change (1 mod 32) with 1. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  change (32%N) with (8 * N.of_nat 4)%N. rewrite swrap32_small by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  change (bv_unsigned (Z_to_bv 64 (mc / 2))) with (bv_unsigned (wa (mc / 2))).
  apply u_wa_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

Ltac zlh H := clear - H; lia.
#[using="rom CA ND SB SP"] Lemma u_rng : forall w : word, 0 <= bv_unsigned w <= 2^64 - 1.
Proof. LiaFast.lf_pins (fun (rom CA ND SB SP : LiaFast.U) => LiaFast.u0). intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2^64) in H. lia. Qed.
Ltac memb' := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)

#[using="ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP HIMG"] Lemma np_refill : cnt_of nc j = 0 ->
  exists R m', msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R (wa 0x43f08) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k KCALLEE -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (SB + c * 4294967296 + j * sz) /\
    INV_C m' CA SB c sz nc newc (j + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP HIMG : LiaFast.U) => LiaFast.u0).
  intros Hcnt0.
  pose proof I as I0. destruct I0 as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (refill_step nc j ltac:(slia) ltac:(slia) Hcnt0) as (Ej & Eb & Ec).
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb.
  rewrite Hcnt0 in Icnt. clear Ich.
  set (b := b_of nc j) in *. set (nf := newc - nc * b) in *.
  destruct Ist as (st & Hst & Rst). destruct Ina as (na & Hna & Rna).
  assert (HC5 : Z.shiftr ((ND + 31) mod 2^64) 5 = c) by (rewrite Hc; apply c_of_nd; exact HND).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (Hsz16 : sz = 16 * (sz / 16)) by (pose proof (Z.div_mod sz 16 ltac:(lia)); slia).
  assert (Hszr : 16 <= sz <= 262144) by (clear - Igeo; destruct Igeo as (_ & H1 & _ & H0 & H1' & H2' & H3 & _); nia).
  assert (Hjs : j * sz <= 262144) by (clear - Igeo Hj; destruct Igeo as (_ & H1 & _ & H0 & H1' & H2' & H3 & _); nia).
  assert (HZ : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 /\ 4194304 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ 2 <= c <= 16 /\ 33 <= ND <= 512 /\
               1 <= nc <= 8 /\ 16 <= sz <= 262144 /\ nc <= nf <= newc /\ newc <= 16384 /\ 0 <= st < 2^64 /\ 0 <= na < 2^64 /\
               (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) /\ j = nc * b /\ 1 <= j /\ j * sz <= 262144) by (unfold nf; slia).
  clear Igeo Hszr Hjs Hcr5 HCA HSB HSEP HND Hst Hna HSP.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  (* [comment removed for export] *)
  assert (P0 : AXF_np0rz.np0r_pre regs m CA ND 0 sz SB st).
  { constructor; [exact H10 | exact H11 | exact H12 | exact H13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSPa; (zlh HZ) | | | | | | ].
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [(zlh HZ) | exact HSTK].
    - rewrite HC5, Z.add_0_r. exact Icnt.
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply Iwrec; (clear - HZ Hd Hk; lia).
    - rewrite HC5. exact Isz.
    - exact ISB.
    - exact Rst.
    - intros d k Hd Hk. replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; (clear - HZ Hd Hk; lia). }
  destruct (AXF_np0rz.np0r_pnp0r regs m rom CA ND 0 sz SB st P0 (sc_np0r_p regs m SP CA ND SB HSPa ltac:((zlh HZ)) ltac:(unfold ca_place; (zlh HZ)) sz st))
    as (R1 & Hms1 & B2 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B18 & B19 & B20 & KK1).
  clear P0 B14 B15.
  set (m1 := m1c m SP (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))).
  assert (EM1 : AXF_np0rz.np0r_mem_pnp0r m regs CA ND 0 sz SB st = m1) by (unfold m1, m1c, AXF_np0rz.np0r_mem_pnp0r; rewrite HSPa; nsub; reflexivity).
  rewrite EM1 in Hms1. clear EM1.
  assert (G1 : mem_grows m m1) by apply m1c_grows.
  assert (F1 : forall x, 0 <= x < 2^64 -> ~ (SP - 48 <= x < SP) -> m1 (wa x) = m (wa x)) by (intros x Hx H; apply m1c_frame; [(zlh HZ) | exact Hx | exact H]).
  regzH B2. regzH B8. regzH B9. regzH B18. regzH B19. regzH B20.
  assert (HSP1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 2))) = SP - 48) by (rewrite B2, HSPa, u_wa_small by (zlh HZ); ring).
  (* [comment removed for export] *)
  assert (P1 : AXF_nprz.npr_pre R1 m1 CA ND (2 * nc)).
  { constructor; [exact B10 | exact B11 | exact B12 | exact B13 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP1; (zlh HZ) | ].
    - replace (getr R1 2) with (wa (SP - 48)) by (rgz; rewrite B2, HSPa; f_equal; ring).
      apply (stk_ok_move m1 SP (SP - 48) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m1 (wa SP) 2048 G1 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite HC5. apply (rd_frame m m1); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F1; clear - HZ Hx; lia | exact Imc]. }
  destruct (AXF_nprz.npr_pnpr R1 m1 rom CA ND (2 * nc) P1 (sc_npr_p R1 m1 (SP - 48) CA ND HSP1 ltac:((zlh HZ)) ltac:(unfold ca_place; (zlh HZ)) (2 * nc) ltac:((zlh HZ))))
    as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & KK2).
  clear P1 C1.
  pose proof (msteps_trans SEGS _ _ _ Hms1 Hms2) as Hms12. clear Hms1 Hms2.
  regzH C2. regzH C8. regzH C9.
  assert (Vn : bv_unsigned (edenot (Ez R1 (AXF_nprz.VALS_npr CA ND (2 * nc))) (EAluw ALU_SRL (EExt true 0 4 (EVar 34)) (ELit 1))) = nc).
  { rewrite (srlw1 R1 (AXF_nprz.VALS_npr CA ND (2 * nc)) (2 * nc) eq_refl ltac:((zlh HZ))). replace (2 * nc) with (nc * 2) by ring. apply Z.div_mul. lia. }
  rewrite Vn in C9, C14.
  assert (V18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = c) by (rewrite B8, HC5, u_wa_small by (zlh HZ); reflexivity).
  assert (V19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = CA + 80 * c) by (rewrite B9, HC5, u_wa_small by (zlh HZ); reflexivity).
  set (m2 := m2c m1 SP c (CA + 80 * c)).
  assert (EM2 : AXF_nprz.npr_mem_pnpr m1 R1 CA ND (2 * nc) = m2) by (unfold m2, m2c, AXF_nprz.npr_mem_pnpr; rewrite HSP1, V18, V19; nsub; reflexivity).
  rewrite EM2 in Hms12. clear EM2.
  assert (HSP2 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 2))) = SP - 80) by (rewrite C2, HSP1, u_wa_small by (zlh HZ); ring).
  assert (G2 : mem_grows m m2) by (exact (mem_grows_trans _ _ _ G1 (m2c_grows m1 SP c (CA + 80 * c)))).
  assert (F12 : forall x, 0 <= x < 2^64 -> ~ (SP - 72 <= x < SP) -> m2 (wa x) = m (wa x)).
  { intros x Hx H. unfold m2. rewrite m2c_frame by (clear - HZ Hx H; lia). apply F1; clear - HZ Hx H; lia. }
  (* [comment removed for export] *)
  assert (P2 : AXF_ng0z.ng0_pre R2 m2 CA ND nc SB (SB + 137438953472) nf).
  { constructor; [exact C10 | exact C11 | exact C12 | exact C13 | exact C14 | | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | (zlh HZ) | rewrite HSP2; (zlh HZ) | (zlh HZ) | | | | | | ].
    - replace (getr R2 2) with (wa (SP - 80)) by (rgz; rewrite C2, HSP1; f_equal; ring).
      apply (stk_ok_move m2 SP (SP - 80) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m2 (wa SP) 2048 G2 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact ISB].
    - apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact IRIB].
    - rewrite HC5, Z.add_0_r. apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact Imu].
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply (store_ok_mono SEGS k m m2 _ G2). apply Iwri; (clear - HZ Hd Hk; lia).
    - rewrite HC5. apply (rd_frame m m2); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F12; clear - HZ Hx; lia | exact Inf].
    - intros d k Hd Hk. rewrite HC5. apply (store_ok_mono SEGS k m m2 _ G2). replace (SB + 137438953472 + 128 * c + 16 + d) with (SB + 137438953472 + 128 * c + (16 + d)) by ring. apply Iwri; (clear - HZ Hd Hk; lia). }
  destruct (AXF_ng0z.ng0_png0 R2 m2 rom CA ND nc SB (SB + 137438953472) nf P2
              (sc_ng0_p R2 m2 (SP - 80) CA ND SB (SB + 137438953472) HSP2 ltac:((zlh HZ)) ltac:(unfold ca_place; (zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) nc nf ltac:((zlh HZ)) ltac:((zlh HZ))))
    as (R3 & Hms3 & D1 & D2 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & KK3).
  clear P2 D1 D5 D6 D7 D9 D10 D12 D15 D16 D17 D21 D22 D23 D24 D25.
  pose proof (msteps_trans SEGS _ _ _ Hms12 Hms3) as Hms13. clear Hms12 Hms3.
  assert (V28 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 8))) = CA + 80 * c) by (rewrite C8, HC5, u_wa_small by (zlh HZ); reflexivity).
  assert (V29 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 9))) = nc) by (rewrite C9, u_wa_small by (zlh HZ); reflexivity).
  assert (V218 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18))) = 8) by (rewrite (KK2 18%nat ltac:(cbn; memb')), B18, u_wa_small by (zlh HZ); reflexivity).
  assert (V219 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19))) = CA) by (rewrite (KK2 19%nat ltac:(cbn; memb')), B19, u_wa_small by (zlh HZ); reflexivity).
  assert (V220 : bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20))) = 923480) by (rewrite (KK2 20%nat ltac:(cbn; memb')), B20, u_wa_small by (zlh HZ); reflexivity).
  assert (W21 : getr R2 (Z_to_bv 5 (Z.of_nat 21)) = getr regs (Z_to_bv 5 (Z.of_nat 21))) by (rewrite (KK2 21%nat ltac:(cbn; memb')), (KK1 21%nat ltac:(cbn; memb')); reflexivity).
  assert (W22 : getr R2 (Z_to_bv 5 (Z.of_nat 22)) = getr regs (Z_to_bv 5 (Z.of_nat 22))) by (rewrite (KK2 22%nat ltac:(cbn; memb')), (KK1 22%nat ltac:(cbn; memb')); reflexivity).
  assert (W23 : getr R2 (Z_to_bv 5 (Z.of_nat 23)) = getr regs (Z_to_bv 5 (Z.of_nat 23))) by (rewrite (KK2 23%nat ltac:(cbn; memb')), (KK1 23%nat ltac:(cbn; memb')); reflexivity).
  assert (W24 : getr R2 (Z_to_bv 5 (Z.of_nat 24)) = getr regs (Z_to_bv 5 (Z.of_nat 24))) by (rewrite (KK2 24%nat ltac:(cbn; memb')), (KK1 24%nat ltac:(cbn; memb')); reflexivity).
  assert (W25 : getr R2 (Z_to_bv 5 (Z.of_nat 25)) = getr regs (Z_to_bv 5 (Z.of_nat 25))) by (rewrite (KK2 25%nat ltac:(cbn; memb')), (KK1 25%nat ltac:(cbn; memb')); reflexivity).
  assert (W26 : getr R2 (Z_to_bv 5 (Z.of_nat 26)) = getr regs (Z_to_bv 5 (Z.of_nat 26))) by (rewrite (KK2 26%nat ltac:(cbn; memb')), (KK1 26%nat ltac:(cbn; memb')); reflexivity).
  assert (W27 : getr R2 (Z_to_bv 5 (Z.of_nat 27)) = getr regs (Z_to_bv 5 (Z.of_nat 27))) by (rewrite (KK2 27%nat ltac:(cbn; memb')), (KK1 27%nat ltac:(cbn; memb')); reflexivity).

  set (m3 := m3c m2 SP (CA + 80 * c) nc CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (SB + 137438953472 + 128 * c) nf).
  assert (EM3 : AXF_ng0z.ng0_mem_png0 m2 R2 CA ND nc SB (SB + 137438953472) nf = m3).
  { unfold m3, m3c, AXF_ng0z.ng0_mem_png0. rewrite HSP2, V28, V29, V218, V219, V220, W21, W22, W23, W24, W25, W26, W27, HC5. nsub. rewrite ?Z.add_0_r. reflexivity. }
  rewrite EM3 in Hms13. clear EM3 V28 V29 V218 V219 V220 W21 W22 W23 W24 W25 W26 W27 C8 C9 C10 C11 C12 C13 C14.
  assert (G3 : mem_grows m m3) by (exact (mem_grows_trans _ _ _ G2 (m3c_grows _ _ _ _ _ _ _ _ _ _ _ _ _ _))).
  assert (F13 : forall x, 0 <= x < 2^64 -> ~ (SP - 184 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1 H3. unfold m3. rewrite m3c_frame by (clear - HZ Hx H1 H3; lia). apply F12; clear - HZ Hx H1 H3; lia. }
  destruct (m3c_RI m2 SP (CA + 80 * c) nc CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (SB + 137438953472 + 128 * c) nf ltac:((zlh HZ)) ltac:((zlh HZ))) as [R3mu R3nf].
  fold m3 in R3mu, R3nf.
  (* [comment removed for export] *)
  regzH D2. regzH D8. regzH D14. regzH D19.
  assert (L11 : getr R3 11 = wa (CA + 80 * c + 16 + 4 * Z.of_nat (Z.to_nat nc))) by (rewrite D11, HC5, Z2Nat.id by (zlh HZ); f_equal; ring).
  assert (L13 : getr R3 13 = wa (CA + 80 * c + 16)) by (rewrite D13, HC5; reflexivity).
  assert (L20 : getr R3 20 = wa (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc))) by (rewrite D20, HC5; f_equal; ring).
  clear D11 D13 D20.
  assert (LW : forall i, 0 <= i < Z.of_nat (Z.to_nat nc) -> 0 <= (newc - 1 - (nf - nc + i)) * (sz / 16) < 2^31 /\
                 rd m3 (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc) + 4 * i) 4 ((newc - 1 - (nf - nc + i)) * (sz / 16))).
  { intros i Hi. rewrite Z2Nat.id in Hi by (zlh HZ). split.
    - assert (0 <= sz / 16 <= 16384) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; (zlh HZ)). clear - HZ Hi H. nia.
    - pose proof (Ifa (nf - nc + i) ltac:(clear - HZ Hi; lia)) as Rf. replace (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc) + 4 * i) with (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc + i)) by ring.
      apply (rd_frame m m3); [clear - HZ Hi; lia | lenq; clear - HZ Hi; lia | intros x Hx; znq; apply F13; clear - HZ Hi Hx; lia | exact Rf]. }
  assert (LWR : wr m3 (CA + 80 * c + 16) (4 * Z.of_nat (Z.to_nat nc))).
  { intros d k Hd Hk. rewrite Z2Nat.id in Hk by (clear - HZ Hd Hk; lia). apply (store_ok_mono SEGS k m m3 _ G3). replace (CA + 80 * c + 16 + d) with (CA + 80 * c + (16 + d)) by ring. apply Iwrec; clear - HZ Hd Hk; lia. }
  destruct (ngl_loop rom (Z.to_nat nc) R3 m3 (SB + c * 4294967296 + 3758096384 + 4 * (nf - nc)) (CA + 80 * c + 16)
              (fun i => (newc - 1 - (nf - nc + i)) * (sz / 16)) ltac:((zlh HZ)) L11 L13 L20
              ltac:((zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) ltac:((zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) ltac:(rewrite Z2Nat.id by (zlh HZ); (zlh HZ)) LW LWR)
    as (R4 & m4 & Hms4 & E13 & E20 & KK4 & RD4 & F4 & G4).
  rewrite Z2Nat.id in RD4, F4 by (zlh HZ). clear LW LWR L11 L13 L20 E13 E20.
  pose proof (msteps_trans SEGS _ _ _ Hms13 Hms4) as Hms14. clear Hms13 Hms4.
  assert (G14 : mem_grows m m4) by exact (mem_grows_trans _ _ _ G3 G4).
  assert (F14 : forall x, 0 <= x < 2^64 -> ~ (SP - 184 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) ->
                  ~ (CA + 80 * c + 16 <= x < CA + 80 * c + 16 + 4 * nc) -> m4 (wa x) = m (wa x)).
  { intros x Hx H1 H3 H4. rewrite F4 by assumption. apply F13; assumption. }
  (* [comment removed for export] *)
  assert (HSP4 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 2))) = SP - 208) by (rewrite (KK4 2%nat ltac:(cbn; memb')), D2, HSP2, u_wa_small by (zlh HZ); ring).
  set (cp := (newc - nf) * (sz / 16)).
  assert (Hcp : 0 <= cp <= 16384).
  { assert (E : cp = j * (sz / 16)) by (unfold cp, nf; destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ejb & _); rewrite Ejb; ring).
    rewrite E. assert (Hq : 1 <= sz / 16) by (apply Z.div_le_lower_bound; (zlh HZ)). clear - HZ Hsz16 Hq. set (q := sz / 16) in *.
    destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj1 & Hjs). rewrite Hsz16 in Hjs. nia. }
  destruct (slots_ok m SP (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) c (CA + 80 * c) nc CA (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (SB + 137438953472 + 128 * c) nf ltac:((zlh HZ)) ltac:((zlh HZ)))
    as (S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31).
  fold m1 m2 m3 in S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31.
  Ltac f4 F4 H := apply (rd_frame _ _); [clear - H; lia | lenq; clear - H; lia | intros x Hx; znq; apply F4; clear - H Hx; lia | ].
  assert (HZ4 : 2^46 + 4096 <= SP <= 2^47 /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 <= SP - 2048 /\ 2 <= c <= 16 /\ 1 <= nc <= 8) by (zlh HZ).
  assert (P4 : AXF_ngtz.ngt_pre R4 m4 CA ND nc SB (SB + 137438953472) na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))).
  { constructor.
    all: try ((zlh HZ) || apply u_rng || (rewrite HSP4; (zlh HZ))).
    - regzG. rewrite (KK4 8%nat ltac:(cbn; memb')). exact D8.
    - regzG. rewrite (KK4 14%nat ltac:(cbn; memb')). exact D14.
    - regzG. rewrite (KK4 19%nat ltac:(cbn; memb')). exact D19.
    - replace (getr R4 2) with (wa (SP - 208)) by (regzG; rewrite (KK4 2%nat ltac:(cbn; memb')), D2, HSP2; f_equal; ring).
      apply (stk_ok_move m4 SP (SP - 208) 1024); [(zlh HZ) | (zlh HZ) | exact (stk_ok_grows m m4 (wa SP) 2048 G14 HSTK) | (zlh HZ) | (zlh HZ) | (zlh HZ)].
    - rewrite HC5. apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rna].
    - intros d k Hd Hk. rewrite HC5. apply (store_ok_mono SEGS k m m4 _ G14). replace (SB + 137438953472 + 128 * c + 72 + d) with (SB + 137438953472 + 128 * c + (72 + d)) by ring. apply Iwri; clear - HZ Hd Hk; lia.
    - rewrite HC5, Z.add_0_r. apply (rd_frame m3 m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F4; clear - HZ Hx; lia | exact R3mu].
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply (store_ok_mono SEGS k m m4 _ G14). apply Iwri; clear - HZ Hd Hk; lia.
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S10].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S11].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S12].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S13].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S14].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S15].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S16].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S17].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S18].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S19].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S20].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S21].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S22].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S23].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S24].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S25].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S26].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S27].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S28].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S29].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S30].
    - rewrite HSP4, ?HC5. apply (rd_frame m3 m4); [clear - HZ4; lia | lenq; clear - HZ4; lia | intros x Hx; znq; apply F4; clear - HZ4 Hx; lia | exact S31].
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply (store_ok_mono SEGS k m m4 _ G14). apply Iwrec; clear - HZ Hd Hk; lia.
    - rewrite HC5. apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Isz].
    - rewrite HC5, chp_off by (zlh HZ). pose proof (RD4 (nc - 1) ltac:((zlh HZ))) as R7.
      replace (CA + 80 * c + 16 + 4 * (nc - 1)) with (CA + (80 * c + 4 * (nc - 1)) + 16) in R7 by ring.
      replace ((newc - 1 - (nf - nc + (nc - 1))) * (sz / 16)) with cp in R7 by (unfold cp; ring). exact R7.
    - apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact ISB].
    - apply (rd_frame m m4); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply F14; clear - HZ Hx; lia | exact Rst].
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m4 _ G14). replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; clear - HZ Hd Hk; lia.
    - intros i Hi. change (Z_to_bv 64 i) with (wa i). rewrite F14 by (clear - HZ Hi; lia). apply HIMG. exact Hi. }
  destruct (AXF_ngtz.ngt_pngt R4 m4 rom CA ND nc SB (SB + 137438953472) na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) P4
              (sc_ngt_p R4 m4 (SP - 208) CA ND SB (SB + 137438953472) HSP4 ltac:((zlh HZ)) ltac:(unfold ca_place; (zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ))
                 nc na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) ltac:((zlh HZ))))
    as (R5 & Hms5 & T1 & T2 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & T28 & KK5).
  clear P4 T5 T6 T7 T11 T12 T13 T14 T15 T16 T17 T28.
  pose proof (msteps_trans SEGS _ _ _ Hms14 Hms5) as Hms. clear Hms14 Hms5.
  set (m5 := m5c m4 (SB + 137438953472 + 128 * c) (CA + 80 * c) CA nc na sz st).
  assert (EM5 : AXF_ngtz.ngt_mem_pngt m4 R4 CA ND nc SB (SB + 137438953472) na cp sz st 0 0 0 0 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 26)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 27)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) = m5).
  { unfold m5, m5c, AXF_ngtz.ngt_mem_pngt. rewrite HC5, ext_Z_lo32_small by (zlh HZ). rewrite ?Z.add_0_r, ?addneg. reflexivity. }
  rewrite EM5 in Hms. clear EM5.
  assert (G5 : mem_grows m m5) by (exact (mem_grows_trans _ _ _ G14 (m5c_grows _ _ _ _ _ _ _ _))).
  assert (FX5 : forall x, 0 <= x < 2^64 -> ~ (SP - 184 <= x < SP) -> ~ (SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 24) ->
                  ~ (SB + 137438953472 + 128 * c + 72 <= x < SB + 137438953472 + 128 * c + 80) -> ~ (CA + 80 * c <= x < CA + 80 * c + 4) ->
                  ~ (CA + 80 * c + 16 <= x < CA + 80 * c + 16 + 4 * nc) -> ~ (CA + 2576 <= x < CA + 2584) -> m5 (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4 Q5 Q6. unfold m5. rewrite m5c_frame by (clear - HZ Hx Q1 Q2 Q3 Q4 Q5 Q6; lia). apply F14; assumption. }
  destruct (m5c_rd m4 (SB + 137438953472 + 128 * c) (CA + 80 * c) CA nc na sz st ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)) ltac:((zlh HZ)))
    as (Rc5 & Rmu5 & Rna5 & Rst5).
  fold m5 in Rc5, Rmu5, Rna5, Rst5.
  exists R5, m5. split; [exact Hms|].
  regzH T2. regzH T8. regzH T9. regzH T10. regzH T18. regzH T19. regzH T20. regzH T21. regzH T22. regzH T23. regzH T24. regzH T25. regzH T26. regzH T27. regzH T1.
  split; [rewrite T2, HSP4; f_equal; ring|].
  split.
  { intros k Hk. cbn [KCALLEE In] in Hk. repeat (destruct Hk as [<-|Hk]; [first [ (match goal with T : getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat ?k)))) |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite T; apply wa_u end)
                                                                          | (lazymatch goal with |- getr R5 (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK5 k ltac:(cbn; memb')), (KK4 k ltac:(cbn; memb')), (KK3 k ltac:(cbn; memb')), (KK2 k ltac:(cbn; memb')), (KK1 k ltac:(cbn; memb')); reflexivity end) ] |]).
    destruct Hk. }
  split.
  { regzG. rewrite T10, HC5, ext_Z_u32 by (zlh HZ). f_equal. unfold cp, nf.
    destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ejb & _). rewrite Hsz16 at 2. rewrite Ejb. ring. }
  assert (HZI : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 <= SP - 2048) by (zlh HZ).
  assert (HZS : 4194304 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\ SP <= 2^47) by (zlh HZ).
  assert (HZP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by (zlh HZ).
  split.
  { apply (inv_refill m m5 CA SB c sz nc newc j SP I Hj HZI HZS HZP G5 Hcnt0).
    - intros x Hx Q1 Q2. unfold owned_C in Q2. apply FX5; clear - HZ Hx Q1 Q2; lia.
    - exact Rc5.
    - apply (rd_frame m m5); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply FX5; clear - HZ Hx; lia | exact Imc].
    - apply (rd_frame m m5); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; apply FX5; clear - HZ Hx; lia | exact Isz].
    - intros i Hi. pose proof (RD4 i Hi) as Ri. replace ((newc - 1 - (nf - nc + i)) * (sz / 16)) with ((j + nc - 1 - i) * (sz / 16)) in Ri.
      2: { unfold nf. destruct HZ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ejb & _). rewrite Ejb. ring. }
      replace (CA + 80 * c + 16 + 4 * i) with (CA + 80 * c + 16 + 4 * i) in Ri by ring.
      apply (rd_frame m4 m5); [clear - HZ Hi; lia | lenq; clear - HZ Hi; lia | intros x Hx; znq; unfold m5; apply m5c_frame; clear - HZ Hi Hx; lia | exact Ri].
    - exact Rmu5.
    - replace (newc - nc * b_of nc j - nc) with (-1 * nc + nf) by (unfold nf, b; ring).
      apply (rd_frame m3 m5); [(zlh HZ) | lenq; (zlh HZ) | intros x Hx; znq; unfold m5; rewrite m5c_frame by (clear - HZ Hx; lia); apply F4; clear - HZ Hx; lia | exact R3nf].
    - exists ((nc + na) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((nc + na) mod 2^64) (nc + na)) by (apply Z.mod_mod; lia). exact Rna5.
    - exists ((sz + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd. rewrite (wa_eqm ((sz + st) mod 2^64) (sz + st)) by (apply Z.mod_mod; lia). exact Rst5. }
  split; [|exact G5].
  intros x Hx Q1 Q2. unfold owned_C in Q2. apply FX5; clear - HZ Hx Q1 Q2; lia.
Qed.

End NR.

(* [comment removed for export] *)
Theorem npop_contract : forall {fx : FPState} rom m regs CA ND c SB sz nc newc j SP,
  c = (ND + 31) / 32 -> INV_C m CA SB c sz nc newc j -> j + 1 + nc <= newc -> 33 <= ND <= 512 ->
  getr regs 2 = wa SP -> 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0 -> stk_ok SEGS m (wa SP) 2048 ->
  getr regs 10 = wa 923480 -> getr regs 11 = wa CA -> getr regs 12 = wa ND -> getr regs 13 = wa 8 ->
  ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 ->
  4194304 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 ->
  (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) ->
  (forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None) ->
  exists R m', msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R (wa 0x43f08) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k KCALLEE -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (SB + c * 4294967296 + j * sz) /\
    INV_C m' CA SB c sz nc newc (j + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof.
  intros fx rom m regs CA ND c SB sz nc newc j SP Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP HIMG.
  pose proof (cnt_of_range nc j ltac:(destruct I as [Igeo]; lia) ltac:(destruct I as [Igeo]; lia)) as Hcr.
  destruct (Z.eq_dec (cnt_of nc j) 0) as [E0|E0].
  - eapply np_refill; eassumption.
  - eapply np_pop; try eassumption. lia.
Qed.
