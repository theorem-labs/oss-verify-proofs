(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mmwz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_am1 AXG_am5 AXG_am6.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt3wz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt4z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt5z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mmrgz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt7z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am5 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma land_neg_aligned : forall b, b mod 4096 = 0 -> Z.land ((-1 * b) mod 2^64) 4095 = 0.
Proof.
  intros b Hb. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia.
  rewrite Z.mod_mod_divide by (first [lia | (exists (2^52); reflexivity)]).
  change (2^12) with 4096. apply Z_mod_zero_opp_full in Hb. replace (-1 * b) with (- b) by ring. exact Hb.
Qed.

Section AM6f.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bnq : forall R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh,
  am_frame R m sp0 can ra s0 s1 s2 s3 s4 -> getr R 8 = wa 4096 ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  0 <= ar <= 2^64-1 -> rdn SEGS m (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa ar)) ->
  0 <= sh <= 34 -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  exists R', msteps SEGS (mkst R (wa 0x53b68) m rom) (mkst R' (wa 0x53ba4) m rom) /\
    getr R' 17 = wa 214 /\ getr R' 10 = wa 0 /\ getr R' 11 = wa 4095 /\ getr R' 8 = wa 4096 /\ getr R' 19 = wa 621712 /\
    (forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh F R8 Mac Mbk Rar Mar Rsh Msh.
  assert (P1 : mt3w_pre R m 0 0 ar sh)
    by (constructor; [exact R8 | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | lia | lia | exact Rar | lia | exact Mac | exact Mbk | exact Mar | exact Msh]).
  destruct (mt3w_pmt3nw R m rom 0 0 ar sh P1) as (R1 & Hms1 & A8 & A9 & A10 & A11 & A17 & A19 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt3w.RES_pmt3nw fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; first [rewrite br_eq_z | rewrite br_ne_z]; cbn [zeval edenot].
    all: rewrite ?(zatom R (VALS_mt3w 0 0 ar sh) 32 0 eq_refl eq_refl) by lia.
    all: rewrite ?(zatom R (VALS_mt3w 0 0 ar sh) 33 0 eq_refl eq_refl) by lia.
    all: reflexivity. }
  change (mt3w_mem_pmt3nw m R 0 0 ar sh) with m in Hms1.
  exists R1. split; [exact Hms1|]. split; [exact A17|]. split; [exact A10|]. split; [exact A11|]. split; [exact A8|]. split; [exact A19|].
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bnx : forall R m rom b,
  getr R 8 = wa 4096 -> getr R 10 = wa b -> getr R 11 = wa 4095 -> getr R 19 = wa 621712 ->
  0 <= b <= 2^47 -> b mod 4096 = 0 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x53ba8) m rom) (mkst R' (wa 0x53bc8) (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa b))) rom) /\
    getr R' 8 = wa 4096 /\ getr R' 9 = wa (b + 8192) /\ getr R' 10 = wa (b + 8192) /\ getr R' 17 = wa 214 /\ getr R' 19 = wa 621712 /\
    (forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom b R8 R10 R11 R19 Rb Ab W5.
  assert (P1 : mt4_pre R m b) by (constructor; first [assumption | lia]).
  destruct (mt4_pmt4 R m rom b P1 ltac:(constructor)) as (R1 & Hms1 & A8 & A9 & A10 & A11 & A12 & A17 & A19 & Ak1).
  rewrite (land_neg_aligned b Ab), Z.add_0_r in A9, A10.
  replace (mt4_mem_pmt4 m R b) with (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa b))) in Hms1
    by (unfold mt4_mem_pmt4; rewrite (land_neg_aligned b Ab), Z.add_0_r; reflexivity).
  exists R1. split; [exact Hms1|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A17|]. split; [exact A19|].
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bnr : forall R m rom res b sh,
  getr R 8 = wa 4096 -> getr R 9 = wa (b + 8192) -> getr R 10 = wa res -> getr R 19 = wa 621712 ->
  0 <= res <= 2^64-1 -> 4096 <= b <= 2^47 -> res <> b + 8192 -> 0 <= sh <= 34 ->
  rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa b)) ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x53bcc) m rom) (mkst R' (wa 0x550e0) (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615))) rom) /\
    getr R' 1 = wa 343108 /\ getr R' 8 = wa 4096 /\ getr R' 9 = wa (Z.shiftl 2 sh) /\ getr R' 10 = wa 0 /\ getr R' 11 = wa (4096 * Z.shiftl 2 sh) /\
    getr R' 12 = wa 0 /\ getr R' 13 = wa 34 /\ getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 19 = wa 621712 /\
    getr R' 20 = wa 18446744073709551615 /\
    (forall k, In k [2; 3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom res b sh R8 R9 R10 R19 Rres Rb Hne Rsh M1 M3 M4 W5.
  assert (P1 : mt5_pre R m res b sh) by (constructor; first [assumption | lia]).
  destruct (mt5_pmt5r R m rom res b sh P1) as (R1 & Hms1 & A1 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A19 & A20 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt5.RES_pmt5r fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot].
    rewrite (zatom R (VALS_mt5 res b sh) 32 res eq_refl eq_refl) by lia. rewrite (zatom R (VALS_mt5 res b sh) 33 b eq_refl eq_refl) by lia.
    rewrite (Z.mod_small (b + 8192)) by lia. rewrite (Z.mod_small res) by lia. apply negb_true_iff. apply Z.eqb_neq. exact Hne. }
  change (mt5_mem_pmt5r m R res b sh) with (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615))) in Hms1.
  exists R1. split; [exact Hms1|].
  do 11 (split; [assumption|]).
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bng : forall R m rom b sh,
  getr R 8 = wa 4096 -> getr R 9 = wa (b + 8192) -> getr R 10 = wa (b + 8192) -> getr R 19 = wa 621712 ->
  4096 <= b <= 2^47 - 8192 -> 0 <= sh <= 34 ->
  rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa b)) ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x53bcc) m rom) (mkst R' (wa 0x550e0) m rom) /\
    getr R' 1 = wa 343020 /\ getr R' 8 = wa 4096 /\ getr R' 9 = wa (b + 8192) /\ getr R' 10 = wa b /\ getr R' 11 = wa 4096 /\
    getr R' 12 = wa 0 /\ getr R' 13 = wa 50 /\ getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 19 = wa 621712 /\
    (forall k, In k [2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom b sh R8 R9 R10 R19 Rb Rsh M1 M3 M4 W5.
  assert (P1 : mt5_pre R m (b + 8192) b sh) by (constructor; first [assumption | lia]).
  destruct (mt5_pmt5g R m rom (b + 8192) b sh P1) as (R1 & Hms1 & A1 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A19 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt5.RES_pmt5g fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot].
    rewrite (zatom R (VALS_mt5 (b + 8192) b sh) 32 (b + 8192) eq_refl eq_refl) by lia. rewrite (zatom R (VALS_mt5 (b + 8192) b sh) 33 b eq_refl eq_refl) by lia.
    rewrite Z.eqb_refl. reflexivity. }
  change (mt5_mem_pmt5g m R (b + 8192) b sh) with m in Hms1.
  exists R1. split; [exact Hms1|].
  do 10 (split; [assumption|]).
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_gmw : forall R m rom sp0 b,
  getr R 1 = wa 343020 -> getr R 2 = wa (sp0 + -64) -> getr R 8 = wa 4096 -> getr R 9 = wa (b + 8192) ->
  getr R 10 = wa b -> getr R 11 = wa 4096 -> getr R 12 = wa 0 -> getr R 13 = wa 50 ->
  getr R 14 = wa 18446744073709551615 -> getr R 15 = wa 0 ->
  getr R 18 = wa 621568 -> getr R 19 = wa 621712 ->
  4096 <= b <= 2^47 - 8192 -> stk_ok SEGS m (wa (sp0 + -64)) 1024 -> 2^20 + 1024 <= sp0 <= 2^47 -> sp0 mod 16 = 0 ->
  exists R' m', msteps SEGS (mkst R (wa 0x550e0) m rom) (mkst R' (wa 0x551a4) m' rom) /\
    getr R' 17 = wa 222 /\ getr R' 10 = wa b /\ getr R' 11 = wa 4096 /\ getr R' 12 = wa 0 /\ getr R' 13 = wa 50 /\
    getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 16 = wa b /\ getr R' 2 = wa (sp0 + -64 + -64) /\
    (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    mmap_saves m' (sp0 + -64) 343020 4096 (b + 8192) 621568 621712 (bv_unsigned (getr R 20)) (bv_unsigned (getr R 21)) /\
    (forall x, 0 <= x < 2^64 -> ~ (sp0 - 128 <= x < sp0 - 64) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 b A1 A2 A8 A9 A10 A11 A12 A13 A14 A15 A18 A19 Rb STK Rsp Asp.
  assert (P2 : mmw_pre R m (sp0 + -64) b 4096 0 50).
  { constructor; [exact A2 | exact A10 | exact A11 | exact A12 | exact A13 | exact A14 | exact A15 | exact STK | lia | lia | lia | lia | lia |].
    clear - Asp. apply Z.mod_divide in Asp; [|lia]. destruct Asp as (k & ->). replace (k * 16 + -64) with ((k - 4) * 16) by ring. apply Z.mod_mul. lia. }
  destruct (mmw_pfx R m rom (sp0 + -64) b 4096 0 50 P2)
    as (R2 & Hms2 & B1 & B2 & B5 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19 & B20 & B21 & Bk2).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz.AXF_mmw.RES_pfx fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot]. rewrite (zatom R (VALS_mmw (sp0 + -64) b 4096 0 50) 36 50 eq_refl eq_refl) by lia.
    reflexivity. }
  set (m2 := mmw_mem_pfx m R (sp0 + -64) b 4096 0 50) in *.
  exists R2, m2. split; [exact Hms2|].
  split; [exact B17|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12|]. split; [exact B13|]. split; [exact B14|].
  split; [exact B15|]. split; [exact B16|]. split; [exact B2|].
  split; [intros k Hk'; apply Bk2; clear - Hk'; klist Hk'|].
  assert (W : forall k v, getr R (Z_to_bv 5 (Z.of_nat k)) = wa v -> 0 <= v < 2^64 -> bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat k))) = v).
  { intros k v E Hv. rewrite E. apply u_wa_small. exact Hv. }
  split.
  - unfold mmap_saves, m2, mmw_mem_pfx.
    assert (E1 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 1))) = 343020) by (apply W; [litr2 A1; reflexivity | lia]).
    assert (E8 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 8))) = 4096) by (apply W; [litr2 A8; reflexivity | lia]).
    assert (E9 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) = b + 8192) by (apply W; [litr2 A9; reflexivity | lia]).
    assert (E18 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) = 621568) by (apply W; [litr2 A18; reflexivity | lia]).
    assert (E19 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19))) = 621712) by (apply W; [litr2 A19; reflexivity | lia]).
    rewrite E1, E8, E9, E18, E19.
    repeat split; repeat (rewrite rdn_wbytes_disjoint; [| side | side]); first [ (apply rdn_wbytes_hit8; side) | (rewrite wa_u; apply rdn_wbytes_hit8; side) ].
  - split.
    + intros x Hx Hn. unfold m2, mmw_mem_pfx. do 7 (rewrite MngWb.wbytes_out by side). reflexivity.
    + unfold m2, mmw_mem_pfx. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_gmr : forall R m rom sp0 b v20 v21,
  getr R 2 = wa (sp0 + -64 + -64) -> getr R 10 = wa b -> getr R 16 = wa b ->
  2^20 + 1024 <= sp0 <= 2^47 -> sp0 mod 16 = 0 -> 4096 <= b <= 2^47 - 8192 -> 0 <= v20 <= 2^64-1 -> 0 <= v21 <= 2^64-1 ->
  mmap_saves m (sp0 + -64) 343020 4096 (b + 8192) 621568 621712 v20 v21 ->
  exists R', msteps SEGS (mkst R (wa 0x551a8) m rom) (mkst R' (wa 0x53bec) m rom) /\
    getr R' 1 = wa 343020 /\ getr R' 2 = wa (sp0 + -64) /\ getr R' 8 = wa 4096 /\ getr R' 9 = wa (b + 8192) /\ getr R' 10 = wa b /\
    getr R' 18 = wa 621568 /\ getr R' 19 = wa 621712 /\ getr R' 20 = wa v20 /\ getr R' 21 = wa v21 /\
    (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 b v20 v21 R2 R10 R16 Rsp Asp Rb R20 R21 (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (Asp' : (sp0 + -64) mod 16 = 0).
  { clear - Asp. apply Z.mod_divide in Asp; [|lia]. destruct Asp as (k & ->). replace (k * 16 + -64) with ((k - 4) * 16) by ring. apply Z.mod_mul. lia. }
  assert (P1 : mmrg_pre R m (sp0 + -64) b b 4096 (b + 8192) 621568 621712 v20 v21).
  { constructor; first [assumption | lia]. }
  destruct (mmrg_pmmrg R m rom (sp0 + -64) b b 4096 (b + 8192) 621568 621712 v20 v21 P1 ltac:(constructor))
    as (R1 & Hms1 & A1 & A2 & A8 & A9 & A10 & A11 & A16 & A18 & A19 & A20 & A21 & Ak1).
  change (mmrg_mem_pmmrg m R (sp0 + -64) b b 4096 (b + 8192) 621568 621712 v20 v21) with m in Hms1.
  exists R1. split; [exact Hms1|].
  do 9 (split; [assumption|]).
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bn7 : forall R m rom nb,
  getr R 8 = wa 4096 -> getr R 9 = wa nb -> getr R 19 = wa 621712 -> 8192 <= nb <= 2^47 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x53bec) m rom)
                     (mkst R' (wa 0x53c78) (wbytes (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa nb))) (wa (0 + 621760)) (word_to_le_bytes 8 (wa 1))) rom) /\
    getr R' 8 = wa 1 /\ getr R' 9 = wa (nb + -4096) /\ getr R' 19 = wa 621712 /\
    (forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom nb R8 R9 R19 Rnb W5 W6.
  assert (P1 : mt7_pre R m nb) by (constructor; first [assumption | lia]).
  destruct (mt7_pmt7 R m rom nb P1 ltac:(constructor)) as (R1 & Hms1 & A8 & A9 & A19 & Ak1).
  change (mt7_mem_pmt7 m R nb) with (wbytes (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa nb))) (wa (0 + 621760)) (word_to_le_bytes 8 (wa 1))) in Hms1.
  exists R1. split; [exact Hms1|]. split; [exact A8|]. split; [exact A9|]. split; [exact A19|].
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.
End AM6f.
