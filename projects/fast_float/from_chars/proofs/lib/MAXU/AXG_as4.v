(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb MngGM AXG_ntfm AXG_ntfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits AxMalloc MngZ MngNtfM MngNtfS AXG_nQ AXG_nD AXG_tam AXG_as1 AXG_as2 AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_dq2z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma span32 : forall W, 0 <= W -> (bv_swrap 32 (Z.shiftl 2 (W mod 32)) + -1) mod 2^32 = 2^(Z.land W 31 + 1) - 1.
Proof.
  intros W HW.
  assert (Hl : 0 <= Z.land W 31 < 32) by (apply land31_bound; lia).
  assert (Hw : W mod 32 = Z.land W 31) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity).
  rewrite Zplus_mod, swrap32_mod, <- Zplus_mod. rewrite Hw. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (0 < 2^(Z.land W 31) <= 2^31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma m1_cond : forall f W, 0 <= f < 2^32 -> 0 <= W ->
  (ext_Z true 0 4 f mod 2^64 =? bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (W mod 32)) + -1) mod 2^64) = (f =? 2^(Z.land W 31 + 1) - 1).
Proof. intros f W Hf HW. rewrite ext4_swrap, sx32_eqb, span32 by exact HW. rewrite Z.mod_small by exact Hf. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m2_cond : forall f h, 0 <= f < 2^32 -> 0 <= h ->
  (Z.land (bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (h mod 32)) + -1) mod 2^64) (ext_Z true 0 4 f mod 2^64) mod 2^64 =? 0 mod 2^64)
  = (Z.land f (2^(Z.land h 31 + 1) - 1) =? 0).
Proof.
  intros f h Hf Hh. rewrite ext4_swrap, sx32_land, Z.mod_mod by lia. change (0 mod 2^64) with 0. rewrite sx32_zero.
  rewrite land_mod32, span32 by exact Hh. rewrite Z.land_comm. rewrite (Z.mod_small f) by exact Hf. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma meta_bits_r63 : forall X R U s g am L, Inv X R U s -> usedX X s g am -> layout_ok L s -> 0 <= meta_bits am <= 2^63 - 1.
Proof.
  intros X R U s g am L HI Hu HL. destruct (masks_range_inv X R U s g am HI Hu) as (_ & _ & Rl & Rs & Rm).
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & _ & Gmp & _).
  destruct (Z.eq_dec (am_maplen am) 0) as [E0|E0]; [unfold meta_bits; rewrite E0; lia|].
  destruct (Gmp ltac:(lia)) as (r & rg & _ & Hr & Hk & Hl & Hlen & _).
  pose proof (footprint_region_In s r rg Hr Hk Hl) as F. pose proof HL as (_ & _ & _ & Lrng).
  pose proof (Lrng _ F) as (B1 & B2). cbn [crange fst snd] in B1, B2. rewrite Hlen in B2. unfold PGSZ in B2.
  unfold meta_bits. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_lo4 : forall m a W, rdn SEGS m (wa a) 8 = Some (word_to_le_bytes 8 (wa W)) ->
  rdn SEGS m (wa a) 4 = Some (word_to_le_bytes 4 (wa (W mod 2^32))).
Proof.
  intros m a W H. pose proof (rdn_slice SEGS m 8 (wa a) _ 0 4 H ltac:(lia)) as E.
  rewrite word_add_0 in E. rewrite E. f_equal. change (skipn 0 (word_to_le_bytes 8 (wa W))) with (word_to_le_bytes 8 (wa W)).
  unfold word_to_le_bytes at 1. rewrite firstn_Z_to_le_bytes by lia.
  change (Z_to_le_bytes 4 (bv_unsigned (wa W))) with (word_to_le_bytes 4 (wa W)).
  apply le_wa_eqm; [|lia]. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma keeps21 : forall (R R' : bvmap 5 word) m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  (forall k, In k [2;8;18;20;22;23]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  getr R' 21 = wa (8 * sc + 621800) ->
  forall k, In k [2;8;18;20;21;22;23]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)).
Proof.
  intros R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F K Q21 k Hk.
  destruct (Nat.eq_dec k 21) as [->|Hne]; [|apply K; clear - Hk Hne; cbn [In] in *; intuition lia].
  destruct F as [_ _ _ _ R21 _ _]. litr2 Q21. symmetry. litr2 R21. reflexivity.
Qed.

Section AS4.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_m1n : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m1 am1,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m1)) -> 0 <= sc < 48 ->
  MT s m1 = Some (MUsed am1) -> am_freed am1 <> ones (am_last am1) ->
  0 <= am_freed am1 <= 2^32-1 -> 0 <= am_last am1 <= 31 -> 0 <= am_sc am1 < 64 -> 0 <= am_maplen am1 -> meta_bits am1 <= 2^63-1 ->
  exists R', msteps SEGS (mkst R (wa 0x54170) m rom) (mkst R' (wa 0x5419c) m rom) /\
    ta_m1 sc m1 s = ta_m2 sc m1 s /\ as_frame R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\
    getr R' 10 = wa (loc_addr L (LMem m1)) /\ getr R' 13 = wa (ext_Z true 0 4 (am_freed am1)) /\ getr R' 14 = wa 2 /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m1 am1 N F R10 Rsc M1 Hf Rfr Rl Rs Rm RW.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (K1 : In m1 (keys s)) by (eapply MT_keys; exact M1).
  set (G1 := loc_addr L (LMem m1)) in *.
  destruct (HMP m1 K1) as (G1a & G1b & G1c & G1d). fold G1 in G1a, G1b, G1c, G1d.
  set (W := meta_bits am1).
  assert (RW0 : 0 <= W) by (apply meta_bits_nonneg; lia).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m1nz.m1n_pre R m sc G1 (am_freed am1) W).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1a G1b Hsp2 HK1; lia); try (clear - RW RW0; lia).
    - exact (rx_freed L s m [] HR HEO HK m1 am1 M1).
    - exact (rx_bits L s m [] HR HEO HK m1 am1 M1). }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m1nz.m1n_pm1n R m rom sc G1 (am_freed am1) W P) as (R' & Hms & Q10 & Q12 & Q13 & Q14 & Q21 & Qk).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m1n.RES_pm1n fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m1nz.VALS_m1n sc G1 (am_freed am1) W)).
    assert (Z34 : bv_unsigned (ev E 34) = am_freed am1) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
    assert (Z35 : bv_unsigned (ev E 35) = W) by (apply zatom; [reflexivity | reflexivity | clear - RW RW0; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z35;
      rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?(Z.mod_small (am_freed am1)), ?(Z.mod_small W) by (clear - Rfr RW RW0; lia).
    - rewrite m1_cond by (clear - Rfr RW0; lia). unfold W. rewrite mb_land31 by lia. apply negb_true_iff. apply Z.eqb_neq. exact Hf.
    - apply Z.eqb_neq. assert (LB : 0 <= Z.land W 32 <= 32) by (split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply land_le_l; lia]).
      rewrite Z.mod_small by lia. unfold W. apply (mb_land32 am1); lia. }
  exists R'. split; [exact Hms|]. split; [exact (ta_m1n s sc m1 am1 M1 Hf)|]. split.
  { apply (as_frame_move R R' m m); [exact F | | intros; reflexivity | intros; reflexivity].
    apply (keeps21 R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F); [|exact Q21].
    intros k Hk. apply Qk. clear - Hk. cbn [In] in *. tauto. }
  split; [exact Q10|]. split; [exact Q13|]. split; [exact Q14|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_m1f : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m1 am1 nx amx,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m1)) -> 0 <= sc < 48 -> length (st_active s) = 48%nat ->
  MT s m1 = Some (MUsed am1) -> am_freed am1 = ones (am_last am1) -> am_next am1 = Some nx -> MT s nx = Some (MUsed amx) ->
  0 <= am_freed am1 <= 2^32-1 -> 0 <= am_last am1 <= 31 -> 0 <= am_sc am1 < 64 -> 0 <= am_maplen am1 -> meta_bits am1 <= 2^63-1 ->
  0 <= am_freed amx <= 2^32-1 ->
  exists R' m', msteps SEGS (mkst R (wa 0x54170) m rom) (mkst R' (wa 0x5419c) m' rom) /\
    ta_m1 sc m1 s = ta_m2 sc nx (s_head s sc (Some nx)) /\ NC L [] [] (s_head s sc (Some nx)) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (s_head s sc (Some nx)) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem nx)) /\ getr R' 13 = wa (ext_Z true 0 4 (am_freed amx)) /\ getr R' 14 = wa 2 /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m1 am1 nx amx N F R10 Rsc Hlen M1 Hf Hnx Mx Rfr Rl Rs Rm RW Rfx.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (K1 : In m1 (keys s)) by (eapply MT_keys; exact M1).
  assert (Kx : In nx (keys s)) by (eapply MT_keys; exact Mx).
  set (G1 := loc_addr L (LMem m1)) in *. set (NX := loc_addr L (LMem nx)) in *.
  destruct (HMP m1 K1) as (G1a & G1b & G1c & G1d). fold G1 in G1a, G1b, G1c, G1d.
  destruct (HMP nx Kx) as (X1 & X2 & X3 & X4). fold NX in X1, X2, X3, X4.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  set (W := meta_bits am1).
  assert (RW0 : 0 <= W) by (apply meta_bits_nonneg; lia).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m1fz.m1f_pre R m sc G1 (am_freed am1) W NX (am_freed amx)).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1a G1b Hsp2 HK1; lia); try (clear - X1 X2 Hsp2 HK1; lia); try (clear - RW RW0; lia).
    all: try (clear - X3 Rsc; lia).
    - exact (rx_freed L s m [] HR HEO HK m1 am1 M1).
    - exact (rx_bits L s m [] HR HEO HK m1 am1 M1).
    - pose proof (rx_next L s m [] HR HEO HK m1 am1 M1) as E. rewrite Hnx in E. exact E.
    - exact (rx_freed L s m [] HR HEO HK nx amx Mx).
    - intros d n Hd Hn. pose proof (rx_act_wr L s m [] HR HEO Hctx k ltac:(lia) d n Hd Hn) as E. rewrite Ek in E.
      replace (8 * sc + 621800 + d) with (621800 + 8 * sc + d) by ring. exact E. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m1fz.m1f_pm1f R m rom sc G1 (am_freed am1) W NX (am_freed amx) P) as (R' & Hms & Q10 & Q12 & Q13 & Q14 & Q21 & Qk).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m1f.RES_pm1f fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m1fz.VALS_m1f sc G1 (am_freed am1) W NX (am_freed amx))).
    assert (Z34 : bv_unsigned (ev E 34) = am_freed am1) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
    assert (Z35 : bv_unsigned (ev E 35) = W) by (apply zatom; [reflexivity | reflexivity | clear - RW RW0; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z35;
      rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?(Z.mod_small (am_freed am1)), ?(Z.mod_small W) by (clear - Rfr RW RW0; lia).
    - rewrite m1_cond by (clear - Rfr RW0; lia). unfold W. rewrite mb_land31 by lia. apply negb_false_iff. apply Z.eqb_eq. exact Hf.
    - apply Z.eqb_neq. assert (LB : 0 <= Z.land W 32 <= 32) by (split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply land_le_l; lia]).
      rewrite Z.mod_small by lia. unfold W. apply (mb_land32 am1); lia. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m1fz.m1f_mem_pm1f m R sc G1 (am_freed am1) W NX (am_freed amx)) with (act_mem m sc NX) in Hms.
  destruct (nc_act L s m sp0 K sc nx N Rsc Hlen) as (N' & HRS & Hgr & FR & Ks' & MOUT).
  exists R', (act_mem m sc NX). split; [exact Hms|]. split; [exact (ta_m1f s sc m1 am1 nx M1 Hf Hnx)|].
  split; [exact N'|]. split.
  { apply (as_frame_move R R' m (act_mem m sc NX)); [exact F | | |].
    - apply (keeps21 R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F); [|exact Q21].
      intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
    - intros x Hx. apply MOUT; [clear - Hx Hsp1 Hsp2 HK1; lia | clear - Hx Hsp1 HK1 Rsc; lia].
    - intros x Hx. apply MOUT; [clear - Hx; lia | clear - Hx Rsc; lia]. }
  split; [exact HRS|]. split; [exact Hgr|]. split; [exact FR|]. split; [exact Q10|]. split; [exact Q13|]. split; [exact Q14|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_m2a : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m2 am2,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m2)) -> getr R 13 = wa (ext_Z true 0 4 (am_freed am2)) -> getr R 14 = wa 2 -> 0 <= sc < 48 ->
  MT s m2 = Some (MUsed am2) -> Z.land (am_freed am2) (ones (am_aidx am2)) <> 0 -> am_avail am2 = 0 ->
  0 <= am_freed am2 <= 2^32-1 -> 0 <= am_aidx am2 <= 31 ->
  exists R', msteps SEGS (mkst R (wa 0x5419c) m rom) (mkst R' (wa 0x541d0) m rom) /\
    ta_m2 sc m2 s = ta_fin m2 s /\ as_frame R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\
    getr R' 10 = wa (loc_addr L (LMem m2)) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m2 am2 N F R10 R13 R14 Rsc M2 Hmask Hav Rfr Rai.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (K2 : In m2 (keys s)) by (eapply MT_keys; exact M2).
  set (G2 := loc_addr L (LMem m2)) in *.
  destruct (HMP m2 K2) as (G2a & G2b & G2c & G2d). fold G2 in G2a, G2b, G2c, G2d.
  destruct (rx_aidx L s m [] m2 am2 HR HEO HK M2 Rai) as (hb & Rhb & Mhb & Ehb).
  set (MEM := loc_addr L (LMem (am_mem am2))) in *.
  assert (RMEM : 1 <= MEM <= 2^63-1).
  { set (CH := MCell (LMem (am_mem am2)) 8 (VP m2)).
    assert (CHi : In CH (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; apply (group_in_gpart s m2 am2 CH M2 (proj1 HK)); left; reflexivity).
    pose proof (HC CH CHi) as (P1 & P2 & _). unfold CH in P1, P2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in P1, P2. fold MEM in P1, P2.
    clear - P1 P2 Hsp2 HK1. lia. }
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m2az.m2a_pre R m sc G2 (am_freed am2) MEM hb).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G2a G2b Hsp2 HK1; lia); try (clear - RMEM; lia).
    - exact (rx_mem L s m [] HR HEO HK m2 am2 M2).
    - pose proof (rx_avail L s m [] HR HEO HK m2 am2 M2) as E. rewrite Hav in E. exact E. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m2az.m2a_pm2a R m rom sc G2 (am_freed am2) MEM hb P) as (R' & Hms & Q10 & Q11 & Q12 & Q21 & Qk).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m2a.RES_pm2a fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_m2az.VALS_m2a sc G2 (am_freed am2) MEM hb)).
    assert (Z34 : bv_unsigned (ev E 34) = am_freed am2) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
    assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | clear - Rhb; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z34, ?Z36;
      rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?(Z.mod_small (am_freed am2)), ?(Z.mod_small hb) by (clear - Rfr Rhb; lia).
    rewrite m2_cond by (clear - Rfr Rhb; lia). rewrite Ehb. apply negb_true_iff. apply Z.eqb_neq. exact Hmask. }
  exists R'. split; [exact Hms|]. split; [exact (ta_m2a s sc m2 am2 M2 Hmask)|]. split.
  { apply (as_frame_move R R' m m); [exact F | | intros; reflexivity | intros; reflexivity].
    apply (keeps21 R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F); [|exact Q21].
    intros k Hk. apply Qk. clear - Hk. cbn [In] in *. tauto. }
  split; [exact Q10|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_m2b : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m2 am2 nx amx,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 10 = wa (loc_addr L (LMem m2)) -> getr R 13 = wa (ext_Z true 0 4 (am_freed am2)) -> getr R 14 = wa 2 -> 0 <= sc < 48 ->
  length (st_active s) = 48%nat ->
  MT s m2 = Some (MUsed am2) -> Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> am_next am2 = Some nx -> nx <> m2 ->
  MT s nx = Some (MUsed amx) -> am_avail amx = 0 ->
  0 <= am_freed am2 <= 2^32-1 -> 0 <= am_aidx am2 <= 31 ->
  exists R' m', msteps SEGS (mkst R (wa 0x5419c) m rom) (mkst R' (wa 0x541d0) m' rom) /\
    ta_m2 sc m2 s = ta_fin nx (s_head s sc (Some nx)) /\ NC L [] [] (s_head s sc (Some nx)) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (s_head s sc (Some nx)) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\ getr R' 10 = wa (loc_addr L (LMem nx)) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m2 am2 nx amx N F R10 R13 R14 Rsc Hlen M2 Hmask Hnx Hne Mx Hav Rfr Rai.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (K2 : In m2 (keys s)) by (eapply MT_keys; exact M2).
  assert (Kx : In nx (keys s)) by (eapply MT_keys; exact Mx).
  set (G2 := loc_addr L (LMem m2)) in *. set (NX := loc_addr L (LMem nx)) in *.
  destruct (HMP m2 K2) as (G2a & G2b & G2c & G2d). fold G2 in G2a, G2b, G2c, G2d.
  destruct (HMP nx Kx) as (X1 & X2 & X3 & X4). fold NX in X1, X2, X3, X4.
  pose proof (HMD nx m2 Kx K2 Hne) as DXG. fold G2 NX in DXG.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  destruct (rx_aidx L s m [] m2 am2 HR HEO HK M2 Rai) as (hb & Rhb & Mhb & Ehb).
  set (MEM := loc_addr L (LMem (am_mem am2))) in *.
  assert (RMEM : 1 <= MEM <= 2^63-1).
  { set (CH := MCell (LMem (am_mem am2)) 8 (VP m2)).
    assert (CHi : In CH (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; apply (group_in_gpart s m2 am2 CH M2 (proj1 HK)); left; reflexivity).
    pose proof (HC CH CHi) as (P1 & P2 & _). unfold CH in P1, P2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in P1, P2. fold MEM in P1, P2.
    clear - P1 P2 Hsp2 HK1. lia. }
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m2bz.m2b_pre R m sc G2 (am_freed am2) MEM hb NX).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G2a G2b Hsp2 HK1; lia); try (clear - X1 X2 Hsp2 HK1; lia); try (clear - RMEM; lia).
    all: try (clear - X3 Rsc; lia).
    - exact (rx_mem L s m [] HR HEO HK m2 am2 M2).
    - pose proof (rx_next L s m [] HR HEO HK m2 am2 M2) as E. rewrite Hnx in E. exact E.
    - pose proof (rx_avail L s m [] HR HEO HK nx amx Mx) as E. rewrite Hav in E. exact E.
    - intros d n Hd Hn. pose proof (rx_act_wr L s m [] HR HEO Hctx k ltac:(lia) d n Hd Hn) as E. rewrite Ek in E.
      replace (8 * sc + 621800 + d) with (621800 + 8 * sc + d) by ring. exact E. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m2bz.m2b_pm2b R m rom sc G2 (am_freed am2) MEM hb NX P) as (R' & Hms & Q10 & Q11 & Q12 & Q13 & Q21 & Qk).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m2b.RES_pm2b fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m2bz.VALS_m2b sc G2 (am_freed am2) MEM hb NX)).
    assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | clear - G2a G2b Hsp2 HK1; lia]).
    assert (Z34 : bv_unsigned (ev E 34) = am_freed am2) by (apply zatom; [reflexivity | reflexivity | clear - Rfr; lia]).
    assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | clear - Rhb; lia]).
    assert (Z37 : bv_unsigned (ev E 37) = NX) by (apply zatom; [reflexivity | reflexivity | clear - X1 X2 Hsp2 HK1; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z33, ?Z34, ?Z36, ?Z37;
      rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?(Z.mod_small (am_freed am2)), ?(Z.mod_small hb), ?(Z.mod_small G2), ?(Z.mod_small NX)
        by (clear - Rfr Rhb G2a G2b X1 X2 Hsp2 HK1; lia).
    - apply Z.eqb_neq. clear - DXG. lia.
    - rewrite m2_cond by (clear - Rfr Rhb; lia). rewrite Ehb. apply negb_false_iff. apply Z.eqb_eq. exact Hmask. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_dq2z.AXF_m2bz.m2b_mem_pm2b m R sc G2 (am_freed am2) MEM hb NX) with (act_mem m sc NX) in Hms.
  destruct (nc_act L s m sp0 K sc nx N Rsc Hlen) as (N' & HRS & Hgr & FR & Ks' & MOUT).
  exists R', (act_mem m sc NX). split; [exact Hms|]. split; [exact (ta_m2b s sc m2 am2 nx M2 Hmask Hnx Hne)|].
  split; [exact N'|]. split.
  { apply (as_frame_move R R' m (act_mem m sc NX)); [exact F | | |].
    - apply (keeps21 R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F); [|exact Q21].
      intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
    - intros x Hx. apply MOUT; [clear - Hx Hsp1 Hsp2 HK1; lia | clear - Hx Hsp1 HK1 Rsc; lia].
    - intros x Hx. apply MOUT; [clear - Hx; lia | clear - Hx Rsc; lia]. }
  split; [exact HRS|]. split; [exact Hgr|]. split; [exact FR|]. split; [exact Q10|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

End AS4.
