(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS MngGM
                        AXF_eez AXG_ntfm AXG_ntfg AXG_nQ AXG_nD AXG_nM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.
Ltac memb := first [ AxSymRun3.memb_refl | repeat first [ (left; reflexivity) | right ] ].      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NR.
Context {fx : FPState}.

#[using="Type"] Theorem seg_nr : forall R m rom sp0 G base len,
  getr R 1 = wa 0x51b58 -> getr R 2 = wa (sp0 + -96) -> getr R 9 = wa 613952 -> getr R 10 = wa base -> getr R 11 = wa len ->
  getr R 18 = wa 614104 -> getr R 19 = wa G -> 2^20 <= sp0 <= 2^47 -> sp0 mod 16 = 0 -> 1 <= G <= 2^63-1 ->
  0 <= base <= 2^64-1 -> 0 <= len <= 2^64-1 ->
  exists R', msteps SEGS (mkst R (wa 0x51ca0) m rom) (mkst R' (wa 0x51bb4) m rom) /\
    getr R' 2 = wa (sp0 + -96) /\ getr R' 9 = wa 613952 /\ getr R' 10 = wa G /\ getr R' 11 = wa len /\ getr R' 12 = wa base /\
    getr R' 18 = wa 614104 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 G base len R1 R2 R9 R10 R11 R18 R19 Rsp Asp RG Rb Rl.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nrz.nr_pre R m G sp0 base len) by (constructor; assumption).
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nrz.nr_pnr R m rom G sp0 base len P ltac:(constructor)) as (R' & Hms & Q1 & Q2 & Q9 & Q10 & Q11 & Q12 & Q18 & Q19 & Poth).
  exists R'. split; [exact Hms|]. split; [exact Q2|]. split; [exact Q9|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q18|].
  apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End NR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ext2_id : forall b, 0 <= b <= 65535 -> ext_Z false 0 2 b = b.
Proof. intros b H. unfold ext_Z. cbn -[Z.pow]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  rewrite Z.mod_small by (change (2 ^ (8 * 2)) with 65536; lia). reflexivity. Qed.

Lemma ext1_id' : forall b, 0 <= b <= 255 -> ext_Z false 0 1 b = b.
Proof. intros b H. unfold ext_Z. cbn -[Z.pow]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  rewrite Z.mod_small by (change (2 ^ (8 * 1)) with 256; lia). reflexivity. Qed.

(* [comment removed for export] *)
Section SC.
Context {fx : FPState}.

#[using="Type"] Lemma ns_scs1 : forall regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ,
  1 <= G <= 2^63-1 -> 2^20 <= sp0 <= 2^47 -> 0 <= W <= 2^64-1 -> 0 <= USG <= 2^64-1 -> 1 <= MEM <= 2^63-1 -> 0 <= H3 <= 255 ->
  0 <= OFF <= 65535 -> 1 <= PG <= 2^63-1 -> 0 <= PW <= 2^64-1 -> 0 <= PAV <= 2^32-1 -> 0 <= PFR <= 2^32-1 -> 0 <= SEC <= 2^64-1 ->
  0 <= PCSZ <= 65535 ->
  Z.shiftr W 12 = 0 -> 1 <= Z.shiftr PW 12 -> Z.land H3 31 <= Z.land PW 31 ->
  Z.testbit PAV (Z.land H3 31) = false -> Z.testbit PFR (Z.land H3 31) = false ->
  PCSZ * Z.land H3 31 <= OFF < PCSZ * (Z.land H3 31 + 1) -> OFF <= 256 * Z.shiftr PW 12 - 1 ->
  scs_denot SEGS m (Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nsz.VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_ns.RES_pns1)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ RG Rsp RW RUSG RMEM RH3 ROFF RPG RPW RPAV RPFR RSEC RPCSZ HML HPML HL HAV HFR HOFF HMO.
  set (E := Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nsz.VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | lia]).
  cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_ns.RES_pns1 fst snd].
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: apply sc_br_z; cbn [zeval edenot].
  all: rewrite ?Z34, ?Z37, ?Z38, ?Z40, ?Z41, ?Z42, ?Z44.
  all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
  all: rewrite ?(mod64_of_range W _ _ RW eq_refl eq_refl), ?(mod64_of_range H3 _ _ RH3 eq_refl eq_refl),
               ?(mod64_of_range OFF _ _ ROFF eq_refl eq_refl), ?(mod64_of_range PW _ _ RPW eq_refl eq_refl),
               ?(mod64_of_range PAV _ _ RPAV eq_refl eq_refl), ?(mod64_of_range PFR _ _ RPFR eq_refl eq_refl),
               ?(mod64_of_range PCSZ _ _ RPCSZ eq_refl eq_refl).
  all: litmods.
  all: rewrite ?ext2_id, ?ext1_id', ?ext4_swrap by lia.
  all: rewrite ?(mod64_of_range W _ _ RW eq_refl eq_refl), ?(mod64_of_range H3 _ _ RH3 eq_refl eq_refl),
               ?(mod64_of_range OFF _ _ ROFF eq_refl eq_refl), ?(mod64_of_range PW _ _ RPW eq_refl eq_refl),
               ?(mod64_of_range PCSZ _ _ RPCSZ eq_refl eq_refl).
  all: pose proof (land31_bound H3 ltac:(lia)) as L31h; pose proof (land31_bound PW ltac:(lia)) as L31p.
  all: rewrite ?(mod64_of_range (Z.land H3 31) 0 31 ltac:(lia) eq_refl eq_refl), ?(mod64_of_range (Z.land PW 31) 0 31 ltac:(lia) eq_refl eq_refl).
  all: rewrite ?(Z.mod_small (Z.land H3 31) 32) by lia.
  all: assert (SH : 0 <= Z.shiftr PW 12 <= 2^52) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  all: assert (B1 : 0 <= PCSZ * Z.land H3 31 <= 65535 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
  all: assert (B2 : 0 <= (Z.land H3 31 + 1) * PCSZ <= 32 * 65535) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
  - rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
  - rewrite Z.mod_small by lia. apply Z.eqb_neq. lia.
  - rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
  - rewrite (mask_bit_clear PFR (Z.land H3 31) ltac:(lia) ltac:(lia) HFR). reflexivity.
  - rewrite (mask_bit_clear PAV (Z.land H3 31) ltac:(lia) ltac:(lia) HAV). reflexivity.
  - apply negb_true_iff, Z.ltb_ge. lia.
  - rewrite HML. reflexivity.
Qed.

#[using="Type"] Lemma ns_scs0 : forall regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ,
  1 <= G <= 2^63-1 -> 2^20 <= sp0 <= 2^47 -> 0 <= W <= 2^64-1 -> 0 <= USG <= 2^64-1 -> 1 <= MEM <= 2^63-1 -> 0 <= H3 <= 255 ->
  0 <= OFF <= 65535 -> 1 <= PG <= 2^63-1 -> 0 <= PW <= 2^64-1 -> 0 <= PAV <= 2^32-1 -> 0 <= PFR <= 2^32-1 -> 0 <= SEC <= 2^64-1 ->
  0 <= PCSZ <= 65535 ->
  Z.shiftr W 12 = 0 -> Z.shiftr PW 12 = 0 -> Z.land H3 31 <= Z.land PW 31 ->
  Z.testbit PAV (Z.land H3 31) = false -> Z.testbit PFR (Z.land H3 31) = false ->
  PCSZ * Z.land H3 31 <= OFF < PCSZ * (Z.land H3 31 + 1) ->
  scs_denot SEGS m (Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nsz.VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) (snd (fst OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_ns.RES_pns0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ RG Rsp RW RUSG RMEM RH3 ROFF RPG RPW RPAV RPFR RSEC RPCSZ HML HPML HL HAV HFR HOFF.
  set (E := Ez regs (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nsz.VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | lia]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | lia]).
  cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_ns.RES_pns0 fst snd].
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: apply sc_br_z; cbn [zeval edenot].
  all: rewrite ?Z34, ?Z37, ?Z38, ?Z40, ?Z41, ?Z42, ?Z44.
  all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
  all: rewrite ?(mod64_of_range W _ _ RW eq_refl eq_refl), ?(mod64_of_range H3 _ _ RH3 eq_refl eq_refl),
               ?(mod64_of_range OFF _ _ ROFF eq_refl eq_refl), ?(mod64_of_range PW _ _ RPW eq_refl eq_refl),
               ?(mod64_of_range PAV _ _ RPAV eq_refl eq_refl), ?(mod64_of_range PFR _ _ RPFR eq_refl eq_refl),
               ?(mod64_of_range PCSZ _ _ RPCSZ eq_refl eq_refl).
  all: litmods.
  all: rewrite ?ext2_id, ?ext1_id', ?ext4_swrap by lia.
  all: rewrite ?(mod64_of_range W _ _ RW eq_refl eq_refl), ?(mod64_of_range H3 _ _ RH3 eq_refl eq_refl),
               ?(mod64_of_range OFF _ _ ROFF eq_refl eq_refl), ?(mod64_of_range PW _ _ RPW eq_refl eq_refl),
               ?(mod64_of_range PCSZ _ _ RPCSZ eq_refl eq_refl).
  all: pose proof (land31_bound H3 ltac:(lia)) as L31h; pose proof (land31_bound PW ltac:(lia)) as L31p.
  all: rewrite ?(mod64_of_range (Z.land H3 31) 0 31 ltac:(lia) eq_refl eq_refl), ?(mod64_of_range (Z.land PW 31) 0 31 ltac:(lia) eq_refl eq_refl).
  all: rewrite ?(Z.mod_small (Z.land H3 31) 32) by lia.
  all: assert (B1 : 0 <= PCSZ * Z.land H3 31 <= 65535 * 31) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
  all: assert (B2 : 0 <= (Z.land H3 31 + 1) * PCSZ <= 32 * 65535) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
  - rewrite HPML. reflexivity.
  - rewrite Z.mod_small by lia. apply negb_false_iff, Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia.
  - rewrite (mask_bit_clear PFR (Z.land H3 31) ltac:(lia) ltac:(lia) HFR). reflexivity.
  - rewrite (mask_bit_clear PAV (Z.land H3 31) ltac:(lia) ltac:(lia) HAV). reflexivity.
  - apply negb_true_iff, Z.ltb_ge. lia.
  - rewrite HML. reflexivity.
Qed.
End SC.

(* [comment removed for export] *)
Lemma gc_forget : forall q am i fr, 0 <= i -> ss_fr (nth_slot am i) = Some fr -> fr_off fr = 0 ->
  group_cells q (upd_slot am i (mkSlot (ss_hdr (nth_slot am i)) None)) = group_cells q am.
Proof.
  intros q am i fr Hi Hfr Hoff.
  assert (Hlen : (Z.to_nat i < length (am_slots am))%nat).
  { destruct (Nat.lt_ge_cases (Z.to_nat i) (length (am_slots am))) as [A|A]; [exact A|].
    exfalso. unfold nth_slot in Hfr. rewrite nth_overflow in Hfr by exact A. discriminate. }
  pose proof (upd_slot_fields am i (mkSlot (ss_hdr (nth_slot am i)) None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss).
  assert (Fa : am_aidx (upd_slot am i (mkSlot (ss_hdr (nth_slot am i)) None)) = am_aidx am) by (destruct am; reflexivity).
  unfold group_cells. rewrite Fm, Fl, Fml, Fa. f_equal. apply flat_map_ext_In. intros j Hj.
  unfold zseq in Hj. apply in_map_iff in Hj as (k & <- & _).
  unfold slot_cells. rewrite Fss. rewrite nth_slot_upd_slot by (first [exact Hi | lia | exact Hlen]).
  destruct (0 + Z.of_nat k =? i) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E. rewrite E. rewrite Hfr, Hoff. reflexivity.
Qed.

Lemma msc_forget : forall q am i x, meta_slot_cells q (Some (MUsed (upd_slot am i x))) = meta_slot_cells q (Some (MUsed am)).
Proof. intros q am i x. destruct am; reflexivity. Qed.

(* [comment removed for export] *)
Lemma repr_x_wexc : forall L s m EXC c0 a bs, repr_x L s (bview SEGS m) EXC -> In c0 (image s) -> In (mc_loc c0) EXC ->
  loc_addr L (mc_loc c0) = a -> length bs = mc_w c0 -> 0 <= a -> a + Z.of_nat (mc_w c0) <= 2^64 ->
  repr_x L s (bview SEGS (wbytes m (wa a) bs)) EXC.
Proof.
  intros L s m EXC c0 a bs HR Hc0 He Ea Hlen Ha1 Ha2.
  pose proof HR as (_ & HPW & _).
  assert (Hg : mem_grows m (wbytes m (wa a) bs)) by apply wbytes_grows.
  apply (repr_x_same L s (bview SEGS m) _ EXC HR (fun x E => bview_grow_n m _ x Hg E)).
  intros x Hx c Hc Hn Hin.
  pose proof (bview_ne_range m _ x Hx) as Rx.
  pose proof (image_cell_width s c Hc) as W1. pose proof (image_cell_width s c0 Hc0) as W2.
  assert (A : a <= x < a + Z.of_nat (mc_w c0)).
  { destruct (decide (a <= x < a + Z.of_nat (mc_w c0))) as [A|A]; [exact A|]. exfalso. apply Hx. apply bview_ext.
    apply MngWb.wbytes_out; [rewrite u_wa_small by lia; rewrite Hlen; exact Ha2 | exact Rx | rewrite u_wa_small by lia; rewrite Hlen; lia]. }
  assert (Hne : c <> c0) by (intros ->; exact (Hn He)).
  pose proof (pairwise_map_In _ (cell_range L) _ _ _ HPW Hc Hc0 Hne) as D.
  unfold ranges_disjoint, in_rng, cell_range in *. cbn [fst snd] in *. rewrite Ea in D. lia.
Qed.

Section NS.
Context {fx : FPState}.

#[using="Type"] Theorem seg_ns : forall L X EXC U1 s s1 m R rom sp0 K canary ra s0v s1v s2v s3v g am1 pg amp idx fr,
  NC L X EXC s1 m sp0 K -> ntf_frame R m sp0 canary ra s0v s1v s2v s3v ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 18 = wa 0x95ed8 ->
  MT s1 g = Some (MUsed am1) -> ~ In g X -> am_maplen am1 = 0 -> 0 <= am_sc am1 < 48 -> 0 <= am_last am1 <= 31 -> meta_bits am1 <= 2^64-1 ->
  st_usage s = st_usage s1 -> 0 <= usage_of s1 (am_sc am1) <= 2^64-1 -> length (st_usage s1) = 48%nat ->
  Inv (g :: X) None U1 s1 -> usedX (g :: X) s1 pg amp -> 0 <= idx <= am_last amp -> ss_fr (nth_slot amp idx) = Some fr -> fr_kind fr = FGroup ->
  am_mem am1 = slot_start amp idx -> 1120 <= K ->
  exists R' m',
    msteps SEGS (mkst R (wa 0x51af8) m rom) (mkst R' (wa 0x518d0) m' rom) /\
    NC L (g :: X) (LMem (am_mem am1) :: EXC) (s_ff (s_usg s s1 (am_sc am1) (am_last am1)) pg amp idx) m' (sp0 - 96) (K - 96) /\
    ntf_frame R' m' sp0 canary ra s0v s1v s2v s3v /\
    RS L (s_ff (s_usg s s1 (am_sc am1) (am_last am1)) pg amp idx) s1 /\
    (forall x, In x X -> MT (s_ff (s_usg s s1 (am_sc am1) (am_last am1)) pg amp idx) x = MT s1 x) /\
    mem_grows m m' /\ FRM L s1 sp0 K m m' /\
    find_frame_in (st_metas (s_usg s s1 (am_sc am1) (am_last am1))) (am_mem am1) = Some (pg, idx) /\
    MT (s_usg s s1 (am_sc am1) (am_last am1)) pg = Some (MUsed amp) /\ slot_is_group (nth_slot amp idx) = true /\
    getr R' 1 = wa 0x51b58 /\ getr R' 2 = wa (sp0 - 96) /\ getr R' 8 = wa (loc_addr L (LMem (am_mem am1))) /\ getr R' 9 = wa 613952 /\
    getr R' 10 = wa (loc_addr L (LMem pg)) /\ getr R' 11 = wa idx /\ getr R' 18 = wa 614104 /\ getr R' 19 = wa (loc_addr L (LMem g)) /\
    keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC U1 s s1 m R rom sp0 K canary ra s0v s1v s2v s3v g am1 pg amp idx fr N F R10 R18 Mg NXg Hml Rsc Rl RW Eus Rus Hlu
    HI Up Ridx Hfr Kfr Emem HK96.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s1 EXC (proj1 HK) HEX) as HEO. pose proof HR as (HL & HPW & _).
  pose proof (usedX_MT _ _ _ _ Up) as [Mp NXp].
  assert (NXp' : ~ In pg X /\ pg <> g).
  { rewrite memb_cons in NXp. apply orb_false_iff in NXp as [E1 E2]. split.
    - intros Hin. apply (proj2 (memb_In pg X)) in Hin. rewrite Hin in E2. discriminate.
    - intros ->. rewrite sptr_eqb_refl in E1. discriminate. }
  destruct NXp' as (NXpX & Hpg).
  assert (Kg : In g (keys s1)) by (eapply MT_keys; exact Mg).
  assert (Kp : In pg (keys s1)) by (eapply MT_keys; exact Mp).
  set (G := loc_addr L (LMem g)) in *. set (PG := loc_addr L (LMem pg)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP pg Kp) as (P1 & P2 & P3 & P4).
  pose proof (HMD g pg Kg Kp (fun E => Hpg (eq_sym E))) as DGP.
  fold G PG in G1, G2, G3, G4, P1, P2, P3, P4, DGP.
  (* [comment removed for export] *)
  pose proof (get_meta_ok_inv (g :: X) None U1 s1 pg amp idx fr HI Up Ridx Hfr) as GM. cbn zeta in GM.
  destruct GM as (C4 & C3 & C16 & CH & CMEM & CAV & CFR & CBITS & GEO & (a & ka & Ha & Hka & Ega & CAREA & CSEC) & HLAND & HASRT & HFF).
  pose proof (inv_groups HI pg amp Up) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl idx Ridx) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (Nf & Of & Bf & H16 & FG) & Hhdr).
  destruct (FG Kfr) as (Hoff0 & Hfn).
  assert (Ep : frame_ptr amp idx fr = am_mem am1).
  { unfold frame_ptr. rewrite Hoff0, Z.mul_0_r, padd_0. symmetry. exact Emem. }
  rewrite Ep in C4, C3, C16, GEO, HASRT, HFF.
  set (MEM := loc_addr L (LMem (am_mem am1))). set (PGM := loc_addr L (LMem (am_mem amp))).
  set (OFF := hdr_off16 amp idx fr). set (H3 := hdr_byte3 amp idx fr).
  assert (EH3 : H3 = idx + 192) by (unfold H3, hdr_byte3; rewrite Kfr; reflexivity).
  assert (ROFF : 0 <= OFF <= 65535).
  { split; [|exact H16]. unfold OFF, hdr_off16. rewrite Hoff0. pose proof (stride_pos _ _ _ _ _ (inv_groups HI pg amp Up)) as Sp.
    apply Z.add_nonneg_nonneg; [apply Z.div_pos; [apply Z.mul_nonneg_nonneg; [clear - Sp; lia | clear - Ridx; lia] | unfold UNIT; lia] | lia]. }
  assert (EBASE : MEM - 16 * OFF - 16 = PGM).
  { pose proof (f_equal (fun q => loc_addr L (LMem q)) GEO) as E. cbn beta in E. rewrite loc_padd in E. unfold UNIT in E. fold MEM PGM OFF in E. lia. }
  (* [comment removed for export] *)
  destruct (used_group_region (g :: X) None U1 s1 pg amp HI Up) as (rgP & HrP & HkP & HlP & HoP & HextP & _).
  pose proof HL as (Lctx & Lal & Ldisj & Lrng).
  pose proof (Lal _ _ HrP HlP) as AlP.
  pose proof (used_group_aligned (g :: X) None U1 s1 HI _ pg amp Up (Nat.le_refl _)) as Al16.
  pose proof (stride_mod16 _ _ _ s1 pg amp HI Up) as Hst16.
  assert (EMEMr : MEM = ly_reg L (prid (am_mem amp)) + poff (am_mem amp) + 16 + stride_of amp * idx).
  { unfold MEM. rewrite Emem. unfold slot_start. destruct (am_mem amp) as [r o]. cbn [loc_addr padd prid poff]. unfold UNIT. ring. }
  assert (EPGMr : PGM = ly_reg L (prid (am_mem amp)) + poff (am_mem amp)) by (unfold PGM; destruct (am_mem amp); reflexivity).
  assert (AMEM : MEM mod 16 = 0).
  { unfold PGSZ in AlP.
    pose proof (Z.div_mod (ly_reg L (prid (am_mem amp))) 4096 ltac:(lia)) as D1. rewrite AlP in D1.
    pose proof (Z.div_mod (poff (am_mem amp)) 16 ltac:(lia)) as D2. rewrite Al16 in D2.
    pose proof (Z.div_mod (stride_of amp) 16 ltac:(lia)) as D3. rewrite Hst16 in D3.
    rewrite EMEMr. rewrite D1, D2, D3.
    replace (4096 * (ly_reg L (prid (am_mem amp)) / 4096) + 0 + (16 * (poff (am_mem amp) / 16) + 0) + 16 + (16 * (stride_of amp / 16) + 0) * idx)
      with ((256 * (ly_reg L (prid (am_mem amp)) / 4096) + poff (am_mem amp) / 16 + 1 + stride_of amp / 16 * idx) * 16) by ring.
    apply Z_mod_mult. }
  (* [comment removed for export] *)
  assert (NEO : ~ In (LMem (am_mem amp)) EXC) by exact (hdr_not_exc L X EXC s1 pg amp HEX HPW (proj1 HK) Mp NXpX).
  assert (NEg : ~ In (LMem (am_mem am1)) EXC) by exact (hdr_not_exc L X EXC s1 g am1 HEX HPW (proj1 HK) Mg NXg).
  Ltac rdc HR HPW HEO C := let H := fresh "Hrd" in
    pose proof (repr_x_rdn SEGS _ _ _ _ _ HR C ltac:(apply (not_exc_w _ _ _ _ HPW HEO C); cbn; lia) ltac:(intros z E; discriminate) ltac:(cbn; lia)) as H;
    cbn [mc_loc mc_w mc_val sval_num optr] in H; rewrite ?loc_padd in H.
  rdc HR HPW HEO C4. rename Hrd into M4. fold MEM in M4.
  rdc HR HPW HEO C3. rename Hrd into M3. fold MEM H3 in M3.
  rdc HR HPW HEO C16. rename Hrd into M16. fold MEM OFF in M16.
  pose proof (repr_x_rdn SEGS L s1 m EXC _ HR CH NEO ltac:(intros z E; discriminate) ltac:(cbn; lia)) as MPG.
  cbn [mc_loc mc_w mc_val sval_num] in MPG. fold PGM PG in MPG.
  (* [comment removed for export] *)
  assert (MPM : rdn SEGS m (wa (PG + 16)) 8 = Some (word_to_le_bytes 8 (wa PGM))) by exact (rx_mem L s1 m EXC HR HEO HK pg amp Mp).
  assert (MPW : rdn SEGS m (wa (PG + 32)) 8 = Some (word_to_le_bytes 8 (wa (meta_bits amp)))) by exact (rx_bits L s1 m EXC HR HEO HK pg amp Mp).
  assert (MPA : rdn SEGS m (wa (PG + 24)) 4 = Some (word_to_le_bytes 4 (wa (am_avail amp)))) by exact (rx_avail L s1 m EXC HR HEO HK pg amp Mp).
  assert (MPF : rdn SEGS m (wa (PG + 28)) 4 = Some (word_to_le_bytes 4 (wa (am_freed amp)))) by exact (rx_freed L s1 m EXC HR HEO HK pg amp Mp).
  assert (MGW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa (meta_bits am1)))) by exact (rx_bits L s1 m EXC HR HEO HK g am1 Mg).
  assert (MGM : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM))) by exact (rx_mem L s1 m EXC HR HEO HK g am1 Mg).
  (* [comment removed for export] *)
  pose proof (inv_areas HI) as (AND & AOK & _).
  destruct (AOK a Ha) as (ra' & oa & rga & Ea & Oal & Opg & Hra & Hla & Hofit & Hkind).
  pose proof (Lal ra' rga Hra Hla) as Aal.
  assert (EPG : PG = loc_addr L (LMem a) + 24 + 40 * ka) by (unfold PG; rewrite Ega, loc_padd; unfold AREA_HDR, META_SIZE; ring).
  assert (EA : loc_addr L (LMem a) = ly_reg L ra' + oa) by (rewrite Ea; reflexivity).
  assert (HAG : 4096 * Z.shiftr PG 12 = loc_addr L (LMem a)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096. rewrite EPG, EA. unfold PGSZ, METAS_PER_AREA in *. clear - Oal Aal Hka.
    assert (E : (ly_reg L ra' + oa) = 4096 * ((ly_reg L ra' + oa) / 4096)).
    { pose proof (Z.div_mod (ly_reg L ra' + oa) 4096 ltac:(lia)) as D. rewrite Zplus_mod, Aal, Oal in D. cbn in D. lia. }
    rewrite E. replace (4096 * ((ly_reg L ra' + oa) / 4096) + 24 + 40 * ka) with ((24 + 40 * ka) + ((ly_reg L ra' + oa) / 4096) * 4096) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
  assert (MAREA : rdn SEGS m (wa (4096 * Z.shiftr PG 12 + 0)) 8 = Some (word_to_le_bytes 8 (wa (ly_sec L mod 2^64)))).
  { rewrite Z.add_0_r, HAG. pose proof (repr_x_rdn SEGS L s1 m EXC _ HR CAREA ltac:(apply (not_exc_front L s1 EXC _ HPW HEO);
      apply in_app_iff; right; apply (In_areas_cells_intro s1 (st_areas s1) a _ Ha); intros next; unfold area_cells; left; reflexivity)
      ltac:(intros z E; discriminate) ltac:(cbn; lia)) as E. cbn [mc_loc mc_w mc_val sval_num] in E. rewrite E. f_equal. f_equal. apply wa_eqm. rewrite Z.mod_mod by lia. reflexivity. }
  assert (CSEC' : In (MCell (LCtx CTX_secret) 8 VSec) (ctx_cells s1 ++ areas_cells s1 (st_areas s1))).
  { apply in_app_iff. left. exact (lctx_in_ctx s1 _ CTX_secret CSEC eq_refl). }
  assert (MSEC : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa (ly_sec L mod 2^64)))).
  { pose proof (rx_front_rd L s1 m EXC HR HEO _ CSEC' ltac:(intros z E; discriminate) ltac:(cbn; lia)) as E. cbn [mc_loc mc_w mc_val sval_num loc_addr] in E.
    rewrite Hctx in E. unfold CTX_secret in E. rewrite Z.add_0_r in E. change (0 + 614104) with 614104. rewrite E. f_equal. f_equal. apply wa_eqm. rewrite Z.mod_mod by lia. reflexivity. }
  (* [comment removed for export] *)
  set (W := meta_bits am1). set (USG := usage_of s1 (am_sc am1)). set (SEC := ly_sec L mod 2^64).
  set (PW := meta_bits amp). set (PCSZ := znth (am_sc amp) size_classes).
  destruct (masks_range_inv _ _ _ s1 pg amp HI Up) as (RPA & RPF & RPl & RPs & RPm).
  pose proof (meta_bits_range_inv _ _ _ s1 pg amp L HI Up HL) as RPW. fold PW in RPW.
  assert (RW0 : 0 <= W) by (unfold W; apply meta_bits_nonneg; clear - Rl Rsc Hml; lia).
  assert (ESC : SCW W = am_sc am1) by (unfold W; apply mb_scw; lia).
  assert (Hsp48 : 0 <= am_sc amp < 48).
  { destruct Gcl as [(C63 & Cl0 & _ & _ & _ & CR) | (C & _)]; [|exact C]. exfalso.
    destruct CR as [CR|(fr' & F' & K' & _)]; [discriminate CR|]. assert (idx = 0) by (clear - Ridx Cl0; lia). subst idx. rewrite Hfr in F'. injection F' as <-.
    rewrite Kfr in K'. discriminate. }
  assert (ESCP : SCW PW = am_sc amp) by (unfold PW; apply mb_scw; lia).
  assert (RSEC : 0 <= SEC <= 2^64-1) by (unfold SEC; pose proof (Z.mod_pos_bound (ly_sec L) (2^64) ltac:(lia)); lia).
  assert (RPCSZ : 0 <= PCSZ <= 65535) by (unfold PCSZ; pose proof (size_classes_range _ Hsp48); lia).
  assert (RUSG : 0 <= USG <= 2^64-1) by exact Rus.
  set (CG := MCell (LMem (am_mem am1)) 8 (VP g)).
  assert (CGi : In CG (image s1)).
  { rewrite image_parts. apply in_app_iff. right. apply in_app_iff. right. apply (group_in_gpart s1 g am1 CG Mg (proj1 HK)). left. reflexivity. }
  pose proof (HC CG CGi) as (Q1 & Q2 & _). unfold CG in Q1, Q2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Q1, Q2. fold MEM in Q1, Q2.
  pose proof (HC _ CH) as (Q3 & Q4 & _). cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Q3, Q4. fold PGM in Q3, Q4.
  pose proof (HC _ CAREA) as (Q5 & Q6 & _). cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Q5, Q6.
  set (k := Z.to_nat (am_sc am1)).
  assert (Ek : Z.of_nat k = am_sc am1) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  set (CU := usg_cell k (nth k (st_usage s1) 0)).
  assert (CUi : In CU (image s1)) by (apply usg_cell_in; clear - Ek Rsc; lia).
  assert (ECU : cell_range L CU = (614568 + 8 * am_sc am1, 8)).
  { unfold CU, usg_cell, cell_range. cbn [mc_loc mc_w loc_addr Z.of_nat Pos.of_succ_nat]. rewrite Hctx, Ek. unfold CTX_usage. f_equal. ring. }
  Ltac dU HPW C1 C2 ECU := let D := fresh "D" in
    pose proof (cells_disj _ _ _ _ HPW C1 C2 ltac:(intros E; discriminate E)) as D; rewrite ECU in D; unfold ranges_disjoint, cell_range in D;
    cbn [fst snd mc_loc mc_w Z.of_nat Pos.of_succ_nat] in D; rewrite ?loc_padd in D.
  dU HPW C4 CUi ECU. rename D into DU4. fold MEM in DU4.
  dU HPW C3 CUi ECU. rename D into DU3. fold MEM in DU3.
  dU HPW C16 CUi ECU. rename D into DU16. fold MEM in DU16.
  dU HPW CGi CUi ECU. rename D into DUG. unfold CG in DUG. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in DUG. fold MEM in DUG.
  dU HPW CH CUi ECU. rename D into DUH. fold PGM in DUH.
  dU HPW CAREA CUi ECU. rename D into DUA.
  (* [comment removed for export] *)
  assert (RG : 1 <= G <= 2^63-1) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (RMEM : 1 <= MEM <= 2^63-1) by (clear - Q1 Q2 Hsp2 HK1; lia).
  assert (RPG : 1 <= PG <= 2^63-1) by (clear - P1 P2 Hsp2 HK1; lia).
  assert (RH3 : 0 <= H3 <= 255) by (rewrite EH3; clear - Ridx Glast; lia).
  assert (RSP : 2^20 <= sp0 <= 2^47) by (clear - Hsp1 Hsp2 HK1; lia).
  assert (RW' : 0 <= W <= 2^64-1) by (clear - RW0 RW; lia).
  assert (RPW' : 0 <= PW <= 2^64-1) by (clear - RPW; lia).
  assert (ESCr : 0 <= SCW W <= 47) by (rewrite ESC; clear - Rsc; lia).
  assert (ESCPr : 0 <= SCW PW <= 47) by (rewrite ESCP; clear - Hsp48; lia).
  assert (MU : rdn SEGS m (wa (8 * SCW W + 614568)) 8 = Some (word_to_le_bytes 8 (wa USG))).
  { rewrite ESC. pose proof (rx_usage L s1 m EXC HR HEO Hctx k ltac:(clear - Rsc Ek; lia)) as E. rewrite Ek in E.
    replace (8 * am_sc am1 + 614568) with (614568 + 8 * am_sc am1) by ring. exact E. }
  assert (WUS : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (8 * SCW W + 614568 + d)) n = true).
  { intros d n Hd Hn. rewrite ESC. pose proof (rx_usage_wr L s1 m EXC HR HEO Hctx k ltac:(clear - Rsc Ek; lia) d n Hd Hn) as E. rewrite Ek in E.
    replace (8 * am_sc am1 + 614568 + d) with (614568 + 8 * am_sc am1 + d) by ring. exact E. }
  assert (CGh : cell_holds L (bview SEGS m) CG) by exact (repr_x_holds L s1 _ EXC CG HR CGi NEg).
  assert (WHD : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (MEM + 0 + d)) n = true).
  { intros d n Hd Hn. rewrite Z.add_0_r. pose proof (holds_store_ok SEGS L m CG CGh ltac:(intros z E; discriminate) d n Hd ltac:(cbn; lia)) as E.
    unfold CG in E. cbn [mc_loc] in E. fold MEM in E. exact E. }
  assert (MTB : rdn SEGS m (wa (2 * SCW PW + 98984)) 2 = Some (word_to_le_bytes 2 (wa PCSZ))).
  { pose proof Henv as (_ & E2 & _). rewrite ESCP. replace (2 * am_sc amp + 98984) with (98984 + 2 * am_sc amp) by ring. exact (E2 _ Hsp48). }
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nsz.ns_pre R m G sp0 W USG MEM H3 OFF PG PW (am_avail amp) (am_freed amp) SEC PCSZ).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor.
    - rewrite R2. f_equal; ring.
    - exact R9.
    - exact R10.
    - exact R18.
    - exact HSTK1.
    - exact RG.
    - exact RSP.
    - exact RW'.
    - exact RUSG.
    - exact RMEM.
    - exact RH3.
    - exact ROFF.
    - exact RPG.
    - exact RPW'.
    - exact RPA.
    - exact RPF.
    - exact RSEC.
    - exact RPCSZ.
    - exact Hsp3.
    - exact G4.
    - exact ESCr.
    - clear - ESCr; lia.
    - exact AMEM.
    - exact P4.
    - rewrite ext2_id by exact ROFF. clear - EBASE Q3 RMEM ROFF; lia.
    - exact ESCPr.
    - clear - ESCPr; lia.
    - rewrite HAG. clear - Q5 Q6 Hsp2 HK1; lia.
    - exact MGW.
    - exact MGM.
    - exact MU.
    - exact M4.
    - exact M3.
    - exact M16.
    - rewrite ext2_id by exact ROFF. replace (MEM + -16 * OFF + -16) with PGM by (clear - EBASE; lia). exact MPG.
    - rewrite ext2_id by exact ROFF. replace (MEM + -16 * OFF + -16) with PGM by (clear - EBASE; lia). exact MPM.
    - exact MPW.
    - exact MPA.
    - exact MPF.
    - exact MAREA.
    - exact MSEC.
    - exact MTB.
    - exact WUS.
    - exact WHD.
    - right. clear - G2 HK1; lia.
    - right. clear - ESCr Hsp1 HK1; lia.
    - right. clear - Q2 HK1; lia.
    - rewrite ESC. clear - G3 Rsc; lia.
    - rewrite ESC. clear - DU4 DU3 DU16 DUG; lia.
    - rewrite ext2_id by exact ROFF. replace (MEM + -16 * OFF + -16) with PGM by (clear - EBASE; lia). rewrite ESC. clear - DUH; lia.
    - rewrite ESC. clear - P3 Rsc; lia.
    - rewrite HAG, ESC. clear - DUA; lia.
    - left. clear - ESCr; lia.
    - left. clear - ESCr ESCPr; lia. }
  (* [comment removed for export] *)
  fold H3 in HLAND.
  assert (GA : idx <= am_last amp /\ Z.testbit (am_avail amp) idx = false /\ Z.testbit (am_freed amp) idx = false /\
               PCSZ * idx <= OFF < PCSZ * (idx + 1) /\ (0 < am_maplen amp -> OFF <= am_maplen amp * 4096 / 16 - 1)).
  { unfold get_meta_asserts, view_of in HASRT.
    cbn [gm_p4 gm_p3 gm_off16 gm_meta gm_mem gm_avail gm_freed gm_last gm_sc gm_maplen gm_area_check] in HASRT.
    fold H3 OFF in HASRT. rewrite HLAND in HASRT.
    replace (am_sc amp <? 48) with true in HASRT by (symmetry; apply Z.ltb_lt; exact (proj2 Hsp48)). fold PCSZ in HASRT.
    apply andb_prop in HASRT as [HASRT A5]. apply andb_prop in HASRT as [HASRT A4]. apply andb_prop in A4 as [A4a A4b].
    apply andb_prop in HASRT as [HASRT _]. apply andb_prop in HASRT as [HASRT A3]. apply andb_prop in HASRT as [HASRT A2].
    apply andb_prop in HASRT as [_ A1].
    apply Z.leb_le in A1. apply negb_true_iff in A2. apply negb_true_iff in A3. apply Z.leb_le in A4a. apply Z.ltb_lt in A4b.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [split; [exact A4a | exact A4b]|].
    intros Hml'. rewrite (proj2 (Z.ltb_lt 0 (am_maplen amp)) Hml') in A5. cbn [implb] in A5. apply Z.leb_le in A5. exact A5. }
  destruct GA as (GA1 & GA2 & GA3 & GA4 & GA5).
  assert (EWS : Z.shiftr W 12 = 0).
  { pose proof (mb_shr12 am1 Rl ltac:(clear - Rsc; lia)) as E. fold W in E. rewrite E. exact Hml. }
  assert (EPS : Z.shiftr PW 12 = am_maplen amp).
  { pose proof (mb_shr12 amp RPl ltac:(clear - RPs; lia)) as E. fold PW in E. exact E. }
  assert (EPL : Z.land PW 31 = am_last amp).
  { pose proof (mb_land31 amp RPl ltac:(clear - RPs; lia) RPm) as E. fold PW in E. exact E. }
  assert (HLW : Z.land H3 31 <= Z.land PW 31) by (rewrite HLAND, EPL; exact GA1).
  assert (HAV : Z.testbit (am_avail amp) (Z.land H3 31) = false) by (rewrite HLAND; exact GA2).
  assert (HFR : Z.testbit (am_freed amp) (Z.land H3 31) = false) by (rewrite HLAND; exact GA3).
  assert (HOFF : PCSZ * Z.land H3 31 <= OFF < PCSZ * (Z.land H3 31 + 1)) by (rewrite HLAND; exact GA4).
  (* [comment removed for export] *)
  set (v := usage_of s (am_sc am1) - (am_last am1 + 1)).
  set (m1 := wbytes m (wa (8 * SCW W + 614568)) (word_to_le_bytes 8 (wa ((USG + Z.land (((-1 * W) + -1) mod 2^64) 31) + -32)))).
  set (m' := wbytes m1 (wa (MEM + 0)) (word_to_le_bytes 8 (wa 0))).
  assert (RUN : exists R', msteps SEGS (mkst R (wa 0x51af8) m rom) (mkst R' (wa 0x518d0) m' rom) /\
     getr R' 1 = wa 334680 /\ getr R' 2 = wa (sp0 + -96) /\ getr R' 8 = wa MEM /\ getr R' 9 = wa 613952 /\ getr R' 10 = wa PG /\
     getr R' 11 = wa (Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R' 18 = wa 614104 /\ getr R' 19 = wa G /\
     (forall k, In k [3; 4; 5; 6; 7; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)))).
  { destruct (Z.eq_dec (am_maplen amp) 0) as [E0|E0].
    - destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nsz.ns_pns0 R m rom G sp0 W USG MEM H3 OFF PG PW (am_avail amp) (am_freed amp) SEC PCSZ P
        (ns_scs0 R m G sp0 W USG MEM H3 OFF PG PW (am_avail amp) (am_freed amp) SEC PCSZ RG RSP RW' RUSG RMEM RH3 ROFF RPG RPW' RPA RPF RSEC RPCSZ
           EWS ltac:(rewrite EPS; exact E0) HLW HAV HFR HOFF))
        as (R' & Hms & T1 & T2 & T8 & T9 & T10 & T11 & _ & _ & _ & _ & T18 & T19 & Toth).
      exists R'. split; [exact Hms|]. split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|].
      split; [exact T11|]. split; [exact T18|]. split; [exact T19 | exact Toth].
    - assert (HMO : OFF <= 256 * Z.shiftr PW 12 - 1).
      { rewrite EPS. pose proof (GA5 ltac:(clear - E0 RPm; lia)) as E. replace (am_maplen amp * 4096 / 16) with (256 * am_maplen amp) in E; [exact E|].
        rewrite <- (Z.div_mul (256 * am_maplen amp) 16) by lia. f_equal. ring. }
      destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_nsz.ns_pns1 R m rom G sp0 W USG MEM H3 OFF PG PW (am_avail amp) (am_freed amp) SEC PCSZ P
        (ns_scs1 R m G sp0 W USG MEM H3 OFF PG PW (am_avail amp) (am_freed amp) SEC PCSZ RG RSP RW' RUSG RMEM RH3 ROFF RPG RPW' RPA RPF RSEC RPCSZ
           EWS ltac:(rewrite EPS; clear - E0 RPm; lia) HLW HAV HFR HOFF HMO))
        as (R' & Hms & T1 & T2 & T8 & T9 & T10 & T11 & _ & _ & _ & _ & T18 & T19 & Toth).
      exists R'. split; [exact Hms|]. split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|].
      split; [exact T11|]. split; [exact T18|]. split; [exact T19 | exact Toth]. }
  destruct RUN as (R' & Hms & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & Toth).
  (* [comment removed for export] *)
  set (sA := set_usage (zupd (st_usage s1) k v) s1).
  assert (EsA : s_usg s s1 (am_sc am1) (am_last am1) = sA).
  { unfold s_usg. replace (am_sc am1 <? 48) with true by (symmetry; apply Z.ltb_lt; clear - Rsc; lia). reflexivity. }
  rewrite EsA.
  set (amp' := upd_slot amp idx (mkSlot (ss_hdr (nth_slot amp idx)) None)).
  set (s3 := s_ff sA pg amp idx).
  assert (Es3 : s3 = set_meta sA pg (MUsed amp')) by reflexivity.
  assert (HKA : KS sA) by exact (KS_ctx s1 sA eq_refl eq_refl HK).
  assert (MpA : MT sA pg = Some (MUsed amp)) by exact Mp.
  assert (MgA : MT sA g = Some (MUsed am1)) by exact Mg.
  assert (KpA : In pg (keys sA)) by exact Kp.
  assert (HK3 : KS s3) by (rewrite Es3; exact (KS_set_meta sA pg _ HKA KpA)).
  assert (Keys3 : keys s3 = keys s1) by (rewrite Es3; rewrite keys_set_meta by exact KpA; reflexivity).
  assert (M3g : MT s3 g = Some (MUsed am1)) by (rewrite Es3; rewrite MT_set_other by exact (fun E => Hpg (eq_sym E)); exact MgA).
  assert (ZOMB3 : forall x, In x X -> MT s3 x = MT s1 x).
  { intros x Hx. rewrite Es3. rewrite MT_set_other by (intros ->; exact (NXpX Hx)). reflexivity. }
  assert (GCF : group_cells pg amp' = group_cells pg amp) by exact (gc_forget pg amp idx fr ltac:(clear - Ridx; lia) Hfr Hoff0).
  assert (RS3A : RS L s3 sA) by (rewrite Es3; apply (RS_set_used L sA pg amp amp' HKA MpA); rewrite GCF; reflexivity).
  assert (RSA1 : RS L sA s1) by (apply RS_ctx_only; reflexivity).
  assert (HRS3 : RS L s3 s1) by exact (RS_trans L s1 sA s3 RS3A RSA1).
  (* [comment removed for export] *)
  assert (EGL : Z.land W 31 = am_last am1).
  { pose proof (mb_land31 am1 Rl ltac:(clear - Rsc; lia) ltac:(clear - Hml; lia)) as E. fold W in E. exact E. }
  assert (USGW : (USG + Z.land (((-1 * W) + -1) mod 2^64) 31) + -32 = v).
  { rewrite (usage_dec_val W USG (am_last am1)) by (first [exact EGL | clear - RW'; lia]).
    unfold v, USG, usage_of. rewrite Eus. reflexivity. }
  assert (RA : repr_x L sA (bview SEGS m1) EXC).
  { apply (step_usage L EXC Hctx s1 m k v _ _ HR ltac:(clear - Rsc Ek; lia) Hlu); [rewrite ESC, Ek; ring | rewrite USGW; reflexivity]. }
  assert (RB : repr_x L sA (bview SEGS m1) (LMem (am_mem am1) :: EXC)) by (apply (repr_x_weaken L sA _ EXC _ RA); intros l Hl; right; exact Hl).
  assert (CGA : In CG (image sA)).
  { rewrite image_parts. apply in_app_iff. right. apply in_app_iff. right. apply (group_in_gpart sA g am1 CG MgA (proj1 HKA)). left. reflexivity. }
  assert (RC : repr_x L sA (bview SEGS m') (LMem (am_mem am1) :: EXC)).
  { unfold m'. apply (repr_x_wexc L sA m1 _ CG (MEM + 0) _ RB CGA ltac:(left; reflexivity)); [unfold CG; cbn [mc_loc]; fold MEM; ring | reflexivity | clear - RMEM; lia | unfold CG; cbn [mc_w Z.of_nat Pos.of_succ_nat]; clear - RMEM; lia]. }
  assert (RD : repr_x L s3 (bview SEGS m') (LMem (am_mem am1) :: EXC)).
  { apply (repr_x_next L sA s3 (bview SEGS m') (bview SEGS m') _ [] RC eq_refl eq_refl RS3A (fun x E => E)).
    - intros c Hc. left. rewrite Es3 in Hc. destruct (cov_setm sA pg amp amp' c HKA MpA Hc) as [H1|[H1|H1]]; [exact H1| |].
      + apply (In_image_used sA pg amp c HKA MpA). left. rewrite <- (msc_forget pg amp idx (mkSlot (ss_hdr (nth_slot amp idx)) None)). exact H1.
      + apply (In_image_used sA pg amp c HKA MpA). right. rewrite <- GCF. exact H1.
    - intros c [].
    - constructor.
    - intros x Hx. exfalso. exact (Hx eq_refl). }
  assert (Hg : mem_grows m m') by (unfold m', m1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (CHG : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (614568 + 8 * am_sc am1 <= x < 614568 + 8 * am_sc am1 + 8) \/ (MEM <= x < MEM + 8)).
  { assert (L8 : forall w, length (word_to_le_bytes 8 w) = 8%nat) by (intros; apply length_Z_to_le_bytes).
    intros x Hx Hne. destruct (chg_split m m1 m' (wa x) Hne) as [A|A].
    - right. unfold m' in A. apply chg_wbytes in A; [| clear - RMEM; lia | rewrite L8; clear - RMEM; lia | exact Hx].
      rewrite L8 in A. clear - A; lia.
    - left. unfold m1 in A. apply chg_wbytes in A; [| clear - ESCr; lia | rewrite L8; clear - ESCr; lia | exact Hx].
      rewrite L8, ESC in A. clear - A; lia. }
  assert (FR : FRM L s1 sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|A].
    - exists CU. split; [exact CUi|]. split; [wide_tac Hctx|]. unfold in_rng. rewrite ECU. cbn [fst snd]. exact A.
    - exists CG. split; [exact CGi|]. split; [wide_tac Hctx|]. unfold in_rng, cell_range, CG. cbn [fst snd mc_loc mc_w Z.of_nat Pos.of_succ_nat]. fold MEM. clear - A; lia. }
  assert (LOW : forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> x < sp0 - K).
  { intros x Hx Hne. destruct (CHG x Hx Hne) as [A|A]; [clear - A Rsc Hsp1; lia | clear - A Q2; lia]. }
  assert (NC3 : NC L (g :: X) (LMem (am_mem am1) :: EXC) s3 m' (sp0 - 96) (K - 96)).
  { constructor.
    - exact RD.
    - intros l [<-|Hl].
      + exists g, am1. split; [left; reflexivity|]. split; [exact M3g | reflexivity].
      + destruct (HEX l Hl) as (x & b & Hx & Mx & El). exists x, b. split; [right; exact Hx|]. split; [rewrite ZOMB3 by exact Hx; exact Mx | exact El].
    - intros x [<-|Hx]; [exists am1; exact M3g | rewrite ZOMB3 by exact Hx; exact (HZU x Hx)].
    - exact HK3.
    - exact Hctx.
    - exact (nenv_keep L s1 sp0 K m m' Henv FR HC Hsp1).
    - apply (stk_ok_shift m' sp0 K 96); [exact (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg) | clear; lia | clear - RSP; lia | clear - RSP; lia].
    - clear - HK96; lia.
    - replace (sp0 - 96 - (K - 96)) with (sp0 - K) by ring. exact Hsp1.
    - clear - Hsp2; lia.
    - clear - Hsp3; lia.
    - intros c Hc. replace (sp0 - 96 - (K - 96)) with (sp0 - K) by ring. exact (cplace_RS L (sp0 - K) s3 s1 HRS3 HC c Hc).
    - rewrite Keys3. replace (sp0 - 96 - (K - 96)) with (sp0 - K) by ring. exact HMP.
    - rewrite Keys3. exact HMD. }
  assert (FRM3 : ntf_frame R' m' sp0 canary ra s0v s1v s2v s3v).
  { apply (frame_keep_heap L s1 sp0 K m m' R R' canary ra s0v s1v s2v s3v FR HC Hsp1 HK1 Hsp2 LOW F T2 T9 Hg). }
  exists R', m'. split; [exact Hms|]. split; [exact NC3|]. split; [exact FRM3|]. split; [exact HRS3|]. split; [exact ZOMB3|].
  split; [exact Hg|]. split; [exact FR|]. split; [exact HFF|]. split; [exact MpA|].
  split; [unfold slot_is_group; rewrite Hfr, Kfr; reflexivity|].
  split; [exact T1|]. split; [rewrite T2; f_equal; ring|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|].
  split; [rewrite T11, ext1_id' by exact RH3; rewrite Z.mod_small by (clear - RH3; lia); rewrite HLAND; reflexivity|].
  split; [exact T18|]. split; [exact T19|].
  apply (keep_of_list R' R _ Toth). reflexivity.
Qed.
End NS.
