(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 131 of its 179 lines of code are new or changed and 3292 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacHuntObserveSeg_ent.v; 687 of its 763 lines of code are new or changed and 103 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntObserveCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.
#[local] Notation ho_shent_gen := (@ReacHuntObserveCore.ho_shent_gen rc PI).
#[local] Notation hoC := (@ReacHuntObserveCore.hoC rc PI).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation ho_svals := (@ReacHuntObserveCore.ho_svals rc PI).
#[local] Notation ho_extraM := (@ReacHuntObserveCore.ho_extraM rc PI B).
#[local] Notation EHOm := (@ReacHuntObserveCore.EHOm rc PI B).

Lemma hoM_sval : forall (c : hoC) (j : nat), (j < 13)%nat ->
  nth j (ho_svals c) 0 = bv_unsigned (getr (c_regs c) (ho_sreg j)).
Proof.
intros c j Hj. unfold ho_svals.
do 13 (destruct j as [|j]; [reflexivity|]). exfalso. lia.
Qed.

Lemma hoM_ew_low : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z) (n : nat), (n < A_TEXT)%nat ->
  ew (EHOm c regs2 FL) n = ew (Ereg regs2 (ho_extraM c FL)) n.
Proof. intros c regs2 FL n Hn. unfold EHOm. apply Eimg_low. exact Hn. Qed.

Lemma hoM_ew_reg : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z) (n : nat) (r : bv 5),
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew (EHOm c regs2 FL) n = getr regs2 r.
Proof.
intros c regs2 FL n r Hr Hn. rewrite hoM_ew_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs2 _ n r Hr).
Qed.

Lemma hoM_ew32 : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z),
  ew (EHOm c regs2 FL) 32 = Z_to_bv 64 SB.
Proof.
intros c regs2 FL. rewrite hoM_ew_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs2 (ho_extraM c FL) 0).
Qed.

Lemma hoM_ew33 : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z),
  ew (EHOm c regs2 FL) 33 = Z_to_bv 64 FL.
Proof.
intros c regs2 FL. rewrite hoM_ew_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs2 (ho_extraM c FL) 1).
Qed.

Lemma hoM_ew59 : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z),
  ew (EHOm c regs2 FL) 59 = Z_to_bv 64 (as_uar_cell B).
Proof.
intros c regs2 FL. rewrite hoM_ew_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs2 (ho_extraM c FL) 27).
Qed.

Lemma hoM_ew_sv : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z) (j : nat), (j < 13)%nat ->
  ew (EHOm c regs2 FL) (34 + j) = Z_to_bv 64 (bv_unsigned (getr (c_regs c) (ho_sreg j))).
Proof.
intros c regs2 FL j Hj. rewrite hoM_ew_low by (unfold A_TEXT; lia).
replace (34 + j)%nat with (32 + (2 + j))%nat by lia.
rewrite (ew_Ereg_extra regs2 (ho_extraM c FL) (2 + j)).
unfold ho_extraM.
rewrite (map_nth (Z_to_bv 64) ([SB; FL] ++ ho_svals c ++ repeat 0 12 ++ [as_uar_cell B]) 0 (2 + j)).
f_equal.
replace (2 + j)%nat with (S (S j)) by lia.
change ([SB; FL] ++ ho_svals c ++ repeat 0 12 ++ [as_uar_cell B])
  with (SB :: FL :: (ho_svals c ++ repeat 0 12 ++ [as_uar_cell B])).
cbn [nth].
rewrite app_nth1 by (unfold ho_svals; rewrite length_map, length_seq; lia).
apply hoM_sval. exact Hj.
Qed.

Lemma hoM_ra_kept : forall (rd rd' : Z -> option Z) (a n : Z),
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. rewrite (HK x Hx). split; [exact Hs | exact Hok].
Qed.

Lemma hoM_sh_in_frame : forall ly S (W : world SEGS) mem md cid pos p n x,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid -> p <= x < p + n ->
  in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S W mem md cid pos p n x HAR Hin Hfp Hpn Hx.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1;
  replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1;
  replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (L1 : f / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (L2 : x / 8 < f / 8 + bs / 8) by (rewrite E8f, E8b; apply Z.div_lt_upper_bound; lia).
unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia.
Qed.

Lemma hoM_sh_off_app : forall ly S (W : world SEGS) mem md cid pos a p n,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
  in_app p n -> p + n <= YM05.alloc_ceiling -> 0 <= n -> ~ (p <= a < p + n).
Proof.
intros ly S W mem md cid pos a p n HAR Hin Ha Happ Hpc Hn.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4096 & Hceil & _).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1;
  replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1;
  replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
pose proof asan_consts as (CA & _).
unfold in_zr, shadow_addr in Ha. cbn [fst snd] in Ha.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Lemma hoM_ro_plain : forall (E : env) (W : world SEGS) (mem : word -> option byte) (n : nat) (p lo hi : Z),
  ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> 0 <= p + lo -> p + hi <= 2 ^ 64 ->
  (forall o, lo <= o < hi -> apresent (w_H W) mem (p + o)) ->
  region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some n) lo hi lo hi []).
Proof.
intros E W mem n p lo hi En Hp Hlo Hhi HP. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite En, (unsigned_lit_small p) by lia.
split; [exact Hlo|]. split; [exact Hhi|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). apply HP. exact Ho.
Qed.

Lemma hoM_ro_cell8 : forall (E : env) (W : world SEGS) (mem : word -> option byte) (nb : nat) (p : Z)
    (e : sv) (v : Z),
  ew E nb = Z_to_bv 64 p -> 0 <= p -> p + 8 <= 2 ^ 64 ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) p = Some v ->
  region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some nb) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 e)]).
Proof.
intros E W mem nb p e v En Hp0 Hp8 He Hv Hrd. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite En, (unsigned_lit_small p) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ p 0 8 e v); [exact He | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hrd).
Qed.

Lemma hoM_ro_uar : forall (E : env) (W : world SEGS) (mem : word -> option byte) (p : Z),
  ew E 59 = Z_to_bv 64 p -> 0 <= p -> p + 4 <= 2 ^ 64 ->
  rd32 (aview SEGS (w_H W) mem) p 1 ->
  region_ok SEGS E (mrestrict (w_H W) mem) (uar_cell_regionP 59).
Proof.
intros E W mem p En Hp0 Hp4 Hrd. unfold uar_cell_regionP, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite En, (unsigned_lit_small p) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ p 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hrd).
Qed.

Lemma hoM_ro_frame : forall (E : env) (W : world SEGS) (mem : word -> option byte) (F FL : Z),
  ew E 18 = Z_to_bv 64 F -> ew E 33 = Z_to_bv 64 FL ->
  0 <= F -> F + 128 <= 2 ^ 64 -> 0 <= FL < 2 ^ 64 ->
  (forall a, F <= a < F + 128 -> apresent (w_H W) mem a) ->
  val_mem SEGS (mrestrict (w_H W) mem) (F + 120) 8 FL ->
  region_ok SEGS E (mrestrict (w_H W) mem) ho_frame_region.
Proof.
intros E W mem F FL E18 E33 HF0 HF8 HFL HP HV. unfold ho_frame_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E18, (unsigned_lit_small F) by lia.
split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ F 120 8 (SOff 33 0) FL);
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  change (N.to_nat 8) with 8%nat. exact HV.
Qed.

Lemma hoM_ro_saved : forall (c : hoC) (W : world SEGS) (mem : word -> option byte)
    (regs2 : bvmap 5 word) (FL sp : Z),
  ew (EHOm c regs2 FL) 8 = Z_to_bv 64 sp -> 104 <= sp -> sp < 2 ^ 64 ->
  (forall a, sp - 104 <= a < sp -> apresent (w_H W) mem a) ->
  (forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (sp - 8 * (Z.of_nat j + 1)) 8
      (bv_unsigned (getr (c_regs c) (ho_sreg j)))) ->
  region_ok SEGS (EHOm c regs2 FL) (mrestrict (w_H W) mem) ho_saved_region.
Proof.
intros c W mem regs2 FL sp E8 Hsp0 Hsp1 HP HS. unfold ho_saved_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E8, (unsigned_lit_small sp) by lia.
split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- apply Forall_forall. intros ch Hch. apply in_map_iff in Hch. destruct Hch as (j & <- & Hj).
  apply in_seq in Hj. destruct Hj as [_ Hj]. cbn [Nat.add] in Hj.
  unfold ho_svchunk.
  pose proof (bv_unsigned_in_range 64 (getr (c_regs c) (ho_sreg j))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr.
  apply (chunk_ok_val SEGS (EHOm c regs2 FL) _ sp (- 8 * (Z.of_nat j + 1)) 8 (SOff (34 + j) 0)
    (bv_unsigned (getr (c_regs c) (ho_sreg j)))).
  + cbn [sv_denot]. rewrite (hoM_ew_sv c regs2 FL j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity.
  + zside.
  + zside.
  + change (N.to_nat 8) with 8%nat.
    replace (sp + - 8 * (Z.of_nat j + 1)) with (sp - 8 * (Z.of_nat j + 1)) by lia.
    exact (HS j ltac:(lia)).
Qed.

Lemma hoM_ro_fsh : forall (E : env) (W : world SEGS) (mem : word -> option byte) (S24 : Z) (SH : list Z),
  ew E 24 = Z_to_bv 64 S24 -> 0 <= S24 -> S24 + 16 <= 2 ^ 64 ->
  length SH = 16%nat -> Forall (fun z : Z => 0 <= z < 256) SH ->
  (forall a, S24 <= a < S24 + 16 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 16 -> aview SEGS (w_H W) mem (S24 + i) = Some (nth (Z.to_nat i) SH 0)) ->
  region_ok SEGS E (mrestrict (w_H W) mem) (ho_fshadow_region SH).
Proof.
intros E W mem S24 SH E24 H0 H16 LSH RSH HP HA. unfold ho_fshadow_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E24, (unsigned_lit_small S24) by lia.
split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- apply Forall_forall. intros ch Hch. apply in_map_iff in Hch. destruct Hch as (i & <- & Hi).
  apply in_seq in Hi. destruct Hi as [_ Hi]. cbn [Nat.add] in Hi.
  unfold ho_shchunk.
  assert (Hv : 0 <= nth i SH 0 < 256)
  by (rewrite Forall_forall in RSH; apply RSH; apply nth_In; lia).
  assert (Hav : aview SEGS (w_H W) mem (S24 + Z.of_nat i) = Some (nth i SH 0)).
  { replace (nth i SH 0) with (nth (Z.to_nat (Z.of_nat i)) SH 0) by (rewrite Nat2Z.id; reflexivity).
    apply HA. lia. }
  destruct (val_mem1_of_aview SEGS (w_H W) mem (S24 + Z.of_nat i) (nth i SH 0) Hav) as [Hvm Hvr].
  apply (chunk_ok_val SEGS E _ S24 (Z.of_nat i) 1 (SLit (nth i SH 0)) (nth i SH 0));
  [reflexivity | zside | zside |].
  change (N.to_nat 1) with 1%nat. exact Hvm.
Qed.

Local Ltac ho_cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac ho_lia_d1 := first
  [ ho_cdisj; lia
  | match goal with H : _ \/ _ |- _ => destruct H as [H|H]; ho_cdisj; lia end
  | lia ].
Lemma hoM_disj : forall (E : env) (SH : list Z) (wo : bool) (out sp1 sp V0 V1 V12 UC F h : Z),
  base_val E (Some 2%nat) = sp1 -> base_val E (Some 8%nat) = sp ->
  base_val E (Some 18%nat) = F -> base_val E (Some 19%nat) = out ->
  base_val E (Some 21%nat) = h -> base_val E (Some 24%nat) = SB + F / 8 ->
  base_val E (Some (A_OBJ 0)) = V0 -> base_val E (Some (A_OBJ 1)) = V1 ->
  base_val E (Some (A_OBJ 12)) = V12 -> base_val E (Some 59%nat) = UC ->
  in_app h 480 -> h + 480 <= YM05.alloc_ceiling ->
  in_app F 128 -> F + 128 <= YM05.alloc_ceiling ->
  (h + 480 <= F \/ F + 128 <= h) ->
  (h + 480 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= h) ->
  (F + 128 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= F) ->
  YM05.alloc_ceiling <= sp - 8688 -> sp - 176 <= sp1 -> sp1 + 56 <= sp - 104 ->
  YImgTop.IMG_LO <= V0 -> V0 + 8 <= YImgTop.IMG_TOP ->
  YImgTop.IMG_LO <= V1 -> V1 + 8 <= YImgTop.IMG_TOP ->
  YImgTop.IMG_LO <= V12 -> V12 + 8 <= YImgTop.IMG_TOP ->
  YImgTop.IMG_LO <= UC -> UC + 8 <= YImgTop.IMG_TOP ->
  zseps [(V0, 8); (V1, 8); (V12, 8); (UC, 4)] ->
  (wo = true -> in_app out 24 /\ out + 24 <= YM05.alloc_ceiling /\
     (out + 24 <= h \/ h + 480 <= out) /\ (out + 24 <= F \/ F + 128 <= out) /\
     (sp <= out \/ out + 24 <= sp1) /\
     (out + 24 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= out)) ->
  pairwise_disjoint E (ho_regionsM SH wo).
Proof.
intros E SH wo out sp1 sp V0 V1 V12 UC F h
  B2 B8 B18 B19 B21 B24 B241 B242 B253 B59
  Ah Ahc AF AFc DhF Oh OF Hspc Hsp1lo Hsp1hi
  HV0a HV0b HV1a HV1b HV12a HV12b HUCa HUCb HSEP HO.
pose proof asan_consts as (CA & _). destruct CA as [CAlo CAhi].
cbn [zseps zseps_from fst snd] in HSEP.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Ah, AF.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. unfold SB in *.
repeat match goal with Hx : _ /\ _ |- _ => destruct Hx as [? ?] end.
assert (Dq : 8 * (F / 8) <= F <= 8 * (F / 8) + 7).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M. lia. }
apply pairwise_disjoint_of_extents.
unfold ho_regionsM, ho_outreg, ho_sp1_region, ho_saved_region, got_regionP, bcell_regionP,
  uar_got_regionP, uar_cell_regionP, ho_frame_region, ho_fshadow_region, ho_hregM, extent_of_region.
destruct wo.
- destruct (HO eq_refl) as (Ao & Aoc & Doh & DoF & Dosp & Oo).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Ao.
  destruct Ao as [Ao0 Ao1].
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B2, B8, B18, B19, B21, B24, B241, B242, B253, B59.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear B2 B8 B18 B19 B21 B24 B241 B242 B253 B59 HO.
  revert Dq. generalize (F / 8). intros q Dq.
  repeat split; ho_lia_d1.
- cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B2, B8, B18, B21, B24, B241, B242, B253, B59.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear B2 B8 B18 B19 B21 B24 B241 B242 B253 B59 HO.
  revert Dq. generalize (F / 8). intros q Dq.
  repeat split; ho_lia_d1.
Qed.

Lemma hoM_atoms : forall (E : env) (wo : bool) (sp1 sp F out h FL UC : Z),
  ew E 2 = Z_to_bv 64 sp1 -> ew E 8 = Z_to_bv 64 sp -> ew E 9 = Z_to_bv 64 sp1 ->
  ew E 18 = Z_to_bv 64 F -> ew E 19 = Z_to_bv 64 out -> ew E 21 = Z_to_bv 64 h ->
  ew E 24 = Z_to_bv 64 (SB + F / 8) -> ew E 25 = Z_to_bv 64 F ->
  ew E 32 = Z_to_bv 64 SB -> ew E 33 = Z_to_bv 64 FL -> ew E 59 = Z_to_bv 64 UC ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
  4096 <= F -> F + 128 <= YM05.alloc_ceiling -> F mod 32 = 0 ->
  4096 <= h -> h + 480 <= YM05.alloc_ceiling -> h mod 8 = 0 ->
  4096 <= FL < YM05.alloc_ceiling ->
  YImgTop.IMG_LO <= UC -> UC + 8 <= YImgTop.IMG_TOP -> UC mod 4 = 0 ->
  (wo = true -> 4096 <= out /\ out + 24 <= YM05.alloc_ceiling /\ out mod 8 = 0) ->
  facts_ok E (mkFacts (ho_atomsM wo) [] []).
Proof.
intros E wo sp1 sp F out h FL UC E2 E8 E9 E18 E19 E21 E24 E25 E32 E33 E59
  Hsp1 Hsp1a Hsp Hspa HF0 HFc HF32 Hh0 Hhc Hh8 HFL HUCa HUCb HUC4 HO.
pose proof asan_consts as (CA & _). destruct CA as [CAlo CAhi].
assert (HFd1 : 512 <= F / 8 <= 17592186044416)
by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (HFd2 : (F / 8) mod 4 = 0).
{ apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [q Hq].
  replace F with (4 * q * 8) by lia. rewrite Z.div_mul by lia.
  apply Z.mod_divide; [lia|]. exists q. lia. }
split; [|split; exact I].
unfold ho_atomsM. destruct wo.
- destruct (HO eq_refl) as (Ho0 & Hoc & Ho8).
  cbn [app f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E9, E18, E19, E21, E24, E25, E32, E33, E59.
  rewrite !unsigned_lit_small by (unfold SB, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
  repeat split; first [exact I | lia].
- cbn [app f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E9, E18, E21, E24, E25, E32, E33, E59.
  rewrite !unsigned_lit_small by (unfold SB, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
  repeat split; first [exact I | lia].
Qed.

Lemma hoM_stk : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  YM05.alloc_ceiling <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK /\ spZ (c_regs c) <= 2 ^ 47 /\
  spZ (c_regs c) mod 16 = 0 /\
  spZ (c_regs c) - 176 <= sp1 <= spZ (c_regs c) - 160 /\ sp1 mod 32 = 0 /\
  (forall a, spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < spZ (c_regs c) -> apresent (w_H W2) mem2 a).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB.
destruct HB as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
destruct HPRE as (_ & _ & _ & _ & _ & _ & Hal16 & Hwin & Hspc & _).
destruct HMID as (HJ2 & _).
destruct HSP1 as (_ & Hsp1r & Hsp1a).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (CA & _). destruct CA as [CAlo CAhi].
split; [lia|]. split; [lia|]. split; [exact Hal16|]. split; [lia|]. split; [exact Hsp1a|].
intros a Ha. apply Hpres2. lia.
Qed.

Lemma hoM_hfacts : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  4096 <= c_h c /\ c_h c + 480 <= YM05.alloc_ceiling /\ in_app (c_h c) 480 /\
  (c_h c + 480 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= c_h c) /\
  (forall a, c_h c <= a < c_h c + 480 -> apresent (w_H W2) mem2 a) /\
  amem_range (c_h c) 480 /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (c_h c) 480 /\
  In (c_hb c, c_hn c) (ablocks B ly2 S2) /\ c_h c mod 8 = 0.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB.
destruct HB as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh8 & Hinb & Hhb & Hhe & _).
destruct HMID as (HJ2 & _ & _ & Hperm & _).
pose proof (proj1 HJ2) as HAR2.
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2))
by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hinb).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) HAR2 Hin2)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ (c_hb c) (c_hn c) HAR2 Hin2) as Hbimg.
unfold off_img in Hbimg.
assert (Happ : in_app (c_h c) 480) by (apply (in_app_sub _ _ _ _ Hbapp); lia).
split; [lia|]. split; [lia|]. split; [exact Happ|].
split; [lia|].
split; [intros a Ha; exact (proj1 (Hbpres a ltac:(lia)))|].
split.
{ apply (amem_range_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) (c_h c) 480 HAR2 Hin2); lia. }
split; [|split; [exact Hin2 | exact Hh8]].
apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) (c_h c) 480 HAR2 Hin2); lia.
Qed.

Lemma hoM_ffacts : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  4096 <= F /\ F + 128 <= YM05.alloc_ceiling /\ in_app F 128 /\ F mod 32 = 0 /\
  (F + 128 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= F) /\
  (forall a, F <= a < F + 128 -> apresent (w_H W2) mem2 a) /\
  (forall i, 0 <= i < 16 -> apresent (w_H W2) mem2 (SB + F / 8 + i)) /\
  4096 <= flag_addr (c_lyc c) 1 fpos < YM05.alloc_ceiling /\
  (c_h c + 480 <= F \/ F + 128 <= c_h c) /\
  val_mem SEGS (mrestrict (w_H W2) mem2) (F + 120) 8 (flag_addr (c_lyc c) 1 fpos).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB.
pose proof HB as HB2.
destruct (hoM_hfacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB2)
  as (_ & _ & _ & _ & _ & _ & _ & Hin2 & _).
destruct HB as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
pose proof HPRE as HPRE2.
destruct HPRE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhb & Hhe & _).
destruct HMID as (HJ2 & Hfrs & Hfa & Hperm & HKEPT & HRO2 & HG2 & LH2 & HFLw).
pose proof (proj1 HJ2) as HAR2.
assert (Hf1 : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity.
assert (HFe : frame_addr ly2 1 fpos = F) by (rewrite (Hfa 1 fpos); symmetry; exact HFeq).
assert (HFLe : flag_addr ly2 1 fpos = flag_addr (c_lyc c) 1 fpos).
{ pose proof (Hfa 1 fpos) as Hq. unfold frame_addr in Hq. unfold flag_addr. lia. }
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 1 fpos HAR2 Hf1) as (Hal32 & Happ & Hpres & Hspres).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 1 fpos HAR2 Hf1) as (H4096 & Hceil & _).
pose proof (frm_off_imgP B ly2 S2 W2 mem2 md2 1 fpos HAR2 Hf1) as Hfimg. unfold off_img in Hfimg.
rewrite HFe in Hal32, Happ, Hpres, H4096, Hceil, Hfimg, Hspres.
rewrite Hfb in Happ, Hpres, Hceil, Hfimg, Hspres.
destruct (FFL ly2 S2 W2 mem2 md2 1 fpos HAR2 Hf1) as (_ & _ & _ & (HFL1 & _ & HFL2)).
rewrite HFLe in HFL1, HFL2.
assert (Hsa : shadow_addr F = SB + F / 8) by reflexivity.
rewrite Hsa in Hspres.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) 1 fpos HAR2 Hin2 Hf1) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFe, Hfb in Hd.
split; [lia|]. split; [lia|]. split; [exact Happ|]. split; [exact Hal32|].
split; [lia|].
split; [intros a Ha; exact (proj1 (Hpres a ltac:(lia)))|].
split; [intros i Hi; exact (proj1 (Hspres i ltac:(cbn; lia)))|].
split; [lia|].
split; [lia|].
rewrite <- HFLe, <- HFe.
exact (val_mem_of_rdword SEGS (w_H W2) mem2 _ _ (proj1 HFLw)).
Qed.

Lemma hoM_ofacts : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F -> c_out c <> 0 ->
  4096 <= c_out c /\ c_out c + 24 <= YM05.alloc_ceiling /\ in_app (c_out c) 24 /\
  c_out c mod 8 = 0 /\
  (c_out c + 24 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= c_out c) /\
  (c_out c + 24 <= c_h c \/ c_h c + 480 <= c_out c) /\
  (c_out c + 24 <= F \/ F + 128 <= c_out c) /\
  (spZ (c_regs c) <= c_out c \/ c_out c + 24 <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK) /\
  (forall a, c_out c <= a < c_out c + 24 -> apresent (w_H W2) mem2 a) /\
  amem_range (c_out c) 24 /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (c_out c) 24.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hne.
pose proof HB as HB2. pose proof HB as HB3.
destruct (hoM_hfacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB2)
  as (Hh0 & Hhc & Hhapp & _ & _ & _ & _ & _ & _).
destruct (hoM_ffacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB3)
  as (HF0 & HFc & HFapp & HF32 & HFimg & _ & _ & _ & _ & _).
destruct HB as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
pose proof HPRE as HPRE2.
destruct HPRE2 as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & HOUT & _).
destruct HJc as (mdc & HJc).
pose proof (proj1 HJc) as HARc.
destruct (HOUT Hne) as (HTO & Doh & _).
destruct HTO as (Ho8 & Ho63 & Hamem & Hosp & Hcls & HRAc & Hhull & Hwr & LO & HGO & HR1).
destruct HMID as (HJ2 & Hfrs & Hfa & Hperm & HKEPT & HRO2 & HG2 & LH2 & HFLw).
destruct HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (proj1 HJ2) as HAR2.
assert (Hf1 : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity.
assert (HFe : frame_addr ly2 1 fpos = F) by (rewrite (Hfa 1 fpos); symmetry; exact HFeq).
assert (MAIN : 4096 <= c_out c /\ c_out c + 24 <= YM05.alloc_ceiling /\ in_app (c_out c) 24 /\
  (c_out c + 24 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= c_out c) /\
  (c_out c + 24 <= F \/ F + 128 <= c_out c) /\
  (forall a, c_out c <= a < c_out c + 24 -> apresent (w_H W2) mem2 a) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (c_out c) 24).
{ destruct HR1 as [(cid & pos & Hin & Hlo & Hhi) | (b & m & Hin & Hlo & Hhi)].
  - assert (Hinf : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
    destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hinf) as (_ & Happ & Hpres & _).
    destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hinf) as (H4096 & Hceil & _).
    pose proof (frm_off_imgP B ly2 S2 W2 mem2 md2 cid pos HAR2 Hinf) as Hoimg. unfold off_img in Hoimg.
    rewrite (Hfa cid pos) in Happ, Hpres, H4096, Hceil, Hoimg.
    assert (Hoapp : in_app (c_out c) 24) by (apply (in_app_sub _ _ _ _ Happ); lia).
    assert (Hoc : c_out c + 24 <= YM05.alloc_ceiling) by lia.
    assert (HdF : c_out c + 24 <= F \/ F + 128 <= c_out c).
    { apply in_split in Hin. destruct Hin as (l2 & l3 & Hsplit).
      pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (1, fpos) (cid, pos) [] l2 l3 HAR2
        ltac:(rewrite Hfrs, Hsplit; reflexivity)) as Hq.
      unfold zdisjoint, frame_rng in Hq. cbn [fst snd] in Hq.
      rewrite HFe, Hfb, (Hfa cid pos) in Hq. lia. }
    split; [lia|]. split; [lia|]. split; [exact Hoapp|]. split; [lia|]. split; [exact HdF|].
    split; [intros a Ha; exact (proj1 (Hpres a ltac:(lia)))|].
    apply (hoM_ra_kept (aview SEGS (w_H (c_W c)) (c_memc c)) (aview SEGS (w_H W2) mem2) (c_out c) 24);
      [| exact HRAc].
    intros x Hx.
    assert (Hzr : in_zr (shadow_of_addr SHADOW_OFF x)
                   (shadow_addr (frame_addr (c_lyc c) cid pos), fs_frame_bytes cid / 8)).
    { apply (hoM_sh_in_frame (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc cid pos (c_out c) 24 x HARc Hin);
      lia. }
    apply (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin (or_intror Hzr)).
    intros [Hw | (_ & Hw)].
    + exact (hoM_sh_off_app (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc cid pos _ (c_h c) 480
        HARc Hin Hzr Hhapp Hhc ltac:(lia) Hw).
    + exact (hoM_sh_off_app (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc cid pos _ (c_out c) 24
        HARc Hin Hzr Hoapp Hoc ltac:(lia) Hw).
  - assert (Hin2 : In (b, m) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2)
      as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
    pose proof (blk_off_imgP _ _ _ _ _ _ b m HAR2 Hin2) as Hoimg. unfold off_img in Hoimg.
    pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 1 fpos HAR2 Hin2 Hf1) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFe, Hfb in Hd.
    split; [lia|]. split; [lia|].
    split; [apply (in_app_sub _ _ _ _ Hbapp); lia|].
    split; [lia|]. split; [lia|].
    split; [intros a Ha; exact (proj1 (Hbpres a ltac:(lia)))|].
    apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 b m (c_out c) 24 HAR2 Hin2); lia. }
destruct MAIN as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact Ho8|].
split; [exact M4|]. split; [exact Doh|]. split; [exact M5|].
split; [exact Hosp|]. split; [exact M6|]. split; [exact Hamem | exact M7].
Qed.

Lemma ho_mid_entry : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F SH (wo : bool) af,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ho_fsh W2 mem2 F SH -> length SH = 16%nat -> Forall (fun z : Z => 0 <= z < 256) SH ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  st_ok_pi (fx := c_fq c) SEGS VAL (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (ss_hoM SH wo af)
    (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + af)) mem2 (seg_rom SEGS)))
  /\ img_env VAL A_LIM (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F SH wo af HB HFSH LSH RSH HWO.
pose proof HB as HB1. pose proof HB as HB2. pose proof HB as HB3. pose proof HB as HB4.
destruct (hoM_stk c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB1)
  as (Hspc & Hsp47 & Hspa & Hsp1r & Hsp1a & Hpres2).
destruct (hoM_hfacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB2)
  as (Hh0 & Hhc & Hhapp & Hhimg & Hhpres & Hhamem & Hhra & Hhin2 & Hh8).
destruct (hoM_ffacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB3)
  as (HF0 & HFc & HFapp & HF32 & HFimg & HFpres & HSpres & HFL & HdhF & HFLv).
pose proof asan_consts as (CA & CB & CC & CD & CE). destruct CA as [CAlo CAhi].
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
rewrite HSTK in Hspc, Hpres2.
set (FL := flag_addr (c_lyc c) 1 fpos) in *.
set (E := EHOm c regs2 FL) in *.
destruct HB as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
destruct HMID as (HJ2 & Hfrs & Hfa & Hperm & HKEPT & HRO2 & HG2 & LH2 & HFLw).
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS ly2 S2 W2 mem2 md2 HAR2) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep.
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 1)) as VR1.
pose proof (pa_val_range (A_OBJ 12)) as VR12.
assert (E2 : ew E 2 = Z_to_bv 64 sp1)
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 2 2%bv eq_refl ltac:(lia)); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ (c_regs c)))
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 8 8%bv eq_refl ltac:(lia)); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 sp1)
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 9 9%bv eq_refl ltac:(lia)); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 F)
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 18 18%bv eq_refl ltac:(lia)); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 (c_h c))
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 21 21%bv eq_refl ltac:(lia)); exact R21).
assert (E24 : ew E 24 = Z_to_bv 64 (SB + F / 8))
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 24 24%bv eq_refl ltac:(lia)); exact R24).
assert (E25 : ew E 25 = Z_to_bv 64 F)
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 25 25%bv eq_refl ltac:(lia)); exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; exact (hoM_ew32 c regs2 FL)).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by (unfold E; exact (hoM_ew33 c regs2 FL)).
assert (E59 : ew E 59 = Z_to_bv 64 (as_uar_cell B)) by (unfold E; exact (hoM_ew59 c regs2 FL)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (unfold E, EHOm; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (unfold E, EHOm; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold E, EHOm; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
set (OUT := bv_unsigned (ew E 19)) in *.
assert (EOUT : ew E 19 = Z_to_bv 64 OUT) by (unfold OUT; symmetry; apply Z_to_bv_bv_unsigned).
assert (BOUT : base_val E (Some 19%nat) = OUT) by reflexivity.
assert (HOeq : wo = true -> OUT = c_out c).
{ intros Hwo. destruct (HWO Hwo) as [Hne R19]. unfold OUT, E.
  rewrite (hoM_ew_reg c regs2 FL 19 19%bv eq_refl ltac:(lia)), R19.
  apply unsigned_lit_small.
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rout1 & Rout2 & _).
  lia. }
clear HPRE HJ2 HAR2 Hfrs Hfa Hperm HKEPT HRO2 HG2 LH2 HFLw HSP1 HB1 HB2 HB3
  R2 R3 R4 R8 R9 R18 R21 R24 R25 Hhamem Hhra Hhin2.
assert (HQ : 0 <= F / 8 <= 17592186044416)
by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; unfold SB in *; lia]).
assert (ROsp1 : region_ok SEGS E (mrestrict (w_H W2) mem2) ho_sp1_region).
{ unfold ho_sp1_region. apply (hoM_ro_plain E W2 mem2 2%nat sp1 0 56 E2 ltac:(lia) ltac:(lia) ltac:(lia)).
  intros o Ho. apply Hpres2. lia. }
assert (ROsv : region_ok SEGS E (mrestrict (w_H W2) mem2) ho_saved_region).
{ unfold E. apply (hoM_ro_saved c W2 mem2 regs2 FL (spZ (c_regs c)) E8 ltac:(lia) ltac:(lia)).
  - intros a Ha. apply Hpres2. lia.
  - exact HSAVED. }
assert (ROgot : region_ok SEGS E (mrestrict (w_H W2) mem2) got_regionP).
{ unfold got_regionP.
  apply (hoM_ro_cell8 E W2 mem2 (A_OBJ 0) (VAL (A_OBJ 0)) (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12))
    EO0 ltac:(lia) ltac:(unfold YImgTop.IMG_TOP in *; lia)); [| lia | exact Kgot].
  cbn [sv_denot]. rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (ROcell : region_ok SEGS E (mrestrict (w_H W2) mem2) (bcell_regionP 32)).
{ unfold bcell_regionP.
  apply (hoM_ro_cell8 E W2 mem2 (A_OBJ 12) (VAL (A_OBJ 12)) (SOff 32 0) SB
    EO12 ltac:(lia) ltac:(unfold YImgTop.IMG_TOP in *; lia)); [| unfold SB; lia | exact Kcell].
  cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (ROugot : region_ok SEGS E (mrestrict (w_H W2) mem2) (uar_got_regionP 59)).
{ unfold uar_got_regionP.
  apply (hoM_ro_cell8 E W2 mem2 (A_OBJ 1) (VAL (A_OBJ 1)) (SOff 59 0) (as_uar_cell B)
    EO1 ltac:(lia) ltac:(unfold YImgTop.IMG_TOP in *; lia));
  [| unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia | exact Kguar].
  cbn [sv_denot]. rewrite E59, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (ROucell : region_ok SEGS E (mrestrict (w_H W2) mem2) (uar_cell_regionP 59)).
{ apply (hoM_ro_uar E W2 mem2 (as_uar_cell B) E59
    ltac:(unfold YImgTop.IMG_LO in *; lia) ltac:(unfold YImgTop.IMG_TOP in *; lia) Kuar). }
assert (ROfrm : region_ok SEGS E (mrestrict (w_H W2) mem2) ho_frame_region).
{ apply (hoM_ro_frame E W2 mem2 F FL E18 E33 ltac:(lia) ltac:(lia) ltac:(lia) HFpres HFLv). }
assert (ROfsh : region_ok SEGS E (mrestrict (w_H W2) mem2) (ho_fshadow_region SH)).
{ apply (hoM_ro_fsh E W2 mem2 (SB + F / 8) SH E24 ltac:(unfold SB in *; lia)
    ltac:(unfold SB in *; lia) LSH RSH).
  - intros a Ha. replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia. apply HSpres. lia.
  - exact HFSH. }
assert (ROhb : region_ok SEGS E (mrestrict (w_H W2) mem2) ho_hregM).
{ unfold ho_hregM.
  apply (hoM_ro_plain E W2 mem2 21%nat (c_h c) 0 480 E21 ltac:(lia) ltac:(lia) ltac:(lia)).
  intros o Ho. apply Hhpres. lia. }
assert (ROout : wo = true -> region_ok SEGS E (mrestrict (w_H W2) mem2) ho_outreg).
{ intros Hwo. destruct (HWO Hwo) as [Hne R19].
  destruct (hoM_ofacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB4 Hne)
    as (Ho0 & Hoc & Hoapp & Ho8 & Hoimg & Hoh & HoF & Hosp & Hopres & Hoamem & Hora).
  assert (E19 : ew E 19 = Z_to_bv 64 (c_out c))
  by (unfold E; rewrite (hoM_ew_reg c regs2 FL 19 19%bv eq_refl ltac:(lia)); exact R19).
  unfold ho_outreg.
  apply (hoM_ro_plain E W2 mem2 19%nat (c_out c) 0 24 E19 ltac:(lia) ltac:(lia) ltac:(lia)).
  intros o Ho. apply Hopres. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_hoM. apply pa_entry_st_ok_full.
  + unfold E, EHOm. apply regs_ok_Eimg_Ereg.
  + unfold ho_regionsM. destruct wo; vm_compute; reflexivity.
  + unfold ho_regionsM. destruct wo.
    * pose proof (ROout eq_refl) as ROout'.
      cbn [app]. repeat apply Forall_cons; try apply Forall_nil; assumption.
    * cbn [app]. repeat apply Forall_cons; try apply Forall_nil; assumption.
  + apply (hoM_disj E SH wo OUT sp1 (spZ (c_regs c)) (VAL (A_OBJ 0)) (VAL (A_OBJ 1))
      (VAL (A_OBJ 12)) (as_uar_cell B) F (c_h c)).
    * exact (VB 2%nat sp1 E2 ltac:(lia)).
    * exact (VB 8%nat (spZ (c_regs c)) E8 ltac:(lia)).
    * exact (VB 18%nat F E18 ltac:(lia)).
    * exact BOUT.
    * exact (VB 21%nat (c_h c) E21 ltac:(lia)).
    * exact (VB 24%nat (SB + F / 8) E24 ltac:(unfold SB in *; lia)).
    * exact (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0 ltac:(lia)).
    * exact (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1 ltac:(lia)).
    * exact (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12 ltac:(lia)).
    * exact (VB 59%nat (as_uar_cell B) E59
        ltac:(unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia)).
    * exact Hhapp.
    * exact Hhc.
    * exact HFapp.
    * exact HFc.
    * lia.
    * exact Hhimg.
    * exact HFimg.
    * exact Hspc.
    * lia.
    * lia.
    * unfold YImgTop.IMG_LO in *; lia.
    * unfold YImgTop.IMG_TOP in *; lia.
    * unfold YImgTop.IMG_LO in *; lia.
    * unfold YImgTop.IMG_TOP in *; lia.
    * unfold YImgTop.IMG_LO in *; lia.
    * unfold YImgTop.IMG_TOP in *; lia.
    * unfold YImgTop.IMG_LO in *; lia.
    * unfold YImgTop.IMG_TOP in *; lia.
    * cbn [zseps zseps_from fst snd] in Hsep |- *. exact Hsep.
    * intros Hwo. destruct (HWO Hwo) as [Hne _]. rewrite (HOeq Hwo).
      destruct (hoM_ofacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB4 Hne)
        as (Ho0 & Hoc & Hoapp & Ho8 & Hoimg & Hoh & HoF & Hosp & Hopres & Hoamem & Hora).
      rewrite HSTK in Hosp.
      split; [exact Hoapp|]. split; [exact Hoc|]. split; [exact Hoh|]. split; [exact HoF|].
      split; [lia | exact Hoimg].
  + apply (hoM_atoms E wo sp1 (spZ (c_regs c)) F OUT (c_h c) FL (as_uar_cell B)
      E2 E8 E9 E18 EOUT E21 E24 E25 E32 E33 E59).
    * lia.
    * exact Hsp1a.
    * lia.
    * exact Hspa.
    * exact HF0.
    * exact HFc.
    * exact HF32.
    * exact Hh0.
    * exact Hhc.
    * exact Hh8.
    * exact HFL.
    * unfold YImgTop.IMG_LO in *; lia.
    * unfold YImgTop.IMG_TOP in *; lia.
    * exact Huar4.
    * intros Hwo. destruct (HWO Hwo) as [Hne _]. rewrite (HOeq Hwo).
      destruct (hoM_ofacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB4 Hne)
        as (Ho0 & Hoc & Hoapp & Ho8 & _).
      split; [exact Ho0|]. split; [exact Hoc | exact Ho8].
- unfold E, EHOm. apply Eimg_env.
Qed.

Lemma ho_shokM : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F (wo : bool),
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  sh_ok SEGS HOBx (ho_SHM wo) (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (mrestrict (w_H W2) mem2).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F wo HB HWO.
pose proof HB as HB1. pose proof HB as HB2.
destruct (hoM_hfacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB2)
  as (Hh0 & Hhc & Hhapp & Hhimg & Hhpres & Hhamem & Hhra & Hhin2 & Hh8).
pose proof HB as HB3.
destruct HB3 as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof asan_consts as (CA & _). destruct CA as [CAlo CAhi].
set (FL := flag_addr (c_lyc c) 1 fpos) in *.
set (E := EHOm c regs2 FL) in *.
assert (E21 : ew E 21 = Z_to_bv 64 (c_h c))
by (unfold E; rewrite (hoM_ew_reg c regs2 FL 21 21%bv eq_refl ltac:(lia)); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; exact (hoM_ew32 c regs2 FL)).
clear HPRE HMID HSP1 R2 R3 R4 R8 R9 R18 R21 R24 R25 HSAVED HB2.
assert (SHh : shent_ok SEGS HOBx E (mrestrict (w_H W2) mem2) (mkSHE 21 0 480)).
{ apply (ho_shent_gen E (w_H W2) mem2 21%nat (c_h c) 0 480 E32 E21 ltac:(lia) ltac:(lia)).
  - replace (c_h c + 0) with (c_h c) by lia. replace (480 - 0) with 480 by lia. exact Hhamem.
  - replace (c_h c + 0) with (c_h c) by lia. replace (480 - 0) with 480 by lia. exact Hhra. }
unfold ho_SHM. destruct wo.
- destruct (HWO eq_refl) as [Hne R19].
  destruct (hoM_ofacts c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB1 Hne)
    as (Ho0 & Hoc & Hoapp & Ho8 & Hoimg & Hoh & HoF & Hosp & Hopres & Hoamem & Hora).
  assert (E19 : ew E 19 = Z_to_bv 64 (c_out c))
  by (unfold E; rewrite (hoM_ew_reg c regs2 FL 19 19%bv eq_refl ltac:(lia)); exact R19).
  cbn [app]. unfold sh_ok. apply Forall_cons; [|apply Forall_cons; [exact SHh | apply Forall_nil]].
  apply (ho_shent_gen E (w_H W2) mem2 19%nat (c_out c) 0 24 E32 E19 ltac:(lia) ltac:(lia)).
  + replace (c_out c + 0) with (c_out c) by lia. replace (24 - 0) with 24 by lia. exact Hoamem.
  + replace (c_out c + 0) with (c_out c) by lia. replace (24 - 0) with 24 by lia. exact Hora.
- cbn [app]. unfold sh_ok. apply Forall_cons; [exact SHh | apply Forall_nil].
Qed.

End h.
End f.
End d.
