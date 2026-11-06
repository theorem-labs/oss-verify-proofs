(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Segment A of sb_dec's ASan walk (fuzz_identity.asan 0x83494 .. 0x835f4): seg_sbd_A of sb_dec_inv.v.
   The prologue and the use-after-return flag load (plain run to the call at 0x834f8), __asan_stack_malloc_0
   (YC85 aj_stack_malloc_atS), the frame header, the frame's shadow and the digit loop (plain runs, split at the
   loop's data-dependent branches 0x835dc and the pad branch 0x835e4), to sbd_A_end. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YI0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85 YC81 YC4b YC45 YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
(* The plain proof of sb_dec (released, origin/ossv/recipes c8557374ad2e): sbd_q, sbd_r, sbd_swrap, used as
   they are; referred to by its full path (lib.A.Prog.sb_dec has the same short name). *)
Require OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec sb_dec_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* YC4b.v switches lia's division / modulo handling off for every file that loads it; switch it back on here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section h.
Variable B : asyms.

(* ---- what the call keeps of its entry state, step by step (tcj_kept) ------------------------------------- *)
(* A byte the call may change besides its window and its write set: its own new frame, the frame's shadow,
   the frame's flag byte; none of these is above the allocator ceiling, in the image, in a heap block of the
   entry state or in a frame of it (or that frame's shadow). *)
Definition sbd_fresh (lyc : alayout) (Sc : astate) (a : Z) : Prop :=
  a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall bb m i, In (bb, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> a <> bb + i) /\
  (forall cid pos, In (cid, pos) (frames Sc) ->
     ~ in_zr a (frame_rng lyc (cid, pos)) /\ ~ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
(* At the call's entry it has kept everything. *)
Lemma sbd_kept0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp (E : Z -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= sp - SB_DEC_STK -> sp <= sp0 ->
  tcj_kept B SB_DEC_STK lyc Sc W memc W memc sp E.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp E HJ Hwin Hsp.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ Hp; exact Hp|].
intros a Ha. apply Hpres. clear - Ha Hwin Hsp. lia.
Qed.
Section k.
Hypothesis LAWS : AR_laws SEGS B.
(* A run that changes only bytes of X, each in the call's window, its write set, or fresh. *)
Lemma sbd_kept_step : forall STK lyc Sc W m0 mdc m1 m2 sp (E X : Z -> Prop),
  alloc_ceiling <= sp - STK -> AR SEGS B lyc Sc W m0 mdc ->
  tcj_kept B STK lyc Sc W m0 W m1 sp E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (forall a, X a -> (sp - STK <= a < sp) \/ (E a /\ ~ in_img SEGS a) \/ sbd_fresh lyc Sc a) ->
  (forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
  tcj_kept B STK lyc Sc W m0 W m2 sp E.
Proof.
intros STK lyc Sc W m0 mdc m1 m2 sp E X Hce HAR (K1 & K2 & K3 & K4 & K5 & K6) HX HXc Hpr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split.
{ intros a Ha Hw HE. rewrite HX; [exact (K1 a Ha Hw HE) | clear - Ha C1; lia |].
  intros Hx. destruct (HXc a Hx) as [Hw' | [(HE' & _) | (Hf & _)]]; [exact (Hw Hw') | exact (HE HE') | clear - Ha Hf; lia]. }
split.
{ intros bb m i Hin Hi HE.
  destruct (al_blocks _ _ LAWS lyc Sc W m0 mdc bb m HAR Hin) as (_ & H4096 & Hceil & _).
  rewrite HX; [exact (K2 bb m i Hin Hi HE) | clear - H4096 Hceil Hi C1; lia |].
  intros Hx. destruct (HXc _ Hx) as [Hw' | [(HE' & _) | (_ & _ & Hf & _)]];
  [clear - Hw' Hce Hceil Hi; lia | exact (HE HE') | exact (Hf bb m i Hin Hi eq_refl)]. }
split.
{ intros a Him Hns Herr. pose proof (pa_segs_low a Him) as Hlo.
  rewrite HX; [exact (K3 a Him Hns Herr) | unfold kLowMemEnd in Hlo; clear - Hlo; lia |].
  intros Hx. destruct (HXc _ Hx) as [Hw' | [(_ & HE') | (_ & Hf & _)]];
  [unfold kLowMemEnd in Hlo; clear - Hw' Hce Hlo C1; lia | exact (HE' Him) | exact (Hf Him)]. }
split.
{ intros cid pos a Hin Hr HE.
  destruct (frames_bounds SEGS B LAWS lyc Sc W m0 mdc cid pos HAR Hin) as (H4096 & Hceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    assert (D1 : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= alloc_ceiling / 8)
      by (apply Z.div_le_mono; [lia | clear - Hceil; lia]).
    assert (D3 : frame_addr lyc cid pos / 8 + fs_frame_bytes cid / 8 <= (frame_addr lyc cid pos + fs_frame_bytes cid) / 8).
    { pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
      pose proof (Z.div_mod (frame_addr lyc cid pos + fs_frame_bytes cid) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (frame_addr lyc cid pos + fs_frame_bytes cid) 8 ltac:(lia)).
      clear - H H0 H1 H2 H3 H4. lia. }
    assert (D4 : 8 * (alloc_ceiling / 8) <= alloc_ceiling).
    { pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)). pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)). clear - H H0. lia. }
    assert (D5 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
    clear - Hr H4096 Hceil C1 D1 D3 D4 D5. destruct Hr as [Hr | Hr]; lia. }
  rewrite HX; [exact (K4 cid pos a Hin Hr HE) | clear - Ha C1; lia |].
  intros Hx. destruct (HXc _ Hx) as [Hw' | [(HE' & _) | (_ & _ & _ & Hf)]];
  [clear - Hw' Hce Ha; lia | exact (HE HE') | destruct (Hf cid pos Hin) as (Hf1 & Hf2); destruct Hr as [Hr | Hr]; [exact (Hf1 Hr) | exact (Hf2 Hr)]]. }
split; [intros a Ha Hw Hp; apply Hpr; exact (K5 a Ha Hw Hp)|].
intros a Ha. apply Hpr. exact (K6 a Ha).
Qed.
(* A runtime call whose clobbered stack [slo, shi) lies in the call's window. *)
Lemma sbd_kept_call : forall STK lyc Sc W m0 m1 m2 sp slo shi (E : Z -> Prop),
  alloc_ceiling <= sp - STK -> sp <= 2 ^ 47 -> sp - STK <= slo -> shi <= sp ->
  tcj_kept B STK lyc Sc W m0 W m1 sp E ->
  acall_kept SEGS B lyc Sc W m1 W m2 slo shi (fun _ => False) ->
  tcj_kept B STK lyc Sc W m0 W m2 sp E.
Proof.
intros STK lyc Sc W m0 m1 m2 sp slo shi E Hce H47 Hlo Hhi (K1 & K2 & K3 & K4 & K5 & K6) (A1 & A2 & A3 & A4 & A5 & A6).
split.
{ intros a Ha Hw HE. rewrite (A1 a Ha) by (intros H; apply Hw; clear - H Hlo Hhi; lia). exact (K1 a Ha Hw HE). }
split.
{ intros bb m i Hin Hi HE. rewrite (A2 bb m i Hin Hi (fun H => H)). exact (K2 bb m i Hin Hi HE). }
split.
{ intros a Him Hns Herr. rewrite (A3 a Him Hns Herr). exact (K3 a Him Hns Herr). }
split.
{ intros cid pos a Hin Hr HE. rewrite (A4 cid pos a Hin Hr (fun H => H)). exact (K4 cid pos a Hin Hr HE). }
split.
{ intros a Ha Hw Hp. apply A5; [exact Ha | intros H; apply Hw; clear - H Hlo Hhi; lia | exact (K5 a Ha Hw Hp)]. }
intros a Ha. destruct (Z_lt_le_dec a slo) as [Hl | Hl]; [|destruct (Z_lt_le_dec a shi) as [Hh | Hh]].
- apply A5; [clear - Ha Hce H47 Hl; lia | clear - Hl; lia | exact (K6 a Ha)].
- apply A6. clear - Hl Hh. lia.
- apply A5; [clear - Ha Hce H47 Hh; lia | clear - Hh; lia | exact (K6 a Ha)].
Qed.
End k.
(* ---- sp after andi sp,sp,-32 (cgif lib/A/ACja.v:93-117, identity's names) ------------------------------- *)
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite YI0s.M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

(* ---- the state right after __asan_stack_malloc_0 returns (0x834fc) ------------------------------------- *)
Definition sbdA_ret (g : sbd_ctx) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = sq_W g /\ exists S2 regs2 mem2 md2 pos sp1,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (AF_sb_dec + 0x68))) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B (sq_STK g) (sq_sp0 g) (sq_FP g) (sq_ly g) (sq_S g) (sq_W0 g) (sq_mem0 g) (sq_md0 g)
      ((0, pos) :: sq_own g) (sq_lyc g) S2 (sq_W g) mem2 md2 (sq_k g) /\
    tcj_kept B SB_DEC_STK (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) (sq_W g) mem2 (sq_sp g)
      (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) (sq_acc g)) /\
    ablocks B (sq_lyc g) S2 = ablocks B (sq_lyc g) (sq_Sc g) /\ ~ In (0, pos) (frames (sq_Sc g)) /\
    zero_shadow (aview SEGS (w_H (sq_W g)) mem2) SHADOW_OFF (sq_F g pos) (fs_frame_bytes 0) /\
    rdword (aview SEGS (w_H (sq_W g)) mem2) (sq_F g pos + fs_frame_bytes 0 - 8) = Some (flag_addr (sq_lyc g) 0 pos) /\
    sq_sp g - 112 <= sp1 <= sq_sp g - 96 /\ sp1 mod 32 = 0 /\
    getr regs2 2 = w64 sp1 /\ getr regs2 9 = w64 sp1 /\ getr regs2 8 = w64 (sq_sp g) /\
    getr regs2 10 = w64 (sq_F g pos) /\ getr regs2 18 = w64 (sq_b g) /\ getr regs2 19 = w64 (sq_md g) /\
    getr regs2 20 = w64 (sq_v g) /\ getr regs2 21 = w64 SB /\
    getr regs2 3 = getr (sq_regs g) 3 /\ getr regs2 4 = getr (sq_regs g) 4 /\
    getr regs2 22 = getr (sq_regs g) 22 /\ getr regs2 23 = getr (sq_regs g) 23 /\
    getr regs2 24 = getr (sq_regs g) 24 /\ getr regs2 25 = getr (sq_regs g) 25 /\
    getr regs2 26 = getr (sq_regs g) 26 /\ getr regs2 27 = getr (sq_regs g) 27 /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 8) 8 (raZ (sq_regs g)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 16) 8 (bv_unsigned (getr (sq_regs g) 8)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 24) 8 (bv_unsigned (getr (sq_regs g) 9)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 32) 8 (bv_unsigned (getr (sq_regs g) 18)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 40) 8 (bv_unsigned (getr (sq_regs g) 19)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 48) 8 (bv_unsigned (getr (sq_regs g) 20)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 56) 8 (bv_unsigned (getr (sq_regs g) 21)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 64) 8 (bv_unsigned (getr (sq_regs g) 22)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_sp g - 72) 8 (bv_unsigned (getr (sq_regs g) 23)) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_b g) 8 (sq_p g) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_b g + 8) 8 (sq_cap g) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_b g + 16) 8 (sq_n g) /\
    val_mem SEGS (mrestrict (w_H (sq_W g)) mem2) (sq_b g + 24) 4 (sq_ov g).
(* A field of a region whose chunk is an atom with a known value. *)
Lemma sbd_fld : forall E m n bse cs lo hi wlo whi od (w : N) i v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal w (SOff i 0))) cs -> ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  Z.of_N w <= 8 ->
  val_mem SEGS m (bse + od) (N.to_nat w) v.
Proof.
intros E m n bse cs lo hi wlo whi od w i v Hr Hb Hc Hi Hv Hw.
eapply (field_of_region E m n bse cs lo hi wlo whi od w (SOff i 0) v Hr Hb Hc); [|exact Hv | exact Hw].
cbn [sv_denot]. rewrite Hi, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma sbd_regv : forall (x : word), x = Z_to_bv 64 (bv_unsigned x) /\ 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
intros x. split; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range _ x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
(* a register of a symbolic state, its expression unnormalised *)
Ltac prreg0 HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
Ltac sbd_in := cbn [In]; repeat first [left; reflexivity | right].

(* ---- shadow geometry, ported from fuzz_disco's sb_dec walk (
   lib/A/Prog/SbDecLib.v:66-93), unchanged *)
Lemma shadow_cell_bound : forall F b, 0 <= F -> 0 <= b -> F + b < 2 ^ 47 ->
  SHADOW_OFF <= shadow_addr F /\ shadow_addr F + b / 8 < kHighMemBeg.
Proof.
intros F b H0 H1 H2. unfold shadow_addr, SHADOW_OFF, kHighMemBeg.
assert (F / 8 + b / 8 <= (F + b) / 8).
{ apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le F 8 ltac:(lia)). pose proof (Z.mul_div_le b 8 ltac:(lia)). lia. }
assert ((F + b) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= F / 8) by (apply Z.div_pos; lia). assert (0 <= b / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma shadow_disj : forall F G b c, F mod 64 = 0 -> G mod 64 = 0 -> b mod 64 = 0 -> c mod 64 = 0 ->
  0 <= F -> 0 <= G -> 0 <= b -> 0 <= c -> (F + b <= G \/ G + c <= F) ->
  forall a, shadow_addr F <= a < shadow_addr F + b / 8 -> shadow_addr G <= a < shadow_addr G + c / 8 -> False.
Proof.
intros F G b c HF HG Hb Hc F0 G0 b0 c0 Hd a Ha1 Ha2. unfold shadow_addr in *.
assert (E8 : forall x, x mod 64 = 0 -> x / 8 = 8 * (x / 64)).
{ intros x Hx. rewrite (Z.div_mod x 64) at 1 by lia. rewrite Hx, Z.add_0_r.
  replace (64 * (x / 64)) with ((8 * (x / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (E64 : forall x, x mod 64 = 0 -> x = 64 * (x / 64)).
{ intros x Hx. rewrite (Z.div_mod x 64) at 1 by lia. rewrite Hx. lia. }
rewrite (E8 F HF), (E8 b Hb) in Ha1. rewrite (E8 G HG), (E8 c Hc) in Ha2.
rewrite (E64 F HF), (E64 G HG), (E64 b Hb), (E64 c Hc) in Hd. lia.
Qed.
Lemma app_not_shadow : forall a F b, 0 <= F -> 0 <= b -> F + b < 2 ^ 47 -> in_app a 1 ->
  ~ (shadow_addr F <= a < shadow_addr F + b / 8).
Proof.
intros a F b H0 H1 H2 Ha Hs. destruct (shadow_cell_bound F b H0 H1 H2) as [S1 S2].
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* ---- segment A part 2: 0x834fc .. 0x835f4, one plain run per digit path ------------------------------- *)
(* The digit loop's quotient step v -> v / 10 (0x835ac..0x835c0) and digit (0x835c4..0x835d0), as the engine
   writes them; x is the dividend's expression. *)
Definition sbd_sq (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRA (SMd M_MUL x (SLit 1717986919)) (SLit 34))
  (SAlu ALU_SRL (SMd M_MUL x (SLit 1717986919)) (SLit 63)).
Definition sbd_dg (x q : sv) : sv := SAlu ALU_ADD (SAlu ALU_SUB x (SMd M_MUL q (SLit 10))) (SLit 48).
(* The branch conditions the paths add: 0x835dc on v (cA), on v / 10 and v / 100 (cQ), 0x835e4 the pad (cP). *)
Definition sbd_cA (t : bool) : acond := mkAC (if t then BC_LTU else BC_GEU) (SLit 18446744073709551596) (SOff 20 (-10)).
Definition sbd_cP (t : bool) : acond := mkAC (if t then BC_GEU else BC_LTU) (SLit 1) (SOff 19 0).
Definition sbd_cQ (x : sv) (t : bool) : acond :=
  mkAC (if t then BC_LTU else BC_GEU) (SLit 18446744073709551596) (SAlu ALU_ADD (SAlu ALU_ADD (sbd_sq x) (SLit 0)) (SLit (-10))).
(* The state at 0x834fc: registers are their own atoms (x2 = x9 = sp1, x8 = entry sp, x10 = F, x18 = b,
   x19 = md, x20 = v, x21 = SB); atom 32 = the flag address, 33 = the frame's shadow SB + F/8. Regions: the
   frame's shadow (written by the prologue's poisoning), the frame (header, digits; its flag word at +56), the
   spill slot sp1+16. *)
Definition sbdA2_regions : smem :=
  [fshadow_region 33 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]; fframe_region 10 32 0 [];
   YP09.mkRegion (Some 9%nat) 16 24 16 24 []].
Definition sbdA2_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
   (10%nat, HPTR 6); (18%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (19%nat, mkAF 1 2 0); (20%nat, mkAF 0 (2 ^ 31 - 1) 0);
   (21%nat, mkAF SB SB 0); (32%nat, HPTR 0); (33%nat, mkAF (SB + 512) (SB + 17592186044416) 3)].
Definition sbdA2_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 21 0), SOff 33 0)].
Definition sbdA2_ss (cs : list acond) : sstate :=
  mkSS (AF_sb_dec + 0x68) sr_atoms sbdA2_regions None (mkFacts sbdA2_atoms cs sbdA2_alias).
Definition sbdA2_extra (F FL : Z) : list word := map (Z_to_bv 64) [FL; SB + F / 8].

(* The quotient and digit expressions denote the plain proof's arithmetic (lib/Prog/sb_dec.v sbd_q, sbd_r). *)
Lemma sbd_U_sq : forall E x v, U E x = v -> 0 <= v < 2 ^ 31 -> U E (sbd_sq x) = v / 10.
Proof.
intros E x v Hx Hv. unfold sbd_sq. rewrite !U_SAlu, !U_SMd, !U_SLit, Hx. cbn [zalu_raw zmd_raw].
change (zcanon 1717986919) with 1717986919. change (zcanon 34) with 34. change (zcanon 63) with 63.
change (Z.land 34 63) with 34. change (Z.land 63 63) with 63.
assert (Hm : 0 <= v * 1717986919 < 2 ^ 62) by lia.
rewrite (zcanon_id (v * 1717986919)) by (rewrite YI0s.M64_val; lia).
rewrite swrap64_id by (unfold half64; lia).
pose proof (OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.sb_dec.sbd_q v Hv) as Q.
rewrite signed_lit, (zcanon_id (v * 1717986919)), swrap64_id in Q by (try rewrite YI0s.M64_val; try unfold half64; lia).
rewrite !Z.shiftr_div_pow2 in Q |- * by lia.
rewrite (Z.div_small (v * 1717986919) (2 ^ 63)) in Q |- * by lia.
assert (Hd : 0 <= v * 1717986919 / 2 ^ 34 < 2 ^ 28)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.add_0_r, Z.mod_small in Q by lia.
rewrite OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.sb_dec.sbd_swrap in Q by lia.
change (zcanon 0) with 0. rewrite !(zcanon_id (v * 1717986919 / 2 ^ 34)) by (rewrite YI0s.M64_val; lia).
rewrite Z.add_0_r. rewrite zcanon_id by (rewrite YI0s.M64_val; lia). exact Q.
Qed.
Lemma sbd_U_add0 : forall E x, U E (SAlu ALU_ADD x (SLit 0)) = U E x.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zcanon_id. exact (U_range E x).
Qed.
Lemma sbd_U_dg : forall E x q v, U E x = v -> U E q = v / 10 -> 0 <= v < 2 ^ 31 -> U E (sbd_dg x q) = 48 + v mod 10.
Proof.
intros E x q v Hx Hq Hv. unfold sbd_dg. rewrite !U_SAlu, U_SMd, !U_SLit, Hx, Hq. cbn [zalu_raw zmd_raw].
change (zcanon 10) with 10. change (zcanon 48) with 48.
pose proof (OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.sb_dec.sbd_r v Hv) as Rr.
pose proof (Z.mod_pos_bound v 10 ltac:(lia)). pose proof (Z.div_mod v 10 ltac:(lia)).
assert (H10 : 0 <= v / 10 * 10 <= v) by lia.
rewrite (Z.mod_small (v / 10)), (Z.mod_small (v / 10 * 10)) in Rr by lia.
rewrite OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.sb_dec.sbd_swrap in Rr by lia.
rewrite (zcanon_id (v / 10 * 10)) by (rewrite YI0s.M64_val; lia).
rewrite (zcanon_id (v - v / 10 * 10)) by (rewrite YI0s.M64_val; lia).
rewrite Rr. rewrite zcanon_id by (rewrite YI0s.M64_val; lia). lia.
Qed.
(* The paths' branch conditions hold (the plain proof's sbd_lt10 for 0x835dc). *)
Lemma sbd_lt10_U : forall E e w t, sv_denot E e = Z_to_bv 64 (w + -10) -> 0 <= w < 2 ^ 31 -> (w <? 10) = t ->
  bv_ltu (sv_denot E (SLit 18446744073709551596)) (sv_denot E e) = t.
Proof.
intros E e w t He Hw Ht. rewrite <- Ht, He.
rewrite <- (OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.sb_dec.sbd_lt10 w Hw).
reflexivity.
Qed.
Lemma sbd_d20 : forall E v, ew E 20 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> sv_denot E (SOff 20 (-10)) = Z_to_bv 64 (v + -10).
Proof. intros E v H20 Hv. cbn [sv_denot]. rewrite H20, unsigned_lit_small by lia. reflexivity. Qed.
Lemma sbd_dq : forall E x w, U E x = w -> 0 <= w < 2 ^ 31 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (sbd_sq x) (SLit 0)) (SLit (-10))) = Z_to_bv 64 (w / 10 + -10).
Proof.
intros E x w Hx Hw. rewrite denot_lit_U, U_SAlu, sbd_U_add0, (sbd_U_sq E x w Hx Hw), U_SLit. cbn [zalu_raw].
rewrite lit_canon. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon. rewrite YI0s.M64_val.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma sbd_cA_ok : forall E v t, ew E 20 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> (v <? 10) = t -> acond_ok E (sbd_cA t).
Proof.
intros E v t H20 Hv Ht. pose proof (sbd_lt10_U E _ v _ (sbd_d20 E v H20 Hv) Hv eq_refl) as L.
unfold acond_ok, sbd_cA. destruct t; cbn [ac_c ac_a ac_b branch_taken]; rewrite L, Ht; reflexivity.
Qed.
Lemma sbd_cP_ok : forall E md t, ew E 19 = Z_to_bv 64 md -> 1 <= md <= 2 -> (1 <? md) = negb t -> acond_ok E (sbd_cP t).
Proof.
intros E md t H19 Hmd Ht.
assert (L : bv_ltu (sv_denot E (SLit 1)) (sv_denot E (SOff 19 0)) = (1 <? md)).
{ rewrite OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.ZBridge.bv_ltu_Z. cbn [sv_denot].
  rewrite H19, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small by lia. reflexivity. }
unfold acond_ok, sbd_cP. destruct t; cbn [ac_c ac_a ac_b branch_taken]; rewrite L, Ht; reflexivity.
Qed.
Lemma sbd_cQ_ok : forall E x w t, U E x = w -> 0 <= w < 2 ^ 31 -> (w / 10 <? 10) = t -> acond_ok E (sbd_cQ x t).
Proof.
intros E x w t Hx Hw Ht.
assert (Hw10 : 0 <= w / 10 < 2 ^ 31) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (sbd_lt10_U E _ (w / 10) _ (sbd_dq E x w Hx Hw) Hw10 eq_refl) as L.
unfold acond_ok, sbd_cQ. destruct t; cbn [ac_c ac_a ac_b branch_taken]; rewrite L, Ht; reflexivity.
Qed.
(* One byte of a region, from a literal chunk or an expression chunk whose value is known. *)
Lemma sbd_fld_lit1 : forall E m n bse cs lo hi wlo whi od z v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal 1 (SLit z))) cs -> z mod 2 ^ 64 mod 256 = v ->
  val_mem SEGS m (bse + od) 1 v.
Proof.
intros E m n bse cs lo hi wlo whi od z v Hr Hb Hc Hv.
pose proof (field_of_region_any E m n bse cs lo hi wlo whi od 1 (SLit z) Hr Hb Hc ltac:(lia)) as H.
cbn [sv_denot N.to_nat Pos.to_nat] in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
change (bv_modulus 64) with (2 ^ 64) in H. change (2 ^ (8 * Z.of_N 1)) with 256 in H. rewrite Hv in H. exact H.
Qed.
Lemma sbd_fld_U1 : forall E m n bse cs lo hi wlo whi od e v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> U E e = v -> 0 <= v < 256 ->
  val_mem SEGS m (bse + od) 1 v.
Proof.
intros E m n bse cs lo hi wlo whi od e v Hr Hb Hc He Hv.
pose proof (field_of_region_any E m n bse cs lo hi wlo whi od 1 e Hr Hb Hc ltac:(lia)) as H.
cbn [N.to_nat Pos.to_nat] in H. change (2 ^ (8 * Z.of_N 1)) with 256 in H. fold (U E e) in H.
rewrite He, Z.mod_small in H by lia. exact H.
Qed.
Lemma sbd_U_atom0 : forall E i v, ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff i 0) = v.
Proof. intros E i v Hi Hv. unfold U. cbn [sv_denot]. rewrite Hi, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. exact Hv. Qed.
(* The byte list rev (sb_dec_D v md) for each path. *)
Lemma sbd_revD1 : forall v md, 0 <= v < 10 -> md = 1 -> rev (sb_dec_c.sb_dec_D v md) = [48 + v mod 10].
Proof.
intros v md Hv ->. unfold sb_dec_c.sb_dec_D. rewrite rev_involutive. cbn [sb_dec_c.sb_dec_lsd].
replace (v <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma sbd_revD2 : forall v md, 0 <= v < 10 -> md = 2 -> rev (sb_dec_c.sb_dec_D v md) = [48 + v mod 10; 48].
Proof.
intros v md Hv ->. unfold sb_dec_c.sb_dec_D. rewrite rev_involutive. cbn [sb_dec_c.sb_dec_lsd].
replace (v <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma sbd_revD3 : forall v md, 10 <= v -> v / 10 < 10 -> 1 <= md <= 2 ->
  rev (sb_dec_c.sb_dec_D v md) = [48 + v mod 10; 48 + (v / 10) mod 10].
Proof.
intros v md Hv Hv1 Hmd. unfold sb_dec_c.sb_dec_D. rewrite rev_involutive. cbn [sb_dec_c.sb_dec_lsd].
replace (v <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
replace (v / 10 <? 10) with true by (symmetry; apply Z.ltb_lt; lia). cbn [length].
replace (Z.of_nat 2 <? md) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma sbd_revD4 : forall v md, 10 <= v -> 10 <= v / 10 -> 1 <= md <= 2 ->
  rev (sb_dec_c.sb_dec_D v md) = [48 + v mod 10; 48 + (v / 10) mod 10; 48 + (v / 10 / 10) mod 10].
Proof.
intros v md Hv Hv1 Hmd. unfold sb_dec_c.sb_dec_D. rewrite rev_involutive. cbn [sb_dec_c.sb_dec_lsd].
replace (v <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
replace (v / 10 <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (v / 10 / 10 <? 10); cbn [length];
replace (Z.of_nat 3 <? md) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity.
Qed.

Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* A1: entry -> the call of __asan_stack_malloc_0 -> its return. *)
Lemma sbdA_part1 : forall g, sbd_pre B g ->
  SRr SEGS (sq_W g) (cfg_at SEGS A_sb_dec (sq_regs g) (sq_memc g) (sq_mdc g)) (sbdA_ret g).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov] Hpre.
unfold sbd_pre in Hpre.
cbn [sq_STK sq_sp0 sq_FP sq_ly sq_S sq_W0 sq_mem0 sq_md0 sq_own sq_lyc sq_Sc sq_W sq_memc sq_mdc sq_k sq_regs
  sq_b sq_v sq_md sq_p sq_cap sq_n sq_ov] in Hpre |- *.
destruct Hpre as (HJc & Hraok & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp & H10 & H11 & H12 & Hv & Hmd & Hb8 & Hb0 & Hb63 &
  Hbsp & Hrec & Vp & Vcap & Vn & Vov & Rp & Rcap & Rn & Rn4 & Rov & HWRb & HQ & Hfr8 & Hnev & Hbb).
pose proof (sbd_entry B TL LAWS TLF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov 0
  HJc Hal16 Hwin Hsp H10 H11 H12 Hv Hmd Hb8 Hrec Hbsp Vp Vcap Vn Vov Rp Rcap Rn Rn4 Rov HWRb (or_introl eq_refl)
  (fun H => False_ind _ (Z.lt_irrefl 0 H))) as [HS _].
pose proof (sbd_kept0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs)
  (tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n)) HJc Hwin Hsp) as HK0.
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstatic & _).
pose proof Hstatic as (Hs16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
set (E := Eimg (Ereg regs (sbd_extra (as_uar_cell B) p cap n ov))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Ub : bv_unsigned (ew E 10) = b) by (rewrite E10; apply unsigned_lit_small; clear - Hb0 Hb63; lia).
unfold cfg_at, A_sb_dec, w64.
paj_run_shc RUNP RUNC HS HJc.
- (* the prologue's writes: the save area and the probe in the caller's window; b+16..b+28 by twr_ok *)
  intros a (r & Hin & Hr). cbn [sbd_ss0 ss_mem sbd_regs0 sbd_qr Z.eqb app] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
  cbn [sbd_rtop sbd_rprobe got_regionP bcell_regionP uar_got_regionP uar_cell_regionP sbd_rb
       YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?Ub in Hr.
  + left. clear - Hr Hwin Hsp WS. lia.
  + left. clear - Hr Hwin Hsp WS. lia.
  + exfalso. clear - Hr. lia.
  + exfalso. clear - Hr. lia.
  + exfalso. clear - Hr. lia.
  + exfalso. clear - Hr. lia.
  + exact (proj1 (HWRb a ltac:(clear - Hr; lia))).
- (* the state at the call: registers and the values the return state needs *)
  assert (E2v : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Rsp : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; pose proof (bv_unsigned_in_range _ (getr regs 2)) as H; exact H).
  set (sp1 := 32 * ((spZ regs + -96) / 32)).
  destruct (sp1_facts (spZ regs + -96) ltac:(clear - Hwin Hstk0 Hceil Hslo C1 WS; lia)
    ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
  fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
  assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by (clear - Hsp1r; lia). clear Hsp1r.
  assert (Dand : sv_denot E (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32))) = Z_to_bv 64 sp1)
    by (apply (denot_and_m32 E 2 (spZ regs) (-96) E2v); clear - Rsp Hwin Hstk0 Hceil Hslo C1 WS; lia).
  prreg0 HS (2%bv : bv 5) R2. rewrite Dand in R2.
  assert (Dadd : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
  { change (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32))) (SLit 0)))
      with (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32)))) (sv_denot E (SLit 0))).
    rewrite Dand. cbn [sv_denot]. rewrite YI08.alu64_add_lit, Z.add_0_r. reflexivity. }
  prreg0 HS (9%bv : bv 5) R9. rewrite Dadd in R9.
  prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
  prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
  prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
  prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
  (* the save area and the struct sb in the state at the call *)
  pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RG0.
  pose proof (st_ok_region_nth E _ _ 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG0, RG6.
  assert (VS : forall (i : nat) (r : bv 5) od, Z.of_nat i = bv_unsigned r ->
     In (YP09.mkChunk od (CVal 8 (SOff i 0))) [YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
       YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
       YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
       YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
       YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
     val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
  { intros i r od Hir Hc. rewrite <- Usp.
    apply (sbd_fld E _ 2 _ _ (-72) 0 (-72) 0 od 8%N i (bv_unsigned (getr regs r)) RG0 eq_refl Hc);
    [rewrite (EE i r Hir); exact (proj1 (sbd_regv _)) | exact (proj2 (sbd_regv _)) | lia]. }
  pose proof (VS 1%nat 1%bv (-8) eq_refl ltac:(sbd_in)) as V1.
  pose proof (VS 8%nat 8%bv (-16) eq_refl ltac:(sbd_in)) as V8.
  pose proof (VS 9%nat 9%bv (-24) eq_refl ltac:(sbd_in)) as V9.
  pose proof (VS 18%nat 18%bv (-32) eq_refl ltac:(sbd_in)) as V18.
  pose proof (VS 19%nat 19%bv (-40) eq_refl ltac:(sbd_in)) as V19.
  pose proof (VS 20%nat 20%bv (-48) eq_refl ltac:(sbd_in)) as V20.
  pose proof (VS 21%nat 21%bv (-56) eq_refl ltac:(sbd_in)) as V21.
  pose proof (VS 22%nat 22%bv (-64) eq_refl ltac:(sbd_in)) as V22.
  pose proof (VS 23%nat 23%bv (-72) eq_refl ltac:(sbd_in)) as V23.
  clear VS.
  assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (sbd_extra (as_uar_cell B) p cap n ov) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  cbn [Nat.add nth sbd_extra map] in E32, E34, E35, E36, E37. clear EX.
  assert (Wb0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (b + 0) 8 p)
    by (apply (sbd_fld E _ 10 _ _ 0 28 16 28 0 8%N 34%nat p RG6 Ub ltac:(sbd_in) E34); [exact Rp | lia]).
  assert (Wb8 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (b + 8) 8 cap)
    by (apply (sbd_fld E _ 10 _ _ 0 28 16 28 8 8%N 35%nat cap RG6 Ub ltac:(sbd_in) E35); [exact Rcap | lia]).
  assert (Wb16 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (b + 16) 8 n)
    by (apply (sbd_fld E _ 10 _ _ 0 28 16 28 16 8%N 36%nat n RG6 Ub ltac:(sbd_in) E36); [clear - Rn Rn4; lia | lia]).
  assert (Wb24 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (b + 24) 4 ov)
    by (apply (sbd_fld E _ 10 _ _ 0 28 16 28 24 4%N 37%nat ov RG6 Ub ltac:(sbd_in) E37); [exact Rov | lia]).
  rewrite Z.add_0_r in Wb0. clear RG0 RG6.
  (* what the run kept of the entry state: it wrote the save area and the probe (window) only *)
  assert (HK1 : tcj_kept B SB_DEC_STK lyc Sc W memc W (ms_mem ms) (spZ regs) (tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n))).
  { apply (sbd_kept_step LAWS SB_DEC_STK lyc Sc W memc mdc memc (ms_mem ms) (spZ regs) _ (in_wrange E (ss_mem (sbd_ss0 0)))
      ltac:(clear - Hwin Hstk0 Hceil Hslo; lia) HARc HK0).
    - intros a Ha Hw. apply aview_eq_of. apply HFr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hw.
    - intros a (r & Hin & Hr). cbn [sbd_ss0 ss_mem sbd_regs0 sbd_qr Z.eqb app] in Hin.
      destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
      cbn [sbd_rtop sbd_rprobe got_regionP bcell_regionP uar_got_regionP uar_cell_regionP sbd_rb
           YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?Ub in Hr.
      + left. clear - Hr WS. lia.
      + left. clear - Hr WS. lia.
      + exfalso. clear - Hr. lia.
      + exfalso. clear - Hr. lia.
      + exfalso. clear - Hr. lia.
      + exfalso. clear - Hr. lia.
      + right; left. split; [unfold tsb_dec_wr; left; clear - Hr; lia|].
        intros Him. pose proof (pa_segs_low a Him) as Hlo. unfold tsb_dec_rec_at in Hrec.
        pose proof HJc as (_ & Hlyc & _). pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
        unfold kLowMemEnd in Hlo. clear - Hlo Hr Hrec Eslo Hceil C1. rewrite Eslo in Hrec. lia.
    - intros a Hp. exact (apresent_grows _ _ _ a HG Hp). }
  pmkst HS. rewrite (palf_sm0 B TLF).
  pose proof (count_cid_le_length 0 (frames Sc)) as Hcnt.
  eapply SRr_bind.
  { eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 0 ASM0 ltac:(lia) W (ms_regs ms) (ms_mem ms)
      STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJc).
    - unfold spZ at 1. rewrite R2, unsigned_lit_small by (clear - Hsp1 Rsp Hwin Hstk0 Hceil Hslo C1 WS; lia). lia.
    - rewrite Zminus_mod, Hsp1al16, Hs16. reflexivity.
    - clear - Hsp1 Hsp; lia.
    - rewrite Hes. clear - Hsp1 Hwin WS; lia.
    - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - change (fs_frames 0) with 16384. clear - Hcnt Hfr8; lia. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 &
    Hz & Hflag & HK & _ & _).
  apply SRr_ret.
  unfold sbdA_ret, sq_F, sq_sp, sq_acc.
  cbn [sq_STK sq_sp0 sq_FP sq_ly sq_S sq_W0 sq_mem0 sq_md0 sq_own sq_lyc sq_Sc sq_W sq_memc sq_mdc sq_k sq_regs
    sq_b sq_v sq_md sq_p sq_cap sq_n sq_ov].
  rewrite Hes in HK. replace (sp0 + (sp1 - sp0) - 4096) with (sp1 - 4096) in HK by lia.
  replace (sp0 + (sp1 - sp0)) with sp1 in HK by lia.
  assert (Hce : alloc_ceiling <= spZ regs - SB_DEC_STK) by (clear - Hwin Hstk0 Hceil Hslo; lia).
  assert (KV : forall a nn vv, alloc_ceiling <= a -> a + Z.of_nat nn <= 2 ^ 64 -> (sp1 <= a \/ a + Z.of_nat nn <= sp1 - 4096) ->
     val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) a nn vv -> val_mem SEGS (mrestrict (w_H W) mem2) a nn vv).
  { intros a nn vv H1 H2 H3 Hvv. apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms) mem2 a nn vv); [|exact Hvv].
    intros kk Hk. apply (proj1 HK); [clear - H1 H2 Hk C1; lia | clear - H3 Hk; lia]. }
  assert (CS : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
  assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
  assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
  assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (CS 18 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (CS 19 ltac:(unfold acallee_saved; lia)).
  assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (CS 20 ltac:(unfold acallee_saved; lia)).
  assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
  assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (CS 22 ltac:(unfold acallee_saved; lia)).
  assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (CS 23 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (CS 24 ltac:(unfold acallee_saved; lia)).
  assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (CS 25 ltac:(unfold acallee_saved; lia)).
  assert (P26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (CS 26 ltac:(unfold acallee_saved; lia)).
  assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (CS 27 ltac:(unfold acallee_saved; lia)).
  clear CS.
  pose proof HJc as (_ & Hlyc & _). pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
  assert (Hb1 : alloc_ceiling <= b) by (unfold tsb_dec_rec_at in Hrec; rewrite Eslo in Hrec; clear - Hrec Hceil; lia).
  assert (Hb2 : sp1 <= b \/ b + 28 <= sp1 - 4096) by (clear - Hbsp Hsp1 WS; lia).
  assert (Hb3 : b + 28 <= 2 ^ 64) by (clear - Hb63; lia).
  split; [reflexivity|]. exists S2, regs2, mem2, md2, pos, sp1.
  split; [reflexivity|].
  split; [exact HJ2|].
  split.
  { apply (sbd_kept_call SB_DEC_STK lyc Sc W memc (ms_mem ms) mem2 (spZ regs) (sp1 - 4096) sp1 _ Hce
      ltac:(clear - Hsp Hshi H47; lia) ltac:(clear - Hsp1 WS; lia) ltac:(clear - Hsp1; lia) HK1 HK). }
  split; [exact Eab|]. split; [exact Hnin|]. split; [exact Hz|]. split; [exact Hflag|].
  split; [exact Hsp1|]. split; [exact Hsp1al|].
  split; [rewrite P2; exact R2|]. split; [rewrite P9; exact R9|].
  split; [rewrite P8, R8; exact E2v|].
  split; [exact Ha0|].
  split; [rewrite P18, R18; exact E10|].
  split; [rewrite P19, R19, (EE 12%nat 12%bv eq_refl); exact H12|].
  split; [rewrite P20, R20, (EE 11%nat 11%bv eq_refl); exact H11|].
  split; [rewrite P21, R21; exact E32|].
  split; [rewrite P3, R3; exact (EE 3%nat 3%bv eq_refl)|].
  split; [rewrite P4, R4; exact (EE 4%nat 4%bv eq_refl)|].
  split; [rewrite P22, R22; exact (EE 22%nat 22%bv eq_refl)|].
  split; [rewrite P23, R23; exact (EE 23%nat 23%bv eq_refl)|].
  split; [rewrite P24, R24; exact (EE 24%nat 24%bv eq_refl)|].
  split; [rewrite P25, R25; exact (EE 25%nat 25%bv eq_refl)|].
  split; [rewrite P26, R26; exact (EE 26%nat 26%bv eq_refl)|].
  split; [rewrite P27, R27; exact (EE 27%nat 27%bv eq_refl)|].
  assert (KS : forall od vv, -72 <= od <= -8 ->
     val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 vv ->
     val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - - od) 8 vv).
  { intros od vv Hod Hvv. replace (spZ regs - - od) with (spZ regs + od) by lia.
    apply KV; [clear - Hce Hod WS; lia | clear - Hsp Hshi H47 Hod Rsp; cbn; lia | left; clear - Hsp1 Hod; lia | exact Hvv]. }
  split; [exact (KS (-8) _ ltac:(lia) V1)|].
  split; [exact (KS (-16) _ ltac:(lia) V8)|].
  split; [exact (KS (-24) _ ltac:(lia) V9)|].
  split; [exact (KS (-32) _ ltac:(lia) V18)|].
  split; [exact (KS (-40) _ ltac:(lia) V19)|].
  split; [exact (KS (-48) _ ltac:(lia) V20)|].
  split; [exact (KS (-56) _ ltac:(lia) V21)|].
  split; [exact (KS (-64) _ ltac:(lia) V22)|].
  split; [exact (KS (-72) _ ltac:(lia) V23)|].
  split; [apply KV; [exact Hb1 | cbn; clear - Hb3; lia | cbn; clear - Hb2; lia | exact Wb0]|].
  split; [apply KV; [clear - Hb1; lia | cbn; clear - Hb3; lia | cbn; clear - Hb2; lia | exact Wb8]|].
  split; [apply KV; [clear - Hb1; lia | cbn; clear - Hb3; lia | cbn; clear - Hb2; lia | exact Wb16]|].
  apply KV; [clear - Hb1; lia | cbn; clear - Hb3; lia | cbn; clear - Hb2; lia | exact Wb24].
Qed.
(* The new frame's bytes and its shadow are fresh: not above the ceiling, not in the image, not in a heap
   block nor a frame (or its shadow) of the entry state. Adapted from fuzz_disco SbDecSeg2.v:102-149 sbd2_fresh
   to this file's sbd_fresh. *)
Lemma sbd_fresh_frame : forall lyc Sc S2 W2 mem2 md2 pos a,
  AR SEGS B lyc S2 W2 mem2 md2 -> frames S2 = (0, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64 \/
   shadow_addr (frame_addr lyc 0 pos) <= a < shadow_addr (frame_addr lyc 0 pos) + 8) ->
  sbd_fresh lyc Sc a.
Proof.
intros lyc Sc S2 W2 mem2 md2 pos a HAR2 Hfrs2 Eab Ha.
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR2 Hin2) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR2 Hin2) as (HFa & HFb & HF64).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hin2) as HFimg.
change (fs_frame_bytes 0) with 64 in HFc, HFapp, HFb, HF64, HFimg.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr lyc 0 pos) in *.
destruct (shadow_cell_bound F 64 ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2'].
change (64 / 8) with 8 in S2'.
split; [destruct Ha as [Ha | Ha]; [lia | unfold kHighMemBeg in *; lia]|].
split.
{ intros Himg. pose proof (pa_img_range a Himg) as Hr.
  destruct Ha as [Ha | Ha]; [destruct HFimg; lia | unfold SHADOW_OFF in *; lia]. }
split.
{ intros bb m i Hin Hi Heq. rewrite <- Eab in Hin.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bb m 0 pos HAR2 Hin Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb m HAR2 Hin) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
  subst a. destruct Ha as [Ha | Ha]; [lia|].
  apply (app_not_shadow (bb + i) F 64); [lia | lia | lia | unfold in_app in *; lia | exact Ha]. }
intros cid' pos' Hin'.
assert (Hin2' : In (cid', pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin').
destruct (al_frames _ _ LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (_ & HGapp & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (HG4096 & HGc & _).
destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR2 Hin2') as (HGa & HGb & HG64).
apply in_split in Hin' as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (0, pos) (cid', pos') [] l2 l3 HAR2
  ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
set (G := frame_addr lyc cid' pos') in *.
unfold in_zr, frame_rng. cbn [fst snd]. fold G.
destruct Ha as [Ha | Ha].
- split; [lia|]. intros Hs.
  apply (app_not_shadow a G (fs_frame_bytes cid')); [lia | lia | lia | unfold in_app in *; lia | exact Hs].
- split; [intros Hf; apply (app_not_shadow a F 64); [lia | lia | lia | unfold in_app in *; lia | exact Ha]|].
  intros Hs. exact (shadow_disj F G _ _ HFa HGa HFb HGb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd a Ha Hs).
Qed.
(* The buffer's shadow at a later state: a heap block's from AR (AR_shadow_law), a frame's kept (tcj_kept). *)
Lemma sbd_buf_shadow : forall STK lyc Sc W memc mdc lyx Sx memx mdx sp (Ew : Z -> Prop) q nq,
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyx Sx W memx mdx -> ablocks B lyx Sx = ablocks B lyc Sc ->
  tdst_ok B lyc Sc q nq -> range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q nq ->
  tcj_kept B STK lyc Sc W memc W memx sp Ew ->
  (forall x, q <= x < q + nq -> ~ Ew (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview SEGS (w_H W) memx) SHADOW_OFF q nq.
Proof.
intros STK lyc Sc W memc mdc lyx Sx memx mdx sp Ew q nq HARc HAR Eab Hd Hra (K1 & K2 & K3 & K4 & K5 & K6) HnE x Hx.
destruct (Hd x Hx) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- rewrite <- Eab in Hin.
  destruct (al_shadow _ _ LAWS _ _ _ _ _ bb m HAR Hin) as ((Hb8 & Hn0 & Hcells) & _).
  pose proof (Z.div_mod bb 8 ltac:(lia)) as D1. pose proof (Z.div_mod x 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (req_size m) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (req_size m) 8 ltac:(lia)) as M3.
  pose proof (Z.div_mod (req_size m + 7) 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (req_size m + 7) 8 ltac:(lia)) as M4.
  exists (if x / 8 - bb / 8 <? req_size m / 8 then 0 else req_size m mod 8). split.
  + replace (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr SHADOW_OFF bb + (x / 8 - bb / 8))
      by (unfold shadow_of_addr; lia).
    apply Hcells. lia.
  + unfold saddr_ok. destruct (Z.ltb_spec (x / 8 - bb / 8) (req_size m / 8)); [left; reflexivity | right; lia].
- destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HARc Hin) as (HFa & HFb & HF64).
  rewrite (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin); [exact Hs | | exact (HnE x Hx)].
  right. unfold in_zr, frame_rng in *. cbn [fst snd] in *. unfold shadow_addr, shadow_of_addr.
  pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)) as D1. pose proof (Z.div_mod x 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D3.
  assert (E1 : frame_addr lyc cid pos mod 8 = 0) by (apply Z.mod_divide in HFa as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (8 * c); lia).
  assert (E2 : fs_frame_bytes cid mod 8 = 0) by (apply Z.mod_divide in HFb as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (8 * c); lia).
  lia.
Qed.
(* The write rights of a part-2 run: the frame's shadow and the frame (own frame (0, pos)), the spill slot
   (the caller's window). *)
Ltac sbdA_awr U33 U10 U9 F pos Hsp1 Hwin Hsp WS :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [sbdA2_ss ss_mem sbdA2_regions] in Hin;
  destruct Hin as [<- | [<- | [<- | []]]];
  unfold fshadow_region, fframe_region in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  change (fs_frame_bytes 0 / 8) with 8 in Hr; change (fs_frame_bytes 0) with 64 in Hr;
  rewrite ?U33, ?U10, ?U9 in Hr;
  [ right; right; right; exists 0, pos; split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
    change (fs_frame_bytes 0 / 8) with 8; fold F; unfold shadow_addr, SHADOW_OFF; unfold SB in Hr; clear - Hr; lia
  | right; right; right; exists 0, pos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    change (fs_frame_bytes 0) with 64; fold F; clear - Hr; lia
  | left; clear - Hr Hsp1 Hwin Hsp WS; lia ].
(* After a part-2 run: what changed (only X), the final regions, the registers, the slot. *)
Ltac sbdA_after HF HFr HG HS X W ms mem2 U33 U10 U9 E EE E2 E9 E8 E10 E33 E18 E21 pos :=
  cbn [ms_mem mkst] in HF, HFr, HG;
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hx := fresh "Hx" in
    let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros a Ha Hx; apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by exact Ha; intros (r & Hin & Hr); apply Hx;
    cbn [sbdA2_ss ss_mem sbdA2_regions] in Hin; destruct Hin as [<- | [<- | [<- | []]]];
    unfold fshadow_region, fframe_region in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    change (fs_frame_bytes 0 / 8) with 8 in Hr; change (fs_frame_bytes 0) with 64 in Hr;
    rewrite ?U33, ?U10, ?U9 in Hr; unfold X; clear - Hr; lia
  | ];
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as RS;
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as RF;
  cbn [ms_mem restrict] in RS, RF;
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms; cbn [ss_pc] in Hms;
  let G2 := fresh "G2" in let G9 := fresh "G9" in let G8 := fresh "G8" in let G3 := fresh "G3" in
  let G4 := fresh "G4" in let G22 := fresh "G22" in let G23 := fresh "G23" in let G24 := fresh "G24" in
  let G25 := fresh "G25" in let G26 := fresh "G26" in let G27 := fresh "G27" in let G10 := fresh "G10" in
  let G16 := fresh "G16" in let G17 := fresh "G17" in let G18 := fresh "G18" in let G21 := fresh "G21" in
  let G14 := fresh "G14" in let G15 := fresh "G15" in
  prreg HS (2%bv : bv 5) G2; prreg HS (9%bv : bv 5) G9; prreg HS (8%bv : bv 5) G8;
  prreg HS (3%bv : bv 5) G3; prreg HS (4%bv : bv 5) G4; prreg HS (22%bv : bv 5) G22; prreg HS (23%bv : bv 5) G23;
  prreg HS (24%bv : bv 5) G24; prreg HS (25%bv : bv 5) G25; prreg HS (26%bv : bv 5) G26; prreg HS (27%bv : bv 5) G27;
  prreg HS (10%bv : bv 5) G10; prreg HS (16%bv : bv 5) G16; prreg HS (17%bv : bv 5) G17; prreg HS (18%bv : bv 5) G18;
  prreg HS (21%bv : bv 5) G21; prreg HS (14%bv : bv 5) G14; prreg HS (15%bv : bv 5) G15;
  rewrite E2 in G2; rewrite E9 in G9; rewrite E8 in G8;
  rewrite (EE 3%nat 3%bv eq_refl) in G3; rewrite (EE 4%nat 4%bv eq_refl) in G4;
  rewrite (EE 22%nat 22%bv eq_refl) in G22; rewrite (EE 23%nat 23%bv eq_refl) in G23;
  rewrite (EE 24%nat 24%bv eq_refl) in G24; rewrite (EE 25%nat 25%bv eq_refl) in G25;
  rewrite (EE 26%nat 26%bv eq_refl) in G26; rewrite (EE 27%nat 27%bv eq_refl) in G27;
  rewrite E10 in G10, G16; rewrite E33 in G17; rewrite E18 in G18; rewrite E21 in G21; rewrite U10 in G14;
  apply SRr_ret; exists pos.
(* The flag word and the frame's shadow at a part-2 end. *)
Ltac sbdA_fl E RF U10 E32 FL HFL4096 HFLc C1 :=
  exact (sbd_fld E _ 10 _ _ _ _ _ _ 56 8%N 32%nat FL RF U10 ltac:(sbd_in) E32 ltac:(clear - HFL4096 HFLc C1; lia) ltac:(lia)).
Ltac sbdA_sh E RS U33 :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; cbn [length SBD_FRAME_SHADOW] in Hj;
  do 8 (destruct j as [|j]; [split; [eapply (sbd_fld_lit1 E _ 33 _ _ _ _ _ _ _ _ _ RS U33); [sbd_in | reflexivity]
                                     | cbn [nth SBD_FRAME_SHADOW]; lia] |]); lia.
(* A2: 0x834fc -> 0x835f4, one plain run per digit path. *)
Lemma sbdA_part2 : forall g W2 c2, sbd_pre B g -> sbdA_ret g W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => exists pos, sbd_A_end B g pos W3 c3).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov] W2 c2 Hpre Hret.
unfold sbd_pre in Hpre. unfold sbdA_ret, sq_F, sq_sp, sq_acc in Hret.
cbn [sq_STK sq_sp0 sq_FP sq_ly sq_S sq_W0 sq_mem0 sq_md0 sq_own sq_lyc sq_Sc sq_W sq_memc sq_mdc sq_k sq_regs
  sq_b sq_v sq_md sq_p sq_cap sq_n sq_ov] in Hpre, Hret |- *.
destruct Hpre as (HJc & Hraok & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp & H10 & H11 & H12 & Hv & Hmd & Hb8 & Hb0 & Hb63 &
  Hbsp & Hrec & Vp & Vcap & Vn & Vov & Rp & Rcap & Rn & Rn4 & Rov & HWRb & HQ & Hfr8 & Hnev & Hbb).
destruct Hret as (-> & S2 & regs2 & mem2 & md2 & pos & sp1 & -> & HJ2 & HK2 & Eab & Hnin & Hz & Hflag & Hsp1 & Hsp1al &
  R2 & R9 & R8 & R10 & R18 & R19 & R20 & R21 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27 &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & Wb0 & Wb8 & Wb16 & Wb24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & HJpresc & Hstatic & _).
pose proof Hstatic as (Hs16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2' & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
assert (Hfrs2 : frames S2 = (0, pos) :: frames Sc) by (rewrite Hfrs2', Hfrsc; reflexivity).
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR2 Hin0) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR2 Hin0) as (HFa & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hin0) as (_ & _ & HFpres & HSHpres).
destruct (FFL _ _ _ _ _ 0 pos HAR2 Hin0) as (_ & _ & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes 0) with 64 in HFc, HFapp, HFpres, HSHpres, Hz, Hflag. change (64 / 8) with 8 in HSHpres.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
destruct (shadow_cell_bound F 64 ltac:(lia) ltac:(lia) ltac:(lia)) as [Sh1 Sh2]. change (64 / 8) with 8 in Sh2.
assert (HF8 : (SB + F / 8) mod 8 = 0) by (unfold SB; clear - HFa; lia).
set (E := Eimg (Ereg regs2 (sbdA2_extra F FL))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs2 r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 FL) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SB + F / 8)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = Z_to_bv 64 b) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 md) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 v) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Rsp : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (bv_unsigned_in_range _ (getr regs 2))).
assert (Hce : alloc_ceiling <= spZ regs - SB_DEC_STK) by (clear - Hwin Hstk0 Hceil Hslo; lia).
assert (Hsp47 : spZ regs <= 2 ^ 47) by (clear - Hsp Hshi H47; lia).
assert (Hb1 : alloc_ceiling <= b /\ b + 32 <= 2 ^ 47)
  by (unfold tsb_dec_rec_at in Hrec; rewrite Eslo, Eshi in Hrec; clear - Hrec Hceil H47; lia).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; clear - Hsp1 Hce Hsp47 C1 WS; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; clear - Hsp1 Hce Hsp47 C1 WS; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; apply unsigned_lit_small; exact Rsp).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; clear - HF4096 HFc C1; lia).
assert (U18 : bv_unsigned (ew E 18) = b) by (rewrite E18; apply unsigned_lit_small; clear - Hb1 C1; lia).
assert (U19 : bv_unsigned (ew E 19) = md) by (rewrite E19; apply unsigned_lit_small; clear - Hmd; lia).
assert (U20 : bv_unsigned (ew E 20) = v) by (rewrite E20; apply unsigned_lit_small; clear - Hv; lia).
assert (U21 : bv_unsigned (ew E 21) = SB) by (rewrite E21; apply unsigned_lit_small; unfold SB; lia).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; clear - HFL4096 HFLc C1; lia).
assert (U33 : bv_unsigned (ew E 33) = SB + F / 8) by (rewrite E33; apply unsigned_lit_small; clear - Sh1 Sh2; unfold shadow_addr, SB, SHADOW_OFF, kHighMemBeg in *; lia).
assert (HSE : forall cs, conds_ok E cs ->
  st_ok_pi SEGS VAL E (sbdA2_ss cs) (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + (AF_sb_dec + 0x68))) mem2 (seg_rom SEGS)))).
{ intros cs Hcs. rewrite restrict_mkst_fx. unfold sbdA2_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold sbdA2_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, fshadow_region, fframe_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0 - 8) with 56; change (fs_frame_bytes 0) with 64.
    + rewrite U33. split; [unfold SB; clear - HF4096; lia|]. split; [clear - Sh1 Sh2; unfold shadow_addr, SB, SHADOW_OFF, kHighMemBeg in *; lia|].
      split.
      * intros o Ho. apply (apresent_writable SEGS).
        replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, SB, SHADOW_OFF; lia).
        exact (proj1 (HSHpres o ltac:(lia))).
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (SB + F / 8) 0 8 (SLit 0) 0); [reflexivity | zside | zside |].
        rewrite Z.add_0_r. apply val_mem_zero8. intros i Hi.
        unfold zero_shadow, shadow_of_addr in Hz. replace (SB + F / 8 + i) with (SHADOW_OFF + F / 8 + i) by reflexivity.
        apply Hz. change (64 / 8) with 8. exact Hi.
    + rewrite U10. split; [clear - HF4096; lia|]. split; [clear - HFc C1; lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ F 56 8 (SOff 32 0) FL);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        replace (F + 56) with (F + 64 - 8) by lia. exact (val_mem_of_rdword SEGS (w_H W) mem2 _ _ Hflag).
    + rewrite U9. split; [clear - Hsp1 Hce WS C1; lia|]. split; [clear - Hsp1 Hsp47; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres2. clear - Ho Hsp1 Hwin Hsp WS. lia.
  - apply pairwise_disjoint_of_extents. unfold sbdA2_regions, fshadow_region, fframe_region.
    cbn [app map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 0 / 8) with 8. change (fs_frame_bytes 0) with 64.
    rewrite U33, U10, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, shadow_addr, SB, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    clear - HFapp HF4096 HFc Sh1 Sh2 Hsp1 Hce WS C1. repeat split; lia.
  - split; [|split; [exact Hcs|]].
    + unfold sbdA2_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite U2, U9, U8, U10, U18, U19, U20, U21, U32, U33.
      change (2 ^ 5) with 32; change (2 ^ 4) with 16; change (2 ^ 6) with 64; change (2 ^ 3) with 8; rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold SB. clear - Hsp1 Hsp1al Hce Hsp47 Hal16 HF4096 HFc HFa Hb1 Hb8 Hmd Hv HFL4096 HFLc HF8 C1 WS Sh1 Sh2.
      unfold shadow_addr, SHADOW_OFF, kHighMemBeg, SB in *.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    + cbn [sbdA2_alias alias_ok]. split; [|exact I].
      exact (shadow_decl_ok E 10%nat 21%nat 33%nat F SB E10 ltac:(clear - HF4096 HFc C1; lia) E21 E33). }
(* What every path's end gives sbd_A_end, the digits aside. *)
set (X := fun a => (sp1 + 16 <= a < sp1 + 24) \/ (F <= a < F + 64) \/ (SB + F / 8 <= a < SB + F / 8 + 8)).
assert (XC : forall a, X a -> (spZ regs - SB_DEC_STK <= a < spZ regs) \/
    (tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n) a /\ ~ in_img SEGS a) \/ sbd_fresh lyc Sc a).
{ intros a [Ha | Ha]; [left; clear - Ha Hsp1 WS; lia | right; right].
  apply (sbd_fresh_frame lyc Sc S2 W mem2 md2 pos a HAR2 Hfrs2 Eab).
  fold F. unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. clear - Ha. lia. }
assert (CLOSE : forall ms mat dl,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a) ->
  mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) (ms_mem ms)) ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + (AF_sb_dec + 0x160))) (ms_mem ms) (seg_rom SEGS) ->
  getr (ms_regs ms) 2 = w64 sp1 -> getr (ms_regs ms) 9 = w64 sp1 -> getr (ms_regs ms) 8 = w64 (spZ regs) ->
  getr (ms_regs ms) 3 = getr regs2 3 -> getr (ms_regs ms) 4 = getr regs2 4 ->
  getr (ms_regs ms) 22 = getr regs2 22 -> getr (ms_regs ms) 23 = getr regs2 23 ->
  getr (ms_regs ms) 24 = getr regs2 24 -> getr (ms_regs ms) 25 = getr regs2 25 ->
  getr (ms_regs ms) 26 = getr regs2 26 -> getr (ms_regs ms) 27 = getr regs2 27 ->
  getr (ms_regs ms) 10 = w64 F -> getr (ms_regs ms) 16 = w64 F -> getr (ms_regs ms) 17 = w64 (SB + F / 8) ->
  getr (ms_regs ms) 18 = w64 b -> getr (ms_regs ms) 21 = w64 SB ->
  getr (ms_regs ms) 14 = w64 (F + 32) -> getr (ms_regs ms) 15 = w64 (Z.of_nat (length dl)) ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (F + 56) 8 FL ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (SB + F / 8) SBD_FRAME_SHADOW ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (F + 32) dl ->
  dl = rev (sb_dec_c.sb_dec_D v md) ->
  sbd_A_end B (mkSbd STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov) pos W
    (mkCfg ms (with_vm_backing (m_vm_lazy md2) mat md2))).
{ intros ms mat dl HJ KX HG Hms G2 G9 G8 G3 G4 G22 G23 G24 G25 G26 G27 G10 G16 G17 G18 G21 G14 G15 GFL GSH GD Hdl.
  assert (HK3 : tcj_kept B SB_DEC_STK lyc Sc W memc W (ms_mem ms) (spZ regs) (tsb_dec_wr b p n (sb_dec_c.sb_dec_acc v md cap n))).
  { apply (sbd_kept_step LAWS SB_DEC_STK lyc Sc W memc mdc mem2 (ms_mem ms) (spZ regs) _ X Hce HARc HK2 KX XC).
    intros a Hp. exact (apresent_grows _ _ _ a HG Hp). }
  assert (KV : forall a nn vv, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 -> (forall j, a <= j < a + Z.of_nat nn -> ~ X j) ->
     val_mem SEGS (mrestrict (w_H W) mem2) a nn vv -> val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) a nn vv).
  { intros a nn vv H1 H2 H3 Hvv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem2 (ms_mem ms) a nn vv); [|exact Hvv].
    intros kk Hk. apply KX; [clear - H1 H2 Hk; lia | apply H3; clear - Hk; lia]. }
  assert (NXs : forall j, spZ regs - 72 <= j < spZ regs -> ~ X j).
  { intros j Hj Hx. unfold X in Hx. unfold SB in Hx. clear - Hj Hx Hsp1 Hce HFc Sh2 C1 WS.
    unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. lia. }
  assert (NXb : forall j, b <= j < b + 28 -> ~ X j).
  { intros j Hj Hx. unfold X in Hx. unfold SB in Hx. clear - Hj Hx Hsp1 Hbsp Hb1 HFc Sh2 C1 WS.
    unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. lia. }
  unfold sbd_A_end, sbd_cut, sbd_common, sq_F, sq_sp, sq_acc, sq_D, sq_kd.
  cbn [sq_STK sq_sp0 sq_FP sq_ly sq_S sq_W0 sq_mem0 sq_md0 sq_own sq_lyc sq_Sc sq_W sq_memc sq_mdc sq_k sq_regs
    sq_b sq_v sq_md sq_p sq_cap sq_n sq_ov]. fold F FL.
  split; [reflexivity|].
  exists lyc, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split. { rewrite Hms at 1. unfold cfg_at, A_sb_dec, SBD_A_END, w64. rewrite <- Z.add_assoc. reflexivity. }
  split; [exact HJ|]. split; [exact HK3|]. split; [exact Eab|]. split; [exact Hnin|].
  split.
  { split; [exact G8|]. split; [exists sp1; split; [exact G2|]; split; [exact G9|]; split; [exact Hsp1 | exact Hsp1al]|].
    split; [rewrite G3; exact R3|]. split; [rewrite G4; exact R4|].
    split; [rewrite G24; exact R24|]. split; [rewrite G25; exact R25|].
    split; [rewrite G26; exact R26|]. split; [rewrite G27; exact R27|].
    split; [exact G10|]. split; [exact G16|]. split; [exact G17|]. split; [exact G18|]. split; [exact G21|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V1]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V8]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V9]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V18]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V19]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V20]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V21]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V22]|].
    split; [apply KV; [clear - Hce WS C1; lia | clear - Hsp47; cbn; lia | intros j Hj; apply NXs; cbn in Hj; clear - Hj; lia | exact V23]|].
    change (fs_frame_bytes 0) with 64. replace (F + 64 - 8) with (F + 56) by lia.
    apply rdword_of_val_mem; [exact GFL | clear - HFL4096 HFLc C1; lia]. }
  split; [rewrite G22; exact R22|]. split; [rewrite G23; exact R23|].
  split; [exact G14|]. split; [rewrite G15, Hdl, length_rev; reflexivity|].
  split; [rewrite <- Hdl; exact GD|]. split; [exact GSH|].
  split; [apply KV; [clear - Hb1 C1; lia | cbn; clear - Hb1; lia | intros j Hj; apply NXb; cbn in Hj; clear - Hj; lia | exact Wb0]|].
  split; [apply KV; [clear - Hb1 C1; lia | cbn; clear - Hb1; lia | intros j Hj; apply NXb; cbn in Hj; clear - Hj; lia | exact Wb8]|].
  split; [apply KV; [clear - Hb1 C1; lia | cbn; clear - Hb1; lia | intros j Hj; apply NXb; cbn in Hj; clear - Hj; lia | exact Wb16]|].
  split; [apply KV; [clear - Hb1 C1; lia | cbn; clear - Hb1; lia | intros j Hj; apply NXb; cbn in Hj; clear - Hj; lia | exact Wb24]|].
  intros Hacc.
  assert (Hroom : 0 < sb_dec_c.sb_dec_room cap n).
  { unfold sb_dec_c.sb_dec_acc in Hacc. pose proof (OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.sb_dec.sbd_room_nn cap n). lia. }
  destruct (HQ Hroom) as (Hp0 & Hpc & Hd & Hra & Hwq & Hdb & Hds).
  pose proof HJ as (HAR3 & _).
  apply (sbd_buf_shadow SB_DEC_STK lyc Sc W memc mdc lyc S2 (ms_mem ms) _ (spZ regs) _ _ _ HARc HAR3 Eab Hd Hra HK3).
  intros x Hx HE. destruct (sbd_dst_byte B LAWS lyc Sc W memc mdc _ _ x HARc Hd Hx) as (D1 & D2 & D3).
  unfold tsb_dec_wr, shadow_of_addr in HE. unfold SHADOW_OFF in *.
  assert (D4 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; clear - D1 C1; lia).
  assert (D5 : 0 <= x / 8) by (apply Z.div_pos; clear - D1; lia).
  destruct HE as [HE | HE]; [clear - HE Hb1 D4 D5 C1; lia|].
  (* the shadow byte of a buffer byte is not a buffer byte *)
  destruct (sbd_dst_byte B LAWS lyc Sc W memc mdc _ _ (2147450880 + x / 8) HARc Hd HE) as (_ & _ & D6).
  apply D6. unfold SHADOW_OFF. clear - D4 D5. lia. }
(* the digit values *)
assert (UV : U E (SOff 20 0) = v) by (apply sbd_U_atom0; [exact E20 | clear - Hv; lia]).
assert (UQ1 : U E (sbd_sq (SOff 20 0)) = v / 10) by exact (sbd_U_sq E _ v UV Hv).
assert (Hv1 : 0 <= v / 10 < 2 ^ 31) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; clear - Hv; lia).
assert (UQ2 : U E (sbd_sq (sbd_sq (SOff 20 0))) = v / 10 / 10) by exact (sbd_U_sq E _ (v / 10) UQ1 Hv1).
assert (Hv2 : 0 <= v / 10 / 10 < 2 ^ 31) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; clear - Hv1; lia).
assert (UQ3 : U E (sbd_sq (sbd_sq (sbd_sq (SOff 20 0)))) = v / 10 / 10 / 10) by exact (sbd_U_sq E _ _ UQ2 Hv2).
assert (UD0 : U E (sbd_dg (SOff 20 0) (sbd_sq (SOff 20 0))) = 48 + v mod 10) by exact (sbd_U_dg E _ _ v UV UQ1 Hv).
assert (UD1 : U E (sbd_dg (SAlu ALU_ADD (sbd_sq (SOff 20 0)) (SLit 0)) (sbd_sq (sbd_sq (SOff 20 0)))) = 48 + (v / 10) mod 10)
  by exact (sbd_U_dg E _ _ (v / 10) (eq_trans (sbd_U_add0 E _) UQ1) UQ2 Hv1).
assert (UD2 : U E (sbd_dg (SAlu ALU_ADD (sbd_sq (sbd_sq (SOff 20 0))) (SLit 0)) (sbd_sq (sbd_sq (sbd_sq (SOff 20 0)))))
  = 48 + (v / 10 / 10) mod 10) by exact (sbd_U_dg E _ _ (v / 10 / 10) (eq_trans (sbd_U_add0 E _) UQ2) UQ3 Hv2).
assert (UL48 : U E (SLit 48) = 48) by (rewrite U_SLit; reflexivity).
pose proof (Z.mod_pos_bound v 10 ltac:(lia)) as M0. pose proof (Z.mod_pos_bound (v / 10) 10 ltac:(lia)) as M1.
pose proof (Z.mod_pos_bound (v / 10 / 10) 10 ltac:(lia)) as M2.
destruct (Z_lt_le_dec v 10) as [Hv10 | Hv10].
- destruct Hmd as [Hmd1 | Hmd2].
  + (* v < 10, md = 1: one digit *)
    pose proof (HSE [sbd_cA true; sbd_cP true]
      (conj (sbd_cA_ok E v true E20 Hv ltac:(apply Z.ltb_lt; lia))
        (conj (sbd_cP_ok E md true E19 ltac:(lia) ltac:(subst md; reflexivity)) I))) as HS.
    paj_run_to_sh RUNTOP HS HJ2 (AF_sb_dec + 0x160);
      [sbdA_awr U33 U10 U9 F pos Hsp1 Hwin Hsp WS | sbdA_after HF HFr HG HS X W ms mem2 U33 U10 U9 E EE E2 E9 E8 E10 E33 E18 E21 pos].
    apply (CLOSE ms mat [48 + v mod 10] HJ2 KX HG Hms G2 G9 G8 G3 G4 G22 G23 G24 G25 G26 G27 G10 G16 G17 G18 G21 G14 G15);
      [sbdA_fl E RF U10 E32 FL HFL4096 HFLc C1 | sbdA_sh E RS U33 | | exact (eq_sym (sbd_revD1 v md ltac:(lia) Hmd1))].
    intros j Hj. cbn [length] in Hj. destruct j as [|j]; [|lia].
    split; [|cbn [nth]; lia]. replace (F + 32 + Z.of_nat 0) with (F + 32) by lia.
    eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 32 _ _ RF U10); [sbd_in | exact UD0 | cbn [nth]; lia].
  + (* v < 10, md = 2: one digit and the pad *)
    pose proof (HSE [sbd_cA true; sbd_cP false]
      (conj (sbd_cA_ok E v true E20 Hv ltac:(apply Z.ltb_lt; lia))
        (conj (sbd_cP_ok E md false E19 ltac:(lia) ltac:(subst md; reflexivity)) I))) as HS.
    paj_run_to_sh RUNTOP HS HJ2 (AF_sb_dec + 0x160);
      [sbdA_awr U33 U10 U9 F pos Hsp1 Hwin Hsp WS | sbdA_after HF HFr HG HS X W ms mem2 U33 U10 U9 E EE E2 E9 E8 E10 E33 E18 E21 pos].
    apply (CLOSE ms mat [48 + v mod 10; 48] HJ2 KX HG Hms G2 G9 G8 G3 G4 G22 G23 G24 G25 G26 G27 G10 G16 G17 G18 G21 G14 G15);
      [sbdA_fl E RF U10 E32 FL HFL4096 HFLc C1 | sbdA_sh E RS U33 | | exact (eq_sym (sbd_revD2 v md ltac:(lia) Hmd2))].
    intros j Hj. cbn [length] in Hj. destruct j as [|[|j]]; [| |lia]; (split; [|cbn [nth]; lia]).
    * replace (F + 32 + Z.of_nat 0) with (F + 32) by lia.
      eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 32 _ _ RF U10); [sbd_in | exact UD0 | cbn [nth]; lia].
    * replace (F + 32 + Z.of_nat 1) with (F + 33) by lia.
      eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 33 _ _ RF U10); [sbd_in | exact UL48 | cbn [nth]; lia].
- destruct (Z_lt_le_dec (v / 10) 10) as [Hv11 | Hv11].
  + (* 10 <= v < 100: two digits *)
    pose proof (HSE [sbd_cA false; sbd_cQ (SOff 20 0) true]
      (conj (sbd_cA_ok E v false E20 Hv ltac:(apply Z.ltb_ge; lia))
        (conj (sbd_cQ_ok E (SOff 20 0) v true UV Hv ltac:(apply Z.ltb_lt; lia)) I))) as HS.
    paj_run_to_sh RUNTOP HS HJ2 (AF_sb_dec + 0x160);
      [sbdA_awr U33 U10 U9 F pos Hsp1 Hwin Hsp WS | sbdA_after HF HFr HG HS X W ms mem2 U33 U10 U9 E EE E2 E9 E8 E10 E33 E18 E21 pos].
    apply (CLOSE ms mat [48 + v mod 10; 48 + (v / 10) mod 10] HJ2 KX HG Hms G2 G9 G8 G3 G4 G22 G23 G24 G25 G26 G27
      G10 G16 G17 G18 G21 G14 G15);
      [sbdA_fl E RF U10 E32 FL HFL4096 HFLc C1 | sbdA_sh E RS U33 | | exact (eq_sym (sbd_revD3 v md Hv10 Hv11 ltac:(lia)))].
    intros j Hj. cbn [length] in Hj. destruct j as [|[|j]]; [| |lia]; (split; [|cbn [nth]; lia]).
    * replace (F + 32 + Z.of_nat 0) with (F + 32) by lia.
      eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 32 _ _ RF U10); [sbd_in | exact UD0 | cbn [nth]; lia].
    * replace (F + 32 + Z.of_nat 1) with (F + 33) by lia.
      eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 33 _ _ RF U10); [sbd_in | exact UD1 | cbn [nth]; lia].
  + (* 100 <= v: three digits, whatever v / 100 is *)
    assert (UQs : U E (sbd_sq (SOff 20 0)) = v / 10) by exact UQ1.
    destruct (Z_lt_le_dec (v / 10 / 10) 10) as [Hv12 | Hv12].
    * pose proof (HSE [sbd_cA false; sbd_cQ (SOff 20 0) false; sbd_cQ (sbd_sq (SOff 20 0)) true]
        (conj (sbd_cA_ok E v false E20 Hv ltac:(apply Z.ltb_ge; lia))
          (conj (sbd_cQ_ok E (SOff 20 0) v false UV Hv ltac:(apply Z.ltb_ge; lia))
            (conj (sbd_cQ_ok E (sbd_sq (SOff 20 0)) (v / 10) true UQs Hv1 ltac:(apply Z.ltb_lt; lia)) I)))) as HS.
      paj_run_to_sh RUNTOP HS HJ2 (AF_sb_dec + 0x160);
        [sbdA_awr U33 U10 U9 F pos Hsp1 Hwin Hsp WS | sbdA_after HF HFr HG HS X W ms mem2 U33 U10 U9 E EE E2 E9 E8 E10 E33 E18 E21 pos].
      apply (CLOSE ms mat [48 + v mod 10; 48 + (v / 10) mod 10; 48 + (v / 10 / 10) mod 10] HJ2 KX HG Hms
        G2 G9 G8 G3 G4 G22 G23 G24 G25 G26 G27 G10 G16 G17 G18 G21 G14 G15);
        [sbdA_fl E RF U10 E32 FL HFL4096 HFLc C1 | sbdA_sh E RS U33 | | exact (eq_sym (sbd_revD4 v md Hv10 Hv11 ltac:(lia)))].
      intros j Hj. cbn [length] in Hj. destruct j as [|[|[|j]]]; [| | |lia]; (split; [|cbn [nth]; lia]).
      -- replace (F + 32 + Z.of_nat 0) with (F + 32) by lia.
         eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 32 _ _ RF U10); [sbd_in | exact UD0 | cbn [nth]; lia].
      -- replace (F + 32 + Z.of_nat 1) with (F + 33) by lia.
         eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 33 _ _ RF U10); [sbd_in | exact UD1 | cbn [nth]; lia].
      -- replace (F + 32 + Z.of_nat 2) with (F + 34) by lia.
         eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 34 _ _ RF U10); [sbd_in | exact UD2 | cbn [nth]; lia].
    * pose proof (HSE [sbd_cA false; sbd_cQ (SOff 20 0) false; sbd_cQ (sbd_sq (SOff 20 0)) false]
        (conj (sbd_cA_ok E v false E20 Hv ltac:(apply Z.ltb_ge; lia))
          (conj (sbd_cQ_ok E (SOff 20 0) v false UV Hv ltac:(apply Z.ltb_ge; lia))
            (conj (sbd_cQ_ok E (sbd_sq (SOff 20 0)) (v / 10) false UQs Hv1 ltac:(apply Z.ltb_ge; lia)) I)))) as HS.
      paj_run_to_sh RUNTOP HS HJ2 (AF_sb_dec + 0x160);
        [sbdA_awr U33 U10 U9 F pos Hsp1 Hwin Hsp WS | sbdA_after HF HFr HG HS X W ms mem2 U33 U10 U9 E EE E2 E9 E8 E10 E33 E18 E21 pos].
      apply (CLOSE ms mat [48 + v mod 10; 48 + (v / 10) mod 10; 48 + (v / 10 / 10) mod 10] HJ2 KX HG Hms
        G2 G9 G8 G3 G4 G22 G23 G24 G25 G26 G27 G10 G16 G17 G18 G21 G14 G15);
        [sbdA_fl E RF U10 E32 FL HFL4096 HFLc C1 | sbdA_sh E RS U33 | | exact (eq_sym (sbd_revD4 v md Hv10 Hv11 ltac:(lia)))].
      intros j Hj. cbn [length] in Hj. destruct j as [|[|[|j]]]; [| | |lia]; (split; [|cbn [nth]; lia]).
      -- replace (F + 32 + Z.of_nat 0) with (F + 32) by lia.
         eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 32 _ _ RF U10); [sbd_in | exact UD0 | cbn [nth]; lia].
      -- replace (F + 32 + Z.of_nat 1) with (F + 33) by lia.
         eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 33 _ _ RF U10); [sbd_in | exact UD1 | cbn [nth]; lia].
      -- replace (F + 32 + Z.of_nat 2) with (F + 34) by lia.
         eapply (sbd_fld_U1 E _ 10 _ _ _ _ _ _ 34 _ _ RF U10); [sbd_in | exact UD2 | cbn [nth]; lia].
Qed.
(* Segment A. *)
Theorem pb_seg_sbd_A : seg_sbd_A B.
Proof.
intros g Hpre. apply (SRr_bind SEGS _ _ _ _ (sbdA_part1 g Hpre)). intros W2 c2 _ Hret.
exact (sbdA_part2 g W2 c2 Hpre Hret).
Qed.
End walk.
End h.
End f.
End d.
