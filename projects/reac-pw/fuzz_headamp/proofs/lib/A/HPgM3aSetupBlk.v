(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b (hd_getr_z,
   hd_aview_some, hd_aview_grows, restated as su_getr_z, su_aview_some, su_aview_grows) and
   proofs/reac-pw/fuzz_role/lib/A/RPgScanSetup.v at a1fdf6ce036 (su_soff; the set-up's shape: one engine run over the
   first block's three fields decided by one shadow entry, split on the booleans) for reac-pw/fuzz_headamp image A;
   the rest of the file is new. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the block lemma of the
   set-up piece of the checking segment M03 of LLVMFuzzerTestOneInput (lib/A/HPgSegM.v hq_piece_M3a_setup_stmt),
   from X 0x82f30 to the pair loop's head PAIR 0x8307c, RC 0x83694 or RCM 0x8369c. Proves no function (kind:
   segment lemma); lib/A/HPgM3aSetup.v turns su_blk into the piece.

   THE CODE (s1 = R, s3 = (F >> 3) + K, s5 = pp + 0x4000, s7 = K, s10 = F + 0x180)
     0x82f30 .. 0x82f34  s2 := R[0x60] + 0x1a0 = x (the frame object, F + 0x1a0)
     0x82f38 .. 0x82f78  17 x `sb zero`: x's shadow granules 52 .. 68 := 0 (x comes into scope)
     0x82f7c .. 0x82f88  memset(x, 0, 0x88): the `jal` of __asan_memset 0x521a8 (ra = 0x82f8c)
     0x82f8c .. 0x82f94  a1 := -1; R[0x40] (the null flag) <> 0 -> RCM
     0x82f98 .. 0x82fb0  the instrumented check of pp + 0x4008, `lw` is_props; 0 -> RCM
     0x82fb4             R[0x108] := x
     0x82fb8 .. 0x82fd0  the check of pp + 0x4010, `lw` params_struct; 0 -> RC
     0x82fd4 .. 0x82fec  the check of pp + 0x4d14 (its shadow index in R[0x90]), `lw` t2 = n_ent (R[0xa0]); <= 0 -> RC
     0x82ff0 .. 0x83078  s5 := 0, R[0xb8] := x + 4, t3 := n_ent - 1, a7 := 104, t4 := 8, t5 := -1,
                         R[0xc0] := 1000000, fs1 := -1.0f (fmv.w.x 0x83030), fs2 := 256.0f (fmv.w.x 0x83044),
                         R[0xb0] / R[0xa8] := the high words of 0.5L / -0.5L, t6 = ra := pp + 0x4014,
                         R[0x100] := R[0xf8] := pp + 0x401c, R[0xe8] := pp + 0x4018; then PAIR.
   The slow blocks of the three checks (0x839e4, 0x839f4, 0x83a1c) are dead: the first block's shadow is 0.

   HOW. Run A (YCbq aj_run_to) from X to the memset's entry: R[0x60] is a read-only chunk and x's shadow granules a
   write window at s3 (the frame's shadow row; YCbq awr_byte's in_frames case, HPgSteps.awr_ok_cons_fshadow), read
   back as 0 by HPgSteps.fsh_byte_of_region. The memset is HPgIntrin.hd_memset_at under the Section hypothesis
   AMEMSET (x's 136 bytes are writable as a frame object the harness owns, outside the memset's stack, and their
   shadow is the 0 run A wrote). Run B (aj_run_to_tok) from 0x82f8c holds pp as the extra atom 32 (s5 pinned to
   pp + 0x4000), the real frame's cells R[0x40], R[0x90], R[0xa0], R[0xf0] in one region at R with the write window
   [R + 0xa8, R + 0x110), the record's three fields as literal chunks in one region at pp, and two shadow entries:
   the first block [pp, pp + 0x4d20) (marked usable: YCbq.shent_ok_of_block) and the real frame's window (above the
   shadow band: YCbq.shent_app_of_high). It is split on the null flag, is_props, params_struct and n_ent = 0, so
   each run is straight-line. On the main path the run stops at the first `fmv.w.x`; su_fmv steps it
   (YK0o.fp_step_fmv_w_x through SRr_msteps_st) and keeps the symbolic state at the new float state, run C goes to
   the second one, su_fmv again, and run D to PAIR. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgMem HPgSteps HPgIntrin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ generic helpers ================================ *)
Lemma su_soff : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* a register named by Z_to_bv 5 n is the register named by the numeral n *)
Lemma su_getr_z : forall (regs : bvmap 5 word) (r : bv 5) n, bv_unsigned r = n -> getr regs (Z_to_bv 5 n) = getr regs r.
Proof.
intros regs r n H. f_equal. apply bv_eq. subst n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (u5_range r). change (bv_modulus 5) with 32. lia.
Qed.

Section g. Context {fx : YK11.FPState}.
(* a byte a block or a frame holds is present *)
Lemma su_aview_some : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* a byte that reads as something still does after a step that keeps every present byte present *)
Lemma su_aview_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
(forall x, apresent H m x -> apresent H m' x) -> aview rsegs H m a <> None -> aview rsegs H m' a <> None.
Proof.
intros H m m' a Hg Hv. unfold aview, mbyte, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exact Hv|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Hm.
- assert (Hp : apresent H m a) by (split; [exact Hh | exists b; exact Hm]).
  destruct (Hg a Hp) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.
(* a 4-byte value whose bytes all still read as something reads as some value *)
Lemma su_rd32_grows : forall (rd rd' : reader) a ev,
rd32 rd a ev -> (forall x, rd x <> None -> rd' x <> None) -> (forall x b, rd' x = Some b -> 0 <= b < 256) ->
exists ev', rd32 rd' a ev'.
Proof.
intros rd rd' a ev Hr Hg Hb.
assert (Hk : forall k, (k < 4)%nat -> exists b, rd' (a + Z.of_nat k) = Some b /\ 0 <= b < 256).
{ intros k Hk. specialize (Hr k Hk). destruct (rd' (a + Z.of_nat k)) as [b|] eqn:E.
  - exists b. split; [reflexivity | exact (Hb _ _ E)].
  - exfalso. apply (Hg (a + Z.of_nat k)); [rewrite Hr; discriminate | exact E]. }
destruct (Hk 0%nat ltac:(lia)) as (b0 & E0 & R0). destruct (Hk 1%nat ltac:(lia)) as (b1 & E1 & R1).
destruct (Hk 2%nat ltac:(lia)) as (b2 & E2 & R2). destruct (Hk 3%nat ltac:(lia)) as (b3 & E3 & R3).
exists (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))).
intros k Hk4. unfold le_byte. change (8 * Z.of_nat 4) with 32.
rewrite (Z.mod_small _ (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- rewrite E0. f_equal. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. lia.
- rewrite E1. f_equal. change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. lia.
- rewrite E2. f_equal. change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. lia.
- rewrite E3. f_equal. change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. lia.
Qed.
End g.

(* ================================ run A: 0x82f30 .. the `jal` of __asan_memset 0x82f88 ================================ *)
Definition su_tblA : ctable := build_table rsegs 0x82f30 23 TEmpty.
Lemma su_tblA_ok : table_ok rsegs su_tblA.
Proof. apply build_table_ok0. lia. Qed.

(* the entry of run A: the frame's shadow row at s3 (granules 52 .. 68 written) and R+0x60 = F (s10 = F + 0x180) *)
Definition su_rshX : YP09.region := YP09.mkRegion (Some 19%nat) 52 69 52 69 [].
Definition su_rA60 : YP09.region := YP09.mkRegion (Some 9%nat) 0x60 0x68 0 0 [YP09.mkChunk 0x60 (CVal 8 (SOff 26 (-0x180)))].
Definition su_ssA : sstate := mkSS 0x82f30 sr_atoms [su_rshX; su_rA60] None (mkFacts [] [] []).

(* the symbolic value of register r in a state, as a closed term *)
Ltac su_sv :=
lazymatch goal with |- context [sr_get (ss_regs ?ss) ?r] =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet A_ASAN_MEMSET.

(* the state at 0x82f8c, after the memset returns *)
Definition su_A_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (R F : Z)
(regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k /\ same_io mdc md1 /\
(forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
 getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
getr regs1 (Z_to_bv 5 18) = w64 (F + 0x1a0) /\
(forall i, 0 <= i < 136 -> aview rsegs (w_H W) mem1 (F + 0x1a0 + i) = Some 0) /\
(forall i, 52 <= i < 69 -> aview rsegs (w_H W) mem1 (shadow_addr F + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x1a0 <= a < F + 0x228) ->
 ~ (shadow_addr F + 52 <= a < shadow_addr F + 69) -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem1 a).

Lemma su_A : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R F pos : Z)
(Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> frame_addr lyc 4 pos = F ->
getr regs (Z_to_bv 5 2) = w64 R -> getr regs (Z_to_bv 5 3) = w64 (as_gp B) -> getr regs (Z_to_bv 5 4) = w64 (as_tp B) ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 19) = w64 (shadow_addr F) ->
getr regs (Z_to_bv 5 26) = w64 (F + 0x180) ->
R mod 32 = 0 -> R + 0x1e0 <= sp0 -> sp0 - STK <= R - ASTACK ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x60) 8 F ->
(forall regs1 mem1 md1, su_A_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F regs1 mem1 md1 ->
 SRr rsegs W (cfg_at rsegs 0x82f8c regs1 mem1 md1) Q) ->
SRr rsegs W (cfg_at rsegs 0x82f30 regs memc mdc) Q.
Proof using AMEMSET.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos Q
  HJ Hown HF H2 H3 H4 H9 H19 H26 HR32 HRS HRstk V60 K.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hs16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF32 & HFapp & HFb & HFsh).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFc & _).
rewrite HF in HF32, HFapp, HFb, HFsh, HF4096, HFc.
change (fs_frame_bytes 4) with 1024 in HFapp, HFb, HFsh, HFc. change (1024 / 8) with 128 in HFsh.
pose proof (ASAN_CEIL_range) as Hceil. unfold ASAN_CEIL in Hceil.
unfold ASTACK in HRstk.
set (E := Ereg regs []).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (exact (eq_trans (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl) H9)).
assert (E19 : ew E 19 = Z_to_bv 64 (shadow_addr F)) by (exact (eq_trans (ew_Ereg_nat regs _ 19 (Z_to_bv 5 19) eq_refl) H19)).
assert (E26 : ew E 26 = Z_to_bv 64 (F + 0x180)) by (exact (eq_trans (ew_Ereg_nat regs _ 26 (Z_to_bv 5 26) eq_refl) H26)).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr F) by (rewrite E19; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (HS : st_ok rsegs E su_ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82f30) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold su_rshX, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E. rewrite U19. unfold shadow_addr, SHADOW_OFF in *.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
    + apply (hm_ro_region rsegs E (w_H W) memc 9 R 0x60 0x68); [exact U9 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ R 0x60 8 _ F); [| | lia | exact V60].
      * rewrite (su_soff E 26 (F + 0x180) (-0x180) E26). f_equal. lia.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - apply pairwise_disjoint_of_extents. unfold su_rshX, su_rA60. cbn [map zpairwise_disjoint zall_disjoint].
    unfold extent_of_region, zdisj. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U19.
    unfold shadow_addr, SHADOW_OFF in *. lia.
  - split; [exact I | split; exact I]. }
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
clearbody E.
unfold cfg_at. change (w64 0x82f30) with (Z_to_bv 64 0x82f30).
aj_run_to su_tblA_ok HS HJ 0x521a8.
{ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat 4 pos);
  [ reflexivity | cbn [base_val]; rewrite U19, HF; reflexivity | exact Hown
  | cbn [YP09.r_wlo su_rshX]; lia | cbn [YP09.r_whi su_rshX]; change (fs_frame_bytes 4 / 8) with 128; lia | ].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
(* the registers at the call *)
assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 0x82f8c)
  by (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS); su_sv; reflexivity).
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (F + 0x1a0))
  by (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS); su_sv; rewrite (su_soff E 26 (F + 0x180) 32 E26); unfold w64; f_equal; lia).
assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 0)
  by (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS); su_sv; reflexivity).
assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 136)
  by (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS); su_sv; reflexivity).
assert (R18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (F + 0x1a0))
  by (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS); su_sv; rewrite (su_soff E 26 (F + 0x180) 32 E26); unfold w64; f_equal; lia).
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  exact (YI04.regs_kept_of_st_ok rsegs E _ _ regs [] (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27])
    HS HAE ltac:(vm_compute; reflexivity) (Z_to_bv 5 r) (in_map _ _ _ Hr)). }
(* the frame's shadow at the call: x's granules are 0 *)
assert (Hsh0 : forall i, 52 <= i < 69 -> aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + i) = Some 0).
{ pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite U19 in Hch.
  intros i Hi. unfold aview.
  fsh_pts Hi ltac:(apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]). }
(* every byte outside x's shadow granules is as at 0x82f30 *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 52 <= a < shadow_addr F + 69) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. intros (rg & Hin & Hr). cbn [In su_ssA ss_mem] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [su_rshX su_rA60 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite U19 in Hr; exact (Hn Hr) | lia]. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
assert (HxR : F + 0x228 <= R - ESTACK) by (unfold ESTACK; lia).
eapply SRr_bind.
{ apply (hd_memset_at (fx := fx) B (AMEMSET fx) W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
    _ k (F + 0x1a0) 0 136 (R - sp0) (Z_to_bv 64 0x82f8c) HJ).
  - rewrite <- (su_getr_z (ms_regs ms) 10 10 eq_refl). exact R10.
  - rewrite <- (su_getr_z (ms_regs ms) 11 11 eq_refl). exact R11.
  - rewrite <- (su_getr_z (ms_regs ms) 12 12 eq_refl). exact R12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite <- (su_getr_z (ms_regs ms) 2 2 eq_refl), (Rk 2 ltac:(cbn; tauto)), H2. unfold w64.
    rewrite unsigned_lit_small by lia. ring.
  - lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite <- (su_getr_z (ms_regs ms) 3 3 eq_refl), (Rk 3 ltac:(cbn; tauto)). exact H3.
  - rewrite <- (su_getr_z (ms_regs ms) 4 4 eq_refl), (Rk 4 ltac:(cbn; tauto)). exact H4.
  - rewrite <- (su_getr_z (ms_regs ms) 1 1 eq_refl). exact R1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + right. right. right. exists 4, pos. split; [exact Hown|]. left.
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 4) with 1024. lia.
    + unfold ESTACK in *. lia.
  - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr F + (x / 8 - F / 8)) by (unfold shadow_of_addr, shadow_addr; ring).
    apply Hsh0. lia.
  - intros _ s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
    replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
    apply su_aview_some. apply (apresent_grows _ _ _ _ HG).
    apply (HFsh (s - shadow_addr F)). unfold shadow_addr, SHADOW_OFF. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hpres2 & H10' & Hset & Hkeep2 & Hgrow2).
apply K.
split; [exact HJ2|].
split; [eapply same_io_trans; [apply same_io_wvb | exact Hio2]|].
split; [intros r Hr; rewrite (Hpres2 r) by (cbn [In] in Hr; unfold acallee_saved; lia); apply Rk; exact Hr|].
split; [rewrite (Hpres2 18) by (unfold acallee_saved; lia); exact R18|].
split; [intros i Hi; rewrite (Hset i Hi); reflexivity|].
assert (Hshx : forall i, 52 <= i < 69 -> ~ (F + 0x1a0 <= shadow_addr F + i < F + 0x1a0 + 136)).
{ intros i Hi. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold shadow_addr, SHADOW_OFF. lia. }
split; [intros i Hi; rewrite Hkeep2; [apply Hsh0; exact Hi | unfold shadow_addr, SHADOW_OFF; lia | exact (Hshx i Hi) | unfold shadow_addr, SHADOW_OFF, ESTACK in *; lia]|].
split; [intros a Ha H1 H2' H3'; rewrite Hkeep2; [apply KA; [exact Ha | exact H3'] | exact Ha | lia | lia]|].
intros a Hp. apply Hgrow2. exact (apresent_grows _ _ _ _ HG Hp).
Qed.
End blk.

(* ================================ run B: 0x82f8c .. RCM / RC / the first `fmv.w.x` 0x83030 ================================ *)
Definition su_tblB : ctable := build_table rsegs 0x82f8c 41 TEmpty.
Lemma su_tblB_ok : table_ok rsegs su_tblB.
Proof. apply build_table_ok0. lia. Qed.
Definition su_Bx : sv := SOff 23 0.
Definition su_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the first block [pp, pp + 0x4d20) (atom 32) and the write window [R + 0xa8, R + 0x110) of the real frame *)
Definition su_SH : list shent := [mkSHE 32 0 0x4d20; mkSHE 9 0x110 0xa8].
Definition su_rR (nz : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x40 0x110 0xa8 0x110
  [ YP09.mkChunk 0x40 (CVal 8 (SLit nz));
    YP09.mkChunk 0x90 (CVal 8 (SAlu ALU_SRL (SOff 32 0x4d14) (SLit 3)));
    YP09.mkChunk 0xa0 (CVal 8 (SOff 32 0x4d14));
    YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0)) ].
Definition su_rP (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 32%nat) 0x4008 0x4d18 0 0 cs.
Definition su_fs0 : list (nat * afact) :=
  [(23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 (2 ^ 47 - 0x4d20) 0)].
Definition su_ssB (rs : list YP09.region) (fs : list (nat * afact)) : sstate :=
  mkSS 0x82f8c (sr_set sr_atoms (Z_to_bv 5 21) (SOff 32 0x4000)) rs None (mkFacts fs [] []).

(* the main path: null = 0, is_props = 1, params_struct = 1, n_ent > 0 *)
Definition su_csM : list YP09.chunk :=
  [YP09.mkChunk 0x4008 (CVal 4 (SLit 1)); YP09.mkChunk 0x4010 (CVal 4 (SLit 1)); YP09.mkChunk 0x4d14 (CVal 4 (SOff 33 0))].
Definition su_fsM : list (nat * afact) := su_fs0 ++ [(33%nat, mkAF 1 32 0)].

Definition su_csN0 : list YP09.chunk :=
  [YP09.mkChunk 0x4008 (CVal 4 (SLit 1)); YP09.mkChunk 0x4010 (CVal 4 (SLit 1)); YP09.mkChunk 0x4d14 (CVal 4 (SLit 0))].
Definition su_csP0 : list YP09.chunk := [YP09.mkChunk 0x4008 (CVal 4 (SLit 1)); YP09.mkChunk 0x4010 (CVal 4 (SLit 0))].
Definition su_csI0 : list YP09.chunk := [YP09.mkChunk 0x4008 (CVal 4 (SLit 0))].

(* ================================ the float steps `fmv.w.x` ================================ *)
Definition su_fset (f : YK11.FPState) (k v : Z) : YK11.FPState :=
  YK11.mkFP (bvmap_set (Z_to_bv 5 k) (nan_box (Z_to_bv 32 v)) (@fp_regs f)) (@fp_csr f).
Definition su_fx (f : YK11.FPState) : YK11.FPState := su_fset (su_fset f 9 0xbf800000) 18 0x43800000.

Section fm. Context {rc : YM05.RunCeil}.
Lemma su_fmv : forall (fxA : YK11.FPState) (W : world rsegs) E ss regs mem md (Q : world rsegs -> config -> Prop)
  pc w (k rs : Z) v (rdb rsb : bv 5),
@st_ok rsegs fxA E ss (restrict (w_H W) (@mkst fxA regs (Z_to_bv 64 pc) mem (seg_rom rsegs))) ->
ss_resv ss = None ->
fetch_word rsegs (Z_to_bv 64 pc) = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_F_X FMT_S rdb rsb, 4) -> rdb = Z_to_bv 5 k -> rsb = Z_to_bv 5 rs ->
v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4) ->
low32 (getr regs (Z_to_bv 5 rs)) = Z_to_bv 32 v ->
(forall X, @st_ok rsegs (su_fset fxA k v) E (mkSS (pc + 4) (ss_regs ss) (ss_mem ss) None (ss_facts ss))
   (restrict (w_H W) (@mkst (su_fset fxA k v) regs (Z_to_bv 64 (pc + 4)) mem (seg_rom rsegs))) ->
 SRr rsegs W (mkCfg (@mkst (su_fset fxA k v) regs (Z_to_bv 64 (pc + 4)) mem (seg_rom rsegs))
   (with_vm_backing (m_vm_lazy md) X md)) Q) ->
SRr rsegs W (mkCfg (@mkst fxA regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) Q.
Proof.
intros fxA W E ss regs mem md Q pc w k rs v rdb rsb HS Hrv Hf He Hd Hrd Hrs Hpc Hv K. subst rdb rsb.
set (fxB := su_fset fxA k v).
set (ss' := mkSS (pc + 4) (ss_regs ss) (ss_mem ss) None (ss_facts ss)).
assert (HS' : @st_ok rsegs fxB E ss' (restrict (w_H W) (@mkst fxB regs (Z_to_bv 64 (pc + 4)) mem (seg_rom rsegs)))).
{ unfold st_ok in HS |- *.
  destruct HS as (_ & _ & H3 & H4 & _ & H6 & H7 & H8 & H9).
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst] in *.
  subst ss'. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot] in *.
  do 5 (split; [reflexivity|]). split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9]. }
refine (@SRr_msteps_st rsegs fxB img_wx W E ss' (@mkst fxA regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) _ md Q _ HS' _).
- rewrite !restrict_mkst_fx. apply msteps_one; [reflexivity|].
  rewrite (YK0o.fp_step_fmv_w_x fxA rsegs regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (seg_rom rsegs) w
    (Z_to_bv 5 k) (Z_to_bv 5 rs) Hf He Hd).
  rewrite Hpc, Hv. reflexivity.
- intros ms' mat' HS2 Hlo Hhi Hreg.
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms' HS2 eq_refl) as Ems.
  assert (Hm : ms_mem ms' = mem).
  { apply functional_extensionality. intros x. destruct (w_H W x) eqn:Hx.
    - rewrite (Hhi x Hx). reflexivity.
    - rewrite (Hlo x Hx). cbn [ms_mem restrict mkst]. unfold mrestrict. rewrite Hx. reflexivity. }
  assert (Hr : ms_regs ms' = regs) by (rewrite Hreg; reflexivity).
  rewrite Hm, Hr in Ems. subst ss'. cbn [ss_pc] in Ems. subst ms'.
  apply K. exact HS2.
Qed.
End fm.

(* a cell of a region read back after a run *)
Lemma su_cell : forall E m b cs off e v, Forall (YP09.chunk_ok rsegs E m b) cs ->
In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem rsegs m (b + off) 8 v.
Proof.
intros E m b cs off e v H Hin He Hv.
exact (val_of_chunk_ok rsegs E m b off 8 e v (proj1 (Forall_forall _ _) H _ Hin) He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)).
Qed.

Ltac su_awr U9 d :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat d); [reflexivity | cbn [base_val]; rewrite U9; lia | cbn; lia | cbn; lia | ] ].

Definition su_tblC : ctable := build_table rsegs 0x83034 4 TEmpty.
Lemma su_tblC_ok : table_ok rsegs su_tblC.
Proof. apply build_table_ok0. lia. Qed.
Definition su_tblD : ctable := build_table rsegs 0x83048 13 TEmpty.
Lemma su_tblD_ok : table_ok rsegs su_tblD.
Proof. apply build_table_ok0. lia. Qed.

Lemma su_fr : forall E rs (m m' : word -> option byte) a, frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
~ in_wrange E rs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros E rs m m' a H Ha Hn. apply H. rewrite unsigned_lit_small by lia. exact Hn. Qed.
(* an address outside the real frame's write window is in no window of a run's regions *)
Ltac su_nw U9 :=
  let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (rg & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try rewrite U9 in Hr; lia|]);
  destruct Hin.

Section blkB. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* what every exit of runs B, C, D keeps *)
Definition su_B_post_c (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(mem1 : word -> option byte) (md1 : Model) (k : Z) (regs1 : bvmap 5 word) (R pp : Z)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k /\ same_io md1 md3 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27] ->
 getr regs3 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xf0) 8 pp /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xa8 <= a < R + 0x110) -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem3 a).

Definition su_B_post_PAIR (W : world rsegs) (R pp X n : Z) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
getr regs3 (Z_to_bv 5 1) = w64 (pp + 0x4014) /\ getr regs3 (Z_to_bv 5 31) = w64 (pp + 0x4014) /\
getr regs3 (Z_to_bv 5 29) = w64 8 /\ getr regs3 (Z_to_bv 5 30) = w64 (-1) /\
getr regs3 (Z_to_bv 5 17) = w64 104 /\ getr regs3 (Z_to_bv 5 21) = w64 0 /\
getr regs3 (Z_to_bv 5 7) = w64 n /\ getr regs3 (Z_to_bv 5 28) = w64 (n - 1) /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xa8) 8 0xbffe000000000000 /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xb0) 8 0x3ffe000000000000 /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xb8) 8 (X + 4) /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xc0) 8 1000000 /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xe8) 8 (pp + 0x4018) /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xf8) 8 (pp + 0x401c) /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0x100) 8 (pp + 0x401c) /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0x108) 8 X.

Lemma su_B : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k (regs1 : bvmap 5 word) (R pp X nz n : Z)
(ip ps : bool) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
In (pp, 19744) (ablocks B lyc Sc) ->
getr regs1 (Z_to_bv 5 9) = w64 R -> getr regs1 (Z_to_bv 5 18) = w64 X ->
getr regs1 (Z_to_bv 5 21) = w64 (pp + 0x4000) -> getr regs1 (Z_to_bv 5 23) = w64 SHADOW_OFF ->
R mod 32 = 0 -> R + 0x1e0 <= sp0 -> sp0 - STK <= R - ASTACK -> 0 <= X < 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x40) 8 nz -> (nz = 0 \/ nz = 1) ->
val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x90) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) mem1) (R + 0xa0) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) mem1) (R + 0xf0) 8 pp ->
val_mem rsegs (mrestrict (w_H W) mem1) (pp + 0x4008) 4 (Z.b2z ip) ->
val_mem rsegs (mrestrict (w_H W) mem1) (pp + 0x4010) 4 (Z.b2z ps) ->
val_mem rsegs (mrestrict (w_H W) mem1) (pp + 0x4d14) 4 n -> 0 <= n <= 32 ->
(forall regs3 mem3 md3,
 su_B_post_c STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 R pp regs3 mem3 md3 ->
 getr regs3 (Z_to_bv 5 11) = w64 (-1) -> (nz = 1 \/ ip = false) ->
 SRr rsegs W (cfg_at rsegs 0x8369c regs3 mem3 md3) Q) ->
(forall regs3 mem3 md3,
 su_B_post_c STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 R pp regs3 mem3 md3 ->
 val_mem rsegs (mrestrict (w_H W) mem3) (R + 0x108) 8 X -> nz = 0 -> ip = true -> (ps = false \/ n = 0) ->
 SRr rsegs W (cfg_at rsegs 0x83694 regs3 mem3 md3) Q) ->
(forall regs3 mem3 md3,
 su_B_post_c STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 R pp regs3 mem3 md3 ->
 su_B_post_PAIR W R pp X n regs3 mem3 -> nz = 0 -> ip = true -> ps = true -> 0 < n ->
 SRr rsegs W (@cfg_at (su_fx fx) rsegs 0x8307c regs3 mem3 md3) Q) ->
SRr rsegs W (cfg_at rsegs 0x82f8c regs1 mem1 md1) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 R pp X nz n ip ps Q
  HJ HPP H9 H18 H21 H23 HR32 HRS HRstk HX V40 Hnz V90 VA0 VF0 Vip Vps Vn Hn KM KC KP.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp 19744 HAR HPP) as (Hp16 & Hp4096 & Hpc & Happ & _).
change (req_size 19744) with 19744 in Hpc, Happ.
pose proof (ASAN_CEIL_range) as Hceil. unfold ASAN_CEIL in Hceil, Happ.
unfold ASTACK in HRstk.
set (E := Ereg regs1 [w64 pp; w64 n]).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (exact (eq_trans (ew_Ereg_nat regs1 _ 9 (Z_to_bv 5 9) eq_refl) H9)).
assert (E18 : ew E 18 = Z_to_bv 64 X) by (exact (eq_trans (ew_Ereg_nat regs1 _ 18 (Z_to_bv 5 18) eq_refl) H18)).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (ew_Ereg_nat regs1 _ 23 (Z_to_bv 5 23) eq_refl) H23)).
assert (E32 : ew E 32 = Z_to_bv 64 pp) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 n) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs1 [w64 pp; w64 n]) E) by (subst E; apply env_agree_refl).
(* the real frame's region and the first block's region *)
assert (HrR : forall nz', val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x40) 8 nz' -> 0 <= nz' <= 1 ->
  region_ok rsegs E (mrestrict (w_H W) mem1) (su_rR nz')).
{ intros nz' V40' Hnz'. unfold su_rR.
  apply (hm_rw_region rsegs E (w_H W) mem1 9 R 0x40 0x110 0xa8 0x110); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
  repeat apply Forall_cons; [..|apply Forall_nil].
  - apply (chunk_ok_val rsegs E _ R 0x40 8 (SLit nz') nz'); [reflexivity | cbn; lia | lia | exact V40'].
  - apply (chunk_ok_val rsegs E _ R 0x90 8 _ (Z.shiftr (pp + 0x4d14) 3)); [| | lia | exact V90].
    + rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SOff, U_SLit, U32. cbn [zalu_raw].
      unfold zcanon, M64. rewrite (Z.mod_small (pp + 0x4d14)) by lia. change (3 mod 2 ^ 64) with 3.
      change (Z.land 3 63) with 3. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by lia. lia.
    + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - apply (chunk_ok_val rsegs E _ R 0xa0 8 _ (pp + 0x4d14)); [exact (su_soff E 32 pp _ E32) | cbn; lia | lia | exact VA0].
  - apply (chunk_ok_val rsegs E _ R 0xf0 8 _ pp); [rewrite (su_soff E 32 pp 0 E32), Z.add_0_r; reflexivity | cbn; lia | lia | exact VF0]. }
assert (HrP : forall cs, Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W) mem1) pp) cs ->
  region_ok rsegs E (mrestrict (w_H W) mem1) (su_rP cs)).
{ intros cs Hcs. apply (hm_ro_region rsegs E (w_H W) mem1 32 pp 0x4008 0x4d18); [exact U32 | lia | lia | exact Hcs]. }
assert (Cip : forall b, Z.b2z ip = b -> YP09.chunk_ok rsegs E (mrestrict (w_H W) mem1) pp (YP09.mkChunk 0x4008 (CVal 4 (SLit b)))).
{ intros b Hb. subst b. apply (chunk_ok_val rsegs E _ pp 0x4008 4 _ (Z.b2z ip)); [reflexivity | destruct ip; cbn; lia | lia | exact Vip]. }
assert (Cps : forall b, Z.b2z ps = b -> YP09.chunk_ok rsegs E (mrestrict (w_H W) mem1) pp (YP09.mkChunk 0x4010 (CVal 4 (SLit b)))).
{ intros b Hb. subst b. apply (chunk_ok_val rsegs E _ pp 0x4010 4 _ (Z.b2z ps)); [reflexivity | destruct ps; cbn; lia | lia | exact Vps]. }
assert (Cn : YP09.chunk_ok rsegs E (mrestrict (w_H W) mem1) pp (YP09.mkChunk 0x4d14 (CVal 4 (SOff 33 0)))).
{ apply (chunk_ok_val rsegs E _ pp 0x4d14 4 _ n); [rewrite (su_soff E 33 n 0 E33), Z.add_0_r; reflexivity | cbn; lia | lia | exact Vn]. }
assert (HF0 : atoms_ok E su_fs0).
{ cbn [su_fs0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E23, U32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF.
  repeat split; try lia; apply Z.mod_1_r. }
(* the shadow entries *)
assert (SHOK : sh_ok rsegs su_Bx su_SH E (mrestrict (w_H W) mem1)).
{ constructor; [|constructor; [|constructor]].
  - eapply (shent_ok_of_block rsegs B LAWS lyc Sc W mem1 md1 E su_Bx 32 pp 19744 0 0x4d20 HAR HPP).
    + unfold su_Bx. apply U_atom; [exact E23 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E32 | lia].
    + lia.
    + change (req_size 19744) with 19744. lia.
  - eapply shent_app_of_high.
    + unfold su_Bx. apply U_atom; [exact E23 | unfold SHADOW_OFF; lia].
    + apply U_atom; [exact E9 | lia].
    + unfold kHighMemBeg. lia.
    + lia. }
assert (HB : forall rs fs, regions_wf rs = true -> Forall (region_ok rsegs E (mrestrict (w_H W) mem1)) rs ->
  pairwise_disjoint E rs -> atoms_ok E fs ->
  st_ok rsegs E (su_ssB rs fs) (restrict (w_H W) (mkst regs1 (Z_to_bv 64 0x82f8c) mem1 (seg_rom rsegs)))).
{ intros rs fs Hwf Hrs Hpd Hfs. rewrite restrict_mkst_fx.
  refine (st_ok_pin_sv rsegs E (mkSS 0x82f8c sr_atoms rs None (mkFacts fs [] [])) _ (Z_to_bv 5 21) (SOff 32 0x4000) _ _ _).
  - apply (entry_st_ok_full rsegs); [apply regs_ok_Ereg | exact Hwf | exact Hrs | exact Hpd |].
    split; [exact Hfs | split; exact I].
  - vm_compute. reflexivity.
  - cbn [ms_regs mkst]. rewrite (su_soff E 32 pp _ E32), H21. reflexivity. }
clearbody E.
unfold cfg_at. change (w64 0x82f8c) with (Z_to_bv 64 0x82f8c).
destruct Hnz as [-> | ->]; [destruct ip; [destruct ps; [destruct (Z.eq_dec n 0) as [-> | Hn0] |] |] |].
(* the four exits of a single run B *)
- (* null = 0, is_props = params_struct = 1, n_ent = 0: RC *)
  assert (Cn0 : YP09.chunk_ok rsegs E (mrestrict (w_H W) mem1) pp (YP09.mkChunk 0x4d14 (CVal 4 (SLit 0))))
    by (apply (chunk_ok_val rsegs E _ pp 0x4d14 4 _ 0); [reflexivity | cbn; lia | lia | exact Vn]).
  pose proof (HB [su_rR 0; su_rP su_csN0] su_fs0 ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; [apply (HrR 0 V40); lia | apply HrP; repeat apply Forall_cons; [apply Cip; reflexivity | apply Cps; reflexivity | exact Cn0 | apply Forall_nil] | apply Forall_nil])
    ltac:(apply pairwise_disjoint_of_extents; unfold su_rR, su_rP; cbn [map zpairwise_disjoint zall_disjoint];
          unfold extent_of_region, zdisj; cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U9, U32; lia)
    HF0) as HS.
  aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x83694; [su_awr U9 (R - sp0) | ].
  assert (Rg : forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r))
  by (intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E _ _ regs1 _
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]) HS HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr))).
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hch. rewrite U9 in Hch.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xa8 <= a < R + 0x110) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a)
  by (intros a Ha Hn'; unfold aview, mbyte; rewrite (su_fr _ _ _ _ a HFr Ha) by su_nw U9; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  apply KC; [ | | reflexivity | reflexivity | right; reflexivity].
  + split; [exact HJ|].
    split; [apply same_io_wvb|].
    split; [exact Rg|].
    split; [apply (su_cell E _ R _ 0xf0 (SOff 32 0) pp Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | rewrite (su_soff E 32 pp 0 E32), Z.add_0_r; reflexivity | lia]|].
    split; [exact KB|].
    intros a Hp. exact (apresent_grows _ _ _ _ HG Hp).
  + apply (su_cell E _ R _ 0x108 (SOff 18 0) X Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | rewrite (su_soff E 18 X 0 E18), Z.add_0_r; reflexivity | lia].
- (* the main path: to 0x83030 *)
  pose proof (HB [su_rR 0; su_rP su_csM] su_fsM ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; [apply (HrR 0 V40); lia | apply HrP; repeat apply Forall_cons; [apply Cip; reflexivity | apply Cps; reflexivity | exact Cn | apply Forall_nil] | apply Forall_nil])
    ltac:(apply pairwise_disjoint_of_extents; unfold su_rR, su_rP; cbn [map zpairwise_disjoint zall_disjoint];
          unfold extent_of_region, zdisj; cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U9, U32; lia)
    ltac:(cbn [su_fsM app su_fs0 atoms_ok] in HF0 |- *; destruct HF0 as (HF23 & HF32 & _);
          split; [exact HF23|]; split; [exact HF32|]; split; [|exact I];
          unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia; repeat split; try lia; apply Z.mod_1_r))
    as HS.
  aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x83030; [su_awr U9 (R - sp0) | ].
  (* the first `fmv.w.x fs1,a3` 0x83030 *)
  assert (RB13 : low32 (getr (ms_regs ms) (Z_to_bv 5 13)) = Z_to_bv 32 0xbf800000)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS); su_sv; vm_refl_bv).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems in HS |- *.
  set (rB := ms_regs ms) in *. set (mB := ms_mem ms) in *. clearbody rB mB. clear Ems ms.
  rename HFr into HFrB, HG into HGB, HF into HFB.
  eapply (su_fmv fx W E _ rB mB _ Q 0x83030 (Z_to_bv 32 4026959059) 9 13 0xbf800000 _ _ HS);
    [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | vm_refl_bv | exact RB13 |].
  intros XB HS0. pose proof (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XB HJ) as HJ0. clear HJ.
  aj_run_to su_tblC_ok HS0 HJ0 0x83044; [su_awr U9 (R - sp0) | ].
  (* the second `fmv.w.x fs2,a4` 0x83044 *)
  assert (RC14 : low32 (getr (ms_regs ms) (Z_to_bv 5 14)) = Z_to_bv 32 0x43800000)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS0); su_sv; vm_refl_bv).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS0 eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems in HS0 |- *.
  set (rC := ms_regs ms) in *. set (mC := ms_mem ms) in *. clearbody rC mC. clear Ems ms.
  rename HFr into HFrC, HG into HGC, HF into HFC.
  eapply (su_fmv _ W E _ rC mC _ Q 0x83044 (Z_to_bv 32 4026992979) 18 14 0x43800000 _ _ HS0);
    [reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | vm_refl_bv | exact RC14 |].
  intros XC HS1. pose proof (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XC HJ0) as HJ1. clear HJ0.
  aj_run_to su_tblD_ok HS1 HJ1 0x8307c; [su_awr U9 (R - sp0) | ].
  (* the state at PAIR 0x8307c *)
  assert (Rg : forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
  { intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs E _ _ regs1 [w64 pp; w64 n]
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]) HS1 HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr)). }
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS1 ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hch. rewrite U9 in Hch.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xa8 <= a < R + 0x110) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a).
  { intros a Ha Hn'. unfold aview, mbyte.
    rewrite (su_fr _ _ _ _ a HFr Ha) by su_nw U9. rewrite (su_fr _ _ _ _ a HFrC Ha) by su_nw U9.
    rewrite (su_fr _ _ _ _ a HFrB Ha) by su_nw U9. reflexivity. }
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS1 eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems.
  apply KP; [ | | reflexivity | reflexivity | reflexivity | lia].
  + split; [exact HJ1|].
    split; [apply same_io_wvb|].
    split; [exact Rg|].
    split; [apply (su_cell E _ R _ 0xf0 (SOff 32 0) pp Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | rewrite (su_soff E 32 pp 0 E32), Z.add_0_r; reflexivity | lia]|].
    split; [exact KB|].
    intros a Hp. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HGC). exact (apresent_grows _ _ _ _ HGB Hp).
  + unfold su_B_post_PAIR.
    repeat split;
    try (rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS1); su_sv);
    try (eapply (su_cell E _ R); [ exact Hch | cbn [In]; repeat (first [left; reflexivity | right]) | | lia ]);
    first [ exact (su_soff E 32 pp _ E32)
          | rewrite (su_soff E 18 X _ E18); try rewrite Z.add_0_r; reflexivity
          | rewrite (su_soff E 33 n _ E33); unfold w64; f_equal; lia
          | reflexivity
          | apply bv_eq; vm_compute; reflexivity ].
- (* null = 0, is_props = 1, params_struct = 0: RC *)
  pose proof (HB [su_rR 0; su_rP su_csP0] su_fs0 ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; [apply (HrR 0 V40); lia | apply HrP; repeat apply Forall_cons; [apply Cip; reflexivity | apply Cps; reflexivity | apply Forall_nil] | apply Forall_nil])
    ltac:(apply pairwise_disjoint_of_extents; unfold su_rR, su_rP; cbn [map zpairwise_disjoint zall_disjoint];
          unfold extent_of_region, zdisj; cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U9, U32; lia)
    HF0) as HS.
  aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x83694; [su_awr U9 (R - sp0) | ].
  assert (Rg : forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r))
  by (intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E _ _ regs1 _
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]) HS HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr))).
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hch. rewrite U9 in Hch.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xa8 <= a < R + 0x110) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a)
  by (intros a Ha Hn'; unfold aview, mbyte; rewrite (su_fr _ _ _ _ a HFr Ha) by su_nw U9; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  apply KC; [ | | reflexivity | reflexivity | left; reflexivity].
  + split; [exact HJ|].
    split; [apply same_io_wvb|].
    split; [exact Rg|].
    split; [apply (su_cell E _ R _ 0xf0 (SOff 32 0) pp Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | rewrite (su_soff E 32 pp 0 E32), Z.add_0_r; reflexivity | lia]|].
    split; [exact KB|].
    intros a Hp. exact (apresent_grows _ _ _ _ HG Hp).
  + apply (su_cell E _ R _ 0x108 (SOff 18 0) X Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | rewrite (su_soff E 18 X 0 E18), Z.add_0_r; reflexivity | lia].
- (* null = 0, is_props = 0: RCM *)
  pose proof (HB [su_rR 0; su_rP su_csI0] su_fs0 ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; [apply (HrR 0 V40); lia | apply HrP; repeat apply Forall_cons; [apply Cip; reflexivity | apply Forall_nil] | apply Forall_nil])
    ltac:(apply pairwise_disjoint_of_extents; unfold su_rR, su_rP; cbn [map zpairwise_disjoint zall_disjoint];
          unfold extent_of_region, zdisj; cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U9, U32; lia)
    HF0) as HS.
  aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x8369c; [su_awr U9 (R - sp0) | ].
  assert (Rg : forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r))
  by (intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E _ _ regs1 _
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]) HS HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr))).
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hch. rewrite U9 in Hch.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xa8 <= a < R + 0x110) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a)
  by (intros a Ha Hn'; unfold aview, mbyte; rewrite (su_fr _ _ _ _ a HFr Ha) by su_nw U9; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  apply KM; [ | | right; reflexivity].
  + split; [exact HJ|].
    split; [apply same_io_wvb|].
    split; [exact Rg|].
    split; [apply (su_cell E _ R _ 0xf0 (SOff 32 0) pp Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | rewrite (su_soff E 32 pp 0 E32), Z.add_0_r; reflexivity | lia]|].
    split; [exact KB|].
    intros a Hp. exact (apresent_grows _ _ _ _ HG Hp).
  + rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS). su_sv. apply bv_eq. vm_compute. reflexivity.
- (* null = 1: RCM *)
  pose proof (HB [su_rR 1] su_fs0 ltac:(vm_compute; reflexivity)
    ltac:(repeat apply Forall_cons; [apply (HrR 1 V40); lia | apply Forall_nil])
    ltac:(cbn; repeat split)
    HF0) as HS.
  aj_run_to_tok su_tblB_ok HS HJ SHOK su_Bspan 0x8369c; [su_awr U9 (R - sp0) | ].
  assert (Rg : forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r))
  by (intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E _ _ regs1 _
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]) HS HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr))).
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hch. rewrite U9 in Hch.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xa8 <= a < R + 0x110) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a)
  by (intros a Ha Hn'; unfold aview, mbyte; rewrite (su_fr _ _ _ _ a HFr Ha) by su_nw U9; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  apply KM; [ | | left; reflexivity].
  + split; [exact HJ|].
    split; [apply same_io_wvb|].
    split; [exact Rg|].
    split; [apply (su_cell E _ R _ 0xf0 (SOff 32 0) pp Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | rewrite (su_soff E 32 pp 0 E32), Z.add_0_r; reflexivity | lia]|].
    split; [exact KB|].
    intros a Hp. exact (apresent_grows _ _ _ _ HG Hp).
  + rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS). su_sv. apply bv_eq. vm_compute. reflexivity.
Qed.
End blkB.

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet A_ASAN_MEMSET.

(* what every exit of the set-up keeps, relative to the state at 0x82f30 *)
Definition su_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (R F pp : Z)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k /\ same_io mdc md3 /\
(forall r, In r [2; 3; 4; 8; 9; 19; 22; 23; 24; 25; 26; 27] ->
 getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
getr regs3 (Z_to_bv 5 18) = w64 (F + 0x1a0) /\
(forall i, 0 <= i < 136 -> aview rsegs (w_H W) mem3 (F + 0x1a0 + i) = Some 0) /\
(forall i, 52 <= i < 69 -> aview rsegs (w_H W) mem3 (shadow_addr F + i) = Some 0) /\
val_mem rsegs (mrestrict (w_H W) mem3) (R + 0xf0) 8 pp /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x1a0 <= a < F + 0x228) ->
 ~ (shadow_addr F + 52 <= a < shadow_addr F + 69) -> ~ (R + 0xa8 <= a < R + 0x110) ->
 aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem3 a).

(* THE BLOCK: from 0x82f30 to RCM 0x8369c, RC 0x83694 or PAIR 0x8307c *)
Lemma su_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R F pp pos nz n : Z)
(ip ps : bool) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> frame_addr lyc 4 pos = F -> In (pp, 19744) (ablocks B lyc Sc) ->
getr regs (Z_to_bv 5 2) = w64 R -> getr regs (Z_to_bv 5 3) = w64 (as_gp B) -> getr regs (Z_to_bv 5 4) = w64 (as_tp B) ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 19) = w64 (shadow_addr F) ->
getr regs (Z_to_bv 5 21) = w64 (pp + 0x4000) -> getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
getr regs (Z_to_bv 5 26) = w64 (F + 0x180) ->
R mod 32 = 0 -> R + 0x1e0 <= sp0 -> sp0 - STK <= R - ASTACK ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x40) 8 nz -> (nz = 0 \/ nz = 1) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x60) 8 F ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x90) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4008) 4 (Z.b2z ip) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4010) 4 (Z.b2z ps) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 n -> 0 <= n <= 32 ->
(forall regs3 mem3 md3,
 su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp regs3 mem3 md3 ->
 getr regs3 (Z_to_bv 5 11) = w64 (-1) -> (nz = 1 \/ ip = false) ->
 SRr rsegs W (cfg_at rsegs 0x8369c regs3 mem3 md3) Q) ->
(forall regs3 mem3 md3,
 su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp regs3 mem3 md3 ->
 val_mem rsegs (mrestrict (w_H W) mem3) (R + 0x108) 8 (F + 0x1a0) -> nz = 0 -> ip = true -> (ps = false \/ n = 0) ->
 SRr rsegs W (cfg_at rsegs 0x83694 regs3 mem3 md3) Q) ->
(forall regs3 mem3 md3,
 su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp regs3 mem3 md3 ->
 su_B_post_PAIR W R pp (F + 0x1a0) n regs3 mem3 -> nz = 0 -> ip = true -> ps = true -> 0 < n ->
 SRr rsegs W (@cfg_at (su_fx fx) rsegs 0x8307c regs3 mem3 md3) Q) ->
SRr rsegs W (cfg_at rsegs 0x82f30 regs memc mdc) Q.
Proof using AMEMSET.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp pos nz n ip ps Q
  HJ Hown HF HPP H2 H3 H4 H9 H19 H21 H23 H26 HR32 HRS HRstk V40 Hnz V60 V90 VA0 VF0 Vip Vps Vn Hn KM KC KP.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hs16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFc & HFapp).
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR HPP Hfin) as Hsep.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp 19744 HAR HPP) as (_ & Hp4096 & Hpc & Happ & _).
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HF in Hsep, HF4096, HFc, HFapp.
change (fs_frame_bytes 4) with 1024 in Hsep, HFc, HFapp. change (req_size 19744) with 19744 in Hsep, Hpc, Happ.
pose proof (ASAN_CEIL_range) as Hceil. unfold ASAN_CEIL in Hceil, Happ, HFapp.
unfold ASTACK in HRstk.
apply (su_A B AMEMSET STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos Q HJ Hown HF H2 H3 H4 H9 H19 H26
  HR32 HRS ltac:(unfold ASTACK; lia) V60).
intros regs1 mem1 md1 (HJ1 & Hio1 & Rk1 & R18 & Hx0 & Hsh0 & KA & Hgr1).
(* the cells and the fields at the memset's return: none lies in x, its shadow or the callee's stack *)
assert (Kc : forall a m v, val_mem rsegs (mrestrict (w_H W) memc) a m v ->
  (forall j, 0 <= j < Z.of_nat m -> 0 <= a + j < 2 ^ 64 /\ ~ (R - ESTACK <= a + j < R) /\
     ~ (F + 0x1a0 <= a + j < F + 0x228) /\ ~ (shadow_addr F + 52 <= a + j < shadow_addr F + 69)) ->
  val_mem rsegs (mrestrict (w_H W) mem1) a m v).
{ intros a m v Hv Hj. apply (val_mem_kept rsegs (w_H W) (w_H W) memc mem1 a m v); [|exact Hv].
  intros j Hj'. destruct (Hj j Hj') as (Ha & H1 & H2' & H3'). exact (KA _ Ha H1 H2' H3'). }
assert (KR : forall o m v, 0 <= o -> o + Z.of_nat m <= 0x1e0 -> val_mem rsegs (mrestrict (w_H W) memc) (R + o) m v ->
  val_mem rsegs (mrestrict (w_H W) mem1) (R + o) m v).
{ intros o m v Ho Hm Hv. apply (Kc _ _ _ Hv). intros j Hj. unfold shadow_addr, SHADOW_OFF, ESTACK.
  unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. lia. }
assert (KP' : forall o m v, 0 <= o -> o + Z.of_nat m <= 19744 -> val_mem rsegs (mrestrict (w_H W) memc) (pp + o) m v ->
  val_mem rsegs (mrestrict (w_H W) mem1) (pp + o) m v).
{ intros o m v Ho Hm Hv. apply (Kc _ _ _ Hv). intros j Hj. unfold shadow_addr, SHADOW_OFF, ESTACK.
  unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp, Happ. lia. }
apply (su_B B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 R pp (F + 0x1a0) nz n ip ps Q HJ1 HPP).
- rewrite (Rk1 9 ltac:(cbn; tauto)). exact H9.
- exact R18.
- rewrite (Rk1 21 ltac:(cbn; tauto)). exact H21.
- rewrite (Rk1 23 ltac:(cbn; tauto)). exact H23.
- exact HR32.
- exact HRS.
- unfold ASTACK. lia.
- lia.
- apply KR; [lia | cbn; lia | exact V40].
- exact Hnz.
- apply KR; [lia | cbn; lia | exact V90].
- apply KR; [lia | cbn; lia | exact VA0].
- apply KR; [lia | cbn; lia | exact VF0].
- apply KP'; [lia | cbn; lia | exact Vip].
- apply KP'; [lia | cbn; lia | exact Vps].
- apply KP'; [lia | cbn; lia | exact Vn].
- exact Hn.
- intros regs3 mem3 md3 (HJ3 & Hio3 & Rk3 & VF3 & KB & Hgr3) H11 Hc. apply (KM regs3 mem3 md3); [|exact H11 | exact Hc].
  split; [exact HJ3|].
  split; [exact (same_io_trans _ _ _ Hio1 Hio3)|].
  split; [intros r Hr; rewrite (Rk3 r) by (cbn [In] in Hr |- *; tauto); apply Rk1; cbn [In] in Hr |- *; tauto|].
  split; [rewrite (Rk3 18) by (cbn; tauto); exact R18|].
  split; [intros i Hi; rewrite KB; [apply Hx0; exact Hi | lia | lia]|].
  split; [intros i Hi; rewrite KB; [apply Hsh0; exact Hi | unfold shadow_addr, SHADOW_OFF; lia | unfold shadow_addr, SHADOW_OFF; lia]|].
  split; [exact VF3|].
  split; [intros a Ha H1 H2' H3' H4'; rewrite KB by assumption; exact (KA a Ha H1 H2' H3')|].
  intros a Hp. exact (Hgr3 a (Hgr1 a Hp)).
- intros regs3 mem3 md3 (HJ3 & Hio3 & Rk3 & VF3 & KB & Hgr3) H108 H0 Hip Hps. apply (KC regs3 mem3 md3); [|exact H108 | exact H0 | exact Hip | exact Hps].
  split; [exact HJ3|].
  split; [exact (same_io_trans _ _ _ Hio1 Hio3)|].
  split; [intros r Hr; rewrite (Rk3 r) by (cbn [In] in Hr |- *; tauto); apply Rk1; cbn [In] in Hr |- *; tauto|].
  split; [rewrite (Rk3 18) by (cbn; tauto); exact R18|].
  split; [intros i Hi; rewrite KB; [apply Hx0; exact Hi | lia | lia]|].
  split; [intros i Hi; rewrite KB; [apply Hsh0; exact Hi | unfold shadow_addr, SHADOW_OFF; lia | unfold shadow_addr, SHADOW_OFF; lia]|].
  split; [exact VF3|].
  split; [intros a Ha H1 H2' H3' H4'; rewrite KB by assumption; exact (KA a Ha H1 H2' H3')|].
  intros a Hp. exact (Hgr3 a (Hgr1 a Hp)).
- intros regs3 mem3 md3 (HJ3 & Hio3 & Rk3 & VF3 & KB & Hgr3) HPr H0 Hip Hps Hn0. apply (KP regs3 mem3 md3); [|exact HPr | exact H0 | exact Hip | exact Hps | exact Hn0].
  split; [exact HJ3|].
  split; [exact (same_io_trans _ _ _ Hio1 Hio3)|].
  split; [intros r Hr; rewrite (Rk3 r) by (cbn [In] in Hr |- *; tauto); apply Rk1; cbn [In] in Hr |- *; tauto|].
  split; [rewrite (Rk3 18) by (cbn; tauto); exact R18|].
  split; [intros i Hi; rewrite KB; [apply Hx0; exact Hi | lia | lia]|].
  split; [intros i Hi; rewrite KB; [apply Hsh0; exact Hi | unfold shadow_addr, SHADOW_OFF; lia | unfold shadow_addr, SHADOW_OFF; lia]|].
  split; [exact VF3|].
  split; [intros a Ha H1 H2' H3' H4'; rewrite KB by assumption; exact (KA a Ha H1 H2' H3')|].
  intros a Hp. exact (Hgr3 a (Hgr1 a Hp)).
Qed.
End blk.

Print Assumptions su_blk.
