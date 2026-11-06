(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S0.v, with its module paths changed; 422 of its 472 lines of code are new or changed and 160 lines of the source are left out. *)
(* Segment lemma cs_S1 of check_step's asan-ubsan walk (a Theorem Labs lane, 2026-10-29), proved against the cut statement of
   lib/AU/P_check_step_cut.v (unchanged by this lane). Rule 24 is met: this file proves one segment of the walk, not
   the function; the callees are the Section hypotheses.
   The asan twin is at 637db22c883 (lib/A/P_check_step_S1.v); this file is its port to the
   asan-ubsan image.

   Segment S1 of the ASan walk of check_step in fuzz_scene.asan-ubsan (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f): 0x833f4 .. 0x835c4.
   The first shadow load, C1 checks of blk[0], [1], [2], [6], the 32-turn sum loop, C2 (segment, length) and the off
   slice the asan-ubsan build computes before the length test (0x8353c-0x8357c, a2 = scene_off k at the cut).
   How: blk's 34 bytes and its shadow come from the entry facts through the journal (FP = [], a frame of the entry
   state: range_addressable_entry_frame, YCbq.v:2661); the symbolic state at 0x833f4 holds blk[0..7) as the literals
   scene_block fixes for the arm of k (1..341, 0, 342) and blk[7..34) as atoms 32..58, so the run decides every
   C1/C2 compare and abort branch and unrolls the loop (trip count 32); the one branch it stops at, the checksum test
   `bnez a0` 0x834fc, is refuted from scene_block's checksum byte. The UBSan guards are decided on their no-trap edge
   inside the run: 0x83414, 0x8343c, 0x83464, 0x8351c, 0x83588 from the facts of blk (4096 <= blk, blk + 34 below the
   allocation ceiling < 2^47); 0x83570 (signed k - 1, 1 <= k <= 341 arm) from the facts of k; the loop guard 0x834b8
   on each of the 32 turns from the entry conditions s1_conds (s1_conds_ok). The one store is the spill slot
   sd s10,0x10(s1) 0x833fc (stack window, below the 13 saved slots), so the flag word and the saved slots of cs_frame
   are kept. Pure lemmas: restated from plain lib/Prog/check_step.v:33-51, :88-92 (scene_fields_length,
   scene_block_length, cks_sum, byte_sum_nonneg, segK, lenK), since that module Requires the plain kit. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.  (* image-specific: lib.AU (gate 6o) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame P_check_step_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* ---- pure facts of the block (released plain lib/Prog/check_step.v:33-51, :88-92, restated here: that module
   Requires the plain kit, whose tactic redefinitions this walk must not load) ---- *)
#[local] Ltac s1_norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.
Lemma s1_fields_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_fields b k) = 31%nat.
Proof.
intros b k Hb Hk. s1_norm_nat_lits. unfold scene_fields, scene_payload, scene_off.
destruct (Z.eqb_spec k 0); [subst; cbn [length app]; rewrite length_firstn, Hb; reflexivity|].
destruct (Z.eqb_spec k 342).
- cbn [length app]. rewrite length_app, length_firstn, length_skipn, Hb. reflexivity.
- cbn [length app]. rewrite length_firstn, length_skipn, Hb. lia.
Qed.
Lemma s1_block_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_block b k) = 34%nat.
Proof. intros b k Hb Hk. unfold scene_block. rewrite !length_app, s1_fields_length by assumption. reflexivity. Qed.
Lemma s1_cks_sum : forall S, 0 <= S -> (S + bv_unsigned (Z_to_bv 8 ((256 - S mod 256) mod 256))) mod 256 = 0.
Proof.
intros S HS. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8).
Z.div_mod_to_equations. lia.
Qed.
Lemma s1_byte_sum_nonneg : forall l, 0 <= byte_sum l.
Proof.
induction l as [|x l IH]; cbn [byte_sum fold_right]; [lia|].
pose proof (bv_unsigned_in_range 8 x). unfold byte_sum in IH. lia.
Qed.
Lemma s1_segK : forall K, K <> 0 -> K <> 342 -> scene_seg K = 0.
Proof. intros K H0 H1. unfold scene_seg. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.
Lemma s1_lenK : forall K, K <> 0 -> K <> 342 -> scene_len K = 26.
Proof. intros K H0 H1. unfold scene_len. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.
(* ---- small word facts ---- *)
Lemma s1_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small x) by lia.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= x / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite ?(Z.mod_small (x / 8)) by exact Hd. reflexivity.
Qed.
Lemma s1_rdword_kept : forall (rd rd' : Z -> option Z) a,
(forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma s1_chunk1 : forall segs E m base off e (y : byte),
sv_denot E e = Z_to_bv 64 (bv_unsigned y) -> val_mem segs m (base + off) 1 (bv_unsigned y) ->
YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 e)).
Proof.
intros segs E m base off e y He Hv. pose proof (bv_unsigned_in_range 8 y) as Hy. change (bv_modulus 8) with 256 in Hy.
apply (chunk_ok_val segs E m base off 1 e (bv_unsigned y)); [exact He | cbn; lia | cbn; lia | exact Hv].
Qed.
Lemma s1_keep_step : forall segs E rs H (m0 m m' : word -> option byte) lo hi,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> lo <= a < hi) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m a = aview segs H m0 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m' a = aview segs H m0 a).
Proof.
intros segs E rs H m0 m m' lo hi HF Hw Hk a Ha Hn. rewrite <- (Hk a Ha Hn).
apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. intros Hin. exact (Hn (Hw a Ha Hin)).
Qed.
(* ---- the symbolic state at 0x833f4 ---- *)
(* blk = s3 (atom 19): its 34 bytes, the seven header bytes as the literals the arm fixes, bytes 7..33 as atoms
   32..58. The spill slot sd s10,0x10(s1) (0x833fc) is the one store: s1 = atom 9 = the realigned sp. *)
Definition s1_chunks (c3 c5 : Z) : list YP09.chunk :=
[ YP09.mkChunk 0 (CVal 1 (SLit 205)); YP09.mkChunk 1 (CVal 1 (SLit 234)); YP09.mkChunk 2 (CVal 1 (SLit 1));
  YP09.mkChunk 3 (CVal 1 (SLit c3)); YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit c5));
  YP09.mkChunk 6 (CVal 1 (SLit 0)) ] ++
map (fun j => YP09.mkChunk (7 + Z.of_nat j) (CVal 1 (SOff (32 + j) 0))) (seq 0 27).
Definition s1_regions (c3 c5 : Z) : smem :=
[ YP09.mkRegion (Some 9%nat) 16 24 16 24 []; YP09.mkRegion (Some 19%nat) 0 34 0 0 (s1_chunks c3 c5) ].
(* The UBSan guard 0x834b8 of the sum loop (`beq a6,a3`, a3 = 32), on turn j: a6 = (mask & (-2 - blk)) + (32 - j), with
   mask = seqz(-1 - blk) - 1 (0x83490-0x834b4), as the run builds it. Its no-trap edge on each of the 32 turns is a
   condition of the entry facts (s1_conds_ok: blk + 34 <= 2^47), so the run decides it. *)
Definition s1_gx : sv := SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_SUB (SLit 0) (SOff 19 1)) (SLit 1)) (SLit (-1)))
  (SAlu ALU_SUB (SLit 0) (SOff 19 2)).
Definition s1_gc (j : nat) : acond := mkAC BC_NE (SAlu ALU_ADD s1_gx (SLit (32 - Z.of_nat j))) (SLit 32).
Definition s1_conds : list acond := map s1_gc (seq 0 32).
Lemma s1_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z H. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma s1_zneg : forall x, 0 < x < 2 ^ 64 -> zcanon (0 - x) = 2 ^ 64 - x.
Proof. intros x Hx. unfold zcanon, M64. rewrite <- (Z.mod_add (0 - x) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma s1_gx_U : forall E blk, bv_unsigned (ew E 19) = blk -> 4096 <= blk < 2 ^ 47 -> U E s1_gx = 2 ^ 64 - (blk + 2).
Proof.
intros E blk H19 Hb. unfold s1_gx. rewrite !U_SAlu, !U_SLit, !U_SOff, H19. cbn [zalu_raw].
change (zcanon 0) with 0. change (zcanon 1) with 1. change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite (s1_zc (blk + 1)), (s1_zc (blk + 2)) by lia.
rewrite (s1_zneg (blk + 1)), (s1_zneg (blk + 2)) by lia.
replace (2 ^ 64 - (blk + 1) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
change (zcanon 0) with 0. rewrite Z.add_0_l, (s1_zc (2 ^ 64 - 1)) by lia.
change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
rewrite Z.mod_small by lia. apply s1_zc. lia.
Qed.
Lemma s1_gc_ok : forall E blk j, bv_unsigned (ew E 19) = blk -> 4096 <= blk < 2 ^ 47 -> (j < 32)%nat -> acond_ok E (s1_gc j).
Proof.
intros E blk j H19 Hb Hj. unfold acond_ok, s1_gc. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U.
rewrite U_SAlu, (s1_gx_U E blk H19 Hb), !U_SLit. cbn [zalu_raw].
rewrite (s1_zc 32), (s1_zc (32 - Z.of_nat j)) by lia.
rewrite s1_zc by lia. apply negb_true_iff, Z.eqb_neq. lia.
Qed.
Lemma s1_conds_ok : forall E blk, bv_unsigned (ew E 19) = blk -> 4096 <= blk < 2 ^ 47 -> conds_ok E s1_conds.
Proof.
intros E blk H19 Hb. unfold s1_conds.
assert (G : forall l, (forall j, In j l -> (j < 32)%nat) -> conds_ok E (map s1_gc l)).
{ induction l as [|j l IH]; intros Hl; cbn [map conds_ok]; [exact I|].
  split; [apply (s1_gc_ok E blk); [exact H19 | exact Hb | apply Hl; left; reflexivity]
  | apply IH; intros j' Hj'; apply Hl; right; exact Hj']. }
apply G. intros j Hj. apply in_seq in Hj. lia.
Qed.
Lemma s1_zc_neg : forall x, - 2 ^ 64 <= x < 0 -> zcanon x = x + 2 ^ 64.
Proof. intros x Hx. unfold zcanon, M64. rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma s1_zc_wrap : forall x, 2 ^ 64 <= x < 2 * 2 ^ 64 -> zcanon x = x - 2 ^ 64.
Proof. intros x Hx. unfold zcanon, M64. rewrite <- (Z.mod_add x (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma s1_conds_app : forall E C D, conds_ok E C -> conds_ok E D -> conds_ok E (C ++ D).
Proof. intros E C D. induction C as [|c C IH]; cbn [app conds_ok]; [tauto|]. intros [Hc HC] HD. split; [exact Hc | apply IH; assumption]. Qed.
Definition s1_facts (f20 : afact) (C : list acond) : facts :=
mkFacts ((9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) :: (19%nat, mkAF 4096 140737479966720 3) :: (20%nat, f20) ::
  (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 27)) (C ++ s1_conds) [].
Definition s1_a1 : sv := SAlu ALU_SRL (SOff 19 0) (SLit 3).
Definition s1_regs : list sv := sr_set sr_atoms (11%bv : bv 5) s1_a1.
Definition ss_s1 (c3 c5 : Z) (f20 : afact) (C : list acond) : sstate :=
mkSS (AF_check_step + 0x160) s1_regs (s1_regions c3 c5) None (s1_facts f20 C).
Definition s1_SH : list shent := [mkSHE 19 0 34].
Definition s1_Bx : sv := SOff 27 0.
Definition S1_STOP : Z := AF_check_step + 0x330.
Definition s1_extra (YS : list byte) : list word := map (fun y : byte => Z_to_bv 64 (bv_unsigned y)) YS.
(* The checksum test 0x834f8/0x834fc (`andi a0,a2,0xff; bnez a0`): a taken branch means the byte sum is not 0 mod 256. *)
Lemma s1_and255 : forall E s l c, lin_nf s = Some (l, c) ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND s (SLit 255))) (sv_denot E (SLit 0)) = true ->
(lin_denot E l + c) mod 256 <> 0.
Proof.
intros E s l c Hl Hb. rewrite branch_ne_U in Hb. apply negb_true_iff, Z.eqb_neq in Hb.
rewrite U_SAlu, !U_SLit in Hb. cbn [zalu_raw] in Hb. rewrite (lin_nf_sound E s l c Hl) in Hb.
unfold zcanon, M64 in Hb. change (255 mod 2 ^ 64) with (Z.ones 8) in Hb. change (0 mod 2 ^ 64) with 0 in Hb.
rewrite Z.land_ones in Hb by lia.
rewrite (Z.mod_mod_divide (lin_denot E l + c) (2 ^ 64) (2 ^ 8)) in Hb by (exists (2 ^ 56); reflexivity).
rewrite (Z.mod_small ((lin_denot E l + c) mod 2 ^ 8) (2 ^ 64)) in Hb by (pose proof (Z.mod_pos_bound (lin_denot E l + c) (2 ^ 8) ltac:(lia)); lia).
change (2 ^ 8) with 256 in Hb. exact Hb.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Definition s1_env (regs : bvmap 5 word) (YS : list byte) : env := Eimg (Ereg regs (s1_extra YS)).
Lemma s1_ew_byte : forall regs YS j, (j < length YS)%nat -> (length YS <= 27)%nat ->
ew (s1_env regs YS) (32 + j) = Z_to_bv 64 (bv_unsigned (nth j YS (Z_to_bv 8 0))).
Proof.
intros regs YS j Hj H27. unfold s1_env. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold s1_extra.
rewrite (nth_indep _ _ (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) by (rewrite length_map; exact Hj).
rewrite (map_nth (fun y : byte => Z_to_bv 64 (bv_unsigned y))). reflexivity.
Qed.
Lemma s1_ew_reg : forall regs YS n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s1_env regs YS) n = getr regs r.
Proof.
intros regs YS n r H. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
unfold s1_env. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
Section h.
Variable B : asyms.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* relocated laws and the glue's bindings (cgif A/ACk1.v:64-74, :82; ScenePaLib.v:307, SceneFrame.v:96). *)
(* LAWS and SMP are theorems, not hypotheses (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803) and
   the model law ml_stack_malloc_progress (YG0d.v:520-521). The UAR flag reads 1 in every AR state by
   al_const (AR_const_law, YG0d.v:461-467), so no flag hypothesis is taken. *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* ---- the walk's steps ---- *)
(* The one store (the spill slot sd s10,0x10(s1), 0x833fc) is in the stack window; blk's region is read-only. *)
#[local] Ltac s1_awr U9 WS :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (-128));
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite U9; lia | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | ] ].
(* The written window of a run is the spill slot [sp0 - 112, sp0 - 104). *)
#[local] Ltac s1_wr rs U9 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a Ha (r & Hin & Hr);
  let rs' := eval vm_compute in rs in change (In r rs') in Hin; cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hr; rewrite ?U9 in Hr; lia |]);
  destruct Hin.
(* After a run: every byte outside the spill slot is the cut's (KEEP), from the run's frame_of. *)
#[local] Ltac s1_keep sp0 U9 KEEP :=
  lazymatch type of KEEP with forall a, _ -> _ -> aview ?sg ?Hh ?mo a = aview _ _ ?m0 a =>
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict Hh mo) (mrestrict _ ?m') |- _ =>
    let K2 := fresh "KEEP" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0 - 104) -> aview sg Hh m' a = aview sg Hh m0 a)
      by (apply (s1_keep_step sg Ex rs Hh m0 mo m' (sp0 - 112) (sp0 - 104) HFr); [s1_wr rs U9 | exact KEEP]);
    clear KEEP; rename K2 into KEEP
  end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* The checksum branch (bnez 0x834fc) taken: the byte sum of blk[2..34) is not 0 mod 256, against scene_block's
   checksum byte (SUM). *)
#[local] Ltac s1_refute UYn YS B3 B5 SUM :=
  exfalso;
  lazymatch goal with Hc : branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_AND ?s (SLit 255))) _ = true |- _ =>
    let r := eval vm_compute in (lin_nf s) in
    lazymatch r with Some (?l, ?c) =>
      let Hne := fresh "Hne" in
      pose proof (s1_and255 Ex s l c ltac:(vm_compute; reflexivity) Hc) as Hne;
      cbn [lin_denot ew ewset Nat.eqb] in Hne;
      rewrite !UYn in Hne by lia;
      unfold YS in Hne; cbn [nth Nat.sub] in Hne;
      rewrite B3, B5 in SUM;
      revert Hne SUM; clear; intros; Z.div_mod_to_equations; lia
    end end.
#[local] Ltac s1_regeq HS ER n r G :=
  let Hr := fresh "Hr" in prreg HS r Hr; rewrite Hr, (ER n r eq_refl); exact G.
#[local] Ltac s1_regoff HS ER G26 r :=
  let Hr := fresh "Hr" in prreg HS r Hr; rewrite Hr, (ER 26%nat (26%bv : bv 5) eq_refl), G26;
  unfold w64; rewrite unsigned_lit_small by lia; reflexivity.
#[local] Ltac s1_reglit HS r SK :=
  let Hr := fresh "Hr" in prreg HS r Hr; rewrite Hr, SK; reflexivity.
(* a2 = off (0x8353c-0x8357c): the run's value of register 12 against scene_off k (SO, the arm's value). *)
#[local] Ltac s1_reg12 HS SO U20 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let Hr := fresh "Hr" in
    pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx (12%bv : bv 5) HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ssx) (12%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (12%bv : bv 5)) with e in Hr; cbn [ms_regs restrict mkst] in Hr;
    rewrite Hr, SO, denot_lit_U; unfold w64; f_equal;
    rewrite ?U_SAlu, ?U_SMd, ?U_SLit, ?U_SOff; cbn [zalu_raw zmd_raw extK ewset ew Nat.eqb]; rewrite ?U20;
    repeat match goal with |- context [zcanon ?x] => lazymatch x with context [zcanon _] => fail | _ =>
      first [ rewrite (s1_zc x) by lia | rewrite (s1_zc_neg x) by lia | rewrite (s1_zc_wrap x) by lia ] end end;
    lia
  end.
Lemma cs_S1 : CS_S1_stmt SK B.
Proof.
unfold CS_S1_stmt.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 HST.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HST as (HPRE & HFR & R9 & R19 & R20 & R5 & R11).
pose proof HPRE as (HAFN & Hal32 & Htop32 & Hfr7 & HROD & H10 & H11 & H12 & Hk & HFO & HBIN & HLb & HBB & HBK & Hev & Hlive).
pose proof HFR as (HJ & HBL & HFLAG & HSAV & G2 & G3 & G4 & G8 & G18 & G25 & G26 & G27).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_STEP_STK = 8496) by (vm_compute; reflexivity).
unfold CS_BLK_LEN, CS_BODY_LEN, CS_LAST in *.
destruct HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hb8 & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof HJ as (HAR1 & _ & _ & _ & _ & Hfrs1 & _ & _ & HKhi & _ & _ & HKfr & _ & HPRES1 & _).
assert (Hown : In (CS_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly1 S1 W1 mem1 md1 CS_CID fpos HAR1 Hown) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes CS_CID) with 256 in HFceil.
(* blk's bytes and shadow at the cut: blk lies in a frame of the entry state, which the journal keeps (FP = []). *)
assert (BKa : forall i, 0 <= i < 34 -> aview SEGS (w_H W1) mem1 (blk + i) = aview SEGS (w_H W) mem (blk + i)).
{ intros i Hi. apply (HKfr cid pos (blk + i) Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil]. }
assert (RA1 : range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF blk 34).
{ eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ | exact Hfin | exact Hcid | exact Hflo | exact Hfhi | exact Hfal
  | intros x Hx; destruct (inFP_nil x Hx) | exact HAR | exact HRA]. }
assert (HLb' : length b = 8904%nat) by (rewrite HLb; vm_compute; reflexivity).
pose proof (s1_block_length b k HLb' Hk) as LB34.
assert (HD : forall i, 0 <= i < 34 -> val_mem SEGS (mrestrict (w_H W1) mem1) (blk + i) 1
  (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))).
{ intros i Hi. refine (proj1 (val_mem1_of_aview SEGS (w_H W1) mem1 (blk + i) _ _)). rewrite (BKa i Hi). exact (HBK i Hi). }
set (L := scene_block b k) in *.
assert (EB : scene_block b k = L) by reflexivity. clearbody L.
destruct L as [|y0 L]; [discriminate LB34|]. destruct L as [|y1 L]; [discriminate LB34|].
destruct L as [|y2 L]; [discriminate LB34|]. destruct L as [|y3 L]; [discriminate LB34|].
destruct L as [|y4 L]; [discriminate LB34|]. destruct L as [|y5 L]; [discriminate LB34|].
destruct L as [|y6 L]; [discriminate LB34|]. destruct L as [|y7 L]; [discriminate LB34|].
destruct L as [|y8 L]; [discriminate LB34|]. destruct L as [|y9 L]; [discriminate LB34|].
destruct L as [|y10 L]; [discriminate LB34|]. destruct L as [|y11 L]; [discriminate LB34|].
destruct L as [|y12 L]; [discriminate LB34|]. destruct L as [|y13 L]; [discriminate LB34|].
destruct L as [|y14 L]; [discriminate LB34|]. destruct L as [|y15 L]; [discriminate LB34|].
destruct L as [|y16 L]; [discriminate LB34|]. destruct L as [|y17 L]; [discriminate LB34|].
destruct L as [|y18 L]; [discriminate LB34|]. destruct L as [|y19 L]; [discriminate LB34|].
destruct L as [|y20 L]; [discriminate LB34|]. destruct L as [|y21 L]; [discriminate LB34|].
destruct L as [|y22 L]; [discriminate LB34|]. destruct L as [|y23 L]; [discriminate LB34|].
destruct L as [|y24 L]; [discriminate LB34|]. destruct L as [|y25 L]; [discriminate LB34|].
destruct L as [|y26 L]; [discriminate LB34|]. destruct L as [|y27 L]; [discriminate LB34|].
destruct L as [|y28 L]; [discriminate LB34|]. destruct L as [|y29 L]; [discriminate LB34|].
destruct L as [|y30 L]; [discriminate LB34|]. destruct L as [|y31 L]; [discriminate LB34|].
destruct L as [|y32 L]; [discriminate LB34|]. destruct L as [|y33 L]; [discriminate LB34|].
destruct L; [|discriminate LB34]. clear LB34.
assert (Y0 : y0 = Z_to_bv 8 0xcd) by exact (f_equal (fun l => nth 0 l (Z_to_bv 8 0)) (eq_sym EB)).
assert (Y1 : y1 = Z_to_bv 8 0xea) by exact (f_equal (fun l => nth 1 l (Z_to_bv 8 0)) (eq_sym EB)).
assert (Y2 : y2 = Z_to_bv 8 1) by exact (f_equal (fun l => nth 2 l (Z_to_bv 8 0)) (eq_sym EB)).
assert (Y3 : y3 = Z_to_bv 8 (scene_seg k)) by exact (f_equal (fun l => nth 3 l (Z_to_bv 8 0)) (eq_sym EB)).
assert (Y4 : y4 = Z_to_bv 8 0) by exact (f_equal (fun l => nth 4 l (Z_to_bv 8 0)) (eq_sym EB)).
assert (Y5 : y5 = Z_to_bv 8 (scene_len k)) by exact (f_equal (fun l => nth 5 l (Z_to_bv 8 0)) (eq_sym EB)).
assert (Y6 : y6 = Z_to_bv 8 0) by exact (f_equal (fun l => nth 6 l (Z_to_bv 8 0)) (eq_sym EB)).
assert (SUM : (bv_unsigned y2 + bv_unsigned y3 + bv_unsigned y4 + bv_unsigned y5 + bv_unsigned y6 + bv_unsigned y7 +
  bv_unsigned y8 + bv_unsigned y9 + bv_unsigned y10 + bv_unsigned y11 + bv_unsigned y12 + bv_unsigned y13 +
  bv_unsigned y14 + bv_unsigned y15 + bv_unsigned y16 + bv_unsigned y17 + bv_unsigned y18 + bv_unsigned y19 +
  bv_unsigned y20 + bv_unsigned y21 + bv_unsigned y22 + bv_unsigned y23 + bv_unsigned y24 + bv_unsigned y25 +
  bv_unsigned y26 + bv_unsigned y27 + bv_unsigned y28 + bv_unsigned y29 + bv_unsigned y30 + bv_unsigned y31 +
  bv_unsigned y32 + bv_unsigned y33) mod 256 = 0).
{ assert (Ef : scene_fields b k ++ [Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256)]
    = [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24;
       y25; y26; y27; y28; y29; y30; y31; y32] ++ [y33]) by exact (f_equal (skipn 2) EB).
  apply app_inj_tail in Ef. destruct Ef as [EF EC].
  rewrite <- EC, EF.
  pose proof (s1_cks_sum (byte_sum [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18;
    y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32]) (s1_byte_sum_nonneg _)) as C.
  unfold byte_sum in C |- *. cbn [fold_right] in C |- *.
  match goal with |- ?X mod 256 = 0 => match type of C with ?Y mod 256 = 0 =>
    replace X with Y by lia; exact C end end. }
set (YS := [y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27;
  y28; y29; y30; y31; y32; y33]).
assert (HYS : length YS = 27%nat) by reflexivity.
assert (HDY : forall j, (j < 27)%nat -> val_mem SEGS (mrestrict (w_H W1) mem1) (blk + (7 + Z.of_nat j)) 1
  (bv_unsigned (nth j YS (Z_to_bv 8 0)))).
{ intros j Hj. pose proof (HD (7 + Z.of_nat j) ltac:(lia)) as V. replace (Z.to_nat (7 + Z.of_nat j)) with (7 + j)%nat in V by lia.
  exact V. }
(* registers and env *)
set (sp0 := spZ regs) in *.
set (F := frame_addr ly1 CS_CID fpos) in *.
set (E := s1_env regs1 YS).
assert (HEI : img_env VAL A_LIM E) by (unfold E, s1_env; apply Eimg_env).
assert (Rblk : 0 <= blk < 2 ^ 64) by lia.
assert (U19 : bv_unsigned (ew E 19) = blk) by (unfold E; rewrite (s1_ew_reg _ _ 19 (19%bv : bv 5)) by reflexivity; rewrite R19; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp0 - 128) by (unfold E; rewrite (s1_ew_reg _ _ 9 (9%bv : bv 5)) by reflexivity; rewrite R9; unfold w64, CHECK_STEP_FRAME; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (unfold E; rewrite (s1_ew_reg _ _ 27 (27%bv : bv 5)) by reflexivity; rewrite G27; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U20 : bv_unsigned (ew E 20) = k) by (unfold E; rewrite (s1_ew_reg _ _ 20 (20%bv : bv 5)) by reflexivity; rewrite R20; unfold w64; apply unsigned_lit_small; lia).
assert (EYS : forall j, (j < 27)%nat -> ew E (32 + j) = Z_to_bv 64 (bv_unsigned (nth j YS (Z_to_bv 8 0))))
  by (intros j Hj; unfold E; apply s1_ew_byte; rewrite HYS; lia).
assert (HSH : sh_ok SEGS s1_Bx s1_SH E (mrestrict (w_H W1) mem1)).
{ unfold sh_ok, s1_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) mem1 E s1_Bx 19 blk 34 blk 0 34 RA1).
  - unfold U, s1_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
  - rewrite U_SOff, U19, Z.add_0_r. unfold zcanon, M64. apply Z.mod_small. lia.
  - lia. - lia.
  - intros x Hx. revert Happ Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia. }
assert (HRG : regs_ok E s1_regs regs1).
{ intros rr. unfold s1_regs. destruct (decide (rr = (11%bv : bv 5))) as [->|Hne].
  - rewrite sr_get_set_same by reflexivity. unfold s1_a1. cbn [sv_denot]. rewrite U19, Z.add_0_r.
    rewrite s1_srl3 by lia. exact R11.
  - rewrite sr_get_set_other by exact Hne. apply regs_ok_Eimg_Ereg. }
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; unfold E; apply s1_ew_reg; exact Hn).
assert (UYn : forall n, (32 <= n < 59)%nat -> bv_unsigned (ew E n) = bv_unsigned (nth (n - 32) YS (Z_to_bv 8 0))).
{ intros n Hn. assert (Hn' : n = (32 + (n - 32))%nat) by lia. rewrite Hn' at 1. rewrite (EYS (n - 32)%nat) by lia.
  apply unsigned_lit_small. pose proof (bv_unsigned_in_range 8 (nth (n - 32) YS (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr. lia. }
rewrite WS in Hslo.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0 - 104) ->
  aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W1) mem1 a) by reflexivity.
assert (SUM' : (1 + bv_unsigned y3 + bv_unsigned y5 + (bv_unsigned y7 + bv_unsigned y8 + bv_unsigned y9 +
  bv_unsigned y10 + bv_unsigned y11 + bv_unsigned y12 + bv_unsigned y13 + bv_unsigned y14 + bv_unsigned y15 +
  bv_unsigned y16 + bv_unsigned y17 + bv_unsigned y18 + bv_unsigned y19 + bv_unsigned y20 + bv_unsigned y21 +
  bv_unsigned y22 + bv_unsigned y23 + bv_unsigned y24 + bv_unsigned y25 + bv_unsigned y26 + bv_unsigned y27 +
  bv_unsigned y28 + bv_unsigned y29 + bv_unsigned y30 + bv_unsigned y31 + bv_unsigned y32 + bv_unsigned y33)) mod 256 = 0).
{ revert SUM. rewrite Y2, Y4, Y6. change (bv_unsigned (Z_to_bv 8 1)) with 1. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  intros SUM. match goal with |- ?X mod 256 = 0 => match type of SUM with ?Y mod 256 = 0 =>
    replace X with Y by lia; exact SUM end end. }
clear SUM. rename SUM' into SUM.
(* The symbolic state at 0x833f4, for the arm's literals blk[3] = c3, blk[5] = c5 and its facts on k. *)
assert (HSgen : forall c3 c5 f20 C, bv_unsigned y3 = c3 -> bv_unsigned y5 = c5 -> afact_ok E 20 f20 -> conds_ok E C ->
  st_ok_pi SEGS VAL E (ss_s1 c3 c5 f20 C)
    (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + (AF_check_step + 0x160))) mem1 (seg_rom SEGS)))).
{ intros c3 c5 f20 C B3 B5 F20 HC.
  rewrite restrict_mkst_fx. unfold ss_s1. apply pa_entry_st_ok_full.
  + exact HRG.
  + vm_compute. reflexivity.
  + unfold s1_regions. constructor; [|constructor; [|constructor]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPRES1. rewrite WS. lia.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold s1_chunks. apply Forall_app. split.
      -- repeat constructor.
         ++ apply (s1_chunk1 SEGS E _ blk 0 (SLit 205) y0); [rewrite Y0; reflexivity | exact (HD 0 ltac:(lia))].
         ++ apply (s1_chunk1 SEGS E _ blk 1 (SLit 234) y1); [rewrite Y1; reflexivity | exact (HD 1 ltac:(lia))].
         ++ apply (s1_chunk1 SEGS E _ blk 2 (SLit 1) y2); [rewrite Y2; reflexivity | exact (HD 2 ltac:(lia))].
         ++ apply (s1_chunk1 SEGS E _ blk 3 (SLit c3) y3); [rewrite B3; reflexivity | exact (HD 3 ltac:(lia))].
         ++ apply (s1_chunk1 SEGS E _ blk 4 (SLit 0) y4); [rewrite Y4; reflexivity | exact (HD 4 ltac:(lia))].
         ++ apply (s1_chunk1 SEGS E _ blk 5 (SLit c5) y5); [rewrite B5; reflexivity | exact (HD 5 ltac:(lia))].
         ++ apply (s1_chunk1 SEGS E _ blk 6 (SLit 0) y6); [rewrite Y6; reflexivity | exact (HD 6 ltac:(lia))].
      -- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
         apply (s1_chunk1 SEGS E _ blk (7 + Z.of_nat j) (SOff (32 + j) 0) (nth j YS (Z_to_bv 8 0))).
         ++ cbn [sv_denot]. rewrite (EYS j) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
         ++ apply HDY. lia.
  + apply pairwise_disjoint_of_extents. unfold s1_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [apply s1_conds_app; [exact HC | apply (s1_conds_ok E blk U19); lia] | exact I]].
    cbn [s1_facts f_atoms atoms_ok map seq app Nat.add].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9; change (2 ^ 5) with 32;
      split; [lia|]; split; [|lia]; revert Hal32; clear; intros; Z.div_mod_to_equations; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19; change (2 ^ 3) with 8; lia|].
    split; [exact F20|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U27; rewrite Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF; lia|].
    repeat match goal with
    | |- afact_ok _ ?n (mkAF 0 255 0) /\ _ =>
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (UYn n) by lia;
        pose proof (bv_unsigned_in_range 8 (nth (n - 32) YS (Z_to_bv 8 0))) as Hr; change (bv_modulus 8) with 256 in Hr;
        rewrite Z.pow_0_r, Z.mod_1_r; lia|]
    end.
    exact I. }
clearbody E.
unfold cfg_at, CS_PC1, A_check_step, w64. replace (BASE + AF_check_step + 0x160) with (BASE + (AF_check_step + 0x160)) by lia.
(* the three arms of k: 1..341 (segment 0, length 26), 0 (segment 1, length 24), 342 (segment 2, length 14) *)
assert (KA : (1 <= k <= 341) \/ k = 0 \/ k = 342) by lia.
destruct KA as [K1 | [K0 | K342]];
[ assert (SK3 : scene_seg k = 0) by (apply s1_segK; lia); assert (SK5 : scene_len k = 26) by (apply s1_lenK; lia);
  assert (B3 : bv_unsigned y3 = 0) by (rewrite Y3, SK3; reflexivity);
  assert (B5 : bv_unsigned y5 = 26) by (rewrite Y5, SK5; reflexivity);
  assert (SO : scene_off k = 24 + 26 * (k - 1)) by (unfold scene_off; rewrite (proj2 (Z.eqb_neq k 0)), (proj2 (Z.eqb_neq k 342)) by lia; reflexivity);
  pose proof (HSgen 0 26 (mkAF 1 341 0) [] B3 B5
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20, Z.pow_0_r, Z.mod_1_r; lia) I) as HS
| assert (SK3 : scene_seg k = 1) by (rewrite K0; reflexivity); assert (SK5 : scene_len k = 24) by (rewrite K0; reflexivity);
  assert (B3 : bv_unsigned y3 = 1) by (rewrite Y3, SK3; reflexivity);
  assert (B5 : bv_unsigned y5 = 24) by (rewrite Y5, SK5; reflexivity);
  assert (SO : scene_off k = 0) by (rewrite K0; reflexivity);
  pose proof (HSgen 1 24 (mkAF 0 0 0) [mkAC BC_EQ (SOff 20 0) (SLit 0)] B3 B5
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20, Z.pow_0_r, Z.mod_1_r; lia)
    ltac:(split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, U_SOff, U20, U_SLit, K0; reflexivity | exact I])) as HS
| assert (SK3 : scene_seg k = 2) by (rewrite K342; reflexivity); assert (SK5 : scene_len k = 14) by (rewrite K342; reflexivity);
  assert (B3 : bv_unsigned y3 = 2) by (rewrite Y3, SK3; reflexivity);
  assert (B5 : bv_unsigned y5 = 14) by (rewrite Y5, SK5; reflexivity);
  assert (SO : scene_off k = 8890) by (rewrite K342; reflexivity);
  pose proof (HSgen 2 14 (mkAF 342 342 0) [mkAC BC_NE (SOff 20 0) (SLit 0)] B3 B5
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20, Z.pow_0_r, Z.mod_1_r; lia)
    ltac:(split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, U_SOff, U20, U_SLit, K342; reflexivity | exact I])) as HS ].
all: clear HSgen HD HBK BKa HRG.
(* the run to the checksum branch, its refutation, the run to 0x835c4, cs_st2 *)
all: paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN S1_STOP;
  [ s1_awr U9 WS
  | s1_keep sp0 U9 KEEP;
    psrr_branch_tok RUN BR HS HSH BAND_SPAN;
    [ s1_refute UYn YS B3 B5 SUM
    | paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN S1_STOP;
      [ s1_awr U9 WS
      | s1_keep sp0 U9 KEEP;
        lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
          pmkst HSx; apply SRr_ret;
          exists ly1, S1, (ms_regs ms), (ms_mem ms); eexists; split;
          [ unfold cfg_at, CS_PC2, A_check_step, w64;
            replace (BASE + AF_check_step + 0x330) with (BASE + 3360) by (unfold AF_check_step; lia); reflexivity
          | unfold cs_st2; split; [exact HPRE|]; split;
            [ unfold cs_frame; split; [exact HJ|]; split; [exact HBL|]; split;
              [ rewrite (s1_rdword_kept (aview SEGS (w_H W1) mem1)); [exact HFLAG |];
                intros i Hi; apply KEEP; change (fs_frame_bytes CS_CID) with 256 in *; lia |];
              split; [ intros j Hj; rewrite (s1_rdword_kept (aview SEGS (w_H W1) mem1)); [apply HSAV; exact Hj |];
                intros i Hi; apply KEEP; lia |];
              split; [s1_regeq HSx ER 2%nat (2%bv : bv 5) G2|]; split; [s1_regeq HSx ER 3%nat (3%bv : bv 5) G3|];
              split; [s1_regeq HSx ER 4%nat (4%bv : bv 5) G4|]; split; [s1_regeq HSx ER 8%nat (8%bv : bv 5) G8|];
              split; [s1_regeq HSx ER 18%nat (18%bv : bv 5) G18|]; split; [s1_regeq HSx ER 25%nat (25%bv : bv 5) G25|];
              split; [s1_regeq HSx ER 26%nat (26%bv : bv 5) G26|]; s1_regeq HSx ER 27%nat (27%bv : bv 5) G27
            | split; [s1_regeq HSx ER 19%nat (19%bv : bv 5) R19|]; split; [s1_regeq HSx ER 20%nat (20%bv : bv 5) R20|];
              split; [s1_reglit HSx (21%bv : bv 5) SK3|]; split; [s1_reglit HSx (24%bv : bv 5) SK5|];
              split; [s1_regoff HSx ER G26 (22%bv : bv 5)|]; split; [s1_regoff HSx ER G26 (23%bv : bv 5)|];
              split; [s1_regeq HSx ER 5%nat (5%bv : bv 5) R5|]; s1_reg12 HSx SO U20 ] ]
        end ] ] ].
Qed.
End h.
End f.
End d.
Print Assumptions cs_S1.
