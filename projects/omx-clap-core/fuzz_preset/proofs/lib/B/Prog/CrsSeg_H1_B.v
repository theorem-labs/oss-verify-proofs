(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module names changed; 683 of its 755 lines of code are new or changed and 856 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): segment H1 of the walk of check_reject_clean_starved against the kit's
   text tcheck_reject_clean_starved_specX, row H1_B (a Theorem Labs lane's internal file BRIEF-crcs-Bprime-seg.md; lane CrsX1H1,
   a working branch). It proves exactly the row's closing lemma
     crs_seg_H1_B : LAWS -> crs_from_X1_B .. -> crs_from_R_B .. -> crs_from_W1_B .. -> crs_from_H1_B ..
   over the FROZEN B' kit lib/B/Prog/CrsKitBp.v (a working branch a179cedc95a7, blob 1dd89c0383ac).
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that lookup;
   CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its released rows
   were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). This file is one SEGMENT of that walk (kind: segment lemma); it is new.
   DONOR (rule 24, reuse): this lane's A' file lib/A/Prog/CrsSeg_H1.v (a working branch 5a39b8409c94): the
   same step kit, loop invariant and closing proof, with the kit's `_B` names and every number re-read at B'.
   INPUTS.
   - Pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (a Theorem Labs lane's listings v3).
     Entry 0x820e0 = slot 645 (B_entry_check_reject_clean_starved). H1 is slots 719 .. 748 and the one slot 763 (X1's
     last instruction, `beqz s3`, which H1's took = 0 arm runs); the loop's UBSan arms go to slot 929 (+1136, `unimp`).
    - The text tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v blob 9ecd8eb167c6
      (as in the kit preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record)).
   THE SEGMENT (offsets from the entry, each read off the B' listing by vm_compute in the step that uses it):
     +296 mv s6, a0 (a0 = fuzz_alloc_live () = lsum Lam); +300 beqz s7 (took = 0) -> +472;
     +304 lui a0, 1; +308 addiw a1, a0, 1285 (a1 = 5381, djb2's seed); +312 beqz s4 (size = 0) -> +416 = X1;
     +316 sltu a2, zero, s5 (a2 = 1: data <> 0); +320 .. +328 a3 = a0 = data, a4 = size; the loop L1 +332 .. +396, one
     byte per iteration: the UBSan pointer-overflow checks `bltu a0, s5` (+332), `sltiu a5, a0, 1; xor a5, a2, a5;
     beqz a5` (+336 .. +344) and `beqz s5` (+348), each to the trap +1136; the shadow byte of a0 by `srli; add s11; lb`
     (+352 .. +360), `bnez` (+364) -> +404 slow path `andi a6, a0, 7; blt a6, a5` (+404 / +408) -> +368 or the report
     arm +412; then a1 = 33 a1 + byte, a4 -= 1, a0 += 1, a3 += 1, `bnez a4` (+396) -> +332; +400 `j` -> +416 = X1.
     took = 0 arm: +472 beqz s3 (doc = 0) -> +736 = R, else +476 = W1.
   Every instruction is stepped by hand on the concrete machine state (RiscvSemantics.step, the listing's slot word
   and its decoding by vm_compute on a closed term): memory is only READ, so the memory and the world stay the
   boundary's own, and only the model is materialised (ajournal_x_materialize keeps crs_J_B).
   THE LOOP cites PRW_CrcGen.djb_loop (a Theorem Labs lane) with this file's one-iteration step h1_iter (hash a1, count a4,
   cursors a0 / a3); the hash update is PRW_CrcGen.djb_hash_step. THE THREE UBSan ARMS ARE UNREACHABLE: a0 = data + i
   with 0 < data and data + size < 2 ^ 62 (crs_pre_B), so `bltu a0, s5` is false, a5 = (a0 == 0) = 0 and a2 xor a5 = 1,
   and s5 = data <> 0; the loop invariant carries a2 = 1 (h1_keep). THE REPORT ARM (+412, `jal __asan_report_load1`,
   the first of pi_err_sites) IS UNREACHABLE: the shadow byte s of the next byte satisfies saddr_ok by
   PRW_CrcGen.djb_byte_shadow over crs_dat_B's range_addressable (s = 0 takes the fast path; 0 < s < 8 with
   (data + i) mod 8 < s takes `blt` back to +368). took < 2 ^ 64 (the `beqz s7` test) is PjGrammar.G7_4 (the reading
   makes at most 2 len + 2 calls) with size <= 3 * 2 ^ 20 (crs_pre_B). NAMED PREMISES: LAWS (the engine's Section
   hypothesis) and the three continuations (H1 makes no call).
   THE STEP KIT (section d below: the hand steps over crs_cfg_B, the word arithmetic) is generic over the listing slot
   and is Required by CrsSeg_X1_B.v; it follows lane CnoA102fA's lib/A/Prog/Cno102A_FA.v cfa_step / cfa_hs_* (origin/
   a working branch 574c27759c8), restated over the kit's crs_cfg_B and PL_prog_B's slot table; h_sltu /
   h_sltiu / h_xor are the B'-only steps of the UBSan checks.
   Numerals: offsets +296 .. +1136 (LENGTH: 4 * slot); 5381, 33, 32, 8, 7, 3, 5, 1 (WORD: djb2's seed and multiplier,
   the shift amounts, the granule mask and the sltiu bound the listing's words carry); 2 ^ 20 .. 2 ^ 64 (LENGTH / WORD
   bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- the word arithmetic of the stretch (no state) ---- *)
Lemma hw_eq : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> w64 a = w64 b.
Proof.
intros a b H. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
exact H.
Qed.
Lemma hw_un : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. apply unsigned_lit_small. exact Ha. Qed.
Lemma hw_addi : forall a n, 0 <= a < 2 ^ 64 -> v_addi (w64 a) n = w64 (a + n).
Proof. intros a n Ha. unfold v_addi. rewrite hw_un by exact Ha. reflexivity. Qed.
Lemma hw_add : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_add (w64 a) (w64 b) = w64 (a + b).
Proof. intros a b Ha Hb. unfold v_add. rewrite !hw_un by assumption. reflexivity. Qed.
Lemma hw_add_m : forall a b, v_add (w64 a) (w64 b) = w64 (a + b).
Proof.
intros a b. unfold v_add, w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma hw_srli3 : forall a, 0 <= a < 2 ^ 64 -> v_srli (w64 a) 3 = w64 (a / 8).
Proof. intros a Ha. unfold v_srli. rewrite hw_un by exact Ha. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma hw_slli5 : forall a, 0 <= a < 2 ^ 64 -> v_slli (w64 a) 5 = w64 (32 * a).
Proof. intros a Ha. unfold v_slli. rewrite hw_un by exact Ha. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.
Lemma hw_andi7 : forall a, 0 <= a < 2 ^ 64 -> v_andi (w64 a) 7 = w64 (a mod 8).
Proof.
intros a Ha. unfold v_andi. rewrite hw_un by exact Ha.
replace (bv_wrap 64 7) with (Z.ones 3) by reflexivity. rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma hw_eqb : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (w64 a) (w64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !hw_un by assumption. reflexivity. Qed.
Lemma hw_lts : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> bv_lts (w64 a) (w64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold bv_lts, bv_signed. rewrite !hw_un by lia.
rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn [Z.of_N]; lia). reflexivity.
Qed.
Lemma hw_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (w64 a) (w64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !hw_un by assumption. reflexivity. Qed.
Lemma hw_sltu0 : forall b, 0 < b < 2 ^ 64 -> v_sltu (w64 0) (w64 b) = w64 1.
Proof.
intros b Hb. unfold v_sltu, c_ltu. rewrite ?hw_un by lia.
try (unfold bv_ltu; rewrite !hw_un by lia).
replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma hw_sltiu1 : forall a, 0 < a < 2 ^ 64 -> v_sltiu (w64 a) 1 = w64 0.
Proof.
intros a Ha. unfold v_sltiu. rewrite hw_un by lia. change (bv_wrap 64 1) with 1.
replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma hw_xor10 : v_xor (w64 1) (w64 0) = w64 1.
Proof. reflexivity. Qed.
Lemma hw_lb : forall (b : byte), 0 <= bv_unsigned b < 128 -> v_lb b = w64 (bv_unsigned b).
Proof.
intros b Hb. unfold v_lb, w64, bv_signed. f_equal.
apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma hw_lbu : forall (b : byte), Z_to_bv 64 (bv_unsigned b) = w64 (bv_unsigned b).
Proof. reflexivity. Qed.

(* the bytes a reader of an image's view returns are bytes (lib/A/Prog/PRW_WalkEnv.v s10_aview_byte, over any segment
   list; that file is not on the B' base, so restated here) *)
Lemma h_aview_byte : forall (sg : list Segment) (H : word -> bool) mem x v, aview sg H mem x = Some v -> 0 <= v < 256.
Proof.
intros sg H mem x v E. unfold aview in E.
destruct (YP09.mbyte sg (mrestrict H mem) x) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
(* a byte the ASan view shows is a byte rdn reads *)
Lemma h_rdn1 : forall segs (H : word -> bool) (m : word -> option byte) a s,
  aview segs H m a = Some s -> exists b, rdn segs (mrestrict H m) (Z_to_bv 64 a) 1 = Some [b] /\ bv_unsigned b = s.
Proof.
intros segs H m a s E. unfold aview in E.
destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. exists b. split; [|reflexivity].
cbn [rdn]. unfold YP09.mbyte in Eb. rewrite Eb. reflexivity.
Qed.
Lemma h_rdn1_mb : forall segs (m : word -> option byte) a b,
  YP09.mbyte segs m a = Some b -> rdn segs m (Z_to_bv 64 a) 1 = Some [b].
Proof. intros segs m a b E. cbn [rdn]. unfold YP09.mbyte in E. rewrite E. reflexivity. Qed.

(* registers *)
Lemma h_getr_same : forall regs (r : bv 5) v, bv_eqb r 0%bv = false -> getr (regupd regs r v) r = v.
Proof. intros regs r v H. apply getr_same. intros E. subst r. discriminate H. Qed.
Lemma h_getr_other : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. apply getr_other. intros E. subst r'. rewrite bv_eqb_refl in H. discriminate H. Qed.
Lemma h_getr_eq : forall regs (r r' : bv 5) v, bv_eqb r' r = true -> bv_eqb r 0%bv = false ->
  getr (regupd regs r v) r' = v.
Proof.
intros regs r r' v H H0. assert (E : r' = r) by (apply bv_eq; unfold bv_eqb in H; apply Z.eqb_eq in H; exact H).
subst r'. exact (h_getr_same regs r v H0).
Qed.
Ltac hgetr := repeat first [rewrite h_getr_eq by reflexivity | rewrite h_getr_other by reflexivity].
Lemma h_vaddi0 : forall (x : word), v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* the decoder's register records (an opaque well-formedness proof) to the kit's numerals (proof I) *)
Ltac hcanon :=
  repeat match goal with
  | |- context [@BV ?w ?n ?p] =>
      lazymatch p with
      | I => fail
      | _ => lazymatch eval vm_compute in w with
             | 5%N => let n' := eval vm_compute in n in
                      progress (replace (@BV w n p) with (@BV w n' I) by (apply bv_eq; reflexivity))
             end
      end
  end.
(* the immediates of closed instruction records to their values *)
Ltac hsig :=
  repeat match goal with
  | |- context [bv_signed (@BV ?w ?n ?p)] =>
      let v := eval vm_compute in (bv_signed (@BV w n p)) in progress change (bv_signed (@BV w n p)) with v
  | |- context [bv_unsigned (@BV ?w ?n ?p)] =>
      let v := eval vm_compute in (bv_unsigned (@BV w n p)) in progress change (bv_unsigned (@BV w n p)) with v
  end.

Lemma h_regsat_get : forall regs l (r : bv 5) v, crs_regsat_B regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma h_regsat_upd : forall regs l (r : bv 5) w, Forall (fun p : bv 5 * Z => bv_eqb (fst p) r = false) l ->
  crs_regsat_B regs l -> crs_regsat_B (regupd regs r w) l.
Proof.
intros regs l r w Hn H. unfold crs_regsat_B in *. rewrite Forall_forall in *. intros p Hp.
rewrite h_getr_other by exact (Hn p Hp). exact (H p Hp).
Qed.
Lemma h_regsat_app : forall regs l1 l2, crs_regsat_B regs l1 -> crs_regsat_B regs l2 -> crs_regsat_B regs (l1 ++ l2).
Proof. intros regs l1 l2 H1 H2. unfold crs_regsat_B in *. apply Forall_app. split; assumption. Qed.
Lemma h_regsat_incl : forall regs l l', crs_regsat_B regs l -> incl l' l -> crs_regsat_B regs l'.
Proof.
intros regs l l' H Hi. unfold crs_regsat_B in *. apply Forall_forall. intros p Hp.
exact (proj1 (Forall_forall _ _) H p (Hi p Hp)).
Qed.
Ltac hin := cbn [app In]; repeat (first [left; reflexivity | right]).
Ltac hnot := cbn [app]; repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil.

(* ======================================================================================================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* ---- the hand steps over crs_cfg_B (Cno102A_FA.v cfa_step / cfa_hs_*, at the kit's configuration) ---- *)
Lemma h_base : 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64.
Proof. pose proof (@pa_B_ok _ _ PA) as (H0 & H1 & _). split; assumption. Qed.
Lemma h_pc0 : 0 <= CRS_PC0_B < 2 ^ 20.
Proof.
assert (E : CRS_PC0_B = ltac:(let v := eval vm_compute in CRS_PC0_B in exact v)) by (vm_compute; reflexivity).
rewrite E. lia.
Qed.
Lemma h_pcn : forall k n, 0 <= k < 2 ^ 30 -> 0 <= k + n < 2 ^ 30 ->
  v_addi (Z_to_bv 64 (BASE + k)) n = Z_to_bv 64 (BASE + (k + n)).
Proof.
intros k n Hk Hn. pose proof h_base as HB. unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma h_step : forall (W : world SEGS) fxk regs mem md regs' pc pc' Q,
  RiscvSemantics.step SEGS (@YK11.mkst fxk regs (Z_to_bv 64 pc) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxk regs' (Z_to_bv 64 pc') (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall X, SRr SEGS W (crs_cfg_B fxk pc' regs' mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk pc regs mem md) Q.
Proof.
intros W fxk regs mem md regs' pc pc' Q Hst HK. unfold crs_cfg_B, w64.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk); exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold crs_cfg_B, w64 in HK. exact HK.
Qed.

Definition HSLOT (k : Z) : option (pinstr asym) := YP0a.plookup B_prog_tpi k.
Lemma h_fetch : forall k w, HSLOT k = Some (PW w) -> fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof. intros k w H. exact (@pa_fetch_pw rc _ PL_prog_B PA k w H). Qed.

Lemma h_addi : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_addi fxk SEGS regs _ _ _ _ rd rs imm (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_lui : forall (W : world SEGS) fxk regs mem md Q k k' w rd imm v,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Lui rd imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> v_lui (bv_signed imm ≪ 12) = v -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd v) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd imm v Hl Hd Hrd Hv Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd v) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_lui_at fxk SEGS regs _ _ _ _ rd imm v (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
rewrite (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_addiw : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm v,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (OpImm32 rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> v_addiw (getr regs rs) (bv_signed imm) = v -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd v) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm v Hl Hd Hrd Hv Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd v) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_addiw_at fxk SEGS regs _ _ _ _ rd rs imm v (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
rewrite (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_srli : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs sh,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs sh Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_srli fxk SEGS regs _ _ _ _ rd rs sh (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_slli : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs sh,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs sh Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_slli fxk SEGS regs _ _ _ _ rd rs sh (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_add : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs1 rs2,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs1 rs2 Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_add fxk SEGS regs _ _ _ _ rd rs1 rs2 (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_andi : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_andi (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_andi (getr regs rs) (bv_signed imm))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_andi fxk SEGS regs _ _ _ _ rd rs imm (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_lb : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm b,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Load SZ1 true rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_lb b)) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm b Hl Hd Hrd Hk -> Hr HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_lb b)) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_lb fxk SEGS regs _ _ _ _ rd rs imm b (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hr).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_lbu : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm b,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm b Hl Hd Hrd Hk -> Hr HK.
apply (h_step W fxk regs mem md (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_lbu fxk SEGS regs _ _ _ _ rd rs imm b (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hr).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_br : forall (W : world SEGS) fxk regs mem md Q k kt kf w c rs1 rs2 imm,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  0 <= k < 2 ^ 29 -> kt = k + bv_signed imm -> 0 <= kt < 2 ^ 29 -> kf = k + 4 ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = true ->
   forall X, SRr SEGS W (crs_cfg_B fxk (BASE + kt) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = false ->
   forall X, SRr SEGS W (crs_cfg_B fxk (BASE + kf) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k kt kf w c rs1 rs2 imm Hl Hd Hk -> Hkt -> HT HF.
destruct (branch_taken c (getr regs rs1) (getr regs rs2)) eqn:Hb.
- apply (h_step W fxk regs mem md regs (BASE + k) (BASE + (k + bv_signed imm)) Q); [|exact (HT eq_refl)].
  rewrite (@step_branch_tk_gen fxk SEGS regs _ _ _ _ c rs1 rs2 imm (h_fetch k w Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hb).
  unfold btgt. rewrite (h_pcn k (bv_signed imm)) by lia. reflexivity.
- apply (h_step W fxk regs mem md regs (BASE + k) (BASE + (k + 4)) Q); [|exact (HF eq_refl)].
  rewrite (@step_branch_ft_gen fxk SEGS regs _ _ _ _ c rs1 rs2 imm (h_fetch k w Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hb).
  rewrite (h_pcn k 4) by lia. reflexivity.
Qed.

(* `j off` (jal x0) *)
Lemma h_j : forall (W : world SEGS) fxk regs mem md Q k kt w rd imm,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Jal rd imm, 4%Z) -> bv_eqb rd 0%bv = true ->
  0 <= k < 2 ^ 29 -> kt = k + bv_signed imm -> 0 <= kt < 2 ^ 29 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + kt) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k kt w rd imm Hl Hd Hrd Hk -> Hkt HK.
apply (h_step W fxk regs mem md regs (BASE + k) (BASE + (k + bv_signed imm)) Q); [|exact HK].
rewrite (@step_jal_link fxk SEGS regs _ _ _ _ rd imm (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd. unfold btgt. rewrite (h_pcn k (bv_signed imm)) by lia. reflexivity.
Qed.

Lemma h_sltu : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs1 rs2,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs1 rs2 Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_sltu fxk SEGS regs _ _ _ _ rd rs1 rs2 (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_sltiu : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_sltiu (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_sltiu (getr regs rs) (bv_signed imm))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_sltiu fxk SEGS regs _ _ _ _ rd rs imm (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_xor : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs1 rs2,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Op ALU_XOR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs1 rs2 Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_xor fxk SEGS regs _ _ _ _ rd rs1 rs2 (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

(* the slot word at k and its decoding, each by vm_compute on a closed term *)
Ltac hfd k Hl Hd :=
  let r := eval vm_compute in (HSLOT k) in
  lazymatch r with
  | Some (PW ?w) =>
      assert (Hl : HSLOT k = Some (PW w)) by (vm_compute; reflexivity);
      let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
      assert (Hd : decode_any (Z_to_bv 32 w) = d) by (vm_compute; reflexivity)
  end.
(* close the side conditions of a hand step: closed register tests, offsets *)
Ltac hside := first [ reflexivity | (pose proof h_pc0; lia) | (vm_compute; reflexivity) ].

(* ======================================================================================================== *)
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation BASEp CTX0 C := (@crs_base_B fx rc ci cp RL SK B ARx CTX0 C).

(* crs_base_B at the next register file and the materialised model, when gp and tp are kept *)
Lemma h_base_step : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X,
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  getr regs' 3%bv = getr regs3 3%bv -> getr regs' 4%bv = getr regs3 4%bv ->
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs' mem3 (with_vm_backing (m_vm_lazy md3) X md3) k sp2.
Proof.
intros CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X HB E3 E4.
destruct HB as (HP & Hz & Hk & HJ & HF & HSV & HSL & HRO & HMN & R3 & R4 & Hsp).
split; [exact HP|]. split; [exact Hz|]. split; [exact Hk|].
split; [unfold crs_J_B in *; exact (ajournal_x_materialize SEGS B prh_pst ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ)|].
split; [exact HF|]. split; [exact HSV|]. split; [exact HSL|]. split; [exact HRO|]. split; [exact HMN|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact Hsp.
Qed.

(* the facts of crs_pre_B the stretch uses *)
Lemma h_pre_facts : forall CTX0 C, crs_pre_B (fx := fx) B ARx CTX0 C ->
  cSize_B C <= 3 * 2 ^ 20 /\ 0 < cb_data C /\ cb_data C + cSize_B C < 2 ^ 62 /\ 0 <= cb_took C <= 2 * cSize_B C + 2 /\
  cb_ran C = 0.
Proof.
intros CTX0 C H. unfold crs_pre_B in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _ & _ & H4 & _ & _ & _ & _ & Hran & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact Hran].
split; [lia|]. apply (Z.le_trans _ _ _ (proj2 H4)). unfold ck_ncalls, cSize_B.
pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod (cb_tb C) []) as G. unfold PjGrammar.ncalls. lia.
Qed.

(* ---- the loop L1 (B' +332 .. +396): its head invariant J (the world and memory the boundary's, crs_base_B at the
   current register file and model, the registers the loop keeps: the boundary's, s6, s7, and a2 = 1, the
   `sltu a2, zero, s5` of +316 the UBSan check at +340 reads) and its one-iteration step ---- *)
Definition h1_keep0 (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ [(23%bv, cb_took C)].
Definition h1_keep (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) := h1_keep0 C sp2 ++ [(12%bv, 1)].
Definition h1_J (CTX0 : list (list Z)) (C : crsC_B) (fxk : YK11.FPState) (ly3 : alayout) (S3 : astate)
  (Hp3 : list Z) (W3 : world SEGS) (mem3 : word -> option byte) (k sp2 : Z)
  : world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun W regs mem md => W = W3 /\ mem = mem3 /\ BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs mem3 md k sp2 /\
    crs_regsat_B regs (h1_keep C sp2).

#[local] Ltac hb_upd HB :=
  lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ (with_vm_backing (m_vm_lazy ?m) ?X ?m)) _ =>
    let H' := fresh "HB'" in
    pose proof (h_base_step _ _ _ _ _ _ _ _ r _ _ _ _ X HB ltac:(hgetr; reflexivity) ltac:(hgetr; reflexivity)) as H';
    clear HB; rename H' into HB end.
#[local] Ltac hrs_upd HR :=
  lazymatch goal with
  | |- SRr _ _ (crs_cfg_B _ _ (regupd ?rg ?rr ?v) _ _) _ =>
    let l := lazymatch type of HR with crs_regsat_B _ ?l => l end in
    let H' := fresh "HR'" in
    pose proof (h_regsat_upd rg l rr v
      ltac:(unfold h1_keep, h1_keep0, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hnot) HR) as H';
    clear HR; rename H' into HR
  | _ => idtac end.
#[local] Ltac hpost := intros; hcanon; hsig; rewrite ?h_vaddi0; hgetr.
#[local] Ltac hz := rewrite ?getr_zero; change (Z_to_bv 64 0) with (w64 0).

Lemma h1_iter : forall CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2 i W c,
  (i < length (cb_tb C))%nat ->
  djb_head (fx := fxk) SEGS (BASE + (CRS_PC0_B + 332)) 11%bv 14%bv [10%bv; 13%bv] (cb_data C) (cb_tb C)
    (h1_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) i W c ->
  SRr SEGS W c (djb_head (fx := fxk) SEGS
    (if (S i <? length (cb_tb C))%nat then BASE + (CRS_PC0_B + 332) else BASE + (CRS_PC0_B + 416))
    11%bv 14%bv [10%bv; 13%bv] (cb_data C) (cb_tb C) (h1_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) (S i)).
Proof.
intros CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2 i W c Hi (regs & mem & md & -> & Hle & Hh & Hc & Hps & Hg & Hra & HJ).
destruct HJ as (-> & -> & HBs & HRs).
pose proof h_pc0 as HPC.
pose proof (Forall_inv Hps) as Ha0. pose proof (Forall_inv (Forall_inv_tail Hps)) as Ha3. cbv beta in Ha0, Ha3.
pose proof (h_pre_facts CTX0 C (proj1 HBs)) as (Hsz & Hd0 & Hd62 & _ & _).
unfold cSize_B in Hsz, Hd62.
set (x := cb_tb C) in *. set (d := cb_data C) in *.
set (n := Z.of_nat (length x)) in *.
set (h := ck_djb2 5381 (firstn i x)) in *.
assert (Hhr : 0 <= h < 2 ^ 64) by apply djb_hash_range.
assert (G27 : getr regs 27%bv = w64 SHADOW_OFF)
  by (apply (h_regsat_get regs (h1_keep C sp2)); [exact HRs | unfold h1_keep, h1_keep0, crs_rbase_B; hin]).
assert (G21 : getr regs 21%bv = w64 d)
  by (apply (h_regsat_get regs (h1_keep C sp2)); [exact HRs | unfold h1_keep, h1_keep0, crs_rbase_B, crs_rsh_B, crs_rargs_B; hin]).
assert (G12 : getr regs 12%bv = w64 1)
  by (apply (h_regsat_get regs (h1_keep C sp2)); [exact HRs | unfold h1_keep, h1_keep0, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hin]).
(* the shadow byte of the next byte, and the byte *)
destruct (djb_byte_shadow _ _ d n (Z.of_nat i) Hra ltac:(lia)) as (s & Hs & Hsok).
pose proof (h_aview_byte _ _ _ _ _ Hs) as Hs256.
destruct (h_rdn1 SEGS (w_H W3) mem3 _ s Hs) as (bs & Hrbs & Hbs).
destruct (djb_byte SEGS (mrestrict (w_H W3) mem3) d x i Hg Hi) as (Hmb & Hc256).
pose proof (h_rdn1_mb SEGS _ _ _ Hmb) as Hrc.
set (cc := nth i x 0) in *.
assert (Hs8 : s = 0 \/ (0 < s < 8 /\ (d + Z.of_nat i) mod 8 < s)) by (unfold saddr_ok in Hsok; lia).
change (cfg_at (fx := fxk) SEGS (BASE + (CRS_PC0_B + 332)) regs mem3 md)
  with (crs_cfg_B fxk (BASE + (CRS_PC0_B + 332)) regs mem3 md).
(* +332 bltu a0, s5 -> the UBSan trap +1136: refuted (a0 = data + i >= data) *)
hfd (CRS_PC0_B + 332) Hl Hd.
eapply (h_br W3 fxk regs mem3 md _ (CRS_PC0_B + 332) (CRS_PC0_B + 1136) (CRS_PC0_B + 336) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
{ intros Hb ?. exfalso. revert Hb. hcanon. rewrite Ha0, G21. cbn [branch_taken]. rewrite hw_ltu by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. discriminate. }
intros _ ?. hcanon. hb_upd HBs.
(* +336 sltiu a5, a0, 1: a5 = 0 (a0 <> 0) *)
clear Hl Hd. hfd (CRS_PC0_B + 336) Hl Hd.
eapply (h_sltiu W3 fxk _ mem3 _ _ (CRS_PC0_B + 336) (CRS_PC0_B + 340) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite Ha0, hw_sltiu1 by lia. hb_upd HBs. hrs_upd HRs.
(* +340 xor a5, a2, a5: a5 = 1 *)
clear Hl Hd. hfd (CRS_PC0_B + 340) Hl Hd.
eapply (h_xor W3 fxk _ mem3 _ _ (CRS_PC0_B + 340) (CRS_PC0_B + 344) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G12, hw_xor10. hb_upd HBs. hrs_upd HRs.
(* +344 beqz a5 -> +1136: refuted (a5 = 1) *)
clear Hl Hd. hfd (CRS_PC0_B + 344) Hl Hd.
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 344) (CRS_PC0_B + 1136) (CRS_PC0_B + 348) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
{ intros Hb ?. exfalso. revert Hb. hcanon. hgetr. hz. cbn [branch_taken]. rewrite hw_eqb by lia. discriminate. }
intros _ ?. hcanon. hb_upd HBs.
(* +348 beqz s5 -> +1136: refuted (data > 0) *)
clear Hl Hd. hfd (CRS_PC0_B + 348) Hl Hd.
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 348) (CRS_PC0_B + 1136) (CRS_PC0_B + 352) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
{ intros Hb ?. exfalso. revert Hb. hcanon. hgetr. hz. rewrite G21. cbn [branch_taken]. rewrite hw_eqb by lia.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate. }
intros _ ?. hcanon. hb_upd HBs.
(* +352 srli a5, a0, 3 *)
clear Hl Hd. hfd (CRS_PC0_B + 352) Hl Hd.
eapply (h_srli W3 fxk _ mem3 _ _ (CRS_PC0_B + 352) (CRS_PC0_B + 356) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite Ha0, hw_srli3 by lia. hb_upd HBs. hrs_upd HRs.
(* +356 add a5, a5, s11 *)
clear Hl Hd. hfd (CRS_PC0_B + 356) Hl Hd.
eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0_B + 356) (CRS_PC0_B + 360) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
assert (H8 : 0 <= (d + Z.of_nat i) / 8 < 2 ^ 64)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (HSO : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
hpost. rewrite G27. rewrite (hw_add _ _ H8 HSO).
hb_upd HBs. hrs_upd HRs.
(* +360 lb a5, 0(a5): the shadow byte s *)
clear Hl Hd. hfd (CRS_PC0_B + 360) Hl Hd.
eapply (h_lb W3 fxk _ mem3 _ _ (CRS_PC0_B + 360) (CRS_PC0_B + 364) _ _ _ _ bs Hl Hd); [reflexivity | lia | lia | |].
{ hcanon. hsig. hgetr. rewrite h_vaddi0.
  replace ((d + Z.of_nat i) / 8 + SHADOW_OFF) with (shadow_of_addr SHADOW_OFF (d + Z.of_nat i))
    by (unfold shadow_of_addr; lia).
  exact Hrbs. }
hpost. rewrite hw_lb by lia. rewrite Hbs. hb_upd HBs. hrs_upd HRs.
(* +364 bnez a5: s = 0 falls through to +368; else the slow path +404 *)
clear Hl Hd. hfd (CRS_PC0_B + 364) Hl Hd.
(* the common tail from +368 (both arms reach it) *)
assert (TAIL : forall regsT mdT,
  getr regsT 10%bv = w64 (d + Z.of_nat i) -> getr regsT 13%bv = w64 (d + Z.of_nat i) ->
  getr regsT 11%bv = w64 h -> getr regsT 14%bv = w64 (n - Z.of_nat i) ->
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regsT mem3 mdT k sp2 -> crs_regsat_B regsT (h1_keep C sp2) ->
  SRr SEGS W3 (crs_cfg_B fxk (BASE + (CRS_PC0_B + 368)) regsT mem3 mdT)
    (djb_head (fx := fxk) SEGS
      (if (S i <? length x)%nat then BASE + (CRS_PC0_B + 332) else BASE + (CRS_PC0_B + 416))
      11%bv 14%bv [10%bv; 13%bv] d x (h1_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) (S i))).
{ clear dependent regs. intros regsT mdT T10 T13 T11 T14 HBt HRt.
  (* +368 slli a5, a1, 5 *)
  clear Hl Hd. hfd (CRS_PC0_B + 368) Hl Hd.
  eapply (h_slli W3 fxk regsT mem3 mdT _ (CRS_PC0_B + 368) (CRS_PC0_B + 372) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T11, hw_slli5 by lia. hb_upd HBt. hrs_upd HRt.
  (* +372 lbu a6, 0(a3) *)
  clear Hl Hd. hfd (CRS_PC0_B + 372) Hl Hd.
  eapply (h_lbu W3 fxk _ mem3 _ _ (CRS_PC0_B + 372) (CRS_PC0_B + 376) _ _ _ _ (Z_to_bv 8 cc) Hl Hd);
    [reflexivity | lia | lia | |].
  { hcanon. hsig. hgetr. rewrite T13, h_vaddi0. exact Hrc. }
  hpost. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia).
  change (Z_to_bv 64 cc) with (w64 cc). hb_upd HBt. hrs_upd HRt.
  (* +376 add a1, a5, a1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 376) Hl Hd.
  eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0_B + 376) (CRS_PC0_B + 380) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T11, hw_add_m. hb_upd HBt. hrs_upd HRt.
  (* +380 addi a4, a4, -1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 380) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 380) (CRS_PC0_B + 384) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T14, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* +384 addi a0, a0, 1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 384) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 384) (CRS_PC0_B + 388) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T10, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* +388 add a1, a1, a6 *)
  clear Hl Hd. hfd (CRS_PC0_B + 388) Hl Hd.
  eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0_B + 388) (CRS_PC0_B + 392) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite hw_add_m. hb_upd HBt. hrs_upd HRt.
  (* +392 addi a3, a3, 1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 392) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 392) (CRS_PC0_B + 396) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T13, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* the head facts at S i *)
  assert (Eh : w64 (32 * h + h + cc) = w64 (ck_djb2 5381 (firstn (S i) x))).
  { apply hw_eq. rewrite (djb_hash_step x i Hi). fold h. fold cc. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Eh. rewrite Eh in HRt.
  (* +396 bnez a4 -> +332 *)
  clear Hl Hd. hfd (CRS_PC0_B + 396) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 396) (CRS_PC0_B + 332) (CRS_PC0_B + 400) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  - (* taken: a4 <> 0, bytes remain, back to the head *)
    intros Hb ?. revert Hb. hcanon. hgetr. hz.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply negb_true_iff, Z.eqb_neq in Hb.
    assert (Hlt : (S i < length x)%nat) by lia.
    rewrite (proj2 (Nat.ltb_lt _ _) Hlt).
    hb_upd HBt. apply SRr_ret.
    lazymatch goal with HBt : BASEp _ _ _ _ _ _ _ ?rr _ ?mm _ _ |- _ =>
      exists rr, mem3, mm end.
    split; [reflexivity|]. split; [lia|].
    split; [hgetr; reflexivity|]. split; [hgetr; unfold n in *; f_equal; lia|].
    split; [apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_nil|].
    split; [exact Hg|]. split; [exact Hra|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HBt|]. exact HRt.
  - (* not taken: the last byte; +400 j -> +416 *)
    intros Hb ?. revert Hb. hcanon. hgetr. hz.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply negb_false_iff, Z.eqb_eq in Hb.
    assert (Hge : length x = S i) by (unfold n in *; lia).
    rewrite Hge, Nat.ltb_irrefl.
    hb_upd HBt.
    clear Hl Hd. hfd (CRS_PC0_B + 400) Hl Hd.
    eapply (h_j W3 fxk _ mem3 _ _ (CRS_PC0_B + 400) (CRS_PC0_B + 416) _ _ _ Hl Hd); [reflexivity | lia | reflexivity | lia |].
    intros ?. hb_upd HBt. apply SRr_ret.
    lazymatch goal with HBt : BASEp _ _ _ _ _ _ _ ?rr _ ?mm _ _ |- _ =>
      exists rr, mem3, mm end.
    split; [reflexivity|]. split; [lia|].
    split; [hgetr; reflexivity|]. split; [hgetr; f_equal; unfold n in *; lia|].
    split; [apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_nil|].
    split; [exact Hg|]. split; [exact Hra|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HBt|]. exact HRt. }
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 364) (CRS_PC0_B + 404) (CRS_PC0_B + 368) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
- (* taken: s <> 0, the slow path *)
  intros Hb ?. revert Hb. hcanon. hgetr. hz.
  cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply negb_true_iff, Z.eqb_neq in Hb.
  destruct Hs8 as [Hs0 | (Hs08 & Hsm)]; [exfalso; exact (Hb Hs0)|].
  hb_upd HBs.
  (* +404 andi a6, a0, 7 *)
  clear Hl Hd. hfd (CRS_PC0_B + 404) Hl Hd.
  eapply (h_andi W3 fxk _ mem3 _ _ (CRS_PC0_B + 404) (CRS_PC0_B + 408) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite Ha0, hw_andi7 by lia. hb_upd HBs. hrs_upd HRs.
  (* +408 blt a6, a5: taken (the byte is inside the granule's valid prefix) -> +368; the report arm +412 refuted *)
  clear Hl Hd. hfd (CRS_PC0_B + 408) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 408) (CRS_PC0_B + 368) (CRS_PC0_B + 412) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  + intros _ ?. hcanon. hb_upd HBs.
    apply TAIL; [hgetr; exact Ha0 | hgetr; exact Ha3 | hgetr; exact Hh | hgetr; exact Hc | exact HBs | exact HRs].
  + intros Hb2 ?. exfalso. revert Hb2. hcanon. hgetr. cbn [branch_taken].
    rewrite hw_lts by (pose proof (Z.mod_pos_bound (d + Z.of_nat i) 8); lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hsm). discriminate.
- (* not taken: s = 0, the fast path *)
  intros Hb ?. hcanon. hb_upd HBs.
  apply TAIL; [hgetr; exact Ha0 | hgetr; exact Ha3 | hgetr; exact Hh | hgetr; exact Hc | exact HBs | exact HRs].
Qed.

(* doc is a word: NULL, or a 56-byte object inside a fake frame of the entry (ck_obj_home), below alloc_ceiling *)
Lemma h_doc_range : forall CTX0 C, crs_pre_B (fx := fx) B ARx CTX0 C -> 0 <= cb_doc C < 2 ^ 64.
Proof.
intros CTX0 C H. pose proof H as H'. unfold crs_pre_B in H'.
destruct H' as (HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdoc & _).
destruct Hdoc as [-> | (_ & (_ & _ & _ & (_ & (cid & pos & Hin & Hlo & Hhi) & _)) & _)]; [lia|].
destruct HF as ((HAR & _) & _).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (H4096 & Hceil & _).
pose proof asan_consts as (C1 & _). lia.
Qed.

(* the boundary register lists, from the loop's kept list *)
Lemma h_regsat_x1 : forall regs C sp2, crs_regsat_B regs (h1_keep0 C sp2) -> getr regs 11%bv = w64 (cHash_B C) ->
  crs_regsat_B regs (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ [(23%bv, cb_took C); (11%bv, cHash_B C)]).
Proof.
intros regs C sp2 H H11. unfold crs_regsat_B, h1_keep0 in *. rewrite !Forall_app in *.
destruct H as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
constructor; [exact (Forall_inv H5)|]. constructor; [exact H11|]. constructor.
Qed.
Lemma h_regsat_w1 : forall regs C sp2, crs_regsat_B regs (h1_keep0 C sp2) ->
  crs_regsat_B regs (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C).
Proof.
intros regs C sp2 H. apply (h_regsat_incl regs (h1_keep0 C sp2)); [exact H|].
intros p Hp. unfold h1_keep0. rewrite !in_app_iff in *. tauto.
Qed.
Lemma h_keep_keep0 : forall regs C sp2, crs_regsat_B regs (h1_keep C sp2) -> crs_regsat_B regs (h1_keep0 C sp2).
Proof.
intros regs C sp2 H. apply (h_regsat_incl regs (h1_keep C sp2)); [exact H|].
intros p Hp. unfold h1_keep. apply in_or_app. left. exact Hp.
Qed.
Lemma h_regsat_r : forall regs C sp2, crs_regsat_B regs (h1_keep0 C sp2) -> crs_regsat_B regs (crs_rbase_B C sp2 ++ crs_rsh_B C).
Proof.
intros regs C sp2 H. apply (h_regsat_incl regs (h1_keep0 C sp2)); [exact H|].
intros p Hp. unfold h1_keep0. rewrite !in_app_iff in *. tauto.
Qed.

(* ==== CR-H1_B: the closing lemma ==== *)
Lemma crs_seg_H1_B : forall CTX0 C,
  @crs_from_X1_B fx rc ci cp RL SK B ARx CTX0 C ->
  @crs_from_R_B fx rc ci cp RL SK B ARx CTX0 C ->
  @crs_from_W1_B fx rc ci cp RL SK B ARx CTX0 C ->
  @crs_from_H1_B fx rc ci cp RL SK B ARx CTX0 C.
Proof.
intros CTX0 C HX1 HR HW1. unfold crs_from_H1_B.
intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Hws HB HRS HL HD HT.
(* the hand steps stay plain: one lift into the re-hiding relation here, SRr_ret before each exit *)
apply YGcfRhLift.ra_rh_of_SRr.
pose proof h_pc0 as HPC.
pose proof (h_pre_facts CTX0 C (proj1 HB)) as (Hsz & Hd0 & Hd62 & Htook & Hran).
pose proof (h_doc_range CTX0 C (proj1 HB)) as Hdoc.
unfold cSize_B in Hsz, Hd62, Htook.
assert (G10 : getr regs3 10%bv = w64 (Ledger.lsum (cb_Lam C)))
  by (apply (h_regsat_get regs3 _ _ _ HRS); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B; hin).
assert (G23 : getr regs3 23%bv = w64 (cb_took C))
  by (apply (h_regsat_get regs3 _ _ _ HRS); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B; hin).
assert (G19 : getr regs3 19%bv = w64 (cb_doc C))
  by (apply (h_regsat_get regs3 _ _ _ HRS); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B; hin).
assert (G20 : getr regs3 20%bv = w64 (cSize_B C))
  by (apply (h_regsat_get regs3 _ _ _ HRS); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B; hin).
assert (G21 : getr regs3 21%bv = w64 (cb_data C))
  by (apply (h_regsat_get regs3 _ _ _ HRS); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B; hin).
unfold cSize_B in G20.
change (BASE + CRS_PC_H1_B) with (BASE + (CRS_PC0_B + 296)).
(* +296 mv s6, a0 *)
hfd (CRS_PC0_B + 296) Hl Hd.
eapply (h_addi W3 fxk regs3 mem3 md3 _ (CRS_PC0_B + 296) (CRS_PC0_B + 300) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G10. hb_upd HB.
lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ _) _ => assert (HK1 : crs_regsat_B r (h1_keep0 C sp2)) end.
{ unfold crs_regsat_B, h1_keep0, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd]; hgetr;
    first [reflexivity | apply (h_regsat_get regs3 _ _ _ HRS); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B; hin] |]).
  apply Forall_nil. }
(* +300 beqz s7: took = 0 -> +472 (X1's last instruction, beqz doc) *)
clear Hl Hd. hfd (CRS_PC0_B + 300) Hl Hd.
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 300) (CRS_PC0_B + 472) (CRS_PC0_B + 304) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
- intros Hb ?. revert Hb. hcanon. hgetr. hz. rewrite G23.
  cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply Z.eqb_eq in Hb.
  hb_upd HB.
  (* +472 beqz s3: doc = 0 -> R (+736), else W1 (+476) *)
  clear Hl Hd. hfd (CRS_PC0_B + 472) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 472) (CRS_PC0_B + 736) (CRS_PC0_B + 476) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. hz. rewrite G19.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_eq in Hb2.
    hb_upd HB. change (BASE + (CRS_PC0_B + 736)) with (BASE + CRS_PC_R_B).
    assert (Eev : crs_evs_at_R_B C = crs_evs_at_H1_B C).
    { unfold crs_evs_at_R_B. rewrite (crs_evs_doc0_B C Hb2). unfold crs_evs_at_W1_B, crs_ev_sp_B, crs_evs_at_H1_B.
      rewrite Hb. reflexivity. }
    rewrite <- Eev in HL.
    apply SRr_ret.
    refine (HR fxk ly3 S3 Hp3 W3 _ mem3 _ k sp2 (cb_Lam C) (cb_peak C) (cb_cnt C) (cb_ran C)
      (crs_baseR_B_mono B ARx (@wle SEGS) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
         (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 _ mem3 _ k sp2 HB)
      _ HL (proj1 HD) HT _).
    * exact (h_regsat_r _ C sp2 HK1).
    * unfold crs_cnt_end_B, ck_crcs_max, ck_crcs_growth. rewrite Hb, Hb2. cbn [Z.eqb]. lia.
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. hz. rewrite G19.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_neq in Hb2.
    hb_upd HB. change (BASE + (CRS_PC0_B + 476)) with (BASE + CRS_PC_W1_B).
    assert (Eev : crs_evs_at_W1_B C = crs_evs_at_H1_B C).
    { unfold crs_evs_at_W1_B, crs_ev_sp_B, crs_evs_at_H1_B. rewrite Hb. reflexivity. }
    rewrite <- Eev in HL.
    apply SRr_ret.
    refine (HW1 fxk ly3 S3 Hp3 W3 _ mem3 _ k sp2 (cb_Lam C) (cb_peak C) (cb_cnt C) (cb_ran C) Hb2
      (crs_baseR_B_mono B ARx (@wle SEGS) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
         (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly3 S3 Hp3 W3 _ mem3 _ k sp2 HB)
      _ HL HD HT _).
    * exact (h_regsat_w1 _ C sp2 HK1).
    * unfold crs_cnt_R_B. split; [intros _; reflexivity | intros Hne; exfalso; exact (Hne Hb)].
- intros Hb ?. revert Hb. hcanon. hgetr. hz. rewrite G23.
  cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply Z.eqb_neq in Hb.
  hb_upd HB.
  (* +304 lui a0, 1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 304) Hl Hd.
  eapply (h_lui W3 fxk _ mem3 _ _ (CRS_PC0_B + 304) (CRS_PC0_B + 308) _ _ _ (w64 4096) Hl Hd);
    [reflexivity | apply bv_eq; vm_compute; reflexivity | lia | lia |].
  hpost. hb_upd HB.
  (* +308 addiw a1, a0, 1285: a1 = 5381 *)
  clear Hl Hd. hfd (CRS_PC0_B + 308) Hl Hd.
  eapply (h_addiw W3 fxk _ mem3 _ _ (CRS_PC0_B + 308) (CRS_PC0_B + 312) _ _ _ _ (w64 5381) Hl Hd);
    [reflexivity | hcanon; hgetr; apply bv_eq; vm_compute; reflexivity | lia | lia |].
  hpost. hb_upd HB.
  (* +312 beqz s4: size = 0 -> X1 (+416) *)
  clear Hl Hd. hfd (CRS_PC0_B + 312) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 312) (CRS_PC0_B + 416) (CRS_PC0_B + 316) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. hz. rewrite G20.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_eq in Hb2.
    assert (Etb : cb_tb C = []) by (destruct (cb_tb C); [reflexivity | cbn [length] in Hb2; lia]).
    hb_upd HB. change (BASE + (CRS_PC0_B + 416)) with (BASE + CRS_PC_X1_B).
    apply SRr_ret.
    refine (HX1 fxk ly3 S3 Hp3 W3 _ mem3 _ k sp2 Hb Hws HB _ HL HD HT).
    apply h_regsat_x1.
    * repeat (apply h_regsat_upd; [unfold h1_keep0, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hnot|]). exact HK1.
    * hgetr. unfold cHash_B. rewrite Etb. reflexivity.
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. hz. rewrite G20.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_neq in Hb2.
    hb_upd HB.
    (* +316 sltu a2, zero, s5: a2 = 1 (data > 0) *)
    clear Hl Hd. hfd (CRS_PC0_B + 316) Hl Hd.
    eapply (h_sltu W3 fxk _ mem3 _ _ (CRS_PC0_B + 316) (CRS_PC0_B + 320) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. hz. rewrite G21, hw_sltu0 by lia. hb_upd HB.
    (* +320 mv a3, s5; +324 mv a0, s5; +328 mv a4, s4 *)
    clear Hl Hd. hfd (CRS_PC0_B + 320) Hl Hd.
    eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 320) (CRS_PC0_B + 324) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. rewrite G21. hb_upd HB.
    clear Hl Hd. hfd (CRS_PC0_B + 324) Hl Hd.
    eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 324) (CRS_PC0_B + 328) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. rewrite G21. hb_upd HB.
    clear Hl Hd. hfd (CRS_PC0_B + 328) Hl Hd.
    eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 328) (CRS_PC0_B + 332) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. rewrite G20. hb_upd HB.
    (* THE LOOP L1 (PRW_CrcGen.djb_loop with h1_iter) *)
    eapply SRr_bind.
    { apply (djb_loop (fx := fxk) SEGS (BASE + (CRS_PC0_B + 332)) (BASE + (CRS_PC0_B + 416)) 11%bv 14%bv [10%bv; 13%bv]
        (cb_data C) (cb_tb C) (h1_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2)).
      - intros i W c Hi Hh. exact (h1_iter CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2 i W c Hi Hh).
      - destruct (cb_tb C) as [|b0 tb0] eqn:Etb; [cbn [length] in Hb2; lia | cbn [length]; lia].
      - unfold djb_head. lazymatch goal with |- context [crs_cfg_B _ _ ?r _ ?m] => exists r, mem3, m end.
        split; [reflexivity|]. split; [lia|].
        split; [hgetr; reflexivity|]. split; [hgetr; f_equal; lia|].
        split; [apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_nil|].
        destruct HD as (HD1 & _ & HD3 & _).
        split; [exact HD1|]. split; [exact HD3|].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact HB|].
        unfold h1_keep. apply h_regsat_app.
        + repeat (apply h_regsat_upd; [unfold h1_keep0, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hnot|]).
          exact HK1.
        + apply Forall_cons; [cbn [fst snd]; hgetr; reflexivity | apply Forall_nil]. }
    cbv beta. intros W' c' _ Hhead.
    destruct (djb_exit_hash (fx := fxk) SEGS _ _ _ _ _ _ _ _ _ Hhead) as (regs5 & mem5 & md5 & -> & H11 & _ & _ & HJ5).
    destruct HJ5 as (-> & -> & HB5 & HR5).
    change (cfg_at (fx := fxk) SEGS (BASE + (CRS_PC0_B + 416)) regs5 mem3 md5)
      with (crs_cfg_B fxk (BASE + CRS_PC_X1_B) regs5 mem3 md5).
    apply SRr_ret.
    refine (HX1 fxk ly3 S3 Hp3 W3 regs5 mem3 md5 k sp2 Hb Hws HB5 _ HL HD HT).
    apply h_regsat_x1; [exact (h_keep_keep0 _ C sp2 HR5) | exact H11].
Qed.

End f.
End d.

Print Assumptions crs_seg_H1_B.
Set Printing Implicit.
About crs_seg_H1_B.
Unset Printing Implicit.
