(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module names changed; 683 of its 755 lines of code are new or changed and 856 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrsSeg_H1_B.v, with its module names and numbers changed; 345 of its 916 lines of code are new or changed and 184 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): segment H2 of the walk of check_reject_clean_starved against
   the kit's text tcheck_reject_clean_starved_specX, row H2_B (a Theorem Labs lane's internal file BRIEF-crcs-Bprime-seg.md; lane CrsX2H2,
   a working branch). It proves the row's closing lemma over the FROZEN B' kit lib/B/Prog/CrsKitBp.v
   (a working branch fb124cd27931):
     crs_seg_H2_B : HT_fuzz_alloc_count -> HT_fuzz_alloc_ran_out -> HK -> crs_from_R_B .. -> crs_from_X2_B .. ->
                    crs_from_H2_B ..
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that lookup;
   CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its released rows
   were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). This file is one SEGMENT of that walk (kind: segment lemma); it is new.
   DONOR (rule 24, reuse): this lane's A' file lib/A/Prog/CrsSeg_H2.v (a working branch 7fea2e4fd8c0, blob
   ea5b62219e06): the same engine prefix, transport, loop invariant and closing proof, with the kit's `_B` names and
   every number re-read at B'. THE HAND-STEP KIT (the hw_ / h_ lemmas and the h* tactics below, h_sltu / h_sltiu /
   h_xor included) and the loop step's UBSan refutations are restated VERBATIM from lane CrsX1H1's
   lib/B/Prog/CrsSeg_H1_B.v :81-453 and :516-701 (a working branch eb01d000c4c), its h1_iter re-read at L2's
   offsets and registers (every register of the loop is one up: hash a2, count a5, cursors a1 / a4, the UBSan flag
   a3, the shadow and byte temporaries a6 / a7).
   INPUTS.
   - Pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
     unstripped twin .../bound-fix/9e1283d1/unstripped/fuzz_preset/fuzz_preset.asan-ubsan sha256 c90d4fa54d43160b
     (the segment read by capstone, the internal file elfdis.py --addr 0x822f0 0xd0).
   - Listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (a Theorem Labs lane's listings v3).
     Entry 0x820e0 = slot 645 (B_entry_check_reject_clean_starved). H2 is slots 777 .. 810; the loop's UBSan arms go
     to slot 929 (+1136, `unimp`).
   - The kit's #102 texts, at the blobs named below: tfuzz_alloc_ran_out_specX
     / tfuzz_alloc_count_specX (lib/A/PRH_FnAlloc.v blob 740f4d11d144), prh_ledger .. ran most own and prh_ledger_own,
     fpre ending with frm_zero (lib/A/PRH_Base.v blob fdb45545469b), all at prh_img_B / PI_prog_B.
   - The transport and call helpers of lib/B/Prog/CrsSeg_X2_B.v (row X2_B, same branch), and the generic djb2 loop of
     lib/A/Prog/PRW_CrcGen.v (djb_loop, with this file's one-iteration step h2_iter).
   THE SEGMENT (offsets from the entry; B' listing, capstone over the twin):
     +528 lbu a0, -1340(s8); +532 bnez a0 (CHECK #2's OWN arm -> R): refuted, the cell reads the boundary ledger's own
          argument 0 (prh_ledger_own; CRS_RO_B + CRS_OFF_OWN_B = pi_g_own_ran_out)
     +536 jal fuzz_alloc_ran_out; +540 bnez a0: g_ran_out = 1 -> R (+736)
     +544 jal fuzz_alloc_count (a0 = the count after the whole pretty write)
     +548 lui a1, 1; +552 addiw a2, a1, 0x505 (a2 = 5381); +556 beqz s4: size = 0 -> X2 (+664)
     +560 sltu a3, zero, s5 (a3 = 1: data <> 0); +564 mv a4, s5; +568 mv a1, s5; +572 mv a5, s4; the djb2 loop L2
          +576 .. +640, one byte per iteration: the UBSan pointer-overflow checks `bltu a1, s5` (+576), `sltiu a6, a1,
          1; xor a6, a3, a6; beqz a6` (+580 .. +588) and `beqz s5` (+592), each to the trap +1136; the shadow byte of
          a1 by `srli; add s11; lb` (+596 .. +604), `bnez` (+608) -> +648 slow path `andi a7, a1, 7; blt a7, a6`
          (+648 / +652) -> +612 or the report arm +656 / +660 (`jal __asan_report_load1`); then a2 = 33 a2 + byte,
          a5 -= 1, a1 += 1, a4 += 1, `bnez a5` (+640) -> +576; +644 `j` -> X2 (+664)
   THE WORLD RELATION. Every boundary of H2 is after a free or a realloc: the kit's crs_from_H2_B / crs_from_X2_B take
   crs_baseR_B at R := wle' SEGS RZ_cf and conclude SRr' (YA0nH, SRrG at R). THE CALLS AND CHECK #2 run on the
   listing engine's R forms (YC1fPx paj_run_xR, YCbqGcall aj_call_x_spR; the plain callee texts lifted by
   CrsSeg_X2_B.cxb_lift_x) over CrsSeg_X2_B.v's B' segment environment TE, and carry the boundary facts by its
   crs_ws_B / crs_ws_run_B / crs_ws_callee_B. From +548 every instruction is stepped by hand (memory is only read), a
   plain SRr stretch whose post is the goal at R. THE THREE UBSan ARMS ARE UNREACHABLE: a1 = data + i
   with 0 < data and data + size < 2 ^ 62 (crs_pre_B), so `bltu a1, s5` is false, a6 = (a1 == 0) = 0 and a3 xor a6 = 1,
   and s5 = data <> 0; the loop invariant carries a3 = 1 (h2_keep). THE REPORT ARM is unreachable by
   PRW_CrcGen.djb_byte_shadow over crs_dat_B's range_addressable.
   PREMISES of crs_seg_H2_B, in the A' order: HT_fuzz_alloc_count, HT_fuzz_alloc_ran_out (the kit's texts exactly, at
   prh_img_B / PI_prog_B, any float state fx'), HK : CrsKeep_B B ARx (the kit's transport record, proved once in the
   composition), then crs_from_R_B and crs_from_X2_B. No named hole.
   Numerals: offsets +528 .. +1136 (LENGTH: 4 * slot); 530124 (ADDRESS: the B' text base pa_val A_TEXT, by
   vm_compute, one assert); 3120 / 3128 / 3316 (LENGTH: CRS_PC0_B = 2580 plus the return sites +540 / +548 and R +736,
   each checked by vm_compute where it meets a kit name); 6152892 (ADDRESS: CRS_RO_B by vm_compute, one assert);
   -1340, 4096 / 5381 (lui 1; addiw 0x505), 33, 32, 8, 7, 5, 3, 1 (WORD: the listing's immediates); 2 ^ 20 .. 2 ^ 64
   (LENGTH / WORD bounds). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjWriteHyp ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB CrsKitBp CrsSeg_X2_B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PRW_WalkEnvB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
#[local] Notation PL := (PL_prog_B).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

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
(* the boundary facts of this walk: every boundary of H2 is after a free or a realloc, so crs_baseR_B at the
   re-hiding relation wle' SEGS RZ_cf *)
#[local] Notation BASEp CTX0 C :=
  (@crs_baseR_B fx rc ci cp RL SK B ARx (wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
(* lib/A/Prog/CrsSeg_X2.v's transport lemmas at this section's entry float state (named: a second FPState fxk is in
   scope at every use) *)
#[local] Notation WS := (crs_ws_B (fx := fx) B ARx).
#[local] Notation WS_RUN := (crs_ws_run_B (fx := fx) B ARx).
#[local] Notation WS_CALLEE := (crs_ws_callee_B (fx := fx) B ARx LAWS).
#[local] Notation CHAIN := (crs_chain_B (fx := fx) B ARx).
#[local] Notation CFPRE := (crs_callee_fpre_B (fx := fx) B ARx).

(* crs_base_B at the next register file and the materialised model, when gp and tp are kept *)
Lemma h_base_step : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X,
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  getr regs' 3%bv = getr regs3 3%bv -> getr regs' 4%bv = getr regs3 4%bv ->
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs' mem3 (with_vm_backing (m_vm_lazy md3) X md3) k sp2.
Proof.
intros CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X HB E3 E4.
destruct HB as (HP & Hz & Hk & HJ & HF & HSV & HSL & HRO & HMN & R3 & R4 & Hsp).
split; [exact HP|]. split; [exact Hz|]. split; [exact Hk|].
split; [unfold crs_JR_B in *;
  exact (ajournal_x_materializeR SEGS B prh_pst ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ)|].
split; [exact HF|]. split; [exact HSV|]. split; [exact HSL|]. split; [exact HRO|]. split; [exact HMN|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact Hsp.
Qed.

(* the facts of crs_pre_B the stretch uses (CrsSeg_H1.v h_pre_facts without its took bound) *)
Lemma h2_pre_facts : forall CTX0 C, crs_pre_B (fx := fx) (rc := rc) B ARx CTX0 C ->
  cSize_B C <= 3 * 2 ^ 20 /\ 0 < cb_data C /\ cb_data C + cSize_B C < 2 ^ 62.
Proof.
intros CTX0 C H. unfold crs_pre_B in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* ---- the loop L2: its head invariant J (the world and memory the boundary's, crs_base_B at the current register
   file and model, the registers the loop keeps: the boundary's, s7 = the count before the pretty write, a0 = the
   count after it) and its one-iteration step ---- *)
Definition h2_keep0 (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rs_B C sp2 ++ [(23%bv, crs_cnt1_B C); (10%bv, crs_cnt1_B C + cN1_B C)].
(* the loop's kept list adds a3 = 1, the `sltu a3, zero, s5` of +560 (data <> 0) the UBSan check at +584 reads *)
Definition h2_keep (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) := h2_keep0 C sp2 ++ [(13%bv, 1)].
Definition h2_J (CTX0 : list (list Z)) (C : crsC_B) (fxk : YK11.FPState) (ly3 : alayout) (S3 : astate)
  (Hp3 : list Z) (W3 : world SEGS) (mem3 : word -> option byte) (k sp2 : Z)
  : world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun W regs mem md => W = W3 /\ mem = mem3 /\ BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs mem3 md k sp2 /\
    crs_regsat_B regs (h2_keep C sp2).

Ltac hb_upd HB :=
  lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ (with_vm_backing (m_vm_lazy ?m) ?X ?m)) _ =>
    let H' := fresh "HB'" in
    pose proof (h_base_step _ _ _ _ _ _ _ _ r _ _ _ _ X HB ltac:(hgetr; reflexivity) ltac:(hgetr; reflexivity)) as H';
    clear HB; rename H' into HB end.
Ltac hrs_upd HR :=
  lazymatch goal with
  | |- SRr _ _ (crs_cfg_B _ _ (regupd ?rg ?rr ?v) _ _) _ =>
    let l := lazymatch type of HR with crs_regsat_B _ ?l => l end in
    let H' := fresh "HR'" in
    pose proof (h_regsat_upd rg l rr v ltac:(unfold h2_keep, h2_keep0, crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B; hnot) HR) as H';
    clear HR; rename H' into HR
  | _ => idtac end.
Ltac hpost := intros; hcanon; hsig; rewrite ?h_vaddi0; hgetr.
Ltac hz := rewrite ?getr_zero; change (Z_to_bv 64 0) with (w64 0).
(* the registers a run of the listing engine leaves alone are `SOff (32 + r) 0` on its symbolic registers
   (CrsSeg_X2.v's cxb_kept_regs, whose Ltac is local to that file's section) *)
Ltac h2_kept_regs := repeat (apply Forall_cons; [vm_compute; reflexivity|]); apply Forall_nil.

Lemma h2_iter : forall CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2 i W c,
  (i < length (cb_tb C))%nat ->
  djb_head (fx := fxk) SEGS (BASE + (CRS_PC0_B + 576)) 12%bv 15%bv [11%bv; 14%bv] (cb_data C) (cb_tb C)
    (h2_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) i W c ->
  SRr SEGS W c (djb_head (fx := fxk) SEGS
    (if (S i <? length (cb_tb C))%nat then BASE + (CRS_PC0_B + 576) else BASE + (CRS_PC0_B + 664))
    12%bv 15%bv [11%bv; 14%bv] (cb_data C) (cb_tb C) (h2_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) (S i)).
Proof.
intros CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2 i W c Hi (regs & mem & md & -> & Hle & Hh & Hc & Hps & Hg & Hra & HJ).
destruct HJ as (-> & -> & HBs & HRs).
pose proof h_pc0 as HPC.
pose proof (Forall_inv Hps) as Ha1. pose proof (Forall_inv (Forall_inv_tail Hps)) as Ha4. cbv beta in Ha1, Ha4.
pose proof (h2_pre_facts CTX0 C (proj1 HBs)) as (Hsz & Hd0 & Hd62).
unfold cSize_B in Hsz, Hd62.
set (x := cb_tb C) in *. set (d := cb_data C) in *.
set (n := Z.of_nat (length x)) in *.
set (h := ck_djb2 5381 (firstn i x)) in *.
assert (Hhr : 0 <= h < 2 ^ 64) by apply djb_hash_range.
assert (G27 : getr regs 27%bv = w64 SHADOW_OFF)
  by (apply (h_regsat_get regs (h2_keep C sp2)); [exact HRs | unfold h2_keep, h2_keep0, crs_rs_B, crs_rbase_B; hin]).
assert (G21 : getr regs 21%bv = w64 d)
  by (apply (h_regsat_get regs (h2_keep C sp2)); [exact HRs | unfold h2_keep, h2_keep0, crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B; hin]).
assert (G13 : getr regs 13%bv = w64 1)
  by (apply (h_regsat_get regs (h2_keep C sp2)); [exact HRs | unfold h2_keep, h2_keep0, crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B; hin]).
(* the shadow byte of the next byte, and the byte *)
destruct (djb_byte_shadow _ _ d n (Z.of_nat i) Hra ltac:(lia)) as (s & Hs & Hsok).
pose proof (h_aview_byte _ _ _ _ _ Hs) as Hs256.
destruct (h_rdn1 SEGS (w_H W3) mem3 _ s Hs) as (bs & Hrbs & Hbs).
destruct (djb_byte SEGS (mrestrict (w_H W3) mem3) d x i Hg Hi) as (Hmb & Hc256).
pose proof (h_rdn1_mb SEGS _ _ _ Hmb) as Hrc.
set (cc := nth i x 0) in *.
assert (Hs8 : s = 0 \/ (0 < s < 8 /\ (d + Z.of_nat i) mod 8 < s)) by (unfold saddr_ok in Hsok; lia).
change (cfg_at (fx := fxk) SEGS (BASE + (CRS_PC0_B + 576)) regs mem3 md)
  with (crs_cfg_B fxk (BASE + (CRS_PC0_B + 576)) regs mem3 md).
(* +332 bltu a0, s5 -> the UBSan trap +1136: refuted (a0 = data + i >= data) *)
hfd (CRS_PC0_B + 576) Hl Hd.
eapply (h_br W3 fxk regs mem3 md _ (CRS_PC0_B + 576) (CRS_PC0_B + 1136) (CRS_PC0_B + 580) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
{ intros Hb ?. exfalso. revert Hb. hcanon. rewrite Ha1, G21. cbn [branch_taken]. rewrite hw_ltu by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. discriminate. }
intros _ ?. hcanon. hb_upd HBs.
(* +336 sltiu a5, a0, 1: a5 = 0 (a0 <> 0) *)
clear Hl Hd. hfd (CRS_PC0_B + 580) Hl Hd.
eapply (h_sltiu W3 fxk _ mem3 _ _ (CRS_PC0_B + 580) (CRS_PC0_B + 584) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite Ha1, hw_sltiu1 by lia. hb_upd HBs. hrs_upd HRs.
(* +340 xor a5, a2, a5: a5 = 1 *)
clear Hl Hd. hfd (CRS_PC0_B + 584) Hl Hd.
eapply (h_xor W3 fxk _ mem3 _ _ (CRS_PC0_B + 584) (CRS_PC0_B + 588) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G13, hw_xor10. hb_upd HBs. hrs_upd HRs.
(* +344 beqz a5 -> +1136: refuted (a5 = 1) *)
clear Hl Hd. hfd (CRS_PC0_B + 588) Hl Hd.
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 588) (CRS_PC0_B + 1136) (CRS_PC0_B + 592) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
{ intros Hb ?. exfalso. revert Hb. hcanon. hgetr. hz. cbn [branch_taken]. rewrite hw_eqb by lia. discriminate. }
intros _ ?. hcanon. hb_upd HBs.
(* +348 beqz s5 -> +1136: refuted (data > 0) *)
clear Hl Hd. hfd (CRS_PC0_B + 592) Hl Hd.
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 592) (CRS_PC0_B + 1136) (CRS_PC0_B + 596) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
{ intros Hb ?. exfalso. revert Hb. hcanon. hgetr. hz. rewrite G21. cbn [branch_taken]. rewrite hw_eqb by lia.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. discriminate. }
intros _ ?. hcanon. hb_upd HBs.
(* +352 srli a5, a0, 3 *)
clear Hl Hd. hfd (CRS_PC0_B + 596) Hl Hd.
eapply (h_srli W3 fxk _ mem3 _ _ (CRS_PC0_B + 596) (CRS_PC0_B + 600) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite Ha1, hw_srli3 by lia. hb_upd HBs. hrs_upd HRs.
(* +356 add a5, a5, s11 *)
clear Hl Hd. hfd (CRS_PC0_B + 600) Hl Hd.
eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0_B + 600) (CRS_PC0_B + 604) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
assert (H8 : 0 <= (d + Z.of_nat i) / 8 < 2 ^ 64)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (HSO : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
hpost. rewrite G27. rewrite (hw_add _ _ H8 HSO).
hb_upd HBs. hrs_upd HRs.
(* +360 lb a5, 0(a5): the shadow byte s *)
clear Hl Hd. hfd (CRS_PC0_B + 604) Hl Hd.
eapply (h_lb W3 fxk _ mem3 _ _ (CRS_PC0_B + 604) (CRS_PC0_B + 608) _ _ _ _ bs Hl Hd); [reflexivity | lia | lia | |].
{ hcanon. hsig. hgetr. rewrite h_vaddi0.
  replace ((d + Z.of_nat i) / 8 + SHADOW_OFF) with (shadow_of_addr SHADOW_OFF (d + Z.of_nat i))
    by (unfold shadow_of_addr; lia).
  exact Hrbs. }
hpost. rewrite hw_lb by lia. rewrite Hbs. hb_upd HBs. hrs_upd HRs.
(* +364 bnez a5: s = 0 falls through to +368; else the slow path +404 *)
clear Hl Hd. hfd (CRS_PC0_B + 608) Hl Hd.
(* the common tail from +368 (both arms reach it) *)
assert (TAIL : forall regsT mdT,
  getr regsT 11%bv = w64 (d + Z.of_nat i) -> getr regsT 14%bv = w64 (d + Z.of_nat i) ->
  getr regsT 12%bv = w64 h -> getr regsT 15%bv = w64 (n - Z.of_nat i) ->
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regsT mem3 mdT k sp2 -> crs_regsat_B regsT (h2_keep C sp2) ->
  SRr SEGS W3 (crs_cfg_B fxk (BASE + (CRS_PC0_B + 612)) regsT mem3 mdT)
    (djb_head (fx := fxk) SEGS
      (if (S i <? length x)%nat then BASE + (CRS_PC0_B + 576) else BASE + (CRS_PC0_B + 664))
      12%bv 15%bv [11%bv; 14%bv] d x (h2_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) (S i))).
{ clear dependent regs. intros regsT mdT T11 T14 T12 T15 HBt HRt.
  (* +368 slli a5, a1, 5 *)
  clear Hl Hd. hfd (CRS_PC0_B + 612) Hl Hd.
  eapply (h_slli W3 fxk regsT mem3 mdT _ (CRS_PC0_B + 612) (CRS_PC0_B + 616) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T12, hw_slli5 by lia. hb_upd HBt. hrs_upd HRt.
  (* +372 lbu a6, 0(a3) *)
  clear Hl Hd. hfd (CRS_PC0_B + 616) Hl Hd.
  eapply (h_lbu W3 fxk _ mem3 _ _ (CRS_PC0_B + 616) (CRS_PC0_B + 620) _ _ _ _ (Z_to_bv 8 cc) Hl Hd);
    [reflexivity | lia | lia | |].
  { hcanon. hsig. hgetr. rewrite T14, h_vaddi0. exact Hrc. }
  hpost. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia).
  change (Z_to_bv 64 cc) with (w64 cc). hb_upd HBt. hrs_upd HRt.
  (* +376 add a1, a5, a1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 620) Hl Hd.
  eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0_B + 620) (CRS_PC0_B + 624) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T12, hw_add_m. hb_upd HBt. hrs_upd HRt.
  (* +380 addi a4, a4, -1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 624) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 624) (CRS_PC0_B + 628) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T15, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* +384 addi a0, a0, 1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 628) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 628) (CRS_PC0_B + 632) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T11, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* +388 add a1, a1, a6 *)
  clear Hl Hd. hfd (CRS_PC0_B + 632) Hl Hd.
  eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0_B + 632) (CRS_PC0_B + 636) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite hw_add_m. hb_upd HBt. hrs_upd HRt.
  (* +392 addi a3, a3, 1 *)
  clear Hl Hd. hfd (CRS_PC0_B + 636) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0_B + 636) (CRS_PC0_B + 640) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T14, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* the head facts at S i *)
  assert (Eh : w64 (32 * h + h + cc) = w64 (ck_djb2 5381 (firstn (S i) x))).
  { apply hw_eq. rewrite (djb_hash_step x i Hi). fold h. fold cc. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Eh. rewrite Eh in HRt.
  (* +396 bnez a4 -> +332 *)
  clear Hl Hd. hfd (CRS_PC0_B + 640) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 640) (CRS_PC0_B + 576) (CRS_PC0_B + 644) _ _ _ _ _ Hl Hd);
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
    clear Hl Hd. hfd (CRS_PC0_B + 644) Hl Hd.
    eapply (h_j W3 fxk _ mem3 _ _ (CRS_PC0_B + 644) (CRS_PC0_B + 664) _ _ _ Hl Hd); [reflexivity | lia | reflexivity | lia |].
    intros ?. hb_upd HBt. apply SRr_ret.
    lazymatch goal with HBt : BASEp _ _ _ _ _ _ _ ?rr _ ?mm _ _ |- _ =>
      exists rr, mem3, mm end.
    split; [reflexivity|]. split; [lia|].
    split; [hgetr; reflexivity|]. split; [hgetr; f_equal; unfold n in *; lia|].
    split; [apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_nil|].
    split; [exact Hg|]. split; [exact Hra|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HBt|]. exact HRt. }
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 608) (CRS_PC0_B + 648) (CRS_PC0_B + 612) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
- (* taken: s <> 0, the slow path *)
  intros Hb ?. revert Hb. hcanon. hgetr. hz.
  cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply negb_true_iff, Z.eqb_neq in Hb.
  destruct Hs8 as [Hs0 | (Hs08 & Hsm)]; [exfalso; exact (Hb Hs0)|].
  hb_upd HBs.
  (* +404 andi a6, a0, 7 *)
  clear Hl Hd. hfd (CRS_PC0_B + 648) Hl Hd.
  eapply (h_andi W3 fxk _ mem3 _ _ (CRS_PC0_B + 648) (CRS_PC0_B + 652) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite Ha1, hw_andi7 by lia. hb_upd HBs. hrs_upd HRs.
  (* +408 blt a6, a5: taken (the byte is inside the granule's valid prefix) -> +368; the report arm +412 refuted *)
  clear Hl Hd. hfd (CRS_PC0_B + 652) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0_B + 652) (CRS_PC0_B + 612) (CRS_PC0_B + 656) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  + intros _ ?. hcanon. hb_upd HBs.
    apply TAIL; [hgetr; exact Ha1 | hgetr; exact Ha4 | hgetr; exact Hh | hgetr; exact Hc | exact HBs | exact HRs].
  + intros Hb2 ?. exfalso. revert Hb2. hcanon. hgetr. cbn [branch_taken].
    rewrite hw_lts by (pose proof (Z.mod_pos_bound (d + Z.of_nat i) 8); lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hsm). discriminate.
- (* not taken: s = 0, the fast path *)
  intros Hb ?. hcanon. hb_upd HBs.
  apply TAIL; [hgetr; exact Ha1 | hgetr; exact Ha4 | hgetr; exact Hh | hgetr; exact Hc | exact HBs | exact HRs].
Qed.

(* the boundary register lists, from the loop's kept list *)
Lemma h2_regsat_x2 : forall regs C sp2, crs_regsat_B regs (h2_keep C sp2) -> getr regs 12%bv = w64 (cHash_B C) ->
  crs_regsat_B regs (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B ++
                   [(23%bv, crs_cnt1_B C); (10%bv, crs_cnt1_B C + cN1_B C); (12%bv, cHash_B C)]).
Proof.
intros regs C sp2 H H12. unfold crs_regsat_B, h2_keep, h2_keep0, crs_rs_B in *. rewrite !Forall_app in *.
destruct H as (((H1 & H2 & H3 & H4 & H5) & H6) & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
constructor; [exact (Forall_inv H6)|]. constructor; [exact (Forall_inv (Forall_inv_tail H6))|].
constructor; [exact H12|]. constructor.
Qed.
Lemma h2_regsat_x2_0 : forall regs C sp2, crs_regsat_B regs (h2_keep0 C sp2) -> getr regs 12%bv = w64 (cHash_B C) ->
  crs_regsat_B regs (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B ++
                   [(23%bv, crs_cnt1_B C); (10%bv, crs_cnt1_B C + cN1_B C); (12%bv, cHash_B C)]).
Proof.
intros regs C sp2 H H12. unfold crs_regsat_B, h2_keep0, crs_rs_B in *. rewrite !Forall_app in *.
destruct H as ((H1 & H2 & H3 & H4 & H5) & H6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
constructor; [exact (Forall_inv H6)|]. constructor; [exact (Forall_inv (Forall_inv_tail H6))|].
constructor; [exact H12|]. constructor.
Qed.
Lemma h2_regsat_r : forall regs C sp2, crs_regsat_B regs (crs_rs_B C sp2) -> crs_regsat_B regs (crs_rbase_B C sp2 ++ crs_rsh_B C).
Proof.
intros regs C sp2 H. apply (h_regsat_incl regs (crs_rs_B C sp2)); [exact H|].
intros p Hp. unfold crs_rs_B. rewrite !in_app_iff in *. tauto.
Qed.

(* ==== CR-H2: the closing lemma ==== *)
Lemma crs_seg_H2_B : forall CTX0 C,
  (forall fx' : YK11.FPState, tfuzz_alloc_count_specX (fx := fx') (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fx' : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fx') (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  CrsKeep_B B ARx ->
  crs_from_R_B (fx := fx) (rc := rc) B ARx CTX0 C -> crs_from_X2_B (fx := fx) (rc := rc) B ARx CTX0 C ->
  crs_from_H2_B (fx := fx) (rc := rc) B ARx CTX0 C.
Proof.
intros CTX0 C HT_fuzz_alloc_count HT_fuzz_alloc_ran_out HK KcR KcX2.
unfold crs_from_H2_B.
intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 ran3 k1 Hdoc HB HR HL HD HT Hkf.
(* the walk's world relation R: the re-hiding relation (the kit's crs_from_H2_B / crs_from_X2_B take crs_baseR_B at
   it and conclude SRr' = SRrG at it), its two laws, and wle <= R *)
unfold SRr' in KcX2 |- *.
set (R := wle' SEGS YGcfRehidePost.RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS YGcfRehidePost.RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS YGcfRehidePost.RZ_cf).
assert (Rw : forall W W', wle W W' -> R W W') by exact (wle_wle' SEGS YGcfRehidePost.RZ_cf).
pose proof h_pc0 as HPC.
assert (HRS0 : crs_regsat_B regs3 (crs_rs_B C sp2)).
{ apply (h_regsat_incl regs3 _ _ HR). intros p Hp. unfold crs_rs_B in Hp. rewrite !in_app_iff in *. tauto. }
assert (R23 : getr regs3 23%bv = w64 (crs_cnt1_B C))
  by (apply (h_regsat_get regs3 _ _ _ HR); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B; hin).
destruct HL as ((HL0 & Hpk & Hran & Hc1 & Hc2 & Hroom & Hpos) & Hperm).
(* check #2's own cell reads 0: the boundary ledger's own argument (kit v3, the kit's E sweep) *)
pose proof (prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ HL0) as (Hown & _).
pose proof HB as (HPRE & Hfrm & Hfk & HJ & HFR & HSV & HSL & HROD & HMN & Hgp & Htp & Hsp2a & Hsp2b & Hsp2c & HDPk).
assert (HW : WS CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 (crs_cnt1_B C + k1) SIZE_MAXZ ran3).
{ split; [exact HB|]. split; [exact HL0|]. split; [exact Hperm|]. split; [exact Hpk|].
  split; [exact Hroom|]. split; [exact HD | exact HT]. }
(* the numbers *)
pose proof HPRE as (HPf & _ & HUNIV & _ & _ & _ & _ & _ & Hsz & Hd0 & Hd62 & HSRC & _ & Htk & HDOC & HLE & Hcnt
  & HRUN & Hran0 & _).
pose proof HPf as (HAFN & _). pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (EFR : CRS_FRAME_B = 144) by (vm_compute; reflexivity).
assert (ESTc : 1000 <= STK_check_reject_clean_starved (PI := prh_img_B)) by (unfold Z.le; vm_compute; discriminate).
pose proof asan_consts as (AC1 & _).
assert (EBASE : BASE = 530124) by (vm_compute; reflexivity).
destruct HDOC as [Hd00 | (Hrd & HTOK & Hwl0 & Hwl1 & Hdep)]; [exfalso; exact (Hdoc Hd00)|].
pose proof (crs_N_bnd_B C true 28 Hwl1 ltac:(lia)) as HN1. fold (cN1_B C) in HN1.
pose proof (crs_N_bnd_B C false 24 Hwl0 ltac:(lia)) as HN0. fold (cN0_B C) in HN0.
pose proof (crs_first_bnd_B C ltac:(lia)) as Hfst.
assert (Hr01 : ran3 = 0 \/ ran3 = 1) by (rewrite Hran0 in Hran; left; exact Hran).
pose proof Hkf as (Hk1 & Hk2). change (PjWriteHyp.wcalls (cb_t C) true) with (cN1_B C) in Hk1, Hk2.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
pose (BR := paj_branchR (fx := fxk) (rc := rc) (L := B_prog_listing) (PI := PA) R).
pose (RUNTO := @paj_run_to_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
(* ---- +504 lbu a0, 540(s8); bnez a0 (+508, check #2's OWN arm -> R): the cell reads 0 (prh_ledger_own), so the
   arm is not taken; +512 jal fuzz_alloc_ran_out ---- *)
set (E := TE (cb_regs C) regs3 []).
pose proof (crs_rs_get_B C sp2 _ HRS0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G24).
assert (ERO : CRS_RO_B = 6152892) by (vm_compute; reflexivity).
assert (X24 : bv_unsigned (ew E (xr 24)) = CRS_RO_B).
{ unfold xr. rewrite (te_cur (cb_regs C) regs3 [] 24%bv 24) by reflexivity. rewrite G24. unfold w64.
  apply unsigned_lit_small. lia. }
assert (Eown : CRS_RO_B + -1340 = @pi_g_own_ran_out prh_img_B) by (vm_compute; reflexivity).
assert (HS : st_ok_pi SEGS VAL E
   (mkSS CRS_PC_H2_B cur_atoms [YP09.mkRegion (Some (xr 24)) (-1340) (-1339) 0 0 [YP09.mkChunk (-1340) (CVal 1 (SLit 0))]] None
      (mkFacts [] [] []))
   (restrict (w_H W3) (@YK11.mkst fxk regs3 (Z_to_bv 64 (BASE + CRS_PC_H2_B)) mem3 (seg_rom SEGS)))).
{ apply ts_st_ok.
  - apply te_regs_ok.
  - first [reflexivity | vm_compute; reflexivity].
  - constructor; [|constructor].
    apply (ts_rok E _ (xr 24) CRS_RO_B); [exact X24 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ (-1340) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Eown. change (N.to_nat 1) with (@pi_gz_own_ran_out prh_img_B). exact Hown.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
unfold crs_JR_B in HJ. unfold crs_cfg_B.
paj_run_tok_x RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hm1 : forall x, ms_mem ms x = mem3 x).
{ intros x; apply HF; intros (r & Hr & Hw). cbn [In] in Hr. destruct Hr as [<- | []]. cbn in Hw. lia. }
clear HF HFr HG.
assert (HRS1 : crs_regsat_B (ms_regs ms) (crs_rs_B C sp2)).
{ apply (cxb_regsat_run_c (fx := fxk) (cb_regs C) regs3 [] _ _ ms _ HS); [|exact HRS0].
  unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app]. h2_kept_regs. }
prreg HS (1%bv : bv 5) Q1. prreg HS (23%bv : bv 5) Q23. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (A55 : ew E 55 = getr regs3 23) by exact (te_cur (cb_regs C) regs3 [] 23%bv 23 eq_refl).
assert (A35 : ew E 35 = getr regs3 3) by exact (te_cur (cb_regs C) regs3 [] 3%bv 3 eq_refl).
assert (A36 : ew E 36 = getr regs3 4) by exact (te_cur (cb_regs C) regs3 [] 4%bv 4 eq_refl).
rewrite A55, R23 in Q23. rewrite A35 in Q3. rewrite A36 in Q4.
pose proof (WS_RUN HK CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 _ _ _ (ms_regs ms) (ms_mem ms) _
  HW HJ Hm1 Q3 Q4) as HW1.
pose proof (crs_rs_get_B C sp2 _ HRS1) as (G2 & G8 & _).
assert (Hsp : spZ (ms_regs ms) = sp2) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = spZ (cb_regs C)) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
pose proof HW1 as (HB1 & HL1 & _ & _ & Hroom1 & _).
pose proof HB1 as (_ & _ & _ & _ & _ & HSV1 & _ & _ & _ & Hgp1 & Htp1 & _).
destruct (CHAIN R CTX0 C ly3 S3 Hp3 W3 (ms_mem ms) _ k sp2 HPRE HJ HSV1 ltac:(lia)) as (ch1 & Hch).
assert (EST3 : STK_fuzz_alloc_ran_out (PI := prh_img_B) + 144 <= STK_check_reject_clean_starved (PI := prh_img_B))
  by (unfold Z.le; vm_compute; discriminate).
assert (EST30 : 0 <= STK_fuzz_alloc_ran_out (PI := prh_img_B)) by (unfold Z.le; vm_compute; discriminate).
eapply (SRrG_bind SEGS R Rt).
{ eapply (aj_call_x_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W3 _ _ ms
    STK_check_reject_clean_starved (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C)
    [(CRS_CID_B, cb_fpos C)] ly3 S3 Hp3 _ k (STK_fuzz_alloc_ran_out (PI := prh_img_B)) []
    (sp2 - spZ (cb_regs C)) _ ch1 _ HS eq_refl HJ).
  - rewrite Hsp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hsp2c; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hsp2c as [q2 Hq2]. exists (2 * q2 - q1). lia.
  - lia.
  - exact EST30.
  - lia.
  - rewrite Hgp1. exact Hgp0.
  - rewrite Htp1. exact Htp0.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite EBASE, unsigned_lit_small; lia.
  - rewrite Hs0. replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 by lia. exact Hch.
  - intros HPRE1. apply (cxb_lift_x (fx := fxk) (SK := SK) SEGS B PST ARx R Rw).
    refine (HT_fuzz_alloc_ran_out fxk ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ ch1 Lam3 peak3 (crs_cnt1_B C + k1)
      SIZE_MAXZ ran3 (cb_most C) 0
      (CFPRE R CTX0 C fxk ly3 S3 Hp3 W3 _ (ms_mem ms) _ k sp2 _ (ms_regs ms) _ ch1 HB1 Hsp _ HPRE1) HL1).
    unfold raZ. rewrite Q1, EBASE, unsigned_lit_small by lia. lia.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k2 & -> & HJc4 & HJ14 & HP4 & HQ4 & HMN4).
destruct HQ4 as (Hrm4 & Ha04 & -> & -> & Eab4 & HL4).
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ14 by lia.
assert (HW2 : WS CTX0 C fxk ly4 S3 Hp3 W4 regs4 mem4 md4 (k + k2) sp2 Lam3 peak3 (crs_cnt1_B C + k1) SIZE_MAXZ ran3).
{ apply (WS_CALLEE HK CTX0 C fxk ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ k sp2 Lam3 peak3 _ _ _
    _ ly4 S3 Hp3 W4 regs4 mem4 md4 k2 Lam3 peak3 _ _ _ HW1 HJ14 HJc4 HMN4 (cxb_ap3 _ _ HP4) (cxb_ap4 _ _ HP4)
    HL4 (Permutation_refl _)).
  - rewrite Eab4. apply Permutation_refl.
  - lia.
  - apply Hrm4. exact Hroom1. }
assert (HRS2 : crs_regsat_B regs4 (crs_rs_B C sp2)) by exact (cxb_regsat_ap _ _ _ HP4 (crs_rs_cs_B C sp2) HRS1).
assert (R23b : getr regs4 23 = w64 (crs_cnt1_B C)).
{ rewrite (cxb_ap _ _ 23%bv HP4) by (change (bv_unsigned (23%bv : bv 5)) with 23; unfold acallee_saved; lia).
  rewrite Q23. reflexivity. }
clear HW HW1 HJ HJ14 HS SHOK HEI HRS0 HRS1 Q1 Q3 Q4 Q23 Hm1 Hsp Hs0 Hch A55 A35 A36 G2 G8 ch1 X24 G24.
clear dependent ms. clear dependent mat.
(* ---- +516 bnez a0: a0 = g_ran_out (the ledger's ran3); else R (+688) ---- *)
set (E2 := TE (cb_regs C) regs4 []).
assert (HS : st_ok_pi SEGS VAL E2 (mkSS 3120 cur_atoms [] None (mkFacts [] [] []))
   (restrict (w_H W4) (@YK11.mkst fxk regs4 (Z_to_bv 64 (BASE + 3120)) mem4 (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E2 (mrestrict (w_H W4) mem4)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E2) by apply te_env.
pose proof HW2 as (HB2 & _). pose proof HB2 as (_ & _ & _ & HJ & _).
unfold crs_JR_B in HJ.
assert (A42 : ew E2 42 = getr regs4 10) by exact (te_cur (cb_regs C) regs4 [] 10%bv 10 eq_refl).
assert (A35 : ew E2 35 = getr regs4 3) by exact (te_cur (cb_regs C) regs4 [] 3%bv 3 eq_refl).
assert (A36 : ew E2 36 = getr regs4 4) by exact (te_cur (cb_regs C) regs4 [] 4%bv 4 eq_refl).
assert (Ura : bv_unsigned (ew E2 42) = ran3)
  by (rewrite A42, Ha04; unfold w64; apply unsigned_lit_small; destruct Hr01 as [-> | ->]; lia).
psrr_branch_tok RUN BR HS SHOK (2 ^ 63, 2 ^ 63).
- (* g_ran_out = 1: a refusal - refuted, nothing is refused *)
  rewrite branch_ne_U, cxb_U0, U_SLit, Ura in Hc. change (zcanon 0) with 0 in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Er : ran3 = 1) by lia.
  (* refuted: g_ran_out is the entry's 0 at every boundary (crs_core_B) *)
  exfalso. lia.
- (* g_ran_out = 0: the whole pretty write made all N1 calls; +520 jal fuzz_alloc_count *)
  rewrite branch_ne_U, cxb_U0, U_SLit, Ura in Hc. change (zcanon 0) with 0 in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  clear Ura. rewrite Hran0 in Hran. subst ran3.
  assert (Ek1 : k1 = cN1_B C) by exact (Hk2 ltac:(lia)). subst k1.
  paj_run_tok_x RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
  { apply awr_ok_nil. }
  assert (Hm1 : forall x, ms_mem ms x = mem4 x) by (intros x; apply HF; intros (r & Hr & _); destruct Hr).
  clear HF HFr HG.
  assert (HRS3 : crs_regsat_B (ms_regs ms) (crs_rs_B C sp2)).
  { apply (cxb_regsat_run_c (fx := fxk) (cb_regs C) regs4 [] _ _ ms _ HS); [|exact HRS2].
    unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app]. h2_kept_regs. }
  prreg HS (1%bv : bv 5) Q1. prreg HS (23%bv : bv 5) Q23. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  assert (A55 : ew E2 55 = getr regs4 23) by exact (te_cur (cb_regs C) regs4 [] 23%bv 23 eq_refl).
  rewrite A55, R23b in Q23. rewrite A35 in Q3. rewrite A36 in Q4.
  pose proof (WS_RUN HK CTX0 C fxk ly4 S3 Hp3 W4 regs4 mem4 md4 (k + k2) sp2 Lam3 peak3 _ _ _
    (ms_regs ms) (ms_mem ms) _ HW2 HJ Hm1 Q3 Q4) as HW3.
  pose proof (crs_rs_get_B C sp2 _ HRS3) as (G2 & G8 & _).
  assert (Hsp : spZ (ms_regs ms) = sp2) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
  assert (Hs0 : s0Z (ms_regs ms) = spZ (cb_regs C))
    by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
  pose proof HW3 as (HB3 & HL3 & _ & _ & Hroom3 & _).
  pose proof HB3 as (_ & _ & _ & _ & _ & HSV3 & _ & _ & _ & Hgp3 & Htp3 & _).
  destruct (CHAIN R CTX0 C ly4 S3 Hp3 W4 (ms_mem ms) _ (k + k2) sp2 HPRE HJ HSV3 ltac:(lia)) as (ch1 & Hch).
  assert (EST4 : STK_fuzz_alloc_count (PI := prh_img_B) + 144 <= STK_check_reject_clean_starved (PI := prh_img_B))
    by (unfold Z.le; vm_compute; discriminate).
  assert (EST40 : 0 <= STK_fuzz_alloc_count (PI := prh_img_B)) by (unfold Z.le; vm_compute; discriminate).
  eapply (SRrG_bind SEGS R Rt).
  { eapply (aj_call_x_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W4 _ _ ms
      STK_check_reject_clean_starved (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C)
      [(CRS_CID_B, cb_fpos C)] ly4 S3 Hp3 _ (k + k2) (STK_fuzz_alloc_count (PI := prh_img_B)) []
      (sp2 - spZ (cb_regs C)) _ ch1 _ HS eq_refl HJ).
    - rewrite Hsp. lia.
    - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hsp2c; [|lia].
      destruct Hal16 as [q1 Hq1]. destruct Hsp2c as [q2 Hq2]. exists (2 * q2 - q1). lia.
    - lia.
    - exact EST40.
    - lia.
    - rewrite Hgp3. exact Hgp0.
    - rewrite Htp3. exact Htp0.
    - exact Q1.
    - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
    - rewrite EBASE, unsigned_lit_small; lia.
    - rewrite Hs0. replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 by lia. exact Hch.
    - intros HPRE1. apply (cxb_lift_x (fx := fxk) (SK := SK) SEGS B PST ARx R Rw).
      refine (HT_fuzz_alloc_count fxk ly4 S3 Hp3 W4 (ms_regs ms) (ms_mem ms) _ ch1 Lam3 peak3 (crs_cnt1_B C + cN1_B C)
        SIZE_MAXZ 0 (cb_most C) 0
        (CFPRE R CTX0 C fxk ly4 S3 Hp3 W4 _ (ms_mem ms) _ (k + k2) sp2 _ (ms_regs ms) _ ch1 HB3 Hsp _ HPRE1) HL3).
      unfold raZ. rewrite Q1, EBASE, unsigned_lit_small by lia. lia.
    - intros a (r & Hr & _). destruct Hr. }
  cbv beta. intros W5 c5 _ (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k3 & -> & HJc5 & HJ15 & HP5 & HQ5 & HMN5).
  destruct HQ5 as (Hrm5 & Hc05 & -> & -> & Eab5 & HL5).
  replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ15 by lia.
  assert (HW4 : WS CTX0 C fxk ly5 S3 Hp3 W5 regs5 mem5 md5 (k + k2 + k3) sp2 Lam3 peak3 (crs_cnt1_B C + cN1_B C)
     SIZE_MAXZ 0).
  { apply (WS_CALLEE HK CTX0 C fxk ly4 S3 Hp3 W4 (ms_regs ms) (ms_mem ms) _ (k + k2) sp2 Lam3 peak3 _ _ _
      _ ly5 S3 Hp3 W5 regs5 mem5 md5 k3 Lam3 peak3 _ _ _ HW3 HJ15 HJc5 HMN5 (cxb_ap3 _ _ HP5) (cxb_ap4 _ _ HP5)
      HL5 (Permutation_refl _)).
    - rewrite Eab5. apply Permutation_refl.
    - lia.
    - apply Hrm5. exact Hroom3. }
  assert (HRS4 : crs_regsat_B regs5 (crs_rs_B C sp2)) by exact (cxb_regsat_ap _ _ _ HP5 (crs_rs_cs_B C sp2) HRS3).
  assert (R23c : getr regs5 23 = w64 (crs_cnt1_B C)).
  { rewrite (cxb_ap _ _ 23%bv HP5) by (change (bv_unsigned (23%bv : bv 5)) with 23; unfold acallee_saved; lia).
    rewrite Q23. reflexivity. }
  clear HW2 HW3 HJ HJ15 HS SHOK HEI HRS2 HRS3 Q1 Q3 Q4 Q23 Hm1 Hsp Hs0 Hch A55 A35 A36 A42 G2 G8 ch1.
  clear dependent ms. clear dependent mat.
  (* ---- from +548 by hand: the memory is only read. The stretch is a plain SRr run (the hand steps and the djb2
     loop make no call) whose post is the walk's goal at R: lifted once by YA0nH.SRr_SRrG and SRrG_bind; each exit
     to X2 closes with SRr_ret ---- *)
  lazymatch goal with |- SRrG _ _ _ _ ?Q =>
    apply (SRrG_bind SEGS R Rt _ _ (fun W' c' => SRrG SEGS R W' c' Q));
      [apply (SRr_SRrG SEGS R Rw) | intros W' c' _ HG'; exact HG'] end.
  replace (BASE + 3128) with (BASE + (CRS_PC0_B + 548)) by (vm_compute; reflexivity).
  lazymatch goal with |- SRr _ _ ?c _ => change c with (crs_cfg_B fxk (BASE + (CRS_PC0_B + 548)) regs5 mem5 md5) end.
  destruct HW4 as (HBh & HL5' & HPm5 & Hpk5 & Hro5 & HD5 & HT5).
  pose proof (crs_rs_get_B C sp2 _ HRS4) as (_ & _ & _ & _ & _ & _ & _ & _ & G20 & G21 & _).
  unfold cSize_B in G20.
  pose proof (h2_pre_facts CTX0 C HPRE) as (Hsz' & Hd0' & Hd62'). unfold cSize_B in Hsz', Hd62'.
  assert (HK1 : crs_regsat_B regs5 (h2_keep0 C sp2)).
  { unfold crs_regsat_B, h2_keep0. apply Forall_app. split; [exact HRS4|].
    constructor; [exact R23c|]. constructor; [exact Hc05|]. constructor. }
  (* the boundary facts X2 asks, at any register file and model of this stretch *)
  assert (HLX : crs_live_B B C ly5 S3 Hp3 W5 mem5 Lam3 peak3 (crs_cnt1_B C + cN1_B C) 0 (crs_evs_at_X2_B C)).
  { split; [|exact HPm5]. split; [exact HL5'|]. split; [lia|]. split; [rewrite Hran0; reflexivity|].
    split; [lia|]. split; [lia|]. split; [exact Hro5|]. exact Hpos. }
  (* +548 lui a1, 1 *)
  hfd (CRS_PC0_B + 548) Hl Hd.
  eapply (h_lui W5 fxk regs5 mem5 md5 _ (CRS_PC0_B + 548) (CRS_PC0_B + 552) _ _ _ (w64 4096) Hl Hd);
    [reflexivity | apply bv_eq; vm_compute; reflexivity | lia | lia |].
  hpost. hb_upd HBh. hrs_upd HK1.
  (* +552 addiw a2, a1, 1285: a2 = 5381 *)
  clear Hl Hd. hfd (CRS_PC0_B + 552) Hl Hd.
  eapply (h_addiw W5 fxk _ mem5 _ _ (CRS_PC0_B + 552) (CRS_PC0_B + 556) _ _ _ _ (w64 5381) Hl Hd);
    [reflexivity | hcanon; hgetr; apply bv_eq; vm_compute; reflexivity | lia | lia |].
  hpost. hb_upd HBh. hrs_upd HK1.
  (* +556 beqz s4: size = 0 -> X2 (+664) *)
  clear Hl Hd. hfd (CRS_PC0_B + 556) Hl Hd.
  eapply (h_br W5 fxk _ mem5 _ _ (CRS_PC0_B + 556) (CRS_PC0_B + 664) (CRS_PC0_B + 560) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. hz. rewrite G20.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_eq in Hb2.
    assert (Etb : cb_tb C = []) by (destruct (cb_tb C); [reflexivity | cbn [length] in Hb2; lia]).
    hb_upd HBh. change (BASE + (CRS_PC0_B + 664)) with (BASE + CRS_PC_X2_B).
    apply SRr_ret. refine (KcX2 fxk ly5 S3 Hp3 W5 _ mem5 _ (k + k2 + k3) sp2 Lam3 peak3 Hdoc HBh _ HLX HD5 HT5).
    apply h2_regsat_x2_0; [exact HK1 | hgetr; unfold cHash_B; rewrite Etb; reflexivity].
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. hz. rewrite G20.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_neq in Hb2.
    hb_upd HBh.
    (* +560 sltu a3, zero, s5: a3 = 1 (data > 0) *)
    clear Hl Hd. hfd (CRS_PC0_B + 560) Hl Hd.
    eapply (h_sltu W5 fxk _ mem5 _ _ (CRS_PC0_B + 560) (CRS_PC0_B + 564) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. hz. rewrite G21, hw_sltu0 by lia. hb_upd HBh. hrs_upd HK1.
    (* +564 mv a4, s5; +568 mv a1, s5; +572 mv a5, s4 *)
    clear Hl Hd. hfd (CRS_PC0_B + 564) Hl Hd.
    eapply (h_addi W5 fxk _ mem5 _ _ (CRS_PC0_B + 564) (CRS_PC0_B + 568) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. rewrite G21. hb_upd HBh. hrs_upd HK1.
    clear Hl Hd. hfd (CRS_PC0_B + 568) Hl Hd.
    eapply (h_addi W5 fxk _ mem5 _ _ (CRS_PC0_B + 568) (CRS_PC0_B + 572) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. rewrite G21. hb_upd HBh. hrs_upd HK1.
    clear Hl Hd. hfd (CRS_PC0_B + 572) Hl Hd.
    eapply (h_addi W5 fxk _ mem5 _ _ (CRS_PC0_B + 572) (CRS_PC0_B + 576) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. rewrite G20. hb_upd HBh. hrs_upd HK1.
    (* THE LOOP L2 (PRW_CrcGen.djb_loop with h2_iter) *)
    eapply SRr_bind.
    { apply (djb_loop (fx := fxk) SEGS (BASE + (CRS_PC0_B + 576)) (BASE + (CRS_PC0_B + 664)) 12%bv 15%bv [11%bv; 14%bv]
        (cb_data C) (cb_tb C) (h2_J CTX0 C fxk ly5 S3 Hp3 W5 mem5 (k + k2 + k3) sp2)).
      - intros i W c Hi Hh. exact (h2_iter CTX0 C fxk ly5 S3 Hp3 W5 mem5 (k + k2 + k3) sp2 i W c Hi Hh).
      - destruct (cb_tb C) as [|b0 tb0] eqn:Etb; [cbn [length] in Hb2; lia | cbn [length]; lia].
      - unfold djb_head. lazymatch goal with |- context [crs_cfg_B _ _ ?r _ ?m] => exists r, mem5, m end.
        split; [reflexivity|]. split; [lia|].
        split; [hgetr; reflexivity|]. split; [hgetr; f_equal; lia|].
        split; [apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_nil|].
        pose proof HD5 as (HD1 & _ & HD3 & _).
        split; [exact HD1|]. split; [exact HD3|].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact HBh|].
        unfold h2_keep. apply h_regsat_app.
        + exact HK1.
        + apply Forall_cons; [cbn [fst snd]; hgetr; reflexivity | apply Forall_nil]. }
    cbv beta. intros W' c' _ Hhead.
    destruct (djb_exit_hash (fx := fxk) SEGS _ _ _ _ _ _ _ _ _ Hhead) as (regs6 & mem6 & md6 & -> & H12 & _ & _ & HJ6).
    destruct HJ6 as (-> & -> & HB6 & HR6).
    change (cfg_at (fx := fxk) SEGS (BASE + (CRS_PC0_B + 664)) regs6 mem5 md6)
      with (crs_cfg_B fxk (BASE + CRS_PC_X2_B) regs6 mem5 md6).
    apply SRr_ret. refine (KcX2 fxk ly5 S3 Hp3 W5 regs6 mem5 md6 (k + k2 + k3) sp2 Lam3 peak3 Hdoc HB6 _ HLX HD5 HT5).
    apply h2_regsat_x2; [exact HR6 | exact H12].
Qed.

End f.
End d.

Set Printing Implicit.
About crs_seg_H2_B.
Unset Printing Implicit.
Print Assumptions crs_seg_H2_B.
