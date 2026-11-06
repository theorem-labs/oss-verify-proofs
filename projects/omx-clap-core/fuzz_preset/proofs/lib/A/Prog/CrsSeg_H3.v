(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 584 of its 656 lines of code are new or changed and 856 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsSeg_H1.v, with its numbers changed; 224 of its 709 lines of code are new or changed and 171 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins): segment H3 of the walk of check_reject_clean_starved (row CR-H3, h-w6u-rep's
   subagent CrsX3H3). Closing lemma crs_seg_H3 : the kit's crs_from_H3 (A' +1004 = 0x8254c .. +1092 = 0x825a4 = X3),
   from fuzz_alloc_count's text (HT_fuzz_alloc_count), the kit's transport record (HK : CrsKeep) and the continuation
   crs_from_X3. THE SEGMENT (the internal file crcs-Aprime.lst :252-273):
     +1004 jal fuzz_alloc_count (a0 = the count, crs_cnt2 + N0; the runner to the call, CrsSeg_X3.x3_acc_call);
     +1008 lui a1, 1; +1012 addiw a2, a1, 1285 (a2 = 5381); +1016 beqz s4 (size = 0) -> +1092 = X3;
     +1020 mv a1, s5; the loop L3 +1024 .. +1068 (it EATS s4 and s5: the shadow byte of a1 by `srli; add s11; lb`,
     `bnez` -> +1076 slow path `andi a4, a1, 7; blt a4, a3` -> +1040 or the report arm +1084 / +1088 (refuted: saddr_ok
     of the byte by PRW_CrcGen.djb_byte_shadow); then a2 = 33 a2 + byte, s4 -= 1, a1 += 1, s5 += 1, `bnez s4` ->
     +1024); +1072 j -> +1092 = X3.
   THE LOOP cites PRW_CrcGen.djb_loop with this file's one-iteration step h3_iter. Its memory facts at the state after
   the call: the bytes by CrsSeg_X3.x3_bytes_keep, the shadow by the kit's kp_home_sh at the reader's home moved by
   kp_home_move (the home is below alloc_ceiling: h3_home_ceil).
   THE HAND-STEP KIT (section d below, the h_ and hw_ lemmas) is restated from lane CrsX1H1's lib/A/Prog/CrsSeg_H1.v
   (cold/h-w6u-rep-p102-CR-X1 1c8cfa6aba13, :74-178, :191-381, :391-439), itself after lane CnoA102fA's
   lib/A/Prog/Cno102A_FA.v cfa_step and the cfa_hs_ steps (cold/h-rw-pre-5-cno102a-f 574c27759c8).
   rule 24: proves function check_reject_clean_starved (reuse search: `proof-index check_reject_clean_starved 0x82160`, the internal file
   index-crcs-Aprime.out, and an internal record of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B,
   its released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for check_reject_clean_starved).
   INPUTS: pin A' asan sha256 1be0f53d96cb9d6c (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
   listing lib/A/Listing_prog.v + lib/A/PAImg_prog.v (listings v3 of kit v2); the texts tfuzz_alloc_count_specX
   (lib/A/PRH_FnAlloc.v) and tcheck_reject_clean_starved_specX (lib/A/PRH_FnCheck.v blob 0d50b048d570, kit
   8f227302a137, then f97c8b2f046b by path in kit v4); kit lib/A/Prog/CrsKitAp.v v4 (kit commit 3adfdcc651aa:
   the ledger carries g_most and g_own_ran_out; crs_from_* conclude crs_post; fpre's frm_zero is
   supplied at fuzz_alloc_count's call by CrsSeg_X3.x3_call from crs_baseR).
   THE WORLD RELATION. Every boundary of H3 is after a free or a realloc: the kit's crs_from_H3 / crs_from_X3 take
   crs_baseR at R := wle' SEGS RZ_cf and conclude SRr' (YA0nH, SRrG at R). The run to the call is YC1fPx.paj_run_xR
   and CrsSeg_X3.x3_acc_call at R; from +1008 the hand steps and the loop are a plain SRr stretch whose post is the
   goal at R (LIFT), and each exit to X3 closes by SRr_ret.
   Numerals: offsets +1004 .. +1092 (LENGTH: 4 * slot); 5381, 4096, 1285, 33, 32, 8, 7, 3, 5 (WORD: djb2's seed and
   multiplier, the shift amounts and granule mask the listing's words carry); 2 ^ 20 .. 2 ^ 64 (LENGTH / WORD bounds).
   No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp WriterApp WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_WalkEnv PRW_CrsModel PRW_CrcGen CrsKitAp CrsWexAp CrsSeg_X3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* the import closure leaves lia's division / modulo conversion off (the flag below); this file's arithmetic over
   bv_half_modulus (= bv_modulus / 2) and x / 8 needs it, so it is on for this file only *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- the hand-step kit's word arithmetic and register facts (CrsSeg_H1.v :74-178, restated) ---- *)
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
Lemma hw_lb : forall (b : byte), 0 <= bv_unsigned b < 128 -> v_lb b = w64 (bv_unsigned b).
Proof.
intros b Hb. unfold v_lb, w64, bv_signed. f_equal.
apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma hw_lbu : forall (b : byte), Z_to_bv 64 (bv_unsigned b) = w64 (bv_unsigned b).
Proof. reflexivity. Qed.

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

Lemma h_regsat_get : forall regs l (r : bv 5) v, crs_regsat regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma h_regsat_upd : forall regs l (r : bv 5) w, Forall (fun p : bv 5 * Z => bv_eqb (fst p) r = false) l ->
  crs_regsat regs l -> crs_regsat (regupd regs r w) l.
Proof.
intros regs l r w Hn H. unfold crs_regsat in *. rewrite Forall_forall in *. intros p Hp.
rewrite h_getr_other by exact (Hn p Hp). exact (H p Hp).
Qed.
Lemma h_regsat_app : forall regs l1 l2, crs_regsat regs l1 -> crs_regsat regs l2 -> crs_regsat regs (l1 ++ l2).
Proof. intros regs l1 l2 H1 H2. unfold crs_regsat in *. apply Forall_app. split; assumption. Qed.
Lemma h_regsat_incl : forall regs l l', crs_regsat regs l -> incl l' l -> crs_regsat regs l'.
Proof.
intros regs l l' H Hi. unfold crs_regsat in *. apply Forall_forall. intros p Hp.
exact (proj1 (Forall_forall _ _) H p (Hi p Hp)).
Qed.
Ltac hin := cbn [app In]; repeat (first [left; reflexivity | right]).
Ltac hnot := cbn [app]; repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil.

(* ======================================================================================================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PL := (PL_prog_A).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).

(* ---- the hand steps over crs_cfg (Cno102A_FA.v cfa_step / cfa_hs_*, at the kit's configuration) ---- *)
Lemma h_base : 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64.
Proof. pose proof (@pa_B_ok _ _ PA) as (H0 & H1 & _). split; assumption. Qed.
Lemma h_pc0 : 0 <= CRS_PC0 < 2 ^ 20.
Proof.
assert (E : CRS_PC0 = ltac:(let v := eval vm_compute in CRS_PC0 in exact v)) by (vm_compute; reflexivity).
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
  (forall X, SRr SEGS W (crs_cfg fxk pc' regs' mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk pc regs mem md) Q.
Proof.
intros W fxk regs mem md regs' pc pc' Q Hst HK. unfold crs_cfg, w64.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk); exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold crs_cfg, w64 in HK. exact HK.
Qed.

Definition HSLOT (k : Z) : option (pinstr asym) := YP0a.plookup A_prog_tpi k.
Lemma h_fetch : forall k w, HSLOT k = Some (PW w) -> fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof. intros k w H. exact (@pa_fetch_pw rc _ PL_prog_A PA k w H). Qed.

Lemma h_addi : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_addi fxk SEGS regs _ _ _ _ rd rs imm (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_lui : forall (W : world SEGS) fxk regs mem md Q k k' w rd imm v,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Lui rd imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> v_lui (bv_signed imm ≪ 12) = v -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd v) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd imm v Hl Hd Hrd Hv Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd v) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_lui_at fxk SEGS regs _ _ _ _ rd imm v (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
rewrite (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_addiw : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm v,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (OpImm32 rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> v_addiw (getr regs rs) (bv_signed imm) = v -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd v) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs imm v Hl Hd Hrd Hv Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd v) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_addiw_at fxk SEGS regs _ _ _ _ rd rs imm v (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
rewrite (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_srli : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs sh,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs sh Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_srli fxk SEGS regs _ _ _ _ rd rs sh (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_slli : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs sh,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs sh Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_slli fxk SEGS regs _ _ _ _ rd rs sh (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_add : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs1 rs2,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs1 rs2 Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_add fxk SEGS regs _ _ _ _ rd rs1 rs2 (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.

Lemma h_andi : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs imm,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd (v_andi (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
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
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd (v_lb b)) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
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
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + k') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
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
   forall X, SRr SEGS W (crs_cfg fxk (BASE + kt) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = false ->
   forall X, SRr SEGS W (crs_cfg fxk (BASE + kf) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
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
  (forall X, SRr SEGS W (crs_cfg fxk (BASE + kt) regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k kt w rd imm Hl Hd Hrd Hk -> Hkt HK.
apply (h_step W fxk regs mem md regs (BASE + k) (BASE + (k + bv_signed imm)) Q); [|exact HK].
rewrite (@step_jal_link fxk SEGS regs _ _ _ _ rd imm (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd. unfold btgt. rewrite (h_pcn k (bv_signed imm)) by lia. reflexivity.
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
(* the boundary facts of this walk: every boundary of H3 is after a free or a realloc, so crs_baseR at the re-hiding
   relation wle' SEGS RZ_cf *)
#[local] Notation BASEp CTX0 C :=
  (@crs_baseR fx rc ci cp RL SK B ARx (wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_A) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_A)).

(* crs_base at the next register file and the materialised model, when gp and tp are kept *)
Lemma h_base_step : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X,
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  getr regs' 3%bv = getr regs3 3%bv -> getr regs' 4%bv = getr regs3 4%bv ->
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs' mem3 (with_vm_backing (m_vm_lazy md3) X md3) k sp2.
Proof.
intros CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X HB E3 E4.
destruct HB as (HP & Hz & Hk & HJ & HF & HSV & HSL & HRO & HMN & R3 & R4 & Hsp).
split; [exact HP|]. split; [exact Hz|]. split; [exact Hk|].
split; [unfold crs_JR in *;
  exact (ajournal_x_materializeR SEGS B prh_pst ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ)|].
split; [exact HF|]. split; [exact HSV|]. split; [exact HSL|]. split; [exact HRO|]. split; [exact HMN|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact Hsp.
Qed.

(* the facts of crs_pre the stretch uses *)
Lemma h_pre_facts : forall CTX0 C, crs_pre (fx := fx) B ARx CTX0 C ->
  cSize C <= 3 * 2 ^ 20 /\ 0 < c_data C /\ c_data C + cSize C < 2 ^ 62 /\ 0 <= c_took C <= 2 * cSize C + 2 /\
  c_ran C = 0.
Proof.
intros CTX0 C H. unfold crs_pre in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _ & _ & H4 & _ & _ & _ & _ & Hran & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact Hran].
split; [lia|]. apply (Z.le_trans _ _ _ (proj2 H4)). unfold ck_ncalls, cSize.
pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod (c_tb C) []) as G. unfold PjGrammar.ncalls. lia.
Qed.

(* ---- the reader's home is below alloc_ceiling: a ledger block, a read-only image range, or an allocator block ---- *)
Lemma h3_home_ceil : forall ly S Hp W mem md Lam peak cnt fail ran most own p n,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  PRH_FnReader.prhReader_home B ly S Hp Lam p n -> 0 <= n -> p + n <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n HAR HL Hh Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cf_head_nonneg as Ch.
destruct Hh as [[(b & m & Hin & Hb & Hm) | [(_ & _ & Htop & _) | (_ & Htop & _)]] | (b & m & Hin & _ & Hb & Hm)].
- pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) as HF. rewrite Forall_forall in HF.
  destruct (HF (b, m) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hc & _).
  unfold req_size in Hc. destruct (Z.eqb_spec (m + cf_head) 0); lia.
- lazymatch type of Htop with _ <= ?h => assert (h <= 0x600000) by (vm_compute; discriminate) end. lia.
- lazymatch type of Htop with _ <= ?h => assert (h <= 0x600000) by (vm_compute; discriminate) end. lia.
- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc & _).
  unfold req_size in Hc. destruct (Z.eqb_spec m 0); lia.
Qed.

(* ---- the registers: at H3 (the kit's list), and the loop's kept list (s4, s5 eaten; a0 = the count) ---- *)
Definition h3_regs (C : crsC) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro ++ [(23%bv, crs_cnt2 C)].
Definition h3_keep (C : crsC) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rbase C sp2 ++ crs_rsh C ++ [(19%bv, c_doc C)] ++ crs_rlive C ++ crs_rro ++
  [(23%bv, crs_cnt2 C); (10%bv, crs_cnt2 C + cN0 C)].

Local Ltac h3_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.
Local Ltac h3_te_close :=
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let nn := eval vm_compute in n in
    lazymatch eval vm_compute in (Nat.ltb nn 32) with
    | true => apply (te_entry r0 rc mo _ nn); reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
      | true => let kk := eval vm_compute in (Nat.sub nn 32) in apply (te_cur r0 rc mo _ kk); reflexivity
      | false => let j := eval vm_compute in (Nat.sub nn 64) in rewrite (te_more_lt r0 rc mo j) by lia; reflexivity
      end
    end
  end.
Local Ltac h3_keepr HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; h3_te_close end.
Local Ltac h3_in := cbv [h3_regs h3_keep crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In]; tauto.

(* the registers of h3_regs are callee-saved: a call keeps them *)
Lemma h3_regs_pres : forall (regs regs2 : bvmap 5 word) C sp2,
  crs_regsat regs (h3_regs C sp2) -> aregs_preserved regs regs2 -> crs_regsat regs2 (h3_regs C sp2).
Proof.
intros regs regs2 C sp2 H HP. unfold crs_regsat in *. rewrite Forall_forall in *. intros p Hp.
rewrite <- (H p Hp). cbv [h3_regs crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In] in Hp.
repeat (destruct Hp as [<- | Hp]; [cbn [fst]; apply (x3_ap regs regs2 _ HP); h3_cs |]). destruct Hp.
Qed.

(* ---- the loop L3: its head invariant J (the world and memory after the call, crs_base at the current register
   file and model, the registers the loop keeps) and its one-iteration step ---- *)
Definition h3_J (CTX0 : list (list Z)) (C : crsC) (fxk : YK11.FPState) (ly3 : alayout) (S3 : astate)
  (Hp3 : list Z) (W3 : world SEGS) (mem3 : word -> option byte) (k sp2 : Z)
  : world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun W regs mem md => W = W3 /\ mem = mem3 /\ BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs mem3 md k sp2 /\
    crs_regsat regs (h3_keep C sp2).

Ltac hb_upd HB :=
  lazymatch goal with |- SRr _ _ (crs_cfg _ _ ?r _ (with_vm_backing (m_vm_lazy ?m) ?X ?m)) _ =>
    let H' := fresh "HB'" in
    pose proof (h_base_step _ _ _ _ _ _ _ _ r _ _ _ _ X HB ltac:(hgetr; reflexivity) ltac:(hgetr; reflexivity)) as H';
    clear HB; rename H' into HB end.
Ltac hrs_upd HR :=
  lazymatch goal with
  | |- SRr _ _ (crs_cfg _ _ (regupd ?rg ?rr ?v) _ _) _ =>
    let l := lazymatch type of HR with crs_regsat _ ?l => l end in
    let H' := fresh "HR'" in
    pose proof (h_regsat_upd rg l rr v
      ltac:(unfold h3_keep, crs_rbase, crs_rsh, crs_rargs, crs_rlive, crs_rro; hnot) HR) as H';
    clear HR; rename H' into HR
  | _ => idtac end.
Ltac hpost := intros; hcanon; hsig; rewrite ?h_vaddi0; hgetr.

Lemma h3_iter : forall CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2 i W c,
  (i < length (c_tb C))%nat ->
  djb_head (fx := fxk) SEGS (BASE + (CRS_PC0 + 1024)) 12%bv 20%bv [11%bv; 21%bv] (c_data C) (c_tb C)
    (h3_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) i W c ->
  SRr SEGS W c (djb_head (fx := fxk) SEGS
    (if (S i <? length (c_tb C))%nat then BASE + (CRS_PC0 + 1024) else BASE + (CRS_PC0 + 1092))
    12%bv 20%bv [11%bv; 21%bv] (c_data C) (c_tb C) (h3_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) (S i)).
Proof.
intros CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2 i W c Hi (regs & mem & md & -> & Hle & Hh & Hc & Hps & Hg & Hra & HJ).
destruct HJ as (-> & -> & HBs & HRs).
pose proof h_pc0 as HPC.
pose proof (Forall_inv Hps) as Ha1. pose proof (Forall_inv (Forall_inv_tail Hps)) as Ha21. cbv beta in Ha1, Ha21.
pose proof (h_pre_facts CTX0 C (proj1 HBs)) as (Hsz & Hd0 & Hd62 & _ & _).
unfold cSize in Hsz, Hd62.
set (x := c_tb C) in *. set (d := c_data C) in *.
set (n := Z.of_nat (length x)) in *.
set (h := ck_djb2 5381 (firstn i x)) in *.
assert (Hhr : 0 <= h < 2 ^ 64) by apply djb_hash_range.
assert (G27 : getr regs 27%bv = w64 SHADOW_OFF)
  by (apply (h_regsat_get regs (h3_keep C sp2)); [exact HRs | unfold h3_keep, crs_rbase; hin]).
(* the shadow byte of the next byte, and the byte *)
destruct (djb_byte_shadow _ _ d n (Z.of_nat i) Hra ltac:(lia)) as (s & Hs & Hsok).
pose proof (s10_aview_byte _ _ _ _ _ Hs) as Hs256.
destruct (h_rdn1 SEGS (w_H W3) mem3 _ s Hs) as (bs & Hrbs & Hbs).
destruct (djb_byte SEGS (mrestrict (w_H W3) mem3) d x i Hg Hi) as (Hmb & Hc256).
pose proof (h_rdn1_mb SEGS _ _ _ Hmb) as Hrc.
set (cc := nth i x 0) in *.
assert (Hs8 : s = 0 \/ (0 < s < 8 /\ (d + Z.of_nat i) mod 8 < s)) by (unfold saddr_ok in Hsok; lia).
change (cfg_at (fx := fxk) SEGS (BASE + (CRS_PC0 + 1024)) regs mem3 md)
  with (crs_cfg fxk (BASE + (CRS_PC0 + 1024)) regs mem3 md).
(* +1024 srli a3, a1, 3 *)
hfd (CRS_PC0 + 1024) Hl Hd.
eapply (h_srli W3 fxk regs mem3 md _ (CRS_PC0 + 1024) (CRS_PC0 + 1028) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite Ha1, hw_srli3 by lia. hb_upd HBs. hrs_upd HRs.
(* +1028 add a3, a3, s11 *)
clear Hl Hd. hfd (CRS_PC0 + 1028) Hl Hd.
eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0 + 1028) (CRS_PC0 + 1032) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
assert (H8 : 0 <= (d + Z.of_nat i) / 8 < 2 ^ 64)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (HSO : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
hpost. rewrite G27. rewrite (hw_add _ _ H8 HSO).
hb_upd HBs. hrs_upd HRs.
(* +1032 lb a3, 0(a3): the shadow byte s *)
clear Hl Hd. hfd (CRS_PC0 + 1032) Hl Hd.
eapply (h_lb W3 fxk _ mem3 _ _ (CRS_PC0 + 1032) (CRS_PC0 + 1036) _ _ _ _ bs Hl Hd); [reflexivity | lia | lia | |].
{ hcanon. hsig. hgetr. rewrite h_vaddi0.
  replace ((d + Z.of_nat i) / 8 + SHADOW_OFF) with (shadow_of_addr SHADOW_OFF (d + Z.of_nat i))
    by (unfold shadow_of_addr; lia).
  exact Hrbs. }
hpost. rewrite hw_lb by lia. rewrite Hbs. hb_upd HBs. hrs_upd HRs.
(* +1036 bnez a3: s = 0 falls through to +1040; else the slow path +1076 *)
clear Hl Hd. hfd (CRS_PC0 + 1036) Hl Hd.
(* the common tail from +1040 (both arms reach it) *)
assert (TAIL : forall regsT mdT,
  getr regsT 11%bv = w64 (d + Z.of_nat i) -> getr regsT 21%bv = w64 (d + Z.of_nat i) ->
  getr regsT 12%bv = w64 h -> getr regsT 20%bv = w64 (n - Z.of_nat i) ->
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regsT mem3 mdT k sp2 -> crs_regsat regsT (h3_keep C sp2) ->
  SRr SEGS W3 (crs_cfg fxk (BASE + (CRS_PC0 + 1040)) regsT mem3 mdT)
    (djb_head (fx := fxk) SEGS
      (if (S i <? length x)%nat then BASE + (CRS_PC0 + 1024) else BASE + (CRS_PC0 + 1092))
      12%bv 20%bv [11%bv; 21%bv] d x (h3_J CTX0 C fxk ly3 S3 Hp3 W3 mem3 k sp2) (S i))).
{ clear dependent regs. intros regsT mdT T11 T21 T12 T20 HBt HRt.
  (* +1040 slli a3, a2, 5 *)
  clear Hl Hd. hfd (CRS_PC0 + 1040) Hl Hd.
  eapply (h_slli W3 fxk regsT mem3 mdT _ (CRS_PC0 + 1040) (CRS_PC0 + 1044) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T12, hw_slli5 by lia. hb_upd HBt. hrs_upd HRt.
  (* +1044 lbu a4, 0(s5) *)
  clear Hl Hd. hfd (CRS_PC0 + 1044) Hl Hd.
  eapply (h_lbu W3 fxk _ mem3 _ _ (CRS_PC0 + 1044) (CRS_PC0 + 1048) _ _ _ _ (Z_to_bv 8 cc) Hl Hd);
    [reflexivity | lia | lia | |].
  { hcanon. hsig. hgetr. rewrite T21, h_vaddi0. exact Hrc. }
  hpost. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia).
  change (Z_to_bv 64 cc) with (w64 cc). hb_upd HBt. hrs_upd HRt.
  (* +1048 add a2, a3, a2 *)
  clear Hl Hd. hfd (CRS_PC0 + 1048) Hl Hd.
  eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0 + 1048) (CRS_PC0 + 1052) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T12, hw_add_m. hb_upd HBt. hrs_upd HRt.
  (* +1052 addi s4, s4, -1 *)
  clear Hl Hd. hfd (CRS_PC0 + 1052) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0 + 1052) (CRS_PC0 + 1056) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T20, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* +1056 addi a1, a1, 1 *)
  clear Hl Hd. hfd (CRS_PC0 + 1056) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0 + 1056) (CRS_PC0 + 1060) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T11, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* +1060 add a2, a2, a4 *)
  clear Hl Hd. hfd (CRS_PC0 + 1060) Hl Hd.
  eapply (h_add W3 fxk _ mem3 _ _ (CRS_PC0 + 1060) (CRS_PC0 + 1064) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite hw_add_m. hb_upd HBt. hrs_upd HRt.
  (* +1064 addi s5, s5, 1 *)
  clear Hl Hd. hfd (CRS_PC0 + 1064) Hl Hd.
  eapply (h_addi W3 fxk _ mem3 _ _ (CRS_PC0 + 1064) (CRS_PC0 + 1068) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite T21, hw_addi by lia. hb_upd HBt. hrs_upd HRt.
  (* the head facts at S i *)
  assert (Eh : w64 (32 * h + h + cc) = w64 (ck_djb2 5381 (firstn (S i) x))).
  { apply hw_eq. rewrite (djb_hash_step x i Hi). fold h. fold cc. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite Eh. rewrite Eh in HRt.
  (* +1068 bnez s4 *)
  clear Hl Hd. hfd (CRS_PC0 + 1068) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0 + 1068) (CRS_PC0 + 1024) (CRS_PC0 + 1072) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  - (* taken: s4 <> 0, bytes remain, back to the head *)
    intros Hb ?. revert Hb. hcanon. hgetr. rewrite ?getr_zero. change (Z_to_bv 64 0) with (w64 0).
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
  - (* not taken: the last byte; +1072 j -> +1092 *)
    intros Hb ?. revert Hb. hcanon. hgetr. rewrite ?getr_zero. change (Z_to_bv 64 0) with (w64 0).
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply negb_false_iff, Z.eqb_eq in Hb.
    assert (Hge : length x = S i) by (unfold n in *; lia).
    rewrite Hge, Nat.ltb_irrefl.
    hb_upd HBt.
    clear Hl Hd. hfd (CRS_PC0 + 1072) Hl Hd.
    eapply (h_j W3 fxk _ mem3 _ _ (CRS_PC0 + 1072) (CRS_PC0 + 1092) _ _ _ Hl Hd); [reflexivity | lia | reflexivity | lia |].
    intros ?. hb_upd HBt. apply SRr_ret.
    lazymatch goal with HBt : BASEp _ _ _ _ _ _ _ ?rr _ ?mm _ _ |- _ =>
      exists rr, mem3, mm end.
    split; [reflexivity|]. split; [lia|].
    split; [hgetr; reflexivity|]. split; [hgetr; f_equal; unfold n in *; lia|].
    split; [apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_cons; [hgetr; f_equal; lia|]; apply Forall_nil|].
    split; [exact Hg|]. split; [exact Hra|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HBt|]. exact HRt. }
eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0 + 1036) (CRS_PC0 + 1076) (CRS_PC0 + 1040) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
- (* taken: s <> 0, the slow path *)
  intros Hb ?. revert Hb. hcanon. hgetr. rewrite ?getr_zero. change (Z_to_bv 64 0) with (w64 0).
  cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply negb_true_iff, Z.eqb_neq in Hb.
  destruct Hs8 as [Hs0 | (Hs08 & Hsm)]; [exfalso; exact (Hb Hs0)|].
  hb_upd HBs.
  (* +1076 andi a4, a1, 7 *)
  clear Hl Hd. hfd (CRS_PC0 + 1076) Hl Hd.
  eapply (h_andi W3 fxk _ mem3 _ _ (CRS_PC0 + 1076) (CRS_PC0 + 1080) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
  hpost. rewrite Ha1, hw_andi7 by lia. hb_upd HBs. hrs_upd HRs.
  (* +1080 blt a4, a3: taken (the byte is inside the granule's valid prefix) -> +1040; the report arm +1084 refuted *)
  clear Hl Hd. hfd (CRS_PC0 + 1080) Hl Hd.
  eapply (h_br W3 fxk _ mem3 _ _ (CRS_PC0 + 1080) (CRS_PC0 + 1040) (CRS_PC0 + 1084) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  + intros _ ?. hcanon. hb_upd HBs.
    apply TAIL; [hgetr; exact Ha1 | hgetr; exact Ha21 | hgetr; exact Hh | hgetr; exact Hc | exact HBs | exact HRs].
  + intros Hb2 ?. exfalso. revert Hb2. hcanon. hgetr. cbn [branch_taken].
    rewrite hw_lts by (pose proof (Z.mod_pos_bound (d + Z.of_nat i) 8); lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hsm). discriminate.
- (* not taken: s = 0, the fast path *)
  intros Hb ?. hcanon. hb_upd HBs.
  apply TAIL; [hgetr; exact Ha1 | hgetr; exact Ha21 | hgetr; exact Hh | hgetr; exact Hc | exact HBs | exact HRs].
Qed.

(* ==== CR-H3: the closing lemma ==== *)
Lemma crs_seg_H3 : forall CTX0 C
  (HT_fuzz_alloc_count : forall fxq, tfuzz_alloc_count_specX (fx := fxq) (rc := rc) (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK)
  (HK : CrsKeep B ARx),
  crs_from_X3 (fx := fx) (rc := rc) B ARx CTX0 C ->
  crs_from_H3 (fx := fx) (rc := rc) B ARx CTX0 C.
Proof.
intros CTX0 C HTC HK HX3. unfold crs_from_H3.
intros fxk ly S Hp W regs mem md k sp2 Lam peak Hdoc HB HRG (HCO & HPM) HDAT HT.
(* the walk's world relation R: the re-hiding relation (the kit's crs_from_H3 / crs_from_X3 take crs_baseR at it and
   conclude SRr' = SRrG at it), its two laws, wle <= R, and the switch of a plain SRr stretch whose post is the goal at
   R (the R form of YGcfRhLift.ra_rh_of_SRr, by YA0nH.SRr_SRrG and SRrG_bind) *)
unfold SRr' in HX3 |- *.
set (R := wle' SEGS YGcfRehidePost.RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS YGcfRehidePost.RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS YGcfRehidePost.RZ_cf).
assert (Rw : forall W W', wle W W' -> R W W') by exact (wle_wle' SEGS YGcfRehidePost.RZ_cf).
assert (LIFT : forall W0 c0 Q0, SRr SEGS W0 c0 (fun W' c' => SRrG SEGS R W' c' Q0) -> SRrG SEGS R W0 c0 Q0).
{ intros W0 c0 Q0 H0. apply (SRrG_bind SEGS R Rt _ _ _ _ (SRr_SRrG SEGS R Rw _ _ _ H0)).
  intros W' c' _ HG'. exact HG'. }
destruct HCO as (HL & Hpk & Hran0 & Hcn & Hc62 & HRL & HPOS).
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof x3_stk as (ESTK & EF0 & EL0 & ER0 & EC0 & EW0).
pose proof crs_frame_is_pi as EFR. unfold CRS_FRAME in EFR, Hs1.
pose proof (h_pre_facts CTX0 C Hpre) as (Hsz & Hd0 & Hd62 & _ & Hcr0).
pose proof HDAT as (HBY & HHOME & HRA0 & HHULL).
assert (HST : x3_st B C (crs_evs_at_H3 C) ly S Hp W mem Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0).
{ split; [exact HL|]. split; [exact Hpk|]. split; [reflexivity|]. split; [exact Hcn|]. split; [exact HRL|].
  split; [exact HPOS|]. split; [exact HPM | split; [exact HBY | exact HT]]. }
assert (E2 : getr regs 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG); h3_in).
assert (E8 : getr regs 8 = w64 (spZ (c_regs C))) by (apply (x3_rget _ _ _ _ HRG); h3_in).
unfold crs_cfg, CRS_PC_H3.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (c_regs C) regs []) (ss_x3 1004)
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0 + 1004))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs [])) by apply te_env.
unfold crs_JR in HJ.
pose (RUN := @paj_run_xR fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
(* +1004 jal fuzz_alloc_count *)
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ss_x3 ss_mem]. apply awr_ok_nil. }
rename HF into HFm. apply frame_of_read_only in HFm; [|vm_compute; reflexivity]. clear HFr HG.
rewrite HFm in HJ.
assert (KR : forall p, In p (h3_regs C sp2) -> getr (ms_regs ms) (fst p) = getr regs (fst p)).
{ intros p Hpp. cbv [h3_regs crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In] in Hpp.
  repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; h3_keepr HS |]). destruct Hpp. }
assert (KR3 : getr (ms_regs ms) 3 = getr regs 3) by h3_keepr HS.
assert (KR4 : getr (ms_regs ms) 4 = getr regs 4) by h3_keepr HS.
prreg HS (1%bv : bv 5) Z1.
assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0 + 1008))).
{ rewrite Z1. f_equal; try (vm_compute; reflexivity). }
assert (HRGm : crs_regsat (ms_regs ms) (h3_regs C sp2)) by exact (x3_regsat_sub regs (ms_regs ms) _ _ HRG (fun p Hp => Hp) KR).
assert (HBm : crs_baseR (fx := fx) B ARx R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md) mat md) k sp2).
{ rewrite HFm. exact (x3_base_md (fx := fx) B ARx R CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms) _ HB HJ KR3 KR4). }
assert (HSTm : x3_st B C (crs_evs_at_H3 C) ly S Hp W (ms_mem ms) Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0)
  by (rewrite HFm; exact HST).
apply (x3_acc_call (fx := fx) B ARx LAWS HK R Rr Rt Rw CTX0 C (crs_evs_at_H3 C) fxk (STK_fuzz_alloc_count (PI := prh_img_A)) 1008
  W _ _ ms _ ly S Hp k sp2 Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0 SIZE_MAXZ
  (fun ly' S' Hp' W' regs' mem' md' =>
     (room_live_cf S -> room_live_cf S') /\
     getr regs' 10 = w64 (crs_cnt2 C + cN0 C) /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
     LEDGER ly' S' Hp' W' mem' Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0 (c_most C) 0)
  _ HS eq_refl HBm).
- rewrite (KR (2%bv, sp2)) by h3_in. exact E2.
- rewrite (KR (8%bv, spZ (c_regs C))) by h3_in. exact E8.
- exact A1.
- lia.
- reflexivity.
- rewrite EC0. lia.
- rewrite EC0, ESTK. unfold CRS_FRAME. rewrite EFR. lia.
- exact HSTm.
- intros ch1 HFPRE.
  exact (HTC fxk ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1 Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0 (c_most C) 0 HFPRE
    ltac:(rewrite HFm; exact HL)).
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 (_ & _ & EHp & ES & EAB & HL2). exact (conj EHp (conj ES (conj EAB HL2))).
- (* after the call (+1008): a0 = the count *)
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HP (_ & R10 & _ & _ & EAB & _) HST2.
  pose proof HB2 as (_ & _ & _ & HJ2 & _). unfold crs_JR in HJ2.
  pose proof HST2 as (HL2 & _ & _ & _ & _ & _ & _ & HBY2 & HT2).
  assert (Hn0 : 0 <= cSize C) by (unfold cSize; lia).
  assert (HHOME2 : PRH_FnReader.prhReader_home B ly2 S2 Hp2 Lam (c_data C) (cSize C)).
  { refine (kp_home_move B ARx HK ly S Hp W mem Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0 (c_most C) 0
      ly2 S2 Hp2 W2 mem2 Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0 (c_most C) 0 (c_data C) (cSize C) HL HL2
      (Permutation_refl _) _ HHOME).
    rewrite EAB. apply Permutation_refl. }
  assert (HRA2 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (c_data C) (cSize C)).
  { destruct (Z.eq_dec (cSize C) 0) as [E0 | Ene].
    - rewrite E0. intros ii Hii. lia.
    - assert (Hceil : c_data C + cSize C <= YM05.alloc_ceiling)
        by exact (h3_home_ceil ly S Hp W mem _ Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0 (c_most C) 0 (c_data C) (cSize C)
                    (ajxR_ar HJ) HL HHOME Hn0).
      exact (proj1 (kp_home_sh B ARx HK ly2 S2 Hp2 W2 mem2 md2 Lam peak (crs_cnt2 C + cN0 C) SIZE_MAXZ 0 (c_most C) 0
        (c_data C) (cSize C) (ajxR_ar HJ2) HL2 HHOME2 ltac:(lia) ltac:(lia) Hceil)). }
  assert (HRG2 : crs_regsat regs2 (h3_regs C sp2)) by exact (h3_regs_pres _ _ C sp2 HRGm HP).
  assert (G20 : getr regs2 20 = w64 (cSize C)) by (apply (x3_rget _ _ _ _ HRG2); h3_in).
  assert (G21 : getr regs2 21 = w64 (c_data C)) by (apply (x3_rget _ _ _ _ HRG2); h3_in).
  assert (HK1 : crs_regsat regs2 (h3_keep C sp2)).
  { apply (h_regsat_incl regs2 (h3_regs C sp2 ++ [(10%bv, crs_cnt2 C + cN0 C)])).
    - apply h_regsat_app; [exact HRG2 | constructor; [exact R10 | constructor]].
    - intros pp Hpp. cbv [h3_regs h3_keep crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In] in *. tauto. }
  unfold cSize in G20, HRA2, Hsz, Hd62.
  change (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRS_PC0 + 1008))) mem2 (YK11.seg_rom SEGS)) md2)
    with (crs_cfg fxk (BASE + (CRS_PC0 + 1008)) regs2 mem2 md2).
  pose proof h_pc0 as HPC.
  clear HS SHOK HEI HJ KR KR3 KR4 Z1 A1 HBm HSTm.
  (* from +1008 by hand: a plain SRr stretch (hand steps and the djb2 loop, no call); each exit to X3 by SRr_ret *)
  apply LIFT.
  (* +1008 lui a1, 1 *)
  hfd (CRS_PC0 + 1008) Hl Hd.
  eapply (h_lui W2 fxk regs2 mem2 md2 _ (CRS_PC0 + 1008) (CRS_PC0 + 1012) _ _ _ (w64 4096) Hl Hd);
    [reflexivity | apply bv_eq; vm_compute; reflexivity | lia | lia |].
  hpost. hb_upd HB2. hrs_upd HK1.
  (* +1012 addiw a2, a1, 1285: a2 = 5381 *)
  clear Hl Hd. hfd (CRS_PC0 + 1012) Hl Hd.
  eapply (h_addiw W2 fxk _ mem2 _ _ (CRS_PC0 + 1012) (CRS_PC0 + 1016) _ _ _ _ (w64 5381) Hl Hd);
    [reflexivity | hcanon; hgetr; apply bv_eq; vm_compute; reflexivity | lia | lia |].
  hpost. hb_upd HB2. hrs_upd HK1.
  (* +1016 beqz s4: size = 0 -> X3 (+1092) *)
  clear Hl Hd. hfd (CRS_PC0 + 1016) Hl Hd.
  eapply (h_br W2 fxk _ mem2 _ _ (CRS_PC0 + 1016) (CRS_PC0 + 1092) (CRS_PC0 + 1020) _ _ _ _ _ Hl Hd);
    [lia | reflexivity | lia | reflexivity | |].
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. rewrite ?getr_zero. change (Z_to_bv 64 0) with (w64 0). rewrite G20.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_eq in Hb2.
    assert (Etb : c_tb C = []) by (destruct (c_tb C); [reflexivity | cbn [length] in Hb2; lia]).
    hb_upd HB2. change (BASE + (CRS_PC0 + 1092)) with (BASE + CRS_PC_X3).
    apply SRr_ret. refine (HX3 fxk ly2 S2 Hp2 W2 _ mem2 _ (k + k1) sp2 Lam peak Hdoc HB2 _ _ HBY2 HT2).
    * apply (h_regsat_incl _ (h3_keep C sp2 ++ [(12%bv, cHash C)])).
      -- apply h_regsat_app; [exact HK1 | constructor; [cbn [fst snd]; hgetr; unfold cHash; rewrite Etb; reflexivity | constructor]].
      -- intros pp Hpp. cbv [h3_keep crs_rbase crs_rsh crs_rlive crs_rro app In] in *. tauto.
    * exact (x3_core_of_st (fx := fx) B ARx CTX0 C (crs_evs_at_H3 C) ly2 S2 Hp2 W2 mem2 Lam peak (crs_cnt2 C + cN0 C) 0
        Hpre HST2 Hc62).
  + intros Hb2 ?. revert Hb2. hcanon. hgetr. rewrite ?getr_zero. change (Z_to_bv 64 0) with (w64 0). rewrite G20.
    cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb2. apply Z.eqb_neq in Hb2.
    hb_upd HB2.
    (* +1020 mv a1, s5 *)
    clear Hl Hd. hfd (CRS_PC0 + 1020) Hl Hd.
    eapply (h_addi W2 fxk _ mem2 _ _ (CRS_PC0 + 1020) (CRS_PC0 + 1024) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
    hpost. rewrite G21. hb_upd HB2. hrs_upd HK1.
    (* THE LOOP L3 (PRW_CrcGen.djb_loop with h3_iter) *)
    eapply SRr_bind.
    { apply (djb_loop (fx := fxk) SEGS (BASE + (CRS_PC0 + 1024)) (BASE + (CRS_PC0 + 1092)) 12%bv 20%bv [11%bv; 21%bv]
        (c_data C) (c_tb C) (h3_J CTX0 C fxk ly2 S2 Hp2 W2 mem2 (k + k1) sp2)).
      - intros i W' c Hi Hh. exact (h3_iter CTX0 C fxk ly2 S2 Hp2 W2 mem2 (k + k1) sp2 i W' c Hi Hh).
      - destruct (c_tb C) as [|b0 tb0] eqn:Etb; [cbn [length] in Hb2; lia | cbn [length]; lia].
      - unfold djb_head. lazymatch goal with |- context [crs_cfg _ _ ?r _ ?m] => exists r, mem2, m end.
        split; [reflexivity|]. split; [lia|].
        split; [hgetr; reflexivity|]. split; [hgetr; rewrite ?G20; f_equal; lia|].
        split; [apply Forall_cons; [hgetr; rewrite ?G21; f_equal; lia|]; apply Forall_cons;
          [hgetr; rewrite ?G21; f_equal; lia|]; apply Forall_nil|].
        split; [exact HBY2|]. split; [exact HRA2|].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact HB2 | exact HK1]. }
    cbv beta. intros W' c' _ Hhead.
    destruct (djb_exit_hash (fx := fxk) SEGS _ _ _ _ _ _ _ _ _ Hhead) as (regs5 & mem5 & md5 & -> & H12 & _ & _ & HJ5).
    destruct HJ5 as (-> & -> & HB5 & HR5).
    change (cfg_at (fx := fxk) SEGS (BASE + (CRS_PC0 + 1092)) regs5 mem2 md5)
      with (crs_cfg fxk (BASE + CRS_PC_X3) regs5 mem2 md5).
    apply SRr_ret. refine (HX3 fxk ly2 S2 Hp2 W2 regs5 mem2 md5 (k + k1) sp2 Lam peak Hdoc HB5 _ _ HBY2 HT2).
    * apply (h_regsat_incl regs5 (h3_keep C sp2 ++ [(12%bv, cHash C)])).
      -- apply h_regsat_app; [exact HR5 | constructor; [exact H12 | constructor]].
      -- intros pp Hpp. cbv [h3_keep crs_rbase crs_rsh crs_rlive crs_rro app In] in *. tauto.
    * exact (x3_core_of_st (fx := fx) B ARx CTX0 C (crs_evs_at_H3 C) ly2 S2 Hp2 W2 mem2 Lam peak (crs_cnt2 C + cN0 C) 0
        Hpre HST2 Hc62).
Qed.

End f.
End d.

Print Assumptions crs_seg_H3.
