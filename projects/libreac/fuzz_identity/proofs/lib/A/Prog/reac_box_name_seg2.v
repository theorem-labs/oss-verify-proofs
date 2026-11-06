(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's ASan build (lib/A). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC1g YC45 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_P2B : Z := 0x1a0.
Definition rbn2_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 112 120 112 120 [];
    YP09.mkRegion (Some 19%nat) 0 24 0 24 [];
    YP09.mkRegion (Some 32%nat) 0 36 0 36 [];
    YP09.mkRegion (Some 8%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition rbn2_facts : facts := mkFacts [] [] [shadow_decl 19 22 32].
Definition ss_rbn2 : sstate := mkSS (AF_reac_box_name + RBN_P2) sr_atoms rbn2_regions None rbn2_facts.
Definition rbn2b_regions : smem := [YP09.mkRegion (Some 8%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]].
Definition ss_rbn2b : sstate := mkSS (AF_reac_box_name + RBN_P2B) sr_atoms rbn2b_regions None (mkFacts [] [] []).
Definition rbn2_keepb (sr : list sv) (cl : list Z) : bool :=
  forallb (fun k => existsb (Z.eqb (Z.of_nat k)) cl || sv_eqb (sr_get sr (Z_to_bv 5 (Z.of_nat k))) (SOff k 0))
    (seq 1 31).
Definition rbn2_ok (name nl token tl dsp dl i o : Z) : Prop :=
  reac_box_name_c.bn_args_ok name nl token tl dsp dl i o = true.
Definition rbn2_shchunk (l : list YP09.chunk) (j v : Z) : bool :=
  existsb (fun c => (YP09.c_off c =? j) &&
    match YP09.c_val c with CVal w e => (N.eqb w 1) && match e with SLit z => z mod 2 ^ 64 mod 256 =? v | _ => false end
    | _ => false end) l.
Lemma rbn2_mod_64_32 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); vm_compute; reflexivity].
Qed.
Lemma rbn2_mod_64_2 : forall z, (z mod 2 ^ 64) mod 2 = z mod 2.
Proof.
intros z. symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 63); vm_compute; reflexivity].
Qed.
Lemma rbn2_args_spec : forall name name_len token token_len display display_len i o,
  reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = true <->
  (name <> 0 /\ token <> 0 /\ display <> 0 /\ name_len <> 0 /\ token_len <> 0 /\ display_len <> 0 /\
   (i = 0 \/ (2 <= i <= 40 /\ i mod 2 = 0)) /\ (o = 0 \/ (2 <= o <= 40 /\ o mod 2 = 0)) /\
   (i <> 0 \/ o <> 0)).
Proof.
assert (Hev : forall x, Z.even x = true <-> x mod 2 = 0).
{ intros x. split.
  - intros H. apply Z.even_spec in H. destruct H as (m & ->). rewrite Z.mul_comm. apply Z_mod_mult.
  - intros H. apply Z.even_spec. exists (x / 2). pose proof (Z.div_mod x 2 ltac:(lia)). lia. }
assert (Hok : forall x, bn_ok x = true <-> (x = 0 \/ (2 <= x <= 40 /\ x mod 2 = 0))).
{ intros x. unfold bn_ok. rewrite orb_true_iff, !andb_true_iff, Z.eqb_eq, !Z.leb_le, Hev. tauto. }
intros name name_len token token_len display display_len i o.
unfold reac_box_name_c.bn_args_ok.
rewrite !andb_true_iff, !negb_true_iff, !Hok, andb_false_iff, !Z.eqb_neq. tauto.
Qed.
Lemma rbn2_accept_false : forall f sd i o name name_len token token_len display display_len,
  reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = false ->
  reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len = false.
Proof.
intros f sd i o name name_len token token_len display display_len H.
unfold reac_box_name_c.bn_accept. rewrite H. reflexivity.
Qed.
Lemma rbn2_eqmod0 : forall v, - 2 ^ 64 < v < 2 ^ 64 -> (v mod 2 ^ 64 =? 0) = (v =? 0).
Proof.
intros v Hv. apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma rbn2_U : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma rbn2_eq0b : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H Hv. rewrite branch_eq_U, (rbn2_U E n v H), U_SLit. change (zcanon 0) with 0.
apply rbn2_eqmod0. exact Hv.
Qed.
Lemma rbn2_eq0_t : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v = 0.
Proof. intros E n v H Hv Hc. rewrite (rbn2_eq0b E n v H Hv) in Hc. apply Z.eqb_eq. exact Hc. Qed.
Lemma rbn2_eq0_f : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v <> 0.
Proof. intros E n v H Hv Hc. rewrite (rbn2_eq0b E n v H Hv) in Hc. apply Z.eqb_neq. exact Hc. Qed.
Lemma rbn2_ne0_t : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v <> 0.
Proof.
intros E n v H Hv Hc. change BC_NE with (neg_bc BC_EQ) in Hc.
rewrite branch_taken_neg, (rbn2_eq0b E n v H Hv) in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq. exact Hc.
Qed.
Lemma rbn2_ne0_f : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v = 0.
Proof.
intros E n v H Hv Hc. change BC_NE with (neg_bc BC_EQ) in Hc.
rewrite branch_taken_neg, (rbn2_eq0b E n v H Hv) in Hc. apply negb_false_iff in Hc. apply Z.eqb_eq. exact Hc.
Qed.
Lemma rbn2_rngb : forall E n i, ew E n = Z_to_bv 64 i -> - 2 ^ 31 <= i < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551577)) =
  negb ((2 <=? i) && (i <=? 40)).
Proof.
intros E n i H Hi.
rewrite branch_ltu_U, U_SLit. replace (zcanon 18446744073709551577) with 18446744073709551577 by reflexivity.
rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (rbn2_U E n i H), rbn2_mod_64_32, U_SLit.
replace (zcanon (-41) mod 2 ^ 32) with 4294967255 by reflexivity.
unfold bv_swrap. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31).
pose proof (Z.div_mod i (2 ^ 32) ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound i (2 ^ 32) ltac:(lia)) as M1.
pose proof (Z.div_mod (i mod 2 ^ 32 + 4294967255 + 2 ^ 31) (2 ^ 32) ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (i mod 2 ^ 32 + 4294967255 + 2 ^ 31) (2 ^ 32) ltac:(lia)) as M2.
pose proof (Z.div_mod ((i mod 2 ^ 32 + 4294967255 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) (2 ^ 64) ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound ((i mod 2 ^ 32 + 4294967255 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) (2 ^ 64) ltac:(lia)) as M3.
apply eq_true_iff_eq. rewrite Z.ltb_lt, negb_true_iff, andb_false_iff, !Z.leb_gt.
split; intros H'; lia.
Qed.
Lemma rbn2_rng_t : forall E n i, ew E n = Z_to_bv 64 i -> - 2 ^ 31 <= i < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551577)) =
  true -> ~ (2 <= i <= 40).
Proof.
intros E n i H Hi Hc. rewrite (rbn2_rngb E n i H Hi) in Hc. apply negb_true_iff, andb_false_iff in Hc.
intros [H1 H2]. destruct Hc as [Hc | Hc]; apply Z.leb_gt in Hc; lia.
Qed.
Lemma rbn2_rng_f : forall E n i, ew E n = Z_to_bv 64 i -> - 2 ^ 31 <= i < 2 ^ 31 ->
  branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551577)) =
  false -> 2 <= i <= 40.
Proof.
intros E n i H Hi Hc. rewrite (rbn2_rngb E n i H Hi) in Hc. apply negb_false_iff, andb_true_iff in Hc.
destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma rbn2_oddb : forall E n i, ew E n = Z_to_bv 64 i ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = negb (i mod 2 =? 0).
Proof.
intros E n i H. rewrite branch_ne_U, U_and_lit by lia. rewrite (rbn2_U E n i H), U_SLit. change (zcanon 0) with 0.
change (Z.land (i mod 2 ^ 64) 1) with (Z.land (i mod 2 ^ 64) (Z.ones 1)).
rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite rbn2_mod_64_2. reflexivity.
Qed.
Lemma rbn2_odd_t : forall E n i, ew E n = Z_to_bv 64 i ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = true -> i mod 2 <> 0.
Proof. intros E n i H Hc. rewrite (rbn2_oddb E n i H) in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq. exact Hc. Qed.
Lemma rbn2_odd_f : forall E n i, ew E n = Z_to_bv 64 i ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = false -> i mod 2 = 0.
Proof. intros E n i H Hc. rewrite (rbn2_oddb E n i H) in Hc. apply negb_false_iff in Hc. apply Z.eqb_eq. exact Hc. Qed.
Lemma rbn2_nowr : forall E a, ~ in_wrange E rbn2b_regions a.
Proof.
intros E a (r & Hr & Ha). unfold rbn2b_regions in Hr. cbn [In] in Hr.
destruct Hr as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia.
Qed.
Lemma rbn2_forall36 : forall f : Z -> bool, forallb (fun k => f (Z.of_nat k)) (seq 0 36) = true ->
  forall j, 0 <= j < 36 -> f j = true.
Proof.
intros f Hf j Hj. rewrite forallb_forall in Hf. specialize (Hf (Z.to_nat j) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in Hf by lia. exact Hf.
Qed.
Lemma rbn2_nin : forall (r : Z) l, existsb (Z.eqb r) l = false -> ~ In r l.
Proof.
intros r l H Hin. assert (Ht : existsb (Z.eqb r) l = true)
  by (apply existsb_exists; exists r; split; [exact Hin | apply Z.eqb_refl]).
congruence.
Qed.
Lemma rbn2_kr : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
  rbn_keep_regs regs regs2 cl -> ~ In (bv_unsigned r) cl -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 cl r K Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
pose proof (K (bv_unsigned r) Hr Hn) as Hk. rewrite Z_to_bv_bv_unsigned in Hk. exact Hk.
Qed.
Ltac rbn2_nin_tac := apply rbn2_nin; vm_compute; reflexivity.
Ltac rbn2_awr :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil].
Ltac rbn2_run RUNTOP HS HJ KM stop :=
  paj_run_to_sh RUNTOP HS HJ stop;
  [ rbn2_awr
  | lazymatch goal with
    | HF : frame_of _ _ (ms_mem _) (ms_mem _), HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _),
      HG : mem_grows _ _ |- _ =>
      let KM' := fresh "KM" in
      pose proof (fun x => eq_trans (HFr x (rbn2_nowr _ (bv_unsigned x))) (KM x)) as KM';
      clear KM HF HFr HG; rename KM' into KM
    end ].
Ltac rbn2_heavy :=
  repeat match goal with
  | H : context [st_ok_pi] |- _ => clear H
  | H : context [ajournal] |- _ => clear H
  | H : context [SRr] |- _ => clear H
  | H : context [mrestrict] |- _ => clear H
  | H : context [ew] |- _ => clear H
  | H : context [getr] |- _ => clear H
  end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma rbn2_shbyte : forall E (H : word -> bool) (mem : word -> option byte) n base lo hi wlo whi cs j v,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = base -> rbn2_shchunk cs j v = true ->
  aview SEGS H mem (base + j) = Some v.
Proof.
intros E H mem n base lo hi wlo whi cs j v HR Hb Hc.
unfold rbn2_shchunk in Hc. apply existsb_exists in Hc as (c & Hin & Hc).
apply andb_true_iff in Hc as (Hoff & Hc). apply Z.eqb_eq in Hoff.
destruct c as [od cv]. cbn [YP09.c_off YP09.c_val] in Hoff, Hc. subst od.
destruct cv as [w e| | |]; try discriminate.
apply andb_true_iff in Hc as (Hw & Hc). apply N.eqb_eq in Hw. subst w.
destruct e as [z| | | | | | | | | |]; try discriminate. apply Z.eqb_eq in Hc.
destruct HR as (_ & _ & _ & HF). cbn [YP09.r_chunks YP09.r_base base_val] in HF.
rewrite Forall_forall in HF. specialize (HF _ Hin). unfold YP09.chunk_ok in HF.
cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in HF. rewrite Hb in HF.
destruct (HF 0 ltac:(cbn; lia)) as (b & Hcb & Hmb).
cbn [cbyte byte_of_word sv_denot YP09.c_off YP09.c_val] in Hcb, Hmb. rewrite Z.add_0_r in Hmb.
injection Hcb as <-. unfold aview. rewrite Hmb. cbn [option_map].
f_equal. rewrite <- Hc, ?Z.mul_0_r, ?Z.shiftr_0_r, ?Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma rbn2_keep_of : forall H ss ms (regs : bvmap 5 word) extra cl,
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) ss (restrict H ms) -> rbn2_keepb (ss_regs ss) cl = true ->
  rbn_keep_regs regs (ms_regs ms) cl.
Proof.
intros H ss ms regs extra cl HS Hk r Hr Hn.
destruct (Z.eq_dec r 0) as [-> | Hr0].
{ replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; reflexivity). rewrite !getr_zero. reflexivity. }
unfold rbn2_keepb in Hk. rewrite forallb_forall in Hk.
specialize (Hk (Z.to_nat r) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in Hk by lia.
apply orb_true_iff in Hk as [Hk | Hk].
{ exfalso. apply Hn. apply existsb_exists in Hk as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. subst x. exact Hx. }
apply sv_eqb_eq in Hk.
rewrite (st_ok_pi_restrict_reg H _ ss ms _ HS), Hk. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Eimg_Ereg_nat.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rbn2b_entry : forall (W : world SEGS) (regs : bvmap 5 word) m sp dsp,
  bv_unsigned (getr regs 8) = sp -> sp + 8 <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) sp 8 dsp -> 0 <= dsp < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 dsp])) ss_rbn2b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P2B))) m (seg_rom SEGS))).
Proof.
intros W regs m sp dsp H8 Hsp Hv Hd.
rewrite restrict_mkst_fx.
assert (E8 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 8) = sp)
  by (rewrite (ew_Eimg_Ereg_nat regs _ 8 8%bv eq_refl); exact H8).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 32 = Z_to_bv 64 dsp)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. change (bv_modulus 64) with (2 ^ 64) in R8.
unfold ss_rbn2b, rbn2b_regions. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E8.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ sp 0 8 (SOff 32 0) dsp);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | rewrite Z.add_0_r; exact Hv].
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [exact I|]. split; exact I.
Qed.
Lemma rbn2_entry : forall (W : world SEGS) (regs : bvmap 5 word) m A F SH SP dsp,
  getr regs 9 = w64 A -> getr regs 19 = w64 F -> getr regs 22 = w64 SHADOW_OFF -> getr regs 8 = w64 SP ->
  SH = shadow_addr F -> 0 <= A -> 0 <= F -> 0 <= SH -> (F + 24 <= SH \/ SH + 36 <= F) ->
  F + 24 <= A + 112 -> SH + 36 <= A + 112 -> A + 120 <= SP -> SP + 8 <= 2 ^ 64 ->
  (forall o, 112 <= o < 120 -> apresent (w_H W) m (A + o)) ->
  (forall o, 0 <= o < 24 -> apresent (w_H W) m (F + o)) ->
  (forall o, 0 <= o < 36 -> apresent (w_H W) m (SH + o)) ->
  val_mem SEGS (mrestrict (w_H W) m) SP 8 dsp -> 0 <= dsp < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SH; Z_to_bv 64 dsp])) ss_rbn2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P2))) m (seg_rom SEGS))).
Proof.
intros W regs m A F SH SP dsp G9 G19 G22 G8 HSH HA HF HSH0 HFS HFA HSA HAS HSP PA PF PS Hv Hd.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 SH; Z_to_bv 64 dsp])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : bv_unsigned (ew E 9) = A)
  by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (E19 : ew E 19 = Z_to_bv 64 F) by (rewrite (EE 19%nat 19%bv eq_refl), G19; reflexivity).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl), G22; reflexivity).
assert (E8 : bv_unsigned (ew E 8) = SP)
  by (rewrite (EE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SH)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 dsp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SH) by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_rbn2, rbn2_regions. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply PA. lia.
  + rewrite U19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply PF. lia.
  + rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply PS. lia.
  + rewrite E8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ SP 0 8 (SOff 33 0) dsp);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | rewrite Z.add_0_r; exact Hv].
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, U19, U32, E8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [exact I|]. split; [exact I|]. split; [|exact I].
  unfold shadow_decl. apply (shadow_decl_ok E 19 22 32 F SHADOW_OFF E19 ltac:(lia) E22).
  rewrite E32, HSH. reflexivity.
Qed.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Definition rbn2_ph2_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (k : Z)
  (W : world SEGS) (m : word -> option byte) (regs : bvmap 5 word) (dsp : Z) (ok : Prop)
  : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 m2 md2,
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 md2 k /\
    (forall x, mrestrict (w_H W) m2 x = mrestrict (w_H W) m x) /\
    rbn_keep_regs regs regs2 [10; 11; 14] /\
    ((ok /\ getr regs2 14 = w64 dsp /\ c2 = rbn_cfg RBN_P3 regs2 m2 md2) \/
     (~ ok /\ c2 = rbn_cfg RBN_P10 regs2 m2 md2)).
Lemma rbn2_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc k (W : world SEGS) m (regs : bvmap 5 word) dsp
  (okP : Prop) ss ms md,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 dsp])) ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> rbn2_keepb (ss_regs ss) [10; 11; 14] = true ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
  (forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) m x) ->
  ((okP /\ sr_get (ss_regs ss) 14%bv = SOff 32 0 /\ ss_pc ss = AF_reac_box_name + RBN_P3) \/
   (~ okP /\ ss_pc ss = AF_reac_box_name + RBN_P10)) ->
  rbn2_ph2_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc k W m regs dsp okP W (mkCfg ms md).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc k W m regs dsp okP ss ms md HS Hrv Hk HJ KM Hx.
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv) as Hms.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md.
split; [exact HJ|]. split; [exact KM|].
split; [exact (rbn2_keep_of _ _ _ _ _ _ HS Hk)|].
destruct Hx as [(Hok & H14 & Hpc) | (Hnok & Hpc)]; [left | right].
- split; [exact Hok|]. split.
  + rewrite (st_ok_pi_restrict_reg _ _ _ _ 14%bv HS), H14. cbn [sv_denot].
    assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 32 = Z_to_bv 64 dsp)
      by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + unfold rbn_cfg, cfg_at. rewrite Hms at 1. rewrite Hpc, Z.add_assoc. reflexivity.
- split; [exact Hnok|].
  unfold rbn_cfg, cfg_at. rewrite Hms at 1. rewrite Hpc, Z.add_assoc. reflexivity.
Qed.
Ltac rbn2_x HS HJ KM :=
  apply SRr_ret; eapply rbn2_fin; [exact HS | reflexivity | vm_compute; reflexivity | exact HJ | exact KM | ].
Ltac rbn2_x10 HS HJ KM :=
  rbn2_x HS HJ KM; right; split; [|vm_compute; reflexivity];
  rbn2_heavy; unfold rbn2_ok; intros Hok; apply rbn2_args_spec in Hok; lia.
Ltac rbn2_x3 HS HJ KM :=
  rbn2_x HS HJ KM; left; split; [|split; vm_compute; reflexivity];
  rbn2_heavy; unfold rbn2_ok; apply rbn2_args_spec; lia.
Lemma rbn2_ph2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc k (W : world SEGS) m md (regs : bvmap 5 word)
  name nl token tl dsp dl i o sp,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  getr regs 16 = w64 dl -> 0 <= dl < 2 ^ 64 -> getr regs 27 = w64 tl -> 0 <= tl < 2 ^ 64 ->
  getr regs 15 = w64 nl -> 0 <= nl < 2 ^ 64 -> getr regs 24 = w64 name -> 0 <= name < 2 ^ 64 ->
  getr regs 23 = w64 token -> 0 <= token < 2 ^ 64 ->
  getr regs 12 = w64 i -> - 2 ^ 31 <= i < 2 ^ 31 -> getr regs 13 = w64 o -> - 2 ^ 31 <= o < 2 ^ 31 ->
  bv_unsigned (getr regs 8) = sp -> sp + 8 <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) sp 8 dsp -> 0 <= dsp < 2 ^ 64 ->
  SRr SEGS W (rbn_cfg RBN_P2B regs m md)
    (rbn2_ph2_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc k W m regs dsp (rbn2_ok name nl token tl dsp dl i o)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc k W m md regs name nl token tl dsp dl i o sp
  HJ G16 R16 G27 R27 G15 R15 G24 R24 G23 R23 G12 R12 G13 R13 H8 Hsp Hv Rd.
pose proof (rbn2b_entry W regs m sp dsp H8 Hsp Hv Rd) as HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E16 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 16 = Z_to_bv 64 dl)
  by (rewrite (EE 16%nat 16%bv eq_refl); exact G16).
assert (E27 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 27 = Z_to_bv 64 tl)
  by (rewrite (EE 27%nat 27%bv eq_refl); exact G27).
assert (E15 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 15 = Z_to_bv 64 nl)
  by (rewrite (EE 15%nat 15%bv eq_refl); exact G15).
assert (E24 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 24 = Z_to_bv 64 name)
  by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
assert (E23 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 23 = Z_to_bv 64 token)
  by (rewrite (EE 23%nat 23%bv eq_refl); exact G23).
assert (E12 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 12 = Z_to_bv 64 i)
  by (rewrite (EE 12%nat 12%bv eq_refl); exact G12).
assert (E13 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 13 = Z_to_bv 64 o)
  by (rewrite (EE 13%nat 13%bv eq_refl); exact G13).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 dsp])) 32 = Z_to_bv 64 dsp)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [Z_to_bv 64 dsp]))) by apply Eimg_env.
clear EE G16 G27 G15 G24 G23 G12 G13 H8 Hv.
set (E := Eimg (Ereg regs [Z_to_bv 64 dsp])) in *.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (paj_branch (L := ident_listing) (PI := PI)) as BR.
unfold rbn_cfg, cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
  replace pc with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P2B))) by (rewrite Z.add_assoc; reflexivity) end.
assert (KM : forall x, mrestrict (w_H W)
  (ms_mem (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P2B))) m (seg_rom SEGS))) x =
  mrestrict (w_H W) m x) by (intros x; reflexivity).
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_eq0_t E 16 dl E16 ltac:(lia)) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_eq0_f E 16 dl E16 ltac:(lia)) in Hc. rename Hc into C1.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_eq0_t E 27 tl E27 ltac:(lia)) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_eq0_f E 27 tl E27 ltac:(lia)) in Hc. rename Hc into C2.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_eq0_t E 15 nl E15 ltac:(lia)) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_eq0_f E 15 nl E15 ltac:(lia)) in Hc. rename Hc into C3.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_eq0_t E 24 name E24 ltac:(lia)) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_eq0_f E 24 name E24 ltac:(lia)) in Hc. rename Hc into C4.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_eq0_t E 23 token E23 ltac:(lia)) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_eq0_f E 23 token E23 ltac:(lia)) in Hc. rename Hc into C5.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_eq0_t E 32 dsp E32 ltac:(lia)) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_eq0_f E 32 dsp E32 ltac:(lia)) in Hc. rename Hc into C6.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_eq0_t E 12 i E12 ltac:(lia)) in Hc. rename Hc into C7.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
  psrr_branch_pi RUNP BR HS.
  { apply (rbn2_eq0_t E 13 o E13 ltac:(lia)) in Hc.
    rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
  apply (rbn2_eq0_f E 13 o E13 ltac:(lia)) in Hc. rename Hc into C10.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
  psrr_branch_pi RUNP BR HS.
  { apply (rbn2_rng_t E 13 o E13 R13) in Hc.
    rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
  apply (rbn2_rng_f E 13 o E13 R13) in Hc. rename Hc into C12.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
  psrr_branch_pi RUNP BR HS.
  { apply (rbn2_odd_t E 13 o E13) in Hc.
    rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
  apply (rbn2_odd_f E 13 o E13) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3). rbn2_x3 HS HJ KM. }
apply (rbn2_eq0_f E 12 i E12 ltac:(lia)) in Hc. rename Hc into C7.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_rng_t E 12 i E12 R12) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_rng_f E 12 i E12 R12) in Hc. rename Hc into C8.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_odd_t E 12 i E12) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
apply (rbn2_odd_f E 12 i E12) in Hc. rename Hc into C9.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
psrr_branch_pi RUNP BR HS.
{ apply (rbn2_ne0_t E 13 o E13 ltac:(lia)) in Hc. rename Hc into C10.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
  psrr_branch_pi RUNP BR HS.
  { apply (rbn2_rng_t E 13 o E13 R13) in Hc.
    rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
  apply (rbn2_rng_f E 13 o E13 R13) in Hc. rename Hc into C12.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3).
  psrr_branch_pi RUNP BR HS.
  { apply (rbn2_odd_t E 13 o E13) in Hc.
    rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P10). rbn2_x10 HS HJ KM. }
  apply (rbn2_odd_f E 13 o E13) in Hc.
  rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3). rbn2_x3 HS HJ KM. }
apply (rbn2_ne0_f E 13 o E13 ltac:(lia)) in Hc.
rbn2_run RUNTOP HS HJ KM (AF_reac_box_name + RBN_P3). rbn2_x3 HS HJ KM.
Qed.
Definition rbn2_wz (X : rbn_in) (pos : Z) (a : Z) : Prop :=
  (rbn_A X + 112 <= a < rbn_A X + 120) \/ (rbn_F X pos <= a < rbn_F X pos + 24) \/
  (rbn_SH X pos <= a < rbn_SH X pos + 36).
Lemma rbn2_geom : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  (forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p) /\ In (3, pos) (frames Sc1) /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\
  (rbn_F X pos + 512 <= kLowShadowBeg \/ kHighMemBeg <= rbn_F X pos) /\
  kLowMemEnd <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighShadowEnd /\
  rbn_SP X - 319 <= rbn_A X <= rbn_SP X - 288 /\
  alloc_ceiling <= rbn_SP X - REAC_BOX_NAME_STK /\ rbn_SP X <= 2 ^ 47 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> ~ in_img SEGS a) /\
  (forall b m, In (b, m) (ablocks B (ri_lyc X) (ri_Sc X)) ->
     4096 <= b /\ b + req_size m <= alloc_ceiling /\
     (b + req_size m <= kLowShadowBeg \/ kHighMemBeg <= b) /\
     (b + req_size m <= rbn_F X pos \/ rbn_F X pos + 512 <= b)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CAC : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
destruct HM as (_ & HJ1 & Hperm & _).
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & Hfrs1 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
assert (HFeq : forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p).
{ intros c p. unfold frame_addr. destruct Hly1 as (_ & _ & _ & _ & _ & HF1 & _). rewrite HF1. reflexivity. }
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HFlo & HFhi & HFapp).
rewrite HFeq in HFlo, HFhi, HFapp. rewrite Hfb3 in HFhi, HFapp.
fold (rbn_F X pos) in HFlo, HFhi, HFapp.
unfold in_app in HFapp.
pose proof (shadow_addr_bounds (rbn_F X pos) ltac:(lia)) as HSHb.
assert (HSHhi : rbn_SH X pos + 64 <= kHighShadowEnd).
{ pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1. change (512 / 8) with 64 in H1.
  pose proof (shadow_addr_bounds (rbn_F X pos + 512) ltac:(lia)) as H2. unfold rbn_SH. lia. }
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
assert (HAr : rbn_SP X - 319 <= rbn_A X <= rbn_SP X - 288).
{ unfold rbn_A. pose proof (Z.div_mod (rbn_SP X - 288) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (rbn_SP X - 288) 32 ltac:(lia)) as M. lia. }
split; [exact HFeq|]. split; [exact Hin3|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold rbn_SH; lia|]. split; [exact HSHhi|]. split; [exact HAr|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. apply (frm_img SEGS B LAWS _ _ _ _ _ 3 pos a HAR1 Hin3). rewrite HFeq, Hfb3. exact Ha. }
intros b m Hb.
assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq, Hfb3 in Hd. fold (rbn_F X pos) in Hd.
unfold in_app in Hbapp.
split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.
Lemma rbn2_mid_new : forall X pos lyc1 Sc1 memc1 mdc1 m2 md2 Er,
  rbn_mid B X pos lyc1 Sc1 (ri_W X) memc1 mdc1 (fun _ => False) (repeat 0 64) ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 (ri_W X) m2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rbn2_wz X pos a ->
     aview SEGS (w_H (ri_W X)) m2 a = aview SEGS (w_H (ri_W X)) memc1 a) ->
  (forall j, 0 <= j < 36 -> aview SEGS (w_H (ri_W X)) m2 (rbn_SH X pos + j) =
     Some (nth (Z.to_nat j) (rbn_sh false false false false) 0)) ->
  rbn_mid B X pos lyc1 Sc1 (ri_W X) m2 md2 Er (rbn_sh false false false false).
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 m2 md2 Er HM HJ2 KK SHB.
pose proof (rbn2_geom X pos lyc1 Sc1 (ri_W X) memc1 mdc1 _ _ HM)
  as (_ & _ & HF4 & HFc & HFapp & HSHlo & HSHhi & HAr & HSPc & HSP47 & HFnimg & HBLK).
destruct HM as (_ & _ & Hperm & Hro & HK & Hfr & Hfl & Hsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hperm|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow.
  assert (Hn : ~ rbn2_wz X pos a).
  { unfold rbn2_wz. intros [Hw | [Hw | Hw]]; [lia | exact (HFnimg a ltac:(lia) Hia) | lia]. }
  rewrite (KK a ltac:(lia) Hn). exact (Hro a Hro0 Ho He). }
split.
{ intros a Hfp (q & N & Hq & Ha) _.
  destruct (HBLK q N Hq) as (Hq4 & Hqc & Hqapp & Hqf).
  assert (HN : N <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
  assert (Hn : ~ rbn2_wz X pos a) by (unfold rbn2_wz; lia).
  rewrite (KK a ltac:(lia) Hn).
  exact (HK a Hfp (ex_intro _ q (ex_intro _ N (conj Hq Ha))) (fun H => H)). }
split.
{ intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length rbn_saved_regs] in Hj13.
  apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H (ri_W X)) memc1 m2); [|exact (Hfr j r Hj)].
  intros k Hk. cbn in Hk. apply KK; [lia | unfold rbn2_wz; lia]. }
split.
{ apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H (ri_W X)) memc1 m2); [|exact Hfl].
  intros k Hk. cbn in Hk. apply KK; [lia | unfold rbn2_wz; lia]. }
intros j Hj.
assert (Hlen : length (rbn_sh false false false false) = 64%nat) by reflexivity.
rewrite Hlen in Hj.
destruct (Z_lt_le_dec j 36) as [Hj36 | Hj36]; [exact (SHB j ltac:(lia))|].
assert (Hn : ~ rbn2_wz X pos (rbn_SH X pos + j)) by (unfold rbn2_wz; lia).
rewrite (KK (rbn_SH X pos + j) ltac:(lia) Hn).
rewrite (Hsh j) by (rewrite repeat_length; lia).
rewrite nth_repeat.
replace (rbn_sh false false false false) with
  ([241; 241; 241; 241; 248; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248;
    242; 242; 242; 242; 242; 248; 248; 248; 248; 248; 248; 243; 243; 243; 243; 243; 243] ++ repeat 0 28)
  by reflexivity.
rewrite app_nth2 by (cbn [length]; lia).
rewrite nth_repeat. reflexivity.
Qed.
Theorem rbn_seg2 : rbn_seg2_stmt B G.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H2.
destruct H2 as (HM & HRB & G26 & G20 & G23 & G24 & G25 & G27 & G12 & G13 & G15 & G16).
pose proof HM as (EW & _). subst W1.
pose proof (rbn2_geom X pos lyc1 Sc1 (ri_W X) memc1 mdc1 _ _ HM)
  as (HFeq & Hin3 & HF4 & HFc & HFapp & HSHlo & HSHhi & HAr & HSPc & HSP47 & HFnimg & HBLK).
pose proof HM as (_ & HJ & _).
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & _).
destruct HRB as (G2 & G3 & G4 & G8 & G9 & G19 & G22).
destruct HX as (_ & _ & _ & _ & _ & _ & _ & Ri & _ & Ro & _ & Rn & _ & Rnl & _ & Rt & _ & Rtl & _ & Md & Rd & _ &
  Rdl & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & _ & HFpres & HFSpres).
rewrite HFeq in HFpres, HFSpres. fold (rbn_F X pos) in HFpres, HFSpres. fold (rbn_SH X pos) in HFSpres.
change (fs_frame_bytes 3) with 512 in HFpres, HFSpres. change (512 / 8) with 64 in HFSpres.
assert (Hdisp : val_mem SEGS (mrestrict (w_H (ri_W X)) memc1) (rbn_SP X) 8 (ri_display X)).
{ apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H (ri_W X)) (ri_memc X) memc1); [|exact Md].
  intros k0 Hk0. cbn in Hk0. apply F1; lia. }
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) ss_rbn2
  (restrict (w_H (ri_W X)) (mkst regs1 (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P2))) memc1 (seg_rom SEGS)))).
{ apply (rbn2_entry (ri_W X) regs1 memc1 (rbn_A X) (rbn_F X pos) (rbn_SH X pos) (rbn_SP X) (ri_display X)
    G9 G19 G22 G8 eq_refl); try lia.
  - intros o Ho. apply Hpres. lia.
  - intros o Ho. exact (proj1 (HFpres (rbn_F X pos + o) ltac:(lia))).
  - intros o Ho. exact (proj1 (HFSpres o ltac:(lia))).
  - exact Hdisp. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])))
  by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) 9) =
  rbn_A X) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) 19) =
  rbn_F X pos) by (rewrite (EE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) 8) =
  rbn_SP X) by (rewrite (EE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (E32 : ew (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) 32 =
  Z_to_bv 64 (rbn_SH X pos)) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (U32 : bv_unsigned (ew (Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) 32) =
  rbn_SH X pos) by (rewrite E32; apply unsigned_lit_small; lia).
clear EE.
set (E := Eimg (Ereg regs1 [Z_to_bv 64 (rbn_SH X pos); Z_to_bv 64 (ri_display X)])) in *.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
unfold rbn_cfg, cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
  replace pc with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P2))) by (rewrite Z.add_assoc; reflexivity) end.
paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_P2B).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (rbn_A X - rbn_SP X));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (rbn_F X pos)); [reflexivity | exact U19 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFeq. fold (rbn_F X pos).
    change (fs_frame_bytes 3) with 512. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (rbn_SH X pos)); [reflexivity | exact U32 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite HFeq. fold (rbn_F X pos).
    fold (rbn_SH X pos). change (fs_frame_bytes 3 / 8) with 64. lia. }
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr, HG.
assert (KK1 : forall a, 0 <= a < 2 ^ 64 -> ~ rbn2_wz X pos a ->
  aview SEGS (w_H (ri_W X)) (ms_mem ms) a = aview SEGS (w_H (ri_W X)) memc1 a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hw). apply Hn. unfold ss_rbn2, rbn2_regions in Hr. cbn [ss_mem In] in Hr. unfold rbn2_wz.
  repeat destruct Hr as [<- | Hr]; try destruct Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U9, ?U19, ?U32, ?U8 in Hw; lia. }
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HR2. cbn [ms_mem restrict] in HR2.
assert (SHB : forall j, 0 <= j < 36 -> aview SEGS (w_H (ri_W X)) (ms_mem ms) (rbn_SH X pos + j) =
  Some (nth (Z.to_nat j) (rbn_sh false false false false) 0)).
{ intros j Hj. eapply rbn2_shbyte; [exact HR2 | exact U32 |]. revert j Hj. apply rbn2_forall36.
  vm_compute. reflexivity. }
clear HR2 HF HFr HG.
pose proof (rbn2_keep_of _ _ _ regs1 _ [5; 10; 11; 14; 17; 18; 21] HS ltac:(vm_compute; reflexivity)) as K1.
pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS) as R18.
pose proof (st_ok_pi_restrict_reg _ _ _ _ 21%bv HS) as R21.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  change (sr_get (ss_regs ss) 18%bv) with (SOff 32 0) in R18;
  change (sr_get (ss_regs ss) 21%bv) with (SLit 18446744073709551615) in R21 end.
cbn [sv_denot] in R18, R21. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in R18.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
  replace pc with (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_P2B))
    by (f_equal; unfold AF_reac_box_name, RBN_P2B; lia) end.
assert (KK : forall r : bv 5, ~ In (bv_unsigned r) [5; 10; 11; 14; 17; 18; 21] -> getr (ms_regs ms) r = getr regs1 r)
  by (intros r Hr; exact (rbn2_kr _ _ _ r K1 Hr)).
eapply SRr_mono.
{ apply (rbn2_ph2 REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 0 (ri_W X) (ms_mem ms) _ (ms_regs ms)
    (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X) (ri_display_len X) (ri_i X) (ri_o X)
    (rbn_SP X) HJ).
  - rewrite KK by rbn2_nin_tac. exact G16.
  - exact Rdl.
  - rewrite KK by rbn2_nin_tac. exact G27.
  - exact Rtl.
  - rewrite KK by rbn2_nin_tac. exact G15.
  - exact Rnl.
  - rewrite KK by rbn2_nin_tac. exact G24.
  - exact Rn.
  - rewrite KK by rbn2_nin_tac. exact G23.
  - exact Rt.
  - rewrite KK by rbn2_nin_tac. exact G12.
  - exact Ri.
  - rewrite KK by rbn2_nin_tac. exact G13.
  - exact Ro.
  - rewrite KK by rbn2_nin_tac. rewrite G8. apply unsigned_lit_small. lia.
  - lia.
  - apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H (ri_W X)) memc1 (ms_mem ms)); [|exact Hdisp].
    intros k0 Hk0. cbn in Hk0. apply KK1; [lia | unfold rbn2_wz; lia].
  - exact Rd. }
cbv beta. intros W2 c2 _ Hpost. unfold rbn2_ph2_post in Hpost.
destruct Hpost as (-> & regs2 & m2 & md2 & HJ2 & KM2 & K2 & Hex).
assert (KK2 : forall r : bv 5, ~ In (bv_unsigned r) [5; 10; 11; 14; 17; 18; 21] -> getr regs2 r = getr regs1 r).
{ intros r Hr.
  assert (Hr2 : ~ In (bv_unsigned r) [10; 11; 14]) by (intros Hin; apply Hr; cbn [In] in Hin |- *; tauto).
  rewrite (rbn2_kr _ _ _ r K2 Hr2). exact (KK r Hr). }
assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> ~ rbn2_wz X pos a ->
  aview SEGS (w_H (ri_W X)) m2 a = aview SEGS (w_H (ri_W X)) memc1 a).
{ intros a Ha Hn. rewrite <- (KK1 a Ha Hn). apply aview_eq_of. apply KM2. }
assert (SHB2 : forall j, 0 <= j < 36 -> aview SEGS (w_H (ri_W X)) m2 (rbn_SH X pos + j) =
  Some (nth (Z.to_nat j) (rbn_sh false false false false) 0)).
{ intros j Hj. rewrite <- (SHB j Hj). apply aview_eq_of. apply KM2. }
assert (HRB2 : rbn_rbase B X pos regs2).
{ unfold rbn_rbase. rewrite !KK2 by rbn2_nin_tac.
  exact (conj G2 (conj G3 (conj G4 (conj G8 (conj G9 (conj G19 G22)))))). }
assert (H18 : getr regs2 18 = w64 (rbn_SH X pos)) by (rewrite (rbn2_kr _ _ _ 18%bv K2 ltac:(rbn2_nin_tac)); exact R18).
assert (H26 : getr regs2 26 = w64 (rbn_F X pos)) by (rewrite KK2 by rbn2_nin_tac; exact G26).
destruct Hex as [(Hok & H14 & ->) | (Hnok & ->)].
- left. exists pos, regs2, lyc1, Sc1, m2, md2. split; [reflexivity|].
  split; [exact (rbn2_mid_new X pos lyc1 Sc1 memc1 mdc1 m2 md2 (fun _ => False) HM HJ2 KM3 SHB2)|].
  split; [exact HRB2|]. split; [exact H18|]. split; [exact H26|].
  split; [rewrite KK2 by rbn2_nin_tac; exact G20|]. split; [rewrite KK2 by rbn2_nin_tac; exact G23|].
  split; [rewrite KK2 by rbn2_nin_tac; exact G24|]. split; [rewrite KK2 by rbn2_nin_tac; exact G25|].
  split; [rewrite KK2 by rbn2_nin_tac; exact G27|]. split; [rewrite KK2 by rbn2_nin_tac; exact G12|].
  split; [rewrite KK2 by rbn2_nin_tac; exact G13|]. split; [exact H14|].
  split; [rewrite KK2 by rbn2_nin_tac; exact G15|]. split; [rewrite KK2 by rbn2_nin_tac; exact G16|].
  exact Hok.
- right. exists pos, regs2, lyc1, Sc1, m2, md2. split; [reflexivity|].
  assert (Hacc : rbm_acc X = false).
  { unfold rbm_acc. apply rbn2_accept_false.
    destruct (reac_box_name_c.bn_args_ok (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
      (ri_display_len X) (ri_i X) (ri_o X)) eqn:Ha; [exfalso; exact (Hnok Ha) | reflexivity]. }
  split; [exact (rbn2_mid_new X pos lyc1 Sc1 memc1 mdc1 m2 md2 (rbn_wr X) HM HJ2 KM3 SHB2)|].
  split; [exact HRB2|]. split; [exact H18|]. split; [exact H26|].
  split.
  + rewrite Hacc. rewrite (rbn2_kr _ _ _ 21%bv K2 ltac:(rbn2_nin_tac)), R21. apply bv_eq. vm_compute. reflexivity.
  + intros Ht. rewrite Hacc in Ht. discriminate.
Qed.
End h.
End f.
End d.
