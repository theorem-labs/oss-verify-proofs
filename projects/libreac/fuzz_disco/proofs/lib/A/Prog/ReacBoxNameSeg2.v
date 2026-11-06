(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 896 of its 930 lines of code are new or changed and 35 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec ReacBoxName ReacBoxNameCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition RBN_P2B : Z := 0x1a0.

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

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).

Lemma rbn2_aview_ext : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' a Hm. apply aview_eq_of. unfold mrestrict. rewrite Hm. reflexivity.
Qed.
Lemma rbn2_val_mem_ext : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, m' x = m x) -> val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hm Hv k Hk. rewrite <- (Hv k Hk). apply mbyte_of_aview. apply rbn2_aview_ext. exact Hm.
Qed.
Lemma rbn2_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Definition rbn2_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 112 120 112 120 [];
    YP09.mkRegion (Some 8%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 19%nat) 0 24 0 24 [];
    YP09.mkRegion (Some 32%nat) 0 64 0 36 [] ].
Definition rbn2_facts0 : facts :=
  mkFacts [] [] [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 22 0), SOff 32 0)].
Definition ss_rbn2 : sstate := mkSS 14240 sr_atoms rbn2_regions None rbn2_facts0.
Definition rbn2_extra (sh display : Z) : list word := map (Z_to_bv 64) [sh; display].
Definition ERB2 (regs : bvmap 5 word) (sh display : Z) : env := Eimg (Ereg regs (rbn2_extra sh display)).
Lemma regs_ok_ERB2 : forall regs sh d, regs_ok (ERB2 regs sh d) sr_atoms regs.
Proof.
intros. unfold ERB2. apply (regs_ok_agree 32 (Ereg regs (rbn2_extra sh d))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn2_sh_tail : forall k, (36 <= k)%nat -> nth k (rbn_sh false false false false) 0 = 0.
Proof.
intros k Hk.
change (rbn_sh false false false false)
  with (firstn 36 (rbn_sh false false false false) ++ repeat 0 28).
rewrite app_nth2 by (vm_compute; lia). apply nth_repeat.
Qed.
Definition rbn2_shchunk (l : list YP09.chunk) (j v : Z) : bool :=
  existsb (fun c => (YP09.c_off c =? j) &&
    match YP09.c_val c with CVal w e => (N.eqb w 1) && match e with SLit z => z mod 2 ^ 64 mod 256 =? v | _ => false end
    | _ => false end) l.
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
rewrite Forall_forall in HF. specialize (HF _ Hin). unfold chunk_ok in HF.
cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in HF. rewrite Hb in HF.
destruct (HF 0 ltac:(cbn; lia)) as (b & Hcb & Hmb).
cbn [cbyte byte_of_word sv_denot YP09.c_off YP09.c_val] in Hcb, Hmb. rewrite Z.add_0_r in Hmb.
injection Hcb as <-. unfold aview. rewrite Hmb. cbn [option_map].
f_equal. rewrite <- Hc, ?Z.mul_0_r, ?Z.shiftr_0_r, ?Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma rbn2_mbyte_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) ->
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m' a Hm. unfold mbyte. rewrite Hm. reflexivity. Qed.
Lemma rbn2_aview_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hm. apply aview_eq_of. apply Hm. Qed.
Lemma rbn2_apresent_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hm (Ha & b & Hb). split; [exact Ha|]. exists b.
pose proof (Hm (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Ha in Hx. rewrite Hx. exact Hb.
Qed.
Lemma rbn2_val_mem_mr : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, mrestrict H m' x = mrestrict H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v Hm Hv k Hk. rewrite (rbn2_mbyte_mr H m m' _ Hm). exact (Hv k Hk). Qed.
Lemma rbn2_land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma rbn2_uoff : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v Hn. unfold U. rewrite denot_SOff, Hn, Z_to_bv_unsigned, Z.add_0_r.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zmod_mod.
Qed.
Lemma rbn2_uand : forall E n v, ew E n = Z_to_bv 64 v -> U E (SAlu ALU_AND (SOff n 0) (SLit 1)) = v mod 2.
Proof.
intros E n v Hn. rewrite U_SAlu. cbn [zalu_raw]. rewrite (rbn2_uoff E n v Hn), U_SLit.
replace (zcanon 1) with 1 by reflexivity. rewrite rbn2_land_1, rbn2_mod_64_2.
unfold zcanon, M64. apply Z.mod_small. pose proof (Z.mod_pos_bound v 2 ltac:(lia)). lia.
Qed.
Lemma rbn2_usub : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
  (U E (SAluw ALU_ADD (SOff n 0) (SLit (-41))) <? U E (SLit 18446744073709551577)) =
  negb ((2 <=? v) && (v <=? 40)).
Proof.
intros E n v Hn Hv.
rewrite U_SLit. replace (zcanon 18446744073709551577) with 18446744073709551577 by reflexivity.
rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (rbn2_uoff E n v Hn), rbn2_mod_64_32, U_SLit.
replace (zcanon (-41) mod 2 ^ 32) with 4294967255 by reflexivity.
unfold bv_swrap. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31).
pose proof (Z.div_mod v (2 ^ 32) ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as M1.
pose proof (Z.div_mod (v mod 2 ^ 32 + 4294967255 + 2 ^ 31) (2 ^ 32) ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (v mod 2 ^ 32 + 4294967255 + 2 ^ 31) (2 ^ 32) ltac:(lia)) as M2.
pose proof (Z.div_mod ((v mod 2 ^ 32 + 4294967255 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) (2 ^ 64) ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound ((v mod 2 ^ 32 + 4294967255 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) (2 ^ 64) ltac:(lia)) as M3.
apply eq_true_iff_eq. rewrite Z.ltb_lt, negb_true_iff, andb_false_iff, !Z.leb_gt.
split; intros H; lia.
Qed.
Lemma rbn2_eqb_true : forall E a b, U E a = U E b -> bv_eqb (sv_denot E a) (sv_denot E b) = true.
Proof. intros E a b H. apply (proj2 (bv_eqb_eq _ _)). apply bv_eq. exact H. Qed.
Lemma rbn2_eqb_false : forall E a b, U E a <> U E b -> bv_eqb (sv_denot E a) (sv_denot E b) = false.
Proof.
intros E a b H. destruct (bv_eqb _ _) eqn:He; [|reflexivity].
apply bv_eqb_eq in He. exfalso. apply H. unfold U. rewrite He. reflexivity.
Qed.
Lemma rbn2_c_eq : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 -> v = 0 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true.
Proof.
intros E n v Hn Hv ->. cbn [branch_taken]. apply rbn2_eqb_true.
rewrite (rbn2_uoff E n 0 Hn), U_SLit. reflexivity.
Qed.
Lemma rbn2_c_ne : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 -> v <> 0 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true.
Proof.
intros E n v Hn Hv Hne. cbn [branch_taken].
rewrite (rbn2_eqb_false E (SOff n 0) (SLit 0)); [reflexivity|].
rewrite (rbn2_uoff E n v Hn), U_SLit. replace (zcanon 0) with 0 by reflexivity.
pose proof (Z.div_mod v (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)). lia.
Qed.
Lemma rbn2_c_ltu : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> ~ (2 <= v <= 40) ->
  branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit (-41))))
    (sv_denot E (SLit 18446744073709551577)) = true.
Proof.
intros E n v Hn Hv Hr. cbn [branch_taken]. unfold bv_ltu. fold (U E (SAluw ALU_ADD (SOff n 0) (SLit (-41)))).
fold (U E (SLit 18446744073709551577)). rewrite (rbn2_usub E n v Hn Hv).
destruct (Z.leb_spec 2 v); destruct (Z.leb_spec v 40); cbn [andb negb]; first [reflexivity | lia].
Qed.
Lemma rbn2_c_geu : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> 2 <= v <= 40 ->
  branch_taken BC_GEU (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit (-41))))
    (sv_denot E (SLit 18446744073709551577)) = true.
Proof.
intros E n v Hn Hv Hr. cbn [branch_taken]. unfold bv_ltu. fold (U E (SAluw ALU_ADD (SOff n 0) (SLit (-41)))).
fold (U E (SLit 18446744073709551577)). rewrite (rbn2_usub E n v Hn Hv).
destruct (Z.leb_spec 2 v); destruct (Z.leb_spec v 40); cbn [andb negb]; first [reflexivity | lia].
Qed.
Lemma rbn2_c_odd : forall E n v, ew E n = Z_to_bv 64 v -> v mod 2 = 1 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = true.
Proof.
intros E n v Hn Hodd. cbn [branch_taken].
rewrite (rbn2_eqb_false E (SAlu ALU_AND (SOff n 0) (SLit 1)) (SLit 0)); [reflexivity|].
rewrite (rbn2_uand E n v Hn), U_SLit. replace (zcanon 0) with 0 by reflexivity. lia.
Qed.
Lemma rbn2_c_even : forall E n v, ew E n = Z_to_bv 64 v -> v mod 2 = 0 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = true.
Proof.
intros E n v Hn Hev. cbn [branch_taken]. apply rbn2_eqb_true.
rewrite (rbn2_uand E n v Hn), U_SLit. rewrite Hev. reflexivity.
Qed.
Definition rbn2b_regions : smem :=
  [ YP09.mkRegion (Some 8%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
Definition ss_rbn2b (cl : list acond) : sstate := mkSS 14452 sr_atoms rbn2b_regions None (mkFacts [] cl []).
Definition ERB2b (regs : bvmap 5 word) (display : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [display])).
Lemma regs_ok_ERB2b : forall regs d, regs_ok (ERB2b regs d) sr_atoms regs.
Proof.
intros. unfold ERB2b. apply (regs_ok_agree 32 (Ereg regs (map (Z_to_bv 64) [d]))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn2b_nowrange : forall cl E a, ~ in_wrange E (ss_mem (ss_rbn2b cl)) a.
Proof.
intros cl E a (r & Hr & Hw). unfold ss_rbn2b, rbn2b_regions in Hr. cbn [ss_mem In] in Hr.
destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia.
Qed.
Definition rbn2_cEQ (n : nat) : acond := mkAC BC_EQ (SOff n 0) (SLit 0).
Definition rbn2_cNE (n : nat) : acond := mkAC BC_NE (SOff n 0) (SLit 0).
Definition rbn2_cLT (n : nat) : acond :=
  mkAC BC_LTU (SAluw ALU_ADD (SOff n 0) (SLit (-41))) (SLit 18446744073709551577).
Definition rbn2_cGE (n : nat) : acond :=
  mkAC BC_GEU (SAluw ALU_ADD (SOff n 0) (SLit (-41))) (SLit 18446744073709551577).
Definition rbn2_cOD (n : nat) : acond := mkAC BC_NE (SAlu ALU_AND (SOff n 0) (SLit 1)) (SLit 0).
Definition rbn2_cEV (n : nat) : acond := mkAC BC_EQ (SAlu ALU_AND (SOff n 0) (SLit 1)) (SLit 0).
Definition rbn2_pre : list acond :=
  [rbn2_cNE 16; rbn2_cNE 27; rbn2_cNE 15; rbn2_cNE 24; rbn2_cNE 23; rbn2_cNE 32].
Definition RBN2_L1 : list acond := [rbn2_cEQ 16].
Definition RBN2_L2 : list acond := [rbn2_cNE 16; rbn2_cEQ 27].
Definition RBN2_L3 : list acond := [rbn2_cNE 16; rbn2_cNE 27; rbn2_cEQ 15].
Definition RBN2_L4 : list acond := [rbn2_cNE 16; rbn2_cNE 27; rbn2_cNE 15; rbn2_cEQ 24].
Definition RBN2_L5 : list acond := [rbn2_cNE 16; rbn2_cNE 27; rbn2_cNE 15; rbn2_cNE 24; rbn2_cEQ 23].
Definition RBN2_L6 : list acond :=
  [rbn2_cNE 16; rbn2_cNE 27; rbn2_cNE 15; rbn2_cNE 24; rbn2_cNE 23; rbn2_cEQ 32].
Definition RBN2_L7 : list acond := rbn2_pre ++ [rbn2_cEQ 12; rbn2_cEQ 13].
Definition RBN2_L8 : list acond := rbn2_pre ++ [rbn2_cEQ 12; rbn2_cNE 13; rbn2_cLT 13].
Definition RBN2_L9 : list acond := rbn2_pre ++ [rbn2_cEQ 12; rbn2_cNE 13; rbn2_cGE 13; rbn2_cOD 13].
Definition RBN2_L10 : list acond := rbn2_pre ++ [rbn2_cEQ 12; rbn2_cNE 13; rbn2_cGE 13; rbn2_cEV 13].
Definition RBN2_L11 : list acond := rbn2_pre ++ [rbn2_cNE 12; rbn2_cLT 12].
Definition RBN2_L12 : list acond := rbn2_pre ++ [rbn2_cNE 12; rbn2_cGE 12; rbn2_cOD 12].
Definition RBN2_L13 : list acond :=
  rbn2_pre ++ [rbn2_cNE 12; rbn2_cGE 12; rbn2_cEV 12; rbn2_cNE 13; rbn2_cLT 13].
Definition RBN2_L14 : list acond := rbn2_pre ++ [rbn2_cNE 12; rbn2_cGE 12; rbn2_cEV 12; rbn2_cEQ 13].
Definition RBN2_L15 : list acond :=
  rbn2_pre ++ [rbn2_cNE 12; rbn2_cGE 12; rbn2_cEV 12; rbn2_cNE 13; rbn2_cGE 13; rbn2_cOD 13].
Definition RBN2_L16 : list acond :=
  rbn2_pre ++ [rbn2_cNE 12; rbn2_cGE 12; rbn2_cEV 12; rbn2_cNE 13; rbn2_cGE 13; rbn2_cEV 13].
Ltac rbn2_ct1 :=
  lazymatch goal with
  | |- branch_taken BC_EQ (sv_denot ?Ex (SAlu ALU_AND (SOff ?n 0) _)) _ = true =>
      lazymatch goal with G : ew Ex n = Z_to_bv 64 ?v |- _ => apply (rbn2_c_even Ex n v G ltac:(lia)) end
  | |- branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_AND (SOff ?n 0) _)) _ = true =>
      lazymatch goal with G : ew Ex n = Z_to_bv 64 ?v |- _ => apply (rbn2_c_odd Ex n v G ltac:(lia)) end
  | |- branch_taken BC_LTU (sv_denot ?Ex (SAluw ALU_ADD (SOff ?n 0) _)) _ = true =>
      lazymatch goal with G : ew Ex n = Z_to_bv 64 ?v |- _ =>
        apply (rbn2_c_ltu Ex n v G ltac:(lia) ltac:(lia)) end
  | |- branch_taken BC_GEU (sv_denot ?Ex (SAluw ALU_ADD (SOff ?n 0) _)) _ = true =>
      lazymatch goal with G : ew Ex n = Z_to_bv 64 ?v |- _ =>
        apply (rbn2_c_geu Ex n v G ltac:(lia) ltac:(lia)) end
  | |- branch_taken BC_EQ (sv_denot ?Ex (SOff ?n 0)) _ = true =>
      lazymatch goal with G : ew Ex n = Z_to_bv 64 ?v |- _ =>
        apply (rbn2_c_eq Ex n v G ltac:(lia) ltac:(lia)) end
  | |- branch_taken BC_NE (sv_denot ?Ex (SOff ?n 0)) _ = true =>
      lazymatch goal with G : ew Ex n = Z_to_bv 64 ?v |- _ =>
        apply (rbn2_c_ne Ex n v G ltac:(lia) ltac:(lia)) end
  end.
Ltac rbn2_ct :=
  unfold RBN2_L1, RBN2_L2, RBN2_L3, RBN2_L4, RBN2_L5, RBN2_L6, RBN2_L7, RBN2_L8, RBN2_L9, RBN2_L10,
    RBN2_L11, RBN2_L12, RBN2_L13, RBN2_L14, RBN2_L15, RBN2_L16, rbn2_pre,
    rbn2_cEQ, rbn2_cNE, rbn2_cLT, rbn2_cGE, rbn2_cOD, rbn2_cEV;
  cbn [conds_ok app]; unfold acond_ok; cbn [ac_c ac_a ac_b];
  repeat (split; [rbn2_ct1|]); exact I.

Ltac rbn2_shvals HR HSHall :=
  lazymatch type of HR with
  | region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      assert (HSHall : forallb (fun k => rbn2_shchunk cs (Z.of_nat k)
        (nth k (rbn_sh false false false false) 0)) (seq 0 36) = true) by (vm_compute; reflexivity)
  end.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Definition rbn2_wz (X : rbn_in) (pos : Z) (a : Z) : Prop :=
  (rbn_A X + 112 <= a < rbn_A X + 120) \/ (rbn_F X pos <= a < rbn_F X pos + 24) \/
  (rbn_SH X pos <= a < rbn_SH X pos + 36).

Lemma rbn2_geom : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  (forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p) /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\
  (rbn_F X pos + 512 <= kLowShadowBeg \/ kHighMemBeg <= rbn_F X pos) /\
  kLowMemEnd <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighShadowEnd /\
  rbn_SP X - 304 <= rbn_A X <= rbn_SP X - 288 /\
  alloc_ceiling <= rbn_SP X - REAC_BOX_NAME_STK /\ rbn_SP X <= 2 ^ 47 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> ~ in_img SEGS a) /\
  (forall b m, In (b, m) (ablocks B (ri_lyc X) (ri_Sc X)) ->
     4096 <= b /\ b + req_size m <= alloc_ceiling /\
     (b + req_size m <= kLowShadowBeg \/ kHighMemBeg <= b) /\
     (b + req_size m <= rbn_F X pos \/ rbn_F X pos + 512 <= b)) /\
  (forall c p, In (c, p) (frames (ri_Sc X)) ->
     4096 <= frame_addr (ri_lyc X) c p /\
     frame_addr (ri_lyc X) c p + fs_frame_bytes c <= alloc_ceiling /\
     (frame_addr (ri_lyc X) c p + fs_frame_bytes c <= kLowShadowBeg \/
      kHighMemBeg <= frame_addr (ri_lyc X) c p) /\ 0 <= fs_frame_bytes c /\
     kLowMemEnd <= shadow_addr (frame_addr (ri_lyc X) c p) /\
     shadow_addr (frame_addr (ri_lyc X) c p) + fs_frame_bytes c / 8 <= kHighShadowEnd /\
     (frame_addr (ri_lyc X) c p + fs_frame_bytes c <= rbn_F X pos \/
      rbn_F X pos + 512 <= frame_addr (ri_lyc X) c p) /\
     (shadow_addr (frame_addr (ri_lyc X) c p) + fs_frame_bytes c / 8 <= rbn_SH X pos \/
      rbn_SH X pos + 64 <= shadow_addr (frame_addr (ri_lyc X) c p))).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CAC : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HSPdef : rbn_SP X = spZ (ri_regs X)) by reflexivity.
assert (HAdef : rbn_A X = 32 * ((rbn_SP X - 288) / 32)) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
destruct HM as (HJ1 & Hfrs1 & Hperm & _ & HK & _).
pose proof HJ as (HARc & HlyX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkX & _).
pose proof HJ1 as (HAR1 & Hly1 & _).
assert (HFeq : forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p).
{ intros c p. unfold frame_addr.
  destruct HlyX as (_ & _ & _ & _ & _ & HFX & _). destruct Hly1 as (_ & _ & _ & _ & _ & HF1 & _).
  rewrite HFX, HF1. reflexivity. }
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HFlo & HFhi & HFapp).
rewrite HFeq in HFlo, HFhi, HFapp. rewrite Hfb3 in HFhi, HFapp.
fold (rbn_F X pos) in HFlo, HFhi, HFapp.
assert (HSH : rbn_SH X pos = shadow_addr (rbn_F X pos)) by reflexivity.
pose proof (shadow_addr_bounds (rbn_F X pos) ltac:(lia)) as HSHb.
assert (HSHhi : rbn_SH X pos + 64 <= kHighShadowEnd).
{ pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1. change (512 / 8) with 64 in H1.
  pose proof (shadow_addr_bounds (rbn_F X pos + 512) ltac:(lia)) as H2. unfold rbn_SH. lia. }
destruct HstkX as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
destruct (sp1_facts (rbn_SP X - 288) ltac:(lia)
  ltac:(rewrite HSPdef, <- Zminus_mod_idemp_l, Hal; reflexivity)) as (HAr & _ & _).
split; [exact HFeq|]. split; [lia|]. split; [lia|].
split; [destruct HFapp as (_ & HFd); lia|].
split; [unfold rbn_SH; lia|]. split; [exact HSHhi|].
split; [lia|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha.
  assert (Hdisj : (exists q n, In (q, n) (ablocks B lyc1 Sc1) /\ q <= a < q + req_size n) \/
    (exists cid p, In (cid, p) (frames Sc1) /\
       frame_addr lyc1 cid p <= a < frame_addr lyc1 cid p + fs_frame_bytes cid) \/
    (exists cid p, In (cid, p) (frames Sc1) /\ a = flag_addr lyc1 cid p)).
  { right. left. exists 3, pos. split; [exact Hin3|]. rewrite HFeq, Hfb3. exact Ha. }
  exact (proj2 (al_client_img SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 a HAR1 Hdisj)). }
split.
{ intros b m Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & Hb4 & Hbc & Hbapp & _).
  destruct Hbapp as (_ & Hbd).
  split; [exact Hb4|]. split; [exact Hbc|]. split; [lia|].
  pose proof (sep_block_frame SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 b m 3 pos HAR1
    (Permutation_in _ (Permutation_sym Hperm) Hb) Hin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq, Hfb3 in Hd. fold (rbn_F X pos) in Hd. lia. }
intros c p Hc.
assert (Hin' : In (c, p) (frames Sc1)) by (rewrite Hfrs1; right; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR1 Hin') as (Hclo & Hchi & Hcapp).
rewrite HFeq in Hclo, Hchi, Hcapp.
destruct (in_split _ _ Hc) as (l2 & l3 & Hsplit).
pose proof (sep_frames_pos SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 (3, pos) (c, p) [] l2 l3 HAR1
  ltac:(rewrite Hfrs1, Hsplit; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !HFeq, Hfb3 in Hd.
fold (rbn_F X pos) in Hd.
pose proof (fs_frame_bytes_nonneg c) as Hcnn.
pose proof (shadow_addr_bounds (frame_addr (ri_lyc X) c p) ltac:(lia)) as HG1.
pose proof (shadow_range_end (frame_addr (ri_lyc X) c p) (fs_frame_bytes c) ltac:(lia)) as HG2.
pose proof (shadow_addr_bounds (frame_addr (ri_lyc X) c p + fs_frame_bytes c) ltac:(lia)) as HG3.
destruct Hcapp as (_ & Hcd).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hcnn|]. split; [lia|]. split; [lia|].
split; [lia|].
destruct Hd as [Hd | Hd].
- right. unfold rbn_SH.
  pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1.
  pose proof (shadow_mono (rbn_F X pos + 512) (frame_addr (ri_lyc X) c p) ltac:(lia)) as H2.
  change (512 / 8) with 64 in H1. lia.
- left. unfold rbn_SH.
  pose proof (shadow_mono (frame_addr (ri_lyc X) c p + fs_frame_bytes c) (rbn_F X pos) ltac:(lia)) as H2.
  lia.
Qed.

Lemma rbn2_mid_weaken : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh Er,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh Er
  (HJ & Hfr & Hp & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & HFr & HFL & HSh).
split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hp|]. split; [exact Hro|].
split; [|split; [exact HFr | split; [exact HFL | exact HSh]]].
split; [intros a H1 H2 _; exact (K1 a H1 H2 ltac:(intros []))|].
split; [intros b m j H1 H2 _; exact (K2 b m j H1 H2 ltac:(intros []))|].
split; [exact K3|].
split; [intros cid p a H1 H2 _; exact (K4 cid p a H1 H2 ltac:(intros []))|].
split; [exact K5 | exact K6].
Qed.

Lemma rbn2_mid_write : forall X pos lyc1 Sc1 W1 memc1 mdc1 memc2 mdc2 sh sh2,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc2 mdc2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rbn2_wz X pos a ->
     aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  mem_grows (mrestrict (w_H W1) memc1) (mrestrict (w_H W1) memc2) ->
  rbn_shadow_at W1 memc2 (rbn_SH X pos) sh2 ->
  rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) sh2.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 memc2 mdc2 sh sh2 HX HM HJ2 Hkp Hgr Hsh.
destruct (rbn2_geom X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as
  (HFeq & HFlo & HFhi & HFz & HSlo & HShi & HAb & HCeil & H47 & HFimg & HBlk & HFrm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
destruct HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & _).
unfold rbn2_wz in Hkp.
split; [exact HJ2|]. split; [exact Hfrs1|]. split; [exact Hperm|].
split.
{ intros a Hroa Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hroa as [(sg & Hsg & _ & Hr) | Hr];
        [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow.
  rewrite (Hkp a ltac:(lia) ltac:(intros [Hw | [Hw | Hw]]; [lia | exact (HFimg a ltac:(lia) Hia) | lia])).
  exact (Hro1 a Hroa Ho He). }
split.
{ split.
  { intros a Ha Hn _.
    rewrite (Hkp a ltac:(lia) ltac:(intros [Hw | [Hw | Hw]]; lia)).
    exact (K1 a Ha Hn ltac:(intros [])). }
  split.
  { intros b m j Hb Hj _. destruct (HBlk b m Hb) as (Hb4 & Hbc & Hbz & Hbd).
    rewrite (Hkp (b + j) ltac:(lia) ltac:(intros [Hw | [Hw | Hw]]; lia)).
    exact (K2 b m j Hb Hj ltac:(intros [])). }
  split.
  { intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow.
    rewrite (Hkp a ltac:(lia) ltac:(intros [Hw | [Hw | Hw]]; [lia | exact (HFimg a ltac:(lia) Hia) | lia])).
    exact (K3 a Hia Ho He). }
  split.
  { intros cid p a Hcp Ha _.
    destruct (HFrm cid p Hcp) as (Hg4 & Hgc & Hgz & Hgn & Hgs1 & Hgs2 & Hgd & Hsd).
    unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
    rewrite (Hkp a ltac:(destruct Ha as [Ha | Ha]; lia)
      ltac:(intros [Hw | [Hw | Hw]]; destruct Ha as [Ha | Ha]; lia)).
    exact (K4 cid p a Hcp ltac:(unfold in_zr, frame_rng; cbn [fst snd]; exact Ha) ltac:(intros [])). }
  split.
  { intros a Ha Hn Hp. apply (apresent_grows _ _ _ _ Hgr). exact (K5 a Ha Hn Hp). }
  intros a Ha. apply (apresent_grows _ _ _ _ Hgr). exact (K6 a Ha). }
split.
{ intros j r Hj.
  assert (Hjr : (j < 13)%nat)
    by (apply (proj1 (nth_error_Some rbn_saved_regs j)); rewrite Hj; discriminate).
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [| exact (HFr1 j r Hj)].
  intros k Hk. apply Hkp; [lia | intros [Hw | [Hw | Hw]]; lia]. }
split; [|exact Hsh].
apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [| exact HFL1].
intros k Hk. apply Hkp; [lia | intros [Hw | [Hw | Hw]]; lia].
Qed.

Lemma rbn2_entry : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_st2 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_SP X) 8 (ri_display X) /\
  st_ok_pi SEGS VAL (ERB2 regs1 (rbn_SH X pos) (ri_display X)) ss_rbn2
    (restrict (w_H W1) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + 14240)) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HS2.
pose proof (rbn2_geom X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX (proj1 HS2)) as
  (HFeq & HFlo & HFhi & HFz & HSlo & HShi & HAb & HCeil & H47 & HFimg & HBlk & HFrm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof HX as (HJX & Hro & Hrv & Hra & Hra4 & Hgp & Htp & Hch & Hal & Hbud & Hsp16 & Hfrl & H10 & Rf & H11 &
  Rsaid & H12 & Ri & H13 & Ro & H14 & Rn & H15 & Rnl & H16 & Rt & H17 & Rtl & Md & Rd & Mdl & Rdl & Himg & Hargs).
pose proof HS2 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22) & R26 & R20 & R23 & R24 & R25 & R27 & R12 & R13 &
  R15 & R16).
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
assert (Hdisp : val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_SP X) 8 (ri_display X)).
{ apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) memc1);
  [ intros k Hk; exact (K1 (rbn_SP X + k) ltac:(lia) ltac:(lia) ltac:(intros [])) | exact Md ]. }
split; [exact Hdisp|].
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
pose proof (proj1 HJ1) as HAR1.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & _ & HFpres & HSHpres).
rewrite HFeq in HFpres, HSHpres. rewrite Hfb3 in HFpres, HSHpres.
fold (rbn_F X pos) in HFpres, HSHpres. fold (rbn_SH X pos) in HSHpres.
change (512 / 8) with 64 in HSHpres.
rewrite restrict_mkst_fx.
set (E := ERB2 regs1 (rbn_SH X pos) (ri_display X)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (B8 : bv_unsigned (ew E 8%nat) = rbn_SP X)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9%nat) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E19 : ew E 19%nat = Z_to_bv 64 (rbn_F X pos)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22%nat = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (B19 : bv_unsigned (ew E 19%nat) = rbn_F X pos)
  by (rewrite E19; apply unsigned_lit_small; lia).
assert (E32 : ew E 32%nat = Z_to_bv 64 (rbn_SH X pos))
  by (subst E; unfold ERB2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33%nat = Z_to_bv 64 (ri_display X))
  by (subst E; unfold ERB2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (B32 : bv_unsigned (ew E 32%nat) = rbn_SH X pos)
  by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_rbn2, rbn2_regions. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_ERB2.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  + rewrite B9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply K6. lia.
  + rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rbn_SP X) 0 8 _ (ri_display X));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Hdisp.
  + rewrite B19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (rbn_F X pos + o) ltac:(lia))).
  + rewrite B32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS).
    exact (proj1 (HSHpres o ltac:(lia))).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite B8, B9, B19, B32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold rbn2_facts0. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I|]. split; [exact I|]. split; [|exact I].
  exact (shadow_decl_ok E 19%nat 22%nat 32%nat (rbn_F X pos) SHADOW_OFF E19 ltac:(lia) E22 E32).
Qed.

Definition rbn2_mid (X : rbn_in) (pos : Z) (regs2 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc2 : word -> option byte) (mdc2 : Model) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) (rbn_sh false false false false) /\
  rbn_rbase B X pos regs2 /\ getr regs2 18 = w64 (rbn_SH X pos) /\ getr regs2 26 = w64 (rbn_F X pos) /\
  getr regs2 20 = w64 (ri_said X) /\ getr regs2 23 = w64 (ri_token X) /\ getr regs2 24 = w64 (ri_name X) /\
  getr regs2 25 = w64 (ri_f X) /\ getr regs2 27 = w64 (ri_token_len X) /\
  getr regs2 12 = w64 (ri_i X) /\ getr regs2 13 = w64 (ri_o X) /\
  getr regs2 15 = w64 (ri_name_len X) /\ getr regs2 16 = w64 (ri_display_len X) /\
  getr regs2 21 = w64 (-1) /\
  val_mem SEGS (mrestrict (w_H W1) memc2) (rbn_SP X) 8 (ri_display X).
Definition rbn2_at2b (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs2 lyc1 Sc1 memc2 mdc2,
    c1 = rbn_cfg X RBN_P2B regs2 memc2 mdc2 /\ rbn2_mid X pos regs2 lyc1 Sc1 W1 memc2 mdc2.

Lemma rbn2_phaseA : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_st2 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P2 regs1 memc1 mdc1) (rbn2_at2b X).
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HS2.
pose proof (rbn2_geom X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX (proj1 HS2)) as
  (HFeq & HFlo & HFhi & HFz & HSlo & HShi & HAb & HCeil & H47 & HFimg & HBlk & HFrm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (HSPdef : rbn_SP X = spZ (ri_regs X)) by reflexivity.
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & Hal & Hbud & Hsp16 & _).
pose proof HJX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HSTK0 & _) & _).
pose proof HS2 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22) & R26 & R20 & R23 & R24 & R25 & R27 & R12 & R13 &
  R15 & R16).
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
destruct (rbn2_entry (ri_fq X) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HS2) as (Hdisp & HS).
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
set (E := ERB2 regs1 (rbn_SH X pos) (ri_display X)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (B9 : bv_unsigned (ew E 9%nat) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (B19 : bv_unsigned (ew E 19%nat) = rbn_F X pos)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (E32 : ew E 32%nat = Z_to_bv 64 (rbn_SH X pos))
  by (subst E; unfold ERB2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (B32 : bv_unsigned (ew E 32%nat) = rbn_SH X pos)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew E 8%nat) = rbn_SP X)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
unfold rbn_cfg, cfg_at.
replace (BASE + AF_reac_box_name + RBN_P2) with (BASE + 14240) by (unfold AF_reac_box_name, RBN_P2; lia).
change (w64 (BASE + 14240)) with (Z_to_bv 64 (BASE + 14240)).
paj_run_to_sh RUNTOP HS HJ1 14452.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | cbn [base_val]; rewrite B9; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (rbn_F X pos)); [reflexivity | exact B19 | | ].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFeq.
    change (fs_frame_bytes 3) with 512. fold (rbn_F X pos). lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (rbn_SH X pos));
    [reflexivity | exact B32 | | apply awr_ok_nil].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite HFeq.
    change (fs_frame_bytes 3 / 8) with 64. fold (rbn_F X pos). fold (rbn_SH X pos). lia. } }
cbn [ms_mem mkst] in HF, HFr, HG.
pose proof (rbn2_kept_frame E _ (w_H W1) memc1 (ms_mem ms) (rbn2_wz X pos) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_rbn2, rbn2_regions in Hr; cbn [ss_mem In] in Hr;
        repeat (destruct Hr as [<- | Hr]); try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?B8, ?B9, ?B19, ?B32 in Hw; unfold rbn2_wz; lia)) as KW.
pose proof (st_ok_pi_region_nth E _ _ 3 _ HS eq_refl) as HR3. cbn [ms_mem restrict] in HR3.
rbn2_shvals HR3 HSHall.
apply SRr_ret.
pmkst HS.
prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9. prreg HS (12%bv : bv 5) G12.
prreg HS (13%bv : bv 5) G13. prreg HS (15%bv : bv 5) G15. prreg HS (16%bv : bv 5) G16.
prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20.
prreg HS (21%bv : bv 5) G21. prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23.
prreg HS (24%bv : bv 5) G24. prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26.
prreg HS (27%bv : bv 5) G27.
rewrite (EE 2%nat 2%bv eq_refl) in G2. rewrite (EE 3%nat 3%bv eq_refl) in G3.
rewrite (EE 4%nat 4%bv eq_refl) in G4. rewrite (EE 8%nat 8%bv eq_refl) in G8.
rewrite (EE 9%nat 9%bv eq_refl) in G9. rewrite (EE 12%nat 12%bv eq_refl) in G12.
rewrite (EE 13%nat 13%bv eq_refl) in G13. rewrite (EE 15%nat 15%bv eq_refl) in G15.
rewrite (EE 16%nat 16%bv eq_refl) in G16. rewrite E32 in G18.
rewrite (EE 19%nat 19%bv eq_refl) in G19. rewrite (EE 20%nat 20%bv eq_refl) in G20.
rewrite (EE 22%nat 22%bv eq_refl) in G22. rewrite (EE 23%nat 23%bv eq_refl) in G23.
rewrite (EE 24%nat 24%bv eq_refl) in G24. rewrite (EE 25%nat 25%bv eq_refl) in G25.
rewrite (EE 26%nat 26%bv eq_refl) in G26. rewrite (EE 27%nat 27%bv eq_refl) in G27.
exists pos, (ms_regs ms), lyc1, Sc1, (ms_mem ms), (with_vm_backing (m_vm_lazy mdc1) mat mdc1).
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_P2B) with (BASE + 14452) by (unfold AF_reac_box_name, RBN_P2B; lia).
  reflexivity. }
unfold rbn2_mid. split.
{ apply (rbn2_mid_write X pos lyc1 Sc1 W1 memc1 mdc1 (ms_mem ms) _ (repeat 0 64) _ HX HM HJ1 KW HG).
  intros j Hj. change (Z.of_nat (length (rbn_sh false false false false))) with 64 in Hj.
  destruct (Z_lt_le_dec j 36) as [Hlt | Hge].
  - assert (Hk : exists k, (k < 36)%nat /\ j = Z.of_nat k) by (exists (Z.to_nat j); split; lia).
    destruct Hk as (k & Hk & ->). rewrite Nat2Z.id.
    eapply rbn2_shbyte; [exact HR3 | exact B32 |].
    apply (proj1 (forallb_forall _ _) HSHall). apply in_seq. lia.
  - rewrite (KW (rbn_SH X pos + j) ltac:(lia) ltac:(unfold rbn2_wz; lia)).
    rewrite (HSh1 j ltac:(cbn [length repeat]; lia)). rewrite nth_repeat.
    symmetry. f_equal. apply rbn2_sh_tail. lia. }
split.
{ split; [rewrite G2; exact R2|]. split; [rewrite G3; exact R3|]. split; [rewrite G4; exact R4|].
  split; [rewrite G8; exact R8|]. split; [rewrite G9; exact R9|].
  split; [rewrite G19; exact R19 | rewrite G22; exact R22]. }
split; [exact G18|]. split; [rewrite G26; exact R26|].
split; [rewrite G20; exact R20|]. split; [rewrite G23; exact R23|]. split; [rewrite G24; exact R24|].
split; [rewrite G25; exact R25|]. split; [rewrite G27; exact R27|].
split; [rewrite G12; exact R12|]. split; [rewrite G13; exact R13|].
split; [rewrite G15; exact R15|]. split; [rewrite G16; exact R16|].
split; [rewrite G21; apply bv_eq; vm_compute; reflexivity|].
apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms)); [| exact Hdisp].
intros k Hk. apply KW; [lia | unfold rbn2_wz; lia].
Qed.

Lemma rbn2b_entry : forall (fq : YK11.FPState) X pos regs2 lyc1 Sc1 W1 memc2 mdc2 cl,
  rbn_cx B X -> rbn2_mid X pos regs2 lyc1 Sc1 W1 memc2 mdc2 ->
  conds_ok (ERB2b regs2 (ri_display X)) cl ->
  st_ok_pi SEGS VAL (ERB2b regs2 (ri_display X)) (ss_rbn2b cl)
    (restrict (w_H W1) (mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + 14452)) memc2 (seg_rom SEGS))).
Proof.
intros fq X pos regs2 lyc1 Sc1 W1 memc2 mdc2 cl HX HMID Hc.
pose proof HMID as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22) & R18 & R26 & R20 & R23 & R24 & R25 & R27 &
  R12 & R13 & R15 & R16 & R21 & Rdisp).
destruct (rbn2_geom X pos lyc1 Sc1 W1 memc2 mdc2 _ _ HX HM) as
  (HFeq & HFlo & HFhi & HFz & HSlo & HShi & HAb & HCeil & H47 & HFimg & HBlk & HFrm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & Rd & _).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
rewrite restrict_mkst_fx.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ERB2b regs2 (ri_display X)) n = getr regs2 r)
  by (intros n r Hn; unfold ERB2b; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (ERB2b regs2 (ri_display X)) 32%nat = Z_to_bv 64 (ri_display X))
  by (unfold ERB2b; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (B8 : bv_unsigned (ew (ERB2b regs2 (ri_display X)) 8%nat) = rbn_SP X)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
unfold ss_rbn2b, rbn2b_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB2b.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS (ERB2b regs2 (ri_display X)) _ (rbn_SP X) 0 8 _ (ri_display X));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Rdisp.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [f_atoms f_conds f_alias atoms_ok alias_ok].
  split; [exact I|]. split; [exact Hc | exact I].
Qed.

Lemma rbn2_mid_same : forall X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc3 mdc3 (ri_k X) ->
  (forall x, mrestrict (w_H W1) memc3 x = mrestrict (w_H W1) memc2 x) ->
  rbn_mid B X pos lyc1 Sc1 W1 memc3 mdc3 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh
  (HJ & Hfr & Hp & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & HFr & HFL & HSh) HJ3 Hm.
assert (Hv : forall a, aview SEGS (w_H W1) memc3 a = aview SEGS (w_H W1) memc2 a)
  by (intros a; apply rbn2_aview_mr; exact Hm).
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hp|].
split; [intros a H1 H2 H3; rewrite Hv; exact (Hro a H1 H2 H3)|].
split.
{ split; [intros a H1 H2 H3; rewrite Hv; exact (K1 a H1 H2 H3)|].
  split; [intros b m j H1 H2 H3; rewrite Hv; exact (K2 b m j H1 H2 H3)|].
  split; [intros a H1 H2 H3; rewrite Hv; exact (K3 a H1 H2 H3)|].
  split; [intros cid p a H1 H2 H3; rewrite Hv; exact (K4 cid p a H1 H2 H3)|].
  split; [intros a H1 H2 H3; apply (rbn2_apresent_mr _ memc2 memc3 a Hm); exact (K5 a H1 H2 H3)|].
  intros a H1. apply (rbn2_apresent_mr _ memc2 memc3 a Hm). exact (K6 a H1). }
split; [intros j r Hj; apply (rbn2_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact (HFr j r Hj)|].
split; [apply (rbn2_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact HFL|].
intros j Hj. rewrite Hv. exact (HSh j Hj).
Qed.

Definition rbn2_rok (regs3 regs2 : bvmap 5 word) : Prop :=
  getr regs3 2 = getr regs2 2 /\ getr regs3 3 = getr regs2 3 /\ getr regs3 4 = getr regs2 4 /\
  getr regs3 8 = getr regs2 8 /\ getr regs3 9 = getr regs2 9 /\ getr regs3 12 = getr regs2 12 /\
  getr regs3 13 = getr regs2 13 /\ getr regs3 15 = getr regs2 15 /\ getr regs3 16 = getr regs2 16 /\
  getr regs3 18 = getr regs2 18 /\ getr regs3 19 = getr regs2 19 /\ getr regs3 20 = getr regs2 20 /\
  getr regs3 21 = getr regs2 21 /\ getr regs3 22 = getr regs2 22 /\ getr regs3 23 = getr regs2 23 /\
  getr regs3 24 = getr regs2 24 /\ getr regs3 25 = getr regs2 25 /\ getr regs3 26 = getr regs2 26 /\
  getr regs3 27 = getr regs2 27.

Lemma rbn2_exit10 : forall X pos regs2 lyc1 Sc1 W1 memc2 mdc2 regs3 memc3 mdc3,
  rbn2_mid X pos regs2 lyc1 Sc1 W1 memc2 mdc2 ->
  (forall x, mrestrict (w_H W1) memc3 x = mrestrict (w_H W1) memc2 x) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc3 mdc3 (ri_k X) ->
  rbn2_rok regs3 regs2 ->
  reac_box_name_c.bn_args_ok (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
    (ri_display_len X) (ri_i X) (ri_o X) = false ->
  rbn_at3 B X W1 (rbn_cfg X RBN_P10 regs3 memc3 mdc3) \/
  rbn_at10 B X W1 (rbn_cfg X RBN_P10 regs3 memc3 mdc3).
Proof.
intros X pos regs2 lyc1 Sc1 W1 memc2 mdc2 regs3 memc3 mdc3 HMID Hm HJ3
  (Q2 & Q3 & Q4 & Q8 & Q9 & Q12 & Q13 & Q15 & Q16 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27)
  Hargs.
right.
pose proof HMID as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22) & R18 & R26 & R20 & R23 & R24 & R25 & R27 &
  R12 & R13 & R15 & R16 & R21 & Rdisp).
assert (Hacc : rbm_acc X = false)
  by (unfold rbm_acc; exact (rbn2_accept_false _ _ _ _ _ _ _ _ _ _ Hargs)).
exists pos, regs3, lyc1, Sc1, memc3, mdc3. split; [reflexivity|].
split; [apply rbn2_mid_weaken; exact (rbn2_mid_same X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 _ HM HJ3 Hm)|].
split.
{ split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q8; exact R8|]. split; [rewrite Q9; exact R9|].
  split; [rewrite Q19; exact R19 | rewrite Q22; exact R22]. }
split; [rewrite Q18; exact R18|]. split; [rewrite Q26; exact R26|].
split; [rewrite Hacc, Q21; exact R21|].
rewrite Hacc. intros Hx. discriminate.
Qed.

Lemma rbn2_exit3 : forall X pos regs2 lyc1 Sc1 W1 memc2 mdc2 regs3 memc3 mdc3,
  rbn2_mid X pos regs2 lyc1 Sc1 W1 memc2 mdc2 ->
  (forall x, mrestrict (w_H W1) memc3 x = mrestrict (w_H W1) memc2 x) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc3 mdc3 (ri_k X) ->
  rbn2_rok regs3 regs2 -> getr regs3 14 = w64 (ri_display X) -> rbm_args X ->
  rbn_at3 B X W1 (rbn_cfg X RBN_P3 regs3 memc3 mdc3) \/
  rbn_at10 B X W1 (rbn_cfg X RBN_P3 regs3 memc3 mdc3).
Proof.
intros X pos regs2 lyc1 Sc1 W1 memc2 mdc2 regs3 memc3 mdc3 HMID Hm HJ3
  (Q2 & Q3 & Q4 & Q8 & Q9 & Q12 & Q13 & Q15 & Q16 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27)
  Q14 Hargs.
left.
pose proof HMID as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22) & R18 & R26 & R20 & R23 & R24 & R25 & R27 &
  R12 & R13 & R15 & R16 & R21 & Rdisp).
exists pos, regs3, lyc1, Sc1, memc3, mdc3. split; [reflexivity|].
split; [exact (rbn2_mid_same X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 _ HM HJ3 Hm)|].
split.
{ split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q8; exact R8|]. split; [rewrite Q9; exact R9|].
  split; [rewrite Q19; exact R19 | rewrite Q22; exact R22]. }
split; [rewrite Q18; exact R18|]. split; [rewrite Q26; exact R26|].
split; [rewrite Q20; exact R20|]. split; [rewrite Q23; exact R23|]. split; [rewrite Q24; exact R24|].
split; [rewrite Q25; exact R25|]. split; [rewrite Q27; exact R27|].
split; [rewrite Q12; exact R12|]. split; [rewrite Q13; exact R13|].
split; [exact Q14|]. split; [rewrite Q15; exact R15|]. split; [rewrite Q16; exact R16 | exact Hargs].
Qed.

Ltac rbn2_rok1 HS EE :=
  lazymatch goal with
  | |- getr _ ?r = _ => let R := fresh "R" in prreg HS r R; rewrite R; apply EE; vm_compute; reflexivity
  end.
Ltac rbn2_rokt HS EE := unfold rbn2_rok; repeat (split; [rbn2_rok1 HS EE|]); rbn2_rok1 HS EE.
Ltac rbn2_argsF :=
  apply not_true_is_false; let Ha := fresh "Ha" in intros Ha;
  apply (proj1 (rbn2_args_spec _ _ _ _ _ _ _ _)) in Ha; lia.
Ltac rbn2_argsT :=
  unfold rbm_args; apply (proj2 (rbn2_args_spec _ _ _ _ _ _ _ _)); repeat split; lia.
Ltac rbn2_run RUNTOP HS HJ :=
  paj_run_to_sh RUNTOP HS HJ 16332;
  [ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
    apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil
  | ].
Ltac rbn2_fin10 HS HJ EE HMID :=
  lazymatch goal with
  | HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply SRr_ret; pmkst HS;
    replace (BASE + 16332) with (BASE + AF_reac_box_name + RBN_P10)
      by (unfold AF_reac_box_name, RBN_P10; lia);
    eapply rbn2_exit10;
      [ exact HMID | intros x; apply HFx; apply rbn2b_nowrange | exact HJ
      | rbn2_rokt HS EE | rbn2_argsF ]
  end.
Ltac rbn2_fin3 HS HJ EE HMID EV32 :=
  lazymatch goal with
  | HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply SRr_ret; pmkst HS;
    replace (BASE + 14536) with (BASE + AF_reac_box_name + RBN_P3)
      by (unfold AF_reac_box_name, RBN_P3; lia);
    eapply rbn2_exit3;
      [ exact HMID | intros x; apply HFx; apply rbn2b_nowrange | exact HJ
      | rbn2_rokt HS EE
      | let R := fresh "R" in prreg HS (14%bv : bv 5) R; rewrite R; exact EV32
      | rbn2_argsT ]
  end.

Lemma rbn2_phaseB : forall X W1 c, rbn_cx B X -> rbn2_at2b X W1 c ->
  SRr SEGS W1 c (fun W2 c2 => rbn_at3 B X W2 c2 \/ rbn_at10 B X W2 c2).
Proof.
intros X W1 c HX HAT.
destruct HAT as (pos & regs2 & lyc1 & Sc1 & memc2 & mdc2 & -> & HMID).
pose proof HX as (HJX & Hro & Hrv & Hra & Hra4 & Hgp & Htp & Hch & Hal & Hbud & Hsp16 & Hfrl & H10 & Rf & H11 &
  Rsaid & H12 & Ri & H13 & Ro & H14 & Rn & H15 & Rnl & H16 & Rt & H17 & Rtl & Md & Rd & Mdl & Rdl & Himg & Hag).
pose proof HMID as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22) & R18 & R26 & R20 & R23 & R24 & R25 & R27 &
  R12 & R13 & R15 & R16 & R21 & Rdisp).
pose proof HM as (HJ0 & Hfrs1 & Hperm & Hro1 & HK & HFr1 & HFL1 & HSh1).
pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (Z.mod_pos_bound (ri_i X) 2 ltac:(lia)) as MI2.
pose proof (Z.mod_pos_bound (ri_o X) 2 ltac:(lia)) as MO2.
assert (HEI : img_env VAL A_LIM (ERB2b regs2 (ri_display X))) by (unfold ERB2b; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ERB2b regs2 (ri_display X)) n = getr regs2 r)
  by (intros n r Hn; unfold ERB2b; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EV12 : ew (ERB2b regs2 (ri_display X)) 12%nat = Z_to_bv 64 (ri_i X))
  by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (EV13 : ew (ERB2b regs2 (ri_display X)) 13%nat = Z_to_bv 64 (ri_o X))
  by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (EV15 : ew (ERB2b regs2 (ri_display X)) 15%nat = Z_to_bv 64 (ri_name_len X))
  by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (EV16 : ew (ERB2b regs2 (ri_display X)) 16%nat = Z_to_bv 64 (ri_display_len X))
  by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (EV23 : ew (ERB2b regs2 (ri_display X)) 23%nat = Z_to_bv 64 (ri_token X))
  by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (EV24 : ew (ERB2b regs2 (ri_display X)) 24%nat = Z_to_bv 64 (ri_name X))
  by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (EV27 : ew (ERB2b regs2 (ri_display X)) 27%nat = Z_to_bv 64 (ri_token_len X))
  by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (EV32 : ew (ERB2b regs2 (ri_display X)) 32%nat = Z_to_bv 64 (ri_display X))
  by (unfold ERB2b; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
unfold rbn_cfg, cfg_at.
replace (BASE + AF_reac_box_name + RBN_P2B) with (BASE + 14452)
  by (unfold AF_reac_box_name, RBN_P2B; lia).
change (w64 (BASE + 14452)) with (Z_to_bv 64 (BASE + 14452)).
assert (Qir : {2 <= ri_i X <= 40} + {~ (2 <= ri_i X <= 40)})
  by (destruct (Z_le_dec 2 (ri_i X)); destruct (Z_le_dec (ri_i X) 40);
      [left; split; assumption | right; intros (?&?); lia | right; intros (?&?); lia
       | right; intros (?&?); lia]).
assert (Qor : {2 <= ri_o X <= 40} + {~ (2 <= ri_o X <= 40)})
  by (destruct (Z_le_dec 2 (ri_o X)); destruct (Z_le_dec (ri_o X) 40);
      [left; split; assumption | right; intros (?&?); lia | right; intros (?&?); lia
       | right; intros (?&?); lia]).
destruct (Z.eq_dec (ri_display_len X) 0) as [Q16 | Q16]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L1 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID | ].
destruct (Z.eq_dec (ri_token_len X) 0) as [Q27 | Q27]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L2 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID | ].
destruct (Z.eq_dec (ri_name_len X) 0) as [Q15 | Q15]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L3 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID | ].
destruct (Z.eq_dec (ri_name X) 0) as [Q24 | Q24]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L4 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID | ].
destruct (Z.eq_dec (ri_token X) 0) as [Q23 | Q23]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L5 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID | ].
destruct (Z.eq_dec (ri_display X) 0) as [Q32 | Q32]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L6 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID | ].
destruct (Z.eq_dec (ri_i X) 0) as [Q12 | Q12].
- destruct (Z.eq_dec (ri_o X) 0) as [Q13 | Q13]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L7 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID | ].
  destruct Qor as [Qo | Qo]; [| pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L8 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID ].
  destruct (Z.eq_dec (ri_o X mod 2) 0) as [Qop | Qop];
    [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L10 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin3 HSB HJB EE HMID EV32 | pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L9 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID ].
- destruct Qir as [Qi | Qi]; [| pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L11 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID ].
  destruct (Z.eq_dec (ri_i X mod 2) 0) as [Qip | Qip]; [| pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L12 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID ].
  destruct (Z.eq_dec (ri_o X) 0) as [Q13 | Q13]; [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L14 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin3 HSB HJB EE HMID EV32 | ].
  destruct Qor as [Qo | Qo]; [| pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L13 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID ].
  destruct (Z.eq_dec (ri_o X mod 2) 0) as [Qop | Qop];
    [pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L16 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin3 HSB HJB EE HMID EV32 | pose proof (rbn2b_entry (ri_fq X) X _ _ _ _ _ _ _ RBN2_L15 HX HMID ltac:(rbn2_ct)) as HSB;
   pose proof HJ0 as HJB; rbn2_run RUNTOP HSB HJB; rbn2_fin10 HSB HJB EE HMID ].
Qed.

Theorem rbn_seg2 : rbn_seg2_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HS2.
eapply SRr_bind; [exact (rbn2_phaseA X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX HS2)|].
intros W2 c2 _ H2. exact (rbn2_phaseB X W2 c2 HX H2).
Qed.
End h.
End f.
End d.
