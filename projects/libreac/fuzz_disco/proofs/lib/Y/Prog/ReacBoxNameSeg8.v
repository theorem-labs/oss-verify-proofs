(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACan.v:341-345
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YP01.v:21-22 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg8.v, with its module paths, module names and numbers changed; 1006 of its 1235 lines of code are new or changed and 1356 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YA0o YCbm YA0q YG0s YC1g YC1h YC4b YC44 YC45 YCj1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn8_globs : forall q sz, In (q, sz) tfib_globs ->
  q mod 32 = 0 /\ 0x20f80 <= q /\ q + sz <= 0xa0700 /\ 0 < sz /\ (sz = 3 -> q = 0x21240).
Proof.
intros q sz H. unfold tfib_globs in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <-; split; [reflexivity|]; lia|]). destruct H.
Qed.
Lemma rbn8_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn8_keep_get : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
  rbn_keep_regs regs regs2 cl -> existsb (Z.eqb (bv_unsigned r)) cl = false -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 cl r HK Hb.
pose proof (u5_range r) as Hr.
assert (Hn : ~ In (bv_unsigned r) cl).
{ intros Hin. assert (E : existsb (Z.eqb (bv_unsigned r)) cl = true)
    by (apply existsb_exists; exists (bv_unsigned r); split; [exact Hin | apply Z.eqb_refl]).
  rewrite E in Hb. discriminate. }
pose proof (HK _ Hr Hn) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn8_pres_get : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
Ltac rbn8cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with v end; lia.
Lemma rbn8_ok_rng : forall v, bn_ok v = true -> 0 <= v <= 40.
Proof.
intros v H. apply bn_ok_in in H.
assert (Hm : bn_oks = [0;2;4;6;8;10;12;14;16;18;20;22;24;26;28;30;32;34;36;38;40]) by (vm_compute; reflexivity).
rewrite Hm in H. cbn [In] in H. lia.
Qed.
Lemma rbn8_dec_eq : forall v, bn_ok v = true -> sb_dec_c.sb_dec_D v 1 = bn_dec v 1.
Proof.
intros v H. apply bn_ok_in in H.
assert (A : forallb (fun x => if list_eq_dec Z.eq_dec (sb_dec_c.sb_dec_D x 1) (bn_dec x 1) then true else false)
  bn_oks = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A v H).
destruct (list_eq_dec Z.eq_dec (sb_dec_c.sb_dec_D v 1) (bn_dec v 1)) as [E | E]; [exact E | discriminate].
Qed.
Lemma rbn8_dec_len : forall v, bn_ok v = true -> (1 <= length (bn_dec v 1) <= 2)%nat.
Proof.
intros v H. apply bn_ok_in in H.
assert (A : forallb (fun x => Nat.leb 1 (length (bn_dec x 1)) && Nat.leb (length (bn_dec x 1)) 2) bn_oks = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A v H). apply andb_prop in A as (A1 & A2).
apply Nat.leb_le in A1. apply Nat.leb_le in A2. lia.
Qed.
Lemma rbn8_sbd : forall v n, 0 <= n -> n + 1 + Z.of_nat (length (sb_dec_c.sb_dec_D v 1)) <= 48 ->
  sb_dec_c.sb_dec_room 48 n = 47 - n /\
  sb_dec_c.sb_dec_acc v 1 48 n = Z.of_nat (length (sb_dec_c.sb_dec_D v 1)) /\
  (sb_dec_c.sb_dec_room 48 n <? Z.of_nat (length (sb_dec_c.sb_dec_D v 1))) = false.
Proof.
intros v n H0 H1. unfold sb_dec_c.sb_dec_acc, sb_dec_c.sb_dec_room.
destruct (Z.leb_spec (n + 1) 48); [|lia].
split; [reflexivity|]. split; [lia|]. apply Z.ltb_ge. lia.
Qed.
Lemma rbn8_hull_sub : forall (rd : reader) x n y k, shadow_hull_vis rd x n -> x <= y -> 0 < k -> y + k <= x + n ->
  shadow_hull_vis rd y k.
Proof.
intros rd x n y k H H1 H2 H3 s Hs. apply H.
assert (M1 : shadow_addr x / 8 <= shadow_addr y / 8) by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
assert (M2 : shadow_addr (y + k - 1) / 8 <= shadow_addr (x + n - 1) / 8)
  by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn8_frame_eq : forall E rs (W : world SEGS) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros E rs W m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn8_denot0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E n v 0 H Hv ltac:(lia)). lia.
Qed.
Lemma rbn8_keep : forall `{fq : YK11.FPState} (H : word -> bool) ss ms (regs0 : bvmap 5 word) extra cl,
  st_ok SEGS (Eimg (Ereg regs0 extra)) ss (restrict H ms) ->
  forallb (fun r : bv 5 => existsb (Z.eqb (bv_unsigned r)) cl
             || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) all_regs = true ->
  rbn_keep_regs regs0 (ms_regs ms) cl.
Proof.
intros fq H ss ms regs0 extra cl HS Hf r Hr Hn.
assert (Hu : bv_unsigned (Z_to_bv 5 r : bv 5) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
assert (Hin : In (Z_to_bv 5 r : bv 5) all_regs).
{ apply In_bv_eq. rewrite Hu.
  assert (Hm : map bv_unsigned all_regs =
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31])
    by (vm_compute; reflexivity).
  rewrite Hm. cbn [In]. lia. }
pose proof (proj1 (forallb_forall _ _) Hf _ Hin) as Hq. cbn beta in Hq. rewrite Hu in Hq.
assert (Hex : existsb (Z.eqb r) cl = false).
{ destruct (existsb (Z.eqb r) cl) eqn:Ee; [exfalso; apply Hn | reflexivity].
  apply existsb_exists in Ee as (x & Hx & He). apply Z.eqb_eq in He. subst x. exact Hx. }
rewrite Hex in Hq. cbn [orb] in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg SEGS H (Eimg (Ereg regs0 extra)) ss ms (Z_to_bv 5 r) HS), Hq.
rewrite (rbn8_denot0 (Eimg (Ereg regs0 extra)) (Z.to_nat r) (bv_unsigned (getr regs0 (Z_to_bv 5 r)))).
- apply Z_to_bv_bv_unsigned.
- rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs0 extra (Z.to_nat r) (Z_to_bv 5 r) ltac:(rewrite Hu; lia)).
  symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
Lemma rbn8_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rbn8_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn8_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; [tauto|]. rewrite IH. tauto.
Qed.
Definition rbn8_cells (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  rbn_argc X ++ rbn_rw X pos 4 0 ++ rbn_rn X pos (Z.of_nat (length (rbm_NB X))) (rbm_ovf 23 (rbm_NM X)) ++
  rbn_rt X pos (Z.of_nat (length (rbm_TB X))) (rbm_ovf 23 (bn_TK (rbm_NB X))).
Lemma rbn8_cells_rng : forall X pos a n v, In (a, n, v) (rbn8_cells X pos) ->
  (rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 64) \/ (rbn_A X + 120 <= a /\ a + Z.of_nat n <= rbn_A X + 212).
Proof.
intros X pos a n v H. unfold rbn8_cells, rbn_argc, rbn_rw, rbn_rn, rbn_rt in H. cbn [In app] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn8_args_ok : forall X, rbm_args X -> bn_ok (ri_i X) = true /\ bn_ok (ri_o X) = true.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
split; assumption.
Qed.
Lemma rbn8_NB_len : forall X, Z.of_nat (length (rbm_NB X)) <= 23.
Proof. intros X. unfold rbm_NB. pose proof (firstn_le_length 23 (rbm_NM X)). lia. Qed.
Lemma rbn8_TB_len : forall X, Z.of_nat (length (rbm_TB X)) <= 23.
Proof. intros X. unfold rbm_TB. pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))). lia. Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn8_p1 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_P8) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L5) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 10; 20; 21; 24] /\
       getr regs1 20 = w64 0 /\ getr regs1 21 = w64 (VAL (A_OBJ 28)) /\ getr regs1 24 = w64 2 /\
       (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a)).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ.
pose proof (pa_val_range (A_OBJ 28)) as VR.
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (mkSS 15400 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + 15400)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok. cbn. tauto. }
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
unfold cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN_P8) with (BASE + 15400) by (unfold AF_both3_reac_box_name, RBN_P8; lia).
paj_run_to_sh RUNTOP HS HJ 15416.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr.
pose proof (rbn8_frame_eq E _ W memc _ (fun _ => False) HFr ltac:(intros a (r & Hr & _); destruct Hr)) as KEQ.
assert (E269 : ew E 269 = Z_to_bv 64 (VAL (A_OBJ 28)))
  by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; split; [apply Nat.leb_le | apply Nat.ltb_lt]; reflexivity).
assert (Dq : sv_denot E (SOff 269 0) = Z_to_bv 64 (VAL (A_OBJ 28))) by exact (rbn8_denot0 E 269 _ E269 VR).
assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by (rewrite denot_lit_U; reflexivity).
assert (D2 : sv_denot E (SLit 2) = Z_to_bv 64 2) by (rewrite denot_lit_U; reflexivity).
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 0) D0 G20.
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (VAL (A_OBJ 28))) Dq G21.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 2) D2 G24.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 10; 20; 21; 24])
  by (apply (rbn8_keep (w_H W) _ _ regs [] _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64.
  replace (BASE + AF_both3_reac_box_name + RBN_L5) with (BASE + 15416) by (unfold AF_both3_reac_box_name, RBN_L5; lia).
  reflexivity. }
split; [exact HJ|]. split; [exact HKP|].
split; [exact G20|]. split; [exact G21|]. split; [exact G24|].
intros a Ha. exact (KEQ a Ha (fun H => H)).
Qed.
Lemma rbn8_p3 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + 0x5c4) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L6) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 10; 20; 21; 24] /\
       getr regs1 20 = w64 0 /\ getr regs1 21 = w64 (VAL (A_OBJ 29)) /\ getr regs1 24 = w64 6 /\
       (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a)).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ.
pose proof (pa_val_range (A_OBJ 29)) as VR.
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (mkSS 15492 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + 15492)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok. cbn. tauto. }
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
unfold cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + 0x5c4) with (BASE + 15492) by (unfold AF_both3_reac_box_name; lia).
paj_run_to_sh RUNTOP HS HJ 15508.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr.
pose proof (rbn8_frame_eq E _ W memc _ (fun _ => False) HFr ltac:(intros a (r & Hr & _); destruct Hr)) as KEQ.
assert (E270 : ew E 270 = Z_to_bv 64 (VAL (A_OBJ 29)))
  by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; split; [apply Nat.leb_le | apply Nat.ltb_lt]; reflexivity).
assert (Dq : sv_denot E (SOff 270 0) = Z_to_bv 64 (VAL (A_OBJ 29))) by exact (rbn8_denot0 E 270 _ E270 VR).
assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by (rewrite denot_lit_U; reflexivity).
assert (D6 : sv_denot E (SLit 6) = Z_to_bv 64 6) by (rewrite denot_lit_U; reflexivity).
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 0) D0 G20.
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (VAL (A_OBJ 29))) Dq G21.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 6) D6 G24.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 10; 20; 21; 24])
  by (apply (rbn8_keep (w_H W) _ _ regs [] _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64.
  replace (BASE + AF_both3_reac_box_name + RBN_L6) with (BASE + 15508) by (unfold AF_both3_reac_box_name, RBN_L6; lia).
  reflexivity. }
split; [exact HJ|]. split; [exact HKP|].
split; [exact G20|]. split; [exact G21|]. split; [exact G24|].
intros a Ha. exact (KEQ a Ha (fun H => H)).
Qed.
Definition rbn8_rr (od : Z) : smem := [ YP09.mkRegion (Some 9%nat) od (od + 8) od od [YP09.mkChunk od (CVal 8 (SOff 32 0))] ].
Lemma rbn8_call_entry : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte)
  (pc A od v : Z),
  regions_wf (rbn8_rr od) = true ->
  getr regs 9 = w64 A -> 0 <= A -> 0 <= od -> A + od + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + od) 8 v ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 v])) (mkSS pc sr_atoms (rbn8_rr od) None (mkFacts [] [] []))
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros fq regs W memc pc A od v Hwf H9 HA1 Hod HA2 Hv Mv.
assert (E9 : ew (Eimg (Ereg regs [Z_to_bv 64 v])) 9 = Z_to_bv 64 A)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 v])) 32 = Z_to_bv 64 v)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB9 : base_val (Eimg (Ereg regs [Z_to_bv 64 v])) (Some 9%nat) = A)
  by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- unfold rbn8_rr. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ A od 8 (SOff 32 0) v); [exact (rbn8_denot0 _ 32 v E32 Hv) | exact Hv | cbn; lia | exact Mv].
- unfold rbn8_rr. cbn. tauto.
- unfold facts_ok. cbn. tauto.
Qed.
Lemma rbn8_denotc : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv Hc. rewrite denot_lit_U. f_equal. apply (U_atom_off E n v c H Hv Hc).
Qed.
Lemma rbn8_p2 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A v : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> 0 <= A -> A + 96 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 40) 8 v ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L5X) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_dec) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 1; 10; 11; 12] /\
       getr regs1 1 = w64 (BASE + AF_both3_reac_box_name + 0x5c4) /\ getr regs1 10 = w64 (A + 88) /\
       getr regs1 11 = w64 v /\ getr regs1 12 = w64 1 /\
       (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a)).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A v HJ H9 HA0 HA1 Hv Mv.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (rbn8_call_entry fq regs W memc 15476 A 40 v ltac:(vm_compute; reflexivity) H9 HA0 ltac:(lia) ltac:(lia) Hv Mv) as HS.
set (E := Eimg (Ereg regs [Z_to_bv 64 v])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E9 : ew E 9 = Z_to_bv 64 A)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E240 : ew E 240 = Z_to_bv 64 BASE)
  by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; split; [apply Nat.leb_le | apply Nat.ltb_lt]; reflexivity).
assert (Dra : sv_denot E (SOff 240 15492) = Z_to_bv 64 (BASE + 15492)) by (apply rbn8_denotc; [exact E240 | lia | lia]).
assert (Drec : sv_denot E (SOff 9 88) = Z_to_bv 64 (A + 88)) by (apply rbn8_denotc; [exact E9 | lia | lia]).
assert (Dv : sv_denot E (SOff 32 0) = Z_to_bv 64 v) by exact (rbn8_denot0 E 32 v E32 Hv).
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (rewrite denot_lit_U; reflexivity).
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
unfold cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN_L5X) with (BASE + 15476) by (unfold AF_both3_reac_box_name, RBN_L5X; lia).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (rbn8_frame_eq E _ W memc _ (fun _ => False) HFr
  ltac:(intros a (r & Hr & Hw); unfold rbn8_rr in Hr; cbn [In] in Hr; destruct Hr as [<- | []];
        cbn [YP09.r_wlo YP09.r_whi] in Hw; lia)) as KEQ.
rreg_by HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15492)) Dra G1.
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (A + 88)) Drec G10.
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 v) Dv G11.
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 1) D1 G12.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 1; 10; 11; 12])
  by (apply (rbn8_keep (w_H W) _ _ regs _ _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [unfold cfg_at, w64; rewrite pa_sigma_sb_dec; reflexivity|].
split; [exact HJ|]. split; [exact HKP|].
split; [unfold w64; rewrite G1; f_equal; unfold AF_both3_reac_box_name; lia|].
split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
intros a Ha. exact (KEQ a Ha (fun H => H)).
Qed.
Lemma rbn8_p4 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A v : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> 0 <= A -> A + 96 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 48) 8 v ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L6X) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_dec) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 1; 10; 11; 12] /\
       getr regs1 1 = w64 (BASE + AF_both3_reac_box_name + RBN_P9) /\ getr regs1 10 = w64 (A + 88) /\
       getr regs1 11 = w64 v /\ getr regs1 12 = w64 1 /\
       (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a)).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A v HJ H9 HA0 HA1 Hv Mv.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (rbn8_call_entry fq regs W memc 15568 A 48 v ltac:(vm_compute; reflexivity) H9 HA0 ltac:(lia) ltac:(lia) Hv Mv) as HS.
set (E := Eimg (Ereg regs [Z_to_bv 64 v])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E9 : ew E 9 = Z_to_bv 64 A)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E240 : ew E 240 = Z_to_bv 64 BASE)
  by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; split; [apply Nat.leb_le | apply Nat.ltb_lt]; reflexivity).
assert (Dra : sv_denot E (SOff 240 15584) = Z_to_bv 64 (BASE + 15584)) by (apply rbn8_denotc; [exact E240 | lia | lia]).
assert (Drec : sv_denot E (SOff 9 88) = Z_to_bv 64 (A + 88)) by (apply rbn8_denotc; [exact E9 | lia | lia]).
assert (Dv : sv_denot E (SOff 32 0) = Z_to_bv 64 v) by exact (rbn8_denot0 E 32 v E32 Hv).
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (rewrite denot_lit_U; reflexivity).
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
unfold cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN_L6X) with (BASE + 15568) by (unfold AF_both3_reac_box_name, RBN_L6X; lia).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (rbn8_frame_eq E _ W memc _ (fun _ => False) HFr
  ltac:(intros a (r & Hr & Hw); unfold rbn8_rr in Hr; cbn [In] in Hr; destruct Hr as [<- | []];
        cbn [YP09.r_wlo YP09.r_whi] in Hw; lia)) as KEQ.
rreg_by HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15584)) Dra G1.
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (A + 88)) Drec G10.
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 v) Dv G11.
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 1) D1 G12.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 1; 10; 11; 12])
  by (apply (rbn8_keep (w_H W) _ _ regs _ _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [unfold cfg_at, w64; rewrite pa_sigma_sb_dec; reflexivity|].
split; [exact HJ|]. split; [exact HKP|].
split; [unfold w64; rewrite G1; f_equal; unfold AF_both3_reac_box_name, RBN_P9; lia|].
split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
intros a Ha. exact (KEQ a Ha (fun H => H)).
Qed.
Lemma rbn8_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma rbn8_stk_eq : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  ly_stk_lo lyc1 = ly_stk_lo (ri_ly X) /\ ly_stk_hi lyc1 = ly_stk_hi (ri_ly X).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
destruct HM as ((_ & L1 & _) & _).
destruct L1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). split; assumption.
Qed.
Lemma rbn8_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_A X mod 32 = 0 /\ rbn_SP X + 16 <= 2 ^ 47 /\
  ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  ly_stk_lo (ri_ly X) + ri_STK X <= ri_sp0 X /\ ri_sp0 X <= ly_stk_hi (ri_ly X) /\ rbn_SP X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
rewrite WS in Hstk. unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
repeat split; lia.
Qed.
Lemma rbn8_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (rbn8_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite Hfb3. exact Ha.
Qed.
Lemma rbn8_F_img : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  rbn_F X pos <= a < rbn_F X pos + 512 -> a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a HX HM Ha.
pose proof (rbn8_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HAR1 as (_ & LG & _). destruct (pa_img_cover lyc1 Sc1 mdc1 LG) as [C1 C2].
assert (Hz : ~ in_zr a (ly_img lyc1)).
{ refine (proj1 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite FA. change (fs_frame_bytes 3) with 512. exact Ha. }
unfold in_zr in Hz. lia.
Qed.
Lemma rbn8_stk_shadow : forall lyc Sc W mem md a n,
  AR SEGS B lyc Sc W mem md ->
  ly_stk_lo lyc + 64 <= a -> a + n + 64 <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros lyc Sc W mem md a n HAR H1 H2 Hn.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  (or_introl eq_refl)) as HZ.
cbn [fst snd] in HZ.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & HPlo & HPhi & _).
unfold page_aligned in HPlo, HPhi.
assert (Hz : forall x, ly_stk_lo lyc <= x < ly_stk_hi lyc -> aview SEGS (w_H W) mem (shadow_addr x) = Some 0).
{ intros x Hx.
  pose proof (HZ (x / 8 - ly_stk_lo lyc / 8) ltac:(lia)) as E.
  unfold shadow_of_addr in E. unfold shadow_addr.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
  exact E. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply Hz. lia.
- intros s Hs.
  assert (Hx : shadow_addr (8 * (s - SHADOW_OFF)) = s) by (unfold shadow_addr; lia).
  rewrite <- Hx. rewrite Hz; [discriminate|]. unfold shadow_addr in Hs. lia.
Qed.
Definition rbn8_step (X : rbn_in) (lyc1 : alayout) (Sc1 : astate) (W W' : world SEGS)
  (m m' : word -> option byte) (Er : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - 4256 <= a < rbn_A X) ->
     ~ (rbn_A X + 104 <= a < rbn_A X + 116) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
  (forall b mm j, In (b, mm) (ablocks B lyc1 Sc1) -> 0 <= j < req_size mm -> ~ Er (b + j) ->
     aview SEGS (w_H W') m' (b + j) = aview SEGS (w_H W) m (b + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
  (forall cid p a, In (cid, p) (frames Sc1) ->
     (in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)) ->
     ~ Er a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - 4256 <= a < rbn_A X) ->
     apresent (w_H W) m a -> apresent (w_H W') m' a).
Lemma rbn8_mid_step : forall X pos lyc1 Sc1 W1 m md lyc2 Sc2 W2 m2 md2 sh (Er : Z -> Prop),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 m2 md2 (ri_k X) ->
  frames Sc2 = frames Sc1 -> Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  rbn8_step X lyc1 Sc1 W1 W2 m m2 Er ->
  (forall a, Er a -> rbn_F X pos <= a < rbn_F X pos + 504) ->
  Z.of_nat (length sh) <= 64 ->
  rbn_mid B X pos lyc2 Sc2 W2 m2 md2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 m md lyc2 Sc2 W2 m2 md2 sh Er HX HM HJ2 Hfr2 Hperm2 HST HEr Hsh.
destruct HST as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn8_fa X pos lyc1 Sc1 W1 m md _ sh HX HM) as FA.
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md _ sh HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
unfold rbn_mid. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|].
split; [exact (Permutation_trans Hperm2 Hperm)|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  rewrite (C3 a Hia Ho He). exact (Hro a Hro0 Ho He). }
split.
{ unfold rbn_kept. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' He. rewrite (C1 a Ha) by (unfold rbn_SP in *; lia). exact (K1 a Ha Hn' He).
  - intros b mm j Hb Hj He.
    assert (Hb1 : In (b, mm) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb1) as (_ & Hb4 & Hbc & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b mm 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    rewrite (C2 b mm j Hb1 Hj ltac:(intros He2; pose proof (HEr _ He2); lia)).
    exact (K2 b mm j Hb Hj He).
  - intros a Hia Ho He. rewrite (C3 a Hia Ho He). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    rewrite FA in Hc4096, Hcceil.
    assert (HnE : ~ Er a).
    { intros He2. pose proof (HEr a He2) as HEa. destruct Ha as [Ha | Ha].
      - destruct (in_split _ _ Hcp) as (l2 & l3 & El).
        pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
          ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
        unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !FA, Hfb3 in Hd.
        unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. unfold rbn_F in HEa. lia.
      - unfold in_zr in Ha. cbn [fst snd] in Ha.
        pose proof (rbn8_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
          (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
        destruct (Happ a ltac:(lia)); unfold kLowShadowBeg, kHighMemBeg in *; lia. }
    assert (Ha1 : in_zr a (frame_rng lyc1 (cid, p)) \/
      in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8))
      by (unfold frame_rng in Ha |- *; cbn [fst snd] in Ha |- *; rewrite !FA; exact Ha).
    rewrite (C4 cid p a Hcp1 Ha1 HnE). exact (K4 cid p a Hcp Ha He).
  - intros a Ha Hn' Hp. apply C5; [lia | unfold rbn_SP in *; lia | exact (K5 a Ha Hn' Hp)].
  - intros a Ha. apply Hpres2. unfold rbn_SP in *. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m2); [|exact (Hfr j r Hj)].
  intros kk Hk. apply C1; unfold rbn_SP in *; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m2); [|exact Hfl].
  intros kk Hk. apply (C4 3 pos); [exact Hin3 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3, Hfb3; lia|].
  intros He2. pose proof (HEr _ He2). lia. }
unfold rbn_shadow_at. intros j Hj.
pose proof (rbn8_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
assert (HnS : ~ Er (shadow_addr (rbn_F X pos) + j)).
{ intros He2. pose proof (HEr _ He2) as HE2.
  destruct (Happ (shadow_addr (rbn_F X pos) + j) ltac:(lia)) as [Hq | Hq];
  unfold kLowShadowBeg, kHighMemBeg in *; lia. }
rewrite (C4 3 pos (shadow_addr (rbn_F X pos) + j) Hin3
  ltac:(right; unfold in_zr; cbn [fst snd]; rewrite FA3, Hfb3; change (512 / 8) with 64; lia) HnS).
exact (Hsh0 j Hj).
Qed.
Definition rbn8_inv (X : rbn_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (m : word -> option byte) (md : Model) (wr : list Z) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) (rbn_sh true true true true) /\
  rbn_cells (mrestrict (w_H W1) m) (rbn8_cells X pos) /\
  rbn_cells (mrestrict (w_H W1) m) (rbn_rd X pos (Z.of_nat (length wr)) 0) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 128) (rbm_TB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 192) wr /\
  Z.of_nat (length wr) <= 47.
Lemma rbn8_inv_step : forall X pos lyc1 Sc1 W1 m md wr lyc2 Sc2 W2 m2 md2 w,
  rbn_cx B X -> rbn8_inv X pos lyc1 Sc1 W1 m md wr ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 m2 md2 (ri_k X) ->
  frames Sc2 = frames Sc1 -> Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  rbn8_step X lyc1 Sc1 W1 W2 m m2
    (fun a => rbn_F X pos + 192 + Z.of_nat (length wr) <= a <
       rbn_F X pos + 192 + Z.of_nat (length wr) + Z.of_nat (length w)) ->
  val_mem SEGS (mrestrict (w_H W2) m2) (rbn_A X + 104) 8 (Z.of_nat (length wr) + Z.of_nat (length w)) ->
  val_mem SEGS (mrestrict (w_H W2) m2) (rbn_A X + 112) 4 0 ->
  garr8 SEGS (mrestrict (w_H W2) m2) (rbn_F X pos + 192 + Z.of_nat (length wr)) w ->
  Z.of_nat (length wr) + Z.of_nat (length w) <= 47 ->
  rbn8_inv X pos lyc2 Sc2 W2 m2 md2 (wr ++ w).
Proof.
intros X pos lyc1 Sc1 W1 m md wr lyc2 Sc2 W2 m2 md2 w HX (HM & HC & HD & G64 & G128 & G192 & Hlw)
  HJ2 Hfr2 Hperm2 HST V104 V112 GW Hlen.
pose proof (rbn8_fa X pos lyc1 Sc1 W1 m md _ _ HX HM) as FA.
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
pose proof HM as (HJ1 & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HST as (C1 & C2 & C3 & C4 & C5).
assert (KF : forall a, rbn_F X pos <= a < rbn_F X pos + 192 + Z.of_nat (length wr) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m a).
{ intros a Ha. apply (C4 3 pos a Hin3);
  [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3; change (fs_frame_bytes 3) with 512; lia | cbv beta; lia]. }
assert (KS : forall a, rbn_A X <= a < rbn_A X + 104 \/ rbn_A X + 116 <= a < rbn_A X + 212 ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m a) by (intros a Ha; apply C1; lia).
pose proof (rbn8_NB_len X) as NBl. pose proof (rbn8_TB_len X) as TBl.
split.
{ apply (rbn8_mid_step X pos lyc1 Sc1 W1 m md lyc2 Sc2 W2 m2 md2 _ _ HX HM HJ2 Hfr2 Hperm2 HST);
  [intros a Ha; cbv beta in Ha; lia | rewrite rbn8_sh_len; lia]. }
split.
{ apply (rbn8_cells_kept (w_H W1) (w_H W2) m m2); [|exact HC].
  intros a n v k Hin Hk. pose proof (rbn8_cells_rng X pos a n v Hin). apply KS. lia. }
split.
{ unfold rbn_rd in HD |- *. cbn [rbn_cells] in HD |- *. destruct HD as (D0 & D8 & _ & _ & _).
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m2); [intros k Hk; apply KS; lia | exact D0]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m2); [intros k Hk; apply KS; lia | exact D8]|].
  split; [rewrite length_app, Nat2Z.inj_add; exact V104|]. split; [exact V112 | exact I]. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact G64|]. intros a Ha.
  rewrite length_app in Ha. cbn [length] in Ha. apply (mbyte_of_aview SEGS). apply KF. lia. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact G128|]. intros a Ha.
  rewrite length_app in Ha. cbn [length] in Ha. apply (mbyte_of_aview SEGS). apply KF. lia. }
split.
{ apply garr8_app. split; [|exact GW].
  apply (garr8_frame SEGS (mrestrict (w_H W1) m)); [exact G192|]. intros a Ha.
  apply (mbyte_of_aview SEGS). apply KF. lia. }
rewrite length_app. lia.
Qed.
Lemma rbn8_inv_eq : forall X pos lyc1 Sc1 W1 m md wr m2 md2,
  rbn_cx B X -> rbn8_inv X pos lyc1 Sc1 W1 m md wr ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  rbn8_inv X pos lyc1 Sc1 W1 m2 md2 wr.
Proof.
intros X pos lyc1 Sc1 W1 m md wr m2 md2 HX HI HJ2 KEQ.
pose proof HI as (HM & HC & HD & _).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _).
pose proof asan_consts as (CC1 & _).
assert (HB : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) by exact KEQ.
rewrite <- (app_nil_r wr).
apply (rbn8_inv_step X pos lyc1 Sc1 W1 m md wr lyc1 Sc1 W1 m2 md2 [] HX HI HJ2 eq_refl (Permutation_refl _)).
- split; [intros a Ha _ _; apply HB; lia|].
  split; [intros b mm j Hb Hj _; apply HB; pose proof HM as (HJ1 & _);
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm (proj1 HJ1) Hb) as (_ & Hb4 & Hbc & _); lia|].
  split; [intros a Hia _ _; apply HB; pose proof (pa_segs_low a Hia) as Hl; unfold kLowMemEnd in Hl; lia|].
  split.
  + intros cid p a Hcp Ha _. pose proof HM as (HJ1 & _).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p (proj1 HJ1) Hcp) as (Hc4096 & Hcceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (Z.mul_div_le (frame_addr lyc1 cid p) 8 ltac:(lia)) as D1.
    pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
    pose proof (Z.div_pos (frame_addr lyc1 cid p) 8 ltac:(lia) ltac:(lia)) as D3.
    pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
    apply HB. destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha; cbn [fst snd] in Ha; lia.
  + intros a Ha _ Hp. apply (apresent_transfer SEGS (w_H W1) (w_H W1) m m2 a);
    [lia | intros Hi; pose proof (pa_segs_low a Hi) as Hl; unfold kLowMemEnd in Hl; lia | apply HB; lia | exact Hp].
- unfold rbn_rd in HD. cbn [rbn_cells] in HD. destruct HD as (_ & _ & D16 & _).
  cbn [length]. rewrite Z.add_0_r. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m2); [|exact D16].
  intros k Hk. apply HB. lia.
- unfold rbn_rd in HD. cbn [rbn_cells] in HD. destruct HD as (_ & _ & _ & D24 & _).
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m2); [|exact D24].
  intros k Hk. apply HB. lia.
- apply garr8_nil.
- pose proof HI as (_ & _ & _ & _ & _ & _ & Hlw). cbn [length]. lia.
Qed.
Definition rbn8_regs (X : rbn_in) (pos : Z) (regs : bvmap 5 word) : Prop :=
  rbn_rbase B X pos regs /\ getr regs 18 = w64 (rbn_SH X pos) /\ getr regs 25 = w64 (rbn_F X pos + 128) /\
  getr regs 26 = w64 (rbn_F X pos + 192) /\ getr regs 27 = w64 (rbn_F X pos + 64).
Lemma rbn8_regs_keep : forall X pos (regs regs2 : bvmap 5 word) cl,
  rbn8_regs X pos regs -> rbn_keep_regs regs regs2 cl ->
  existsb (Z.eqb 2) cl = false /\ existsb (Z.eqb 3) cl = false /\ existsb (Z.eqb 4) cl = false /\
  existsb (Z.eqb 8) cl = false /\ existsb (Z.eqb 9) cl = false /\ existsb (Z.eqb 18) cl = false /\
  existsb (Z.eqb 19) cl = false /\ existsb (Z.eqb 22) cl = false /\ existsb (Z.eqb 23) cl = false /\
  existsb (Z.eqb 25) cl = false /\ existsb (Z.eqb 26) cl = false /\ existsb (Z.eqb 27) cl = false ->
  rbn8_regs X pos regs2.
Proof.
intros X pos regs regs2 cl ((B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23) & R18 & R25 & R26 & R27) HK
  (N2 & N3 & N4 & N8 & N9 & N18 & N19 & N22 & N23 & N25 & N26 & N27).
unfold rbn8_regs, rbn_rbase.
rewrite (rbn8_keep_get regs regs2 cl (2%bv : bv 5) HK N2), (rbn8_keep_get regs regs2 cl (3%bv : bv 5) HK N3),
  (rbn8_keep_get regs regs2 cl (4%bv : bv 5) HK N4), (rbn8_keep_get regs regs2 cl (8%bv : bv 5) HK N8),
  (rbn8_keep_get regs regs2 cl (9%bv : bv 5) HK N9), (rbn8_keep_get regs regs2 cl (18%bv : bv 5) HK N18),
  (rbn8_keep_get regs regs2 cl (19%bv : bv 5) HK N19), (rbn8_keep_get regs regs2 cl (22%bv : bv 5) HK N22),
  (rbn8_keep_get regs regs2 cl (23%bv : bv 5) HK N23), (rbn8_keep_get regs regs2 cl (25%bv : bv 5) HK N25),
  (rbn8_keep_get regs regs2 cl (26%bv : bv 5) HK N26), (rbn8_keep_get regs regs2 cl (27%bv : bv 5) HK N27).
repeat split; assumption.
Qed.
Lemma rbn8_regs_pres : forall X pos (regs regs2 : bvmap 5 word),
  rbn8_regs X pos regs -> aregs_preserved regs regs2 -> rbn8_regs X pos regs2.
Proof.
intros X pos regs regs2 ((B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23) & R18 & R25 & R26 & R27) HP.
unfold rbn8_regs, rbn_rbase.
rewrite (rbn8_pres_get regs regs2 (2%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (3%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (4%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (8%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (9%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (18%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (19%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (22%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (23%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (25%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (26%bv : bv 5) HP) by rbn8cs.
rewrite (rbn8_pres_get regs regs2 (27%bv : bv 5) HP) by rbn8cs.
repeat split; assumption.
Qed.
Lemma rbn8_io : forall X pos lyc1 Sc1 W1 m md wr, rbn8_inv X pos lyc1 Sc1 W1 m md wr ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 40) 8 (ri_i X) /\
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 48) 8 (ri_o X).
Proof.
intros X pos lyc1 Sc1 W1 m md wr (_ & HC & _).
unfold rbn8_cells in HC. apply rbn8_cells_app in HC as [HC _].
unfold rbn_argc in HC. cbn [rbn_cells] in HC.
destruct HC as (_ & _ & _ & _ & _ & Vi & Vo & _). split; assumption.
Qed.
Lemma rbn8_lcx : forall X pos lyc1 Sc1 W1 m md wr (regs : bvmap 5 word),
  rbn_cx B X -> rbn8_inv X pos lyc1 Sc1 W1 m md wr -> rbn8_regs X pos regs ->
  spZ regs = rbn_A X /\
  rbn_lcx B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) regs.
Proof.
intros X pos lyc1 Sc1 W1 m md wr regs HX (HM & _) ((B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23) & _).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & _).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HM as (HJ1 & _ & _ & Hro & _).
assert (Hsp : spZ regs = rbn_A X) by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; lia).
split; [exact Hsp|].
unfold rbn_lcx. split; [exact HJ1|]. split; [exact Hro|]. split; [exact B3|]. split; [exact B4|].
split; [rewrite B9, B2; reflexivity|]. split; [exact B22|]. rewrite Hsp, HTS.
split; [lia|]. split; lia.
Qed.
Lemma rbn8_rb : forall X pos lyc1 Sc1 W1 m md wr,
  rbn_cx B X -> rbn8_inv X pos lyc1 Sc1 W1 m md wr ->
  rbn_lrec B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 m
    (rbn_A X) (rbn_A X + 88) (rbn_F X pos + 192) 48 (Z.of_nat (length wr)) 0 /\
  rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 m
    (rbn_A X) (rbn_A X + 88) (rbn_F X pos + 192) 48.
Proof.
intros X pos lyc1 Sc1 W1 m md wr HX (HM & HC & HD & G64 & G128 & G192 & Hlw).
pose proof (rbn8_fa X pos lyc1 Sc1 W1 m md _ _ HX HM 3 pos) as FA.
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
destruct (rbn8_stk_eq X pos lyc1 Sc1 W1 m md _ _ HM) as [Elo Ehi].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & _ & _ & _ & Hsh0).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPst & _).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
pose proof (rbn8_F_img X pos lyc1 Sc1 W1 m md _ _ (rbn_F X pos + 192) HX HM ltac:(lia)) as I1.
pose proof (rbn8_F_img X pos lyc1 Sc1 W1 m md _ _ (rbn_F X pos + 239) HX HM ltac:(lia)) as I2.
unfold rbn_rd in HD. cbn [rbn_cells] in HD. destruct HD as (D0 & D8 & D16 & D24 & _).
split.
{ unfold rbn_lrec.
  destruct (rbn8_stk_shadow lyc1 Sc1 W1 m md (rbn_A X + 88) 28 HAR1 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhv].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold amem_range, kHighMemBeg, kHighMemEnd; lia|].
  split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
  split; [left; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact D0|].
  split; [replace (rbn_A X + 88 + 8) with (rbn_A X + 96) by lia; exact D8|].
  split; [replace (rbn_A X + 88 + 16) with (rbn_A X + 104) by lia; exact D16|].
  split; [replace (rbn_A X + 88 + 24) with (rbn_A X + 112) by lia; exact D24|].
  split; [exact Hra|]. split; [exact Hhv|].
  intros a Ha. split; [left; lia | apply HPst; lia]. }
unfold rbn_lbuf.
split; [lia|]. split; [lia|]. split; [apply (in_app_sub _ _ _ _ HFapp); lia|].
split; [unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
split; [right; rewrite HTS; lia|]. split; [left; lia|].
split.
{ apply zero_shadow_range; [lia | reflexivity |].
  intros i Hi. change (48 / 8) with 6 in Hi.
  replace (shadow_of_addr SHADOW_OFF (rbn_F X pos + 192) + i) with (rbn_SH X pos + (24 + i))
    by (unfold rbn_SH, shadow_addr, shadow_of_addr; lia).
  rewrite (Hsh0 (24 + i)) by (rewrite rbn8_sh_len; lia).
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia;
  reflexivity. }
split.
{ intros sx Hsx.
  assert (Hj : 0 <= sx - rbn_SH X pos < 64) by (unfold rbn_SH, shadow_addr in *; lia).
  pose proof (Hsh0 (sx - rbn_SH X pos) ltac:(rewrite rbn8_sh_len; lia)) as E.
  replace (rbn_SH X pos + (sx - rbn_SH X pos)) with sx in E by lia. rewrite E. discriminate. }
intros a Ha. split; [|exact (proj1 (HFpr a ltac:(lia)))].
right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
change (fs_frame_bytes 3) with 512. lia.
Qed.
Lemma rbn8_step_of : forall X pos lyc1 Sc1 W1 m md sh W2 m2 STKc (E Er : Z -> Prop),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) sh -> 0 <= STKc <= 4256 ->
  (forall a, E a -> (rbn_A X + 104 <= a < rbn_A X + 116) \/ Er a) ->
  (forall a, Er a -> rbn_F X pos <= a < rbn_F X pos + 512) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - STKc <= a < rbn_A X) -> ~ E a ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m a) ->
  (forall b mm j, In (b, mm) (ablocks B lyc1 Sc1) -> 0 <= j < req_size mm -> ~ E (b + j) ->
     aview SEGS (w_H W2) m2 (b + j) = aview SEGS (w_H W1) m (b + j)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m a) ->
  (forall cid p a, In (cid, p) (frames Sc1) ->
     (in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - STKc <= a < rbn_A X) ->
     apresent (w_H W1) m a -> apresent (w_H W2) m2 a) ->
  rbn8_step X lyc1 Sc1 W1 W2 m m2 Er.
Proof.
intros X pos lyc1 Sc1 W1 m md sh W2 m2 STKc E Er HX HM HSK HE HEr K1 K2 K3 K4 K5.
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md _ sh HX HM) as (HF4096 & HFceil & _).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & _).
pose proof asan_consts as (C1 & _).
pose proof HM as (HJ1 & _). pose proof (proj1 HJ1) as HAR1.
split; [|split; [|split; [|split]]].
- intros a Ha H1 H2. apply K1; [exact Ha | lia |]. intros HEa.
  destruct (HE a HEa) as [Hx | Hx]; [lia | pose proof (HEr a Hx); lia].
- intros b mm j Hb Hj HnE. apply (K2 b mm j); [exact Hb | exact Hj |]. intros HEa.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb) as (_ & Hb4 & Hbc & _).
  destruct (HE _ HEa) as [Hx | Hx]; [lia | exact (HnE Hx)].
- exact K3.
- intros cid p a Hcp Ha HnE. apply (K4 cid p a); [exact Hcp | exact Ha |]. intros HEa.
  destruct (HE _ HEa) as [Hx | Hx]; [|exact (HnE Hx)].
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp) as (Hc4096 & Hcceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (Z.mul_div_le (frame_addr lyc1 cid p) 8 ltac:(lia)) as D1.
  pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
  pose proof (Z.div_pos (frame_addr lyc1 cid p) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
  destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha; cbn [fst snd] in Ha; lia.
- intros a Ha H1 Hp. apply K5; [exact Ha | lia | exact Hp].
Qed.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Lemma rbn8_lsrc : forall X pos lyc1 Sc1 W1 m md sh q s,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) sh ->
  rbn_lit (ri_W X) (ri_memc X) q s -> rbn_ro q (Z.of_nat (length s) + 1) ->
  rbn_lsrc W1 m q (s ++ [0]) /\ q mod 8 = 0 /\
  rbn_lsep (rbn_A X) (rbn_A X + 88) (rbn_F X pos + 192) 48 q (Z.of_nat (length s) + 1).
Proof.
intros X pos lyc1 Sc1 W1 m md sh q s HX HM (Lg & Lra & Li) Hro.
destruct (rbn8_globs q _ Hro) as (Q32 & Q0 & Q1 & Q2 & _).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _).
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md _ sh HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HM as (HJ1 & _ & _ & _ & (_ & _ & K3 & _) & _).
pose proof (tfib_ro_unowned_at B q _ DRO ltac:(apply in_or_app; left; exact Hro)) as HU.
split.
{ split.
  - apply (garr8_frame SEGS (mrestrict (w_H (ri_W X)) (ri_memc X))); [exact Lg|]. intros a Ha.
    rewrite length_app in Ha. cbn [length] in Ha.
    destruct (HU a ltac:(lia)) as [U1 U2].
    apply (mbyte_of_aview SEGS). apply K3; [apply Li; lia | exact U1 | exact U2].
  - rewrite length_app. cbn [length]. split; [lia|]. split; [lia|]. split; [lia|].
    replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia.
    exact (ro_usable_glob SEGS B tfib_globs lyc1 Sc1 W1 m md q (Z.of_nat (length s) + 1) q
      (Z.of_nat (length s) + 1) GM Hro (proj1 HJ1) ltac:(lia) ltac:(lia)). }
split; [lia|].
unfold rbn_lsep. split; [|split; rewrite ?HTS; lia].
destruct (Z_le_gt_dec (q + (Z.of_nat (length s) + 1)) (rbn_F X pos + 192)) as [Hl | Hl]; [left; exact Hl|].
destruct (Z_le_gt_dec (rbn_F X pos + 192 + 48) q) as [Hr | Hr]; [right; exact Hr|].
exfalso. set (x := Z.max q (rbn_F X pos + 192)).
apply (proj2 (HFpr x ltac:(unfold x; lia))). apply Li. unfold x; lia.
Qed.
Hypothesis HSBDEC : tsb_dec_spec B.
Lemma rbn8_dec : forall X pos lyc1 Sc1 W1 m md wr v (regs : bvmap 5 word) (Q : world SEGS -> config -> Prop),
  rbn_cx B X -> rbn8_inv X pos lyc1 Sc1 W1 m md wr ->
  getr regs 2 = w64 (rbn_A X) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (rbn_A X + 88) -> getr regs 11 = w64 v -> getr regs 12 = w64 1 ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  bn_ok v = true -> Z.of_nat (length wr) <= 45 ->
  (forall lyc2 Sc2 W2 (regs2 : bvmap 5 word) m2 md2,
     rbn8_inv X pos lyc2 Sc2 W2 m2 md2 (wr ++ bn_dec v 1) -> aregs_preserved regs regs2 ->
     SRr SEGS W2 (mkCfg (mkst (fx := ri_fq X) regs2 (getr regs 1) m2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W1 (cfg_at (fx := ri_fq X) SEGS (BASE + AF_both3_sb_dec) regs m md) Q.
Proof.
intros X pos lyc1 Sc1 W1 m md wr v regs Q HX HI G2 G3 G4 G10 G11 G12 Hra Hra4 Hv Hl K.
pose proof HI as (HM & _ & _ & _ & _ & _ & Hlw).
destruct (rbn8_rb X pos lyc1 Sc1 W1 m md wr HX HI) as (Hrec & Hbuf).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HM as (HJ1 & Hfrs & _ & Hro & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPst & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrl & _).
assert (HDS : SB_DEC_STK = 4256) by reflexivity.
assert (Hsp : spZ regs = rbn_A X) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
pose proof (rbn8_ok_rng v Hv) as Vr. pose proof (rbn8_dec_len v Hv) as DL. pose proof (rbn8_dec_eq v Hv) as DE.
destruct (rbn8_sbd v (Z.of_nat (length wr)) ltac:(lia) ltac:(rewrite DE; lia)) as (SR & SA & SL).
destruct Hrec as (R0 & R8 & R63 & Ram & Rimg & Rsp & RD & Rcap & Rn & Rn1 & Rov & V0 & V8 & V16 & V24 & Rra & Rhv & Rwr).
destruct Hbuf as (D0 & D63 & Dapp & Dam & Dimg & Dsp & DR & Dra & Dhv & Dwr).
assert (S0 : s0Z (regupd regs 8 (Z_to_bv 64 0)) = 0) by (unfold s0Z; rewrite getr_same by reg_neq_tac; reflexivity).
assert (HCH : achain lyc1 (aview SEGS (w_H W1) m) (spZ regs) (s0Z (regupd regs 8 (Z_to_bv 64 0))) [])
  by (left; split; [left; rewrite S0; lia | reflexivity]).
assert (HFL : Z.of_nat (length (frames Sc1)) <= 9) by (rewrite Hfrs; cbn [length]; lia).
assert (HAW : forall a, rbn_A X + 88 <= a < rbn_A X + 88 + 28 ->
  awr_byte (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B lyc1 Sc1) lyc1
    ((3, pos) :: ri_own X) a /\ apresent (w_H W1) m a)
  by (intros a Ha; split; [left; lia | apply HPst; lia]).
assert (HROOM : 0 < sb_dec_c.sb_dec_room 48 (Z.of_nat (length wr)) ->
  0 < rbn_F X pos + 192 /\
  rbn_F X pos + 192 + Z.of_nat (length wr) + sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr)) <= 2 ^ 63 /\
  amem_range (rbn_F X pos + 192 + Z.of_nat (length wr)) (sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr))) /\
  off_img (rbn_F X pos + 192 + Z.of_nat (length wr)) (sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr))) /\
  (rbn_F X pos + 192 + Z.of_nat (length wr) + sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr)) <= rbn_A X + 88 \/
   rbn_A X + 88 + 28 <= rbn_F X pos + 192 + Z.of_nat (length wr)) /\
  (spZ regs <= rbn_F X pos + 192 + Z.of_nat (length wr) \/
   rbn_F X pos + 192 + Z.of_nat (length wr) + sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr)) <= spZ regs - SB_DEC_STK) /\
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (rbn_F X pos + 192 + Z.of_nat (length wr))
    (sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr))) /\
  shadow_hull_vis (aview SEGS (w_H W1) m) (rbn_F X pos + 192 + Z.of_nat (length wr))
    (sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr))) /\
  (forall a, rbn_F X pos + 192 + Z.of_nat (length wr) <= a <
       rbn_F X pos + 192 + Z.of_nat (length wr) + sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr)) ->
     awr_byte (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B lyc1 Sc1) lyc1
       ((3, pos) :: ri_own X) a /\ apresent (w_H W1) m a)).
{ intros _. rewrite SA, DE, Hsp, HDS.
  split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split; [unfold off_img in *; lia|].
  split; [left; lia|]. split; [right; lia|].
  split; [apply (range_addressable_sub _ _ _ _ _ _ Dra); lia|].
  split; [apply (rbn8_hull_sub _ _ _ _ _ Dhv); lia|].
  intros a Ha. apply Dwr. lia. }
eapply SRr_bind.
{ apply (HSBDEC (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) regs [] (rbn_A X + 88) v 1 (rbn_F X pos + 192) 48
    (Z.of_nat (length wr)) 0 HJ1 Hro Hra Hra4 G3 G4 G10 G11 G12 HCH);
  first [ exact HROOM | rewrite ?Hsp, ?HDS;
  first [ exact HFL | exact V0 | exact V8 | exact V16 | exact V24 | exact Rra | exact Rhv | exact HAW
        | exact R0 | exact R8 | exact R63 | exact Ram | exact Rimg | lia | (left; lia) | (left; reflexivity) ] ]. }
intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & -> & HJ2 & HP & Hfr2 & Hperm2 & K1 & K2 & K3 & K4 & P1 & P2 &
  VA & VA8 & VA16 & VA24 & GW).
rewrite Hsp, HDS in K1, P1.
apply (K ly2 S2 W2 regs2 m2 md2); [|exact HP].
apply (rbn8_inv_step X pos lyc1 Sc1 W1 m md wr ly2 S2 W2 m2 md2 (bn_dec v 1) HX HI HJ2 Hfr2 Hperm2).
- apply (rbn8_step_of X pos lyc1 Sc1 W1 m md _ W2 m2 4256
    (fun a => (rbn_A X + 88 + 16 <= a < rbn_A X + 88 + 28) \/
       (0 < sb_dec_c.sb_dec_room 48 (Z.of_nat (length wr)) /\ rbn_F X pos + 192 + Z.of_nat (length wr) <= a <
          rbn_F X pos + 192 + Z.of_nat (length wr) + sb_dec_c.sb_dec_acc v 1 48 (Z.of_nat (length wr))))
    _ HX HM ltac:(lia)).
  + intros a [Ha | (_ & Ha)]; [left; lia | right; rewrite SA, DE in Ha; exact Ha].
  + intros a Ha. cbv beta in Ha. lia.
  + intros a Ha H1 HnE. apply K1; [exact Ha | exact H1 | intros Hx; apply HnE; left; exact Hx |
      intros Hx; apply HnE; right; exact Hx].
  + intros b mm j Hb Hj HnE. apply (K2 b mm j); [exact Hb | exact Hj | intros Hx; apply HnE; left; exact Hx |
      intros Hx; apply HnE; right; exact Hx].
  + exact K3.
  + intros cid p a Hcp Ha HnE. apply (K4 cid p a); [exact Hcp | exact Ha | intros Hx; apply HnE; left; exact Hx |
      intros Hx; apply HnE; right; exact Hx].
  + intros a Ha H1 Hp. apply P1; [exact Ha | exact H1 | exact Hp].
- replace (rbn_A X + 104) with (rbn_A X + 88 + 16) by lia. rewrite SA, DE in VA16. exact VA16.
- replace (rbn_A X + 112) with (rbn_A X + 88 + 24) by lia. rewrite SL in VA24. exact VA24.
- specialize (GW ltac:(rewrite SR; lia)). rewrite SA, Nat2Z.id, firstn_all, DE in GW. exact GW.
- lia.
Qed.
Hypothesis L5F : rbn_L5_fits B.
Hypothesis L6F : rbn_L6_fits B.
Lemma rbn8_L5 : forall X pos lyc1 Sc1 W1 m md wr (regs : bvmap 5 word) (Q : world SEGS -> config -> Prop),
  rbn_cx B X -> rbn8_inv X pos lyc1 Sc1 W1 m md wr -> rbn8_regs X pos regs ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 28)) -> getr regs 24 = w64 2 ->
  Z.of_nat (length wr) + 2 <= 47 ->
  (forall lyc2 Sc2 W2 (regs2 : bvmap 5 word) m2 md2,
     rbn8_inv X pos lyc2 Sc2 W2 m2 md2 (wr ++ rbn_lit5) -> rbn8_regs X pos regs2 ->
     SRr SEGS W2 (rbn_cfg X RBN_L5X regs2 m2 md2) Q) ->
  SRr SEGS W1 (rbn_cfg X RBN_L5 regs m md) Q.
Proof.
intros X pos lyc1 Sc1 W1 m md wr regs Q HX HI HR G20 G21 G24 Hl K.
destruct (rbn8_lcx X pos lyc1 Sc1 W1 m md wr regs HX HI HR) as (Hsp & Hlcx).
destruct (rbn8_rb X pos lyc1 Sc1 W1 m md wr HX HI) as (Hrec & Hbuf).
pose proof HI as (HM & _).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _). pose proof asan_consts as (C1 & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
destruct Himg as (t1 & t2 & t3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L28 & L29 & L30 &
  _ & _ & _ & _ & _ & O28 & O29 & O30).
destruct (rbn8_lsrc X pos lyc1 Sc1 W1 m md _ (VAL (A_OBJ 28)) [32; 40] HX HM L28 O28) as (Hsrc & H8 & Hsep).
pose proof (L5F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) regs (rbn_F X pos + 192) (Z.of_nat (length wr)) 0 Hl) as RUN.
unfold rbn_L5_run in RUN. rewrite Hsp in RUN.
eapply SRr_bind; [apply RUN; first [exact Hlcx | exact Hrec | exact Hbuf | exact Hsrc | exact H8 | exact Hsep | lia
  | left; reflexivity | assumption] |].
intros W2 c2 _ (lyc2 & Sc2 & regs2 & m2 & md2 & -> & HJ2 & Hfr2 & Hab2 & Hro2 & HK & O16 & O24 & HG & HT).
destruct HT as (T1 & T2 & T3 & T4 & T5 & T6). rewrite Hsp in T1, T5.
apply (K lyc2 Sc2 W2 regs2 m2 md2).
- apply (rbn8_inv_step X pos lyc1 Sc1 W1 m md wr lyc2 Sc2 W2 m2 md2 rbn_lit5 HX HI HJ2 Hfr2
    ltac:(rewrite Hab2; apply Permutation_refl)).
  + apply (rbn8_step_of X pos lyc1 Sc1 W1 m md _ W2 m2 TSB_CH_STK
      (fun a => rbn_A X + 88 + 16 <= a < rbn_A X + 88 + 28 \/
         rbn_F X pos + 192 + Z.of_nat (length wr) <= a <
         rbn_F X pos + 192 + Z.of_nat (length wr) + Z.of_nat (length rbn_lit5))
      _ HX HM).
    * unfold TSB_CH_STK, ESTACK. lia.
    * intros a [Ha | Ha]; [left; lia | right; exact Ha].
    * intros a Ha. cbv beta in Ha. unfold rbn_lit5 in Ha. cbn [length] in Ha. lia.
    * intros a Ha H1 H2. apply T1; [lia | exact H1 | exact H2].
    * exact T2.
    * exact T3.
    * exact T4.
    * exact T5.
  + replace (rbn_A X + 104) with (rbn_A X + 88 + 16) by lia. exact O16.
  + replace (rbn_A X + 112) with (rbn_A X + 88 + 24) by lia. exact O24.
  + exact HG.
  + unfold rbn_lit5. cbn [length]. lia.
- apply (rbn8_regs_keep X pos regs regs2 _ HR HK). repeat split; reflexivity.
Qed.
Lemma rbn8_L6 : forall X pos lyc1 Sc1 W1 m md wr (regs : bvmap 5 word) (Q : world SEGS -> config -> Prop),
  rbn_cx B X -> rbn8_inv X pos lyc1 Sc1 W1 m md wr -> rbn8_regs X pos regs ->
  getr regs 20 = w64 0 -> getr regs 21 = w64 (VAL (A_OBJ 29)) -> getr regs 24 = w64 6 ->
  Z.of_nat (length wr) + 6 <= 47 ->
  (forall lyc2 Sc2 W2 (regs2 : bvmap 5 word) m2 md2,
     rbn8_inv X pos lyc2 Sc2 W2 m2 md2 (wr ++ rbn_lit6) -> rbn8_regs X pos regs2 ->
     SRr SEGS W2 (rbn_cfg X RBN_L6X regs2 m2 md2) Q) ->
  SRr SEGS W1 (rbn_cfg X RBN_L6 regs m md) Q.
Proof.
intros X pos lyc1 Sc1 W1 m md wr regs Q HX HI HR G20 G21 G24 Hl K.
destruct (rbn8_lcx X pos lyc1 Sc1 W1 m md wr regs HX HI HR) as (Hsp & Hlcx).
destruct (rbn8_rb X pos lyc1 Sc1 W1 m md wr HX HI) as (Hrec & Hbuf).
pose proof HI as (HM & _).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _). pose proof asan_consts as (C1 & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
destruct Himg as (t1 & t2 & t3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L28 & L29 & L30 &
  _ & _ & _ & _ & _ & O28 & O29 & O30).
destruct (rbn8_lsrc X pos lyc1 Sc1 W1 m md _ (VAL (A_OBJ 29)) [32; 105; 110; 32; 47; 32] HX HM L29 O29)
  as (Hsrc & H8 & Hsep).
pose proof (L6F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) regs (rbn_F X pos + 192) (Z.of_nat (length wr)) 0 Hl) as RUN.
unfold rbn_L6_run in RUN. rewrite Hsp in RUN.
eapply SRr_bind; [apply RUN; first [exact Hlcx | exact Hrec | exact Hbuf | exact Hsrc | exact H8 | exact Hsep | lia
  | left; reflexivity | assumption] |].
intros W2 c2 _ (lyc2 & Sc2 & regs2 & m2 & md2 & -> & HJ2 & Hfr2 & Hab2 & Hro2 & HK & O16 & O24 & HG & HT).
destruct HT as (T1 & T2 & T3 & T4 & T5 & T6). rewrite Hsp in T1, T5.
apply (K lyc2 Sc2 W2 regs2 m2 md2).
- apply (rbn8_inv_step X pos lyc1 Sc1 W1 m md wr lyc2 Sc2 W2 m2 md2 rbn_lit6 HX HI HJ2 Hfr2
    ltac:(rewrite Hab2; apply Permutation_refl)).
  + apply (rbn8_step_of X pos lyc1 Sc1 W1 m md _ W2 m2 TSB_CH_STK
      (fun a => rbn_A X + 88 + 16 <= a < rbn_A X + 88 + 28 \/
         rbn_F X pos + 192 + Z.of_nat (length wr) <= a <
         rbn_F X pos + 192 + Z.of_nat (length wr) + Z.of_nat (length rbn_lit6))
      _ HX HM).
    * unfold TSB_CH_STK, ESTACK. lia.
    * intros a [Ha | Ha]; [left; lia | right; exact Ha].
    * intros a Ha. cbv beta in Ha. unfold rbn_lit6 in Ha. cbn [length] in Ha. lia.
    * intros a Ha H1 H2. apply T1; [lia | exact H1 | exact H2].
    * exact T2.
    * exact T3.
    * exact T4.
    * exact T5.
  + replace (rbn_A X + 104) with (rbn_A X + 88 + 16) by lia. exact O16.
  + replace (rbn_A X + 112) with (rbn_A X + 88 + 24) by lia. exact O24.
  + exact HG.
  + unfold rbn_lit6. cbn [length]. lia.
- apply (rbn8_regs_keep X pos regs regs2 _ HR HK). repeat split; reflexivity.
Qed.
Lemma rbn8_init : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_st8 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  rbn8_inv X pos lyc1 Sc1 W1 memc1 mdc1 (rbm_NB X) /\ rbn8_regs X pos regs1 /\ rbm_args X.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX (HM & HRB & R18 & R25 & R26 & R27 & HC & G64 & G128 & G192 & HA).
pose proof (rbn8_NB_len X) as NBl.
assert (E47 : firstn 47 (rbm_NB X) = rbm_NB X) by (apply firstn_all2; lia).
assert (O47 : rbm_ovf 47 (rbm_NB X) = 0)
  by (unfold rbm_ovf; replace (47 <? Z.of_nat (length (rbm_NB X))) with false by (symmetry; apply Z.ltb_ge; lia);
      reflexivity).
rewrite E47, O47 in HC. rewrite E47 in G192.
assert (HCs : rbn_cells (mrestrict (w_H W1) memc1)
  (rbn8_cells X pos ++ rbn_rd X pos (Z.of_nat (length (rbm_NB X))) 0))
  by (unfold rbn8_cells; rewrite <- !app_assoc; exact HC).
apply rbn8_cells_app in HCs as [HC1 HC2].
split; [|split; [exact (conj HRB (conj R18 (conj R25 (conj R26 R27)))) | exact HA]].
unfold rbn8_inv. refine (conj HM (conj HC1 (conj HC2 (conj G64 (conj G128 (conj G192 _)))))). lia.
Qed.
Lemma rbn8_close : forall X pos regs lyc1 Sc1 W1 m md,
  rbn8_inv X pos lyc1 Sc1 W1 m md (rbm_D9 X) -> rbn8_regs X pos regs -> rbm_args X ->
  rbn_st9 B X pos regs lyc1 Sc1 W1 m md.
Proof.
intros X pos regs lyc1 Sc1 W1 m md (HM & HC1 & HC2 & G64 & G128 & G192 & Hl) (HRB & R18 & R25 & R26 & R27) HA.
assert (E47 : firstn 47 (rbm_D9 X) = rbm_D9 X) by (apply firstn_all2; lia).
assert (O47 : rbm_ovf 47 (rbm_D9 X) = 0)
  by (unfold rbm_ovf; replace (47 <? Z.of_nat (length (rbm_D9 X))) with false by (symmetry; apply Z.ltb_ge; lia);
      reflexivity).
unfold rbn_st9. rewrite E47, O47.
split; [exact HM|]. split; [exact HRB|]. split; [exact R18|]. split; [exact R25|]. split; [exact R26|].
split; [exact R27|].
split; [|split; [exact G64 | split; [exact G128 | split; [exact G192 | exact HA]]]].
assert (H : rbn_cells (mrestrict (w_H W1) m) (rbn8_cells X pos ++ rbn_rd X pos (Z.of_nat (length (rbm_D9 X))) 0))
  by (apply rbn8_cells_app; split; assumption).
unfold rbn8_cells in H. rewrite <- !app_assoc in H. exact H.
Qed.
Theorem rbn_seg8 : rbn_seg8_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H8.
destruct (rbn8_init X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H8) as (HI1 & HR1 & HA).
destruct (rbn8_args_ok X HA) as (Hoki & Hoko).
pose proof (rbn8_NB_len X) as NBl.
pose proof (rbn8_dec_len _ Hoki) as DLi. pose proof (rbn8_dec_len _ Hoko) as DLo.
pose proof (rbn8_ok_rng _ Hoki) as Ri. pose proof (rbn8_ok_rng _ Hoko) as Ro.
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
eapply SRr_bind.
{ apply (rbn8_p1 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) regs1 (proj1 (proj1 HI1))). }
intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & HJ2 & HK2 & G20 & G21 & G24 & KEQ2).
pose proof (rbn8_inv_eq X pos lyc1 Sc1 W1 memc1 mdc1 _ m2 md2 HX HI1 HJ2 KEQ2) as HI2.
pose proof (rbn8_regs_keep X pos regs1 regs2 _ HR1 HK2 ltac:(repeat split; reflexivity)) as HR2.
apply (rbn8_L5 X pos lyc1 Sc1 W1 m2 md2 (rbm_NB X) regs2 _ HX HI2 HR2 G20 G21 G24 ltac:(lia)).
intros lyc3 Sc3 W3 regs3 m3 md3 HI3 HR3.
destruct (rbn8_io X pos lyc3 Sc3 W3 m3 md3 _ HI3) as (Mi3 & _).
pose proof HR3 as ((B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23) & _).
eapply SRr_bind.
{ apply (rbn8_p2 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc3 Sc3 W3 m3 md3 (ri_k X) regs3 (rbn_A X) (ri_i X) (proj1 (proj1 HI3)) B9
    ltac:(lia) ltac:(lia) ltac:(lia) Mi3). }
intros W4 c4 _ (-> & regs4 & m4 & md4 & -> & HJ4 & HK4 & G1 & G10 & G11 & G12 & KEQ4).
pose proof (rbn8_inv_eq X pos lyc3 Sc3 W3 m3 md3 _ m4 md4 HX HI3 HJ4 KEQ4) as HI4.
pose proof (rbn8_regs_keep X pos regs3 regs4 _ HR3 HK4 ltac:(repeat split; reflexivity)) as HR4.
clear B2 B3 B4 B8 B9 B19 B22 B23.
pose proof HR4 as ((B2 & B3 & B4 & _) & _).
apply (rbn8_dec X pos lyc3 Sc3 W3 m4 md4 (rbm_NB X ++ rbn_lit5) (ri_i X) regs4 _ HX HI4 B2 B3 B4 G10 G11 G12).
{ rewrite G1. unfold w64. replace (BASE + AF_both3_reac_box_name + 0x5c4) with (BASE + 15492)
    by (unfold AF_both3_reac_box_name; lia). apply ret_ok_codeptr_v; lia. }
{ unfold raZ. rewrite G1. unfold w64. rewrite unsigned_lit_small by (unfold AF_both3_reac_box_name; lia).
  unfold AF_both3_reac_box_name. lia. }
{ exact Hoki. }
{ rewrite length_app. unfold rbn_lit5. cbn [length]. lia. }
intros lyc5 Sc5 W5 regs5 m5 md5 HI5 HP5.
pose proof (rbn8_regs_pres X pos regs4 regs5 HR4 HP5) as HR5.
rewrite G1.
change (mkCfg (mkst (fx := ri_fq X) regs5 (w64 (BASE + AF_both3_reac_box_name + 0x5c4)) m5 (seg_rom SEGS)) md5)
  with (rbn_cfg X 0x5c4 regs5 m5 md5).
eapply SRr_bind.
{ apply (rbn8_p3 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc5 Sc5 W5 m5 md5 (ri_k X) regs5 (proj1 (proj1 HI5))). }
intros W6 c6 _ (-> & regs6 & m6 & md6 & -> & HJ6 & HK6 & G20' & G21' & G24' & KEQ6).
pose proof (rbn8_inv_eq X pos lyc5 Sc5 W5 m5 md5 _ m6 md6 HX HI5 HJ6 KEQ6) as HI6.
pose proof (rbn8_regs_keep X pos regs5 regs6 _ HR5 HK6 ltac:(repeat split; reflexivity)) as HR6.
apply (rbn8_L6 X pos lyc5 Sc5 W5 m6 md6 _ regs6 _ HX HI6 HR6 G20' G21' G24').
{ rewrite !length_app. unfold rbn_lit5. cbn [length]. lia. }
intros lyc7 Sc7 W7 regs7 m7 md7 HI7 HR7.
destruct (rbn8_io X pos lyc7 Sc7 W7 m7 md7 _ HI7) as (_ & Mo7).
clear B2 B3 B4.
pose proof HR7 as ((B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23) & _).
eapply SRr_bind.
{ apply (rbn8_p4 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc7 Sc7 W7 m7 md7 (ri_k X) regs7 (rbn_A X) (ri_o X) (proj1 (proj1 HI7)) B9
    ltac:(lia) ltac:(lia) ltac:(lia) Mo7). }
intros W8 c8 _ (-> & regs8 & m8 & md8 & -> & HJ8 & HK8 & G1' & G10' & G11' & G12' & KEQ8).
pose proof (rbn8_inv_eq X pos lyc7 Sc7 W7 m7 md7 _ m8 md8 HX HI7 HJ8 KEQ8) as HI8.
pose proof (rbn8_regs_keep X pos regs7 regs8 _ HR7 HK8 ltac:(repeat split; reflexivity)) as HR8.
clear B2 B3 B4 B8 B9 B19 B22 B23.
pose proof HR8 as ((B2 & B3 & B4 & _) & _).
apply (rbn8_dec X pos lyc7 Sc7 W7 m8 md8 _ (ri_o X) regs8 _ HX HI8 B2 B3 B4 G10' G11' G12').
{ rewrite G1'. unfold w64. replace (BASE + AF_both3_reac_box_name + RBN_P9) with (BASE + 15584)
    by (unfold AF_both3_reac_box_name, RBN_P9; lia). apply ret_ok_codeptr_v; lia. }
{ unfold raZ. rewrite G1'. unfold w64. rewrite unsigned_lit_small by (unfold AF_both3_reac_box_name, RBN_P9; lia).
  unfold AF_both3_reac_box_name, RBN_P9. lia. }
{ exact Hoko. }
{ rewrite !length_app. unfold rbn_lit5, rbn_lit6. cbn [length]. lia. }
intros lyc9 Sc9 W9 regs9 m9 md9 HI9 HP9.
pose proof (rbn8_regs_pres X pos regs8 regs9 HR8 HP9) as HR9.
apply SRr_ret. exists pos, regs9, lyc9, Sc9, m9, md9. split.
{ unfold rbn_cfg, cfg_at. rewrite G1'. reflexivity. }
apply (rbn8_close X pos regs9 lyc9 Sc9 W9 m9 md9); [|exact HR9 | exact HA].
replace (rbm_D9 X) with ((((rbm_NB X ++ rbn_lit5) ++ bn_dec (ri_i X) 1) ++ rbn_lit6) ++ bn_dec (ri_o X) 1)
  by (unfold rbm_D9, rbn_lit5, rbn_lit6; rewrite <- !app_assoc; reflexivity).
exact HI9.
Qed.
End h.
End f.
End d.
