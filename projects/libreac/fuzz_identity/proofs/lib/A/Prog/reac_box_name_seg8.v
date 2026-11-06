(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACan.v:341-345
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YP01.v:21-22 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentAddr IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85 IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC45.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
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
Lemma rbn8_dec_bytes : forall v, bn_ok v = true -> Forall (fun c => 0 <= c < 256) (bn_dec v 1).
Proof.
intros v H. apply bn_ok_in in H.
assert (A : forallb (fun x => forallb (fun c => (0 <=? c) && (c <? 256)) (bn_dec x 1)) bn_oks = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A v H). rewrite forallb_forall in A.
apply Forall_forall. intros c Hc. specialize (A c Hc). apply andb_prop in A as (A1 & A2).
apply Z.leb_le in A1. apply Z.ltb_lt in A2. lia.
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
Lemma rbn8_sep : forall (P : Z -> Prop) lo1 n1 lo2 n2, 0 < n1 -> 0 < n2 ->
  (forall x, lo1 <= x < lo1 + n1 -> P x) -> (forall x, lo2 <= x < lo2 + n2 -> ~ P x) ->
  lo1 + n1 <= lo2 \/ lo2 + n2 <= lo1.
Proof.
intros P lo1 n1 lo2 n2 H1 H2 HA HB.
destruct (Z_le_gt_dec (lo1 + n1) lo2) as [H | H]; [left; lia|].
destruct (Z_le_gt_dec (lo2 + n2) lo1) as [H' | H']; [right; lia|].
exfalso. apply (HB (Z.max lo1 lo2) ltac:(lia)). apply HA. lia.
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
Lemma rbn8_out_get : forall (regs2 : bvmap 5 word) (r : bv 5) v,
  getr regs2 (Z_to_bv 5 (bv_unsigned r)) = v -> getr regs2 r = v.
Proof. intros regs2 r v H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma rbn8_pres_get : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Ltac rbn8_rreg HS r v pf H :=
lazymatch type of HS with
| st_ok_pi ?segs _ ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf)
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)
end.
Ltac rbn8_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition rbn8_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 80 96 80 80
      [YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 88 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 9%nat) 128 148 136 148
      [YP09.mkChunk 128 (CVal 8 (SOff 34 0)); YP09.mkChunk 136 (CVal 8 (SOff 35 0));
       YP09.mkChunk 144 (CVal 4 (SOff 36 0))] ].
Definition rbn8_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 31) 0); (33%nat, mkAF 0 (2 ^ 31) 0);
            (34%nat, mkAF 0 (2 ^ 31) 0); (35%nat, mkAF 0 (2 ^ 31) 0); (36%nat, mkAF 0 1 0) ] [] [].
Definition ss_rbn8 (pc : Z) : sstate := mkSS pc sr_atoms rbn8_regions None rbn8_facts.
Definition ss_rbn8T (pc : Z) : sstate :=
  mkSS pc sr_atoms (YP09.mkRegion (Some 9%nat) 40 48 40 48 [] :: rbn8_regions) None rbn8_facts.
Definition rbn8_extra (i o cap n ov : Z) : list word := map (Z_to_bv 64) [i; o; cap; n; ov].
Definition ERB8 (regs : bvmap 5 word) (i o cap n ov : Z) : env := Eimg (Ereg regs (rbn8_extra i o cap n ov)).
Lemma regs_ok_ERB8 : forall regs i o cap n ov, regs_ok (ERB8 regs i o cap n ov) sr_atoms regs.
Proof.
intros. unfold ERB8. apply (regs_ok_agree 32 (Ereg regs (rbn8_extra i o cap n ov))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn8_ew : forall (regs : bvmap 5 word) i o cap n ov,
  (forall m, (m < A_TEXT)%nat -> ew (ERB8 regs i o cap n ov) m = ew (Ereg regs (rbn8_extra i o cap n ov)) m).
Proof. intros regs i o cap n ov m Hm. unfold ERB8. apply Eimg_low. exact Hm. Qed.
Lemma rbn8_denot_atom0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E n v 0 H Hv ltac:(lia)). lia.
Qed.
Lemma rbn8_denot_lit0 : forall E v, 0 <= v < 2 ^ 64 -> sv_denot E (SLit v) = Z_to_bv 64 v.
Proof.
intros E v Hv. rewrite denot_lit_U. f_equal. rewrite U_SLit. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rbn8_denot_atomc : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv Hc. rewrite denot_lit_U. f_equal. apply (U_atom_off E n v c H Hv Hc).
Qed.
Lemma rbn8_frame_eq : forall E rs (W : world SEGS) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros E rs W m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn8_cell8 : forall E (m : word -> option byte) A cs lo hi wlo whi od e v,
  region_ok SEGS E m (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 9) = A ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (A + od) 8 v.
Proof.
intros E m A cs lo hi wlo whi od e v HR HA Hin He Hv.
change 8%nat with (N.to_nat 8).
apply (field_of_region E m 9%nat A cs lo hi wlo whi od 8 e v HR HA Hin He); zside.
Qed.
Lemma rbn8_cell4 : forall E (m : word -> option byte) A cs lo hi wlo whi od e v,
  region_ok SEGS E m (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 9) = A ->
  In (YP09.mkChunk od (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  val_mem SEGS m (A + od) 4 v.
Proof.
intros E m A cs lo hi wlo whi od e v HR HA Hin He Hv.
change 4%nat with (N.to_nat 4).
apply (field_of_region E m 9%nat A cs lo hi wlo whi od 4 e v HR HA Hin He); zside.
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
Lemma rbn8_locs6_rng : forall X pos a n v, In (a, n, v) (rbn_locs6 X pos) ->
  rbn_A X + 8 <= a /\ a + Z.of_nat n <= rbn_A X + 180 /\ (a + Z.of_nat n <= rbn_A X + 40 \/ rbn_A X + 48 <= a) /\
  (a + Z.of_nat n <= rbn_A X + 120 \/ rbn_A X + 152 <= a).
Proof.
intros X pos a n v H. unfold rbn_locs6, rbn_locs4 in H. apply in_app_or in H. destruct H as [H | H]; cbn [In] in H;
repeat (destruct H as [H | H]; [injection H as <- <- <-; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]); destruct H.
Qed.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn8_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A pc i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  st_ok_pi SEGS VAL (ERB8 regs i o cap n ov) (ss_rbn8 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A pc i o cap n ov
HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (HA : 2 ^ 46 <= A <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := ERB8 regs i o cap n ov).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (rbn8_extra i o cap n ov)) m)
by (intros m Hm; subst E; apply rbn8_ew; exact Hm).
assert (E9 : ew E 9 = Z_to_bv 64 A)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ov) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold ss_rbn8, rbn8_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB8.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  rewrite (VB 9%nat A E9) by lia.
  + split; [lia|]. split; [lia|]. split; [intros o0 Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ A 80 8 _ i);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Mi.
    * apply (chunk_ok_val SEGS E _ A 88 8 _ o);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Mo.
  + split; [lia|]. split; [lia|]. split.
    * intros o0 Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ A 128 8 _ cap);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact Mc.
      -- apply (chunk_ok_val SEGS E _ A 136 8 _ n);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact Mn.
      -- apply (chunk_ok_val SEGS E _ A 144 4 _ ov);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact Mv.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 9%nat A E9) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold rbn8_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E9, unsigned_lit_small by lia;
          change (2 ^ 5) with 32; split; [lia|]; split; [exact HA32 | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E36, unsigned_lit_small by lia;
          rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
  exact I.
Qed.
Lemma rbn8_entryT : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A pc i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  st_ok_pi SEGS VAL (ERB8 regs i o cap n ov) (ss_rbn8T pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A pc i o cap n ov
HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof (rbn8_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A pc i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
set (E := ERB8 regs i o cap n ov) in *.
assert (E9 : ew E 9 = Z_to_bv 64 A)
by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (VB9 : base_val E (Some 9%nat) = A) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
unfold ss_rbn8T.
change (mkSS pc sr_atoms (YP09.mkRegion (Some 9%nat) 40 48 40 48 [] :: rbn8_regions) None rbn8_facts)
  with (mkSS (ss_pc (ss_rbn8 pc)) (ss_regs (ss_rbn8 pc))
          (YP09.mkRegion (Some 9%nat) 40 48 40 48 [] :: ss_mem (ss_rbn8 pc)) (ss_resv (ss_rbn8 pc))
          (ss_facts (ss_rbn8 pc))).
apply st_ok_pi_add_region.
- exact HS.
- vm_compute. reflexivity.
- unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VB9. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o0 Ho. cbn [ms_mem restrict mkst]. apply (apresent_writable SEGS). apply Hpres. lia.
- unfold all_disjoint. cbn [ss_mem ss_rbn8 rbn8_regions]. repeat apply Forall_cons; try apply Forall_nil;
  unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite VB9; lia.
Qed.
Lemma rbn8_p1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN_P8) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at SEGS (BASE + AF_reac_box_name + RBN_L5) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       aregs_preserved regs regs1 /\
       getr regs1 11 = w64 1 /\ getr regs1 12 = w64 ov /\ getr regs1 13 = w64 47 /\
       getr regs1 14 = w64 (VAL (A_OBJ 22)) /\ getr regs1 15 = w64 3 /\ getr regs1 16 = w64 n /\
       getr regs1 17 = w64 32 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 n /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ov).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov
HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof (pa_val_range (A_OBJ 22)) as VR28.
pose proof (rbn8_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 10600 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_to_pi_AJ _ _ _ _ _ _ B LAWS) as RUNTOP.
set (E := ERB8 regs i o cap n ov) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB8; apply Eimg_env).
assert (E9 : ew E 9 = Z_to_bv 64 A)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E34 : ew E 34 = Z_to_bv 64 cap)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ov)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E22o : ew E (A_OBJ 22) = Z_to_bv 64 (VAL (A_OBJ 22)))
  by (subst E; unfold ERB8; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = A) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_P8) with (BASE + 10600) by (unfold AF_reac_box_name, RBN_P8; lia).
paj_run_to_sh RUNTOP HS HJ 10632.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP _ _ lyc own 9%nat (A - sp0));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr.
pose proof (rbn8_frame_eq E _ W memc _ (fun a => A + 136 <= a < A + 148) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_rbn8, rbn8_regions in Hr; cbn [ss_mem In] in Hr;
        repeat (destruct Hr as [<- | Hr]); try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U9 in Hw; lia)) as KEQ.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (apply rbn8_denot_lit0; lia).
assert (D47 : sv_denot E (SLit 47) = Z_to_bv 64 47) by (apply rbn8_denot_lit0; lia).
assert (D3 : sv_denot E (SLit 3) = Z_to_bv 64 3) by (apply rbn8_denot_lit0; lia).
assert (D32 : sv_denot E (SLit 32) = Z_to_bv 64 32) by (apply rbn8_denot_lit0; lia).
assert (Dov : sv_denot E (SOff 36 0) = Z_to_bv 64 ov) by (apply (rbn8_denot_atom0 E 36 ov E36); lia).
assert (Dn : sv_denot E (SOff 35 0) = Z_to_bv 64 n) by (apply (rbn8_denot_atom0 E 35 n E35); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (rbn8_denot_atom0 E 34 cap E34); lia).
assert (Dq : sv_denot E (SOff (A_OBJ 22) 0) = Z_to_bv 64 (VAL (A_OBJ 22)))
  by (apply (rbn8_denot_atom0 E (A_OBJ 22) (VAL (A_OBJ 22)) E22o); lia).
rbn8_rreg HS (11%bv : bv 5) (Z_to_bv 64 1) D1 G11.
rbn8_rreg HS (12%bv : bv 5) (Z_to_bv 64 ov) Dov G12.
rbn8_rreg HS (13%bv : bv 5) (Z_to_bv 64 47) D47 G13.
rbn8_rreg HS (14%bv : bv 5) (Z_to_bv 64 (VAL (A_OBJ 22))) Dq G14.
rbn8_rreg HS (15%bv : bv 5) (Z_to_bv 64 3) D3 G15.
rbn8_rreg HS (16%bv : bv 5) (Z_to_bv 64 n) Dn G16.
rbn8_rreg HS (17%bv : bv 5) (Z_to_bv 64 32) D32 G17.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs (rbn8_extra i o cap n ov) HS);
  [split; [intros mm Hm; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity] | vm_compute; reflexivity]. }
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_L5) with (BASE + 10632) by (unfold AF_reac_box_name, RBN_L5; lia).
  reflexivity. }
split; [exact HJ|]. split; [exact HPRES|].
split; [exact G11|]. split; [exact G12|]. split; [exact G13|]. split; [exact G14|].
split; [exact G15|]. split; [exact G16|]. split; [exact G17|].
split; [exact KEQ|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 128 (SOff 34 0) cap HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dcap ltac:(lia))|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 136 (SOff 35 0) n HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dn ltac:(lia))|].
exact (rbn8_cell4 E _ A _ 128 148 136 148 144 (SOff 36 0) ov HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dov ltac:(lia)).
Qed.
Lemma rbn8_p3 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  SRr SEGS W (cfg_at SEGS (BASE + 10772) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at SEGS (BASE + AF_reac_box_name + RBN_L6) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       aregs_preserved regs regs1 /\
       getr regs1 11 = w64 cap /\ getr regs1 12 = w64 ov /\ getr regs1 13 = w64 (VAL (A_OBJ 23)) /\
       getr regs1 14 = w64 7 /\ getr regs1 15 = w64 n /\ getr regs1 16 = w64 32 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 n /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ov).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov
HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof (pa_val_range (A_OBJ 23)) as VR29.
pose proof (rbn8_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 10772 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_to_pi_AJ _ _ _ _ _ _ B LAWS) as RUNTOP.
set (E := ERB8 regs i o cap n ov) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB8; apply Eimg_env).
assert (E9 : ew E 9 = Z_to_bv 64 A)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E34 : ew E 34 = Z_to_bv 64 cap)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ov)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E23o : ew E (A_OBJ 23) = Z_to_bv 64 (VAL (A_OBJ 23)))
  by (subst E; unfold ERB8; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = A) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at, w64.
paj_run_to_sh RUNTOP HS HJ 10800.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP _ _ lyc own 9%nat (A - sp0));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr.
pose proof (rbn8_frame_eq E _ W memc _ (fun a => A + 136 <= a < A + 148) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_rbn8, rbn8_regions in Hr; cbn [ss_mem In] in Hr;
        repeat (destruct Hr as [<- | Hr]); try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U9 in Hw; lia)) as KEQ.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
assert (D7 : sv_denot E (SLit 7) = Z_to_bv 64 7) by (apply rbn8_denot_lit0; lia).
assert (D32 : sv_denot E (SLit 32) = Z_to_bv 64 32) by (apply rbn8_denot_lit0; lia).
assert (Dov : sv_denot E (SOff 36 0) = Z_to_bv 64 ov) by (apply (rbn8_denot_atom0 E 36 ov E36); lia).
assert (Dn : sv_denot E (SOff 35 0) = Z_to_bv 64 n) by (apply (rbn8_denot_atom0 E 35 n E35); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (rbn8_denot_atom0 E 34 cap E34); lia).
assert (Dq : sv_denot E (SOff (A_OBJ 23) 0) = Z_to_bv 64 (VAL (A_OBJ 23)))
  by (apply (rbn8_denot_atom0 E (A_OBJ 23) (VAL (A_OBJ 23)) E23o); lia).
rbn8_rreg HS (11%bv : bv 5) (Z_to_bv 64 cap) Dcap G11.
rbn8_rreg HS (12%bv : bv 5) (Z_to_bv 64 ov) Dov G12.
rbn8_rreg HS (13%bv : bv 5) (Z_to_bv 64 (VAL (A_OBJ 23))) Dq G13.
rbn8_rreg HS (14%bv : bv 5) (Z_to_bv 64 7) D7 G14.
rbn8_rreg HS (15%bv : bv 5) (Z_to_bv 64 n) Dn G15.
rbn8_rreg HS (16%bv : bv 5) (Z_to_bv 64 32) D32 G16.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs (rbn8_extra i o cap n ov) HS);
  [split; [intros mm Hm; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity] | vm_compute; reflexivity]. }
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_L6) with (BASE + 10800) by (unfold AF_reac_box_name, RBN_L6; lia).
  reflexivity. }
split; [exact HJ|]. split; [exact HPRES|].
split; [exact G11|]. split; [exact G12|]. split; [exact G13|].
split; [exact G14|]. split; [exact G15|]. split; [exact G16|].
split; [exact KEQ|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 128 (SOff 34 0) cap HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dcap ltac:(lia))|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 136 (SOff 35 0) n HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dn ltac:(lia))|].
exact (rbn8_cell4 E _ A _ 128 148 136 148 144 (SOff 36 0) ov HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dov ltac:(lia)).
Qed.
Lemma rbn8_keepr : forall (H : word -> bool) ss ms (regs0 : bvmap 5 word) i o cap n ov cl,
  st_ok SEGS (ERB8 regs0 i o cap n ov) ss (restrict H ms) ->
  forallb (fun r : bv 5 => existsb (Z.eqb (bv_unsigned r)) cl
             || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) all_regs = true ->
  rbn_keep_regs regs0 (ms_regs ms) cl.
Proof.
intros H ss ms regs0 i o cap n ov cl HS Hf r Hr Hn.
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
rewrite (st_ok_restrict_reg SEGS H (ERB8 regs0 i o cap n ov) ss ms (Z_to_bv 5 r) HS), Hq.
rewrite (rbn8_denot_atom0 (ERB8 regs0 i o cap n ov) (Z.to_nat r) (bv_unsigned (getr regs0 (Z_to_bv 5 r)))).
- apply Z_to_bv_bv_unsigned.
- rewrite rbn8_ew by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs0 (rbn8_extra i o cap n ov) (Z.to_nat r) (Z_to_bv 5 r) ltac:(rewrite Hu; lia)).
  symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
Lemma rbn8_p2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A i o cap n ov tok nn ovv : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  getr regs 21 = w64 tok -> 0 <= tok < 2 ^ 64 ->
  getr regs 16 = w64 nn -> 0 <= nn < 2 ^ 64 ->
  getr regs 12 = w64 ovv -> 0 <= ovv < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  SRr SEGS W (cfg_at SEGS (BASE + 10740) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at SEGS (SIGMA IS_sb_dec) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 1; 10; 11; 12; 23] /\
       getr regs1 1 = w64 (BASE + 10772) /\ getr regs1 10 = w64 (A + 120) /\
       getr regs1 11 = w64 i /\ getr regs1 12 = w64 1 /\ getr regs1 23 = w64 1 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 40 <= a < A + 48) -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 40) 8 tok /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 nn /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ovv).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov tok nn ovv
HJ H9 HAc HA32 HAlo HAhi Hsp0 H21 Rtok H16 Rnn H12 Rovv Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (rbn8_entryT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 10740 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_pi_AJ _ _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call _ _ _ _ _ _ B LAWS) as RUNC.
set (E := ERB8 regs i o cap n ov) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB8; apply Eimg_env).
assert (E9 : ew E 9 = Z_to_bv 64 A)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E12 : ew E 12 = Z_to_bv 64 ovv)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E16 : ew E 16 = Z_to_bv 64 nn)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
assert (E21 : ew E 21 = Z_to_bv 64 tok)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E32 : ew E 32 = Z_to_bv 64 i)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 cap)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E240 : ew E A_TEXT = Z_to_bv 64 BASE)
  by (subst E; unfold ERB8; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = A) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at, w64.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP _ _ lyc own 9%nat (A - sp0));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP _ _ lyc own 9%nat (A - sp0));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
pose proof (rbn8_frame_eq E _ W memc _
  (fun a => (A + 40 <= a < A + 48) \/ (A + 136 <= a < A + 148)) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_rbn8T, ss_rbn8, rbn8_regions in Hr; cbn [ss_mem In] in Hr;
        repeat (destruct Hr as [<- | Hr]); try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U9 in Hw; lia)) as KEQ0.
assert (KEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (A + 40 <= a < A + 48) -> ~ (A + 136 <= a < A + 148) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (intros a Ha H1 H2; apply KEQ0; [exact Ha | intros [HC | HC]; [exact (H1 HC) | exact (H2 HC)]]).
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (st_ok_region_nth E _ _ 2 _ HS eq_refl) as HR2. cbn [ms_mem restrict] in HR2.
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (apply rbn8_denot_lit0; lia).
assert (Di : sv_denot E (SOff 32 0) = Z_to_bv 64 i) by (apply (rbn8_denot_atom0 E 32 i E32); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (rbn8_denot_atom0 E 34 cap E34); lia).
assert (Dnn : sv_denot E (SOff 16 0) = Z_to_bv 64 nn) by (apply (rbn8_denot_atom0 E 16 nn E16); lia).
assert (Dovv : sv_denot E (SOff 12 0) = Z_to_bv 64 ovv) by (apply (rbn8_denot_atom0 E 12 ovv E12); lia).
assert (Dtok : sv_denot E (SOff 21 0) = Z_to_bv 64 tok) by (apply (rbn8_denot_atom0 E 21 tok E21); lia).
assert (Dra : sv_denot E (SOff A_TEXT 10772) = Z_to_bv 64 (BASE + 10772))
  by (apply (rbn8_denot_atomc E A_TEXT BASE 10772 E240); lia).
assert (Drec : sv_denot E (SOff 9 120) = Z_to_bv 64 (A + 120))
  by (apply (rbn8_denot_atomc E 9 A 120 E9); lia).
rbn8_rreg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 10772)) Dra G1.
rbn8_rreg HS (10%bv : bv 5) (Z_to_bv 64 (A + 120)) Drec G10.
rbn8_rreg HS (11%bv : bv 5) (Z_to_bv 64 i) Di G11.
rbn8_rreg HS (12%bv : bv 5) (Z_to_bv 64 1) D1 G12.
rbn8_rreg HS (23%bv : bv 5) (Z_to_bv 64 1) D1 G23.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 1; 10; 11; 12; 23])
  by (apply (rbn8_keepr (w_H W) _ _ regs i o cap n ov _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64. reflexivity. }
split; [exact HJ|]. split; [exact HKP|].
split; [exact G1|]. split; [exact G10|]. split; [exact G11|]. split; [exact G12|]. split; [exact G23|].
split; [exact KEQ|].
split; [exact (rbn8_cell8 E _ A _ 40 48 40 48 40 (SOff 21 0) tok HR0 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dtok ltac:(lia))|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 128 (SOff 34 0) cap HR2 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dcap ltac:(lia))|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 136 (SOff 16 0) nn HR2 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dnn ltac:(lia))|].
exact (rbn8_cell4 E _ A _ 128 148 136 148 144 (SOff 12 0) ovv HR2 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dovv ltac:(lia)).
Qed.
Lemma rbn8_p4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A i o cap n ov nn ovv : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  getr regs 15 = w64 nn -> 0 <= nn < 2 ^ 64 ->
  getr regs 12 = w64 ovv -> 0 <= ovv < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  SRr SEGS W (cfg_at SEGS (BASE + 10912) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at SEGS (SIGMA IS_sb_dec) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 1; 10; 11; 12; 21] /\
       getr regs1 1 = w64 (BASE + 10940) /\ getr regs1 10 = w64 (A + 120) /\
       getr regs1 11 = w64 o /\ getr regs1 12 = w64 1 /\ getr regs1 21 = w64 1 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 nn /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ovv).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov nn ovv
HJ H9 HAc HA32 HAlo HAhi Hsp0 H15 Rnn H12 Rovv Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (rbn8_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 10912 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_pi_AJ _ _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call _ _ _ _ _ _ B LAWS) as RUNC.
set (E := ERB8 regs i o cap n ov) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB8; apply Eimg_env).
assert (E9 : ew E 9 = Z_to_bv 64 A)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E12 : ew E 12 = Z_to_bv 64 ovv)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E15 : ew E 15 = Z_to_bv 64 nn)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E33 : ew E 33 = Z_to_bv 64 o)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap)
  by (subst E; rewrite rbn8_ew by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E240 : ew E A_TEXT = Z_to_bv 64 BASE)
  by (subst E; unfold ERB8; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = A) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at, w64.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP _ _ lyc own 9%nat (A - sp0));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
pose proof (rbn8_frame_eq E _ W memc _ (fun a => A + 136 <= a < A + 148) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_rbn8, rbn8_regions in Hr; cbn [ss_mem In] in Hr;
        repeat (destruct Hr as [<- | Hr]); try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U9 in Hw; lia)) as KEQ.
pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as HR1. cbn [ms_mem restrict] in HR1.
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (apply rbn8_denot_lit0; lia).
assert (Do : sv_denot E (SOff 33 0) = Z_to_bv 64 o) by (apply (rbn8_denot_atom0 E 33 o E33); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (rbn8_denot_atom0 E 34 cap E34); lia).
assert (Dnn : sv_denot E (SOff 15 0) = Z_to_bv 64 nn) by (apply (rbn8_denot_atom0 E 15 nn E15); lia).
assert (Dovv : sv_denot E (SOff 12 0) = Z_to_bv 64 ovv) by (apply (rbn8_denot_atom0 E 12 ovv E12); lia).
assert (Dra : sv_denot E (SOff A_TEXT 10940) = Z_to_bv 64 (BASE + 10940))
  by (apply (rbn8_denot_atomc E A_TEXT BASE 10940 E240); lia).
assert (Drec : sv_denot E (SOff 9 120) = Z_to_bv 64 (A + 120))
  by (apply (rbn8_denot_atomc E 9 A 120 E9); lia).
rbn8_rreg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 10940)) Dra G1.
rbn8_rreg HS (10%bv : bv 5) (Z_to_bv 64 (A + 120)) Drec G10.
rbn8_rreg HS (11%bv : bv 5) (Z_to_bv 64 o) Do G11.
rbn8_rreg HS (12%bv : bv 5) (Z_to_bv 64 1) D1 G12.
rbn8_rreg HS (21%bv : bv 5) (Z_to_bv 64 1) D1 G21.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 1; 10; 11; 12; 21])
  by (apply (rbn8_keepr (w_H W) _ _ regs i o cap n ov _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64. reflexivity. }
split; [exact HJ|]. split; [exact HKP|].
split; [exact G1|]. split; [exact G10|]. split; [exact G11|]. split; [exact G12|]. split; [exact G21|].
split; [exact KEQ|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 128 (SOff 34 0) cap HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dcap ltac:(lia))|].
split; [exact (rbn8_cell8 E _ A _ 128 148 136 148 136 (SOff 15 0) nn HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dnn ltac:(lia))|].
exact (rbn8_cell4 E _ A _ 128 148 136 148 144 (SOff 12 0) ovv HR1 U9
          ltac:(cbn [YP09.r_chunks In]; tauto) Dovv ltac:(lia)).
Qed.
Lemma rbn8_A_rng : forall X, rbn_cx B G X ->
  alloc_ceiling + REAC_BOX_NAME_STK <= rbn_SP X /\ rbn_SP X - 319 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  rbn_SP X <= 2 ^ 47 /\ rbn_A X mod 32 = 0.
Proof.
intros X HX. destruct HX as ((_ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
unfold rbn_A, rbn_SP in *.
pose proof (Z.div_mod (spZ (ri_regs X) - 288) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 288) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma rbn8_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh -> forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM c p.
destruct HM as (_ & (_ & L1 & _) & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F1. reflexivity.
Qed.
Lemma rbn8_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  In (3, pos) (frames Sc1) /\ frame_addr lyc1 3 pos = rbn_F X pos /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
pose proof (rbn8_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM 3 pos) as FA.
destruct HM as (_ & HJ1 & _). pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact Hin3|]. split; [reflexivity|].
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite Hfb3. exact Ha.
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
Lemma rbn8_args : forall X, rbm_args X ->
  ri_name X <> 0 /\ ri_token X <> 0 /\ ri_display X <> 0 /\ bn_ok (ri_i X) = true /\ bn_ok (ri_o X) = true.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [HA Hi].
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA _].
apply andb_prop in HA as [HA Hd]. apply andb_prop in HA as [Hn Ht].
apply negb_true_iff, Z.eqb_neq in Hn. apply negb_true_iff, Z.eqb_neq in Ht. apply negb_true_iff, Z.eqb_neq in Hd.
auto.
Qed.
Lemma rbn8_nsink : forall X, rbn_cx B G X -> rbm_args X -> ~ YI16.sink_open_fp (rbn_FPX X).
Proof.
intros X HX HA (r & Hr & H0).
destruct (rbn8_args X HA) as (Hn & Ht & Hd & _).
destruct HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rn & _ & _ & _ & Rt & _ & _ & _ & _ & Rd & _).
unfold rbn_FPX, rbn_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia.
Qed.
Definition rbn8_step (X : rbn_in) (lyc1 : alayout) (Sc1 : astate) (W W' : world SEGS)
  (m m' : word -> option byte) (Er : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - 4208 <= a < rbn_A X + 180) -> ~ Er a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
  (forall b mm j, In (b, mm) (ablocks B lyc1 Sc1) -> 0 <= j < req_size mm -> ~ Er (b + j) ->
     aview SEGS (w_H W') m' (b + j) = aview SEGS (w_H W) m (b + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
  (forall cid p a, In (cid, p) (frames Sc1) ->
     (in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)) ->
     ~ Er a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a).
Lemma rbn8_step_stk : forall X lyc1 Sc1 (W1 : world SEGS) (m m' : word -> option byte) md1 lo hi,
  rbn_cx B G X -> AR SEGS B lyc1 Sc1 W1 m md1 ->
  rbn_A X - 4208 <= lo -> hi <= rbn_A X + 180 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
  rbn8_step X lyc1 Sc1 W1 W1 m m' (fun _ => False).
Proof.
intros X lyc1 Sc1 W1 m m' md1 lo hi HX HAR Hlo Hhi HEQ.
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
split; [|split; [|split]].
- intros a Ha Hw _. apply HEQ; [lia | lia].
- intros b mm j Hb Hj _.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR Hb) as (_ & Hb4 & Hbc & _).
  apply HEQ; lia.
- intros a Hia _ _. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  apply HEQ; lia.
- intros cid p a Hcp Ha _.
  destruct (frame_zone SEGS B LAWS _ _ _ _ _ cid p a HAR Hcp Ha) as (Hac & Hz).
  assert (Ha0 : 0 <= a) by (destruct Hz as [(Hz & Hap) | Hz]; [unfold in_app in Hap | unfold kLowMemEnd in Hz]; lia).
  apply HEQ; lia.
Qed.
Lemma rbn8_step_fr : forall X pos lyc1 Sc1 W1 m md1 sh (m' : word -> option byte) lo hi,
  rbn_mid B X pos lyc1 Sc1 W1 m md1 (fun _ => False) sh ->
  rbn_F X pos <= lo -> hi <= rbn_F X pos + 504 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
  rbn8_step X lyc1 Sc1 W1 W1 m m' (fun a => lo <= a < hi).
Proof.
intros X pos lyc1 Sc1 W1 m md1 sh m' lo hi HM Hlo Hhi HEQ.
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md1 _ sh HM) as (Hin3 & FA3 & HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof HM as (_ & HJ1 & _). pose proof (proj1 HJ1) as HAR.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
split; [|split; [|split]].
- intros a Ha _ He. apply HEQ; [lia | exact He].
- intros b mm j Hb Hj He.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR Hb) as (_ & Hb4 & Hbc & _).
  apply HEQ; [lia | exact He].
- intros a Hia _ _. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  apply HEQ; [lia|]. intros Hc. exact (proj2 (HFpr a ltac:(lia)) Hia).
- intros cid p a Hcp Ha He.
  destruct (frame_zone SEGS B LAWS _ _ _ _ _ cid p a HAR Hcp Ha) as (Hac & Hz).
  assert (Ha0 : 0 <= a) by (destruct Hz as [(Hz & Hap) | Hz]; [unfold in_app in Hap | unfold kLowMemEnd in Hz]; lia).
  apply HEQ; [lia | exact He].
Qed.
Lemma rbn8_mid_step : forall X pos lyc1 Sc1 lyc2 Sc2 (W1 : world SEGS) m mdc1 m' md' sh Er,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc2 Sc2 W1 m' md' 0 ->
  Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  rbn8_step X lyc1 Sc1 W1 W1 m m' Er ->
  (forall a, Er a -> rbn_F X pos <= a < rbn_F X pos + 504) ->
  Z.of_nat (length sh) <= 64 ->
  rbn_mid B X pos lyc2 Sc2 W1 m' md' (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 lyc2 Sc2 W1 m mdc1 m' md' sh Er HX HM HJ2 Hperm2 HST HEr Hsh.
destruct HST as (C1 & C2 & C3 & C4).
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m mdc1 _ sh HM) as (Hin3 & FA3 & HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HnErH : forall a, alloc_ceiling <= a -> ~ Er a) by (intros a Ha He; pose proof (HEr a He); lia).
pose proof HM as (HW & HJ1 & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
unfold rbn_mid. split; [exact HW|]. split; [exact HJ2|].
split; [exact (Permutation_trans Hperm2 Hperm)|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  rewrite (C3 a Hia Ho He). exact (Hro a Hro0 Ho He). }
split.
{ unfold rbn_kept. intros a HfpA HblkA He.
  pose proof HblkA as (q & N & HqN & Hq).
  assert (Hb1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) HqN).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hb1) as (_ & Hb4 & Hbc & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 pos HAR1 Hb1 Hin3) as Hd.
  rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos N ltac:(lia)) as (RS1 & RS2).
  replace a with (q + (a - q)) by lia.
  rewrite (C2 q N (a - q) Hb1 ltac:(lia) ltac:(replace (q + (a - q)) with a by lia; intros He2; pose proof (HEr _ He2); lia)).
  replace (q + (a - q)) with a by lia. exact (HK a HfpA HblkA He). }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m'); [|exact (Hfr j r Hj)].
  intros kk Hk. apply C1; [unfold rbn_SP in *; lia | unfold rbn_SP in *; lia |].
  apply HnErH. unfold rbn_SP in *. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) m m'); [|exact Hfl].
  intros kk Hk. apply (C4 3 pos); [exact Hin3 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3, Hfb3; lia|].
  intros He2. pose proof (HEr _ He2). lia. }
unfold rbn_shadow_at. intros j Hj.
pose proof (rbn8_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
assert (HnS : ~ Er (shadow_addr (rbn_F X pos) + j)).
{ intros He2. pose proof (HEr _ He2) as HE2.
  destruct (Happ (shadow_addr (rbn_F X pos) + j) ltac:(lia)) as [Hq | Hq];
  unfold kLowShadowBeg in Hb, Hq; unfold kHighMemBeg in Hb, Hq; lia. }
rewrite (C4 3 pos (shadow_addr (rbn_F X pos) + j) Hin3
  ltac:(right; unfold in_zr; cbn [fst snd]; rewrite FA3, Hfb3; change (512 / 8) with 64; lia) HnS).
exact (Hsh0 j Hj).
Qed.
Lemma rbn8_lbuf_dp : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true true) ->
  rbn_lbuf B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) [(3, pos)] lyc1 Sc1 W1 memc1
    (rbn_F X pos + 192) 48.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HM.
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (Hin3 & FA3 & HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
assert (HF8 : rbn_F X pos mod 8 = 0) by (apply mod32_mod8; exact HFal).
split; [lia|]. split; [lia|]. split.
{ apply (in_app_sub _ _ _ _ HFapp); lia. }
split.
{ replace (rbn_F X pos + 192) with (rbn_F X pos + 8 * 24) by lia. replace 48 with (8 * 6) by lia.
  apply zero_shadow_range.
  - replace (rbn_F X pos + 8 * 24) with (rbn_F X pos + 24 * 8) by lia. rewrite Z.mod_add by lia. exact HF8.
  - reflexivity.
  - intros i Hi. change (8 * 6 / 8) with 6 in Hi.
    rewrite shadow_of_addr_add8. change (shadow_of_addr SHADOW_OFF (rbn_F X pos)) with (rbn_SH X pos).
    replace (rbn_SH X pos + 24 + i) with (rbn_SH X pos + (24 + i)) by lia.
    rewrite (Hsh0 (24 + i)) by (rewrite rbn8_sh_len; lia).
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as Hc by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity. }
intros a Ha. split.
- right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite FA3. change (fs_frame_bytes 3) with 512. lia.
- exact (proj1 (HFpr a ltac:(lia))).
Qed.
Lemma rbn8_lsrc : forall X pos lyc1 Sc1 W1 m mdc1 sh q l,
  rbn_cx B G X -> rbm_args X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  globs_marked SEGS B G ->
  rbn_imgstr B G (ri_W X) (ri_memc X) q l ->
  rbn_lsrc W1 m q (l ++ [0]).
Proof.
intros X pos lyc1 Sc1 W1 m mdc1 sh q l HX HA HM HGM (Hlo & Hhi & Hf & Hg & (q0 & z0 & Hq0 & Hq1 & Hq2) & Hfix & Htl).
pose proof HM as (HW & HJ1 & _). pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (rbn8_nsink X HX HA) as Hns.
assert (Hlen : Z.of_nat (length (l ++ [0])) = Z.of_nat (length l) + 1) by (rewrite length_app; cbn [length]; lia).
split.
{ apply (garr8_frame SEGS (mrestrict (w_H (ri_W X)) (ri_memc X))); [exact Hg|].
  intros a Ha. rewrite Hlen in Ha. apply (mbyte_of_aview SEGS). subst W1.
  destruct (Hfix a ltac:(lia)) as (Hia & Hno & Her).
  exact (F3 a Hia Hno Her (fp_spares_closed _ a Hns)). }
rewrite Hlen. split; [lia|]. split; [lia|]. split; [lia|].
exact (ro_usable_glob SEGS B G lyc1 Sc1 W1 m mdc1 q0 z0 q (Z.of_nat (length l) + 1) HGM Hq0 HAR1 Hq1 Hq2).
Qed.
Lemma rbn8_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; [tauto|].
rewrite IH. tauto.
Qed.
Lemma rbn8_garr8_kept : forall (W : world SEGS) (m m' : word -> option byte) p l,
  garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  garr8 SEGS (mrestrict (w_H W) m') p l.
Proof.
intros W m m' p l HG HE. apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact HG|].
intros a Ha. apply (mbyte_of_aview SEGS). exact (HE a Ha).
Qed.
Hypothesis HSB : tsb_dec_spec B.
Lemma rbn8_call : forall X pos lyc1 Sc1 W1 m md (regs : bvmap 5 word) (v nn ret : Z) (Q : world SEGS -> config -> Prop),
  rbn_cx B G X ->
  rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) (rbn_sh true true true true) ->
  getr regs 1 = w64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr regs 2 = w64 (rbn_A X) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (rbn_A X + 120) -> getr regs 11 = w64 v -> getr regs 12 = w64 1 -> 0 <= v <= 40 ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 120) 8 (rbn_F X pos + 192) ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 128) 8 48 ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 136) 8 nn ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 144) 4 0 ->
  0 <= nn -> nn + 1 + Z.of_nat (length (sb_dec_c.sb_dec_D v 1)) <= 48 ->
  (forall regs2 ly2 S2 m2 md2,
     rbn_mid B X pos ly2 S2 W1 m2 md2 (fun _ => False) (rbn_sh true true true true) ->
     aregs_preserved regs regs2 ->
     val_mem SEGS (mrestrict (w_H W1) m2) (rbn_A X + 136) 8 (nn + Z.of_nat (length (sb_dec_c.sb_dec_D v 1))) ->
     val_mem SEGS (mrestrict (w_H W1) m2) (rbn_A X + 144) 4 0 ->
     garr8 SEGS (mrestrict (w_H W1) m2) (rbn_F X pos + 192 + nn) (sb_dec_c.sb_dec_D v 1) ->
     (forall a, rbn_A X <= a < rbn_A X + 180 -> ~ (rbn_A X + 136 <= a < rbn_A X + 148) ->
        aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
     (forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
        ~ (rbn_F X pos + 192 + nn <= a < rbn_F X pos + 192 + nn + Z.of_nat (length (sb_dec_c.sb_dec_D v 1))) ->
        aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
     SRr SEGS W1 (cfg_at SEGS (BASE + ret) regs2 m2 md2) Q) ->
  SRr SEGS W1 (cfg_at SEGS (BASE + AF_sb_dec) regs m md) Q.
Proof.
intros X pos lyc1 Sc1 W1 m md regs v nn ret Q HX HM H1 Hret Hret2 H2 H3 H4 H10 H11 H12 Hv V120 V128 V136 V144
  Hnn Hroom K.
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5).
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 m md _ _ HM) as (Hin3 & FA3 & HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof (rbn8_lbuf_dp X pos lyc1 Sc1 W1 m md HM) as (_ & _ & _ & HRA & HWR).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (WSB : SB_DEC_STK = 4208) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HM as (HW & HJ1 & Hperm & _).
pose proof HJ1 as (HAR1 & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HFR & HEV & HLV).
destruct (rbn8_sbd v nn Hnn Hroom) as (Eroom & Eacc & Eov).
assert (SPA : spZ regs = rbn_A X) by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
assert (HA16 : rbn_A X mod 16 = 0).
{ pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D. rewrite AR5, Z.add_0_r in D. rewrite D.
  replace (32 * (rbn_A X / 32)) with ((2 * (rbn_A X / 32)) * 16) by lia. apply Z_mod_mult. }
assert (HA8 : (rbn_A X + 120) mod 8 = 0).
{ pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D. rewrite AR5, Z.add_0_r in D. rewrite D.
  replace (32 * (rbn_A X / 32) + 120) with ((4 * (rbn_A X / 32) + 15) * 8) by lia. apply Z_mod_mult. }
eapply SRr_bind.
{ apply (HSB REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 m md 0 regs (rbn_A X + 120) v 1 (rbn_F X pos + 192) 48 nn 0).
  - exact HJ1.
  - rewrite H1. unfold w64. apply ret_ok_codeptr_v; [lia | exact Hret2].
  - unfold raZ. rewrite H1. unfold w64. rewrite unsigned_lit_small by lia.
    pose proof (@pa_base_lo _ _ PL_ident PI) as HBLO. lia.
  - exact H3.
  - exact H4.
  - rewrite SPA. exact HA16.
  - rewrite SPA, WSB, WS. unfold rbn_SP in *. lia.
  - rewrite SPA. unfold rbn_SP in *. lia.
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - left; reflexivity.
  - exact HA8.
  - lia.
  - lia.
  - left. rewrite SPA. lia.
  - unfold tsb_dec_rec_at. rewrite Eslo, Eshi. unfold rbn_SP in *. lia.
  - exact V120.
  - replace (rbn_A X + 120 + 8) with (rbn_A X + 128) by lia. exact V128.
  - replace (rbn_A X + 120 + 16) with (rbn_A X + 136) by lia. exact V136.
  - replace (rbn_A X + 120 + 24) with (rbn_A X + 144) by lia. exact V144.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros a Ha.
    assert (Hw : awr_byte REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ablocks B (ri_lyc X) (ri_Sc X))
      (ablocks B lyc1 Sc1) lyc1 [(3, pos)] a) by (left; unfold rbn_SP in *; lia).
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ1 Hw) as [Hp Ho].
    split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|]. rewrite SPA, Hes. lia.
  - intros _. rewrite Eacc.
    split; [lia|]. split; [lia|]. split.
    { intros a Ha. right. exists 3, pos. split; [exact Hin3|]. unfold in_zr, frame_rng. cbn [fst snd].
      rewrite FA3. change (fs_frame_bytes 3) with 512. lia. }
    split; [eapply range_addressable_sub; [exact HRA | lia | lia]|].
    split.
    { intros a Ha. destruct (HWR a ltac:(lia)) as [Hw _].
      destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ1 Hw) as [Hp Ho].
      split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|]. rewrite SPA, Hes. lia. }
    split; [left; lia | left; rewrite SPA, WSB; lia].
  - rewrite Hfrs, length_app. cbn [length]. lia.
  - unfold EV_SB_DEC, EV_REAC_BOX_NAME in *. lia.
  - unfold LIVE_SB_DEC, LIVE_REAC_BOX_NAME in *.
    rewrite (blocks_bytes_bsum B lyc1 Sc1), (bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (ri_lyc X) (ri_Sc X)). lia. }
intros W2 c2 _ (-> & ly2 & S2 & regs2 & m2 & md2 & -> & HJ2 & HP2 & HF2 & HPerm2 & HK2 & Vb & Vb8 & Vb16 & Vb24 & HG2).
rewrite Eacc in HK2, Vb16, HG2. rewrite Eov in Vb24.
change (0 + EV_SB_DEC) with 0 in HJ2.
destruct HK2 as (C1 & C2 & C3 & C4 & _ & _).
rewrite SPA, WSB in C1.
unfold tsb_dec_wr in C1, C2, C4.
assert (HST : rbn8_step X lyc1 Sc1 W1 W1 m m2
  (fun a => rbn_F X pos + 192 + nn <= a < rbn_F X pos + 192 + nn + Z.of_nat (length (sb_dec_c.sb_dec_D v 1)))).
{ split; [|split; [|split]].
  - intros a Ha Hw He. apply C1; [exact Ha | lia |]. intros [Hb | Hb]; [lia | exact (He Hb)].
  - intros b mm j Hb Hj He.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb) as (_ & Hb4 & Hbc & _).
    apply (C2 b mm j); [exact Hb | exact Hj |]. intros [Hq | Hq]; [lia | exact (He Hq)].
  - exact C3.
  - intros cid p a Hcp Ha He.
    destruct (frame_zone SEGS B LAWS _ _ _ _ _ cid p a HAR1 Hcp Ha) as (Hac & _).
    apply (C4 cid p a Hcp Ha). intros [Hq | Hq]; [lia | exact (He Hq)]. }
pose proof (rbn8_mid_step X pos lyc1 Sc1 ly2 S2 W1 m md m2 md2 (rbn_sh true true true true) _ HX HM HJ2 HPerm2 HST
  ltac:(intros a Ha; cbv beta in Ha; lia) ltac:(rewrite rbn8_sh_len; lia)) as HM2.
rewrite H1.
apply (K regs2 ly2 S2 m2 md2 HM2 HP2).
- replace (rbn_A X + 136) with (rbn_A X + 120 + 16) by lia. exact Vb16.
- replace (rbn_A X + 144) with (rbn_A X + 120 + 24) by lia. exact Vb24.
- rewrite firstn_all2 in HG2 by lia. exact HG2.
- intros a Ha Hn. apply C1; [lia | lia | intros [Hq | Hq]; lia].
- intros a Ha Hn. apply (C4 3 pos a Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3;
    change (fs_frame_bytes 3) with 512; lia | intros [Hq | Hq]; lia].
Qed.
Hypothesis PSIG : ident_prog_sig_ok.
Hypothesis GM : globs_marked SEGS B G.
Lemma rbn8_sig : SIGMA IS_sb_dec = BASE + AF_sb_dec.
Proof. exact (PSIG IS_sb_dec AF_sb_dec eq_refl). Qed.
Definition rbn8_keepl : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 26; 27].
Lemma rbn8_kl_get : forall (regs regs1 : bvmap 5 word) (r : bv 5),
  (forall z, In z rbn8_keepl -> getr regs (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z)) ->
  existsb (Z.eqb (bv_unsigned r)) rbn8_keepl = true -> getr regs r = getr regs1 r.
Proof.
intros regs regs1 r KK Hr. apply existsb_exists in Hr as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. subst x.
pose proof (KK _ Hx) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn8_garr8_cat : forall (m : word -> option byte) p q l1 l2,
  garr8 SEGS m p l1 -> garr8 SEGS m q l2 -> q = p + Z.of_nat (length l1) -> garr8 SEGS m p (l1 ++ l2).
Proof. intros m p q l1 l2 H1 H2 ->. apply (proj2 (garr8_app SEGS m p l1 l2)). split; assumption. Qed.
Hypothesis L5F : rbn_L5_fits B.
Lemma rbn8_pA : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 (Q : world SEGS -> config -> Prop),
  rbn_cx B G X -> rbn_st8 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall (regs : bvmap 5 word) m md,
     rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) (rbn_sh true true true true) ->
     (forall r, In r rbn8_keepl -> getr regs (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
     getr regs 1 = w64 (BASE + 10772) -> getr regs 10 = w64 (rbn_A X + 120) -> getr regs 11 = w64 (ri_i X) ->
     getr regs 12 = w64 1 -> getr regs 23 = w64 1 ->
     val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 40) 8 (rbm_tok X) ->
     val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 136) 8 (Z.of_nat (length (rbm_NB X)) + 2) ->
     val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 144) 4 0 ->
     garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X))) rbn_lit5 ->
     (forall a, rbn_A X <= a < rbn_A X + 180 -> ~ (rbn_A X + 40 <= a < rbn_A X + 48) ->
        ~ (rbn_A X + 136 <= a < rbn_A X + 148) -> aview SEGS (w_H W1) m a = aview SEGS (w_H W1) memc1 a) ->
     (forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
        ~ (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) <= a < rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + 2) ->
        aview SEGS (w_H W1) m a = aview SEGS (w_H W1) memc1 a) ->
     SRr SEGS W1 (cfg_at SEGS (BASE + AF_sb_dec) regs m md) Q) ->
  SRr SEGS W1 (rbn_cfg RBN_P8 regs1 memc1 mdc1) Q.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 Q HX H8 K.
destruct H8 as (HM & HRB & R18 & R27 & R24 & R25 & R20 & R26 & R21 & HC & HNB & HTB & HDB & HA).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5).
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (Hin3 & FA3 & HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
destruct (rbn8_args X HA) as (Hnm & Htk & Hdp & Hoki & Hoko).
pose proof (rbn8_ok_rng _ Hoki) as Ri. pose proof (rbn8_ok_rng _ Hoko) as Ro.
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
pose proof HM as (HW & HJ1 & _). pose proof (proj1 HJ1) as HAR1.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct HIMG as (_ & _ & _ & _ & _ & _ & _ & H22m8 & Hstr22 & _).
apply rbn8_cells_app in HC. destruct HC as (HC6 & HR2).
cbn [rbn_rec2 rbn_cells] in HR2. destruct HR2 as (V120 & V128 & V136 & V144 & _).
rewrite Z.min_l in V136 by lia.
assert (Eov : rbm_ovf 47 (rbm_NB X) = 0) by (unfold rbm_ovf; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
rewrite Eov in V144.
pose proof HC6 as HC6'. unfold rbn_locs6, rbn_locs4 in HC6'. cbn [app rbn_cells] in HC6'.
destruct HC6' as (_ & _ & _ & _ & _ & Vi & Vo & _).
unfold rbn_cfg.
eapply SRr_bind.
{ apply (rbn8_p1 REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memc1 mdc1 0 regs1 (rbn_A X) (ri_i X) (ri_o X) 48 (Z.of_nat (length (rbm_NB X))) 0
    HJ1 B9 ltac:(lia) AR5 ltac:(lia) ltac:(lia) ltac:(lia)
    Vi ltac:(lia) Vo ltac:(lia) V128 ltac:(lia) V136 ltac:(lia) V144 ltac:(lia)). }
intros W2 c2 _ (-> & regsA & memA & mdA & -> & HJA & HPA & GA11 & GA12 & GA13 & GA14 & GA15 & GA16 & GA17 &
  KEQA & VcapA & VnA & VovA).
assert (HMA : rbn_mid B X pos lyc1 Sc1 W1 memA mdA (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 memc1 mdc1 memA mdA _ (fun _ => False) HX HM HJA (Permutation_refl _)).
  - exact (rbn8_step_stk X lyc1 Sc1 W1 memc1 memA mdc1 (rbn_A X + 136) (rbn_A X + 148) HX HAR1
      ltac:(lia) ltac:(lia) KEQA).
  - intros a [].
  - rewrite rbn8_sh_len; lia. }
pose proof (L5F REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
  [(3, pos)] lyc1 Sc1 W1 memA mdA 0 regsA (rbn_F X pos + 192) (Z.of_nat (length (rbm_NB X))) 0 ltac:(lia)) as R5.
unfold rbn_L5_run in R5.
assert (R20A : getr regsA 20 = w64 (rbn_F X pos + 192))
  by (rewrite (rbn8_pres_get regs1 regsA 20%bv HPA) by rbn8_cs; exact R20).
assert (R22A : getr regsA 22 = w64 SHADOW_OFF)
  by (rewrite (rbn8_pres_get regs1 regsA 22%bv HPA) by rbn8_cs; exact B22).
assert (Hsep5 : VAL (A_OBJ 22) + 3 <= rbn_F X pos + 192 \/ rbn_F X pos + 192 + 48 <= VAL (A_OBJ 22)).
{ pose proof Hstr22 as (_ & _ & _ & _ & _ & Hfix22 & _).
  apply (rbn8_sep (in_img SEGS) (VAL (A_OBJ 22)) 3 (rbn_F X pos + 192) 48); [lia | lia | |].
  - intros x Hx. exact (proj1 (Hfix22 x ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia))).
  - intros x Hx Hi. exact (proj2 (HFpr x ltac:(lia)) Hi). }
eapply SRr_bind.
{ apply R5.
  - exact HJA.
  - exact (rbn8_lsrc X pos lyc1 Sc1 W1 memA mdA _ (VAL (A_OBJ 22)) [32; 40] HX HA HMA GM Hstr22).
  - exact H22m8.
  - exact (rbn8_lbuf_dp X pos lyc1 Sc1 W1 memA mdA HMA).
  - exact Hsep5.
  - lia.
  - left; reflexivity.
  - exact GA16.
  - exact GA12.
  - exact GA17.
  - exact GA11.
  - exact GA15.
  - exact GA13.
  - exact GA14.
  - exact R20A.
  - exact R22A. }
intros W3 c3 _ (-> & regsB & memB & mdB & -> & HJB & HKB & HOB & HEQB & HGB).
pose proof (Forall_inv HOB) as OB16. pose proof (Forall_inv (Forall_inv_tail HOB)) as OB12.
cbn [fst snd] in OB16, OB12.
cbn [rbn_lit5 length Z.of_nat Pos.of_succ_nat Pos.succ] in HEQB.
assert (HMB : rbn_mid B X pos lyc1 Sc1 W1 memB mdB (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 memA mdA memB mdB _ _ HX HMA HJB (Permutation_refl _)
    (rbn8_step_fr X pos lyc1 Sc1 W1 memA mdA _ memB (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)))
      (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + 2) HMA ltac:(lia) ltac:(lia) HEQB)).
  - intros a Ha. cbv beta in Ha. lia.
  - rewrite rbn8_sh_len; lia. }
assert (KAB : forall a, rbn_A X <= a < rbn_A X + 180 -> ~ (rbn_A X + 136 <= a < rbn_A X + 148) ->
  aview SEGS (w_H W1) memB a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha Hn. rewrite (HEQB a ltac:(lia) ltac:(lia)). exact (KEQA a ltac:(lia) Hn). }
assert (KAB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos + 192 <= a < rbn_F X pos + 240) ->
  aview SEGS (w_H W1) memB a = aview SEGS (w_H W1) memA a)
  by (intros a Ha Hn; apply HEQB; [exact Ha | lia]).
assert (ViB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 80) 8 (ri_i X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memB); [intros k Hk; apply KAB; lia | exact Vi]).
assert (VoB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 88) 8 (ri_o X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memB); [intros k Hk; apply KAB; lia | exact Vo]).
assert (VcapB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 128) 8 48)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memA memB); [intros k Hk; apply KAB2; lia | exact VcapA]).
assert (VnB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 136) 8 (Z.of_nat (length (rbm_NB X))))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memA memB); [intros k Hk; apply KAB2; lia | exact VnA]).
assert (VovB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 144) 4 0)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memA memB); [intros k Hk; apply KAB2; lia | exact VovA]).
assert (B9B : getr regsB 9 = w64 (rbn_A X)).
{ rewrite (rbn8_keep_get regsA regsB _ 9%bv HKB) by reflexivity.
  rewrite (rbn8_pres_get regs1 regsA 9%bv HPA) by rbn8_cs. exact B9. }
assert (R21B : getr regsB 21 = w64 (rbm_tok X)).
{ rewrite (rbn8_keep_get regsA regsB _ 21%bv HKB) by reflexivity.
  rewrite (rbn8_pres_get regs1 regsA 21%bv HPA) by rbn8_cs. exact R21. }
assert (Htok : 0 <= rbm_tok X <= 1) by (unfold rbm_tok, rbm_ovf; destruct (23 <? _); lia).
unfold rbn_cfg. replace (BASE + AF_reac_box_name + RBN_L5X) with (BASE + 10740) by (unfold AF_reac_box_name, RBN_L5X; lia).
eapply SRr_bind.
{ apply (rbn8_p2 REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memB mdB 0 regsB (rbn_A X) (ri_i X) (ri_o X) 48 (Z.of_nat (length (rbm_NB X))) 0
    (rbm_tok X) (Z.of_nat (length (rbm_NB X)) + 2) 0
    HJB B9B ltac:(lia) AR5 ltac:(lia) ltac:(lia) ltac:(lia) R21B ltac:(lia)
    (rbn8_out_get regsB 16%bv _ OB16) ltac:(lia) (rbn8_out_get regsB 12%bv _ OB12) ltac:(lia)
    ViB ltac:(lia) VoB ltac:(lia) VcapB ltac:(lia) VnB ltac:(lia) VovB ltac:(lia)). }
intros W4 c4 _ (-> & regsC & memC & mdC & -> & HJC & HKC & GC1 & GC10 & GC11 & GC12 & GC23 & KEQC & V40C & VcapC &
  VnC & VovC).
assert (HMC : rbn_mid B X pos lyc1 Sc1 W1 memC mdC (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 memB mdB memC mdC _ (fun _ => False) HX HMB HJC (Permutation_refl _)).
  - apply (rbn8_step_stk X lyc1 Sc1 W1 memB memC mdB (rbn_A X + 40) (rbn_A X + 148) HX (proj1 HJB)); [lia | lia |].
    intros a Ha Hn. apply KEQC; [exact Ha | lia | lia].
  - intros a [].
  - rewrite rbn8_sh_len; lia. }
rewrite rbn8_sig.
apply (K regsC memC mdC HMC).
- intros r Hr. unfold rbn8_keepl in Hr. cbn [In] in Hr.
  assert (Hr32 : 0 <= r < 32) by lia.
  rewrite (HKC r Hr32) by (cbn [In]; lia).
  rewrite (HKB r Hr32) by (cbn [In]; lia).
  apply HPA. unfold acallee_saved. lia.
- exact GC1.
- exact GC10.
- exact GC11.
- exact GC12.
- exact GC23.
- exact V40C.
- exact VnC.
- exact VovC.
- apply (rbn8_garr8_kept W1 memB memC); [exact HGB|]. intros a Ha. cbn [rbn_lit5 length Z.of_nat] in Ha.
  apply KEQC; lia.
- intros a Ha H1 H2. rewrite (KEQC a ltac:(lia) H1 H2). exact (KAB a Ha H2).
- intros a Ha Hn. rewrite (KEQC a ltac:(lia) ltac:(lia) ltac:(lia)). rewrite (HEQB a ltac:(lia) Hn).
  exact (KEQA a ltac:(lia) ltac:(lia)).
Qed.
Hypothesis L6F : rbn_L6_fits B.
Lemma rbn8_pC : forall X pos regs1 (regs : bvmap 5 word) lyc Sc W1 m md n1 (Q : world SEGS -> config -> Prop),
  rbn_cx B G X -> rbm_args X ->
  rbn_mid B X pos lyc Sc W1 m md (fun _ => False) (rbn_sh true true true true) ->
  rbn_rbase B X pos regs1 ->
  (forall r, In r rbn8_keepl -> getr regs (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  getr regs 23 = w64 1 ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 80) 8 (ri_i X) ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 88) 8 (ri_o X) ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 120) 8 (rbn_F X pos + 192) ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 128) 8 48 ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 136) 8 n1 ->
  val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 144) 4 0 ->
  0 <= n1 -> n1 + 6 <= 47 ->
  (forall (regs' : bvmap 5 word) m' md',
     rbn_mid B X pos lyc Sc W1 m' md' (fun _ => False) (rbn_sh true true true true) ->
     (forall r, In r rbn8_keepl -> getr regs' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
     getr regs' 1 = w64 (BASE + 10940) -> getr regs' 10 = w64 (rbn_A X + 120) -> getr regs' 11 = w64 (ri_o X) ->
     getr regs' 12 = w64 1 -> getr regs' 21 = w64 1 ->
     val_mem SEGS (mrestrict (w_H W1) m') (rbn_A X + 136) 8 (n1 + 6) ->
     val_mem SEGS (mrestrict (w_H W1) m') (rbn_A X + 144) 4 0 ->
     garr8 SEGS (mrestrict (w_H W1) m') (rbn_F X pos + 192 + n1) rbn_lit6 ->
     (forall a, rbn_A X <= a < rbn_A X + 180 -> ~ (rbn_A X + 136 <= a < rbn_A X + 148) ->
        aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
     (forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
        ~ (rbn_F X pos + 192 + n1 <= a < rbn_F X pos + 192 + n1 + 6) ->
        aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
     SRr SEGS W1 (cfg_at SEGS (BASE + AF_sb_dec) regs' m' md') Q) ->
  SRr SEGS W1 (cfg_at SEGS (BASE + 10772) regs m md) Q.
Proof.
intros X pos regs1 regs lyc Sc W1 m md n1 Q HX HA HM HRB KR R23 Vi Vo V120 V128 V136 V144 Hn1 Hn6 K.
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5).
destruct (rbn8_F_facts X pos lyc Sc W1 m md _ _ HM) as (Hin3 & FA3 & HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
destruct (rbn8_args X HA) as (Hnm & Htk & Hdp & Hoki & Hoko).
pose proof (rbn8_ok_rng _ Hoki) as Ri. pose proof (rbn8_ok_rng _ Hoko) as Ro.
pose proof HM as (HW & HJ1 & _). pose proof (proj1 HJ1) as HAR1.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct HIMG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H23m8 & Hstr23 & _).
assert (G9 : getr regs 9 = w64 (rbn_A X)) by (rewrite (rbn8_kl_get regs regs1 9%bv KR) by reflexivity; exact B9).
assert (G22 : getr regs 22 = w64 SHADOW_OFF) by (rewrite (rbn8_kl_get regs regs1 22%bv KR) by reflexivity; exact B22).
eapply SRr_bind.
{ apply (rbn8_p3 REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc Sc W1 m md 0 regs (rbn_A X) (ri_i X) (ri_o X) 48 n1 0
    HJ1 G9 ltac:(lia) AR5 ltac:(lia) ltac:(lia) ltac:(lia)
    Vi ltac:(lia) Vo ltac:(lia) V128 ltac:(lia) V136 ltac:(lia) V144 ltac:(lia)). }
intros W2 c2 _ (-> & regsA & memA & mdA & -> & HJA & HPA & GA11 & GA12 & GA13 & GA14 & GA15 & GA16 &
  KEQA & VcapA & VnA & VovA).
assert (HMA : rbn_mid B X pos lyc Sc W1 memA mdA (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc Sc lyc Sc W1 m md memA mdA _ (fun _ => False) HX HM HJA (Permutation_refl _)).
  - exact (rbn8_step_stk X lyc Sc W1 m memA md (rbn_A X + 136) (rbn_A X + 148) HX HAR1
      ltac:(lia) ltac:(lia) KEQA).
  - intros a [].
  - rewrite rbn8_sh_len; lia. }
assert (V120A : val_mem SEGS (mrestrict (w_H W1) memA) (rbn_A X + 120) 8 (rbn_F X pos + 192))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) m memA); [intros k Hk; apply KEQA; lia | exact V120]).
pose proof (L6F REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
  [(3, pos)] lyc Sc W1 memA mdA 0 regsA (rbn_A X) (rbn_F X pos + 192) n1 0 ltac:(lia)) as R6.
unfold rbn_L6_run in R6.
assert (R23A : getr regsA 23 = w64 1) by (rewrite (rbn8_pres_get regs regsA 23%bv HPA) by rbn8_cs; exact R23).
assert (R9A : getr regsA 9 = w64 (rbn_A X)) by (rewrite (rbn8_pres_get regs regsA 9%bv HPA) by rbn8_cs; exact G9).
assert (R22A : getr regsA 22 = w64 SHADOW_OFF) by (rewrite (rbn8_pres_get regs regsA 22%bv HPA) by rbn8_cs; exact G22).
pose proof Hstr23 as (_ & H23hi & _ & _ & _ & Hfix23 & _).
cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in H23hi, Hfix23.
assert (Hsep6 : VAL (A_OBJ 23) + 7 <= rbn_F X pos + 192 \/ rbn_F X pos + 192 + 48 <= VAL (A_OBJ 23)).
{ apply (rbn8_sep (in_img SEGS) (VAL (A_OBJ 23)) 7 (rbn_F X pos + 192) 48); [lia | lia | |].
  - intros x Hx. exact (proj1 (Hfix23 x ltac:(lia))).
  - intros x Hx Hi. exact (proj2 (HFpr x ltac:(lia)) Hi). }
eapply SRr_bind.
{ apply R6.
  - exact HJA.
  - exact (rbn8_lsrc X pos lyc Sc W1 memA mdA _ (VAL (A_OBJ 23)) [32; 105; 110; 32; 47; 32] HX HA HMA GM Hstr23).
  - exact H23m8.
  - lia.
  - lia.
  - right. lia.
  - exact (rbn8_lbuf_dp X pos lyc Sc W1 memA mdA HMA).
  - exact Hsep6.
  - exact V120A.
  - right. lia.
  - lia.
  - left; reflexivity.
  - exact GA15.
  - exact GA12.
  - exact GA16.
  - exact R23A.
  - exact GA14.
  - exact GA11.
  - exact GA13.
  - exact R9A.
  - exact R22A. }
intros W3 c3 _ (-> & regsB & memB & mdB & -> & HJB & HKB & HOB & HEQB & HGB).
pose proof (Forall_inv HOB) as OB15. pose proof (Forall_inv (Forall_inv_tail HOB)) as OB12.
cbn [fst snd] in OB15, OB12.
cbn [rbn_lit6 length Z.of_nat Pos.of_succ_nat Pos.succ] in HEQB.
assert (HMB : rbn_mid B X pos lyc Sc W1 memB mdB (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc Sc lyc Sc W1 memA mdA memB mdB _ _ HX HMA HJB (Permutation_refl _)
    (rbn8_step_fr X pos lyc Sc W1 memA mdA _ memB (rbn_F X pos + 192 + n1) (rbn_F X pos + 192 + n1 + 6)
      HMA ltac:(lia) ltac:(lia) HEQB)).
  - intros a Ha. cbv beta in Ha. lia.
  - rewrite rbn8_sh_len; lia. }
assert (KAB : forall a, rbn_A X <= a < rbn_A X + 180 -> ~ (rbn_A X + 136 <= a < rbn_A X + 148) ->
  aview SEGS (w_H W1) memB a = aview SEGS (w_H W1) m a).
{ intros a Ha Hn. rewrite (HEQB a ltac:(lia) ltac:(lia)). exact (KEQA a ltac:(lia) Hn). }
assert (KAB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_F X pos + 192 <= a < rbn_F X pos + 240) ->
  aview SEGS (w_H W1) memB a = aview SEGS (w_H W1) memA a)
  by (intros a Ha Hn; apply HEQB; [exact Ha | lia]).
assert (ViB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 80) 8 (ri_i X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) m memB); [intros k Hk; apply KAB; lia | exact Vi]).
assert (VoB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 88) 8 (ri_o X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) m memB); [intros k Hk; apply KAB; lia | exact Vo]).
assert (VcapB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 128) 8 48)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memA memB); [intros k Hk; apply KAB2; lia | exact VcapA]).
assert (VnB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 136) 8 n1)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memA memB); [intros k Hk; apply KAB2; lia | exact VnA]).
assert (VovB : val_mem SEGS (mrestrict (w_H W1) memB) (rbn_A X + 144) 4 0)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memA memB); [intros k Hk; apply KAB2; lia | exact VovA]).
assert (B9B : getr regsB 9 = w64 (rbn_A X))
  by (rewrite (rbn8_keep_get regsA regsB _ 9%bv HKB) by reflexivity; exact R9A).
unfold rbn_cfg. replace (BASE + AF_reac_box_name + RBN_L6X) with (BASE + 10912) by (unfold AF_reac_box_name, RBN_L6X; lia).
eapply SRr_bind.
{ apply (rbn8_p4 REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc Sc W1 memB mdB 0 regsB (rbn_A X) (ri_i X) (ri_o X) 48 n1 0 (n1 + 6) 0
    HJB B9B ltac:(lia) AR5 ltac:(lia) ltac:(lia) ltac:(lia)
    (rbn8_out_get regsB 15%bv _ OB15) ltac:(lia) (rbn8_out_get regsB 12%bv _ OB12) ltac:(lia)
    ViB ltac:(lia) VoB ltac:(lia) VcapB ltac:(lia) VnB ltac:(lia) VovB ltac:(lia)). }
intros W4 c4 _ (-> & regsC & memC & mdC & -> & HJC & HKC & GC1 & GC10 & GC11 & GC12 & GC21 & KEQC & VcapC & VnC & VovC).
assert (HMC : rbn_mid B X pos lyc Sc W1 memC mdC (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc Sc lyc Sc W1 memB mdB memC mdC _ (fun _ => False) HX HMB HJC (Permutation_refl _)).
  - exact (rbn8_step_stk X lyc Sc W1 memB memC mdB (rbn_A X + 136) (rbn_A X + 148) HX (proj1 HJB)
      ltac:(lia) ltac:(lia) KEQC).
  - intros a [].
  - rewrite rbn8_sh_len; lia. }
rewrite rbn8_sig.
apply (K regsC memC mdC HMC).
- intros r Hr. unfold rbn8_keepl in Hr. cbn [In] in Hr.
  assert (Hr32 : 0 <= r < 32) by lia.
  rewrite (HKC r Hr32) by (cbn [In]; lia).
  rewrite (HKB r Hr32) by (cbn [In]; lia).
  rewrite (HPA r) by (unfold acallee_saved; lia).
  exact (KR r ltac:(unfold rbn8_keepl; cbn [In]; lia)).
- exact GC1.
- exact GC10.
- exact GC11.
- exact GC12.
- exact GC21.
- exact VnC.
- exact VovC.
- apply (rbn8_garr8_kept W1 memB memC); [exact HGB|]. intros a Ha. cbn [rbn_lit6 length Z.of_nat] in Ha.
  apply KEQC; lia.
- intros a Ha H1. rewrite (KEQC a ltac:(lia) H1). exact (KAB a Ha H1).
- intros a Ha Hn. rewrite (KEQC a ltac:(lia) ltac:(lia)). rewrite (HEQB a ltac:(lia) Hn).
  exact (KEQA a ltac:(lia) ltac:(lia)).
Qed.
Theorem rbn_seg8 : rbn_seg8_stmt B G.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H8.
pose proof H8 as (HM & HRB & R18 & R27 & R24 & R25 & R20 & R26 & R21 & HC & HNB & HTB & HDB & HA).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn8_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5).
destruct (rbn8_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (Hin3 & FA3 & HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
destruct (rbn8_args X HA) as (Hnm & Htk & Hdp & Hoki & Hoko).
pose proof (rbn8_ok_rng _ Hoki) as Ri. pose proof (rbn8_ok_rng _ Hoko) as Ro.
pose proof (rbn8_dec_len _ Hoki) as Li. pose proof (rbn8_dec_len _ Hoko) as Lo.
pose proof (rbn8_dec_eq _ Hoki) as Ei. pose proof (rbn8_dec_eq _ Hoko) as Eo.
assert (HNB23 : Z.of_nat (length (rbm_NB X)) <= 23)
  by (unfold rbm_NB; pose proof (firstn_le_length 23 (rbm_NM X)); lia).
assert (HTB23 : Z.of_nat (length (rbm_TB X)) <= 23)
  by (unfold rbm_TB; pose proof (firstn_le_length 23 (bn_TK (rbm_NB X))); lia).
assert (LEi : Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1)) <= 2) by (rewrite Ei; lia).
assert (LEo : Z.of_nat (length (sb_dec_c.sb_dec_D (ri_o X) 1)) <= 2) by (rewrite Eo; lia).
pose proof HC as HC0. apply rbn8_cells_app in HC0. destruct HC0 as (HC6 & HR2).
cbn [rbn_rec2 rbn_cells] in HR2. destruct HR2 as (V120 & V128 & _).
pose proof HC6 as HC6'. unfold rbn_locs6, rbn_locs4 in HC6'. cbn [app rbn_cells] in HC6'.
destruct HC6' as (_ & _ & _ & _ & _ & Vi & Vo & _).
rewrite firstn_all2 in HDB by lia.
apply (rbn8_pA X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ HX H8).
intros regsA mA mdA HMA KA GA1 GA10 GA11 GA12 GA23 VA40 VA136 VA144 HGA KSA KFA.
assert (VA120 : val_mem SEGS (mrestrict (w_H W1) mA) (rbn_A X + 120) 8 (rbn_F X pos + 192))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mA); [intros k Hk; apply KSA; lia | exact V120]).
assert (VA128 : val_mem SEGS (mrestrict (w_H W1) mA) (rbn_A X + 128) 8 48)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mA); [intros k Hk; apply KSA; lia | exact V128]).
assert (ViA : val_mem SEGS (mrestrict (w_H W1) mA) (rbn_A X + 80) 8 (ri_i X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mA); [intros k Hk; apply KSA; lia | exact Vi]).
assert (VoA : val_mem SEGS (mrestrict (w_H W1) mA) (rbn_A X + 88) 8 (ri_o X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mA); [intros k Hk; apply KSA; lia | exact Vo]).
assert (GA2 : getr regsA 2 = w64 (rbn_A X)) by (rewrite (rbn8_kl_get regsA regs1 2%bv KA) by reflexivity; exact B2).
assert (GA3 : getr regsA 3 = w64 (as_gp B)) by (rewrite (rbn8_kl_get regsA regs1 3%bv KA) by reflexivity; exact B3).
assert (GA4 : getr regsA 4 = w64 (as_tp B)) by (rewrite (rbn8_kl_get regsA regs1 4%bv KA) by reflexivity; exact B4).
apply (rbn8_call X pos lyc1 Sc1 W1 mA mdA regsA (ri_i X) (Z.of_nat (length (rbm_NB X)) + 2) 10772 _ HX HMA GA1
  ltac:(lia) eq_refl GA2 GA3 GA4 GA10 GA11 GA12 ltac:(lia) VA120 VA128 VA136 VA144 ltac:(lia) ltac:(lia)).
intros regsD lyD SD mD mdD HMD HPD VD136 VD144 HGD KSD KFD.
assert (KD : forall r, In r rbn8_keepl -> getr regsD (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HPD r) by (unfold rbn8_keepl in Hr; cbn [In] in Hr; unfold acallee_saved; lia).
  exact (KA r Hr). }
assert (GD23 : getr regsD 23 = w64 1) by (rewrite (rbn8_pres_get regsA regsD 23%bv HPD) by rbn8_cs; exact GA23).
assert (VD120 : val_mem SEGS (mrestrict (w_H W1) mD) (rbn_A X + 120) 8 (rbn_F X pos + 192))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mA mD); [intros k Hk; apply KSD; lia | exact VA120]).
assert (VD128 : val_mem SEGS (mrestrict (w_H W1) mD) (rbn_A X + 128) 8 48)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mA mD); [intros k Hk; apply KSD; lia | exact VA128]).
assert (ViD : val_mem SEGS (mrestrict (w_H W1) mD) (rbn_A X + 80) 8 (ri_i X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mA mD); [intros k Hk; apply KSD; lia | exact ViA]).
assert (VoD : val_mem SEGS (mrestrict (w_H W1) mD) (rbn_A X + 88) 8 (ri_o X))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mA mD); [intros k Hk; apply KSD; lia | exact VoA]).
apply (rbn8_pC X pos regs1 regsD lyD SD W1 mD mdD
  (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1))) _
  HX HA HMD HRB KD GD23 ViD VoD VD120 VD128 VD136 VD144 ltac:(lia) ltac:(lia)).
intros regsE mE mdE HME KE GE1 GE10 GE11 GE12 GE21 VE136 VE144 HGE KSE KFE.
assert (VE120 : val_mem SEGS (mrestrict (w_H W1) mE) (rbn_A X + 120) 8 (rbn_F X pos + 192))
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mD mE); [intros k Hk; apply KSE; lia | exact VD120]).
assert (VE128 : val_mem SEGS (mrestrict (w_H W1) mE) (rbn_A X + 128) 8 48)
  by (apply (val_mem_kept SEGS (w_H W1) (w_H W1) mD mE); [intros k Hk; apply KSE; lia | exact VD128]).
assert (GE2 : getr regsE 2 = w64 (rbn_A X)) by (rewrite (rbn8_kl_get regsE regs1 2%bv KE) by reflexivity; exact B2).
assert (GE3 : getr regsE 3 = w64 (as_gp B)) by (rewrite (rbn8_kl_get regsE regs1 3%bv KE) by reflexivity; exact B3).
assert (GE4 : getr regsE 4 = w64 (as_tp B)) by (rewrite (rbn8_kl_get regsE regs1 4%bv KE) by reflexivity; exact B4).
apply (rbn8_call X pos lyD SD W1 mE mdE regsE (ri_o X)
  (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1)) + 6) 10940 _ HX HME GE1
  ltac:(lia) eq_refl GE2 GE3 GE4 GE10 GE11 GE12 ltac:(lia) VE120 VE128 VE136 VE144 ltac:(lia) ltac:(lia)).
intros regsF lyF SF mF mdF HMF HPF VF136 VF144 HGF KSF KFF.
assert (KF : forall r, In r rbn8_keepl -> getr regsF (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HPF r) by (unfold rbn8_keepl in Hr; cbn [In] in Hr; unfold acallee_saved; lia).
  exact (KE r Hr). }
assert (KSall : forall a, rbn_A X <= a < rbn_A X + 180 -> ~ (rbn_A X + 40 <= a < rbn_A X + 48) ->
  ~ (rbn_A X + 136 <= a < rbn_A X + 148) -> aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2. rewrite (KSF a Ha H2), (KSE a Ha H2), (KSD a Ha H2). exact (KSA a Ha H1 H2). }
assert (KS40 : forall a, rbn_A X <= a < rbn_A X + 180 -> ~ (rbn_A X + 136 <= a < rbn_A X + 148) ->
  aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) mA a).
{ intros a Ha H2. rewrite (KSF a Ha H2), (KSE a Ha H2). exact (KSD a Ha H2). }
assert (KFlow : forall a, rbn_F X pos <= a < rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) ->
  aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha. rewrite (KFF a ltac:(lia) ltac:(lia)), (KFE a ltac:(lia) ltac:(lia)), (KFD a ltac:(lia) ltac:(lia)).
  exact (KFA a ltac:(lia) ltac:(lia)). }
assert (HD9 : Z.of_nat (length (rbm_D9 X)) = Z.of_nat (length (rbm_NB X)) + 2 +
  Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1)) + 6 + Z.of_nat (length (sb_dec_c.sb_dec_D (ri_o X) 1))).
{ unfold rbm_D9. rewrite Ei, Eo. rewrite !length_app. cbn [length]. lia. }
apply SRr_ret.
exists pos, regsF, lyF, SF, mF, mdF. split.
{ unfold rbn_cfg. replace (BASE + AF_reac_box_name + RBN_P9) with (BASE + 10940)
    by (unfold AF_reac_box_name, RBN_P9; lia). reflexivity. }
unfold rbn_st9.
split; [exact HMF|].
split.
{ unfold rbn_rbase.
  split; [rewrite (rbn8_kl_get regsF regs1 2%bv KF) by reflexivity; exact B2|].
  split; [rewrite (rbn8_kl_get regsF regs1 3%bv KF) by reflexivity; exact B3|].
  split; [rewrite (rbn8_kl_get regsF regs1 4%bv KF) by reflexivity; exact B4|].
  split; [rewrite (rbn8_kl_get regsF regs1 8%bv KF) by reflexivity; exact B8|].
  split; [rewrite (rbn8_kl_get regsF regs1 9%bv KF) by reflexivity; exact B9|].
  split; [rewrite (rbn8_kl_get regsF regs1 19%bv KF) by reflexivity; exact B19|].
  rewrite (rbn8_kl_get regsF regs1 22%bv KF) by reflexivity; exact B22. }
split; [rewrite (rbn8_kl_get regsF regs1 18%bv KF) by reflexivity; exact R18|].
split; [rewrite (rbn8_kl_get regsF regs1 27%bv KF) by reflexivity; exact R27|].
split; [rewrite (rbn8_kl_get regsF regs1 24%bv KF) by reflexivity; exact R24|].
split; [rewrite (rbn8_kl_get regsF regs1 25%bv KF) by reflexivity; exact R25|].
split; [rewrite (rbn8_kl_get regsF regs1 20%bv KF) by reflexivity; exact R20|].
split; [rewrite (rbn8_kl_get regsF regs1 26%bv KF) by reflexivity; exact R26|].
split; [rewrite (rbn8_pres_get regsE regsF 21%bv HPF) by rbn8_cs; exact GE21|].
split.
{ apply rbn8_cells_app. split.
  { apply (rbn8_cells_kept (w_H W1) (w_H W1) memc1 mF); [|exact HC6].
    intros a n v k Hin Hk. pose proof (rbn8_locs6_rng X pos a n v Hin) as (L1 & L2 & L3 & L4).
    apply KSall; lia. }
  apply rbn8_cells_app. split.
  { cbn [rbn_rec2 rbn_cells].
    split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mF); [intros k Hk; apply KSall; lia | exact V120]|].
    split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mF); [intros k Hk; apply KSall; lia | exact V128]|].
    split; [rewrite Z.min_l by lia; rewrite HD9; exact VF136|].
    split; [|exact I].
    unfold rbm_ovf. rewrite (proj2 (Z.ltb_ge _ _)) by lia. exact VF144. }
  cbn [rbn_cells]. split; [|exact I].
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) mA mF); [intros k Hk; apply KS40; lia | exact VA40]. }
split.
{ apply (rbn8_garr8_kept W1 memc1 mF); [exact HNB|]. intros a Ha.
  rewrite length_app in Ha. cbn [length] in Ha. apply KFlow. lia. }
split.
{ apply (rbn8_garr8_kept W1 memc1 mF); [exact HTB|]. intros a Ha.
  rewrite length_app in Ha. cbn [length] in Ha. apply KFlow. lia. }
split; [|exact HA].
rewrite firstn_all2 by lia.
assert (G1 : garr8 SEGS (mrestrict (w_H W1) mF) (rbn_F X pos + 192) (rbm_NB X)).
{ apply (rbn8_garr8_kept W1 memc1 mF); [exact HDB|]. intros a Ha. apply KFlow. lia. }
assert (G2 : garr8 SEGS (mrestrict (w_H W1) mF) (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X))) rbn_lit5).
{ apply (rbn8_garr8_kept W1 mA mF); [exact HGA|]. intros a Ha. cbn [rbn_lit5 length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
  rewrite (KFF a ltac:(lia) ltac:(lia)), (KFE a ltac:(lia) ltac:(lia)). exact (KFD a ltac:(lia) ltac:(lia)). }
assert (G3 : garr8 SEGS (mrestrict (w_H W1) mF) (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2))
  (sb_dec_c.sb_dec_D (ri_i X) 1)).
{ apply (rbn8_garr8_kept W1 mD mF); [exact HGD|]. intros a Ha.
  rewrite (KFF a ltac:(lia) ltac:(lia)). exact (KFE a ltac:(lia) ltac:(lia)). }
assert (G4 : garr8 SEGS (mrestrict (w_H W1) mF)
  (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1)))) rbn_lit6).
{ apply (rbn8_garr8_kept W1 mE mF); [exact HGE|]. intros a Ha.
  cbn [rbn_lit6 length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. exact (KFF a ltac:(lia) ltac:(lia)). }
unfold rbm_D9. rewrite <- Ei, <- Eo.
apply (rbn8_garr8_cat _ _ (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X))) _ _ G1); [|lia].
apply (rbn8_garr8_cat _ _ (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2)) _ _ G2);
  [|cbn [rbn_lit5 length Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
apply (rbn8_garr8_cat _ _ (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 +
  Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1)))) _ _ G3); [|lia].
apply (rbn8_garr8_cat _ _ (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 +
  Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1)) + 6)) _ _ G4);
  [exact HGF | cbn [rbn_lit6 length Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.
End h.
End f.
End d.
