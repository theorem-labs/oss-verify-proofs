(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1668 of its 1701 lines of code are new or changed and 36 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YG0t YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoRo SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops ReacBoxNameSeg4.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn8_globs_rng : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 47)) disco_globs = true.
Proof. vm_compute. reflexivity. Qed.
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
Lemma rbn8_sep : forall (P : Z -> Prop) lo1 n1 lo2 n2, 0 < n1 -> 0 < n2 ->
  (forall x, lo1 <= x < lo1 + n1 -> P x) -> (forall x, lo2 <= x < lo2 + n2 -> ~ P x) ->
  lo1 + n1 <= lo2 \/ lo2 + n2 <= lo1.
Proof.
intros P lo1 n1 lo2 n2 H1 H2 HA HB.
destruct (Z_le_gt_dec (lo1 + n1) lo2) as [H | H]; [left; lia|].
destruct (Z_le_gt_dec (lo2 + n2) lo1) as [H' | H']; [right; lia|].
exfalso. apply (HB (Z.max lo1 lo2) ltac:(lia)). apply HA. lia.
Qed.
Lemma rbn8_sh_db : forall i, 24 <= i < 30 -> nth (Z.to_nat i) (rbn_sh true true true true) 0 = 0.
Proof.
intros i Hi.
assert (E : Z.to_nat i = 24%nat \/ Z.to_nat i = 25%nat \/ Z.to_nat i = 26%nat \/ Z.to_nat i = 27%nat \/
            Z.to_nat i = 28%nat \/ Z.to_nat i = 29%nat) by lia.
destruct E as [E | [E | [E | [E | [E | E]]]]]; rewrite E; reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
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
Lemma denot_atom0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E n v 0 H Hv ltac:(lia)). lia.
Qed.
Lemma denot_lit0 : forall E v, 0 <= v < 2 ^ 64 -> sv_denot E (SLit v) = Z_to_bv 64 v.
Proof.
intros E v Hv. rewrite denot_lit_U. f_equal. rewrite U_SLit. apply zcanon_id. unfold M64. lia.
Qed.
Lemma denot_atomc : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
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
Lemma rbn8_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; [tauto|]. rewrite IH. tauto.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn8_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A pc i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  st_ok_pi SEGS VAL (ERB8 regs i o cap n ov) (ss_rbn8 pc)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A pc i o cap n ov
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
Lemma rbn8_entryT : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A pc i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  st_ok_pi SEGS VAL (ERB8 regs i o cap n ov) (ss_rbn8T pc)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A pc i o cap n ov
HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof (rbn8_entry fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A pc i o cap n ov
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
Lemma rbn8_step_glob : forall X pos lyc1 Sc1 W1 mdc1 sh (m m' : word -> option byte) lo hi,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  (forall a, lo <= a < hi -> ~ in_img SEGS a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
  rbn8_step X lyc1 Sc1 W1 W1 m m' (fun a => lo <= a < hi).
Proof.
intros X pos lyc1 Sc1 W1 mdc1 sh m m' lo hi HX HM Hni HEQ.
pose proof HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
split; [|split; [|split]].
- intros a Ha Hw He. apply HEQ; [lia | exact He].
- intros b mm j Hb Hj He.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb) as (_ & Hb4 & Hbc & _).
  apply HEQ; [lia | exact He].
- intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  apply HEQ; [lia|]. intros Hc. exact (Hni a Hc Hia).
- intros cid p a Hcp Ha He.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp) as (Hc4096 & Hcceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
  assert (Hrng : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha; [lia|].
    pose proof (rbn_sh_band (frame_addr lyc1 cid p) (fs_frame_bytes cid)
      (a - shadow_addr (frame_addr lyc1 cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
    unfold kLowShadowBeg, kHighMemBeg in Hb. lia. }
  apply HEQ; [exact Hrng | exact He].
Qed.
Lemma rbn8_mid_step : forall X pos lyc1 Sc1 lyc2 Sc2 (W1 W2 : world SEGS) m mdc1 m' md' sh Er,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 m' md' (ri_k X) ->
  frames Sc2 = frames Sc1 -> Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  rbn8_step X lyc1 Sc1 W1 W2 m m' Er ->
  (forall a, Er a -> rbn_F X pos <= a < rbn_F X pos + 504) ->
  Z.of_nat (length sh) <= 64 ->
  rbn_mid B X pos lyc2 Sc2 W2 m' md' (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 lyc2 Sc2 W1 W2 m mdc1 m' md' sh Er HX HM HJ2 Hfr2 Hperm2 HST HEr Hsh.
destruct HST as (C1 & C2 & C3 & C4).
pose proof (rbn_fa B X pos lyc1 Sc1 W1 m mdc1 _ sh HX HM) as FA.
destruct (rbn_F_facts B LAWS X pos lyc1 Sc1 W1 m mdc1 _ sh HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (FR : forall c p, frame_rng lyc1 (c, p) = frame_rng (ri_lyc X) (c, p))
  by (intros c p0; unfold frame_rng; cbn [fst snd]; rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HnErH : forall a, alloc_ceiling <= a -> ~ Er a) by (intros a Ha He; pose proof (HEr a He); lia).
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
  - intros a Ha Hn' He. rewrite (C1 a Ha ltac:(unfold rbn_SP in *; lia) (HnErH a ltac:(lia))).
    exact (K1 a Ha Hn' He).
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
    assert (HnE : ~ Er a).
    { intros He2. pose proof (HEr a He2) as HEa. unfold rbn_F in HEa. destruct Ha as [Ha | Ha].
      - destruct (in_split _ _ Hcp) as (l2 & l3 & El).
        pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
          ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
        unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !FA, Hfb3 in Hd.
        unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. lia.
      - unfold in_zr in Ha. cbn [fst snd] in Ha. rewrite FA in Hc4096, Hcceil.
        pose proof (rbn_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
          (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
        unfold rbn_F in Happ. destruct (Happ a ltac:(lia)); unfold kLowShadowBeg, kHighMemBeg in *; lia. }
    rewrite (C4 cid p a Hcp1 ltac:(rewrite FR, FA; exact Ha) HnE). exact (K4 cid p a Hcp Ha He).
  - intros a Ha Hn' Hp.
    apply (apresent_transfer SEGS (w_H W1) (w_H W2) m m' a);
      [lia | intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia
       | apply C1; [lia | unfold rbn_SP in *; lia | exact (HnErH a ltac:(lia))]
       | exact (K5 a Ha Hn' Hp)].
  - intros a Ha. apply Hpres2. unfold rbn_SP in *. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m'); [|exact (Hfr j r Hj)].
  intros kk Hk. apply C1; [unfold rbn_SP in *; lia | unfold rbn_SP in *; lia |].
  apply HnErH. unfold rbn_SP in *. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m'); [|exact Hfl].
  intros kk Hk. apply (C4 3 pos); [exact Hin3 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3, Hfb3; lia|].
  intros He2. pose proof (HEr _ He2). lia. }
unfold rbn_shadow_at. intros j Hj.
pose proof (rbn_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
assert (HnS : ~ Er (shadow_addr (rbn_F X pos) + j)).
{ intros He2. pose proof (HEr _ He2) as HE2.
  destruct (Happ (shadow_addr (rbn_F X pos) + j) ltac:(lia)) as [Hq | Hq];
  unfold kLowShadowBeg in Hb, Hq; unfold kHighMemBeg in Hb, Hq; lia. }
rewrite (C4 3 pos (shadow_addr (rbn_F X pos) + j) Hin3
  ltac:(right; unfold in_zr; cbn [fst snd]; rewrite FA3, Hfb3; change (512 / 8) with 64; lia) HnS).
exact (Hsh0 j Hj).
Qed.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Lemma rbn8_ro_eq : forall (W1 W2 : world SEGS) (m1 m2 : word -> option byte) q sz a,
  rbn_ro q sz ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) m1) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m2) ->
  q <= a < q + sz -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a.
Proof.
intros W1 W2 m1 m2 q sz a Hro HA1 HA2 Ha.
assert (Hin : In (q, sz) disco_ro_ranges) by (apply in_or_app; left; exact (proj1 Hro)).
assert (Hin' : In (q, sz) disco_ro_all) by (unfold disco_ro_all; apply in_or_app; left; exact Hin).
pose proof (disco_ro_in_ro q sz a Hin' Ha) as Hinro.
pose proof (disco_ro_unowned_at B q sz DRO Hin) as HU.
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ q sz a HA2 Hinro HU Ha).
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ q sz a HA1 Hinro HU Ha). reflexivity.
Qed.
Lemma rbn8_lsrc_of : forall ly1 S1 (W1 W2 : world SEGS) (m1 m2 : word -> option byte) md1 q sz l,
  AR SEGS B ly1 S1 W1 m1 md1 -> rbn_ro q sz -> Z.of_nat (length l) = sz -> 0 < sz ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) m1) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m2) ->
  garr8 SEGS (mrestrict (w_H W2) m2) q l ->
  rbn_lsrc W1 m1 q l.
Proof.
intros ly1 S1 W1 W2 m1 m2 md1 q sz l HAR Hro Hlen Hsz HA1 HA2 HG.
assert (Hb : (0 <=? fst (q, sz)) && (fst (q, sz) + snd (q, sz) <=? 2 ^ 47) = true).
{ pose proof rbn8_globs_rng as HF. rewrite forallb_forall in HF. exact (HF (q, sz) (proj1 Hro)). }
cbn [fst snd] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W2) m2)); [exact HG|].
  intros a Ha. apply (mbyte_of_aview SEGS). apply (rbn8_ro_eq W2 W1 m2 m1 q sz a Hro HA2 HA1). lia. }
split; [lia|]. split; [lia|]. split; [lia|].
exact (ro_usable_glob SEGS B disco_globs ly1 S1 W1 m1 md1 q sz q (Z.of_nat (length l)) GM (proj1 Hro) HAR
  ltac:(lia) ltac:(lia)).
Qed.
Lemma rbn8_p1 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_P8) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L5) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       aregs_preserved regs regs1 /\
       getr regs1 11 = w64 1 /\ getr regs1 12 = w64 ov /\ getr regs1 13 = w64 47 /\
       getr regs1 14 = w64 (VAL (A_OBJ 28)) /\ getr regs1 15 = w64 3 /\ getr regs1 16 = w64 n /\
       getr regs1 17 = w64 32 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 n /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ov).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov
HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof (pa_val_range (A_OBJ 28)) as VR28.
pose proof (rbn8_entry fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 15652 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
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
assert (E269 : ew E 269 = Z_to_bv 64 (VAL (A_OBJ 28)))
  by (subst E; unfold ERB8; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = A) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_P8) with (BASE + 15652) by (unfold AF_reac_box_name, RBN_P8; lia).
paj_run_to_sh RUNTOP HS HJ 15684.
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
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (apply denot_lit0; lia).
assert (D47 : sv_denot E (SLit 47) = Z_to_bv 64 47) by (apply denot_lit0; lia).
assert (D3 : sv_denot E (SLit 3) = Z_to_bv 64 3) by (apply denot_lit0; lia).
assert (D32 : sv_denot E (SLit 32) = Z_to_bv 64 32) by (apply denot_lit0; lia).
assert (Dov : sv_denot E (SOff 36 0) = Z_to_bv 64 ov) by (apply (denot_atom0 E 36 ov E36); lia).
assert (Dn : sv_denot E (SOff 35 0) = Z_to_bv 64 n) by (apply (denot_atom0 E 35 n E35); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (denot_atom0 E 34 cap E34); lia).
assert (Dq : sv_denot E (SOff 269 0) = Z_to_bv 64 (VAL (A_OBJ 28)))
  by (apply (denot_atom0 E 269 (VAL (A_OBJ 28)) E269); lia).
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 1) D1 G11.
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 ov) Dov G12.
rreg_by HS (13%bv : bv 5) (Z_to_bv 64 47) D47 G13.
rreg_by HS (14%bv : bv 5) (Z_to_bv 64 (VAL (A_OBJ 28))) Dq G14.
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 3) D3 G15.
rreg_by HS (16%bv : bv 5) (Z_to_bv 64 n) Dn G16.
rreg_by HS (17%bv : bv 5) (Z_to_bv 64 32) D32 G17.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs (rbn8_extra i o cap n ov) HS);
  [split; [intros mm Hm; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity] | vm_compute; reflexivity]. }
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_L5) with (BASE + 15684) by (unfold AF_reac_box_name, RBN_L5; lia).
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
Lemma rbn8_p3 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A i o cap n ov : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> alloc_ceiling <= A -> A mod 32 = 0 -> sp0 - STK <= A -> A + 180 <= sp0 -> sp0 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> 0 <= i <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o -> 0 <= o <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 128) 8 cap -> 0 <= cap <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 n -> 0 <= n <= 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 ov -> 0 <= ov <= 1 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + 15824) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L6) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       aregs_preserved regs regs1 /\
       getr regs1 11 = w64 cap /\ getr regs1 12 = w64 ov /\ getr regs1 13 = w64 (VAL (A_OBJ 29)) /\
       getr regs1 14 = w64 7 /\ getr regs1 15 = w64 n /\ getr regs1 16 = w64 32 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 n /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ov).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov
HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof (pa_val_range (A_OBJ 29)) as VR29.
pose proof (rbn8_entry fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 15824 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
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
assert (E270 : ew E 270 = Z_to_bv 64 (VAL (A_OBJ 29)))
  by (subst E; unfold ERB8; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = A) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cfg_at, w64.
paj_run_to_sh RUNTOP HS HJ 15852.
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
assert (D7 : sv_denot E (SLit 7) = Z_to_bv 64 7) by (apply denot_lit0; lia).
assert (D32 : sv_denot E (SLit 32) = Z_to_bv 64 32) by (apply denot_lit0; lia).
assert (Dov : sv_denot E (SOff 36 0) = Z_to_bv 64 ov) by (apply (denot_atom0 E 36 ov E36); lia).
assert (Dn : sv_denot E (SOff 35 0) = Z_to_bv 64 n) by (apply (denot_atom0 E 35 n E35); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (denot_atom0 E 34 cap E34); lia).
assert (Dq : sv_denot E (SOff 270 0) = Z_to_bv 64 (VAL (A_OBJ 29)))
  by (apply (denot_atom0 E 270 (VAL (A_OBJ 29)) E270); lia).
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 cap) Dcap G11.
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 ov) Dov G12.
rreg_by HS (13%bv : bv 5) (Z_to_bv 64 (VAL (A_OBJ 29))) Dq G13.
rreg_by HS (14%bv : bv 5) (Z_to_bv 64 7) D7 G14.
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 n) Dn G15.
rreg_by HS (16%bv : bv 5) (Z_to_bv 64 32) D32 G16.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs (rbn8_extra i o cap n ov) HS);
  [split; [intros mm Hm; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity] | vm_compute; reflexivity]. }
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_L6) with (BASE + 15852) by (unfold AF_reac_box_name, RBN_L6; lia).
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
Lemma rbn8_keep : forall `{fq : YK11.FPState} (H : word -> bool) ss ms (regs0 : bvmap 5 word) i o cap n ov cl,
  st_ok SEGS (ERB8 regs0 i o cap n ov) ss (restrict H ms) ->
  forallb (fun r : bv 5 => existsb (Z.eqb (bv_unsigned r)) cl
             || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) all_regs = true ->
  rbn_keep_regs regs0 (ms_regs ms) cl.
Proof.
intros fq H ss ms regs0 i o cap n ov cl HS Hf r Hr Hn.
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
rewrite (denot_atom0 (ERB8 regs0 i o cap n ov) (Z.to_nat r) (bv_unsigned (getr regs0 (Z_to_bv 5 r)))).
- apply Z_to_bv_bv_unsigned.
- rewrite rbn8_ew by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs0 (rbn8_extra i o cap n ov) (Z.to_nat r) (Z_to_bv 5 r) ltac:(rewrite Hu; lia)).
  symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
Lemma rbn8_p2 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
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
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + 15792) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 1; 10; 11; 12; 23] /\
       getr regs1 1 = w64 (BASE + 15824) /\ getr regs1 10 = w64 (A + 120) /\
       getr regs1 11 = w64 i /\ getr regs1 12 = w64 1 /\ getr regs1 23 = w64 1 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 40 <= a < A + 48) -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 40) 8 tok /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 nn /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ovv).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov tok nn ovv
HJ H9 HAc HA32 HAlo HAhi Hsp0 H21 Rtok H16 Rnn H12 Rovv Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (rbn8_entryT fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 15792 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
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
assert (E240 : ew E 240 = Z_to_bv 64 BASE)
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
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (apply denot_lit0; lia).
assert (Di : sv_denot E (SOff 32 0) = Z_to_bv 64 i) by (apply (denot_atom0 E 32 i E32); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (denot_atom0 E 34 cap E34); lia).
assert (Dnn : sv_denot E (SOff 16 0) = Z_to_bv 64 nn) by (apply (denot_atom0 E 16 nn E16); lia).
assert (Dovv : sv_denot E (SOff 12 0) = Z_to_bv 64 ovv) by (apply (denot_atom0 E 12 ovv E12); lia).
assert (Dtok : sv_denot E (SOff 21 0) = Z_to_bv 64 tok) by (apply (denot_atom0 E 21 tok E21); lia).
assert (Dra : sv_denot E (SOff 240 15824) = Z_to_bv 64 (BASE + 15824))
  by (apply (denot_atomc E 240 BASE 15824 E240); lia).
assert (Drec : sv_denot E (SOff 9 120) = Z_to_bv 64 (A + 120))
  by (apply (denot_atomc E 9 A 120 E9); lia).
rreg_by HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15824)) Dra G1.
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (A + 120)) Drec G10.
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 i) Di G11.
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 1) D1 G12.
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 1) D1 G23.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 1; 10; 11; 12; 23])
  by (apply (rbn8_keep (w_H W) _ _ regs i o cap n ov _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64. rewrite pa_sigma_sb_dec. reflexivity. }
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
Lemma rbn8_p4 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
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
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + 15964) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn_keep_regs regs regs1 [0; 1; 10; 11; 12; 21] /\
       getr regs1 1 = w64 (BASE + 15992) /\ getr regs1 10 = w64 (A + 120) /\
       getr regs1 11 = w64 o /\ getr regs1 12 = w64 1 /\ getr regs1 21 = w64 1 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 136 <= a < A + 148) ->
          aview SEGS (w_H W) memc1 a = aview SEGS (w_H W) memc a) /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 128) 8 cap /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 136) 8 nn /\
       val_mem SEGS (mrestrict (w_H W) memc1) (A + 144) 4 ovv).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A i o cap n ov nn ovv
HJ H9 HAc HA32 HAlo HAhi Hsp0 H15 Rnn H12 Rovv Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (rbn8_entry fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A 15964 i o cap n ov
  HJ H9 HAc HA32 HAlo HAhi Hsp0 Mi Ri Mo Ro Mc Rc Mn Rn Mv Rv) as HS.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
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
assert (E240 : ew E 240 = Z_to_bv 64 BASE)
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
assert (D1 : sv_denot E (SLit 1) = Z_to_bv 64 1) by (apply denot_lit0; lia).
assert (Do : sv_denot E (SOff 33 0) = Z_to_bv 64 o) by (apply (denot_atom0 E 33 o E33); lia).
assert (Dcap : sv_denot E (SOff 34 0) = Z_to_bv 64 cap) by (apply (denot_atom0 E 34 cap E34); lia).
assert (Dnn : sv_denot E (SOff 15 0) = Z_to_bv 64 nn) by (apply (denot_atom0 E 15 nn E15); lia).
assert (Dovv : sv_denot E (SOff 12 0) = Z_to_bv 64 ovv) by (apply (denot_atom0 E 12 ovv E12); lia).
assert (Dra : sv_denot E (SOff 240 15992) = Z_to_bv 64 (BASE + 15992))
  by (apply (denot_atomc E 240 BASE 15992 E240); lia).
assert (Drec : sv_denot E (SOff 9 120) = Z_to_bv 64 (A + 120))
  by (apply (denot_atomc E 9 A 120 E9); lia).
rreg_by HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15992)) Dra G1.
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (A + 120)) Drec G10.
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 o) Do G11.
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 1) D1 G12.
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 1) D1 G21.
assert (HKP : rbn_keep_regs regs (ms_regs ms) [0; 1; 10; 11; 12; 21])
  by (apply (rbn8_keep (w_H W) _ _ regs i o cap n ov _ HS); vm_compute; reflexivity).
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64. rewrite pa_sigma_sb_dec. reflexivity. }
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
Lemma rbn8_pres_get : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn8_stack_ra : forall ly S (W : world SEGS) m md a len,
  AR SEGS B ly S W m md -> ly_stk_lo ly <= a -> a + len + 8 <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len.
Proof.
intros ly S W m md a len HAR H1 H2 H3 x Hx.
pose proof (al_zshadow _ _ LAWS ly S W m md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  (or_introl eq_refl)) as HZ.
unfold zero_shadow in HZ. cbn [fst snd] in HZ.
destruct (zshadow_range_facts B ly S (aview SEGS (w_H W) m)
  (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (proj1 HAR) (or_introl eq_refl))
  as (Hal8 & _ & _ & _ & _).
cbn [fst snd] in Hal8.
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)) as Dlo. rewrite Hal8, Z.add_0_r in Dlo.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Dh.
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Mh.
specialize (HZ (x / 8 - ly_stk_lo ly / 8) ltac:(lia)).
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr in HZ |- *.
replace (SHADOW_OFF + ly_stk_lo ly / 8 + (x / 8 - ly_stk_lo ly / 8)) with (SHADOW_OFF + x / 8) in HZ by lia.
exact HZ.
Qed.
Lemma rbn8_chain : forall X pos lyc1 Sc1 W1 m mdc1 sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  exists ch, achain lyc1 (aview SEGS (w_H W1) m) (rbn_A X) (rbn_SP X) ch.
Proof.
intros X pos lyc1 Sc1 W1 m mdc1 sh HX HM.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
destruct (rbn_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof HM as (HJ1 & _ & _ & _ & HK & Hfr & _).
pose proof HJ1 as (HAR1 & LY1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HX as (HJ0 & Hro0 & Hcv & Hrok & Hra4 & Hgp & Htp & Hch & Hal & Hstk & Hsp & Hfrl &
  Q10 & Rf & Q11 & Rsaid & Q12 & Rii & Q13 & Roo & Q14 & Rnm & Q15 & Rnml & Q16 & Rtk & Q17 & Rtkl &
  Md & Rd & Mdl & Rdl & Himg & Hargs).
pose proof HJ0 as (_ & LY0 & _).
destruct LY0 as (_ & _ & _ & _ & _ & _ & _ & _ & LT0 & _).
destruct LY1 as (_ & _ & _ & _ & _ & _ & _ & _ & LT1 & _).
destruct (Z_lt_le_dec (rbn_SP X) (ly_top lyc1 - 16)) as [Hlt | Hge].
- exists ((rbn_SP X, raZ (ri_regs X), s0Z (ri_regs X)) :: ri_ch X).
  assert (E1 : (Z_to_bv 5 1 : bv 5) = 1%bv) by (apply bv_eq; reflexivity).
  assert (E8 : (Z_to_bv 5 8 : bv 5) = 8%bv) by (apply bv_eq; reflexivity).
  pose proof (Hfr 0%nat 1 eq_refl) as Vra. pose proof (Hfr 1%nat 8 eq_refl) as Vs0.
  replace (rbn_SP X - 8 - 8 * Z.of_nat 0) with (rbn_SP X - 8) in Vra by lia.
  replace (rbn_SP X - 8 - 8 * Z.of_nat 1) with (rbn_SP X - 16) in Vs0 by lia.
  apply (achain_ly_top (ri_lyc X) lyc1); [rewrite LT1, LT0; reflexivity|].
  apply (achain_push (ri_lyc X) (aview SEGS (w_H (ri_W X)) (ri_memc X)) _ (rbn_SP X) (s0Z (ri_regs X))
    (raZ (ri_regs X)) (ri_ch X) (rbn_A X) Hch ltac:(lia)).
  + intros a Ha. apply (proj1 HK); [lia | lia | intros []].
  + apply (rdword_of_val_mem SEGS (w_H W1) m); [unfold raZ; rewrite <- E1; exact Vra|].
    unfold raZ. pose proof (bv_unsigned_in_range 64 (getr (ri_regs X) 1)) as Hq.
    change (bv_modulus 64) with (2 ^ 64) in Hq. exact Hq.
  + apply (rdword_of_val_mem SEGS (w_H W1) m); [unfold s0Z; rewrite <- E8; exact Vs0|].
    unfold s0Z. pose proof (bv_unsigned_in_range 64 (getr (ri_regs X) 8)) as Hq.
    change (bv_modulus 64) with (2 ^ 64) in Hq. exact Hq.
  + exact Hra4.
  + lia.
  + unfold rbn_SP. pose proof (Z.div_mod (spZ (ri_regs X)) 16 ltac:(lia)) as D16.
    rewrite Hal, Z.add_0_r in D16. rewrite D16.
    replace (16 * (spZ (ri_regs X) / 16)) with ((2 * (spZ (ri_regs X) / 16)) * 8) by lia.
    apply Z_mod_mult.
  + rewrite LT0, <- LT1. exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
Lemma rbn8_step_call : forall X pos lyc1 Sc1 (W W' : world SEGS) m mdc1 sh m' Arec (Er : Z -> Prop),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W m mdc1 (fun _ => False) sh ->
  rbn_A X - 4208 <= Arec -> Arec + 28 <= rbn_A X + 180 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - 4208 <= a < rbn_A X) ->
     ~ (Arec + 16 <= a < Arec + 28) -> ~ Er a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall b mm j, In (b, mm) (ablocks B lyc1 Sc1) -> 0 <= j < req_size mm ->
     ~ (Arec + 16 <= b + j < Arec + 28) -> ~ Er (b + j) ->
     aview SEGS (w_H W') m' (b + j) = aview SEGS (w_H W) m (b + j)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall cid p a, In (cid, p) (frames Sc1) ->
     (in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)) ->
     ~ (Arec + 16 <= a < Arec + 28) -> ~ Er a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  rbn8_step X lyc1 Sc1 W W' m m' Er.
Proof.
intros X pos lyc1 Sc1 W W' m mdc1 sh m' Arec Er HX HM Hlo Hhi D1 D2 D3 D4.
pose proof HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
destruct (rbn_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
split; [|split; [|split]].
- intros a Ha Hw He. apply D1; [exact Ha | lia | lia | exact He].
- intros b mm j Hb Hj He.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb) as (_ & Hb4 & Hbc & _).
  apply (D2 b mm j); [exact Hb | exact Hj | lia | exact He].
- intros a Hia Ho He. apply D3; assumption.
- intros cid p a Hcp Ha He.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp) as (Hc4096 & Hcceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
  apply (D4 cid p a); [exact Hcp | exact Ha | | exact He].
  destruct Ha as [Ha | Ha].
  + unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. lia.
  + unfold in_zr in Ha. cbn [fst snd] in Ha.
    pose proof (rbn_sh_band (frame_addr lyc1 cid p) (fs_frame_bytes cid)
      (a - shadow_addr (frame_addr lyc1 cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
    unfold kLowShadowBeg, kHighMemBeg in Hb. lia.
Qed.
Lemma rbn8_garr_keep : forall (W W' : world SEGS) (m m' : word -> option byte) base l,
  (forall a, base <= a < base + Z.of_nat (length l) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  garr8 SEGS (mrestrict (w_H W) m) base l -> garr8 SEGS (mrestrict (w_H W') m') base l.
Proof.
intros W W' m m' base l HE HG. apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact HG|].
intros a Ha. apply (mbyte_of_aview SEGS). exact (HE a Ha).
Qed.
Lemma rbn8_step_stack : forall X pos lyc1 Sc1 W1 mdc1 sh (m m' : word -> option byte) lo hi,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  rbn_A X - 4208 <= lo -> hi <= rbn_A X + 180 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
  rbn8_step X lyc1 Sc1 W1 W1 m m' (fun _ => False).
Proof.
intros X pos lyc1 Sc1 W1 mdc1 sh m m' lo hi HX HM Hlo Hhi HEQ.
pose proof HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
destruct (rbn_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
split; [|split; [|split]].
- intros a Ha Hw He. apply HEQ; lia.
- intros b mm j Hb Hj He.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb) as (_ & Hb4 & Hbc & _).
  apply HEQ; lia.
- intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  apply HEQ; lia.
- intros cid p a Hcp Ha He.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp) as (Hc4096 & Hcceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
  destruct Ha as [Ha | Ha].
  + unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. apply HEQ; lia.
  + unfold in_zr in Ha. cbn [fst snd] in Ha.
    pose proof (rbn_sh_band (frame_addr lyc1 cid p) (fs_frame_bytes cid)
      (a - shadow_addr (frame_addr lyc1 cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
    unfold kLowShadowBeg, kHighMemBeg in Hb. apply HEQ; lia.
Qed.
Hypothesis HSBDEC : tsb_dec_spec B.
Hypothesis L5F : rbn_L5_fits B.
Hypothesis L6F : rbn_L6_fits B.
Theorem rbn_seg8 : rbn_seg8_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H8.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
destruct (rbn_A_rng B X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6).
pose proof H8 as (HM & HRB & R18 & R27 & R24 & R25 & R20 & R26 & R21 & HC & G64 & G128 & G192 & HA).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
destruct (rbn_F_facts B LAWS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof HM as (HJ1 & Hfrs1 & Hperm1 & Hro1 & HK1 & Hfr1 & Hfl1 & Hshw1).
pose proof HJ1 as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HX as (HJ0 & Hro0 & Hcv & Hrok & Hra4 & Hgp & Htp & Hch & Hal & Hstk & Hsp & Hfrl &
  Q10 & Rf & Q11 & Rsaid & Q12 & Rii & Q13 & Roo & Q14 & Rnm & Q15 & Rnml & Q16 & Rtk & Q17 & Rtkl &
  Md & Rd & Mdl & Rdl & Himg & Hargs).
destruct Himg as (t1 & t2 & t3 & Hal26 & Himg26 & Hra26 & Mt1 & Mt2 & Mt3 & St1 & St2 & St3 & S0img &
  L28 & L29 & L30 & RO26 & ROt1 & ROt2 & ROt3 & RO27 & RO28 & RO29 & RO30).
pose proof HA as HAb. unfold rbm_args, reac_box_name_c.bn_args_ok in HAb.
apply andb_prop in HAb as (HAb & Hne0). apply andb_prop in HAb as (HAb & Hok_o).
apply andb_prop in HAb as (HAb & Hok_i).
pose proof (rbn8_ok_rng _ Hok_i) as Rig. pose proof (rbn8_ok_rng _ Hok_o) as Rog.
pose proof (rbn8_dec_len _ Hok_i) as Dil. pose proof (rbn8_dec_len _ Hok_o) as Dol.
pose proof (rbn8_dec_eq _ Hok_i) as Die. pose proof (rbn8_dec_eq _ Hok_o) as Doe.
assert (Hnb23 : (length (rbm_NB X) <= 23)%nat) by (unfold rbm_NB; apply firstn_le_length).
pose proof (rbn_NB_ne X) as Hnb1.
unfold rbn_locs6, rbn_locs4, rbn_rec2 in HC. cbn [app rbn_cells] in HC.
destruct HC as (C8 & C16 & C32 & C56 & C64c & C80 & C88 & C152 & C160 & C168 & C176 &
  C24 & C48 & C72 & C120 & C128 & C136 & C144 & _).
assert (Emin : Z.min (Z.of_nat (length (rbm_NB X))) 47 = Z.of_nat (length (rbm_NB X))) by lia.
assert (Eovf : rbm_ovf 47 (rbm_NB X) = 0).
{ unfold rbm_ovf.
  replace (47 <? Z.of_nat (length (rbm_NB X))) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite Emin in C136. rewrite Eovf in C144.
assert (HA32 : rbn_A X mod 32 = 0) by (unfold rbn_A; rewrite Z.mul_comm; apply Z_mod_mult).
assert (HAc : alloc_ceiling <= rbn_A X) by lia.
assert (HAlo : ri_sp0 X - ri_STK X <= rbn_A X) by lia.
assert (HAhi : rbn_A X + 180 <= ri_sp0 X) by lia.
assert (Hsp047 : ri_sp0 X <= 2 ^ 47) by lia.
assert (HFlt : rbn_F X pos + 512 <= rbn_A X - 4208) by lia.
assert (HV28 : VAL (A_OBJ 28) = 135744) by (rewrite (pa_obj_val 28 ltac:(unfold disco_nobj; lia)); reflexivity).
assert (HV29 : VAL (A_OBJ 29) = 135776) by (rewrite (pa_obj_val 29 ltac:(unfold disco_nobj; lia)); reflexivity).
assert (SEPF : forall q n, (forall x, q <= x < q + n -> in_img SEGS x) -> 0 < n ->
  q + n <= rbn_F X pos + 192 \/ rbn_F X pos + 192 + 48 <= q).
{ intros q n Hq Hn. apply (rbn8_sep (in_img SEGS) q n (rbn_F X pos + 192) 48 Hn ltac:(lia) Hq).
  intros x Hx. exact (proj2 (HFpr x ltac:(lia))). }
assert (SEP5 : VAL (A_OBJ 28) + 3 <= rbn_F X pos + 192 \/ rbn_F X pos + 192 + 48 <= VAL (A_OBJ 28)).
{ apply SEPF; [|lia]. intros x Hx. apply (proj2 (proj2 L28)). cbn [length]. lia. }
assert (SEP6 : VAL (A_OBJ 29) + 7 <= rbn_F X pos + 192 \/ rbn_F X pos + 192 + 48 <= VAL (A_OBJ 29)).
{ apply SEPF; [|lia]. intros x Hx. apply (proj2 (proj2 L29)). cbn [length]. lia. }
assert (LSRC : forall (W : world SEGS) (ly : alayout) (S : astate) (m : word -> option byte) (md : Model),
  AR SEGS B ly S W m md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  rbn_lsrc W m (VAL (A_OBJ 28)) (rbn_lit5 ++ [0]) /\ rbn_lsrc W m (VAL (A_OBJ 29)) (rbn_lit6 ++ [0])).
{ intros W ly S m md HARx Hrox. split.
  - exact (rbn8_lsrc_of ly S W (ri_W X) m (ri_memc X) md (VAL (A_OBJ 28)) 3 (rbn_lit5 ++ [0]) HARx RO28
      eq_refl ltac:(lia) Hrox Hro0 (proj1 L28)).
  - exact (rbn8_lsrc_of ly S W (ri_W X) m (ri_memc X) md (VAL (A_OBJ 29)) 7 (rbn_lit6 ++ [0]) HARx RO29
      eq_refl ltac:(lia) Hrox Hro0 (proj1 L29)). }
unfold rbn_cfg.
eapply SRr_bind.
{ exact (rbn8_p1 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) regs1 (rbn_A X) (ri_i X) (ri_o X) 48
    (Z.of_nat (length (rbm_NB X))) 0 HJ1 B9 HAc HA32 HAlo HAhi Hsp047
    C80 ltac:(lia) C88 ltac:(lia) C128 ltac:(lia) C136 ltac:(lia) C144 ltac:(lia)). }
intros Wa ca Hlea (-> & regs2 & memc2 & mdc2 & -> & HJ2 & HP2 & P11 & P12 & P13 & P14 & P15 & P16 & P17 &
  KEQ2 & M128a & M136a & M144a).
assert (HM2 : rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 W1 memc1 mdc1 memc2 mdc2 _ (fun _ => False)
    HX HM HJ2 eq_refl (Permutation_refl _)
    (rbn8_step_stack X pos lyc1 Sc1 W1 mdc1 _ memc1 memc2 (rbn_A X + 136) (rbn_A X + 148) HX HM
       ltac:(lia) ltac:(lia) KEQ2)
    ltac:(intros a []) ltac:(rewrite rbn_sh_len; lia)). }
pose proof HM2 as (HJ2b & Hfrs2 & Hperm2 & Hro2 & HK2 & Hfr2 & Hfl2 & Hshw2).
destruct (LSRC W1 lyc1 Sc1 memc2 mdc2 (proj1 HJ2) Hro2) as (LS5a & LS6a).
pose proof (rbn_lbuf_fr B LAWS X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) (rbn_sh true true true true) 24 6
  HX HM2 ltac:(lia) ltac:(lia) ltac:(rewrite rbn_sh_len; lia) ltac:(lia)
  ltac:(intros ii Hii; apply rbn8_sh_db; lia)) as LB2.
replace (rbn_F X pos + 8 * 24) with (rbn_F X pos + 192) in LB2 by lia.
replace (8 * 6) with 48 in LB2 by lia.
pose proof (L5F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc2 mdc2 (ri_k X) regs2 (rbn_F X pos + 192)
  (Z.of_nat (length (rbm_NB X))) 0 ltac:(lia)) as R5.
unfold rbn_L5_run in R5.
eapply SRr_bind.
{ apply R5; clear R5.
  - exact HJ2.
  - exact LS5a.
  - rewrite HV28. reflexivity.
  - exact LB2.
  - exact SEP5.
  - lia.
  - left; reflexivity.
  - exact P16.
  - exact P12.
  - exact P17.
  - exact P11.
  - exact P15.
  - exact P13.
  - exact P14.
  - assert (G20 : getr regs2 (20%bv : bv 5) = getr regs1 (20%bv : bv 5))
      by (apply (rbn8_pres_get regs1 regs2 (20%bv : bv 5) HP2);
          change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia).
    rewrite G20. exact R20.
  - assert (G22 : getr regs2 (22%bv : bv 5) = getr regs1 (22%bv : bv 5))
      by (apply (rbn8_pres_get regs1 regs2 (22%bv : bv 5) HP2);
          change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia).
    rewrite G22. exact B22. }
intros Wb cb Hleb (-> & regs3 & memc3 & mdc3 & -> & HJ3 & HK3 & HO3 & HEQ3 & HG3).
assert (HM3 : rbn_mid B X pos lyc1 Sc1 W1 memc3 mdc3 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 W1 memc2 mdc2 memc3 mdc3 _
    (fun a => rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) <= a <
              rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + Z.of_nat (length rbn_lit5))
    HX HM2 HJ3 eq_refl (Permutation_refl _)
    (rbn8_step_glob X pos lyc1 Sc1 W1 mdc2 (rbn_sh true true true true) memc2 memc3
       (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)))
       (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + Z.of_nat (length rbn_lit5)) HX HM2
       ltac:(intros a Ha; unfold rbn_lit5 in Ha; cbn [length] in Ha;
             exact (proj2 (HFpr a ltac:(lia)))) HEQ3)
    ltac:(unfold rbn_lit5; cbn [length]; intros a Ha; lia) ltac:(rewrite rbn_sh_len; lia)). }
assert (TR2 : forall a nn vv, rbn_A X + 8 <= a -> a + Z.of_nat nn <= rbn_A X + 136 ->
  val_mem SEGS (mrestrict (w_H W1) memc1) a nn vv -> val_mem SEGS (mrestrict (w_H W1) memc2) a nn vv).
{ intros a nn vv H1 H2 HV. apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [|exact HV].
  intros kk Hk. apply KEQ2; [lia | lia]. }
assert (TR3 : forall a nn vv, rbn_A X + 8 <= a -> a + Z.of_nat nn <= rbn_A X + 180 ->
  val_mem SEGS (mrestrict (w_H W1) memc2) a nn vv -> val_mem SEGS (mrestrict (w_H W1) memc3) a nn vv).
{ intros a nn vv H1 H2 HV. apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc2 memc3); [|exact HV].
  intros kk Hk. apply HEQ3; [lia|]. unfold rbn_lit5. cbn [length]. lia. }
assert (KEEP3 : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [5; 6; 10; 11; 12; 16; 17] = false ->
  acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs1 r).
{ intros r Hc Hs. rewrite (rbn_keep_get regs2 regs3 _ r HK3 Hc). exact (rbn8_pres_get regs1 regs2 r HP2 Hs). }
assert (G9c : getr regs3 (9%bv : bv 5) = w64 (rbn_A X))
  by (rewrite (KEEP3 (9%bv : bv 5) ltac:(vm_compute; reflexivity)
        ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)); exact B9).
assert (G21c : getr regs3 (21%bv : bv 5) = w64 (rbm_tok X))
  by (rewrite (KEEP3 (21%bv : bv 5) ltac:(vm_compute; reflexivity)
        ltac:(change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia)); exact R21).
pose proof (Forall_inv HO3) as O16. pose proof (Forall_inv (Forall_inv_tail HO3)) as O12.
cbn [fst snd] in O16, O12.
assert (G16c : getr regs3 (16%bv : bv 5) = w64 (Z.of_nat (length (rbm_NB X)) + 2))
  by (apply rbn_out_get; exact O16).
assert (G12c : getr regs3 (12%bv : bv 5) = w64 0) by (apply rbn_out_get; exact O12).
assert (Rtok : 0 <= rbm_tok X < 2 ^ 64).
{ unfold rbm_tok, rbm_ovf. destruct (23 <? Z.of_nat (length (bn_TK (rbm_NB X)))); lia. }
replace (BASE + AF_reac_box_name + RBN_L5X) with (BASE + 15792) by (unfold AF_reac_box_name, RBN_L5X; lia).
eapply SRr_bind.
{ exact (rbn8_p2 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc3 mdc3 (ri_k X) regs3 (rbn_A X) (ri_i X) (ri_o X) 48
    (Z.of_nat (length (rbm_NB X))) 0 (rbm_tok X) (Z.of_nat (length (rbm_NB X)) + 2) 0
    HJ3 G9c HAc HA32 HAlo HAhi Hsp047 G21c Rtok G16c ltac:(lia) G12c ltac:(lia)
    (TR3 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
       (TR2 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia) C80)) ltac:(lia)
    (TR3 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
       (TR2 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia) C88)) ltac:(lia)
    (TR3 (rbn_A X + 128) 8%nat 48 ltac:(lia) ltac:(lia) M128a) ltac:(lia)
    (TR3 (rbn_A X + 136) 8%nat (Z.of_nat (length (rbm_NB X))) ltac:(lia) ltac:(lia) M136a) ltac:(lia)
    (TR3 (rbn_A X + 144) 4%nat 0 ltac:(lia) ltac:(lia) M144a) ltac:(lia)). }
intros Wc cc Hlec (-> & regs4 & memc4 & mdc4 & -> & HJ4 & HK4 & Q1 & Q10r & Q11r & Q12r & Q23r &
  KEQ4 & M40 & M128c & M136c & M144c).
assert (HM4 : rbn_mid B X pos lyc1 Sc1 W1 memc4 mdc4 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 W1 memc3 mdc3 memc4 mdc4 _ (fun _ => False)
    HX HM3 HJ4 eq_refl (Permutation_refl _)
    (rbn8_step_stack X pos lyc1 Sc1 W1 mdc3 _ memc3 memc4 (rbn_A X + 40) (rbn_A X + 148) HX HM3
       ltac:(lia) ltac:(lia) ltac:(intros a Ha Hn; apply KEQ4; [exact Ha | lia | lia]))
    ltac:(intros a []) ltac:(rewrite rbn_sh_len; lia)). }
pose proof HJ1 as (_ & LYc1 & _).
destruct LYc1 as (_ & _ & _ & _ & _ & _ & _ & _ & LTc & LSLO & LSHI & _).
assert (TR4 : forall a nn vv, rbn_A X + 48 <= a -> a + Z.of_nat nn <= rbn_A X + 136 ->
  val_mem SEGS (mrestrict (w_H W1) memc3) a nn vv -> val_mem SEGS (mrestrict (w_H W1) memc4) a nn vv).
{ intros a nn vv H1 H2 HV. apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc3 memc4); [|exact HV].
  intros kk Hk. apply KEQ4; [lia | lia | lia]. }
assert (KEEP4 : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [0; 1; 10; 11; 12; 23] = false ->
  existsb (Z.eqb (bv_unsigned r)) [5; 6; 10; 11; 12; 16; 17] = false ->
  acallee_saved (bv_unsigned r) -> getr regs4 r = getr regs1 r).
{ intros r Hc4 Hc3 Hs. rewrite (rbn_keep_get regs3 regs4 _ r HK4 Hc4). exact (KEEP3 r Hc3 Hs). }
assert (G2d : getr regs4 (2%bv : bv 5) = w64 (rbn_A X))
  by (rewrite (KEEP4 (2%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)); exact B2).
assert (G8d : getr regs4 (8%bv : bv 5) = w64 (rbn_SP X))
  by (rewrite (KEEP4 (8%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)); exact B8).
assert (Hspd : spZ regs4 = rbn_A X) by (unfold spZ; rewrite G2d; apply unsigned_lit_small; lia).
assert (Hs0d : s0Z regs4 = rbn_SP X) by (unfold s0Z; rewrite G8d; apply unsigned_lit_small; lia).
destruct (rbn8_chain X pos lyc1 Sc1 W1 memc4 mdc4 _ HX HM4) as (ch1 & HCH1).
pose proof (rbn_lbuf_fr B LAWS X pos lyc1 Sc1 W1 memc4 mdc4 (fun _ => False) (rbn_sh true true true true) 24 6
  HX HM4 ltac:(lia) ltac:(lia) ltac:(rewrite rbn_sh_len; lia) ltac:(lia)
  ltac:(intros ii Hii; apply rbn8_sh_db; lia)) as LB4.
replace (rbn_F X pos + 8 * 24) with (rbn_F X pos + 192) in LB4 by lia.
replace (8 * 6) with 48 in LB4 by lia.
destruct LB4 as (LB4a & LB4b & LB4c & LB4d & LB4e).
pose proof HM4 as (HJ4b & Hfrs4 & Hperm4 & Hro4 & HK4m & Hfr4 & Hfl4 & Hshw4).
pose proof HJ4 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
pose proof (frm_off_imgP B lyc1 Sc1 W1 memc4 mdc4 3 pos HAR4 ltac:(rewrite Hfrs4; left; reflexivity)) as HFoi.
pose proof (rbn_fa B X pos lyc1 Sc1 W1 memc4 mdc4 _ _ HX HM4) as FA4.
rewrite FA4 in HFoi. change (fs_frame_bytes 3) with 512 in HFoi. unfold off_img in HFoi.
change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos) in HFoi.
destruct (rbn8_sbd (ri_i X) (Z.of_nat (length (rbm_NB X)) + 2) ltac:(lia) ltac:(rewrite Die; lia))
  as (Hrm1 & Hacc1 & Hovf1).
eapply SRr_bind.
{ apply (HSBDEC (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc4 mdc4 (ri_k X) regs4 ch1 (rbn_A X + 120) (ri_i X) 1
    (rbn_F X pos + 192) 48 (Z.of_nat (length (rbm_NB X)) + 2) 0).
  - exact HJ4.
  - exact Hro4.
  - rewrite Q1. unfold w64. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite (KEEP4 (3%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)). exact B3.
  - rewrite (KEEP4 (4%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)). exact B4.
  - exact Q10r.
  - exact Q11r.
  - exact Q12r.
  - rewrite Hspd, Hs0d. exact HCH1.
  - rewrite Hspd. pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D32.
    rewrite HA32, Z.add_0_r in D32.
    replace (rbn_A X) with ((2 * (rbn_A X / 32)) * 16) by lia. apply Z_mod_mult.
  - rewrite Hspd. assert (SBK : SB_DEC_STK = 4208) by reflexivity. lia.
  - rewrite Hspd. lia.
  - rewrite Hfrs4. cbn [length]. lia.
  - lia.
  - left; reflexivity.
  - pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D32. rewrite HA32, Z.add_0_r in D32.
    replace (rbn_A X + 120) with ((4 * (rbn_A X / 32) + 15) * 8) by lia. apply Z_mod_mult.
  - right. lia.
  - lia.
  - right. unfold IMG_TOP. lia.
  - left. rewrite Hspd. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact (TR4 (rbn_A X + 120) 8%nat (rbn_F X pos + 192) ltac:(lia) ltac:(lia)
            (TR3 (rbn_A X + 120) 8%nat (rbn_F X pos + 192) ltac:(lia) ltac:(lia)
              (TR2 (rbn_A X + 120) 8%nat (rbn_F X pos + 192) ltac:(lia) ltac:(lia) C120))).
  - replace (rbn_A X + 120 + 8) with (rbn_A X + 128) by lia. exact M128c.
  - replace (rbn_A X + 120 + 16) with (rbn_A X + 136) by lia. exact M136c.
  - replace (rbn_A X + 120 + 24) with (rbn_A X + 144) by lia. exact M144c.
  - apply (rbn8_stack_ra lyc1 Sc1 W1 memc4 mdc4); [exact HAR4 | lia | lia | lia].
  - intros a Ha. apply Hpres4. lia.
  - intros a Ha. left. lia.
  - intros Hroom. rewrite Hacc1, Die.
    split; [lia|]. split.
    { apply (in_app_sub (rbn_F X pos) 512); [exact HFapp | lia | lia | lia]. }
    split; [destruct HFoi as [Hoi | Hoi]; [left | right]; clear - Hoi Hnb23 Dil;
            try unfold IMG_LO in *; try unfold IMG_TOP in *; lia|].
    split; [left; lia|].
    split; [rewrite Hspd; right; assert (SBK : SB_DEC_STK = 4208) by reflexivity; lia|].
    split.
    { apply (range_addressable_sub (aview SEGS (w_H W1) memc4) SHADOW_OFF (rbn_F X pos + 192) 48);
      [exact LB4d | lia | lia]. }
    intros a Ha. apply LB4e. lia. }
intros Wd cd Hled (ly5 & S5 & regs5 & memc5 & mdc5 & -> & HJ5 & HP5 & Hfrs5 & Hperm5 &
  KB1 & KB2 & KB3 & KB4 & KB5 & KB6 & V120 & V128 & V136 & V144 & VG).
assert (SBK : SB_DEC_STK = 4208) by reflexivity.
rewrite Hspd, SBK in KB1. rewrite Hspd in KB5.
rewrite Hacc1 in KB1, KB2, KB4, V136, VG. rewrite Hovf1 in V144.
assert (HM5 : rbn_mid B X pos ly5 S5 Wd memc5 mdc5 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos lyc1 Sc1 ly5 S5 W1 Wd memc4 mdc4 memc5 mdc5 _
    (fun a => 0 < sb_dec_c.sb_dec_room 48 (Z.of_nat (length (rbm_NB X)) + 2) /\
       rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2) <= a <
       rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2) +
         Z.of_nat (length (sb_dec_c.sb_dec_D (ri_i X) 1)))
    HX HM4 HJ5 Hfrs5 Hperm5); [| | rewrite rbn_sh_len; lia].
  - apply (rbn8_step_call X pos lyc1 Sc1 W1 Wd memc4 mdc4 (rbn_sh true true true true) memc5
      (rbn_A X + 120) _ HX HM4 ltac:(lia) ltac:(lia) KB1 KB2 KB3 KB4).
  - intros a (Hr & Hd). rewrite Die in Hd. lia. }
rewrite Q1. unfold w64.
assert (KEEP5 : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [0; 1; 10; 11; 12; 23] = false ->
  existsb (Z.eqb (bv_unsigned r)) [5; 6; 10; 11; 12; 16; 17] = false ->
  acallee_saved (bv_unsigned r) -> getr regs5 r = getr regs1 r).
{ intros r Hc4 Hc3 Hs. rewrite (rbn8_pres_get regs4 regs5 r HP5 Hs). exact (KEEP4 r Hc4 Hc3 Hs). }
assert (G9e : getr regs5 (9%bv : bv 5) = w64 (rbn_A X))
  by (rewrite (KEEP5 (9%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)); exact B9).
assert (TR5 : forall a nn vv, rbn_A X + 8 <= a -> a + Z.of_nat nn <= rbn_A X + 136 ->
  val_mem SEGS (mrestrict (w_H W1) memc4) a nn vv -> val_mem SEGS (mrestrict (w_H Wd) memc5) a nn vv).
{ intros a nn vv H1 H2 HV. apply (val_mem_kept SEGS (w_H W1) (w_H Wd) memc4 memc5); [|exact HV].
  intros kk Hk. apply KB1; [lia | lia | lia | intros (Hr & Hd); rewrite Die in Hd; lia]. }
replace (BASE + 15824) with (BASE + 15824) by reflexivity.
eapply SRr_bind.
{ exact (rbn8_p3 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) ly5 S5 Wd memc5 mdc5 (ri_k X) regs5 (rbn_A X) (ri_i X) (ri_o X) 48
    (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1))) 0
    HJ5 G9e HAc HA32 HAlo HAhi Hsp047
    (TR5 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
       (TR4 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
         (TR3 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
           (TR2 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia) C80)))) ltac:(lia)
    (TR5 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
       (TR4 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
         (TR3 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
           (TR2 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia) C88)))) ltac:(lia)
    ltac:(replace (rbn_A X + 128) with (rbn_A X + 120 + 8) by lia; exact V128) ltac:(lia)
    ltac:(replace (rbn_A X + 136) with (rbn_A X + 120 + 16) by lia; rewrite Die in V136; exact V136)
    ltac:(lia)
    ltac:(replace (rbn_A X + 144) with (rbn_A X + 120 + 24) by lia; exact V144) ltac:(lia)). }
intros We ce Hlee (-> & regs6 & memc6 & mdc6 & -> & HJ6 & HP6 & S11 & S12 & S13 & S14 & S15 & S16 &
  KEQ6 & N128 & N136 & N144).
assert (HM6 : rbn_mid B X pos ly5 S5 Wd memc6 mdc6 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos ly5 S5 ly5 S5 Wd Wd memc5 mdc5 memc6 mdc6 _ (fun _ => False)
    HX HM5 HJ6 eq_refl (Permutation_refl _)
    (rbn8_step_stack X pos ly5 S5 Wd mdc5 _ memc5 memc6 (rbn_A X + 136) (rbn_A X + 148) HX HM5
       ltac:(lia) ltac:(lia) KEQ6)
    ltac:(intros a []) ltac:(rewrite rbn_sh_len; lia)). }
pose proof HM6 as (HJ6b & Hfrs6 & Hperm6 & Hro6 & HK6 & Hfr6 & Hfl6 & Hshw6).
destruct (LSRC Wd ly5 S5 memc6 mdc6 (proj1 HJ6) Hro6) as (LS5d & LS6d).
pose proof (rbn_lbuf_fr B LAWS X pos ly5 S5 Wd memc6 mdc6 (fun _ => False) (rbn_sh true true true true) 24 6
  HX HM6 ltac:(lia) ltac:(lia) ltac:(rewrite rbn_sh_len; lia) ltac:(lia)
  ltac:(intros ii Hii; apply rbn8_sh_db; lia)) as LB6.
replace (rbn_F X pos + 8 * 24) with (rbn_F X pos + 192) in LB6 by lia.
replace (8 * 6) with 48 in LB6 by lia.
assert (TR6 : forall a nn vv, rbn_A X + 8 <= a -> a + Z.of_nat nn <= rbn_A X + 136 ->
  val_mem SEGS (mrestrict (w_H Wd) memc5) a nn vv -> val_mem SEGS (mrestrict (w_H Wd) memc6) a nn vv).
{ intros a nn vv H1 H2 HV. apply (val_mem_kept SEGS (w_H Wd) (w_H Wd) memc5 memc6); [|exact HV].
  intros kk Hk. apply KEQ6; [lia | lia]. }
assert (G23e : getr regs5 (23%bv : bv 5) = w64 1)
  by (rewrite (rbn8_pres_get regs4 regs5 (23%bv : bv 5) HP5
        ltac:(change (bv_unsigned (23%bv : bv 5)) with 23; unfold acallee_saved; lia)); exact Q23r).
assert (G23f : getr regs6 (23%bv : bv 5) = w64 1)
  by (rewrite (rbn8_pres_get regs5 regs6 (23%bv : bv 5) HP6
        ltac:(change (bv_unsigned (23%bv : bv 5)) with 23; unfold acallee_saved; lia)); exact G23e).
assert (G9f : getr regs6 (9%bv : bv 5) = w64 (rbn_A X))
  by (rewrite (rbn8_pres_get regs5 regs6 (9%bv : bv 5) HP6
        ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)); exact G9e).
assert (G22f : getr regs6 (22%bv : bv 5) = w64 SHADOW_OFF).
{ rewrite (rbn8_pres_get regs5 regs6 (22%bv : bv 5) HP6
    ltac:(change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia)).
  rewrite (KEEP5 (22%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia)). exact B22. }
pose proof (L6F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) ly5 S5 Wd memc6 mdc6 (ri_k X) regs6 (rbn_A X) (rbn_F X pos + 192)
  (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1))) 0 ltac:(lia)) as R6.
unfold rbn_L6_run in R6.
eapply SRr_bind.
{ apply R6; clear R6.
  - exact HJ6.
  - exact LS6d.
  - rewrite HV29. reflexivity.
  - lia.
  - lia.
  - right. lia.
  - exact LB6.
  - exact SEP6.
  - exact (TR6 (rbn_A X + 120) 8%nat (rbn_F X pos + 192) ltac:(lia) ltac:(lia) V120).
  - right. lia.
  - lia.
  - left; reflexivity.
  - exact S15.
  - exact S12.
  - exact S16.
  - exact G23f.
  - exact S14.
  - exact S11.
  - exact S13.
  - exact G9f.
  - exact G22f. }
intros Wf cf Hlef (-> & regs7 & memc7 & mdc7 & -> & HJ7 & HK7 & HO7 & HEQ7 & HG7).
assert (HM7 : rbn_mid B X pos ly5 S5 Wd memc7 mdc7 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos ly5 S5 ly5 S5 Wd Wd memc6 mdc6 memc7 mdc7 _
    (fun a => rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)))
       <= a < rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)))
              + Z.of_nat (length rbn_lit6))
    HX HM6 HJ7 eq_refl (Permutation_refl _)
    (rbn8_step_glob X pos ly5 S5 Wd mdc6 (rbn_sh true true true true) memc6 memc7
       (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1))))
       (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)))
          + Z.of_nat (length rbn_lit6)) HX HM6
       ltac:(intros a Ha; unfold rbn_lit6 in Ha; cbn [length] in Ha;
             exact (proj2 (HFpr a ltac:(lia)))) HEQ7)
    ltac:(unfold rbn_lit6; cbn [length]; intros a Ha; lia) ltac:(rewrite rbn_sh_len; lia)). }
pose proof (Forall_inv HO7) as O15. pose proof (Forall_inv (Forall_inv_tail HO7)) as O12b.
cbn [fst snd] in O15, O12b.
assert (G15g : getr regs7 (15%bv : bv 5) =
  w64 (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6))
  by (apply rbn_out_get; exact O15).
assert (G12g : getr regs7 (12%bv : bv 5) = w64 0) by (apply rbn_out_get; exact O12b).
assert (G9g : getr regs7 (9%bv : bv 5) = w64 (rbn_A X))
  by (rewrite (rbn_keep_get regs6 regs7 _ (9%bv : bv 5) HK7 ltac:(vm_compute; reflexivity)); exact G9f).
assert (TR7 : forall a nn vv, rbn_A X + 8 <= a -> a + Z.of_nat nn <= rbn_A X + 180 ->
  val_mem SEGS (mrestrict (w_H Wd) memc6) a nn vv -> val_mem SEGS (mrestrict (w_H Wd) memc7) a nn vv).
{ intros a nn vv H1 H2 HV. apply (val_mem_kept SEGS (w_H Wd) (w_H Wd) memc6 memc7); [|exact HV].
  intros kk Hk. apply HEQ7; [lia|]. unfold rbn_lit6. cbn [length]. lia. }
replace (BASE + AF_reac_box_name + RBN_L6X) with (BASE + 15964) by (unfold AF_reac_box_name, RBN_L6X; lia).
eapply SRr_bind.
{ exact (rbn8_p4 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) ly5 S5 Wd memc7 mdc7 (ri_k X) regs7 (rbn_A X) (ri_i X) (ri_o X) 48
    (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1))) 0
    (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6) 0
    HJ7 G9g HAc HA32 HAlo HAhi Hsp047 G15g ltac:(lia) G12g ltac:(lia)
    (TR7 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
       (TR6 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
         (TR5 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
           (TR4 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
             (TR3 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia)
               (TR2 (rbn_A X + 80) 8%nat (ri_i X) ltac:(lia) ltac:(lia) C80)))))) ltac:(lia)
    (TR7 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
       (TR6 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
         (TR5 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
           (TR4 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
             (TR3 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia)
               (TR2 (rbn_A X + 88) 8%nat (ri_o X) ltac:(lia) ltac:(lia) C88)))))) ltac:(lia)
    (TR7 (rbn_A X + 128) 8%nat 48 ltac:(lia) ltac:(lia) N128) ltac:(lia)
    (TR7 (rbn_A X + 136) 8%nat
       (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)))
       ltac:(lia) ltac:(lia) N136) ltac:(lia)
    (TR7 (rbn_A X + 144) 4%nat 0 ltac:(lia) ltac:(lia) N144) ltac:(lia)). }
intros Wg cg Hleg (-> & regs8 & memc8 & mdc8 & -> & HJ8 & HK8 & T1r & T10r & T11r & T12r & T21r &
  KEQ8 & P128 & P136 & P144).
assert (HM8 : rbn_mid B X pos ly5 S5 Wd memc8 mdc8 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos ly5 S5 ly5 S5 Wd Wd memc7 mdc7 memc8 mdc8 _ (fun _ => False)
    HX HM7 HJ8 eq_refl (Permutation_refl _)
    (rbn8_step_stack X pos ly5 S5 Wd mdc7 _ memc7 memc8 (rbn_A X + 136) (rbn_A X + 148) HX HM7
       ltac:(lia) ltac:(lia) KEQ8)
    ltac:(intros a []) ltac:(rewrite rbn_sh_len; lia)). }
pose proof HM8 as (HJ8b & Hfrs8 & Hperm8 & Hro8 & HK8m & Hfr8 & Hfl8 & Hshw8).
pose proof HJ8 as (HAR8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres8 & _).
destruct (rbn8_chain X pos ly5 S5 Wd memc8 mdc8 _ HX HM8) as (ch2 & HCH2).
pose proof (rbn_lbuf_fr B LAWS X pos ly5 S5 Wd memc8 mdc8 (fun _ => False) (rbn_sh true true true true) 24 6
  HX HM8 ltac:(lia) ltac:(lia) ltac:(rewrite rbn_sh_len; lia) ltac:(lia)
  ltac:(intros ii Hii; apply rbn8_sh_db; lia)) as LB8.
replace (rbn_F X pos + 8 * 24) with (rbn_F X pos + 192) in LB8 by lia.
replace (8 * 6) with 48 in LB8 by lia.
destruct LB8 as (LB8a & LB8b & LB8c & LB8d & LB8e).
pose proof (frm_off_imgP B ly5 S5 Wd memc8 mdc8 3 pos HAR8 ltac:(rewrite Hfrs8; left; reflexivity)) as HFoi2.
pose proof (rbn_fa B X pos ly5 S5 Wd memc8 mdc8 _ _ HX HM8) as FA8.
rewrite FA8 in HFoi2. change (fs_frame_bytes 3) with 512 in HFoi2. unfold off_img in HFoi2.
change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos) in HFoi2.
assert (KEEPA : forall r : bv 5,
  existsb (Z.eqb (bv_unsigned r)) [0; 1; 10; 11; 12; 21] = false ->
  existsb (Z.eqb (bv_unsigned r)) [5; 10; 12; 15; 16; 17; 23] = false ->
  existsb (Z.eqb (bv_unsigned r)) [0; 1; 10; 11; 12; 23] = false ->
  existsb (Z.eqb (bv_unsigned r)) [5; 6; 10; 11; 12; 16; 17] = false ->
  acallee_saved (bv_unsigned r) -> getr regs8 r = getr regs1 r).
{ intros r Ha Hb Hc Hd Hs.
  rewrite (rbn_keep_get regs7 regs8 _ r HK8 Ha), (rbn_keep_get regs6 regs7 _ r HK7 Hb),
    (rbn8_pres_get regs5 regs6 r HP6 Hs). exact (KEEP5 r Hc Hd Hs). }
assert (G2h : getr regs8 (2%bv : bv 5) = w64 (rbn_A X))
  by (rewrite (KEEPA (2%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)); exact B2).
assert (G8h : getr regs8 (8%bv : bv 5) = w64 (rbn_SP X))
  by (rewrite (KEEPA (8%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)); exact B8).
assert (Hsph : spZ regs8 = rbn_A X) by (unfold spZ; rewrite G2h; apply unsigned_lit_small; lia).
assert (Hs0h : s0Z regs8 = rbn_SP X) by (unfold s0Z; rewrite G8h; apply unsigned_lit_small; lia).
assert (TR8 : forall a nn vv, rbn_A X + 8 <= a -> a + Z.of_nat nn <= rbn_A X + 136 ->
  val_mem SEGS (mrestrict (w_H Wd) memc7) a nn vv -> val_mem SEGS (mrestrict (w_H Wd) memc8) a nn vv).
{ intros a nn vv H1 H2 HV. apply (val_mem_kept SEGS (w_H Wd) (w_H Wd) memc7 memc8); [|exact HV].
  intros kk Hk. apply KEQ8; [lia | lia]. }
destruct (rbn8_sbd (ri_o X)
  (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6)
  ltac:(lia) ltac:(rewrite Doe; lia)) as (Hrm2 & Hacc2 & Hovf2).
eapply SRr_bind.
{ apply (HSBDEC (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) ly5 S5 Wd memc8 mdc8 (ri_k X) regs8 ch2 (rbn_A X + 120) (ri_o X) 1
    (rbn_F X pos + 192) 48
    (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6) 0).
  - exact HJ8.
  - exact Hro8.
  - rewrite T1r. unfold w64. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite T1r. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite (KEEPA (3%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)). exact B3.
  - rewrite (KEEPA (4%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)). exact B4.
  - exact T10r.
  - exact T11r.
  - exact T12r.
  - rewrite Hsph, Hs0h. exact HCH2.
  - rewrite Hsph. pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D32.
    rewrite HA32, Z.add_0_r in D32.
    replace (rbn_A X) with ((2 * (rbn_A X / 32)) * 16) by lia. apply Z_mod_mult.
  - rewrite Hsph. lia.
  - rewrite Hsph. lia.
  - rewrite Hfrs8. cbn [length]. lia.
  - lia.
  - left; reflexivity.
  - pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D32. rewrite HA32, Z.add_0_r in D32.
    replace (rbn_A X + 120) with ((4 * (rbn_A X / 32) + 15) * 8) by lia. apply Z_mod_mult.
  - right. lia.
  - lia.
  - right. unfold IMG_TOP. lia.
  - left. rewrite Hsph. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact (TR8 (rbn_A X + 120) 8%nat (rbn_F X pos + 192) ltac:(lia) ltac:(lia)
            (TR7 (rbn_A X + 120) 8%nat (rbn_F X pos + 192) ltac:(lia) ltac:(lia)
              (TR6 (rbn_A X + 120) 8%nat (rbn_F X pos + 192) ltac:(lia) ltac:(lia) V120))).
  - replace (rbn_A X + 120 + 8) with (rbn_A X + 128) by lia. exact P128.
  - replace (rbn_A X + 120 + 16) with (rbn_A X + 136) by lia. exact P136.
  - replace (rbn_A X + 120 + 24) with (rbn_A X + 144) by lia. exact P144.
  - pose proof HJ8 as (_ & LYc8 & _).
    destruct LYc8 as (_ & _ & _ & _ & _ & _ & _ & _ & LTc8 & LSLO8 & LSHI8 & _).
    apply (rbn8_stack_ra ly5 S5 Wd memc8 mdc8); [exact HAR8 | lia | lia | lia].
  - intros a Ha. apply Hpres8. lia.
  - intros a Ha. left. lia.
  - intros Hroom. rewrite Hacc2, Doe.
    split; [lia|]. split.
    { apply (in_app_sub (rbn_F X pos) 512); [exact HFapp | lia | lia | lia]. }
    split; [destruct HFoi2 as [Hoi | Hoi]; [left | right]; clear - Hoi Hnb23 Dil Dol;
            try unfold IMG_LO in *; try unfold IMG_TOP in *; lia|].
    split; [left; lia|].
    split; [rewrite Hsph; right; lia|].
    split.
    { apply (range_addressable_sub (aview SEGS (w_H Wd) memc8) SHADOW_OFF (rbn_F X pos + 192) 48);
      [exact LB8d | lia | lia]. }
    intros a Ha. apply LB8e. lia. }
intros Wh ch3 Hleh (ly9 & S9 & regs9 & memc9 & mdc9 & -> & HJ9 & HP9 & Hfrs9 & Hperm9 &
  KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & U120 & U128 & U136 & U144 & UG).
rewrite Hsph, SBK in KC1. rewrite Hsph in KC5.
rewrite Hacc2 in KC1, KC2, KC4, U136, UG. rewrite Hovf2 in U144.
assert (HM9 : rbn_mid B X pos ly9 S9 Wh memc9 mdc9 (fun _ => False) (rbn_sh true true true true)).
{ apply (rbn8_mid_step X pos ly5 S5 ly9 S9 Wd Wh memc8 mdc8 memc9 mdc9 _
    (fun a => 0 < sb_dec_c.sb_dec_room 48
                (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6) /\
       rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6) <= a <
       rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6) +
         Z.of_nat (length (sb_dec_c.sb_dec_D (ri_o X) 1)))
    HX HM8 HJ9 Hfrs9 Hperm9); [| | rewrite rbn_sh_len; lia].
  - apply (rbn8_step_call X pos ly5 S5 Wd Wh memc8 mdc8 (rbn_sh true true true true) memc9
      (rbn_A X + 120) _ HX HM8 ltac:(lia) ltac:(lia) KC1 KC2 KC3 KC4).
  - intros a (Hr & Hd). rewrite Doe in Hd. lia. }
assert (FR4 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> in_zr a (frame_rng lyc1 (3, pos)))
  by (intros a Ha; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA4; change (fs_frame_bytes 3) with 512;
      change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos); lia).
assert (FR8 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> in_zr a (frame_rng ly5 (3, pos)))
  by (intros a Ha; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA8; change (fs_frame_bytes 3) with 512;
      change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos); lia).
assert (F98 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
  ~ (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6) <= a <
     rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6) +
       Z.of_nat (length (bn_dec (ri_o X) 1))) ->
  aview SEGS (w_H Wh) memc9 a = aview SEGS (w_H Wd) memc8 a).
{ intros a Ha Hn. apply (KC4 3 pos a); [rewrite Hfrs8; left; reflexivity | left; exact (FR8 a Ha) | lia |].
  intros (Hr & Hd). rewrite Doe in Hd. exact (Hn Hd). }
assert (F87 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> aview SEGS (w_H Wd) memc8 a = aview SEGS (w_H Wd) memc7 a)
  by (intros a Ha; apply KEQ8; lia).
assert (F76 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
  ~ (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1))) <= a <
     rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1))) + 6) ->
  aview SEGS (w_H Wd) memc7 a = aview SEGS (w_H Wd) memc6 a)
  by (intros a Ha Hn; apply HEQ7; [lia | unfold rbn_lit6; cbn [length]; exact Hn]).
assert (F65 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> aview SEGS (w_H Wd) memc6 a = aview SEGS (w_H Wd) memc5 a)
  by (intros a Ha; apply KEQ6; lia).
assert (F54 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
  ~ (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2) <= a <
     rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2) + Z.of_nat (length (bn_dec (ri_i X) 1))) ->
  aview SEGS (w_H Wd) memc5 a = aview SEGS (w_H W1) memc4 a).
{ intros a Ha Hn. apply (KB4 3 pos a); [rewrite Hfrs4; left; reflexivity | left; exact (FR4 a Ha) | lia |].
  intros (Hr & Hd). rewrite Die in Hd. exact (Hn Hd). }
assert (F43 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> aview SEGS (w_H W1) memc4 a = aview SEGS (w_H W1) memc3 a)
  by (intros a Ha; apply KEQ4; lia).
assert (F32 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
  ~ (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) <= a < rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + 2) ->
  aview SEGS (w_H W1) memc3 a = aview SEGS (w_H W1) memc2 a)
  by (intros a Ha Hn; apply HEQ3; [lia | unfold rbn_lit5; cbn [length]; exact Hn]).
assert (F21 : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha; apply KEQ2; lia).
assert (S98 : forall a, rbn_A X + 8 <= a < rbn_A X + 180 -> ~ (rbn_A X + 136 <= a < rbn_A X + 148) ->
  aview SEGS (w_H Wh) memc9 a = aview SEGS (w_H W1) memc4 a).
{ intros a Ha Hn.
  rewrite (KC1 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros (Hr & Hd); lia)), (KEQ8 a ltac:(lia) Hn),
    (HEQ7 a ltac:(lia) ltac:(unfold rbn_lit6; cbn [length]; lia)), (KEQ6 a ltac:(lia) Hn).
  exact (KB1 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros (Hr & Hd); lia)). }
assert (SEQ : forall a, rbn_A X + 8 <= a < rbn_A X + 180 -> ~ (rbn_A X + 40 <= a < rbn_A X + 48) ->
  ~ (rbn_A X + 136 <= a < rbn_A X + 148) -> aview SEGS (w_H Wh) memc9 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2. rewrite (S98 a Ha H2), (KEQ4 a ltac:(lia) H1 H2),
    (HEQ3 a ltac:(lia) ltac:(unfold rbn_lit5; cbn [length]; lia)).
  exact (KEQ2 a ltac:(lia) H2). }
assert (HD9 : Z.of_nat (length (rbm_D9 X)) = Z.of_nat (length (rbm_NB X)) + 2 +
  Z.of_nat (length (bn_dec (ri_i X) 1)) + 6 + Z.of_nat (length (bn_dec (ri_o X) 1))).
{ unfold rbm_D9. rewrite !length_app. cbn [length]. lia. }
pose proof H8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HCf & _).
apply rbn8_cells_app in HCf. destruct HCf as (HC6 & _).
assert (KEEPB : forall r : bv 5,
  existsb (Z.eqb (bv_unsigned r)) [0; 1; 10; 11; 12; 21] = false ->
  existsb (Z.eqb (bv_unsigned r)) [5; 10; 12; 15; 16; 17; 23] = false ->
  existsb (Z.eqb (bv_unsigned r)) [0; 1; 10; 11; 12; 23] = false ->
  existsb (Z.eqb (bv_unsigned r)) [5; 6; 10; 11; 12; 16; 17] = false ->
  acallee_saved (bv_unsigned r) -> getr regs9 r = getr regs1 r).
{ intros r Ha Hb Hc Hd Hs. rewrite (rbn8_pres_get regs8 regs9 r HP9 Hs). exact (KEEPA r Ha Hb Hc Hd Hs). }
apply SRr_ret.
exists pos, regs9, ly9, S9, memc9, mdc9. split.
{ unfold rbn_cfg, cfg_at. rewrite T1r. unfold w64.
  replace (BASE + AF_reac_box_name + RBN_P9) with (BASE + 15992) by (unfold AF_reac_box_name, RBN_P9; lia).
  reflexivity. }
unfold rbn_st9.
split; [exact HM9|].
split.
{ unfold rbn_rbase.
  split; [rewrite (KEEPB (2%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)); exact B2|].
  split; [rewrite (KEEPB (3%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)); exact B3|].
  split; [rewrite (KEEPB (4%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)); exact B4|].
  split; [rewrite (KEEPB (8%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)); exact B8|].
  split; [rewrite (KEEPB (9%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)); exact B9|].
  split; [rewrite (KEEPB (19%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (19%bv : bv 5)) with 19; unfold acallee_saved; lia)); exact B19|].
  rewrite (KEEPB (22%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia)); exact B22. }
split; [rewrite (KEEPB (18%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)); exact R18|].
split; [rewrite (KEEPB (27%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(change (bv_unsigned (27%bv : bv 5)) with 27; unfold acallee_saved; lia)); exact R27|].
split; [rewrite (KEEPB (24%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia)); exact R24|].
split; [rewrite (KEEPB (25%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(change (bv_unsigned (25%bv : bv 5)) with 25; unfold acallee_saved; lia)); exact R25|].
split; [rewrite (KEEPB (20%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia)); exact R20|].
split; [rewrite (KEEPB (26%bv : bv 5) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(change (bv_unsigned (26%bv : bv 5)) with 26; unfold acallee_saved; lia)); exact R26|].
split; [rewrite (rbn8_pres_get regs8 regs9 (21%bv : bv 5) HP9
  ltac:(change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia)); exact T21r|].
split.
{ apply rbn8_cells_app. split.
  { apply (rbn_cells_kept (w_H W1) (w_H Wh) memc1 memc9); [|exact HC6].
    intros a n v kk Hin Hk. pose proof (rbn_locs6_rng X pos a n v Hin) as (L1 & L2).
    unfold rbn_locs6, rbn_locs4 in Hin. cbn [In app] in Hin.
    apply SEQ; [lia | |]; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia|]);
    destruct Hin. }
  apply rbn8_cells_app. split.
  { unfold rbn_rec2. cbn [rbn_cells].
    split; [exact U120|].
    split; [replace (rbn_A X + 128) with (rbn_A X + 120 + 8) by lia; exact U128|].
    split; [rewrite Z.min_l by lia; rewrite HD9; replace (rbn_A X + 136) with (rbn_A X + 120 + 16) by lia;
            rewrite Doe in U136; replace (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6
              + Z.of_nat (length (bn_dec (ri_o X) 1))) with
              (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6 +
               Z.of_nat (length (bn_dec (ri_o X) 1))) by lia; exact U136|].
    split; [|exact I].
    unfold rbm_ovf. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    replace (rbn_A X + 144) with (rbn_A X + 120 + 24) by lia. exact U144. }
  cbn [rbn_cells]. split; [|exact I].
  apply (val_mem_kept SEGS (w_H W1) (w_H Wh) memc4 memc9); [|exact M40].
  intros kk Hk. apply S98; lia. }
assert (FALL : forall a, rbn_F X pos <= a < rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) ->
  aview SEGS (w_H Wh) memc9 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha. rewrite (F98 a ltac:(lia) ltac:(lia)), (F87 a ltac:(lia)), (F76 a ltac:(lia) ltac:(lia)),
    (F65 a ltac:(lia)), (F54 a ltac:(lia) ltac:(lia)), (F43 a ltac:(lia)), (F32 a ltac:(lia) ltac:(lia)).
  exact (F21 a ltac:(lia)). }
split.
{ apply (rbn8_garr_keep W1 Wh memc1 memc9); [|exact G64]. intros a Ha.
  rewrite length_app in Ha. cbn [length] in Ha. apply FALL. lia. }
split.
{ apply (rbn8_garr_keep W1 Wh memc1 memc9); [|exact G128]. intros a Ha.
  rewrite length_app in Ha. cbn [length] in Ha.
  assert (HTB23 : (length (rbm_TB X) <= 23)%nat) by (unfold rbm_TB; apply firstn_le_length).
  apply FALL. lia. }
split; [|exact HA].
rewrite firstn_all2 by lia.
rewrite firstn_all2 in G192 by lia.
assert (GD1 : garr8 SEGS (mrestrict (w_H Wh) memc9) (rbn_F X pos + 192) (rbm_NB X)).
{ apply (rbn8_garr_keep W1 Wh memc1 memc9); [|exact G192]. intros a Ha. apply FALL. lia. }
assert (GD2 : garr8 SEGS (mrestrict (w_H Wh) memc9) (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X))) rbn_lit5).
{ apply (rbn8_garr_keep W1 Wh memc3 memc9); [|exact HG3]. intros a Ha. unfold rbn_lit5 in Ha. cbn [length] in Ha.
  rewrite (F98 a ltac:(lia) ltac:(lia)), (F87 a ltac:(lia)), (F76 a ltac:(lia) ltac:(lia)),
    (F65 a ltac:(lia)), (F54 a ltac:(lia) ltac:(lia)). exact (F43 a ltac:(lia)). }
assert (GD3 : garr8 SEGS (mrestrict (w_H Wh) memc9) (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2))
  (bn_dec (ri_i X) 1)).
{ pose proof (VG ltac:(rewrite Hrm1; lia)) as VG1. rewrite Nat2Z.id, firstn_all, Die in VG1.
  apply (rbn8_garr_keep Wd Wh memc5 memc9); [|exact VG1]. intros a Ha.
  rewrite (F98 a ltac:(lia) ltac:(lia)), (F87 a ltac:(lia)), (F76 a ltac:(lia) ltac:(lia)). exact (F65 a ltac:(lia)). }
assert (GD4 : garr8 SEGS (mrestrict (w_H Wh) memc9)
  (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)))) rbn_lit6).
{ apply (rbn8_garr_keep Wd Wh memc7 memc9); [|exact HG7]. intros a Ha. unfold rbn_lit6 in Ha. cbn [length] in Ha.
  rewrite (F98 a ltac:(lia) ltac:(lia)). exact (F87 a ltac:(lia)). }
assert (GD5 : garr8 SEGS (mrestrict (w_H Wh) memc9)
  (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6))
  (bn_dec (ri_o X) 1)).
{ pose proof (UG ltac:(rewrite Hrm2; lia)) as UG1. rewrite Nat2Z.id, firstn_all, Doe in UG1. exact UG1. }
unfold rbm_D9.
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact GD1|].
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact GD2|].
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
{ replace (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + Z.of_nat (length [32; 40]))
    with (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2)) by (cbn [length]; lia). exact GD3. }
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
{ replace (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + Z.of_nat (length [32; 40]) +
    Z.of_nat (length (bn_dec (ri_i X) 1)))
    with (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1))))
    by (cbn [length]; lia). exact GD4. }
replace (rbn_F X pos + 192 + Z.of_nat (length (rbm_NB X)) + Z.of_nat (length [32; 40]) +
  Z.of_nat (length (bn_dec (ri_i X) 1)) + Z.of_nat (length [32; 105; 110; 32; 47; 32]))
  with (rbn_F X pos + 192 + (Z.of_nat (length (rbm_NB X)) + 2 + Z.of_nat (length (bn_dec (ri_i X) 1)) + 6))
  by (cbn [length]; lia).
exact GD5.
Qed.



End h.
End f.
End d.
