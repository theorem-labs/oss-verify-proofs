(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmitDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v. *)
(* The admission tests of fuzz_grant's entry function LLVMFuzzerTestOneInput on the
   ASan build (slots 0x80d90 .. 0x80e58, fuzz_grant.c:256-277), cut in two halves:

   - the head, 0x80d90 .. 0x80e30: the harness computes its own admission rule from
     the base and the channel count, calls reac_grant_alloc_fits and aborts if the two
     disagree (the branch at 0x80e2c);
   - the tail, 0x80e30 .. 0x80e58: it marks the 2-byte `a` usable in the shadow, zeroes
     it, calls reac_grant_allocate and aborts unless the answer is 0 exactly when the
     box fits (the branch at 0x80e54).

   This file holds what both halves use: the cut between them (`GI_mid`), the
   environment and the symbolic registers of a seat (`admE`, `adm_srA`, `adm_srC`), the
   region list with the windows the tests write through (`adm_rs`), and the transfer of
   a cut's memory facts across a step that writes only `a` and its shadow byte
   (`admZ`, `admKeep`). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
YC1g YC1h YC88 GrantFrame YC45 YC85 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the frame's shadow bytes, before and after `a` is marked usable ---- *)
Lemma gsh_tables_len : length GSH_tables = 104%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma gsh_a_len : length GSH_a = 104%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma gsh_a_56 : nth 56 GSH_a 0 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma gsh_a_other : forall i, (i < 104)%nat -> i <> 56%nat -> nth i GSH_a 0 = nth i GSH_tables 0.
Proof.
assert (H : forallb (fun i => orb (Nat.eqb i 56) (Z.eqb (nth i GSH_a 0) (nth i GSH_tables 0)))
              (seq 0 104) = true) by (vm_compute; reflexivity).
intros i Hi Hne.
pose proof (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)) as Hb.
apply orb_prop in Hb. destruct Hb as [Hb | Hb].
- apply Nat.eqb_eq in Hb. lia.
- apply Z.eqb_eq in Hb. exact Hb.
Qed.

Lemma gsh_a_bytes : Forall (fun v => 0 <= v < 256) GSH_a.
Proof.
apply Forall_forall. intros v Hv.
assert (H : forallb (fun v => andb (Z.leb 0 v) (Z.ltb v 256)) GSH_a = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) H v Hv) as Hb.
apply andb_prop in Hb as [H1 H2]. split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.

Lemma gsh_tables_bytes : Forall (fun v => 0 <= v < 256) GSH_tables.
Proof.
apply Forall_forall. intros v Hv.
assert (H : forallb (fun v => andb (Z.leb 0 v) (Z.ltb v 256)) GSH_tables = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) H v Hv) as Hb.
apply andb_prop in Hb as [H1 H2]. split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

(* Every word a walk reads back from memory is an unsigned 64-bit value. *)
Lemma adm_rdword_range : forall (H : word -> bool) (mem : word -> option byte) a v,
  rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hr. unfold rdword in Hr.
assert (Hb : forall x y, aview SEGS H mem x = Some y -> 0 <= y < 256).
{ intros x y Hx. unfold aview in Hx.
  destruct (YP09.mbyte SEGS (mrestrict H mem) x) as [b|] eqn:Hm; [|discriminate].
  cbn [option_map] in Hx. injection Hx as <-. apply u8_range. }
destruct (aview SEGS H mem a) as [b0|] eqn:H0; [|discriminate].
destruct (aview SEGS H mem (a+1)) as [b1|] eqn:H1; [|discriminate].
destruct (aview SEGS H mem (a+2)) as [b2|] eqn:H2; [|discriminate].
destruct (aview SEGS H mem (a+3)) as [b3|] eqn:H3; [|discriminate].
destruct (aview SEGS H mem (a+4)) as [b4|] eqn:H4; [|discriminate].
destruct (aview SEGS H mem (a+5)) as [b5|] eqn:H5; [|discriminate].
destruct (aview SEGS H mem (a+6)) as [b6|] eqn:H6; [|discriminate].
destruct (aview SEGS H mem (a+7)) as [b7|] eqn:H7; [|discriminate].
apply Hb in H0. apply Hb in H1. apply Hb in H2. apply Hb in H3.
apply Hb in H4. apply Hb in H5. apply Hb in H6. apply Hb in H7.
injection Hr as <-. lia.
Qed.

(* ---- the environment a seat of this phase runs in ---- *)
(* atoms: 0..32 the caller's registers (the shadow offset at 32), 60 the realigned
   stack pointer, 516 the frame, 528 its flag word, 529 its shadow bytes, 530..561 the
   registers the cut starts from, 562.. the values of the spill slots it reads. *)
Definition admE (cx : ecx) (fp : Z) (ms : machine_state) (vs : list word) : env :=
  Eimg (mkEnv (fun n =>
      if (n <? 33)%nat then ew (c_E0 cx) n
      else if (n =? 60)%nat then w64 (c_sp1 cx)
      else if (n =? 516)%nat then w64 (gF cx fp)
      else if (n =? 528)%nat then w64 (gFL cx fp)
      else if (n =? 529)%nat then w64 (gSH cx fp)
      else if (n <? 530)%nat then w64 0
      else if (n <? 562)%nat then getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat (n - 530)))
      else nth (n - 562) vs (w64 0))
    (ed (c_E0 cx))).

Lemma admE_low : forall cx fp ms vs n, (n < 33)%nat -> ew (admE cx fp ms vs) n = ew (c_E0 cx) n.
Proof.
intros cx fp ms vs n Hn. unfold admE. rewrite Eimg_low by (unfold A_TEXT; lia).
cbn [ew]. destruct (Nat.ltb_spec n 33); [reflexivity | lia].
Qed.

Lemma admE_60 : forall cx fp ms vs, ew (admE cx fp ms vs) 60%nat = w64 (c_sp1 cx).
Proof.
intros cx fp ms vs. unfold admE. rewrite Eimg_low by (unfold A_TEXT; lia).
cbn [ew]. reflexivity.
Qed.

Lemma admE_hi : forall cx fp ms vs n, (512 <= n)%nat ->
  ew (admE cx fp ms vs) n =
    (if (n =? 516)%nat then w64 (gF cx fp)
     else if (n =? 528)%nat then w64 (gFL cx fp)
     else if (n =? 529)%nat then w64 (gSH cx fp)
     else if (n <? 530)%nat then w64 0
     else if (n <? 562)%nat then getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat (n - 530)))
     else nth (n - 562) vs (w64 0)).
Proof.
intros cx fp ms vs n Hn. unfold admE, Eimg. cbn [ew].
replace ((A_TEXT <=? n) && (n <? A_LIM))%nat%bool with false
  by (symmetry; apply andb_false_iff; right; apply Nat.ltb_ge; unfold A_LIM; lia).
cbn [ew].
destruct (Nat.ltb_spec n 33); [lia|].
destruct (Nat.eqb_spec n 60); [lia|]. reflexivity.
Qed.

Lemma admE_F : forall cx fp ms vs, ew (admE cx fp ms vs) GA_F = w64 (gF cx fp).
Proof. intros cx fp ms vs. rewrite (admE_hi cx fp ms vs GA_F ltac:(unfold GA_F; lia)). reflexivity. Qed.

Lemma admE_FL : forall cx fp ms vs, ew (admE cx fp ms vs) GA_FL = w64 (gFL cx fp).
Proof. intros cx fp ms vs. rewrite (admE_hi cx fp ms vs GA_FL ltac:(unfold GA_FL; lia)). reflexivity. Qed.

Lemma admE_FSH : forall cx fp ms vs, ew (admE cx fp ms vs) GA_FSH = w64 (gSH cx fp).
Proof. intros cx fp ms vs. rewrite (admE_hi cx fp ms vs GA_FSH ltac:(unfold GA_FSH; lia)). reflexivity. Qed.

Lemma admE_reg : forall cx fp ms vs r, (r < 32)%nat ->
  ew (admE cx fp ms vs) (530 + r) = getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)).
Proof.
intros cx fp ms vs r Hr. rewrite (admE_hi cx fp ms vs (530 + r) ltac:(lia)).
destruct (Nat.eqb_spec (530 + r) 516); [lia|].
destruct (Nat.eqb_spec (530 + r) 528); [lia|].
destruct (Nat.eqb_spec (530 + r) 529); [lia|].
destruct (Nat.ltb_spec (530 + r) 530); [lia|].
destruct (Nat.ltb_spec (530 + r) 562); [|lia].
f_equal. f_equal. lia.
Qed.

Lemma admE_vs : forall cx fp ms vs j, ew (admE cx fp ms vs) (562 + j) = nth j vs (w64 0).
Proof.
intros cx fp ms vs j. rewrite (admE_hi cx fp ms vs (562 + j) ltac:(lia)).
destruct (Nat.eqb_spec (562 + j) 516); [lia|].
destruct (Nat.eqb_spec (562 + j) 528); [lia|].
destruct (Nat.eqb_spec (562 + j) 529); [lia|].
destruct (Nat.ltb_spec (562 + j) 530); [lia|].
destruct (Nat.ltb_spec (562 + j) 562); [lia|].
f_equal. lia.
Qed.

Lemma admE_regN : forall cx fp ms vs n r, (n = 530 + r)%nat -> (r < 32)%nat ->
  ew (admE cx fp ms vs) n = getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)).
Proof. intros cx fp ms vs n r Hn Hr. subst n. apply admE_reg. exact Hr. Qed.

Lemma admE_vsN : forall cx fp ms vs n j, (n = 562 + j)%nat ->
  ew (admE cx fp ms vs) n = nth j vs (w64 0).
Proof. intros cx fp ms vs n j Hn. subst n. apply admE_vs. Qed.

Lemma admE_img : forall cx fp ms vs, img_env VAL A_LIM (admE cx fp ms vs).
Proof. intros cx fp ms vs. unfold admE. apply Eimg_env. Qed.

(* ---- the symbolic registers of a seat ---- *)
Definition admR (r : nat) : sv := SOff (530 + r) 0.

(* The head's seat: the frame's `a` in s2, everything else as it comes. *)
Definition adm_srA : list sv :=
  [ SLit 0; admR 1; SOff GA_SP1 0; SOff 3 0; SOff 4 0; admR 5; admR 6; admR 7;
    SOff GA_SP 0; SOff GA_SP1 0; admR 10; admR 11; admR 12; admR 13; admR 14; admR 15;
    admR 16; admR 17; SOff GA_F 448; admR 19; admR 20; admR 21; admR 22; admR 23;
    admR 24; admR 25; admR 26; admR 27; admR 28; admR 29; admR 30; admR 31 ].

(* The tail's seat: the frame's shadow base is in s6, which the store at 0x80e34 uses. *)
Definition adm_srC : list sv :=
  [ SLit 0; admR 1; SOff GA_SP1 0; SOff 3 0; SOff 4 0; admR 5; admR 6; admR 7;
    SOff GA_SP 0; SOff GA_SP1 0; admR 10; admR 11; admR 12; admR 13; admR 14; admR 15;
    admR 16; admR 17; SOff GA_F 448; admR 19; admR 20; admR 21; SOff GA_FSH 0; admR 23;
    admR 24; admR 25; admR 26; admR 27; admR 28; admR 29; admR 30; admR 31 ].

(* The regions of a seat with the windows this phase writes through: never the spill
   slots, the frame only at `a`, its shadow only at the byte that marks `a`. *)
Definition adm_rs (cx : ecx) (fp : Z) (sh : list Z) (scs fcs : list YP09.chunk)
  (fwlo fwhi swlo swhi : Z) : YP09.smem :=
  ge_saved_region :: set_window (ge_spill_region scs) 0 0
  :: set_window (ge_frame_region fcs) fwlo fwhi
  :: ge_shadow_region swlo swhi (ge_sh_chunks sh) :: ge_obj_regions.

Lemma adm_subregion_refl : forall r : YP09.region, subregion r r.
Proof.
intros r. unfold subregion.
split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [right; split; lia|]. intros c Hc. exact Hc.
Qed.

Lemma adm_narrow_sub : forall cx fp sh scs fcs wlo whi fwlo fwhi,
  0 <= fwlo -> fwhi <= fs_frame_bytes GE_CID ->
  submem (adm_rs cx fp sh scs fcs fwlo fwhi wlo whi)
         (ge_regions cx fp sh scs fcs wlo whi []).
Proof.
intros cx fp sh scs fcs wlo whi fwlo fwhi Hlo Hhi.
unfold adm_rs, ge_regions, ge_regions0. rewrite app_nil_r.
apply submem_keep; [apply adm_subregion_refl|].
apply submem_keep;
  [ unfold subregion, set_window, ge_spill_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|];
    split; [left; lia|]; intros c Hc; exact Hc |].
apply submem_keep;
  [ unfold subregion, set_window, ge_frame_region, fframe_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|];
    split; [right; split; lia|]; intros c Hc; exact Hc |].
apply submem_keep; [apply adm_subregion_refl|].
unfold ge_obj_regions.
apply submem_keep; [apply adm_subregion_refl|].
apply submem_keep; [apply adm_subregion_refl|].
apply submem_keep; [apply adm_subregion_refl|].
apply submem_keep; [apply adm_subregion_refl|].
apply submem_nil.
Qed.

Lemma adm_seat_narrow : forall cx fp sh scs fcs wlo whi fwlo fwhi E pc sr G ms,
  st_ok_pi SEGS VAL E (ge_ss cx fp pc sr sh scs fcs wlo whi [] G) ms ->
  0 <= fwlo -> fwhi <= fs_frame_bytes GE_CID ->
  regions_wf (adm_rs cx fp sh scs fcs fwlo fwhi wlo whi) = true ->
  st_ok_pi SEGS VAL E
    (mkSS pc sr (adm_rs cx fp sh scs fcs fwlo fwhi wlo whi) None G) ms.
Proof.
intros cx fp sh scs fcs wlo whi fwlo fwhi E pc sr G ms HS Hlo Hhi Hwf.
pose proof (st_ok_pi_submem E _ _ (adm_rs cx fp sh scs fcs fwlo fwhi wlo whi) HS
   (adm_narrow_sub cx fp sh scs fcs wlo whi fwlo fwhi Hlo Hhi) Hwf) as HS2.
cbn [ge_ss ss_pc ss_regs ss_resv ss_facts] in HS2. exact HS2.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- what a step of this phase keeps ---- *)
(* Every byte this phase's facts speak about, but for the two bytes of `a` and the
   shadow byte that marks them usable, which the tests write. *)
Definition admZ (cx : ecx) (fp t a : Z) : Prop :=
  c_sp1 cx <= a < 2 ^ 64 \/
  c_p cx <= a < c_p cx + c_n cx \/
  (gF cx fp <= a < gF cx fp + 1024 /\ ~ (gF cx fp + 448 <= a < gF cx fp + 450)) \/
  (gSH cx fp <= a < gSH cx fp + 128 /\ a <> gSH cx fp + 56) \/
  t <= a < t + 460.

Definition admKeep (cx : ecx) (fp t : Z) (W : world SEGS) (m m' : word -> option byte) : Prop :=
  forall a, admZ cx fp t a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.

Lemma admKeep_pw : forall cx fp t W m m', (forall x, m' x = m x) -> admKeep cx fp t W m m'.
Proof.
intros cx fp t W m m' Hm a _. unfold aview, YP09.mbyte, mrestrict. rewrite Hm. reflexivity.
Qed.

Lemma admKeep_trans : forall cx fp t W m1 m2 m3,
  admKeep cx fp t W m1 m2 -> admKeep cx fp t W m2 m3 -> admKeep cx fp t W m1 m3.
Proof. intros cx fp t W m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma admK_rdword : forall cx fp t W m m' a v,
  admKeep cx fp t W m m' -> (forall i, 0 <= i < 8 -> admZ cx fp t (a + i)) ->
  rdword (aview SEGS (w_H W) m) a = Some v ->
  rdword (aview SEGS (w_H W) m') a = Some v.
Proof.
intros cx fp t W m m' a v Hk Hz Hr. rewrite <- Hr. apply rdword_ext.
intros i Hi. apply Hk. apply Hz. exact Hi.
Qed.

Lemma admK_garr8 : forall cx fp t W m m' a l,
  admKeep cx fp t W m m' -> (forall i, 0 <= i < Z.of_nat (length l) -> admZ cx fp t (a + i)) ->
  garr8 SEGS (mrestrict (w_H W) m) a l ->
  garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros cx fp t W m m' a l Hk Hz Hg j Hj.
destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros u Hu. replace u with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
rewrite <- Hv0. apply (mbyte_of_aview SEGS (w_H W) (w_H W) m m'). apply Hk. apply Hz. lia.
Qed.

(* ---- the cut between the two halves ---- *)
(* 0x80e30: the harness's admission rule and the library's agree, and the answer is in
   s3 and in a0. `a` is not yet marked usable, so the frame's shadow is still
   GSH_tables. s2 is the address of `a`, s4 the head-amp table, s5 the shadow offset,
   s6 the frame's shadow base, s7 the base, s8 the bytes of input left, s10 the width
   the input asked for. *)
Definition GP_mid : Z := 0x780.

Definition GI_mid (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_mid W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\
  getr (ms_regs ms3) 19 = w64 (Z.b2z (GrantSlotPlan.ok (c_pl cx))) /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 23 = w64 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))) /\
  getr (ms_regs ms3) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 26 = w64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 120 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_LIT) /\
  gslots_late cx fp W3 ms3 /\
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

End c.
End b.
End a.
