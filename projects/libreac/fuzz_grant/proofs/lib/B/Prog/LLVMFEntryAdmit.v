(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmitDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmitTail), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryAdmitDefs.v, lib/A/Prog/GrantEntryAdmit.v and lib/A/Prog/GrantEntryAdmitTail.v. *)
(* The image B (fuzz_grant.asan-ubsan, bin sha256 fde52226dc48) walk of the admission tests of
   LLVMFuzzerTestOneInput, in the shape of lib/A/Prog/GrantEntryAdmitDefs.v, GrantEntryAdmit.v and
   GrantEntryAdmitTail.v at a working branch 3d3b73e282f (the same three blobs, 33897b6de93 / ab603369992 /
   2f7eef63e78, are on a working branch 5651bf66924),
   which cover image A's 0x80d90 .. 0x80e58 and were written for fuzz_grant's entry walk. Every address, register,
   spill-slot offset and byte below is read from image B. The frame facts and the caller's chain come from the
   foundation, LLVMFEntrySeat.v's `ge_frame_addr_eq`, `ge_F_facts` and `ge_achain`. `hdr_ranges`, `fits_spec` and
   `fits_false` are restated here from lib/Prog/Seg_admit.v with their proofs, so that this file's Require closure
   does not carry Seg_main and the C-level walk modules; they name no address.

   IMAGE B's RANGE, 0x81300 (GP_admit) .. 0x81390 (GP_sweep), 32 instructions on the path:

     81300 ld s7,32(s1) ; addi a0,s7,-1 ; li a1,39 ; li s2,0 ; bltu a1,a0,0x8134c
     81314 ld a0,24(s1) ; slli a0,a0,48 ; ld s5,48(s1) ; ld s6,64(s1) ; ld s4,88(s1) ; ld s8,120(s1)
     8132c blt a0,zero,0x8135c ; add a0,s4,s7 ; slti s2,a0,49 ; j 0x8135c
     8134c ld s5,48(s1) ; ld s6,64(s1) ; ld s4,88(s1) ; ld s8,120(s1)
     8135c mv a0,s4 ; mv a1,s7 ; call reac_grant_alloc_fits
     81368 bne a0,s2,0x81d98          <- refuted: the library's answer is the harness's own rule
     8136c li a0,2 ; sb a0,56(s3)     <- marks the granule of `a` 0x02
     81374 sh zero,0(s8)              <- a := 0,0
     81378 mv a0,s8 ; mv a1,s4 ; mv a2,s7 ; call reac_grant_allocate
     81388 addi s2,s2,-1 ; bne a0,s2,0x81d98   <- refuted the same way
     81390 (GP_sweep)

   so s4 is the base (spill slot s1+88), s7 the width (s1+32), s8 the address of `a` = F + 448 (s1+120), s3 the
   frame's shadow base, and s2 the harness's own rule
   `(width - 1 <=u 39) && (sext16 (the header's halfword) >= 0) && (base + width < 49)`, which is GrantModel.fits
   of the base and the width, which is GrantSlotPlan.ok of the input.

   WHAT IMAGE B MAKES DIFFERENT from image A's text, all measured:
   - the registers are renamed: image A had the width in s10, the base in s7, the answer in s3, `a` in s2 and the
     frame's shadow base in s6, which it reloaded from a spill slot; image B keeps the shadow base in s3 across
     the whole body and never reloads it here;
   - the spill slots differ: image B reads 24, 32, 48, 64, 88 and 120 where image A read 24, 48, 56, 64, 120, 152;
   - SLOT 24 HOLDS `256 * (u16 / 256)`, NOT the whole halfword: image B stores a4 = (the high byte << 8) at
     0x811d8 where image A stores the whole halfword at 0x80dec. The sign test `slli 48; bltz` reads the same bit
     either way, and `adm_hi_lt` below is the one extra lemma that needs;
   - image B has no `ld s9,0x48(s1)` between the call of reac_grant_allocate and the branch, which image A has at
     0x80e50, so the symbolic state of the tail needs no spill region at all;
   - image A's GrantEntryAdmitDefs.v also carries `admE`, `adm_srA`, `adm_srC`, `adm_rs`, `adm_narrow_sub` and
     `adm_seat_narrow`, which neither of its two proof files uses; they are not ported.

   THE THREE IMAGE-A LEAK CLASSES IN THE PORT SOURCE, and what was done:
   1. `frm_off_imgP` at GrantEntryAdmitTail.v:228 -> `YC1h.frm_off_imgB` here (image A's `_imgP` form carries image A's
      top 0x5fa000; on the integration tree off_img is lib/B/YCbq.v's, over image B's top 0x5fb000; the walk does
      not depend on which). `off_img (gF + 448) 2` at :365, which image A's contract of
      reac_grant_allocate asks for, is image B's `(p + 2 <= IMG_LO_B \/ IMG_TOP_B <= p)`, which image B's contract
      asks for by name. No other `off_img` or `_imgP` is in the two source files.
   2. `%nat` ATOM indices: image A's two walks use 2, 9, 18, 19, 20, 21, 22, 23, 24, 26, 32..37, 40, 44 and 33, 37,
      all below A_TEXT = 240, i.e. registers or phase-local atoms. They are re-derived for image B's registers:
      the frame's shadow base is atom 19 (not 22) and `a` is atom 24 (not 18); the six spill-slot atoms 32..37
      carry image B's six slots.
   3. OBJECT numbers: neither image-A file names `A_OBJ`, `pa_obj_img` or any image object, so there is nothing to
      re-key, and this file names none. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo YC1g YC1h YC45 YC85 GrantACjr
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* Every `lia` in this file is linear once `/` and `mod` are atoms: each division or remainder it needs is stated
   by hand (Z.div_mod, Z.div_unique, Z.mod_small). So zify's euclidean-division expansion stays off here, whatever
   the Require closure sets: with it on, `rocq compile -time` measured three `lia` calls of the tail's GEO at
   100 s, 170 s and 175 s, because each expanded every `/` and `mod` of the context. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- the header of the input, as fuzz_grant's own plain walk reads it ---- *)
(* Restated from lib/Prog/Seg_admit.v:13-39 with its proof; it names no address and no image. *)
Lemma adm_rd8_range : forall pl pos, 0 <= fst (GrantSlotPlan.rd8 pl pos) < 256.
Proof.
intros pl pos. unfold GrantSlotPlan.rd8. destruct (pos <? length pl)%nat; cbn [fst]; [|lia].
unfold GrantSlotPlan.pbz. pose proof (bv_unsigned_in_range _ (nth pos pl (Z_to_bv 8 0))) as H.
change (bv_modulus 8) with 256 in H. lia.
Qed.

Lemma adm_rd16_range : forall pl pos, 0 <= fst (GrantSlotPlan.rd16 pl pos) < 65536.
Proof.
intros pl pos. unfold GrantSlotPlan.rd16.
destruct (GrantSlotPlan.rd8 pl pos) as [lo p1] eqn:E1.
destruct (GrantSlotPlan.rd8 pl p1) as [hi p2] eqn:E2. cbn [fst].
pose proof (adm_rd8_range pl pos) as H1. pose proof (adm_rd8_range pl p1) as H2.
rewrite E1 in H1. rewrite E2 in H2. cbn [fst] in H1, H2. lia.
Qed.

Lemma adm_hdr_ranges : forall pl,
  0 <= GrantSlotPlan.h_u16 (GrantSlotPlan.header pl) < 65536 /\
  -32768 <= GrantSlotPlan.h_base (GrantSlotPlan.header pl) < 32768 /\
  0 <= GrantSlotPlan.h_in (GrantSlotPlan.header pl) < 256 /\
  0 <= GrantSlotPlan.h_rows (GrantSlotPlan.header pl) < 256 /\
  (0 <= GrantSlotPlan.h_base (GrantSlotPlan.header pl) <->
     GrantSlotPlan.h_u16 (GrantSlotPlan.header pl) < 32768).
Proof.
intros pl. unfold GrantSlotPlan.header.
destruct (GrantSlotPlan.rd16 pl 0) as [u p1] eqn:E1.
destruct (GrantSlotPlan.rd8 pl p1) as [i p2] eqn:E2.
destruct (GrantSlotPlan.rd8 pl p2) as [r p3] eqn:E3.
pose proof (adm_rd16_range pl 0) as H1. pose proof (adm_rd8_range pl p1) as H2.
pose proof (adm_rd8_range pl p2) as H3.
rewrite E1 in H1. rewrite E2 in H2. rewrite E3 in H3. cbn [fst] in *.
unfold GrantSlotPlan.h_base, GrantSlotPlan.sext16;
  cbn [GrantSlotPlan.h_u16 GrantSlotPlan.h_in GrantSlotPlan.h_rows].
destruct (u <? 32768) eqn:Eu; [apply Z.ltb_lt in Eu | apply Z.ltb_ge in Eu]; repeat split; lia.
Qed.

(* Restated from lib/Prog/Seg_admit.v:136-140 with its proof. *)
Lemma adm_fits_spec : forall b w, fits b w = true <-> (1 <= w <= 40 /\ 0 <= b /\ b + w <= 48).
Proof. intros b w. unfold fits. rewrite !andb_true_iff, !Z.leb_le. tauto. Qed.
Lemma adm_fits_false : forall b w, ~ (1 <= w <= 40 /\ 0 <= b /\ b + w <= 48) -> fits b w = false.
Proof. intros b w H. destruct (fits b w) eqn:E; [apply adm_fits_spec in E; contradiction | reflexivity]. Qed.

(* The word image B keeps in the spill slot 24 is the header's halfword with its low byte dropped; the sign test at
   0x81314 .. 0x8132c reads the same bit as image A's test on the whole halfword, because 32768 = 128 * 256. *)
Lemma adm_hi_range : forall u, 0 <= u < 65536 -> 0 <= 256 * (u / 256) <= 65280.
Proof.
intros u Hu. pose proof (Z.div_mod u 256 ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound u 256 ltac:(lia)) as Hm. lia.
Qed.
Lemma adm_hi_lt : forall u, 0 <= u < 65536 -> (256 * (u / 256) < 32768 <-> u < 32768).
Proof.
intros u Hu. pose proof (Z.div_mod u 256 ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound u 256 ltac:(lia)) as Hm. lia.
Qed.

Local Notation hbase cx := (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))).
Local Notation hwid cx := (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))).
Local Notation hu16 cx := (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx))).
Local Notation hhi cx := (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)).

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

(* ---- the pcs inside this phase, as offsets in image B's listing ---- *)
(* 0x8135c, where the three paths of the harness's own rule meet: the call reads no memory. *)
Definition AH_PC : Z := 0x920.
(* 0x8136c, where the library's answer has been checked against the harness's. *)
Definition GP_mid : Z := 0x930.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* ---- small facts on the environment of the run ---- *)
Lemma at_ewR : forall (regs : bvmap 5 word) extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma at_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma at_denot_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma ah_mod64 : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma ah_aview_pw : forall (W : world SEGS) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros W m m' a H. unfold aview, mbyte, mrestrict. rewrite H. reflexivity. Qed.
Lemma ah_rdword_pw : forall (W : world SEGS) (m m' : word -> option byte) a v,
  (forall x, m' x = m x) -> rdword (aview SEGS (w_H W) m) a = Some v ->
  rdword (aview SEGS (w_H W) m') a = Some v.
Proof.
intros W m m' a v H Hr. rewrite <- Hr. apply rdword_ext. intros i Hi. apply ah_aview_pw. exact H.
Qed.
Lemma ah_garr8_pw : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, m' x = m x) -> garr8 SEGS (mrestrict (w_H W) m) a l ->
  garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l H Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros q Hq. unfold mbyte, mrestrict. rewrite H. exact (Hv q Hq).
Qed.
(* Every word a walk reads back from memory is an unsigned 64-bit value. *)
Lemma adm_rdword_range : forall (H : word -> bool) (mem : word -> option byte) a v,
  rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hr. unfold rdword in Hr.
assert (Hb : forall x y, aview SEGS H mem x = Some y -> 0 <= y < 256).
{ intros x y Hx. unfold aview in Hx.
  destruct (mbyte SEGS (mrestrict H mem) x) as [b|] eqn:Hm; [|discriminate].
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
(* A run that writes only into its windows keeps every byte outside them. *)
Lemma at_keep_outside : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a HF Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
(* A run whose regions have no window writes no byte. *)
Lemma at_frame_none : forall E rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hr & Hb).
rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.
(* Two zero bytes written as one halfword are two zero bytes. *)
Lemma at_val2_garr8 : forall (m : word -> option byte) a,
  val_mem SEGS m a 2 0 -> garr8 SEGS m a [0; 0].
Proof.
intros m a H j Hj. cbn [length] in Hj.
assert (Hc : j = 0%nat \/ j = 1%nat) by lia.
destruct Hc as [-> | ->]; cbn [nth]; (split; [|lia]); intros q Hq; replace q with 0%nat by lia.
- specialize (H 0%nat ltac:(lia)).
  replace (a + Z.of_nat 0 + Z.of_nat 0) with (a + Z.of_nat 0) by lia. rewrite H.
  do 2 f_equal; vm_compute; reflexivity.
- specialize (H 1%nat ltac:(lia)).
  replace (a + Z.of_nat 1 + Z.of_nat 0) with (a + Z.of_nat 1) by lia. rewrite H.
  do 2 f_equal; vm_compute; reflexivity.
Qed.
(* The signed compare of a branch, as the engine denotes it. *)
Lemma ah_branch_lt : forall E a b,
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold Sg. reflexivity. Qed.

(* ---- the symbolic states of the two runs ---- *)
(* The six spill slots the tests read, above the realigned stack pointer s1 (atom 9): the header's halfword with
   its low byte dropped at 24, the width at 32, the input cursor at 48, the address of `ch` at 64, the base at 88
   and the address of `a` at 120. Their values are the atoms 32 .. 37 of the run's environment. *)
Definition AH_Rsp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 128 0 0
    [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
     YP09.mkChunk 48 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0));
     YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 120 (CVal 8 (SOff 37 0))].
Definition ah_ss0 : sstate := mkSS GP_admit sr_atoms [AH_Rsp] None (mkFacts [] [] []).
Definition ah_ss1 : sstate := mkSS AH_PC sr_atoms [] None (mkFacts [] [] []).

(* The shadow byte that marks `a`: s3 + 56, s3 the frame's shadow base (atom 19). *)
Definition AT_Rsh : YP09.region := YP09.mkRegion (Some 19%nat) 56 57 56 57 [].
(* The two bytes of `a`: s8 (atom 24). *)
Definition AT_Ra : YP09.region := YP09.mkRegion (Some 24%nat) 0 2 0 2 [].
Definition at_ss0 : sstate :=
  mkSS GP_mid sr_atoms [AT_Rsh; AT_Ra] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (24%nat, mkAF 4096 (2 ^ 47) 5)] [] []).

(* the value of a register of the symbolic state, from the atom facts *)
Local Ltac regval HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = w64 ?v =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R;
    lazymatch e with
    | SOff ?n 0 =>
        rewrite at_denot_off0;
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite F; unfold w64; first [reflexivity | f_equal; lia] end
    | SOff ?n ?x =>
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite (at_denot_off_val Ex n u x F) by lia; unfold w64; f_equal; lia end
    end end end.
(* the register r of the symbolic state, as the symbolic value the run left in it *)
Local Ltac regsv HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R
  end end.
(* After a call: the facts on the atoms below k hold in the new environment. *)
Local Ltac restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = Z_to_bv 64 ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = Z_to_bv 64 v |- _ => fail
      | _ => let F' := fresh "F" in assert (F' : ew En n = Z_to_bv 64 v) by (rewrite OLD by (cbv; lia); exact F)
      end
  end end.
(* a run whose regions have no window writes no byte *)
Local Ltac nowin HF :=
  lazymatch type of HF with frame_of ?Ex ?rs ?m ?m' =>
    let rs' := eval vm_compute in rs in change rs with rs' in HF;
    apply (at_frame_none Ex rs' m m'); [repeat constructor; cbn; lia | exact HF] end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HFITS : tb_reac_grant_alloc_fits_spec B.
Hypothesis HALLOC : tb_reac_grant_allocate_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- what a step of this phase keeps ---- *)
(* Every byte this phase's facts speak about, but for the two bytes of `a` and the shadow byte that marks them
   usable, which the tests write. *)
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
intros cx fp t W m m' Hm a _. unfold aview, mbyte, mrestrict. rewrite Hm. reflexivity.
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

(* The machine stack pointer the entry function was called with, and the realigned one. *)
Lemma at_gsp : forall cx, ge_base B MT cx ->
  alloc_ceiling + GE_STK <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 320 < c_sp1 cx <= spZ (c_regs cx) - 288 /\
  c_sp1 cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
intros cx HB.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hmp.
rewrite Hsp1. split; [lia|]. split; [lia|]. split; [|exact Hal16].
rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

(* The twenty spill slots GI_admit and GI_sweep carry, and the model of the input the two tables keep, named
   once so that the two cuts inside this phase can carry them as two facts. *)
Definition gslots_adm (cx : ecx) (fp t : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  gslot cx W3 ms3 0 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 16 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 24 (hhi cx) /\ gslot cx W3 ms3 32 (hwid cx) /\
  gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 56 (gF cx fp + GO_LIT) /\ gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\
  gslot cx W3 ms3 72 (gF cx fp) /\ gslot cx W3 ms3 80 (gF cx fp + GO_POLL) /\
  gslot cx W3 ms3 88 (hbase cx mod 2 ^ 64) /\ gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\
  gslot cx W3 ms3 104 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\ gslot cx W3 ms3 120 (gF cx fp + GO_A) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t.
Definition gmodel (cx : ecx) (fp : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t : Z) : Prop :=
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* ---- the two cuts inside this phase ---- *)
(* 0x8135c: the harness's own answer is in s2 and the call of reac_grant_alloc_fits is next. *)
Definition ah_GI (cx : ecx) (fp : Z) (kk acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp AH_PC W3 ms3 GSH_tables /\ kk <= 1 /\ acc <= GE_A1 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (Z.b2z (GrantSlotPlan.ok (c_pl cx))) /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 20 = w64 (hbase cx) /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (hwid cx) /\
  getr (ms_regs ms3) 24 = w64 (gF cx fp + GO_A) /\
  gslots_adm cx fp t W3 ms3 /\ gmodel cx fp ly3 S3 W3 ms3 t.

(* 0x8136c: the library's answer and the harness's agree, and both are in s2 and in a0. *)
Definition GI_mid (cx : ecx) (fp : Z) (kk acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GP_mid W3 ms3 GSH_tables /\ kk <= 1 /\ acc <= GE_A1 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (Z.b2z (GrantSlotPlan.ok (c_pl cx))) /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 20 = w64 (hbase cx) /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (hwid cx) /\
  getr (ms_regs ms3) 24 = w64 (gF cx fp + GO_A) /\
  gslots_adm cx fp t W3 ms3 /\ gmodel cx fp ly3 S3 W3 ms3 t.

(* ---- 0x8135c .. 0x8136c: the call of reac_grant_alloc_fits and its check ---- *)
Theorem ah_call : forall POST,
  ge_from B MT POST (GI_mid) -> ge_from B MT POST (ah_GI).
Proof.
intros POST HNEXT cx fp kk acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & HBODY & Hk & Hacc & HBLK & HCN & R18 & R19 & R20 & R21 & R22 & R23 & R24
                 & SLOTS & HMOD).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL
                     & Hlen & HIN).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO. rewrite IMG_LO_B_val in HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (at_gsp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16).
unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp.
pose proof HB as ((_ & Hra0 & Hra4 & Hgp0 & Htp0 & _) & _).
pose proof (adm_hdr_ranges (c_pl cx)) as (Ru & Rb & Ri & Rr & Rs).
assert (Eok : GrantSlotPlan.ok (c_pl cx) = fits (hbase cx) (hwid cx)) by reflexivity.
assert (Hs16 : c_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as Hdm. rewrite Hsp32, Z.add_0_r in Hdm. rewrite Hdm.
  replace (32 * (c_sp1 cx / 32)) with ((c_sp1 cx / 32 * 2) * 16) by lia. apply Z_mod_mult. }
pose proof HJ as (HARJ & HlyJ & _).
pose proof HlyJ as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r Hq; subst E; apply at_ewR; exact Hq).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx))))
  by (rewrite (EE 18%nat 18%bv eq_refl), R18, Eok; reflexivity).
assert (F19 : ew E 19 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (F20 : ew E 20 = Z_to_bv 64 (hbase cx)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (F21 : ew E 21 = Z_to_bv 64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (F22 : ew E 22 = Z_to_bv 64 (gF cx fp + GO_CH)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (F23 : ew E 23 = Z_to_bv 64 (hwid cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (F24 : ew E 24 = Z_to_bv 64 (gF cx fp + GO_A)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
(* the machine state as the engine's symbolic state at 0x8135c *)
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AH_PC))
  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E ah_ss1 (restrict (w_H W3) ms3)).
{ rewrite Hms. unfold ah_ss1. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE EE.
(* 0x8135c .. 0x81364: the two arguments and the call *)
paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msN) |- _ => rename msN into msC end.
assert (PC : forall x, ms_mem msC x = ms_mem ms3 x) by nowin HF.
clear HF HFr HG.
pmkst HS.
rewrite pa_sigma_reac_grant_alloc_fits.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs msC) = c_sp1 cx)
  by (unfold spZ; rewrite Q2, F2; apply unsigned_lit_small; lia).
assert (Qs0 : s0Z (ms_regs msC) = spZ (c_regs cx))
  by (unfold s0Z; rewrite Q8, F8; apply unsigned_lit_small; lia).
(* the caller's chain, from the saved words of its machine frame *)
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem msC)) (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
                (s0Z (ms_regs msC)) (gch cx)).
{ rewrite Qs0. replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
  apply (achain_ly_top (c_ly cx) ly3); [exact Etop|].
  destruct HSV as (Hra & Hsj).
  apply (ge_achain B MT cx HB).
  - intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & FJ1 & _). apply FJ1; lia.
  - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msC) _ _ PC). exact Hra.
  - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msC) _ _ PC).
    pose proof (Hsj 0 ltac:(lia)) as H0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    cbn [Z.ltb] in H0. exact H0.
  - lia. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs msC) (ms_mem msC) _ GE_STK (spZ (c_regs cx)) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ kk
    STK_reac_grant_alloc_fits [] 0 (c_sp1 cx - spZ (c_regs cx)) _ (gch cx)
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
       (forall x, mem2 x = ms_mem msC x) /\
       getr regs2 10 = w64 (Z.b2z (fits (hbase cx) (hwid cx)))) HJ);
  [ rewrite Qsp; lia
  | rewrite Zminus_mod, Hs16, Hsp16; reflexivity
  | lia | unfold STK_reac_grant_alloc_fits, ESTACK; lia
  | unfold STK_reac_grant_alloc_fits, ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput; lia
  | rewrite Q3, F3; reflexivity | rewrite Q4, F4; reflexivity
  | reflexivity
  | rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite Q1, unsigned_lit_small by lia; lia
  | exact HCH
  | | intros a (r & Hr & _); destruct Hr ].
  intros HPRE1. eapply SRr_mono.
  { exact (HFITS ly3 S3 W3 (ms_regs msC) (ms_mem msC) _ (gch cx) (hbase cx) (hwid cx) HPRE1
      ltac:(rewrite Q10, F20; reflexivity) ltac:(rewrite Q11, F23; reflexivity)
      ltac:(unfold int32; lia) ltac:(unfold int32; lia) ltac:(intros; lia)). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJf & HPf & Ha0 & Ely & ES & EW & Hmem & _).
  exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJf|]. split; [exact HPf|].
  split; [exact Ely|]. split; [exact ES|]. split; [exact EW|]. split; [exact Hmem | exact Ha0]. }
(* ---- after the call: the check at 0x81368 ---- *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HJc & HP2 & Ely & ES & EW & Hmem & Ha0).
subst ly2 S2 W2. subst c2.
rewrite Z.add_0_r in HJ2.
assert (PM : forall x, mem2 x = ms_mem ms3 x) by (intros x; rewrite Hmem; apply PC).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W3) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite Q1.
remember (havoc E 40 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall q, (q < 40)%nat -> ew E1 q = ew E q)
  by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
assert (G18 : ew E1 18 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx))))
  by (rewrite OLD1 by lia; exact F18).
assert (G19' : ew E1 19 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F19).
assert (G20 : ew E1 20 = Z_to_bv 64 (hbase cx)) by (rewrite OLD1 by lia; exact F20).
assert (G21 : ew E1 21 = Z_to_bv 64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite OLD1 by lia; exact F21).
assert (G22 : ew E1 22 = Z_to_bv 64 (gF cx fp + GO_CH)) by (rewrite OLD1 by lia; exact F22).
assert (G23 : ew E1 23 = Z_to_bv 64 (hwid cx)) by (rewrite OLD1 by lia; exact F23).
assert (G24 : ew E1 24 = Z_to_bv 64 (gF cx fp + GO_A)) by (rewrite OLD1 by lia; exact F24).
assert (G2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2).
assert (G3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3).
assert (G4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4).
assert (G8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8).
assert (G9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9).
assert (G44 : ew E1 44 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx)))).
{ rewrite HE1. change 44%nat with (40 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Ha0. }
clear HE1.
clear HJ. rename HJ2 into HJ.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ =>
  let v := eval vm_compute in ss3 in change ss3 with v in HS end.
psrr_branch_pi RUNP BR HS.
{ (* the branch into 0x81d98 is taken only if the call and the harness disagree *)
  exfalso. rewrite branch_ne_U in Hc. apply (proj1 (Bool.negb_true_iff _)), Z.eqb_neq in Hc. apply Hc.
  rewrite !U_SOff, G44, G18. reflexivity. }
paj_run_to_shc RUNTOP HS HJ GP_mid; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msF end.
assert (PF : forall x, ms_mem msF x = mem2 x) by nowin HF.
clear HF HFr HG.
assert (PT : forall x, ms_mem msF x = ms_mem ms3 x) by (intros x; rewrite PF; apply PM).
(* ---- 0x8136c: GI_mid ---- *)
pmkst HS.
eapply HNEXT; [exact HB | exact HJ | exact HFR | exact HMO |].
unfold GI_mid. exists t.
assert (KSL : forall off v, gslot cx W3 ms3 off v -> gslot cx W3 msF off v)
  by (intros off v Hv; unfold gslot in Hv |- *;
      apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT); exact Hv).
split.
{ unfold ge_body, gregs.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
    split; [rewrite Hgp0; regval HS | rewrite Htp0; regval HS]. }
  split.
  { destruct HSV as (Hra & Hsj). split.
    - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact Hra.
    - intros j Hj. apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact (Hsj j Hj). }
  split.
  { intros i Hi. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msF) _ PT). exact (HSH i Hi). }
  split.
  { apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HFL. }
  split; [exact Hlen|].
  apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HIN. }
split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact HCN|].
split; [regval HS|]. split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
split.
{ unfold gslots_adm in SLOTS |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; apply KSL; assumption. }
{ destruct HMOD as (HTAB & HWAS & HSET & HREL & HI1).
  split.
  { pose proof HTAB as (Tin & Tpos & Tlen & Tb).
    split; [exact Tin|]. split; [exact Tpos|]. split; [exact Tlen|].
    intros i Hi H1 H2 H3. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msF) _ PT).
    exact (Tb i Hi H1 H2 H3). }
  split.
  { unfold gfarr in HWAS |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HWAS. }
  split.
  { unfold gfarr in HSET |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HSET. }
  split; [exact HREL | exact HI1]. }
Qed.

(* ---- 0x81300 .. 0x8135c: the harness computes its own admission rule ---- *)
Theorem ge_admit_head : forall POST,
  ge_from B MT POST (GI_mid) -> ge_from B MT POST (GI_admit B MT).
Proof.
intros POST HNEXT. pose proof (ah_call POST HNEXT) as HMID.
intros cx fp kk acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & HBODY & Hk & Hacc & HBLK & HCN & R19
                 & SL0 & SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & SL64 & SL72 & SL80 & SL88 & SL96
                 & SL104 & SL112 & SL120 & SL128 & SL136 & SL144 & SL152
                 & HTAB0 & HWAS0 & HSET0 & HREL0 & HI10).
assert (SLOTS : gslots_adm cx fp t W3 ms3).
{ unfold gslots_adm. repeat match goal with |- _ /\ _ => split end; assumption. }
assert (HMOD : gmodel cx fp ly3 S3 W3 ms3 t)
  by (exact (conj HTAB0 (conj HWAS0 (conj HSET0 (conj HREL0 HI10))))).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL
                     & Hlen & HIN).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO. rewrite IMG_LO_B_val in HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (at_gsp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16).
unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp.
pose proof HB as ((_ & Hra0 & Hra4 & Hgp0 & Htp0 & _) & _).
pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 kk HB HJ HFR) as (HF0 & HFc & HFia & HFo & HSHeq).
assert (HSHrng : 0 <= gSH cx fp < 2 ^ 64).
{ assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  rewrite HSHeq. unfold SHADOW_OFF. lia. }
pose proof (adm_hdr_ranges (c_pl cx)) as (Ru & Rb & Ri & Rr & Rs).
assert (Eok : GrantSlotPlan.ok (c_pl cx) = fits (hbase cx) (hwid cx)) by reflexivity.
assert (Hhir : 0 <= hhi cx <= 65280) by (apply adm_hi_range; lia).
pose proof (adm_rdword_range _ _ _ _ SL48) as RN48.
pose proof (adm_rdword_range _ _ _ _ SL64) as RN64.
pose proof (adm_rdword_range _ _ _ _ SL120) as RN120.
remember (Eimg (Ereg (ms_regs ms3)
   [Z_to_bv 64 (hhi cx); Z_to_bv 64 (hwid cx);
    Z_to_bv 64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)));
    Z_to_bv 64 (gF cx fp + GO_CH); Z_to_bv 64 (hbase cx mod 2 ^ 64);
    Z_to_bv 64 (gF cx fp + GO_A)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r Hq; subst E; apply at_ewR; exact Hq).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j
   [Z_to_bv 64 (hhi cx); Z_to_bv 64 (hwid cx);
    Z_to_bv 64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)));
    Z_to_bv 64 (gF cx fp + GO_CH); Z_to_bv 64 (hbase cx mod 2 ^ 64);
    Z_to_bv 64 (gF cx fp + GO_A)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F19 : ew E 19 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (F32 : ew E 32 = Z_to_bv 64 (hhi cx)) by (exact (EX 0%nat ltac:(lia))).
assert (F33 : ew E 33 = Z_to_bv 64 (hwid cx)) by (exact (EX 1%nat ltac:(lia))).
assert (F34 : ew E 34 = Z_to_bv 64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (exact (EX 2%nat ltac:(lia))).
assert (F35 : ew E 35 = Z_to_bv 64 (gF cx fp + GO_CH)) by (exact (EX 3%nat ltac:(lia))).
assert (F36 : ew E 36 = Z_to_bv 64 (hbase cx mod 2 ^ 64)) by (exact (EX 4%nat ltac:(lia))).
assert (F37 : ew E 37 = Z_to_bv 64 (gF cx fp + GO_A)) by (exact (EX 5%nat ltac:(lia))).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U32 : U E (SOff 32 0) = hhi cx) by (apply (U_atom E 32 (hhi cx) F32); lia).
assert (U33 : U E (SOff 33 0) = hwid cx) by (apply (U_atom E 33 (hwid cx) F33); lia).
assert (U36 : U E (SOff 36 0) = hbase cx mod 2 ^ 64)
  by (apply (U_atom E 36 _ F36); apply Z.mod_pos_bound; lia).
(* the memory facts of the cut, for any state whose memory is this one *)
assert (MEMOK : forall msX : machine_state, (forall x, ms_mem msX x = ms_mem ms3 x) ->
   gsaved cx W3 msX /\
   gshadow cx fp W3 msX GSH_tables /\
   rdword (aview SEGS (w_H W3) (ms_mem msX)) (gF cx fp + 1016) = Some (gFL cx fp) /\
   garr8 SEGS (mrestrict (w_H W3) (ms_mem msX)) (c_p cx)
     (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
   (forall off v, gslot cx W3 ms3 off v -> gslot cx W3 msX off v) /\
   gmodel cx fp ly3 S3 W3 msX t).
{ intros msX PX. split.
  { destruct HSV as (Hra & Hsj). split.
    - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact Hra.
    - intros j Hj. apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact (Hsj j Hj). }
  split.
  { intros i Hi. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msX) _ PX). exact (HSH i Hi). }
  split.
  { apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HFL. }
  split.
  { apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HIN. }
  split.
  { intros off v Hv. unfold gslot in Hv |- *.
    apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact Hv. }
  destruct HMOD as (HTAB & HWAS & HSET & HREL & HI1).
  split.
  { pose proof HTAB as (Tin & Tpos & Tlen & Tb).
    split; [exact Tin|]. split; [exact Tpos|]. split; [exact Tlen|].
    intros i Hi H1 H2 H3. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msX) _ PX).
    exact (Tb i Hi H1 H2 H3). }
  split.
  { unfold gfarr in HWAS |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HWAS. }
  split.
  { unfold gfarr in HSET |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HSET. }
  split; [exact HREL | exact HI1]. }
(* the cut at 0x8135c, once a path of the rule has reached it *)
assert (ATMID : forall (msX : machine_state) (mdX : Model) ssX,
   st_ok_pi SEGS VAL E ssX (restrict (w_H W3) msX) -> ss_pc ssX = AH_PC ->
   ss_resv ssX = None ->
   (forall x, ms_mem msX x = ms_mem ms3 x) ->
   getr (ms_regs msX) 2 = w64 (c_sp1 cx) ->
   getr (ms_regs msX) 8 = w64 (spZ (c_regs cx)) ->
   getr (ms_regs msX) 9 = w64 (c_sp1 cx) ->
   getr (ms_regs msX) 3 = getr (c_regs cx) 3 ->
   getr (ms_regs msX) 4 = getr (c_regs cx) 4 ->
   getr (ms_regs msX) 18 = w64 (Z.b2z (GrantSlotPlan.ok (c_pl cx))) ->
   getr (ms_regs msX) 19 = w64 (gSH cx fp) ->
   getr (ms_regs msX) 20 = w64 (hbase cx) ->
   getr (ms_regs msX) 21 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) ->
   getr (ms_regs msX) 22 = w64 (gF cx fp + GO_CH) ->
   getr (ms_regs msX) 23 = w64 (hwid cx) ->
   getr (ms_regs msX) 24 = w64 (gF cx fp + GO_A) ->
   ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
     [(GE_CID, fp)] ly3 S3 W3 (ms_mem msX) mdX kk ->
   SRr SEGS W3 (mkCfg msX mdX) (POST cx)).
{ intros msX mdX ssX HSX Hpcx Hrvx PX X2 X8 X9 X3 X4 X18 X19 X20 X21 X22 X23 X24 HJX.
  destruct (MEMOK msX PX) as (MSV & MSH & MFL & MIN & MSL & MMOD).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) E ssX msX HSX Hrvx) as Hshape.
  rewrite Hpcx in Hshape.
  eapply HMID; [exact HB | exact HJX | exact HFR | exact HMO |].
  unfold ah_GI. exists t.
  split.
  { unfold ge_body, gregs.
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split;
      [ split; [exact X2|]; split; [exact X8|]; split; [exact X9|];
        split; [exact X3 | exact X4] |].
    split; [exact MSV|]. split; [exact MSH|]. split; [exact MFL|].
    split; [exact Hlen | exact MIN]. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact HCN|].
  split; [exact X18|]. split; [exact X19|]. split; [exact X20|]. split; [exact X21|].
  split; [exact X22|]. split; [exact X23|]. split; [exact X24|].
  split; [|exact MMOD].
  unfold gslots_adm. repeat match goal with |- _ /\ _ => split end; apply MSL; assumption. }
(* the machine state as the engine's symbolic state at 0x81300 *)
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_admit))
  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E ah_ss0 (restrict (w_H W3) ms3)).
{ rewrite Hms. unfold ah_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold AH_Rsp. apply Forall_cons; [|apply Forall_nil].
    unfold YP09.region_ok; cbv zeta;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 24 8 (SOff 32 0) (hhi cx));
      [ rewrite at_denot_off0; exact F32 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact SL24 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 32 8 (SOff 33 0) (hwid cx));
      [ rewrite at_denot_off0; exact F33 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact SL32 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 48 8 (SOff 34 0)
               (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))));
      [ rewrite at_denot_off0; exact F34 | cbn [Z.of_N]; change (8 * 8) with 64; exact RN48
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact SL48 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 64 8 (SOff 35 0) (gF cx fp + GO_CH));
      [ rewrite at_denot_off0; exact F35 | cbn [Z.of_N]; change (8 * 8) with 64; exact RN64
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact SL64 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 88 8 (SOff 36 0) (hbase cx mod 2 ^ 64));
      [ rewrite at_denot_off0; exact F36
      | cbn [Z.of_N]; change (8 * 8) with 64; apply Z.mod_pos_bound; lia
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact SL88 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 120 8 (SOff 37 0) (gF cx fp + GO_A));
      [ rewrite at_denot_off0; exact F37 | cbn [Z.of_N]; change (8 * 8) with 64; exact RN120
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact SL120 ] |].
    apply Forall_nil.
  - unfold AH_Rsp. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - split; [exact I | split; exact I]. }
clear HE EE EX Hms.
(* 0x81300 .. 0x81310: the channel count against 40 *)
paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msA end.
assert (PA : forall x, ms_mem msA x = ms_mem ms3 x) by nowin HF.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* the count is 0 or more than 40: the box does not fit *)
  assert (Hf : fits (hbase cx) (hwid cx) = false).
  { apply adm_fits_false. intros (Hw & Hb0 & Hbw).
    rewrite branch_ltu_U, U_SLit, U_SOff, F33, unsigned_lit_small in Hc by lia.
    apply Z.ltb_lt in Hc. unfold zcanon, M64 in Hc.
    rewrite (Z.mod_small 39) in Hc by lia.
    rewrite (Z.mod_small (hwid cx + -1)) in Hc by lia. lia. }
  paj_run_to_shc RUNTOP HS HJ AH_PC; [first [apply awr_ok_nil | awr_ok_tac] |].
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msB end.
  assert (PB : forall x, ms_mem msB x = ms_mem msA x) by nowin HF.
  clear HF HFr HG.
  assert (PB3 : forall x, ms_mem msB x = ms_mem ms3 x) by (intros x; rewrite PB; apply PA).
  eapply (ATMID msB _ _ HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) PB3);
    [ regval HS | regval HS | regval HS
    | rewrite Hgp0; regval HS | rewrite Htp0; regval HS
    | rewrite Eok, Hf; cbn [Z.b2z]; regsv HS; reflexivity
    | regval HS
    | replace (w64 (hbase cx)) with (w64 (hbase cx mod 2 ^ 64))
        by (unfold w64; apply ah_mod64); regval HS
    | regval HS | regval HS | regval HS | regval HS | exact HJ ].
- (* the count is between 1 and 40 *)
  assert (Hw : 1 <= hwid cx <= 40).
  { rewrite branch_ltu_U, U_SLit, U_SOff, F33, unsigned_lit_small in Hc by lia.
    apply Z.ltb_ge in Hc. unfold zcanon, M64 in Hc.
    rewrite (Z.mod_small 39) in Hc by lia.
    assert (Hne : hwid cx <> 0).
    { intros E0. rewrite E0 in Hc.
      change ((0 + -1) mod 2 ^ 64) with (2 ^ 64 - 1) in Hc. lia. }
    rewrite (Z.mod_small (hwid cx + -1)) in Hc by lia. lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msB end.
  assert (PB : forall x, ms_mem msB x = ms_mem msA x) by nowin HF.
  clear HF HFr HG.
  assert (PB3 : forall x, ms_mem msB x = ms_mem ms3 x) by (intros x; rewrite PB; apply PA).
  psrr_branch_pi RUNP BR HS.
  + (* the base is negative: the box does not fit *)
    rewrite ah_branch_lt, S_SAlu, S_SLit, U32, U_SLit in Hc.
    cbn [zalu_raw] in Hc.
    assert (Hneg : hbase cx < 0).
    { destruct (Z_lt_le_dec (hbase cx) 0) as [Hlt | Hge]; [exact Hlt | exfalso].
      assert (Hu : hu16 cx < 32768) by (apply Rs; lia).
      assert (Hh : hhi cx < 32768) by (apply adm_hi_lt; lia).
      change (Z.land (zcanon 48) 63) with 48 in Hc.
      rewrite Z.shiftl_mul_pow2 in Hc by lia.
      unfold bv_swrap, bv_wrap in Hc.
      change (bv_modulus 64) with (2 ^ 64) in Hc.
      change (bv_half_modulus 64) with (2 ^ 63) in Hc.
      rewrite (Z.mod_small (hhi cx * 2 ^ 48 + 2 ^ 63)) in Hc by lia.
      rewrite (Z.mod_small (0 + 2 ^ 63)) in Hc by lia.
      apply Z.ltb_lt in Hc. lia. }
    assert (Hf : fits (hbase cx) (hwid cx) = false)
      by (apply adm_fits_false; intros (_ & Hb0 & _); lia).
    paj_run_to_shc RUNTOP HS HJ AH_PC; [first [apply awr_ok_nil | awr_ok_tac] |].
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msD end.
    assert (PD : forall x, ms_mem msD x = ms_mem msB x) by nowin HF.
    clear HF HFr HG.
    assert (PD3 : forall x, ms_mem msD x = ms_mem ms3 x) by (intros x; rewrite PD; apply PB3).
    eapply (ATMID msD _ _ HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) PD3);
      [ regval HS | regval HS | regval HS
      | rewrite Hgp0; regval HS | rewrite Htp0; regval HS
      | rewrite Eok, Hf; cbn [Z.b2z]; regsv HS; reflexivity
      | regval HS
      | replace (w64 (hbase cx)) with (w64 (hbase cx mod 2 ^ 64))
          by (unfold w64; apply ah_mod64); regval HS
      | regval HS | regval HS | regval HS | regval HS | exact HJ ].
  + (* the base is not negative: the rule is base + count against 48 *)
    rewrite ah_branch_lt, S_SAlu, S_SLit, U32, U_SLit in Hc.
    cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 48) 63) with 48 in Hc.
    rewrite Z.shiftl_mul_pow2 in Hc by lia.
    unfold bv_swrap, bv_wrap in Hc.
    change (bv_modulus 64) with (2 ^ 64) in Hc.
    change (bv_half_modulus 64) with (2 ^ 63) in Hc.
    rewrite (Z.mod_small (0 + 2 ^ 63)) in Hc by lia.
    apply Z.ltb_ge in Hc.
    assert (Hh : hhi cx < 32768).
    { destruct (Z_lt_le_dec (hhi cx) 32768) as [Hlt | Hge]; [exact Hlt | exfalso].
      assert (Hmod : (hhi cx * 2 ^ 48 + 2 ^ 63) mod 2 ^ 64 = hhi cx * 2 ^ 48 - 2 ^ 63).
      { replace (hhi cx * 2 ^ 48 + 2 ^ 63) with ((hhi cx * 2 ^ 48 - 2 ^ 63) + 1 * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      rewrite Hmod in Hc. lia. }
    assert (Hu : hu16 cx < 32768) by (apply adm_hi_lt; lia).
    assert (Hb0 : 0 <= hbase cx) by (apply Rs; exact Hu).
    assert (Hfit : fits (hbase cx) (hwid cx) = (hbase cx + hwid cx <=? 48)).
    { unfold fits.
      replace (1 <=? hwid cx) with true by (symmetry; apply Z.leb_le; lia).
      replace (hwid cx <=? 40) with true by (symmetry; apply Z.leb_le; lia).
      replace (0 <=? hbase cx) with true by (symmetry; apply Z.leb_le; lia).
      cbn [andb]. reflexivity. }
    assert (Hz : zcanon (if bv_swrap 64 (zcanon (hbase cx + hwid cx)) <? bv_swrap 64 (zcanon 49)
                         then 1 else 0) = Z.b2z (hbase cx + hwid cx <=? 48)).
    { assert (Hs1 : bv_swrap 64 (zcanon (hbase cx + hwid cx)) = hbase cx + hwid cx).
      { unfold zcanon, M64, bv_swrap, bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
        rewrite (Z.mod_small (hbase cx + hwid cx)) by lia.
        rewrite (Z.mod_small (hbase cx + hwid cx + 2 ^ 63)) by lia. lia. }
      assert (Hs2 : bv_swrap 64 (zcanon 49) = 49).
      { unfold zcanon, M64, bv_swrap, bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
        rewrite (Z.mod_small 49) by lia. rewrite (Z.mod_small (49 + 2 ^ 63)) by lia. lia. }
      rewrite Hs1, Hs2. unfold zcanon, M64.
      destruct (Z.ltb_spec (hbase cx + hwid cx) 49) as [Hlt | Hge].
      - replace (hbase cx + hwid cx <=? 48) with true by (symmetry; apply Z.leb_le; lia).
        cbn [Z.b2z]. apply Z.mod_small. lia.
      - replace (hbase cx + hwid cx <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
        cbn [Z.b2z]. apply Z.mod_small. lia. }
    paj_run_to_shc RUNTOP HS HJ AH_PC; [first [apply awr_ok_nil | awr_ok_tac] |].
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msE end.
    assert (PE : forall x, ms_mem msE x = ms_mem msB x) by nowin HF.
    clear HF HFr HG.
    assert (PE3 : forall x, ms_mem msE x = ms_mem ms3 x) by (intros x; rewrite PE; apply PB3).
    eapply (ATMID msE _ _ HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) PE3);
      [ regval HS | regval HS | regval HS
      | rewrite Hgp0; regval HS | rewrite Htp0; regval HS
      | rewrite Eok, Hfit; regsv HS;
        rewrite denot_lit_U, !U_SAlu, U36, U33, U_SLit;
        rewrite (Z.mod_small (hbase cx)) by lia;
        (* the engine keeps image B's `add a0,s4,s7` as width + base *)
        cbn [zalu_raw]; rewrite (Z.add_comm (hwid cx) (hbase cx)), Hz; reflexivity
      | regval HS
      | replace (w64 (hbase cx)) with (w64 (hbase cx mod 2 ^ 64))
          by (unfold w64; apply ah_mod64); regval HS
      | regval HS | regval HS | regval HS | regval HS | exact HJ ].
Qed.

(* ---- 0x8136c .. 0x81390: mark `a` usable, zero it, call reac_grant_allocate and check ---- *)
Theorem ge_admit_tail : forall POST,
  ge_from B MT POST (GI_sweep B MT) -> ge_from B MT POST (GI_mid).
Proof.
intros POST HNEXT cx fp kk acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & HBODY & Hk & Hacc & HBLK & HCN & R18 & R19 & R20 & R21 & R22 & R23 & R24
                 & SLOTS & HMOD).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL
                     & Hlen & HIN).
pose proof SLOTS as (SL0 & SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & SL64 & SL72 & SL80 & SL88 & SL96 & SL104
                     & SL112 & SL120 & SL128 & SL136 & SL144 & SL152).
destruct HMOD as (HTAB & HWAS & HSET & HREL & HI1).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO. rewrite IMG_LO_B_val in HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (at_gsp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16).
unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp.
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & Hinp & _).
pose proof (adm_hdr_ranges (c_pl cx)) as (Ru & Rb & Ri & Rr & Rs).
assert (Eok : GrantSlotPlan.ok (c_pl cx) = fits (hbase cx) (hwid cx)) by reflexivity.
pose proof HJ as (HAR & Hly & _).
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF1 & HF2 & _).
assert (EgF : gF cx fp = frame_addr ly3 GE_CID fp)
  by (symmetry; exact (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 kk HB HJ)).
rewrite <- EgF in HF1, HF2. change (fs_frame_bytes GE_CID) with 1024 in HF2.
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HAR Hfin) as (HFal & HFia & HFpres & HFSpres).
rewrite <- EgF in HFal, HFia, HFpres, HFSpres.
change (fs_frame_bytes GE_CID) with 1024 in HFia, HFpres.
change (fs_frame_bytes GE_CID / 8) with 128 in HFSpres.
assert (HshA : shadow_addr (gF cx fp) = gSH cx fp)
  by (unfold shadow_addr, gSH, shadow_of_addr; reflexivity).
rewrite HshA in HFSpres.
assert (HSHeq : gSH cx fp = SHADOW_OFF + gF cx fp / 8) by reflexivity.
assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (Hm8 : gF cx fp mod 8 = 0).
{ pose proof HFal as H32. apply Z.mod_divide in H32; [|lia]. destruct H32 as [q Hq].
  apply Z.mod_divide; [lia|]. exists (4 * q). lia. }
pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as Hq8. rewrite Hm8, Z.add_0_r in Hq8.
assert (Hs16 : c_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as Hdm. rewrite Hsp32, Z.add_0_r in Hdm. rewrite Hdm.
  replace (32 * (c_sp1 cx / 32)) with ((c_sp1 cx / 32 * 2) * 16) by lia. apply Z_mod_mult. }
assert (GEOF : gF cx fp + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= gF cx fp)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; lia).
assert (GEOS : 0x7fff8000 <= gSH cx fp /\ gSH cx fp + 128 <= 0x10007fef8080)
  by (rewrite HSHeq; unfold SHADOW_OFF; lia).
pose proof (frm_off_imgB B ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as HFo.
rewrite <- EgF in HFo. change (fs_frame_bytes GE_CID) with 1024 in HFo.
assert (Htin : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ t 460 HAR Htin) as (_ & Ht4096 & Htceil & Htapp & _).
change (req_size 460) with 460 in Htceil, Htapp.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ t 460 GE_CID fp HAR Htin Hfin) as Htd.
rewrite <- EgF in Htd. change (req_size 460) with 460 in Htd.
change (fs_frame_bytes GE_CID) with 1024 in Htd.
unfold zdisjoint in Htd. cbn [fst snd] in Htd.
unfold in_app, kLowShadowBeg, kHighMemBeg in Htapp.
(* the caller's input block *)
assert (HINP : c_n cx = 0 \/
  (In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ c_p cx + c_n cx <= alloc_ceiling /\
   c_n cx <= req_size (c_n cx) /\ 4096 <= c_p cx /\
   (c_p cx + req_size (c_n cx) <= 0x7fff7000 \/ 0x10007fff8000 <= c_p cx) /\
   (c_p cx + req_size (c_n cx) <= gF cx fp \/ gF cx fp + 1024 <= c_p cx))).
{ destruct Hinp as [(Hn0 & _) | (Hn & Hin0)]; [left; exact Hn0 | right].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & Happ & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ GE_CID fp HAR Hin3 Hfin) as Hd.
  rewrite <- EgF in Hd. change (fs_frame_bytes GE_CID) with 1024 in Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  split; [exact Hin3|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Hd]. }
(* Every byte the cut's facts speak about lies outside the two windows the run writes. *)
assert (GEO : forall a, admZ cx fp t a ->
  0 <= a < 2 ^ 64 /\ ~ (gSH cx fp + 56 <= a < gSH cx fp + 57) /\
  ~ (gF cx fp + 448 <= a < gF cx fp + 450)).
{ (* measured at 260 s in the whole context; these twelve facts are all it needs *)
  clear - C1 Hsp Hsp1 HF1 HF2 GEOF GEOS HINP Htapp Htd Ht4096 Htceil.
  intros a Ha. unfold admZ in Ha.
  destruct Ha as [Ha | [Ha | [[Ha Hx] | [[Ha Hx] | Ha]]]].
  - lia.
  - destruct HINP as [Hn0 | (_ & Hpc1 & Hrq & Hp4 & Hpa & Hpd)]; lia.
  - lia.
  - lia.
  - lia. }
(* the environment of the run *)
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r Hq; subst E; apply at_ewR; exact Hq).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx))))
  by (rewrite (EE 18%nat 18%bv eq_refl), R18, Eok; reflexivity).
assert (F19 : ew E 19 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (F20 : ew E 20 = Z_to_bv 64 (hbase cx)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (F21 : ew E 21 = Z_to_bv 64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (F22 : ew E 22 = Z_to_bv 64 (gF cx fp + GO_CH)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (F23 : ew E 23 = Z_to_bv 64 (hwid cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (F24 : ew E 24 = Z_to_bv 64 (gF cx fp + 448))
  by (rewrite (EE 24%nat 24%bv eq_refl); unfold GO_A in R24; exact R24).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = gSH cx fp) by (rewrite F19; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = gF cx fp + 448) by (rewrite F24; apply unsigned_lit_small; lia).
(* the machine state as the engine's symbolic state at 0x8136c *)
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_mid))
  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E at_ss0 (restrict (w_H W3) ms3)).
{ rewrite Hms. unfold at_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold AT_Rsh, AT_Ra.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold YP09.region_ok; cbv zeta;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    + rewrite U19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite U24. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFpres (gF cx fp + 448 + o) ltac:(lia))).
  - unfold AT_Rsh, AT_Ra. cbn [YP09.pairwise_disjoint YP09.all_disjoint]; repeat split;
      unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
      rewrite ?U19, ?U24; clear - GEOF GEOS HF1 HF2 C1; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|split; [|exact I]];
      unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?U9, ?U24; change (2 ^ 5) with 32.
    + split; [lia|]. split; [exact Hsp32 | lia].
    + split; [lia|]. split; [|lia]. rewrite Z.add_mod, HFal by lia. reflexivity. }
clear HE EE.
(* ---- 0x8136c .. 0x81384: mark `a` usable, zero it, and call reac_grant_allocate ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (gSH cx fp)); [reflexivity | exact U19 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists GE_CID, fp.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite <- EgF, HshA. change (fs_frame_bytes GE_CID / 8) with 128. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 24%nat (gF cx fp + 448)); [reflexivity | exact U24 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists GE_CID, fp.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite <- EgF. change (fs_frame_bytes GE_CID) with 1024. lia. }
  apply awr_ok_nil. }
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msN) |- _ => rename msN into msC end.
rename HF into HFC. rename HFr into HFrC. clear HG.
(* What the run kept: every byte of the cut's facts. *)
assert (KA : admKeep cx fp t W3 (ms_mem ms3) (ms_mem msC)).
{ intros a Ha. destruct (GEO a Ha) as (Ha64 & N1 & N2).
  apply (at_keep_outside E _ _ _ (w_H W3) a HFC Ha64).
  intros (r & Hr & Hb). unfold at_ss0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold AT_Rsh, AT_Ra in Hb;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U19, ?U24 in Hb; lia. }
(* What the run wrote: the shadow byte 2 at s3 + 56 and the two zero bytes of `a`. *)
pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as RG1.
assert (V56 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (gSH cx fp + 56) 1 2).
{ apply (field_of_region E _ 19%nat (gSH cx fp) _ _ _ _ _ 56 1%N (SLit 2) 2 RG0 U19);
    [cbn [In]; left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
assert (VA : val_mem SEGS (mrestrict (w_H W3) (ms_mem msC)) (gF cx fp + 448 + 0) 2 0).
{ apply (field_of_region E _ 24%nat (gF cx fp + 448) _ _ _ _ _ 0 2%N (SLit 0) 0 RG1 U24);
    [cbn [In]; left; reflexivity | reflexivity | cbn; lia | cbn; lia]. }
rewrite Z.add_0_r in VA.
assert (A56 : aview SEGS (w_H W3) (ms_mem msC) (gSH cx fp + 56) = Some 2)
  by (apply (aview_of_val_mem1 SEGS); [exact V56 | lia]).
(* the registers at the call *)
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
rewrite pa_sigma_reac_grant_allocate.
assert (Qsp : spZ (ms_regs msC) = c_sp1 cx)
  by (unfold spZ; rewrite Q2, F2; apply unsigned_lit_small; lia).
pose proof HJ as (HARC & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HARC Hfin) as (_ & _ & HFpresC & _).
rewrite <- EgF in HFpresC. change (fs_frame_bytes GE_CID) with 1024 in HFpresC.
(* the premises of reac_grant_allocate's contract that rule out NULL and image B for `a` *)
assert (POFF : gF cx fp + 448 + 2 <= IMG_LO_B \/ IMG_TOP_B <= gF cx fp + 448)
  by (destruct HFo as [Ho | Ho]; [left | right]; lia).
assert (PAPP : forall x, gF cx fp + 448 <= x < gF cx fp + 448 + 2 -> app_addr x)
  by (intros x Hx; apply (in_app_addr (gF cx fp) 1024 x HFia); lia).
assert (TWR : twr_ok B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) ly3 S3 [(GE_CID, fp)] W3
  (ms_mem msC) (spZ (ms_regs msC)) (gF cx fp + 448) 2).
{ intros a Ha. split; [|split; [|split]].
  - right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite <- EgF. change (fs_frame_bytes GE_CID) with 1024. lia.
  - exact (proj1 (HFpresC a ltac:(lia))).
  - exact (proj2 (HFpresC a ltac:(lia))).
  - rewrite Qsp. unfold ESTACK. lia. }
assert (RAD : bytes_ok W3 (ms_mem msC) (gF cx fp + 448) 2).
{ intros x Hx.
  assert (Hx8 : x / 8 = gF cx fp / 8 + 56).
  { symmetry. apply (Z.div_unique x 8 (gF cx fp / 8 + 56) (x - 8 * (gF cx fp / 8 + 56)));
      [left; lia | lia]. }
  exists 2. split.
  - unfold shadow_of_addr. rewrite Hx8.
    replace (SHADOW_OFF + (gF cx fp / 8 + 56)) with (gSH cx fp + 56) by lia.
    exact A56.
  - right. split; [|lia]. rewrite Z.mod_eq by lia. rewrite Hx8. lia. }
assert (GA0 : garr8 SEGS (mrestrict (w_H W3) (ms_mem msC)) (gF cx fp + 448) [0; 0])
  by (apply at_val2_garr8; exact VA).
eapply SRr_bind.
{ exact (HALLOC GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 _ _ kk (ms_regs msC) (gF cx fp + 448) (hbase cx) (hwid cx) 0 0 HJ
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
    ltac:(rewrite Q3, F3; reflexivity) ltac:(rewrite Q4, F4; reflexivity)
    ltac:(rewrite Q10, F24; reflexivity) ltac:(rewrite Q11, F20; reflexivity)
    ltac:(rewrite Q12, F23; reflexivity)
    ltac:(unfold int32; lia) ltac:(unfold int32; lia) ltac:(intros; lia)
    ltac:(rewrite Qsp; exact Hs16)
    ltac:(rewrite Qsp; unfold STK_reac_grant_allocate, ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput; lia)
    ltac:(rewrite Qsp; lia)
    ltac:(lia) ltac:(rewrite Qsp; right; unfold STK_reac_grant_allocate, ESTACK; lia)
    POFF PAPP TWR RAD GA0). }
(* ---- after the call ---- *)
intros W2 c2 _ (EW & regs2 & mem2 & md2 & Ec2 & HJ2 & HP2 & Ha0 & Hga & HKT). subst W2 c2.
rewrite Qsp in HKT. destruct HKT as (K1 & K2 & K3 & K4 & K5 & K6).
(* What the call kept: every byte of the cut's facts, and the shadow byte of `a`. *)
assert (KC : admKeep cx fp t W3 (ms_mem msC) mem2).
{ intros a Ha. destruct (GEO a Ha) as (Ha64 & N1 & N2).
  unfold admZ in Ha. destruct Ha as [Ha | [Ha | [[Ha Hx] | [[Ha Hx] | Ha]]]].
  - apply K1; [lia | unfold STK_reac_grant_allocate, ESTACK; lia | cbv beta; lia].
  - destruct HINP as [Hn0 | (Hin3 & Hpc1 & Hrq & Hp4 & Hpa & Hpd)]; [lia|].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin3); [lia | cbv beta; lia].
  - apply (K4 GE_CID fp a Hfin); [|cbv beta; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EgF.
    change (fs_frame_bytes GE_CID) with 1024. lia.
  - apply (K4 GE_CID fp a Hfin); [|cbv beta; lia].
    right. unfold in_zr. cbn [fst snd]. rewrite <- EgF, HshA.
    change (fs_frame_bytes GE_CID / 8) with 128. lia.
  - replace a with (t + (a - t)) by lia.
    apply (K2 t 460 (a - t) Htin); [change (req_size 460) with 460; lia | cbv beta; lia]. }
assert (A56b : aview SEGS (w_H W3) mem2 (gSH cx fp + 56) = Some 2).
{ rewrite <- A56. apply (K4 GE_CID fp _ Hfin); [|cbv beta; clear - GEOF GEOS; lia].
  right. unfold in_zr. cbn [fst snd]. rewrite <- EgF, HshA.
  change (fs_frame_bytes GE_CID / 8) with 128. lia. }
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W3) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite Q1.
remember (havoc E 33 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall q, (q < 33)%nat -> ew E1 q = ew E q)
  by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
assert (F37 : ew E1 37 = Z_to_bv 64 (if fits (hbase cx) (hwid cx) then 0 else -1)).
{ rewrite HE1. change 37%nat with (33 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 33 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Ha0. }
clear HE1.
restate OLD1.
clear HJ. rename HJ2 into HJ.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ =>
  let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* ---- 0x81388 .. 0x8138c: s2 - 1 and the check ---- *)
paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msD end.
assert (PD : forall x, ms_mem msD x = mem2 x) by nowin HF.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ (* the branch into 0x81d98 is taken only if a0 <> s2 - 1, and both are the answer *)
  exfalso. rewrite branch_ne_U in Hc. apply (proj1 (Bool.negb_true_iff _)), Z.eqb_neq in Hc. apply Hc.
  rewrite !U_SOff.
  repeat match goal with F : ew E1 18 = _ |- _ => rewrite F end.
  rewrite F37.
  destruct (fits (hbase cx) (hwid cx)); vm_compute; reflexivity. }
paj_run_to_shc RUNTOP HS HJ GP_sweep; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msF end.
assert (PF : forall x, ms_mem msF x = ms_mem msD x) by nowin HF.
clear HF HFr HG.
(* ---- 0x81390: GI_sweep ---- *)
assert (PM : forall x, ms_mem msF x = mem2 x) by (intros x; rewrite PF; apply PD).
assert (KD : admKeep cx fp t W3 mem2 (ms_mem msF)) by (apply admKeep_pw; exact PM).
assert (AVF : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem2 a)
  by (intros a; unfold aview, mbyte, mrestrict; rewrite PM; reflexivity).
assert (KT : admKeep cx fp t W3 (ms_mem ms3) (ms_mem msF))
  by (eapply admKeep_trans; [exact KA | eapply admKeep_trans; [exact KC | exact KD]]).
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Lws & Lst & _).
assert (MSV : gsaved cx W3 msF).
{ destruct HSV as (Hra & Hsj). split.
  - eapply (admK_rdword _ _ _ _ _ _ _ _ KT); [intros i Hi; unfold admZ; left; lia | exact Hra].
  - intros j Hj. eapply (admK_rdword _ _ _ _ _ _ _ _ KT);
      [intros i Hi; unfold admZ; left; lia | exact (Hsj j Hj)]. }
assert (MSH : gshadow cx fp W3 msF GSH_a).
{ intros i Hi. rewrite gsh_a_len in Hi.
  destruct (Nat.eq_dec i 56) as [-> | Hne].
  - rewrite gsh_a_56. change (Z.of_nat 56) with 56. rewrite AVF. exact A56b.
  - rewrite (gsh_a_other i Hi Hne). rewrite (KT (gSH cx fp + Z.of_nat i)).
    + apply HSH. rewrite gsh_tables_len. exact Hi.
    + unfold admZ. right; right; right; left. clear - Hi Hne. split; lia. }
assert (MFL : rdword (aview SEGS (w_H W3) (ms_mem msF)) (gF cx fp + 1016) = Some (gFL cx fp)).
{ eapply (admK_rdword _ _ _ _ _ _ _ _ KT); [|exact HFL].
  intros i Hi. unfold admZ. right; right; left. split; lia. }
assert (MIN : garr8 SEGS (mrestrict (w_H W3) (ms_mem msF)) (c_p cx)
                (map (fun b : byte => bv_unsigned b) (c_pl cx))).
{ eapply (admK_garr8 _ _ _ _ _ _ _ _ KT); [|exact HIN].
  intros i Hi. rewrite length_map in Hi. unfold admZ, c_n. right; left. lia. }
assert (KSL : forall off v, (0 <=? off) && (off <=? 184) = true -> gslot cx W3 ms3 off v ->
  rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + off) = Some v).
{ intros off v Ho Hv. unfold gslot in Hv. apply andb_prop in Ho as [Ho1 Ho2].
  apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
  eapply (admK_rdword _ _ _ _ _ _ _ _ KT); [intros i Hi; unfold admZ; left; lia | exact Hv]. }
assert (MAB : if GrantSlotPlan.ok (c_pl cx)
   then gfb cx fp W3 msF GO_A (hbase cx) /\ gfb cx fp W3 msF (GO_A + 1) (hwid cx)
   else gfb cx fp W3 msF GO_A 0 /\ gfb cx fp W3 msF (GO_A + 1) 0).
{ rewrite Eok. unfold gfb, GO_A. rewrite !AVF.
  destruct (fits (hbase cx) (hwid cx)) eqn:Ef.
  - pose proof (proj1 (adm_fits_spec _ _) Ef) as (Hw & Hb0 & Hbw).
    assert (Hga' : garr8 SEGS (mrestrict (w_H W3) mem2) (gF cx fp + 448)
                     [hbase cx mod 256; hwid cx mod 256])
      by (first [exact Hga | rewrite Ef in Hga; exact Hga]).
    destruct (Hga' 0%nat ltac:(cbn; lia)) as [Hv0 Hr0].
    destruct (Hga' 1%nat ltac:(cbn; lia)) as [Hv1 Hr1].
    cbn [nth] in Hv0, Hr0, Hv1, Hr1. change (Z.of_nat 0) with 0 in Hv0. rewrite Z.add_0_r in Hv0.
    change (Z.of_nat 1) with 1 in Hv1.
    rewrite (Z.mod_small (hbase cx) 256) in Hv0 by lia.
    rewrite (Z.mod_small (hwid cx) 256) in Hv1 by lia.
    split; [apply (aview_of_val_mem1 SEGS); [exact Hv0 | lia]|].
    replace (gF cx fp + (448 + 1)) with (gF cx fp + 448 + 1) by lia.
    apply (aview_of_val_mem1 SEGS); [exact Hv1 | lia].
  - assert (Hga' : garr8 SEGS (mrestrict (w_H W3) mem2) (gF cx fp + 448) [0; 0])
      by (first [exact Hga | rewrite Ef in Hga; exact Hga]).
    destruct (Hga' 0%nat ltac:(cbn; lia)) as [Hv0 Hr0].
    destruct (Hga' 1%nat ltac:(cbn; lia)) as [Hv1 Hr1].
    cbn [nth] in Hv0, Hr0, Hv1, Hr1. change (Z.of_nat 0) with 0 in Hv0. rewrite Z.add_0_r in Hv0.
    change (Z.of_nat 1) with 1 in Hv1.
    split; [apply (aview_of_val_mem1 SEGS); [exact Hv0 | lia]|].
    replace (gF cx fp + (448 + 1)) with (gF cx fp + 448 + 1) by lia.
    apply (aview_of_val_mem1 SEGS); [exact Hv1 | lia]. }
pose proof HTAB as (Tin & Tpos & Tlen & Tb).
assert (MTAB : gtab B cx ly3 S3 W3 msF t (GrantSlotPlan.T_end (c_pl cx))).
{ split; [exact Tin|]. split; [exact Tpos|]. split; [exact Tlen|].
  intros i Hi H1 H2 H3. rewrite (KT (t + i)); [exact (Tb i Hi H1 H2 H3)|].
  unfold admZ. right; right; right; right. lia. }
assert (MWAS : gfarr cx fp W3 msF GO_WAS (GrantSlotPlan.ws_end (c_pl cx))).
{ unfold gfarr in *. eapply (admK_garr8 _ _ _ _ _ _ _ _ KT); [|exact HWAS].
  intros i Hi. rewrite length_map, Lws in Hi. unfold admZ, GO_WAS. right; right; left. split; lia. }
assert (MSET : gfarr cx fp W3 msF GO_SET (GrantSlotPlan.st_end (c_pl cx))).
{ unfold gfarr in *. eapply (admK_garr8 _ _ _ _ _ _ _ _ KT); [|exact HSET].
  intros i Hi. rewrite length_map, Lst in Hi. unfold admZ, GO_SET. right; right; left. split; lia. }
pmkst HS.
eapply HNEXT; [exact HB | exact HJ | exact HFR | exact HMO |].
unfold GI_sweep. exists t.
split.
{ unfold ge_body, gregs.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [ split; [regval HS|]; split; [regval HS|]; split; [regval HS|];
           split; [rewrite Hgp0; regval HS | rewrite Htp0; regval HS] |].
  split; [exact MSV|]. split; [exact MSH|]. split; [exact MFL|].
  split; [exact gsh_a_len | exact MIN]. }
split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact HCN|].
split; [regval HS|]. split; [regval HS|]. split; [regval HS|]. split; [regval HS|].
split; [regval HS|]. split; [regval HS|].
split.
{ regsv HS. cbn [sv_denot].
  repeat match goal with F : ew E1 18 = _ |- _ => rewrite F end.
  rewrite Eok. destruct (fits (hbase cx) (hwid cx)); apply bv_eq; vm_compute; reflexivity. }
split.
{ regsv HS. rewrite at_denot_off0, F37, Eok. reflexivity. }
split; [exact MAB|].
(* the twenty spill slots, then the model of the input *)
repeat match goal with |- _ /\ _ => split end;
  [ .. | exact MTAB | exact MWAS | exact MSET | exact HREL | exact HI1 ];
  unfold gslot; cbn [ms_mem mkst]; (apply KSL; [reflexivity | assumption]).
Qed.

(* ---- the whole phase: image B 0x81300 .. 0x81390 ---- *)
Theorem ge_admit : forall POST,
  ge_from B MT POST (GI_sweep B MT) -> ge_from B MT POST (GI_admit B MT).
Proof.
intros POST HNEXT. apply ge_admit_head. exact (ge_admit_tail POST HNEXT).
Qed.
End c.
End b.
End a.
