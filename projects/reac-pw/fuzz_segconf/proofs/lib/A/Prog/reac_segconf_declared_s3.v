(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 602 of its 638 lines of code are new or changed and 417 lines of the source are left out. *)
(* Segment S3 of the ASan image-A walk of reac_segconf_declared (fuzz_segconf.asan, interface
   reac_segconf_declared_d.v): from the cut KA i (0x89a00), where reac_declared_vlan_split answered 1, through
   the load of the vid (lhu 0x89a00), the reload of tab / max / n from 32/40/48(s1), the call of
   reac_declared_vlan_add at 0x89a14 (cl_callS_wide, PaNoChain.v), and the edge `bltz a0` at 0x89a18 -- taken to
   0x89b54, which re-poisons parent and vid and leaves -1 in 56(s1) before joining KX (0x89a78), not taken to
   the count update 0x89a1c-0x89a24 and the re-poison 0x89a28-0x89a30 that falls into KT i (0x89a34). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI67 YG0s YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot PaSB
PaNoChain PaCallRun PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegBase SegObj SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem reac_segconf_declared_s3a reac_segconf_declared_s3b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at KA: the registers themselves, the vid cell at s11 (atom 32 = v) and the three argument
   words at 32/40/48(s1) (atoms 33 / 34 / 35 = tab / max / n), all read-only *)
Definition dcs3_rvid : YP09.region :=
YP09.mkRegion (Some 27%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 2 (SOff 32 0))].
Definition dcs3_rs1 : YP09.region :=
YP09.mkRegion (Some 9%nat) 32 56 0 0
[YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0))].
Definition ss_dcs3A : sstate := mkSS DC_KA sr_atoms [dcs3_rvid; dcs3_rs1] None (mkFacts [] [] []).

(* the symbolic state at the return of add (0x89a18): the running count at 56(s1) (atom 32 = added), writable,
   and the frame's 16 shadow bytes at s3, writable *)
Definition dcs3_rs1b : YP09.region :=
YP09.mkRegion (Some 9%nat) 56 64 56 64 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition dcs3_rsh : YP09.region := YP09.mkRegion (Some 19%nat) 0 16 0 16 [].
Definition ss_dcs3R : sstate := mkSS DC_RET sr_atoms [dcs3_rs1b; dcs3_rsh] None (mkFacts [] [] []).

(* the two arms after the call, with the answer pinned to each of the three numbers add can give *)
Definition ss_dcs3P (z : Z) : sstate :=
mkSS DC_RET (sr_set sr_atoms 10 (SLit z)) [dcs3_rs1b; dcs3_rsh] None (mkFacts [] [] []).

(* the 32-bit add of the running count: no wrap, the count stays small *)
Lemma dcs3_addw : forall E a b x y, U E a = x -> U E b = y ->
0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> x + y < 2 ^ 31 ->
U E (SAluw ALU_ADD a b) = x + y.
Proof.
intros E a b x y Ha Hb Hx Hy Hs.
rewrite U_of_S, S_SAluw, Ha, Hb. cbn [zalu_raw].
rewrite (Z.mod_small x (2 ^ 32)) by lia. rewrite (Z.mod_small y (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x + y + 2 ^ 31) (2 ^ 32)) by lia.
replace (x + y + 2 ^ 31 - 2 ^ 31) with (x + y) by lia.
apply Z.mod_small. lia.
Qed.

(* the two-byte zero-extending load of the vid *)
Lemma dcs3_zext16 : forall v, 0 <= v < 65536 ->
zext 64 (bv_extract 0 16 (Z_to_bv 64 v)) = Z_to_bv 64 v.
Proof.
intros v Hv. apply bv_eq.
rewrite (zext64_unsigned (bv_extract 0 16 (Z_to_bv 64 v)) ltac:(lia)).
rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. cbn [Z.of_N].
repeat (rewrite (Z.mod_small v) by lia). reflexivity.
Qed.

Ltac dcs3_cs := cbv [acallee_saved];
match goal with |- context [bv_unsigned ?x] =>
  let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition dcs3_EA (regs : bvmap 5 word) (v tab max n : Z) : env :=
Eimg (Ereg regs [w64 v; w64 tab; w64 max; w64 n]).
Definition dcs3_ER (regs : bvmap 5 word) (added : Z) : env := Eimg (Ereg regs [w64 added]).

Lemma dcs3_ea_reg : forall regs v tab max n k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (dcs3_EA regs v tab max n) k = getr regs r.
Proof. intros. unfold dcs3_EA. apply ew_Eimg_Ereg_nat. assumption. Qed.
Lemma dcs3_er_reg : forall regs added k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (dcs3_ER regs added) k = getr regs r.
Proof. intros. unfold dcs3_ER. apply ew_Eimg_Ereg_nat. assumption. Qed.
Lemma dcs3_ea_x : forall regs v tab max n j, (j < 4)%nat ->
ew (dcs3_EA regs v tab max n) (32 + j) = nth j [w64 v; w64 tab; w64 max; w64 n] (Z_to_bv 64 0).
Proof. intros. unfold dcs3_EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma dcs3_er_x : forall regs added j, (j < 1)%nat ->
ew (dcs3_ER regs added) (32 + j) = nth j [w64 added] (Z_to_bv 64 0).
Proof. intros. unfold dcs3_ER. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma dcs3_ea_32 : forall regs v tab max n, ew (dcs3_EA regs v tab max n) 32 = w64 v.
Proof. intros. change (32%nat) with (32 + 0)%nat. rewrite (dcs3_ea_x regs v tab max n 0 ltac:(lia)). reflexivity. Qed.
Lemma dcs3_ea_33 : forall regs v tab max n, ew (dcs3_EA regs v tab max n) 33 = w64 tab.
Proof. intros. change (33%nat) with (32 + 1)%nat. rewrite (dcs3_ea_x regs v tab max n 1 ltac:(lia)). reflexivity. Qed.
Lemma dcs3_ea_34 : forall regs v tab max n, ew (dcs3_EA regs v tab max n) 34 = w64 max.
Proof. intros. change (34%nat) with (32 + 2)%nat. rewrite (dcs3_ea_x regs v tab max n 2 ltac:(lia)). reflexivity. Qed.
Lemma dcs3_ea_35 : forall regs v tab max n, ew (dcs3_EA regs v tab max n) 35 = w64 n.
Proof. intros. change (35%nat) with (32 + 3)%nat. rewrite (dcs3_ea_x regs v tab max n 3 ltac:(lia)). reflexivity. Qed.
Lemma dcs3_er_32 : forall regs added, ew (dcs3_ER regs added) 32 = w64 added.
Proof. intros. change (32%nat) with (32 + 0)%nat. rewrite (dcs3_er_x regs added 0 ltac:(lia)). reflexivity. Qed.

Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Hypothesis ADD : forall fx0 : YK11.FPState,
  @reac_declared_vlan_add_contract fx0 rc SK SEGS B (BASE + AF_reac_declared_vlan_add) STK_reac_declared_vlan_add RLO RHI.
Hypothesis SIGP : seg_sig_prog.
Hypothesis ROIMG : dc_ro_imgP RLO RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* the symbolic state at KA, from the cut's facts *)
Lemma dcs3_seedA : forall (regs : bvmap 5 word) (W : world SEGS) mem v tab max n F s1,
getr regs 27 = w64 (F + 64) -> getr regs 9 = w64 s1 ->
0 <= v < 65536 -> 0 <= tab < 2 ^ 64 -> 0 <= max < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
0 <= F -> F + 128 <= s1 -> s1 + 56 <= 2 ^ 64 ->
sa_val (rdW W mem) (F + 64) 2 v ->
rdword (rdW W mem) (s1 + 32) = Some tab -> rdword (rdW W mem) (s1 + 40) = Some max ->
rdword (rdW W mem) (s1 + 48) = Some n ->
st_ok_pi SEGS VAL (dcs3_EA regs v tab max n) ss_dcs3A
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DC_KA)) mem (seg_rom SEGS))).
Proof using.
intros regs W mem v tab max n F s1 R27 R9 Hv Htab Hmax Hn HF0 HFs Hs1 HVAL H32 H40 H48.
set (E := dcs3_EA regs v tab max n).
assert (E27 : ew E 27 = w64 (F + 64)) by (unfold E; rewrite (dcs3_ea_reg regs v tab max n 27 27%bv eq_refl); exact R27).
assert (E9 : ew E 9 = w64 s1) by (unfold E; rewrite (dcs3_ea_reg regs v tab max n 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = w64 v) by (unfold E; exact (dcs3_ea_x regs v tab max n 0 ltac:(lia))).
assert (E33 : ew E 33 = w64 tab) by (unfold E; exact (dcs3_ea_x regs v tab max n 1 ltac:(lia))).
assert (E34 : ew E 34 = w64 max) by (unfold E; exact (dcs3_ea_x regs v tab max n 2 ltac:(lia))).
assert (E35 : ew E 35 = w64 n) by (unfold E; exact (dcs3_ea_x regs v tab max n 3 ltac:(lia))).
assert (U27 : base_val E (Some 27%nat) = F + 64)
  by (cbn [base_val]; rewrite E27; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : base_val E (Some 9%nat) = s1)
  by (cbn [base_val]; rewrite E9; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_dcs3A. apply pa_entry_st_ok_full.
- unfold E, dcs3_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dcs3_rvid, dcs3_rs1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (F + 64) 0 2 (SOff 32 0) v).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn. lia.
    * cbn. lia.
    * rewrite Z.add_0_r. apply (dcs3_val_mem SEGS (w_H W) mem (F + 64) 2 v). exact HVAL.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons; [|]); try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 32 8 (SOff 33 0) tab);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS (w_H W) mem (s1 + 32) tab). exact H32.
    * apply (chunk_ok_val SEGS E _ s1 40 8 (SOff 34 0) max);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS (w_H W) mem (s1 + 40) max). exact H40.
    * apply (chunk_ok_val SEGS E _ s1 48 8 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS (w_H W) mem (s1 + 48) n). exact H48.
- apply pairwise_disjoint_of_extents. unfold dcs3_rvid, dcs3_rs1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U27, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; [exact I | exact I]].
Qed.

(* the symbolic state at the return of add *)
Lemma dcs3_seedR : forall (regs : bvmap 5 word) (W : world SEGS) mem added F s1,
getr regs 9 = w64 s1 -> getr regs 19 = w64 (SB + F / 8) ->
0 <= added < 2 ^ 64 -> 0 <= F -> SB + F / 8 + 16 <= s1 -> s1 + 64 <= 2 ^ 64 ->
rdword (rdW W mem) (s1 + 56) = Some added ->
(forall o, 56 <= o < 64 -> writable_at SEGS (mrestrict (w_H W) mem) (s1 + o)) ->
(forall o, 0 <= o < 16 -> writable_at SEGS (mrestrict (w_H W) mem) (SB + F / 8 + o)) ->
st_ok_pi SEGS VAL (dcs3_ER regs added) ss_dcs3R
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DC_RET)) mem (seg_rom SEGS))).
Proof using.
intros regs W mem added F s1 R9 R19 Hadd HF0 HFs Hs1 H56 HW1 HW2.
set (E := dcs3_ER regs added).
assert (E9 : ew E 9 = w64 s1) by (unfold E; rewrite (dcs3_er_reg regs added 9 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = w64 (SB + F / 8))
  by (unfold E; rewrite (dcs3_er_reg regs added 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = w64 added) by (unfold E; exact (dcs3_er_x regs added 0 ltac:(lia))).
assert (HSB : 0 <= SB + F / 8) by (pose proof (Z.div_pos F 8 HF0 ltac:(lia)); unfold SB; lia).
assert (U9 : base_val E (Some 9%nat) = s1)
  by (cbn [base_val]; rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : base_val E (Some 19%nat) = SB + F / 8)
  by (cbn [base_val]; rewrite E19; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_dcs3R. apply pa_entry_st_ok_full.
- unfold E, dcs3_ER. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dcs3_rs1b, dcs3_rsh. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW1; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ s1 56 8 (SOff 32 0) added);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    apply (val_mem_of_rdword SEGS (w_H W) mem (s1 + 56) added). exact H56.
  + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW2; lia | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold dcs3_rs1b, dcs3_rsh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U9, U19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; [exact I | exact I]].
Qed.


(* add's post, the part this segment uses *)
Definition dcs3_Q (c : dcx) (ti : list (list Z * Z)) (p : list Z) (v : Z) (ly3 : alayout) (S3 : astate)
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
  getr regs' 10 = w64 (fst (vlan_add ti (x_max c) p v)) /\
  sa_rtab (rdW W' mem') (x_tab c) (snd (vlan_add ti (x_max c) p v)) /\
  sa_val (rdW W' mem') (x_n c) 4 (Z.of_nat (length (snd (vlan_add ti (x_max c) p v)))) /\
  sa_noalloc B ly3 S3 ly' S'.

Lemma dc_S3 : dc_S3P B STK_reac_segconf_declared RLO RHI GOTW GUARD.
Proof using ADD LAWS RO ROIMG SIGP.
intros c i HPRE HKT HKX ti added p v ly3 S3 W3 regs3 mem3 md3 HINV.
pose proof HINV as HKA0.
destruct HINV as (HFI & HUN & HTAB & Hi & HLOOP & HLR & H56 & Hign & Hsp & Hstrz & Hvid & Hsh4 & Hsh5 & Hsh8).
destruct HLR as (R23 & R22 & R25 & R24 & R21 & R26 & R27 & R18).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F19 F20 Fsaved Ff16 Ff24 Ftab Fmax Fn Fflag].
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs3 & Hnev3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HB0. pose proof (pa_base_lo (PL := PL_seg)) as HBLO.
pose proof (cp_afn _ _ _ _ _ _ _ HPRE) as HAFN.
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (cp_nev _ _ _ _ _ _ _ HPRE) as Hnev0.
pose proof (cp_tab64 _ _ _ _ _ _ _ HPRE) as Htab64.
pose proof (cp_max64 _ _ _ _ _ _ _ HPRE) as Hmax64.
pose proof (cp_n64 _ _ _ _ _ _ _ HPRE) as Hn64.
pose proof (cp_a1 _ _ _ _ _ _ _ HPRE) as Ha1.
pose proof (cp_a2 _ _ _ _ _ _ _ HPRE) as Ha2.
pose proof (cp_a3 _ _ _ _ _ _ _ HPRE) as Ha3.
assert (Ea1 : dc_a1 c = x_tab c)
  by (unfold dc_a1; rewrite Ha1; unfold w64; apply unsigned_lit_small; lia).
assert (Ea2 : dc_a2 c = x_max c)
  by (unfold dc_a2; rewrite Ha2; unfold w64; apply unsigned_lit_small; lia).
assert (Ea3 : dc_a3 c = x_n c)
  by (unfold dc_a3; rewrite Ha3; unfold w64; apply unsigned_lit_small; lia).
rewrite Ea1 in Ftab. rewrite Ea2 in Fmax. rewrite Ea3 in Fn.
destruct (dcs3_nums B RLO RHI GOTW GUARD c 0 ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as
  (NF1 & NF2 & NF3 & NFapp & NS1 & NS2 & NS3 & NS4 & NIN1 & NEF & NLY & NT1 & NT2 & NT3 & NT4 & NT5).
assert (HSTKv : STK_reac_segconf_declared = 12560) by (vm_compute; reflexivity).
assert (HSTKA : STK_reac_declared_vlan_add = 8304) by (vm_compute; reflexivity).
destruct (dcl_split_some _ _ _ Hsp) as (Hv16 & Hplen).
destruct HTAB as (T1 & T2 & T3 & T4).
pose proof (dcl_add_len ti (x_max c) p v T4) as [L1 L2].
set (ti' := snd (vlan_add ti (x_max c) p v)) in *.
set (rv := fst (vlan_add ti (x_max c) p v)) in *.
set (FP1 := vtab_W (x_tab c) (x_n c) ti ti') in *.
(* ---------------- the stretch 0x89a00 .. 0x89a14 and the call ---------------- *)
pose proof (dcs3_seedA regs3 W3 mem3 v (x_tab c) (x_max c) (x_n c) (dc_F c) (dc_s1 c)
  R27 F9 Hv16 Htab64 Hmax64 Hn64 ltac:(lia) ltac:(lia) ltac:(lia) Hvid Ftab Fmax Fn) as HS.
assert (HEI : img_env VAL A_LIM (dcs3_EA regs3 v (x_tab c) (x_max c) (x_n c)))
  by (unfold dcs3_EA; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + DC_KA)) with (Z_to_bv 64 (BASE + DC_KA)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdv. clear mat.
pose proof (dcs3_frame_ro (dcs3_EA regs3 v (x_tab c) (x_max c) (x_n c)) (ss_mem ss_dcs3A) mem3 (ms_mem ms)
  ltac:(unfold ss_dcs3A, dcs3_rvid, dcs3_rs1; cbn [ss_mem];
        apply Forall_cons; [cbn; lia|]; apply Forall_cons; [cbn; lia|]; apply Forall_nil) HF) as HEQ.
assert (HRDc : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a; exact (dcs3_aview_ext SEGS (w_H W3) mem3 (ms_mem ms) HEQ a)).
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 2 2%bv eq_refl) in Q2.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 3 3%bv eq_refl) in Q3.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 4 4%bv eq_refl) in Q4.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 8 8%bv eq_refl) in Q8.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 9 9%bv eq_refl) in Q9.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 26 26%bv eq_refl) in Q13.
rewrite (dcs3_ea_33 regs3 v (x_tab c) (x_max c) (x_n c)) in Q10.
rewrite (dcs3_ea_34 regs3 v (x_tab c) (x_max c) (x_n c)) in Q11.
rewrite (dcs3_ea_35 regs3 v (x_tab c) (x_max c) (x_n c)) in Q12.
rewrite (dcs3_ea_32 regs3 v (x_tab c) (x_max c) (x_n c)) in Q14.
assert (QSP : spZ (ms_regs ms) = dc_s1 c)
  by (unfold spZ; rewrite Q2, F2; unfold w64; apply unsigned_lit_small; lia).
assert (QS0 : s0Z (ms_regs ms) = dc_sp0 c)
  by (unfold s0Z; rewrite Q8, F8; unfold w64; apply unsigned_lit_small; lia).
assert (Q14' : getr (ms_regs ms) 14 = w64 v)
  by (rewrite Q14; unfold w64; apply dcs3_zext16; lia).
assert (Q13' : getr (ms_regs ms) 13 = w64 (dc_F c + 32)) by (rewrite Q13; exact R26).
assert (HROD : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms))).
{ intros a H1 H2 H3. rewrite HRDc.
  exact (dcs3_rod B RLO RHI GOTW GUARD c 0 ly3 S3 W3 regs3 mem3 md3 HPRE ROIMG RO HFI HUN a H1 H2 H3). }
pose proof (dcs3_add_pre B RLO RHI GOTW GUARD c i ti added p v ly3 S3 W3 regs3 mem3 md3
  (ms_regs ms) (ms_mem ms) HPRE HKA0 HEQ QSP) as HADDPRE.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 19 19%bv eq_refl) in Q19.
rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 20 20%bv eq_refl) in Q20.
assert (HFIc : dc_fi B STK_reac_segconf_declared c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv).
{ apply (dcs3_fi_run B RLO RHI GOTW GUARD c 0 ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdv
    HPRE HFI HUN HJ ltac:(intros x _ _; exact (HEQ x)) Q2 Q3 Q4 Q8 Q9 Q19 Q20). }
assert (HTABc : dc_tab c ti W3 (ms_mem ms))
  by (apply (dcs3_tab_ext c ti W3 mem3 (ms_mem ms) (conj T1 (conj T2 (conj T3 T4))) HRDc)).
destruct (dcs3_chain B RLO RHI GOTW GUARD c ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ti
  HPRE HFIc HUN HTABc) as (ch1 & HCH).
pose proof (dcs3_fp_apart B RLO RHI GOTW GUARD c i ti added p v ly3 S3 W3 regs3 mem3 md3 HPRE HKA0) as HAPART.
destruct (dc_sp1_facts (dc_sp0 c) NT5) as (Hs1m & Hs1v).
assert (Ho16 : (dc_s1 c - dc_sp0 c) mod 16 = 0).
{ unfold dc_s1. destruct Hs1v as [E1 | E1]; rewrite E1;
  [replace (dc_sp0 c - 192 - dc_sp0 c) with (-192) by lia
  | replace (dc_sp0 c - 208 - dc_sp0 c) with (-208) by lia]; reflexivity. }
assert (HNEV : st_nev S3 + EV_reac_declared_vlan_add <= EV_MAX).
{ unfold EV_reac_declared_vlan_add. unfold EV_reac_segconf_declared in Hnev0. lia. }
assert (HSIG : SIGMA SS_reac_declared_vlan_add = BASE + AF_reac_declared_vlan_add).
{ rewrite (SIGP SS_reac_declared_vlan_add ltac:(cbv [seg_prog_syms In]; tauto)).
  first [reflexivity | f_equal; vm_compute; reflexivity]. }
pmkst HS. rewrite HSIG.
eapply SRr_bind.
{ refine (cl_callS_wide B LAWS W3 (ms_regs ms) (ms_mem ms)
    (Z_to_bv 64 (BASE + AF_reac_declared_vlan_add)) STK_reac_segconf_declared (dc_sp0 c) (dc_FP c)
    (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)] ly3 S3 mdv 0
    STK_reac_declared_vlan_add FP1 EV_reac_declared_vlan_add (dc_s1 c - dc_sp0 c) (getr (ms_regs ms) 1) ch1
    (dcs3_Q c ti p v ly3 S3) HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - rewrite QSP. lia.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - rewrite Q3. exact F3.
  - rewrite Q4. exact F4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - replace (dc_sp0 c + (dc_s1 c - dc_sp0 c)) with (dc_s1 c) by lia. rewrite QS0. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { apply (ADD fx ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ch1 (x_tab c) (x_max c) (x_n c)
        (dc_F c + 32) v ti p HPRE1 HROD Q10 Htab64 Q11 Hmax64 Q12 Hn64 Q13' ltac:(lia) Q14'
        ltac:(lia) HADDPRE HNEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HKQ).
    destruct HKQ as (K1 & K2 & K3 & _ & _ & K5).
    exists ly', S', regs', mem', md'. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP'|].
    unfold dcs3_Q. split; [exact K1|]. split; [exact K2|]. split; [exact K3 | exact K5].
  - intros a Ha.
    exact (dcs3_awr B RLO RHI GOTW GUARD c i ti added p v ly3 S3 W3 regs3 mem3 md3 HPRE HKA0 a Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    destruct (HAPART a Ha) as [[Hx | Hx] _]; lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
replace (dc_sp0 c + (dc_s1 c - dc_sp0 c)) with (dc_s1 c) in HJc2 by lia.
unfold dcs3_Q in HK2. destruct HK2 as (HA0 & HRT & HVL & HNA).
assert (HA0' : getr regs2 10 = w64 rv) by exact HA0.
pose proof HNA as (HPERM2 & HLY2 & fs2 & HFS2).
change (0 + EV_reac_declared_vlan_add) with 0 in HJ2.
(* the cut parts carried over the call *)
pose proof (dcs3_fi_call B RLO RHI GOTW GUARD c ti p v 0 EV_reac_declared_vlan_add ly3 S3 W3
  (ms_regs ms) (ms_mem ms) mdv ly2 S2 W2 regs2 mem2 md2 HPRE HAPART HFIc HUN HJ2 HJc2 HP2) as HFI2.
change (0 + EV_reac_declared_vlan_add) with 0 in HFI2.
pose proof (dcs3_un_call B c ly3 S3 ly2 S2 HUN HNA) as HUN2.
assert (H56c : rdword (rdW W3 (ms_mem ms)) (dc_s1 c + 56) = Some added).
{ rewrite (rdword_ext (rdW W3 mem3) (rdW W3 (ms_mem ms)) (dc_s1 c + 56)
    ltac:(intros k _; apply HRDc)). exact H56. }
pose proof (dcs3_w56_call B RLO RHI GOTW GUARD c 0 ti p v added ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv
  ly2 S2 W2 mem2 md2 EV_reac_declared_vlan_add HPRE HFIc HUN HAPART H56c HJc2) as HW56.
assert (HTAB2 : dc_tab c ti' W2 mem2)
  by (apply (dcs3_tab_call c ti ti' W2 mem2 HRT HVL T3 L1); lia).
(* the numbers again, at the state after the call *)
destruct (dcs3_nums B RLO RHI GOTW GUARD c 0 ly2 S2 W2 regs2 mem2 md2 HPRE HFI2 HUN2) as
  (MF1 & MF2 & MF3 & MFapp & MS1 & MS2 & MS3 & MS4 & MIN1 & MEF & MLY & MT1 & MT2 & MT3 & MT4 & MT5).
pose proof HFI2 as [HJ2' G2 G3 G4 G8 G9 G19 G20 Gsaved Gf16 Gf24 Gtab Gmax Gn Gflag].
pose proof (proj1 HJ2') as HAR2.
(* the writable windows of the two regions of the return state *)
assert (HWR1 : forall o, 56 <= o < 64 -> writable_at SEGS (mrestrict (w_H W2) mem2) (dc_s1 c + o)).
{ intros o Ho. apply (apresent_writable SEGS).
  pose proof HJ2' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  apply Hpres2. lia. }
assert (HWR2 : forall o, 0 <= o < 16 ->
  writable_at SEGS (mrestrict (w_H W2) mem2) (SB + dc_F c / 8 + o)).
{ intros o Ho. apply (apresent_writable SEGS).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 (x_fpos c) HAR2 MIN1) as (_ & _ & _ & HFS).
  rewrite MEF in HFS. change (fs_frame_bytes 1 / 8) with 16 in HFS.
  pose proof (proj1 (HFS o Ho)) as Hp. unfold shadow_addr in Hp. rewrite <- SB_SHADOW_OFF in Hp. exact Hp. }
assert (HD1 : 0 <= dc_F c / 8) by (apply Z.div_pos; lia).
assert (HD3 : dc_F c / 8 <= 17592185946112) by (Z.div_mod_to_equations; lia).
assert (HSH1 : SB + dc_F c / 8 + 16 <= dc_s1 c) by (unfold SB; lia).
assert (HRV : rv = 0 \/ rv = 1 \/ rv = -1) by (unfold rv; apply dcl_add_rv).
assert (HADD31 : 0 <= added <= Z.of_nat i) by (destruct HLOOP as [_ Hb]; exact Hb).
assert (HI31 : (i < 32)%nat).
{ pose proof (cp_dpre _ _ _ _ _ _ _ HPRE) as HD.
  destruct HD as (_ & _ & Hrc & _). unfold dc_segs in Hi.
  destruct Hrc as (bs & Hbs & Henc). destruct Henc as (_ & Hn32 & _). lia. }
(* the model step at this pass *)
pose proof (dcl_go_split (dc_segs c) i ti (x_max c) added p v Hi Hign Hsp) as HGO.
destruct HLOOP as [HGOEQ HADDB].
assert (HGO2 : (if rv <? 0 then (-1, ti') else
    r_decl_go (skipn (S i) (dc_segs c)) ti' (x_max c) (added + rv)) = dc_res c)
  by (unfold rv, ti'; rewrite <- HGO; exact HGOEQ).
(* the state at the return of add *)
assert (HEIR : img_env VAL A_LIM (dcs3_ER regs2 added)) by (unfold dcs3_ER; apply Eimg_env).
pose proof (dcs3_seedR regs2 W2 mem2 added (dc_F c) (dc_s1 c)
  ltac:(rewrite (dcs3_pres (ms_regs ms) regs2 (9%bv : bv 5) HP2 ltac:(dcs3_cs));
        rewrite Q9; exact F9)
  ltac:(rewrite (dcs3_pres (ms_regs ms) regs2 (19%bv : bv 5) HP2 ltac:(dcs3_cs));
        rewrite Q19; exact F19)
  ltac:(lia) ltac:(lia) HSH1 ltac:(lia) HW56 HWR1 HWR2) as HS2.
rewrite Q1. change (19684%Z) with DC_RET.
(* the registers add kept *)
assert (CSV : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (dcs3_pres (ms_regs ms) regs2 r HP2 Hr)).
assert (HAWR2 : forall a, in_wrange (dcs3_ER regs2 added) (ss_mem ss_dcs3R) a ->
  awr_byte SEGS B STK_reac_segconf_declared (dc_sp0 c) (dc_FP c) (ablocks B (x_ly c) (x_S c)) (ablocks B ly2 S2)
    (frames (x_S c)) ly2 [(1, x_fpos c)] a).
{ intros a (r & Hr & Ha).
  change (ss_mem ss_dcs3R) with [dcs3_rs1b; dcs3_rsh] in Hr.
  assert (U9b : base_val (dcs3_ER regs2 added) (Some 9%nat) = dc_s1 c).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 9 9%bv eq_refl), (CSV (9%bv : bv 5) ltac:(dcs3_cs)),
      Q9, F9. unfold w64. apply unsigned_lit_small. lia. }
  assert (U19b : base_val (dcs3_ER regs2 added) (Some 19%nat) = SB + dc_F c / 8).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 19 19%bv eq_refl), (CSV (19%bv : bv 5) ltac:(dcs3_cs)),
      Q19, F19. unfold w64. apply unsigned_lit_small. unfold SB. lia. }
  destruct Hr as [<- | [<- | []]]; unfold dcs3_rs1b, dcs3_rsh in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
  - rewrite U9b in Ha. left. lia.
  - rewrite U19b in Ha. right. right. right. left. exists 1, (x_fpos c). split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite MEF.
    change (fs_frame_bytes 1 / 8) with 16. rewrite <- SB_SHADOW_OFF. lia. }
(* the registers of the loop and of the frame part, through add and the run *)
assert (HLRk : forall (regs4 : bvmap 5 word),
  getr regs4 23 = getr regs2 23 -> getr regs4 22 = getr regs2 22 -> getr regs4 25 = getr regs2 25 ->
  getr regs4 24 = getr regs2 24 -> getr regs4 21 = getr regs2 21 -> getr regs4 26 = getr regs2 26 ->
  getr regs4 27 = getr regs2 27 -> getr regs4 18 = getr regs2 18 ->
  dc_lregs c (Z.of_nat i) regs4).
{ intros regs4 Z23 Z22 Z25 Z24 Z21 Z26 Z27 Z18. unfold dc_lregs.
  rewrite Z23, Z22, Z25, Z24, Z21, Z26, Z27, Z18.
  rewrite (CSV (23%bv : bv 5) ltac:(dcs3_cs)), (CSV (22%bv : bv 5) ltac:(dcs3_cs)),
    (CSV (25%bv : bv 5) ltac:(dcs3_cs)), (CSV (24%bv : bv 5) ltac:(dcs3_cs)),
    (CSV (21%bv : bv 5) ltac:(dcs3_cs)), (CSV (26%bv : bv 5) ltac:(dcs3_cs)),
    (CSV (27%bv : bv 5) ltac:(dcs3_cs)), (CSV (18%bv : bv 5) ltac:(dcs3_cs)).
  prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 18 18%bv eq_refl) in P18.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 21 21%bv eq_refl) in P21.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 22 22%bv eq_refl) in P22.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 23 23%bv eq_refl) in P23.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 24 24%bv eq_refl) in P24.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 25 25%bv eq_refl) in P25.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 26 26%bv eq_refl) in P26.
  rewrite (dcs3_ea_reg regs3 v (x_tab c) (x_max c) (x_n c) 27 27%bv eq_refl) in P27.
  rewrite P18, P21, P22, P23, P24, P25, P26, P27.
  split; [exact R23|]. split; [exact R22|]. split; [exact R25|]. split; [exact R24|].
  split; [exact R21|]. split; [exact R26|]. split; [exact R27 | exact R18]. }
(* a pinned answer: the engine resolves `bltz a0` *)
assert (HPIN : forall z, getr regs2 10 = Z_to_bv 64 z ->
  st_ok_pi SEGS VAL (dcs3_ER regs2 added) (ss_dcs3P z)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + DC_RET)) mem2 (seg_rom SEGS)))).
{ intros z Hz. unfold ss_dcs3P.
  exact (st_ok_pi_pin_reg' (dcs3_ER regs2 added) ss_dcs3R _ (10%bv : bv 5) z HS2 Hz eq_refl). }
destruct HRV as [Erv | [Erv | Erv]].
- (* add answered 0: the count is unchanged, the walk falls into KT *)
  pose proof (HPIN 0 ltac:(rewrite HA0', Erv; reflexivity)) as HS3.
  paj_run_to_sh RUNTOP HS3 HJ2 DC_KT.
  { exact HAWR2. }
  set (mdk := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdk. clear mat.
  pmkst HS3.
  prreg HS3 (2%bv : bv 5) Z2. prreg HS3 (3%bv : bv 5) Z3. prreg HS3 (4%bv : bv 5) Z4.
  prreg HS3 (8%bv : bv 5) Z8. prreg HS3 (9%bv : bv 5) Z9. prreg HS3 (18%bv : bv 5) Z18.
  prreg HS3 (19%bv : bv 5) Z19. prreg HS3 (20%bv : bv 5) Z20. prreg HS3 (21%bv : bv 5) Z21.
  prreg HS3 (22%bv : bv 5) Z22. prreg HS3 (23%bv : bv 5) Z23. prreg HS3 (24%bv : bv 5) Z24.
  prreg HS3 (25%bv : bv 5) Z25. prreg HS3 (26%bv : bv 5) Z26. prreg HS3 (27%bv : bv 5) Z27.
  repeat match goal with
  | H : getr (ms_regs ms0) ?r = ew (dcs3_ER regs2 added) ?k |- _ =>
      rewrite (dcs3_er_reg regs2 added k r eq_refl) in H
  end.
  assert (U9b : base_val (dcs3_ER regs2 added) (Some 9%nat) = dc_s1 c).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 9 9%bv eq_refl), (CSV (9%bv : bv 5) ltac:(dcs3_cs)),
      Q9, F9. unfold w64. apply unsigned_lit_small. lia. }
  assert (U19b : base_val (dcs3_ER regs2 added) (Some 19%nat) = SB + dc_F c / 8).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 19 19%bv eq_refl), (CSV (19%bv : bv 5) ltac:(dcs3_cs)),
      Q19, F19. unfold w64. apply unsigned_lit_small. unfold SB. lia. }
  assert (HMEM : forall x, ~ (dc_s1 c + 56 <= bv_unsigned x < dc_s1 c + 64) ->
    ~ (SB + dc_F c / 8 <= bv_unsigned x < SB + dc_F c / 8 + 16) -> ms_mem ms0 x = mem2 x).
  { intros x H1 H2. apply HF. intros (r & Hr & Ha).
    change (ss_mem (ss_dcs3P 0)) with [dcs3_rs1b; dcs3_rsh] in Hr.
    destruct Hr as [<- | [<- | []]]; unfold dcs3_rs1b, dcs3_rsh in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    [rewrite U9b in Ha | rewrite U19b in Ha]; lia. }
  assert (HMEMr : forall a, 0 <= a < 2 ^ 64 -> ~ (dc_s1 c + 56 <= a < dc_s1 c + 64) ->
    ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
  { intros a Ha H1 H2. unfold aview, mbyte, mrestrict. cbv beta.
    rewrite (HMEM (Z_to_bv 64 a)); [reflexivity | |];
    rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite (Z.mod_small a (2 ^ 64)) by lia; assumption. }
  (* the word the count update left at 56(s1) *)
  assert (HW56k : rdword (rdW W2 (ms_mem ms0)) (dc_s1 c + 56) = Some (added + rv)).
  { pose proof (st_ok_pi_region_nth (dcs3_ER regs2 added) _ _ 0%nat _ HS3 eq_refl) as HRG.
    destruct HRG as (_ & _ & _ & Hcs). apply Forall_inv in Hcs.
    cbn [YP09.r_base base_val] in Hcs.
    assert (U9c : bv_unsigned (ew (dcs3_ER regs2 added) 9) = dc_s1 c) by exact U9b.
    rewrite U9c in Hcs.
    pose proof (val_mem_low_of_chunk SEGS (dcs3_ER regs2 added)
      (mrestrict (w_H W2) (ms_mem ms0)) (dc_s1 c) 56 8
      (SAluw ALU_ADD (SLit 0) (SOff 32 0)) Hcs ltac:(cbn; lia)) as HV.
    assert (HU : U (dcs3_ER regs2 added) (SAluw ALU_ADD (SLit 0) (SOff 32 0)) = added).
    { rewrite (dcs3_addw (dcs3_ER regs2 added) (SLit 0) (SOff 32 0) 0 added
        ltac:(rewrite U_SLit; reflexivity)
        ltac:(exact (U_atom (dcs3_ER regs2 added) 32 added (dcs3_er_32 regs2 added) ltac:(lia)))
        ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
    unfold U in HU. cbn [N.to_nat] in HV. rewrite HU in HV.
    change (8 * Z.of_N 8) with 64 in HV. rewrite (Z.mod_small added (2 ^ 64)) in HV by lia.
    rewrite Erv, Z.add_0_r.
    exact (rdword_of_val_mem SEGS (w_H W2) (ms_mem ms0) (dc_s1 c + 56) added HV ltac:(lia)). }
  (* the cut at KT *)
  change (Z_to_bv 64 (BASE + 19712)) with (w64 (BASE + DC_KT)).
  apply (HKT ti' (added + rv) ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) mdk).
  unfold INV_KT.
  split; [apply (dcs3_fi_run B RLO RHI GOTW GUARD c 0 ly2 S2 W2 regs2 mem2 md2
      (ms_regs ms0) (ms_mem ms0) mdk HPRE HFI2 HUN2 HJ2 HMEM Z2 Z3 Z4 Z8 Z9 Z19 Z20)|].
  split; [exact HUN2|].
  split; [apply (dcs3_tab_keep B RLO RHI GOTW GUARD c 0 ly2 S2 W2 regs2 mem2 md2 ti' W2 mem2
      (ms_mem ms0) HPRE HFI2 HUN2 HTAB2 HMEMr)|].
  split; [exact Hi|].
  assert (HGOK : r_decl_go (skipn (S i) (dc_segs c)) ti' (x_max c) (added + rv) = dc_res c).
  { rewrite <- HGO2. replace (rv <? 0) with false by (rewrite Erv; reflexivity). reflexivity. }
  unfold dc_res in HGOK.
  split; [unfold dc_loop; split; [exact HGOK | lia]|].
  split; [exact (HLRk (ms_regs ms0) Z23 Z22 Z25 Z24 Z21 Z26 Z27 Z18) | exact HW56k].
- (* add answered 1: the count grows by one, the walk falls into KT *)
  pose proof (HPIN 1 ltac:(rewrite HA0', Erv; reflexivity)) as HS3.
  paj_run_to_sh RUNTOP HS3 HJ2 DC_KT.
  { exact HAWR2. }
  set (mdk := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdk. clear mat.
  pmkst HS3.
  prreg HS3 (2%bv : bv 5) Z2. prreg HS3 (3%bv : bv 5) Z3. prreg HS3 (4%bv : bv 5) Z4.
  prreg HS3 (8%bv : bv 5) Z8. prreg HS3 (9%bv : bv 5) Z9. prreg HS3 (18%bv : bv 5) Z18.
  prreg HS3 (19%bv : bv 5) Z19. prreg HS3 (20%bv : bv 5) Z20. prreg HS3 (21%bv : bv 5) Z21.
  prreg HS3 (22%bv : bv 5) Z22. prreg HS3 (23%bv : bv 5) Z23. prreg HS3 (24%bv : bv 5) Z24.
  prreg HS3 (25%bv : bv 5) Z25. prreg HS3 (26%bv : bv 5) Z26. prreg HS3 (27%bv : bv 5) Z27.
  repeat match goal with
  | H : getr (ms_regs ms0) ?r = ew (dcs3_ER regs2 added) ?k |- _ =>
      rewrite (dcs3_er_reg regs2 added k r eq_refl) in H
  end.
  assert (U9b : base_val (dcs3_ER regs2 added) (Some 9%nat) = dc_s1 c).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 9 9%bv eq_refl), (CSV (9%bv : bv 5) ltac:(dcs3_cs)),
      Q9, F9. unfold w64. apply unsigned_lit_small. lia. }
  assert (U19b : base_val (dcs3_ER regs2 added) (Some 19%nat) = SB + dc_F c / 8).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 19 19%bv eq_refl), (CSV (19%bv : bv 5) ltac:(dcs3_cs)),
      Q19, F19. unfold w64. apply unsigned_lit_small. unfold SB. lia. }
  assert (HMEM : forall x, ~ (dc_s1 c + 56 <= bv_unsigned x < dc_s1 c + 64) ->
    ~ (SB + dc_F c / 8 <= bv_unsigned x < SB + dc_F c / 8 + 16) -> ms_mem ms0 x = mem2 x).
  { intros x H1 H2. apply HF. intros (r & Hr & Ha).
    change (ss_mem (ss_dcs3P 1)) with [dcs3_rs1b; dcs3_rsh] in Hr.
    destruct Hr as [<- | [<- | []]]; unfold dcs3_rs1b, dcs3_rsh in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    [rewrite U9b in Ha | rewrite U19b in Ha]; lia. }
  assert (HMEMr : forall a, 0 <= a < 2 ^ 64 -> ~ (dc_s1 c + 56 <= a < dc_s1 c + 64) ->
    ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
  { intros a Ha H1 H2. unfold aview, mbyte, mrestrict. cbv beta.
    rewrite (HMEM (Z_to_bv 64 a)); [reflexivity | |];
    rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite (Z.mod_small a (2 ^ 64)) by lia; assumption. }
  (* the word the count update left at 56(s1) *)
  assert (HW56k : rdword (rdW W2 (ms_mem ms0)) (dc_s1 c + 56) = Some (added + rv)).
  { pose proof (st_ok_pi_region_nth (dcs3_ER regs2 added) _ _ 0%nat _ HS3 eq_refl) as HRG.
    destruct HRG as (_ & _ & _ & Hcs). apply Forall_inv in Hcs.
    cbn [YP09.r_base base_val] in Hcs.
    assert (U9c : bv_unsigned (ew (dcs3_ER regs2 added) 9) = dc_s1 c) by exact U9b.
    rewrite U9c in Hcs.
    pose proof (val_mem_low_of_chunk SEGS (dcs3_ER regs2 added)
      (mrestrict (w_H W2) (ms_mem ms0)) (dc_s1 c) 56 8
      (SAluw ALU_ADD (SLit 1) (SOff 32 0)) Hcs ltac:(cbn; lia)) as HV.
    assert (HU : U (dcs3_ER regs2 added) (SAluw ALU_ADD (SLit 1) (SOff 32 0)) = 1 + added).
    { rewrite (dcs3_addw (dcs3_ER regs2 added) (SLit 1) (SOff 32 0) 1 added
        ltac:(rewrite U_SLit; reflexivity)
        ltac:(exact (U_atom (dcs3_ER regs2 added) 32 added (dcs3_er_32 regs2 added) ltac:(lia)))
        ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
    unfold U in HU. cbn [N.to_nat] in HV. rewrite HU in HV.
    change (8 * Z.of_N 8) with 64 in HV. rewrite (Z.mod_small (1 + added) (2 ^ 64)) in HV by lia.
    rewrite Erv. replace (added + 1) with (1 + added) by lia.
    exact (rdword_of_val_mem SEGS (w_H W2) (ms_mem ms0) (dc_s1 c + 56) (1 + added) HV ltac:(lia)). }
  (* the cut at KT *)
  change (Z_to_bv 64 (BASE + 19712)) with (w64 (BASE + DC_KT)).
  apply (HKT ti' (added + rv) ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) mdk).
  unfold INV_KT.
  split; [apply (dcs3_fi_run B RLO RHI GOTW GUARD c 0 ly2 S2 W2 regs2 mem2 md2
      (ms_regs ms0) (ms_mem ms0) mdk HPRE HFI2 HUN2 HJ2 HMEM Z2 Z3 Z4 Z8 Z9 Z19 Z20)|].
  split; [exact HUN2|].
  split; [apply (dcs3_tab_keep B RLO RHI GOTW GUARD c 0 ly2 S2 W2 regs2 mem2 md2 ti' W2 mem2
      (ms_mem ms0) HPRE HFI2 HUN2 HTAB2 HMEMr)|].
  split; [exact Hi|].
  assert (HGOK : r_decl_go (skipn (S i) (dc_segs c)) ti' (x_max c) (added + rv) = dc_res c).
  { rewrite <- HGO2. replace (rv <? 0) with false by (rewrite Erv; reflexivity). reflexivity. }
  unfold dc_res in HGOK.
  split; [unfold dc_loop; split; [exact HGOK | lia]|].
  split; [exact (HLRk (ms_regs ms0) Z23 Z22 Z25 Z24 Z21 Z26 Z27 Z18) | exact HW56k].
- (* add answered a negative number: the walk leaves -1 in 56(s1) and joins KX *)
  pose proof (HPIN (-1) ltac:(rewrite HA0', Erv; reflexivity)) as HS3.
  paj_run_to_sh RUNTOP HS3 HJ2 DC_KX.
  { exact HAWR2. }
  set (mdk := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdk. clear mat.
  pmkst HS3.
  prreg HS3 (2%bv : bv 5) Z2. prreg HS3 (3%bv : bv 5) Z3. prreg HS3 (4%bv : bv 5) Z4.
  prreg HS3 (8%bv : bv 5) Z8. prreg HS3 (9%bv : bv 5) Z9. prreg HS3 (18%bv : bv 5) Z18.
  prreg HS3 (19%bv : bv 5) Z19. prreg HS3 (20%bv : bv 5) Z20. prreg HS3 (21%bv : bv 5) Z21.
  prreg HS3 (22%bv : bv 5) Z22. prreg HS3 (23%bv : bv 5) Z23. prreg HS3 (24%bv : bv 5) Z24.
  prreg HS3 (25%bv : bv 5) Z25. prreg HS3 (26%bv : bv 5) Z26. prreg HS3 (27%bv : bv 5) Z27.
  repeat match goal with
  | H : getr (ms_regs ms0) ?r = ew (dcs3_ER regs2 added) ?k |- _ =>
      rewrite (dcs3_er_reg regs2 added k r eq_refl) in H
  end.
  assert (U9b : base_val (dcs3_ER regs2 added) (Some 9%nat) = dc_s1 c).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 9 9%bv eq_refl), (CSV (9%bv : bv 5) ltac:(dcs3_cs)),
      Q9, F9. unfold w64. apply unsigned_lit_small. lia. }
  assert (U19b : base_val (dcs3_ER regs2 added) (Some 19%nat) = SB + dc_F c / 8).
  { cbn [base_val]. rewrite (dcs3_er_reg regs2 added 19 19%bv eq_refl), (CSV (19%bv : bv 5) ltac:(dcs3_cs)),
      Q19, F19. unfold w64. apply unsigned_lit_small. unfold SB. lia. }
  assert (HMEM : forall x, ~ (dc_s1 c + 56 <= bv_unsigned x < dc_s1 c + 64) ->
    ~ (SB + dc_F c / 8 <= bv_unsigned x < SB + dc_F c / 8 + 16) -> ms_mem ms0 x = mem2 x).
  { intros x H1 H2. apply HF. intros (r & Hr & Ha).
    change (ss_mem (ss_dcs3P (-1))) with [dcs3_rs1b; dcs3_rsh] in Hr.
    destruct Hr as [<- | [<- | []]]; unfold dcs3_rs1b, dcs3_rsh in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    [rewrite U9b in Ha | rewrite U19b in Ha]; lia. }
  assert (HMEMr : forall a, 0 <= a < 2 ^ 64 -> ~ (dc_s1 c + 56 <= a < dc_s1 c + 64) ->
    ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
  { intros a Ha H1 H2. unfold aview, mbyte, mrestrict. cbv beta.
    rewrite (HMEM (Z_to_bv 64 a)); [reflexivity | |];
    rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite (Z.mod_small a (2 ^ 64)) by lia; assumption. }
  (* the word the negative arm left at 56(s1) *)
  assert (HRES : dc_res c = (-1, ti')).
  { rewrite <- HGO2. replace (rv <? 0) with true by (rewrite Erv; reflexivity). reflexivity. }
  assert (HW56k : rdword (rdW W2 (ms_mem ms0)) (dc_s1 c + 56) = Some (fst (dc_res c) mod 2 ^ 64)).
  { pose proof (st_ok_pi_region_nth (dcs3_ER regs2 added) _ _ 0%nat _ HS3 eq_refl) as HRG.
    destruct HRG as (_ & _ & _ & Hcs). apply Forall_inv in Hcs.
    cbn [YP09.r_base base_val] in Hcs.
    assert (U9c : bv_unsigned (ew (dcs3_ER regs2 added) 9) = dc_s1 c) by exact U9b.
    rewrite U9c in Hcs.
    pose proof (val_mem_low_of_chunk SEGS (dcs3_ER regs2 added)
      (mrestrict (w_H W2) (ms_mem ms0)) (dc_s1 c) 56 8
      (SLit 18446744073709551615) Hcs ltac:(cbn; lia)) as HV.
    assert (HU : U (dcs3_ER regs2 added) (SLit 18446744073709551615) = 18446744073709551615)
      by (rewrite U_SLit; reflexivity).
    unfold U in HU. cbn [N.to_nat] in HV. rewrite HU in HV.
    change (8 * Z.of_N 8) with 64 in HV.
    rewrite (Z.mod_small 18446744073709551615 (2 ^ 64)) in HV by lia.
    rewrite HRES. cbn [fst].
    replace ((-1) mod 2 ^ 64) with 18446744073709551615 by reflexivity.
    exact (rdword_of_val_mem SEGS (w_H W2) (ms_mem ms0) (dc_s1 c + 56) 18446744073709551615 HV
      ltac:(lia)). }
  (* the cut at KX *)
  change (Z_to_bv 64 (BASE + 19780)) with (w64 (BASE + DC_KX)).
  apply (HKX ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) mdk).
  unfold INV_KX.
  split; [apply (dcs3_fi_run B RLO RHI GOTW GUARD c 0 ly2 S2 W2 regs2 mem2 md2
      (ms_regs ms0) (ms_mem ms0) mdk HPRE HFI2 HUN2 HJ2 HMEM Z2 Z3 Z4 Z8 Z9 Z19 Z20)|].
  split; [exact HUN2|].
  split; [rewrite HRES; cbn [snd];
          apply (dcs3_tab_keep B RLO RHI GOTW GUARD c 0 ly2 S2 W2 regs2 mem2 md2 ti' W2 mem2
            (ms_mem ms0) HPRE HFI2 HUN2 HTAB2 HMEMr) | exact HW56k].
Qed.





End e.
End f.
End d.
