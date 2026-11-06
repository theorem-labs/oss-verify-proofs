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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 760 of its 799 lines of code are new or changed and 414 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image A: the point K1 (0x89bec) and the digit loop KL (0x89c24). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d reac_declared_vlan_split_lem reac_declared_vlan_split_h reac_declared_vlan_split_r.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the shadow base the body keeps in s6 (atom 22) and the band the token engine checks against *)
Definition VL_BSPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a byte of the reader is a one-byte value of the restricted memory *)
Lemma vl_view_range : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> 0 <= v < 256.
Proof using.
intros H m a v Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) a) as [bb|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- Hb.
pose proof (bv_unsigned_in_range 8 bb) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma vl_val1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof using.
intros H m a v Hv k Hk. replace k with 0%nat by lia.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) a) as [bb|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hb. pose proof (bv_unsigned_in_range 8 bb) as R. change (bv_modulus 8) with 256 in R.
f_equal. rewrite <- Hb.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned bb) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* range_addressable moves to a reader that agrees on the shadow bytes it names *)
Lemma vl_ra_ext : forall (rd rd' : reader) Bx a n,
  (forall x, a <= x < a + n -> rd' (shadow_of_addr Bx x) = rd (shadow_of_addr Bx x)) ->
  range_addressable rd Bx a n -> range_addressable rd' Bx a n.
Proof using.
intros rd rd' Bx a n HK H x Hx. destruct (H x Hx) as (s & Hs & Ho).
exists s. rewrite (HK x Hx). split; [exact Hs | exact Ho].
Qed.
(* the value of an atom with an offset, without normalising the term *)
Lemma vl_den : forall E n v off, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + off < 2 ^ 64 ->
  sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof using.
intros E n v off Hn Hv Ho. apply bv_eq.
change (bv_unsigned (sv_denot E (SOff n off))) with (U E (SOff n off)).
rewrite (U_atom_off E n v off Hn Hv Ho), unsigned_lit_small by lia. reflexivity.
Qed.
(* the region of the one byte a pass loads, at the atom of the register that addresses it *)
Definition vl_rK1 : YP09.region := YP09.mkRegion (Some 10%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 40 0))].
Definition vl_rKL : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 40 0))].
(* the seeded state of vs_seedK with that byte region added, the byte as the extra word ys *)
Lemma vl_seedB : forall (W : world SEGS) (regs regs' : bvmap 5 word) mem' pc fs (ys : list word)
    (r : YP09.region) (n : nat) (lo x b : Z),
  r = YP09.mkRegion (Some n) lo (lo + 1) 0 0 [YP09.mkChunk lo (CVal 1 (SOff 40 0))] ->
  YP09.region_wf r = true ->
  vs_slots (rdW W mem') (spZ regs' + 64) regs ->
  2 ^ 46 <= spZ regs' <= 2 ^ 47 - 64 -> spZ regs' mod 16 = 0 -> getr regs' 22 = w64 SB ->
  atoms_ok (Eimg (Ereg regs' (vs_xs regs ++ ys))) fs ->
  ew (Eimg (Ereg regs' (vs_xs regs ++ ys))) n = Z_to_bv 64 x ->
  nth 0 ys (Z_to_bv 64 0) = Z_to_bv 64 b -> 0 <= b < 256 ->
  0 <= x -> 0 <= lo -> x + lo + 1 <= spZ regs' -> rdW W mem' (x + lo) = Some b ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs' (vs_xs regs ++ ys)))
    (mkSS pc sr_atoms (r :: [vs_slots_r]) None
      (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (22%nat, mkAF SB SB 0) :: fs) [] []))
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) mem' (seg_rom SEGS))).
Proof using.
intros W regs regs' mem' pc fs ys r n lo x b Hr Hwf HSL Hsp Hal H22 HF Hn Hb Hbr Hx0 Hlo0 Hxsp HV.
pose proof (vs_seedK W regs regs' mem' pc fs ys HSL Hsp Hal H22 HF) as HS.
pose proof (vs_EE regs' (vs_xs regs ++ ys) 2 2%bv eq_refl) as E2.
pose proof (vs_Ey regs' regs ys 0%nat ltac:(lia)) as EY. cbn [Nat.add] in EY.
set (E := Eimg (Ereg regs' (vs_xs regs ++ ys))) in *.
assert (EX : bv_unsigned (ew E n) = x) by (rewrite Hn; apply unsigned_lit_small; lia).
assert (E40 : sv_denot E (SOff 40 0) = Z_to_bv 64 b)
  by (cbn [sv_denot]; rewrite EY, Hb, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (E2' : bv_unsigned (ew E 2) = spZ regs') by (rewrite E2; reflexivity).
rewrite restrict_mkst_fx in HS |- *.
apply (st_ok_pi_add_region E (vs_ssK pc fs) _ r HS Hwf).
- subst r. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite EX. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ x lo 1 (SOff 40 0) b); [exact E40 | cbn; lia | cbn; lia |].
  exact (vl_val1 (w_H W) mem' (x + lo) b HV).
- subst r. cbn [ss_mem vs_ssK]. unfold all_disjoint, extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi vs_slots_r base_val].
  rewrite EX, E2'. split; [left; lia | exact I].
Qed.
(* the environment after a run: it agrees with the seeded one on every register atom *)
Lemma vl_EV_ewset : forall E k w (regs : bvmap 5 word), (32 <= k)%nat ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ewset E k w) n = getr regs r.
Proof using.
intros E k w regs Hk H n r Hr. pose proof (bv_unsigned_in_range 5 r) as R.
change (bv_modulus 5) with 32 in R. rewrite ew_ewset_other by lia. exact (H n r Hr).
Qed.
(* the registers the body keeps, at the end of a run that left them as their atoms *)
Lemma vl_regs_of : forall E ss (ms : machine_state) (H : word -> bool) (e : vsE) (regs : bvmap 5 word),
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  vs_regs e regs ->
  sr_get (ss_regs ss) (2%bv : bv 5) = SOff 2 0 -> sr_get (ss_regs ss) (3%bv : bv 5) = SOff 3 0 ->
  sr_get (ss_regs ss) (4%bv : bv 5) = SOff 4 0 -> sr_get (ss_regs ss) (8%bv : bv 5) = SOff 8 0 ->
  sr_get (ss_regs ss) (9%bv : bv 5) = SOff 9 0 -> sr_get (ss_regs ss) (18%bv : bv 5) = SOff 18 0 ->
  sr_get (ss_regs ss) (19%bv : bv 5) = SOff 19 0 -> sr_get (ss_regs ss) (22%bv : bv 5) = SOff 22 0 ->
  sr_get (ss_regs ss) (23%bv : bv 5) = SOff 23 0 -> sr_get (ss_regs ss) (24%bv : bv 5) = SOff 24 0 ->
  sr_get (ss_regs ss) (25%bv : bv 5) = SOff 25 0 -> sr_get (ss_regs ss) (26%bv : bv 5) = SOff 26 0 ->
  sr_get (ss_regs ss) (27%bv : bv 5) = SOff 27 0 ->
  vs_regs e (ms_regs ms).
Proof using.
intros E ss ms H e regs HS EV HR S2 S3 S4 S8 S9 S18 S19 S22 S23 S24 S25 S26 S27.
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
split; [unfold spZ; rewrite (vs_reg_atom E ss ms H regs 2 2%bv HS (EV 2%nat 2%bv eq_refl) S2); exact Hsp|].
split; [rewrite (vs_reg_atom E ss ms H regs 3 3%bv HS (EV 3%nat 3%bv eq_refl) S3); exact G3|].
split; [rewrite (vs_reg_atom E ss ms H regs 4 4%bv HS (EV 4%nat 4%bv eq_refl) S4); exact G4|].
split; [rewrite (vs_reg_atom E ss ms H regs 8 8%bv HS (EV 8%nat 8%bv eq_refl) S8); exact G8|].
split; [rewrite (vs_reg_atom E ss ms H regs 9 9%bv HS (EV 9%nat 9%bv eq_refl) S9); exact G9|].
split; [rewrite (vs_reg_atom E ss ms H regs 18 18%bv HS (EV 18%nat 18%bv eq_refl) S18); exact G18|].
split; [rewrite (vs_reg_atom E ss ms H regs 19 19%bv HS (EV 19%nat 19%bv eq_refl) S19); exact G19|].
split; [rewrite (vs_reg_atom E ss ms H regs 22 22%bv HS (EV 22%nat 22%bv eq_refl) S22); exact G22|].
intros r Hr.
assert (Hc : r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [Er|[Er|[Er|[Er|Er]]]]; rewrite Er.
- exact (eq_trans (vs_reg_atom E ss ms H regs 23 23%bv HS (EV 23%nat 23%bv eq_refl) S23) (G27 23 ltac:(lia))).
- exact (eq_trans (vs_reg_atom E ss ms H regs 24 24%bv HS (EV 24%nat 24%bv eq_refl) S24) (G27 24 ltac:(lia))).
- exact (eq_trans (vs_reg_atom E ss ms H regs 25 25%bv HS (EV 25%nat 25%bv eq_refl) S25) (G27 25 ltac:(lia))).
- exact (eq_trans (vs_reg_atom E ss ms H regs 26 26%bv HS (EV 26%nat 26%bv eq_refl) S26) (G27 26 ltac:(lia))).
- exact (eq_trans (vs_reg_atom E ss ms H regs 27 27%bv HS (EV 27%nat 27%bv eq_refl) S27) (G27 27 ltac:(lia))).
Qed.
(* the nine registers the epilogue asks a stretch to keep *)
Lemma vl_regs_kept : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word),
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  sr_get (ss_regs ss) (2%bv : bv 5) = SOff 2 0 -> sr_get (ss_regs ss) (3%bv : bv 5) = SOff 3 0 ->
  sr_get (ss_regs ss) (4%bv : bv 5) = SOff 4 0 -> sr_get (ss_regs ss) (22%bv : bv 5) = SOff 22 0 ->
  sr_get (ss_regs ss) (23%bv : bv 5) = SOff 23 0 -> sr_get (ss_regs ss) (24%bv : bv 5) = SOff 24 0 ->
  sr_get (ss_regs ss) (25%bv : bv 5) = SOff 25 0 -> sr_get (ss_regs ss) (26%bv : bv 5) = SOff 26 0 ->
  sr_get (ss_regs ss) (27%bv : bv 5) = SOff 27 0 ->
  forall r, r = 2 \/ r = 3 \/ r = 4 \/ 22 <= r <= 27 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof using.
intros E ss ms H regs HS EV S2 S3 S4 S22 S23 S24 S25 S26 S27 r Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|Er]]]]]]]]; rewrite Er;
first [ exact (vs_reg_atom E ss ms H regs 2 2%bv HS (EV 2%nat 2%bv eq_refl) S2)
      | exact (vs_reg_atom E ss ms H regs 3 3%bv HS (EV 3%nat 3%bv eq_refl) S3)
      | exact (vs_reg_atom E ss ms H regs 4 4%bv HS (EV 4%nat 4%bv eq_refl) S4)
      | exact (vs_reg_atom E ss ms H regs 22 22%bv HS (EV 22%nat 22%bv eq_refl) S22)
      | exact (vs_reg_atom E ss ms H regs 23 23%bv HS (EV 23%nat 23%bv eq_refl) S23)
      | exact (vs_reg_atom E ss ms H regs 24 24%bv HS (EV 24%nat 24%bv eq_refl) S24)
      | exact (vs_reg_atom E ss ms H regs 25 25%bv HS (EV 25%nat 25%bv eq_refl) S25)
      | exact (vs_reg_atom E ss ms H regs 26 26%bv HS (EV 26%nat 26%bv eq_refl) S26)
      | exact (vs_reg_atom E ss ms H regs 27 27%bv HS (EV 27%nat 27%bv eq_refl) S27) ].
Qed.
Ltac vl_ew0 := repeat (rewrite ew_ewset_other by lia).
Ltac vl_EV EV := repeat (apply vl_EV_ewset; [lia|]); exact EV.
(* the memory a run left: with no write window it is the memory the run started from *)
Ltac vl_mem KA PA :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- _ =>
    let K := fresh "K" in
    pose proof (kept_of_frame (segs := SEGS) Ex rs Hh m1 m2 (fun _ => False) HFr
      ltac:(let bb := fresh in let wlo := fresh in let whi := fresh in let aa := fresh in
            let Hin := fresh in let Hrr := fresh in let Hq := fresh in
            intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]);
            destruct Hin)) as K;
    let KN := fresh "KN" in let PN := fresh "PN" in
    lazymatch type of KA with forall a, aview _ _ ?m0 a = aview _ _ ?mb a =>
      assert (KN : forall a, aview SEGS Hh m2 a = aview SEGS Hh mb a)
        by (apply vs_view_ext; let a := fresh "a" in let Ha := fresh "Ha" in
            intros a Ha; rewrite (K a Ha (fun q => q)); exact (KA a)) end;
    lazymatch goal with HG : mem_grows (mrestrict Hh m1) (mrestrict Hh m2) |- _ =>
      lazymatch type of PA with forall a, apresent _ ?mb a -> _ =>
        assert (PN : forall a, apresent Hh mb a -> apresent Hh m2 a)
          by (let a := fresh "a" in let Ha := fresh "Ha" in
              intros a Ha; exact (apresent_grows Hh m1 m2 a HG (PA a Ha))) end;
      clear HG end;
    clear K KA PA HFr; rename KN into KA; rename PN into PA;
    lazymatch goal with HFx : frame_of _ _ _ _ |- _ => clear HFx end
  end.

(* an unaligned atom fact from the value of the atom *)
Lemma vl_fact0 : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= lo -> lo <= v -> v <= hi < 2 ^ 64 ->
  afact_ok E n (mkAF lo hi 0).
Proof using.
intros E n v lo hi Hn Hlo0 Hlo Hhi. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
(* the value a zero-extending byte load leaves in a register *)
Lemma vl_zext_byte : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 v.
Proof using.
intros E n v Hn Hv. apply bv_eq.
change (bv_unsigned (sv_denot E (SExt false 8 (SOff n 0)))) with (U E (SExt false 8 (SOff n 0))).
rewrite U_zext, (U_atom E n v Hn ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* a list whose i-th byte is no digit is no run of digits *)
Lemma vl_forallb_false : forall (l : list Z) (i : nat), (i < length l)%nat ->
  SegModel.isdigit (nth i l 0) = false -> forallb SegModel.isdigit l = false.
Proof using.
intros l i Hi Hf. destruct (forallb SegModel.isdigit l) eqn:E; [|reflexivity].
rewrite (proj1 (forallb_forall _ _) E (nth i l 0) (nth_In l 0 Hi)) in Hf. discriminate Hf.
Qed.


Section e.
Variable B : asyms.
Variables gotw guard : Z.

(* what the entry's segment gives at a state of the body: its bytes, its shadow, where it lies, the frame *)
Lemma vl_now : forall e regs' mem' md', vs_entry B gotw guard e -> vs_ctx0 B e regs' mem' md' ->
  (forall i, (i < length (e_s e) + 1)%nat ->
     rdW (e_W e) mem' (e_seg e + Z.of_nat i) = Some (nth i (e_s e ++ [0]) 0)) /\
  range_addressable (rdW (e_W e) mem') SHADOW_OFF (e_seg e) (Z.of_nat (length (e_s e)) + 1) /\
  4096 <= e_seg e /\ e_seg e + Z.of_nat (length (e_s e)) + 1 <= e_sp e - STK_reac_declared_vlan_split /\
  2 ^ 46 <= e_sp e - 64 <= 2 ^ 47 - 64 /\ (e_sp e - 64) mod 16 = 0 /\
  SegModel.nulfree (e_s e) /\ (length (e_s e) < 16)%nat.
Proof using.
intros e regs' mem' md' HE HC.
pose proof (AR_laws_ok SEGS B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HE as (HPRE & HRO & R10 & Rseg & R11 & Rpar & R12 & R13 & Rvid & HSP & HNEV).
unfold vs_ctx0, vs_ctxW in HC. pose proof HC as (HJ & HREG & HSL & HK & HPRES).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HSP as (Hseg0 & HSTR & HL16 & HADDR & HMR & HLOC & Hpar0 & Hcap & HDP & HAP & HDJ &
  Hvid0 & Hvid2 & HDV & HAV & HDJ2 & HSSP).
destruct HSTR as ((HZS & HNF) & HTL).
destruct HADDR as (A1 & A2 & A3 & A4 & A5).
unfold e_sp in *.
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
assert (Hlen : 0 <= Z.of_nat (length (e_s e)) < 16) by lia.
assert (HKK : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - STK_reac_declared_vlan_split <= a < spZ (e_regs e)) ->
  rdW (e_W e) mem' a = rdW (e_W e) (e_mem e) a)
  by (intros a Ha Hw; apply HK; [exact Ha | exact Hw | cbv beta; intros []]).
assert (HLO : 4096 <= e_seg e /\ e_seg e + Z.of_nat (length (e_s e)) + 1 <= alloc_ceiling).
{ destruct HLOC as [(b & m & Hin & P1 & P2) | [(cid & pos & Hin & Hcid & P1 & P2) | Himg]].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Q0 & Q1 & Q2 & _ & _ & Qm).
    pose proof (req_size_pos m ltac:(lia)) as [S1 S2]. lia.
  - destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (F0 & F1 & F2). lia.
  - pose proof (pa_img_range (e_seg e) (proj1 (Himg (e_seg e) ltac:(lia)))) as K1.
    pose proof (pa_img_range (e_seg e + Z.of_nat (length (e_s e)))
      (proj1 (Himg (e_seg e + Z.of_nat (length (e_s e))) ltac:(lia)))) as K2.
    unfold kImgEnd in *. lia. }
destruct HLO as (HS0 & HS1).
assert (HSP16 : (spZ (e_regs e) - 64) mod 16 = 0).
{ replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16. }
split.
{ intros i Hi.
  assert (Hl : length (e_s e ++ [0]) = (length (e_s e) + 1)%nat) by (rewrite length_app; reflexivity).
  rewrite (HKK (e_seg e + Z.of_nat i) ltac:(lia) ltac:(lia)). apply HZS. lia. }
split;
  [|split; [exact HS0 | split; [lia | split; [lia | split; [exact HSP16 | split; [exact HNF | exact HL16]]]]]].
apply (vl_ra_ext (rdW (e_W e) (e_mem e))); [|exact A4].
intros x Hx. unfold shadow_of_addr.
assert (Hd1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (Hd2 : 8 * (x / 8) <= x) by (apply Z.mul_div_le; lia).
unfold amem_range in HMR. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *.
apply HKK; lia.
Qed.

(* one pass of the digit loop: from its head with j digits read, to its head with j + 1, or out to K2, or to
   the epilogue with 0 when the byte is no digit *)
Lemma vl_step : vs_KR_stmt B gotw guard -> vs_K2_stmt B gotw guard ->
  forall j, vs_KL_stmt B gotw guard (S j) -> vs_KL_stmt B gotw guard j.
Proof using.
intros HKR HK2 j HIH e regs' mem' md' di HE HC Hdot Hdi0 Hjlen Hdig R10 R11 R12 R13 R14 R20.
pose proof (AR_laws_ok SEGS B) as LAWS.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (vl_now e regs' mem' md' HE HC) as (HBY & HRA & HS0 & HS1 & HSP2 & HSP16 & HNF & HL16).
unfold vs_ctx0, vs_ctxW in HC. pose proof HC as (HJ & HREG & HSL & HK & HPRES).
pose proof HREG as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
unfold e_sp in *.
(* the byte a4 holds, and the byte this pass loads *)
remember (nth (S di + j) (e_s e) 0) as c eqn:Ec.
remember (nth (S di + S j) (e_s e ++ [0]) 0) as b eqn:Eb.
assert (Hnthc : nth (S di + j) (e_s e ++ [0]) 0 = c) by (rewrite Ec; apply app_nth1; lia).
assert (HVc : rdW (e_W e) mem' (e_seg e + Z.of_nat (S di + j)) = Some c)
  by (rewrite <- Hnthc; apply HBY; lia).
assert (Hcr : 0 <= c < 256) by exact (vl_view_range _ _ _ _ HVc).
assert (HV : rdW (e_W e) mem' (e_seg e + Z.of_nat di + 2 + Z.of_nat j) = Some b).
{ rewrite Eb. replace (e_seg e + Z.of_nat di + 2 + Z.of_nat j) with (e_seg e + Z.of_nat (S di + S j)) by lia.
  apply HBY. lia. }
assert (Hbr : 0 <= b < 256) by exact (vl_view_range _ _ _ _ HV).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b])))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b])))
  (mrestrict (w_H (e_W e)) mem')) by apply Forall_nil.
pose proof (vs_EE regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b])) as EV.
pose proof (vs_Ey regs' (e_regs e) [Z_to_bv 64 b] 0%nat ltac:(lia)) as E40.
cbn [Nat.add nth] in E40.
assert (E14 : bv_unsigned (ew (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b]))) 14) = c)
  by (rewrite (EV 14%nat 14%bv eq_refl), R14; apply unsigned_lit_small; lia).
assert (KA : forall a, aview SEGS (w_H (e_W e)) mem' a = aview SEGS (w_H (e_W e)) mem' a)
  by (intros a; reflexivity).
assert (PA : forall a, apresent (w_H (e_W e)) mem' a -> apresent (w_H (e_W e)) mem' a)
  by (intros a Ha; exact Ha).
pose proof (vl_seedB (e_W e) (e_regs e) regs' mem' VS_KL [(11%nat, mkAF 4096 (2 ^ 47 - 8) 0)]
  [Z_to_bv 64 b] vl_rKL 12%nat 0
  (e_seg e + Z.of_nat di + 2 + Z.of_nat j) b eq_refl ltac:(vm_compute; reflexivity)
  ltac:(replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL)
  ltac:(lia) ltac:(rewrite Hsp; exact HSP16) G22
  ltac:(split; [|exact I];
        apply (vl_fact0 _ 11 (e_seg e + Z.of_nat di + 2 + Z.of_nat j) 4096 (2 ^ 47 - 8));
        try lia; rewrite (EV 11%nat 11%bv eq_refl); exact R11)
  ltac:(rewrite (EV 12%nat 12%bv eq_refl); exact R12) eq_refl Hbr
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact HV)) as HS.
unfold vs_goal, vs_cfg.
(* 0x89c24 addi a4,a4,-48; 0x89c28 bltu a3,a4 *)
paj_run_tok RUN HS HJ SHOK VL_BSPAN.
{ vs_awr_ro. }
vl_mem KA PA.
psrr_branch_tok RUN BR HS SHOK VL_BSPAN.
- (* a4 - 48 >u 9: the byte is no digit, the code returns 0 *)
  rewrite branch_ltu_U in Hc.
  rewrite (U_atom _ 13 9 ltac:(vl_ew0; rewrite (EV 13%nat 13%bv eq_refl); exact R13) ltac:(lia)) in Hc.
  rewrite U_SOff in Hc. vl_ew0. rewrite E14 in Hc.
  unfold zcanon, M64 in Hc. replace (c + -48) with (c - 48) in Hc by lia.
  rewrite (reac_declared_vlan_split_lem.vs_digit_test c ltac:(lia)) in Hc.
  apply negb_true_iff in Hc.
  assert (HNONE : SegModel.vlan_split (e_s e) = None).
  { rewrite (reac_declared_vlan_split_lem.vs_code_eq (e_s e) HNF HL16).
    apply (reac_declared_vlan_split_lem.vs_none_nodigit (e_s e) di Hdot).
    apply (vl_forallb_false _ j); [rewrite length_skipn; lia|].
    rewrite reac_declared_vlan_split_lem.vs_tail_nth, <- Ec. exact Hc. }
  (* 0x89c84 li a0,0, then the epilogue *)
  paj_run_to_tok RUNTO HS HJ SHOK VL_BSPAN VS_KR.
  { vs_awr_ro. }
  vl_mem KA PA.
  pmkst HS.
  lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
    apply (vs_exit_KR B gotw guard HKR e (e_ly e) (e_S e) (e_W e) regs' mem' (ms_regs mF) (ms_mem mF) _ 0
      HE HREG HSL HJ
      (vl_regs_kept E2 ss2 mF (w_H (e_W e)) regs' HS ltac:(vl_EV EV)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)))
  end.
  + intros a Ha. apply KA.
  + vs_preg HS (10%bv : bv 5) F10. rewrite F10. reflexivity.
  + intros regs'' md'' H10. unfold vs_Q. rewrite HNONE.
    split; [exact H10|]. split; [exact I|]. split.
    * apply (vs_kept_step (e_W e) (e_mem e) (e_W e) mem' _ (e_regs e) STK_reac_declared_vlan_split _).
      -- apply (vs_kept_ctxW B e (fun _ => False) _ regs' mem' md' HC). intros a [].
      -- intros a Ha Hw He. apply KA.
    * split; [apply Permutation_refl|]. split; [reflexivity|].
      exists (st_fs (e_S e)). destruct (e_S e); reflexivity.
- (* the byte is a digit: the check of the next byte, then the lbu *)
  rewrite branch_ltu_U in Hc.
  rewrite (U_atom _ 13 9 ltac:(vl_ew0; rewrite (EV 13%nat 13%bv eq_refl); exact R13) ltac:(lia)) in Hc.
  rewrite U_SOff in Hc. vl_ew0. rewrite E14 in Hc.
  unfold zcanon, M64 in Hc. replace (c + -48) with (c - 48) in Hc by lia.
  rewrite (reac_declared_vlan_split_lem.vs_digit_test c ltac:(lia)) in Hc.
  apply negb_false_iff in Hc.
  (* 0x89c2c .. 0x89c48: the shadow byte of a1, the lbu of a2, the branch on the byte *)
  paj_run_tok RUN HS HJ SHOK VL_BSPAN.
  { eapply (obl_of_range SEGS (w_H (e_W e)) _ _ (SOff 22 0) _ 1 (e_seg e)
      (Z.of_nat (length (e_s e)) + 1)).
    - apply (vl_ra_ext (rdW (e_W e) mem')); [|exact HRA].
      intros x Hx. apply KA.
    - lazymatch goal with |- U ?E2 _ = _ =>
        rewrite (U_atom E2 22 SB ltac:(vl_ew0; rewrite (EV 22%nat 22%bv eq_refl); exact G22)
          ltac:(unfold SB; lia)) end.
      unfold SB, SHADOW_OFF. reflexivity.
    - lazymatch goal with |- _ <= U ?E2 _ =>
        rewrite (U_atom E2 11 (e_seg e + Z.of_nat di + 2 + Z.of_nat j)
          ltac:(vl_ew0; rewrite (EV 11%nat 11%bv eq_refl); exact R11) ltac:(lia)) end.
      lia.
    - lazymatch goal with |- U ?E2 _ + _ <= _ =>
        rewrite (U_atom E2 11 (e_seg e + Z.of_nat di + 2 + Z.of_nat j)
          ltac:(vl_ew0; rewrite (EV 11%nat 11%bv eq_refl); exact R11) ltac:(lia)) end.
      lia. }
  { vs_awr_ro. }
  vl_mem KA PA.
  psrr_branch_tok RUN BR HS SHOK VL_BSPAN.
  + (* the byte is not the NUL: one more digit, back to the head *)
    rewrite branch_ne_U in Hc0.
    lazymatch type of Hc0 with context [U ?E2 (SExt false 8 (SOff 40 0))] =>
      rewrite (U_zext E2 8 (SOff 40 0)),
              (U_atom E2 40 b ltac:(vl_ew0; exact E40) ltac:(lia)) in Hc0 end.
    change (2 ^ Z.of_N 8) with 256 in Hc0.
    rewrite (Z.mod_small b 256 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc0.
    apply negb_true_iff, Z.eqb_neq in Hc0.
    assert (Hlt : (S di + S j < length (e_s e))%nat).
    { destruct (Nat.lt_ge_cases (S di + S j) (length (e_s e))) as [Hq|Hq]; [exact Hq|].
      exfalso. apply Hc0. rewrite Eb. replace (S di + S j)%nat with (length (e_s e)) by lia.
      apply nth_middle. }
    assert (Hnb : nth (S di + S j) (e_s e ++ [0]) 0 = nth (S di + S j) (e_s e) 0)
      by (apply app_nth1; lia).
    paj_run_to_tok RUNTO HS HJ SHOK VL_BSPAN VS_KL.
    { vs_awr_ro. }
    vl_mem KA PA.
    pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
      apply (HIH e (ms_regs mF) (ms_mem mF) _ di HE)
    end.
    * unfold vs_ctx0, vs_ctxW. split; [exact HJ|].
      split.
      { lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
          exact (vl_regs_of E2 ss2 mF (w_H (e_W e)) e regs' HS ltac:(vl_EV EV) HREG
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity)) end. }
      split; [apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL | intros a Ha; apply KA]|].
      split; [intros a Ha Hw He; rewrite (KA a); apply HK; [exact Ha | exact Hw | intros []]|].
      intros a Ha. apply PA. apply HPRES. exact Ha.
    * exact Hdot.
    * exact Hdi0.
    * exact Hlt.
    * rewrite (reac_declared_vlan_split_lem.vs_forallb_firstn_S (vs_tail e di) j
        ltac:(unfold vs_tail; rewrite length_skipn; lia)).
      rewrite Hdig. cbn [andb]. unfold vs_tail.
      rewrite reac_declared_vlan_split_lem.vs_tail_nth, <- Ec. exact Hc.
    * vs_preg HS (10%bv : bv 5) F10. rewrite F10.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_den E2 10 (e_seg e + Z.of_nat di + 1) 0
          ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
      unfold w64; f_equal; lia.
    * vs_preg HS (11%bv : bv 5) F11. rewrite F11.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_den E2 11 (e_seg e + Z.of_nat di + 2 + Z.of_nat j) 1
          ltac:(vl_ew0; rewrite (EV 11%nat 11%bv eq_refl); exact R11) ltac:(lia) ltac:(lia)) end.
      unfold w64; f_equal; lia.
    * vs_preg HS (12%bv : bv 5) F12. rewrite F12.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_den E2 12 (e_seg e + Z.of_nat di + 2 + Z.of_nat j) 1
          ltac:(vl_ew0; rewrite (EV 12%nat 12%bv eq_refl); exact R12) ltac:(lia) ltac:(lia)) end.
      unfold w64; f_equal; lia.
    * vs_preg HS (13%bv : bv 5) F13. rewrite F13.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_den E2 13 9 0 ltac:(vl_ew0; rewrite (EV 13%nat 13%bv eq_refl); exact R13)
          ltac:(lia) ltac:(lia)) end.
      unfold w64; f_equal; lia.
    * vs_preg HS (14%bv : bv 5) F14. rewrite F14.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_zext_byte E2 40 b ltac:(vl_ew0; exact E40) ltac:(lia)) end.
      rewrite Eb, Hnb. reflexivity.
    * vs_preg HS (20%bv : bv 5) F20. rewrite F20.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_den E2 20 (e_seg e + Z.of_nat di) 0
          ltac:(vl_ew0; rewrite (EV 20%nat 20%bv eq_refl); exact R20) ltac:(lia) ltac:(lia)) end.
      unfold w64; f_equal; lia.
  + (* the byte is the NUL: the tail is a run of digits, on to K2 *)
    rewrite branch_ne_U in Hc0.
    lazymatch type of Hc0 with context [U ?E2 (SExt false 8 (SOff 40 0))] =>
      rewrite (U_zext E2 8 (SOff 40 0)),
              (U_atom E2 40 b ltac:(vl_ew0; exact E40) ltac:(lia)) in Hc0 end.
    change (2 ^ Z.of_N 8) with 256 in Hc0.
    rewrite (Z.mod_small b 256 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc0.
    apply negb_false_iff, Z.eqb_eq in Hc0.
    assert (Heq : (S di + S j)%nat = length (e_s e)).
    { destruct (Nat.lt_ge_cases (S di + S j) (length (e_s e))) as [Hq|Hq]; [|lia].
      exfalso. apply HNF.
      assert (Hz : nth (S di + S j) (e_s e) 0 = 0)
        by (rewrite <- (app_nth1 (e_s e) [0] 0 Hq), <- Eb; exact Hc0).
      rewrite <- Hz. apply nth_In. exact Hq. }
    assert (Hlen2 : length (vs_tail e di) = S j) by (unfold vs_tail; rewrite length_skipn; lia).
    assert (Hall : forallb SegModel.isdigit (vs_tail e di) = true).
    { replace (vs_tail e di) with (firstn (S j) (vs_tail e di)) by (apply firstn_all2; lia).
      rewrite (reac_declared_vlan_split_lem.vs_forallb_firstn_S (vs_tail e di) j ltac:(lia)).
      rewrite Hdig. cbn [andb]. unfold vs_tail.
      rewrite reac_declared_vlan_split_lem.vs_tail_nth, <- Ec. exact Hc. }
    paj_run_to_tok RUNTO HS HJ SHOK VL_BSPAN VS_K2.
    { vs_awr_ro. }
    vl_mem KA PA.
    pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
      apply (HK2 e (ms_regs mF) (ms_mem mF) _ di HE)
    end.
    * unfold vs_ctx0, vs_ctxW. split; [exact HJ|].
      split.
      { lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
          exact (vl_regs_of E2 ss2 mF (w_H (e_W e)) e regs' HS ltac:(vl_EV EV) HREG
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity)) end. }
      split; [apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL | intros a Ha; apply KA]|].
      split; [intros a Ha Hw He; rewrite (KA a); apply HK; [exact Ha | exact Hw | intros []]|].
      intros a Ha. apply PA. apply HPRES. exact Ha.
    * exact Hdot.
    * exact Hdi0.
    * intros Hnil. assert (length (vs_tail e di) = 0%nat) by (rewrite Hnil; reflexivity). lia.
    * exact Hall.
    * vs_preg HS (10%bv : bv 5) F10. rewrite F10.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_den E2 10 (e_seg e + Z.of_nat di + 1) 0
          ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
      unfold w64; f_equal; lia.
    * vs_preg HS (20%bv : bv 5) F20. rewrite F20.
      lazymatch goal with |- sv_denot ?E2 _ = _ =>
        rewrite (vl_den E2 20 (e_seg e + Z.of_nat di) 0
          ltac:(vl_ew0; rewrite (EV 20%nat 20%bv eq_refl); exact R20) ltac:(lia) ltac:(lia)) end.
      unfold w64; f_equal; lia.
Qed.

(* the digit loop at any pass: the segment is shorter than 16 bytes, so 16 passes exhaust it *)
Lemma vs_KL_all : vs_KR_stmt B gotw guard -> vs_K2_stmt B gotw guard ->
  forall j, vs_KL_stmt B gotw guard j.
Proof using.
intros HKR HK2.
assert (Hind : forall k j, (16 <= j + k)%nat -> vs_KL_stmt B gotw guard j).
{ induction k as [|k IH]; intros j Hk.
  - intros e regs' mem' md' di HE HC Hdot Hdi0 Hjlen Hdig R10 R11 R12 R13 R14 R20.
    exfalso. pose proof (vl_now e regs' mem' md' HE HC) as (_ & _ & _ & _ & _ & _ & _ & HL16). lia.
  - exact (vl_step HKR HK2 j (IH (S j) ltac:(lia))). }
intros j. exact (Hind 16%nat j ltac:(lia)).
Qed.

(* K1, 0x89bec: strrchr's answer is in a0; the three tests before the digit loop *)
Lemma vs_K1 : vs_KR_stmt B gotw guard -> vs_K2_stmt B gotw guard -> vs_K1_stmt B gotw guard.
Proof using.
intros HKR HK2 e regs' mem' md' r HE HC R10 Hr.
pose proof (AR_laws_ok SEGS B) as LAWS.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (vl_now e regs' mem' md' HE HC) as (HBY & HRA & HS0 & HS1 & HSP2 & HSP16 & HNF & HL16).
pose proof HE as (HPRE & HRO & R10e & Rseg & R11e & Rpar & R12e & R13e & Rvid & HSP & HNEV).
pose proof HSP as (Hseg0 & _).
unfold vs_ctx0, vs_ctxW in HC. pose proof HC as (HJ & HREG & HSL & HK & HPRES).
pose proof HREG as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
unfold e_sp in *.
(* the post of every exit of this point, all of which return 0 *)
assert (HQ0 : forall (mF : word -> option byte),
  (forall a, aview SEGS (w_H (e_W e)) mF a = aview SEGS (w_H (e_W e)) mem' a) ->
  SegModel.vlan_split (e_s e) = None ->
  forall regs'' md'', getr regs'' 10 = w64 0 ->
  vs_Q B e (e_ly e) (e_S e) (e_W e) regs'' mF md'').
{ intros mF KF HNONE regs'' md'' H10. unfold vs_Q. rewrite HNONE.
  split; [exact H10|]. split; [exact I|]. split.
  - apply (vs_kept_step (e_W e) (e_mem e) (e_W e) mem' _ (e_regs e) STK_reac_declared_vlan_split _).
    + apply (vs_kept_ctxW B e (fun _ => False) _ regs' mem' md' HC). intros a [].
    + intros a Ha Hw He. apply KF.
  - split; [apply Permutation_refl|]. split; [reflexivity|].
    exists (st_fs (e_S e)). destruct (e_S e); reflexivity. }
destruct Hr as [(Hr0 & Hnone) | (di & Hdot & Hrdi)].
- (* strrchr found no dot: a0 = 0, the code returns 0 *)
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [])))) by apply Eimg_env.
  assert (SHOK : sh_ok SEGS (SOff 22 0) [] (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [])))
    (mrestrict (w_H (e_W e)) mem')) by apply Forall_nil.
  pose proof (vs_EE regs' (vs_xs (e_regs e) ++ [])) as EV.
  assert (KA : forall a, aview SEGS (w_H (e_W e)) mem' a = aview SEGS (w_H (e_W e)) mem' a)
    by (intros a; reflexivity).
  assert (PA : forall a, apresent (w_H (e_W e)) mem' a -> apresent (w_H (e_W e)) mem' a)
    by (intros a Ha; exact Ha).
  assert (HNONE : SegModel.vlan_split (e_s e) = None).
  { rewrite (reac_declared_vlan_split_lem.vs_code_eq (e_s e) HNF HL16).
    apply (reac_declared_vlan_split_lem.vs_none_dot (e_s e) Hnone). }
  pose proof (vs_seedK (e_W e) (e_regs e) regs' mem' VS_K1 [] []
    ltac:(replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL)
    ltac:(lia) ltac:(rewrite Hsp; exact HSP16) G22 I) as HS.
  unfold vs_goal, vs_cfg.
  (* 0x89bec mv s4,a0; li a0,0; beqz s4 *)
  paj_run_tok RUN HS HJ SHOK VL_BSPAN.
  { vs_awr_ro. }
  vl_mem KA PA.
  psrr_branch_tok RUN BR HS SHOK VL_BSPAN.
  + (* s4 = 0: the epilogue *)
    paj_run_to_tok RUNTO HS HJ SHOK VL_BSPAN VS_KR.
    { vs_awr_ro. }
    vl_mem KA PA.
    pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
      apply (vs_exit_KR B gotw guard HKR e (e_ly e) (e_S e) (e_W e) regs' mem' (ms_regs mF) (ms_mem mF) _ 0
        HE HREG HSL HJ
        (vl_regs_kept E2 ss2 mF (w_H (e_W e)) regs' HS ltac:(vl_EV EV)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)))
    end.
    * intros a Ha. apply KA.
    * vs_preg HS (10%bv : bv 5) F10. rewrite F10. reflexivity.
    * lazymatch goal with |- forall _ _, _ -> vs_Q _ _ _ _ _ _ ?mF _ =>
        exact (HQ0 mF KA HNONE) end.
  + (* s4 <> 0 is impossible: a0 is 0 *)
    exfalso. rewrite branch_eq_U in Hc.
    rewrite (U_atom _ 10 r ltac:(rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia)),
      (U_lit _ 0 ltac:(lia)) in Hc.
    apply Z.eqb_neq in Hc. lia.
- (* strrchr found a dot at di *)
  pose proof (reac_declared_vlan_split_lem.vs_di_lt (e_s e) di HNF Hdot) as Hdilt.
  assert (Hrr : 4096 <= r <= 2 ^ 47 - 8) by lia.
  destruct (Nat.eq_dec di 0) as [Hdi0 | Hdi0].
  + (* the dot is the first byte: the code returns 0 *)
    assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [])))) by apply Eimg_env.
    assert (SHOK : sh_ok SEGS (SOff 22 0) [] (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [])))
      (mrestrict (w_H (e_W e)) mem')) by apply Forall_nil.
    pose proof (vs_EE regs' (vs_xs (e_regs e) ++ [])) as EV.
    assert (KA : forall a, aview SEGS (w_H (e_W e)) mem' a = aview SEGS (w_H (e_W e)) mem' a)
      by (intros a; reflexivity).
    assert (PA : forall a, apresent (w_H (e_W e)) mem' a -> apresent (w_H (e_W e)) mem' a)
      by (intros a Ha; exact Ha).
    assert (HNONE : SegModel.vlan_split (e_s e) = None).
    { rewrite (reac_declared_vlan_split_lem.vs_code_eq (e_s e) HNF HL16).
      apply (reac_declared_vlan_split_lem.vs_none_first (e_s e)). rewrite Hdot, Hdi0. reflexivity. }
    pose proof (vs_seedK (e_W e) (e_regs e) regs' mem' VS_K1 [] []
      ltac:(replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL)
      ltac:(lia) ltac:(rewrite Hsp; exact HSP16) G22 I) as HS.
    unfold vs_goal, vs_cfg.
    paj_run_tok RUN HS HJ SHOK VL_BSPAN.
    { vs_awr_ro. }
    vl_mem KA PA.
    psrr_branch_tok RUN BR HS SHOK VL_BSPAN.
    * (* s4 = 0 is impossible: the segment is not 0 *)
      exfalso. rewrite branch_eq_U in Hc.
      rewrite (U_atom _ 10 r ltac:(rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia)),
        (U_lit _ 0 ltac:(lia)) in Hc.
      apply Z.eqb_eq in Hc. lia.
    * (* 0x89bf8 beq s4,s2 *)
      paj_run_tok RUN HS HJ SHOK VL_BSPAN.
      { vs_awr_ro. }
      vl_mem KA PA.
      psrr_branch_tok RUN BR HS SHOK VL_BSPAN.
      -- (* taken: the epilogue *)
         paj_run_to_tok RUNTO HS HJ SHOK VL_BSPAN VS_KR.
         { vs_awr_ro. }
         vl_mem KA PA.
         pmkst HS.
         lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
           apply (vs_exit_KR B gotw guard HKR e (e_ly e) (e_S e) (e_W e) regs' mem'
             (ms_regs mF) (ms_mem mF) _ 0 HE HREG HSL HJ
             (vl_regs_kept E2 ss2 mF (w_H (e_W e)) regs' HS ltac:(vl_EV EV)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)))
         end.
         ++ intros a Ha. apply KA.
         ++ vs_preg HS (10%bv : bv 5) F10. rewrite F10. reflexivity.
         ++ lazymatch goal with |- forall _ _, _ -> vs_Q _ _ _ _ _ _ ?mF _ =>
              exact (HQ0 mF KA HNONE) end.
      -- (* not taken is impossible: the dot is the segment *)
         exfalso.
         lazymatch type of Hc0 with context [sv_denot ?E2 (SOff 10 0)] =>
           rewrite branch_eq_U,
             (U_atom E2 10 r ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia)),
             (U_atom E2 18 (e_seg e) ltac:(vl_ew0; rewrite (EV 18%nat 18%bv eq_refl); exact G18)
               ltac:(lia)) in Hc0 end.
         apply Z.eqb_neq in Hc0. apply Hc0. rewrite Hrdi, Hdi0. cbn [Z.of_nat]. lia.
  + (* a dot inside the segment: the byte after it decides *)
    remember (nth (S di) (e_s e ++ [0]) 0) as b eqn:Eb.
    assert (HV : rdW (e_W e) mem' (r + 1) = Some b).
    { rewrite Eb, Hrdi. replace (e_seg e + Z.of_nat di + 1) with (e_seg e + Z.of_nat (S di)) by lia.
      apply HBY. lia. }
    assert (Hbr : 0 <= b < 256) by exact (vl_view_range _ _ _ _ HV).
    assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b]))))
      by apply Eimg_env.
    assert (SHOK : sh_ok SEGS (SOff 22 0) [] (Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b])))
      (mrestrict (w_H (e_W e)) mem')) by apply Forall_nil.
    pose proof (vs_EE regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b])) as EV.
    pose proof (vs_Ey regs' (e_regs e) [Z_to_bv 64 b] 0%nat ltac:(lia)) as E40.
    cbn [Nat.add nth] in E40.
    assert (KA : forall a, aview SEGS (w_H (e_W e)) mem' a = aview SEGS (w_H (e_W e)) mem' a)
      by (intros a; reflexivity).
    assert (PA : forall a, apresent (w_H (e_W e)) mem' a -> apresent (w_H (e_W e)) mem' a)
      by (intros a Ha; exact Ha).
    pose proof (vl_seedB (e_W e) (e_regs e) regs' mem' VS_K1 [(10%nat, mkAF 4096 (2 ^ 47 - 8) 0)]
      [Z_to_bv 64 b] vl_rK1 10%nat 1 r b eq_refl ltac:(vm_compute; reflexivity)
      ltac:(replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL)
      ltac:(lia) ltac:(rewrite Hsp; exact HSP16) G22
      ltac:(split; [|exact I];
            apply (vl_fact0 _ 10 r 4096 (2 ^ 47 - 8));
            try lia; rewrite (EV 10%nat 10%bv eq_refl); exact R10)
      ltac:(rewrite (EV 10%nat 10%bv eq_refl); exact R10) eq_refl Hbr
      ltac:(lia) ltac:(lia) ltac:(lia) HV) as HS.
    unfold vs_goal, vs_cfg.
    paj_run_tok RUN HS HJ SHOK VL_BSPAN.
    { vs_awr_ro. }
    vl_mem KA PA.
    psrr_branch_tok RUN BR HS SHOK VL_BSPAN.
    * (* the dot is the segment: impossible, di is not 0 *)
      exfalso. rewrite branch_eq_U in Hc.
      rewrite (U_atom _ 10 r ltac:(rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia)),
        (U_atom _ 18 (e_seg e) ltac:(rewrite (EV 18%nat 18%bv eq_refl); exact G18) ltac:(lia)) in Hc.
      apply Z.eqb_eq in Hc. lia.
    * (* 0x89bfc: the shadow byte of dot + 1, the lbu, the branch on it *)
      paj_run_tok RUN HS HJ SHOK VL_BSPAN.
      { eapply (obl_of_range SEGS (w_H (e_W e)) _ _ (SOff 22 0) _ 1 (e_seg e)
          (Z.of_nat (length (e_s e)) + 1)).
        - apply (vl_ra_ext (rdW (e_W e) mem')); [|exact HRA]. intros x Hx. apply KA.
        - lazymatch goal with |- U ?E2 _ = _ =>
            rewrite (U_atom E2 22 SB ltac:(vl_ew0; rewrite (EV 22%nat 22%bv eq_refl); exact G22)
              ltac:(unfold SB; lia)) end.
          unfold SB, SHADOW_OFF. reflexivity.
        - lazymatch goal with |- _ <= U ?E2 _ =>
            rewrite (U_atom_off E2 10 r 1
              ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
          lia.
        - lazymatch goal with |- U ?E2 _ + _ <= _ =>
            rewrite (U_atom_off E2 10 r 1
              ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
          lia. }
      { vs_awr_ro. }
      vl_mem KA PA.
      psrr_branch_tok RUN BR HS SHOK VL_BSPAN.
      -- (* the byte after the dot is the NUL: the code returns 0 *)
         lazymatch type of Hc0 with context [sv_denot ?E2 (SExt false 8 (SOff 40 0))] =>
           rewrite branch_eq_U, (U_zext E2 8 (SOff 40 0)),
             (U_atom E2 40 b ltac:(vl_ew0; exact E40) ltac:(lia)) in Hc0 end.
         change (2 ^ Z.of_N 8) with 256 in Hc0.
         rewrite (Z.mod_small b 256 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc0.
         apply Z.eqb_eq in Hc0.
         assert (Heq : (S di)%nat = length (e_s e)).
         { destruct (Nat.lt_ge_cases (S di) (length (e_s e))) as [Hq|Hq]; [|lia].
           exfalso. apply HNF.
           assert (Hz : nth (S di) (e_s e) 0 = 0)
             by (rewrite <- (app_nth1 (e_s e) [0] 0 Hq), <- Eb; exact Hc0).
           rewrite <- Hz. apply nth_In. exact Hq. }
         assert (HNONE : SegModel.vlan_split (e_s e) = None).
         { rewrite (reac_declared_vlan_split_lem.vs_code_eq (e_s e) HNF HL16).
           apply (reac_declared_vlan_split_lem.vs_none_empty (e_s e) di Hdot).
           apply skipn_all2. lia. }
         paj_run_to_tok RUNTO HS HJ SHOK VL_BSPAN VS_KR.
         { vs_awr_ro. }
         vl_mem KA PA.
         pmkst HS.
         lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
           apply (vs_exit_KR B gotw guard HKR e (e_ly e) (e_S e) (e_W e) regs' mem'
             (ms_regs mF) (ms_mem mF) _ 0 HE HREG HSL HJ
             (vl_regs_kept E2 ss2 mF (w_H (e_W e)) regs' HS ltac:(vl_EV EV)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)))
         end.
         ++ intros a Ha. apply KA.
         ++ vs_preg HS (10%bv : bv 5) F10. rewrite F10. reflexivity.
         ++ lazymatch goal with |- forall _ _, _ -> vs_Q _ _ _ _ _ _ ?mF _ =>
              exact (HQ0 mF KA HNONE) end.
      -- (* a byte after the dot: the head of the digit loop *)
         lazymatch type of Hc0 with context [sv_denot ?E2 (SExt false 8 (SOff 40 0))] =>
           rewrite branch_eq_U, (U_zext E2 8 (SOff 40 0)),
             (U_atom E2 40 b ltac:(vl_ew0; exact E40) ltac:(lia)) in Hc0 end.
         change (2 ^ Z.of_N 8) with 256 in Hc0.
         rewrite (Z.mod_small b 256 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc0.
         apply Z.eqb_neq in Hc0.
         assert (Hlt : (S di + 0 < length (e_s e))%nat).
         { destruct (Nat.lt_ge_cases (S di) (length (e_s e))) as [Hq|Hq]; [lia|].
           exfalso. apply Hc0. rewrite Eb. replace (S di) with (length (e_s e)) by lia.
           apply nth_middle. }
         assert (Hnb : nth (S di) (e_s e ++ [0]) 0 = nth (S di + 0) (e_s e) 0)
           by (replace (S di + 0)%nat with (S di) by lia; apply app_nth1; lia).
         paj_run_to_tok RUNTO HS HJ SHOK VL_BSPAN VS_KL.
         { vs_awr_ro. }
         vl_mem KA PA.
         pmkst HS.
         lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
           apply (vs_KL_all HKR HK2 0%nat e (ms_regs mF) (ms_mem mF) _ di HE)
         end.
         ++ unfold vs_ctx0, vs_ctxW. split; [exact HJ|].
            split.
            { lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?mF) |- _ =>
                exact (vl_regs_of E2 ss2 mF (w_H (e_W e)) e regs' HS ltac:(vl_EV EV) HREG
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)) end. }
            split; [apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL | intros a Ha; apply KA]|].
            split; [intros a Ha Hw He; rewrite (KA a); apply HK; [exact Ha | exact Hw | intros []]|].
            intros a Ha. apply PA. apply HPRES. exact Ha.
         ++ exact Hdot.
         ++ exact Hdi0.
         ++ exact Hlt.
         ++ reflexivity.
         ++ vs_preg HS (10%bv : bv 5) F10. rewrite F10.
            lazymatch goal with |- sv_denot ?E2 _ = _ =>
              rewrite (vl_den E2 10 r 1
                ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
            rewrite Hrdi. unfold w64; f_equal; lia.
         ++ vs_preg HS (11%bv : bv 5) F11. rewrite F11.
            lazymatch goal with |- sv_denot ?E2 _ = _ =>
              rewrite (vl_den E2 10 r 2
                ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
            rewrite Hrdi. unfold w64; f_equal; lia.
         ++ vs_preg HS (12%bv : bv 5) F12. rewrite F12.
            lazymatch goal with |- sv_denot ?E2 _ = _ =>
              rewrite (vl_den E2 10 r 2
                ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
            rewrite Hrdi. unfold w64; f_equal; lia.
         ++ vs_preg HS (13%bv : bv 5) F13. rewrite F13. reflexivity.
         ++ vs_preg HS (14%bv : bv 5) F14. rewrite F14.
            lazymatch goal with |- sv_denot ?E2 _ = _ =>
              rewrite (vl_zext_byte E2 40 b ltac:(vl_ew0; exact E40) ltac:(lia)) end.
            rewrite Eb, Hnb. reflexivity.
         ++ vs_preg HS (20%bv : bv 5) F20. rewrite F20.
            lazymatch goal with |- sv_denot ?E2 _ = _ =>
              rewrite (vl_den E2 10 r 0
                ltac:(vl_ew0; rewrite (EV 10%nat 10%bv eq_refl); exact R10) ltac:(lia) ltac:(lia)) end.
            rewrite Hrdi. unfold w64; f_equal; lia.
Qed.

End e.
End f.
End d.
