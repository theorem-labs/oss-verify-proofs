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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 315 of its 363 lines of code are new or changed and 405 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the point K3 (listing offset 0x5548,
   image B 0x8a308), after the strtol wrapper; a0 = v, strtol's value of the tail, s4 = dot. Image A's walk has no
   K3 file yet (commit ceb7e39832b2 has K6 and KR only), so this one is written for image B.
     0x8a308 `mv s5,a0`; 0x8a30c-0x8a318 a0 = v - 4095, a1 = -4094 (`lui a1,0xfffff; addiw a1,a1,2`);
     0x8a31c `bgeu a0,a1` to 0x8a34c iff 1 <= v <= 4094 (vs_range_test; v = strtol10 of at most 14 digits is in
       [0, 10^14), vs3_strtol_lt); not taken: 0x8a320 `li a0,0` and the epilogue KR with vlan_split = None
       (vs_code_eq, vs_none_range).
     0x8a34c `sub s4,s4,s2` (s4 = plen = di); `addi a1,s4,1`; `li a0,0`;
     0x8a358 `bltu s3,a1` to KR: refuted at the branch, s3 = 16 and di + 1 <= 15 (vs_plen_small);
     0x8a35c `li a2,16`; 0x8a360 `bltu a2,a1` to KR: refuted at the branch the same way;
     0x8a364 `mv a0,s2`; 0x8a368 `jal` the strlen wrapper (trampoline SS___interceptor_trampoline_strlen), its
       contract RtString.astrlen_realizes through PaArt.aj_art_at; it returns to K4 (0x8a36c) with a0 = length s.
   The stretch has no instrumented check, no store and no branch to the UBSan trap `unimp` 0x8a3d8. The wrapper's
   post keeps every byte outside its scratch window (E = False), so vs_ctx0 holds at K4. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition vs_Bx3 : sv := SOff 22 0.
Definition vs_Bspan3 : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* strtol10 of a run of digits is below 10 ^ (its length) *)
Lemma vs3_fold_lt : forall l acc, 0 <= acc -> forallb SegModel.isdigit l = true ->
  0 <= fold_left SegModel.dstep l acc < (acc + 1) * 10 ^ Z.of_nat (length l).
Proof.
induction l as [|d l IH]; intros acc Hacc H.
- cbn [fold_left length]. change (10 ^ Z.of_nat 0) with 1. lia.
- cbn [fold_left length forallb] in *. apply andb_true_iff in H as [Hd Hl]. apply SegModel.isdigit_range in Hd.
  specialize (IH (SegModel.dstep acc d) ltac:(unfold SegModel.dstep; lia) Hl).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. unfold SegModel.dstep in *.
  pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (length l)) ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma vs3_strtol_lt : forall l, forallb SegModel.isdigit l = true -> 0 <= SegModel.strtol10 l < 10 ^ Z.of_nat (length l).
Proof. intros l H. rewrite SegModel.strtol10_fold. pose proof (vs3_fold_lt l 0 ltac:(lia) H). lia. Qed.

(* the two register words of 0x8a34c / 0x8a350 as the run leaves them (s4 = -s2 + dot, a1 = (s2 * (2^64 - 1) + 1)
   + dot) are di and di + 1 for dot = segment + di; vs3_mod3 folds the nested reductions mod 2^64 *)
Lemma vs3_mod3 : forall a b c, ((a mod 2 ^ 64 + b) mod 2 ^ 64 + c) mod 2 ^ 64 = (a + b + c) mod 2 ^ 64.
Proof.
intros a b c. rewrite (Z.add_mod_idemp_l (a mod 2 ^ 64 + b) c (2 ^ 64)) by lia.
rewrite <- (Z.add_assoc (a mod 2 ^ 64) b c). rewrite (Z.add_mod_idemp_l a (b + c) (2 ^ 64)) by lia.
rewrite Z.add_assoc. reflexivity.
Qed.
Lemma vs3_U_dot : forall E seg d, ew E 18 = Z_to_bv 64 seg -> ew E 20 = Z_to_bv 64 (seg + d) ->
  0 <= seg < 2 ^ 64 -> 0 <= seg + d < 2 ^ 64 -> 0 <= d < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 18 0) (SLit (-1))) (SOff 20 0)) = d.
Proof.
intros E seg d H18 H20 Hs Hsd Hd.
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw]. rewrite H18, H20, !unsigned_lit_small by lia.
rewrite !Z.add_0_r. rewrite (zcanon_small seg), (zcanon_small (seg + d)) by lia.
replace (zcanon (-1)) with 18446744073709551615 by reflexivity.
assert (HM : M64 = 2 ^ 64) by reflexivity. unfold zcanon. rewrite HM.
rewrite (Z.add_mod_idemp_l (seg * 18446744073709551615) (seg + d) (2 ^ 64)) by lia.
replace (seg * 18446744073709551615 + (seg + d)) with (d + seg * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma vs3_U_plen : forall E seg d, ew E 18 = Z_to_bv 64 seg -> ew E 20 = Z_to_bv 64 (seg + d) ->
  0 <= seg < 2 ^ 64 -> 0 <= seg + d < 2 ^ 64 -> 0 <= d + 1 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 18 0) (SLit 18446744073709551615)) (SLit 1)) (SOff 20 0)) = d + 1.
Proof.
intros E seg d H18 H20 Hs Hsd Hd.
rewrite !U_SAlu, U_SMd, !U_SOff, !U_SLit. cbn [zalu_raw zmd_raw]. rewrite H18, H20, !unsigned_lit_small by lia.
rewrite !Z.add_0_r. rewrite (zcanon_small seg), (zcanon_small (seg + d)), (zcanon_small 18446744073709551615),
  (zcanon_small 1) by lia.
assert (HM : M64 = 2 ^ 64) by reflexivity. unfold zcanon. rewrite HM.
rewrite vs3_mod3.
replace (seg * 18446744073709551615 + 1 + (seg + d)) with ((d + 1) + seg * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma vs3_set_fs_id : forall S : astate, S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a register a run left as its atom n, at a state stopped at a call *)
Lemma vs3_reg_call : forall E ss (ms : machine_state) (H : word -> bool) n (r : bv 5) w,
  st_ok SEGS E ss (restrict H ms) -> ew E n = w -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = w.
Proof using.
intros E ss ms H n r w HS Hn Hs. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hs.
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the memory facts of the entry carried across a run of the body that writes nothing: KEEP and PRS from the
   entry state mem0 move to the run's last memory *)
Ltac vs3_keep W0 m0 KEEP PRS :=
  lazymatch goal with
  | Hfr : frame_of _ _ (mrestrict _ ?ma) (mrestrict _ ?mb), Hg : mem_grows (mrestrict _ ?ma) (mrestrict _ ?mb) |- _ =>
    let UN := fresh "UN" in let K2 := fresh "K2" in let P2 := fresh "P2" in
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
      ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
            intros b wlo whi x Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN;
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W0) mb a = aview SEGS (w_H W0) m0 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite (UN a Ha (fun x => x)); exact (KEEP a Ha));
    assert (P2 : forall a, apresent (w_H W0) m0 a -> apresent (w_H W0) mb a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a Hg (PRS a Ha)));
    clear UN KEEP PRS; rename K2 into KEEP; rename P2 into PRS
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ => clear old end;
  try (match goal with m : machine_state |- _ => rename m into ms end).

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis TL : PALib B.

(* an object that lies in a heap block, a side-stack frame or the image ends at or below the allocator's ceiling *)
Lemma vs3_loc_low : forall ly S W mem md q n, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q n -> 0 < n ->
  q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR HL Hn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & B0 & B1 & B2 & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & F2). lia.
- destruct (HI (q + n - 1) ltac:(lia)) as (Hi & _ & _). pose proof (pa_segs_low _ Hi) as R. lia.
Qed.

Lemma vs_K3 : vs_KR_stmt B gotw guard -> vs_K4_stmt B gotw guard -> vs_K3_stmt B gotw guard.
Proof using STRLEN TL.
intros HKR HK4. unfold vs_K3_stmt. intros e regs' mem' md' di HE HC Hdi Hdi0 Hne Hdig R10 R20.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj2 (@YG0f.ASAN_CEIL_range _)) as CM. unfold YG0f.ASAN_CEIL in CM.
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
pose proof HC as (HJ & HR & HSL & HKP & HPR).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
assert (HVS : VS_STK = 12352) by reflexivity. assert (HE4 : ESTACK = 4096) by reflexivity.
unfold e_sp in *.
(* the model: the tail, its value v, the segment's length and place *)
remember (SegModel.strtol10 (vs_tail e di)) as v eqn:Hveq in R10.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
pose proof (vs_di_lt _ _ Hnul Hdi) as Hdil.
pose proof (vs_plen_small _ _ Hnul Hlen Hdi) as Hpl.
assert (Hvb : 0 <= v < 2 ^ 63).
{ pose proof (vs3_strtol_lt _ Hdig) as Hb. rewrite <- Hveq in Hb.
  assert (Htl : (length (vs_tail e di) <= 14)%nat) by (unfold vs_tail; rewrite length_skipn; lia).
  assert (Hp : 10 ^ Z.of_nat (length (vs_tail e di)) <= 10 ^ 14) by (apply Z.pow_le_mono_r; lia). lia. }
pose proof Hsadd as (Q0 & Q63 & Qam & Qra & Qsh).
pose proof (vs3_loc_low _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as Hlow.
assert (Ham47 : e_seg e + Z.of_nat (length (e_s e)) + 1 <= 2 ^ 47) by (unfold amem_range in Qam; lia).
(* the seeded state at K3 *)
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K3 [])
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K3)) mem' (seg_rom SEGS)))).
{ apply vs_seedK.
  - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
  - lia.
  - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  - exact G22.
  - exact I. }
clearbody E.
assert (E18 : ew E 18 = Z_to_bv 64 (e_seg e)) by (rewrite (EV 18%nat 18%bv eq_refl); exact G18).
assert (E20 : ew E 20 = Z_to_bv 64 (e_seg e + Z.of_nat di)) by (rewrite (EV 20%nat 20%bv eq_refl); exact R20).
assert (SHOK0 : sh_ok SEGS vs_Bx3 [] E (mrestrict (w_H (e_W e)) mem')) by (unfold sh_ok; apply Forall_nil).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW (e_W e) mem' a = rdW (e_W e) mem' a) by (intros; reflexivity).
assert (PRS : forall a, apresent (w_H (e_W e)) mem' a -> apresent (w_H (e_W e)) mem' a) by (intros a Ha; exact Ha).
unfold vs_goal, vs_cfg.
(* 0x8a308 .. 0x8a318, to the range test *)
paj_run_tok RUN HS HJ SHOK0 vs_Bspan3.
{ vs_awr_ro. }
vs3_keep (e_W e) mem' KEEP PRS. try (repeat rewrite wvb_collapse in HJ).
(* 0x8a31c `bgeu a0,a1`, a0 = v - 4095, a1 = -4094: taken iff 1 <= v <= 4094 *)
psrr_branch_tok RUN BR HS SHOK0 vs_Bspan3.
- (* in range: on to 0x8a34c *)
  assert (Hv : 1 <= v <= 4094).
  { rewrite branch_geu_U, U_SOff, U_SLit in Hc. rewrite (EV 10%nat 10%bv eq_refl), R10 in Hc. unfold w64 in Hc.
    rewrite unsigned_lit_small in Hc by lia. rewrite (zcanon_small 18446744073709547522) in Hc by lia.
    assert (HM : M64 = 2 ^ 64) by reflexivity. unfold zcanon in Hc. rewrite HM in Hc.
    replace (v + -4095) with (v - 4095) in Hc by lia.
    apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
    pose proof (vs_range_test v Hvb) as T.
    assert (T1 : (2 ^ 64 - 4094 <=? (v - 4095) mod 2 ^ 64) = true) by (apply Z.leb_le; lia).
    rewrite T in T1. apply andb_true_iff in T1 as [T2 T3]. apply Z.leb_le in T2. apply Z.leb_le in T3. lia. }
  rename Hc into Hb1.
  (* 0x8a34c `sub s4,s4,s2`, `addi a1,s4,1`, `li a0,0`, to 0x8a358 *)
  paj_run_tok RUN HS HJ SHOK0 vs_Bspan3.
  { vs_awr_ro. }
  vs3_keep (e_W e) mem' KEEP PRS. try (repeat rewrite wvb_collapse in HJ).
  (* 0x8a358 `bltu s3,a1` -> KR: s3 = 16, a1 = di + 1 <= 15 *)
  psrr_branch_tok RUN BR HS SHOK0 vs_Bspan3.
  + exfalso.
    rewrite branch_ltu_U in Hc.
    rewrite (U_atom E 19 16 ltac:(rewrite (EV 19%nat 19%bv eq_refl); exact G19) ltac:(lia)) in Hc.
    rewrite (vs3_U_plen E (e_seg e) (Z.of_nat di) E18 E20 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    apply Z.ltb_lt in Hc. lia.
  + rename Hc into Hb2.
    (* 0x8a35c `li a2,16`, to 0x8a360 *)
    paj_run_tok RUN HS HJ SHOK0 vs_Bspan3.
    { vs_awr_ro. }
    vs3_keep (e_W e) mem' KEEP PRS. try (repeat rewrite wvb_collapse in HJ).
    (* 0x8a360 `bltu a2,a1` -> KR: a2 = 16, a1 = di + 1 <= 15 *)
    psrr_branch_tok RUN BR HS SHOK0 vs_Bspan3.
    * exfalso.
      rewrite branch_ltu_U, (U_lit E 16 ltac:(lia)) in Hc.
      rewrite (vs3_U_plen E (e_seg e) (Z.of_nat di) E18 E20 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
      apply Z.ltb_lt in Hc. lia.
    * rename Hc into Hb3.
      (* 0x8a364 `mv a0,s2`, 0x8a368 `jal` the strlen wrapper *)
      paj_run_tok RUN HS HJ SHOK0 vs_Bspan3.
      { vs_awr_ro. }
      vs3_keep (e_W e) mem' KEEP PRS. try (repeat rewrite wvb_collapse in HJ).
      (* the registers at the call *)
      assert (CK : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ 22 <= r <= 27 ->
        getr (ms_regs ms) (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
      { intros r Hr.
        assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 22 \/ r = 23 \/
          r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct Hcases as [-> | Hcases]); try subst r;
        lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
          let n := eval compute in (Z.to_nat k) in
          eapply (vs3_reg_call _ _ _ _ n _ _ HS); [apply EV; reflexivity | vm_compute; reflexivity] end. }
      assert (C10 : getr (ms_regs ms) 10 = w64 (e_seg e)).
      { rewrite (vs3_reg_call _ _ _ _ 18%nat 10%bv _ HS (EV 18%nat 18%bv eq_refl) ltac:(vm_compute; reflexivity)).
        exact G18. }
      assert (C21 : getr (ms_regs ms) 21 = w64 v).
      { rewrite (vs3_reg_call _ _ _ _ 10%nat 21%bv _ HS (EV 10%nat 10%bv eq_refl) ltac:(vm_compute; reflexivity)).
        exact R10. }
      assert (C20 : getr (ms_regs ms) 20 = w64 (Z.of_nat di)).
      { pose proof (st_ok_restrict_reg SEGS _ _ _ _ (20%bv : bv 5) HS) as F20.
        lazymatch type of F20 with _ = sv_denot _ (sr_get ?a ?r) =>
          let x := eval vm_compute in (sr_get a r) in change (sr_get a r) with x in F20 end.
        pose proof (vs3_U_dot E (e_seg e) (Z.of_nat di) E18 E20 ltac:(lia) ltac:(lia) ltac:(lia)) as HU.
        unfold U in HU. rewrite F20. unfold w64. rewrite <- HU. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (Cgp : getr (ms_regs ms) 3 = w64 (as_gp B)).
      { change (getr (ms_regs ms) 3) with (getr (ms_regs ms) (Z_to_bv 5 3)). rewrite (CK 3 ltac:(lia)).
        exact (eq_trans G3 Hgp). }
      assert (Ctp : getr (ms_regs ms) 4 = w64 (as_tp B)).
      { change (getr (ms_regs ms) 4) with (getr (ms_regs ms) (Z_to_bv 5 4)). rewrite (CK 4 ltac:(lia)).
        exact (eq_trans G4 Htp). }
      assert (Hsp1 : spZ (ms_regs ms) = spZ (e_regs e) + -64).
      { change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 2))). rewrite (CK 2 ltac:(lia)).
        change (bv_unsigned (getr regs' (Z_to_bv 5 2))) with (spZ regs'). lia. }
      prreg HS (1%bv : bv 5) R1.
      assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
      (* the entry's facts of the segment, at the call's memory: every byte the wrapper reads lies below the
         allocator's ceiling, under the stack window [sp0 - VS_STK, sp0) *)
      assert (KO : kept_out (rdW (e_W e) (e_mem e)) (rdW (e_W e) (ms_mem ms)) (spZ (e_regs e) - VS_STK) (spZ (e_regs e))).
      { intros a Ha Hn. rewrite (KEEP a Ha). exact (HKP a Ha Hn (fun x => x)). }
      assert (Hzl : astr_len (seg_spec.zb (e_s e)) = Z.of_nat (length (e_s e)))
        by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
      assert (RD0 : aread_ok SEGS 0 (e_W e) (e_regs e) (e_mem e) (e_seg e) (Z.of_nat (length (e_s e)) + 1)).
      { unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
        - intros a Ha. split; [|unfold ascratch_stk; lia].
          pose proof (proj1 (proj1 Hstr) (Z.to_nat (a - e_seg e)) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
          rewrite Z2Nat.id in Hb by lia. replace (e_seg e + (a - e_seg e)) with a in Hb by lia. rewrite Hb. discriminate.
        - split; [exact Qam|]. split; [exact Qra | exact Qsh]. }
      pmkst HS.
      eapply SRr_bind.
      { eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False)
          (SIG SS___interceptor_trampoline_strlen) (e_W e) (ms_regs ms) (ms_mem ms) VS_STK (spZ (e_regs e))
          (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [] (e_ly e) (e_S e) _ 0 (-64) (getr (ms_regs ms) 1)
          (fun regs2 mem2 => getr regs2 10 = w64 (astr_len (seg_spec.zb (e_s e))) /\
             (forall a, apresent (w_H (e_W e)) (ms_mem ms) a -> apresent (w_H (e_W e)) mem2 a)) HJ).
        1: exact Hsp1. 1: reflexivity. 1: lia. 1: lia. 1: lia. 1: reflexivity. 1: intros a' [].
        eapply SRr_mono.
        - apply (STRLEN fx (e_ly e) (e_S e) (e_W e) (ms_regs ms) (ms_mem ms) _ (e_seg e) (seg_spec.zb (e_s e))).
          + eapply (ecall_pre_stk_at SEGS B ESTACK VS_STK (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e)
              (e_mem e) (e_md e) [] (e_ly e) (e_S e) (e_W e) (ms_mem ms) _ 0 (ms_regs ms) (-64) HJ);
            [exact Hsp1 | reflexivity | lia | lia | lia | exact Hra1 | exact Cgp | exact Ctp].
          + exact C10.
          + lia.
          + destruct (sa_strz_bytes SEGS (w_H (e_W e)) (e_mem e) (e_seg e) (e_s e) (proj1 Hstr)) as (HBY & HNZ & _).
            split; [|exact HNZ]. intros i Hi.
            assert (Hi' : (i < length (e_s e) + 1)%nat)
              by (unfold seg_spec.zb in Hi; rewrite length_app, length_map in Hi; cbn [length] in Hi; lia).
            rewrite (KO (e_seg e + Z.of_nat i)) by lia. exact (HBY i Hi).
          + rewrite Hzl.
            apply (aread_ok_kept SEGS 0 ESTACK (e_W e) (e_regs e) (ms_regs ms) (e_mem e) (ms_mem ms)
              (spZ (e_regs e) - VS_STK) (spZ (e_regs e)) (e_seg e) (Z.of_nat (length (e_s e)) + 1) KO RD0); lia.
          + rewrite Hzl.
            assert (Htb : e_seg e + Z.of_nat (length (e_s e)) - (e_seg e + Z.of_nat (length (e_s e))) mod 8 + 8
              <= alloc_ceiling) by (apply tail_below; [lia | exact CM]).
            apply (atail_vis_kept SEGS (e_W e) (e_mem e) (ms_mem ms) (spZ (e_regs e) - VS_STK) (spZ (e_regs e))
              (e_seg e + Z.of_nat (length (e_s e))) KO (proj2 Hstr)); lia.
          + intros a Hr Ho He.
            assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hs & _ & Hsr); exists sg; split; [exact Hs | exact Hsr]).
            pose proof (pa_segs_low _ Hi) as R.
            rewrite (KO a) by lia. exact (HROD a (or_introl Hr) Ho He).
        - cbv beta. intros W' c' _ (HW & regs2 & mem2 & md2 & Hc' & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
          split; [exact HW|]. exists regs2, mem2, md2.
          split; [exact Hc'|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
          split; [exact (conj HQ Hpres2)|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hscr]. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQ2 & HPR2) & HFR2).
      rewrite R1.
      (* K4: the state after the wrapper *)
      assert (CR : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ 22 <= r <= 27 ->
        getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
      { intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)). exact (CK r Hr). }
      assert (CTX : vs_ctx0 B e regs2 mem2 md2).
      { unfold vs_ctx0, vs_ctxW, vs_regs, e_sp. split; [exact HJ2|]. split.
        { split; [change (spZ regs2) with (bv_unsigned (getr regs2 (Z_to_bv 5 2))); rewrite (CR 2 ltac:(lia)); exact Hsp|].
          split; [change (getr regs2 3) with (getr regs2 (Z_to_bv 5 3)); rewrite (CR 3 ltac:(lia)); exact G3|].
          split; [change (getr regs2 4) with (getr regs2 (Z_to_bv 5 4)); rewrite (CR 4 ltac:(lia)); exact G4|].
          split; [change (getr regs2 8) with (getr regs2 (Z_to_bv 5 8)); rewrite (CR 8 ltac:(lia)); exact G8|].
          split; [change (getr regs2 9) with (getr regs2 (Z_to_bv 5 9)); rewrite (CR 9 ltac:(lia)); exact G9|].
          split; [change (getr regs2 18) with (getr regs2 (Z_to_bv 5 18)); rewrite (CR 18 ltac:(lia)); exact G18|].
          split; [change (getr regs2 19) with (getr regs2 (Z_to_bv 5 19)); rewrite (CR 19 ltac:(lia)); exact G19|].
          split; [change (getr regs2 22) with (getr regs2 (Z_to_bv 5 22)); rewrite (CR 22 ltac:(lia)); exact G22|].
          intros r Hr. rewrite (CR r ltac:(lia)). exact (G27 r Hr). }
        split.
        { apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a Ha.
          rewrite (HFR2 a ltac:(lia) ltac:(lia) (fun x => x)). exact (KEEP a ltac:(lia)). }
        split.
        { intros a Ha Hw _. rewrite (HFR2 a Ha ltac:(lia) (fun x => x)), (KEEP a Ha). exact (HKP a Ha Hw (fun x => x)). }
        intros a Ha. exact (HPR2 a (PRS a (HPR a Ha))). }
      assert (D10 : getr regs2 10 = w64 (Z.of_nat (length (e_s e)))) by (rewrite HQ2, Hzl; reflexivity).
      assert (D20 : getr regs2 20 = w64 (Z.of_nat di)).
      { change (getr regs2 20) with (getr regs2 (Z_to_bv 5 20)). rewrite (HP2 20 ltac:(unfold acallee_saved; lia)).
        exact C20. }
      assert (D21 : getr regs2 21 = w64 v).
      { change (getr regs2 21) with (getr regs2 (Z_to_bv 5 21)). rewrite (HP2 21 ltac:(unfold acallee_saved; lia)).
        exact C21. }
      exact (HK4 e regs2 mem2 md2 di v HE CTX Hdi Hdi0 Hne Hdig Hveq Hv D10 D20 D21).
- (* out of range: 0x8a320 `li a0,0`, the epilogue; vlan_split = None *)
  assert (Hrng : (v <? 1) || (4094 <? v) = true).
  { rewrite branch_geu_U, U_SOff, U_SLit in Hc. rewrite (EV 10%nat 10%bv eq_refl), R10 in Hc. unfold w64 in Hc.
    rewrite unsigned_lit_small in Hc by lia. rewrite (zcanon_small 18446744073709547522) in Hc by lia.
    assert (HM : M64 = 2 ^ 64) by reflexivity. unfold zcanon in Hc. rewrite HM in Hc.
    replace (v + -4095) with (v - 4095) in Hc by lia.
    apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
    pose proof (vs_range_test v Hvb) as T.
    assert (T1 : (2 ^ 64 - 4094 <=? (v - 4095) mod 2 ^ 64) = false) by (apply Z.leb_gt; lia).
    rewrite T in T1.
    destruct (Z.ltb_spec v 1); [reflexivity|]. destruct (Z.ltb_spec 4094 v); [reflexivity|].
    exfalso. rewrite (proj2 (Z.leb_le 1 v) ltac:(lia)), (proj2 (Z.leb_le v 4094) ltac:(lia)) in T1. cbn in T1.
    discriminate T1. }
  assert (Hvs : SegModel.vlan_split (e_s e) = None).
  { rewrite (vs_code_eq _ Hnul Hlen). rewrite Hveq in Hrng. exact (vs_none_range _ di Hdi Hrng). }
  paj_run_to_tok RUNTO HS HJ SHOK0 vs_Bspan3 VS_KR.
  { vs_awr_ro. }
  vs3_keep (e_W e) mem' KEEP PRS. try (repeat rewrite wvb_collapse in HJ).
  pmkst HS.
  apply (vs_exit_KR B gotw guard HKR e (e_ly e) (e_S e) (e_W e) regs' mem' (ms_regs ms) (ms_mem ms) _ 0 HE HR HSL HJ).
  + intros r Hr.
    assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hcases as [-> | Hcases]); try subst r;
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      let n := eval compute in (Z.to_nat k) in
      eapply (vs_reg_atom _ _ _ _ _ n _ HS); [apply EV; reflexivity | vm_compute; reflexivity] end.
  + intros a Ha. unfold e_sp in Ha. exact (KEEP a ltac:(lia)).
  + pose proof (st_ok_pi_restrict_reg (w_H (e_W e)) _ _ ms 10%bv HS) as F10.
    lazymatch type of F10 with _ = sv_denot _ (sr_get ?a ?r) =>
      let x := eval vm_compute in (sr_get a r) in change (sr_get a r) with x in F10 end.
    rewrite F10. reflexivity.
  + intros regs'' md'' H10''. unfold vs_Q. rewrite Hvs. split; [exact H10''|]. split; [exact I|]. split.
    * apply (vs_kept_step _ _ _ mem');
        [exact (vs_kept_ctxW B e (fun _ => False) _ regs' mem' md' HC (fun a (H : False) => False_ind _ H))|].
      intros a Ha Hw He. exact (KEEP a Ha).
    * split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs (e_S e)). apply vs3_set_fs_id.
Qed.
End e.
End f.
End d.
