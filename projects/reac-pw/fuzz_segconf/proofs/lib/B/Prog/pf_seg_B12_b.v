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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 147 of its 186 lines of code are new or changed and 414 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B12 of reac_segconf_parse_file's
   walk, the exit piece BAD -> KREF, b12_bad_ok : B12_BAD_stmt B (lib/B/Prog/pf_seg_B12_k.v). A B12 sub-lane of
   the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma of reac_segconf_parse_file's walk, piece BAD of
   segment B12). ADAPTED from a working branch (the bad-ignore refusal of segment A12) + the unit owner's
   UBSan piece walk lib/U/Prog/pf_p8.v, re-derived on image B's code; the run form is the B5 segment lane's
   pf_seg_B5_r2.v (commit 2305ce2c2c85: a plain run to the next cut, kept_of_frame, registers read
   back), the cut rebuild the B10b segment lane's pf_seg_B10b_j.v (the keep family is pf_seg_B12_x.v).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 6 instructions, no inline check, no UBSan
   trap, no call, no write:
     0x888a4 auipc a0           (listing PHi 77)
     0x888a8 addi a2,a0,92      a2 = .str.22 = F_badignore (listing object 54, 0x21900)
     0x888ac ld a0,200(s1)      a0 = c (slot 0xc8)
     0x888b0 mv a1,s6           a1 = lineno = ln + 1 (PF_RM)
     0x888b4 ld a3,64(s1)       a3 = cur_name = F + 0x20 (slot 0x40)
     0x888b8 j 0x889a0          KREF (PF_KREF); a4 = val is the cut's (premise getr regs1 14 = w64 vp)
   The seed: every register its own atom, one read-only region on s1's atom 9 holding the two slots as the extra
   atoms 32 (cur_name) and 33 (c). One plain run to KREF, the registers read back, INV_KREF rebuilt with
   cur = Some gi, f = F_badignore, args = [AS nm; AS val], xp = vp, and HA_KREF at the ambient FP state; the post
   is b12_post by b12_spine with parse_bool val = None.
   SECTION HYPOTHESIS: OBJ (lib/B/Prog/SegObj.v seg_val_objs: the listing object 54's value, as
   lib/B/Prog/reac_segconf_parse.v takes it). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B12_k pf_seg_B12_x.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register of the state after a run, as the executor wrote it (pf_seg_B5_r2.v b5r2_rreg) *)
Ltac b12b_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b12b_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma b12b_den0 : forall E n x, ew E n = Z_to_bv 64 x -> sv_denot E (SOff n 0) = Z_to_bv 64 x.
Proof. intros E n x H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the seed at BAD 0x888a4: every register its own atom; s1's slots 0x40 (cur_name, atom 32) and 0xc8 (c, atom 33)
   as one read-only region on s1 (atom 9) *)
Definition b12b_ss : sstate :=
  mkSS B12_BAD sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x40 0xd0 0 0
       [YP09.mkChunk 0x40 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 33 0))]] None
    (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition b12b_E (regs1 : bvmap 5 word) (cn c : Z) : env := Eimg (Ereg regs1 [w64 cn; w64 c]).

Lemma b12b_seed : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 cn c,
  getr regs1 (Z_to_bv 5 9) = w64 s1 -> 0 <= cn < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  rdword (rdW W memc) (s1 + 0x40) = Some cn -> rdword (rdW W memc) (s1 + 0xc8) = Some c ->
  0 <= s1 -> s1 + 0xd0 <= 2 ^ 64 ->
  st_ok_pi SEGS VAL (b12b_E regs1 cn c) b12b_ss
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + B12_BAD)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 cn c H9 Hcn Hc Hw40 Hwc8 Hs1 Hs2.
set (E := b12b_E regs1 cn c).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j [w64 cn; w64 c] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold b12b_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth] in E32, E33. clear EX.
assert (E9 : ew E 9 = w64 s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
rewrite restrict_mkst_fx. unfold b12b_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val SEGS E _ s1 0x40 8 (SOff 32 0) cn);
      [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
    exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw40).
  + apply (chunk_ok_val SEGS E _ s1 0xc8 8 (SOff 33 0) c);
      [cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
    exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hwc8).
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Section e.
Variable B : asyms.
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

(* listing object 54 is .str.22 = F_badignore (0x21900) *)
Lemma b12b_lit_atom : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 54) = Z_to_bv 64 (seg_litA_rc F_badignore).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 54) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 54%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
pose proof b12_lits as (_ & _ & _ & _ & L54 & _ & _ & _ & _ & _ & N54 & _). rewrite N54, L54. reflexivity.
Qed.

Lemma b12_bad_ok : B12_BAD_stmt B.
Proof.
unfold B12_BAD_stmt, b12_at.
intros e regs1 memc1 mdc1 HE HM Hpb R14.
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & Hc1 & Hc2 & Hc16 & Hheap & Hgi32 & Hgi & Hs1a & Hs1b
  & Hsp47 & Hs1m & Hsp16 & Hv1 & Hv2 & HAR & Hs1c).
destruct (b12_slots B e regs1 memc1 mdc1 HE HM) as (S40 & S48 & S70 & SC0 & SC8). cbv zeta in S40, SC8.
pose proof HE as (HI & _ & _ & _ & HKREF & _).
pose proof HM as (HJ & HKO & HKR).
pose proof asan_consts as (C1 & _). assert (ES : ESTACK = 4096) by reflexivity.
assert (R9 : getr regs1 (Z_to_bv 5 9) = w64 (pf_s1 (e_v e)))
  by (apply (b12_kreg B e regs1 memc1 mdc1 9 _ HE HM); unfold B12_KEPT; cbn [In app PF_RL PF_RM]; tauto).
assert (R22 : getr regs1 (Z_to_bv 5 22) = w64 (e_ln e + 1))
  by (apply (b12_kreg B e regs1 memc1 mdc1 22 _ HE HM); unfold B12_KEPT; cbn [In app PF_RL PF_RM]; tauto).
(* the seed *)
assert (Hcn : 0 <= pf_F (e_v e) (e_pos e) + PF_O_CN < 2 ^ 64) by (unfold PF_O_CN; lia).
assert (Hc64 : 0 <= p_c (e_v e) < 2 ^ 64) by (unfold seg_spec.SEG_C_SIZE in Hc2; lia).
assert (Hs10 : 0 <= pf_s1 (e_v e)) by lia.
assert (Hs1d : pf_s1 (e_v e) + 0xd0 <= 2 ^ 64) by lia.
pose proof (b12b_seed (e_W e) regs1 memc1 (pf_s1 (e_v e)) (pf_F (e_v e) (e_pos e) + PF_O_CN) (p_c (e_v e)) R9 Hcn Hc64 S40 SC8 Hs10 Hs1d) as HS.
set (E := b12b_E regs1 (pf_F (e_v e) (e_pos e) + PF_O_CN) (p_c (e_v e))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold b12b_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 [w64 (pf_F (e_v e) (e_pos e) + PF_O_CN); w64 (p_c (e_v e))]) E)
  by (split; [intros n0 Hn0; subst E; unfold b12b_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs1 r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (pf_F (e_v e) (e_pos e) + PF_O_CN))
  by (subst E; unfold b12b_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_c (e_v e)))
  by (subst E; unfold b12b_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 (e_ln e + 1)) by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); exact R22).
assert (E14 : ew E 14 = Z_to_bv 64 (e_vp e)) by (rewrite (EE 14%nat (Z_to_bv 5 14) eq_refl); exact R14).
assert (E54 : ew E (A_OBJ 54) = Z_to_bv 64 (seg_litA_rc F_badignore)) by exact (b12b_lit_atom E HEI).
(* 0x888a4 .. 0x888b8: the four arguments, the jump to KREF *)
paj_run_to_sh RUNTO HS HJ PF_KREF.
{ intros a (r & Hr & Ha). unfold b12b_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b12b_clear_md.
(* the run wrote nothing *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW (e_W e) (ms_mem ms) a = rdW (e_W e) memc1 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem b12b_ss) (w_H (e_W e)) memc1 (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
clear HFr HG HF.
assert (KP : b12x_kept (e_v e) (pf_s1 (e_v e) - 8) (rdW (e_W e) (e_mem e)) (rdW (e_W e) (ms_mem ms)))
  by (apply (b12x_kept_step (e_v e) (pf_s1 (e_v e) - 8) _ (rdW (e_W e) memc1)); [exact (b12x_kept_mid B e regs1 memc1 mdc1 HM)
      | intros a Ha _; exact (K1 a Ha)]).
(* the registers at KREF: B12_KEPT the cut's, a0 .. a4 the refusal's arguments *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (map (Z_to_bv 5) B12_KEPT) HS HA0 ltac:(vm_compute; reflexivity))
  as HKb.
cbn [ms_regs restrict] in HKb.
assert (HRK : forall r, In r B12_KEPT -> getr (ms_regs ms) (Z_to_bv 5 r) = getr (e_rX e) (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HKb (Z_to_bv 5 r) (in_map _ _ _ Hr)). exact (HKR r Hr). }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (p_c (e_v e))) by (b12b_rreg HS; exact (b12b_den0 E 33 _ E33)).
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (e_ln e + 1)) by (b12b_rreg HS; exact (b12b_den0 E 22 _ E22)).
assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_badignore))
  by (b12b_rreg HS; exact (b12b_den0 E (A_OBJ 54) _ E54)).
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (pf_F (e_v e) (e_pos e) + PF_O_CN)) by (b12b_rreg HS; exact (b12b_den0 E 32 _ E32)).
assert (Q14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 (e_vp e)) by (b12b_rreg HS; exact (b12b_den0 E 14 _ E14)).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_KREF) rg mm mdx) end.
(* the post: r_key's ignore branch with parse_bool val = None is the bad-ignore refusal *)
unfold b12_post. rewrite (b12_spine B e HE), Hpb.
apply (HKREF fx (e_v e) (e_pos e) (e_ly e) (e_S e) (e_W e) (ms_regs ms) (ms_mem ms) mdv (e_cf e) (Some (e_gi e)) (e_nm e)
  (e_o e) (e_ln e) (e_d e) F_badignore (seg_litA_rc F_badignore) [AS (e_nm e); AS (e_val e)] (e_vp e)).
pose proof HI as (_ & HMID & HST & _).
assert (Hwc : pf_s1 (e_v e) - 8 + 8 <= p_c (e_v e) \/ p_c (e_v e) + seg_spec.SEG_C_SIZE <= pf_s1 (e_v e) - 8) by (right; lia).
pose proof (b12x_geo B e regs1 memc1 mdc1 (pf_s1 (e_v e) - 8) HE HM (b12x_wok_win (e_v e))) as GX.
destruct (b12x_val B e regs1 memc1 mdc1 (pf_s1 (e_v e) - 8) (ms_mem ms) HE HM (b12x_wok_win (e_v e)) KP) as (HVS & HVB).
destruct (b12x_regs B e (ms_regs ms) HE HRK) as (_ & HRLRM).
split; [exact (b12x_base B e regs1 memc1 mdc1 (pf_s1 (e_v e) - 8) (ms_regs ms) (ms_mem ms) mdv HE HM (b12x_wok_win (e_v e)) HJ KP HRK)|].
split; [exact HMID|].
split; [exact (b12x_st (e_v e) (e_pos e) (pf_s1 (e_v e) - 8) _ _ GX KP Hwc _ _ _ _ HST)|].
split.
- split; [right; right; reflexivity|]. split; [reflexivity|].
  exists (e_val e). split; [reflexivity|]. split; [exact HVS | exact HVB].
- unfold pf_rg in *. rewrite app_assoc, Forall_app. split; [exact HRLRM|].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption.
Qed.
End e.
End f.
End d.

(* the piece, for the segment's assembly: at every FP state, with OBJ *)
Theorem pb12_bad_ok : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing} (B : asyms),
  seg_val_objs (PI := PI) -> forall f0 : YK11.FPState, B12_BAD_stmt (fx := f0) B.
Proof. intros rc SK PI B OBJ f0. exact (b12_bad_ok (fx := f0) B OBJ). Qed.
