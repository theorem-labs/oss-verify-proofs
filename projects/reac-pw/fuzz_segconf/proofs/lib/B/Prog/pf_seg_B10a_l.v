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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 225 of its 265 lines of code are new or changed and 413 lines of the source are left out. *)
(* reac_segconf_parse_file (image B, 0x87e38), segment B10a: the role fold's loop LOOP 0x88674 (0x88674-0x886c4,
   the slow arm 0x886c8-0x886d0 and the error call 0x8923c-0x89240), b10_loop_ok : B10_EXIT_stmt n -> forall k,
   B10_LOOP_k n k, by strong induction on 63 - k. The B10a segment lane of the image-B G3 walk owner, 2026-10-30; ADAPTED from
   the image-A G3 walk owner's image-A kit lib/A/Prog/pf_a10a_k.v (a10_mid_step, commit 73bafa8e5cd9),
   the unit owner's UBSan walk of the same fold lib/U/Prog/pf_p6.v (commit afa0b72ba4ad: the
   q++ no-wrap discharge) and the loop form of the image-B trim walk (lib/B/Prog/trim_l.v: re-seeded at each
   iteration). One iteration with li = k (val[k] <> 0):
     0x88674 `li a3,63; beq a6,a3`: k = 63 leaves to EXIT with a3 = 63 (then |r_low val 0 64| = 63);
     0x8867c-0x88698 low[k] = fold(val[k]) (the store to low + k, written region atom 34);
     0x8869c T17 `beq a3,s10` (a3 = val + k, s10 = -1): not taken, val + k <= buf + 512 <= 0x7fffff800000 (the
       seed's range fact on atom 32), decided by the executor;
     0x886a0-0x886b0 check B#17 (load1 at val + k + 1): covered by the shadow entry of val + k + 1 (k + 1 <=
       |val|, inside buf, whose 64 cells are 0), so the slow arm's error call 0x89240 is not reached;
     0x886b4 `lbu a2,1(a3)`, li++, `mv a3,a6`; `beqz a2`: val[k + 1] = 0 leaves to EXIT with a3 = k + 1 (then
       |val| = k + 1 = |r_low val 0 64|), else `j` LOOP with k + 1. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegInstB
  refuse_c reac_segconf_parse_file_c pf_pieces trim_k pf_seg_B10a_k pf_seg_B10a_s pf_seg_B10a_x.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the kept registers the loop's seed leaves as their own atoms (s10 is pinned to -1) *)
Definition B10_KZ2b : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 25].
Lemma b10_kz_of2 : forall (a b : bvmap 5 word), (forall r : bv 5, In r B10_KZ2b -> getr a r = getr b r) ->
  getr a (Z_to_bv 5 26) = getr b (Z_to_bv 5 26) ->
  forall r, In r B10_KZ -> getr a (Z_to_bv 5 r) = getr b (Z_to_bv 5 r).
Proof.
intros a b H H26 r Hr. unfold B10_KZ in Hr. cbn [In] in Hr.
destruct (Z.eq_dec r 26) as [->|Hne]; [exact H26|].
apply H. unfold B10_KZ2b. apply in_map. cbn [In]. lia.
Qed.
(* val's bytes: a NUL-free list has no 0 before its end, and 0 at it *)
Lemma b10_nth_nz : forall (l : list Z) i, ~ In 0 l -> (i < length l)%nat -> nth i l 0 <> 0.
Proof. intros l i H Hi E. apply H. rewrite <- E. apply nth_In. exact Hi. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Definition B10_LOOP_m (n m : nat) : Prop := forall k, (63 - k = m)%nat -> B10_LOOP_k B n k.

(* after a run whose one written window is low + k: name the new state ms', chain the kept bytes to memc *)
Ltac b10_after E0 memc low k E34 KSp msname KSname :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let Uo := fresh "Uo" in
    assert (Uo : bv_unsigned (ew Eo 34) = low + Z.of_nat k)
      by (rewrite (b10_ag_ew E0 Eo 40 34 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E34);
          apply unsigned_lit_small; lia);
    assert (KSname : forall a, 0 <= a < 2 ^ 64 -> a <> low + Z.of_nat k -> aview SEGS Hh (ms_mem msn) a = aview SEGS Hh memc a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in intros a Ha Hne;
          rewrite (kept_of_frame (segs := SEGS) Eo rs Hh m0 (ms_mem msn) (fun a' => a' = low + Z.of_nat k) HFr);
          [ exact (KSp a Ha Hne)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in
                    destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; first [lia | rewrite Uo in Hrr; lia] |]);
            destruct Hin
          | exact Ha | exact Hne ]);
    clear Uo KSp;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
    rename msn into msname
  end.

Lemma b10_loop_step : forall n, B10_EXIT_stmt B n ->
  forall m, (forall m', (m' < m)%nat -> B10_LOOP_m n m') -> B10_LOOP_m n m.
Proof.
intros n HEXIT m IH k Hm. unfold B10_LOOP_k, b10_at.
intros v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc HM Hkv H10 H11 H12 H16.
pose proof (b10_mid_facts B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc _ HM)
  as (R9 & R20 & R26 & Hs1 & Hs1e & W70 & W30 & WA0 & NZ & VB & VR & Hb1 & Hb2 & F4096 & F47 & Fc & Fapp &
      RAV & RAL & Fp & HFA & Hin & NSB).
pose proof HM as (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (b10_r_low64_len val NZ) as RLL.
unfold PF_O_BUF in Hb1, Hb2.
set (low := pf_F v pos + PF_O_LOW) in *.
assert (Hlow : 4096 <= low /\ low + 64 <= alloc_ceiling /\ pf_F v pos + 576 < low) by (unfold low, PF_O_LOW; lia).
set (c := nth k val 0) in *.
set (c1 := nth (S k) val 0) in *.
assert (Hc : 0 < c < 256) by (unfold c; pose proof (VR k Hkv); pose proof (b10_nth_nz val k NZ Hkv); lia).
assert (Hc1 : 0 <= c1 < 256).
{ destruct (Nat.lt_ge_cases (S k) (length val)) as [Hl|Hl]; [exact (VR _ Hl)|].
  unfold c1. rewrite nth_overflow by exact Hl. lia. }
assert (V1 : rdW Wc memc (vp + Z.of_nat k + 1) = Some c1).
{ replace (vp + Z.of_nat k + 1) with (vp + Z.of_nat (S k)) by lia. exact (VB (S k) ltac:(lia)). }
pose proof (b10_entry2 Wc regs1 memc (pf_s1 v) vp (Z.of_nat k) low c1 R9 R20 R26 H10 H11 H16 ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WA0 V1 Hc1 (Fp (low + Z.of_nat k) ltac:(unfold low, PF_O_LOW; lia))
  ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (b10_E2 regs1 vp (Z.of_nat k) low c1)) by (unfold b10_E2; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 [w64 (vp + Z.of_nat k); w64 low; w64 (low + Z.of_nat k); Z_to_bv 64 c1])
  (b10_E2 regs1 vp (Z.of_nat k) low c1))
  by (split; [intros n0 Hn0; unfold b10_E2; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew (b10_E2 regs1 vp (Z.of_nat k) low c1) nn = getr regs1 r)
  by (intros nn r Hn; unfold b10_E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 10 = Z_to_bv 64 vp)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 11 = Z_to_bv 64 (vp + 1))
  by (rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 12 = Z_to_bv 64 c)
  by (rewrite (EE 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E16 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 16 = Z_to_bv 64 (Z.of_nat k))
  by (rewrite (EE 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E20 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 20 = Z_to_bv 64 SB)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 32 = Z_to_bv 64 (vp + Z.of_nat k))
  by (unfold b10_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E34 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 34 = Z_to_bv 64 (low + Z.of_nat k))
  by (unfold b10_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew (b10_E2 regs1 vp (Z.of_nat k) low c1) 35 = Z_to_bv 64 c1)
  by (unfold b10_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
clear EE.
revert HS HEI HA0 E10 E11 E12 E16 E20 E32 E34 E35. generalize (b10_E2 regs1 vp (Z.of_nat k) low c1) as E0.
intros E0 HS HEI HA0 E10 E11 E12 E16 E20 E32 E34 E35.
assert (U34 : bv_unsigned (ew E0 34) = low + Z.of_nat k) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UB : U E0 b10_Bx = SHADOW_OFF) by (unfold b10_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS b10_Bx b10_SH2 E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b10_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b10_Bx 32%nat vp (Z.of_nat (length val) + 1) (vp + Z.of_nat k) 1 2 RAV UB
      ltac:(apply U_atom; [exact E32 | lia])); [lia | lia |].
    intros x Hx. change (Z.min 1 2) with 1 in Hx. change (Z.max 1 2) with 2 in Hx. apply NSB. lia.
  - eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b10_Bx 34%nat low 64 (low + Z.of_nat k) 0 1 RAL UB
      ltac:(apply U_atom; [exact E34 | lia])); [lia | lia |].
    intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx. apply NSB. unfold low, PF_O_LOW in *. lia. }
assert (HFRM : forall a, low + Z.of_nat k + 0 <= a < low + Z.of_nat k + 1 ->
  awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (ablocks B (p_ly v) (p_S v))
    (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a).
{ intros a Ha. apply (b10_awr_frame B v pos lyc _ _ _ _ _ _ a HFA). unfold low, PF_O_LOW in *. lia. }
assert (KS0 : forall a, 0 <= a < 2 ^ 64 -> a <> low + Z.of_nat k -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
(* 0x88674 .. 0x88678: `li a3,63; beq a6,a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b10_awr1 34%nat U34 HFRM. }
b10_after E0 memc low k E34 KS0 ms1 KS1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* k = 63: EXIT with a3 = 63 *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b10_br_eq_lit En 16 (Z.of_nat k) 63 true (b10_ag_ew E0 En 40 16 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E16)
      ltac:(lia) ltac:(lia) Hc0) as Hk63' end.
  apply Z.eqb_eq in Hk63'. assert (Hk : k = 63%nat) by lia. clear Hc0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B10_EXIT.
  { b10_awr1 34%nat U34 HFRM. }
  b10_after E0 memc low k E34 KS1 ms2 KS2.
  lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B10_KZ2b HS (b10_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HKb.
  cbn [ms_regs restrict] in HKb.
  b10_reg HS (Z_to_bv 5 26) N26. b10_reg HS (Z_to_bv 5 13) N13.
  pmkst HS.
  assert (RL : length (r_low val 0 64) = k) by (rewrite RLL; lia).
  apply (HEXIT v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val (ms_regs ms2) (ms_mem ms2) _).
  + rewrite RL.
    apply (b10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
      (ms_regs ms2) (ms_mem ms2) _ k HM HJ KS2 (or_introl eq_refl) Hkl Hk63).
    apply (b10_kz_of2 _ _ HKb). rewrite N26, R26. cbn [sv_denot]. unfold w64. apply w64_mod. reflexivity.
  + rewrite RL, N13. cbn [sv_denot]. rewrite Hk. reflexivity.
- (* k < 63: the fold step, T17 (decided), B#17 (covered), the byte val[k + 1] *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b10_br_eq_lit En 16 (Z.of_nat k) 63 false (b10_ag_ew E0 En 40 16 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E16)
      ltac:(lia) ltac:(lia) Hc0) as Hk63' end.
  apply Z.eqb_neq in Hk63'. assert (Hk : (k < 63)%nat) by lia. clear Hc0.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { b10_awr1 34%nat U34 HFRM. }
  b10_after E0 memc low k E34 KS1 ms2 KS2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* val[k + 1] = 0: EXIT with a3 = k + 1 *)
    lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
      pose proof (b10_br_eq_lit En 35 c1 0 true (b10_ag_ew E0 En 40 35 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E35)
        ltac:(lia) ltac:(lia) Hc0) as Hz end.
    apply Z.eqb_eq in Hz. clear Hc0.
    assert (HL : length val = S k).
    { destruct (Nat.lt_ge_cases (S k) (length val)) as [Hl|Hl]; [|lia].
      exfalso. exact (b10_nth_nz val (S k) NZ Hl Hz). }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B10_EXIT.
    { b10_awr1 34%nat U34 HFRM. }
    b10_after E0 memc low k E34 KS2 ms3 KS3.
    lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
      assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
    (* the folded byte at low + k *)
    assert (HWB : rdW Wc (ms_mem ms3) (low + Z.of_nat k) = Some (lower c)).
    { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
        pose proof (b10_rbyte Ex ssx ms3 (w_H Wc) 34%nat 2%nat 0 1 0 1 [YP09.mkChunk 0 (CVal 1 b10_fold_sv)] 0 b10_fold_sv
          (low + Z.of_nat k) HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as V;
        rewrite Z.add_0_r in V; rewrite V;
        [ rewrite (b10_fold_U Ex c (b10_ag_ew E0 Ex 40 12 _ HAE ltac:(lia) E12) ltac:(lia)); reflexivity
        | rewrite (b10_ag_ew E0 Ex 40 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia ] end. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B10_KZ2b HS (b10_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HKb.
    cbn [ms_regs restrict] in HKb.
    b10_reg HS (Z_to_bv 5 26) N26. b10_reg HS (Z_to_bv 5 13) N13.
    pmkst HS.
    assert (RL : length (r_low val 0 64) = S k) by (rewrite RLL; lia).
    apply (HEXIT v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val (ms_regs ms3) (ms_mem ms3) _).
    * rewrite RL.
      apply (b10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
        (ms_regs ms3) (ms_mem ms3) _ (S k) HM HJ KS3 (or_intror (conj eq_refl HWB)) ltac:(lia) ltac:(lia)).
      apply (b10_kz_of2 _ _ HKb). rewrite N26, R26. cbn [sv_denot]. unfold w64. apply w64_mod. reflexivity.
    * rewrite RL. rewrite (b10_reg_atom _ _ _ 16 1 (Z.of_nat k) N13 (b10_ag_ew E0 _ 40 16 _ HAE ltac:(lia) E16) ltac:(lia)).
      f_equal. lia.
  + (* val[k + 1] <> 0: LOOP with k + 1 *)
    lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
      pose proof (b10_br_eq_lit En 35 c1 0 false (b10_ag_ew E0 En 40 35 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E35)
        ltac:(lia) ltac:(lia) Hc0) as Hz end.
    apply Z.eqb_neq in Hz. clear Hc0.
    assert (HL : (S k < length val)%nat).
    { destruct (Nat.lt_ge_cases (S k) (length val)) as [Hl|Hl]; [exact Hl|].
      exfalso. apply Hz. unfold c1. apply nth_overflow. exact Hl. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B10_LOOP.
    { b10_awr1 34%nat U34 HFRM. }
    b10_after E0 memc low k E34 KS2 ms3 KS3.
    lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
      assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
    assert (HWB : rdW Wc (ms_mem ms3) (low + Z.of_nat k) = Some (lower c)).
    { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
        pose proof (b10_rbyte Ex ssx ms3 (w_H Wc) 34%nat 2%nat 0 1 0 1 [YP09.mkChunk 0 (CVal 1 b10_fold_sv)] 0 b10_fold_sv
          (low + Z.of_nat k) HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as V;
        rewrite Z.add_0_r in V; rewrite V;
        [ rewrite (b10_fold_U Ex c (b10_ag_ew E0 Ex 40 12 _ HAE ltac:(lia) E12) ltac:(lia)); reflexivity
        | rewrite (b10_ag_ew E0 Ex 40 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia ] end. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B10_KZ2b HS (b10_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HKb.
    cbn [ms_regs restrict] in HKb.
    b10_reg HS (Z_to_bv 5 26) N26. b10_reg HS (Z_to_bv 5 10) N10. b10_reg HS (Z_to_bv 5 11) N11.
    b10_reg HS (Z_to_bv 5 12) N12. b10_reg HS (Z_to_bv 5 16) N16.
    pmkst HS.
    apply (IH (63 - S k)%nat ltac:(lia) (S k) eq_refl v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
      (ms_regs ms3) (ms_mem ms3) _).
    * apply (b10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
        (ms_regs ms3) (ms_mem ms3) _ (S k) HM HJ KS3 (or_intror (conj eq_refl HWB)) ltac:(lia) ltac:(lia)).
      apply (b10_kz_of2 _ _ HKb). rewrite N26, R26. cbn [sv_denot]. unfold w64. apply w64_mod. reflexivity.
    * exact HL.
    * rewrite (b10_reg_atom _ _ _ 10 0 vp N10 (b10_ag_ew E0 _ 40 10 _ HAE ltac:(lia) E10) ltac:(lia)).
      f_equal. lia.
    * rewrite (b10_reg_atom _ _ _ 11 0 (vp + 1) N11 (b10_ag_ew E0 _ 40 11 _ HAE ltac:(lia) E11) ltac:(lia)).
      f_equal. lia.
    * rewrite (b10_reg_atom _ _ _ 35 0 c1 N12 (b10_ag_ew E0 _ 40 35 _ HAE ltac:(lia) E35) ltac:(lia)).
      f_equal. unfold c1. lia.
    * rewrite (b10_reg_atom _ _ _ 16 1 (Z.of_nat k) N16 (b10_ag_ew E0 _ 40 16 _ HAE ltac:(lia) E16) ltac:(lia)).
      f_equal. lia.
Qed.

Lemma b10_loop_ok : forall n, B10_EXIT_stmt B n -> forall k, B10_LOOP_k B n k.
Proof.
intros n HEXIT.
assert (ALL : forall j m, (m <= j)%nat -> B10_LOOP_m n m).
{ induction j as [|j IHj]; intros m Hm.
  - apply (b10_loop_step n HEXIT m). intros m' Hm'. lia.
  - apply (b10_loop_step n HEXIT m). intros m' Hm'. apply (IHj m'). lia. }
intros k. exact (ALL _ _ (le_n _) k eq_refl).
Qed.
End e.
End f.
End d.
