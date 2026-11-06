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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 118 of its 158 lines of code are new or changed and 413 lines of the source are left out. *)
(* reac_segconf_parse_file (image B, 0x87e38), segment B10a: the fold's exit EXIT 0x888c0 -> INTENT 0x888e4
   (10 instructions 0x888c0-0x888e0 and the slow arm 0x88fc0-0x88fc8 / error call 0x89284), b10_exit_ok :
   H_INTENT n -> B10_EXIT_stmt n. The B10a segment lane of the image-B G3 walk owner, 2026-10-30; ADAPTED from the image-A G3 walk owner's image-A
   kit lib/A/Prog/pf_a10a_k.v (a10_intent, commit 73bafa8e5cd9) and the image-B trim walk's
   run form (lib/B/Prog/trim_f.v: one written byte, its check decided by a shadow entry).
     T20 0x888c4 `bltu a0,a3` (a0 = slot 0x30 = ~low, a3 = li): the trap is not taken, ~low >= 2 ^ 64 - 1 - 2 ^ 47
       > 63 >= li; the executor decides it from the seed's range facts on atoms 32 and 13 (b10_ss3).
     B#25 0x888cc-0x888dc (store1 at low + li): covered by the shadow entry of low + li (b10_SH3); low's eight
       cells were zeroed by P0 (b10_mid), so the error arm 0x88fc0 / 0x89284 is not reached.
   The run ends at INTENT with low[li] = 0 and s7 = low; b10_intent rebuilds INV_INTENT and H_INTENT finishes. *)
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
  refuse_c reac_segconf_parse_file_c pf_pieces trim_k pf_seg_B10a_k pf_seg_B10a_s.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- helpers the three token runs share ---- *)
(* the kept registers as a list of register names, for regs_kept_of_st_ok_pi *)
Definition B10_KZb : list (bv 5) := map (Z_to_bv 5) B10_KZ.
Lemma b10_kz_of : forall (a b : bvmap 5 word), (forall r : bv 5, In r B10_KZb -> getr a r = getr b r) ->
  forall r, In r B10_KZ -> getr a (Z_to_bv 5 r) = getr b (Z_to_bv 5 r).
Proof. intros a b H r Hr. apply H. unfold B10_KZb. apply in_map. exact Hr. Qed.
Lemma b10_kz_trans : forall (a b c : bvmap 5 word),
  (forall r, In r B10_KZ -> getr a (Z_to_bv 5 r) = getr b (Z_to_bv 5 r)) ->
  (forall r, In r B10_KZ -> getr b (Z_to_bv 5 r) = getr c (Z_to_bv 5 r)) ->
  forall r, In r B10_KZ -> getr a (Z_to_bv 5 r) = getr c (Z_to_bv 5 r).
Proof. intros a b c H1 H2 r Hr. rewrite H1 by exact Hr. exact (H2 r Hr). Qed.
Lemma b10_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma b10_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = v -> ew E n = v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma b10_br_eq_lit : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? z) = b.
Proof.
intros E n v z b H Hv Hz Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.
Lemma b10_reg_atom : forall (regs : bvmap 5 word) (r : bv 5) E n c v,
  getr regs r = sv_denot E (SOff n c) -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> getr regs r = w64 (v + c).
Proof. intros regs r E n c v H Hn Hv. rewrite H. exact (b10_den_off E n v c Hn Hv). Qed.
(* a register of the final state as the executor's term *)
Ltac b10_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* the awr obligation of a run whose regions are read-only, but for one written byte of the class-5 frame at
   atom nn *)
Ltac b10_awr1 nn U HFRM :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (first [ apply awr_ok_nil
                | apply awr_ok_cons_ro; [cbn; lia|]
                | eapply awr_ok_cons_gen with (n := nn); [reflexivity | exact U | apply HFRM |] ]).

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

(* a byte of the class-5 frame is one the segment may write (its own frame, awr_byte's in_frames) *)
Lemma b10_awr_frame : forall v pos lyc STK sp0 FP bl0 blc fr0 a,
  pf_F v pos = frame_addr lyc 5 pos -> pf_F v pos <= a < pf_F v pos + 2048 ->
  awr_byte SEGS B STK sp0 FP bl0 blc fr0 lyc [(5, pos)] a.
Proof.
intros v pos lyc STK sp0 FP bl0 blc fr0 a HF Ha. right; right; right; left.
exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite <- HF.
change (fs_frame_bytes 5) with 2048. lia.
Qed.

Lemma b10_exit_ok : forall n, H_INTENT B n -> B10_EXIT_stmt B n.
Proof.
intros n HINT. unfold B10_EXIT_stmt, b10_at.
intros v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc HM H13.
pose proof (b10_mid_facts B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc _ HM)
  as (R9 & R20 & R26 & Hs1 & Hs1e & W70 & W30 & WA0 & NZ & VB & VR & Hb1 & Hb2 & F4096 & F47 & Fc & Fapp &
      RAV & RAL & Fp & HFA & Hin & NSB).
pose proof HM as (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK).
pose proof HKV as (_ & _ & _ & (Hsplit & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (k := length (r_low val 0 64)) in *.
set (low := pf_F v pos + PF_O_LOW) in *.
assert (Hlow : 4096 <= low /\ low + 64 <= alloc_ceiling) by (unfold low, PF_O_LOW; lia).
pose proof (b10_entry3 Wc regs1 memc (pf_s1 v) (Z.of_nat k) low R9 R20 H13 ltac:(lia) ltac:(lia) ltac:(lia)
  W30 WA0 (Fp (low + Z.of_nat k) ltac:(unfold low, PF_O_LOW; lia)) ltac:(lia) ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (b10_E3 regs1 low (Z.of_nat k))) by (unfold b10_E3; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 [w64 (pf_nt low); w64 low; w64 (low + Z.of_nat k)]) (b10_E3 regs1 low (Z.of_nat k)))
  by (split; [intros n0 Hn0; unfold b10_E3; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E20 : ew (b10_E3 regs1 low (Z.of_nat k)) 20 = Z_to_bv 64 SB)
  by (unfold b10_E3; rewrite (ew_Eimg_Ereg_nat regs1 _ 20 (Z_to_bv 5 20) eq_refl); exact R20).
assert (E33 : ew (b10_E3 regs1 low (Z.of_nat k)) 33 = Z_to_bv 64 low)
  by (unfold b10_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew (b10_E3 regs1 low (Z.of_nat k)) 34 = Z_to_bv 64 (low + Z.of_nat k))
  by (unfold b10_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
revert HS HEI HA0 E20 E33 E34. generalize (b10_E3 regs1 low (Z.of_nat k)) as E0. intros E0 HS HEI HA0 E20 E33 E34.
assert (U34 : bv_unsigned (ew E0 34) = low + Z.of_nat k) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UB : U E0 b10_Bx = SHADOW_OFF) by (unfold b10_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS b10_Bx b10_SH3 E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b10_SH3. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b10_Bx 34%nat low 64 (low + Z.of_nat k) 0 1 RAL UB
    ltac:(apply U_atom; [exact E34 | lia])); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  apply NSB. unfold low, PF_O_LOW in *. lia. }
assert (HFRM : forall a, low + Z.of_nat k + 0 <= a < low + Z.of_nat k + 1 ->
  awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (ablocks B (p_ly v) (p_S v))
    (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a).
{ intros a Ha. apply (b10_awr_frame v pos lyc _ _ _ _ _ _ a HFA). unfold low, PF_O_LOW in *. lia. }
(* 0x888c0 .. 0x888e0: T20 (decided), s7 = low, B#25 (covered), low[li] = 0; up to INTENT *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_INTENT.
{ b10_awr1 34%nat U34 HFRM. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
lazymatch goal with HS' : st_ok_pi _ _ ?En _ (restrict _ ?msn) |- _ =>
  assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0));
  rename msn into ms1 end.
(* the bytes the run kept: all but low + li *)
assert (KS : forall a, 0 <= a < 2 ^ 64 -> a <> low + Z.of_nat k -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hne. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms1) (fun a' => a' = low + Z.of_nat k) HFr);
    [|exact Ha | exact Hne].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr; [lia | rewrite U34 in Hrr; lia]. }
(* the NUL it wrote *)
assert (HW0 : rdW Wc (ms_mem ms1) (low + Z.of_nat k) = Some 0).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
    pose proof (b10_rbyte Ex ssx ms1 (w_H Wc) 34%nat 1%nat 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 (SLit 0) (low + Z.of_nat k) HS
      ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as V end.
  rewrite Z.add_0_r in V. rewrite V; [reflexivity|].
  rewrite (b10_ag_ew E0 _ 40 34 _ HAE ltac:(lia) E34). apply unsigned_lit_small. lia. }
(* the registers *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B10_KZb HS (b10_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
  ltac:(vm_compute; reflexivity)) as HKb.
cbn [ms_regs restrict] in HKb.
b10_reg HS (Z_to_bv 5 23) N23.
pose proof (b10_reg_atom _ _ _ 33 0 low N23 (b10_ag_ew E0 _ 40 33 _ HAE ltac:(lia) E33) ltac:(lia)) as R23.
rewrite Z.add_0_r in R23.
pmkst HS.
(* INTENT *)
unfold b10_post. rewrite (b10_r_key_role cf gi nm (ln + 1) (pf_tline (p_s v) o) key val Hsplit Hrole).
apply (HINT v pos lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv cf nm o ln d gi vp val).
apply (b10_intent B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val (ms_regs ms1) (ms_mem ms1) mdv).
- apply (b10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
    (ms_regs ms1) (ms_mem ms1) mdv k HM HJ KS (or_introl eq_refl) Hkl Hk63 (b10_kz_of _ _ HKb)).
- exact HW0.
- exact R23.
Qed.
End e.
End f.
End d.
