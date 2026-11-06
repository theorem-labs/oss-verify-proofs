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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 146 of its 187 lines of code are new or changed and 412 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the seed of piece KWOK of segment A7 at the two places it
   reads a byte of buf (segment A7's proof, 2026-10-30):
     0x88304  lbu a1, 0(a0)   a0 = s3 + 7, body[7]     (seeded at KWOK 0x882f0: s3 = body, atom 19, offset 7)
     0x88328  lbu a0, 0(s9)   s9 = a0 = the name, name[0] (seeded at 0x88314, trim's return: a0, atom 10, offset 0)
   The symbolic executor finds a load's region by the address's base atom and offset (YP09.sload), so the byte is a
   region of its own on the pointer register's atom, [d, d + 1), read-only, whose one chunk holds a fresh atom 47 with
   the byte's value (trim_l.v's tl_regions, the same thing for trim's own byte loop). It is built from pf_a7_q.v's
   a7_seed: buf's chunkless region is dropped (the runs that read the byte write nothing), the environment gets atom 47
   (the regions and facts of a7_ss name no atom above 46), the byte's region and two facts are added: atom 47 is a
   byte and the pointer atom r lies in [4096, 2^47 - 16] (the token executor's pointer fact, pf_a7_w1.v's w1_GF).
   The inline check before the load (#20 at 0x88300, #21 at 0x88324) is decided by the shadow entry w3_SH r d, whose
   range_addressable is pf_a7_d.v's a7_addr_buf (w3_shok). The slot region a7_slot_r stays: 0x8832c reloads s3 from it.
   No instruction is walked here; no Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a5_k pf_a7_d pf_a7_q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the byte's region: base atom r, [d, d + 1), read-only, its value atom 47 *)
Definition w3_byte_r (r : nat) (d : Z) : YP09.region :=
  YP09.mkRegion (Some r) d (d + 1) d d [YP09.mkChunk d (CVal 1 (SOff 47 0))].
Definition w3_ss0 (pc : Z) (r : nat) (d : Z) : sstate :=
  mkSS pc sr_atoms [w3_byte_r r d; a7_saved_r; a7_slot_r; a7_sh_r] None a7_facts.
Definition w3_ss (pc : Z) (r : nat) (d : Z) : sstate :=
  add_atom (add_atom (w3_ss0 pc r d) 47%nat (mkAF 0 255 0)) r (mkAF 4096 (2 ^ 47 - 16) 0).
Definition w3_SH (r : nat) (d : Z) : list shent := [mkSHE r d (d + 1)].

Lemma w3_byte_wf : forall r d, region_wf (w3_byte_r r d) = true.
Proof.
  intros r d. assert (E1 : (d <=? d + 1) = true) by (apply Z.leb_le; lia).
  unfold region_wf, w3_byte_r, chunk_inside.
  cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb YP09.c_off YP09.c_len YP09.c_val
    YP09.cv_len Z.of_N].
  rewrite E1, !Z.leb_refl. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environment: a7_E with atom 47 = the byte *)
Definition w3_E (rX : bvmap 5 word) (v : pfv) (pos z : Z) : env :=
  Eimg (Ereg rX (a7_extra v pos ++ [Z_to_bv 64 z])).

Lemma w3_E_img : forall rX v pos z, img_env VAL A_LIM (w3_E rX v pos z).
Proof. intros. unfold w3_E. apply Eimg_env. Qed.

Lemma w3_extra_len : forall v pos, length (a7_extra v pos) = 15%nat.
Proof. intros v pos. unfold a7_extra. rewrite length_app, !length_map. reflexivity. Qed.

(* below atom 47 the environment is a7_E *)
Lemma w3_E_agree47 : forall rX v pos z, env_agree 47 (a7_E rX v pos) (w3_E rX v pos z).
Proof.
  intros rX v pos z. split; [|reflexivity]. intros n Hn. unfold w3_E, a7_E.
  rewrite !Eimg_low by (unfold A_TEXT; lia).
  destruct (Nat.lt_ge_cases n 32) as [H32 | H32].
  - unfold Ereg. cbn [ew]. replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  - replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra.
    rewrite app_nth1 by (rewrite w3_extra_len; lia). reflexivity.
Qed.

Lemma w3_E_agree : forall rX v pos z, env_agree 32 (Ereg rX (a7_extra v pos ++ [Z_to_bv 64 z])) (w3_E rX v pos z).
Proof.
  intros rX v pos z. split; [|reflexivity]. intros n Hn. unfold w3_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.

Lemma w3_ew_lt47 : forall rX v pos z n, (n < 47)%nat -> ew (w3_E rX v pos z) n = ew (a7_E rX v pos) n.
Proof. intros rX v pos z n Hn. exact (proj1 (w3_E_agree47 rX v pos z) n Hn). Qed.

Lemma w3_ew_47 : forall rX v pos z, ew (w3_E rX v pos z) 47 = Z_to_bv 64 z.
Proof.
  intros rX v pos z. unfold w3_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 47%nat with (32 + 15)%nat. rewrite ew_Ereg_extra. rewrite app_nth2 by (rewrite w3_extra_len; lia).
  rewrite w3_extra_len. reflexivity.
Qed.

Section e.
Variable B : asyms.

(* the seed: a7_seed's state with buf's region replaced by the byte's *)
Lemma w3_seed : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc (pc : Z) (r : nat) (rb : bv 5) q d z,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  (r < 32)%nat -> Z.of_nat r = bv_unsigned rb -> getr rX rb = w64 q ->
  a7_buf v pos <= q -> 0 <= d -> q + d < a7_buf v pos + 512 ->
  rdW Wc memc (q + d) = Some z ->
  st_ok_pi SEGS VAL (w3_E rX v pos z) (w3_ss pc r d)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
  intros v pos lyc Sc Wc rX memc mdc pc r rb q d z HB Hr Hrb Hq Hq0 Hd Hqd Hz.
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB))
    as (HF1 & HF2 & HF3 & HF4).
  pose proof alloc_ceiling_lt as Hac.
  assert (Hq64 : 0 <= q < 2 ^ 64) by (unfold a7_buf, PF_O_BUF in *; lia).
  pose proof (a7_seed B v pos lyc Sc Wc rX memc mdc pc false HB) as HS0.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
  pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HRG.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
  destruct (aview_byte SEGS (w_H Wc) memc (q + d) z Hz) as (b & Hb & Hzb & Hz256).
  (* drop buf's region *)
  assert (HS1 : st_ok_pi SEGS VAL (a7_E rX v pos) (mkSS pc sr_atoms [a7_saved_r; a7_slot_r; a7_sh_r] None a7_facts)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))).
  { unfold st_ok_pi, abs_ss in HS0 |- *.
    pose proof (st_ok_submem SEGS _ _ _ [a7_saved_r; a7_slot_r; a7_sh_r] HS0 ltac:(cbn; submem_tac)
      ltac:(vm_compute; reflexivity)) as H. exact H. }
  (* atom 47 *)
  assert (HS2 : st_ok_pi SEGS VAL (w3_E rX v pos z) (mkSS pc sr_atoms [a7_saved_r; a7_slot_r; a7_sh_r] None a7_facts)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))).
  { unfold st_ok_pi, abs_ss in HS1 |- *.
    exact (st_ok_agree SEGS 47 _ _ _ _ HS1 (w3_E_agree47 rX v pos z) ltac:(vm_compute; reflexivity)). }
  set (E := w3_E rX v pos z) in *.
  assert (Ur : bv_unsigned (ew E r) = q).
  { subst E. rewrite (w3_ew_lt47 rX v pos z r) by lia. rewrite (a7_ew_reg rX v pos r rb Hrb), Hq.
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U8 : bv_unsigned (ew E 8) = pf_sp0 v).
  { subst E. rewrite (w3_ew_lt47 rX v pos z 8) by lia.
    rewrite (a7_ew_reg rX v pos 8 (Z_to_bv 5 8) eq_refl).
    rewrite (a5_rg_get rX _ 8 (pf_sp0 v) HRG ltac:(unfold a5_FI; cbn [In]; tauto)). unfold w64. apply unsigned_lit_small. lia. }
  assert (U9 : bv_unsigned (ew E 9) = pf_s1 v).
  { subst E. rewrite (w3_ew_lt47 rX v pos z 9) by lia.
    rewrite (a7_ew_reg rX v pos 9 (Z_to_bv 5 9) eq_refl).
    rewrite (a5_rg_get rX _ 9 (pf_s1 v) HRG ltac:(unfold a5_FI; cbn [In]; tauto)). unfold w64. apply unsigned_lit_small. lia. }
  assert (U33 : bv_unsigned (ew E 33) = pf_SH v pos).
  { subst E. rewrite (w3_ew_lt47 rX v pos z 33) by lia. rewrite a7_ew_SH. apply unsigned_lit_small.
    unfold kLowMemEnd, kHighShadowEnd in *. lia. }
  assert (U47 : bv_unsigned (ew E 47) = z) by (subst E; rewrite w3_ew_47; apply unsigned_lit_small; lia).
  (* the byte's region *)
  pose proof (st_ok_pi_add_region E (mkSS pc sr_atoms [a7_saved_r; a7_slot_r; a7_sh_r] None a7_facts) _
    (w3_byte_r r d) HS2 (w3_byte_wf r d)) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  assert (HS4 : st_ok_pi SEGS VAL E (w3_ss0 pc r d)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))).
  { unfold w3_ss0. apply HS3.
    - unfold region_ok, w3_byte_r.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
      rewrite Ur. unfold a7_buf, PF_O_BUF in Hqd, Hq0.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val Z.of_N]. intros i Hi.
      assert (i = 0) as -> by lia. exists b. split.
      + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot].
        rewrite !Z.add_0_r, Z_to_bv_bv_unsigned, U47.
        change (8 * 0) with 0. rewrite Z.shiftr_0_r, Hzb.
        subst z. apply Z_to_bv_bv_unsigned.
      + rewrite !Z.add_0_r. exact Hb.
    - unfold a7_saved_r, a7_slot_r, a7_sh_r, w3_byte_r.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Ur, U8, U9, U33.
      unfold a7_buf, PF_O_BUF in Hqd, Hq0.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd in *.
      destruct G9 as [_ [G9 | [G9a G9b]]]; repeat split; lia. }
  (* atom 47 is a byte, atom r a pointer *)
  unfold w3_ss. apply st_ok_pi_add_fact; [apply st_ok_pi_add_fact; [exact HS4|]|].
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U47. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ur. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold a7_buf, PF_O_BUF in Hqd, Hq0. repeat split; lia.
Qed.

(* the shadow entry of the byte: it is in buf, so its shadow says addressable (a7_addr_buf) *)
Lemma w3_shok : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc (r : nat) (rb : bv 5) q d z,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  (r < 32)%nat -> Z.of_nat r = bv_unsigned rb -> getr rX rb = w64 q ->
  a7_buf v pos <= q -> 0 <= d -> q + d < a7_buf v pos + 512 ->
  sh_ok SEGS a7_Bx (w3_SH r d) (w3_E rX v pos z) (mrestrict (w_H Wc) memc).
Proof.
  intros v pos lyc Sc Wc rX memc mdc r rb q d z HB Hr Hrb Hq Hq0 Hd Hqd.
  pose proof (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HST7.
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc HST7) as (HF1 & HF2 & HF3 & HF4).
  pose proof alloc_ceiling_lt as Hac.
  pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HRG.
  assert (Hq64 : 0 <= q < 2 ^ 64) by (unfold a7_buf, PF_O_BUF in *; lia).
  assert (HRA : sa_addr (rdW Wc memc) (q + d) 1)
    by exact (a7_addr_buf B v pos lyc Sc Wc memc mdc (q + d) 1 HST7 ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (UBx : U (w3_E rX v pos z) a7_Bx = SHADOW_OFF).
  { unfold a7_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
    rewrite (w3_ew_lt47 rX v pos z 22) by lia. rewrite (a7_ew_reg rX v pos 22 (Z_to_bv 5 22) eq_refl).
    exact (a5_rg_get rX _ 22 SHADOW_OFF HRG ltac:(unfold a5_FI; cbn [In]; tauto)). }
  assert (UE : U (w3_E rX v pos z) (SOff r 0) = q).
  { apply U_atom; [|exact Hq64].
    rewrite (w3_ew_lt47 rX v pos z r) by lia. rewrite (a7_ew_reg rX v pos r rb Hrb). exact Hq. }
  unfold sh_ok, w3_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc (w3_E rX v pos z) a7_Bx r (q + d) 1 q d (d + 1)
    (proj1 (proj2 (proj2 (proj2 HRA)))) UBx UE); [lia | lia |].
  intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF3. unfold SHADOW_OFF.
  unfold a7_buf, PF_O_BUF in Hq0, Hqd. lia.
Qed.

End e.
End f.
End d.
