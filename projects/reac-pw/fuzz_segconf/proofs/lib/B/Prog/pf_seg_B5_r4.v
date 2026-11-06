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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 230 of its 272 lines of code are new or changed and 411 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   piece R4 -> L 0 (the B5 segment lane of the image-B G3 walk owner, piece prover: a sub-lane, 2026-10-30): b5_r4_ok : H_L B 0 n -> H_R4 B n.
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-B walk; the function's rule-24 record
   is the rule-24 lookup record).
   ADAPTED from the image-A G3 walk owner's image-A piece lib/A/Prog/pf_a5_r3.v (commit 003b9dc874eb, a5_r4_ok)
   and the unit owner's UBSan piece lib/U/Prog/pf_p2.v (the trap's arithmetic), re-derived on image B's code with the B5
   kit (pf_seg_B5_k.v) and the template piece pf_seg_B5_r2.v (the B5 segment lane, 2305ce2c2c85).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), reached from R3 when LEN < 512 and the checked
   memcpy has copied the line into buf:
     0x882cc `ld a0,176(s1)`    a0 = slot 0xb0 = pf_nt buf = 2 ^ 64 - 1 - buf (PF_SL)
     0x882d0 `bltu a0,s7`       UBSan trap T07 (pointer overflow of `buf + len`, reac_segconf.c:139): taken only when
                                2 ^ 64 - 1 - buf < LEN; refuted: buf + 511 < 2 ^ 47 (b5_geoP: F + 2048 <=
                                alloc_ceiling), LEN < 512 (INV_R4)
     0x882d4 `li a3,0`
     0x882d8 `ld a0,208(s1)`    a0 = slot 0xd0 = buf (PF_SL)
     0x882dc `add s7,a0,s7`     s7 = buf + LEN (the seed's alias fact: atom 34)
     0x882e0 `sb zero,0(s7)`    buf[LEN] = 0: an UNCHECKED store (no inline ASan check in front of it) into the owned
                                class-5 frame (awr_byte's in_frames clause; writable by the frame's presence)
     0x882e4 `mv a1,a0`         a1 = buf
     0x882e8 .. 0x882f4         a6 = 1, a7 = ' ', t0 = '\t', t1 = ';'
   then L 0 at 0x882f8 (k = 0: a0 = a1 = buf, a3 = 0). 11 of B5's 116 instructions walked (0x882cc .. 0x882f4), trap
   T07 discharged, no inline check, no call, one write (buf[LEN]). Section hypotheses: none. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B5_d pf_seg_B5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register of the state after a run, as the executor wrote it *)
Ltac b5r4_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b5r4_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* the seed at R4: every register its own atom; the extra atoms 32 = pf_nt buf, 33 = buf, 34 = buf + LEN; the slots
   0xb0 / 0xd0 read on s1's atom 9 (no byte of that region written); the one byte buf[LEN] writable on atom 34; the
   alias buf + LEN = atom 34 (0x882dc) *)
Definition b5r4_ss : sstate := mkSS B5_R4 sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xb0 0xd8 0xb0 0xb0
     [YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 34%nat) 0 1 0 1 []] None
  (mkFacts [] [] [(SAlu ALU_ADD (SOff 33 0) (SOff 23 0), SOff 34 0)]).

(* reading back the byte a run wrote into a region (pf_a5_r3.v r3_byte_of_region) *)
Lemma b5r4_byte_of_region : forall {segs : list Segment} E H m n b lo hi wlo whi cs od e,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> aview segs H m (b + od) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros segs E H m n b lo hi wlo whi cs od e HR Hb Hin.
pose proof (field_of_region_any (segs := segs) E (mrestrict H m) n b cs lo hi wlo whi od 1 e HR Hb Hin
  ltac:(cbn; lia)) as V.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. change (N.to_nat 1) with 1%nat in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

(* the trap T07 (0x882d0 `bltu a0,s7` taken, a0 = pf_nt buf): 2 ^ 64 - 1 - buf < LEN is false when buf + LEN < 2 ^ 63 *)
Lemma b5r4_t07 : forall E a b bf len, U E a = 2 ^ 64 - 1 - bf -> U E b = len -> 0 <= bf -> 0 <= len ->
  bf + len < 2 ^ 63 -> branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = true -> False.
Proof.
intros E a b bf len Ha Hb H0 H1 H2 Hc. rewrite branch_ltu_U, Ha, Hb in Hc. apply Z.ltb_lt in Hc. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* the registers a run left as their own atoms keep the values they had (pf_a5_r3.v r3_rg_keep_pi) *)
Lemma b5r4_rg_keep : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Hs, b5_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma b5_r4_ok : forall n, H_L B 0 n -> H_R4 B n.
Proof.
intros n HL0 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HL512 & HZB & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & LS & HSTR & HADDR & HTH & HCH).
pose proof HLN as (HCTX & Ho & Hk & HST).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & _).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & Hfb & _).
rewrite EF in Hfb. change (fs_frame_bytes 5) with 2048 in Hfb.
set (LEN := b5_len v o) in *.
set (bf := b5_buf v pos) in *.
assert (Ebf : bf = pf_F v pos + 64) by reflexivity.
assert (HbE : 0 <= Z.of_nat LEN < 512) by lia.
(* the slots 0xb0 / 0xd0 *)
assert (SB0 : rdword (rdW Wc memc) (pf_s1 v + 0xb0) = Some (pf_nt bf)).
{ unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xb0, pf_nt (pf_F v pos + PF_O_BUF)) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
assert (SD0 : rdword (rdW Wc memc) (pf_s1 v + 0xd0) = Some bf).
{ unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xd0, pf_F v pos + PF_O_BUF) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
(* the registers at R4 *)
rewrite b5_rg_app in HRG. destruct HRG as (HRL & HRR). rewrite b5_rg_app in HRR. destruct HRR as (HRM & HR23).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b5_rg rX _ 9 _ HRG0); b5_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (Z.of_nat LEN)) by (apply (b5_rg rX _ 23 _ HR23); b5_in).
(* the seed *)
set (E := Eimg (Ereg rX [w64 (pf_nt bf); w64 bf; w64 (bf + Z.of_nat LEN)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (pf_nt bf))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bf)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (bf + Z.of_nat LEN))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat LEN)) by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = bf + Z.of_nat LEN)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E b5r4_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B5_R4)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b5r4_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xb0 8 (SOff 32 0) (pf_nt bf)).
        -- rewrite b5_den_atom0. exact E32.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold pf_nt. lia.
        -- change (Z.of_N 8) with 8. lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ SB0).
      * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xd0 8 (SOff 33 0) bf).
        -- rewrite b5_den_atom0. exact E33.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- change (Z.of_N 8) with 8. lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ SD0).
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o0 Ho0. apply (apresent_writable SEGS). apply (proj1 (Hfb (bf + Z.of_nat LEN + o0) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U34.
    split; [split; [right; lia | exact I] | split; exact I].
  - split; [exact I | split; [exact I |]].
    cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu.
    rewrite (U_atom E 33 bf E33) by lia. rewrite (U_atom E 23 (Z.of_nat LEN) E23) by lia.
    rewrite (U_atom E 34 (bf + Z.of_nat LEN) E34) by lia.
    cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
unfold cfg_at. change (w64 (BASE + B5_R4)) with (Z_to_bv 64 (BASE + B5_R4)).
(* 0x882cc `ld a0,176(s1)`, up to the trap branch 0x882d0 *)
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr & Ha). unfold b5r4_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite U9 in Ha. lia.
  - rewrite U34 in Ha. right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr.
    cbn [fst snd]. rewrite EF. change (fs_frame_bytes 5) with 2048. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b5r4_clear_md.
rename ms into ms1, HG into HG1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> a <> bf + Z.of_nat LEN -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E (ss_mem b5r4_ss) (w_H Wc) memc (ms_mem ms1)
    (fun a => a = bf + Z.of_nat LEN) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
    [rewrite U9 in Hrr; lia | rewrite U34 in Hrr; cbv beta; lia]. }
clear HFr HF.
psrr_branch_pi RUNP BR HS.
- (* taken: the trap T07, refuted *)
  exfalso.
  lazymatch type of Hc with branch_taken BC_LTU (sv_denot _ ?a) (sv_denot _ ?b) = true =>
    refine (b5r4_t07 E a b bf (Z.of_nat LEN) _ _ ltac:(lia) ltac:(lia) ltac:(lia) Hc) end.
  + apply (U_atom E 32 _ E32). unfold pf_nt. lia.
  + apply (U_atom E 23 _ E23). lia.
- (* not taken: to L 0 *)
  clear Hc.
  paj_run_to_sh RUNTO HS HJ B5_L.
  { intros a (r & Hr & Ha). vm_compute in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    - rewrite U9 in Ha. lia.
    - rewrite U34 in Ha. right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr.
      cbn [fst snd]. rewrite EF. change (fs_frame_bytes 5) with 2048. lia. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b5r4_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> a <> bf + Z.of_nat LEN -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem ms1) a).
  { intros a Ha Hn. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms1) (ms_mem ms) (fun a => a = bf + Z.of_nat LEN) HFr);
      [|exact Ha | exact Hn] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    destruct Hin' as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
      [rewrite U9 in Hrr; lia | rewrite U34 in Hrr; cbv beta; lia]. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> bf + Z.of_nat LEN -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)).
  assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None).
  { intros a Hv. apply (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem ms) a HG).
    exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms1) a HG1 Hv). }
  (* buf[LEN] = 0, read back from the byte's region *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
  cbn [ms_mem restrict] in HR1.
  assert (HW0 : rdW Wc (ms_mem ms) (bf + Z.of_nat LEN) = Some 0).
  { pose proof (b5r4_byte_of_region E (w_H Wc) (ms_mem ms) 34 _ _ _ _ _ _ 0 (SLit 0) HR1 U34
      ltac:(cbn [In]; left; reflexivity)) as HB0.
    rewrite Z.add_0_r in HB0. rewrite HB0. reflexivity. }
  clear HFr HF.
  assert (KP : b5_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { split.
    - intros a Ha Hn. apply KM; [exact Ha|]. intros ->. apply Hn. unfold b5_Wr. right; left. fold bf. lia.
    - intros a _ Hv. exact (HV a Hv). }
  (* the registers at L 0 *)
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
      getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b5r4_rreg HS; rewrite b5_den_atom0; apply EE; reflexivity |]). destruct Hr. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B5_L) rg mm mdx) end.
  apply (HL0 v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) _ cf cur nm o ln d).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  + (* pf_base: the same frame state, buf's shadow cells untouched *)
    apply (b5_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc (ms_regs ms) (ms_mem ms) _ PF_SC_LINE HB HJ).
    * destruct HSc as (f0 & HS0). exists f0. rewrite HS0. rewrite b5_set_fs2. reflexivity.
    * apply Permutation_refl.
    * exact KP.
    * unfold pf_rg, b5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b5_rg rX _ _ _ HRG0); b5_in | b5_in]).
    * apply (b5_keep_fsh_same v pos _ _ PF_SC_LINE G KP); [|exact HFSH].
      intros i Hi. destruct (b5_SHv v pos G) as (ESH & SH1 & SH2 & F8).
      apply KM; [lia|]. intros Hq. rewrite Ebf in Hq. lia.
  + split; [exact HCTX|]. split; [exact Ho|]. split; [exact Hk|].
    exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm _ G HAR Hin EF KP HCH HST).
  + exact HL512.
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i LEN) as [Hi1 | Hi1].
    * rewrite app_nth1 by exact Hi1. rewrite KM by lia. exact (HZB i Hi1).
    * assert (i = LEN) as -> by (unfold LEN, b5_len in *; lia).
      rewrite app_nth2 by (unfold LEN, b5_len; lia).
      replace (LEN - length (pf_line (p_s v) o))%nat with 0%nat by (unfold LEN, b5_len; lia).
      cbn [nth]. exact HW0.
  + lia.
  + intros j Hj. lia.
  + unfold pf_rg. rewrite !Forall_app. split; [|split].
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b5_rg rX _ _ _ HRL); b5_in | b5_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b5_rg rX _ _ _ HRM); unfold PF_RM; b5_in | b5_in]).
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
      -- rewrite Z.add_0_r. b5r4_rreg HS. rewrite b5_den_atom0. exact E33.
      -- rewrite Z.add_0_r. b5r4_rreg HS. rewrite b5_den_atom0. exact E33.
      -- b5r4_rreg HS. reflexivity.
      -- b5r4_rreg HS. reflexivity.
      -- b5r4_rreg HS. reflexivity.
      -- b5r4_rreg HS. reflexivity.
      -- b5r4_rreg HS. reflexivity.
Qed.
End e.
End f.
End d.
