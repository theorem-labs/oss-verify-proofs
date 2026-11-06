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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 386 of its 431 lines of code are new or changed and 408 lines of the source are left out. *)
(* reac_segconf_parse_file (image B, 0x87e38), segment B10a (ROLE 0x88630 -> INTENT 0x888e4): the internal points,
   the four symbolic seeds of the walk, their entry lemmas, and the internal statements. The B10a segment lane of
   the image-B G3 walk owner, 2026-10-30. ADAPTED from the image-A G3 walk owner's image-A segment kit lib/A/Prog/pf_a10a_k.v (commit
   73bafa8e5cd9) and the seed form of the image-B G3 walk owner's image-B trim walk lib/B/Prog/trim_l.v /
   trim_f.v (fuzz_command's answer_l.v al_entry form: a loop re-seeded at each iteration).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), cut into four runs:
     P0   0x88630-0x8864c  `sb zero,80..87(s5)`: low's eight shadow cells in scope; a PLAIN run (its only region,
          the eight cells at s5 = SH, lies in the shadow band, which a token run must not write).
     P1   0x88650-0x88670  `ld a0,112(s1)` (val, slot 0x70); check B#16 (0x88654-0x88660, slow arm 0x88fb4-0x88fbc,
          error call 0x89280 errpath_load1) on val[0], decided by the shadow entry of val (val lies in buf, whose
          64 cells are 0 inside a line); `lbu a2,0(a0)`; `beqz a2` -> 0x888bc (`li a3,0`, EXIT) else `li a6,0`,
          `addi a1,a0,1` -> LOOP.
     LOOP 0x88674-0x886c4  the fold: `li a3,63; beq a6,a3` -> EXIT (li = 63); low[li] = fold(c) (0x88698, no
          check: buf ... the store is to low, in scope since P0); UBSan trap T17 `beq a3,s10` (0x8869c: q = val + li
          would wrap; s10 = -1), not taken: q <= buf + 512 < 2 ^ 47 (the seed's range fact on atom 32, decided by
          the executor); check B#17 (0x886a0-0x886b0, slow arm 0x886c8-0x886d0, error call 0x89240 errpath_load1)
          on val[li + 1], decided by the shadow entry of val + li + 1 (li + 1 <= |val|, inside buf); `lbu
          a2,1(a3)`; li++; `beqz a2` -> EXIT (a3 = li) else `j` LOOP.
     EXIT 0x888c0-0x888e0  UBSan trap T20 `bltu a0,a3` (0x888c4: a0 = slot 0x30 = ~low, a3 = li <= 63): not
          taken, ~low >= 2 ^ 64 - 1 - 2 ^ 47 > 63 (the seed's range facts, decided by the executor); s7 = low
          (slot 0xa0); check B#25 (0x888cc-0x888dc, slow arm 0x88fc0-0x88fc8, error call 0x89284
          errpath_store1) on low + li, decided by the shadow entry of low + li (low's cells zeroed by P0);
          `sb zero,0(a0)` (low[li] = 0) -> INTENT 0x888e4.
   61 instructions: 0x88630-0x886d4 (41), 0x888bc-0x888e4 (10), 0x88fb4-0x88fcc (6), 0x8923c-0x89244 (2),
   0x89280-0x89288 (2). Checks: B#16, B#17, B#25 (3). Traps: T17, T20 (2). No call. *)
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
  refuse_c reac_segconf_parse_file_c pf_pieces trim_k pf_seg_B10a_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the internal points (listing offsets; BASE + AF_reac_segconf_parse_file = 0x87e38) ---- *)
Definition B10_P1 : Z := AF_reac_segconf_parse_file + 0x818.    (* 0x88650 ld a0,112(s1) *)
Definition B10_LOOP : Z := AF_reac_segconf_parse_file + 0x83c.  (* 0x88674 li a3,63: the fold's head *)
Definition B10_EXIT : Z := AF_reac_segconf_parse_file + 0xa88.  (* 0x888c0 ld a0,48(s1): the fold's exit *)
Lemma b10_pcs : seg_text + PF_ROLE = 0x88630 /\ seg_text + B10_P1 = 0x88650 /\ seg_text + B10_LOOP = 0x88674 /\
  seg_text + B10_EXIT = 0x888c0 /\ seg_text + PF_INTENT = 0x888e4.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the range facts: a frame address lies in [4096, 0x7fffff800000] (pf_tf: 4096 <= F; the journal's frame:
   F + 2048 <= alloc_ceiling <= 0x7fffff800000, asan_consts) *)
Definition B10_HI : Z := 0x7fffff800000.
Definition B10_M1 : Z := 2 ^ 64 - 1.
Definition b10_Bx : sv := SOff 20 0.

(* ---- the seeds ---- *)
(* P0, ROLE 0x88630: every register its own atom; the one region is low's eight shadow cells at s5 = SH (atom 21),
   written *)
Definition b10_ss0 : sstate :=
  mkSS PF_ROLE sr_atoms [YP09.mkRegion (Some 21%nat) 80 88 80 88 []] None (mkFacts [] [] []).
(* P1, 0x88650: s1's slot 0x70 holds val (atom 32), the byte val[0] is atom 33; s4 = SB (atom 20); the shadow
   entry of val[0] *)
Definition b10_ss1 : sstate :=
  mkSS B10_P1 sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x70 0x78 0 0 [YP09.mkChunk 0x70 (CVal 8 (SOff 32 0))];
     YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
    (mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 B10_HI 0); (33%nat, mkAF 0 255 0)] [] []).
Definition b10_SH1 : list shent := [mkSHE 32 0 1].
(* LOOP, 0x88674: a0 = val (atom 10), a1 = val + 1 (atom 11), a6 = li (atom 16), a2 = val[li] (atom 12), s10 = -1
   (pinned); atom 32 = val + li, 33 = low (slot 0xa0), 34 = low + li (written), 35 = val[li + 1]; the aliases
   name the code's sums a0 + a6, a1 + a6, low + a6 by these atoms *)
Definition b10_ss2 : sstate :=
  mkSS B10_LOOP (sr_set sr_atoms 26%bv (SLit B10_M1))
    [YP09.mkRegion (Some 9%nat) 0xa0 0xa8 0 0 [YP09.mkChunk 0xa0 (CVal 8 (SOff 33 0))];
     YP09.mkRegion (Some 32%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 35 0))];
     YP09.mkRegion (Some 34%nat) 0 1 0 1 []] None
    (mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 B10_HI 0); (33%nat, mkAF 4096 B10_HI 0);
              (34%nat, mkAF 4096 B10_HI 0); (35%nat, mkAF 0 255 0)] []
       [(SAlu ALU_ADD (SOff 10 0) (SOff 16 0), SOff 32 0); (SAlu ALU_ADD (SOff 11 0) (SOff 16 0), SOff 32 1);
        (SAlu ALU_ADD (SOff 33 0) (SOff 16 0), SOff 34 0)]).
Definition b10_SH2 : list shent := [mkSHE 32 1 2; mkSHE 34 0 1].
(* EXIT, 0x888c0: a3 = li (atom 13, at most 63), atom 32 = ~low (slot 0x30), 33 = low (slot 0xa0), 34 = low + li
   (written) *)
Definition b10_ss3 : sstate :=
  mkSS B10_EXIT sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x30 0xa8 0 0
       [YP09.mkChunk 0x30 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xa0 (CVal 8 (SOff 33 0))];
     YP09.mkRegion (Some 34%nat) 0 1 0 1 []] None
    (mkFacts [(20%nat, mkAF SB SB 0); (13%nat, mkAF 0 63 0); (32%nat, mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1 - 4096) 0);
              (33%nat, mkAF 4096 B10_HI 0); (34%nat, mkAF 4096 B10_HI 0)] []
       [(SAlu ALU_ADD (SOff 33 0) (SOff 13 0), SOff 34 0)]).
Definition b10_SH3 : list shent := [mkSHE 34 0 1].

(* ---- small facts ---- *)
Lemma b10_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b10_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma b10_m1 : w64 (-1) = Z_to_bv 64 B10_M1.
Proof. apply w64_mod. reflexivity. Qed.
Lemma b10_u_add : forall E a b x y, U E a = x -> U E b = y -> 0 <= x + y < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Ha Hb H. rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.
Ltac b10_in := cbn [In app PF_RL PF_RM PF_SL]; repeat first [left; reflexivity | right].
(* the byte the fold stores (0x88688-0x88698), as the executor leaves it *)
Definition b10_fold_sv : sv :=
  SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 12 (-65)) (SLit 26)) (SLit 5)).
Lemma b10_fold_U : forall E c, ew E 12 = Z_to_bv 64 c -> 0 <= c < 256 -> U E b10_fold_sv mod 256 = lower c.
Proof.
intros E c H Hc. unfold b10_fold_sv.
rewrite U_SAlu, U_SAlu, U_SAlu, !U_SOff, !U_SLit, H, unsigned_lit_small by lia. cbn [zalu_raw].
change (Z.land (zcanon 5) 63) with 5. change (zcanon 26) with 26.
rewrite <- (b10_fold_arith c Hc). unfold zcanon, M64. rewrite Z.add_0_r.
rewrite (Z.mod_small c) by lia.
f_equal. f_equal. f_equal.
destruct ((c + -65) mod 2 ^ 64 <? 26); cbn; reflexivity.
Qed.
(* a byte a run left in a one-byte chunk of a region *)
Lemma b10_rbyte : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {PI : PAImg seg_listing}
  E ss ms (H : word -> bool) (nn i : nat) lo hi wlo whi cs od e b,
  st_ok_pi (@pa_segs _ seg_listing PI) (@pa_val _ seg_listing PI) E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  In (YP09.mkChunk od (CVal 1 e)) cs ->
  bv_unsigned (ew E nn) = b ->
  aview (@pa_segs _ seg_listing PI) H (ms_mem ms) (b + od) = Some (U E e mod 256).
Proof.
intros fx rc PI E ss ms H nn i lo hi wlo whi cs od e b HS Hn Hin Hb.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ nn b cs lo hi wlo whi od 1%N e Hr Hb Hin ltac:(lia)) as V.
cbn [ms_mem restrict] in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V. cbn [N.to_nat] in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- the entry lemmas: each seed holds at a concrete state ---- *)
Lemma b10_entry0 : forall (W : world SEGS) (regs1 : bvmap 5 word) memc SH,
  getr regs1 (Z_to_bv 5 21) = w64 SH -> 0 <= SH -> SH + 88 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> apresent (w_H W) memc (SH + 80 + i)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) b10_ss0
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + PF_ROLE)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc SH H21 HS0 HS1 HP.
set (E := Eimg (Ereg regs1 [])).
assert (U21 : bv_unsigned (ew E 21) = SH)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs1 _ 21 (Z_to_bv 5 21) eq_refl), H21; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b10_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U21. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). replace (SH + o) with (SH + 80 + (o - 80)) by lia. apply HP. lia.
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.

Lemma b10_entry1 : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 vp c0,
  getr regs1 (Z_to_bv 5 9) = w64 s1 -> getr regs1 (Z_to_bv 5 20) = w64 SB ->
  rdword (rdW W memc) (s1 + 0x70) = Some vp -> rdW W memc vp = Some c0 -> 0 <= c0 < 256 ->
  4096 <= vp -> vp + 1 <= alloc_ceiling -> alloc_ceiling <= s1 -> s1 + 0x78 <= 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])) b10_ss1
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + B10_P1)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 vp c0 H9 H20 Hw Hc Hc0 Hvp Hvp2 Hs1 Hs2.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])).
assert (E9 : ew E 9 = w64 s1) by (subst E; rewrite (ew_Eimg_Ereg_nat regs1 _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E20 : ew E 20 = w64 SB) by (subst E; rewrite (ew_Eimg_Ereg_nat regs1 _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E32 : ew E 32 = w64 vp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (HB : alloc_ceiling <= B10_HI < 2 ^ 64) by (unfold B10_HI; lia).
rewrite restrict_mkst_fx. unfold b10_ss1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1 0x70 8 (SOff 32 0) vp);
      [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
    exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc vp c0 Hc) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E33.
      rewrite !Z.add_0_r, (unsigned_lit_small c0), (unsigned_lit_small c0) by lia. change (8 * 0) with 0.
      rewrite Z.shiftr_0_r. subst c0. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32. unfold w64. rewrite !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E32, E33. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
Qed.

Definition b10_E2 (regs1 : bvmap 5 word) (vp k low c1 : Z) : env :=
  Eimg (Ereg regs1 [w64 (vp + k); w64 low; w64 (low + k); Z_to_bv 64 c1]).
Lemma b10_entry2 : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 vp k low c1,
  getr regs1 (Z_to_bv 5 9) = w64 s1 -> getr regs1 (Z_to_bv 5 20) = w64 SB ->
  getr regs1 (Z_to_bv 5 26) = w64 (-1) ->
  getr regs1 (Z_to_bv 5 10) = w64 vp -> getr regs1 (Z_to_bv 5 11) = w64 (vp + 1) ->
  getr regs1 (Z_to_bv 5 16) = w64 k -> 0 <= k <= 63 ->
  4096 <= vp -> vp + k + 2 <= alloc_ceiling -> 4096 <= low -> low + 64 <= alloc_ceiling ->
  rdword (rdW W memc) (s1 + 0xa0) = Some low ->
  rdW W memc (vp + k + 1) = Some c1 -> 0 <= c1 < 256 ->
  apresent (w_H W) memc (low + k) ->
  alloc_ceiling <= s1 -> s1 + 0xa8 <= 2 ^ 64 ->
  vp + k + 2 <= low + k ->
  st_ok_pi SEGS VAL (b10_E2 regs1 vp k low c1) b10_ss2
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + B10_LOOP)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 vp k low c1 H9 H20 H26 H10 H11 H16 Hk Hv1 Hv2 Hl1 Hl2 Hw Hc Hc1 Hp Hs1 Hs2 Hd.
pose proof asan_consts as (C1 & _).
set (E := b10_E2 regs1 vp k low c1).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j [w64 (vp + k); w64 low; w64 (low + k); Z_to_bv 64 c1] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold b10_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth] in E32, E33, E34, E35. clear EX.
assert (E9 : ew E 9 = w64 s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew E 10 = w64 vp) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew E 11 = w64 (vp + 1)) by (rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E16 : ew E 16 = w64 k) by (rewrite (EE 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E20 : ew E 20 = w64 SB) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (HB : alloc_ceiling <= B10_HI < 2 ^ 64) by (unfold B10_HI; lia).
rewrite restrict_mkst_fx. unfold b10_ss2. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. rewrite <- b10_m1. exact (b10_bvr regs1 26%bv 26 _ eq_refl H26).
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1 0xa0 8 (SOff 33 0) low);
      [cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
    exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc (vp + k + 1) c1 Hc) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E35.
      rewrite !Z.add_0_r, (unsigned_lit_small c1), (unsigned_lit_small c1) by lia. change (8 * 0) with 0.
      rewrite Z.shiftr_0_r. subst c1. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E34. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hp.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32, E34. unfold w64. rewrite !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E20, E32, E33, E34, E35. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|split; [|split; [|exact I]]]; apply U_inj.
    * rewrite (b10_u_add E _ _ vp k); [| apply U_atom; [exact E10 | lia] | apply U_atom; [exact E16 | lia] | lia].
      symmetry. apply U_atom; [exact E32 | lia].
    * rewrite (b10_u_add E _ _ (vp + 1) k); [| apply U_atom; [exact E11 | lia] | apply U_atom; [exact E16 | lia] | lia].
      rewrite (U_atom_off E 32 (vp + k) 1 E32) by lia. lia.
    * rewrite (b10_u_add E _ _ low k); [| apply U_atom; [exact E33 | lia] | apply U_atom; [exact E16 | lia] | lia].
      symmetry. apply U_atom; [exact E34 | lia].
Qed.

Definition b10_E3 (regs1 : bvmap 5 word) (low k : Z) : env :=
  Eimg (Ereg regs1 [w64 (pf_nt low); w64 low; w64 (low + k)]).
Lemma b10_entry3 : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 k low,
  getr regs1 (Z_to_bv 5 9) = w64 s1 -> getr regs1 (Z_to_bv 5 20) = w64 SB ->
  getr regs1 (Z_to_bv 5 13) = w64 k -> 0 <= k <= 63 ->
  4096 <= low -> low + 64 <= alloc_ceiling ->
  rdword (rdW W memc) (s1 + 0x30) = Some (pf_nt low) ->
  rdword (rdW W memc) (s1 + 0xa0) = Some low ->
  apresent (w_H W) memc (low + k) ->
  alloc_ceiling <= s1 -> s1 + 0xa8 <= 2 ^ 64 ->
  st_ok_pi SEGS VAL (b10_E3 regs1 low k) b10_ss3
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + B10_EXIT)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 k low H9 H20 H13 Hk Hl1 Hl2 Hw30 Hwa0 Hp Hs1 Hs2.
pose proof asan_consts as (C1 & _).
set (E := b10_E3 regs1 low k).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [w64 (pf_nt low); w64 low; w64 (low + k)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold b10_E3; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth] in E32, E33, E34. clear EX.
assert (E9 : ew E 9 = w64 s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E13 : ew E 13 = w64 k) by (rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E20 : ew E 20 = w64 SB) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (HB : alloc_ceiling <= B10_HI < 2 ^ 64) by (unfold B10_HI; lia).
assert (HN : 0 <= pf_nt low < 2 ^ 64) by (unfold pf_nt, B10_HI in *; lia).
rewrite restrict_mkst_fx. unfold b10_ss3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ s1 0x30 8 (SOff 32 0) (pf_nt low));
        [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw30).
    * apply (chunk_ok_val SEGS E _ s1 0xa0 8 (SOff 33 0) low);
        [cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hwa0).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E34. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hp.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E34. unfold w64. rewrite !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E20, E13, E32, E33, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SB, pf_nt; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold pf_nt, B10_HI in *. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj.
    rewrite (b10_u_add E _ _ low k); [| apply U_atom; [exact E33 | lia] | apply U_atom; [exact E13 | lia] | lia].
    symmetry. apply U_atom; [exact E34 | lia].
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* ---- the internal statements: from a point of B10a the walk reaches ROLE's post ---- *)
Definition b10_post (v : pfv) (cf : rconf) (gi : nat) (nm : list Z) (o : nat) (ln : Z) : world SEGS -> config -> Prop :=
  pf_postm B v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln.
Definition b10_at (Wc : world SEGS) (regs1 : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (pc : Z)
  (Q : world SEGS -> config -> Prop) : Prop :=
  SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) Q.
(* EXIT: the fold has stopped after k = |r_low val 0 64| bytes, a3 = k *)
Definition B10_EXIT_stmt (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
  b10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc (length (r_low val 0 64)) ->
  getr regs1 (Z_to_bv 5 13) = w64 (Z.of_nat (length (r_low val 0 64))) ->
  b10_at Wc regs1 memc mdc B10_EXIT (b10_post v cf gi nm o ln).
(* LOOP with li = k: low[0 .. k) folded, a0 = val, a1 = val + 1, a2 = val[k] (not NUL), a6 = k *)
Definition B10_LOOP_k (n k : nat) : Prop :=
  forall v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
  b10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k ->
  (k < length val)%nat ->
  getr regs1 (Z_to_bv 5 10) = w64 vp -> getr regs1 (Z_to_bv 5 11) = w64 (vp + 1) ->
  getr regs1 (Z_to_bv 5 12) = w64 (nth k val 0) -> getr regs1 (Z_to_bv 5 16) = w64 (Z.of_nat k) ->
  b10_at Wc regs1 memc mdc B10_LOOP (b10_post v cf gi nm o ln).
(* P1: low's shadow cells in scope, nothing folded *)
Definition B10_P1_stmt (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
  b10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc 0 ->
  b10_at Wc regs1 memc mdc B10_P1 (b10_post v cf gi nm o ln).

(* ---- the facts a point of B10a reads off b10_mid ---- *)
Lemma b10_mid_facts : forall n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k,
  b10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k ->
  getr regs1 (Z_to_bv 5 9) = w64 (pf_s1 v) /\ getr regs1 (Z_to_bv 5 20) = w64 SB /\
  getr regs1 (Z_to_bv 5 26) = w64 (-1) /\
  alloc_ceiling <= pf_s1 v /\ pf_s1 v + 0xd8 + 8 <= 2 ^ 64 /\
  rdword (rdW Wc memc) (pf_s1 v + 0x70) = Some vp /\
  rdword (rdW Wc memc) (pf_s1 v + 0x30) = Some (pf_nt (pf_F v pos + PF_O_LOW)) /\
  rdword (rdW Wc memc) (pf_s1 v + 0xa0) = Some (pf_F v pos + PF_O_LOW) /\
  ~ In 0 val /\
  (forall i, (i <= length val)%nat -> rdW Wc memc (vp + Z.of_nat i) = Some (nth i val 0)) /\
  (forall i, (i < length val)%nat -> 0 <= nth i val 0 < 256) /\
  pf_F v pos + PF_O_BUF <= vp /\ vp + Z.of_nat (length val) < pf_F v pos + PF_O_BUF + 512 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= 2 ^ 47 /\ pf_F v pos + 2048 <= alloc_ceiling /\
  in_app (pf_F v pos) 2048 /\
  range_addressable (rdW Wc memc) SHADOW_OFF vp (Z.of_nat (length val) + 1) /\
  range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_LOW) 64 /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> apresent (w_H Wc) memc a) /\
  pf_F v pos = frame_addr lyc 5 pos /\ In (5, pos) (frames Sc) /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
Proof.
intros n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
  (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK).
pose proof (b10_geo B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val HKV)
  as (Gsp & Gsp47 & Gs1 & Gs32 & F32 & Fapp & Foff & F4096 & Fc & F47).
destruct HKV as ((HCX & HFI & HOBJ & HSL & HFSH) & HMID & HST & HKVS & HSLB & HRG).
pose proof HFI as (HJ0 & Hly & HSc & Hperm & HSV & HFL & HFRM & HTF & HC8 & HRG0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_reac_segconf_parse_file = 12832) by reflexivity. rewrite HSTK in Gsp.
destruct (b10_frame B LAWS v pos lyc Sc Wc memc mdc HJ Hly) as (Hin & _ & _ & _ & _ & _ & _ & Fp & _ & _).
assert (FS : forall a, alloc_ceiling <= a < 2 ^ 64 -> b10_far v pos a).
{ intros a Ha. split; [lia|]. apply (b10_nD v pos a F32 Fapp Foff Fc). right; right; right. lia. }
assert (FIN : forall a, pf_F v pos <= a < pf_F v pos + 2048 ->
  (a < pf_F v pos + PF_O_LOW \/ pf_F v pos + PF_O_LOW + 64 <= a) -> b10_far v pos a).
{ intros a Ha Ho. split; [lia|]. apply (b10_nD_in v pos a F32 Fapp Fc). left. split; [exact Ha | exact Ho]. }
assert (SLK : forall off, 0 <= off <= 0xd8 -> forall kk, 0 <= kk < 8 -> b10_far v pos (pf_s1 v + off + kk)).
{ intros off Hoff kk Hkk. apply FS. lia. }
assert (KW : forall off w, 0 <= off <= 0xd8 -> rdword (rdW Wc memc0) (pf_s1 v + off) = w ->
  rdword (rdW Wc memc) (pf_s1 v + off) = w).
{ intros off w Hoff Hw. apply (b10t_word _ _ (b10_far v pos) KM _ _ Hw). intros kk Hkk.
  replace (pf_s1 v + off + kk) with (pf_s1 v + off + kk) by lia. apply SLK; lia. }
destruct HKVS as (Hsplit & Hks & Hkb & Hvs & Hvb).
pose proof Hvs as ((HVZ & NZ) & _).
unfold pf_inb, PF_O_BUF in Hvb.
assert (HSL' : forall off w, In (off, w) (PF_SL v pos) -> rdword (rdW Wc memc0) (pf_s1 v + off) = Some w).
{ intros off w Hi. exact (proj1 (Forall_forall _ _) HSL (off, w) Hi). }
split.
{ rewrite HK by b10_inZ. exact (b10_rg_in rX0 _ 9 _ HRG0 ltac:(b10_in)). }
split.
{ rewrite HK by b10_inZ. rewrite SB_SHADOW_OFF. exact (b10_rg_in rX0 _ 20 _ HRG0 ltac:(b10_in)). }
split.
{ rewrite HK by b10_inZ. apply (b10_rg_in rX0 _ 26 _ HRG). b10_in. }
split; [lia|]. split; [lia|].
split; [apply KW; [lia | exact (proj1 (Forall_forall _ _) HSLB (0x70, vp) ltac:(b10_in))]|].
split; [apply KW; [lia | apply HSL'; b10_in]|].
split; [apply KW; [lia | apply HSL'; b10_in]|].
split; [exact NZ|].
assert (VB : forall i, (i <= length val)%nat -> rdW Wc memc0 (vp + Z.of_nat i) = Some (nth i val 0))
  by (intros i Hi; exact (sa_zs_nth _ vp val i HVZ Hi)).
split.
{ intros i Hi. rewrite KM; [exact (VB i Hi)|]. apply FIN; unfold PF_O_LOW; lia. }
split.
{ intros i Hi. pose proof (VB i ltac:(lia)) as E. destruct (aview_byte SEGS _ _ _ _ E) as (_ & _ & _ & Hr). exact Hr. }
split; [unfold PF_O_BUF; lia|]. split; [unfold PF_O_BUF; lia|].
split; [exact F4096|]. split; [exact F47|]. split; [exact Fc|]. split; [exact Fapp|].
split.
{ apply (b10_frame_ra _ v pos vp _ F32); [lia | lia |]. intros x Hx.
  assert (Hi : 8 <= (x - pf_F v pos) / 8 < 72).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite KM; [rewrite (HFSH ((x - pf_F v pos) / 8)) by lia; rewrite b10_shb_buf by lia; reflexivity|].
  split; [unfold pf_SH, shadow_addr, SHADOW_OFF; pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia));
          pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)); lia|].
  apply (b10_nD_in v pos _ F32 Fapp Fc). right. exists ((x - pf_F v pos) / 8). split; [reflexivity|]. lia. }
split.
{ apply (b10_frame_ra _ v pos _ _ F32); [unfold PF_O_LOW; lia | lia |]. intros x Hx. unfold PF_O_LOW in Hx.
  assert (Hi : 80 <= (x - pf_F v pos) / 8 < 88).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  replace (pf_SH v pos + (x - pf_F v pos) / 8) with (pf_SH v pos + 80 + ((x - pf_F v pos) / 8 - 80)) by lia.
  apply Z0. lia. }
split; [exact Fp|].
split; [unfold pf_F; rewrite Hly; reflexivity|].
split; [exact Hin|].
intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* b10_mid at P1: P0 has zeroed low's eight shadow cells and changed nothing else *)
Lemma b10_mid_init : forall n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
  INV_KV B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role = 0 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 80 <= a < pf_SH v pos + 88) -> rdW Wc memc a = rdW Wc memc0 a) ->
  (forall i, 0 <= i < 8 -> rdW Wc memc (pf_SH v pos + 80 + i) = Some 0) ->
  (forall r, In r B10_KZ -> getr regs1 (Z_to_bv 5 r) = getr rX0 (Z_to_bv 5 r)) ->
  b10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc 0.
Proof.
intros n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc HKV Hrole HJ KS Z0 HK.
split; [exact HKV|]. split; [exact Hrole|]. split; [exact HJ|].
split; [intros a (Ha & HD); apply KS; [exact Ha | intros Hr; apply HD; right; exact Hr]|].
split; [exact Z0|]. split; [intros i Hi; lia|]. split; [lia|]. split; [lia|]. exact HK.
Qed.
End e.
End f.
End d.
