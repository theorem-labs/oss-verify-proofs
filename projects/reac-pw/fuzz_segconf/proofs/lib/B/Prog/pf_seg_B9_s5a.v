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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 883 of its 935 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a9_s1.v, with its module paths and module names changed; 357 of its 424 lines of code are new or changed and 868 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_5 of
   segment B9 of reac_segconf_parse_file's walk, its two quote arms (lib/B/Prog/pf_seg_B9_s5k.v): from B9S5_DQ
   0x88480 (v0 starts with DQ) and from B9S5_SQ 0x88530 (v0 starts with SQ), each to the strip cut B9S5_ST 0x88554
   (the last byte is the same quote) or to K5 0x88570 (it is not: the value is v0, b9_unq_keep).
   A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: pieces of stretch SB9_5).
   ADAPTED from lib/B/Prog/trim_l.v (a load with its inline check, the byte an extra atom of a read-only one-byte
   region, the branch on it split by psrr_branch_tok) and lib/B/Prog/pf_seg_B9_s1.v (the B9 cut rebuilt):
     DQ: 0x88480 srli a3,a0,3; add a3,a3,s4; lb a3,0(a3); 0x8848c bnez a3 -> 0x88fec   check B#11 (load1 at a0)
         0x88490 lbu a0,0(a0); li a3,34; 0x88498 beq a0,a3 -> 0x8854c; 0x8849c j 0x88570 (K5)
     SQ: 0x88530 srli a3,a0,3; add a3,a3,s4; lb a3,0(a3); 0x8853c bnez a3 -> 0x88ff8   check B#13 (load1 at a0)
         0x88540 lbu a0,0(a0); li a3,39; 0x88548 bne a0,a3 -> 0x88570 (K5)
     both: 0x8854c bltu a2,a1 -> 0x891c8   UBSan trap T15 (vp0 + |v0| - 1 wraps): decided not taken by the executor
                                         from the seed's range facts (a2 = ~vp0 >= 2 ^ 64 - 2 ^ 47, a1 = |v0| - 1
                                         <= 511); 0x88550 add a0,s3,a1 -> B9S5_ST
   The checks are decided by the token executor from the shadow entry of a0 (a byte of buf, shadow 0 under
   PF_SC_LINE); their slow arms 0x88fec .. 0x88ff4 / 0x88ff8 .. 0x89000 and error calls 0x89290 / 0x89294
   (errpath_load1) are not reached. Instructions walked: DQ 0x88480 .. 0x8849c (8), SQ 0x88530 .. 0x88548 (7),
   0x8854c .. 0x88550 (2). Checks B#11, B#13; trap T15. No call. No Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
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
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c pf_seg_B9_s5k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac b9s5a_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b9s5a_kept HS EE :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = getr _ (Z_to_bv 5 ?r) =>
    let Hk := fresh "Hk" in prreg HS (Z_to_bv 5 r) Hk; rewrite Hk; apply EE; reflexivity end.
Lemma b9s5a_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* the byte branch: an atom of value b against a literal *)
Lemma b9s5a_br_eq : forall E (n : nat) b z r, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = r -> (b =? z) = r.
Proof. intros E n b z r H Hb Hz Hc. rewrite branch_eq_U, (U_atom E n b H Hb), (U_lit E z Hz) in Hc. exact Hc. Qed.
Lemma b9s5a_br_ne : forall E (n : nat) b z r, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = r -> negb (b =? z) = r.
Proof. intros E n b z r H Hb Hz Hc. rewrite branch_ne_U, (U_atom E n b H Hb), (U_lit E z Hz) in Hc. exact Hc. Qed.

(* the seed at an arm (pc = B9S5_DQ or B9S5_SQ): every register its own atom; the last byte of v0 at a0 the extra
   atom 32 of a read-only one-byte region of atom 10; range facts for a0 (the check's shadow entry), a1 and a2 (the
   trap T15), the shadow base s4 = SB and the byte *)
Definition b9s5a_regions : smem := [YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]].
Definition b9s5a_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (11%nat, mkAF 1 511 0); (12%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0);
           (20%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)] [] [].
Definition b9s5a_ss (pc : Z) : sstate := mkSS pc sr_atoms b9s5a_regions None b9s5a_facts.
Definition b9s5a_Bx : sv := SOff 20 0.
Definition b9s5a_SH : list shent := [mkSHE 10 0 1].
(* the registers an arm does not write *)
Definition b9s5a_keep : list Z := [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 23; 19; 15].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma b9s5a_seed : forall pc (Wc : world SEGS) (rX : bvmap 5 word) memc w N vp0 C,
  getr rX (Z_to_bv 5 10) = w64 w -> getr rX (Z_to_bv 5 11) = w64 (N - 1) ->
  getr rX (Z_to_bv 5 12) = w64 (2 ^ 64 - 1 - vp0) -> getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF ->
  4096 <= w <= 2 ^ 47 - 1 -> 2 <= N <= 512 -> 4096 <= vp0 <= 2 ^ 47 - 1 -> 0 <= C <= 255 ->
  rdW Wc memc w = Some C ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [Z_to_bv 64 C])) (b9s5a_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros pc Wc rX memc w N vp0 C H10 H11 H12 H20 Hw HN Hv HC HrdC.
set (E := Eimg (Ereg rX [Z_to_bv 64 C])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U10 : bv_unsigned (ew E 10) = w)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = N - 1)
  by (rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = 2 ^ 64 - 1 - vp0)
  by (rewrite (EE 12%nat (Z_to_bv 5 12) eq_refl), H12; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SB)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), H20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF, SB; lia).
assert (E32 : ew E 32 = Z_to_bv 64 C)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U32 : bv_unsigned (ew E 32) = C) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b9s5a_ss. apply pa_entry_st_ok_full.
- unfold E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b9s5a_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  destruct (aview_byte SEGS (w_H Wc) memc w C HrdC) as (b & Hb & Hvb & _).
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r, (unsigned_lit_small C), (unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    rewrite Hvb. apply Z_to_bv_bv_unsigned.
  + rewrite !Z.add_0_r. exact Hb.
- cbn. tauto.
- split; [|split; exact I]. cbn [b9s5a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U11, U12, U20, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

(* the strip cut at the end of an arm run, from the cut's facts and the registers the run left *)
Lemma b9s5a_to_S : forall n q x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc',
  b9s5_Q B q n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r b9s5a_keep -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length (b9_v0 x ei)) - 1) ->
  (q = DQ \/ q = SQ) -> nth (length (b9_v0 x ei) - 1) (b9_v0 x ei) 0 = q ->
  b9s5_S B q n x ei kp vp0 lyc Sc Wc rX' memc' mdc'.
Proof.
intros n q x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' (HD & HL2 & Hq0 & HRG) HJ' KM KV QK Q10 Hq HqN.
pose proof (b9s5_D_rng B _ _ _ _ _ _ _ _ _ _ _ HD) as (_ & _ & _ & _ & _ & _ & _ & _).
pose proof HD as ((HB & _) & _).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
unfold B9_R, PF_RL, PF_RM in HRG.
assert (HFI' : pf_rg rX' (b9_FI B (y_v x))).
{ unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (b9_rg_get rX _ _ _ HFI); unfold b9_FI; b9s5a_in | unfold b9s5a_keep; b9s5a_in]). }
split; [exact (b9s5_D_move B n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HD HJ' KM KV HFI')|].
split; [exact HL2|]. split; [exact Hq|]. split; [exact Hq0|]. split; [exact HqN|].
unfold B9_R, PF_RL, PF_RM, pf_rg. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  first [ exact Q10
        | rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s5a_in | unfold b9s5a_keep; b9s5a_in] ].
Qed.

(* K5 at the end of an arm run: the value is v0 *)
Lemma b9s5a_to_K5 : forall n q x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc',
  b9s5_Q B q n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r b9s5a_keep -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  (q = DQ \/ q = SQ) -> nth (length (b9_v0 x ei) - 1) (b9_v0 x ei) 0 <> q ->
  INV_K5 B n x ei kp vp0 lyc Sc Wc rX' memc' mdc'.
Proof.
intros n q x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' (HD & HL2 & Hq0 & HRG) HJ' KM KV QK Hq HqN.
pose proof (b9s5_D_rng B _ _ _ _ _ _ _ _ _ _ _ HD) as (_ & _ & _ & _ & _ & _ & _ & HNZ).
pose proof HD as ((HB & _) & _).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
unfold B9_R, PF_RL, PF_RM in HRG.
apply (b9s5_k5_keep B n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HD HJ' KM KV).
- unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (b9_rg_get rX _ _ _ HFI); unfold b9_FI; b9s5a_in | unfold b9s5a_keep; b9s5a_in]).
- unfold B9_R, PF_RL, PF_RM, pf_rg. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s5a_in | unfold b9s5a_keep; b9s5a_in]).
- unfold b9_val. apply (b9_unq_keep (b9_v0 x ei) HNZ HL2).
  intros [[H1 H2] | [H1 H2]]; destruct Hq as [-> | ->]; congruence.
Qed.

(* the two arms: from the cut to the strip cut or to K5 *)
Section arm.
Variables (n : nat) (HK5 : from_K5 B n) (HS5 : from_S5 B n).

Lemma b9s5_dq_ok : from_Q5 B DQ B9S5_DQ n.
Proof.
intros x ei kp vp0 lyc Sc Wc rX memc mdc HQI.
pose proof HQI as (HD & HL2 & Hq0 & HRG).
pose proof (b9s5_D_rng B _ _ _ _ _ _ _ _ _ _ _ HD) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & HNZ).
pose proof HD as (HC & HCH & HKEY & HKLT & HV0).
pose proof HC as (HB & HM & HST & HL & HD0 & HDL).
destruct (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & (HJ & _) & _).
pose proof (b9_st_of_base B _ _ _ _ _ _ _ _ HB) as HST0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HV0 as [HSTR _].
pose proof HSTR as [[HZS _] _].
unfold b9_buf, PF_O_BUF in R1, R2, R4, R5.
pose proof HRG as HRG0.
unfold B9_R, PF_RL, PF_RM in HRG.
set (V := b9_v0 x ei) in *.
assert (Hw0 : 4096 <= vp0 + Z.of_nat (length V) - 1 <= 2 ^ 47 - 1) by lia.
(* the last byte of v0 *)
set (C := nth (length V - 1) V 0).
assert (VC : rdW Wc memc (vp0 + Z.of_nat (length V) - 1) = Some C).
{ replace (vp0 + Z.of_nat (length V) - 1) with (vp0 + Z.of_nat (length V - 1)) by lia.
  rewrite (HZS (length V - 1)%nat) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia. reflexivity. }
assert (HC0 : 0 <= C <= 255) by (destruct (aview_byte SEGS (w_H Wc) memc _ C VC) as (_ & _ & _ & Hr); lia).
(* the registers at the arm *)
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length V) - 1))
  by (apply (b9_rg_get rX _ 10 _ HRG); b9s5a_in).
assert (R11 : getr rX (Z_to_bv 5 11) = w64 (Z.of_nat (length V) - 1)) by (apply (b9_rg_get rX _ 11 _ HRG); b9s5a_in).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 (2 ^ 64 - 1 - vp0)) by (apply (b9_rg_get rX _ 12 _ HRG); b9s5a_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 vp0) by (apply (b9_rg_get rX _ 19 _ HRG); b9s5a_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b9_rg_get rX _ 20 _ HFI); unfold b9_FI; b9s5a_in).
(* the seed *)
pose proof (b9s5a_seed B9S5_DQ Wc rX memc (vp0 + Z.of_nat (length V) - 1) (Z.of_nat (length V)) vp0 C
  R10 R11 R12 R20 Hw0 ltac:(lia) ltac:(lia) HC0 VC) as HS.
set (E := Eimg (Ereg rX [Z_to_bv 64 C])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E10 : ew E 10 = Z_to_bv 64 (vp0 + Z.of_nat (length V) - 1))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length V) - 1)) by (rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl); exact R11).
assert (E19 : ew E 19 = Z_to_bv 64 vp0) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew E 32 = Z_to_bv 64 C)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
clearbody E.
(* the shadow entry of the byte: check B#11 *)
destruct (b9_addr_buf B _ _ _ _ _ _ _ (vp0 + Z.of_nat (length V) - 1) 1 HST0
  ltac:(unfold b9_bufp, PF_O_BUF; lia) ltac:(lia) ltac:(unfold b9_bufp, PF_O_BUF; lia)) as (_ & _ & _ & HRA & _).
assert (UB : U E b9s5a_Bx = SHADOW_OFF) by (unfold b9s5a_Bx; apply (U_atom E 20 _ E20); unfold SHADOW_OFF; lia).
assert (UW : U E (SOff 10 0) = vp0 + Z.of_nat (length V) - 1) by (apply (U_atom E 10 _ E10); lia).
assert (SHOK : sh_ok SEGS b9s5a_Bx b9s5a_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b9s5a_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E b9s5a_Bx 10%nat (vp0 + Z.of_nat (length V) - 1) 1
    (vp0 + Z.of_nat (length V) - 1) 0 1 HRA UB UW); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + B9S5_DQ)) with (Z_to_bv 64 (BASE + B9S5_DQ)).
(* 0x88480 .. 0x88498: check B#11, the byte, `beq a0,a3` (a3 = 34) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the last byte is DQ: 0x8854c the trap T15 (decided), 0x88550 add a0,s3,a1, the strip cut *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    pose proof (b9s5a_br_eq E1 32 C 34 true E32 ltac:(lia) ltac:(lia) Hc) as BC end.
  apply Z.eqb_eq in BC. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B9S5_ST.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv0 := with_vm_backing _ _ _) in *; clearbody mdv0.
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM1 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms0) a <> None)
    by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms) (ms_mem ms0) a HG (KV1 a Hv))).
  clear HFr HG HF.
  assert (QK : forall r, In r b9s5a_keep -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b9s5a_keep in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s5a_kept HS EE |]). destruct Hr. }
  prreg HS (Z_to_bv 5 10) Q10.
  assert (Q10' : getr (ms_regs ms0) (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length V) - 1)).
  { rewrite Q10, E19, E11, alu64_add_lit. unfold w64. f_equal. lia. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9S5_ST) rg mm mdx) end.
  apply (HS5 DQ x ei kp vp0 lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0).
  exact (b9s5a_to_S n DQ x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms0) (ms_mem ms0) mdv0 HQI HJ KM2 KV2 QK Q10'
    (or_introl eq_refl) BC).
- (* the last byte is not DQ: 0x8849c j K5, the value is v0 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    pose proof (b9s5a_br_eq E1 32 C 34 false E32 ltac:(lia) ltac:(lia) Hc) as BC end.
  apply Z.eqb_neq in BC. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B9_K5.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv0 := with_vm_backing _ _ _) in *; clearbody mdv0.
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM1 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms0) a <> None)
    by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms) (ms_mem ms0) a HG (KV1 a Hv))).
  clear HFr HG HF.
  assert (QK : forall r, In r b9s5a_keep -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b9s5a_keep in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s5a_kept HS EE |]). destruct Hr. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9_K5) rg mm mdx) end.
  apply (HK5 x ei kp vp0 lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0).
  exact (b9s5a_to_K5 n DQ x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms0) (ms_mem ms0) mdv0 HQI HJ KM2 KV2 QK
    (or_introl eq_refl) BC).
Qed.

Lemma b9s5_sq_ok : from_Q5 B SQ B9S5_SQ n.
Proof.
intros x ei kp vp0 lyc Sc Wc rX memc mdc HQI.
pose proof HQI as (HD & HL2 & Hq0 & HRG).
pose proof (b9s5_D_rng B _ _ _ _ _ _ _ _ _ _ _ HD) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & HNZ).
pose proof HD as (HC & HCH & HKEY & HKLT & HV0).
pose proof HC as (HB & HM & HST & HL & HD0 & HDL).
destruct (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & (HJ & _) & _).
pose proof (b9_st_of_base B _ _ _ _ _ _ _ _ HB) as HST0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HV0 as [HSTR _].
pose proof HSTR as [[HZS _] _].
unfold b9_buf, PF_O_BUF in R1, R2, R4, R5.
unfold B9_R, PF_RL, PF_RM in HRG.
set (V := b9_v0 x ei) in *.
assert (Hw0 : 4096 <= vp0 + Z.of_nat (length V) - 1 <= 2 ^ 47 - 1) by lia.
set (C := nth (length V - 1) V 0).
assert (VC : rdW Wc memc (vp0 + Z.of_nat (length V) - 1) = Some C).
{ replace (vp0 + Z.of_nat (length V) - 1) with (vp0 + Z.of_nat (length V - 1)) by lia.
  rewrite (HZS (length V - 1)%nat) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia. reflexivity. }
assert (HC0 : 0 <= C <= 255) by (destruct (aview_byte SEGS (w_H Wc) memc _ C VC) as (_ & _ & _ & Hr); lia).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length V) - 1))
  by (apply (b9_rg_get rX _ 10 _ HRG); b9s5a_in).
assert (R11 : getr rX (Z_to_bv 5 11) = w64 (Z.of_nat (length V) - 1)) by (apply (b9_rg_get rX _ 11 _ HRG); b9s5a_in).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 (2 ^ 64 - 1 - vp0)) by (apply (b9_rg_get rX _ 12 _ HRG); b9s5a_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 vp0) by (apply (b9_rg_get rX _ 19 _ HRG); b9s5a_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b9_rg_get rX _ 20 _ HFI); unfold b9_FI; b9s5a_in).
pose proof (b9s5a_seed B9S5_SQ Wc rX memc (vp0 + Z.of_nat (length V) - 1) (Z.of_nat (length V)) vp0 C
  R10 R11 R12 R20 Hw0 ltac:(lia) ltac:(lia) HC0 VC) as HS.
set (E := Eimg (Ereg rX [Z_to_bv 64 C])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E10 : ew E 10 = Z_to_bv 64 (vp0 + Z.of_nat (length V) - 1))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length V) - 1)) by (rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl); exact R11).
assert (E19 : ew E 19 = Z_to_bv 64 vp0) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew E 32 = Z_to_bv 64 C)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
clearbody E.
destruct (b9_addr_buf B _ _ _ _ _ _ _ (vp0 + Z.of_nat (length V) - 1) 1 HST0
  ltac:(unfold b9_bufp, PF_O_BUF; lia) ltac:(lia) ltac:(unfold b9_bufp, PF_O_BUF; lia)) as (_ & _ & _ & HRA & _).
assert (UB : U E b9s5a_Bx = SHADOW_OFF) by (unfold b9s5a_Bx; apply (U_atom E 20 _ E20); unfold SHADOW_OFF; lia).
assert (UW : U E (SOff 10 0) = vp0 + Z.of_nat (length V) - 1) by (apply (U_atom E 10 _ E10); lia).
assert (SHOK : sh_ok SEGS b9s5a_Bx b9s5a_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b9s5a_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E b9s5a_Bx 10%nat (vp0 + Z.of_nat (length V) - 1) 1
    (vp0 + Z.of_nat (length V) - 1) 0 1 HRA UB UW); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + B9S5_SQ)) with (Z_to_bv 64 (BASE + B9S5_SQ)).
(* 0x88530 .. 0x88548: check B#13, the byte, `bne a0,a3` (a3 = 39) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the last byte is not SQ: j K5, the value is v0 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    pose proof (b9s5a_br_ne E1 32 C 39 true E32 ltac:(lia) ltac:(lia) Hc) as BC end.
  apply Bool.negb_true_iff, Z.eqb_neq in BC. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B9_K5.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv0 := with_vm_backing _ _ _) in *; clearbody mdv0.
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM1 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms0) a <> None)
    by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms) (ms_mem ms0) a HG (KV1 a Hv))).
  clear HFr HG HF.
  assert (QK : forall r, In r b9s5a_keep -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b9s5a_keep in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s5a_kept HS EE |]). destruct Hr. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9_K5) rg mm mdx) end.
  apply (HK5 x ei kp vp0 lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0).
  exact (b9s5a_to_K5 n SQ x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms0) (ms_mem ms0) mdv0 HQI HJ KM2 KV2 QK
    (or_intror eq_refl) BC).
- (* the last byte is SQ: 0x8854c the trap T15 (decided), 0x88550 add a0,s3,a1, the strip cut *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    pose proof (b9s5a_br_ne E1 32 C 39 false E32 ltac:(lia) ltac:(lia) Hc) as BC end.
  apply Bool.negb_false_iff, Z.eqb_eq in BC. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B9S5_ST.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv0 := with_vm_backing _ _ _) in *; clearbody mdv0.
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM1 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms0) a <> None)
    by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms) (ms_mem ms0) a HG (KV1 a Hv))).
  clear HFr HG HF.
  assert (QK : forall r, In r b9s5a_keep -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b9s5a_keep in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s5a_kept HS EE |]). destruct Hr. }
  prreg HS (Z_to_bv 5 10) Q10.
  assert (Q10' : getr (ms_regs ms0) (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length V) - 1)).
  { rewrite Q10, E19, E11, alu64_add_lit. unfold w64. f_equal. lia. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9S5_ST) rg mm mdx) end.
  apply (HS5 SQ x ei kp vp0 lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0).
  exact (b9s5a_to_S n SQ x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms0) (ms_mem ms0) mdv0 HQI HJ KM2 KV2 QK Q10'
    (or_intror eq_refl) BC).
Qed.
End arm.

End x.
End d.
