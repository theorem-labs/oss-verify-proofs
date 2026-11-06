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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 774 of its 829 lines of code are new or changed and 398 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   piece L (the B5 segment lane, piece prover: a sub-lane, 2026-10-30): b5_lp_ok : H_C B n -> forall k, H_L B k n, the inlined
   strip_comment loop (reac_segconf.c:65-74) from its head L k 0x882f8 to C 0x88388.
   ADAPTED from the image-A G3 walk owner's image-A segment lane on a working branch (pf_a5_d.v's L k -> C; its R6 token run
   pf_a5_tl.v a5_r6_ok and its store at R4 pf_a5_r3.v a5_r4_ok are the templates of the token run and of the store)
   and image B's trim_l.v (a loop with an inline check, strong induction) / trim_f.v (a one-byte written region
   under a shadow entry), re-derived on image B's code; the cut rebuild follows the B5 segment lane's pf_seg_B5_r2.v.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), one iteration from L k (a0 = a1 = buf + k,
   a3 = -k, a6 = 1, a7 = ' ', t0 = '\t', t1 = ';', s2 = '#', s4 = SHADOW_OFF, s10 = -1):
     0x882f8 .. 0x88304  check B#4 on a1 = buf + k (load1; slow path 0x88358 .. 0x88360, error stub 0x8922c)
     0x88308 lbu a2,0(a0)  c = (line ++ [0])[k]
     0x8830c beq a2,s2 / 0x88310 beq a2,t1   '#' or ';' to 0x8831c
     0x88314 beqz a2       the NUL: to C 0x88388 (k = LEN, nothing to cut)
     0x88318 j 0x88344
     0x8831c beqz a3       k = 0: to 0x88370 `ld a0,208(s1)` (a0 = buf, slot 0xd0)
     0x88320 beq a0,a6     UBSan trap T08 (to the unimp 0x891c8): a0 = buf + k >= 4096 + 64, so a0 <> 1
     0x88324 .. 0x88334  check B#5 on a1 - 1 = buf + k - 1 (load1; slow path 0x88364 .. 0x8836c, error stub 0x89224)
     0x88338 lbu a2,-1(a0) p = line[k - 1]; 0x8833c beq a2,a7 / 0x88340 beq a2,t0   ' ' or '\t' to 0x88374
     0x88344 beq a0,s10    UBSan trap T09: a0 = buf + k < 2 ^ 47, so a0 <> 2 ^ 64 - 1
     0x88348 .. 0x88354  a0 += 1, a1 += 1, a3 -= 1, j 0x882f8 (L (k + 1))
     0x88374 .. 0x88380  check B#6 on a0 = buf + k (store1; slow path 0x88f6c .. 0x88f74, error stub 0x8925c)
     0x88384 sb zero,0(a0) the cut store buf[k] = 0, then C 0x88388.
   The proof: per iteration a fresh seed at L k (every register its own atom but the loop constants, which are
   pinned, and a1 = a0's atom 10; the one written region is buf + k on atom 10, with the bytes c (atom 32) and,
   for k > 0, p (atom 33) as its chunks, a read-only region on s1 = atom 9 holding slot 0xd0 for k = 0); the token
   executor (Bx = s4 = atom 20 = SHADOW_OFF) with the one shadow entry buf + k (- 1 for k > 0) .. buf + k + 1, which
   covers the three checks (sh_ok from b5_addr_buf; no open obligation); the executor decides T08, T09 and the
   k = 0 test from the seed's facts; the branches on c and p by psrr_branch_tok; the exits INV_L (k + 1)
   (b5lp_inv_next), INV_C at the NUL (b5lp_inv_c0) and INV_C after the cut store (b5lp_inv_cs, pfA_facts
   r_strip_comment_at); b5_lp_ok by strong induction on LEN - k (trim_l.v tr_lead_ok's form).
   36 instructions in 0x882f8 .. 0x88384 plus 3 in 0x88f6c .. 0x88f74; 36 of the 39 walked (the slow-path
   instructions inside the three check tokens; the three error-stub jumps 0x88360, 0x8836c, 0x88f74 are never
   reached); checks B#4, B#5, B#6 discharged; traps T08 0x88320 and T09 0x88344 discharged. Section hypotheses:
   none (the loop calls nothing). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
  PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B5_d pf_seg_B5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- words, lists, the comment test ---------- *)
Lemma b5lp_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma b5lp_w64_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. exact H. Qed.
Lemma b5lp_neg : forall k, Z_to_bv 64 (- k) = Z_to_bv 64 (2 ^ 64 - k).
Proof.
intros k. apply b5lp_w64_mod. replace (2 ^ 64 - k) with (- k + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma b5lp_nth_lt : forall (l : list Z) i, (i < length l)%nat -> nth i (l ++ [0]) 0 = nth i l 0.
Proof. intros l i H. apply app_nth1. exact H. Qed.
Lemma b5lp_klt : forall (l : list Z) k, (k <= length l)%nat -> nth k (l ++ [0]) 0 <> 0 -> (k < length l)%nat.
Proof.
intros l k Hk Hc. destruct (Nat.lt_ge_cases k (length l)) as [H|H]; [exact H|]. exfalso. apply Hc.
rewrite app_nth2 by lia. replace (k - length l)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma b5lp_keq : forall (l : list Z) k, ~ In 0 l -> (k <= length l)%nat -> nth k (l ++ [0]) 0 = 0 -> k = length l.
Proof.
intros l k Hn Hk Hc. destruct (Nat.lt_ge_cases k (length l)) as [H|H]; [|lia]. exfalso. apply Hn.
rewrite (app_nth1 l [0] 0 H) in Hc. rewrite <- Hc. apply nth_In. exact H.
Qed.
Lemma b5lp_cm_nomark : forall l k, is_mark (nth k l 0) = false -> r_comment_at l k = false.
Proof. intros l k H. unfold r_comment_at. rewrite H. reflexivity. Qed.
Lemma b5lp_cm_nosp : forall l k, (0 < k)%nat -> sp_tab (nth (k - 1) l 0) = false -> r_comment_at l k = false.
Proof.
intros l k Hk H. unfold r_comment_at. rewrite H. replace (k =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
cbn [orb]. apply andb_false_r.
Qed.
Lemma b5lp_cm_sp : forall l k, is_mark (nth k l 0) = true -> sp_tab (nth (k - 1) l 0) = true -> r_comment_at l k = true.
Proof. intros l k H1 H2. unfold r_comment_at. rewrite H1, H2, orb_true_r. reflexivity. Qed.
Lemma b5lp_cm_0 : forall l, is_mark (nth 0 l 0) = true -> r_comment_at l 0 = true.
Proof. intros l H. unfold r_comment_at. rewrite H. reflexivity. Qed.
Lemma b5lp_mark_nz : forall c, is_mark c = true -> c <> 0.
Proof. intros c H Hc. rewrite Hc in H. discriminate H. Qed.
Lemma b5lp_nomark : forall c, c <> 35 -> c <> 59 -> is_mark c = false.
Proof. intros c H1 H2. unfold is_mark. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity. Qed.
Lemma b5lp_nosp : forall c, c <> 32 -> c <> 9 -> sp_tab c = false.
Proof. intros c H1 H2. unfold sp_tab. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity. Qed.

(* ---------- the executor's terms ---------- *)
Lemma b5lp_beq : forall E n c z b, ew E n = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (c =? z) = b.
Proof. intros E n c z b Hn Hc Hz H. rewrite branch_eq_U, (U_atom E n c Hn Hc), U_lit in H by lia. exact H. Qed.
Lemma b5lp_ag_ew : forall E0 E (n : nat) v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v ->
  ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma b5lp_U : forall E0 E (n : nat) v, env_agree 34 E0 E -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E0 E n v H Hn H0 Hv. rewrite (b5lp_ag_ew E0 E n v H Hn H0). apply unsigned_lit_small. exact Hv. Qed.
Ltac b5lp_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b5lp_den :=
  cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?b5lp_w64_off, ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  unfold w64; first [ apply (f_equal (Z_to_bv 64)); lia
    | apply b5lp_w64_mod; match goal with H : ?kk = 0%nat |- context [?kk] => rewrite H end; vm_compute; reflexivity ].
Ltac b5lp_pins := first [ apply regs_ok_Eimg_Ereg
  | apply regs_ok_pin; [b5lp_pins | let Hx := fresh "Hx" in intros Hx; discriminate Hx | ] ].

(* ---------- the seeds at L k ---------- *)
(* every register its own atom, but a1 = a0's atom (the check address of B#4 and B#5) and the loop constants pinned:
   a6 = 1 (T08's operand), a7 = ' ', t0 = '\t', t1 = ';', s2 = '#', s10 = -1 (T09's operand) *)
Definition b5lp_regsS : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 11%bv (SOff 10 0)) 16%bv (SLit 1)) 17%bv (SLit 32))
    5%bv (SLit 9)) 6%bv (SLit 59)) 18%bv (SLit 35)) 26%bv (SLit (-1)).
(* k = 0: a3 = 0 too (0x8831c `beqz a3` decided) *)
Definition b5lp_regs0 : list sv := sr_set b5lp_regsS 13%bv (SLit 0).
(* k > 0: buf + k written (the cut store), its byte c (atom 32) and the byte before it p (atom 33) *)
Definition b5lp_regionsS : smem :=
  [ YP09.mkRegion (Some 10%nat) (-1) 1 0 1 [YP09.mkChunk (-1) (CVal 1 (SOff 33 0)); YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
(* k = 0: buf written at 0, its byte c; slot 0xd0 of s1 (= buf, read at 0x88370) *)
Definition b5lp_regions0 : smem :=
  [ YP09.mkRegion (Some 10%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 0xd0 0xd8 0 0 [YP09.mkChunk 0xd0 (CVal 8 (SOff 10 0))] ].
Definition b5lp_factsS : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0); (13%nat, mkAF (2 ^ 64 - 511) (2 ^ 64 - 1) 0);
            (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] [].
Definition b5lp_facts0 : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition b5lp_ssS : sstate := mkSS B5_L b5lp_regsS b5lp_regionsS None b5lp_factsS.
Definition b5lp_ss0 : sstate := mkSS B5_L b5lp_regs0 b5lp_regions0 None b5lp_facts0.
(* the token executor's shadow base s4 and its shadow entries (buf + k, and buf + k - 1 for k > 0) *)
Definition b5lp_Bx : sv := SOff 20 0.
Definition b5lp_SHS : list shent := [mkSHE 10 (-1) 1].
Definition b5lp_SH0 : list shent := [mkSHE 10 0 1].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition b5lp_ES (rX : bvmap 5 word) (c p : Z) : env := Eimg (Ereg rX [Z_to_bv 64 c; Z_to_bv 64 p]).
Definition b5lp_E0 (rX : bvmap 5 word) (c : Z) : env := Eimg (Ereg rX [Z_to_bv 64 c]).

(* a one-byte chunk whose value is an atom, from the byte the reader shows *)
Lemma b5lp_chunk1 : forall E (W : world SEGS) memc base off (n : nat) c,
  ew E n = Z_to_bv 64 c -> 0 <= c <= 255 -> rdW W memc (base + off) = Some c ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros E W memc base off n c Hn Hc Hrd.
unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
destruct (aview_byte SEGS (w_H W) memc _ c Hrd) as (b & Hb & Hv & _).
exists b. split.
- cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Hn.
  rewrite !Z.add_0_r, (unsigned_lit_small c), (unsigned_lit_small c) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
  subst c. apply Z_to_bv_bv_unsigned.
- rewrite Z.add_0_r. exact Hb.
Qed.
(* the byte a one-byte chunk of a region holds at the state the executor reached (pf_a5_r3.v r3_byte_of_region) *)
Lemma b5lp_byte_of_region : forall E H m n b lo hi wlo whi cs od e,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> aview SEGS H m (b + od) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E H m n b lo hi wlo whi cs od e HR Hb Hin.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 1 e HR Hb Hin
  ltac:(cbn; lia)) as V.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. change (N.to_nat 1) with 1%nat in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

Lemma b5lp_seedS : forall (Wc : world SEGS) (rX : bvmap 5 word) memc Xb Cv Pv (k : nat),
  getr rX 10%bv = w64 Xb -> getr rX 11%bv = w64 Xb -> getr rX 13%bv = w64 (- Z.of_nat k) ->
  getr rX 16%bv = w64 1 -> getr rX 17%bv = w64 32 -> getr rX 5%bv = w64 9 -> getr rX 6%bv = w64 59 ->
  getr rX 18%bv = w64 35 -> getr rX 26%bv = w64 (-1) -> getr rX 20%bv = w64 SB ->
  4097 <= Xb <= 2 ^ 47 - 1 -> (0 < k < 512)%nat -> 0 <= Cv <= 255 -> 0 <= Pv <= 255 ->
  rdW Wc memc Xb = Some Cv -> rdW Wc memc (Xb + -1) = Some Pv -> apresent (w_H Wc) memc Xb ->
  st_ok_pi SEGS VAL (b5lp_ES rX Cv Pv) b5lp_ssS
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B5_L)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc Xb Cv Pv k H10 H11 H13 H16 H17 H5 H6 H18 H26 H20 HX Hk HC HP VC VP HPR.
set (E := b5lp_ES rX Cv Pv).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hnn; subst E; unfold b5lp_ES; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (E10 : ew E 10 = Z_to_bv 64 Xb) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E13 : ew E 13 = Z_to_bv 64 (2 ^ 64 - Z.of_nat k)) by (rewrite (EE 13%nat 13%bv eq_refl), H13; apply b5lp_neg).
assert (E32 : ew E 32 = Z_to_bv 64 Cv)
  by (subst E; unfold b5lp_ES; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Pv)
  by (subst E; unfold b5lp_ES; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U10 : bv_unsigned (ew E 10) = Xb) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SB) by (rewrite E20; apply unsigned_lit_small; unfold SB; lia).
assert (U13 : bv_unsigned (ew E 13) = 2 ^ 64 - Z.of_nat k) by (rewrite E13; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = Cv) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = Pv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (P11 : getr rX 11%bv = sv_denot E (SOff 10 0)) by (rewrite b5_den_atom0, E10; exact H11).
rewrite restrict_mkst_fx. unfold b5lp_ssS. apply pa_entry_st_ok_full.
- unfold b5lp_regsS. b5lp_pins.
  all: first [exact P11 | exact H16 | exact H17 | exact H5 | exact H6 | exact H18 | exact H26].
- vm_compute. reflexivity.
- unfold b5lp_regionsS. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U10. split; [lia|]. split; [lia|]. split.
  + intros q Hq. replace (Xb + q) with Xb by lia. apply (apresent_writable SEGS). exact HPR.
  + constructor; [|constructor; [|constructor]].
    * exact (b5lp_chunk1 E Wc memc Xb (-1) 33 Pv E33 HP VP).
    * apply (b5lp_chunk1 E Wc memc Xb 0 32 Cv E32 HC). rewrite Z.add_0_r. exact VC.
- cbn. tauto.
- split; [|split; exact I].
  cbn [b5lp_factsS f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U20, U13, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Lemma b5lp_seed0 : forall (Wc : world SEGS) (rX : bvmap 5 word) memc Xb Cv S1,
  getr rX 10%bv = w64 Xb -> getr rX 11%bv = w64 Xb -> getr rX 13%bv = w64 0 ->
  getr rX 16%bv = w64 1 -> getr rX 17%bv = w64 32 -> getr rX 5%bv = w64 9 -> getr rX 6%bv = w64 59 ->
  getr rX 18%bv = w64 35 -> getr rX 26%bv = w64 (-1) -> getr rX 20%bv = w64 SB -> getr rX 9%bv = w64 S1 ->
  4096 <= Xb <= 2 ^ 47 - 1 -> 0 <= Cv <= 255 -> Xb + 1 <= S1 -> S1 + 0xd8 <= 2 ^ 64 ->
  rdW Wc memc Xb = Some Cv -> rdword (rdW Wc memc) (S1 + 0xd0) = Some Xb -> apresent (w_H Wc) memc Xb ->
  st_ok_pi SEGS VAL (b5lp_E0 rX Cv) b5lp_ss0
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B5_L)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc Xb Cv S1 H10 H11 H13 H16 H17 H5 H6 H18 H26 H20 H9 HX HC HS1 HS2 VC HSL HPR.
set (E := b5lp_E0 rX Cv).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr rX r)
  by (intros nn r Hnn; subst E; unfold b5lp_E0; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (E10 : ew E 10 = Z_to_bv 64 Xb) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E9 : ew E 9 = Z_to_bv 64 S1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 Cv)
  by (subst E; unfold b5lp_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U10 : bv_unsigned (ew E 10) = Xb) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = S1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SB) by (rewrite E20; apply unsigned_lit_small; unfold SB; lia).
assert (U32 : bv_unsigned (ew E 32) = Cv) by (rewrite E32; apply unsigned_lit_small; lia).
assert (P11 : getr rX 11%bv = sv_denot E (SOff 10 0)) by (rewrite b5_den_atom0, E10; exact H11).
rewrite restrict_mkst_fx. unfold b5lp_ss0. apply pa_entry_st_ok_full.
- unfold b5lp_regs0, b5lp_regsS. b5lp_pins.
  all: first [exact P11 | exact H13 | exact H16 | exact H17 | exact H5 | exact H6 | exact H18 | exact H26].
- vm_compute. reflexivity.
- unfold b5lp_regions0. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split.
    * intros q Hq. replace (Xb + q) with Xb by lia. apply (apresent_writable SEGS). exact HPR.
    * constructor; [|constructor].
      apply (b5lp_chunk1 E Wc memc Xb 0 32 Cv E32 HC). rewrite Z.add_0_r. exact VC.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ S1 0xd0 8 (SOff 10 0) Xb);
      [rewrite b5_den_atom0; exact E10 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HSL).
- unfold b5lp_regions0. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U10, U9. repeat split; lia.
- split; [|split; exact I].
  cbn [b5lp_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U20, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ======================= the cuts after an iteration ======================= *)
(* pf_base, the line's context and the loop's constant registers at a state that differs from L k's only at buf + k *)
Lemma b5lp_rebuild : forall n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc',
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> b5_buf v pos + Z.of_nat k -> rdW Wc memc' a = rdW Wc memc a) ->
  rdW Wc memc' (b5_buf v pos + Z.of_nat k) <> None ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 21; 22; 25] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 18) = w64 0x23 -> getr rX' (Z_to_bv 5 26) = w64 (-1) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE /\ b5_ln n v pos (rdW Wc memc') cf cur nm o ln d /\
  pf_rg rX' (PF_RL v pos ++ PF_RM v o ln).
Proof.
intros n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KMx VX0 QK Q18 Q26.
destruct HI as (HB & HLN & HL512 & HZS & HkL & HNC & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & (f0 & HS0) & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & _ & _ & HCH).
pose proof HGEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
destruct (b5_SHv v pos HGEO) as (ESH & SH1 & SH2 & SH3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EB : b5_buf v pos = pf_F v pos + 64) by reflexivity.
unfold PF_RL, PF_RM in HRG. cbn [app] in HRG.
assert (K : b5_kept v pos (rdW Wc memc) (rdW Wc memc')).
{ split.
  - intros a Ha Hn. apply KMx; [exact Ha|]. intros ->. apply Hn. unfold b5_Wr. right; left. lia.
  - intros a Ha Hv. destruct (Z.eq_dec a (b5_buf v pos + Z.of_nat k)) as [-> | Hne]; [exact VX0|].
    rewrite (KMx a Ha Hne). exact Hv. }
assert (HFI' : pf_rg rX' (b5_FI B v)).
{ unfold pf_rg, b5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b5_rg rX _ _ _ HRG0); b5_in | b5_in]). }
assert (HFSH' : pf_fsh (rdW Wc memc') (pf_SH v pos) PF_SC_LINE).
{ intros i Hi. rewrite KMx; [exact (HFSH i Hi) | lia | lia]. }
split; [|split].
- apply (b5_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc rX' memc' mdc' PF_SC_LINE HB HJ').
  + exists f0. rewrite HS0. rewrite b5_set_fs2. reflexivity.
  + apply Permutation_refl.
  + exact K.
  + exact HFI'.
  + exact HFSH'.
- destruct HLN as (HCTX & Ho & Hk & HST).
  split; [exact HCTX|]. split; [exact Ho|]. split; [exact Hk|].
  exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm _ HGEO HAR Hin EF K HCH HST).
- unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [exact Q18 | exact Q26 | rewrite QK; [apply (b5_rg rX _ _ _ HRG); b5_in | b5_in]].
Qed.

(* the plain step to L (k + 1): no comment starts at k *)
Lemma b5lp_inv_next : forall {n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc'},
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 21; 22; 25] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 18) = w64 0x23 -> getr rX' (Z_to_bv 5 26) = w64 (-1) ->
  getr rX' (Z_to_bv 5 10) = w64 (b5_buf v pos + Z.of_nat (S k)) ->
  getr rX' (Z_to_bv 5 11) = w64 (b5_buf v pos + Z.of_nat (S k)) ->
  getr rX' (Z_to_bv 5 13) = w64 (- Z.of_nat (S k)) -> getr rX' (Z_to_bv 5 16) = w64 1 ->
  getr rX' (Z_to_bv 5 17) = w64 0x20 -> getr rX' (Z_to_bv 5 5) = w64 9 -> getr rX' (Z_to_bv 5 6) = w64 0x3b ->
  (k < b5_len v o)%nat -> r_comment_at (pf_line (p_s v) o) k = false ->
  INV_L B (S k) n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d.
Proof.
intros n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM QK Q18 Q26 Q10 Q11 Q13 Q16 Q17 Q5 Q6
  Hk Hcm.
pose proof HI as (HB & _ & HL512 & HZS & HkL & HNC & _).
pose proof HB as (HCX & HFI & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & _).
pose proof HGEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EB : b5_buf v pos = pf_F v pos + 64) by reflexivity.
assert (VX0 : rdW Wc memc' (b5_buf v pos + Z.of_nat k) <> None).
{ rewrite KM by lia. rewrite (HZS k) by (rewrite length_app; cbn [length]; unfold b5_len in Hk; lia). discriminate. }
destruct (b5lp_rebuild n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ'
  (fun a Ha _ => KM a Ha) VX0 QK Q18 Q26) as (HB' & HLN' & HRL').
split; [exact HB'|]. split; [exact HLN'|]. split; [exact HL512|]. split.
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. unfold b5_len in HL512.
  rewrite KM by lia. apply HZS. rewrite length_app. cbn [length]. lia. }
split; [lia|]. split.
{ intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hne]; [exact Hcm | apply HNC; lia]. }
apply (proj2 (b5_rg_app _ _ _)). apply (proj1 (b5_rg_app _ _ _)) in HRL'. destruct HRL' as [HRL HRM].
split; [exact HRL|]. apply (proj2 (b5_rg_app _ _ _)). split; [exact HRM|].
unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption.
Qed.

(* C at the line's NUL: k = LEN, nothing to cut *)
Lemma b5lp_inv_c0 : forall {n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc'},
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 21; 22; 25] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 18) = w64 0x23 -> getr rX' (Z_to_bv 5 26) = w64 (-1) ->
  k = b5_len v o ->
  INV_C B n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d.
Proof.
intros n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KM QK Q18 Q26 Hk.
pose proof HI as (HB & _ & HL512 & HZS & HkL & HNC & _).
pose proof HB as (HCX & HFI & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & _).
pose proof HGEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & _).
destruct (L_line_bytes_holds (p_s v) o NUL) as (_ & LNUL & _).
assert (EB : b5_buf v pos = pf_F v pos + 64) by reflexivity.
assert (VX0 : rdW Wc memc' (b5_buf v pos + Z.of_nat k) <> None).
{ rewrite KM by lia. rewrite (HZS k) by (rewrite length_app; cbn [length]; unfold b5_len in Hk; lia). discriminate. }
destruct (b5lp_rebuild n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ'
  (fun a Ha _ => KM a Ha) VX0 QK Q18 Q26) as (HB' & HLN' & HRL').
assert (HSC : r_strip_comment (pf_line (p_s v) o) = pf_line (p_s v) o).
{ unfold b5_len in Hk. rewrite (r_strip_comment_at (pf_line (p_s v) o) k LNUL ltac:(lia) HNC
    (fun H => ltac:(exfalso; lia))).
  rewrite Hk. apply firstn_all. }
split; [exact HB'|]. split; [exact HLN'|]. split; [exact HL512|]. split; [|exact HRL'].
rewrite HSC. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. unfold b5_len in HL512.
rewrite KM by lia. apply HZS. rewrite length_app. cbn [length]. lia.
Qed.

(* C after the cut store buf[k] = 0 (0x88384): a comment starts at k *)
Lemma b5lp_inv_cs : forall {n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc'},
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> b5_buf v pos + Z.of_nat k -> rdW Wc memc' a = rdW Wc memc a) ->
  rdW Wc memc' (b5_buf v pos + Z.of_nat k) = Some 0 ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 21; 22; 25] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 18) = w64 0x23 -> getr rX' (Z_to_bv 5 26) = w64 (-1) ->
  (k < b5_len v o)%nat -> r_comment_at (pf_line (p_s v) o) k = true ->
  INV_C B n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d.
Proof.
intros n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ' KMx VX QK Q18 Q26 Hk Hcm.
pose proof HI as (HB & _ & HL512 & HZS & HkL & HNC & _).
pose proof HB as (HCX & HFI & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & _).
pose proof HGEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & _).
destruct (L_line_bytes_holds (p_s v) o NUL) as (_ & LNUL & _).
assert (EB : b5_buf v pos = pf_F v pos + 64) by reflexivity.
destruct (b5lp_rebuild n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d rX' memc' mdc' HI HJ'
  KMx ltac:(rewrite VX; discriminate) QK Q18 Q26) as (HB' & HLN' & HRL').
assert (HSC : r_strip_comment (pf_line (p_s v) o) = firstn k (pf_line (p_s v) o)).
{ unfold b5_len in Hk. exact (r_strip_comment_at (pf_line (p_s v) o) k LNUL ltac:(lia) HNC (fun _ => Hcm)). }
split; [exact HB'|]. split; [exact HLN'|]. split; [exact HL512|]. split; [|exact HRL'].
rewrite HSC. unfold b5_len in Hk, HL512.
assert (Hfl : length (firstn k (pf_line (p_s v) o)) = k) by (rewrite length_firstn; lia).
intros i Hi. rewrite length_app, Hfl in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i k) as [Hik | Hik].
- rewrite (app_nth1 _ _ _ ltac:(rewrite Hfl; exact Hik)), nth_firstn.
  replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hik).
  rewrite KMx by lia. rewrite (HZS i) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia. reflexivity.
- assert (i = k) as -> by lia. rewrite app_nth2 by (rewrite Hfl; lia). rewrite Hfl, Nat.sub_diag. exact VX.
Qed.

(* ======================= the iteration ======================= *)
(* after a token run that writes at most buf + k: the environment agrees with E0 below 34 (HAE), every byte but
   buf + k is memc's (KM), every byte present in memc is present (KP) (pf_a5_tl.v tl_after with a written byte) *)
Ltac b5lp_after E0 HAE KM KP Xb M0 E10 Wc :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> a <> Xb -> aview SEGS (w_H Wc) (ms_mem msn) a = aview SEGS (w_H Wc) M0 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in intros a Ha Hne;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun a' => a' = Xb) HFr);
          [ exact (KM a Ha Hne)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
                    [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
                     first [lia | rewrite (b5lp_U E0 Eo 10%nat Xb HAE ltac:(lia) E10 ltac:(lia)) in Hrr; lia] |]);
            destruct Hin
          | exact Ha | exact Hne ]);
    assert (KPn : forall a, apresent (w_H Wc) M0 a -> apresent (w_H Wc) (ms_mem msn) a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
(* the written region on atom 10 (buf + k) is in the owned class-5 frame (awr_byte's in_frames clause) *)
Ltac b5lp_awr HAE E10 Xb EF pos :=
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  eapply awr_ok_cons_gen with (n := 10%nat) (b := Xb);
  [ reflexivity
  | exact (b5lp_U _ _ 10%nat Xb HAE ltac:(lia) E10 ltac:(lia))
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    right; right; right; left; exists 5, pos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    rewrite EF; change (fs_frame_bytes 5) with 2048; lia
  | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ].
(* the region of buf + k at the state the executor reached *)
Ltac b5lp_rb0 HR0 :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) |- _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end;
  cbn [ms_mem restrict] in HR0.
(* buf + k still holds c (no store) *)
Ltac b5lp_rbC VX Xb Cv HAE E10 E32 :=
  let HR0 := fresh "HR0" in b5lp_rb0 HR0;
  lazymatch type of HR0 with region_ok _ ?Ex (mrestrict ?Hh _) _ =>
  pose proof (b5lp_byte_of_region Ex Hh _ 10%nat Xb _ _ _ _ _ 0 (SOff 32 0) HR0
    (b5lp_U _ Ex 10%nat Xb HAE ltac:(lia) E10 ltac:(lia)) ltac:(cbn [In]; repeat first [left; reflexivity | right]))
    as VX;
  rewrite Z.add_0_r, b5_den_atom0, (b5lp_ag_ew _ Ex 32%nat Cv HAE ltac:(lia) E32), unsigned_lit_small, Z.mod_small
    in VX by lia;
  clear HR0 end.
(* buf + k holds 0 (the cut store) *)
Ltac b5lp_rbZ VX Xb HAE E10 :=
  let HR0 := fresh "HR0" in b5lp_rb0 HR0;
  lazymatch type of HR0 with region_ok _ ?Ex (mrestrict ?Hh _) _ =>
  pose proof (b5lp_byte_of_region Ex Hh _ 10%nat Xb _ _ _ _ _ 0 (SLit 0) HR0
    (b5lp_U _ Ex 10%nat Xb HAE ltac:(lia) E10 ltac:(lia)) ltac:(cbn [In]; repeat first [left; reflexivity | right]))
    as VX;
  rewrite Z.add_0_r in VX; cbn [sv_denot] in VX; rewrite unsigned_lit_small in VX by lia; rewrite Zmod_0_l in VX;
  clear HR0 end.
(* the seed's atoms below 32 at the state the executor reached *)
Ltac b5lp_EEn EEn rX HAE EE :=
  lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ _) |- _ =>
  assert (EEn : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew En kk = getr rX r)
    by (let kk := fresh "kk" in let r := fresh "r" in let Hkk := fresh "Hkk" in let Hr5 := fresh "Hr5" in
        intros kk r Hkk; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite (proj1 HAE kk) by lia; exact (EE kk r Hkk))
  end.
(* a register goal at the state the executor reached: a pinned constant, a stepped atom, or the kept atoms *)
Ltac b5lp_regs HS EEn :=
  first [ b5lp_rreg HS; b5lp_den
        | let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
          repeat (destruct Hr as [<- | Hr]; [b5lp_rreg HS; rewrite b5_den_atom0; apply EEn; reflexivity |]); destruct Hr ].
Ltac b5lp_cfg pc :=
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx) with (cfg_at SEGS (BASE + pc) rg mm mdx) end.
(* exit to L (k + 1), no store *)
Ltac b5lp_fin_L Hk1 Hcm Xb Cv rX HAE EE E10 E13 E32 VC KM HI HJ HNX :=
  lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ ?msR) |- _ =>
  let E10n := fresh "E10n" in let E13n := fresh "E13n" in let EEn := fresh "EEn" in let VX := fresh "VX" in
  pose proof (b5lp_ag_ew _ _ 10%nat Xb HAE ltac:(lia) E10) as E10n;
  pose proof (b5lp_ag_ew _ _ 13%nat _ HAE ltac:(lia) E13) as E13n;
  b5lp_EEn EEn rX HAE EE;
  b5lp_rbC VX Xb Cv HAE E10 E32;
  pmkst HS; b5lp_cfg B5_L; apply HNX;
  eapply b5lp_inv_next;
  [ exact HI | exact HJ
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in intros a Ha;
    destruct (Z.eq_dec a Xb) as [-> | Hne]; [rewrite VX; symmetry; exact VC | exact (KM a Ha Hne)]
  | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn
  | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn
  | exact Hk1 | exact Hcm ]
  end.
(* exit to C at the NUL, no store *)
Ltac b5lp_fin_C0 HkE Xb Cv rX HAE EE E10 E32 VC KM HI HJ HC :=
  lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ ?msR) |- _ =>
  let EEn := fresh "EEn" in let VX := fresh "VX" in
  b5lp_EEn EEn rX HAE EE;
  b5lp_rbC VX Xb Cv HAE E10 E32;
  pmkst HS; b5lp_cfg B5_C; eapply HC;
  eapply b5lp_inv_c0;
  [ exact HI | exact HJ
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in intros a Ha;
    destruct (Z.eq_dec a Xb) as [-> | Hne]; [rewrite VX; symmetry; exact VC | exact (KM a Ha Hne)]
  | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn
  | exact HkE ]
  end.
(* exit to C after the cut store *)
Ltac b5lp_fin_Cs Hk1 Hcm Xb rX HAE EE E10 EX KM HI HJ HC :=
  lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ ?msR) |- _ =>
  let EEn := fresh "EEn" in let VX := fresh "VX" in
  b5lp_EEn EEn rX HAE EE;
  b5lp_rbZ VX Xb HAE E10;
  rewrite EX in KM, VX;
  pmkst HS; b5lp_cfg B5_C; eapply HC;
  eapply b5lp_inv_cs;
  [ exact HI | exact HJ | exact KM | exact VX
  | b5lp_regs HS EEn | b5lp_regs HS EEn | b5lp_regs HS EEn
  | exact Hk1 | exact Hcm ]
  end.
Ltac b5lp_brC z H Cv HAE E32 :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
  pose proof (b5lp_beq _ 32%nat Cv z _ (b5lp_ag_ew _ _ 32%nat Cv HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as H;
  clear Hc end.
Ltac b5lp_brP z H Pv HAE E33 :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
  pose proof (b5lp_beq _ 33%nat Pv z _ (b5lp_ag_ew _ _ 33%nat Pv HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as H;
  clear Hc end.

Lemma b5lp_walkS : forall n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  H_C B n -> (0 < k)%nat ->
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  (forall rX' memc' mdc', INV_L B (S k) n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d ->
     SRr SEGS Wc (cfg_at SEGS (BASE + B5_L) rX' memc' mdc') (b5_post B v cf cur nm o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_L) rX memc mdc) (b5_post B v cf cur nm o ln).
Proof.
intros n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HC Hk0 HI HNX. unfold H_C in HC.
pose proof HI as (HB & HLN & HL512 & HZS & HkL & HNC & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & _).
pose proof HGEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (L_line_bytes_holds (p_s v) o NUL) as (_ & LNUL & _).
assert (EB : b5_buf v pos = pf_F v pos + 64) by reflexivity.
unfold PF_RL, PF_RM in HRG. cbn [app] in HRG.
pose (Xb := b5_buf v pos + Z.of_nat k).
assert (EX : Xb = b5_buf v pos + Z.of_nat k) by reflexivity. clearbody Xb.
pose (Cv := nth k (pf_line (p_s v) o ++ [0]) 0).
assert (EC : Cv = nth k (pf_line (p_s v) o ++ [0]) 0) by reflexivity. clearbody Cv.
pose (Pv := nth (k - 1) (pf_line (p_s v) o ++ [0]) 0).
assert (EP : Pv = nth (k - 1) (pf_line (p_s v) o ++ [0]) 0) by reflexivity. clearbody Pv.
assert (VC : rdW Wc memc Xb = Some Cv)
  by (rewrite EX, EC; apply HZS; rewrite length_app; cbn [length]; unfold b5_len in HkL; lia).
assert (VP : rdW Wc memc (Xb + -1) = Some Pv).
{ replace (Xb + -1) with (b5_buf v pos + Z.of_nat (k - 1)) by lia. rewrite EP. apply HZS.
  rewrite length_app. cbn [length]. unfold b5_len in HkL. lia. }
destruct (aview_byte SEGS (w_H Wc) memc _ _ VC) as (_ & _ & _ & HCr).
destruct (aview_byte SEGS (w_H Wc) memc _ _ VP) as (_ & _ & _ & HPr).
assert (HXr : 4096 + 64 <= Xb /\ Xb + 1 <= pf_F v pos + 2048 /\ pf_F v pos + 2048 <= alloc_ceiling) by lia.
assert (HPR : apresent (w_H Wc) memc Xb).
{ apply (apresent_of_aview SEGS); [lia | | rewrite VC; discriminate].
  intros Himg. destruct (b5_out_inimg v pos HGEO Xb Himg) as (_ & _ & Hn). apply Hn. lia. }
assert (R10 : getr rX 10%bv = w64 Xb) by (rewrite EX; apply (b5_rg_bv rX _ 10 _ 10%bv HRG); [b5_in | reflexivity]).
assert (R11 : getr rX 11%bv = w64 Xb) by (rewrite EX; apply (b5_rg_bv rX _ 11 _ 11%bv HRG); [b5_in | reflexivity]).
assert (R13 : getr rX 13%bv = w64 (- Z.of_nat k)) by (apply (b5_rg_bv rX _ 13 _ 13%bv HRG); [b5_in | reflexivity]).
assert (R16 : getr rX 16%bv = w64 1) by (apply (b5_rg_bv rX _ 16 _ 16%bv HRG); [b5_in | reflexivity]).
assert (R17 : getr rX 17%bv = w64 32) by (apply (b5_rg_bv rX _ 17 _ 17%bv HRG); [b5_in | reflexivity]).
assert (R5 : getr rX 5%bv = w64 9) by (apply (b5_rg_bv rX _ 5 _ 5%bv HRG); [b5_in | reflexivity]).
assert (R6 : getr rX 6%bv = w64 59) by (apply (b5_rg_bv rX _ 6 _ 6%bv HRG); [b5_in | reflexivity]).
assert (R18 : getr rX 18%bv = w64 35) by (apply (b5_rg_bv rX _ 18 _ 18%bv HRG); [b5_in | reflexivity]).
assert (R26 : getr rX 26%bv = w64 (-1)) by (apply (b5_rg_bv rX _ 26 _ 26%bv HRG); [b5_in | reflexivity]).
assert (R20 : getr rX 20%bv = w64 SB)
  by (rewrite SB_SHADOW_OFF; apply (b5_rg_bv rX _ 20 _ 20%bv HRG0); [b5_in | reflexivity]).
(* the seed *)
pose proof (b5lp_seedS Wc rX memc Xb Cv Pv k R10 R11 R13 R16 R17 R5 R6 R18 R26 R20 ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) VC VP HPR) as HS.
assert (HEI : img_env VAL A_LIM (b5lp_ES rX Cv Pv)) by (unfold b5lp_ES; apply Eimg_env).
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew (b5lp_ES rX Cv Pv) kk = getr rX r)
  by (intros kk r Hkk; unfold b5lp_ES; apply ew_Eimg_Ereg_nat; exact Hkk).
assert (E10 : ew (b5lp_ES rX Cv Pv) 10 = Z_to_bv 64 Xb) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E13 : ew (b5lp_ES rX Cv Pv) 13 = Z_to_bv 64 (- Z.of_nat k)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E20 : ew (b5lp_ES rX Cv Pv) 20 = Z_to_bv 64 SB) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E32 : ew (b5lp_ES rX Cv Pv) 32 = Z_to_bv 64 Cv)
  by (unfold b5lp_ES; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (b5lp_ES rX Cv Pv) 33 = Z_to_bv 64 Pv)
  by (unfold b5lp_ES; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
revert HS HEI EE E10 E13 E20 E32 E33. generalize (b5lp_ES rX Cv Pv) as E0.
intros E0 HS HEI EE E10 E13 E20 E32 E33.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> Xb -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).
assert (UB : U E0 b5lp_Bx = SHADOW_OFF) by (unfold b5lp_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
assert (UX : U E0 (SOff 10 0) = Xb) by (apply (U_atom E0 10 Xb E10); lia).
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (Xb - 1) 2).
{ destruct (b5_addr_buf B v pos lyc Sc Wc rX memc mdc (Xb - 1) 2 HB ltac:(lia) ltac:(lia) ltac:(unfold b5_len in *; lia))
    as (_ & _ & _ & HRA & _). exact HRA. }
assert (SHOK : sh_ok SEGS b5lp_Bx b5lp_SHS E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b5lp_SHS. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b5lp_Bx 10%nat (Xb - 1) 2 Xb (-1) 1 HRA UB UX); [lia | lia |].
  intros x Hx. change (Z.min (-1) 1) with (-1) in Hx. change (Z.max (-1) 1) with 1 in Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + B5_L)) with (Z_to_bv 64 (BASE + B5_L)).
(* 0x882f8 .. 0x8830c: check B#4, c, up to `beq a2,s2` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b5lp_awr HAE E10 Xb EF pos. }
b5lp_after E0 HAE KM KP Xb memc E10 Wc.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* c = '#': 0x8831c .. (T08, check B#5, p) *)
  b5lp_brC 35 HC1 Cv HAE E32. apply Z.eqb_eq in HC1.
  assert (HM : is_mark Cv = true) by (rewrite HC1; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
  b5lp_after E0 HAE KM KP Xb memc E10 Wc.
  assert (Hk1 : (k < b5_len v o)%nat)
    by (apply (b5lp_klt (pf_line (p_s v) o) k HkL); rewrite <- EC; exact (b5lp_mark_nz Cv HM)).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { (* p = ' ': check B#6, the cut store, C *)
    b5lp_brP 32 HP1 Pv HAE E33. apply Z.eqb_eq in HP1.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    assert (Hcm : r_comment_at (pf_line (p_s v) o) k = true).
    { apply b5lp_cm_sp; [rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) k Hk1), <- EC; exact HM |].
      rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) (k - 1) ltac:(unfold b5_len in Hk1; lia)), <- EP, HP1. reflexivity. }
    b5lp_fin_Cs Hk1 Hcm Xb rX HAE EE E10 EX KM HI HJ HC. }
  b5lp_brP 32 HP1 Pv HAE E33. apply Z.eqb_neq in HP1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
  b5lp_after E0 HAE KM KP Xb memc E10 Wc.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { (* p = '\t': check B#6, the cut store, C *)
    b5lp_brP 9 HP2 Pv HAE E33. apply Z.eqb_eq in HP2.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    assert (Hcm : r_comment_at (pf_line (p_s v) o) k = true).
    { apply b5lp_cm_sp; [rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) k Hk1), <- EC; exact HM |].
      rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) (k - 1) ltac:(unfold b5_len in Hk1; lia)), <- EP, HP2. reflexivity. }
    b5lp_fin_Cs Hk1 Hcm Xb rX HAE EE E10 EX KM HI HJ HC. }
  (* p not blank: T09, the step, L (k + 1) *)
  b5lp_brP 9 HP2 Pv HAE E33. apply Z.eqb_neq in HP2.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
  b5lp_after E0 HAE KM KP Xb memc E10 Wc.
  assert (Hcm : r_comment_at (pf_line (p_s v) o) k = false).
  { apply b5lp_cm_nosp; [exact Hk0 |].
    rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) (k - 1) ltac:(unfold b5_len in Hk1; lia)), <- EP.
    exact (b5lp_nosp Pv HP1 HP2). }
  b5lp_fin_L Hk1 Hcm Xb Cv rX HAE EE E10 E13 E32 VC KM HI HJ HNX.
- b5lp_brC 35 HC1 Cv HAE E32. apply Z.eqb_neq in HC1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
  b5lp_after E0 HAE KM KP Xb memc E10 Wc.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* c = ';' *)
    b5lp_brC 59 HC2 Cv HAE E32. apply Z.eqb_eq in HC2.
    assert (HM : is_mark Cv = true) by (rewrite HC2; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    assert (Hk1 : (k < b5_len v o)%nat)
      by (apply (b5lp_klt (pf_line (p_s v) o) k HkL); rewrite <- EC; exact (b5lp_mark_nz Cv HM)).
    psrr_branch_tok RUN BR HS SHOK Bspan.
    { b5lp_brP 32 HP1 Pv HAE E33. apply Z.eqb_eq in HP1.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
      b5lp_after E0 HAE KM KP Xb memc E10 Wc.
      assert (Hcm : r_comment_at (pf_line (p_s v) o) k = true).
      { apply b5lp_cm_sp; [rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) k Hk1), <- EC; exact HM |].
        rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) (k - 1) ltac:(unfold b5_len in Hk1; lia)), <- EP, HP1. reflexivity. }
      b5lp_fin_Cs Hk1 Hcm Xb rX HAE EE E10 EX KM HI HJ HC. }
    b5lp_brP 32 HP1 Pv HAE E33. apply Z.eqb_neq in HP1.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    { b5lp_brP 9 HP2 Pv HAE E33. apply Z.eqb_eq in HP2.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
      b5lp_after E0 HAE KM KP Xb memc E10 Wc.
      assert (Hcm : r_comment_at (pf_line (p_s v) o) k = true).
      { apply b5lp_cm_sp; [rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) k Hk1), <- EC; exact HM |].
        rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) (k - 1) ltac:(unfold b5_len in Hk1; lia)), <- EP, HP2. reflexivity. }
      b5lp_fin_Cs Hk1 Hcm Xb rX HAE EE E10 EX KM HI HJ HC. }
    b5lp_brP 9 HP2 Pv HAE E33. apply Z.eqb_neq in HP2.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    assert (Hcm : r_comment_at (pf_line (p_s v) o) k = false).
    { apply b5lp_cm_nosp; [exact Hk0 |].
      rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) (k - 1) ltac:(unfold b5_len in Hk1; lia)), <- EP.
      exact (b5lp_nosp Pv HP1 HP2). }
    b5lp_fin_L Hk1 Hcm Xb Cv rX HAE EE E10 E13 E32 VC KM HI HJ HNX.
  + b5lp_brC 59 HC2 Cv HAE E32. apply Z.eqb_neq in HC2.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* c = 0: the line's NUL, k = LEN *)
      b5lp_brC 0 HC3 Cv HAE E32. apply Z.eqb_eq in HC3.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
      b5lp_after E0 HAE KM KP Xb memc E10 Wc.
      assert (HkE : k = b5_len v o) by (apply (b5lp_keq (pf_line (p_s v) o) k LNUL HkL); rewrite <- EC; exact HC3).
      b5lp_fin_C0 HkE Xb Cv rX HAE EE E10 E32 VC KM HI HJ HC.
    * (* another byte: T09, the step, L (k + 1) *)
      b5lp_brC 0 HC3 Cv HAE E32. apply Z.eqb_neq in HC3.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
      b5lp_after E0 HAE KM KP Xb memc E10 Wc.
      assert (Hk1 : (k < b5_len v o)%nat) by (apply (b5lp_klt (pf_line (p_s v) o) k HkL); rewrite <- EC; exact HC3).
      assert (Hcm : r_comment_at (pf_line (p_s v) o) k = false).
      { apply b5lp_cm_nomark. rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) k Hk1), <- EC. exact (b5lp_nomark Cv HC1 HC2). }
      b5lp_fin_L Hk1 Hcm Xb Cv rX HAE EE E10 E13 E32 VC KM HI HJ HNX.
Qed.

Lemma b5lp_walk0 : forall n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  H_C B n -> k = 0%nat ->
  INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  (forall rX' memc' mdc', INV_L B (S k) n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d ->
     SRr SEGS Wc (cfg_at SEGS (BASE + B5_L) rX' memc' mdc') (b5_post B v cf cur nm o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_L) rX memc mdc) (b5_post B v cf cur nm o ln).
Proof.
intros n k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HC Hk0 HI HNX. unfold H_C in HC.
pose proof HI as (HB & HLN & HL512 & HZS & HkL & HNC & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & _).
pose proof HGEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (L_line_bytes_holds (p_s v) o NUL) as (_ & LNUL & _).
assert (EB : b5_buf v pos = pf_F v pos + 64) by reflexivity.
unfold PF_RL, PF_RM in HRG. cbn [app] in HRG.
pose (Xb := b5_buf v pos + Z.of_nat k).
assert (EX : Xb = b5_buf v pos + Z.of_nat k) by reflexivity. clearbody Xb.
pose (Cv := nth k (pf_line (p_s v) o ++ [0]) 0).
assert (EC : Cv = nth k (pf_line (p_s v) o ++ [0]) 0) by reflexivity. clearbody Cv.
assert (VC : rdW Wc memc Xb = Some Cv)
  by (rewrite EX, EC; apply HZS; rewrite length_app; cbn [length]; unfold b5_len in HkL; lia).
destruct (aview_byte SEGS (w_H Wc) memc _ _ VC) as (_ & _ & _ & HCr).
assert (HXr : 4096 + 64 <= Xb /\ Xb + 1 <= pf_F v pos + 2048 /\ pf_F v pos + 2048 <= alloc_ceiling) by lia.
assert (HPR : apresent (w_H Wc) memc Xb).
{ apply (apresent_of_aview SEGS); [lia | | rewrite VC; discriminate].
  intros Himg. destruct (b5_out_inimg v pos HGEO Xb Himg) as (_ & _ & Hn). apply Hn. lia. }
assert (R10 : getr rX 10%bv = w64 Xb) by (rewrite EX; apply (b5_rg_bv rX _ 10 _ 10%bv HRG); [b5_in | reflexivity]).
assert (R11 : getr rX 11%bv = w64 Xb) by (rewrite EX; apply (b5_rg_bv rX _ 11 _ 11%bv HRG); [b5_in | reflexivity]).
assert (R13 : getr rX 13%bv = w64 (- Z.of_nat k)) by (apply (b5_rg_bv rX _ 13 _ 13%bv HRG); [b5_in | reflexivity]).
assert (R16 : getr rX 16%bv = w64 1) by (apply (b5_rg_bv rX _ 16 _ 16%bv HRG); [b5_in | reflexivity]).
assert (R17 : getr rX 17%bv = w64 32) by (apply (b5_rg_bv rX _ 17 _ 17%bv HRG); [b5_in | reflexivity]).
assert (R5 : getr rX 5%bv = w64 9) by (apply (b5_rg_bv rX _ 5 _ 5%bv HRG); [b5_in | reflexivity]).
assert (R6 : getr rX 6%bv = w64 59) by (apply (b5_rg_bv rX _ 6 _ 6%bv HRG); [b5_in | reflexivity]).
assert (R18 : getr rX 18%bv = w64 35) by (apply (b5_rg_bv rX _ 18 _ 18%bv HRG); [b5_in | reflexivity]).
assert (R26 : getr rX 26%bv = w64 (-1)) by (apply (b5_rg_bv rX _ 26 _ 26%bv HRG); [b5_in | reflexivity]).
assert (R20 : getr rX 20%bv = w64 SB)
  by (rewrite SB_SHADOW_OFF; apply (b5_rg_bv rX _ 20 _ 20%bv HRG0); [b5_in | reflexivity]).
assert (R9 : getr rX 9%bv = w64 (pf_s1 v)) by (apply (b5_rg_bv rX _ 9 _ 9%bv HRG0); [b5_in | reflexivity]).
unfold pf_sl in HSL.
assert (HSL0 : rdword (rdW Wc memc) (pf_s1 v + 0xd0) = Some Xb).
{ rewrite EX, Hk0. replace (b5_buf v pos + Z.of_nat 0) with (pf_F v pos + PF_O_BUF) by (unfold PF_O_BUF; lia).
  exact (proj1 (Forall_forall _ _) HSL (0xd0, pf_F v pos + PF_O_BUF)
    ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
assert (Hs1 : Xb + 1 <= pf_s1 v /\ pf_s1 v + 0xd8 <= 2 ^ 64) by lia.
(* the seed *)
pose proof (b5lp_seed0 Wc rX memc Xb Cv (pf_s1 v) R10 R11 ltac:(rewrite R13, Hk0; reflexivity) R16 R17 R5 R6 R18 R26
  R20 R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) VC HSL0 HPR) as HS.
assert (HEI : img_env VAL A_LIM (b5lp_E0 rX Cv)) by (unfold b5lp_E0; apply Eimg_env).
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew (b5lp_E0 rX Cv) kk = getr rX r)
  by (intros kk r Hkk; unfold b5lp_E0; apply ew_Eimg_Ereg_nat; exact Hkk).
assert (E10 : ew (b5lp_E0 rX Cv) 10 = Z_to_bv 64 Xb) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E13 : ew (b5lp_E0 rX Cv) 13 = Z_to_bv 64 (- Z.of_nat k)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E20 : ew (b5lp_E0 rX Cv) 20 = Z_to_bv 64 SB) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E32 : ew (b5lp_E0 rX Cv) 32 = Z_to_bv 64 Cv)
  by (unfold b5lp_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI EE E10 E13 E20 E32. generalize (b5lp_E0 rX Cv) as E0.
intros E0 HS HEI EE E10 E13 E20 E32.
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> Xb -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).
assert (UB : U E0 b5lp_Bx = SHADOW_OFF) by (unfold b5lp_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
assert (UX : U E0 (SOff 10 0) = Xb) by (apply (U_atom E0 10 Xb E10); lia).
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF Xb 1).
{ destruct (b5_addr_buf B v pos lyc Sc Wc rX memc mdc Xb 1 HB ltac:(lia) ltac:(lia) ltac:(unfold b5_len in *; lia))
    as (_ & _ & _ & HRA & _). exact HRA. }
assert (SHOK : sh_ok SEGS b5lp_Bx b5lp_SH0 E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b5lp_SH0. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b5lp_Bx 10%nat Xb 1 Xb 0 1 HRA UB UX); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + B5_L)) with (Z_to_bv 64 (BASE + B5_L)).
(* 0x882f8 .. 0x8830c: check B#4, c, up to `beq a2,s2` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b5lp_awr HAE E10 Xb EF pos. }
b5lp_after E0 HAE KM KP Xb memc E10 Wc.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* c = '#': k = 0 (0x8831c `beqz a3` taken), a0 = buf (0x88370), check B#6, the cut store *)
  b5lp_brC 35 HC1 Cv HAE E32. apply Z.eqb_eq in HC1.
  assert (HM : is_mark Cv = true) by (rewrite HC1; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
  b5lp_after E0 HAE KM KP Xb memc E10 Wc.
  assert (Hk1 : (k < b5_len v o)%nat)
    by (apply (b5lp_klt (pf_line (p_s v) o) k HkL); rewrite <- EC; exact (b5lp_mark_nz Cv HM)).
  assert (Hcm : r_comment_at (pf_line (p_s v) o) k = true).
  { rewrite Hk0 in Hk1, EC |- *. apply b5lp_cm_0. rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) 0 Hk1), <- EC. exact HM. }
  b5lp_fin_Cs Hk1 Hcm Xb rX HAE EE E10 EX KM HI HJ HC.
- b5lp_brC 35 HC1 Cv HAE E32. apply Z.eqb_neq in HC1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
  b5lp_after E0 HAE KM KP Xb memc E10 Wc.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* c = ';' *)
    b5lp_brC 59 HC2 Cv HAE E32. apply Z.eqb_eq in HC2.
    assert (HM : is_mark Cv = true) by (rewrite HC2; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    assert (Hk1 : (k < b5_len v o)%nat)
      by (apply (b5lp_klt (pf_line (p_s v) o) k HkL); rewrite <- EC; exact (b5lp_mark_nz Cv HM)).
    assert (Hcm : r_comment_at (pf_line (p_s v) o) k = true).
    { rewrite Hk0 in Hk1, EC |- *. apply b5lp_cm_0. rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) 0 Hk1), <- EC. exact HM. }
    b5lp_fin_Cs Hk1 Hcm Xb rX HAE EE E10 EX KM HI HJ HC.
  + b5lp_brC 59 HC2 Cv HAE E32. apply Z.eqb_neq in HC2.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
    b5lp_after E0 HAE KM KP Xb memc E10 Wc.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* c = 0: the empty line *)
      b5lp_brC 0 HC3 Cv HAE E32. apply Z.eqb_eq in HC3.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_C. { b5lp_awr HAE E10 Xb EF pos. }
      b5lp_after E0 HAE KM KP Xb memc E10 Wc.
      assert (HkE : k = b5_len v o) by (apply (b5lp_keq (pf_line (p_s v) o) k LNUL HkL); rewrite <- EC; exact HC3).
      b5lp_fin_C0 HkE Xb Cv rX HAE EE E10 E32 VC KM HI HJ HC.
    * (* another byte: T09, the step, L 1 *)
      b5lp_brC 0 HC3 Cv HAE E32. apply Z.eqb_neq in HC3.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_L. { b5lp_awr HAE E10 Xb EF pos. }
      b5lp_after E0 HAE KM KP Xb memc E10 Wc.
      assert (Hk1 : (k < b5_len v o)%nat) by (apply (b5lp_klt (pf_line (p_s v) o) k HkL); rewrite <- EC; exact HC3).
      assert (Hcm : r_comment_at (pf_line (p_s v) o) k = false).
      { apply b5lp_cm_nomark. rewrite <- (b5lp_nth_lt (pf_line (p_s v) o) k Hk1), <- EC. exact (b5lp_nomark Cv HC1 HC2). }
      b5lp_fin_L Hk1 Hcm Xb Cv rX HAE EE E10 E13 E32 VC KM HI HJ HNX.
Qed.

(* ======================= the loop, by strong induction on LEN - k ======================= *)
Definition b5lp_HLm (n m : nat) : Prop :=
  forall k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  (b5_len v o - k)%nat = m -> INV_L B k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_L) rX memc mdc) (b5_post B v cf cur nm o ln).

Lemma b5lp_step : forall n, H_C B n -> forall m, (forall m', (m' < m)%nat -> b5lp_HLm n m') -> b5lp_HLm n m.
Proof.
intros n HC m IH k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d Hm HI.
assert (NEXT : forall rX' memc' mdc', INV_L B (S k) n v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_L) rX' memc' mdc') (b5_post B v cf cur nm o ln)).
{ intros rX' memc' mdc' HI'. pose proof HI' as (_ & _ & _ & _ & Hk1 & _).
  apply (IH (b5_len v o - S k)%nat ltac:(lia) (S k) v pos lyc Sc Wc rX' memc' mdc' cf cur nm o ln d eq_refl HI'). }
destruct k as [|k'].
- exact (b5lp_walk0 n 0 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HC eq_refl HI NEXT).
- exact (b5lp_walkS n (S k') v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HC ltac:(lia) HI NEXT).
Qed.

Theorem b5_lp_ok : forall n, H_C B n -> forall k, H_L B k n.
Proof.
intros n HC.
assert (ALL : forall M m, (m <= M)%nat -> b5lp_HLm n m).
{ induction M as [|M IHM]; intros m Hm.
  - apply (b5lp_step n HC m). intros m' Hm'. lia.
  - apply (b5lp_step n HC m). intros m' Hm'. apply (IHM m'). lia. }
intros k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
exact (ALL _ _ (le_n _) k v pos lyc Sc Wc rX memc mdc cf cur nm o ln d eq_refl HI).
Qed.
End e.
End f.
End d.
