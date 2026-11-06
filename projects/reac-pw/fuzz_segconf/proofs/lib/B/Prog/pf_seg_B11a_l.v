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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10a_s.v, with its module paths, module names, addresses and numbers changed; 636 of its 805 lines of code are new or changed and 262 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B11a of reac_segconf_parse_file's
   walk, the CHK and LOOP cuts of lib/B/Prog/pf_seg_B11a_k.v. The B11a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, B11a's CHK and LOOP cuts)
   What it proves (both at every FP state):
     b11_loop_ok : (forall li, B11_ZST_stmt n li) -> forall li, B11_LOOP_stmt n li   (strong induction on 23 - li)
     b11_chk_ok  : (forall li, B11_LOOP_stmt n li) -> (forall li, B11_ZST_stmt n li) -> B11_CHK_stmt n
   The pcs it walks (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     CHK  0x886e0-0x88700 (9) and 0x889a8 (1): `ld a0,112(s1)` (val = slot 0x70), check B#18 (0x886e4-0x886f0, load1
          at val), `lbu a2,0(a0)`, `beqz a2` -> 0x889a8 `li a3,0` -> ZST (li = 0, val empty), else `li a6,0`,
          `addi a1,a0,1` -> LOOP (li = 0).
     LOOP 0x88704-0x88754 (21): `li a3,23; beq a6,a3` -> ZST (li = 23); a3 = val + li, a4 = slot 0x90 + li = model
          low + li, the ASCII fold, 0x88728 `sb a2,0(a4)` (low[li] = lower val[li]), 0x8872c T18 `beq a3,s10`, check
          B#19 (0x88730-0x88740, load1 at val + li + 1), `lbu a2,1(a3)`, li++, `mv a3,a6`, `beqz a2` -> ZST (li + 1),
          else `j` LOOP (li + 1).
   The slow arms 0x89010-0x89018 / error call 0x8929c (B#18) and 0x88758-0x88760 / 0x89244-0x89248 (B#19) are not
   reached: the token executor covers both checks with shadow entries.
   Checks and traps discharged:
     B#18 (load1 at vp): covered by the shadow entry mkSHE 32 0 1 on vp (atom 32), from range_addressable of buf
          (b11_ra_frame: scope PF_SC_L146 has sc_buf = true, cells 8 .. 0x47 are 0) narrowed to [vp, vp + |val| + 1)
          (pf_inb), and the frame lying off the shadow band (b11_G);
     B#19 (load1 at vp + li + 1): covered by mkSHE 32 1 2 on vp + li (alias atom 32), the same range (li + 1 <= |val|);
     the fold's store to model low + li: a writable one-byte region on the alias atom 34, its own SH entry
          mkSHE 34 0 1 from range_addressable of model low (cells 0x5c .. 0x5e are 0 in PF_SC_L146); the byte is an
          own-frame byte (awr_byte's in_frames case);
     T18 0x8872c `beq a3,s10` (a3 = vp + li, s10 pinned to SLit (2 ^ 64 - 1) from PF_RL's (26, -1)): decided not taken
          by the executor from atom 32's range fact [4096, 0x7fffff800000] (vp + li lies in buf, below alloc_ceiling).
   Section hypotheses: none.
   ADAPTED from a working branch + U piece walks; templates the B10a segment lane's role fold
   (its clone's lib/B/Prog/pf_seg_B10a_s.v seeds and entry lemmas, pf_seg_B10a_p.v P1, pf_seg_B10a_l.v
   LOOP, pf_seg_B10a_x.v run helpers, pf_seg_B10a_k.v b10_fold_arith), the B11a segment lane's pf_seg_B11a_m.v (the cut
   rebuilt on the B11a kit), lib/B/Prog/trim_l.v (the loop by strong induction). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11a_k pf_seg_B11a_g
  pf_seg_B11a_f.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seeds ---- *)
(* the range fact of a frame address: [4096, 0x7fffff800000] (4096 <= F, F + 2048 <= alloc_ceiling <= 0x7fffff800000) *)
Definition B11L_HI : Z := 0x7fffff800000.
Definition B11L_M1 : Z := 2 ^ 64 - 1.
Definition b11l_Bx : sv := SOff 20 0.
(* CHK, 0x886e0: s1's slot 0x70 holds vp (atom 32), the byte val[0] is atom 33; s4 = SB (atom 20); the shadow entry
   of val[0] covers check B#18 *)
Definition b11l_ss1 : sstate :=
  mkSS B11_CHK sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x70 0x78 0 0 [YP09.mkChunk 0x70 (CVal 8 (SOff 32 0))];
     YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
    (mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 B11L_HI 0); (33%nat, mkAF 0 255 0)] [] []).
Definition b11l_SH1 : list shent := [mkSHE 32 0 1].
(* LOOP, 0x88704: a0 = vp (atom 10), a1 = vp + 1 (atom 11), a6 = li (atom 16), a2 = val[li] (atom 12), s10 = -1
   (pinned); atom 32 = vp + li, 33 = model low (slot 0x90), 34 = model low + li (written), 35 = val[li + 1]; the
   aliases name the code's sums a0 + a6, a1 + a6, low + a6 by these atoms *)
Definition b11l_ss2 : sstate :=
  mkSS B11_LOOP (sr_set sr_atoms 26%bv (SLit B11L_M1))
    [YP09.mkRegion (Some 9%nat) 0x90 0x98 0 0 [YP09.mkChunk 0x90 (CVal 8 (SOff 33 0))];
     YP09.mkRegion (Some 32%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 35 0))];
     YP09.mkRegion (Some 34%nat) 0 1 0 1 []] None
    (mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 B11L_HI 0); (33%nat, mkAF 4096 B11L_HI 0);
              (34%nat, mkAF 4096 B11L_HI 0); (35%nat, mkAF 0 255 0)] []
       [(SAlu ALU_ADD (SOff 10 0) (SOff 16 0), SOff 32 0); (SAlu ALU_ADD (SOff 11 0) (SOff 16 0), SOff 32 1);
        (SAlu ALU_ADD (SOff 33 0) (SOff 16 0), SOff 34 0)]).
Definition b11l_SH2 : list shent := [mkSHE 32 1 2; mkSHE 34 0 1].
(* the registers each run leaves as their own atoms (the LOOP seed pins s10) *)
Definition B11L_KZ : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26].
Definition B11L_KZ2 : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 25].

(* ---- small facts (the B10a segment lane's pf_seg_B10a_s.v / _x.v / _k.v, lib/B/Prog/trim_k.v) ---- *)
Lemma b11l_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b11l_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma b11l_w64_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. exact H. Qed.
Lemma b11l_m1 : w64 (-1) = Z_to_bv 64 B11L_M1.
Proof. apply b11l_w64_mod. reflexivity. Qed.
Lemma b11l_u_add : forall E a b x y, U E a = x -> U E b = y -> 0 <= x + y < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Ha Hb H. rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.
(* the fold of one byte (0x88718-0x88724: c - 'A' <u 26, shifted by 5 and added; `sb` keeps the low byte) *)
Lemma b11l_fold_arith : forall c,
  0 <= c < 256 ->
  ((c + Z.shiftl (if (c + -65) mod 2 ^ 64 <? 26 then 1 else 0) 5) mod 2 ^ 64) mod 256 = lower c.
Proof.
intros c Hc. unfold lower.
destruct (Z.ltb_spec ((c + -65) mod 2 ^ 64) 26) as [Hlt|Hge].
- assert (Hu : (65 <=? c) && (c <=? 90) = true).
  { destruct (Z.leb_spec 65 c) as [H1|H1]; cbn [andb].
    - destruct (Z.leb_spec c 90) as [H2|H2]; [reflexivity|].
      rewrite Z.mod_small in Hlt by lia. lia.
    - assert (Hm : (c + -65) mod 2 ^ 64 = c + -65 + 1 * 2 ^ 64).
      { rewrite <- (Z_mod_plus_full (c + -65) 1 (2 ^ 64)). apply Z.mod_small. lia. }
      rewrite Hm in Hlt. lia. }
  rewrite Hu. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
  apply andb_prop in Hu as [Hu1 Hu2]. apply Z.leb_le in Hu1. apply Z.leb_le in Hu2.
  rewrite Z.mod_small by lia. rewrite Z.mod_small; lia.
- assert (Hu : (65 <=? c) && (c <=? 90) = false).
  { destruct (Z.leb_spec 65 c) as [H1|H1]; cbn [andb]; [|reflexivity].
    destruct (Z.leb_spec c 90) as [H2|H2]; [|reflexivity].
    rewrite Z.mod_small in Hge by lia. lia. }
  rewrite Hu. cbn [Z.shiftl]. rewrite Z.add_0_r, !Z.mod_small by lia. reflexivity.
Qed.
(* the byte the fold stores (0x88718-0x88728), as the executor leaves it in the written region's chunk *)
Definition b11l_fold_sv : sv :=
  SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 12 (-65)) (SLit 26)) (SLit 5)).
Lemma b11l_fold_U : forall E c, ew E 12 = Z_to_bv 64 c -> 0 <= c < 256 -> U E b11l_fold_sv mod 256 = lower c.
Proof.
intros E c H Hc. unfold b11l_fold_sv.
rewrite U_SAlu, U_SAlu, U_SAlu, !U_SOff, !U_SLit, H, unsigned_lit_small by lia. cbn [zalu_raw].
change (Z.land (zcanon 5) 63) with 5. change (zcanon 26) with 26.
rewrite <- (b11l_fold_arith c Hc). unfold zcanon, M64. rewrite Z.add_0_r.
rewrite (Z.mod_small c) by lia.
f_equal. f_equal. f_equal.
destruct ((c + -65) mod 2 ^ 64 <? 26); cbn; reflexivity.
Qed.
Lemma b11l_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma b11l_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = v -> ew E n = v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma b11l_br_eq_lit : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? z) = b.
Proof.
intros E n v z b H Hv Hz Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.
Lemma b11l_reg_atom : forall (regs : bvmap 5 word) (r : bv 5) E n c v,
  getr regs r = sv_denot E (SOff n c) -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> getr regs r = w64 (v + c).
Proof. intros regs r E n c v H Hn Hv. rewrite H. exact (b11l_den_off E n v c Hn Hv). Qed.
Lemma b11l_kz : forall (a b : bvmap 5 word) (L : list Z), (forall r : bv 5, In r (map (Z_to_bv 5) L) -> getr a r = getr b r) ->
  forall r, In r L -> getr a (Z_to_bv 5 r) = getr b (Z_to_bv 5 r).
Proof. intros a b L H r Hr. apply H. apply in_map. exact Hr. Qed.
Lemma b11l_zs_nth : forall (rd : reader) p (s : list Z) i, sa_zs rd p (s ++ [0]) -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
intros rd p s i H Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia).
destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
- rewrite app_nth1 by exact Hl. reflexivity.
- assert (i = length s) as -> by lia. rewrite app_nth2, Nat.sub_diag by lia. cbn [nth].
  rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma b11l_nth_nz : forall (l : list Z) i, ~ In 0 l -> (i < length l)%nat -> nth i l 0 <> 0.
Proof. intros l i H Hi E. apply H. rewrite <- E. apply nth_In. exact Hi. Qed.
Lemma b11l_set_fs_id : forall s, set_fs (st_fs s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma b11l_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
(* buf's 64 cells and model low's three cells are 0 in scope PF_SC_L146 *)
Lemma b11l_shb_buf : forall i, 8 <= i < 72 -> pf_shb PF_SC_L146 i = 0.
Proof.
intros i Hi. unfold pf_shb, PF_SC_L146. cbn [sc_cn sc_buf sc_low sc_l146 sc_known pf_io].
repeat match goal with |- context [i <? ?x] => destruct (Z.ltb_spec i x) end; try reflexivity; lia.
Qed.
Lemma b11l_shb_l146 : forall i, 0x5c <= i < 0x5f -> pf_shb PF_SC_L146 i = 0.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (b11l_zrange (fun i => pf_shb PF_SC_L146 i =? 0) 0x5c 3). vm_compute. reflexivity.
Qed.
(* a register of the final state as the executor's term *)
Ltac b11l_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* the awr obligation of a run whose regions are all read-only *)
Ltac b11l_awr0 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the awr obligation of a run whose regions are read-only, but for one written byte of the class-5 frame at
   atom nn *)
Ltac b11l_awr1 nn U HFRM :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (first [ apply awr_ok_nil
                | apply awr_ok_cons_ro; [cbn; lia|]
                | eapply awr_ok_cons_gen with (n := nn); [reflexivity | exact U | apply HFRM |] ]).
Ltac b11l_in := cbn [In app PF_RL PF_RM PF_SL b11_FI]; repeat first [left; reflexivity | right].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the registers of PF_RL ++ PF_RM after a run that kept s2, s5, s6, s9 and left s10 = -1 *)
Lemma b11l_rg_next : forall (rX rX' : bvmap 5 word) v pos o ln,
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 26) = w64 (-1) ->
  pf_rg rX' (PF_RL v pos ++ PF_RM v o ln).
Proof.
intros rX rX' v pos o ln H QK H26.
assert (G : forall r x, In (r, x) (PF_RL v pos ++ PF_RM v o ln) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x Hi; exact (b11_rg_get rX _ r x H Hi)).
unfold pf_rg, PF_RL, PF_RM. cbn [app].
repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first [exact H26 | rewrite QK by b11l_in; apply G; b11l_in].
Qed.

(* a byte left in a one-byte chunk of a region by a run *)
Lemma b11l_rbyte : forall E ss ms (H : word -> bool) (nn i : nat) lo hi wlo whi cs od e b,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  In (YP09.mkChunk od (CVal 1 e)) cs ->
  bv_unsigned (ew E nn) = b ->
  aview SEGS H (ms_mem ms) (b + od) = Some (U E e mod 256).
Proof.
intros E ss ms H nn i lo hi wlo whi cs od e b HS Hn Hin Hb.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ nn b cs lo hi wlo whi od 1%N e Hr Hb Hin ltac:(lia)) as V.
cbn [ms_mem restrict] in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V. cbn [N.to_nat] in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

(* a byte of the class-5 frame is one the segment may write (its own frame, awr_byte's in_frames) *)
Lemma b11l_awr_frame : forall v pos lyc STK sp0 FP bl0 blc fr0 a,
  pf_F v pos = frame_addr lyc 5 pos -> pf_F v pos <= a < pf_F v pos + 2048 ->
  awr_byte SEGS B STK sp0 FP bl0 blc fr0 lyc [(5, pos)] a.
Proof.
intros v pos lyc STK sp0 FP bl0 blc fr0 a HF Ha. right; right; right; left.
exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite <- HF.
change (fs_frame_bytes 5) with 2048. lia.
Qed.

(* ---- the entry lemmas: each seed holds at a concrete state ---- *)
Lemma b11l_entry1 : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 vp c0,
  getr regs1 (Z_to_bv 5 9) = w64 s1 -> getr regs1 (Z_to_bv 5 20) = w64 SB ->
  rdword (rdW W memc) (s1 + 0x70) = Some vp -> rdW W memc vp = Some c0 -> 0 <= c0 < 256 ->
  4096 <= vp -> vp + 1 <= alloc_ceiling -> alloc_ceiling <= s1 -> s1 + 0x78 <= 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])) b11l_ss1
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + B11_CHK)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 vp c0 H9 H20 Hw Hc Hc0 Hvp Hvp2 Hs1 Hs2.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])).
assert (E9 : ew E 9 = w64 s1) by (subst E; rewrite (ew_Eimg_Ereg_nat regs1 _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E20 : ew E 20 = w64 SB) by (subst E; rewrite (ew_Eimg_Ereg_nat regs1 _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E32 : ew E 32 = w64 vp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (HB : alloc_ceiling <= B11L_HI < 2 ^ 64) by (unfold B11L_HI; lia).
rewrite restrict_mkst_fx. unfold b11l_ss1. apply pa_entry_st_ok_full.
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

Definition b11l_E2 (regs1 : bvmap 5 word) (vp k low c1 : Z) : env :=
  Eimg (Ereg regs1 [w64 (vp + k); w64 low; w64 (low + k); Z_to_bv 64 c1]).
Lemma b11l_entry2 : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 vp k low c1,
  getr regs1 (Z_to_bv 5 9) = w64 s1 -> getr regs1 (Z_to_bv 5 20) = w64 SB ->
  getr regs1 (Z_to_bv 5 26) = w64 (-1) ->
  getr regs1 (Z_to_bv 5 10) = w64 vp -> getr regs1 (Z_to_bv 5 11) = w64 (vp + 1) ->
  getr regs1 (Z_to_bv 5 16) = w64 k -> 0 <= k <= 23 ->
  4096 <= vp -> vp + k + 2 <= alloc_ceiling -> 4096 <= low -> low + 24 <= alloc_ceiling ->
  rdword (rdW W memc) (s1 + 0x90) = Some low ->
  rdW W memc (vp + k + 1) = Some c1 -> 0 <= c1 < 256 ->
  apresent (w_H W) memc (low + k) ->
  alloc_ceiling <= s1 -> s1 + 0x98 <= 2 ^ 64 ->
  vp + k + 2 <= low + k ->
  st_ok_pi SEGS VAL (b11l_E2 regs1 vp k low c1) b11l_ss2
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + B11_LOOP)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 vp k low c1 H9 H20 H26 H10 H11 H16 Hk Hv1 Hv2 Hl1 Hl2 Hw Hc Hc1 Hp Hs1 Hs2 Hd.
pose proof asan_consts as (C1 & _).
set (E := b11l_E2 regs1 vp k low c1).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j [w64 (vp + k); w64 low; w64 (low + k); Z_to_bv 64 c1] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold b11l_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth] in E32, E33, E34, E35. clear EX.
assert (E9 : ew E 9 = w64 s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew E 10 = w64 vp) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew E 11 = w64 (vp + 1)) by (rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E16 : ew E 16 = w64 k) by (rewrite (EE 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E20 : ew E 20 = w64 SB) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (HB : alloc_ceiling <= B11L_HI < 2 ^ 64) by (unfold B11L_HI; lia).
rewrite restrict_mkst_fx. unfold b11l_ss2. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. rewrite <- b11l_m1. exact (b11l_bvr regs1 26%bv 26 _ eq_refl H26).
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1 0x90 8 (SOff 33 0) low);
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
    * rewrite (b11l_u_add E _ _ vp k); [| apply U_atom; [exact E10 | lia] | apply U_atom; [exact E16 | lia] | lia].
      symmetry. apply U_atom; [exact E32 | lia].
    * rewrite (b11l_u_add E _ _ (vp + 1) k); [| apply U_atom; [exact E11 | lia] | apply U_atom; [exact E16 | lia] | lia].
      rewrite (U_atom_off E 32 (vp + k) 1 E32) by lia. lia.
    * rewrite (b11l_u_add E _ _ low k); [| apply U_atom; [exact E33 | lia] | apply U_atom; [exact E16 | lia] | lia].
      symmetry. apply U_atom; [exact E34 | lia].
Qed.

(* ---- what a cut of B11a gives the two seeds (b11_cx) ---- *)
Lemma b11l_facts : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  b11_cx B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) /\ getr rX (Z_to_bv 5 20) = w64 SB /\
  alloc_ceiling <= pf_s1 v /\ pf_s1 v + 0xe0 <= 2 ^ 64 /\
  rdword (rdW Wc memc) (pf_s1 v + 0x70) = Some vp /\
  rdword (rdW Wc memc) (pf_s1 v + 0x90) = Some (pf_F v pos + PF_O_L146) /\
  ~ In 0 val /\
  (forall i, (i <= length val)%nat -> rdW Wc memc (vp + Z.of_nat i) = Some (nth i val 0)) /\
  (forall i, (i < length val)%nat -> 0 <= nth i val 0 < 256) /\
  pf_F v pos + PF_O_BUF <= vp /\ vp + Z.of_nat (length val) < pf_F v pos + PF_O_BUF + 512 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\
  range_addressable (rdW Wc memc) SHADOW_OFF vp (Z.of_nat (length val) + 1) /\
  range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_L146) 24 /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> apresent (w_H Wc) memc a) /\
  pf_F v pos = frame_addr lyc 5 pos /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) /\
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HCX.
pose proof HCX as (HB & HMID & HST & HSTR & HINB & HSL70).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (HG & Hin & EF & Hfrs & HAR & Hly & Hfp & Hsh).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof HB as (_ & HFI & _ & HSL & _).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof asan_consts as (C1 & _).
destruct HSTR as ((HZS & NZ) & _).
unfold pf_inb in HINB.
assert (VB : forall i, (i <= length val)%nat -> rdW Wc memc (vp + Z.of_nat i) = Some (nth i val 0))
  by (intros i Hi; exact (b11l_zs_nth _ vp val i HZS Hi)).
assert (RAB : range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + 0x40) 512).
{ apply (b11_ra_frame B v pos lyc Sc Wc rX memc mdc PF_SC_L146 0x40 512 HB); try reflexivity; try lia.
  intros i [Hi1 Hi2]. apply b11l_shb_buf.
  split; [refine (Z.le_trans _ _ _ _ Hi1) | refine (Z.lt_le_trans _ _ _ Hi2 _)]; vm_compute; intros X; discriminate X. }
assert (RAL : range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_L146) 24).
{ unfold PF_O_L146. apply (b11_ra_frame B v pos lyc Sc Wc rX memc mdc PF_SC_L146 0x2e0 24 HB); try reflexivity; try lia.
  intros i [Hi1 Hi2]. apply b11l_shb_l146.
  split; [refine (Z.le_trans _ _ _ _ Hi1) | refine (Z.lt_le_trans _ _ _ Hi2 _)]; vm_compute; intros X; discriminate X. }
split; [apply (b11_rg_get rX _ 9 _ HRG0); b11l_in|].
split; [rewrite SB_SHADOW_OFF; apply (b11_rg_get rX _ 20 _ HRG0); b11l_in|].
split; [lia|]. split; [lia|].
split; [exact (b11_slot_get _ _ _ 0x70 vp HSL70 (or_introl eq_refl))|].
split; [apply (b11_slot_get _ _ _ 0x90 _ HSL); b11l_in|].
split; [exact NZ|].
split; [exact VB|].
split; [intros i Hi; pose proof (VB i ltac:(lia)) as E; destruct (aview_byte SEGS _ _ _ _ E) as (_ & _ & _ & Hr); exact Hr|].
split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|].
split; [exact (range_addressable_sub _ _ _ _ vp (Z.of_nat (length val) + 1) RAB
          ltac:(unfold PF_O_BUF in *; lia) ltac:(unfold PF_O_BUF in *; lia))|].
split; [exact RAL|].
split; [exact Hfp|].
split; [symmetry; exact EF|].
split; [intros a Ha; unfold SHADOW_OFF; destruct F4; lia|].
exact HJ.
Qed.

(* b11_cx after a run that kept every byte but one byte w of model low, kept every visible byte visible, and kept
   the registers of b11_FI (and of PF_RL / PF_RM) *)
Lemma b11l_cx_next : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rX' memc' mdc' w,
  b11_cx B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> w -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_F v pos + PF_O_L146 <= w < pf_F v pos + PF_O_L146 + 24 ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  b11_cx B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rX' memc' mdc' w HCX HJ' KS Hw KV QK.
pose proof HCX as ((_ & HFI & _) & _).
pose proof HFI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
apply (b11_cx_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Sc Wc rX' memc' mdc' HCX HJ').
- exists (st_fs Sc). symmetry. apply b11l_set_fs_id.
- apply Permutation_refl.
- split.
  + intros a Ha Hn. apply KS; [exact Ha|]. intros E. apply Hn. unfold b11_Wr. right; left. rewrite E. exact Hw.
  + intros a _ Hv. exact (KV a Hv).
- unfold pf_rg, b11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b11_rg_get rX _ _ _ HRG0); b11l_in | b11l_in]).
Qed.

(* after a run of the CHK seed (it writes nothing): the memory reads as memc, every visible byte stays visible *)
Ltac b11l_after0 memc KSp KVp msname KSname KVname :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m0) (mrestrict _ (ms_mem ?msn)),
    HGr : mem_grows (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    assert (KSname : forall a, 0 <= a < 2 ^ 64 -> aview SEGS Hh (ms_mem msn) a = aview SEGS Hh memc a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo rs Hh m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KSp a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in
                    destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KVname : forall a, aview SEGS Hh memc a <> None -> aview SEGS Hh (ms_mem msn) a <> None)
      by (let a := fresh "a" in let Hv := fresh "Hv" in intros a Hv;
          exact (aview_keeps_vis SEGS Hh _ (ms_mem msn) a HGr (KVp a Hv)));
    clear KSp KVp;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
    rename msn into msname
  end.

(* after a run of the LOOP seed, whose one written window is model low + li (atom 34) *)
Ltac b11l_after E0 memc low k E34 KSp KVp msname KSname KVname :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m0) (mrestrict _ (ms_mem ?msn)),
    HGr : mem_grows (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let Uo := fresh "Uo" in
    assert (Uo : bv_unsigned (ew Eo 34) = low + Z.of_nat k)
      by (rewrite (b11l_ag_ew E0 Eo 40 34 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E34);
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
    assert (KVname : forall a, aview SEGS Hh memc a <> None -> aview SEGS Hh (ms_mem msn) a <> None)
      by (let a := fresh "a" in let Hv := fresh "Hv" in intros a Hv;
          exact (aview_keeps_vis SEGS Hh _ (ms_mem msn) a HGr (KVp a Hv)));
    clear Uo KSp KVp;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
    rename msn into msname
  end.

(* ---- LOOP (0x88704), one iteration; by strong induction on 23 - li ---- *)
Definition B11L_m (n m : nat) : Prop := forall li, (23 - li = m)%nat -> B11_LOOP_stmt (fx := fx) B n li.

Lemma b11l_loop_step : forall n, (forall li, B11_ZST_stmt (fx := fx) B n li) ->
  forall m, (forall m', (m' < m)%nat -> B11L_m n m') -> B11L_m n m.
Proof.
intros n HZST m IH li Hm. unfold B11_LOOP_stmt.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct HI as (HCX & Hli & Hlv & HLOW & HRG).
unfold B11_CAP in Hli.
pose proof (b11l_facts n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HCX)
  as (R9 & R20 & Hs1 & Hs1e & W70 & W90 & NZ & VB & VR & Hb1 & Hb2 & F4096 & Fc & RAV & RAL & Fp & HFA & NSB & HJ).
assert (R26 : getr rX (Z_to_bv 5 26) = w64 (-1)) by (apply (b11_rg_get rX _ 26 _ HRG); b11l_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 vp) by (apply (b11_rg_get rX _ 10 _ HRG); b11l_in).
assert (R11 : getr rX (Z_to_bv 5 11) = w64 (vp + 1)) by (apply (b11_rg_get rX _ 11 _ HRG); b11l_in).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 (nth li val 0)) by (apply (b11_rg_get rX _ 12 _ HRG); b11l_in).
assert (R16 : getr rX (Z_to_bv 5 16) = w64 (Z.of_nat li)) by (apply (b11_rg_get rX _ 16 _ HRG); b11l_in).
assert (HRL : pf_rg rX (PF_RL v pos ++ PF_RM v o ln)).
{ rewrite app_assoc in HRG. exact (proj1 (proj1 (b11_rg_app _ _ _) HRG)). }
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold PF_O_BUF in Hb1, Hb2.
pose proof (b11f_low_len val 24 NZ) as RLL.
set (low := pf_F v pos + PF_O_L146) in *.
assert (Hlow : 4096 <= low /\ low + 24 <= alloc_ceiling /\ pf_F v pos + 576 < low) by (unfold low, PF_O_L146; lia).
set (c := nth li val 0) in *.
set (c1 := nth (S li) val 0) in *.
assert (HCR : 0 < c < 256) by (unfold c; pose proof (VR li Hlv); pose proof (b11l_nth_nz val li NZ Hlv); lia).
assert (HCR1 : 0 <= c1 < 256).
{ destruct (Nat.lt_ge_cases (S li) (length val)) as [Hl|Hl]; [exact (VR _ Hl)|].
  unfold c1. rewrite nth_overflow by exact Hl. lia. }
assert (V1 : rdW Wc memc (vp + Z.of_nat li + 1) = Some c1).
{ replace (vp + Z.of_nat li + 1) with (vp + Z.of_nat (S li)) by lia. exact (VB (S li) ltac:(lia)). }
pose proof (b11l_entry2 Wc rX memc (pf_s1 v) vp (Z.of_nat li) low c1 R9 R20 R26 R10 R11 R16 ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) W90 V1 HCR1 (Fp (low + Z.of_nat li) ltac:(unfold low, PF_O_L146 in *; lia))
  ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (b11l_E2 rX vp (Z.of_nat li) low c1)) by (unfold b11l_E2; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX [w64 (vp + Z.of_nat li); w64 low; w64 (low + Z.of_nat li); Z_to_bv 64 c1])
  (b11l_E2 rX vp (Z.of_nat li) low c1))
  by (split; [intros n0 Hn0; unfold b11l_E2; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew (b11l_E2 rX vp (Z.of_nat li) low c1) nn = getr rX r)
  by (intros nn r Hn; unfold b11l_E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 10 = Z_to_bv 64 vp)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E11 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 11 = Z_to_bv 64 (vp + 1))
  by (rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl); exact R11).
assert (E12 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 12 = Z_to_bv 64 c)
  by (rewrite (EE 12%nat (Z_to_bv 5 12) eq_refl); exact R12).
assert (E16 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 16 = Z_to_bv 64 (Z.of_nat li))
  by (rewrite (EE 16%nat (Z_to_bv 5 16) eq_refl); exact R16).
assert (E20 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 20 = Z_to_bv 64 SB)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 32 = Z_to_bv 64 (vp + Z.of_nat li))
  by (unfold b11l_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E34 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 34 = Z_to_bv 64 (low + Z.of_nat li))
  by (unfold b11l_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (E35 : ew (b11l_E2 rX vp (Z.of_nat li) low c1) 35 = Z_to_bv 64 c1)
  by (unfold b11l_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 3)).
clear EE.
revert HS HEI HA0 E10 E11 E12 E16 E20 E32 E34 E35. generalize (b11l_E2 rX vp (Z.of_nat li) low c1) as E0.
intros E0 HS HEI HA0 E10 E11 E12 E16 E20 E32 E34 E35.
assert (U34 : bv_unsigned (ew E0 34) = low + Z.of_nat li) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UB : U E0 b11l_Bx = SHADOW_OFF) by (unfold b11l_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS b11l_Bx b11l_SH2 E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b11l_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b11l_Bx 32%nat vp (Z.of_nat (length val) + 1) (vp + Z.of_nat li) 1 2
      RAV UB ltac:(apply U_atom; [exact E32 | lia])); [lia | lia |].
    intros x Hx. change (Z.min 1 2) with 1 in Hx. change (Z.max 1 2) with 2 in Hx. apply NSB. lia.
  - eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b11l_Bx 34%nat low 24 (low + Z.of_nat li) 0 1 RAL UB
      ltac:(apply U_atom; [exact E34 | lia])); [lia | lia |].
    intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    apply NSB. unfold low, PF_O_L146 in *. lia. }
assert (HFRM : forall a, low + Z.of_nat li + 0 <= a < low + Z.of_nat li + 1 ->
  awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (ablocks B (p_ly v) (p_S v))
    (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a).
{ intros a Ha. apply (b11l_awr_frame v pos lyc _ _ _ _ _ _ a HFA). unfold low, PF_O_L146 in *. lia. }
assert (KS0 : forall a, 0 <= a < 2 ^ 64 -> a <> low + Z.of_nat li -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KV0 : forall a, rdW Wc memc a <> None -> rdW Wc memc a <> None) by (intros a Hv; exact Hv).
unfold cfg_at. change (w64 (BASE + B11_LOOP)) with (Z_to_bv 64 (BASE + B11_LOOP)).
(* 0x88704 .. 0x88708: `li a3,23; beq a6,a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b11l_awr1 34%nat U34 HFRM. }
b11l_after E0 memc low li E34 KS0 KV0 ms1 KS1 KV1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* li = 23: ZST with a3 = 23 *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b11l_br_eq_lit En 16 (Z.of_nat li) 23 true (b11l_ag_ew E0 En 40 16 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E16)
      ltac:(lia) ltac:(lia) Hc) as Hk23 end.
  apply Z.eqb_eq in Hk23. assert (Hk : li = 23%nat) by lia. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B11_ZST.
  { b11l_awr1 34%nat U34 HFRM. }
  b11l_after E0 memc low li E34 KS1 KV1 ms2 KS2 KV2.
  lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ B11L_KZ2 HS (b11l_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HKb.
  cbn [ms_regs restrict] in HKb.
  pose proof (b11l_kz _ _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 25] HKb) as QK.
  b11l_reg HS (Z_to_bv 5 26) N26. b11l_reg HS (Z_to_bv 5 13) N13.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B11_ZST) rg mm mdx) end.
  assert (RL : length (r_low val 0 24) = li) by (rewrite RLL; lia).
  apply (HZST li v pos lyc Sc Wc (ms_regs ms2) (ms_mem ms2) _ cf nm o ln d gi vp val).
  split; [|split; [|split; [|split]]].
  + apply (b11l_cx_next n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ _ _ (low + Z.of_nat li) HCX HJ KS2
      ltac:(unfold low, PF_O_L146 in *; lia) KV2 QK).
  + symmetry. exact RL.
  + unfold B11_CAP. lia.
  + intros j Hj. rewrite (KS2 (pf_F v pos + PF_O_L146 + Z.of_nat j)) by (unfold low, PF_O_L146 in *; lia).
    apply HLOW. lia.
  + rewrite app_assoc. apply (proj2 (b11_rg_app _ _ _)). split.
    * apply (b11l_rg_next rX _ v pos o ln HRL QK).
      rewrite N26. cbn [sv_denot]. apply b11l_w64_mod. reflexivity.
    * apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. rewrite N13. cbn [sv_denot]. rewrite Hk. reflexivity.
- (* li < 23: the fold step, T18 (decided), B#19 (covered), the byte val[li + 1] *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b11l_br_eq_lit En 16 (Z.of_nat li) 23 false (b11l_ag_ew E0 En 40 16 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E16)
      ltac:(lia) ltac:(lia) Hc) as Hk23 end.
  apply Z.eqb_neq in Hk23. assert (Hk : (li < 23)%nat) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { b11l_awr1 34%nat U34 HFRM. }
  b11l_after E0 memc low li E34 KS1 KV1 ms2 KS2 KV2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* val[li + 1] = 0: ZST with a3 = li + 1 *)
    lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
      pose proof (b11l_br_eq_lit En 35 c1 0 true (b11l_ag_ew E0 En 40 35 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E35)
        ltac:(lia) ltac:(lia) Hc) as Hz end.
    apply Z.eqb_eq in Hz. clear Hc.
    assert (HL : length val = S li).
    { destruct (Nat.lt_ge_cases (S li) (length val)) as [Hl|Hl]; [|lia].
      exfalso. exact (b11l_nth_nz val (S li) NZ Hl Hz). }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B11_ZST.
    { b11l_awr1 34%nat U34 HFRM. }
    b11l_after E0 memc low li E34 KS2 KV2 ms3 KS3 KV3.
    lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
      assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
    (* the folded byte at low + li *)
    assert (HWB : rdW Wc (ms_mem ms3) (low + Z.of_nat li) = Some (lower c)).
    { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
        pose proof (b11l_rbyte Ex ssx ms3 (w_H Wc) 34%nat 2%nat 0 1 0 1 [YP09.mkChunk 0 (CVal 1 b11l_fold_sv)] 0 b11l_fold_sv
          (low + Z.of_nat li) HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as V;
        rewrite Z.add_0_r in V; rewrite V;
        [ rewrite (b11l_fold_U Ex c (b11l_ag_ew E0 Ex 40 12 _ HAE ltac:(lia) E12) ltac:(lia)); reflexivity
        | rewrite (b11l_ag_ew E0 Ex 40 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia ] end. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ B11L_KZ2 HS (b11l_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HKb.
    cbn [ms_regs restrict] in HKb.
    pose proof (b11l_kz _ _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 25] HKb) as QK.
    b11l_reg HS (Z_to_bv 5 26) N26. b11l_reg HS (Z_to_bv 5 13) N13.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B11_ZST) rg mm mdx) end.
    assert (RL : length (r_low val 0 24) = S li) by (rewrite RLL; lia).
    apply (HZST (S li) v pos lyc Sc Wc (ms_regs ms3) (ms_mem ms3) _ cf nm o ln d gi vp val).
    split; [|split; [|split; [|split]]].
    * apply (b11l_cx_next n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ _ _ (low + Z.of_nat li) HCX HJ KS3
        ltac:(unfold low, PF_O_L146 in *; lia) KV3 QK).
    * symmetry. exact RL.
    * unfold B11_CAP. lia.
    * intros j Hj. destruct (Nat.eq_dec j li) as [->|Hne]; [exact HWB|].
      rewrite (KS3 (pf_F v pos + PF_O_L146 + Z.of_nat j)) by (unfold low, PF_O_L146 in *; lia).
      apply HLOW. lia.
    * rewrite app_assoc. apply (proj2 (b11_rg_app _ _ _)). split.
      -- apply (b11l_rg_next rX _ v pos o ln HRL QK).
         rewrite N26. cbn [sv_denot]. apply b11l_w64_mod. reflexivity.
      -- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
         rewrite (b11l_reg_atom _ _ _ 16 1 (Z.of_nat li) N13 (b11l_ag_ew E0 _ 40 16 _ HAE ltac:(lia) E16) ltac:(lia)).
         f_equal. lia.
  + (* val[li + 1] <> 0: LOOP with li + 1 *)
    lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
      pose proof (b11l_br_eq_lit En 35 c1 0 false (b11l_ag_ew E0 En 40 35 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E35)
        ltac:(lia) ltac:(lia) Hc) as Hz end.
    apply Z.eqb_neq in Hz. clear Hc.
    assert (HL : (S li < length val)%nat).
    { destruct (Nat.lt_ge_cases (S li) (length val)) as [Hl|Hl]; [exact Hl|].
      exfalso. apply Hz. unfold c1. apply nth_overflow. exact Hl. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B11_LOOP.
    { b11l_awr1 34%nat U34 HFRM. }
    b11l_after E0 memc low li E34 KS2 KV2 ms3 KS3 KV3.
    lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
      assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
    assert (HWB : rdW Wc (ms_mem ms3) (low + Z.of_nat li) = Some (lower c)).
    { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
        pose proof (b11l_rbyte Ex ssx ms3 (w_H Wc) 34%nat 2%nat 0 1 0 1 [YP09.mkChunk 0 (CVal 1 b11l_fold_sv)] 0 b11l_fold_sv
          (low + Z.of_nat li) HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as V;
        rewrite Z.add_0_r in V; rewrite V;
        [ rewrite (b11l_fold_U Ex c (b11l_ag_ew E0 Ex 40 12 _ HAE ltac:(lia) E12) ltac:(lia)); reflexivity
        | rewrite (b11l_ag_ew E0 Ex 40 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia ] end. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ B11L_KZ2 HS (b11l_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HKb.
    cbn [ms_regs restrict] in HKb.
    pose proof (b11l_kz _ _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 25] HKb) as QK.
    b11l_reg HS (Z_to_bv 5 26) N26. b11l_reg HS (Z_to_bv 5 10) N10. b11l_reg HS (Z_to_bv 5 11) N11.
    b11l_reg HS (Z_to_bv 5 12) N12. b11l_reg HS (Z_to_bv 5 16) N16.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B11_LOOP) rg mm mdx) end.
    apply (IH (23 - S li)%nat ltac:(lia) (S li) eq_refl v pos lyc Sc Wc (ms_regs ms3) (ms_mem ms3) _ cf nm o ln d gi vp val).
    split; [|split; [|split; [|split]]].
    * apply (b11l_cx_next n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ _ _ (low + Z.of_nat li) HCX HJ KS3
        ltac:(unfold low, PF_O_L146 in *; lia) KV3 QK).
    * unfold B11_CAP. lia.
    * exact HL.
    * intros j Hj. destruct (Nat.eq_dec j li) as [->|Hne]; [exact HWB|].
      rewrite (KS3 (pf_F v pos + PF_O_L146 + Z.of_nat j)) by (unfold low, PF_O_L146 in *; lia).
      apply HLOW. lia.
    * rewrite app_assoc. apply (proj2 (b11_rg_app _ _ _)). split.
      -- apply (b11l_rg_next rX _ v pos o ln HRL QK).
         rewrite N26. cbn [sv_denot]. apply b11l_w64_mod. reflexivity.
      -- repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
         ++ rewrite (b11l_reg_atom _ _ _ 10 0 vp N10 (b11l_ag_ew E0 _ 40 10 _ HAE ltac:(lia) E10) ltac:(lia)).
            f_equal. lia.
         ++ rewrite (b11l_reg_atom _ _ _ 11 0 (vp + 1) N11 (b11l_ag_ew E0 _ 40 11 _ HAE ltac:(lia) E11) ltac:(lia)).
            f_equal. lia.
         ++ rewrite (b11l_reg_atom _ _ _ 35 0 c1 N12 (b11l_ag_ew E0 _ 40 35 _ HAE ltac:(lia) E35) ltac:(lia)).
            f_equal. unfold c1. lia.
         ++ rewrite (b11l_reg_atom _ _ _ 16 1 (Z.of_nat li) N16 (b11l_ag_ew E0 _ 40 16 _ HAE ltac:(lia) E16) ltac:(lia)).
            f_equal. lia.
Qed.

Lemma b11l_loop : forall n, (forall li, B11_ZST_stmt (fx := fx) B n li) -> forall li, B11_LOOP_stmt (fx := fx) B n li.
Proof.
intros n HZST.
assert (ALL : forall j m, (m <= j)%nat -> B11L_m n m).
{ induction j as [|j IHj]; intros m Hm.
  - apply (b11l_loop_step n HZST m). intros m' Hm'. lia.
  - apply (b11l_loop_step n HZST m). intros m' Hm'. apply (IHj m'). lia. }
intros li. exact (ALL _ _ (le_n _) li eq_refl).
Qed.

(* ---- CHK (0x886e0): val, check B#18 (covered), val[0], `beqz a2` ---- *)
Lemma b11l_chk : forall n, (forall li, B11_LOOP_stmt (fx := fx) B n li) -> (forall li, B11_ZST_stmt (fx := fx) B n li) ->
  B11_CHK_stmt (fx := fx) B n.
Proof.
intros n HLOOP HZST. unfold B11_CHK_stmt.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct HI as (HCX & HRG).
pose proof (b11l_facts n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HCX)
  as (R9 & R20 & Hs1 & Hs1e & W70 & W90 & NZ & VB & VR & Hb1 & Hb2 & F4096 & Fc & RAV & RAL & Fp & HFA & NSB & HJ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold PF_O_BUF in Hb1, Hb2.
pose proof (b11f_low_len val 24 NZ) as RLL.
set (c0 := nth 0 val 0) in *.
assert (HC0 : 0 <= c0 < 256).
{ destruct val as [|x r]; [unfold c0; cbn; lia|]. exact (VR 0%nat ltac:(cbn; lia)). }
assert (V0 : rdW Wc memc vp = Some c0) by (pose proof (VB 0%nat ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
pose proof (b11l_entry1 Wc rX memc (pf_s1 v) vp c0 R9 R20 W70 V0 HC0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX [w64 vp; Z_to_bv 64 c0]))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX [w64 vp; Z_to_bv 64 c0]) (Eimg (Ereg rX [w64 vp; Z_to_bv 64 c0])))
  by (split; [intros n0 Hn0; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E20 : ew (Eimg (Ereg rX [w64 vp; Z_to_bv 64 c0])) 20 = Z_to_bv 64 SB)
  by (rewrite (ew_Eimg_Ereg_nat rX _ 20 (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew (Eimg (Ereg rX [w64 vp; Z_to_bv 64 c0])) 32 = Z_to_bv 64 vp)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (Eimg (Ereg rX [w64 vp; Z_to_bv 64 c0])) 33 = Z_to_bv 64 c0)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
revert HS HEI HA0 E20 E32 E33. generalize (Eimg (Ereg rX [w64 vp; Z_to_bv 64 c0])) as E0.
intros E0 HS HEI HA0 E20 E32 E33.
assert (UB : U E0 b11l_Bx = SHADOW_OFF) by (unfold b11l_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS b11l_Bx b11l_SH1 E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b11l_SH1. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b11l_Bx 32%nat vp (Z.of_nat (length val) + 1) vp 0 1 RAV UB
    ltac:(apply U_atom; [exact E32 | lia])); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx. apply NSB. lia. }
assert (KS0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KV0 : forall a, rdW Wc memc a <> None -> rdW Wc memc a <> None) by (intros a Hv; exact Hv).
unfold cfg_at. change (w64 (BASE + B11_CHK)) with (Z_to_bv 64 (BASE + B11_CHK)).
(* 0x886e0 .. 0x886f8: val, check B#18 (covered), val[0], up to `beqz a2` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b11l_awr0. }
b11l_after0 memc KS0 KV0 ms1 KS1 KV1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* val[0] = 0: val is empty; ZST with a3 = 0 (0x889a8) *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b11l_br_eq_lit En 33 c0 0 true (b11l_ag_ew E0 En 40 33 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E33)
      ltac:(lia) ltac:(lia) Hc) as Hz end.
  apply Z.eqb_eq in Hz. clear Hc.
  assert (HL : length val = 0%nat).
  { destruct val as [|x r]; [reflexivity|]. exfalso. apply NZ. left. exact Hz. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B11_ZST.
  { b11l_awr0. }
  b11l_after0 memc KS1 KV1 ms2 KS2 KV2.
  lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ B11L_KZ HS (b11l_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HKb.
  cbn [ms_regs restrict] in HKb.
  pose proof (b11l_kz _ _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26] HKb) as QK11.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25] ->
    getr (ms_regs ms2) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) by (intros r Hr; apply QK11; cbn [In] in *; tauto).
  b11l_reg HS (Z_to_bv 5 13) N13.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B11_ZST) rg mm mdx) end.
  apply (HZST 0%nat v pos lyc Sc Wc (ms_regs ms2) (ms_mem ms2) _ cf nm o ln d gi vp val).
  split; [|split; [|split; [|split]]].
  + apply (b11l_cx_next n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ _ _ (pf_F v pos + PF_O_L146) HCX HJ
      (fun a Ha _ => KS2 a Ha) ltac:(unfold PF_O_L146; lia) KV2 QK).
  + rewrite RLL. lia.
  + unfold B11_CAP. lia.
  + intros j Hj. lia.
  + rewrite app_assoc. apply (proj2 (b11_rg_app _ _ _)). split.
    * apply (b11l_rg_next rX _ v pos o ln HRG QK).
      rewrite QK11 by b11l_in. apply (b11_rg_get rX _ 26 _ HRG). b11l_in.
    * apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. rewrite N13. reflexivity.
- (* val[0] <> 0: LOOP with li = 0 (0x886fc `li a6,0`, 0x88700 `addi a1,a0,1`) *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b11l_br_eq_lit En 33 c0 0 false (b11l_ag_ew E0 En 40 33 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E33)
      ltac:(lia) ltac:(lia) Hc) as Hz end.
  apply Z.eqb_neq in Hz. clear Hc.
  assert (HL : (0 < length val)%nat) by (destruct val as [|x r]; [exfalso; apply Hz; reflexivity | cbn; lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B11_LOOP.
  { b11l_awr0. }
  b11l_after0 memc KS1 KV1 ms2 KS2 KV2.
  lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ B11L_KZ HS (b11l_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HKb.
  cbn [ms_regs restrict] in HKb.
  pose proof (b11l_kz _ _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26] HKb) as QK11.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25] ->
    getr (ms_regs ms2) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) by (intros r Hr; apply QK11; cbn [In] in *; tauto).
  b11l_reg HS (Z_to_bv 5 10) N10. b11l_reg HS (Z_to_bv 5 11) N11.
  b11l_reg HS (Z_to_bv 5 12) N12. b11l_reg HS (Z_to_bv 5 16) N16.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B11_LOOP) rg mm mdx) end.
  apply (HLOOP 0%nat v pos lyc Sc Wc (ms_regs ms2) (ms_mem ms2) _ cf nm o ln d gi vp val).
  split; [|split; [|split; [|split]]].
  + apply (b11l_cx_next n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ _ _ (pf_F v pos + PF_O_L146) HCX HJ
      (fun a Ha _ => KS2 a Ha) ltac:(unfold PF_O_L146; lia) KV2 QK).
  + unfold B11_CAP. lia.
  + exact HL.
  + intros j Hj. lia.
  + rewrite app_assoc. apply (proj2 (b11_rg_app _ _ _)). split.
    * apply (b11l_rg_next rX _ v pos o ln HRG QK).
      rewrite QK11 by b11l_in. apply (b11_rg_get rX _ 26 _ HRG). b11l_in.
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
      -- rewrite (b11l_reg_atom _ _ _ 32 0 vp N10 (b11l_ag_ew E0 _ 40 32 _ HAE ltac:(lia) E32) ltac:(lia)).
         f_equal. lia.
      -- rewrite (b11l_reg_atom _ _ _ 32 1 vp N11 (b11l_ag_ew E0 _ 40 32 _ HAE ltac:(lia) E32) ltac:(lia)).
         reflexivity.
      -- rewrite (b11l_reg_atom _ _ _ 33 0 c0 N12 (b11l_ag_ew E0 _ 40 33 _ HAE ltac:(lia) E33) ltac:(lia)).
         f_equal. unfold c0. lia.
      -- rewrite N16. reflexivity.
Qed.
End x.

(* the two cuts at every FP state *)
Theorem b11_loop_ok : forall (fx : YK11.FPState) (n : nat),
  (forall li, B11_ZST_stmt (fx := fx) B n li) -> forall li, B11_LOOP_stmt (fx := fx) B n li.
Proof. intros fx n H. exact (b11l_loop (fx := fx) n H). Qed.
Theorem b11_chk_ok : forall (fx : YK11.FPState) (n : nat),
  (forall li, B11_LOOP_stmt (fx := fx) B n li) -> (forall li, B11_ZST_stmt (fx := fx) B n li) ->
  B11_CHK_stmt (fx := fx) B n.
Proof. intros fx n HL HZ. exact (b11l_chk (fx := fx) n HL HZ). Qed.
End d.
