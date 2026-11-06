(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheck.v (ck_entry, the code table ck_tbl / ck_wx / ck_segs_low) and
   lib/A/RPgCheckStr.v (rl_cstr_kept) at 77f59d02b01 for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02:
   the half's code table, the entry state of a run that starts at one of its cuts (the registers, the real frame at
   s1 and the role cell as regions), the stack facts of lib/A/RPgSeg.v's rs_pre, the seam between RPgSeg's rs_core and
   lib/A/RPgCSpec.v's callee contracts (rl_pre before a call, rl_post after it), and the strings and cells the callees
   read, carried from the segment's start to a cut (rl_cstr_kept with two worlds and the half's write set). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 887bee7c56d and
   proofs/reac-pw/fuzz_rate/lib/AU/RtPgM02BaseB.v at f07713e8e823 for image B (fuzz_role.asan-ubsan): image B's pcs,
   callees and literals; the code table covers the key compare to the malformed check (0x82370 .. 0x82500) and the
   three runs of slow blocks of its five instrumented checks; the shadow base is s11 (atom 27); the role cell is at
   F+0x2a0 held in s4 (atom 20); the real frame's size is 0x200; the frame for locals is a side-stack frame of class
   4 (1024 bytes); the cuts are lib/AU/RPgSeg.v's; the zone of the callees' strings is image B's read-only segment
   and the start of its relro segment; and image B's extras of fuzz_rate's image-B file (the first block's bounds
   m2_pp, the image bytes kept m2_keep_img, rom_view at a cut m2_rom_at, the harness's key m2_key_at, the write-range
   and I/O tactics m2_kwr / m2_io and the register lemmas) are added under role's m2_ names. *)
(* reac-pw/fuzz_role, image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes): the vocabulary the
   walks of M02's match half share. Statement text and shared lemmas only; no segment is walked here. Proves no
   function (kind: statement text).

   WHAT THE MATCH HALF IS. M02 is role_check_contract (lib/A/RPgCSpec.v) at image B's record
   lib/AU/RPgImgA.v role_himg_B: from C3 0x82168 to C4 0x82570. Its scan half (C3 -> E 0x821dc -> O 0x82278 /
   I 0x822a4, the two expect_role loops) is walked elsewhere; this half begins at the four pcs the scan leaves:

     KM  0x82370  a key was found at ent[m]: the strcmp of its body against "reac.cfg.role" (.str.3 0x20f20), and on
                  a match the flag cell R+0x178 := -1 and the value ent[v], v = m + 1, read as an Int (type 4) or a
                  Float (type 6, through pod_nearest 0x82eb4), the value < 2 test, then check_role 0x82aac; on a
                  mismatch back to the scan's outer head O 0x82278 with at = m + 2.
     ABS 0x8245c  no pair matched: check_absent 0x82a80, then T.
     MAL 0x824f8  the value is not a role: check_malformed 0x82ad8, whose return address is T itself.
     T   0x82504  the tail: reac_role_cfg_changes 0x83108, reac_role_cfg_apply_state 0x83114, check_answer 0x82b08,
                  reac_role_refuse_code 0x8309c twice and check_code 0x82b5c; C4 0x82570 is the instruction after
                  check_code returns.

   THE CODE (the neutral listing of the walk; `SHADOW load` marks an instrumented check's shadow byte; "trap" a
   branch to the `unimp` 0x82604):
     0x82370 addiw s8,a2,1; 0x82374 blt s8,a2 -> trap (a2 = m + 1 <= 32); 0x82378 bltz a2 -> ABS (dead)
     0x8237c/0x82380 auipc/addi a1 = 0x20f20; 0x82384 .. 0x82394 five spills a7, t0, t1, t2, t3 to R+0x150,
             R+0x148, R+0x138, R+0x130, R+0x128; 0x82398 jal 0x41b68 (the strcmp wrapper, a0 = &ent[m].body),
             ra = 0x8239c
     0x8239c li t4,8; 0x823a0 .. 0x823b0 the five reloads; 0x823b4 mv a2,s8; 0x823b8 bnez a0 -> O (mismatch,
             at = m + 2)
     0x823bc li a0,-1; 0x823c0 li a1,33; 0x823c4 sd a0,0x178(s1) (the flag cell); 0x823c8 bgeu s5,a1 -> trap
             (s5 = m + 1); 0x823cc ld s9,0x158(s1) (rc); 0x823d0 bltu s6,s7 -> trap (s6 = ~(pp + 0x4014),
             s7 = 104 (m + 1)); 0x823d4 add a0,s10,s7 = &ent[v]
     KV 0x823d8 srli/add/lb SHADOW load; 0x823e4 ld s8,0x40(s1) (the flags byte); 0x823e8 bnez -> 0x82834 (slow,
             back at 0x823ec); 0x823ec lw a1,0(a0) = ent[v].type; 0x823f0 li a2,6; 0x823f4 ld s10,0x38(s1) (F);
             0x823f8 ld s6,0x140(s1) (pp); 0x823fc beq a1,a2 -> 0x8247c (Float); 0x82400 li a2,4; 0x82404 bne -> MAL
     Int:   0x82408 a1 := a7 + s7; 0x8240c .. 0x82414 SHADOW load (slow 0x82930); 0x8241c lw a0,4(a0) = size;
            0x82424 bltu a0,4 -> MAL; 0x82428 s7 := s6 + s7; 0x8242c ld a0,0x120(s1) (0x4018); 0x82430 .. 0x82440
            a0 := s7 + 0x4018 + 4 and its SHADOW load (slow 0x829fc); 0x82448 .. 0x82450 a0 := s7 + 0x401c;
            0x82454 lw a2,0(a0) = the body word; 0x82458 j 0x824dc
     Float: 0x8247c .. 0x82488 the size's SHADOW load (slow 0x82944); 0x82490 lw a0,4(a0) = size;
            0x82498 bltu a0,4 -> MAL; 0x8249c .. 0x824b4 the body's SHADOW load (slow 0x82a0c); 0x824bc .. 0x824c4
            a0 := s7 + 0x401c; 0x824c8 flw fa0,0(a0); 0x824cc a0 := s1 + 0x178; 0x824d0 jal pod_nearest,
            ra = 0x824d4; 0x824d4 beqz a0 -> MAL; 0x824d8 ld a2,0x178(s1)
     0x824dc li a0,2; 0x824e0 bgeu a2,a0 -> MAL; 0x824e4 lw a1,0(s4) (the role cell, no check: a constant offset in
            the frame for locals); 0x824e8 sext.w a2,a2; 0x824ec mv a0,s9; 0x824f0 jal check_role, ra = 0x824f4;
            0x824f4 j T
     ABS   0x8245c lw a1,0(s4); 0x82460 ld s9,0x158(s1) (rc = 0); 0x82464 mv a0,s9; 0x82468 jal check_absent,
            ra = 0x8246c; 0x8246c ld s10,0x38(s1); 0x82470 ld s6,0x140(s1); 0x82474 ld s8,0x40(s1); 0x82478 j T
     MAL   0x824f8 lw a1,0(s4); 0x824fc mv a0,s9; 0x82500 jal check_malformed (ra = T)
   The five instrumented checks of this half (0x823e0, 0x82414, 0x82440, 0x82488, 0x824b4) are 4-byte loads inside
   the first block, which the allocator's law marks usable to its last byte; each has the NE-SLOW form, and its slow
   block (0x82834, 0x82930, 0x829fc, 0x82944, 0x82a0c: andi, addi, `blt` back to the fast path, the report call) is
   in the table. The reads of the role cell (0x824e4, 0x8245c, 0x824f8) carry no check. The three trap branches of
   the half are 0x82374, 0x823c8 and 0x823d0.

   THE CUTS ARE lib/AU/RPgSeg.v's. Every cut of this half (rs_cut_KM, rs_cut_ABS, rs_cut_MAL, rs_cut_T, rs_cut_C4,
   and rs_cut_O on the mismatch arm) and every piece statement (rs_piece_W11b_key_stmt / _checks_stmt / _tail_stmt)
   is stated there; this file states none. What it gives the walk files:
   - the code table m2_tbl (123 words in four runs) and the engine's shadow base M2_Bx = the register s11;
   - m2_stack: the stack facts of rs_pre (sp = R at the segment's start, R's bounds, the callees' window);
   - m2_frameF: the frame for locals F (32-aligned, below the allocator's ceiling, outside the image); m2_pp: the
     first block (above 4096, below the allocator's ceiling, outside the image);
   - m2_entry and the regions m2_frame (the real frame at s1 = R) and m2_rcell (the role cell at s4 = F + 0x2a0),
     with their region_ok lemmas; m2_facts (atom 9 = R in [2^46, 2^47], 16-aligned); m2_awr / m2_kwr (the write
     windows of the real frame lie in the journal's stack window / in real-frame runs);
   - m2_pre_call (rs_core at a call state gives a callee contract's rl_pre) and m2_core_call (a callee's rl_post
     gives rs_core at the returned state), m2_core_step (rs_core across a run of the engine);
   - m2_keep_img and m2_rom_at (rom_view at a cut, which pod_nearest's contract asks);
   - m2_strs: the strings, the five doubles and the refuse_code table of RPgSiteA.role_B_site_strs, at a cut, and
     m2_key_at: the harness's key at 0x20f20 as rl_cstr at a cut, which the strcmp wrapper's contract asks.
   The callee contracts themselves are the theorems of lib/AU/RPgCheck.v, RPgCheckStr.v, RPgRefuse.v,
   RPgCfgChanges.v, RPgCfgApply.v and RPgNearA.v; this file assumes nothing beyond MTL and LAWS. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSiteA RPgSeg RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCheck RPgCheckStr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the image ======================================= *)
Definition M2_KM : Z := 0x82370.
Definition M2_KV : Z := 0x823d8.
Definition M2_ABS : Z := 0x8245c.
Definition M2_MAL : Z := 0x824f8.
Definition M2_T : Z := 0x82504.
Definition M2_C4 : Z := 0x82570.
Definition M2_O : Z := 0x82278.
(* the callees of this half, and the key literal the harness compares with *)
Definition M2_STRCMP : Z := 0x41b68.        (* the strcmp wrapper's 4-byte jump *)
Definition M2_A_ABSENT : Z := 0x82a80.
Definition M2_A_ROLE : Z := 0x82aac.
Definition M2_A_MALFORMED : Z := 0x82ad8.
Definition M2_A_ANSWER : Z := 0x82b08.
Definition M2_A_CODE : Z := 0x82b5c.
Definition M2_A_NEAREST : Z := 0x82eb4.
Definition M2_A_REFUSE : Z := 0x8309c.
Definition M2_A_CHANGES : Z := 0x83108.
Definition M2_A_APPLY : Z := 0x83114.
Definition M2_KEY : Z := 0x20f20.           (* .str.3 "reac.cfg.role", the harness's own literal *)
Definition M2_LIT_APPLIED : Z := 0x214c0.
Definition M2_LIT_PENDING : Z := 0x21480.
Definition M2_LIT_NONE : Z := 0x214e0.
Definition M2_LIT_MALFORMED : Z := 0x21500.
Definition M2_TBL_CODES : Z := 0x9a920.     (* reac_role_refuse_code.codes *)
Definition M2_CODE_NONE : Z := 0x21540.
Definition M2_CODE_MALFORMED : Z := 0x21560.
(* the offset of the role cell in the frame for locals; the lowest real-frame cell the key compare spills to (t3 at
   0x128, t2 0x130, t1 0x138, t0 0x148, a7 0x150); the flag cell, which is also pod_nearest's out cell *)
Definition M2_ROLE : Z := 0x2a0.
Definition M2_SPILL_LO : Z := 0x128.
Definition M2_OUT : Z := 0x178.

(* The 123 4-byte words the half's run reads: 101 from the key compare to the malformed check's call (0x82370 ..
   0x82500, the two readers and the join inside), and the three runs of slow blocks of its five instrumented checks
   (0x82834 .. 0x82840, 0x82930 .. 0x82954 which holds two of them, 0x829fc .. 0x82a18 which holds the other two),
   each slow block to its report call. The end pcs O 0x82278 and T 0x82504 lie outside it, as the engine's stop pcs
   may. *)
Definition m2_tbl : ctable :=
  Eval vm_compute in
  (build_table rsegs M2_KM 101
    (build_table rsegs 0x82834 4
      (build_table rsegs 0x82930 10
        (build_table rsegs 0x829fc 8 TEmpty)))).
Lemma m2_tbl_eq : m2_tbl =
  build_table rsegs M2_KM 101
    (build_table rsegs 0x82834 4
      (build_table rsegs 0x82930 10
        (build_table rsegs 0x829fc 8 TEmpty))).
Proof. vm_cast_no_check (eq_refl m2_tbl). Qed.
Lemma m2_tbl_ok : table_ok rsegs m2_tbl.
Proof.
rewrite m2_tbl_eq.
apply build_table_ok; [unfold M2_KM; lia|].
apply build_table_ok; [lia|].
apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.
Lemma m2_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma m2_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* the shadow base: the code adds s11 (atom 27) to every shadow index, so the engine's base is that register *)
Definition M2_SB : Z := 0x7fff8000.
Definition M2_Bx : sv := SOff 27 0.
Definition M2_Bspan : Z * Z := (M2_SB, M2_SB + 2 ^ 44 - 1).

(* ======================================= the image's ranges ======================================= *)
(* The two image segments the callees' strings, doubles and table lie in ([0x10000, 0x2f000) inside the read-only
   segment [0x10000, 0x2f6ac), [0x9a400, 0x9b000) inside the relro segment from 0x9a388) and their shadow bytes: no
   byte of this zone is in M02's write set or in the callees' stack (m2_szone_ok). *)
Definition m2_szone (a : Z) : Prop :=
(0x10000 <= a < 0x2f000) \/ (0x9a400 <= a < 0x9b000) \/
(SHADOW_OFF + 0x2000 <= a < SHADOW_OFF + 0x5e00) \/ (SHADOW_OFF + 0x13480 <= a < SHADOW_OFF + 0x13600).

Lemma m2_img_zone : forall a, (0x10000 <= a < 0x2f000) \/ (0x9a400 <= a < 0x9b000) -> in_img rsegs a.
Proof.
intros a Ha. destruct Ha as [Ha|Ha].
- assert (H1 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x10000) &&
    (0x2f000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
  apply existsb_exists in H1. destruct H1 as (sg & Hin & Hb).
  apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  exists sg. split; [exact Hin | lia].
- assert (H2 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x9a400) &&
    (0x9b000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
  apply existsb_exists in H2. destruct H2 as (sg & Hin & Hb).
  apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  exists sg. split; [exact Hin | lia].
Qed.

(* reac_role_refuse_code's table [0x9a920, 0x9a930) is in the image (rl_refuse_code_specX's premise) *)
Lemma m2_tbl_img : forall i, 0 <= i < 16 -> in_img rsegs (0x9a920 + i).
Proof. intros i Hi. apply m2_img_zone. right. lia. Qed.

(* ---- the run tactics: aj_run_tok / aj_run_to_tok over this half's table, srr_branch_tok at a branch ---- *)
(* the write-range obligation: read-only regions, and the real frame (atom 9 = R) whose window lies in the
   journal's stack window [sp0 - STK, sp0); E9 : bv_unsigned (ew E 9) = R, and the two window facts in context *)
Ltac m2_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|])
| lazymatch goal with E9 : bv_unsigned (ew E 9) = ?R |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ]
end.
(* every write window of the state lies in a run of real-frame cells that lia bounds from E9 *)
Ltac m2_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with E9 : bv_unsigned (ew _ 9) = _ |- _ => rewrite E9 in Hb end; lia | lia ] | ]);
destruct Hr.
Ltac m2_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok m2_tbl_ok HS HJ SHOK M2_Bspan; [awr | ] end.
Ltac m2_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok m2_tbl_ok HS HJ SHOK M2_Bspan stop; [awr | ] end.
Ltac m2_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok m2_tbl_ok HS SH M2_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac m2_io := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_ck]; m2_io].

(* ======================================= the callee-saved registers across a cut ======================================= *)
(* cs_eq and its lemmas are lib/AU/RPgCheckStr.v's *)
Lemma m2_sp_of_cs : forall L r1 r2, In (2%bv : bv 5) L -> cs_eq L r1 r2 -> spZ r2 = spZ r1.
Proof. intros L r1 r2 Hin H. unfold spZ. rewrite (H 2%bv Hin). reflexivity. Qed.
Lemma m2_sp_pres : forall r1 r2, aregs_preserved r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. unfold spZ. f_equal. exact (H 2 ltac:(unfold acallee_saved; lia)). Qed.
Lemma m2_ereg : forall regs extra (n : nat), (n < 32)%nat -> ew (Ereg regs extra) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs extra n Hn. apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma m2_w64_mod : forall x, w64 (x mod 2 ^ 64) = w64 x.
Proof.
intros x. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a string of the zone whose bytes and shadow bytes read the same in another world and memory is the same string
   there [RPgCheckStr.v rl_cstr_kept, with two worlds] *)
Lemma m2_cstr_kept : forall H H' (m m' : word -> option byte) a s,
(forall x, m2_szone x -> aview rsegs H' m' x = aview rsegs H m x) ->
0x10000 <= a -> a + Z.of_nat (length s) < 0x2f000 ->
rl_cstr rsegs H m a s -> rl_cstr rsegs H' m' a s.
Proof.
intros H H' m m' a s HK Ha Hb (Hc & Hn & Hf & Ha0 & Hhi & Himg & Ham & Hra & Hhv).
assert (Kx : forall x, 0x10000 <= x < 0x2f000 -> aview rsegs H' m' x = aview rsegs H m x)
by (intros x Hx; apply HK; left; exact Hx).
assert (Ks : forall x, 0x10000 <= x < 0x2f000 ->
  aview rsegs H' m' (shadow_of_addr SHADOW_OFF x) = aview rsegs H m (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. apply HK. right. right. left. unfold shadow_of_addr.
  assert (0x2000 <= x / 8 < 0x5e00) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia. }
split; [intros i Hi; rewrite Kx by lia; exact (Hc i Hi)|].
split; [rewrite Kx by lia; exact Hn|].
split; [exact Hf|]. split; [exact Ha0|]. split; [exact Hhi|]. split; [exact Himg|]. split; [exact Ham|].
split.
- intros x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok]. rewrite Ks by lia. exact Hsv.
- intros t Ht. rewrite (HK t); [exact (Hhv t Ht)|]. right. right. left.
  unfold shadow_addr, SHADOW_OFF in Ht |- *.
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Ht by lia.
  assert (L1 : 0x2000 <= a / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (a + Z.of_nat (length s)) / 8 <= 0x5dff) by (apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia).
  assert (L3 : (0x7fff8000 + 0x2000) / 8 <= (0x7fff8000 + a / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (L4 : (0x7fff8000 + (a + Z.of_nat (length s)) / 8) / 8 <= (0x7fff8000 + 0x5dff) / 8)
  by (apply Z.div_le_mono; lia).
  change ((0x7fff8000 + 0x2000) / 8) with 268432384 in L3.
  change ((0x7fff8000 + 0x5dff) / 8) with 268434367 in L4.
  lia.
Qed.

(* the entry state of a run of this half at pc: the registers as atoms with the overrides ov (register, value it
   already has), the regions rs, the facts G [RPgCheck.v ck_entry, with the regions and facts as arguments] *)
Lemma m2_entry : forall pc ov rs G (W : world rsegs) regs2 extra mem2,
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 extra) (snd p) = getr regs2 (fst p)) ov ->
regions_wf rs = true ->
Forall (region_ok rsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2)) rs ->
pairwise_disjoint (Ereg regs2 extra) rs ->
facts_ok (Ereg regs2 extra) G ->
st_ok rsegs (Ereg regs2 extra) (mkSS pc (ck_sr ov) rs None G)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs))).
Proof.
intros pc ov rs G W regs2 extra mem2 Hov Hwf Hrs Hpd HG.
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); try assumption. apply ck_regs_ok. exact Hov.
Qed.

(* ---- the regions ---- *)
(* the real frame at s1 = R (atom 9): [R + lo, R + hi) known, [R + wlo, R + whi) writable, the chunks cs *)
Definition m2_frame (lo hi wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo hi wlo whi cs.
(* the role cell at s4 = F + 0x2a0 (atom 20): 4 bytes, read only *)
Definition m2_rcell (v : sv) : YP09.region := YP09.mkRegion (Some 20%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 v)].

Lemma m2_frame_ok : forall E (W : world rsegs) mem2 R STK sp0 lo hi wlo whi cs,
bv_unsigned (ew E 9) = R -> 0 <= R + lo -> R + hi <= 2 ^ 64 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a) ->
(wlo < whi -> sp0 - STK <= R + wlo /\ R + whi <= sp0) ->
Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W) mem2) R) cs ->
region_ok rsegs E (mrestrict (w_H W) mem2) (m2_frame lo hi wlo whi cs).
Proof.
intros E W mem2 R STK sp0 lo hi wlo whi cs H9 Hlo Hhi Hpres Hwin Hcs.
apply (rm_rw_region rsegs E (w_H W) mem2 9 R lo hi wlo whi cs H9 Hlo Hhi); [|exact Hcs].
intros o Ho. apply Hpres. destruct (Hwin ltac:(lia)). lia.
Qed.

Lemma m2_rcell_ok : forall E (W : world rsegs) mem2 F v z,
bv_unsigned (ew E 20) = F + 0x2a0 -> 0 <= F -> F + 0x2a4 <= 2 ^ 64 ->
sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x2a0) 4 z ->
region_ok rsegs E (mrestrict (w_H W) mem2) (m2_rcell v).
Proof.
intros E W mem2 F v z H20 HF0 HF1 Hv Hz Hval.
apply (rm_ro_region rsegs E (w_H W) mem2 20 (F + 0x2a0) 0 4); [exact H20 | lia | lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val rsegs E _ (F + 0x2a0) 0 4 v z Hv); [exact Hz | cbn; lia |].
rewrite Z.add_0_r. exact Hval.
Qed.

(* the facts: atom 9 (R) in [2^46, 2^47], 16-aligned *)
Definition m2_facts : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Lemma m2_facts_ok : forall E R, bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
facts_ok E m2_facts.
Proof.
intros E R H9 HR Hal. split; [|split; [exact I | exact I]]. cbn [m2_facts f_atoms atoms_ok]. unfold afact_ok.
cbn [af_lo af_hi af_al2]. rewrite H9. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================================= rs_pre's stack and frame facts ======================================= *)
Lemma m2_stack : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) mod 16 = 0 /\
e_R (x_e rsegs cx) + 0x200 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= e_R (x_e rsegs cx) - T_SEG_STK /\
alloc_ceiling <= e_R (x_e rsegs cx) - T_SEG_STK /\
2 ^ 46 <= e_R (x_e rsegs cx) <= 2 ^ 47 /\ x_sp0 rsegs cx <= 2 ^ 47 /\ x_sp0 rsegs cx mod 16 = 0 /\
st_nev (x_S rsegs cx) + x_k rsegs cx <= EV_MAX /\
getr (x_regs rsegs cx) 3 = w64 (as_gp B) /\ getr (x_regs rsegs cx) 4 = w64 (as_tp B).
Proof.
intros cx Hpre. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
cbn [hi_rsz role_himg_B] in Hrsz. rewrite HS in Hrsz.
unfold T_SEG_STK, ASTACK in *.
assert (HR : spZ (x_regs rsegs cx) = e_R (x_e rsegs cx))
by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
repeat split; first [assumption | lia].
Qed.

(* the frame for locals F = e_F: the side-stack frame (class 4) the harness holds, 32-aligned, above 4096, below
   the allocator's ceiling, and none of its 1024 bytes in the image *)
Lemma m2_frameF : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
e_F (x_e rsegs cx) mod 32 = 0 /\ 4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
in_app (e_F (x_e rsegs cx)) 1024 /\
(forall a, e_F (x_e rsegs cx) <= a < e_F (x_e rsegs cx) + 1024 -> ~ in_img rsegs a).
Proof.
intros cx Hpre. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _).
cbn [hi_cid role_himg_B] in Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H32 & Happ & _).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as (H4096 & Hceil). cbn [fst snd] in H4096, Hceil.
change (fs_frame_bytes 4) with 1024 in *.
rewrite HF.
split; [exact H32|]. split; [exact H4096|]. split; [exact Hceil|]. split; [exact Happ|].
intros a Ha. apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR). right. left.
exists 4, (x_pos rsegs cx). split; [exact Hin | change (fs_frame_bytes 4) with 1024; lia].
Qed.

(* the first block: above 4096, below the allocator's ceiling, and none of its bytes in the image *)
Lemma m2_pp : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(forall a, e_pp (x_e rsegs cx) <= a < e_pp (x_e rsegs cx) + Layout.PP_SIZE -> ~ in_img rsegs a).
Proof.
intros cx Hpre.
pose proof Hpre as Hp. unfold rs_pre, rl_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpp & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & H4096 & Hceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hceil.
split; [exact H4096|]. split; [exact Hceil|].
intros a Ha. apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR). left.
exists (e_pp (x_e rsegs cx)), Layout.PP_SIZE. split; [exact Hpp | rewrite Hrq; lia].
Qed.

(* ======================================= what M02 never writes ======================================= *)
(* no byte of the zone is in M02's write set or in the callees' stack below R. M02's write set is image B's five
   ranges hi_w2: the role cell [F+0x2a0, F+0x2a4) and the pod block, both kept out of the image; its shadow granule
   shF+0x54, which is a shadow byte of the zone only when F+0x2a0 is an image address; and the three real-frame runs
   at R >= 2^46. *)
Lemma m2_szone_ok : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, m2_szone a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rs_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a Ha.
pose proof (m2_stack cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2_frameF cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _).
pose proof Hpre as Hpre'. unfold rs_pre, rl_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _ & _ & Pn).
assert (Pimg : forall x, e_pod (x_e rsegs cx) <= x < e_pod (x_e rsegs cx) + req_size (e_len (x_e rsegs cx)) ->
  ~ in_img rsegs x).
{ intros x Hx. apply (al_client_img _ _ LAWS _ _ _ _ _ x HAR). left.
  exists (e_pod (x_e rsegs cx)), (e_len (x_e rsegs cx)). split; [exact Hpod | exact Hx]. }
assert (Hreq : e_len (x_e rsegs cx) <= req_size (e_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e rsegs cx)) 0); lia).
assert (Kimg : forall x, ~ in_img rsegs x -> ~ ((0x10000 <= x < 0x2f000) \/ (0x9a400 <= x < 0x9b000)))
by (intros x Hn Hx; apply Hn; apply m2_img_zone; exact Hx).
assert (F8 : e_F (x_e rsegs cx) = 8 * (e_F (x_e rsegs cx) / 8)).
{ pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
  assert (e_F (x_e rsegs cx) mod 8 = 0) by (rewrite <- (Z.mod_mod_divide _ 32 8) by (exists 4; lia); rewrite F32; reflexivity).
  lia. }
rewrite HR. unfold m2_szone, SHADOW_OFF in Ha. unfold T_SEG_STK, ASTACK.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
split; [lia|]. split; [lia|].
unfold rs_E2, rl_inw. cbn [hi_w2 role_himg_B]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rl_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]].
  + destruct Ha as [Ha|[Ha|Ha]].
    * apply (Kimg a (Fimg a ltac:(lia))). left. exact Ha.
    * apply (Kimg a (Fimg a ltac:(lia))). right. exact Ha.
    * lia.
  + unfold shadow_addr, SHADOW_OFF in Hw.
    destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | lia | |].
    * apply (Kimg (e_F (x_e rsegs cx) + 0x2a0) (Fimg (e_F (x_e rsegs cx) + 0x2a0) ltac:(lia))). left. lia.
    * apply (Kimg (e_F (x_e rsegs cx) + 0x2a0) (Fimg (e_F (x_e rsegs cx) + 0x2a0) ltac:(lia))). right. lia.
  + lia.
  + lia.
  + lia.
- destruct Ha as [Ha|[Ha|Ha]].
  + apply (Kimg a (Pimg a ltac:(lia))). left. exact Ha.
  + apply (Kimg a (Pimg a ltac:(lia))). right. exact Ha.
  + lia.
Qed.

(* A byte of the image is outside the callees' stack and outside M02's write set: the frame-object run of hi_w2 is
   F's bytes and the pod block is the allocator's, both kept out of the image; the shadow byte and the three
   real-frame runs are at or above SHADOW_OFF = kLowMemEnd, which every image byte is below. *)
Lemma m2_keep_img : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, in_img rsegs a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rs_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a Ha.
pose proof (m2_stack cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2_frameF cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (m2_segs_low a Ha) as Hlow. rewrite C5 in Hlow.
pose proof Hpre as Hpre'. unfold rs_pre, rl_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & _).
assert (Pimg : forall x, e_pod (x_e rsegs cx) <= x < e_pod (x_e rsegs cx) + req_size (e_len (x_e rsegs cx)) ->
  ~ in_img rsegs x).
{ intros x Hx. apply (al_client_img _ _ LAWS _ _ _ _ _ x HAR). left.
  exists (e_pod (x_e rsegs cx)), (e_len (x_e rsegs cx)). split; [exact Hpod | exact Hx]. }
assert (Hreq : e_len (x_e rsegs cx) <= req_size (e_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e rsegs cx)) 0); lia).
assert (FS : 0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
rewrite HR. unfold T_SEG_STK, ASTACK.
split; [lia|]. split; [lia|].
unfold rs_E2, rl_inw. cbn [hi_w2 role_himg_B]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rl_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]];
  try (unfold shadow_addr, SHADOW_OFF in Hw; lia);
  apply (Fimg a ltac:(lia)); exact Ha.
- apply (Pimg a ltac:(lia)); exact Ha.
Qed.

(* ======================================= the read-only image at a cut ======================================= *)
(* rom_view, which pod_nearest's contract asks of the memory it is called at: every byte of a read-only segment is
   the image's, and M02 writes no such byte (m2_keep_img). *)
Lemma m2_rom_at : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rom_view rsegs W2 mem2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
pose proof Hpre as Hp. unfold rs_pre, rl_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
intros a Ha.
destruct (m2_keep_img cx Hpre Hpod a ltac:(destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]))
  as (H64 & Hstk & HE).
rewrite (HK a H64 Hstk HE). exact (Hrom a Ha).
Qed.

(* ======================================= the strings at a cut ======================================= *)
(* the premises the callees of this half read, from role_B_site_strs at the segment's start, at a cut's memory *)
Lemma m2_strs : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rl_cstr rsegs (w_H W2) mem2 0x214c0 STR_APPLIED /\ rl_cstr rsegs (w_H W2) mem2 0x21480 STR_PENDING /\
rl_cstr rsegs (w_H W2) mem2 0x215c0 STR_APPLIED /\ rl_cstr rsegs (w_H W2) mem2 0x21580 STR_PENDING /\
rl_cstr rsegs (w_H W2) mem2 0x214e0 STR_NONE /\ rl_cstr rsegs (w_H W2) mem2 0x21500 STR_MALFORMED /\
rl_cstr rsegs (w_H W2) mem2 0x21540 STR_NONE /\ rl_cstr rsegs (w_H W2) mem2 0x21560 STR_MALFORMED /\
rl_cstr rsegs (w_H W2) mem2 0x215e0 (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY) /\
rl_cstr rsegs (w_H W2) mem2 0x20f20 (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY) /\
rl_ro_cells rsegs (w_H W2) mem2
  [(0x10380, 0x3fe0000000000000); (0x103e8, 0xc1e0000000000000); (0x10330, 0x41e0000000000000);
   (0x103f8, 0xc3e0000000000001); (0x10358, 0x43e0000000000000)] /\
val_mem rsegs (mrestrict (w_H W2) mem2) 0x9a920 8 0x21540 /\
val_mem rsegs (mrestrict (w_H W2) mem2) (0x9a920 + 8) 8 0x21560 /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF 0x9a920 16.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
assert (HK : forall x, m2_szone x ->
  aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (m2_szone_ok cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & HKc). exact (HKc x Hx64 Hstk HE). }
pose proof Hpre as Hpre'. unfold rs_pre in Hpre'.
destruct (role_B_site_strs rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre')
as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & SC & ST0 & ST1 & STR).
assert (Kv : forall a n v, (forall k, 0 <= k < Z.of_nat n -> m2_szone (a + k)) ->
  val_mem rsegs (mrestrict (w_H (x_W rsegs cx)) (x_memc rsegs cx)) a n v ->
  val_mem rsegs (mrestrict (w_H W2) mem2) a n v).
{ intros a n v Hz Hv. eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. apply HK. apply Hz. exact Hk. }
rewrite role_B_key_text in S9, S10 |- *.
unfold STR_APPLIED, STR_PENDING, STR_NONE, STR_MALFORMED in *.
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S1]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S2']|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S3]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S4]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S5]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S6]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S7]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S8]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S9]|].
split; [apply (m2_cstr_kept _ _ _ _ _ _ HK); [lia | cbn; lia | exact S10]|].
split.
{ unfold rl_ro_cells in SC |- *. rewrite !Forall_cons_iff in SC. destruct SC as (C1 & C2 & C3 & C4 & C5 & _).
  cbn [fst snd] in C1, C2, C3, C4, C5.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; apply Kv; try assumption;
  intros k Hk; left; cbn in Hk; lia. }
split; [apply Kv; [intros k Hk; right; left; cbn in Hk; lia | exact ST0]|].
split; [apply Kv; [intros k Hk; right; left; cbn in Hk; lia | exact ST1]|].
intros x Hx. destruct (STR x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite HK; [exact Hsv|]. right. right. right. unfold shadow_of_addr, SHADOW_OFF.
assert (0x13524 <= x / 8 < 0x13526) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
lia.
Qed.

(* the harness's own key literal "reac.cfg.role" at 0x20f20, at a cut's memory (m2_strs' tenth premise) *)
Lemma m2_key_at : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rl_cstr rsegs (w_H W2) mem2 M2_KEY (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
destruct (m2_strs cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K & _).
exact K.
Qed.

(* ======================================= the seam with RPgCSpec's callee contracts ======================================= *)
(* rs_core at a call state whose sp is R gives a callee contract's rl_pre, for any callee stack T <= T_SEG_STK *)
Lemma m2_pre_call : forall (cx : rs_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regsT memT mdT T,
rs_pre rsegs B cx -> rs_core rsegs B MT cx E ly2 S2 W2 regsT memT mdT ->
YK0s.ret_ok (getr regsT 1) -> 4096 <= raZ regsT -> spZ regsT = e_R (x_e rsegs cx) -> 0 <= T <= T_SEG_STK ->
rl_pre rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
(x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) T regsT ly2 S2 W2 memT mdT.
Proof.
intros cx E ly2 S2 W2 regsT memT mdT T Hpre (HJ & Hr & _) Hra Hra4 HspT HT.
pose proof (m2_stack cx Hpre) as (HR & Hal & Hrsz & Hwin & _ & _ & _ & _ & Hev & Hgp & Htp).
unfold rl_pre. split; [exact HJ|]. split; [exact Hra|]. split; [exact Hra4|].
split; [transitivity (getr (x_regs rsegs cx) (Z_to_bv 5 3)); [exact (Hr 3 ltac:(lia)) | exact Hgp]|].
split; [transitivity (getr (x_regs rsegs cx) (Z_to_bv 5 4)); [exact (Hr 4 ltac:(lia)) | exact Htp]|].
rewrite HspT. split; [exact Hal|]. split; [lia|]. split; [lia | exact Hev].
Qed.

(* rs_core across a step that keeps sp / gp / tp, the frames, the blocks, the I/O state and the meter, and every
   byte outside the callees' stack and the write set E: a run of the engine, or a call *)
Lemma m2_core_step : forall (cx : rs_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
(x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) -> ~ E a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & Hr & Hfr & Hperm & Hio & Hmo & HK)
HJ3 Hr3 Hfr3 Hperm3 Hio3 Hmo3 HK3.
split; [exact HJ3|].
split; [intros r Hrr; rewrite (Hr3 r Hrr); exact (Hr r Hrr)|].
split; [rewrite Hfr3; exact Hfr|].
split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm]|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3)|].
intros a Ha Hs He. rewrite (HK3 a Ha Hs He). exact (HK a Ha Hs He).
Qed.

(* a callee's rl_post, called with sp = R and a stack T <= T_SEG_STK, gives rs_core at the returned state, the
   callee-saved registers as at the call, every byte outside [R - T, R) and the callee's write set Ec as at the
   call, and the callee's own result *)
Lemma m2_core_call : forall (cx : rs_scx rsegs) (Ec : Z -> Prop) T ly2 S2 W2 regsT memT mdT FX
(Rc : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W3 c3,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regsT memT mdT ->
spZ regsT = e_R (x_e rsegs cx) -> 0 <= T <= T_SEG_STK -> (forall a, Ec a -> rs_E2 rsegs cx a) ->
rl_post rsegs B MT (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
(x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) T regsT ly2 S2 W2 memT mdT FX Ec Rc W3 c3 ->
exists (fx3 : YK11.FPState) ly3 S3 regs3 mem3 md3,
c3 = mkCfg (@mkst fx3 regs3 (getr regsT 1) mem3 (seg_rom rsegs)) md3 /\ FX fx3 /\
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 /\ aregs_preserved regsT regs3 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T <= a < e_R (x_e rsegs cx)) -> ~ Ec a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) memT a) /\
Rc W3 regs3 mem3.
Proof.
intros cx Ec T ly2 S2 W2 regsT memT mdT FX Rc W3 c3 Hpre Hcore HspT HT HEc
(fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HFX & HJ3 & Hpres & Hfr3 & Hperm3 & Hio3 & Hmo3 & HK3 & HR3).
pose proof (m2_stack cx Hpre) as (HR & _).
exists fx3, ly3, S3, regs3, mem3, md3.
split; [exact Hc3|]. split; [exact HFX|].
split.
{ apply (m2_core_step cx (rs_E2 rsegs cx) ly2 S2 W2 regsT memT mdT ly3 S3 W3 regs3 mem3 md3 Hcore HJ3);
  [intros r Hr; apply Hpres; unfold acallee_saved; lia | exact Hfr3 | exact Hperm3 | exact Hio3 | exact Hmo3 |].
  intros a Ha Hs He. apply HK3; [exact Ha | rewrite HspT; rewrite HR in Hs; unfold T_SEG_STK in *; lia |].
  intros Hc. exact (He (HEc a Hc)). }
split; [exact Hpres|].
split; [intros a Ha Hs He; apply HK3; [exact Ha | rewrite HspT; exact Hs | exact He] | exact HR3].
Qed.
End d.
End b.
