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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 218 of its 265 lines of code are new or changed and 406 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): the segment S_MF_TAIL of its walk, 13
   instructions from the cut TAIL 0x86820 (the image-B m_file segment table section 12, the image-B m_file cut map section 4).
   A walk lane of the image-B m_file-family owner's G2B. Adapted from image A's lib/A/Prog/m_file_s_tail.v mf_tail_at (the image-A m_file-family lane,
   commit ba33778143e7) at image B's numbers. No call, no UBSan trap.

   What the code does (B pc), with p = s10 (image A: a7):
     0x86820-0x8682c  the instrumented check of *p (a load of the shadow byte at (p >> 3) + s2 and a compare; the
                      slow path 0x86c48-0x86c50 and the error path 0x86ee0-0x86ee4, a call of errpath_load1, are not
                      reached: the token run turns the check into the obligation `p is addressable', which mf_loop's
                      sa_addr gives)
     0x86830          `lbu a0,0(s10)`
     0x86834          s5 = s11 (the lines consumed: HEAD's s5)
     0x86838          `bnez a0` back to HEAD 0x86378
     0x8683c          `j` EXIT 0x86da0
   *p is the first byte of the text left (mf_loop_hd): 0 exactly when the text left is empty, and then the
   block holds the final model (the line list of [] is [], mf_lines_nil). The run writes no byte: every region
   of its state is read-only, so the cut facts hold at the new memory (mf_carry_eq).
   The seed is lib/B/Prog/m_file_sd.v's mf_seed (written by a walk lane); the frame cells' region is made read-only here
   (ast_ok_pi_set_region, as fuzz_command's check_reply_s7.v cr7_seed does with its frame header); the keep facts are
   the shared lib/B/Prog/m_file_k.v (commit 84ea19e46fcc). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac mft_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac mft_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

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
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* S_MF_TAIL at one FP state *)
Lemma mf_tail_at : forall n, MF_HEAD_stmt B n -> MF_EXIT_stmt B -> MF_TAIL_stmt B n.
Proof.
intros n HEAD EXIT. unfold MF_TAIL_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA Hn LOOP MOD R26 R27 R20.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & Btapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bt mt 1 pos HAR Hbt Hin) as Hsep.
change (fs_frame_bytes 1) with 128 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & (PA1 & PA2 & PA3 & PRA & _) & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Hcurok) as Hcur.
destruct (mf_loop_hd v Wc memc mcc cur line p rest LOOP) as (Hp & Hrest).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold in_app in Btapp. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Btapp.
assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
destruct rest as [|b rest'].
- (* the text left is empty: *p = 0, the tail goes to EXIT *)
  cbn [hd0] in Hp.
  pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur 0 [] MF_TAIL true false [] false false
    [] false CX CORE RB (fun _ => CELLS) Hcur ltac:(intros Hf; discriminate Hf) ltac:(lia)
    ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
  remember (mfE regs1 v lyc pos cur 0 []) as E eqn:HE.
  assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
    by (subst E; intros; apply mfE_reg; assumption).
  assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur 0 []) (Z_to_bv 64 0))
    by (subst E; intros; apply mfE_extra; assumption).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
  clear HE.
  pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
  pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
  cbn [Nat.add nth mf_extra map app] in E32, E34, E36.
  assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
    by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
    by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = p)
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
    by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
  assert (UP : U E (SOff 26 0) = p) by (apply (U_atom E 26 p); [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia]).
  (* the frame cells read-only *)
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
  lazymatch type of HR1 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
  clear HS0 HR1. mft_norm HS1.
  (* p, the cursor in s10, is a heap pointer (the fact the token run's obligation needs) *)
  apply (st_ok_pi_add_fact E _ _ 26 (HPTR 0)) in HS1;
    [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U26; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  mft_norm HS1.
  (* the byte at p *)
  assert (HS2 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS1
    ltac:(vm_compute; reflexivity)).
  clear HS1.
  lapply HS2; clear HS2; [intros HS2|].
  2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. cbn [restrict ms_mem mkst].
      exact (mf_val1_of_aview (w_H Wc) memc p 0 Hp). }
  lapply HS2; clear HS2; [intros HS2|].
  2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U26, ?U2, ?U8, ?U34, ?U36.
      unfold mf_s1, SHADOW_OFF in *. repeat split; first [exact I | lia]. }
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
  unfold mf_at.
  paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_EXIT.
  { rewrite UP. eapply (obl_of_range SEGS _ _ E (SOff 32 0) p 1 p _ PRA UB); cbn [length Z.of_nat]; lia. }
  { mft_awr_ro. }
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_OFF mcc mcc cur line p [] CX CORE HJ K0
    LOOP) as (CORE' & _ & _ & _).
  rewrite mf_lines_nil in MOD. cbn [fst] in MOD. rewrite MOD in CORE'.
  prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
  prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
  assert (RX' : mf_regs_ex B v lyc pos (ms_regs ms)).
  { apply (mf_regs_ex_of B v lyc pos regs1 (ms_regs ms) (proj1 RA)).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q23. apply EE. reflexivity.
    - rewrite Q24. apply EE. reflexivity. }
  pmkst HS2.
  apply (EXIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos CX LS CORE' RX').
- (* the text left is not empty: *p = its first byte, nonzero; the tail goes back to HEAD *)
  cbn [hd0] in Hp.
  assert (Hb0 : b <> 0) by (intros Hb; apply (proj2 Hrest) in Hb; discriminate Hb).
  destruct (aview_byte SEGS (w_H Wc) memc p b Hp) as (bb & _ & _ & Hb256).
  pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur 0 [b] MF_TAIL true false [] false false
    [] false CX CORE RB (fun _ => CELLS) Hcur ltac:(intros Hf; discriminate Hf) ltac:(lia)
    ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
  remember (mfE regs1 v lyc pos cur 0 [b]) as E eqn:HE.
  assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
    by (subst E; intros; apply mfE_reg; assumption).
  assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur 0 [b]) (Z_to_bv 64 0))
    by (subst E; intros; apply mfE_extra; assumption).
  assert (E52 : ew E 52 = Z_to_bv 64 b) by (subst E; exact (mfE_xs regs1 v lyc pos cur 0 [b] 0 ltac:(unfold A_TEXT; lia))).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
  clear HE.
  pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
  pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
  cbn [Nat.add nth mf_extra map app] in E32, E34, E36.
  assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
    by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
    by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = p)
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
    by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U52 : bv_unsigned (ew E 52) = b) by (rewrite E52; apply unsigned_lit_small; lia).
  assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
  assert (UP : U E (SOff 26 0) = p) by (apply (U_atom E 26 p); [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia]).
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
  lazymatch type of HR1 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
  clear HS0 HR1. mft_norm HS1.
  (* the byte's atom 52 is in [1, 255] *)
  pose proof (st_ok_pi_add_fact E _ _ 52 (mkAF 1 255 0) HS1) as HS1'.
  lapply HS1'; clear HS1'; [intros HS1'|].
  2:{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U52. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
  clear HS1. mft_norm HS1'.
  apply (st_ok_pi_add_fact E _ _ 26 (HPTR 0)) in HS1';
    [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U26; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  mft_norm HS1'.
  assert (HS2 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))])
    HS1' ltac:(vm_compute; reflexivity)).
  clear HS1'.
  lapply HS2; clear HS2; [intros HS2|].
  2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SOff 52 0) b);
        [cbn [sv_denot]; rewrite E52, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. cbn [restrict ms_mem mkst].
      exact (mf_val1_of_aview (w_H Wc) memc p b Hp). }
  lapply HS2; clear HS2; [intros HS2|].
  2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U26, ?U2, ?U8, ?U34, ?U36.
      unfold mf_s1, SHADOW_OFF in *. repeat split; first [exact I | lia]. }
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
  unfold mf_at.
  paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_HEAD.
  { rewrite UP. eapply (obl_of_range SEGS _ _ E (SOff 32 0) p 1 p _ PRA UB); cbn [length Z.of_nat]; lia. }
  { mft_awr_ro. }
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
      intros bb' wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_OFF mcc mcc cur line p (b :: rest') CX
    CORE HJ K0 LOOP) as (CORE' & LOOP' & CELLSf & _).
  prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
  prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
  prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (25%bv : bv 5) Q25.
  prreg HS2 (26%bv : bv 5) Q26. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (20%bv : bv 5) Q20.
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q23. apply EE. reflexivity.
    - rewrite Q24. apply EE. reflexivity.
    - rewrite Q19. apply EE. reflexivity.
    - rewrite Q22. apply EE. reflexivity.
    - rewrite Q25. apply EE. reflexivity. }
  pmkst HS2.
  apply (HEAD v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p (b :: rest') CX LS FRM CORE' (CELLSf cur CELLS)
    RA' Hn ltac:(discriminate) LOOP' MOD).
  + rewrite Q26, (EE 26%nat 26%bv eq_refl). exact R26.
  + rewrite Q21, (EE 27%nat 27%bv eq_refl). exact R27.
  + rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
Qed.
End e.
End f.
End d.

(* the segment at every FP state (m_file_m.v's S_MF_TAIL shape) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Lemma S_MF_TAIL_ok : S_MF_TAIL (rc := rc) (SK := SK) (PI := PI) B.
Proof. intros n HEAD EXIT fx0. exact (mf_tail_at (fx := fx0) B VOBJS n (HEAD fx0) (EXIT fx0)). Qed.
(* inside the Sections: the segment's hypotheses as its assumptions *)
About S_MF_TAIL_ok. Print Assumptions S_MF_TAIL_ok.
End i.
End h.
End g.
About S_MF_TAIL_ok. Print Assumptions S_MF_TAIL_ok.
