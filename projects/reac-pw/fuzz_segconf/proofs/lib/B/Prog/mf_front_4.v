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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 283 of its 335 lines of code are new or changed and 401 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_FRONT of lib/B/Prog/m_file_m.v,
   piece 4 (fr_e): the walk from the point E 0x863c4 (lib/B/Prog/mf_front_m.v FR_E_stmt) to LONG 0x863d4, the strip
   call's set-up ST 0x864b4 and the comment loop's head CL 0x86430 at index 0. A walk lane of the image-B m_file-family owner's
   G2B (a piece worker). No call.

   What the code does (B pc; s5 = line, s10 = p, a0 = p + L with L = |mf_line rest|, a2 = mf_next p rest, s4 = 511):
     0x863c4  `addiw s11,s5,1`       s11 = line + 1 (the executor forms atom 21 + 1: 0 <= line <= 65,534)
     0x863c8  `blt s11,s5,86e84`     the UBSan trap (line + 1 overflows): decided not taken by the executor itself
                                     (decide_cond2 under the fact 0 <= line <= 65,534 on atom 21, added here with
                                     st_ok_pi_add_fact from mf_loop's 0 <= line and line + |rest| <= 65,535, rest <> [])
     0x863cc  `sub a1,a0,s10`        a1 = L
     0x863d0  `bge s4,a1,86420`      not taken (L >= 512): the fall-through 0x863d4 is MF_LONG
     0x86420  `sd a2,152(s1)`        152(s1) = mf_next p rest (fr_short's mf_np)
     0x86424  `bgeu s10,a0,864b4`    taken iff L = 0: FR_ST (168(s1) = p + L = p + fr_C rest, fr_C_le)
     0x86428  `li a3,0`, 0x8642c `mv a1,s10`, then FR_CL at index 0
   The run is the token executor over lib/B/Prog/m_file_sd.v's mf_seed at FR_E, the frame cells' region 1 with the
   write window [152, 160) only; the run's written bytes are inside [s1 + 152, s1 + 160), so m_file_k.v's
   mf_keep_run_s keeps mf_core, mf_cells, mf_loop (fr4_keep) and mf_val_keep the cells 168 / 176; the new 152(s1) is
   the final state's chunk at 152 (atom 12 = a2). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_front_mdl mf_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the state's form, computed *)
Ltac fr4_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* 0x863d0 `bge s4,a1`: s4 = 511 (atom 20), a1 = a0 - s10 as the executor forms it, = L *)
Lemma fr4_bge : forall E p L, ew E 20 = Z_to_bv 64 511 -> ew E 10 = Z_to_bv 64 (p + L) -> ew E 26 = Z_to_bv 64 p ->
  0 <= p -> 0 <= L -> p + L < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SOff 20 0))
    (sv_denot E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 26 0) (SLit (-1))))) = (L <=? 511).
Proof.
intros E p L E20 E10 E26 Hp HL HpL.
assert (U1 : U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 26 0) (SLit (-1)))) = L).
{ rewrite U_SAlu, U_SMd, U_SLit. rewrite (U_atom E 10 (p + L) E10) by lia. rewrite (U_atom E 26 p E26) by lia.
  cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  rewrite Z.add_mod_idemp_r by lia.
  replace (p + L + p * (2 ^ 64 - 1)) with (L + p * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
assert (U20 : U E (SOff 20 0) = 511) by (apply (U_atom E 20 511 E20); lia).
assert (Hs : forall e, 0 <= U E e < 2 ^ 63 -> bv_signed (sv_denot E e) = U E e)
  by (intros e He; apply YK11.bv_signed_small; unfold U in He; lia).
cbn [branch_taken]. rewrite bv_lts_signed.
rewrite (Hs (SOff 20 0)) by (rewrite U20; lia).
rewrite (Hs (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 26 0) (SLit (-1))))) by (rewrite U1; lia).
rewrite U20, U1.
destruct (Z.ltb_spec 511 L) as [H|H]; destruct (Z.leb_spec L 511) as [H'|H']; cbn [negb];
  first [reflexivity | exfalso; lia].
Qed.

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
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the head's facts across a run that writes only [s1 + 152, s1 + 160) (m_file_k.v mf_keep_run_s with that set),
   and the frame cells from 160(s1) on *)
Lemma fr4_keep : forall v lyc Sc (Wc : world SEGS) memc mdc pos mcc cur line p rest mem2 md2,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_loop v Wc memc mcc cur line p rest ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 152 <= a < mf_s1 (mv_sp v) + 160) ->
     rdW Wc mem2 a = rdW Wc memc a) ->
  mf_core B v lyc Sc Wc mem2 md2 pos MF_LOW_OFF mcc /\ mf_cells v lyc pos mem2 Wc cur /\
  mf_loop v Wc mem2 mcc cur line p rest /\
  (forall o x, 160 <= o -> o + 8 <= 216 -> mf_slot v memc Wc o x -> mf_slot v mem2 Wc o x).
Proof.
intros v lyc Sc Wc memc mdc pos mcc cur line p rest mem2 md2 CX CORE CELLS LOOP HJ2 K.
set (RW := fun a => mf_s1 (mv_sp v) + 152 <= a < mf_s1 (mv_sp v) + 160) in K.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (RWok : forall a, RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold mf_rw; unfold RW in Ha; right; right; right; right; right; lia).
assert (RWS : mf_rws v RW) by (intros a Ha _; right; unfold RW in Ha; lia).
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 RW MF_LOW_OFF cur mcc CX CORE CELLS
  HJ2 K RWok RWS) as (C1 & C2 & C3).
- intros i Hi. apply (mf_val_keep Wc Wc memc mem2 RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH i Hi)].
  intros k Hk HR. unfold RW, mf_s1 in HR. change (Z.of_nat 1) with 1 in Hk. unfold SHADOW_OFF in HR. lia.
- apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V136].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. lia.
- apply (mf_mconf_keep Wc Wc memc mem2 RW _ _ K); [lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact Hmc].
  intros a Ha HR. unfold RW, mf_s1 in HR. unfold seg_spec.SEG_M_SIZE in *. lia.
- split; [exact C1|]. split; [exact C2|]. split; [exact (C3 _ _ _ _ _ LOOP)|].
  intros o x Ho1 Ho2 V. unfold mf_slot in V |- *.
  apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. lia.
Qed.

(* the run's write permission: region 1 (base s1, window [152, 160)) is the caller's real stack below sp0, every
   other region read-only *)
Ltac fr4_awr v U2v HSTKv :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  repeat first
    [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
        [ reflexivity | rewrite U2v; ring
        | cbn [YP09.r_wlo YP09.r_whi]; try rewrite HSTKv; unfold mf_s1; lia
        | cbn [YP09.r_wlo YP09.r_whi]; unfold mf_s1; lia |] ];
  apply awr_ok_nil.
(* the reader after a run equals the start reader mc outside [s1 + 152, s1 + 160) (K, updated); the run's frame
   hypotheses and the machine states no hypothesis names any more are dropped, the current one named ms *)
Ltac fr4_k v mc K HS U2v :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m0) (mrestrict _ ?m1) |- _ =>
    let K1 := fresh "K" in
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 152 <= a < mf_s1 (mv_sp v) + 160) ->
      aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mc a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
      intros a Ha Hna; transitivity (aview SEGS (w_H W) m0 a); [|exact (K a Ha Hna)];
      refine (kept_of_frame Ex rs (w_H W) m0 m1 (fun x => mf_s1 (mv_sp v) + 152 <= x < mf_s1 (mv_sp v) + 160)
        HFr _ a Ha Hna);
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hinw := fresh "Hinw" in let Hr := fresh "Hr" in
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw; cbv beta;
      repeat (let Hq := fresh "Hq" in destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U2v in Hr; lia |]); destruct Hinw
    | clear K; rename K1 into K ] end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ =>
    lazymatch type of HS with context [old] => fail | _ => clear old end end;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => try rename msx into ms end.

Lemma fr_e : forall n, MF_LONG_stmt B n -> FR_ST_stmt B n -> (forall i, FR_CL_stmt B n i) -> FR_E_stmt B n.
Proof.
intros n LONG ST CL. unfold FR_E_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX R26 R21 R20 S176 S168 R10 R12 R16.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & MOD).
pose proof CORE as (HJ & _).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & (PA1 & PA2 & _) & Hcurok & _ & Hl0 & Hl1 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Hcurok) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnx.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (fr_line_len rest) as HLL.
assert (Hrl : (1 <= length rest)%nat) by (destruct rest; [congruence | cbn [length]; lia]).
set (L := length (mf_line rest)) in *.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur 0 [] FR_E true false [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur ltac:(intros Hf; discriminate Hf) ltac:(lia)
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur 0 []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = line)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = Z_to_bv 64 511) by (rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (p + Z.of_nat L)) by (rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity).
assert (E26 : ew E 26 = Z_to_bv 64 p) by (rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity).
assert (E12 : ew E 12 = Z_to_bv 64 (mf_next p rest)) by (rewrite (EE 12%nat 12%bv eq_refl), R12; reflexivity).
(* region 1 (the frame cells) written only at [152, 160) *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 152 160) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 152 160 HR1
      ltac:(destruct HR1 as (_ & _ & HW & _); intros o Ho; apply HW; cbv [mf_r_slots YP09.r_wlo YP09.r_whi]; lia))) as HS end.
clear HS0 HR1. fr4_norm HS.
(* the line number's range, the fact that decides the trap branch 0x863c8 *)
apply (st_ok_pi_add_fact E _ _ 21 (mkAF 0 65534 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U21; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
fr4_norm HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 152 <= a < mf_s1 (mv_sp v) + 160) ->
  rdW Wc memc a = rdW Wc memc a) by reflexivity.
unfold mf_at.
(* 0x863c4 .. 0x863cc: s11 = line + 1, the trap 0x863c8 decided not taken, a1 = L; stop at 0x863d0 *)
paj_run_tok RUN HS HJ SHOK Bspan; [fr4_awr v U2 HSTK|].
fr4_k v memc K HS U2.
pose proof (fr4_bge E p (Z.of_nat L) E20 E10 E26 PA1 ltac:(lia) ltac:(lia)) as HGE.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 0x863d0 taken: L <= 511; 0x86420 152(s1) = a2; stop at 0x86424 *)
  rewrite HGE in Hc. apply Z.leb_le in Hc. clear HGE.
  paj_run_tok RUN HS HJ SHOK Bspan; [fr4_awr v U2 HSTK|].
  fr4_k v memc K HS U2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* 0x86424 taken: p + L <= p, so L = 0; to FR_ST *)
    rewrite branch_geu_U, (U_atom E 26 p E26), (U_atom E 10 (p + Z.of_nat L) E10) in Hc0 by lia.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan FR_ST; [fr4_awr v U2 HSTK|].
    fr4_k v memc K HS U2.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (mf_r_slots true false [])) in
      pose proof (st_ok_pi_region_nth E ssx (restrict (w_H Wc) msx) 1 r1 HS eq_refl) as HRf end.
    cbn [ms_mem restrict mkst] in HRf.
    pose proof (field_of_region (segs := SEGS) E _ 2%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 152 8%N (SOff 12 0)
      (mf_next p rest) HRf U2 ltac:(cbn [In]; left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E12)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia))
      as V152.
    change (N.to_nat 8) with 8%nat in V152. clear HRf.
    destruct (fr4_keep v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ CX CORE CELLS LOOP HJ K)
      as (CORE' & CELLS' & LOOP' & SLK).
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
    prreg HS (27%bv : bv 5) Q27. prreg HS (20%bv : bv 5) Q20.
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
    pmkst HS.
    assert (HC0 : fr_C rest = 0%nat) by (pose proof (fr_C_le rest) as HCle; fold L in HCle; lia).
    apply (ST v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest).
    * exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj RA' (conj Hn (conj Hne (conj LOOP' MOD))))))))).
    * split; [rewrite Q27, U21; reflexivity|]. split; [rewrite Q20, E20; reflexivity|].
      split; [exact V152 | fold L; lia].
    * apply (SLK 176 p ltac:(lia) ltac:(lia) S176).
    * rewrite HC0. replace (p + Z.of_nat 0) with (p + Z.of_nat L) by lia. apply (SLK 168 _ ltac:(lia) ltac:(lia) S168).
  + (* 0x86424 not taken: 0 < L; 0x86428 a3 = 0, 0x8642c a1 = s10; to FR_CL at index 0 *)
    rewrite branch_geu_U, (U_atom E 26 p E26), (U_atom E 10 (p + Z.of_nat L) E10) in Hc0 by lia.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan FR_CL; [fr4_awr v U2 HSTK|].
    fr4_k v memc K HS U2.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (mf_r_slots true false [])) in
      pose proof (st_ok_pi_region_nth E ssx (restrict (w_H Wc) msx) 1 r1 HS eq_refl) as HRf end.
    cbn [ms_mem restrict mkst] in HRf.
    pose proof (field_of_region (segs := SEGS) E _ 2%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 152 8%N (SOff 12 0)
      (mf_next p rest) HRf U2 ltac:(cbn [In]; left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E12)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia))
      as V152.
    change (N.to_nat 8) with 8%nat in V152. clear HRf.
    destruct (fr4_keep v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ CX CORE CELLS LOOP HJ K)
      as (CORE' & CELLS' & LOOP' & SLK).
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
    prreg HS (27%bv : bv 5) Q27. prreg HS (20%bv : bv 5) Q20.
    prreg HS (10%bv : bv 5) Q10. prreg HS (16%bv : bv 5) Q16. prreg HS (26%bv : bv 5) Q26.
    prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13.
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
    pmkst HS.
    apply (CL 0%nat v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest).
    * exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj RA' (conj Hn (conj Hne (conj LOOP' MOD))))))))).
    * split; [rewrite Q27, U21; reflexivity|]. split; [rewrite Q20, E20; reflexivity|].
      split; [exact V152 | fold L; lia].
    * apply (SLK 176 p ltac:(lia) ltac:(lia) S176).
    * apply (SLK 168 _ ltac:(lia) ltac:(lia) S168).
    * rewrite Q10, E10. reflexivity.
    * rewrite Q16, (EE 16%nat 16%bv eq_refl). exact R16.
    * rewrite Q26, E26, Z.add_0_r. reflexivity.
    * rewrite Q11, E26, Z.add_0_r. reflexivity.
    * rewrite Q13. reflexivity.
    * fold L. lia.
    * intros k Hk. lia.
- (* 0x863d0 not taken: 512 <= L; the fall-through 0x863d4 is MF_LONG *)
  rewrite HGE in Hc. apply Z.leb_gt in Hc. clear HGE.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_LONG; [fr4_awr v U2 HSTK|].
  fr4_k v memc K HS U2.
  destruct (fr4_keep v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ CX CORE CELLS LOOP HJ K)
    as (CORE' & CELLS' & LOOP' & _).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
  prreg HS (27%bv : bv 5) Q27. prreg HS (20%bv : bv 5) Q20.
  prreg HS (10%bv : bv 5) Q10. prreg HS (16%bv : bv 5) Q16. prreg HS (26%bv : bv 5) Q26.
  prreg HS (12%bv : bv 5) Q12.
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
  pmkst HS.
  apply (LONG v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest CX LS FRM CORE' CELLS' RA' Hn Hne LOOP'
    ltac:(fold L; lia) (fr_eq_long (mcc, cur) line rest (mf_final v) Hne MOD)).
  + rewrite Q26, E26. reflexivity.
  + rewrite Q10, E10. reflexivity.
  + rewrite Q12, E12. reflexivity.
  + rewrite Q16, (EE 16%nat 16%bv eq_refl). exact R16.
  + rewrite Q27, U21. reflexivity.
  + rewrite Q20, E20. reflexivity.
Qed.
End e.
End f.
End d.

(* inside nothing: the lemma's assumptions *)
About fr_e.
Print Assumptions fr_e.
