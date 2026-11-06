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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 315 of its 363 lines of code are new or changed and 405 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): piece 7 (fr_sr) of the segment S_MF_FRONT
   of its walk (HEAD 0x86378 -> LONG / HDR / KEY / TAIL; the image-B m_file segment table section 2), from the point
   FR_SR 0x864c4 of lib/B/Prog/mf_front_m.v (back from strip(s1 + 176, s1 + 168) 0x864c0) to the cuts TAIL 0x86820,
   HDR 0x864f4 and KEY 0x8661c of lib/B/Prog/m_file_m.v. A walk lane of the image-B m_file-family owner's G2B (a piece
   worker). No call. Templates: image B's lib/B/Prog/mf_tail.v (commit
   cfabffb32905: the seed, the read-only frame cells, the byte region, the token run, mf_carry_eq) and image A's
   lib/A/Prog/m_file_s_front_cl.v (a working branch: runs and symbolic branches in turn, the reader kept
   across the runs).

   What the code does (B pc; the neutral listing of m_file in image B lines 227-238,
   426-428, 711-713, 851, 876-877), with p the text left, the line L = mf_line rest and strip's answer
   slice i0 j0 L = h_strip (fr_cut rest):
     0x864c4  `ld s10,176(s1)`     s10 = p + i0 (176(s1), strip's first cell)
     0x864c8  `ld s4,168(s1)`      s4 = p + j0 (168(s1), strip's second cell)
     0x864cc  `beq s10,s4,867e0`   taken exactly when i0 = j0: the stripped line is empty (fr_slice_len_nil); the
                                   join 0x867e0 `li s4,511`, 0x867e4 `ld s10,152(s1)` (the next line's address,
                                   fr_short's mf_np), 0x867e8 `j` TAIL with line + 1 in s11; the model steps over
                                   the line unchanged (mf_front_mdl.v fr_eq_empty), mf_loop to the next line
                                   (m_file_k.v mf_loop_next)
     0x864d0  `beqz s10,86e84`     the UBSan trap (null pointer): not taken, s10 = p + i0 >= 4096 (the atom's
                                   fact HPTR 0, from the text's live heap block; the executor decides the branch)
     0x864d4-0x864e0               the instrumented check of the byte at p + i0 (a load of the shadow byte at
                                   ((p + i0) >> 3) + the shadow base and a compare; the slow path 0x86c54-0x86c5c and
                                   the error path 0x86ee8-0x86eec, a call of errpath_load1, are not reached: the token
                                   run turns the check into the obligation `p + i0 is addressable', which mf_loop's
                                   sa_addr of [p, p + |rest| + 1) gives, i0 < j0 <= |L| <= |rest|)
     0x864e4  `lbu a0,0(s10)`      a0 = nth i0 L 0 (a one-byte text region at p + i0, m_file_sd.v mf_txt_region)
     0x864e8  `sub a2,s4,s10`      a2 = j0 - i0
     0x864ec  `li a1,91`
     0x864f0  `bne a0,a1,8661c`    taken: the first byte is not '[', KEY (fr_eq_key); not taken: HDR 0x864f4
                                   (fr_eq_hdr); the first byte of the stripped line is nth i0 L 0 (fr_hd_slice)
   The piece stores nothing: every region of its states is read-only, so the reader is the same byte for byte at
   each exit and m_file_k.v's mf_carry_eq carries the cut facts (mf_core, mf_loop, mf_cells, mf_np).

   POSITIONAL NAMES, each checked against image B's listing and m_file_sd.v's seed: the frame cells 176(s1) and
   168(s1) (B.s lines 227-228 `ld s10,176(s1)` / `ld s4,168(s1)` at 0x864c4 / 0x864c8, strip's two cells set up
   by `addi a0,s1,176` / `addi a1,s1,168` 0x864b8 / 0x864bc) and 152(s1) (line 427 `ld s10,152(s1)` 0x867e4, the
   seed's chunk 152 = atom 38 = np when hnp = true); the atoms 32 (the shadow base, s2), 38 (np), 52 = p + i0,
   53 = p + j0, 54 = nth i0 L 0 (the seed's xs from atom 52 on); the registers s10 = x26, s4 = x20, a2 = x12, s5 =
   x21, s11 = x27 (the cut statements' registers); the pcs FR_SR = AF_m_file + 0x384 (0x864c4), MF_TAIL + 0x6e0
   (0x86820), MF_HDR + 0x3b4 (0x864f4), MF_KEY + 0x4dc (0x8661c). 14 checked, 0 pointing elsewhere.
   Built with a build tool snapshot (sha256 27c990b77310). *)
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

(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac fr7_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac fr7_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* a register's value as the state's symbolic value, not normalized *)
Ltac fr7_rawreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* a run whose regions are all read-only keeps every byte (image A's m_file_s_front_g.v fr_frame_ro) *)
Lemma fr7_frame_ro : forall E rs (m m' : word -> option byte),
frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' Hf Hw x. apply Hf. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hw r Hr) as H. apply Z.leb_le in H. lia.
Qed.
(* addressability through two readers that agree *)
Lemma fr7_ra_eq : forall (rd rd' : reader) Bx a n, (forall x, rd' x = rd x) ->
range_addressable rd Bx a n -> range_addressable rd' Bx a n.
Proof. intros rd rd' Bx a n Hk H x Hx. rewrite Hk. exact (H x Hx). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run whose regions are all read-only keeps the reader *)
Lemma fr7_aview_ro : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hw a. unfold aview, mbyte. rewrite (fr7_frame_ro E rs _ _ Hf Hw). reflexivity.
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run: the reader is the piece's start reader (MEQ), byte for byte (m_file_s_front_cl.v fr_meq) *)
Ltac fr7_meq :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    MEQ : forall a, aview _ _ ?m0 a = aview _ _ ?mc a |- _ =>
    let M := fresh "M" in
    pose proof (fr7_aview_ro _ rs H m0 m1 HFr ltac:(vm_compute; reflexivity)) as M;
    let MEQ' := fresh "MEQ" in
    assert (MEQ' : forall a, aview SEGS H m1 a = aview SEGS H mc a) by (intros a; rewrite M; apply MEQ);
    clear M MEQ HFr; rename MEQ' into MEQ end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

(* the atoms' values at the state's current environment (image A's m_file_s_front_cl.v cl_ux) *)
Ltac fr7_ux UXL UXN :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    pose proof (UXL Ex ltac:(intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)) as UXN end.
(* the machine state of the current symbolic state, under the fixed name msF (a run after a run names its state
   afresh) *)
Ltac fr7_ms :=
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => set (msF := msx) in * end.


(* the piece: from FR_SR to TAIL (an empty stripped line), HDR or KEY *)
Lemma fr_sr : forall n, MF_TAIL_stmt B n -> MF_HDR_stmt B n -> MF_KEY_stmt B n -> FR_SR_stmt B n.
Proof.
intros n TAIL HDR KEY. unfold FR_SR_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i0 j0 CTX SH R21 SL176 SL168 Hij Hsl.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & MOD).
destruct SH as (R27 & R20 & NP & HL512).
unfold fr_cut in Hsl.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & Btapp & _).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & HSTR & (PA1 & PA2 & PA3 & PRA & _) & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Hcurok) as Hcur.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
unfold in_app in Btapp. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Btapp.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnp64.
pose proof (fr_line_len rest) as HLL.
assert (Hpi : 0 <= p + Z.of_nat i0 < 2 ^ 64) by lia.
assert (Hpj : 0 <= p + Z.of_nat j0 < 2 ^ 64) by lia.
destruct (Nat.eq_dec i0 j0) as [<- | Hne0].
- (* i0 = j0: the stripped line is empty; 0x864cc to the join 0x867e0-0x867e8 and TAIL *)
  assert (HSN : h_strip (h_cut_comment (mf_line rest)) = []) by (rewrite <- Hsl; apply fr_slice_len_nil).
  assert (E52 : ew (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0]) 52 = Z_to_bv 64 (p + Z.of_nat i0))
    by exact (mfE_xs regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0] 0 ltac:(unfold A_TEXT; lia)).
  assert (FSLX : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0])
      (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v)))
    [YP09.mkChunk 168 (CVal 8 (SOff 52 0)); YP09.mkChunk 176 (CVal 8 (SOff 52 0))]).
  { constructor; [|constructor; [|constructor]].
    - apply (mf_chunk_atom _ _ _ 168 52 0 (p + Z.of_nat i0) E52 Hpi ltac:(lia)). rewrite Z.add_0_r. exact SL168.
    - apply (mf_chunk_atom _ _ _ 176 52 0 (p + Z.of_nat i0) E52 Hpi ltac:(lia)). rewrite Z.add_0_r. exact SL176. }
  pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [p + Z.of_nat i0]
    FR_SR true true [YP09.mkChunk 168 (CVal 8 (SOff 52 0)); YP09.mkChunk 176 (CVal 8 (SOff 52 0))] false false [] false
    CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp64 ltac:(unfold MF_LOW_OFF; lia) FSLX (Forall_nil _)
    ltac:(vm_compute; reflexivity)) as HS0.
  remember (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0]) as E eqn:HE.
  assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
    by (subst E; intros; apply mfE_reg; assumption).
  assert (EX : forall j, (32 + j < A_TEXT)%nat ->
    ew E (32 + j) = nth j (mf_extra v lyc pos cur (mf_next p rest) [p + Z.of_nat i0]) (Z_to_bv 64 0))
    by (subst E; intros; apply mfE_extra; assumption).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
  clear HE.
  pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
  cbn [Nat.add nth mf_extra map app] in E32, E38.
  (* the frame cells read-only *)
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
  lazymatch type of HR1 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
  clear HS0 HR1. fr7_norm HS1.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
  assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
  unfold mf_at.
  (* 0x864c4-0x864cc (s10 = s4 = atom 52, `beq` taken), 0x867e0-0x867e8: s4 = 511, s10 = 152(s1), `j` TAIL *)
  paj_run_to_tok RUNTO HS1 HJ SHOK Bspan MF_TAIL.
  { fr7_awr_ro. }
  fr7_meq.
  destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) _ pos MF_LOW_OFF mcc mcc cur line p rest CX CORE HJ
    (fun a _ => MEQ a) LOOP) as (CORE' & LOOP' & CELLSf & _).
  pose proof (mf_loop_next v Wc (ms_mem ms) mcc cur line p rest mcc cur LOOP' Hne ltac:(lia) ltac:(lia) (le_n _)
    Hcurok) as LOOPn.
  prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
  prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
  prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (25%bv : bv 5) Q25.
  prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (27%bv : bv 5) Q27. prreg HS1 (20%bv : bv 5) Q20.
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
  pmkst HS1.
  apply (TAIL v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur (line + 1) (mf_next p rest) (mf_rest rest) CX LS FRM
    CORE' (CELLSf cur CELLS) RA' ltac:(pose proof (fr_mf_rest_lt rest Hne); lia) LOOPn
    (fr_eq_empty mcc cur line rest (mf_final v) Hne MOD HL512 HSN)).
  + rewrite Q26, E38. reflexivity.
  + rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
  + rewrite Q20. reflexivity.
- (* i0 < j0: the trap 0x864d0, the check 0x864dc, the byte, the '[' test 0x864f0 to HDR or KEY *)
  assert (Hlt : (i0 < j0)%nat) by lia.
  set (bb := nth i0 (mf_line rest) 0).
  assert (HBY : rdW Wc memc (p + Z.of_nat i0) = Some bb).
  { destruct HSTR as ((HZS & _) & _). rewrite (HZS i0 ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth1 by lia. unfold bb. rewrite (fr_line_nth rest i0) by lia. reflexivity. }
  destruct (aview_byte SEGS (w_H Wc) memc (p + Z.of_nat i0) bb HBY) as (bv0 & _ & _ & Hbb).
  assert (HNE : h_strip (h_cut_comment (mf_line rest)) <> []) by (rewrite <- Hsl; apply fr_slice_ne; lia).
  assert (HHD : hd0 (h_strip (h_cut_comment (mf_line rest))) = bb) by (rewrite <- Hsl; apply fr_hd_slice; lia).
  assert (E52 : ew (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb]) 52 =
    Z_to_bv 64 (p + Z.of_nat i0))
    by exact (mfE_xs regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb] 0
      ltac:(unfold A_TEXT; lia)).
  assert (E53 : ew (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb]) 53 =
    Z_to_bv 64 (p + Z.of_nat j0))
    by exact (mfE_xs regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb] 1
      ltac:(unfold A_TEXT; lia)).
  assert (E54 : ew (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb]) 54 =
    Z_to_bv 64 bb)
    by exact (mfE_xs regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb] 2
      ltac:(unfold A_TEXT; lia)).
  assert (FSLX : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb])
      (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v)))
    [YP09.mkChunk 168 (CVal 8 (SOff 53 0)); YP09.mkChunk 176 (CVal 8 (SOff 52 0))]).
  { constructor; [|constructor; [|constructor]].
    - apply (mf_chunk_atom _ _ _ 168 53 0 (p + Z.of_nat j0) E53 Hpj ltac:(lia)). rewrite Z.add_0_r. exact SL168.
    - apply (mf_chunk_atom _ _ _ 176 52 0 (p + Z.of_nat i0) E52 Hpi ltac:(lia)). rewrite Z.add_0_r. exact SL176. }
  assert (FCS : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb])
      (mrestrict (w_H Wc) memc) (p + Z.of_nat i0))
    [YP09.mkChunk 0 (CVal 1 (SOff 54 0))]).
  { constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (p + Z.of_nat i0) 0 1 (SOff 54 0) bb);
      [cbn [sv_denot]; rewrite E54, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc (p + Z.of_nat i0) bb HBY). }
  (* the byte at p + i0: a read-only text region at atom 52 *)
  destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest)
    [p + Z.of_nat i0; p + Z.of_nat j0; bb] 52 (p + Z.of_nat i0) 1 [YP09.mkChunk 0 (CVal 1 (SOff 54 0))] line p rest
    true true [YP09.mkChunk 168 (CVal 8 (SOff 53 0)); YP09.mkChunk 176 (CVal 8 (SOff 52 0))] false false [] false
    CX CORE RB LOOP E52 ltac:(lia) ltac:(lia) ltac:(lia) FCS) as (TRok & TRdis & _).
  pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest)
    [p + Z.of_nat i0; p + Z.of_nat j0; bb] FR_SR true true
    [YP09.mkChunk 168 (CVal 8 (SOff 53 0)); YP09.mkChunk 176 (CVal 8 (SOff 52 0))] false false [] false
    CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp64 ltac:(unfold MF_LOW_OFF; lia) FSLX (Forall_nil _)
    ltac:(vm_compute; reflexivity)) as HS0.
  pose proof (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 52%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 54 0))])
    HS0 ltac:(vm_compute; reflexivity) TRok TRdis) as HS1.
  clear HS0 TRok TRdis.
  remember (mfE regs1 v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb]) as E eqn:HE.
  assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
    by (subst E; intros; apply mfE_reg; assumption).
  assert (EX : forall j, (32 + j < A_TEXT)%nat ->
    ew E (32 + j) = nth j (mf_extra v lyc pos cur (mf_next p rest) [p + Z.of_nat i0; p + Z.of_nat j0; bb]) (Z_to_bv 64 0))
    by (subst E; intros; apply mfE_extra; assumption).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
  assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (subst E; apply mfE_U32).
  clear HE.
  pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
  assert (U52 : U E (SOff 52 0) = p + Z.of_nat i0) by exact (U_atom E 52 _ E52 Hpi).
  assert (U53 : U E (SOff 53 0) = p + Z.of_nat j0) by exact (U_atom E 53 _ E53 Hpj).
  assert (U54 : U E (SOff 54 0) = bb) by (apply (U_atom E 54 _ E54); lia).
  (* the atoms' values at any later environment of the piece (a token run's fresh atoms are 1024 and up): the byte
     the `lbu` 0x864e4 loads, and a2 = s4 - s10 as the executor forms it (0x864e8 `sub a2,s4,s10`: (-1) * s10 + s4) *)
  assert (UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew E k) ->
    U Ex (SExt false 8 (SOff 54 0)) = bb /\
    U Ex (SAlu ALU_ADD (SMd M_MUL (SOff 52 0) (SLit (-1))) (SOff 53 0)) = Z.of_nat (j0 - i0)).
  { intros Ex HK.
    assert (X52 : ew Ex 52 = Z_to_bv 64 (p + Z.of_nat i0)) by (rewrite (HK 52%nat ltac:(lia)); exact E52).
    assert (X53 : ew Ex 53 = Z_to_bv 64 (p + Z.of_nat j0)) by (rewrite (HK 53%nat ltac:(lia)); exact E53).
    assert (X54 : ew Ex 54 = Z_to_bv 64 bb) by (rewrite (HK 54%nat ltac:(lia)); exact E54).
    pose proof (U_atom Ex 52 _ X52 Hpi) as Y52. pose proof (U_atom Ex 53 _ X53 Hpj) as Y53.
    pose proof (U_atom Ex 54 bb X54 ltac:(lia)) as Y54.
    split.
    - rewrite U_zext, Y54. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
    - rewrite U_SAlu, U_SMd, Y52, Y53, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
      change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite Zplus_mod_idemp_l, Nat2Z.inj_sub by lia.
      replace ((p + Z.of_nat i0) * (2 ^ 64 - 1) + (p + Z.of_nat j0)) with
        ((Z.of_nat j0 - Z.of_nat i0) + (p + Z.of_nat i0) * 2 ^ 64) by ring.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  fr7_norm HS1.
  (* the frame cells read-only *)
  pose proof (st_ok_pi_region_nth E _ _ 2 _ HS1 eq_refl) as HR2.
  lazymatch type of HR2 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 2 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS E _ r 0 0 HR2 ltac:(intros o Ho; lia))) as HS2 end.
  clear HS1 HR2. fr7_norm HS2.
  (* s10 = p + i0 is a heap pointer: the trap's executor decision and the token run's check need it *)
  apply (st_ok_pi_add_fact E _ _ 52 (HPTR 0)) in HS2;
    [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E52, unsigned_lit_small by lia;
       change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  fr7_norm HS2.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
  assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
  unfold mf_at.
  (* 0x864c4-0x864c8: s10 = 176(s1) = atom 52, s4 = 168(s1) = atom 53; the `beq` 0x864cc *)
  paj_run_tok RUN HS2 HJ SHOK Bspan.
  { fr7_awr_ro. }
  fr7_meq.
  psrr_branch_tok RUN BR HS2 SHOK Bspan.
  { (* taken: p + i0 = p + j0, against i0 < j0 *)
    exfalso. rewrite branch_eq_U, U52, U53 in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  (* 0x864d0 the trap (not taken: atom 52 >= 4096), 0x864d4-0x864e0 the check of the byte at p + i0, 0x864e4 its
     load, 0x864e8 a2 = s4 - s10, 0x864ec a1 = '['; the `bne` 0x864f0 *)
  paj_run_tok RUN HS2 HJ SHOK Bspan.
  { rewrite ?U52. eapply (obl_of_range SEGS _ _ E (SOff 32 0) (p + Z.of_nat i0) 1 p _
      (fr7_ra_eq _ _ _ _ _ MEQ PRA) UB); lia. }
  { fr7_awr_ro. }
  fr7_meq.
  psrr_branch_tok RUN BR HS2 SHOK Bspan.
  + (* taken: the first byte of the stripped line is not '[': KEY 0x8661c *)
    fr7_ux UX UXc. destruct UXc as (X54z & _).
    rewrite branch_ne_U, X54z, U_lit in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_KEY.
    { fr7_awr_ro. }
    fr7_meq. fr7_ms.
    destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem msF) _ pos MF_LOW_OFF mcc mcc cur line p rest CX CORE HJ
      (fun a _ => MEQ a) LOOP) as (CORE' & LOOP' & CELLSf & NPf).
    prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
    prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
    prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (25%bv : bv 5) Q25.
    prreg HS2 (26%bv : bv 5) Q26. prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (21%bv : bv 5) Q21.
    prreg HS2 (27%bv : bv 5) Q27. fr7_rawreg HS2 (12%bv : bv 5) Q12.
    fr7_ux UX UXf. destruct UXf as (_ & X12).
    assert (RA' : mf_regs_at B v lyc pos (ms_regs msF)).
    { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs msF) RA).
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
    apply (KEY v lyc Sc Wc (ms_regs msF) (ms_mem msF) _ pos mcc cur line p rest i0 j0 CX LS FRM CORE' (CELLSf cur CELLS)
      RA' Hn Hne LOOP' HL512 Hlt ltac:(lia) Hsl Hc
      (fr_eq_key mcc cur line rest (mf_final v) Hne MOD HL512 HNE ltac:(rewrite HHD; exact Hc))).
    * rewrite Q26, E52. reflexivity.
    * rewrite Q20, E53. reflexivity.
    * rewrite Q12, denot_lit_U, X12. reflexivity.
    * rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
    * exact (NPf _ NP).
    * rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
  + (* not taken: the first byte is '[': HDR 0x864f4 *)
    fr7_ux UX UXc. destruct UXc as (X54z & _).
    rewrite branch_ne_U, X54z, U_lit in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_HDR.
    { fr7_awr_ro. }
    fr7_meq. fr7_ms.
    destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem msF) _ pos MF_LOW_OFF mcc mcc cur line p rest CX CORE HJ
      (fun a _ => MEQ a) LOOP) as (CORE' & LOOP' & CELLSf & NPf).
    prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
    prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
    prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (25%bv : bv 5) Q25.
    prreg HS2 (26%bv : bv 5) Q26. prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (21%bv : bv 5) Q21.
    prreg HS2 (27%bv : bv 5) Q27. fr7_rawreg HS2 (12%bv : bv 5) Q12.
    fr7_ux UX UXf. destruct UXf as (_ & X12).
    assert (RA' : mf_regs_at B v lyc pos (ms_regs msF)).
    { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs msF) RA).
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
    apply (HDR v lyc Sc Wc (ms_regs msF) (ms_mem msF) _ pos mcc cur line p rest i0 j0 CX LS FRM CORE' (CELLSf cur CELLS)
      RA' Hn Hne LOOP' HL512 Hlt ltac:(lia) Hsl Hc
      (fr_eq_hdr mcc cur line rest (mf_final v) Hne MOD HL512 ltac:(rewrite HHD; exact Hc))).
    * rewrite Q26, E52. reflexivity.
    * rewrite Q20, E53. reflexivity.
    * rewrite Q12, denot_lit_U, X12. reflexivity.
    * rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
    * exact (NPf _ NP).
    * rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
Qed.
(* inside the Sections: the piece's hypotheses as its assumptions *)
About fr_sr. Print Assumptions fr_sr.
End e.
End f.
End d.
About fr_sr. Print Assumptions fr_sr.
