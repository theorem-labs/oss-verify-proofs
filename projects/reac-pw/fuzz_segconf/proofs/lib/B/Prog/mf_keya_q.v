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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 408 of its 454 lines of code are new or changed and 407 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_KEYA: the quotes, KB_Q 0x86668 to
   KB_U 0x866ec (mf_keya_d.v kb_quote : KB_U_stmt n -> KB_Q_stmt n), in the form of plugin-hostd/fuzz_command's
   lib/A/Prog walks (origin/ossv/recipes 501c0d516c69). The neutral listing of m_file in image B lines 338-364:
     0x86668  ld a1,184(s1); ld a0,192(s1); sub a2,a1,a0; li a3,2   a1 = ve = p + d, a0 = v = p + c, a2 = d - c
     0x86678  blt a2,a3 -> 0x866dc                                     d - c < 2: no quote
     0x8667c  beqz a0 -> 0x86e84                                       UBSan trap (v = NULL), not taken
     0x86680  the instrumented check of the byte at v (a load of the shadow byte at (v >> 3) + s2 and a compare;
              slow path 0x86c6c-0x86c74, error path 0x86ef8, not reached)
     0x86690  lbu a2,0(a0); a2 = 39 -> 0x866a4; a2 <> 34 -> 0x866dc   the first byte a single or a double quote
     0x866a8  bltu a1,2 -> 0x86e84                                     UBSan trap (ve <u 2), not taken
     0x866ac  addi a1,a1,-1; the instrumented check of the byte at ve - 1 (slow path 0x86c78-0x86c80, error path
              0x86efc / 0x86f00, not reached); lbu a3,0(a1); a3 <> a2 -> 0x866dc   the last byte the same quote
     0x866cc  beq a0,-1 -> 0x86e84                                     UBSan trap (v + 1 wraps), not taken
     0x866d0  addi a0,a0,1; sd a0,192(s1); sd a1,184(s1)               v + 1 and ve - 1 into the cells
     0x866dc  ld a1,200(s1); ld a0,208(s1); ld a2,184(s1); ld a3,192(s1); KB_U 0x866ec
   The seed is m_file_sd.v's mf_seed at KB_Q with the frame cells writable only at [184, 200) and the four scratch
   cells as atoms 52 .. 55 (p + a, p + b, p + c, p + d); atoms 56, 57 are the two end bytes, atom 58 is d - c. Every
   branch is decided by the symbolic run itself, one run per case:
   - the three UBSan traps by the facts that atoms 54 and 55 (v and ve) are heap pointers of the text block (HPTR:
     4096 .. 2 ^ 47 - 2 ^ 23, from mf_loop_blk and the block bounds of AR): v <> 0, ve >= 2, v <> 2 ^ 64 - 1;
   - blt by the alias ve - v = atom 58 and its range ([0, 1] or [2, 2 ^ 47]);
   - the quote tests by the byte regions: a known quote byte as its literal, any other byte as an atom with a
     branch condition (kq_add_cond) that it differs from the quote.
   The two instrumented checks leave the obligation that the byte is addressable, which mf_loop's
   range_addressable of the text left gives (obl_of_range). The run writes only 184(s1) .. 199(s1), so m_file_k.v's
   mf_keep_run_s / mf_val_keep carry the cut facts (LEAF below), and 192(s1) is read from the final frame-cells
   region (kq_slot). The quoted value is mf_keya_m.v's kb_unquote_idx with kb_q. A walk lane of the image-B m_file-family owner's G2B
   (the owner's walk lane). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_keya_m mf_keya_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Ltac kq_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* the bytes the quotes may write: the two cells 184(s1) and 192(s1) *)
Definition kq_rw (s1 x : Z) : Prop := s1 + 184 <= x < s1 + 200.
(* the write check of a run: the frame cells' region (base s1 = atom 2) is the only writable one, its window
   [184, 200) inside the caller-stack band (awr_ok_cons_stack_off); U2 : bv_unsigned (ew E 2) = s1 *)
Ltac kq_awr U2 HSTK :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
lazymatch goal with |- awr_ok ?sg ?bb _ _ _ ?sp0 _ _ _ _ _ _ =>
lazymatch type of U2 with bv_unsigned (ew _ _) = ?s1v =>
repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | apply (awr_ok_cons_stack_off sg bb _ _ _ _ _ _ _ _ _ _ _ 2%nat (s1v - sp0));
      [reflexivity | rewrite U2; ring | rewrite HSTK; cbn; unfold mf_s1; lia | cbn; unfold mf_s1; lia | ] ]
end end.
(* after a run: every byte outside [s1 + 184, s1 + 200) keeps its view (kept_of_frame over the run's windows) *)
Ltac kq_keep K U2 :=
lazymatch goal with |- SRr ?sg _ _ _ =>
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
lazymatch type of U2 with bv_unsigned (ew _ _) = ?s1v =>
  assert (K : forall x, 0 <= x < 2 ^ 64 -> ~ kq_rw s1v x -> aview sg H (ms_mem msc) x = aview sg H m0 x);
  [ let x := fresh "x" in let Hx := fresh "Hx" in let HnW := fresh "HnW" in
    intros x Hx HnW; refine (kept_of_frame Ex rs H m0 (ms_mem msc) (kq_rw s1v) HFr _ x Hx HnW);
    let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let y := fresh "y" in
    let Hinw := fresh "Hinw" in let Hy := fresh "Hy" in let Hq := fresh "Hq" in
    intros bb wlo whi y Hinw Hy; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hy; first [lia | rewrite U2 in Hy; unfold kq_rw; lia] |]);
    destruct Hinw
  | ]
end end end.
(* a register the run does not write: its entry value *)
Ltac kq_same HS EE R2 R9 E32 R18 :=
lazymatch goal with
| |- getr (ms_regs ?ms) ?r = getr ?regs1 ?r =>
  let Q := fresh "Q" in prreg HS r Q; rewrite Q;
  first [ apply EE; reflexivity
        | rewrite (EE 2%nat 2%bv eq_refl), R2, R9; reflexivity
        | rewrite E32, R18; reflexivity ]
| |- _ => idtac
end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* an 8-byte chunk of a region of a state, as the value of its expression *)
Lemma kq_slot : forall E m n b cs lo hi wlo whi od e x,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CVal 8 e)) cs -> U E e = x -> val_mem SEGS m (b + od) 8 x.
Proof.
intros E m n b cs lo hi wlo whi od e x HR Hb Hin Hx.
pose proof (field_of_region_any E m n b cs lo hi wlo whi od 8%N e HR Hb Hin ltac:(cbn; lia)) as V.
change (N.to_nat 8) with 8%nat in V. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V.
change (bv_unsigned (sv_denot E e)) with (U E e) in V.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as HR64. change (bv_modulus 64) with (2 ^ 64) in HR64.
change (bv_unsigned (sv_denot E e)) with (U E e) in HR64.
rewrite Z.mod_small in V by lia. rewrite <- Hx. exact V.
Qed.
(* a branch condition that holds, as a fact of the state (the run then decides that branch) *)
Lemma kq_add_cond : forall E ss ms c a b, st_ok_pi SEGS VAL E ss ms ->
branch_taken c (sv_denot E a) (sv_denot E b) = true -> st_ok_pi SEGS VAL E (add_cond ss (mkAC c a b)) ms.
Proof. intros E ss ms c a b HS Hc. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_add_cond SEGS E _ ms c a b HS Hc). Qed.
(* a read-only one-byte region at atom n + lo, the byte the reader shows there *)
Lemma kq_byte_ok : forall E (H : word -> bool) m n base lo e z,
bv_unsigned (ew E n) = base -> 0 <= base + lo -> base + lo + 1 <= 2 ^ 64 ->
sv_denot E e = Z_to_bv 64 z -> 0 <= z < 256 -> aview SEGS H m (base + lo) = Some z ->
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo (lo + 1) 0 0 [YP09.mkChunk lo (CVal 1 e)]).
Proof.
intros E H m n base lo e z Hb H0 H1 He Hz Hv. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ base lo 1 e z He ltac:(cbn; lia) ltac:(cbn; lia)).
exact (mf_val1_of_aview H m (base + lo) z Hv).
Qed.
(* the extents of a new region against the state's regions *)
Ltac kq_disj := cbn [all_disjoint ss_mem add_atom add_cond]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
(* a run from KB_Q to KB_U: the instrumented checks of *v (atom 54) and ve[-1] (atom 55 - 1) leave the obligation
   that the byte is addressable, which mf_loop's range_addressable of the text left gives (obl_of_range); the write
   check (kq_awr); then the kept bytes (kq_keep) *)
Ltac kq_run RUNTO HS HJ SHOK UV UVE PRA UB U2 HSTK E p K :=
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KB_U;
  lazymatch goal with
  | |- range_addressable _ _ _ _ =>
    cbn [ms_mem mkst]; first [rewrite UV | rewrite UVE];
    eapply (obl_of_range SEGS _ _ E (SOff 32 0) _ 1 p _ PRA UB); lia
  | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => kq_awr U2 HSTK
  | |- _ => kq_keep K U2
  end.
(* 192(s1) after a run: the chunk of the final frame-cells region (its environment may hold fresh atoms past the
   seed's: ew of a seed atom reduces through ewset) *)
Ltac kq_slot192 HR U2 U54 k :=
  lazymatch type of HR with region_ok _ ?Ex _ _ =>
    unfold mf_slot; apply (kq_slot Ex _ 2 _ _ _ _ _ _ 192 (SOff 54 k) _ HR);
    [ cbn [ew ewset Nat.eqb]; exact U2
    | cbn; repeat (first [left; reflexivity | right])
    | rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite U54, zcanon_small by lia; lia ]
  end.
(* the end of a run with no quote: 192(s1) = v, a2 = ve (atom 55), a3 = v (atom 54) *)
Ltac kq_fin0 LEAF HS HJ K Hq idx U2 E52 E53 E54 E55 U54 EE R2 R9 E32 R18 c d :=
  let HR := fresh "HR" in
  pose proof (st_ok_pi_region_nth _ _ _ idx _ HS eq_refl) as HR; cbn [restrict ms_mem] in HR;
  let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q13 := fresh "Q13" in
  prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
  prreg HS (13%bv : bv 5) Q13;
  pmkst HS;
  apply (LEAF _ _ _ false c d HJ K Hq eq_refl eq_refl); kq_same HS EE R2 R9 E32 R18;
  [ kq_slot192 HR U2 U54 0
  | rewrite Q10, E52; reflexivity
  | rewrite Q11, E53; reflexivity
  | rewrite Q12, E55; reflexivity
  | rewrite Q13, E54; reflexivity ].
(* the end of the quote path: 192(s1) = v + 1 (the stored atom 54 + 1), a2 = ve - 1, a3 = v + 1 *)
Ltac kq_fin1 LEAF HS HJ K Hq idx U2 E52 E53 U54 U55 EE R2 R9 E32 R18 c d :=
  let HR := fresh "HR" in
  pose proof (st_ok_pi_region_nth _ _ _ idx _ HS eq_refl) as HR; cbn [restrict ms_mem] in HR;
  let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q13 := fresh "Q13" in
  prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
  prreg HS (13%bv : bv 5) Q13;
  pmkst HS;
  apply (LEAF _ _ _ true (S c) (d - 1)%nat HJ K Hq eq_refl eq_refl); kq_same HS EE R2 R9 E32 R18;
  [ kq_slot192 HR U2 U54 1
  | rewrite Q10, E52; reflexivity
  | rewrite Q11, E53; reflexivity
  | rewrite Q12, U55; unfold w64; f_equal; lia
  | rewrite Q13, U54; unfold w64; f_equal; lia ].
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

Lemma kb_quote : forall n, KB_U_stmt B n -> KB_Q_stmt B n.
Proof.
intros n KU. unfold KB_Q_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest i j ei a b c d CTX RG KEY VA S208 S200 S192 S184.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & Hn & Hr & LOOP & Hij & HjL & HMC & HFIN & NP).
pose proof RG as (RA & R27).
pose proof VA as (Vc1 & Vc2 & Vc3 & Vstr).
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc (Some gi) line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & Btapp & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bt mt 1 pos HAR Hbt Hin) as Hsep.
change (fs_frame_bytes 1) with 128 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & (PA1 & PA2 & PA3 & PRA & _) & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (Some gi) CX CORE Hcurok) as Hcur.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold in_app in Btapp. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Btapp.
pose proof (kb_line_len rest) as HLr.
destruct (kb_memchr_some _ _ _ HMC) as (Hei & _ & _).
rewrite kb_slice_length in Hei by lia.
pose proof KEY as (Ka1 & Ka2 & Ka3 & Kstr).
assert (HcdL : (c <= d <= length (mf_line rest))%nat) by lia.
assert (Hd1 : (1 <= d)%nat) by lia.
assert (Hp64 : 0 <= p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 63) by lia.
remember [p + Z.of_nat a; p + Z.of_nat b; p + Z.of_nat c; p + Z.of_nat d; nth c (mf_line rest) 0;
  nth (d - 1) (mf_line rest) 0; Z.of_nat (d - c)] as xs eqn:Hxs.
remember (mfE regs1 v lyc pos (Some gi) 0 xs) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 xs) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (EXS : forall j, (52 + j < A_TEXT)%nat -> ew E (52 + j) = Z_to_bv 64 (nth j xs 0))
  by (subst E; intros; apply mfE_xs; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
pose proof (EXS 0%nat ltac:(unfold A_TEXT; lia)) as E52. pose proof (EXS 1%nat ltac:(unfold A_TEXT; lia)) as E53.
pose proof (EXS 2%nat ltac:(unfold A_TEXT; lia)) as E54. pose proof (EXS 3%nat ltac:(unfold A_TEXT; lia)) as E55.
pose proof (EXS 4%nat ltac:(unfold A_TEXT; lia)) as E56. pose proof (EXS 5%nat ltac:(unfold A_TEXT; lia)) as E57.
pose proof (EXS 6%nat ltac:(unfold A_TEXT; lia)) as E58.
rewrite Hxs in E52, E53, E54, E55, E56, E57, E58. cbn [nth Nat.add] in E52, E53, E54, E55, E56, E57, E58.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E34, E36.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc (Some gi) 0 xs KB_Q true false
  [YP09.mkChunk 208 (CVal 8 (SOff 52 0)); YP09.mkChunk 200 (CVal 8 (SOff 53 0));
   YP09.mkChunk 192 (CVal 8 (SOff 54 0)); YP09.mkChunk 184 (CVal 8 (SOff 55 0))] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur ltac:(intros Hf; discriminate Hf) ltac:(lia)
  ltac:(unfold MF_LOW_OFF; lia)) as HS0.
rewrite <- HE in HS0.
lapply HS0; clear HS0; [intros HS0|].
2:{ repeat apply Forall_cons; try apply Forall_nil.
    - apply (mf_chunk_atom E _ _ 208 52 0 (p + Z.of_nat a) E52 ltac:(lia) ltac:(lia)). rewrite Z.add_0_r. exact S208.
    - apply (mf_chunk_atom E _ _ 200 53 0 (p + Z.of_nat b) E53 ltac:(lia) ltac:(lia)). rewrite Z.add_0_r. exact S200.
    - apply (mf_chunk_atom E _ _ 192 54 0 (p + Z.of_nat c) E54 ltac:(lia) ltac:(lia)). rewrite Z.add_0_r. exact S192.
    - apply (mf_chunk_atom E _ _ 184 55 0 (p + Z.of_nat d) E55 ltac:(lia) ltac:(lia)). rewrite Z.add_0_r. exact S184. }
specialize (HS0 (Forall_nil _) ltac:(vm_compute; reflexivity)).
clear HE.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U54 : bv_unsigned (ew E 54) = p + Z.of_nat c) by (rewrite E54; apply unsigned_lit_small; lia).
assert (U55 : bv_unsigned (ew E 55) = p + Z.of_nat d) by (rewrite E55; apply unsigned_lit_small; lia).
assert (U58 : bv_unsigned (ew E 58) = Z.of_nat (d - c)) by (rewrite E58; apply unsigned_lit_small; lia).
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
(* the frame cells: only 184(s1) .. 199(s1) writable *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof HR1 as (_ & _ & HW1 & _);
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 184 200) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 184 200 HR1 ltac:(intros o Ho; apply HW1; cbn; lia))) as HS1 end.
clear HS0 HR1 HW1. kq_norm HS1.
(* the two cursors v and ve: heap pointers of the text's block *)
apply (st_ok_pi_add_fact E _ _ 54 (HPTR 0)) in HS1;
  [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U54; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
apply (st_ok_pi_add_fact E _ _ 55 (HPTR 0)) in HS1;
  [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U55; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
(* ve - v as atom 58 *)
apply (st_ok_pi_add_alias E _ _ (SAlu ALU_SUB (SOff 55 0) (SOff 54 0)) (SOff 58 0)) in HS1;
  [| apply U_inj; rewrite U_SAlu, (U_atom E 55 (p + Z.of_nat d) E55 ltac:(lia)),
       (U_atom E 54 (p + Z.of_nat c) E54 ltac:(lia)), (U_atom E 58 (Z.of_nat (d - c)) E58 ltac:(lia));
     cbn [zalu_raw]; rewrite zcanon_small by lia; lia].
kq_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & Bc4096 & Bcceil & _).
(* the common end of every path: the cut facts at KB_U from a run that wrote only 184(s1) .. 199(s1) *)
assert (LEAF : forall (m2 : word -> option byte) md2 (regs2 : bvmap 5 word) (q : bool) (ov oe : nat),
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc m2 md2 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ kq_rw (mf_s1 (mv_sp v)) x -> rdW Wc m2 x = rdW Wc memc x) ->
  kb_q (mf_line rest) c d = q -> ov = (if q then S c else c) -> oe = (if q then (d - 1)%nat else d) ->
  mf_slot v m2 Wc 192 (p + Z.of_nat ov) ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
  getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 -> getr regs2 19 = getr regs1 19 ->
  getr regs2 22 = getr regs1 22 -> getr regs2 25 = getr regs1 25 -> getr regs2 27 = getr regs1 27 ->
  getr regs2 10 = w64 (p + Z.of_nat a) -> getr regs2 11 = w64 (p + Z.of_nat b) ->
  getr regs2 12 = w64 (p + Z.of_nat oe) -> getr regs2 13 = w64 (p + Z.of_nat ov) ->
  SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + KB_U)) m2 (seg_rom SEGS)) md2) (MF_POST B v)).
{ intros m2 md2 regs2 q ov oe HJ2 K2 Hq Hov Hoe S192' Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25 Q27 Q10 Q11 Q12 Q13.
  assert (RWok : forall x, kq_rw (mf_s1 (mv_sp v)) x -> mf_rw v lyc pos x)
    by (intros x Hx; unfold mf_rw, kq_rw in *; right; right; right; right; right; lia).
  assert (RWS : mf_rws v (kq_rw (mf_s1 (mv_sp v)))) by (intros x Hx _; unfold kq_rw in Hx; right; lia).
  pose proof CORE as (_ & _ & _ & VSH & _ & _ & VMC & _).
  assert (VSH' : forall k, 4 <= k < 12 -> val_mem SEGS (mrestrict (w_H Wc) m2)
    (SHADOW_OFF + frame_addr lyc 1 pos / 8 + k) 1 MF_LOW_OFF).
  { intros k Hk. apply (mf_val_keep Wc Wc memc m2 (kq_rw (mf_s1 (mv_sp v))) _ 1 _ K2);
      [unfold SHADOW_OFF; lia | cbn; unfold SHADOW_OFF; lia | | exact (VSH k Hk)].
    intros k' Hk' HR. unfold kq_rw, mf_s1 in HR. cbn in Hk'. unfold SHADOW_OFF in *. lia. }
  pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
  assert (V136' : val_mem SEGS (mrestrict (w_H Wc) m2) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) (Some gi))).
  { apply (mf_val_keep Wc Wc memc m2 _ _ 8 _ K2); [unfold mf_s1; lia | cbn; unfold mf_s1; lia | | exact V136].
    intros k' Hk' HR. unfold kq_rw in HR. cbn in Hk'. lia. }
  assert (MC' : sa_mconf (rdW Wc m2) (mv_c v) mcc).
  { apply (mf_mconf_keep Wc Wc memc m2 _ (mv_c v) mcc K2); [lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact VMC].
    intros x Hx HR. unfold kq_rw, mf_s1 in HR. unfold seg_spec.SEG_M_SIZE in *. lia. }
  destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc (Some gi) m2 md2 (kq_rw (mf_s1 (mv_sp v)))
    MF_LOW_OFF (Some gi) mcc CX CORE CELLS HJ2 K2 RWok RWS VSH' V136' MC') as (CORE' & CELLS' & LKEEP).
  pose proof (LKEEP mcc (Some gi) line p rest LOOP) as LOOP'.
  assert (NP' : mf_np v m2 Wc (mf_next p rest)).
  { unfold mf_np, mf_slot in NP |- *. apply (mf_val_keep Wc Wc memc m2 _ _ 8 _ K2);
      [unfold mf_s1; lia | cbn; unfold mf_s1; lia | | exact NP].
    intros k' Hk' HR. unfold kq_rw in HR. cbn in Hk'. lia. }
  assert (S208' : mf_slot v m2 Wc 208 (p + Z.of_nat a)).
  { unfold mf_slot in S208 |- *. apply (mf_val_keep Wc Wc memc m2 _ _ 8 _ K2);
      [unfold mf_s1; lia | cbn; unfold mf_s1; lia | | exact S208].
    intros k' Hk' HR. unfold kq_rw in HR. cbn in Hk'. lia. }
  assert (CTX' : kb_ctx B v lyc Sc Wc m2 md2 pos mcc gi line p rest i j ei n)
    by exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj Hn (conj Hr (conj LOOP'
      (conj Hij (conj HjL (conj HMC (conj HFIN NP')))))))))))).
  assert (RG' : kb_regs B v lyc pos regs2 line).
  { split; [|rewrite Q27; exact R27].
    exact (mf_regs_at_of B v lyc pos regs1 regs2 RA Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25). }
  destruct q; cbn in Hov, Hoe; subst ov oe.
  - assert (H2 : (2 <= d - c)%nat).
    { unfold kb_q in Hq. apply andb_prop in Hq as [Hq _]. apply andb_prop in Hq as [Hq _].
      apply Nat.leb_le in Hq. exact Hq. }
    apply (KU v lyc Sc Wc regs2 m2 md2 pos mcc gi line p rest i j ei a b (S c) (d - 1 - S c)%nat CTX' RG' KEY).
    + lia.
    + rewrite Vstr, (kb_unquote_idx _ c d HcdL), Hq. f_equal. lia.
    + exact S208'.
    + exact S192'.
    + exact Q10.
    + exact Q11.
    + rewrite Q12. unfold w64. f_equal. lia.
    + exact Q13.
  - apply (KU v lyc Sc Wc regs2 m2 md2 pos mcc gi line p rest i j ei a b c (d - c)%nat CTX' RG' KEY).
    + lia.
    + rewrite Vstr, (kb_unquote_idx _ c d HcdL), Hq. f_equal. lia.
    + exact S208'.
    + exact S192'.
    + exact Q10.
    + exact Q11.
    + rewrite Q12. unfold w64. f_equal. lia.
    + exact Q13. }
unfold mf_at.
destruct (Nat.lt_ge_cases (d - c) 2) as [Hsh | Hlg].
- (* ve - v < 2: no quote, straight to 0x866dc *)
  apply (st_ok_pi_add_fact E _ _ 58 (mkAF 0 1 0)) in HS1;
    [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U58; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  kq_norm HS1.
  paj_run_to_tok RUNTO HS1 HJ SHOK Bspan KB_U.
  { kq_awr U2 HSTK. }
  kq_keep K U2.
  assert (Hq : kb_q (mf_line rest) c d = false)
    by (unfold kb_q; rewrite (proj2 (Nat.leb_gt 2 (d - c)) Hsh); reflexivity).
  kq_fin0 LEAF HS1 HJ K Hq 1%nat U2 E52 E53 E54 E55 U54 EE R2 R9 E32 R18 c d.
- (* ve - v >= 2: the two end bytes *)
  apply (st_ok_pi_add_fact E _ _ 58 (mkAF 2 (2 ^ 47) 0)) in HS1;
    [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U58; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  kq_norm HS1.
  pose proof LOOP as (_ & _ & _ & ((ZS & _) & _) & _).
  assert (RB1 : rdW Wc memc (p + Z.of_nat c + 0) = Some (nth c (mf_line rest) 0)).
  { rewrite Z.add_0_r, (ZS c ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
    rewrite app_nth1 by lia. apply kb_line_nth. lia. }
  assert (RB2 : rdW Wc memc (p + Z.of_nat d + -1) = Some (nth (d - 1) (mf_line rest) 0)).
  { replace (p + Z.of_nat d + -1) with (p + Z.of_nat (d - 1)) by lia.
    rewrite (ZS (d - 1)%nat ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
    rewrite app_nth1 by lia. apply kb_line_nth. lia. }
  destruct (aview_byte SEGS (w_H Wc) memc _ _ RB1) as (bb1 & _ & _ & HB1r).
  destruct (aview_byte SEGS (w_H Wc) memc _ _ RB2) as (bb2 & _ & _ & HB2r).
  assert (U56 : bv_unsigned (ew E 56) = nth c (mf_line rest) 0) by (rewrite E56; apply unsigned_lit_small; lia).
  assert (U57 : bv_unsigned (ew E 57) = nth (d - 1) (mf_line rest) 0) by (rewrite E57; apply unsigned_lit_small; lia).
  assert (UV : U E (SOff 54 0) = p + Z.of_nat c) by (apply (U_atom E 54 _ E54); lia).
  assert (UVE : U E (SOff 55 (-1)) = p + Z.of_nat d - 1) by (rewrite (U_atom_off E 55 _ (-1) E55) by lia; lia).
  assert (Hle2 : (2 <=? d - c)%nat = true) by (apply Nat.leb_le; exact Hlg).
  destruct (Z.eq_dec (nth c (mf_line rest) 0) 39) as [H39 | H39].
  { (* *v is a single quote (39): 0x86698 beq to 0x866a4 *)
    apply (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 54%nat) 0 (0 + 1) 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 39))]))
      in HS1;
      [| vm_compute; reflexivity
       | cbn [restrict ms_mem mkst]; apply (kq_byte_ok E _ _ 54 (p + Z.of_nat c) 0 _ 39 U54);
         [lia | lia | reflexivity | lia | rewrite <- H39; exact RB1]
       | kq_disj; rewrite ?U54, ?U2, ?U8, ?U34, ?U36; unfold mf_s1, SHADOW_OFF in *; repeat split; first [exact I | lia] ].
    destruct (Z.eq_dec (nth (d - 1) (mf_line rest) 0) 39) as [H39' | H39'].
    - (* ve[-1] = *v: the quotes go, 192(s1) = v + 1, 184(s1) = ve - 1 *)
      apply (st_ok_pi_add_region E _ _
        (YP09.mkRegion (Some 55%nat) (-1) (-1 + 1) 0 0 [YP09.mkChunk (-1) (CVal 1 (SLit 39))])) in HS1;
        [| vm_compute; reflexivity
         | cbn [restrict ms_mem mkst]; apply (kq_byte_ok E _ _ 55 (p + Z.of_nat d) (-1) _ 39 U55);
           [lia | lia | reflexivity | lia | rewrite <- H39'; exact RB2]
         | kq_disj; rewrite ?U55, ?U54, ?U2, ?U8, ?U34, ?U36; unfold mf_s1, SHADOW_OFF in *; repeat split;
           first [exact I | lia] ].
      kq_norm HS1.
      kq_run RUNTO HS1 HJ SHOK UV UVE PRA UB U2 HSTK E p K.
      assert (Hq : kb_q (mf_line rest) c d = true)
        by (unfold kb_q; rewrite Hle2, H39', H39; reflexivity).
      kq_fin1 LEAF HS1 HJ K Hq 3%nat U2 E52 E53 U54 U55 EE R2 R9 E32 R18 c d.
    - (* ve[-1] <> *v: no quote *)
      apply (st_ok_pi_add_fact E _ _ 57 (mkAF 0 255 0)) in HS1;
        [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U57; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
      apply (st_ok_pi_add_region E _ _
        (YP09.mkRegion (Some 55%nat) (-1) (-1 + 1) 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 57 0))])) in HS1;
        [| vm_compute; reflexivity
         | cbn [restrict ms_mem mkst];
           apply (kq_byte_ok E _ _ 55 (p + Z.of_nat d) (-1) _ (nth (d - 1) (mf_line rest) 0) U55);
           [lia | lia | cbn [sv_denot]; rewrite U57, Z.add_0_r; reflexivity | lia | exact RB2]
         | kq_disj; rewrite ?U55, ?U54, ?U2, ?U8, ?U34, ?U36; unfold mf_s1, SHADOW_OFF in *; repeat split;
           first [exact I | lia] ].
      apply (kq_add_cond E _ _ BC_NE (SOff 57 0) (SLit 39)) in HS1;
        [| rewrite branch_ne_U, U_SLit, (U_atom E 57 _ E57 ltac:(lia)), zcanon_small by lia;
           apply negb_true_iff; apply Z.eqb_neq; exact H39'].
      kq_norm HS1.
      kq_run RUNTO HS1 HJ SHOK UV UVE PRA UB U2 HSTK E p K.
      assert (Hq : kb_q (mf_line rest) c d = false)
        by (unfold kb_q; rewrite Hle2, H39, (proj2 (Z.eqb_neq _ 39) H39'); reflexivity).
      kq_fin0 LEAF HS1 HJ K Hq 3%nat U2 E52 E53 E54 E55 U54 EE R2 R9 E32 R18 c d. }
  destruct (Z.eq_dec (nth c (mf_line rest) 0) 34) as [H34 | H34].
  { (* *v is a double quote (34): 0x866a0 bne falls through to 0x866a4 *)
    apply (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 54%nat) 0 (0 + 1) 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 34))]))
      in HS1;
      [| vm_compute; reflexivity
       | cbn [restrict ms_mem mkst]; apply (kq_byte_ok E _ _ 54 (p + Z.of_nat c) 0 _ 34 U54);
         [lia | lia | reflexivity | lia | rewrite <- H34; exact RB1]
       | kq_disj; rewrite ?U54, ?U2, ?U8, ?U34, ?U36; unfold mf_s1, SHADOW_OFF in *; repeat split; first [exact I | lia] ].
    destruct (Z.eq_dec (nth (d - 1) (mf_line rest) 0) 34) as [H34' | H34'].
    - apply (st_ok_pi_add_region E _ _
        (YP09.mkRegion (Some 55%nat) (-1) (-1 + 1) 0 0 [YP09.mkChunk (-1) (CVal 1 (SLit 34))])) in HS1;
        [| vm_compute; reflexivity
         | cbn [restrict ms_mem mkst]; apply (kq_byte_ok E _ _ 55 (p + Z.of_nat d) (-1) _ 34 U55);
           [lia | lia | reflexivity | lia | rewrite <- H34'; exact RB2]
         | kq_disj; rewrite ?U55, ?U54, ?U2, ?U8, ?U34, ?U36; unfold mf_s1, SHADOW_OFF in *; repeat split;
           first [exact I | lia] ].
      kq_norm HS1.
      kq_run RUNTO HS1 HJ SHOK UV UVE PRA UB U2 HSTK E p K.
      assert (Hq : kb_q (mf_line rest) c d = true)
        by (unfold kb_q; rewrite Hle2, H34', H34; reflexivity).
      kq_fin1 LEAF HS1 HJ K Hq 3%nat U2 E52 E53 U54 U55 EE R2 R9 E32 R18 c d.
    - apply (st_ok_pi_add_fact E _ _ 57 (mkAF 0 255 0)) in HS1;
        [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U57; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
      apply (st_ok_pi_add_region E _ _
        (YP09.mkRegion (Some 55%nat) (-1) (-1 + 1) 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 57 0))])) in HS1;
        [| vm_compute; reflexivity
         | cbn [restrict ms_mem mkst];
           apply (kq_byte_ok E _ _ 55 (p + Z.of_nat d) (-1) _ (nth (d - 1) (mf_line rest) 0) U55);
           [lia | lia | cbn [sv_denot]; rewrite U57, Z.add_0_r; reflexivity | lia | exact RB2]
         | kq_disj; rewrite ?U55, ?U54, ?U2, ?U8, ?U34, ?U36; unfold mf_s1, SHADOW_OFF in *; repeat split;
           first [exact I | lia] ].
      apply (kq_add_cond E _ _ BC_NE (SOff 57 0) (SLit 34)) in HS1;
        [| rewrite branch_ne_U, U_SLit, (U_atom E 57 _ E57 ltac:(lia)), zcanon_small by lia;
           apply negb_true_iff; apply Z.eqb_neq; exact H34'].
      kq_norm HS1.
      kq_run RUNTO HS1 HJ SHOK UV UVE PRA UB U2 HSTK E p K.
      assert (Hq : kb_q (mf_line rest) c d = false)
        by (unfold kb_q; rewrite Hle2, H34, (proj2 (Z.eqb_neq _ 34) H34'); reflexivity).
      kq_fin0 LEAF HS1 HJ K Hq 3%nat U2 E52 E53 E54 E55 U54 EE R2 R9 E32 R18 c d. }
  (* *v is no quote: 0x866a0 bne to 0x866dc *)
  apply (st_ok_pi_add_fact E _ _ 56 (mkAF 0 255 0)) in HS1;
    [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U56; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  apply (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 54%nat) 0 (0 + 1) 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 56 0))]))
    in HS1;
    [| vm_compute; reflexivity
     | cbn [restrict ms_mem mkst]; apply (kq_byte_ok E _ _ 54 (p + Z.of_nat c) 0 _ (nth c (mf_line rest) 0) U54);
       [lia | lia | cbn [sv_denot]; rewrite U56, Z.add_0_r; reflexivity | lia | exact RB1]
     | kq_disj; rewrite ?U54, ?U2, ?U8, ?U34, ?U36; unfold mf_s1, SHADOW_OFF in *; repeat split; first [exact I | lia] ].
  apply (kq_add_cond E _ _ BC_NE (SOff 56 0) (SLit 39)) in HS1;
    [| rewrite branch_ne_U, U_SLit, (U_atom E 56 _ E56 ltac:(lia)), zcanon_small by lia;
       apply negb_true_iff; apply Z.eqb_neq; exact H39].
  apply (kq_add_cond E _ _ BC_NE (SOff 56 0) (SLit 34)) in HS1;
    [| rewrite branch_ne_U, U_SLit, (U_atom E 56 _ E56 ltac:(lia)), zcanon_small by lia;
       apply negb_true_iff; apply Z.eqb_neq; exact H34].
  kq_norm HS1.
  kq_run RUNTO HS1 HJ SHOK UV UVE PRA UB U2 HSTK E p K.
  assert (Hq : kb_q (mf_line rest) c d = false).
  { unfold kb_q. rewrite Hle2.
    rewrite (proj2 (Z.eqb_neq _ 34) H34), (proj2 (Z.eqb_neq _ 39) H39). reflexivity. }
  kq_fin0 LEAF HS1 HJ K Hq 2%nat U2 E52 E53 E54 E55 U54 EE R2 R9 E32 R18 c d.
Qed.
(* inside the Sections: the Section hypotheses as its assumptions *)
About kb_quote. Print Assumptions kb_quote.
End e.
End f.
End d.
About kb_quote. Print Assumptions kb_quote.
