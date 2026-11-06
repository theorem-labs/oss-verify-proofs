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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 440 of its 492 lines of code are new or changed and 401 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3; 0x86140), segment S_MF_HDRA: the two refusal
   points REF and REF3 of lib/B/Prog/mf_hdra_m.v, each from MF_TAIL_F (the tail at every FP state):
     hda_ref  : forall n, MF_TAIL_F B n -> HDA_REF_stmt B n
     hda_ref3 : forall n, MF_TAIL_F B n -> HDA_REF3_stmt B n
   A walk lane of the image-B m_file-family owner's G2B (piece 6). The code (the neutral listing of m_file in image B lines
   418-428 and 642-646):
     REF   0x867c0 `mv a0,s9`, 0x867c4 `mv a1,s11`, 0x867c8 `jal m_refuse`, 0x867cc `sd zero,136(s1)`,
           0x867d0 `j 0x867e0`, 0x867e0 `li s4,511`, 0x867e4 `ld s10,152(s1)`, 0x867e8 `j` TAIL 0x86820
     REF3  0x86b40 `mv a0,s9`, 0x86b44 `mv a1,s11`, 0x86b48 `jal m_refuse`, 0x86b4c `sd zero,136(s1)`,
           0x86b50 `j 0x867e4`, 0x867e4 `ld s10,152(s1)`, 0x867e8 `j` TAIL (s4 = 511 is HDA_REF3_stmt's premise; the
           call keeps it, s4 = x20 is callee-saved)
   THE WALK of each point: (1) the seed (m_file_sd.v's mf_seed) at the point, every region read-only, one run to the
   `jal` (a0 = s9 = c, a1 = s11 = line + 1; no byte written, so m_file_k.v's mf_keep_run0 carries the cut facts);
   (2) the call, m_file_rf.v's mf_refuse_step at the `jal`'s listing offset (HDA_J_REF / HDA_J_REF3, slot `PCall
   SS_m_refuse 1`) with knock = false and mcl = mcc; its kept bound from m_file_mdl.v's mf_kept_le_refuse and the
   statement's model equation; (3) back at j + 4 at the FP state fx1 the call returns (sa_frm0 there by
   PaFx.fxrel_frm0), hd6_post1 / hd6_post3: the seed with the frame cells' region writable only on [136, 144) (the
   cur cell) and 152(s1) a chunk (the next line's address, atom 38), one run to TAIL; 136(s1) holds 0 =
   mf_cur_ptr c None, read off the final region (hd6_field); every other byte is kept (kept_of_frame), and
   m_file_k.v's mf_keep_run_s carries mf_core / mf_cells (cur := None) / mf_loop with RW = [s1 + 136, s1 + 144),
   inside mf_rw's last arm and mf_rws. TAIL then gets the refusal's model m_refuse mcc (line + 1) false, cur =
   None, the lines consumed line + 1, the text left mf_rest rest at mf_next p rest (s10 from 152(s1)), the next
   line's loop facts from m_file_k.v's mf_loop_next (refused and overflow grow by at most one, kept does not shrink:
   m_file_mdl.v's m_refuse_sizes), the bound |mf_rest rest| < n from |rest| <= n, rest <> [] and m_file_k.v's
   mf_break_snd, and its model premise from the statement's mf_fin equation.
   OWNS: the two `jal m_refuse` sites 0x867c8 and 0x86b48 and the stores 0x867cc / 0x86b4c. No UBSan trap branch and
   no instrumented check lies in this code. The post-call runs (0x867cc .. 0x867e8, 0x86b4c .. 0x867e8) are adapted
   from the image-B m_file-family owner's walk lane lib/B/Prog/mf_hdrb_5.v hb5_rref2_at (commit
   e93dc77e2c18, the same instructions from 0x86b4c), the call step from a walk lane's mf_keya_r.v kb_ref.
   Section hypotheses: VOBJS (the seed) and m_file_rf.v's SIGP, SSP, RELRO, M_REFUSE, verbatim. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_refuse_c m_file_m m_file_mdl
  m_file_sd m_file_k m_file_rf mf_hdra_t mf_hdra_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the value chunk at offset off of a concrete chunk list (SLit 0 if there is none) *)
Fixpoint hd6_find (off : Z) (cs : list YP09.chunk) : sv :=
  match cs with
  | [] => SLit 0
  | YP09.mkChunk o (CVal _ e) :: r => if Z.eqb o off then e else hd6_find off r
  | _ :: r => hd6_find off r
  end.

(* membership of a concrete chunk in a concrete chunk list *)
Ltac hd6_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the state's form, computed *)
Ltac hd6_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* the awr_ok goal with its region list computed *)
Ltac hd6_awr_norm :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
(* every region of the state is read-only *)
Ltac hd6_awr_ro := hd6_awr_norm; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the w-byte field at offset off of a final region HR whose base atom U names *)
Ltac hd6_field HR U off w V :=
  lazymatch type of HR with region_ok _ ?E _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    let e := eval vm_compute in (hd6_find off cs) in
    pose proof (field_of_region_any E _ n _ cs lo hi wlo whi off w e HR U ltac:(hd6_in) ltac:(cbn; lia)) as V
  end.
(* the pc of the goal's configuration as the listing offset pc *)
Ltac hd6_pc pc := lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ =>
  let Hk := fresh in assert (Hk : k = pc) by (vm_compute; reflexivity); rewrite Hk; clear Hk end.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* the text after the line is shorter than the text left *)
Lemma hd6_rest_lt : forall rest, rest <> [] -> (length (mf_rest rest) < length rest)%nat.
Proof. intros rest Hne. destruct (mf_break_snd rest) as (_ & Hlt & _). unfold mf_rest. exact (Hlt Hne). Qed.

(* ============================ the runs after the call, at one FP state ============================ *)
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

(* the numbers every run reads: the block below the ceiling, the stack above it, the frame *)
Lemma hd6_geo : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= alloc_ceiling /\ mv_c v mod 16 = 0 /\
alloc_ceiling + 8592 <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\
mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320 /\
0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX CORE.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & Hc16 & _).
destruct (mf_s1_facts B v CX) as (S1 & S2 & S3). destruct (mf_sp0 B v CX) as (P1 & P2 & P3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S3, P1.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
repeat split; try lia.
Qed.

(* REF's run after the call: 0x867cc `sd zero,136(s1)` (cur = NULL), `j 0x867e0`, `li s4,511`,
   `ld s10,152(s1)`, `j` TAIL. The block holds mcn (the refusal's model), 136(s1) still holds the line's cursor cur0,
   the line loop is at the line's start model mc0, and the next line's loop facts are given at mcn and None *)
Lemma hd6_post1 : forall n, MF_TAIL_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcn : mconf) (cur0 : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn -> mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest ->
mf_loop v Wc memc mcn None (line + 1) (mf_next p rest) (mf_rest rest) ->
fst (m_lines (mcn, None) (line + 1) (lines (mf_rest rest))) = mf_final v ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc (HDA_J_REF + 4).
Proof.
intros n HT v lyc Sc Wc regs1 memc mdc pos mc0 mcn cur0 line p rest
  CX LS FRM CORE CELLS RA Hlen Hne LP LPN FIN R27 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hd6_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold seg_spec.SEG_M_SIZE in G2.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcn None (mf_next p rest) [] (HDA_J_REF + 4)
  false true [] false false [] false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia)
  (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos None (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos None (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E38.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply mf_w64_u; lia).
(* the frame cells writable only on [136, 144): the cur cell *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 136 144) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 136 144 HR1
      ltac:(intros o Ho; apply (proj1 (proj2 (proj2 HR1))); cbn; lia))) as HS1 end.
clear HS0 HR1. hd6_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan MF_TAIL.
{ hd6_awr_norm.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite ?HSTK; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the bytes outside the cur cell are kept *)
set (RW := fun x => mf_s1 (mv_sp v) + 136 <= x < mf_s1 (mv_sp v) + 144).
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) RW HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; unfold RW; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U2 in Hr; lia] |]);
    destruct Hinw | ] end.
(* 136(s1) holds 0 = mf_cur_ptr c None *)
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 1%nat _ HS1 eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
hd6_field HRS U2 136 8%N V136.
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) None)).
{ cbn [mf_cur_ptr]. lazymatch type of V136 with val_mem _ _ _ _ ?x => replace x with 0 in V136 by (vm_compute; reflexivity) end.
  change (N.to_nat 8) with 8%nat in V136. exact V136. }
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj. pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH j Hj)].
  intros k Hk HR. unfold RW, SHADOW_OFF in HR. lia. }
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcn).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) RW _ _ K);
    [lia | unfold seg_spec.SEG_M_SIZE; lia | intros a Ha HR; unfold RW in HR; unfold seg_spec.SEG_M_SIZE in Ha; lia
    | exact Hmc]. }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold RW in Ha; unfold mf_rw; right; right; right; right; right; lia).
assert (RWS : mf_rws v RW) by (intros a Ha _; unfold RW in Ha; left; exact Ha).
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn cur0 (ms_mem ms) _ RW MF_LOW_OFF None mcn
  CX CORE CELLS HJ K RWok RWS VSH' V136' MC') as (CORE' & CELLS' & LOOPK).
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
pose proof (hd6_rest_lt rest Hne) as Hrl.
pmkst HS1.
apply (HT v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcn None (line + 1) (mf_next p rest) (mf_rest rest)
  CX LS FRM CORE' CELLS' RA').
+ lia.
+ exact (LOOPK _ _ _ _ _ LPN).
+ exact FIN.
+ rewrite Q26, E38. reflexivity.
+ rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
+ rewrite Q20. first [reflexivity | vm_compute; reflexivity].
Qed.

(* REF3's run after the call: 0x86b4c `sd zero,136(s1)` (cur = NULL), `j 0x867e4`, `ld s10,152(s1)`, `j` TAIL; s4 =
   511 already *)
Lemma hd6_post3 : forall n, MF_TAIL_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcn : mconf) (cur0 : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn -> mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest ->
mf_loop v Wc memc mcn None (line + 1) (mf_next p rest) (mf_rest rest) ->
fst (m_lines (mcn, None) (line + 1) (lines (mf_rest rest))) = mf_final v ->
getr regs1 27 = w64 (line + 1) -> getr regs1 20 = w64 511 -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc (HDA_J_REF3 + 4).
Proof.
intros n HT v lyc Sc Wc regs1 memc mdc pos mc0 mcn cur0 line p rest
  CX LS FRM CORE CELLS RA Hlen Hne LP LPN FIN R27 R20 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hd6_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold seg_spec.SEG_M_SIZE in G2.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcn None (mf_next p rest) [] (HDA_J_REF3 + 4)
  false true [] false false [] false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia)
  (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos None (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos None (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E38.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply mf_w64_u; lia).
(* the frame cells writable only on [136, 144): the cur cell *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 136 144) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 136 144 HR1
      ltac:(intros o Ho; apply (proj1 (proj2 (proj2 HR1))); cbn; lia))) as HS1 end.
clear HS0 HR1. hd6_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan MF_TAIL.
{ hd6_awr_norm.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite ?HSTK; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the bytes outside the cur cell are kept *)
set (RW := fun x => mf_s1 (mv_sp v) + 136 <= x < mf_s1 (mv_sp v) + 144).
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) RW HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; unfold RW; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U2 in Hr; lia] |]);
    destruct Hinw | ] end.
(* 136(s1) holds 0 = mf_cur_ptr c None *)
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 1%nat _ HS1 eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
hd6_field HRS U2 136 8%N V136.
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) None)).
{ cbn [mf_cur_ptr]. lazymatch type of V136 with val_mem _ _ _ _ ?x => replace x with 0 in V136 by (vm_compute; reflexivity) end.
  change (N.to_nat 8) with 8%nat in V136. exact V136. }
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj. pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH j Hj)].
  intros k Hk HR. unfold RW, SHADOW_OFF in HR. lia. }
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcn).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) RW _ _ K);
    [lia | unfold seg_spec.SEG_M_SIZE; lia | intros a Ha HR; unfold RW in HR; unfold seg_spec.SEG_M_SIZE in Ha; lia
    | exact Hmc]. }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold RW in Ha; unfold mf_rw; right; right; right; right; right; lia).
assert (RWS : mf_rws v RW) by (intros a Ha _; unfold RW in Ha; left; exact Ha).
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcn cur0 (ms_mem ms) _ RW MF_LOW_OFF None mcn
  CX CORE CELLS HJ K RWok RWS VSH' V136' MC') as (CORE' & CELLS' & LOOPK).
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
pose proof (hd6_rest_lt rest Hne) as Hrl.
pmkst HS1.
apply (HT v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcn None (line + 1) (mf_next p rest) (mf_rest rest)
  CX LS FRM CORE' CELLS' RA').
+ lia.
+ exact (LOOPK _ _ _ _ _ LPN).
+ exact FIN.
+ rewrite Q26, E38. reflexivity.
+ rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
+ rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
Qed.
End e.
End f.
End d.

(* ============================ the two refusal points ============================ *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a run whose regions are all read-only changed no byte *)
Ltac hd6_kept0 K := lazymatch goal with
| HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m1 a = aview SEGS H m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs H m0 m1 (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hin Hr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia | ]); destruct Hin
  | ] end.
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
(* the shared hypotheses m_file_rf.v's mf_refuse_step needs, verbatim *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
(* the callee, at every FP state (the image-B m_file segment table's m_refuse row) *)
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* 0x867c0: a0 = s9 = c, a1 = s11 = line + 1, m_refuse (c, line + 1) at 0x867c8, then hd6_post1 at the returned FP
   state *)
Lemma hda_ref : forall n, MF_TAIL_F B n -> HDA_REF_stmt B n.
Proof.
intros n TL. unfold HDA_REF_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP)
  RA FIN R27.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & LK0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnp.
pose proof CORE as (HJ & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] HDA_REF
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
(* the frame cells read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. hd6_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
(* `mv a0,s9`, `mv a1,s11`, stopped at the `jal` 0x867c8 *)
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan HDA_J_REF.
{ hd6_awr_ro. }
hd6_kept0 K0.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md1 := d) in *; clearbody md1 end.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) md1 CX CORE CELLS HJ K0)
  as (CORE1 & CELLS1 & NPK1 & LOOPK1).
pose proof (NPK1 _ NP) as NP1. pose proof (LOOPK1 _ _ _ _ _ LOOP) as LOOP1. clear NPK1 LOOPK1.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (27%bv : bv 5) Q27. prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11.
assert (RA1 : mf_regs_at B v lyc pos (ms_regs ms)).
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
assert (A10 : getr (ms_regs ms) 10 = w64 (mv_c v)) by (rewrite Q10, (EE 25%nat 25%bv eq_refl); exact R25).
assert (A11 : getr (ms_regs ms) 11 = w64 (line + 1)) by (rewrite Q11, (EE 27%nat 27%bv eq_refl); exact R27).
assert (A27 : getr (ms_regs ms) 27 = w64 (line + 1)) by (rewrite Q27, (EE 27%nat 27%bv eq_refl); exact R27).
pose proof (mf_regs_at_call B v lyc pos _ RA1) as (S2r & S3r & S4r & S8r).
pmkst HS1. hd6_pc HDA_J_REF.
(* the call: m_refuse (c, line + 1), knock = false, the loop at mcc *)
apply (mf_refuse_step (fx := fx) B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) md1 pos MF_LOW_OFF mcc mcc
  false cur line p rest (mf_next p rest) HDA_J_REF CX LS FRM
  (mf_corek_of_core B v lyc Sc Wc (ms_mem ms) md1 pos MF_LOW_OFF mcc CORE1) CELLS1 NP1 S2r S3r S4r S8r LOOP1 Hne
  eq_refl LK0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) A10 A11
  (mf_kept_le_refuse mcc (line + 1) false None (line + 1) (lines (mf_rest rest)) (mf_final v) I FIN)).
intros fx1 ly2 S2 W2 regs2 mem2 md2 HFX LS2 CORE2 CELLS2 NP2 LOOP2 HCS.
assert (Ely : ly2 = lyc) by (destruct LS2 as (E1 & _); destruct LS as (E2 & _); congruence). subst ly2.
assert (H27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (HCS 27 ltac:(unfold acallee_saved; lia)).
(* the next line's loop facts at the refusal's model and cur = NULL *)
assert (LOOPn : mf_loop v W2 mem2 (m_refuse mcc (line + 1) false) None (line + 1) (mf_next p rest) (mf_rest rest)).
{ apply (mf_loop_next v W2 mem2 mcc cur line p rest (m_refuse mcc (line + 1) false) None LOOP2 Hne).
  - unfold m_refuse. cbn [mc_refused]. lia.
  - unfold m_refuse. cbn [mc_overflow]. lia.
  - exact (proj1 (proj2 (m_refuse_sizes mcc (line + 1) false))).
  - exact I. }
exact (hd6_post1 (fx := fx1) B VOBJS n (TL fx1) v lyc S2 W2 regs2 mem2 md2 pos mcc (m_refuse mcc (line + 1) false)
  cur line p rest CX LS2 (PaFx.fxrel_frm0 fx fx1 FRM HFX) CORE2 CELLS2
  (mf_regs_at_kept B v lyc pos (ms_regs ms) regs2 RA1 HCS) Hlen Hne LOOP2 LOOPn FIN
  ltac:(rewrite H27; exact A27) NP2).
Qed.

(* 0x86b40: a0 = s9 = c, a1 = s11 = line + 1, m_refuse (c, line + 1) at 0x86b48, then hd6_post3 at the returned FP
   state; s4 = 511 is the statement's and the call keeps it *)
Lemma hda_ref3 : forall n, MF_TAIL_F B n -> HDA_REF3_stmt B n.
Proof.
intros n TL. unfold HDA_REF3_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP)
  RA FIN R27 R20.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & LK0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnp.
pose proof CORE as (HJ & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] HDA_REF3
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
(* the frame cells read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. hd6_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
(* `mv a0,s9`, `mv a1,s11`, stopped at the `jal` 0x86b48 *)
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan HDA_J_REF3.
{ hd6_awr_ro. }
hd6_kept0 K0.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => set (md1 := d) in *; clearbody md1 end.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) md1 CX CORE CELLS HJ K0)
  as (CORE1 & CELLS1 & NPK1 & LOOPK1).
pose proof (NPK1 _ NP) as NP1. pose proof (LOOPK1 _ _ _ _ _ LOOP) as LOOP1. clear NPK1 LOOPK1.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (27%bv : bv 5) Q27. prreg HS1 (20%bv : bv 5) Q20. prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11.
assert (RA1 : mf_regs_at B v lyc pos (ms_regs ms)).
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
assert (A10 : getr (ms_regs ms) 10 = w64 (mv_c v)) by (rewrite Q10, (EE 25%nat 25%bv eq_refl); exact R25).
assert (A11 : getr (ms_regs ms) 11 = w64 (line + 1)) by (rewrite Q11, (EE 27%nat 27%bv eq_refl); exact R27).
assert (A27 : getr (ms_regs ms) 27 = w64 (line + 1)) by (rewrite Q27, (EE 27%nat 27%bv eq_refl); exact R27).
assert (A20 : getr (ms_regs ms) 20 = w64 511) by (rewrite Q20, (EE 20%nat 20%bv eq_refl); exact R20).
pose proof (mf_regs_at_call B v lyc pos _ RA1) as (S2r & S3r & S4r & S8r).
pmkst HS1. hd6_pc HDA_J_REF3.
(* the call: m_refuse (c, line + 1), knock = false, the loop at mcc *)
apply (mf_refuse_step (fx := fx) B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) md1 pos MF_LOW_OFF mcc mcc
  false cur line p rest (mf_next p rest) HDA_J_REF3 CX LS FRM
  (mf_corek_of_core B v lyc Sc Wc (ms_mem ms) md1 pos MF_LOW_OFF mcc CORE1) CELLS1 NP1 S2r S3r S4r S8r LOOP1 Hne
  eq_refl LK0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) A10 A11
  (mf_kept_le_refuse mcc (line + 1) false None (line + 1) (lines (mf_rest rest)) (mf_final v) I FIN)).
intros fx1 ly2 S2 W2 regs2 mem2 md2 HFX LS2 CORE2 CELLS2 NP2 LOOP2 HCS.
assert (Ely : ly2 = lyc) by (destruct LS2 as (E1 & _); destruct LS as (E2 & _); congruence). subst ly2.
assert (H27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (HCS 27 ltac:(unfold acallee_saved; lia)).
assert (H20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (HCS 20 ltac:(unfold acallee_saved; lia)).
(* the next line's loop facts at the refusal's model and cur = NULL *)
assert (LOOPn : mf_loop v W2 mem2 (m_refuse mcc (line + 1) false) None (line + 1) (mf_next p rest) (mf_rest rest)).
{ apply (mf_loop_next v W2 mem2 mcc cur line p rest (m_refuse mcc (line + 1) false) None LOOP2 Hne).
  - unfold m_refuse. cbn [mc_refused]. lia.
  - unfold m_refuse. cbn [mc_overflow]. lia.
  - exact (proj1 (proj2 (m_refuse_sizes mcc (line + 1) false))).
  - exact I. }
exact (hd6_post3 (fx := fx1) B VOBJS n (TL fx1) v lyc S2 W2 regs2 mem2 md2 pos mcc (m_refuse mcc (line + 1) false)
  cur line p rest CX LS2 (PaFx.fxrel_frm0 fx fx1 FRM HFX) CORE2 CELLS2
  (mf_regs_at_kept B v lyc pos (ms_regs ms) regs2 RA1 HCS) Hlen Hne LOOP2 LOOPn FIN
  ltac:(rewrite H27; exact A27) ltac:(rewrite H20; exact A20) NP2).
Qed.
End i.
End h.
End g.
About hda_ref.
About hda_ref3.
Print Assumptions hda_ref.
Print Assumptions hda_ref3.
