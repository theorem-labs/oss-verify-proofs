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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 151 of its 209 lines of code are new or changed and 395 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP:
   the helpers its piece files (mf_kignp_1.v ..) share. A walk lane of the image-B m_file-family owner's G2B. ADAPTED from
   the image-A m_file-family lane's image-A lib/A/Prog/m_file_s_kign_1.v (commit a11e040adbd4: ki_st_reg,
   ki_slice_facts, ki_pres) at image B.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's helpers).

   - ki_seed: lib/B/Prog/m_file_sd.v's mf_seed at a K state (low.i in scope, the frame cells, 152(s1) = np, the
     caller's scratch-cell chunks slx) with s9 pinned to atom 33 (= c; mf_regs_at's x25), so that the code's
     reloads `ld s9,112(s1)` (0x8697c, 0x86a50, 0x86c08) leave the symbolic s9 as it was.
   - ki_kslx / ki_vslx: the scratch-cell chunks 208(s1) = k (atom 52) and 192(s1) = v (atom 53), or 192(s1) = v
     alone (atom 52), with their chunk_ok from mf_slot (ki_slot_chunk).
   - ki_reg_same / ki_pres_gen: a register (all callee-saved ones) the run left as the seed had it is the cut's.
   - ki_slot_keep: a frame cell above s1 kept across a callee whose writes are below s1 (ieq's sa_kept).
   - ki_slice_facts: a slice [o, o + n) of the line as ieq_pre's bytes (sa_bytes, sa_addr, sa_heap). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_iq mf_kignp_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the seed's registers with s9 = atom 33 *)
Definition sr_mf9 : list sv := sr_set sr_mf (25%bv : bv 5) (SOff 33 0).
(* the scratch-cell chunks: 208(s1) = k (atom 52), 192(s1) = v (atom 53); or 192(s1) = v alone (atom 52) *)
Definition ki_kslx : list YP09.chunk :=
  [YP09.mkChunk 208 (CVal 8 (SOff 52 0)); YP09.mkChunk 192 (CVal 8 (SOff 53 0))].
Definition ki_vslx : list YP09.chunk := [YP09.mkChunk 192 (CVal 8 (SOff 52 0))].
(* the seed's regions at a K state: cells, 152(s1) = np, the scratch cells, low.i read-only, shadow read-only *)
Definition ki_regions (slx : list YP09.chunk) : smem := mf_regions true true slx false false [] false MF_LOW_ON.
(* the same with the frame cells read-only too (a run that stores nothing): every write window empty *)
Definition ki_regions_ro (slx : list YP09.chunk) : smem :=
  [mf_r_saved; set_window (mf_r_slots true true slx) 0 0; mf_r_fh false; mf_r_low false []; mf_r_ft;
   mf_r_fs false MF_LOW_ON].
Lemma ki_kslx_wf : regions_wf (ki_regions ki_kslx) = true /\ regions_wf (ki_regions_ro ki_kslx) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma ki_vslx_wf : regions_wf (ki_regions ki_vslx) = true /\ regions_wf (ki_regions_ro ki_vslx) = true.
Proof. split; vm_compute; reflexivity. Qed.
(* a run from such a state changed no byte *)
Lemma ki_ro_frame : forall E slx (m m' : word -> option byte), frame_of E (ki_regions_ro slx) m m' -> forall x, m' x = m x.
Proof.
intros E slx m m' HF x. apply HF. intros (r & Hin & Hw).
unfold ki_regions_ro, mf_r_saved, set_window, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs in Hin.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia |]). destruct Hin.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom *)
Lemma ki_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* a register the run left as the seed had it *)
Lemma ki_reg_same : forall E (R0 R : list sv) (regs1 rr : bvmap 5 word) (r : bv 5),
  (forall r, getr regs1 r = sv_denot E (sr_get R0 r)) -> (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  sv_eqb (sr_get R r) (sr_get R0 r) = true -> getr rr r = getr regs1 r.
Proof. intros E R0 R regs1 rr r H0 H1 Hq. rewrite H0, H1. apply sv_eqb_eq in Hq. rewrite Hq. reflexivity. Qed.
(* every callee-saved register the run left as the seed had it *)
Lemma ki_pres_gen : forall E (R0 R : list sv) (regs1 rr : bvmap 5 word),
  (forall r, getr regs1 r = sv_denot E (sr_get R0 r)) -> (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get R0 r)) CALLEE_SAVED = true ->
  aregs_preserved regs1 rr.
Proof.
intros E R0 R regs1 rr H0 H1 HC r Hr.
apply (ki_reg_same E R0 R regs1 rr _ H0 H1).
assert (Hin : In (Z_to_bv 5 r) CALLEE_SAVED).
{ unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    unfold CALLEE_SAVED; cbn [In]; first [ tauto | intuition (apply bv_eq; reflexivity) ]. }
exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.

(* the cur cell's value is a 64-bit word *)
Lemma ki_cur_range : forall v lyc Sc Wc memc mdc pos lowsh mcc cur,
  mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cur_ok mcc cur -> 0 <= mf_cur_ptr (mv_c v) cur < 2 ^ 64.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur CORE LCUR.
pose proof CORE as (_ & _ & _ & _ & _ & _ & (bs & _ & (_ & HL32 & _)) & (CA0 & CA1 & _) & _).
destruct cur as [i|]; [|cbn; lia].
unfold mf_cur_ok in LCUR. unfold mf_cur_ptr, seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* the seed at a K state, s9 pinned to atom 33 *)
Lemma ki_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc cur np (xs : list Z) slx pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_regs_at B v lyc pos regs1 -> mf_cur_ok mcc cur -> mf_np v memc Wc np -> 0 <= np < 2 ^ 64 ->
  Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) slx ->
  regions_wf (ki_regions slx) = true ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos cur np xs) (mkSS pc sr_mf9 (ki_regions slx) None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur np xs slx pc CX CORE CELLS RA LCUR NP Hnp FSLX HWF.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (ki_cur_range v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur CORE LCUR) as Hcur.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc cur np xs pc true true slx false false []
  false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) FSLX (Forall_nil _) HWF)
  as HS0.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _).
pose proof RA as (_ & _ & _ & R25).
assert (E33 : ew (mfE regs1 v lyc pos cur np xs) 33 = Z_to_bv 64 (mv_c v)).
{ pose proof (mfE_extra regs1 v lyc pos cur np xs 1 ltac:(unfold A_TEXT; lia)) as E.
  cbn [Nat.add nth mf_extra map app] in E. exact E. }
pose proof (ast_ok_pi_set_reg_fp _ _ _ (25%bv : bv 5) (SOff 33 0) HS0 eq_refl) as HS1.
unfold ss_mf in HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply HS1.
cbn [restrict ms_regs mkst]. rewrite R25. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* the same seed with the frame cells read-only (for a run that stores nothing: ki_ro_frame) *)
Lemma ki_seed_ro : forall v lyc Sc Wc regs1 memc mdc pos mcc cur np (xs : list Z) slx pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_regs_at B v lyc pos regs1 -> mf_cur_ok mcc cur -> mf_np v memc Wc np -> 0 <= np < 2 ^ 64 ->
  Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) slx ->
  regions_wf (ki_regions slx) = true -> regions_wf (ki_regions_ro slx) = true ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos cur np xs) (mkSS pc sr_mf9 (ki_regions_ro slx) None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur np xs slx pc CX CORE CELLS RA LCUR NP Hnp FSLX HWF HWF2.
pose proof (ki_seed v lyc Sc Wc regs1 memc mdc pos mcc cur np xs slx pc CX CORE CELLS RA LCUR NP Hnp FSLX HWF) as HS.
set (E := mfE regs1 v lyc pos cur np xs) in *.
set (r := mf_r_slots true true slx).
assert (Hn : nth_error (ss_mem (mkSS pc sr_mf9 (ki_regions slx) None mf_facts)) 1 = Some r) by reflexivity.
exact (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS Hn eq_refl HWF2
  (region_ok_rewindow _ E _ r 0 0 (st_ok_pi_region_nth E _ _ 1 r HS Hn) ltac:(intros o Ho; lia))).
Qed.

(* a scratch cell as a chunk of the extra atom 52 + i *)
Lemma ki_slot_chunk : forall v regs1 lyc pos cur np (xs : list Z) (Wc : world SEGS) memc off (i : nat) x,
  nth i xs 0 = x -> (52 + i < A_TEXT)%nat -> 0 <= x < 2 ^ 64 -> mf_slot v memc Wc off x ->
  YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))
    (YP09.mkChunk off (CVal 8 (SOff (52 + i) 0))).
Proof.
intros v regs1 lyc pos cur np xs Wc memc off i x Hx Hi Hx64 Hs.
apply (mf_chunk_atom _ _ _ off (52 + i) 0 x); [rewrite (mfE_xs regs1 v lyc pos cur np xs i Hi), Hx; reflexivity
  | exact Hx64 | lia | rewrite Z.add_0_r; exact Hs].
Qed.
Lemma ki_kslx_ok : forall v regs1 lyc pos cur np (Wc : world SEGS) memc k vv,
  0 <= k < 2 ^ 64 -> 0 <= vv < 2 ^ 64 -> mf_slot v memc Wc 208 k -> mf_slot v memc Wc 192 vv ->
  Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np [k; vv]) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) ki_kslx.
Proof.
intros v regs1 lyc pos cur np Wc memc k vv Hk Hv Sk Sv. unfold ki_kslx.
apply Forall_cons; [apply (ki_slot_chunk v regs1 lyc pos cur np [k; vv] Wc memc 208 0 k); [reflexivity | unfold A_TEXT; lia | exact Hk | exact Sk]|].
apply Forall_cons; [apply (ki_slot_chunk v regs1 lyc pos cur np [k; vv] Wc memc 192 1 vv); [reflexivity | unfold A_TEXT; lia | exact Hv | exact Sv]|].
apply Forall_nil.
Qed.
Lemma ki_vslx_ok : forall v regs1 lyc pos cur np (Wc : world SEGS) memc vv,
  0 <= vv < 2 ^ 64 -> mf_slot v memc Wc 192 vv ->
  Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np [vv]) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) ki_vslx.
Proof.
intros v regs1 lyc pos cur np Wc memc vv Hv Sv. unfold ki_vslx.
apply Forall_cons; [apply (ki_slot_chunk v regs1 lyc pos cur np [vv] Wc memc 192 0 vv); [reflexivity | unfold A_TEXT; lia | exact Hv | exact Sv]|].
apply Forall_nil.
Qed.

(* a frame cell kept across a change below s1 *)
Lemma ki_slot_keep : forall v (Wc W2 : world SEGS) memc mem2 lo off x,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < mf_s1 (mv_sp v)) -> rdW W2 mem2 a = rdW Wc memc a) ->
  0 <= mf_s1 (mv_sp v) -> 0 <= off -> mf_s1 (mv_sp v) + off + 8 <= 2 ^ 64 ->
  mf_slot v memc Wc off x -> mf_slot v mem2 W2 off x.
Proof.
intros v Wc W2 memc mem2 lo off x K H0 Hoff Hhi Hs. unfold mf_slot in *.
apply (iq_val_keep Wc W2 memc mem2); [|exact Hs]. intros y Hy. apply K; lia.
Qed.

(* the text left's sub-range [o, o + n) inside the line: its bytes as list byte, addressable, in the text block *)
Lemma ki_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc cur line p rest ->
  (o + n <= length rest)%nat ->
  sa_bytes (rdW Wc memc) (p + Z.of_nat o) (seg_spec.zb (firstn n (skipn o rest))) /\
  seg_spec.zs (seg_spec.zb (firstn n (skipn o rest))) = firstn n (skipn o rest) /\
  Z.of_nat (length (seg_spec.zb (firstn n (skipn o rest)))) = Z.of_nat n /\
  sa_addr (rdW Wc memc) (p + Z.of_nat o) (Z.of_nat n) /\ sa_heap B lyc Sc (p + Z.of_nat o) (Z.of_nat n) /\
  p + Z.of_nat o <> 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n CX CORE LOOP Hon.
pose proof LOOP as (L1 & L2 & L3 & ((LZ & LN) & LT) & LADDR & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
assert (HZ : sa_zs (rdW Wc memc) (p + Z.of_nat o) (firstn n (skipn o rest))).
{ intros i Hi. rewrite length_firstn, length_skipn in Hi.
  replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia.
  rewrite (LZ (o + i)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [Hlt|Hge]; [|lia].
  rewrite nth_skipn. apply app_nth1. lia. }
destruct (ki_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB & _).
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bt & mt & Hin & Hb & He).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hin) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
assert (Hlen : length (seg_spec.zb (firstn n (skipn o rest))) = n).
{ unfold seg_spec.zb. rewrite length_map, length_firstn, length_skipn. lia. }
pose proof LADDR as (A0 & A1 & AM & ARA & AHV).
assert (Hpe : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hpt : mv_t v <= p) by (rewrite L3; lia).
split; [exact HB|]. split; [exact HZB|]. split; [rewrite Hlen; reflexivity|]. split.
- split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR Hin
      ltac:(lia) ltac:(lia)).
  + intros Hn. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR
      Hin ltac:(lia) ltac:(lia) Hn).
- split; [exists bt, mt; split; [exact Hin | lia] | lia].
Qed.
End e.
End f.
End d.
